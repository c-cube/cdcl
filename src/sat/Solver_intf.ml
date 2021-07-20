(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

(** Interface for Solvers

    This modules defines the safe external interface for solvers.
    Solvers that implements this interface can be obtained using the [Make]
    functor in {!Solver} or {!Mcsolver}.
*)

type 'a printer = Format.formatter -> 'a -> unit

module type SAT_STATE = sig
  type formula

  val eval : formula -> bool
  (** Returns the valuation of a formula in the current state
      of the sat solver.
      @raise UndecidedLit if the literal is not decided *)

  val eval_level : formula -> bool * int
  (** Return the current assignement of the literals, as well as its
      decision level. If the level is 0, then it is necessary for
      the atom to have this value; otherwise it is due to choices
      that can potentially be backtracked.
      @raise UndecidedLit if the literal is not decided *)

  val iter_trail : (formula -> unit) -> unit
  (** Iter through the formulas in order of decision/propagation
      (starting from the first propagation, to the last propagation). *)
end

type 'form sat_state = (module SAT_STATE with type formula = 'form)
(** The type of values returned when the solver reaches a SAT state. *)

module type UNSAT_STATE = sig
  type atom
  type clause
  type proof

  val unsat_conflict : unit -> clause
  (** Returns the unsat clause found at the toplevel *)

  val get_proof : unit -> proof
  (** returns a persistent proof of the empty clause from the Unsat result. *)

  val unsat_assumptions: unit -> atom list
  (** Subset of assumptions responsible for "unsat" *)
end

type ('atom, 'clause, 'proof) unsat_state =
  (module UNSAT_STATE with type atom = 'atom
                       and type clause = 'clause
                       and type proof = 'proof)
(** The type of values returned when the solver reaches an UNSAT state. *)

type negated =
  | Negated     (** changed sign *)
  | Same_sign   (** kept sign *)
(** This type is used during the normalisation of formulas.
    See {!val:Expr_intf.S.norm} for more details. *)

(** The type of reasons for propagations of a formula [f]. *)
type ('formula, 'proof) reason =
  | Consequence of (unit -> 'formula list * 'proof) [@@unboxed]
  (** [Consequence (l, p)] means that the formulas in [l] imply the propagated
      formula [f]. The proof should be a proof of the clause "[l] implies [f]".

      invariant: in [Consequence (fun () -> l,p)], all elements of [l] must be true in
      the current trail.

      {b note} on lazyiness: the justification is suspended (using [unit -> …])
      to avoid potentially costly computations that might never be used
      if this literal is backtracked without participating in a conflict.
      Therefore the function that produces [(l,p)] needs only be safe in
      trails (partial models) that are conservative extensions of the current
      trail.
      If the theory isn't robust w.r.t. extensions of the trail (e.g. if
      its internal state undergoes significant changes),
      it can be easier to produce the explanation eagerly when
      propagating, and then use [Consequence (fun () -> expl, proof)] with
      the already produced [(expl,proof)] tuple.
  *)

type lbool = L_true | L_false | L_undefined
(** Valuation of an atom *)

module type ACTS = sig
  type formula
  type proof

  val iter_assumptions: (formula -> unit) -> unit
  (** Traverse the new assumptions on the boolean trail. *)

  val eval_lit: formula -> lbool
  (** Obtain current value of the given literal *)

  val mk_lit: ?default_pol:bool -> formula -> unit
  (** Map the given formula to a literal, which will be decided by the
      SAT solver. *)

  val add_clause: ?keep:bool -> formula list -> proof -> unit
  (** Add a clause to the solver.
      @param keep if true, the clause will be kept by the solver.
        Otherwise the solver is allowed to GC the clause and propose this
        partial model again.
  *)

  val raise_conflict: formula list -> proof -> 'b
  (** Raise a conflict, yielding control back to the solver.
      The list of atoms must be a valid theory lemma that is false in the
      current trail. *)

  val propagate: formula -> (formula, proof) reason -> unit
  (** Propagate a formula, i.e. the theory can evaluate the formula to be true
      (see the definition of {!type:eval_res} *)

  val add_decision_lit: formula -> bool -> unit
  (** Ask the SAT solver to decide on the given formula with given sign
      before it can answer [SAT]. The order of decisions is still unspecified.
      Useful for theory combination. This will be undone on backtracking. *)
end

(* TODO: find a way to use atoms instead of formulas here *)
type ('formula, 'proof) acts =
  (module ACTS with type formula = 'formula
                and type proof = 'proof)
(** The type for a slice of assertions to assume/propagate in the theory. *)

exception No_proof

module type FORMULA = sig
  (** formulas *)

  type t
  (** The type of atomic formulas over terms. *)

  val equal : t -> t -> bool
  (** Equality over formulas. *)

  val hash : t -> int
  (** Hashing function for formulas. Should be such that two formulas equal according
      to {!val:Expr_intf.S.equal} have the same hash. *)

  val pp : t printer
  (** Printing function used among other thing for debugging.  *)

  val neg : t -> t
  (** Formula negation *)

  val norm : t -> t * negated
  (** Returns a 'normalized' form of the formula, possibly negated
      (in which case return [Negated]).
      [norm] must be so that [a] and [neg a] normalise to the same formula,
      but one returns [Negated] and the other [Same_sign]. *)
end

(** Signature for theories to be given to the CDCL(T) solver *)
module type PLUGIN_CDCL_T = sig
  type t
  (** The plugin state itself *)

  module Formula : FORMULA

  type proof

  val push_level : t -> unit
  (** Create a new backtrack level *)

  val pop_levels : t -> int -> unit
  (** Pop [n] levels of the theory *)

  val partial_check : t -> (Formula.t, proof) acts -> unit
  (** Assume the formulas in the slice, possibly using the [slice]
      to push new formulas to be propagated or to raising a conflict or to add
      new lemmas. *)

  val final_check : t -> (Formula.t, proof) acts -> unit
  (** Called at the end of the search in case a model has been found.
      If no new clause is pushed, then proof search ends and "sat" is returned;
      if lemmas are added, search is resumed;
      if a conflict clause is added, search backtracks and then resumes. *)
end

(** Signature for pure SAT solvers *)
module type PLUGIN_SAT = sig
  module Formula : FORMULA

  type proof
end

module type PROOF = sig
  (** Signature for a module handling proof by resolution from sat solving traces *)

  (** {3 Type declarations} *)

  exception Resolution_error of string
  (** Raised when resolution failed. *)

  type formula
  type atom
  type lemma
  type clause
  (** Abstract types for atoms, clauses and theory-specific lemmas *)

  type store

  type t
  (** Lazy type for proof trees. Proofs are persistent objects, and can be
      extended to proof nodes using functions defined later. *)

  and proof_node = {
    conclusion : clause;  (** The conclusion of the proof *)
    step : step;          (** The reasoning step used to prove the conclusion *)
  }
  (** A proof can be expanded into a proof node, which show the first step of the proof. *)

  (** The type of reasoning steps allowed in a proof. *)
  and step =
    | Hypothesis of lemma
    (** The conclusion is a user-provided hypothesis *)
    | Assumption
    (** The conclusion has been locally assumed by the user *)
    | Lemma of lemma
    (** The conclusion is a tautology provided by the theory, with associated proof *)
    | Duplicate of t * atom list
    (** The conclusion is obtained by eliminating multiple occurences of the atom in
        the conclusion of the provided proof. *)
    | Hyper_res of hyper_res_step

  and hyper_res_step = {
    hr_init: t;
    hr_steps: (atom * t) list; (* list of pivot+clause to resolve against [init] *)
  }

  (** {3 Proof building functions} *)

  val prove : store -> clause -> t
  (** Given a clause, return a proof of that clause.
      @raise Resolution_error if it does not succeed. *)

  val prove_unsat : store -> clause -> t
  (** Given a conflict clause [c], returns a proof of the empty clause.
      @raise Resolution_error if it does not succeed. *)

  val prove_atom : store -> atom -> t option
  (** Given an atom [a], returns a proof of the clause [[a]] if [a] is true at level 0 *)

  val res_of_hyper_res : store -> hyper_res_step -> t * t * atom
  (** Turn an hyper resolution step into a resolution step.
      The conclusion can be deduced by performing a resolution between the conclusions
      of the two given proofs.
      The atom on which to perform the resolution is also given. *)

  (** {3 Proof Nodes} *)

  val parents : step -> t list
  (** Returns the parents of a proof node. *)

  val is_leaf : step -> bool
  (** Returns wether the the proof node is a leaf, i.e. an hypothesis,
      an assumption, or a lemma.
      [true] if and only if {!parents} returns the empty list. *)

  val expl : step -> string
  (** Returns a short string description for the proof step; for instance
      ["hypothesis"] for a [Hypothesis]
      (it currently returns the variant name in lowercase). *)


  (** {3 Proof Manipulation} *)

  val expand : store -> t -> proof_node
  (** Return the proof step at the root of a given proof. *)

  val conclusion : t -> clause
  (** What is proved at the root of the clause *)

  val fold : store -> ('a -> proof_node -> 'a) -> 'a -> t -> 'a
  (** [fold f acc p], fold [f] over the proof [p] and all its node. It is guaranteed that
      [f] is executed exactly once on each proof node in the tree, and that the execution of
      [f] on a proof node happens after the execution on the parents of the nodes. *)

  val unsat_core : t -> clause list
  (** Returns the unsat_core of the given proof, i.e the lists of conclusions
      of all leafs of the proof.
      More efficient than using the [fold] function since it has
      access to the internal representation of proofs *)

  (** {3 Misc} *)

  val check_empty_conclusion : store -> t -> unit
  (** Check that the proof's conclusion is the empty clause,
      @raise Resolution_error otherwise *)

  val check : store -> t -> unit
  (** Check the contents of a proof. Mainly for internal use. *)

  module Tbl : Hashtbl.S with type key = t
end

(** The external interface implemented by safe solvers, such as the one
    created by the {!Solver.Make} and {!Mcsolver.Make} functors. *)
module type S = sig
  (** {2 Internal modules}
      These are the internal modules used, you should probably not use them
      if you're not familiar with the internals of mSAT. *)

  module Formula : FORMULA

  type formula = Formula.t (** user formulas *)

  type atom
  (** The type of atoms given by the module argument for formulas.
      An atom is a user-defined atomic formula whose truth value is
      picked by Msat. *)

  type clause

  type theory

  type lemma
  (** A theory lemma or an input axiom *)

  type solver

  type store

  (* TODO: keep this internal *)
  module Atom : sig
    type t = atom

    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
    val neg : t -> t
    val sign : t -> bool
    val abs : t -> t

    val pp : store -> t printer
    (** Print the atom *)

    val formula : store -> t -> formula
    (** Get back the formula for this atom *)
  end

  module Clause : sig
    type t = clause
    val equal : t -> t -> bool

    module Tbl : Hashtbl.S with type key = t

    val pp : store -> t printer
    (** Print the clause *)

    val short_name : store -> t -> string
    (** Short name for a clause. Unspecified *)

    val atoms : store -> t -> atom Iter.t
    (** Atoms of a clause *)

    val atoms_a : store -> t -> atom array

    val atoms_l : store -> t -> atom list
    (** List of atoms of a clause *)
  end

  module Proof : PROOF
    with type clause = clause
     and type atom = atom
     and type formula = formula
     and type lemma = lemma
     and type store = store
  (** A module to manipulate proofs. *)

  type t = solver
  (** Main solver type, containing all state for solving. *)

  val create :
    ?on_conflict:(atom array -> unit) ->
    ?on_decision:(atom -> unit) ->
    ?on_new_atom:(atom -> unit) ->
    ?store_proof:bool ->
    ?size:[`Tiny|`Small|`Big] ->
    theory ->
    t
  (** Create new solver
      @param theory the theory
      @param store_proof if true, stores proof (default [true]). Otherwise
        the functions that return proofs will fail with [No_proof]
      @param size the initial size of internal data structures. The bigger,
        the faster, but also the more RAM it uses. *)

  val theory : t -> theory
  (** Access the theory state *)

  val store : t -> store
  (** Store for the solver *)

  (** {2 Types} *)

  (** Result type for the solver *)
  type res =
    | Sat of formula sat_state (** Returned when the solver reaches SAT, with a model *)
    | Unsat of (atom,clause,Proof.t) unsat_state (** Returned when the solver reaches UNSAT, with a proof *)

  exception UndecidedLit
  (** Exception raised by the evaluating functions when a literal
      has not yet been assigned a value. *)

  (** {2 Base operations} *)

  val assume : t -> formula list list -> lemma -> unit
  (** Add the list of clauses to the current set of assumptions.
      Modifies the sat solver state in place. *)

  val add_clause : t -> atom list -> lemma -> unit
  (** Lower level addition of clauses *)

  val add_clause_a : t -> atom array -> lemma -> unit
  (** Lower level addition of clauses *)

  val solve :
    ?assumptions:atom list ->
    t -> res
  (** Try and solves the current set of clauses.
      @param assumptions additional atomic assumptions to be temporarily added.
        The assumptions are just used for this call to [solve], they are
        not saved in the solver's state. *)

  val make_atom : t -> ?default_pol:bool -> formula -> atom
  (** Add a new atom (i.e propositional formula) to the solver.
      This formula will be decided on at some point during solving,
      wether it appears in clauses or not.
      @param default_pol default polarity of the boolean variable.
        Default is [true]. *)

  val true_at_level0 : t -> atom -> bool
  (** [true_at_level0 a] returns [true] if [a] was proved at level0, i.e.
      it must hold in all models *)

  val eval_atom : t -> atom -> lbool
  (** Evaluate atom in current state *)

  val n_propagations : t -> int
  val n_decisions : t -> int
  val n_conflicts : t -> int
  val n_minimized_away : t -> int
end

