
(** {1 Main Environment}

    Theories and concrete solvers rely on an environment that defines
    several important types:

    - sorts
    - terms (to represent logic expressions and formulas)
    - a congruence closure instance
*)

module Fmt = CCFormat

module type MERGE_PP = sig
  type t
  val merge : t -> t -> t
  val pp : t Fmt.printer
end

module CC_view = struct
  type ('f, 't, 'ts) t =
    | Bool of bool
    | App_fun of 'f * 'ts
    | App_ho of 't * 'ts
    | If of 't * 't * 't
    | Eq of 't * 't
    | Not of 't
    | Opaque of 't (* do not enter *)

  let[@inline] map_view ~f_f ~f_t ~f_ts (v:_ t) : _ t =
    match v with
    | Bool b -> Bool b
    | App_fun (f, args) -> App_fun (f_f f, f_ts args)
    | App_ho (f, args) -> App_ho (f_t f, f_ts args)
    | Not t -> Not (f_t t)
    | If (a,b,c) -> If (f_t a, f_t b, f_t c)
    | Eq (a,b) -> Eq (f_t a, f_t b)
    | Opaque t -> Opaque (f_t t)

  let iter_view ~f_f ~f_t ~f_ts (v:_ t) : unit =
    match v with
    | Bool _ -> ()
    | App_fun (f, args) -> f_f f; f_ts args
    | App_ho (f, args) -> f_t f; f_ts args
    | Not t -> f_t t
    | If (a,b,c) -> f_t a; f_t b; f_t c;
    | Eq (a,b) -> f_t a; f_t b
    | Opaque t -> f_t t
end

module type TERM = sig
  module Fun : sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer
  end

  module Ty : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer

    val is_bool : t -> bool
  end

  module Term : sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer
    val ty : t -> Ty.t

    val iter_dag : t -> t Iter.t
    (** Iterate over the subterms, using sharing *)

    type state

    val bool : state -> bool -> t
  end
end

module type TERM_LIT = sig
  include TERM

  module Lit : sig
    type t
    val neg : t -> t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
    val pp : t Fmt.printer

    val term : t -> Term.t
    val sign : t -> bool
    val abs : t -> t
    val apply_sign : t -> bool -> t
    val norm_sign : t -> t * bool
    (** Invariant: if [u, sign = norm_sign t] then [apply_sign u sign = t] *)

    val atom : Term.state -> ?sign:bool -> Term.t -> t
  end
end

module type CORE_TYPES = sig
  include TERM_LIT

  (** {3 Semantic values} *)
  module Value : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val ty : t -> Ty.t
    val pp : t Fmt.printer
  end

  module Lemma : sig
    type t
    val pp : t Fmt.printer

    val default : t
    (* TODO: to give more details? or make this extensible?
       or have a generative function for new proof cstors?
    val cc_lemma : unit -> t
       *)
  end
end

module type CC_ARG = sig
  module A : CORE_TYPES
  open A

  val cc_view : Term.t -> (Fun.t, Term.t, Term.t Iter.t) CC_view.t
  (** View the term through the lens of the congruence closure *)

  module Actions : sig
    type t

    val raise_conflict : t -> Lit.t list -> Lemma.t -> 'a

    val propagate : t -> Lit.t -> reason:Lit.t Iter.t -> Lemma.t -> unit
  end
end

module type CC_S = sig
  module A : CORE_TYPES
  module CC_A : CC_ARG with module A=A
  type term_state = A.Term.state
  type term = A.Term.t
  type fun_ = A.Fun.t
  type lit = A.Lit.t
  type lemma = A.Lemma.t
  type actions = CC_A.Actions.t

  type t
  (** Global state of the congruence closure *)

  (** An equivalence class is a set of terms that are currently equal
      in the partial model built by the solver.
      The class is represented by a collection of nodes, one of which is
      distinguished and is called the "representative".

      All information pertaining to the whole equivalence class is stored
      in this representative's node.

      When two classes become equal (are "merged"), one of the two
      representatives is picked as the representative of the new class.
      The new class contains the union of the two old classes' nodes.

      We also allow theories to store additional information in the
      representative. This information can be used when two classes are
      merged, to detect conflicts and solve equations à la Shostak.
  *)
  module N : sig
    type t

    val term : t -> term
    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t Fmt.printer

    val is_root : t -> bool
    (** Is the node a root (ie the representative of its class)? *)

    val iter_class : t -> t Iter.t
    (** Traverse the congruence class.
        Precondition: [is_root n] (see {!find} below) *)
  end

  module Expl : sig
    type t
    val pp : t Fmt.printer

    val mk_merge : N.t -> N.t -> t
    val mk_merge_t : term -> term -> t
    val mk_lit : lit -> t
    val mk_list : t list -> t
  end

  type node = N.t
  (** A node of the congruence closure *)

  type repr = N.t
  (** Node that is currently a representative *)

  type explanation = Expl.t

  type conflict = lit list

  (** Accessors *)

  val term_state : t -> term_state

  val find : t -> node -> repr
  (** Current representative *)

  val add_term : t -> term -> node
  (** Add the term to the congruence closure, if not present already.
      Will be backtracked. *)

  module Theory : sig
    type cc = t

    val raise_conflict : cc -> Expl.t -> unit
    (** Raise a conflict with the given explanation
        it must be a theory tautology that [expl ==> absurd].
        To be used in theories. *)

    val merge : cc -> N.t -> N.t -> Expl.t -> unit
    (** Merge these two nodes given this explanation.
        It must be a theory tautology that [expl ==> n1 = n2].
        To be used in theories. *)

    val add_term : cc -> term -> N.t
    (** Add/retrieve node for this term.
        To be used in theories *)
  end

  type ev_on_merge = t -> N.t -> N.t -> Expl.t -> unit
  type ev_on_new_term = t -> N.t -> term -> unit

  val create :
    ?stat:Stat.t ->
    ?on_merge:ev_on_merge list ->
    ?on_new_term:ev_on_new_term list ->
    ?size:[`Small | `Big] ->
    term_state ->
    t
  (** Create a new congruence closure. *)

  (* TODO: remove? this is managed by the solver anyway? *)
  val on_merge : t -> ev_on_merge -> unit
  (** Add a function to be called when two classes are merged *)

  val on_new_term : t -> ev_on_new_term -> unit
  (** Add a function to be called when a new node is created *)

  val set_as_lit : t -> N.t -> lit -> unit
  (** map the given node to a literal. *)

  val find_t : t -> term -> repr
  (** Current representative of the term.
      @raise Not_found if the term is not already {!add}-ed. *)

  val add_seq : t -> term Iter.t -> unit
  (** Add a sequence of terms to the congruence closure *)

  val all_classes : t -> repr Iter.t
  (** All current classes. This is costly, only use if there is no other solution *)

  val assert_lit : t -> lit -> unit
  (** Given a literal, assume it in the congruence closure and propagate
      its consequences. Will be backtracked.
  
      Useful for the theory combination or the SAT solver's functor *)

  val assert_lits : t -> lit Iter.t -> unit
  (** Addition of many literals *)

  val assert_eq : t -> term -> term -> lit list -> unit
  (** merge the given terms with some explanations *)

  (* TODO: remove and move into its own library as a micro theory
  val assert_distinct : t -> term list -> neq:term -> lit -> unit
  (** [assert_distinct l ~neq:u e] asserts all elements of [l] are distinct
      because [lit] is true
      precond: [u = distinct l] *)
     *)

  val check : t -> actions -> unit
  (** Perform all pending operations done via {!assert_eq}, {!assert_lit}, etc.
      Will use the {!actions} to propagate literals, declare conflicts, etc. *)

  val push_level : t -> unit
  (** Push backtracking level *)

  val pop_levels : t -> int -> unit
  (** Restore to state [n] calls to [push_level] earlier. Used during backtracking. *)

  val get_model : t -> N.t Iter.t Iter.t
  (** get all the equivalence classes so they can be merged in the model *)

  (**/**)
  module Debug_ : sig
    val check_invariants : t -> unit
    val pp : t Fmt.printer
  end
  (**/**)
end

type ('model, 'proof, 'ucore, 'unknown) solver_res =
  | Sat of 'model
  | Unsat of {
      proof: 'proof option;
      unsat_core: 'ucore;
    }
  | Unknown of 'unknown

(** A view of the solver from a theory's point of view *)
module type SOLVER_INTERNAL = sig
  module A : CORE_TYPES
  module CC : CC_S with module A=A
  module CC_A = CC.CC_A

  type ty = A.Ty.t
  type lit = A.Lit.t
  type term = A.Term.t
  type term_state = A.Term.state
  type lemma = A.Lemma.t

  (** {3 Main type for a solver} *)
  type t
  type solver = t

  (**/**)
  module Debug_ : sig
    val on_check_invariants : t -> (unit -> unit) -> unit
    val check_model : t -> unit
  end
  (**/**)

  module Expl = CC.Expl
  module N = CC.N

  (** Unsatisfiable conjunction.
      Its negation will become a conflict clause *)
  type conflict = lit list

  (** {3 Storage of theory-specific data in the CC}

      Theories can create keys to store data in each representative of the
      congruence closure. The data will be automatically merged
      when classes are merged.

      A callback must be provided, called before merging two classes
      containing this data, to check consistency of the theory.
  *)
  module Key : sig
    type 'a t

    type 'a data = (module MERGE_PP with type t = 'a)

    val create : 'a data -> 'a t
    (** Create a key for storing and accessing data of type ['a].
        Values have to be mergeable. *)
  end

  (** {3 Actions available to theories} *)

  val tst : t -> term_state

  val cc : t -> CC.t
  (** Congruence closure for this solver *)

  val raise_conflict: t -> conflict -> 'a
  (** Give a conflict clause to the solver *)

  val propagate: t -> lit -> (unit -> lit list) -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val propagate_l: t -> lit -> lit list -> unit
  (** Propagate a boolean using a unit clause.
      [expl => lit] must be a theory lemma, that is, a T-tautology *)

  val mk_lit : t -> ?sign:bool -> term -> lit
  (** Create a literal *)

  val add_lit : t -> lit -> unit
  (** Add the given literal to the SAT solver, so it gets assigned
      a boolean value *)

  val add_lit_t : t -> ?sign:bool -> term -> unit
  (** Add the given (signed) bool term to the SAT solver, so it gets assigned
      a boolean value *)

  val add_local_axiom: t -> lit list -> unit
  (** Add local clause to the SAT solver. This clause will be
      removed when the solver backtracks. *)

  val add_persistent_axiom: t -> lit list -> unit
  (** Add toplevel clause to the SAT solver. This clause will
      not be backtracked. *)

  val raise_conflict : t -> Expl.t -> 'a
  (** Raise a conflict with the given explanation
      it must be a theory tautology that [expl ==> absurd].
      To be used in theories. *)

  val cc_find : t -> N.t -> N.t
  (** Find representative of the node *)

  val cc_merge : t -> N.t -> N.t -> Expl.t -> unit
  (** Merge these two nodes in the congruence closure, given this explanation.
      It must be a theory tautology that [expl ==> n1 = n2].
      To be used in theories. *)

  val cc_add_term : t -> term -> N.t
  (** Add/retrieve congruence closure node for this term.
      To be used in theories *)

  val cc_data : t -> k:'a Key.t -> N.t -> 'a option
  (** Theory specific data for the given node *)

  val cc_add_data : t -> k:'a Key.t -> N.t -> 'a -> unit
  (** Add data for this node. This might trigger a conflict if the class
      already contains data that is not compatible. *)

  val cc_merge_t : t -> term -> term -> Expl.t -> unit
  (** Merge these two terms in the congruence closure, given this explanation.
      See {!cc_merge} *)

  val on_cc_merge :
    t ->
    k:'a Key.t ->
    (t -> N.t -> 'a -> N.t -> 'a -> Expl.t -> unit) ->
    unit
  (** Callback for when two classes containing data for this key are merged *)

  val on_cc_merge_all : t -> (t -> N.t -> N.t -> Expl.t -> unit) -> unit
  (** Callback for when any two classes are merged *)

  val on_cc_new_term :
    t ->
    k:'a Key.t ->
    (t -> N.t -> term -> 'a option) ->
    unit
  (** Callback to add data on terms when they are added to the congruence
      closure *)

  val on_partial_check : t -> (t -> lit Iter.t -> unit) -> unit
  (** Register callbacked to be called with the slice of literals
      newly added on the trail.

      This is called very often and should be efficient. It doesn't have
      to be complete, only correct. It's given only the slice of
      the trail consisting in new literals. *)

  val on_final_check: t -> (t -> lit Iter.t -> unit) -> unit
  (** Register callback to be called during the final check.

      Must be complete (i.e. must raise a conflict if the set of literals is
      not satisfiable) and can be expensive. The function
      is given the whole trail. *)
end

(** Public view of the solver *)
module type SOLVER = sig
  module A : CORE_TYPES
  module Solver_internal : SOLVER_INTERNAL with module A = A
  (** Internal solver, available to theories.  *)

  type t
  type solver = t
  type term = A.Term.t
  type ty = A.Ty.t
  type lit = A.Lit.t
  type lemma = A.Lemma.t
  type value = A.Value.t

  (** {3 A theory}


      Theories are abstracted over the concrete implementation of the solver,
      so they can work with any implementation.

      Typically a theory should be a functor taking an argument containing
      a [SOLVER_INTERNAL] and some additional views on terms, literals, etc.
      that are specific to the theory (e.g. to map terms to linear
      expressions).
      The theory can then be instantiated on any kind of solver for any
      term representation that also satisfies the additional theory-specific
      requirements. Instantiated theories (ie values of type {!SOLVER.theory})
      can be added to the solver.
  *)
  module type THEORY = sig
    type t
    (** The theory's state *)

    val name : string
    (** Name of the theory *)

    val create_and_setup : Solver_internal.t -> t
    (** Instantiate the theory's state for the given (internal) solver,
        register callbacks, create keys, etc. *)

    val push_level : t -> unit
    (** Push backtracking level *)

    val pop_levels : t -> int -> unit
    (** Pop backtracking levels, restoring the theory to its former state *)
  end

  type theory = (module THEORY)
  (** A theory that can be used for this particular solver. *)

  val mk_theory :
    name:string ->
    create_and_setup:(Solver_internal.t -> 'th) ->
    ?push_level:('th -> unit) ->
    ?pop_levels:('th -> int -> unit) ->
    unit ->
    theory
  (** Helper to create a theory *)

  (** {3 Boolean Atoms} *)
  module Atom : sig
    type t

    val equal : t -> t -> bool
    val hash : t -> int
    val pp : t CCFormat.printer
  end

  module Model : sig
    type t

    val empty : t

    val mem : term -> t -> bool

    val find : term -> t -> value option

    val eval : t -> term -> value option

    val pp : t Fmt.printer
  end

  module Unknown : sig
    type t
    val pp : t CCFormat.printer

    (*
    type unknown =
      | U_timeout
      | U_incomplete
       *)
  end

  module Proof : sig
    type t
    (* TODO: expose more? *)

  end

  type proof = Proof.t

  (** {3 Main API} *)

  val stats : t -> Stat.t

  val create :
    ?stat:Stat.t ->
    ?size:[`Big | `Tiny | `Small] ->
    (* TODO? ?config:Config.t -> *)
    ?store_proof:bool ->
    theories:theory list ->
    A.Term.state ->
    unit ->
    t
  (** Create a new solver.
      @param theories theories to load from the start. *)

  val add_theory : t -> theory -> unit
  (** Add a theory to the solver. This should be called before
      any call to {!solve} or to {!add_clause} and the likes (otherwise
      the theory will have a partial view of the problem). *)

  val mk_atom_lit : t -> lit -> Atom.t

  val mk_atom_t : t -> ?sign:bool -> term -> Atom.t

  val add_clause_lits : t -> lit IArray.t -> unit

  val add_clause_lits_l : t -> lit list -> unit

  val add_clause : t -> Atom.t IArray.t -> unit

  val add_clause_l : t -> Atom.t list -> unit

  type res = (Model.t, proof, lit IArray.t, Unknown.t) solver_res
  (** Result of solving for the current set of clauses *)

  val solve :
    ?on_exit:(unit -> unit) list ->
    ?check:bool ->
    assumptions:Atom.t list ->
    t ->
    res
  (** [solve s] checks the satisfiability of the statement added so far to [s]
      @param check if true, the model is checked before returning
      @param assumptions a set of atoms held to be true. The unsat core,
        if any, will be a subset of [assumptions].
      @param on_exit functions to be run before this returns *)

  val pp_term_graph: t CCFormat.printer
  val pp_stats : t CCFormat.printer
end