
(* pure SAT solver *)

module E = CCResult
module SS = Sidekick_sat

module Arg = struct
  module Formula = struct
    type t = int
    let norm t = if t>0 then t, SS.Same_sign else -t, SS.Negated
    let abs = abs
    let sign t = t>0
    let equal = CCInt.equal
    let hash = CCHash.int
    let neg x = -x
    let pp = Fmt.int
  end
  type proof=unit
end

module SAT = Sidekick_sat.Make_pure_sat(Arg)

module Dimacs = struct
  open Sidekick_base
  module T = Term

  let parse_file (solver:SAT.t) (file:string) : (unit, string) result =
    let get_lit i : SAT.atom = SAT.make_atom solver i in

    try
      CCIO.with_in file
        (fun ic ->
           let p = Dimacs_parser.create ic in
           Dimacs_parser.iter p
             (fun c ->
                let atoms = List.rev_map get_lit c in
                SAT.add_clause solver atoms ());
           Ok ())
    with e ->
      E.of_exn_trace e
end

let solve ?(check=false) (solver:SAT.t) : (unit, string) result =
  let res =
    Profile.with_ "solve" (fun () -> SAT.solve solver)
  in
  let t2 = Sys.time () in
  Printf.printf "\r"; flush stdout;
  begin match res with
    | SAT.Sat _ ->
      let t3 = Sys.time () -. t2 in
      Format.printf "Sat (%.3f/%.3f)@." t2 t3;
    | SAT.Unsat (module US) ->

      if check then (
        SAT.Proof.check (SAT.store solver) (US.get_proof())
      );

      let t3 = Sys.time () -. t2 in
      Format.printf "Unsat (%.3f/%.3f)@." t2 t3;
  end;
  Ok ()

