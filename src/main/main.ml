(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

module E = CCResult
module Fmt = CCFormat
module Term = Sidekick_base.Term
module Solver = Sidekick_smtlib.Solver
module Process = Sidekick_smtlib.Process

open E.Infix

type 'a or_error = ('a, string) E.t

exception Out_of_time
exception Out_of_space

let file = ref ""
let p_cnf = ref false
let p_dot_proof = ref ""
let p_proof = ref false
let p_model = ref false
let check = ref false
let time_limit = ref 300.
let size_limit = ref 1000_000_000.
let restarts = ref true
let gc = ref true
let p_stat = ref false
let p_gc_stat = ref false
let p_progress = ref false
let proof_file = ref ""

let hyps : Term.t list ref = ref []

(* Arguments parsing *)
let int_arg r arg =
  let l = String.length arg in
  let multiplier m =
    let arg1 = String.sub arg 0 (l-1) in
    r := m *. (float_of_string arg1)
  in
  if l = 0 then raise (Arg.Bad "bad numeric argument")
  else
    try
      match arg.[l-1] with
        | 'k' -> multiplier 1e3
        | 'M' -> multiplier 1e6
        | 'G' -> multiplier 1e9
        | 'T' -> multiplier 1e12
        | 's' -> multiplier 1.
        | 'm' -> multiplier 60.
        | 'h' -> multiplier 3600.
        | 'd' -> multiplier 86400.
        | '0'..'9' -> r := float_of_string arg
        | _ -> raise (Arg.Bad "bad numeric argument")
    with Failure _ -> raise (Arg.Bad "bad numeric argument")

let input_file = fun s -> file := s

let usage = "Usage : main [options] <file>"
let argspec = Arg.align [
    "--bt", Arg.Unit (fun () -> Printexc.record_backtrace true), " enable stack traces";
    "--cnf", Arg.Set p_cnf, " prints the cnf used.";
    "--check", Arg.Set check, " build, check and print the proof (if output is set), if unsat";
    "--no-check", Arg.Clear check, " inverse of -check";
    "--gc", Arg.Set gc, " enable garbage collection";
    "--no-gc", Arg.Clear gc, " disable garbage collection";
    "--restarts", Arg.Set restarts, " enable restarts";
    "--no-restarts", Arg.Clear restarts, " disable restarts";
    "--dot", Arg.Set_string p_dot_proof, " if provided, print the dot proof in the given file";
    "--stat", Arg.Set p_stat, " print statistics";
    "--proof", Arg.Set p_proof, " print proof";
    "--no-proof", Arg.Clear p_proof, " do not print proof";
    "-o", Arg.Set_string proof_file, " file into which to output a proof";
    "--model", Arg.Set p_model, " print model";
    "--no-model", Arg.Clear p_model, " do not print model";
    "--gc-stat", Arg.Set p_gc_stat, " outputs statistics about the GC";
    "-p", Arg.Set p_progress, " print progress bar";
    "--no-p", Arg.Clear p_progress, " no progress bar";
    "--size", Arg.String (int_arg size_limit), " <s>[kMGT] sets the size limit for the sat solver";
    "--time", Arg.String (int_arg time_limit), " <t>[smhd] sets the time limit for the sat solver";
    "-t", Arg.String (int_arg time_limit), " short for --time";
    "--version", Arg.Unit (fun () -> Printf.printf "version: %s\n%!" Sidekick_version.version; exit 0), " show version and exit";
    "-d", Arg.Int Log.set_debug, "<lvl> sets the debug verbose level";
    "--debug", Arg.Int Log.set_debug, "<lvl> sets the debug verbose level";
  ] |> List.sort compare

(* Limits alarm *)
let check_limits () =
  let t = Sys.time () in
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let s = float heap_size *. float Sys.word_size /. 8. in
  if t > !time_limit then
    raise Out_of_time
  else if s > !size_limit then
    raise Out_of_space

let main_smt ~dot_proof () : _ result =
  let tst = Term.create ~size:4_096 () in
  let solver =
    let theories =
      (* TODO: probes, to load only required theories *)
      [
        Process.th_bool;
        Process.th_data;
        Process.th_lra;
      ]
    in
    let store_proof = !check || !p_proof || !proof_file <> "" in
    Process.Solver.create ~store_proof ~theories tst () ()
  in
  let proof_file = if !proof_file ="" then None else Some !proof_file in
  if !check then (
    (* might have to check conflicts *)
    Solver.add_theory solver Process.Check_cc.theory;
  );
  begin
    Sidekick_smtlib.parse tst !file
  end
  >>= fun input ->
  (* process statements *)
  let res =
    try
      let hyps = Vec.create() in
      E.fold_l
        (fun () ->
           Process.process_stmt
             ~hyps ~gc:!gc ~restarts:!restarts ~pp_cnf:!p_cnf ?proof_file
             ~time:!time_limit ~memory:!size_limit
             ?dot_proof ~pp_model:!p_model
             ~check:!check ~progress:!p_progress
             solver)
        () input
    with Exit ->
      E.return()
  in
  if !p_stat then (
    Format.printf "%a@." Solver.pp_stats solver;
  );
  res

let main_cnf () : _ result =
  let module S = Pure_sat_solver in
  let n_atoms = ref 0 in
  let solver =
    S.SAT.create
      ~on_new_atom:(fun _ -> incr n_atoms)
      ~size:`Big ()
  in
  S.Dimacs.parse_file solver !file >>= fun () ->
  let r = S.solve solver in
  if !p_stat then (
    Fmt.printf
      "; n-conflicts=%d n-decisions=%d n-propagations=%d \
       n-minimized-away=%d n-atoms=%d@."
      (S.SAT.n_conflicts solver) (S.SAT.n_decisions solver)
      (S.SAT.n_propagations solver) (S.SAT.n_minimized_away solver) !n_atoms;
  );
  r

let main () =

  (* instrumentation and tracing *)
  Sidekick_tef.setup();
  at_exit Sidekick_tef.teardown;
  Sidekick_memtrace.trace_if_requested ~context:"sidekick" ();

  CCFormat.set_color_default true;
  (* Administrative duties *)
  Arg.parse argspec input_file usage;
  if !file = "" then (
    Arg.usage argspec usage;
    exit 2
  );
  let dot_proof = if !p_dot_proof = "" then None else Some !p_dot_proof in
  check := !check || CCOpt.is_some dot_proof; (* dot requires a proof *)
  let al = Gc.create_alarm check_limits in
  Util.setup_gc();
  let is_cnf = Filename.check_suffix !file ".cnf" in
  let res =
    if is_cnf then (
      main_cnf ()
    ) else (
      main_smt ~dot_proof ()
    )
  in
  if !p_gc_stat then (
    Printf.printf "(gc_stats\n%t)\n" Gc.print_stat;
  );
  Gc.delete_alarm al;
  res

let () = match main() with
  | E.Ok () -> ()
  | E.Error msg ->
    Format.printf "@{<Red>Error@}: %s@." msg;
    exit 1
  | exception e ->
    let b = Printexc.get_backtrace () in
    let exit_ n =
      if Printexc.backtrace_status () then (
        Format.fprintf Format.std_formatter "%s@." b
      );
      CCShims_.Stdlib.exit n
    in
    begin match e with
      | Error.Error msg ->
        Format.printf "@{<Red>Error@}: %s@." msg;
        ignore @@ exit_ 1
      | Out_of_time ->
        Format.printf "Timeout@.";
        exit_ 2
      | Out_of_space ->
        Format.printf "Spaceout@.";
        exit_ 3
      | Invalid_argument e ->
        Format.printf "invalid argument:\n%s@." e;
        exit_ 127
      | _ -> raise e
    end

