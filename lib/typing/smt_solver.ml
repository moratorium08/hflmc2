open Fpl
open Smt2

type solver = [`Z3]
let name_of_solver = function
  | `Z3 -> "z3"

let selected_cmd = function
  | `Z3 -> [|"z3" |]

let get_epilogue = function
  | `Z3 -> "\n(check-sat)\n"

let gen_assert solver fml = 
  let fpl_smt = fpl2smt2 fml in
  Printf.sprintf "(assert %s)" fpl_smt 

let fpl2smt2 = gen_assert

let save_fpl_to_smt2 solver fpl =
    let smt2 = fpl2smt2 solver fpl in
    Random.self_init ();
    let r = Random.int 0x10000000 in
    let file = Printf.sprintf "/tmp/%s-%d.smt2" (name_of_solver solver) r in
    let oc = open_out file in
    Printf.fprintf oc "%s" smt2;
    close_out oc;
    file

let check_sat_fpl ?(timeout=100000.0) solver fpl = 
  let open Hflmc2_util in
  let file = save_fpl_to_smt2 solver fpl in
  let cmd = selected_cmd solver in
  let _, out, _ = Fn.run_command ~timeout:timeout (Array.concat [cmd; [|file|]]) in
  match String.lsplit2 out ~on:'\n' with
  | Some ("unsat", _) -> `Unsat
  | Some ("sat", _) -> `Sat
  | Some ("unknown", _) -> `Unknown
  | _ -> failwith "failed to handle smt solver result"