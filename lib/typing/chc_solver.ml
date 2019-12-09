open Hflmc2_syntax
open Hflmc2_options
open Chc
open Rtype

(* set of template *)

let selected_cmd () = 
  let sv = !Typing.solver in
  if sv = "z3" then 
    "z3"
  else if sv = "hoice" then 
    "hoice"
  else if sv = "fptprover" then
    "fptprover --format smt-lib2"
  else
    failwith "selected solver is not found"

let prologue = "(set-logic HORN)
"

let epilogue = "\
(check-sat)
"

let rec collect_preds chcs m = 
  let rec inner rt m = match rt with 
  | RTemplate (p, l) -> Rid.M.add p (List.length l) m
  | RAnd(x, y) | ROr(x, y) ->
    m |> inner x |> inner y
  | _ -> m
  in
  match chcs with
  | [] -> m
  | chc::chcs ->
    m |> inner chc.body |> inner chc.head |> collect_preds chcs

let collect_vars chc = 
  let collect_from_arith a m =
    let fvs = Arith.fvs a in
    List.fold_left IdSet.add m fvs
  in
  let rec collect_from_ariths ars m = match ars with
    | [] -> m
    | x::xs -> 
      m |> collect_from_arith x |> collect_from_ariths xs
  in
  let rec inner rt m = match rt with
  | RTemplate(_, l) | RPred(_, l) -> 
    collect_from_ariths l m
  | RAnd(x, y) | ROr(x, y) -> 
    m |> inner x |> inner y
  | _ -> m
  in 
  IdSet.empty |> inner chc.head |> inner chc.body

let rec gen_len_args len = 
  if len < 1 then ""
  else if len = 1 then "Int"
  else "Int " ^ gen_len_args (len - 1)

let pred_def (name, len) =
  gen_len_args len |> Printf.sprintf "(declare-fun %s (%s) Bool)\n" (Rid.to_string name)

let var_def id = id |> Id.to_string |> Printf.sprintf "(%s Int)"

let op2smt2 = 
  let open Arith in
  function
  | Add -> "+"
  | Sub -> "-"
  | Mult -> "*"

let pred2smt2 pred args = 
  let open Formula in
  Printf.sprintf 
  begin
    match pred with
    | Eq -> "(= %s)"
    | Neq -> "(not (= %s))"
    | Le -> "(<= %s)"
    | Ge -> "(>= %s)"
    | Lt -> "(< %s)"
    | Gt -> "(> %s)"
  end args

let rec arith2smt2 = 
  let open Arith in
  function 
  | Int x -> Printf.sprintf "%d" x
  | Var id -> Id.to_string id
  | Op (op, l) -> 
    let args = ariths2smt2 l in
    let op_s = op2smt2 op in
    Printf.sprintf "(%s %s)" op_s args
and ariths2smt2 l =
    l |> List.map arith2smt2 |> List.fold_left (fun s x -> s ^ " " ^ x) "" 

let template2smt2 (p, l) =
  let name = Rid.to_string p in
  let args = ariths2smt2 l in
    Printf.sprintf "(%s %s)" name args

let pred2smt2 (p, l) =
  let args = ariths2smt2 l in
  pred2smt2 p args

let rec ref2smt2 rt = match rt with
  | RTrue -> "true"
  | RFalse -> "false"
  | RAnd(x, y) -> Printf.sprintf "(and %s %s)" (ref2smt2 x) (ref2smt2 y)
  | ROr(x, y) -> Printf.sprintf "(or%s %s)" (ref2smt2 x) (ref2smt2 y)
  | RTemplate(p, l) -> template2smt2 (p, l)
  | RPred(p, l) -> pred2smt2(p, l)

let gen_assert chc =
  let vars = collect_vars chc in
  let vars_s = vars |> IdSet.to_list |> List.map var_def |> List.fold_left (^) "" in
  let body = ref2smt2 chc.body in
  let head = ref2smt2 chc.head in
  let s = Printf.sprintf "(=> %s %s)" body head in
  Printf.sprintf "(assert (forall (%s) %s))\n" vars_s s

let chc2smt2 chcs = 
  let preds = collect_preds chcs Rid.M.empty in
  let def = preds |> Rid.M.bindings |> List.map pred_def |> List.fold_left (^) "" in
  let body = chcs |> List.map gen_assert |> List.fold_left (^) "" in
  prologue ^ def ^ body ^ epilogue


let check_sat chcs = 
  let smt2 = chc2smt2 chcs in
  Random.self_init ();
  let r = Random.int 0x10000000 in
  let filename = Printf.sprintf "tmp/%d.smt2" r in
  let out_filename = Printf.sprintf "tmp/%d.out" r in
  let oc = open_out filename in
  Printf.fprintf oc "%s" smt2;
  close_out oc;
  let cmd = selected_cmd () in
  let cmd = Printf.sprintf "%s %s > %s" cmd filename out_filename in
  let _ = Sys.command cmd in
  let ic = open_in out_filename in
  let line = input_line ic in
  close_in ic;
  if line = "sat" then `Sat
  else if line = "unsat" then `Unsat
  else if line = "unknown" then (Printf.printf "%s\n" line; `Unknown)
  else (Printf.printf "%s\n" line; `Fail)
