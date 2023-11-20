open Hflmc2_syntax
open Rtype
open Fpl

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
  | Div -> "/"
  | Mod -> "mod"
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
    if args = "" then
      Printf.sprintf "%s" name 
    else
      Printf.sprintf "(%s %s)" name args

let pred2smt2 (p, l) =
  let args = ariths2smt2 l in
  pred2smt2 p args

let rec ref2smt2 rt = match rt with
  | RTrue -> "true"
  | RFalse -> "false"
  | RAnd(x, y) -> Printf.sprintf "(and %s %s)" (ref2smt2 x) (ref2smt2 y)
  | ROr(x, y) -> Printf.sprintf "(or %s %s)" (ref2smt2 x) (ref2smt2 y)
  | RTemplate(p, l) -> template2smt2 (p, l)
  | RPred(p, l) -> pred2smt2(p, l)

let rec fpl2smt2 fml = 
  let open Fpl in
  match fml with
  | Bool x when x -> "true"
  | Bool x -> "false"
  | Or(x, y) -> Printf.sprintf "(or %s %s)" (fpl2smt2 x) (fpl2smt2 y)
  | And(x, y) -> Printf.sprintf "(and %s %s)" (fpl2smt2 x) (fpl2smt2 y)
  | Forall(x, y) -> 
    Printf.sprintf "(forall ((%s Int)) %s)" (Id.to_string x) (fpl2smt2 y)
  | Pred(p, l) -> pred2smt2(p, l)