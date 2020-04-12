open Chc_solver
open Rhflz
open Rtype
open Rid

let gen_map nodes = 
  List.fold_left (fun m x -> 
    match M.find_opt x.name m with
    | Some(l) -> M.add x.name (x::l) m
    | None -> M.add x.name [x] m
  ) M.empty nodes


let expand unsat_proof hes =
  let map = gen_map unsat_proof in
  let rec expand_nu_formula expand_cnt rule = 
    if expand_cnt <= 0 then
      Bool(true)
    else begin
      (* inline expand_cnt times *)
      let rec inner fml = match fml with
        | Or(x, y, a, b) -> Or(inner x, inner y, a, b)
        | And(x, y, a, b) -> And(inner x, inner y, a, b)
        | Forall(x, t, s) -> Forall(x, inner t, s)
        (* recursive `call' of this prediate *)
        | App(x, y, t) -> App(inner x, inner y, t)
        | Abs(x, y) -> Abs(x, inner y)
        | Var(x) when x = rule.var-> expand_nu_formula (expand_cnt - 1) rule 
        | x -> x
      in
      inner rule.body
    end
  in
  let rec extract_result_type ty = 
    match ty with
    | RBool r -> r
    | RArrow (_, x) -> extract_result_type x
    | _ -> failwith "program error(extract_result_type)"
  in
  let count_rule map rule = 
    let result_type = extract_result_type rule.var.ty in
    let id = 
    match result_type with
    | RTemplate(id, _) -> id
    | _ -> failwith "program error(result_type)"
    in
    List.length @@ M.find id map 
  in
  let expand_rule rule = 
    let expand_cnt = count_rule map rule in
    Printf.printf "%s\n" @@ Hflmc2_syntax.Id.to_string rule.var;
    print_int expand_cnt;
    let fml = expand_nu_formula expand_cnt rule in
    {rule with body=fml}
  in
  List.map expand_rule hes
