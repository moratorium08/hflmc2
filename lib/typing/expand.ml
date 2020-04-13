open Chc_solver
open Rhflz
open Rtype
open Rid
open Hflmc2_syntax

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
  let count_rule map rule = 
    let id, _ = Rtype.get_top rule.var.ty in
    List.length @@ (match M.find_opt id map with Some(l) -> l | None -> [])
  in
  let rec subst_rules fml var rules = 
    let rec inner fml' = match fml' with
      | Var(x) when Id.eq x var -> fml
      | Or(x, y, a, b) -> Or(inner x, inner y, a, b)
      | And(x, y, a, b) -> And(inner x, inner y, a, b)
      | Forall(x, t, s) -> Forall(x, inner t, s)
      | App(x, y, t) -> App(inner x, inner y, t)
      | Abs(x, y) -> Abs(x, inner y)
      | x -> x
    in
    match rules with
    | [] -> []
    | rule::rules when rule.var = var -> 
      {rule with body=fml}::subst_rules fml var rules
    | rule::rules -> 
      Printf.printf "- %s%d " rule.var.name rule.var.id;
      {rule with body=inner rule.body}::subst_rules fml var rules
  in
  let rec expand_rule iters rules = match iters with
    | [] -> rules
    | rule::xs -> 
      let expand_cnt = count_rule map rule in
      Printf.printf "%s%d %d" rule.var.name rule.var.id expand_cnt;
      let fml = expand_nu_formula expand_cnt rule in
      let rules' = subst_rules fml rule.var rules in
      print_newline ();
      expand_rule xs rules'
  in
  expand_rule hes hes

