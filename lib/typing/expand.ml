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
  let expand_forall rule = 
    let rec inner fml = match fml with
      | Or(x, y, a, b) -> Or(inner x, inner y, a, b)
      | And(x, y, a, b) -> And(inner x, inner y, a, b)
      | App(x, y, t) -> App(inner x, inner y, t)
      | Abs(x, y) -> Abs(x, inner y)
      | Forall(x, t, s) -> 
      (* replace forall to finite conjunctions *)
        Forall(x, inner t, s)
      | x -> x
    in
    {rule with body=inner rule.body}
  in
  (* should use Set-like structure. Current implmenetation: O(n) *)
  let rec is_fixpoint x rules = match rules with
    | [] -> None
    | y::ys when Id.eq x y.var -> Some(y)
    | y::ys -> is_fixpoint x ys
  in
  let rec expand_nu_formula expand_cnt rule rules = 
    if expand_cnt <= 0 then
      Rhflz.top_hflz rule.var.ty
    else begin
      (* inline expand_cnt times *)
      let rec inner fml = match fml with
        | Or(x, y, a, b) -> Or(inner x, inner y, a, b)
        | And(x, y, a, b) -> And(inner x, inner y, a, b)
        | Forall(x, t, s) -> Forall(x, inner t, s)
        | App(x, y, t) -> App(inner x, inner y, t)
        | Abs(x, y) -> Abs(x, inner y)
        | Var(x) -> 
          begin match is_fixpoint x rules with 
            | Some(rule) -> expand_nu_formula (expand_cnt - 1) rule rules
            | None -> Var(x)
          end
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
      | Var(x) when Id.eq x var -> 
        fml
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
      {rule with body=inner rule.body}::subst_rules fml var rules
  in
  let rec gen_count_map rules = match rules with
    | [] -> []
    | rule::rules -> (rule.var, count_rule map rule)::gen_count_map rules
  in
  let rec expand_rule iters rules = 
    let count_map = gen_count_map rules in
    match iters with
    | [] -> rules
    | rule::xs -> 
      (* temporal fix *)
      (*let expand_cnt = count_rule map rule in *)
      let expand_cnt = List.fold_left (fun x rule -> x + count_rule map rule) 0 rules in
      let fml = expand_nu_formula expand_cnt rule rules in
      let rules' = subst_rules fml rule.var rules in
      expand_rule xs rules'
  in
  expand_rule hes hes

