open Rhflz 
open Rtype
open Hflmc2_syntax

type chc = {head: refinement; body: refinement}
let print_chc chc = 
  print_refinement chc.body;
  Printf.printf " => ";
  print_refinement chc.head

let rec print_constraints = function
  | [] -> ()
  | x::xs -> print_chc x; print_newline(); print_constraints xs


(* check whether t <= t' holds *)
let rec rty = function
  | RArrow(RInt(_), t) -> rty t
  | RArrow(_, s) -> rty s
  | RBool(phi) -> phi
  | _ -> failwith "program error(rty)"

let rec _subtype t t' renv m = 
  match (t, t') with
 | RBool(p), RBool(p') -> 
  (*print_rtype t;
  Printf.printf "=";
  print_rtype t';
  print_newline ();*)
   {head=RAnd(renv, p'); body=p} :: m
 | RArrow(RInt(_), t), RArrow(RInt(_), t')  ->
   _subtype t t' renv m
 | RArrow(t, s), RArrow(t', s') ->
   let m' = _subtype t' t (RAnd(renv, rty t')) m in
   _subtype s s' renv m' 
 | _, _ -> 
 failwith "program error(subtype)"

let subtype t t' m = _subtype t t' RTrue m

let rec subst_pred id rint (_, l) = match rint with 
  | RId id' -> 
    List.map (Trans.Subst.Arith.arith id (Arith.Var(id'))) l
  | RArith a ->
    List.map (Trans.Subst.Arith.arith id a) l

let rec subst_refinement id rint = function
  | RPred (p, l) -> RPred(p, subst_pred id rint (p, l))
  | RAnd(x, y) -> RAnd(subst_refinement id rint x, subst_refinement id rint y)
  | ROr(x, y) -> ROr(subst_refinement id rint x, subst_refinement id rint y)
  | RTemplate(id, l) -> RTemplate(id, (id, rint) ::l)
  | x -> x

let rec subst id rint = function
  | RBool r -> RBool(subst_refinement id rint r)
  | RArrow(x, y) -> RArrow(subst id rint x, subst id rint y)
  | RInt x -> RInt x

(* And, Or, Appで制約を生成 *)
let rec infer_formula formula env m = 
  (*print_formula formula;
  print_newline ();*)
  match formula with
  | Bool b when b -> (RBool(RTrue), m)
  | Bool _ -> (RBool(RFalse), m)
  | Var id -> 
    begin
    match IdMap.find env id with
    | Some(t) -> (t, m)
    | None -> failwith "no var(infer_formula)"
    end
  | Abs (arg, body) -> 
    let env' = IdMap.add env arg arg.ty in
    let (body_t, l) = infer_formula body env' m in
    (RArrow(arg.ty, body_t), l)
  | Pred (f, args) -> (RBool(RPred(f, args)), m)
  | Arith x -> (RInt (RArith x), m)
  | Or (x, y) | And (x, y) -> 
    let (x', mx) = infer_formula x env m in
    let (y', m') = infer_formula y env mx in
    let (rx, ry) = match (x', y') with
      | (RBool(rx), RBool(ry)) -> (rx, ry)
      | _ -> failwith "type is not correct"
    in begin
    match formula with 
    | Or _ -> (RBool(ROr(rx, ry)), m')
    | And _ -> (RBool(RAnd(rx, ry)), m')
    | _ -> failwith "program error(1)"
    end
  | App(x, y) -> 
    let (x', mx) = infer_formula x env m in
    let (y', m') = infer_formula y env mx in
    let (arg, body, tau) = match (x', y') with
      | (RArrow(arg, body), tau) -> (arg, body, tau)
      | _ -> failwith "type is not correct"
    in begin
      (*
      match (arg, tau) with
       | RInt(RId(id)), RInt m -> 
         (subst body id tau
      *)
      let m'' = subtype arg tau m' in
      (body, m'')
    end
  
let infer_rule (rule: hes_rule) env (chcs: chc list): chc list = 
  print_string "uo\n";
  print_constraints chcs;
  print_string "hoge\n";
  let (t, m) = infer_formula rule.body env chcs in
  print_string "piyo\n";
  print_constraints m;
  print_string "nyan\n";
  (*print_rtype rule.var.ty;
  print_newline ();
  print_rtype t;
  print_newline ();*)
  subtype t rule.var.ty m 
 
let rec infer_hes (hes: hes) env (accum: chc list): chc list = match hes with
  | [] -> accum
  | rule::xs -> 
    let accum' = infer_rule rule env accum in
    infer_hes xs env accum'

let infer hes env = 
  let constraints = infer_hes hes env [] in
  print_constraints constraints