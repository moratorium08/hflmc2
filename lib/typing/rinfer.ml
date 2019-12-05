open Rhflz 
open Rtype
open Hflmc2_syntax

type chc = {head: refinement; body: refinement}
(* check whether t <= t' holds *)
let rec rty = function
  | RArrow(RInt(_), t) -> rty t
  | RArrow(_, s) -> rty s
  | RBool(phi) -> phi
  | _ -> failwith "program error"

let rec subtype t t' renv m = match (t, t') with
 | RBool(p), RBool(p') -> 
   {head=RAnd(renv, p'); body=p} :: m
 | RArrow(RInt(_), t), RArrow(RInt(_), t')  ->
   subtype t t' renv m
 | RArrow(t, s), RArrow(t', s') ->
   let m' = subtype t' t (RAnd(renv, rty t')) m in
   subtype s s' renv m' 
 | _, _ -> failwith "program error"
(* And, Or, Appで制約を生成 *)
let rec infer_formula formula env m = match formula with
  | Bool b when b -> (RBool(RTrue), m)
  | Bool _ -> (RBool(RFalse), m)
  | Var id -> (id.ty, [])
  | Abs (arg, body) -> 
    let env' = IdMap.add env arg arg.ty in
    let (body_t, l) = infer_formula body env' m in
    (RArrow(arg.ty, body_t), l)
  | Pred (f, args) -> (RBool(RPred(f, args)), m)
  | Arith x -> (RInt (RArith x), [])
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
    | _ -> failwith "program error"
    end
  | App(x, y) -> 
    let (x', mx) = infer_formula x env m in
    let (y', m') = infer_formula y env mx in
    let (arg, body, tau) = match (x', y') with
      | (RArrow(arg, body), tau) -> (arg, body, tau)
      | _ -> failwith "type is not correct"
    in begin
      let m'' = subtype arg tau RTrue m' in
      (body, m'')
    end