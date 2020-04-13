open Hflmc2_syntax

open Rtype
module Rhflz = Rhflz

(* ここらへんきれいに実装できるのかな *)
(* 型によってdispatchする関数を変えるようにする的な *)
let rec translate_id id = { id with Id.ty = translate_simple_ty [] Id.(id.ty) }
and translate_id_arg env id = 
  let (ty, env) = translate_simple_arg env id in
  { id with Id.ty = ty}, env
and translate_simple_ty env = 
  let open Rtype in
  function 
  (* should handle annotation? *)
  | Type.TyBool _ -> 
    RBool (RTemplate(generate_template env))
  | Type.TyArrow (a, s) -> 
    let (ty, env) = translate_simple_arg env a in
    RArrow(ty, translate_simple_ty env s)
and translate_simple_arg env id = match id.ty with
  | Type.TyInt -> 
    let id = {id with Id.ty = `Int} in
    RInt (RId(id)), id::env
  | Type.TySigma t -> 
    translate_simple_ty env t, env

let rec translate_body env body =
  let open Rhflz in
  match body with 
  | Hflz.Var id -> Var (translate_id id)
  | Hflz.Abs (arg, body) ->
    let (id, env) = translate_id_arg env arg in
    Abs(id, translate_body env body)
  | Hflz.Forall (arg, body) ->
    let (id, env') = translate_id_arg env arg in
    let id = {id with ty=Rtype.to_bottom id.ty} in
    let template = generate_template env in
    Forall(id, translate_body env' body, template)
  | Hflz.Or(x, y) -> 
    let t1 = generate_template env in
    let t2 = generate_template env in
    Or(translate_body env x, translate_body env y, t1, t2)
  | Hflz.And(x, y) -> 
    let t1 = generate_template env in
    let t2 = generate_template env in
    And(translate_body env x, translate_body env y, t1, t2)
  | Hflz.App(x, y) -> 
    let template = generate_template env in
    App(translate_body env x, translate_body env y, template)
  | Hflz.Bool x -> Bool x
  | Hflz.Arith x -> Arith x
  | Hflz.Pred (x, y) -> Pred (x, y)
  
let translate_rule
  (formula: Type.simple_ty Hflz.hes_rule)
  : Rhflz.hes_rule
  =  
  let var = translate_id formula.var 
  in
  let body = translate_body [] formula.body in
  let var = {var with Id.ty=var.ty} in
  {Rhflz.var=var; Rhflz.fix=formula.fix; Rhflz.body = body}


let rec translate_hes = function
  | [] -> []
  | x::xs -> 
    let open Hflz in
    translate_rule x::translate_hes xs

let translate = translate_hes