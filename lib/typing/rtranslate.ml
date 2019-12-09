open Hflmc2_syntax

module Rtype = Rtype
module Rhflz = Rhflz

let id_source = ref 0
let id_top = 0
let created = ref false

let generate_id () = id_source := !id_source + 1; !id_source
let generate_template () = (generate_id (), [])
let generate_top_template () = 
  if !created then
    failwith "You attempted to create top template twice"
  else
    created := true;
    (id_top, [])

let rec add_args_to_pred (args: Arith.t list): Rtype.t -> Rtype.t= 
  let open Rtype in
  function 
  | RArrow(x, y) -> 
    RArrow (add_args_to_pred args x, add_args_to_pred args y)
  | RBool(RTemplate(id, _)) -> RBool(RTemplate(id, args))
  | RInt x -> RInt x
  | _ -> failwith "add_args_to_pred"

(* ここらへんきれいに実装できるのかな *)
(* 型によってdispatchする関数を変えるようにする的な *)
let rec translate_id (id: 'a Type.ty Id.t) : (Rtype.t Id.t) = { id with Id.ty = translate_simple_ty id.ty }
and translate_id_arg (id: 'a Type.ty Type.arg Id.t): (Rtype.t Id.t) = { id with Id.ty = translate_simple_arg id }
and _translate_simple_arg = function 
  | Type.TyInt -> Rtype.RInt (RId(Id.gen `Int))
  | Type.TySigma t -> (translate_simple_ty t)
and translate_simple_ty:'a Type.ty -> Rtype.t = function 
  (* should handle annotation? *)
  | Type.TyBool _ -> RBool (RTemplate(generate_template ()))
  | Type.TyArrow (a, s) -> 
    RArrow((translate_id_arg a).ty, translate_simple_ty s)
and translate_simple_arg id = match id.ty with
  | Type.TyInt -> RInt (RId({id with Id.ty = `Int}))
  | Type.TySigma t -> (translate_simple_ty t)

let rec collect_id_from_type accum = function
  | Rtype.RArrow(x, y) -> 
    collect_id_from_type (collect_id_from_type accum y) x
  | Rtype.RInt(RId(id)) -> 
    id::accum
  | _ -> accum

let translate_top_id (id: 'a Type.ty Id.t) : (Rtype.t Id.t) = 
  let rec replace_return_template ty = match ty with
    | Rtype.RBool _ -> Rtype.RBool(RTemplate(generate_top_template ()))
    | Rtype.RArrow(a, s) -> Rtype.RArrow(a, replace_return_template s)
    | _ -> failwith "program error" (* should not occur int *)
  in
  let id = translate_id id in
  {id with Id.ty=replace_return_template id.ty}

let rec translate_body body =
  let open Rhflz in
  match body with 
  | Hflz.Var id -> Var (translate_id id)
  | Hflz.Abs (arg, body) ->
    Abs(translate_id_arg arg, translate_body body)
  | Hflz.Or(x, y) -> Or(translate_body x, translate_body y)
  | Hflz.And(x, y) -> And(translate_body x, translate_body y)
  | Hflz.App(x, y) -> App(translate_body x, translate_body y)
  | Hflz.Bool x -> Bool x
  | Hflz.Arith x -> Arith x
  | Hflz.Pred (x, y) -> Pred (x, y)

let rec collect_id_from_body (body: Rhflz.t): [`Int] Id.t list =
  let open Rhflz in
  let open Rtype in
  match body with 
  | Var _ -> []
  | Abs (arg, body) ->
    let ids = collect_id_from_type [] arg.ty in
    ids @ collect_id_from_body body
  | Or(x, y) | And(x, y) | App(x, y) ->
     collect_id_from_body x @ collect_id_from_body y
  | _ -> []

let rec update_body_with_ids body ids =
  let open Rhflz in
  match body with 
  | Abs (arg, body) ->
    Abs({arg with Id.ty=add_args_to_pred ids arg.ty}, update_body_with_ids body ids)
  | Or(x, y) -> Or(update_body_with_ids x ids, update_body_with_ids y ids)
  | And(x, y) -> And(update_body_with_ids x ids, update_body_with_ids y ids)
  | App(x, y) -> App(update_body_with_ids x ids,  update_body_with_ids y ids)
  | x -> x
(*
let rec collect_id_from_formula accum = 
  let open Rhflz in function
  | Abs(id, body) -> 
    collect_id_from_formula (collect_id_from_type accum id.ty) body
  | Or(x, y) | And(x, y) | App(x, y)  -> 
    collect_id_from_formula (collect_id_from_formula accum x) y
  | _ -> accum
*)
let collect_id (var: Rtype.t Id.t): Arith.t list = 
  collect_id_from_type [] var.ty |> List.map (fun x -> Arith.Var x)

let translate_rule
  ?(top=false)
  (formula: Type.simple_ty Hflz.hes_rule)
  : Rhflz.hes_rule
  =  
  let var = 
  if top then
    translate_top_id formula.var 
  else
    translate_id formula.var 
  in
  let ids = collect_id var in
  let body = translate_body formula.body in
  let ids' = List.map (fun x -> Arith.Var x) (collect_id_from_body body) in
  let body' = update_body_with_ids body ids' in
  let var = {var with Id.ty=add_args_to_pred ids var.ty} in
  {Rhflz.var=var; Rhflz.fix=formula.fix; Rhflz.body = body'}

let rec get_top = function
  | Rtype.RBool(RTemplate(x)) -> x
  | Rtype.RArrow(_, s) -> get_top s
  | _ -> failwith "program error" (* should not occur int *)

let rec translate_hes = function
  | [] -> ([], None)
  | x::xs -> 
    let open Hflz in
    let flag = x.var.name = "S" in
    let (l, y) = translate_hes xs in
    let rule = translate_rule x ~top:flag in
    let y = 
      if flag then 
        let open Rhflz in
        Some(get_top rule.var.ty)
      else 
        y
    in
    (rule :: l, y)

let translate = translate_hes