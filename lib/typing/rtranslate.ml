open Hflmc2_syntax

module Rtype = Rtype
module Rhflz = Rhflz

let id_source = ref 0

let generate_id () = id_source := !id_source + 1; !id_source
let generate_template () = (generate_id (), [])

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

let rec translate_body body ty =
  let open Rhflz in
  match body with 
  | Hflz.Var id -> Var ({id with Id.ty=ty})
  | Hflz.Abs (arg, body) ->
    begin
      match ty with
      | RArrow(arg_ty, ty') ->
        Abs({arg with Id.ty=arg_ty}, translate_body body ty')
      | _ -> failwith "translate_body"
    end
  | Hflz.Or(x, y) -> Or(translate_body x ty, translate_body y ty)
  | Hflz.And(x, y) -> And(translate_body x ty, translate_body y ty)
  | Hflz.App(x, y) -> App(translate_body x ty, translate_body y ty)
  | Hflz.Bool x -> Bool x
  | Hflz.Arith x -> Arith x
  | Hflz.Pred (x, y) -> Pred (x, y)

let rec collect_id_from_type accum = function
  | Rtype.RArrow(x, y) -> 
    collect_id_from_type (collect_id_from_type accum y) x
  | Rtype.RInt(RId(id)) -> 
    id::accum
  | _ -> accum

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

let rec add_args_to_pred (args: Arith.t list): Rtype.t -> Rtype.t= 
  let open Rtype in
  function 
  | RArrow(x, y) -> 
    RArrow (add_args_to_pred args x, add_args_to_pred args y)
  | RBool(RTemplate(id, _)) -> RBool(RTemplate(id, args))
  | RInt x -> RInt x
  | _ -> failwith "add_args_to_pred"

let translate_rule
  (formula: Type.simple_ty Hflz.hes_rule)
  : Rhflz.hes_rule
  =  
  let var = translate_id formula.var in
  let body = translate_body formula.body var.ty in
  let ids = collect_id var in
  let var = {var with Id.ty=add_args_to_pred ids var.ty} in
  {Rhflz.var=var; Rhflz.fix=formula.fix; Rhflz.body = body}

let rec translate_hes = function
  | [] -> []
  | x::xs -> (translate_rule x) :: (translate_hes xs)

let translate = translate_hes