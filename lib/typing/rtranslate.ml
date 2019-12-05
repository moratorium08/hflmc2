open Hflmc2_syntax

module Rtype = Rtype
module Rhflz = Rhflz

let id_source = ref 0

let generate_id () = id_source := !id_source + 1; !id_source
let generate_template () = (generate_id (), [])

(* ここらへんきれいに実装できるのかな *)
(* 型によってdispatchする関数を変えるようにする的な *)
let rec translate_id (id: 'a Type.ty Id.t) : (Rtype.t Id.t) = { id with Id.ty = translate_simple_ty id.ty }
and translate_id_arg (id: 'a Type.ty Type.arg Id.t): (Rtype.t Id.t) = { id with Id.ty = translate_simple_arg id.ty }
and translate_simple_arg = function 
  | Type.TyInt -> RInt (RId(generate_id ()))
  | Type.TySigma t -> (translate_simple_ty t)
and translate_simple_ty:'a Type.ty -> Rtype.t = function 
  (* should handle annotation? *)
  | Type.TyBool _ -> RBool (RTemplate(generate_template ()))
  | Type.TyArrow (a, s) -> 
    RArrow((translate_id_arg a).ty, translate_simple_ty s)

let rec translate_arith = function
  | Arith.Int x -> RArith.Int x

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

let translate_rule
  (formula: Type.simple_ty Hflz.hes_rule)
  : Rhflz.hes_rule
  =  
  let body = translate_body formula.body in
  {Rhflz.var=translate_id formula.var; Rhflz.fix=formula.fix; Rhflz.body = body}

let rec translate_hes = function
  | [] -> []
  | x::xs -> (translate_rule x) :: (translate_hes xs)

let translate = translate_hes