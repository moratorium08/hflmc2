open Hflmc2_syntax

type id = int
type template = id * id list (* template prdicate name and its args *)

type arg 
  = RInt of id
  | RSigma of sigma
and sigma 
  = RBool of template
  | RArrow of arg * sigma

type t = sigma

let id_source = ref 0

let generate_id () = id_source := !id_source + 1; !id_source
let generate_template () = (generate_id (), [])

(* ここらへんきれいに実装できるのかな *)
(* 型によってdispatchする関数を変えるようにする的な *)
let rec translate_id (id: 'a Type.ty Id.t) : (t Id.t) = { id with Id.ty = translate_simple_ty id.ty }
and translate_id_arg (id: 'a Type.ty Type.arg Id.t): (arg Id.t) = { id with Id.ty = translate_simple_arg id.ty }
and translate_simple_arg = function 
  | Type.TyInt -> RInt (generate_id ())
  | Type.TySigma t -> RSigma (translate_simple_ty t)
and translate_simple_ty:'a Type.ty -> t = function 
  (* should handle annotation? *)
  | Type.TyBool _ -> RBool (generate_template ()) 
  | Type.TyArrow (a, s) -> 
    RArrow(translate_id_arg a, translate_simple_ty s)


let rec translate_body body =
  let open Hflz in
  match body with 
  | Var id -> Var (translate_id id)
  | Abs (arg, body) ->
    Abs(translate_simple_id_arg arg, translate_body body)
  | Or(x, y) -> Or(translate_body x, translate_body y)
  | And(x, y) -> And(translate_body x, translate_body y)
  | App(x, y) -> App(translate_body x, translate_body y)
  | x -> x

let rec translate_body hes_rule
  formula: Type.simple_ty Hflz.hes_rule
  -> t Hflz.hes_rule
  =  
  let body = translate_body formula.body in
  {formula with body = body}