
open Hflmc2_util
open Id
open Type

type t =
  | Bool   of bool
  | Var    of abstracted_ty Id.t
  | Or     of t * t * [ `Original | `Inserted ]
  | And    of t * t * [ `Original | `Inserted ]
  | Exists of string * t
  | Forall of string * t
  | Fix    of abstracted_ty Id.t * t * Fixpoint.t
  | Abs    of abstracted_argty Id.t * t
  | App    of t * t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* Construction *)

let mk_var x = Var x

let mk_and ?(kind=`Original) a b= And(a,b,kind)

let mk_ands ?(kind=`Original) = function
  | [] -> Bool true
  | x::xs -> List.fold_left xs ~init:x ~f:(mk_and ~kind)

let mk_or ?(kind=`Original) a b = Or(a,b,kind)

let mk_ors ?(kind=`Original) = function
  | [] -> Bool false
  | x::xs -> List.fold_left xs ~init:x ~f:(mk_or ~kind)

let mk_app t1 t2 = App(t1,t2)
let mk_apps t ts = List.fold_left ts ~init:t ~f:mk_app

let mk_abs x t = Abs(x, t)
let mk_abss xs t = List.fold_right xs ~init:t ~f:mk_abs

let mk_const : 'ty -> t -> t =
  fun ty t ->
    let x = Id.gen ty in
    Abs(x, t)

let mk_identity : abstracted_ty -> t =
  fun ty ->
    let x = Id.gen ty in
    Abs(x, Var x)

(* Deconstruct *)

let decompose_lambda =
  let rec go acc phi = match phi with
    | Abs(x,phi) -> go (x::acc) phi
    | _ -> (acc, phi)
  in
  go []



