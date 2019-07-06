
open Hflmc2_util
open Id
open Type

type t =
  | Bool   of bool
  | Var    of abstracted_ty Id.t
  | Or     of t list * [ `Original | `Inserted ]
  | And    of t list * [ `Original | `Inserted ]
  | Exists of string * t
  | Forall of string * t
  (* | Fix    of abstracted_ty Id.t * t * Fixpoint.t *)
  | Abs    of abstracted_argty Id.t * t
  | App    of t * t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type hes_rule =
  { var  : abstracted_ty Id.t
  ; body : t
  ; fix  : Fixpoint.t
  }
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type hes = hes_rule list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* Construction *)

let mk_var x = Var x

let mk_ands ?(kind=`Original) = function
  | [] -> Bool true
  | [x] -> x
  | xs -> And(xs, kind)

let mk_ors ?(kind=`Original) = function
  | [] -> Bool false
  | [x] -> x
  | xs -> Or(xs, kind)

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

let decompose_app =
  let rec go phi acc = match phi with
    | App(phi,x) -> go phi (x::acc)
    | _ -> (phi, List.rev acc)
  in
  fun phi -> go phi []


