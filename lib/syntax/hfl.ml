
open Hflmc2_util
open Id
open Type

type t =
  | Bool   of bool
  | Var    of abstracted_ty Id.t
  | Or     of t * t
  | And    of t * t
  | Exists of string * t
  | Forall of string * t
  | Fix    of abstracted_ty Id.t * t * Fixpoint.t
  | Abs    of abstracted_argty Id.t * t
  | App    of t * t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_const : 'ty -> t -> t =
  fun ty t ->
    let x = Id.gen ty in
    Abs(x, t)

(* TODO avoid capture
 * 或いはα変換を仮定する
 * *)
let [@warning "-3"] rec subst : t IdMap.t -> t -> t =
  fun map t -> match t with
    | Bool _ -> t
    | Var x ->
        begin match IdMap.lookup map x with
        | t -> t
        | exception Not_found -> Var x
        end
    | Or(t1,t2) -> Or(subst map t1, subst map t2)
    | And(t1,t2) -> And(subst map t1, subst map t2)
    | App(t1,t2) -> App(subst map t1, subst map t2)
    | Exists(label,t) -> Exists(label, subst map t)
    | Forall(label,t) -> Forall(label, subst map t)
    | Fix(x, t, z) -> Fix(x, subst map t, z)
    | Abs(x, t) -> Abs(x, subst map t)

let type_of : t -> Type.abstracted_ty =
  fun _ -> assert false

let identity : abstracted_ty -> t =
  fun ty ->
    let x = Id.gen ty in
    Abs(x, Var x)


