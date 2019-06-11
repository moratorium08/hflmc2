open Hflmc2_util
open Id

type pred =
  | Eq
  (* | Neq *)
  | Le
  | Ge
  | Lt
  | Gt
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type t
  = Bool of bool
  | Var  of unit Id.t (* unitが気持ち悪いなあ *)
  | Or   of t * t
  | And  of t * t
  | Pred of pred * Arith.t list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_var x = Var (Id.remove_ty x)

let mk_and a b = And(a,b)

let mk_ands = function
  | [] -> Bool true
  | x::xs -> List.fold_left xs ~init:x ~f:mk_and

let mk_or a b = Or(a,b)

let mk_ors = function
  | [] -> Bool false
  | x::xs -> List.fold_left xs ~init:x ~f:mk_or

(* let mk_implies (a, b) =  *)

