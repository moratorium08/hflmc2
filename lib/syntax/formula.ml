open Hflmc2_util
open Id

type t
  = Bool of bool
  | Var  of unit Id.t (* unitが気持ち悪いなあ *)
  | Or   of t * t
  | And  of t * t
  | Pred of string * Arith.t list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

