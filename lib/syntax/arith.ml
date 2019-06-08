open Hflmc2_util
type t =
  | Int of int
  | Var of unit Id.t
  | Op  of string * t list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_int n = Int(n)
let mk_var v = Var(Id.remove_ty v)
let mk_op op as' = Op(op,as')
