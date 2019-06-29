open Hflmc2_util

type op =
  | Add
  | Sub
  | Mult
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type t =
  | Int of int
  | Var of [`Int] Id.t
  | Op  of op * t list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_int n = Int(n)
let mk_var v = Var({v with ty = `Int})
let mk_op op as' = Op(op,as')
