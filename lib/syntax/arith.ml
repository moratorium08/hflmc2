open Hflmc2_util

type op =
  | Add
  | Sub
  | Mult
  [@@deriving eq,ord,show,iter,map,fold,sexp]

(* arithmetic expresion parametrized by variable type *)
type 'var gen_t =
  | Int of int
  | Var of 'var
  | Op  of op * 'var gen_t list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type t = [`Int] Id.t gen_t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_int n     = Int(n)
let mk_op op as' = Op(op,as')
let mk_var' v    = Var v
(* specific to [t] *)
let mk_var v : t = Var({v with ty = `Int})

let rec fvs : 'var gen_t -> 'var list = function
  | Int _ -> []
  | Var v -> [v]
  | Op (_, as') -> List.concat_map as' ~f:fvs
