open Hflmc2_util
open Id

type pred =
  | Eq
  | Neq
  | Le
  | Ge
  | Lt
  | Gt
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type t
  = Bool of bool
  | Or   of t * t
  | And  of t * t
  | Pred of pred * Arith.t list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_and a b = And(a,b)

let mk_ands = function
  | [] -> Bool true
  | x::xs -> List.fold_left xs ~init:x ~f:mk_and

let mk_or a b = Or(a,b)

let mk_ors = function
  | [] -> Bool false
  | x::xs -> List.fold_left xs ~init:x ~f:mk_or

let rec mk_not = function
  | Bool b -> Bool (not b)
  | Or (f1,f2) -> And(mk_not f1, mk_not f2)
  | And(f1,f2) -> Or (mk_not f1, mk_not f2)
  | Pred(pred, as') ->
      let pred' = match pred with
        | Eq  -> Neq
        | Neq -> Eq
        | Le  -> Gt
        | Gt  -> Le
        | Lt  -> Ge
        | Ge  -> Lt
      in Pred(pred', as')

let mk_implies a b = mk_or (mk_not a) b

