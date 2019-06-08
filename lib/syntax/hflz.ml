open Hflmc2_util
open Id
open Type

type 'ty t =
  | Bool   of bool
  | Var    of 'ty Id.t
  | Or     of 'ty t * 'ty t
  | And    of 'ty t * 'ty t
  | Exists of string * 'ty t
  | Forall of string * 'ty t
  | Fix    of 'ty Id.t * 'ty t * Fixpoint.t
  | Abs    of 'ty arg Id.t * 'ty t
  | App    of 'ty t * 'ty t
  (* constructers only for hflz *)
  | Arith  of Arith.t
  | Pred   of string * Arith.t list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

