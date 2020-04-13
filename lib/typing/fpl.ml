open Rtype
open Hflmc2_syntax

type t =
  | Bool   of bool
  | Var    of Rtype.t Id.t
  (* template is used for tracking counterexample. *)
  | Or     of t * t 
  | And    of t * t 
  | Forall of Rtype.t Id.t * t * template
  | Arith  of Arith.t
  | Pred   of Formula.pred * Arith.t list