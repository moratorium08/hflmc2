open Hflmc2_syntax

type id = int

type template = id * id list (* template prdicate name and its args *)


type refinement
  = RTrue
   | RFalse
   | RPred of Formula.pred * Arith.t list
   | RAnd of refinement * refinement
   | ROr of refinement * refinement
   | RTemplate of template
  
type rint =
  | RId of id
  | RArith of Arith.t

type t 
  = RBool of refinement
  | RArrow of t * t
  | RInt of rint