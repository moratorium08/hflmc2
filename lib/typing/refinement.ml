open Hflmc2_syntax

type t
  = RTrue
   | RFalse
   | Pred of Formula.pred * Arith.t list
   | And of t * t 
   | Or of t * t
  
