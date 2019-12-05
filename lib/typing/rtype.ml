open Hflmc2_syntax

type id = int
type template = id * id list (* template prdicate name and its args *)

type arg 
  = RInt of id
  | RSigma of sigma
and sigma 
  = RBool of template
  | RArrow of arg Id.t * sigma

type t = sigma