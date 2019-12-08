module Type = Rtype
module Translate = Rtranslate
module Infer = Rinfer
module Rhflz = Rhflz
module RArith = RArith


let rec generate_env = function 
  | [] -> Hflmc2_syntax.IdMap.empty
  | x::xs -> 
    let m = generate_env xs in
    let open Rhflz in
    Hflmc2_syntax.IdMap.add m x.var x.var.ty
  
let rec print_types = function
  | [] -> ()
  | x::xs -> 
    let open Rhflz in
    Rtype.print_rtype x.var.ty;
    print_newline ();
    print_types xs

let main x = 
  let y = Translate.translate x in
  (*
  print_types y;
  print_newline();
  *)
  let env = generate_env y in
  Infer.infer y env