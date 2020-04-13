module Type = Rtype
module Translate = Rtranslate
module Infer = Rinfer
module Rhflz = Rhflz
module Result = Rresult
module Chc = Chc

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

let main x top_old = 
  let y = Translate.translate x in
  let top_rule = Rhflz.lookup_rule top_old y in
  let top = top_rule.var in
  (*
  print_types y;
  print_newline();
  *)
  let env = generate_env y in
  Infer.infer y env top