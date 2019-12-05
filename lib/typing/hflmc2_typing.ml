module Type = Rtype
module Translate = Rtranslate
module Infer = Rinfer
module Rhflz = Rhflz


let rec generate_env = function 
  | [] -> Hflmc2_syntax.IdMap.empty
  | x::xs -> 
    let m = generate_env xs in
    let open Rhflz in
    Hflmc2_syntax.IdMap.add m x.var x.var.ty

let main x = 
  let y = Translate.translate x in
  let env = generate_env y in
  Infer.infer y env