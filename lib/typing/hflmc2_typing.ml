module Type = Rtype
module Translate = Rtranslate
module Infer = Rinfer


let main x = 
  let y = Translate.translate x in
  Infer.infer y