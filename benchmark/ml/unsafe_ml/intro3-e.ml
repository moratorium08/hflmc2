let succ f x = f (x - 1)
let rec app3 f g = if Random.bool () then app3 (succ f) g else g f
let app x f = f x
let check x y = if x <= y then () else assert false
let main i = app3 (check i) (app i)
