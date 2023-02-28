let succ f x = f (x + 1)
let rec app f x = if Random.bool () then app (succ f) (x + 1) else f x
let check x y = if x = y then () else assert false
let main n = app (check n) n
