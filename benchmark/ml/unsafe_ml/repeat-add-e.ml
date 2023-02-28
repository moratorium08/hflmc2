let add x1 x2 = x1 - x2
let rec repeat f k x = if k <= 0 then x else f (repeat f (k - 1) x)
let main n k = if n >= 0 && k > 0 then assert (repeat (add n) k 0 >= n)
