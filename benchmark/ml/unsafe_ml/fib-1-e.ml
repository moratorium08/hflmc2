let rec fib n =
  if n<2 then 1 else
    fib (n-2) + fib (n-3)
let main n =
  assert (n <= fib n)

