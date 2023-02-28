let rec sum n =
  if n <= 1 then
    0
  else
    n + sum (n-1)
let main n = assert (3*n-3 <= sum n)

