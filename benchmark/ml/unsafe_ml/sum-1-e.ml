let rec sum n =
  if n <= 1 then
    0
  else
    n + sum (n-1)
let main n = assert (4*n-6 <= sum n)
