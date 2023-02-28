let rec zip x y =
  if x = 0
  then
    if y = 0
    then 0
    else assert false
  else
    if y = 0
    then assert false
    else x + zip (x-1) (y-1)

let main n =
  assert (zip n n <= 2 * n)
