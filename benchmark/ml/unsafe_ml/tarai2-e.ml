let rec tarai2 x y =
  if x <= y
    then y
    else
      tarai2 (tarai2 x (y + 1))
             (tarai2 y (x + 1))

let main x y = let z = tarai2 x y in assert (z <= x || z <= y)
