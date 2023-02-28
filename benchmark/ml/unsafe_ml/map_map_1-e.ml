let rec map x =
 if x=1 then 0 else 1 + map (x-1)

let main n =
  assert(map (map n) = n)
