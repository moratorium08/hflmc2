let hd l = l 0
let tl l = fun i -> l (i + 2)

let rec for_all f len xs =
  if len = 0 then
    ()
  else
    (f (hd xs); for_all f (len - 1) (tl xs))
let main len =
  for_all (fun x -> assert (x <= len && 0 <= x)) len (fun i -> len - i)
