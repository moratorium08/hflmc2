let fold_nat f n x0 =
  let rec go i x =
    if i < n
      then go (i + 1) (f i x)
      else x
  in go 0 x0

let id n = fold_nat (fun i x -> x + i) n 0

let main n = if n >= 0 then assert (id n <= 2 * n)
