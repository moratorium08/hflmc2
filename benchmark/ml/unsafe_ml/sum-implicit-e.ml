let rec sum k x = if x <= 1 then k 0 else sum (fun r -> k (r + x)) (x - 1)

let main n = sum (fun r -> assert(r >= 3*n-3)) n
