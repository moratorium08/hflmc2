let rec ack m n =
  if m=0 then n
  else if n=0 then ack (m-1) 1
  else ack (m-1) (ack m (n-1))

let main m n =
  if (m>=0 && n>=0)
  then assert (ack m n >= n)
