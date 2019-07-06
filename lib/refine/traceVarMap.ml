open Hflmc2_util
include Map.Make(TraceVar)
let add_override : 'a t -> key:TraceVar.t -> data:'a -> 'a t =
  fun map ~key ~data ->
    let map = remove map key in
    add_exn map ~key ~data
let merge : 'a t -> 'a t -> 'a t =
  fun m1 m2 ->
    merge m1 m2
      ~f:begin fun ~key -> let _ = key in function
      | `Both _ -> assert false
      | `Left x -> Some x
      | `Right x -> Some x
      end
