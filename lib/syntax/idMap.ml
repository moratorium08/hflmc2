open Hflmc2_util
include Map.Make(Id.Key)
let add : 'x t -> 'a Id.t -> 'x -> 'x t =
  fun env v data ->
    add_exn env ~key:(Id.remove_ty v) ~data
let lookup : 'x t -> 'a Id.t -> 'x =
  fun map v -> find_exn map (Id.remove_ty v)
