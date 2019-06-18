open Hflmc2_util
include Set.Make(Id.Key)
let mem set x = mem set (Id.remove_ty x)
let add set x = add set (Id.remove_ty x)
