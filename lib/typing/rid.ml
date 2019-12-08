open Hflmc2_syntax

type id = int

let print_id = print_int

let to_string id = Printf.sprintf "X%d" id

module M = Map.Make(Int)