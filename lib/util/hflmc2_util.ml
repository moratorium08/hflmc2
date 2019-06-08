
open Core

module List     = struct
  include List
  let enumurate xs = List.zip_exn xs (List.init (List.length xs) ~f:(fun x -> x))
  let find_with_index (p : 'a -> bool) (xs : 'a list) =
    List.find_exn (enumurate xs) ~f:(fun (x,_) -> p x)
end

module Map      = Map

module Set      = Set

module Option   = Option

module Sexp     = Sexp

module Hashtbl  = Hashtbl

module Hash_set = Hash_set

module Fn = struct
  include Fn

  exception Fatal of string
  exception Unsupported of string
  exception TODO of string
  let unsupported ?(info="") () = raise (Fatal info)
  let todo ?(info="") () = raise (TODO info)

  let print ?(tag="") pp x =
    if tag = ""
    then Format.printf "%a@." pp x
    else Format.printf "%s: %a@." tag pp x

  let curry f x y = f (x, y)
  let uncurry f (x,y) = f x y

  let assert_no_exn f = try f () with e -> print_endline (Exn.to_string e); assert false
end

let char_of_sexp      = char_of_sexp
let sexp_of_char      = sexp_of_char
let bool_of_sexp      = bool_of_sexp
let sexp_of_bool      = sexp_of_bool
let sexp_of_exn       = sexp_of_exn
let float_of_sexp     = float_of_sexp
let sexp_of_float     = sexp_of_float
let int_of_sexp       = int_of_sexp
let sexp_of_int       = sexp_of_int
let int32_of_sexp     = int32_of_sexp
let sexp_of_int32     = sexp_of_int32
let int64_of_sexp     = int64_of_sexp
let sexp_of_int64     = sexp_of_int64
let list_of_sexp      = list_of_sexp
let sexp_of_list      = sexp_of_list
let nativeint_of_sexp = nativeint_of_sexp
let sexp_of_nativeint = sexp_of_nativeint
let option_of_sexp    = option_of_sexp
let sexp_of_option    = sexp_of_option
let sexp_of_ref       = sexp_of_ref
let string_of_sexp    = string_of_sexp
let sexp_of_string    = sexp_of_string
let bytes_of_sexp     = bytes_of_sexp
let sexp_of_bytes     = sexp_of_bytes
let unit_of_sexp      = unit_of_sexp
let sexp_of_unit      = sexp_of_unit

module Fmt = Fmt

