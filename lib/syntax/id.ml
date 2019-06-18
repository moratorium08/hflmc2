open Hflmc2_util

(** ['ty] is typically a type of the id *)
type 'ty t =
  { name : string
  ; id   : int
  ; ty   : 'ty
  }
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let id_count = ref 0
let gen_id () =
  let x = !id_count in
  let () = id_count := x + 1 in
  x

let to_string id = id.name ^ string_of_int id.id

let gen : ?name:string -> 'annot -> 'anno t =
  fun ?(name="x") ann ->
     { name = name
     ; id = gen_id()
     ; ty = ann
     }

let remove_ty : 'ty t -> unit t = fun x -> { x with ty = () }

module Key : Map.Key with type t = unit t = struct
  type nonrec t = unit t
  let sexp_of_t = sexp_of_t sexp_of_unit
  let t_of_sexp = t_of_sexp unit_of_sexp
  let compare = compare Core.compare
end

