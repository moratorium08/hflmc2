open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type

type t =
  | Nt of
      { orig : simple_ty Id.t
      ; age  : int
      }
  | Local of
      (* parentのnth番目のargument. 0-indexed *)
      { parent : t
      ; name   : simple_ty arg Id.t
      ; fvs    : t list
      ; nth    : int
      }
  [@@deriving eq,ord,show,iter,map,fold,sexp]
let rec pp_hum : t Print.t =
  fun ppf tvar -> match tvar with
    | Nt { orig; age } ->
        Print.string ppf (orig.name ^ "^" ^ string_of_int age)
    | Local { parent; nth; _ } ->
        Print.pf ppf "%a.%d" pp_hum parent nth
        (* Print.pf ppf "%a.%s@%d" pp_hum parent (Id.to_string name) nth *)
let to_string = Print.strf "%a" pp_hum

let type_of = function
  | Nt    { orig; _ } -> TySigma orig.ty
  | Local { name; _ } -> name.ty

let mk_nt : ?age:int -> simple_ty Id.t -> t =
  fun ?(age=0) orig -> Nt { orig; age }

let counters : (unit Id.t, int) Hashtbl.t = Hashtbl.create (module Id.Key)

let reset_counters () = Hashtbl.clear counters

let gen_nt : simple_ty Id.t -> t =
  fun orig ->
    let key = Id.remove_ty orig in
    match Hashtbl.find counters key with
    | None ->
        Hashtbl.add_exn counters ~key ~data:1;
        mk_nt ~age:0 orig
    | Some n ->
        Hashtbl.replace counters ~key ~data:(n+1);
        mk_nt ~age:n orig

let mk_locals : t -> t list =
  fun parent -> match type_of parent with
    | TyInt -> []
    | TySigma ty ->
        let rec go acc nth ty = match ty with
          | TyBool () -> List.rev acc
          | TyArrow(x, ret_ty) ->
              let x = Local { parent; name=x; fvs=List.rev acc; nth } in
              go (x::acc) (nth+1) ret_ty
        in go [] 0 ty
