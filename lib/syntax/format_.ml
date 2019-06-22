open Hflmc2_util

include Fmt
let print = Fn.print

let list_comma : 'a Fmt.t -> 'a list Fmt.t =
  fun format_x ppf xs ->
    let sep ppf () = Fmt.pf ppf ",@," in
    Fmt.pf ppf "[@[%a@]]" Fmt.(list ~sep format_x) xs
let list_semi : 'a Fmt.t -> 'a list Fmt.t =
  fun format_x ppf xs ->
    let sep ppf () = Fmt.pf ppf ";@," in
    Fmt.pf ppf "[@[%a@]]" Fmt.(list ~sep format_x) xs
let list_set : 'a Fmt.t -> 'a list Fmt.t =
  fun format_x ppf xs ->
    let sep ppf () = Fmt.pf ppf ",@," in
    Fmt.pf ppf "{@[%a@]}" Fmt.(list ~sep format_x) xs


module Prec = struct
  type t = int
  let succ x = x + 1
  let succ_if b x = if b then x + 1 else x

  let zero  = 0
  let arrow = 1
  let abs   = 1
  let or_   = 2
  let and_  = 3
  let eq    = 4
  let add   = 6
  let mult  = 7
  let app   = 10

  let of_op = function
    | Arith.Add -> add
    | Arith.Sub -> add
    | Arith.Mult -> mult
  let op_is_leftassoc = function
    | Arith.Add -> true
    | Arith.Sub -> true
    | Arith.Mult -> true
  let op_is_rightassoc = function
    | Arith.Add -> false
    | Arith.Sub -> false
    | Arith.Mult -> false
  let of_pred = fun _ -> eq
end

let show_paren
     : bool
    -> Format.formatter
    -> ('a, Format.formatter, unit) format
    -> 'a =
  fun b ppf fmt ->
    if b
    then Fmt.pf ppf ("(" ^^ fmt ^^ ")")
    else Fmt.pf ppf fmt

let id : 'ty Id.t Fmt.t =
  fun ppf id ->
    Fmt.pf ppf "%s" @@ id.name ^ string_of_int id.id

(* Arith *)

let op : Arith.op Fmt.t =
  fun ppf op -> match op with
    | Add  -> Fmt.string ppf "+"
    | Sub  -> Fmt.string ppf "-"
    | Mult -> Fmt.string ppf "*"

let rec arith_ : Prec.t -> Arith.t Fmt.t =
  fun prec ppf a -> match a with
    | Int n -> Fmt.int ppf n
    | Var x -> id ppf x
    | Op (op',[a1;a2]) ->
        let op_prec = Prec.of_op op' in
        let prec_l = Prec.(succ_if (not @@ op_is_leftassoc op') op_prec) in
        let prec_r = Prec.(succ_if (not @@ op_is_rightassoc op') op_prec) in
        show_paren (prec > op_prec) ppf "@[<1>%a@ %a@ %a@]"
          (arith_ prec_l) a1
          op op'
          (arith_ prec_r) a2
    | _ -> assert false (* 今の所2項演算子しか考えていない *)
let arith : Arith.t Fmt.t = arith_ Prec.zero

(* Formula *)

let pred : Formula.pred Fmt.t =
  fun ppf pred -> match pred with
    | Eq  -> Fmt.string ppf "="
    | Neq -> Fmt.string ppf "<>"
    | Le  -> Fmt.string ppf "<="
    | Ge  -> Fmt.string ppf ">="
    | Lt  -> Fmt.string ppf "<"
    | Gt  -> Fmt.string ppf ">"

let rec formula_ : Prec.t -> Formula.t Fmt.t =
  fun prec ppf f -> match f with
    | Bool true -> Fmt.string ppf "true"
    | Bool false -> Fmt.string ppf "false"
    | Or(f1,f2) ->
        show_paren (prec > Prec.or_) ppf "@[<0>%a@ || %a@]"
          (formula_ Prec.(succ or_)) f1 (* infixr *)
          (formula_ Prec.or_) f2
    | And(f1,f2) ->
        show_paren (prec > Prec.and_) ppf "@[<0>%a@ && %a@]"
          (formula_ Prec.(succ and_)) f1 (* infixr *)
          (formula_ Prec.and_) f2
    | Pred(pred',[f1;f2]) ->
        Fmt.pf ppf "@[<1>%a@ %a@ %a@]"
          arith f1
          pred pred'
          arith f2
    | _ -> assert false
let formula : Formula.t Fmt.t = formula_ Prec.zero

(* Type *)

let argty_ : (Prec.t -> 'ty Fmt.t) -> Prec.t -> 'ty Type.arg Fmt.t =
  fun format_ty_ prec ppf arg -> match arg with
    | TyInt -> Fmt.string ppf "int"
    | TySigma sigma -> format_ty_ prec ppf sigma

let argty : 'ty Fmt.t -> 'ty Type.arg Fmt.t =
  fun format_ty ppf arg -> match arg with
    | TyInt -> Fmt.string ppf "int"
    | TySigma sigma -> format_ty ppf sigma

let rec ty_ : 'annot Fmt.t -> Prec.t -> 'annot Type.ty Fmt.t =
  fun format_annot prec ppf ty -> match ty with
      | TyBool annot ->
          Fmt.pf ppf "bool@[%a@]" format_annot annot
      | TyArrow (x, ret) ->
          show_paren (prec > Prec.arrow) ppf "@[<1>%a:%a ->@ %a@]"
            id x
            (argty (ty_ format_annot Prec.(succ arrow))) x.ty
            (ty_ format_annot Prec.arrow) ret
let ty : 'annot Fmt.t -> 'annot Type.ty Fmt.t =
  fun format_annot -> ty_ format_annot Prec.zero

let simple_ty_ : Prec.t -> Type.simple_ty Fmt.t = ty_ Fmt.nop
let simple_ty : Type.simple_ty Fmt.t = simple_ty_ Prec.zero
let simple_argty_ : Prec.t -> Type.simple_ty Type.arg Fmt.t = argty_ simple_ty_
let simple_argty : Type.simple_ty Type.arg Fmt.t = simple_argty_ Prec.zero

let abstraction_ty : Type.abstraction_ty Fmt.t =
  let annot ppf fs =
    Fmt.pf ppf "[%a]"
      (Fmt.list ~sep:Fmt.comma formula) fs
  in ty annot
let abstraction_argty  : Type.abstraction_argty Fmt.t =
  argty @@ ty (Fmt.list ~sep:Fmt.comma formula)


let rec abstracted_ty_ : Prec.t -> Type.abstracted_ty Fmt.t =
  fun prec ppf aty -> match aty with
    | ATyBool ->
        Fmt.string ppf "bool"
    | ATyArrow(arg,ret) ->
        show_paren (prec > Prec.arrow) ppf "%a ->@ %a"
          (abstracted_ty_ Prec.(succ arrow)) arg
          (abstracted_ty_ Prec.arrow) ret
let abstracted_ty : Type.abstracted_ty Fmt.t = abstracted_ty_ Prec.zero
let abstracted_argty : Type.abstracted_argty Fmt.t = abstracted_ty

(* Fixpoint *)

let fixpoint : Fixpoint.t Fmt.t =
  fun ppf t -> match t with
    | Least    -> Fmt.string ppf "μ"
    | Greatest -> Fmt.string ppf "ν"

(* Hfl *)


let rec hfl_ prec ppf (phi : Hfl.t) = match phi with
  | Bool true ->
      Fmt.string ppf "true"
  | Bool false ->
      Fmt.string ppf "false"
  | Var x ->
      id ppf x
  | Or (phis, `Inserted) ->
      let sep ppf () = Fmt.pf ppf "@ ||' " in
      show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@]"
        (list ~sep (hfl_ Prec.or_)) phis
  | And (phis, `Inserted) ->
      let sep ppf () = Fmt.pf ppf "@ &&' " in
      show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@]"
        (list ~sep (hfl_ Prec.and_)) phis
  | Or (phis, `Original) ->
      let sep ppf () = Fmt.pf ppf "@ || " in
      show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@]"
        (list ~sep (hfl_ Prec.or_)) phis
  | And (phis, `Original) ->
      let sep ppf () = Fmt.pf ppf "@ && " in
      show_paren (prec > Prec.and_) ppf "@[<hv 0>%a@]"
        (list ~sep (hfl_ Prec.and_)) phis
  | Exists (l, phi) ->
      show_paren (prec > Prec.app) ppf "@[<1><%s>%a@]"
        l
        (hfl_ Prec.(succ app)) phi
  | Forall (l, psi) ->
      show_paren (prec > Prec.app) ppf "@[<1>[%s]%a@]"
        l
        (hfl_ Prec.(succ app)) psi
  | Abs (x, psi) ->
      show_paren (prec > Prec.abs) ppf "@[<1>λ%a:%a.@,%a@]"
        id x
        (abstracted_ty_ Prec.(succ arrow)) x.ty
        (hfl_ Prec.abs) psi
  | App (psi1, psi2) ->
      show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]"
        (hfl_ Prec.app) psi1
        (hfl_ Prec.(succ app)) psi2
let hfl : Hfl.t Fmt.t = hfl_ Prec.zero

let hfl_hes_rule : Hfl.hes_rule Fmt.t =
  fun ppf rule ->
    Fmt.pf ppf "@[<2>%s =%a %a@]"
      (Id.to_string rule.var)
      fixpoint rule.fix
      hfl rule.body

let hfl_hes : Hfl.hes Fmt.t =
  fun ppf hes ->
    Fmt.pf ppf "@[<v>%a@]"
      (Fmt.list hfl_hes_rule) hes

(* Hflz *)

let rec hflz_ : (Prec.t -> 'ty Fmt.t) -> Prec.t -> 'ty Hflz.t Fmt.t =
  fun format_ty_ prec ppf (phi : 'ty Hflz.t) -> match phi with
    | Bool true -> Fmt.string ppf "true"
    | Bool false -> Fmt.string ppf "false"
    | Var x -> id ppf x
    | Or phis  ->
        let sep ppf () = Fmt.pf ppf "@ || " in
        show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@]"
          (list ~sep (hflz_ format_ty_ Prec.or_)) phis
    | And phis  ->
        let sep ppf () = Fmt.pf ppf "@ && " in
        show_paren (prec > Prec.or_) ppf "@[<hv 0>%a@]"
          (list ~sep (hflz_ format_ty_ Prec.and_)) phis
    | Exists (l, psi) ->
        show_paren (prec > Prec.app) ppf "@[<1><%s>%a@]"
          l
          (hflz_ format_ty_ Prec.(succ app)) psi
    | Forall (l, psi) ->
        show_paren (prec > Prec.app) ppf "@[<1>[%s]%a@]"
          l
          (hflz_ format_ty_ Prec.(succ app)) psi
    | Abs (x, psi) ->
        show_paren (prec > Prec.abs) ppf "@[<1>λ%a:%a.@,%a@]"
          id x
          (argty (format_ty_ Prec.(succ arrow))) x.ty
          (hflz_ format_ty_ Prec.abs) psi
    | App (psi1, psi2) ->
        show_paren (prec > Prec.app) ppf "@[<1>%a@ %a@]"
          (hflz_ format_ty_ Prec.app) psi1
          (hflz_ format_ty_ Prec.(succ app)) psi2
    | Arith a ->
        arith_ prec ppf a
    | Pred (pred, as') ->
        show_paren (prec > Prec.eq) ppf "%a"
          formula (Formula.Pred(pred, as'))
let hflz : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.t Fmt.t =
  fun format_ty_ -> hflz_ format_ty_ Prec.zero

let hflz_hes_rule : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.hes_rule Fmt.t =
  fun format_ty_ ppf rule ->
    Fmt.pf ppf "@[<2>%s =%a %a@]"
      (Id.to_string rule.var)
      fixpoint rule.fix
      (hflz format_ty_) rule.body

let hflz_hes : (Prec.t -> 'ty Fmt.t) -> 'ty Hflz.hes Fmt.t =
  fun format_ty_ ppf hes ->
    Fmt.pf ppf "@[<v>%a@]"
      (Fmt.list (hflz_hes_rule format_ty_)) hes

