open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type

module Log = (val Logs.src_log @@ Logs.Src.create __MODULE__)


(******************************************************************************)
(* Predicate Variable                                                         *)
(******************************************************************************)

(* F : x:int -> g:(y:int -> o{P1(x,y)}) -> o{P2(x)} のとき
 * PredVar F = P2(x)
 * PredVar g = P1(x,y)
 * PredVar x = invalid
 * （ここでageは省略してある）
 * *)
type pred_var = PredVar of TraceVar.aged
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let args_of_pred_var (PredVar aged) =
  let fvs = match aged.var with
    | Nt _ -> []
    | Local {fvs;_} -> fvs
  in
    List.filter (fvs @ TraceVar.mk_childlen aged)
       ~f:(fun child -> TraceVar.type_of child = TyInt)

let pp_hum_pred_var : pred_var Print.t =
  fun ppf (PredVar aged as pv) ->
    let args = args_of_pred_var pv in
    Print.pf ppf "@[<h>P[%a](%a)@]"
      TraceVar.pp_hum_aged aged
      Print.(list ~sep:comma TraceVar.pp_hum) args

(******************************************************************************)
(* Arithmetic Expression                                                      *)
(******************************************************************************)

(* `E means external variable *)
type arith_var = [ `I of TraceVar.t | `E of unit Id.t ]
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let pp_hum_arith_var : arith_var Print.t =
  fun ppf -> function
    | `I tv -> TraceVar.pp_hum ppf tv
    | `E ev -> Print.id ppf ev
let pp_hum_arith_var_ : arith_var Print.t_with_prec =
  Print.ignore_prec pp_hum_arith_var

type arith   = arith_var Arith.gen_t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let pp_hum_arith_ : arith Print.t_with_prec =
  Print.gen_arith_ pp_hum_arith_var_
let pp_hum_arith : arith Print.t =
  pp_hum_arith_ Print.Prec.zero

(******************************************************************************)
(* Formula                                                                    *)
(******************************************************************************)

type formula = (Void.t, arith_var) Formula.gen_t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let pp_hum_formula_ : formula Print.t_with_prec =
  Print.gen_formula_ Print.void_ pp_hum_arith_var_
let pp_hum_formula : formula Print.t =
  pp_hum_formula_ Print.Prec.zero

type head = pred_var option
  [@@deriving eq,ord,show,iter,map,fold,sexp]
let pp_hum_head : head Print.t =
  fun ppf -> function
    | None   -> Print.string ppf "_|_"
    | Some v -> pp_hum_pred_var ppf v

type body =
  { pvs: pred_var list
  ; phi: formula
  } [@@deriving eq,ord,show,iter,map,fold,sexp]

let pp_hum_body : body Print.t =
  fun ppf body ->
    if List.is_empty body.pvs
    then
      pp_hum_formula ppf body.phi
    else
      Print.pf ppf "@[@[<h>%a@],@ @[<h>%a@]@]"
        Print.(list ~sep:comma pp_hum_pred_var) body.pvs
        pp_hum_formula body.phi

(******************************************************************************)
(* Clause                                                                     *)
(******************************************************************************)

type t =
  { head : head
  ; body : body
  } [@@deriving eq,ord,show,iter,map,fold,sexp]

let pp_hum : t Print.t =
  fun ppf { head; body } ->
    Print.pf ppf "@[<v 2>%a@ <= @[<h>%a@]@]"
      pp_hum_head head
      pp_hum_body body

