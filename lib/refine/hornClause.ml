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
 * *)
type pred_var = PredVar of TraceVar.t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let args_of_pred_var (PredVar tv) =
  let fvs = match tv with
    | Nt _ -> []
    | Local {fvs;_} -> fvs
  in
    List.filter (fvs @ TraceVar.mk_locals tv)
       ~f:(fun child -> TraceVar.type_of child = TyInt)

let pp_hum_pred_var : pred_var Print.t =
  fun ppf (PredVar tv as pv) ->
    let args = args_of_pred_var pv in
    Print.pf ppf "@[<h>P[%a](%a)@]"
      TraceVar.pp_hum tv
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
      Print.pf ppf "@[<h>%a@],@ %a"
        Print.(list ~sep:comma pp_hum_pred_var) body.pvs
        pp_hum_formula body.phi

(******************************************************************************)
(* Clause                                                                     *)
(******************************************************************************)

type t =
  { head : pred_var option
  ; body : body
  } [@@deriving eq,ord,show,iter,map,fold,sexp]

let pp_hum : t Print.t =
  fun ppf { head; body } ->
    match head with
    | Some pv -> Print.pf ppf "@[<v 2>%a@ => @[<h>%a@]@]"
                   pp_hum_body body
                   pp_hum_pred_var pv
    | None    -> Print.pf ppf "@[<2>%a@ => _|_@]"
                   pp_hum_body body

