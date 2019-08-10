open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type

module Log = (val Logs.src_log @@ Logs.Src.create __MODULE__)


(******************************************************************************)
(* Predicate Variable                                                         *)
(******************************************************************************)

(* F : x:int -> g:(y:int -> o) -> o
 * x:int -> g:(y:int -> P_g(x,y)) -> P_F(x) : template
 * PredVar F = P_F(x)
 * PredVar g = P_g(x,y)
 * (age of F and g is omitted here)
 * *)
type pred_var = PredVar of TraceVar.aged  (* underapproximation of predicate  *)
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_pred_var aged = match TraceVar.type_of_aged aged with
  | TyInt -> invalid_arg "mk_pred_var"
  | _     -> PredVar(aged)

let args_of_pred_var pv =
  let all_args =
    match pv with
    | PredVar aged ->
        let fvs = match aged.var with
          | Nt _ -> []
          | Local {fvs;_} -> fvs
        in fvs @ TraceVar.mk_childlen aged
  in List.filter all_args
      ~f:(fun x -> TraceVar.type_of x = TyInt)


let pp_hum_pred_var : pred_var Print.t =
  fun ppf pv ->
    let args = args_of_pred_var pv in
    match pv with
    | PredVar aged ->
        Print.pf ppf "@[<h>P[%a](%a)@]"
          TraceVar.pp_hum_aged aged
          Print.(list ~sep:comma TraceVar.pp_hum) args

(******************************************************************************)
(* Arithmetic Expression                                                      *)
(******************************************************************************)

(* `E means external variable *)
type arith_var = [ `I of TraceVar.t | `E of unit Id.t ]
(* type arith_var = TraceVar.t *)
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let pp_hum_arith_var : arith_var Print.t =
  fun ppf -> function
    (* | tv -> TraceVar.pp_hum ppf tv *)
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

let rec arith_to_orig : arith -> Arith.t = function
  | Var (`I x) -> Var { (TraceVar.to_orig x) with ty = `Int }
  | Var (`E x) -> Var { x with ty = `Int }
  | Int n -> Int n
  | Op(op,as') -> Op(op, List.map ~f:arith_to_orig as')

(******************************************************************************)
(* Formula                                                                    *)
(******************************************************************************)

type formula = (Void.t, arith_var) Formula.gen_t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let pp_hum_formula_ : formula Print.t_with_prec =
  Print.gen_formula_ Print.void_ pp_hum_arith_var_
let pp_hum_formula : formula Print.t =
  pp_hum_formula_ Print.Prec.zero

let rec formula_to_orig : formula -> Formula.t = function
  | Bool b           -> Bool b
  | Var x            -> Var x
  | Or fs            -> Or (List.map ~f:formula_to_orig fs)
  | And fs           -> And (List.map ~f:formula_to_orig fs)
  | Pred (pred, as') -> Pred (pred, List.map ~f:arith_to_orig as')

(******************************************************************************)
(* Head and Body                                                              *)
(******************************************************************************)

type head = pred_var option
  [@@deriving eq,ord,show,iter,map,fold,sexp]
let pp_hum_head : head Print.t =
  fun ppf -> function
    | None   -> Print.string ppf "_|_"
    | Some v -> pp_hum_pred_var ppf v

type body =
  { pvs: pred_var list
  ; phi: formula list
  } [@@deriving eq,ord,show,iter,map,fold,sexp]

let pp_hum_body : body Print.t =
  fun ppf body ->
    if List.is_empty body.pvs
    then
      Print.(list ~sep:comma pp_hum_formula) ppf body.phi
    else
      Print.pf ppf "@[@[<h>%a@],@ @[<h>%a@]@]"
        Print.(list ~sep:comma pp_hum_pred_var) body.pvs
        Print.(list ~sep:comma pp_hum_formula) body.phi

let append_phi phi body = { body with phi = phi @ body.phi }
let append_pvs pvs body = { body with pvs = pvs @ body.pvs }

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

