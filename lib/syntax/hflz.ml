open Hflmc2_util
open Id
open Type

type 'ty t =
  | Bool   of bool
  | Var    of 'ty Id.t
  | Or     of 'ty t list
  | And    of 'ty t list
  | Exists of string * 'ty t
  | Forall of string * 'ty t
  | Abs    of 'ty arg Id.t * 'ty t
  | App    of 'ty t * 'ty t
  (* constructers only for hflz *)
  | Arith  of Arith.t
  | Pred   of Formula.pred * Arith.t list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type 'ty hes_rule =
  { var  : 'ty Id.t
  ; body : 'ty t
  ; fix  : Fixpoint.t
  }
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let lookup_rule f hes =
  List.find_exn hes ~f:(fun r -> Id.eq r.var f)

type 'ty hes = 'ty hes_rule list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let main_symbol = function
  | [] -> failwith "empty hes"
  | s::_ -> s.var
let main hes = Var(main_symbol hes)

(* Construction *)
let mk_bool b = Bool b

let mk_var x = Var x

let mk_ands = function
  | [] -> Bool true
  | [x] -> x
  | xs -> And xs

let mk_ors = function
  | [] -> Bool false
  | [x] -> x
  | xs -> Or xs

let mk_pred pred a1 a2 = Pred(pred, [a1;a2])

let mk_forall l t = Forall(l,t)
let mk_exists l t = Exists(l,t)

let mk_arith a = Arith a

let mk_app t1 t2 = App(t1,t2)
let mk_apps t ts = List.fold_left ts ~init:t ~f:mk_app

let mk_abs x t = Abs(x, t)
let mk_abss xs t = List.fold_right xs ~init:t ~f:mk_abs

(* Decomposition *)
let decompose_abs =
  let rec go acc phi = match phi with
    | Abs(x,phi) -> go (x::acc) phi
    | _ -> (List.rev acc, phi)
  in fun phi -> go [] phi

let decompose_app =
  let rec go phi acc = match phi with
    | App(phi,x) -> go phi (x::acc)
    | _ -> (phi, acc)
  in
  fun phi -> go phi []

(* let mk_app t1 t2 = App(t1,t2) *)
(* let mk_apps t ts = List.fold_left ts ~init:t ~f:mk_app *)
