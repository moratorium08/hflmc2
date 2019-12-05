(* できれば、syntax/hflz.mlを使いたいが、現状argを多相化するのが
 * めんどうくさい *)

open Hflmc2_util
open Hflmc2_syntax
open Id
open Rtype

type t =
  | Bool   of bool
  | Var    of sigma Id.t
  | Or     of t * t
  | And    of t * t
  | Abs    of arg Id.t * t
  | App    of t * t
  (* constructers only for hflz *)
  | Arith  of Arith.t
  | Pred   of Formula.pred * Arith.t list

type hes_rule =
  { var  : sigma Id.t
  ; body : t
  ; fix  : Fixpoint.t
  }

let lookup_rule f hes =
  List.find_exn hes ~f:(fun r -> Id.eq r.var f)

type hes = hes_rule list

let main_symbol = function
  | [] -> failwith "empty hes"
  | s::_ -> s.var
let main hes = Var(main_symbol hes)

(* Construction *)
let mk_bool b = Bool b

let mk_var x = Var x

let mk_ands = function
  | [] -> Bool true
  | x::xs -> List.fold_left xs ~init:x ~f:(fun a b -> And(a,b))

let mk_ors = function
  | [] -> Bool false
  | x::xs -> List.fold_left xs ~init:x ~f:(fun a b -> Or(a,b))

let mk_pred pred a1 a2 = Pred(pred, [a1;a2])

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

let rec fvs = function
  | Var x          -> IdSet.singleton x
  | Bool _         -> IdSet.empty
  | Or (phi1,phi2) -> IdSet.union (fvs phi1) (fvs phi2)
  | And(phi1,phi2) -> IdSet.union (fvs phi1) (fvs phi2)
  | App(phi1,phi2) -> IdSet.union (fvs phi1) (fvs phi2)
  | Abs(x,phi)     -> IdSet.remove (fvs phi) x
  | Arith a        -> IdSet.of_list @@ List.map ~f:Id.remove_ty @@ Arith.fvs a
  | Pred (_,as')   -> IdSet.union_list @@ List.map as' ~f:begin fun a ->
                        IdSet.of_list @@ List.map ~f:Id.remove_ty @@ Arith.fvs a
                      end

