open Hflmc2_util
open Type

module Arith = struct
  let rec arith : unit Id.t -> Arith.t -> Arith.t -> Arith.t =
    fun x a a' ->
      match a' with
      | Int _ -> a'
      | Var x' -> if Id.equal (=) x x' then a else a'
      | Op(op, as') -> Op(op, List.map ~f:(arith x a) as')
  let arith : 'a. 'a Id.t -> Arith.t -> Arith.t -> Arith.t =
    fun x a a' -> arith (Id.remove_ty x) a a'

  let rec formula : unit Id.t -> Arith.t -> Formula.t -> Formula.t =
    fun x a p ->
      match p with
      | Pred(prim, as') -> Pred(prim, List.map as' ~f:(arith x a))
      | And(p1,p2) -> And(formula x a p1, formula x a p2)
      | Or(p1,p2) -> Or(formula x a p1, formula x a p2)
      | _ -> p
  let formula : 'a. 'a Id.t -> Arith.t -> Formula.t -> Formula.t =
    fun x a p -> formula (Id.remove_ty x) a p

  let rec abstraction_ty : unit Id.t -> Arith.t -> abstraction_ty -> abstraction_ty =
    fun x a sigma ->
      let x = Id.remove_ty x in
      match sigma with
      | TyBool preds ->
          TyBool (List.map ~f:(formula x a) preds)
      | TyArrow (arg,ret) ->
          TyArrow({ arg with ty = abstraction_argty x a arg.ty }, abstraction_ty x a ret)
  and abstraction_argty : unit Id.t -> Arith.t -> abstraction_ty arg -> abstraction_ty arg =
    fun x a arg ->
      let x = Id.remove_ty x in
      match arg with
      | TyInt -> TyInt
      | TySigma(sigma) -> TySigma(abstraction_ty x a sigma)
  let abstraction_ty : 'a Id.t -> Arith.t -> abstraction_ty -> abstraction_ty =
    fun x a sigma -> abstraction_ty (Id.remove_ty x) a sigma
  let abstraction_argty : 'a Id.t -> Arith.t -> abstraction_ty arg -> abstraction_ty arg =
    fun x a arg -> abstraction_argty (Id.remove_ty x) a arg
end
