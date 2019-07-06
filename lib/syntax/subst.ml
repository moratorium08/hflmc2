open Hflmc2_util
open Type

(* TODO 適切な場所にmove *)

type 'x t = 'x IdMap.t

module Id' = struct
  let rec arith : [`Int] Id.t -> [`Int ] Id.t -> Arith.t -> Arith.t =
    fun x x' a ->
      match a with
      | Int _ -> a
      | Var v -> if Id.equal (=) v x then Var x' else Var v
      | Op(op, as') -> Op(op, List.map ~f:(arith x x') as')
  let arith : 'a. 'a Id.t -> [`Int ] Id.t -> Arith.t -> Arith.t =
    fun x x' a' -> arith {x with ty=`Int} x' a'

  let rec formula : unit Id.t -> [`Int] Id.t -> Formula.t -> Formula.t =
    fun x a p ->
      match p with
      | Pred(prim, as') -> Pred(prim, List.map as' ~f:(arith x a))
      | And ps -> And(List.map ~f:(formula x a) ps)
      | Or  ps -> Or (List.map ~f:(formula x a) ps)
      | _ -> p
  let formula : 'a. 'a Id.t -> [`Int] Id.t -> Formula.t -> Formula.t =
    fun x a p -> formula (Id.remove_ty x) a p

  let rec abstraction_ty : unit Id.t -> [`Int] Id.t -> abstraction_ty -> abstraction_ty =
    fun x x' ty -> match ty with
      | TyBool fs -> TyBool (List.map fs ~f:(formula x x'))
      | TyArrow({ty=TyInt;_} as y, _) when Id.eq x y ->
          assert false
      | TyArrow({ty=TyInt;_} as y, ty) ->
          TyArrow(y, abstraction_ty x x' ty)
      | TyArrow({ty=TySigma ty_arg;_} as y, ret_ty) ->
          TyArrow( { y with ty = TySigma (abstraction_ty x x' ty_arg)}
                 , abstraction_ty x x' ret_ty)
  let abstraction_ty : 'a. 'a Id.t -> [`Int] Id.t -> abstraction_ty -> abstraction_ty =
    fun x a a' -> abstraction_ty (Id.remove_ty x) a a'
end

(* TODO IdMapを使う *)
module Arith = struct
  let rec arith : [`Int] Id.t -> Arith.t -> Arith.t -> Arith.t =
    fun x a a' ->
      match a' with
      | Int _ -> a'
      | Var x' -> if Id.equal (=) x x' then a else a'
      | Op(op, as') -> Op(op, List.map ~f:(arith x a) as')
  let arith : 'a. 'a Id.t -> Arith.t -> Arith.t -> Arith.t =
    fun x a a' -> arith {x with ty=`Int} a a'

  let rec formula : unit Id.t -> Arith.t -> Formula.t -> Formula.t =
    fun x a p ->
      match p with
      | Pred(prim, as') -> Pred(prim, List.map as' ~f:(arith x a))
      | And ps -> And(List.map ~f:(formula x a) ps)
      | Or  ps -> Or (List.map ~f:(formula x a) ps)
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

module Hflz = struct
  let rec hflz : 'ty Hflz.t t -> 'ty Hflz.t -> 'ty Hflz.t =
    fun env phi -> match phi with
      | Var x ->
          begin match IdMap.lookup env x with
          | t -> t
          | exception Not_found -> Var x
          end
      | Or(phis)      -> Or(List.map ~f:(hflz env) phis)
      | And(phis)     -> And(List.map ~f:(hflz env) phis)
      | App(phi1,phi2)  -> App(hflz env phi1, hflz env phi2)
      | Exists(label,t) -> Exists(label, hflz env t)
      | Forall(label,t) -> Forall(label, hflz env t)
      | Abs(x, t)       -> Abs(x, hflz (IdMap.remove env x) t)
      | Bool _
      | Pred _
      | Arith _  -> phi

  (** Invariant: phi must have type TyBool *)
  let reduce_head : 'ty Hflz.hes -> 'ty Hflz.t -> 'ty Hflz.t =
    fun hes phi -> match phi with
    | Var x ->
        begin match x.ty, List.find hes ~f:(fun rule -> Id.eq x rule.var) with
        | TyBool _, Some phi -> phi.body
        | _ -> invalid_arg "reduce_head"
        end
    | App(_, _) ->
        let head, args = Hflz.decompose_app phi in
        let vars, body =
          match Hflz.decompose_abs head with
          | vars0, Var x ->
              let x_rule = List.find_exn hes ~f:(fun rule -> Id.eq x rule.var) in
              (* TODO このbodyがTyBool型を持っていることは隠れinvariant．parserで保証されている？ *)
              let vars1, body = Hflz.decompose_abs x_rule.body in
              (vars0@vars1), body
          | vars, body -> vars, body
        in
        let env = IdMap.of_list @@ List.zip_exn vars args in
        hflz env body
    | _ -> invalid_arg "reduce_head"
end

module Hfl = struct
  let rec hfl : Hfl.t IdMap.t -> Hfl.t -> Hfl.t =
    fun env phi -> match phi with
      | Var x ->
          begin match IdMap.lookup env x with
          | t -> t
          | exception Not_found -> Var x
          end
      | Bool _ -> phi
      | Or(phis,k)      -> Or(List.map ~f:(hfl env) phis, k)
      | And(phis,k)     -> And(List.map ~f:(hfl env) phis, k)
      | App(phi1,phi2)  -> App(hfl env phi1, hfl env phi2)
      | Exists(label,t) -> Exists(label, hfl env t)
      | Forall(label,t) -> Forall(label, hfl env t)
      | Abs(x, t)       -> Abs(x, hfl (IdMap.remove env x) t)
  let rec reduce : Hfl.t -> Hfl.t = function
    | Or (phis, k) -> Or (List.map ~f:reduce phis, k)
    | And(phis, k) -> And(List.map ~f:reduce phis, k)
    | App(phi1, phi2) ->
        begin match reduce phi1, reduce phi2 with
        | Abs(x, phi1), phi2 -> hfl (IdMap.of_list [x,phi2]) phi1
        | phi1, phi2 -> App(phi1, phi2)
        end
    | Exists(label, t) -> Exists(label, reduce t)
    | Forall(label, t) -> Forall(label, reduce t)
    | Abs(x, phi) -> Abs(x, reduce phi)
    | phi -> phi
end

