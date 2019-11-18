open Hflmc2_util
open Type
module S = struct
  module Id      = Id
  module Type    = Type
  module Arith   = Arith
  module Formula = Formula
  module Hfl     = Hfl
  module Hflz    = Hflz
end


module Subst = struct
  type 'x env = 'x IdMap.t
  module Id = struct
    let rec arith : [`Int ] S.Id.t env -> S.Arith.t -> S.Arith.t =
      fun env a ->
        match a with
        | Int _ -> a
        | Var v ->
            begin match IdMap.find env v with
            | None -> a
            | Some v' -> Var v'
            end
        | Op(op, as') -> Op(op, List.map ~f:(arith env) as')

    let rec formula : [`Int ] S.Id.t IdMap.t -> S.Formula.t -> S.Formula.t =
      fun env p ->
        match p with
        | Pred(prim, as') -> Pred(prim, List.map as' ~f:(arith env))
        | And ps -> And(List.map ~f:(formula env) ps)
        | Or  ps -> Or (List.map ~f:(formula env) ps)
        | _ -> p

    let rec abstraction_ty
              : [`Int ] S.Id.t env
             -> abstraction_ty
             -> abstraction_ty =
      fun env ty -> match ty with
        | TyBool fs -> TyBool (List.map fs ~f:(formula env))
        | TyArrow({ty=TyInt;_} as x, ty) ->
            TyArrow(x, abstraction_ty (IdMap.remove env x) ty)
        | TyArrow({ty=TySigma ty_arg;_} as y, ret_ty) ->
            TyArrow({y with ty = TySigma (abstraction_ty env ty_arg)},
                    abstraction_ty env ret_ty)
  end

  (* TODO IdMapを使う *)
  module Arith = struct
    let rec arith_
              : ('var -> 'var -> bool)
             -> 'var
             -> 'var S.Arith.gen_t
             -> 'var S.Arith.gen_t
             -> 'var S.Arith.gen_t =
      fun equal x a a' ->
        match a' with
        | Int _ -> a'
        | Var x' -> if equal x x' then a else a'
        | Op(op, as') -> Op(op, List.map ~f:(arith_ equal x a) as')
    let arith : 'a. 'a S.Id.t -> S.Arith.t -> S.Arith.t -> S.Arith.t =
      fun x a a' -> arith_ S.Id.eq {x with ty=`Int} a a'

    let rec formula_
              : ('var -> 'var -> bool)
             -> 'var
             -> 'var S.Arith.gen_t
             -> ('bvar,'var) S.Formula.gen_t
             -> ('bvar,'var) S.Formula.gen_t =
      fun equal x a p ->
        match p with
        | Pred(prim, as') -> Pred(prim, List.map as' ~f:(arith_ equal x a))
        | And ps -> And(List.map ~f:(formula_ equal x a) ps)
        | Or  ps -> Or (List.map ~f:(formula_ equal x a) ps)
        | _ -> p
    let formula : 'a. 'a S.Id.t -> S.Arith.t -> S.Formula.t -> S.Formula.t =
      fun x a p -> formula_ S.Id.eq {x with ty = `Int} a p

    let rec abstraction_ty
              : unit S.Id.t
             -> S.Arith.t
             -> abstraction_ty
             -> abstraction_ty =
      fun x a sigma ->
        match sigma with
        | TyBool preds ->
            TyBool (List.map ~f:(formula x a) preds)
        | TyArrow (arg,ret) ->
            TyArrow( { arg with ty = abstraction_argty x a arg.ty }
                   , abstraction_ty x a ret)
    and abstraction_argty
          : unit S.Id.t
         -> S.Arith.t
         -> abstraction_ty arg
         -> abstraction_ty arg =
      fun x a arg ->
        match arg with
        | TyInt -> TyInt
        | TySigma(sigma) -> TySigma(abstraction_ty x a sigma)
    let abstraction_ty
          : 'a S.Id.t
         -> S.Arith.t
         -> abstraction_ty
         -> abstraction_ty =
      fun x a sigma -> abstraction_ty (S.Id.remove_ty x) a sigma
    let abstraction_argty
          : 'a S.Id.t
         -> S.Arith.t
         -> abstraction_ty arg
         -> abstraction_ty arg =
      fun x a arg -> abstraction_argty (S.Id.remove_ty x) a arg
  end

  module Hflz = struct
    let rec hflz : 'ty S.Hflz.t env -> 'ty S.Hflz.t -> 'ty S.Hflz.t =
      fun env phi -> match phi with
        | Var x ->
            begin match IdMap.lookup env x with
            | t -> t
            | exception Not_found -> Var x
            end
        | Or(phi1,phi2)  -> Or(hflz env phi1, hflz env phi2)
        | And(phi1,phi2) -> And(hflz env phi1, hflz env phi2)
        | App(phi1,phi2) -> App(hflz env phi1, hflz env phi2)
        | Abs(x, t)      -> Abs(x, hflz (IdMap.remove env x) t)
        | Bool _
        | Pred _
        | Arith _  -> phi

    (** Invariant: phi must have type TyBool *)
    let reduce_head : 'ty S.Hflz.hes -> 'ty S.Hflz.t -> 'ty S.Hflz.t =
      fun hes phi -> match phi with
      | Var x ->
          begin match x.ty, List.find hes ~f:(fun rule -> S.Id.eq x rule.var) with
          | TyBool _, Some phi -> phi.body
          | _ -> invalid_arg "reduce_head"
          end
      | App(_, _) ->
          let head, args = S.Hflz.decompose_app phi in
          let vars, body =
            match S.Hflz.decompose_abs head with
            | vars0, Var x ->
                let x_rule =
                  List.find_exn hes ~f:(fun rule -> S.Id.eq x rule.var)
                in
                let vars1, body = S.Hflz.decompose_abs x_rule.body in
                vars0@vars1, body
            | vars, body -> vars, body
          in
          let env = IdMap.of_list @@ List.zip_exn vars args in
          hflz env body
      | _ -> invalid_arg "reduce_head"
  end

  module Hfl = struct
    let rec hfl : S.Hfl.t env -> S.Hfl.t -> S.Hfl.t =
      fun env phi -> match phi with
        | Var x ->
            begin match IdMap.lookup env x with
            | t -> t
            | exception Not_found -> Var x
            end
        | Bool _         -> phi
        | Or(phis,k)     -> Or(List.map ~f:(hfl env) phis, k)
        | And(phis,k)    -> And(List.map ~f:(hfl env) phis, k)
        | App(phi1,phi2) -> App(hfl env phi1, hfl env phi2)
        | Abs(x, t)      -> Abs(x, hfl (IdMap.remove env x) t)
  end
end

module Reduce = struct
  module Hfl = struct
    let rec beta : S.Hfl.t -> S.Hfl.t = function
      | Or (phis, k) -> Or (List.map ~f:beta phis, k)
      | And(phis, k) -> And(List.map ~f:beta phis, k)
      | App(phi1, phi2) ->
          begin match beta phi1, beta phi2 with
          | Abs(x, phi1), phi2 -> Subst.Hfl.hfl (IdMap.of_list [x,phi2]) phi1
          | phi1, phi2 -> App(phi1, phi2)
          end
      | Abs(x, phi) -> Abs(x, beta phi)
      | phi -> phi
    let rec eta : S.Hfl.t -> S.Hfl.t = function (* The Coercion rule generates many eta reduxes *)
      | Abs(x, (App (phi, Var x')))
          when Id.eq x x' && not (IdSet.mem (Hfl.fvs phi) x) -> phi
      | Abs(x, phi)     -> Abs(x, eta phi)
      | Or (phis, k)    -> Or (List.map ~f:eta phis, k)
      | And(phis, k)    -> And(List.map ~f:eta phis, k)
      | App(phi1, phi2) -> App(eta phi1, eta phi2)
      | phi             -> phi
    let beta_eta = eta <<< beta
  end
  module Hflz = struct
    let rec beta : 'a S.Hflz.t -> 'a S.Hflz.t = function
      | Or (phi1, phi2) -> Or (beta phi1, beta phi2)
      | And(phi1, phi2) -> And(beta phi1, beta phi2)
      | App(phi1, phi2) ->
          begin match beta phi1, beta phi2 with
          | Abs(x, phi1), phi2 -> Subst.Hflz.hflz (IdMap.of_list [x,phi2]) phi1
          | phi1, phi2 -> App(phi1, phi2)
          end
      | Abs(x, phi) -> Abs(x, beta phi)
      | phi -> phi
  end
end

module Simplify = struct
  let hflz : 'a Hflz.t -> 'a Hflz.t =
    let rec is_trivially_true : 'a Hflz.t -> bool =
      fun phi -> match phi with
      | Bool b -> b
      | Or (phi1,phi2) -> is_trivially_true phi1 || is_trivially_true phi2
      | And(phi1,phi2) -> is_trivially_true phi1 && is_trivially_true phi2
      | _ -> false
    in
    let rec is_trivially_false : 'a Hflz.t -> bool =
      fun phi -> match phi with
      | Bool b -> not b
      | And(phi1,phi2) -> is_trivially_false phi1 || is_trivially_false phi2
      | Or (phi1,phi2) -> is_trivially_false phi1 && is_trivially_false phi2
      | _ -> false
    in
    let rec go phi =
      match Reduce.Hflz.beta phi with
      | And(phi1, phi2) ->
          let phi1 = go phi1 in
          let phi2 = go phi2 in
          let phis = List.filter ~f:Fn.(not <<< is_trivially_true) [phi1;phi2] in
          Hflz.mk_ands phis
      | Or (phi1, phi2) ->
          let phi1 = go phi1 in
          let phi2 = go phi2 in
          let phis = List.filter ~f:Fn.(not <<< is_trivially_false) [phi1;phi2] in
          Hflz.mk_ors phis
      | Abs(x,phi)     -> Abs(x, go phi)
      | App(phi1,phi2) -> App(go phi1, go phi2)
      | phi -> phi
    in go
  let hflz_hes_rule : 'a Hflz.hes_rule -> 'a Hflz.hes_rule =
    fun rule -> { rule with body = hflz rule.body }
  let hflz_hes : 'a Hflz.hes -> 'a Hflz.hes =
    fun rules -> List.map ~f:hflz_hes_rule rules

  let rec hfl : ?force:bool -> Hfl.t -> Hfl.t =
    let is_trivially_true : Hfl.t -> bool =
      fun phi -> match phi with
      | Bool b -> b
      | _ -> false
    in
    let is_trivially_false : Hfl.t -> bool =
      fun phi -> match phi with
      | Bool b -> not b
      | _ -> false
    in
    fun ?(force=false) phi ->
      match Reduce.Hfl.beta_eta phi with
      | And(phis, k) when k = `Inserted || force ->
          let phis = List.map ~f:hfl phis in
          let phis = List.filter ~f:Fn.(not <<< is_trivially_true) phis in
          Hfl.mk_ands phis ~kind:k
      | Or(phis, k) when k = `Inserted || force ->
          let phis = List.map ~f:hfl phis in
          let phis = List.filter ~f:Fn.(not <<< is_trivially_false) phis in
          Hfl.mk_ors phis ~kind:k
      | And(phis, k) -> And(List.map ~f:hfl phis, k)(* preserve the structure *)
      | Or (phis, k) -> Or (List.map ~f:hfl phis, k)(* preserve the structure *)
      | Abs(x,phi)     -> Abs(x, hfl ~force phi)
      | App(phi1,phi2) -> App(hfl ~force phi1, hfl ~force phi2)
      | phi -> phi

  let rec is_true_def =
    fun phi -> match phi with
    | Formula.Bool b -> b
    | Formula.And phis -> List.for_all ~f:is_true_def phis
    | Formula.Or  phis -> List.exists  ~f:is_true_def phis
    | _ -> false
  let rec is_false_def =
    fun phi -> match phi with
    | Formula.Bool b -> not b
    | Formula.And phis -> List.exists  ~f:is_false_def phis
    | Formula.Or  phis -> List.for_all ~f:is_false_def phis
    | _ -> false

  let rec formula
            : 'bvar 'avar
            . ?is_true:(('bvar, 'avar) Formula.gen_t -> bool)
           -> ?is_false:(('bvar, 'avar) Formula.gen_t -> bool)
           -> ('bvar, 'avar) Formula.gen_t
           -> ('bvar, 'avar) Formula.gen_t =
    fun ?(is_true=is_true_def) ?(is_false=is_false_def) -> function
    | Formula.And phis ->
        let phis = List.map ~f:formula phis in
        let phis = List.filter ~f:Fn.(not <<< is_true) phis in
        begin if List.exists ~f:is_false phis then
          Bool false
        else match phis with
          | []    -> Bool true
          | [phi] -> phi
          | _     -> And phis
        end
    | Formula.Or phis ->
        let phis = List.map ~f:formula phis in
        let phis = List.filter ~f:Fn.(not <<< is_false) phis in
        begin if List.exists ~f:is_true phis then
          Bool true
        else match phis with
          | []    -> Bool false
          | [phi] -> phi
          | _     -> Or phis
        end
    | phi -> phi
end

