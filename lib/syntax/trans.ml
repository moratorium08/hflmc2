open Hflmc2_util
open Type

module Subst = struct
  type 'x env = 'x IdMap.t
  module Id' = struct
    let rec arith : [`Int ] Id.t env -> Arith.t -> Arith.t =
      fun env a ->
        match a with
        | Int _ -> a
        | Var v ->
            begin match IdMap.find env v with
            | None -> a
            | Some v' -> Var v'
            end
        | Op(op, as') -> Op(op, List.map ~f:(arith env) as')

    let rec formula : [`Int ] Id.t IdMap.t -> Formula.t -> Formula.t =
      fun env p ->
        match p with
        | Pred(prim, as') -> Pred(prim, List.map as' ~f:(arith env))
        | And ps -> And(List.map ~f:(formula env) ps)
        | Or  ps -> Or (List.map ~f:(formula env) ps)
        | _ -> p

    let rec abstraction_ty
              : [`Int ] Id.t env
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
  module Arith' = struct
    let rec arith_
              : ('var -> 'var -> bool)
             -> 'var
             -> 'var Arith.gen_t
             -> 'var Arith.gen_t
             -> 'var Arith.gen_t =
      fun equal x a a' ->
        match a' with
        | Int _ -> a'
        | Var x' -> if equal x x' then a else a'
        | Op(op, as') -> Op(op, List.map ~f:(arith_ equal x a) as')
    let arith : 'a. 'a Id.t -> Arith.t -> Arith.t -> Arith.t =
      fun x a a' -> arith_ Id.eq {x with ty=`Int} a a'

    let rec formula_
              : ('var -> 'var -> bool)
             -> 'var
             -> 'var Arith.gen_t
             -> ('bvar,'var) Formula.gen_t
             -> ('bvar,'var) Formula.gen_t =
      fun equal x a p ->
        match p with
        | Pred(prim, as') -> Pred(prim, List.map as' ~f:(arith_ equal x a))
        | And ps -> And(List.map ~f:(formula_ equal x a) ps)
        | Or  ps -> Or (List.map ~f:(formula_ equal x a) ps)
        | _ -> p
    let formula : 'a. 'a Id.t -> Arith.t -> Formula.t -> Formula.t =
      fun x a p -> formula_ Id.eq {x with ty = `Int} a p

    let rec abstraction_ty
              : unit Id.t
             -> Arith.t
             -> abstraction_ty
             -> abstraction_ty =
      fun x a sigma ->
        let x = Id.remove_ty x in
        match sigma with
        | TyBool preds ->
            TyBool (List.map ~f:(formula x a) preds)
        | TyArrow (arg,ret) ->
            TyArrow( { arg with ty = abstraction_argty x a arg.ty }
                   , abstraction_ty x a ret)
    and abstraction_argty
          : unit Id.t
         -> Arith.t
         -> abstraction_ty arg
         -> abstraction_ty arg =
      fun x a arg ->
        let x = Id.remove_ty x in
        match arg with
        | TyInt -> TyInt
        | TySigma(sigma) -> TySigma(abstraction_ty x a sigma)
    let abstraction_ty
          : 'a Id.t
         -> Arith.t
         -> abstraction_ty
         -> abstraction_ty =
      fun x a sigma -> abstraction_ty (Id.remove_ty x) a sigma
    let abstraction_argty
          : 'a Id.t
         -> Arith.t
         -> abstraction_ty arg
         -> abstraction_ty arg =
      fun x a arg -> abstraction_argty (Id.remove_ty x) a arg
  end

  module Hflz' = struct
    let rec hflz : 'ty Hflz.t env -> 'ty Hflz.t -> 'ty Hflz.t =
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
                let x_rule =
                  List.find_exn hes ~f:(fun rule -> Id.eq x rule.var)
                in
                (* TODO
                 * このbodyがTyBool型を持っていることは隠れinvariant．
                 * parserで保証されている？ *)
                let vars1, body = Hflz.decompose_abs x_rule.body in
                (vars0@vars1), body
            | vars, body -> vars, body
          in
          let env = IdMap.of_list @@ List.zip_exn vars args in
          hflz env body
      | _ -> invalid_arg "reduce_head"
  end

  module Hfl' = struct
    let rec hfl : Hfl.t env -> Hfl.t -> Hfl.t =
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
  end
end

module Reduce = struct
  module Hfl' = struct
    let rec beta : Hfl.t -> Hfl.t = function
      | Or (phis, k) -> Or (List.map ~f:beta phis, k)
      | And(phis, k) -> And(List.map ~f:beta phis, k)
      | App(phi1, phi2) ->
          begin match beta phi1, beta phi2 with
          | Abs(x, phi1), phi2 -> Subst.Hfl'.hfl (IdMap.of_list [x,phi2]) phi1
          | phi1, phi2 -> App(phi1, phi2)
          end
      | Exists(label, t) -> Exists(label, beta t)
      | Forall(label, t) -> Forall(label, beta t)
      | Abs(x, phi) -> Abs(x, beta phi)
      | phi -> phi
    let rec eta : Hfl.t -> Hfl.t = function
      | Abs(x, (App (phi, Var x')))
          when Id.eq x x' && not (IdSet.mem (Hfl.fvs phi) x) -> phi
      | Abs(x, phi)      -> Abs(x, eta phi)
      | Or (phis, k)     -> Or (List.map ~f:eta phis, k)
      | And(phis, k)     -> And(List.map ~f:eta phis, k)
      | App(phi1, phi2)  -> App(eta phi1, eta phi2)
      | Exists(label, t) -> Exists(label, eta t)
      | Forall(label, t) -> Forall(label, eta t)
      | phi              -> phi
    let beta_eta = eta <<< beta
  end
end

module Simplify = struct
  let rec hfl : ?force:bool -> Hfl.t -> Hfl.t =
    let rec is_true : Hfl.t -> bool =
      fun phi -> match phi with
      | Bool b -> b
      | And(phis, _) -> List.for_all ~f:is_true phis
      | Or (phis, _) -> List.exists  ~f:is_true phis
      | _ -> false
    in
    let rec is_false : Hfl.t -> bool =
      fun phi -> match phi with
      | Bool b -> not b
      | And(phis, _) -> List.exists  ~f:is_false phis
      | Or (phis, _) -> List.for_all ~f:is_false phis
      | _ -> false
    in
    fun ?(force=false) phi ->
      match Reduce.Hfl'.beta_eta phi with
      (* | And(phis, k) when k = `Inserted || force -> *)
      (*     let phis = List.map ~f:hfl phis in *)
      (*     let phis = List.filter ~f:Fn.(not <<< is_true) phis in *)
      (*     begin match phis with *)
      (*     | []    -> Bool true *)
      (*     | [phi] -> phi *)
      (*     | _     -> And(phis, k) *)
      (*     end *)
      (* | Or(phis, k) when k = `Inserted || force -> *)
      (*     let phis = List.map ~f:hfl phis in *)
      (*     let phis = List.filter ~f:Fn.(not <<< is_false) phis in *)
      (*     begin match phis with *)
      (*     | []    -> Bool false *)
      (*     | [phi] -> phi *)
      (*     | _     -> Or(phis, k) *)
      (*     end *)
      | And(phis, k) -> And(List.map ~f:hfl phis, k)(* preserve the structure *)
      | Or (phis, k) -> Or (List.map ~f:hfl phis, k)(* preserve the structure *)
      | Exists(l,phi)  -> Exists(l, hfl ~force phi)
      | Forall(l,phi)  -> Forall(l, hfl ~force phi)
      | Abs(x,phi)     -> Abs(x, hfl ~force phi)
      | App(phi1,phi2) -> App(hfl ~force phi1, hfl ~force phi2)
      | phi -> phi

  let rec formula
            : 'bvar 'avar
            . ('bvar, 'avar) Formula.gen_t
           -> ('bvar, 'avar) Formula.gen_t =
    let rec is_true =
      fun phi -> match phi with
      | Formula.Bool b -> b
      | Formula.And phis -> List.for_all ~f:is_true phis
      | Formula.Or  phis -> List.exists  ~f:is_true phis
      | _ -> false
    in
    let rec is_false =
      fun phi -> match phi with
      | Formula.Bool b -> not b
      | Formula.And phis -> List.exists  ~f:is_false phis
      | Formula.Or  phis -> List.for_all ~f:is_false phis
      | _ -> false
    in
    function
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

