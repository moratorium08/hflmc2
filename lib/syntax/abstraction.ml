
open Hflmc2_util
open Type

type env = abstraction_ty IdMap.t

(* For Or and And: (λxs.u1, λxs.u2) -> λxs.f u1 u2 *)
let merge_lambda : int -> (Hfl.t -> Hfl.t -> Hfl.t) -> Hfl.t -> Hfl.t -> Hfl.t =(*{{{*)
  fun len merge t1 t2 ->
    let new_vars = List.init len ~f:(fun _ -> Id.gen ATyBool) in

    let rec gather_vars len t = match t with
      | _ when len = 0 ->
          ([], t)
      | Hfl.Abs(x, t) ->
          let (xs, u) = gather_vars (len-1) t in
          (x::xs, u)
      | _ ->
          let x = Id.gen ATyBool in
          let (xs, u) = gather_vars (len-1) (Hfl.App(t, Var(x))) in
          (x::xs, u)
    in

    let rename orig_vars t =
      let map =
        try IdMap.of_alist_exn @@ List.zip_exn
              (List.map ~f:Id.remove_ty orig_vars)
              (List.map ~f:(fun z -> Hfl.Var z) new_vars)
        with
          | Invalid_argument _ -> assert false
          | _ -> assert false
      in
      Hfl.subst map t
    in

    let u1' = Fn.uncurry rename @@ gather_vars len t1 in
    let u2' = Fn.uncurry rename @@ gather_vars len t2 in
    List.fold_right new_vars ~init:(merge u1' u2') ~f:(fun z t -> Hfl.Abs(z, t))
(*}}}*)

(* Γ |- σ <= σ ↪ φ' で得たφ'にφを適用 *)
let rec abstract_coerce : env -> abstraction_ty -> abstraction_ty -> Hfl.t -> Hfl.t =
  fun env sigma sigma' phi -> match sigma, sigma' with
    | TyBool ps, TyBool qs ->
        begin try
          (* Simple case: forall p[i], there exists j_i s.t. p[i] = q[j_i] *)
          let xs = List.init (List.length qs) ~f:(fun _ -> Id.gen ATyBool) in
          (* x[j] is a variable for q[j] *)
          let qxs = Fn.assert_no_exn @@ fun _ -> List.zip_exn qs xs in
          (* gather x[j_i] *)
          let pxs = List.map ps ~f:(fun p -> snd @@ List.find_exn qxs ~f:(fun (q,_) -> p=q)) in
          let body = List.fold_left pxs ~init:phi ~f:(fun t x -> Hfl.(App (t, Var x))) in
          List.fold_right xs ~init:body ~f:(fun x t -> Hfl.Abs(x, t))
        with
          | Not_found ->
              Fn.todo ~info:"Coercion: base case" ()
        end
    | TyArrow({ty = TyInt; _}, sigma), TyArrow({ty = TyInt; _}, sigma') ->
        abstract_coerce env sigma sigma' phi
    | TyArrow({ty = TySigma sigma1 ; _}, sigma2 )
    , TyArrow({ty = TySigma sigma1'; _}, sigma2') ->
        let f = Id.gen ~name:"ac_f" (Type.abstract sigma) in
        let x = Id.gen ~name:"ac_x" (Type.abstract sigma1') in
        let phi1x = abstract_coerce env sigma1' sigma1 (Var x) in
        abstract_coerce env sigma2 sigma2' @@ App(Var f, phi1x)
    | _ -> assert false

let rec abstract_infer : env -> simple_ty Hflz.t -> Type.abstraction_ty * Hfl.t =
  fun env psi -> match psi with
  (* Var *)
  | Var v ->
      let sigma = try IdMap.lookup env v with _ -> assert false in
      (sigma , Var { v with ty = Type.abstract sigma })
  (* Bool *)
  | Bool b ->
      let sigma = TyBool Formula.[Bool b] in
      (sigma, Hfl.identity ATyBool)
  (* Pred-Simple *)
  | Pred(p,as') ->
      let sigma = TyBool Formula.[Pred(p,as')] in
      (sigma, Hfl.identity ATyBool)

  (* Abs-Int *)
  | Abs({ty = TyInt; _} as v, psi) ->
      let (sigma, phi) = abstract_infer env psi in
      (TyArrow(v, sigma), phi)

  | App(psi, Arith a) ->
      begin match abstract_infer env psi with
      | TyArrow({ty = TyInt; _} as x, sigma), phi ->
          (Subst.Arith.abstraction_ty x a sigma, phi)
      | _ -> assert false
      end
  | App(psi1, psi2) ->
      begin match abstract_infer env psi1 with
      | TyArrow({ty = TySigma sigma'; _}, sigma), phi1 ->
          let phi2 = abstract env psi2 sigma' in
          (sigma, App(phi1, phi2))
      | _ -> assert false
      end

  (* And, Or *)
  | And(psi1,psi2) | Hflz.Or(psi1,psi2) ->
      let make_ope = match psi with
        | And _ -> fun x y -> Hfl.And(x,y)
        | Or _  -> fun x y -> Hfl.Or (x,y)
        | _     -> assert false
      in
      begin match abstract_infer env psi1, abstract_infer env psi2 with
      | (TyBool preds1, phi1), (TyBool preds2, phi2) ->
          let preds' = List.remove_consecutive_duplicates
                        (List.append preds1 preds2)
                        ~equal:Formula.equal
          in
          let sigma = TyBool preds' in
          let phi1' = abstract_coerce env (TyBool preds1) sigma phi1 in
          let phi2' = abstract_coerce env (TyBool preds2) sigma phi2 in
          let phi   = merge_lambda (List.length preds') make_ope phi1' phi2' in
          (sigma, phi)
      | _ -> assert false
      end

  | Fix(x, psi, Greatest) ->
      let sigma = try IdMap.lookup env x with _ -> assert false in
      let phi = abstract env psi sigma in
      (sigma, phi)

  | Exists _ | Forall _ | Fix(_,_,Least) -> assert false (* unimplemented *)
  | Abs _ | Arith _ -> assert false (* impossible *)
      (* NOTE Absはpsiがβ-reduxを持たないという仮定の元でimpossible *)

and abstract : env -> simple_ty Hflz.t -> Type.abstraction_ty -> Hfl.t =
  fun env psi sigma -> match psi, sigma with
    | Abs(x, psi), TyArrow({ty = TySigma sigma'; _}, sigma) ->
        let env' = IdMap.add env x sigma' in
        abstract env' psi sigma
    | _ ->
        let sigma', phi = abstract_infer env psi in
        abstract_coerce env sigma' sigma phi

