open Hflmc2_util
open Hflmc2_syntax
open Type
module Options = Hflmc2_options.Abstraction
module FpatInterface = FpatInterface

let log_src = Logs.Src.create ~doc:"Predicate Abstraction" "Abstraction"
module Log = (val Logs.src_log log_src)

type env = abstraction_ty IdMap.t

module FormulaMap = Map.Make'(Formula)
type preds_map = (abstracted_ty Id.t) FormulaMap.t

type gamma =
  { env   : env
  ; preds : preds_map
  ; guard : Formula.t (* for optimization only. always [true] for now *)
  }

let pp_env : env Print.t =
  fun ppf env ->
    let compare_id (x,_) (y,_) = compare x.Id.id y.Id.id in
    let item ppf (f,aty) =
      Print.pf ppf "@[<h>%a : %a@]" Print.id f Print.abstraction_ty aty
    in
    Print.pf ppf "@[<v>%a@]"
      (Print.list item)
      (List.sort ~compare:compare_id @@ IdMap.to_alist env)
let pp_preds_map =
  fun ppf preds ->
    let compare_id (_,x) (_,y) = compare x.Id.id y.Id.id in
    let item ppf (f,b) =
      Print.pf ppf "@[<h>%a[%a]@]"
        Print.id b
        Print.formula f
    in
    Print.pf ppf "@[<h>%a@]"
      Print.(list_set item)
      (List.sort ~compare:compare_id @@ FormulaMap.to_alist preds)


let pp_gamma : gamma Print.t =
  fun ppf gamma ->
    Print.pf ppf "%a | %a "
      pp_preds_map gamma.preds
      Print.formula gamma.guard

let return_preds (aty : abstraction_ty) : Formula.t list =
  snd @@ decompose_arrow aty

let merge_types tys =
  let append_preds ps qs =
    List.remove_duplicates ~equal:FpatInterface.(<=>) @@ (ps@qs)
  in Type.merges append_preds tys

let merge_env : env -> env -> env =
  fun env1 env2 ->
    IdMap.merge env1 env2
      ~f:begin fun ~key:_ -> function
      | `Left l -> Some l
      | `Right r -> Some r
      | `Both (l, r) -> Some (merge_types [l;r])
      end

(* For Or and And: (λxs.u1, λxs.u2) -> λxs.f u1 u2 *)
let merge_lambda : int -> (Hfl.t list -> Hfl.t) -> Hfl.t list -> Hfl.t =
  fun len merge phis ->
    let new_vars = List.init len ~f:(fun _ -> Id.gen ATyBool) in
    let rec gather_vars len phi = match phi with
      | _ when len = 0 ->
          ([], phi)
      | Hfl.Abs(x, phi) ->
          let (xs, phi') = gather_vars (len-1) phi in
          (x::xs, phi')
      | _ ->
          let x = Id.gen ATyBool in
          let xs, phi = gather_vars (len-1) (Hfl.App(phi, Var(x))) in
          (x::xs, phi)
    in
    let rename orig_vars phi =
      let map =
        try IdMap.of_alist_exn @@ List.zip_exn
              (List.map ~f:Id.remove_ty orig_vars)
              (List.map ~f:Hfl.mk_var new_vars)
        with _ -> assert false
      in Trans.Subst.Hfl'.hfl map phi
    in
    let phis' = List.map phis ~f:Fn.(uncurry rename <<< gather_vars len) in
    Hfl.mk_abss new_vars (merge phis')

(******************************************************************************)

(* 最初はとりあえず効率を考えないでbacktrackで実装しよう *)
let rec infer_type : env -> simple_ty Hflz.t -> abstraction_ty =
  fun env psi -> match psi with
    | Bool _ -> TyBool []
    | Var x -> IdMap.lookup env x
    | Pred(p,as') -> TyBool [Pred(p,as')]
    | App(psi1, Arith a) ->
        begin match infer_type env psi1 with
        | TyArrow(x, ret_ty) ->
            Trans.Subst.Arith'.abstraction_ty x a ret_ty
        | _ -> assert false
        end
    | App(psi1,_) ->
        begin match infer_type env psi1 with
        | TyArrow(_,ret_ty) -> ret_ty
        | _ -> assert false
        end
    | Abs({ty=TyInt;_} as x,psi) -> TyArrow(x,infer_type env psi)
    | Or(psi1,psi2) | And(psi1,psi2) ->
        let ty1 = infer_type env psi1 in
        let ty2 = infer_type env psi2 in
        merge_types [ty1;ty2]
    | Arith _ -> Fn.fatal "impossible"
    | Abs({ty=TySigma _ty;_} as _x,_psi) -> Fn.todo()

(* Γ |- σ <= σ ↪ φ' で得たφ'にφを適用 *)
let rec abstract_coerce
          : gamma
         -> abstraction_ty
         -> abstraction_ty
         -> Hfl.t
         -> Hfl.t =
  fun gamma sigma sigma' phi ->
    let phi' =
      match sigma, sigma' with (* {{{ *)
      | TyBool ps, TyBool qs ->
          (* filter out predicates already introduced by gamma *)
          let qs0 =
            List.filter qs ~f:begin fun q ->
              not @@ FormulaMap.mem gamma.preds q
            end
          in
          (* xs0 is new vars introduced in phi': phi' is a form of λxs0. ... *)
          let xs0 = List.map qs0 ~f:(fun _ -> Id.gen ~name:"b" ATyBool) in
          let qxs = List.zip_exn qs0 xs0 @ FormulaMap.to_alist gamma.preds in
          let qs,xs = List.unzip qxs in
          let body =
            begin try
              (* Simple case: forall p[i] there exists j_i s.t. p[i] = q[j_i] *)
              let pxs =
                List.map ps ~f:begin fun p -> snd @@
                  List.find_exn qxs ~f:(fun (q,_) -> FpatInterface.(p <=> q))
                end
              in
              Hfl.mk_apps phi (List.map ~f:Hfl.mk_var pxs)
            with Not_found ->
              (* Let ps be P1,...,Pk and qs be Q1,...,Ql.
               * To compute φ, find I ⊆ {1,...,l} and J1,...,Jm ⊆ {1,...,k}
               * such that
               *    ∧ _{i \in I}Qi => ∨ _{h \in 1,...,m}∧ _{j \in Jh} Pj
               * Let
               *    φ'_{I,J1,...,Jm} =
               *      ∧ _{i \in I}b_i ∧
               *      ∧ _{h \in 1,...,m} φ (1 \in Jh) ... (l \in Jh)
               * then φ' is the union of all φ'_{I,J1,...,Jm}.
               * *)
              let l = List.length qs in
              let k = List.length ps in
              let max_ands = !Options.max_ands in
              let max_ors  = !Options.max_ors in
              let one_to_l = List.(range 0 l) in (* to be honest, 0 to l-1 *)
              let one_to_k = List.(range 0 k) in
              let _Is = List.powerset one_to_l in
              let search_space =
                if !Options.exhaustive_search then
                  let _Js =
                    List.filter (List.powerset ~limit:max_ands one_to_k) ~f:
                      begin fun _J ->
                        let ps' = List.(map ~f:(nth_exn ps) _J) in
                        FpatInterface.is_consistent_set ps'
                      end
                  in
                  List.filter (List.powerset ~limit:max_ors _Js)
                      ~f:(fun l -> not (List.is_empty l))
                else [] (* unused (for optimization) *)
              in
              let phi's =
                let _IJs =
                  List.map _Is ~f:begin fun _I ->
                    let qs' = List.(map ~f:(nth_exn qs) _I) in
                    let _Q  = Formula.mk_ands (gamma.guard::qs') in
                    (* Q => \/i(/\Ji) を満たす極大の J1,...,Jh の集合を得る *)
                    let _Jss =
                      if FpatInterface.(_Q ==> Formula.Bool false) then
                        [[one_to_k]] (* /\{P1,...,Pk}が唯一の極大元 *)
                      else if !Options.exhaustive_search then
                        let candidates : (int list list * Formula.t) list =
                          List.filter_map search_space ~f:begin fun _Js ->
                            let pss =
                              List.map _Js ~f:begin fun _J ->
                                List.map _J ~f:begin fun j ->
                                  List.nth_exn ps j end end
                            in
                            let body =
                              Formula.mk_ors @@ List.map ~f:Formula.mk_ands pss
                            in
                            if FpatInterface.(_Q ==> body)
                            then Some (_Js, body)
                            else None
                          end
                        in
                        let (<=) (_,p1) (_,p2) = FpatInterface.(p2 ==> p1) in
                        List.map ~f:fst @@ Fn.maximals' (<=) candidates
                      else if FpatInterface.is_valid _Q then
                        [FpatInterface.min_valid_cores (Array.of_list ps)]
                      else
                        [FpatInterface.strongest_post_cond _Q (Array.of_list ps)]
                    in
                    (_I, _Jss)
                  end
                in
                (* If Jss1=Jss2 and I1⊆ I2, then (I2,Jss2) is redundant *)
                let _IJs = _IJs
                  (* Group by equality of Jss *)
                  |> List.sort ~compare:Fn.(on snd compare)
                  |> List.group ~break:Fn.(on snd (<>))
                  (* Remove I which has its subset in the same group *)
                  |> List.concat_map ~f:Fn.(maximals' (on fst (flip List.subset)))
                in
                List.map _IJs ~f:begin fun (_I,_Jss) ->
                  let conjunctions =
                    List.map _Jss ~f:begin fun _Js ->
                      let mk_var i = Hfl.mk_var (List.nth_exn xs i) in
                      let mk_atom _J =
                        Hfl.mk_apps phi @@
                          List.map one_to_k ~f:begin fun j ->
                            Hfl.Bool (List.mem ~equal:(=) _J j)
                          end
                      in
                      Hfl.mk_ands ~kind:`Inserted
                       @@ List.map _I ~f:mk_var
                        @ List.map _Js ~f:mk_atom
                    end
                  in
                  if Logs.Src.level log_src = Some Logs.Debug then begin (* {{{ *)
                    List.iter _Jss ~f:begin fun _Js ->
                      let pss =
                        List.map _Js ~f:begin fun _J ->
                          List.map _J ~f:begin fun j ->
                            List.nth_exn ps j end end
                      in
                      Log.debug begin fun m -> m ~header:"Coerce" "I = %a,@ J = %a"
                        Print.(list_set formula) List.(map ~f:(nth_exn qs) _I)
                        Print.(list_set (list_set formula)) pss
                      end
                    end
                  end; (* }}} *)
                  Hfl.mk_ors ~kind:`Inserted conjunctions
                end
              in Hfl.mk_ors ~kind:`Inserted phi's
            end
          in Hfl.mk_abss xs0 body
      | TyArrow({ty = TyInt; _} as x, sigma)
      , TyArrow({ty = TyInt; _} as y, sigma') ->
          let sigma =
            Trans.Subst.Arith'.abstraction_ty x (Arith.mk_var y) sigma
          in
          abstract_coerce gamma sigma sigma' phi
      | TyArrow({ty = TySigma sigma1 ; _}, sigma2 )
      , TyArrow({ty = TySigma sigma1'; _}, sigma2') ->
          let x = Id.gen ~name:"q" (Type.abstract sigma1') in
          let phi1x = abstract_coerce gamma sigma1' sigma1 (Var x) in
          Hfl.Abs(x, abstract_coerce gamma sigma2 sigma2' @@ App(phi, phi1x))
      | _ -> assert false
      (*}}}*)
    in
    Log.debug begin fun m -> m ~header:"Term:Coerce"
      "@[<hv 0>%a⊢@;%a@;<1 1>: %a ≺  %a@;<1 0>⇢  %a@]"
        pp_gamma gamma
        Print.hfl phi
        Print.abstraction_ty sigma
        Print.abstraction_ty sigma'
        Print.hfl phi'
    end;
    phi'

let rec abstract_infer
          : gamma
         -> simple_ty Hflz.t
         -> Type.abstraction_ty * Hfl.t =
  fun gamma psi ->
    let (sigma, phi) : Type.abstraction_ty * Hfl.t = match psi with
      (* Var *)
      | Var v ->
          let sigma =
            try
              IdMap.lookup gamma.env v
            with _ -> Fn.fatal @@
              Fmt.strf "Variable %s not found in environment" (Id.to_string v)
            in
          (sigma , Var { v with ty = Type.abstract sigma })
      (* Bool *)
      | Bool b ->
          let sigma = TyBool [] in
          (sigma, Hfl.Bool b)
      (* Pred-Simple *)
      | Pred(p,as') ->
          let sigma = TyBool Formula.[Pred(p,as')] in
          (sigma, Hfl.mk_identity ATyBool)

      (* Abs-Int *)
      | Abs({ty = TyInt; _} as v, psi) ->
          let (sigma, phi) = abstract_infer gamma psi in
          (TyArrow(v, sigma), phi)

      | App(psi, Arith a) ->
          begin match abstract_infer gamma psi with
          | TyArrow({ty = TyInt; _} as x, sigma), phi ->
              (Trans.Subst.Arith'.abstraction_ty x a sigma, phi)
          | _ -> assert false
          end
      | App(psi1, psi2) ->
          begin match abstract_infer gamma psi1 with
          | TyArrow({ty = TySigma sigma'; _}, sigma), phi1 ->
              let preds =
                List.remove_duplicates ~equal:Formula.equal @@
                  List.filter (return_preds sigma)
                    ~f:(not <<< FormulaMap.mem gamma.preds)
              in
              let vars  =
                List.map preds ~f:(fun _ -> Id.gen ~name:"b" ATyBool)
              in
              let preds_map =
                FormulaMap.merge'
                  gamma.preds
                  (FormulaMap.of_alist_exn (List.zip_exn preds vars))
              in
              let gamma = { gamma with preds = preds_map } in
              let phi2 = abstract_check gamma psi2 sigma' in
              let phi =
                Hfl.(mk_abss vars @@
                      mk_apps (App(phi1,phi2))
                        (List.map vars ~f:mk_var))
              in
              (sigma, phi)
          | _ -> assert false
          end

      (* And, Or *)
      | And (psi1,psi2) | Or (psi1,psi2) ->
          let ope,make_ope = match psi with
            | And _ -> `And, Hfl.mk_ands ~kind:`Original
            | Or _  -> `Or,  Hfl.mk_ors  ~kind:`Original
            | _ -> assert false
          in
          let [@warning "-8"] TyBool preds =
            infer_type gamma.env psi
          in
          let vars =
            List.map preds ~f:(fun _ -> Id.gen ~name:"b" ATyBool)
          in
          (* infer_typeでunique up to (<=>) になっているのでexnでよい *)
          let preds_map = FormulaMap.of_alist_exn @@
            List.zip_exn preds vars
          in
          let gamma = { gamma with preds = preds_map } in
          let sigma' = TyBool preds in
          let psi1',psi2' = match psi1,psi2 with
            | Pred(p,as'), _ ->
                let gamma2 =
                  let c = match ope with
                    | `And -> Formula.Pred(p,as')
                    | `Or  -> Formula.(mk_not (Pred(p,as')))
                  in
                  { gamma with guard = Formula.mk_and c gamma.guard }
                in
                abstract_check gamma  psi1 sigma',
                abstract_check gamma2 psi2 sigma'
            | _, Pred(p,as') ->
                let gamma1 =
                  let c = match ope with
                    | `And -> Formula.Pred(p,as')
                    | `Or  -> Formula.(mk_not (Pred(p,as')))
                  in
                  { gamma with guard = Formula.mk_and c gamma.guard }
                in
                abstract_check gamma1 psi1 sigma',
                abstract_check gamma  psi2 sigma'
            | _ ->
                abstract_check gamma psi1 sigma',
                abstract_check gamma psi2 sigma'
          in
          let phi' = Hfl.mk_abss vars @@ make_ope [psi1';psi2']
          in
          (sigma', phi')
      | Abs _ | Arith _ ->
          Print.(print (hflz simple_ty_) psi);
          Fn.fatal "impossible"
          (* NOTE Absはpsiがβ-reduxを持たないという仮定の元でimpossible *)
    in
      let phi = Trans.Simplify.hfl phi in
      Log.debug begin fun m -> m ~header:"Term:Infer"
        "@[<hv 0>%a⊢@;%a@ ==> %a@;<1 1>⇢  %a@]"
          pp_gamma gamma
          Print.(hflz simple_ty_) psi
          Print.abstraction_ty sigma
          Print.hfl phi
      end;
      sigma, phi

and abstract_check : gamma -> simple_ty Hflz.t -> Type.abstraction_ty -> Hfl.t =
  fun gamma psi sigma ->
    let phi : Hfl.t = match psi, sigma with
      | Abs({ty=TyInt;_} as x, psi), TyArrow({ty=TyInt;_} as x', sigma) ->
          let sigma =
            Trans.Subst.Id'.abstraction_ty
              (IdMap.singleton x' {x with ty=`Int}) sigma
          in
          abstract_check gamma psi sigma
      | Abs(x, psi), TyArrow({ty = TySigma sigma'; _}, sigma) ->
          let env = IdMap.add gamma.env x sigma' in
          let x'  = Id.{ x with ty = Type.abstract sigma' } in
          Abs(x', abstract_check {gamma with env} psi sigma)
      | _ ->
          let sigma', phi = abstract_infer gamma psi in
          abstract_coerce gamma sigma' sigma phi
    in
      let phi = Trans.Simplify.hfl phi in
      Log.debug begin fun m -> m ~header:"Term:Check"
        "@[<hv 0>%a⊢@;%a@ <== %a@;<1 1>⇢  %a@]"
          pp_gamma gamma
          Print.(hflz simple_ty_) psi
          Print.abstraction_ty sigma
          Print.hfl phi
      end;
      phi

let abstract_main : env -> simple_ty Hflz.t -> Hfl.t =
  fun env psi ->
    let gamma = { env; preds=FormulaMap.empty; guard=Bool true} in
    let sigma, phi = abstract_infer gamma psi in
    let targs, ps  = decompose_arrow sigma in
    let mk_ty qs   = mk_arrows targs (TyBool qs) in
    let complement = Formula.(mk_not (mk_ors ps)) in
    if FpatInterface.(complement ==> Formula.Bool false)
    then
      phi
      |> abstract_coerce gamma (mk_ty ps) (mk_ty [])
      |> Trans.Simplify.hfl
    else
      let ps' = complement::ps in
      phi
      |> abstract_coerce gamma (mk_ty ps ) (mk_ty ps')
      |> abstract_coerce gamma (mk_ty ps') (mk_ty [])
      |> Trans.Simplify.hfl

let abstract_rule : env -> simple_ty Hflz.hes_rule -> Hfl.hes_rule =
  fun env { var; body; fix } ->
    let gamma = { env; preds=FormulaMap.empty; guard=Bool true} in
    let aty = IdMap.lookup env var in
    let rule' =
      Hfl.{ var  = Id.{ var with ty = Type.abstract aty }
          ; body = abstract_check gamma body aty
          ; fix  = fix
          }
    in
    begin Log.debug @@ fun m -> m ~header:"Nonterminal" "%a"
      Print.hfl_hes_rule rule'
    end;
    rule'

let abstract : env -> simple_ty Hflz.hes -> Hfl.hes =
  fun env hes -> match hes with
    | main::hes ->
        let main' =
          Hfl.{ var  = Id.{ main.var with ty = ATyBool }
              ; body = abstract_main env main.body
              ; fix  = main.fix
              }
        in
        begin Log.debug @@ fun m -> m ~header:"Nonterminal" "%a"
          Print.hfl_hes_rule main'
        end;
        main' :: List.map ~f:(abstract_rule env) hes
    | [] -> assert false

module Int_base = Int_base
