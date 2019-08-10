open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type
open Hflmc2_modelcheck

module Log = (val Logs.src_log @@ Logs.Src.create "Refine")
module TraceVar = TraceVar
module HornClause = HornClause

type guard = HornClause.body
let empty_guard : guard = { pvs = []; phi = [] }

(* [(tv, (e, guard)) \in reduce_env] means that
 * `when [tv] was bound to [e], [guard] holded`.
 * *)
type reduce_env = (TraceExpr.t * guard) TraceVar.Map.t

let rec approximate
    :  simple_ty Hflz.hes
    -> reduce_env
    -> TraceExpr.t
    -> Counterexample.normalized option
    -> HornClause.formula =
(* {{{ *)
  fun hes reduce_env expr cex ->
    (* Log.debug begin fun m -> m ~header:"Approximate" *)
    (*   "@[<2>%a@]" *)
    (*     TraceExpr.pp_hum expr *)
    (* end; *)
    match expr, cex with
    | (Bool true | And []), _ -> Bool true
    | (Bool false | Or []), _ -> Bool false
    | Pred (op,as'), _ -> Pred (op, as')
    | And exprs, Some (And (_,i,c)) ->
        approximate hes reduce_env (List.nth_exn exprs i) (Some c)
    | And exprs, (None | Some False) ->
        let fs = List.map exprs ~f:(approximate hes reduce_env -$- None) in
        Formula.mk_ands fs
    | Or exprs, Some (Or cs) ->
        Formula.mk_ors
          (List.map2_exn exprs cs
             ~f:(fun expr c -> approximate hes reduce_env expr (Some c)))
    | Or exprs, (None | Some False) ->
        Formula.mk_ors
          (List.map exprs
             ~f:(approximate hes reduce_env -$- None))
    | (App _| Var _), Some c ->
        let head, args = TraceExpr.decompose_app expr in
        begin match head with
        | Var (`I (Nt { orig; _ } as tv)) ->
            let rule = List.find_exn hes ~f:(fun r -> Id.eq r.var orig) in
            let orig_vars, orig_body = Hflz.decompose_abs rule.body in
            let aged   = TraceVar.gen_aged tv in
            let vars   = TraceVar.mk_childlen aged in
            let rename = IdMap.of_list @@ List.zip_exn orig_vars vars in
            let body   = TraceExpr.Make.hflz hes rename orig_body in
            let bind   = TraceVar.Map.of_alist_exn @@ List.zip_exn vars args in
            let expr   = TraceExpr.subst bind body in
            approximate hes reduce_env expr (Some c)
        | Var (`I (Local _ as tv)) ->
            let head, _ = TraceVar.Map.find_exn reduce_env tv in
            let expr = TraceExpr.mk_apps head args in
            approximate hes reduce_env expr (Some c)
        | Abs(x, phi) ->
            let [@warning "-8"] e::es = args in
            let phi' = TraceExpr.beta_head x e phi in
            let expr = TraceExpr.mk_apps phi' es in
            approximate hes reduce_env expr (Some c)
        | _ -> assert false
        end
    | (App _| Var _), None -> Bool true
    | Arith _, _ -> assert false
    | Exists _, _ | Forall _, _ -> Fn.todo()
    | _ -> assert false
(* }}} *)

let is_feasible : simple_ty Hflz.hes -> Counterexample.normalized -> bool =
(* {{{ *)
  fun hes cex ->
    TraceVar.reset_counters();
    let main =
      let head =
        Hflz.main_symbol hes
        |> TraceVar.mk_nt
      in
      let args = TraceVar.mk_childlen TraceVar.{ var = head; age = 0 } in
      TraceExpr.(mk_apps (mk_var head) (List.map args ~f:mk_var))
    in
    let approx = Trans.Simplify.formula @@
      approximate hes TraceVar.Map.empty main (Some cex)
    in
    Log.debug begin fun m -> m ~header:"Expansion" "%a"
      HornClause.pp_hum_formula approx
    end;
    not @@ HornClauseSolver.is_valid approx
(* }}} *)

let gen_HCCS
    :  simple_ty Hflz.hes
    -> Counterexample.normalized
    -> HornClause.t list =
  fun hes cex ->
    let rec go
        :  reduce_env
        -> guard
        -> HornClause.pred_var option
        -> TraceExpr.t
        -> Counterexample.normalized option
        -> HornClause.t list =
      fun reduce_env guard pv expr cex ->
        Log.debug begin fun m -> m ~header:"gen_HCCS"
          "@[<v>@[<2>expr : %a@]@,@[<2>guard: %a@]@,@[<2>pv   : %a@]@,@[<2>cex  : %a@]@]"
            TraceExpr.pp_hum expr
            HornClause.pp_hum_body guard
            Print.(option HornClause.pp_hum_pred_var) pv
            Print.(option ~none:(fun ppf () -> string ppf "None")
              Counterexample.pp_hum_normalized) cex
        end;
        match expr, cex with
        | (Bool true | And []), _
        | (App _ | Var _)     , None
        | (And _ | Or _)      , (None | Some False) ->
            []
        | (Bool false | Or []), _ ->
            [{ head=None; body=guard }]
        | Pred (pred, as'), _ ->
            let body = guard
              |> HornClause.append_phi Formula.[mk_not @@ mk_pred pred as']
              |> HornClause.append_pvs Option.(to_list pv)
            in
            [{ head=None; body }]
        | And psis, Some (And (_,i,c)) ->
            go reduce_env guard pv (List.nth_exn psis i) (Some c)
        | Or [psi1;psi2], Some (Or [c1;c2]) ->
            let _ = psi1, psi2, c1, c2 in
            (* guard => P_psi1 \/ P_psi2 *)
            (* let [@warning "-8"] hcc1::hccs1  = go reduce_env guard psi1 (Some c1) in *)
            (* let [@warning "-8"] hcc2::hccs2  = go reduce_env guard psi2 (Some c2) in *)
            (* let p1 = List.hd_exn hcc1.body.pvs in *)
            (* let p2 = List.hd_exn hcc1.body.pvs in *)
            (* Log.err begin fun m -> m "@[<v>%a@,%a@]" *)
            (*   HornClause.pp_hum_pred_var p1 *)
            (*   HornClause.pp_hum_pred_var p2 *)
            (* end; *)
            Fn.todo ~info:"Or" ()
        | Or _, _ ->
            Fn.todo ~info:"impossible? 3 or more disjunctions" ()
        | (App _| Var _), Some _ ->
            let expr_head, args = TraceExpr.decompose_app expr in
            begin match expr_head with
            | Var (`I tv) ->
                let aged = TraceVar.gen_aged tv in
                let vars = TraceVar.mk_childlen aged in
                let bind = List.zip_exn vars args in
                let next_expr, next_guard =
                  match tv with
                  | Local _ ->
                      Pair.first
                        (TraceExpr.mk_apps -$-
                          (List.map vars ~f:(TraceExpr.mk_var)))
                        (TraceVar.Map.find_exn reduce_env tv)
                  | Nt { orig; _} ->
                      let rule = List.find_exn hes ~f:(fun r -> Id.eq r.var orig) in
                      let orig_vars, orig_body = Hflz.decompose_abs rule.body in
                      let rename = IdMap.of_list @@ List.zip_exn orig_vars vars in
                      let next_expr = TraceExpr.Make.hflz hes rename orig_body in
                      next_expr, guard
                in
                Log.debug begin fun m -> m ~header:"Guard" "@[<v>%a@]"
                  HornClause.pp_hum_body guard
                end;


                let bind_constr =
                  List.filter_map bind ~f:begin fun (x, e) ->
                    match TraceVar.type_of x, e with
                    | TyInt, Arith a ->
                        let f : HornClause.formula =
                          Formula.mk_pred Eq [ Arith.mk_var' (`I x); a ]
                        in Some f
                    | _ -> None
                  end
                in
                Log.debug begin fun m -> m ~header:"BindConstr" "@[<v>%a@]"
                  (Print.list HornClause.pp_hum_formula) bind_constr
                end;

                let current_guard = guard
                  |> HornClause.append_phi
                      (List.filter ~f:(not <<< HornClauseSolver.is_valid) bind_constr)
                  |> HornClause.append_pvs
                      (Option.to_list pv)
                in
                Log.debug begin fun m -> m ~header:"CurrentGuard" "@[<v>%a@]"
                  HornClause.pp_hum_body current_guard
                end;

                let hcc =
                  let head = Some (HornClause.mk_pred_var aged) in
                  HornClause.{ body=current_guard; head }
                in
                Log.debug begin fun m -> m ~header:"CHC" "%a"
                  HornClause.pp_hum hcc
                end;

                let _, bind_with_guard =
                  let init_guard =
                    HornClause.(append_pvs [mk_pred_var aged] guard)
                  in
                  List.fold_left bind ~init:(init_guard, []) ~f:
                    begin fun (g, rev_acc) (x,e) ->
                      let b, g' =
                        match TraceVar.type_of x, e with
                        | TyInt, Arith a ->
                            let b  = (x, (e, empty_guard)) in
                            let g' =
                              HornClause.
                              { pvs = g.pvs
                              ; phi = Formula.mk_pred Eq [ Arith.mk_var' (`I x); a ] :: g.phi
                              }
                            in b, g'
                        | _ ->
                            (x, (e, g)), g
                      in
                      (g', b::rev_acc)
                    end
                in
                Log.debug begin fun m -> m ~header:"NewBind" "@[<v>%a@]"
                  Print.(list ~sep:cut @@
                    pair ~sep:(fun ppf () -> string ppf " --> ")
                      TraceVar.pp_hum
                      (fun ppf (e,g) ->
                         pf ppf "@[<2>%a@] under %a"
                           TraceExpr.pp_hum e
                           HornClause.pp_hum_body g))
                    (List.rev bind_with_guard)
                end;

                let next_reduce_env =
                  TraceVar.Map.merge'
                    reduce_env
                    (TraceVar.Map.of_alist_exn bind_with_guard)
                in
                let next_pv = Some (HornClause.mk_pred_var aged) in

                hcc :: go next_reduce_env next_guard next_pv next_expr cex
            | Abs(x, phi) ->
                let [@warning "-8"] e::es = args in
                let phi' = TraceExpr.beta_head x e phi in
                let expr = TraceExpr.mk_apps phi' es in
                go reduce_env guard pv expr cex
            | _ ->
                Print.print TraceExpr.pp_hum expr_head;
                assert false
            end
        | Arith _, _ -> assert false
        | Exists _, _ | Forall _, _ -> Fn.todo()
        | _ -> assert false
    in
    TraceVar.reset_counters();
    let main, _main_args =
      let head =
        Hflz.main_symbol hes
        |> TraceVar.mk_nt
      in
      let args = TraceVar.mk_childlen TraceVar.{ var = head; age = 0 } in
      TraceExpr.(mk_apps (mk_var head) (List.map args ~f:mk_var)), args
    in
    go TraceVar.Map.empty empty_guard None main (Some cex)


type result = [ `Feasible | `Refined of Hflmc2_abstraction.env ]

let run
     : simple_ty Hflz.hes
    -> Counterexample.normalized
    -> Hflmc2_abstraction.env
    -> result =
  fun hes cex old_gamma ->
    if is_feasible hes cex then
      `Feasible
    else
      let hccs = gen_HCCS hes cex in
      Log.debug begin fun m -> m ~header:"HCCS" "@[<v>%a@]"
        (Print.list HornClause.pp_hum) hccs
      end;
      let new_gamma = HornClauseSolver.solve hes hccs in
      `Refined (Hflmc2_abstraction.merge_env old_gamma new_gamma)

