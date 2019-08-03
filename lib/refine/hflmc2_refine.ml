open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type
open Hflmc2_modelcheck

module Log = (val Logs.src_log @@ Logs.Src.create "Refine")
module TraceVar = TraceVar
module HornClause = HornClause

type guard = HornClause.formula list
let empty_guard : guard = []

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

(* NOTE HornClauseにするときにdualを取る
 *
 * HFL
 * S n =v F n (H n)
 * F x g =v g (x + x) \/ x < 0.
 * H y z =v z >= y
 *
 * HoCHC
 * ¬S n    =μ ¬F n (¬H n)
 * ¬F x ¬g =μ ¬g (n + n) /\ x >= 0.
 * ¬H y z  =μ z < y
 *
 * CHC
 * ¬S n   =μ ¬F n
 * ¬F x   =μ ¬g x (x + x) /\ x >= 0.
 * ¬g n w =μ ¬H n w
 * ¬H y z =μ z >= y
 * *)
let gen_HCCS
    :  simple_ty Hflz.hes
    -> Counterexample.normalized
    -> HornClause.t list =
  fun hes cex ->
    let rec go
        :  HornClause.head
        -> reduce_env
        -> guard
        -> TraceExpr.t
        -> Counterexample.normalized option
        -> HornClause.t list =
      fun head reduce_env guard expr cex ->
        Log.debug begin fun m -> m ~header:"gen_HCCS"
          "@[<v>@[<h 2>head : %a@]@,@[<2>expr : %a@]@,@[<2>guard: %a@]@,@[<2>cex  : %a@]@]"
            HornClause.pp_hum_head head
            TraceExpr.pp_hum expr
            Print.(list_comma HornClause.pp_hum_formula) guard
            Print.(option ~none:(fun ppf () -> string ppf "None")
              Counterexample.pp_hum_normalized) cex
        end;
        match expr, cex with
        | (Bool true | And []), _
        | (App _ | Var _)     , None ->
            let pvs  = [] in
            let phi  = [Formula.Bool false] in
            let body = HornClause.{ pvs; phi } in
            [{ head; body }]
        | (Bool false | Or []), _ ->
            let body = HornClause.{ phi=guard; pvs =[] } in
            [{ head; body }]
        | Pred (pred, as'), _ ->
            let pvs  = [] in
            let phi  = Formula.(mk_not @@ mk_pred pred as') :: guard in
            let body = HornClause.{ pvs; phi } in
            [{ head; body }]
        | And psis, Some (And (_,i,c)) ->
            go head reduce_env guard (List.nth_exn psis i) (Some c)
        | And _psis, (None | Some False) ->
            (* NOTE
             * dualを取るからorになる．
             * body1 \/ body2 => head は
             * body1 => head; body2 => head と同値 *)
            (* List.concat_map _psis ~f:(go head reduce_env preconds -$- None) *)
            (* No! Fpat can solve only linear CHC! *)
            let pvs  = [] in
            let phi  = [Formula.Bool false] in
            let body = HornClause.{ pvs; phi } in
            [{ head; body }]
        | Or psis, _ ->
            (* XXX dirty hack *)
            let hccss =
              match cex with
              | Some (Or cs) ->
                  List.map2_exn psis cs ~f:begin fun psi c ->
                    go head reduce_env guard psi (Some c)
                  end
              | Some False | None ->
                  List.map psis ~f:begin fun psi ->
                    go head reduce_env guard psi None
                  end
              | _ -> assert false
            in
            let hc_s, hcs_s =
              List.unzip @@ List.filter_map hccss ~f:begin function
              | [] -> None
              | hc::hcs -> Some (hc, hcs)
              end
            in
            let hc = (* merge bodies *)
              let body =
                let init = HornClause.{ pvs = []; phi = [] } in
                List.fold_left hc_s ~init ~f:begin fun body hc ->
                  assert (HornClause.equal_head head hc.head);
                  HornClause.
                    { pvs = List.remove_consecutive_duplicates ~equal:HornClause.equal_pred_var @@
                            List.sort ~compare:HornClause.compare_pred_var (body.pvs @ hc.body.pvs)
                    ; phi = List.filter ~f:(not <<< HornClauseSolver.is_valid)
                                @@ body.phi @ hc.body.phi
                    }
                end
              in HornClause.{ head; body }
            in
            Log.debug begin fun m -> m ~header:"Or:MergeCHC" "@[<v>%a@,⇓@,%a@]"
              (Print.list HornClause.pp_hum) hc_s
              HornClause.pp_hum hc
            end;
            hc :: List.concat hcs_s
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
                      next_expr, empty_guard
                in

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

                let current_guard =
                  List.filter ~f:(not <<< HornClauseSolver.is_valid) bind_constr
                    @ guard
                in
                Log.debug begin fun m -> m ~header:"CurrentGuard" "@[<v>%a@]"
                  Print.(list HornClause.pp_hum_formula) current_guard
                end;

                (* Qn(n), m=n |= ¬PS(n) <= ¬PTwice(m) *)
                let hcc =
                  let pvs = HornClause.mk_pred_var aged :: [] in
                  let body = HornClause.{ phi = current_guard; pvs } in
                  HornClause.{ body; head }
                in
                Log.debug begin fun m -> m ~header:"CHC" "%a"
                  HornClause.pp_hum hcc
                end;

                let _, bind_with_guard =
                  List.fold_left bind ~init:(guard, []) ~f:
                    begin fun (guard, rev_acc) (x,e) ->
                      let b = x, (e, guard) in
                      let guard =
                        match TraceVar.type_of x, e with
                        | TyInt, Arith a ->
                            Formula.mk_pred Eq [ Arith.mk_var' (`I x); a ] :: guard
                        | _ ->
                            guard
                      in
                      (guard, b::rev_acc)
                    end
                in
                Log.debug begin fun m -> m ~header:"NewBind" "@[<v>%a@]"
                  Print.(list ~sep:cut @@
                    pair ~sep:(fun ppf () -> string ppf " --> ")
                      TraceVar.pp_hum
                      (fun ppf (e,g) ->
                         pf ppf "@[<2>%a@] under %a"
                           TraceExpr.pp_hum e
                           Print.(list HornClause.pp_hum_formula) g))
                    (List.rev bind_with_guard)
                end;

                let next_reduce_env =
                  TraceVar.Map.merge'
                    reduce_env
                    (TraceVar.Map.of_alist_exn bind_with_guard)
                in

                let int_vars =
                  List.filter_map vars ~f:begin fun x ->
                    match TraceVar.type_of x with
                    | TyInt -> Some x
                    | _     -> None
                  end
                in

                let hccs = go (Some (PredVar aged)) next_reduce_env next_guard next_expr cex in
                hcc::hccs
            | Abs(x, phi) ->
                let [@warning "-8"] e::es = args in
                let phi' = TraceExpr.beta_head x e phi in
                let expr = TraceExpr.mk_apps phi' es in
                go head reduce_env guard expr cex
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
    go None TraceVar.Map.empty empty_guard main (Some cex)


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

