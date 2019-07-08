open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type
open Hflmc2_abstraction
open Hflmc2_modelcheck

module Log = (val Logs.src_log @@ Logs.Src.create "Refine")

type guard = HornClause.body
type reduce_env = TraceExpr.t TraceVar.Map.t

let rec approximate
    :  simple_ty Hflz.hes
    -> reduce_env
    -> TraceExpr.t
    -> Counterexample.normalized option
    -> HornClause.formula =
  fun hes reduce_env expr cex -> match expr, cex with
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
        | Var ({ var = Nt { orig; _ } as tv; _ } as aged) ->
            let rule = List.find_exn hes ~f:(fun r -> Id.eq r.var orig) in
            let orig_vars, orig_body = Hflz.decompose_abs rule.body in
            let vars   = TraceVar.mk_childlen aged in
            let rename = IdMap.of_list @@ List.zip_exn orig_vars vars in
            let body   = TraceExpr.of_hflz hes rename orig_body in
            let bind   = TraceVar.Map.of_alist_exn @@ List.zip_exn vars args in
            let expr   = TraceExpr.subst bind body in
            approximate hes reduce_env expr (Some c)
        | Var ({ var = Local _ as tv; _ } as aged) ->
            let head = TraceVar.Map.find_exn reduce_env tv in
            let expr = TraceExpr.mk_apps head args in
            approximate hes reduce_env expr (Some c)
        | _ -> assert false
        end
    | (App _| Var _), None -> Bool true
    | Arith _, _ -> assert false
    | Exists _, _ | Forall _, _ -> Fn.todo()
    | _ -> assert false

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
    let [@warning "-27-39"] rec go
        :  HornClause.head
        -> reduce_env
        -> TraceExpr.t
        -> Counterexample.normalized option
        -> HornClause.t list =
      fun head reduce_env expr cex ->
        Log.debug begin fun m -> m ~header:"gen_HCCS"
          "@[<v>@[<h 2>head: %a@]@,@[<2>expr: %a@]@]"
            HornClause.pp_hum_head head
            TraceExpr.pp_hum expr
        end;
        match expr, cex with
        | (Bool true | And []), _ ->
            let pvs  = [] in
            let phi  = Formula.Bool false in
            let body = HornClause.{ pvs; phi } in
            [{ head; body }]
        | (Bool false | Or []), _ ->
            let pvs  = [] in
            let phi  = Formula.Bool true in
            let body = HornClause.{ pvs; phi } in
            [{ head; body }]
        | Pred (pred, as'), _ ->
            let pvs  = [] in
            let phi = Formula.(mk_not @@ mk_pred pred as') in
            let body = HornClause.{ pvs; phi } in
            [{ head; body }]
        | And psis, Some (And (_,i,c)) ->
            go head reduce_env (List.nth_exn psis i) (Some c)
        | And psis, (None | Some False) ->
            (* NOTE
             * dualを取るからorになる．
             * body1 \/ body2 => head は
             * body1 => head; body2 => head と同値 *)
            List.concat_map psis ~f:(go head reduce_env -$- None)
        | Or psis, _ ->
            (* XXX dirty hack *)
            let hccss =
              match cex with
              | Some (Or cs) ->
                  List.map2_exn psis cs ~f:begin fun psi c ->
                    go head reduce_env psi (Some c)
                  end
              | Some False | None ->
                  List.map psis ~f:begin fun psi ->
                    go head reduce_env psi None
                  end
              | _ -> assert false
            in
            let hc_s, hcs_s =
              List.unzip @@ List.map hccss ~f:begin function
              | [] -> assert false
              | hc::hcs -> (hc, hcs)
              end
            in
            let hc = (* merge bodies *)
              let body =
                let init = HornClause.{ pvs = []; phi = Bool true } in
                List.fold_left hc_s ~init ~f:begin fun body hc ->
                  assert (HornClause.equal_head head hc.head);
                  HornClause.
                    { pvs = body.pvs @ hc.body.pvs
                    ; phi = Simplify.formula @@ Formula.mk_and body.phi hc.body.phi
                    }
                end
              in HornClause.{ head; body }
            in
            hc :: List.concat hcs_s
        | (App _| Var _), Some _ ->
            let expr_head, args = TraceExpr.decompose_app expr in
            begin match expr_head with
            | Var ({ var = Nt { orig; _ } as tv; age } as aged) ->
                (* assume args = [n; H n] *)
                (* F x g = g (x + 1) *)
                let rule = List.find_exn hes ~f:(fun r -> Id.eq r.var orig) in
                (* [x;g], g (x + 1) *)
                let orig_vars, orig_body = Hflz.decompose_abs rule.body in
                (* [F.x; F.g] *)
                let vars   = TraceVar.mk_childlen aged in
                (* x -> F.x; g -> F.g *)
                let rename = IdMap.of_list @@ List.zip_exn orig_vars vars in
                (* F.g (F.x + 1) *)
                let new_expr = TraceExpr.of_hflz hes rename orig_body in
                (* F.x -> n; F.g -> H n *)
                let bind   = List.zip_exn vars args in
                Log.debug begin fun m -> m ~header:"NewBind" "@[<v>%a@]"
                  Print.(list ~sep:cut @@
                    pair ~sep:(fun ppf _ -> string ppf " => ")
                      TraceVar.pp_hum
                      (fun ppf -> pf ppf "@[<2>%a@]" @@
                          TraceExpr.pp_hum))
                    bind
                end;

                let hc =
                  let body =
                    let head_bind = match head with
                      | Some (PredVar { var = Local{ fvs; _ }; _}) ->
                          List.map fvs ~f:begin fun fv ->
                            fv, TraceVar.Map.find_exn reduce_env fv
                          end
                      | _ -> []
                    in
                    let int_bind =
                      List.filter_map (bind@head_bind) ~f:begin fun (tv, e) ->
                        match TraceVar.type_of tv, e with
                        | TyInt, Arith a ->
                            let f : HornClause.formula =
                              Formula.mk_pred Eq [ Arith.mk_var' (`I tv); a ]
                            in Some f
                        | TyInt, Var a ->
                            let f : HornClause.formula =
                              Formula.mk_pred Eq [ Arith.mk_var' (`I tv)
                                                 ; Arith.mk_var' (`I a.var) ]
                            in Some f
                        | _ -> None
                      end
                    in
                    HornClause.{ pvs = [PredVar aged]
                               ; phi = Simplify.formula @@ Formula.mk_ands int_bind }
                  in
                    HornClause.{ head; body }
                in
                Log.debug begin fun m -> m ~header:"CHC" "%a"
                  HornClause.pp_hum hc
                end;
                let new_reduce_env =
                  TraceVar.Map.merge reduce_env
                    @@ TraceVar.Map.of_alist_exn bind
                in
                hc :: go (Some (PredVar aged)) new_reduce_env new_expr cex
            | Var ({ var = Local _ as tv; age } as aged) ->
                let vars = TraceVar.mk_childlen aged in
                let bind = List.zip_exn vars args in
                Log.debug begin fun m -> m ~header:"NewBind" "@[<v>%a@]"
                  Print.(list ~sep:cut @@
                    pair ~sep:(fun ppf _ -> string ppf " => ")
                      TraceVar.pp_hum
                      (fun ppf -> pf ppf "@[<2>%a@]" @@
                          TraceExpr.pp_hum))
                    bind
                end;
                let hc =
                  let body =
                    let head_bind = match head with
                      | Some (PredVar { var = Local{ fvs; _ }; _}) ->
                          List.map fvs ~f:begin fun fv ->
                            fv, TraceVar.Map.find_exn reduce_env fv
                          end
                      | _ -> []
                    in
                    let int_bind =
                      List.filter_map (bind@head_bind) ~f:begin fun (tv, e) ->
                        match TraceVar.type_of tv, e with
                        | TyInt, Arith a ->
                            let f : HornClause.formula =
                              Formula.mk_pred Eq [ Arith.mk_var' (`I tv); a ]
                            in Some f
                        | _ -> None
                      end
                    in
                    HornClause.{ pvs = [PredVar aged]
                               ; phi = Simplify.formula @@ Formula.mk_ands int_bind }
                  in
                    HornClause.{ head; body }
                in
                Log.debug begin fun m -> m ~header:"CHC" "%a"
                  HornClause.pp_hum hc
                end;

                let new_expr =
                  TraceExpr.mk_apps
                    (TraceVar.Map.find_exn reduce_env tv)
                    (List.map vars ~f:(TraceExpr.mk_var <<< TraceVar.gen_aged))
                in
                let new_reduce_env =
                  TraceVar.Map.merge reduce_env
                    @@ TraceVar.Map.of_alist_exn bind
                in
                hc :: go (Some (PredVar aged)) new_reduce_env new_expr cex
            | _ ->

                Print.print TraceExpr.pp expr_head;
                assert false
            end
        | (App _| Var _), None -> []
        | Arith _, _ -> assert false
        | Exists _, _ | Forall _, _ -> Fn.todo()
        | _ -> assert false
    in
    let main =
      Hflz.main_symbol hes
      |> TraceVar.mk_nt
      |> TraceVar.gen_aged
      |> TraceExpr.mk_var
    in
    go None TraceVar.Map.empty main (Some cex)

(* TODO hesはλ-liftingしておく *)
(* TODO feasibility check *)
let run : simple_ty Hflz.hes -> Counterexample.normalized -> Hflmc2_abstraction.env =
  fun hes cex ->
    TraceVar.reset_counters();
    let hccs = gen_HCCS hes cex in
    Log.debug begin fun m -> m ~header:"HCCS" "@[<v>%a@]"
      (Print.list HornClause.pp_hum) hccs
    end;
    HornClauseSolver.solve hes hccs

