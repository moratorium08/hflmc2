open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type
open Hflmc2_modelcheck

let log_src = Logs.Src.create "Refine"
module Log = (val Logs.src_log log_src)

let with_logs_disabled f =
  let level = Logs.Src.level log_src in
  Logs.Src.set_level log_src None;
  let r = f () in
  Logs.Src.set_level log_src level;
  r
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
    -> Counterexample.normalized
    -> HornClause.formula =
(* {{{ *)
  fun hes reduce_env expr cex ->
    Log.debug begin fun m -> m ~header:"Approximate"
      "@[<v>@[<2>%a@]@,%a@]"
        TraceExpr.pp_hum expr
        Counterexample.pp_hum_normalized cex
    end;
    match expr, cex with
    | Bool true, _ -> Bool true
    | Bool false, _ -> Bool false
    | Pred (op,as'), _ -> Pred (op, as')
    | And (expr1,_), AndL c ->
        approximate hes reduce_env expr1 c
    | And (_,expr2), AndR c ->
        approximate hes reduce_env expr2 c
    | And _, False ->
        Log.err (fun m -> m ~header:"approximate:And" "impossible?");
        assert false
    | Or (expr1,expr2), Or (c1,c2) ->
        Formula.mk_ors
          [ approximate hes reduce_env expr1 c1
          ; approximate hes reduce_env expr2 c2
          ]
    | Or _, False ->
        Log.err (fun m -> m ~header:"approximate:Or" "impossible?");
        assert false
        (* Formula.mk_ors *)
        (*   (List.map exprs *)
        (*      ~f:(approximate hes reduce_env -$- None)) *)
    | (App _| Var _), c ->
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
            approximate hes reduce_env expr c
        | Var (`I (Local _ as tv)) ->
            let head, _ = TraceVar.Map.find_exn reduce_env tv in
            let expr = TraceExpr.mk_apps head args in
            approximate hes reduce_env expr c
        | Abs(x, phi) ->
            let [@warning "-8"] e::es = args in
            let phi' = TraceExpr.beta_head x e phi in
            let expr = TraceExpr.mk_apps phi' es in
            approximate hes reduce_env expr c
        | _ ->
            assert false
        end
    | Arith _, _ -> assert false
    | _ -> assert false
(* }}} *)

let underapproximate_by
      : simple_ty Hflz.hes
     -> Counterexample.normalized
     -> HornClause.formula =
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
    let approx =
      approximate hes TraceVar.Map.empty main cex
    in
    Log.debug begin fun m -> m ~header:"Expansion" "%a"
      HornClause.pp_hum_formula approx
    end;
    approx
(* }}} *)

(** solve [e] for [x]
    [e] must be the form of [a=a] *)
let solve_for (x: TraceVar.t) (e: HornClause.formula) : HornClause.arith =
  let open HornClause in
  let rec arith : arith -> (arith -> arith) option = function
    | Var (`I x') when TraceVar.equal x x' -> Some (fun a -> a)
    | Op (op, [a1;a2]) ->
        begin match op, arith a1, arith a2 with
        | Add, Some f, None -> Some (fun a -> f Arith.(Op(Sub, [a; a2])))
        | Add, None, Some f -> Some (fun a -> f Arith.(Op(Sub, [a; a1])))
        | Sub, Some f, None -> Some (fun a -> f Arith.(Op(Add, [a; a2])))
        | Sub, None, Some f -> Some (fun a -> f Arith.(Op(Sub, [a1; a])))
        | _ -> None
        end
    | _ -> None
  in
  match e with
  | Pred(Eq, [a1;a2]) ->
      begin match arith a1, arith a2 with
      | Some f, None -> f a2
      | None, Some f -> f a1
      | None, None ->
          Log.err begin fun m -> m ~header:"uhen" "%a"
            HornClause.pp_hum_formula e
          end;
          assert false (* TODO x + x = 2 みたいなのときに困る *)
      | Some _, Some _ ->
          Log.err begin fun m -> m ~header:"uhen" "%a"
            HornClause.pp_hum_formula e
          end;
          assert false (* TODO x + x = 2 みたいなのときに困る *)
      end
  | _ -> assert false

let elim_variables'
      : using:(HornClause.formula list)
     -> keep:TraceVar.Set.t
     -> HornClause.formula
     -> HornClause.formula =
  fun ~using:eqs ~keep target ->
    let rec go : HornClause.formula list
              -> HornClause.formula
              -> HornClause.formula =
      fun eqs target -> match eqs with
      | [] -> target
      | phi::phis ->
          let fvs = TraceVar.Set.of_list @@
            List.filter_map (snd @@ Formula.fvs phi) ~f:
              begin function
              | `I x -> Some x
              | _ -> None
              end
          in
          if HornClauseSolver.is_valid phi then begin
            Log.debug begin fun m -> m ~header:"elim_variables':1"
              "skip %a" HornClause.pp_hum_formula phi
            end;
            go phis target
          end else if TraceVar.Set.(is_empty (diff fvs keep)) then begin
            Log.debug begin fun m -> m ~header:"elim_variables':2"
              "skip %a" HornClause.pp_hum_formula phi
            end;
            go phis target
          end else begin
            let x = TraceVar.Set.(min_elt_exn (diff fvs keep)) in
            let e = solve_for x phi in (* phi <=> x = e *)
            let equal a b = match a, b with
              | `I a, `I b -> TraceVar.equal a b
              | `E a, `E b -> Id.eq a b
              | _ -> false
            in
            let phis =
              List.map ~f:(Trans.Subst.Arith.formula_ equal (`I x) e) phis
            in
            let target = Trans.Subst.Arith.formula_ equal (`I x) e target in
            go phis target
          end
    in go eqs target

let rec to_simple_expr : TraceExpr.t -> Counterexample.normalized -> HornClause.formula option =
  fun psi c -> match psi, c with
  | Pred(p,as'), _ -> Some (Pred(p,as'))
  | And(psi,_), AndL c -> to_simple_expr psi c
  | And(_,psi), AndR c -> to_simple_expr psi c
  | And(psi1,psi2), _ ->
      begin try
        let [@warning "-8"] Some f1 = to_simple_expr psi1 False in
        let [@warning "-8"] Some f2 = to_simple_expr psi2 False in
        Some (And [f1;f2])
      with _ -> None end
  | Or (psi1,psi2), Or (c1, c2) ->
      begin try
        let [@warning "-8"] Some f1 = to_simple_expr psi1 c1 in
        let [@warning "-8"] Some f2 = to_simple_expr psi2 c2 in
        Some (Or [f1;f2])
      with _ -> None end
  | _ -> None

type node =
  { clause      : HornClause.t [@printer HornClause.pp_hum]
  ; actual_head : (HornClause.head [@printer HornClause.pp_hum_head]) list
      (* required in optimization for Or. See Note[OrOpt] *)
  }
  [@@deriving eq,ord,show,iter,fold,sexp]

let simple_node clause = { clause; actual_head = [clause.head] }

type hcc_tree =
  | Leaf
  | Seq  of node * hcc_tree
  | Br   of hcc_tree * hcc_tree
  [@@deriving eq,ord,show,iter,fold,sexp]

let rec heads_of_hcc_tree = function
  | Leaf -> []
  | Seq (c, _) -> [c]
  | Br (t1,t2) -> heads_of_hcc_tree t1 @ heads_of_hcc_tree t2

let rec modify_heads_of_hcc_tree ~f = function
  | Leaf -> Leaf
  | Seq (c, t) -> Seq (f c, t)
  | Br (t1, t2) -> Br (modify_heads_of_hcc_tree ~f t1,
                       modify_heads_of_hcc_tree ~f t2)

let rec map_hcc_tree ~f =function
  | Leaf -> Leaf
  | Seq (c, t) -> Seq (f c, map_hcc_tree ~f t)
  | Br (t1, t2) -> Br (map_hcc_tree ~f t1, map_hcc_tree ~f t2)

let rec hcc_tree_to_lists = function
  | Leaf -> []
  | Seq ({clause=hc;_}, hcc_tree) ->
      begin match hcc_tree_to_lists hcc_tree with
      | [] -> [[hc]]
      | hccs -> List.map hccs ~f:(fun x -> hc::x)
      end
  | Br (hcc_tree1, hcc_tree) ->
      hcc_tree_to_lists hcc_tree1 @ hcc_tree_to_lists hcc_tree

type trace =
  | Leaf of (HornClause.formula [@printer HornClause.pp_hum_formula])
  | Or   of ((HornClause.formula [@printer HornClause.pp_hum_formula]) * trace)
          * ((HornClause.formula [@printer HornClause.pp_hum_formula]) * trace)
  | AndL of trace
  | AndR of trace
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let make_trace
      : Counterexample.normalized
     -> HornClause.formula
     -> trace =
  let rec go
         : Counterexample.normalized
        -> HornClause.formula
        -> trace =
    fun cex phi -> match cex, phi with
      | Or (c1,c2), Or [f1;f2] ->
          let t1 = go c1 f1 in
          let t2 = go c2 f2 in
          Or ((f1,t1),(f2,t2))
      | AndL cex, f -> AndL (go cex f)
      | AndR cex, f -> AndR (go cex f)
      | _,p -> Leaf p
  in go

let rec cex_of_trace : trace -> Counterexample.Normalized.t = function
  | Leaf _ -> False
  | Or ((_,t1),(_,t2)) -> Or (cex_of_trace t1, cex_of_trace t2)
  | AndL t -> AndL (cex_of_trace t)
  | AndR t -> AndR (cex_of_trace t)

let gen_HCCS
    :  simple_ty Hflz.hes
    -> trace
    -> hcc_tree =
  fun hes cex ->
    let rec go
        :  reduce_env
        -> guard
        -> HornClause.pred_var option
        -> TraceExpr.t
        -> trace
        -> hcc_tree * reduce_env =
          (* reduce_env should be returned back to calculate exact binding *)
      fun reduce_env guard pv expr cex ->
        Log.debug begin fun m -> m ~header:"gen_HCCS"
          ("@[<v>"^^
           "@[<2>expr : %a@]@,"^^
           "@[<2>guard: %a@]@,"^^
           "@[<2>pv   : %a@]@,"^^
           "@[<2>cex  : %a@]@]")
            TraceExpr.pp_hum expr
            HornClause.pp_hum_body guard
            Print.(option HornClause.pp_hum_pred_var) pv
            pp_trace cex
        end;
        match expr, cex with
        | Bool true, _
        | (And _ | Or _), Leaf _ ->
            Leaf, reduce_env
        | Bool false, _ ->
            let body = HornClause.append_pvs (Option.to_list pv) guard in
            Seq (simple_node { head= `P (Formula.mk_bool false); body }, Leaf), reduce_env
        | Pred (pred, as'), _ ->
            let body = HornClause.append_pvs (Option.to_list pv) guard in
            Seq (simple_node { head= `P (Formula.mk_pred pred as'); body }, Leaf), reduce_env
        | And (psi1,_), AndL cex ->
            go reduce_env guard pv psi1 cex
        | And (_,psi2), AndR cex ->
            go reduce_env guard pv psi2 cex
        | Or (psi1,psi2), Or ((_f1, cex1),(f2, cex2)) ->
            begin match (to_simple_expr psi1 (cex_of_trace cex1), psi1, cex1) ,
                        (to_simple_expr psi2 (cex_of_trace cex2), psi2, cex2) with
            | (Some f1, _, _), (Some f2, _, _) ->
                Log.info begin fun m -> m  ~header:"OptimizeOr:Both" "@[<v>%a@,%a@]"
                  HornClause.pp_hum_formula f1
                  HornClause.pp_hum_formula f2
                end;
                let body = HornClause.append_pvs (Option.to_list pv) guard in
                Seq (simple_node { head= `P (Formula.mk_or f1 f2); body }, Leaf), reduce_env
            | (Some f, _, _), (_, psi, cex)
            | (_, psi, cex), (Some f, _, _) ->
                Log.info begin fun m -> m  ~header:"OptimizeOr" "%a"
                  HornClause.pp_hum_formula f
                end;
                let guard = HornClause.append_phi [Formula.mk_not f] guard in
                go reduce_env guard pv psi cex
                |> Pair.first ~f:begin
                     modify_heads_of_hcc_tree ~f:begin fun c ->
                       { c with actual_head = `P f :: c.actual_head }
                     end
                   end
            | (None,_,_), (None,_,_) ->
                let (reduce_env1,  ps1,  extra_f1, fvs1) ,
                    (reduce_env2, _ps2, _extra_f2, fvs2)
                  =
                    TraceVar.with_counters_rollbacked @@ fun _ ->
                    with_logs_disabled @@ fun _ ->
                      let aux psi cex =
                        let hcc_tree, reduce_env = go reduce_env guard pv psi cex in
                        let nodes = heads_of_hcc_tree hcc_tree in
                        let ps, extra_f =
                          let ubs = List.concat_map nodes ~f:(fun node -> node.actual_head) in
                          List.partition_map ubs ~f:begin function
                          | `V v -> `Fst v
                          | `P f -> `Snd f
                          end
                        in
                        let fvs =
                          List.concat_map ps ~f:HornClause.args_of_pred_var
                          |> List.remove_duplicates ~equal:TraceVar.equal
                        in
                        reduce_env, ps, extra_f, fvs
                      in
                      let r1 = aux psi1 cex1 in (* Evaluation order matters!!! *)
                      let r2 = aux psi2 cex2 in
                      (r1, r2)
                in
                let ret_reduce_env =
                  TraceVar.Map.merge reduce_env1 reduce_env2
                    ~f:begin fun ~key:_ -> function
                    | `Left x -> Some x
                    | `Right x -> Some x
                    | `Both (x,_) -> Some x
                    end
                in

                let bind_constr1, bind_constr2 =
                  Pair.bimap (fvs1, fvs2) ~f:begin fun fvs_p ->
                    (* let fvs = List.remove_duplicates ~equal:TraceVar.equal @@ fvs1@fvs2 in *)
                    let fvs = List.remove_duplicates ~equal:TraceVar.equal fvs_p in
                    List.map fvs ~f:begin fun x ->
                      match TraceVar.type_of x, TraceVar.Map.find_exn ret_reduce_env x with
                      | TyInt, (Arith a, _) ->
                          Formula.mk_pred Eq [ Arith.mk_var' (`I x); a ]
                      | _ -> assert false
                    end
                  end
                in
                Log.info begin fun m -> m ~header:"BindConstr1" "%a"
                  (Print.list_set HornClause.pp_hum_formula) bind_constr1
                end;
                Log.info begin fun m -> m ~header:"BindConstr2" "%a"
                  (Print.list_set HornClause.pp_hum_formula) bind_constr2
                end;
                let ub_p2 =
                  let fvs = TraceVar.Set.of_list @@ List.concat
                    [ fvs1
                    ; fvs2
                    ; List.concat_map (Option.to_list pv @ guard.pvs)
                        ~f:HornClause.args_of_pred_var
                    ; List.concat_map guard.phi ~f:begin fun x ->
                        List.map (snd (Formula.fvs x)) ~f:begin function
                        | `I x -> x
                        | `E _ -> assert false
                        end
                      end
                    ]
                  in
                  let bind = List.filter_map (TraceVar.Map.to_alist ret_reduce_env) ~f:
                      begin fun (x, (e, _)) ->
                        match TraceVar.type_of x, e with
                        | TyInt, Arith (Var (`I y)) when TraceVar.equal x y ->
                            None
                        | TyInt, Arith a ->
                            Some (Formula.mk_pred Eq [ Arith.mk_var' (`I x); a ])
                        | _ -> None
                      end
                  in
                  Log.info begin fun m -> m ~header:"UbP2:Orig" "@[<v>%a@]"
                    HornClause.pp_hum_formula f2
                  end;
                  Log.info begin fun m -> m ~header:"UbP2:Bind" "@[<v>%a@]"
                    Print.(list HornClause.pp_hum_formula) bind
                  end;
                  Log.info begin fun m -> m ~header:"UbP2:FVS" "%a"
                    Print.(list_comma TraceVar.pp_hum) (TraceVar.Set.to_list fvs)
                  end;
                  (* TODO どこまで使って良いのか分からない fvs1@fvs2でもよい？ *)
                  elim_variables' ~using:bind ~keep:(TraceVar.Set.of_list fvs2) f2
                in
                Log.info begin fun m -> m ~header:"UbP2" "%a"
                  HornClause.pp_hum_formula ub_p2
                end;
                let hcc_tree1' =
                  let guard = guard
                    |> HornClause.append_phi [Formula.mk_not ub_p2]
                    |> HornClause.append_phi bind_constr2
                  in
                  let hcc_tree1, _ = go reduce_env guard pv psi1 cex1 in
                  hcc_tree1
                in
                let hcc_tree2' =
                  let guard = guard
                    |> HornClause.append_pvs (List.map ~f:HornClause.negate_pv ps1)
                    |> HornClause.append_phi (List.map ~f:Formula.mk_not extra_f1)
                    (* |> HornClause.append_phi bind_constr1 *)
                        (* TODO
                         * あるとBurn_POPL18/a-max.inがNoProgress
                         * ないとok/valid/2.inとかが死ぬ
                         * *)
                  in
                  let hcc_tree2, _ = go reduce_env guard pv psi2 cex2 in
                  (* hcc_tree2 *)
                  (* これで良いのか？正当性が何もわからん *)
                  modify_heads_of_hcc_tree hcc_tree2 ~f:begin fun c ->
                    { c with
                      clause =
                        { c.clause with 
                          body = HornClause.append_phi bind_constr1 c.clause.body } }
                  end
                in
                Br (hcc_tree1', hcc_tree2'), ret_reduce_env
            end
        | (App _| Var _), _ ->
            let expr_head, args = TraceExpr.decompose_app expr in
            begin match expr_head with
            | Var (`I tv) ->
                let aged = TraceVar.gen_aged tv in
                let vars = TraceVar.mk_childlen aged in
                let bind = List.zip_exn vars args in
                let next_pv = HornClause.mk_pred_var aged in
                let next_expr, next_guard = match tv with
                  | Local _ ->
                      let head, guard = TraceVar.Map.find_exn reduce_env tv in
                      let expr = TraceExpr.mk_apps head (List.map vars ~f:TraceExpr.mk_var) in
                      expr, guard
                  | Nt { orig; _} ->
                      let rule = Hflz.lookup_rule orig hes in
                      let ovars, obody = Hflz.decompose_abs rule.body in
                      let rename = IdMap.of_list @@ List.zip_exn ovars vars in
                      let next_expr = TraceExpr.Make.hflz hes rename obody in
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
                      (List.filter bind_constr
                         ~f:(not <<< HornClauseSolver.is_valid))
                  |> HornClause.append_pvs
                      (Option.to_list pv)
                in
                Log.debug begin fun m -> m ~header:"CurrentGuard" "@[<v>%a@]"
                  HornClause.pp_hum_body current_guard
                end;

                let hcc =
                  HornClause.{ body=current_guard; head = `V next_pv }
                in
                Log.debug begin fun m -> m ~header:"CHC" "%a"
                  HornClause.pp_hum hcc
                end;

                let _, bind_with_guard =
                  let init_guard =
                    HornClause.(append_pvs (next_pv :: Option.to_list pv) guard)
                    (* HornClause.(append_pvs (Option.to_list pv) guard) *)
                        (* 例えばinputs/mochi/mc91.inで見つかる述語が複雑になってタイムアウト *)
                    (* HornClause.(append_pvs [next_pv] guard) *)
                        (* 例えばinputs/mochi/max.inがダメ *)
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
                              ; phi = Formula.mk_pred Eq
                                        [ Arith.mk_var' (`I x); a ] :: g.phi
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
                let hcc_tree, reduce_env' =
                  go next_reduce_env next_guard (Some next_pv) next_expr cex
                in Seq (simple_node hcc, hcc_tree), reduce_env'
            | Abs(x, phi) ->
                let [@warning "-8"] e::es = args in
                let phi' = TraceExpr.beta_head x e phi in
                let expr = TraceExpr.mk_apps phi' es in
                go reduce_env guard pv expr cex
            | _ ->
                Print.print TraceExpr.pp_hum expr_head;
                assert false
            end
        | _ -> assert false
    in
    TraceVar.reset_counters();
    let main =
      let head =
        Hflz.main_symbol hes
        |> TraceVar.mk_nt
      in
      let args = TraceVar.mk_childlen TraceVar.{ var = head; age = 0 } in
      TraceExpr.(mk_apps (mk_var head) (List.map args ~f:mk_var))
    in
    fst @@ go TraceVar.Map.empty empty_guard None main cex


type result = [ `Feasible | `Refined of Hflmc2_abstraction.env ]

let run
     : simple_ty Hflz.hes
    -> Counterexample.normalized
    -> Hflmc2_abstraction.env
    -> result =
  fun hes cex old_gamma ->
    let expanded = underapproximate_by hes cex in
    if not @@ HornClauseSolver.is_valid expanded then
      `Feasible
    else
      let trace = make_trace cex expanded in
      let hccss = hcc_tree_to_lists @@ gen_HCCS hes trace in
      List.iter hccss ~f:begin fun hccs ->
        Log.info begin fun m -> m ~header:"HCCS" "@[<v>%a@]"
          (Print.list HornClause.pp_hum) hccs
        end;
      end;
      let new_gamma = HornClauseSolver.solve hes hccss in
      `Refined (Hflmc2_abstraction.merge_env old_gamma new_gamma)
