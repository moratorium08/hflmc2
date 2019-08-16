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
    -> Counterexample.normalized
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
    | And exprs, And (_,i,c) ->
        approximate hes reduce_env (List.nth_exn exprs i) c
    | And _, False ->
        Log.err (fun m -> m ~header:"approximate:And" "impossible?");
        assert false
    | Or exprs, Or cs ->
        Formula.mk_ors
          (List.map2_exn exprs cs
             ~f:(fun expr c -> approximate hes reduce_env expr c))
    | Or _, False ->
        Log.warn (fun m -> m ~header:"approximate:Or" "impossible?");
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
        | _ -> assert false
        end
    | Arith _, _ -> assert false
    | Exists _, _ | Forall _, _ -> Fn.todo()
    | _ -> assert false
(* }}} *)

let is_feasible : simple_ty Hflz.hes -> Counterexample.normalized -> bool * HornClause.formula =
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
      approximate hes TraceVar.Map.empty main cex
    in
    Log.debug begin fun m -> m ~header:"Expansion" "%a"
      HornClause.pp_hum_formula approx
    end;
    (not @@ HornClauseSolver.is_valid approx, approx)
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
          assert false
          (* TODO x + x = 2 みたいなのときに困る *)
      | Some _, Some _ ->
          Log.err begin fun m -> m ~header:"uhen" "%a"
            HornClause.pp_hum_formula e
          end;
          assert false (* TODO x + x = 2 みたいなのときに困る *)
      end
  | _ -> assert false

(* TODO 2x=n; 2x+1=m から n+1=m を引き出す *)
(** @require every predicate in phi must be "=" *)
let elim_variables : HornClause.formula -> keep:TraceVar.Set.t -> HornClause.formula =
  fun phi ~keep:vars ->
    let rec go : HornClause.formula list -> HornClause.formula list = function
      | [] -> []
      | phi::phis ->
          let fvs = TraceVar.Set.of_list @@ List.filter_map (snd @@ Formula.fvs phi) ~f:begin function
            | `I x -> Some x
            | _ -> None
            end
          in
          if HornClauseSolver.is_valid phi then
            go phis
          else if TraceVar.Set.(is_empty (diff fvs vars)) then
            phi :: go phis
          else
            let x = TraceVar.Set.(min_elt_exn (diff fvs vars)) in
            let e = solve_for x phi in (* phi <=> x = e *)
            let equal a b = match a, b with
              | `I a, `I b -> TraceVar.equal a b
              | `E a, `E b -> Id.eq a b
              | _ -> false
            in
            go @@ List.map
              ~f:(Trans.Subst.Arith'.formula_ equal (`I x) e)
              phis
    in
    Formula.mk_ors @@
      List.map Formula.(to_DNF phi) ~f:begin fun e ->
        Formula.mk_ands (go e)
      end

let elim_variables'
      : using:(HornClause.formula list)
     -> keep:TraceVar.Set.t
     -> HornClause.formula
     -> HornClause.formula =
  fun ~using:eqs ~keep target ->
    let rec go : HornClause.formula list -> HornClause.formula -> HornClause.formula =
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
              List.map ~f:(Trans.Subst.Arith'.formula_ equal (`I x) e) phis
            in
            let target = Trans.Subst.Arith'.formula_ equal (`I x) e target in
            go phis target
          end
    in go eqs target

type trace =
  | Leaf of (HornClause.formula [@printer HornClause.pp_hum_formula])
  | Or   of (HornClause.formula [@printer HornClause.pp_hum_formula]) * trace list
  | And  of int * int * trace (** (n,i,_) ith branch in n. 0-indexed *)
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let rec peek : trace -> HornClause.formula = function
  | Leaf f -> f
  | Or (f,_) -> f
  | And (_,_,t) -> peek t

let tree_interpolant : Counterexample.normalized -> HornClause.formula -> trace =
  let rec go
         : HornClause.formula list
        -> HornClause.formula
        -> Counterexample.normalized
        -> HornClause.formula
        -> trace =
    fun guard p cex phi -> match cex, phi with
      | Or [c1;c2], Or [f1;f2] ->
          let f1' = Trans.Simplify.formula @@
            Formula.(mk_implies (mk_ands (p::guard)) f1)
          in
          let f2' = Trans.Simplify.formula @@
            Formula.(mk_implies (mk_ands (p::guard)) f2)
          in
          let [@warning "-8"] Some ip =
            HornClauseSolver.interpolate
              (Formula.mk_not f1')
              (Formula.mk_not f2')
          in
          Log.debug begin fun m -> m ~header:"tree_interpolant" "@[<v>%a@,%a@,%a@]"
            HornClause.pp_hum_formula f1'
            HornClause.pp_hum_formula f2'
            HornClause.pp_hum_formula ip
          end;
          let t1 = go (p::guard) (Formula.mk_not ip) c1 f1 in
          let t2 = go (p::guard) ip c2 f2 in
          Or (p, [t1;t2])
      | And (n,i,cex), f ->
          And (n, i, go guard p cex f)
      | _ -> Leaf p
  in
  go [] (Formula.Bool true)

let gen_HCCS
    :  simple_ty Hflz.hes
    -> trace
    -> HornClause.t list =
  fun hes cex ->
    let rec go
        :  reduce_env
        -> guard
        -> HornClause.pred_var option
        -> TraceExpr.t
        -> trace
        -> HornClause.t list =
      fun reduce_env guard pv expr cex ->
        Log.debug begin fun m -> m ~header:"gen_HCCS"
          "@[<v>@[<2>expr : %a@]@,@[<2>guard: %a@]@,@[<2>pv   : %a@]@,@[<2>cex  : %a@]@]"
            TraceExpr.pp_hum expr
            HornClause.pp_hum_body guard
            Print.(option HornClause.pp_hum_pred_var) pv
            pp_trace cex
            (* Print.(pair ~sep:comma *)
            (*     Counterexample.pp_hum_normalized *)
            (*     HornClause.pp_hum_formula *)
            (*   ) cex *)
        end;
        match expr, cex with
        | (Bool true | And []), _
        | (And _ | Or _)      , Leaf _ ->
            []
        | (Bool false | Or []), _ ->
            [{ head=None; body=guard }]
        | Pred (pred, as'), _ ->
            let body = guard
              |> HornClause.append_phi Formula.[mk_not @@ mk_pred pred as']
              |> HornClause.append_pvs Option.(to_list pv)
            in
            [{ head=None; body }]
        | And psis, And (_,i,c) ->
            go reduce_env guard pv (List.nth_exn psis i) c
        | Or [psi1;psi2], Or (_, [c1;c2]) ->
            let f1 = peek c1 in
            let f2 = peek c2 in
            Log.debug begin fun m -> m ~header:"f" "@[<v>%a@,%a@]"
              HornClause.pp_hum_formula f1
              HornClause.pp_hum_formula f2
            end;
            let fvs = TraceVar.Set.of_list @@
              List.concat_map ~f:HornClause.args_of_pred_var (Option.to_list pv @ guard.pvs) @
              List.concat_map (guard.phi) ~f:begin fun x ->
                match Formula.fvs x with
                | (_, vs) ->
                    List.filter_map vs ~f:begin function
                    | `I x -> Some x
                    | `E _ -> None
                    end
              end;
            in
            let bind = List.filter_map (TraceVar.Map.to_alist reduce_env) ~f:
                begin fun (x, (e, _)) ->
                  match TraceVar.type_of x, e with
                  | TyInt, Arith a ->
                      Some (Formula.mk_pred Eq [ Arith.mk_var' (`I x); a ])
                  | _ -> None
                end
            in
            let f1' = elim_variables' ~using:bind ~keep:fvs f1 in
            let f2' = elim_variables' ~using:bind ~keep:fvs f2 in
            Log.debug begin fun m -> m ~header:"fvs" "@[<v>%a@]"
              Print.(list_comma TraceVar.pp_hum) (TraceVar.Set.to_list fvs)
            end;
            Log.debug begin fun m -> m ~header:"bind" "@[<v>%a@]"
              Print.(list_comma HornClause.pp_hum_formula) bind
            end;
            Log.debug begin fun m -> m ~header:"f'" "@[<v>%a@,%a@]"
              HornClause.pp_hum_formula f1'
              HornClause.pp_hum_formula f2'
            end;
            let hccs1 = go reduce_env guard pv psi1 c1 in
            let hccs2 = go reduce_env guard pv psi2 c2 in

            let hccs1' = match hccs1 with
              | [] -> []
              | hcc1::hccs1 ->
                  let hcc1' =
                    { hcc1 with body = HornClause.append_phi [f1'] hcc1.body }
                  in
                  Log.debug begin fun m -> m ~header:"CHC1" "@[<v>%a@,⇓@,%a@]"
                    HornClause.pp_hum hcc1
                    HornClause.pp_hum hcc1'
                  end;
                  hcc1'::hccs1
            in
            let hccs2' = match hccs2 with
              | [] -> []
              | hcc2::hccs2 ->
                  (* TODO 先頭だけで良い？orが続くとダメでは *)
                  let hcc2' =
                    { hcc2 with body = HornClause.append_phi [f2'] hcc2.body }
                  in
                  Log.debug begin fun m -> m ~header:"CHC2" "@[<v>%a@,⇓@,%a@]"
                    HornClause.pp_hum hcc2
                    HornClause.pp_hum hcc2'
                  end;
                  hcc2'::hccs2
            in
            hccs1' @ hccs2'
        | Or _, _ ->
            Fn.todo ~info:"impossible? 3 or more disjunctions" ()
        | (App _| Var _), _ ->
            let expr_head, args = TraceExpr.decompose_app expr in
            begin match expr_head with
            | Var (`I tv) ->
                let aged = TraceVar.gen_aged tv in
                let vars = TraceVar.mk_childlen aged in
                let bind = List.zip_exn vars args in
                let next_pv = HornClause.mk_pred_var aged in
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
                  HornClause.{ body=current_guard; head=Some next_pv }
                in
                Log.debug begin fun m -> m ~header:"CHC" "%a"
                  HornClause.pp_hum hcc
                end;

                let _, bind_with_guard =
                  let init_guard =
                    HornClause.(append_pvs [next_pv] guard)
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

                hcc :: go next_reduce_env next_guard (Some next_pv) next_expr cex
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
    go TraceVar.Map.empty empty_guard None main cex


type result = [ `Feasible | `Refined of Hflmc2_abstraction.env ]

let run
     : simple_ty Hflz.hes
    -> Counterexample.normalized
    -> Hflmc2_abstraction.env
    -> result =
  fun hes cex old_gamma ->
    let is_feasible, expanded = is_feasible hes cex in
    if is_feasible then
      `Feasible
    else
      let tree_interpolant = tree_interpolant cex expanded in
      Log.debug begin fun m -> m ~header:"Trace" "@[<v>%a@]"
        pp_trace tree_interpolant
      end;
      let hccs = gen_HCCS hes tree_interpolant in
      Log.debug begin fun m -> m ~header:"HCCS" "@[<v>%a@]"
        (Print.list HornClause.pp_hum) hccs
      end;
      let new_gamma = HornClauseSolver.solve hes hccs in
      `Refined (Hflmc2_abstraction.merge_env old_gamma new_gamma)

