open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type
open Hflmc2_abstraction
open Hflmc2_modelcheck

module Log = (val Logs.src_log @@ Logs.Src.create "Refine")

type guard = HornClause.body
type reduce_env = (TraceExpr.t * guard) TraceVarMap.t

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
        | Var (Nt { orig; _ } as tv) ->
            let rule = List.find_exn hes ~f:(fun r -> Id.eq r.var orig) in
            let orig_vars, orig_body = Hflz.decompose_abs rule.body in
            let vars   = TraceVar.mk_locals tv in
            let rename = IdMap.of_list @@ List.zip_exn orig_vars vars in
            let body   = TraceExpr.of_hflz hes rename orig_body in
            let bind   = TraceVarMap.of_alist_exn @@ List.zip_exn vars args in
            let expr   = TraceExpr.subst bind body in
            approximate hes reduce_env expr (Some c)
        | Var (Local _ as tv) ->
            let head, _ = TraceVarMap.find_exn reduce_env tv in
            let expr    = TraceExpr.mk_apps head args in
            approximate hes reduce_env expr (Some c)
        | _ -> assert false
        end
    | (App _| Var _), None -> Bool true
    | Arith _, _ -> assert false
    | Exists _, _ | Forall _, _ -> Fn.todo()
    | _ -> assert false

let gen_HCCS
    :  simple_ty Hflz.hes
    -> Counterexample.normalized
    -> HornClause.t list =
  fun hes cex ->
    let [@warning "-27-39"] rec go
        :  guard
        -> reduce_env
        -> TraceExpr.t
        -> Counterexample.normalized option
        -> HornClause.t list =
      fun guard reduce_env expr cex ->
        Log.debug begin fun m -> m ~header:"gen_HCCS"
          "@[<v>@[<h 2>guard: %a@]@,@[<2>expr : %a@]@]"
            HornClause.pp_hum_body guard
            TraceExpr.pp_hum expr
        end;
        match expr, cex with
        | (Bool true | And []), _ ->
            []
        | (Bool false | Or []), _ ->
            Fn.todo()
        | Pred (op,as'), _ ->
            Fn.todo()
        | And psis, Some (And (_,i,c)) ->
            go guard reduce_env (List.nth_exn psis i) (Some c)
        | And psis, (None | Some False) ->
            List.concat_map psis ~f:(go guard reduce_env -$- None)
        | Or [psi1;psi2], Some (Or [c1;c2]) ->
            Fn.todo()
        | Or psis, Some (Or cs) ->
            Fn.todo()
        | Or psis, (None | Some False) ->
            Fn.todo()
        | (App _| Var _), Some _ ->
            let head, args = TraceExpr.decompose_app expr in
            begin match head with
            | Var (Nt { orig; age } as nt) ->
                Fn.todo()
            | Var (Local { parent; name; fvs; nth } as tv) ->
                Fn.todo()
            | _ ->
                Print.print TraceExpr.pp head;
                assert false
            end
        | (App _| Var _), None -> []
        | Arith _, _ -> assert false
        | Exists _, _ | Forall _, _ -> Fn.todo()
        | _ -> assert false
    in
    let main = TraceExpr.mk_var @@ TraceVar.gen_nt @@ Hflz.main_symbol hes in
    let guard = HornClause.{ pvs =[]; phi = Formula.Bool true } in
    go guard TraceVarMap.empty main (Some cex)

(* TODO hesはλ-liftingしておく *)
let run : simple_ty Hflz.hes -> Counterexample.normalized -> Hflmc2_abstraction.env =
  fun hes cex ->
    TraceVar.reset_counters();
    let hccs = gen_HCCS hes cex in
    Log.debug begin fun m -> m ~header:"HCCS" "@[<v>%a@]"
      (Print.list HornClause.pp_hum) hccs
    end;
    HornClauseSolver.solve hes hccs

