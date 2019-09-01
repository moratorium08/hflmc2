open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type

open HornClause

module Log = (val Logs.src_log @@ Logs.Src.create "HornClauseSolver")

let () = Fpat.FPATConfig.set_default()

module ToFpat = struct

  let idnt_of_tv : TraceVar.t -> Fpat.Idnt.t =
    fun t -> Fpat.Idnt.make (Print.strf "%a" TraceVar.pp_hum t)

  let term_of_tv : TraceVar.t -> Fpat.Term.t =
    fun t -> Fpat.Term.mk_var (idnt_of_tv t)

  let typed_term_of_tv : TraceVar.t -> Fpat.TypTerm.t =
    fun t ->
      assert (TraceVar.type_of t = TyInt);
      Fpat.TypTerm.make (term_of_tv t) Fpat.Type.mk_int

  let idnt_of_aged : TraceVar.aged -> Fpat.Idnt.t =
    fun aged -> Fpat.Idnt.make (Print.strf "%a" TraceVar.pp_hum_aged aged)

  let term_of_aged : TraceVar.aged -> Fpat.Term.t =
    fun aged -> Fpat.Term.mk_var (idnt_of_aged aged)

  let typed_term_of_aged : TraceVar.aged -> Fpat.TypTerm.t =
    fun aged ->
      assert (TraceVar.type_of_aged aged = TyInt);
      Fpat.TypTerm.make (term_of_aged aged) Fpat.Type.mk_int

  let idnt_of_trace_var : TraceVar.t -> Fpat.Idnt.t =
    fun tv -> Fpat.Idnt.make (Print.strf "%a" TraceVar.pp_hum tv)

  let term_of_trace_var : TraceVar.t -> Fpat.Term.t =
    fun tv -> Fpat.Term.mk_var (idnt_of_trace_var tv)

  let typed_term_of_trace_var : TraceVar.t -> Fpat.TypTerm.t =
    fun tv ->
      assert (TraceVar.type_of tv = TyInt);
      Fpat.TypTerm.make (term_of_trace_var tv) Fpat.Type.mk_int

  let pva : pred_var -> Fpat.Pva.t =
    function
    | PredVar aged as pv ->
        Fpat.Pva.make
          (idnt_of_aged aged)
          (List.map (args_of_pred_var pv) ~f:typed_term_of_trace_var)

  let pred_var : pred_var -> Fpat.PredVar.t =
    fun pv ->
      let typ_env =
        List.map (args_of_pred_var pv) ~f:begin fun tv ->
          idnt_of_trace_var tv, Fpat.Type.mk_int
        end
      in
      let idnt = match pv with
        | PredVar aged -> idnt_of_aged aged
      in
      Fpat.PredVar.make idnt typ_env

  let head : pred_var option -> Fpat.HornClause.head =
    fun head ->
      Fpat.HornClause.mk_head @@ Hflmc2_util.Option.map head ~f:pred_var

  let rec formula_of_arith : arith -> Fpat.Formula.t = function
    | Int n -> Fpat.Formula.of_term @@ Fpat.Term.mk_const (Fpat.Const.Int n)
    | Var (`E x) ->
        let x' = Fpat.Idnt.make (Id.to_string x) in
        Fpat.Formula.mk_var x' []
    | Var (`I tv) ->
        Fpat.Formula.of_term @@ term_of_trace_var tv
    | Op(op, [a1;a2]) ->
        let op' = Fpat.Term.mk_const @@ match op with
          | Add  -> Fpat.Const.Add Fpat.Type.mk_int
          | Sub  -> Fpat.Const.Sub Fpat.Type.mk_int
          | Mult -> Fpat.Const.Mul Fpat.Type.mk_int
        in Fpat.Formula.of_term @@ Fpat.Term.mk_app op'
              [ Fpat.Formula.term_of @@ formula_of_arith a1
              ; Fpat.Formula.term_of @@ formula_of_arith a2 ]
    | Op(_,_) -> assert false

  let rec formula : formula -> Fpat.Formula.t = function
    | Var x -> Void.absurd x
    | Bool true | And [] ->
        Fpat.Formula.mk_true
    | Bool false | Or [] ->
        Fpat.Formula.mk_false
    | Or (f::fs) ->
        List.fold_left fs ~init:(formula f) ~f:begin fun f1 f2 ->
          Fpat.Formula.mk_or f1 (formula f2)
        end
    | And (f::fs) ->
        List.fold_left fs ~init:(formula f) ~f:begin fun f1 f2 ->
          Fpat.Formula.mk_and f1 (formula f2)
        end
    | Pred(pred, [a1;a2]) ->
        let op' = Fpat.Term.mk_const @@ match pred with
          | Eq  -> Fpat.Const.Eq  Fpat.Type.mk_int
          | Neq -> Fpat.Const.Neq Fpat.Type.mk_int
          | Le  -> Fpat.Const.Leq Fpat.Type.mk_int
          | Ge  -> Fpat.Const.Geq Fpat.Type.mk_int
          | Lt  -> Fpat.Const.Lt  Fpat.Type.mk_int
          | Gt  -> Fpat.Const.Gt  Fpat.Type.mk_int
        in Fpat.Formula.of_term @@ Fpat.Term.mk_app op'
              [ Fpat.Formula.term_of @@ formula_of_arith a1
              ; Fpat.Formula.term_of @@ formula_of_arith a2 ]
    | Pred(_,_) -> assert false

  let body : body -> Fpat.HornClause.body =
    fun { pvs ; phi } ->
      Fpat.HornClause.mk_body
        (List.map pvs ~f:pva)
        (formula (Formula.mk_ands phi))

  let hornClause : t -> Fpat.HornClause.t =
    fun chc -> Fpat.HornClause.make (head chc.head) (body chc.body)

  let hccs : t list -> Fpat.HCCS.t =
    List.map ~f:(hornClause) >>> Fpat.HCCS.normalize2
end

module OfFpat = struct
  let rec arith : 'var. (string -> 'var) -> Fpat.Term.t -> 'var Arith.gen_t =
    fun into_id a ->
        let open Fpat.Term in
        match a with
        | Var (V s) -> Var (into_id s)
        | Const (Int n) -> Int n
        | App (App (Const (Add _), a1), a2) ->
            Arith.mk_op Add  [arith into_id a1; arith into_id a2]
        | App (App (Const (Sub _), a1), a2) ->
            Arith.mk_op Sub  [arith into_id a1; arith into_id a2]
        | App (App (Const (Mul _), a1), a2) ->
            Arith.mk_op Mult [arith into_id a1; arith into_id a2]
        | _ -> assert false

  let formula
        : 'avar
        . (string -> 'avar)
       -> Fpat.Formula.t
       -> (Void.t, 'avar) Formula.gen_t =
    fun into_id ->
      let rec of_term =
        let open Fpat.Term in
        function
        | Const True  -> Formula.Bool true
        | Const False -> Formula.Bool false
        | App (Const Not, f) -> Formula.mk_not' Void.absurd (of_term f)
        | App ((App (Const And, f1)), f2) ->
            Formula.mk_and (of_term f1) (of_term f2)
        | App ((App (Const Or , f1)), f2) ->
            Formula.mk_or  (of_term f1) (of_term f2)
        | App ((App (Const (Eq  _) , f1)), f2) ->
            Formula.mk_pred Eq  [arith into_id f1; arith into_id f2]
        | App ((App (Const (Neq _) , f1)), f2) ->
            Formula.mk_pred Neq [arith into_id f1; arith into_id f2]
        | App ((App (Const (Leq _) , f1)), f2) ->
            Formula.mk_pred Le  [arith into_id f1; arith into_id f2]
        | App ((App (Const (Geq _) , f1)), f2) ->
            Formula.mk_pred Ge  [arith into_id f1; arith into_id f2]
        | App ((App (Const (Lt  _) , f1)), f2) ->
            Formula.mk_pred Lt  [arith into_id f1; arith into_id f2]
        | App ((App (Const (Gt  _) , f1)), f2) ->
            Formula.mk_pred Gt  [arith into_id f1; arith into_id f2]
        | _ -> assert false
      in fun x -> of_term (Fpat.Formula.term_of x)

  let abstracion_env
        : simple_ty Hflz.hes
       -> Fpat.PredSubst.t
       -> Hflmc2_abstraction.env =
    fun hes subst ->
      let pred_map : Fpat.Pred.t StrMap.t =
        StrMap.of_alist_exn @@ List.map subst ~f:begin function
          | Fpat.Idnt.V x, pred -> x, pred
          | _ -> assert false
        end
      in
      let lookup_pred : HornClause.pred_var -> Formula.t =
        fun pv ->
          let pv_name = match pv with
            | PredVar aged -> TraceVar.string_of_aged aged
          in
          let fpat_args, fpat_pred =
            StrMap.find_exn pred_map pv_name
            |> Pair.first begin List.map ~f:begin function
                 | Fpat.Idnt.V x, _ -> x
                 | _ -> assert false
                 end
               end
          in
          let pv_args =
            List.map (args_of_pred_var pv) ~f:begin function
              | Local { name; _ } -> name
              | _ -> assert false
              end
          in
          let rename_map = StrMap.of_alist_exn @@
            List.map2_exn fpat_args pv_args ~f:begin fun fx x ->
              fx, { x with ty = `Int }
            end
          in
          formula (StrMap.find_exn rename_map) fpat_pred
      in
      let rec abstraction_ty_of_aged (aged : TraceVar.aged) : abstraction_ty =
        let sty        = Type.unsafe_unlift @@ TraceVar.type_of_aged aged in
        let args, ()   = Type.decompose_arrow sty in
        let tv_args    = TraceVar.mk_childlen aged in

        (* main part *)
        let preds : Formula.t list =
          let underapproximation = lookup_pred (HornClause.mk_pred_var aged) in
          Log.debug begin fun m -> m ~header:"Underapproximation" "%a : %a"
            TraceVar.pp_hum_aged aged
            Print.formula underapproximation
          end;
          let phi =
            Trans.Simplify.formula @@ underapproximation
          in
          match phi with
          | Bool _ -> []
          | _ -> [phi]
        in

        (* recursive part *)
        let new_args' =
          List.map2_exn args tv_args ~f:begin fun arg tv_arg ->
            match arg.ty with
            | TyInt     ->
                { arg with ty = TyInt }
            | TySigma _ ->
                { arg with ty = TySigma (abstraction_ty_of_trace_var tv_arg) }
          end
        in
        (* merge *)
        Type.mk_arrows new_args' (TyBool preds)
      and abstraction_ty_of_trace_var : TraceVar.t -> abstraction_ty =
        fun tv ->
          let on_age age =
            let aged = TraceVar.(mk_aged ~age tv) in
            abstraction_ty_of_aged aged
          in
          let abstraction_ty =
            let n = match Hashtbl.find TraceVar.counters tv with
              | None -> 0
              | Some n -> n
            in
            if n = 0
            then
              Type.map_ty (Fn.const []) @@
                Type.unsafe_unlift @@ TraceVar.type_of tv
            else
              (* NOTE
               * Duplication is removed when merged with old environmet.
               * See [Hflmc2_abstraction.merge_env] *)
              Type.merges (@) (List.init n ~f:on_age)
          in
          abstraction_ty
      in
      IdMap.of_list @@ List.map hes ~f:begin fun rule ->
        rule.var, abstraction_ty_of_trace_var (TraceVar.mk_nt rule.var)
      end
end

let interpolate : formula -> formula -> formula option =
  fun f1 f2 ->
    let f1' = ToFpat.formula f1 in
    let f2' = ToFpat.formula f2 in
    let preserve_name = Fn.const true in
    match Fpat.InterpProver.interpolate_dyn preserve_name f1' f2' with
    | ip ->
        let rev_map =
          let _, xs1 = Formula.fvs f1 in
          let _, xs2 = Formula.fvs f2 in
          let xs =
            List.remove_duplicates (xs1@xs2) ~equal:begin fun x1 x2 ->
              match x1, x2 with
              | `I x1, `I x2 -> TraceVar.equal x1 x2
              | `E x1, `E x2 -> Id.eq x1 x2
              | _ -> false
            end
          in
          let map = StrMap.of_alist_exn @@ List.map xs ~f:begin function
            | `I x -> TraceVar.string_of x, `I x
            | `E n -> Id.to_string n, `E n
            end
          in fun x -> StrMap.find_exn map x
        in
        Some (OfFpat.formula rev_map ip)
    | exception Fpat.InterpProver.NoInterpolant ->
        None


let is_valid : formula -> bool =
  fun f -> Fpat.SMTProver.is_valid_dyn (ToFpat.formula f)

let solve : simple_ty Hflz.hes -> t list -> Hflmc2_abstraction.env =
  fun hes hccs ->
    let hccs' = ToFpat.hccs hccs in
    let solvers =
      [ "GenHCCSSolver"
          , Fpat.(GenHCCSSolver.solve (CHGenInterpProver.interpolate false))
      ; "GenHCCSSolver+Interp"
          , Fpat.(GenHCCSSolver.solve (CHGenInterpProver.interpolate true))
      ; "BwIPHCCSSolver"
          , Fpat.BwIPHCCSSolver.solve
      ; "FwHCCSSolver"
          , Fpat.FwHCCSSolver.solve_simp
      ]
    in
    let map =
      match
        List.find_map solvers ~f:begin fun (name, solver) ->
          match solver hccs' with
          | ans -> Some ans
          | exception e ->
              Log.warn begin fun m -> m ~header:"Fpat"
                "`%s` failed to solve the HCCS: %s"
                name (Printexc.to_string e)
              end;
              None
        end
      with
      | Some map -> map
      | None ->
          Log.err (fun m -> m ~header:"Fpat" "Could not solve HCCS");
          Fn.fatal "Failed to solve HCCS"
    in
    Log.debug begin fun m -> m ~header:"FpatAnswer" "%a"
      Fpat.PredSubst.pr map;
    end;
    OfFpat.abstracion_env hes map

