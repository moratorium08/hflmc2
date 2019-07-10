open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type

open HornClause

module Log = (val Logs.src_log @@ Logs.Src.create "HornClauseSolver")

let () = Fpat.FPATConfig.set_default()

(* TODO refactering *)

module ToFpat = struct

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
    fun (PredVar aged as pv) ->
      Fpat.Pva.make
        (idnt_of_aged aged)
        (List.map (args_of_pred_var pv) ~f:typed_term_of_trace_var)

  let pred_var : pred_var -> Fpat.PredVar.t =
    fun (PredVar aged as pv) ->
      let typ_env =
        List.map (args_of_pred_var pv) ~f:begin fun tv ->
          idnt_of_trace_var tv, Fpat.Type.mk_int
        end
      in Fpat.PredVar.make (idnt_of_aged aged) typ_env

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
        (formula phi)

  let hornClause : t -> Fpat.HornClause.t =
    fun chc -> Fpat.HornClause.make (head chc.head) (body chc.body)

  let hccs : t list -> Fpat.HCCS.t = List.map ~f:hornClause
end

(* TODO refacter
 * 今のままだと一ヶ月もしたら確実に読めなくなる
 * *)
module OfFpat = struct
  let rec arith : 'var. (string -> 'var) -> Fpat.Term.t -> 'var Arith.gen_t =
    fun into_id a ->
        let open Fpat.Term in
        match a with
        | Var (V s) -> Var (into_id s)
        | Const (Int n) -> Int n
        | App (App (Const (Add _), a1), a2) -> Arith.mk_op Add  [arith into_id a1; arith into_id a2]
        | App (App (Const (Sub _), a1), a2) -> Arith.mk_op Sub  [arith into_id a1; arith into_id a2]
        | App (App (Const (Mul _), a1), a2) -> Arith.mk_op Mult [arith into_id a1; arith into_id a2]
        | _ -> assert false

  let formula : 'avar. (string -> 'avar) -> Fpat.Formula.t -> (Void.t, 'avar) Formula.gen_t =
    fun into_id ->
      let rec of_term =
        let open Fpat.Term in
        function
        | Const True  -> Formula.Bool true
        | Const False -> Formula.Bool false
        | App (Const Not, f) -> Formula.mk_not' Void.absurd (of_term f)
        | App ((App (Const And, f1)), f2) -> Formula.mk_and (of_term f1) (of_term f2)
        | App ((App (Const Or , f1)), f2) -> Formula.mk_or  (of_term f1) (of_term f2)
        | App ((App (Const (Eq  _) , f1)), f2) -> Formula.mk_pred Eq  [arith into_id f1; arith into_id f2]
        | App ((App (Const (Neq _) , f1)), f2) -> Formula.mk_pred Neq [arith into_id f1; arith into_id f2]
        | App ((App (Const (Leq _) , f1)), f2) -> Formula.mk_pred Le  [arith into_id f1; arith into_id f2]
        | App ((App (Const (Geq _) , f1)), f2) -> Formula.mk_pred Ge  [arith into_id f1; arith into_id f2]
        | App ((App (Const (Lt  _) , f1)), f2) -> Formula.mk_pred Lt  [arith into_id f1; arith into_id f2]
        | App ((App (Const (Gt  _) , f1)), f2) -> Formula.mk_pred Gt  [arith into_id f1; arith into_id f2]
        | _ -> assert false
      in fun x -> of_term (Fpat.Formula.term_of x)

  let abstracion_env : simple_ty Hflz.hes -> Fpat.PredSubst.t -> Hflmc2_abstraction.env =
    fun hes subst ->
      let subst : Fpat.Pred.t StrMap.t =
        StrMap.of_alist_exn @@ List.map subst ~f:begin function
          | Fpat.Idnt.V x, pred -> x, pred
          | _ -> assert false
        end
      in
      let lookup_pred : TraceVar.aged -> Fpat.Pred.t option =
        StrMap.find subst <<< TraceVar.string_of_aged
      in
      let lookup_pred_exn : TraceVar.aged -> Fpat.Pred.t =
        StrMap.find_exn subst <<< TraceVar.string_of_aged
      in
      let rec abstraction_ty_of_aged (aged : TraceVar.aged) : abstraction_ty =
        let sty        = Type.unsafe_unlift @@ TraceVar.type_of_aged aged in
        let args, ()   = Type.decompose_arrow sty in
        let tenv, pred = lookup_pred_exn aged in
        let new_args' =
          let tv_args = TraceVar.mk_childlen aged in
          List.map2_exn args tv_args ~f:begin fun arg tv_arg ->
            match arg.ty with
            | TyInt     -> { arg with ty = TyInt }
            | TySigma _ -> { arg with ty = TySigma (abstraction_ty_of_trace_var tv_arg) }
          end
        in
        let pred : Formula.t =
          let int_args =
            List.map (args_of_pred_var (HornClause.PredVar aged)) ~f:begin function
            | Local { name; _ } -> name
            | _ -> assert false
            end
          in
          let formula_vars =
            List.map tenv ~f:begin function
            | Fpat.Idnt.V x, _ -> x
            | _ -> assert false
            end
          in
          (* Log.debug begin fun m -> m ~header:"type_of_" "@[<v>%a@;%a@]" *)
          (*   Print.(list_set id) int_args *)
          (*   Print.(list_set string) formula_args *)
          (* end; *)
          let into_map =
            let map = StrMap.of_alist_exn @@
              List.map2_exn formula_vars int_args ~f:begin fun fx ix ->
                fx, { ix with ty = `Int }
              end
            in
            fun x -> StrMap.find_exn map x
          in
          Formula.mk_not @@ formula into_map @@ pred
        in
        Type.mk_arrows new_args' (TyBool[pred])
      and abstraction_ty_of_trace_var : TraceVar.t -> abstraction_ty =
        fun tv ->
          let on_age age =
            let aged = TraceVar.(mk_aged ~age tv) in
            match lookup_pred aged with
            | Some _ -> Some (abstraction_ty_of_aged aged)
            | None -> None (* 生成されたが呼び出されなかった場合 *)
          in
          let abstraction_ty =
            let n = match Hashtbl.find TraceVar.counters tv with
              | None -> 0
              | Some n -> n
            in
            (* Log.debug begin fun m -> m ~header:"TV" "%a : %d" *)
            (*   TraceVar.pp_hum tv n *)
            (* end; *)
            match List.filter_map (List.init n ~f:on_age) ~f:Fn.id with
            | [] -> Type.map_ty (Fn.const []) @@
                      Type.unsafe_unlift @@ TraceVar.type_of tv
            (* NOTE
             * Duplication is removed when merged with old environmet.
             * See Hflmc2_abstraction.merge_env *)
            | tys -> Type.merges (@) tys
          in
          abstraction_ty
      in
      IdMap.of_list @@ List.map hes ~f:begin fun rule ->
        rule.var, abstraction_ty_of_trace_var (TraceVar.mk_nt rule.var)
      end
end

let is_valid : formula -> bool =
  fun f -> Fpat.SMTProver.is_valid_dyn (ToFpat.formula f)

let solve : simple_ty Hflz.hes -> t list -> Hflmc2_abstraction.env =
  fun hes hccs ->
    let hccs' = ToFpat.hccs hccs in
    let map = Fpat.HCCSSolver.solve_dyn hccs' in
    Log.debug begin fun m -> m ~header:"FpatAnswer" "%a"
      Fpat.PredSubst.pr map;
    end;
    OfFpat.abstracion_env hes map
