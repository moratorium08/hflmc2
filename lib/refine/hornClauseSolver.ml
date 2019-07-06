open Hflmc2_util
open Hflmc2_syntax
open Hflmc2_syntax.Type

open HornClause

module Log = (val Logs.src_log @@ Logs.Src.create "Refine")

let () = Fpat.FPATConfig.set_default()

(* TODO refactering *)

module ToFpat = struct

  let idnt_of_trace_var : TraceVar.t -> Fpat.Idnt.t =
    fun tv -> Fpat.Idnt.make (Print.strf "%a" TraceVar.pp_hum tv)

  let term_of_trace_var : TraceVar.t -> Fpat.Term.t =
    fun tv -> Fpat.Term.mk_var (idnt_of_trace_var tv)

  let typed_term_of_trace_var : TraceVar.t -> Fpat.TypTerm.t =
    fun tv ->
      assert (TraceVar.type_of tv = TyInt);
      Fpat.TypTerm.make (term_of_trace_var tv) Fpat.Type.mk_int

  let pva : pred_var -> Fpat.Pva.t =
    fun (PredVar tv as pv) ->
      Fpat.Pva.make
        (idnt_of_trace_var tv)
        (List.map (args_of_pred_var pv) ~f:typed_term_of_trace_var)

  let pred_var : pred_var -> Fpat.PredVar.t =
    fun (PredVar tv as pv) ->
      let typ_env =
        List.map (args_of_pred_var pv) ~f:begin fun tv ->
          idnt_of_trace_var tv, Fpat.Type.mk_int
        end
      in Fpat.PredVar.make (idnt_of_trace_var tv) typ_env

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
      let subst =
        StrMap.of_alist_exn @@ List.map subst ~f:begin function
          | Fpat.Idnt.V x, pred -> x, pred
          | _ -> assert false
        end
      in
      let fuga : simple_ty Id.t -> abstraction_ty =
        fun nt ->
          let rec go (tv : TraceVar.t) (sty : simple_ty) : abstraction_ty =
            let args, ()   = Type.decompose_arrow sty in
            let tenv, pred = StrMap.find_exn subst (TraceVar.to_string tv) in
            let pred : Formula.t =
              let int_args =
                List.map (args_of_pred_var (HornClause.PredVar tv)) ~f:begin function
                | Local { name; _ } -> name
                | _ -> assert false
                end
                (* List.filter args ~f:begin fun x -> *)
                (*   x.ty = TyInt *)
                (* end *)
              in
              let formula_args =
                List.map tenv ~f:begin function
                | Fpat.Idnt.V x, _ -> x
                | _ -> assert false
                end
              in
              (* Log.debug begin fun m -> m ~header:"fuga" "@[<v>%a@;%a@]" *)
              (*   Print.(list_set id) int_args *)
              (*   Print.(list_set string) formula_args *)
              (* end; *)
              let into_map =
                let map = StrMap.of_alist_exn @@
                  List.map2_exn formula_args int_args ~f:begin fun fx ix ->
                    fx, { ix with ty = `Int }
                  end
                in
                fun x -> StrMap.find_exn map x
              in
              formula into_map @@ pred
            in
            let tv_args = TraceVar.mk_locals tv in
            let new_args' =
              List.map2_exn args tv_args ~f:begin fun arg tv_arg ->
                match arg.ty with
                | TyInt -> { arg with ty = TyInt }
                | TySigma sty -> { arg with ty = TySigma (go tv_arg sty) }
              end
            in
            Type.mk_arrows new_args' (TyBool[pred])
          in

          let on_age age =
            let tv = TraceVar.mk_nt ~age nt in
            match StrMap.find subst (TraceVar.to_string tv) with
            | Some _ -> Some (go tv nt.ty)
            | None -> None
          in
          let rec go acc age =
            match on_age age with
            | Some ty -> go (ty::acc) (age+1)
            | None    -> acc
          in
          let abstraction_ty =
            let n = match Hashtbl.find TraceVar.counters (Id.remove_ty nt) with
              | None -> 0
              | Some n -> n
            in
            match List.filter_map (List.init n ~f:on_age) ~f:Fn.id with
            | [] -> Type.map_ty (Fn.const []) nt.ty
            | tys -> Type.merges (@) tys
          in
          (* Log.debug begin fun m -> m ~header:"MergeTypes" "%s: @[<v>%a@]" *)
          (*   nt.name *)
          (*   Print.(abstraction_ty) abstraction_ty *)
          (* end; *)
          abstraction_ty
      in
      IdMap.of_list @@ List.map hes ~f:(fun rule -> rule.var, fuga rule.var)
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
            List.remove_consecutive_duplicates (xs1@xs2) ~equal:begin fun x1 x2 ->
              match x1, x2 with
              | `I x1, `I x2 -> TraceVar.equal x1 x2
              | `E x1, `E x2 -> Id.eq x1 x2
              | _ -> false
            end
          in
          let map = StrMap.of_alist_exn @@ List.map xs ~f:begin function
            | `I x -> TraceVar.to_string x, `I x
            | `E n -> Id.to_string n, `E n
            end
          in fun x -> StrMap.find_exn map x
        in
        Some (OfFpat.formula rev_map ip)
    | exception Fpat.InterpProver.NoInterpolant ->
        None

let solve : simple_ty Hflz.hes -> t list -> Hflmc2_abstraction.env =
  fun hes hccs ->
    let hccs' = ToFpat.hccs hccs in
    let map = Fpat.HCCSSolver.solve_dyn hccs' in
    (* Print.print Fpat.PredSubst.pr map; *)
    OfFpat.abstracion_env hes map

