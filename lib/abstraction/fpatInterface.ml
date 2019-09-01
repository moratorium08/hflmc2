
open Hflmc2_util
open Hflmc2_syntax

module Log = (val Logs.src_log @@ Logs.Src.create "FpatInterface")

(* Initialize *)

let () =
  Fpat.FPATConfig.set_default();
  Fpat.PredAbst.incomplete_opt := false

(* Conversion *)

(* Boolean formula *)
type bvar = (string * [`Pos|`Neg])
let negate_var (x, p) : bvar = match p with
  | `Pos -> (x, `Neg)
  | `Neg -> (x, `Pos)
type bformula = (bvar, Void.t) Formula.gen_t

let rec of_arith : Arith.t -> Fpat.Formula.t = function
  | Int n -> Fpat.Formula.of_term @@ Fpat.Term.mk_const (Fpat.Const.Int n)
  | Var x ->
      let x' = Fpat.Idnt.make (Id.to_string x) in
      Fpat.Formula.mk_var x' []
  | Op(op, [a1;a2]) ->
      let op' = Fpat.Term.mk_const @@ match op with
        | Add  -> Fpat.Const.Add Fpat.Type.mk_int
        | Sub  -> Fpat.Const.Sub Fpat.Type.mk_int
        | Mult -> Fpat.Const.Mul Fpat.Type.mk_int
      in Fpat.Formula.of_term @@ Fpat.Term.mk_app op'
            [ Fpat.Formula.term_of @@ of_arith a1
            ; Fpat.Formula.term_of @@ of_arith a2 ]
  | Op(_,_) -> assert false

let rec of_formula : Formula.t -> Fpat.Formula.t = function
  | Bool true | And [] ->
      Fpat.Formula.mk_true
  | Bool false | Or [] ->
      Fpat.Formula.mk_false
  | Or (f::fs) ->
      List.fold_left fs ~init:(of_formula f) ~f:begin fun f1 f2 ->
        Fpat.Formula.mk_or f1 (of_formula f2)
      end
  | And (f::fs) ->
      List.fold_left fs ~init:(of_formula f) ~f:begin fun f1 f2 ->
        Fpat.Formula.mk_and f1 (of_formula f2)
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
            [ Fpat.Formula.term_of @@ of_arith a1
            ; Fpat.Formula.term_of @@ of_arith a2 ]
  | Pred(_,_) -> assert false
  | Var _ -> assert false

let to_bformula : Fpat.Formula.t -> bformula =
  let rec to_formula : Fpat.Term.t -> bformula =
    let open Fpat.Term in
    function
    | Const True  -> Bool true
    | Const False -> Bool false
    | App (Const Not, f) -> Formula.mk_not' negate_var (to_formula f)
    | App ((App (Const And, f1)), f2) ->
        Formula.mk_and (to_formula f1) (to_formula f2)
    | App ((App (Const Or , f1)), f2) ->
        Formula.mk_or  (to_formula f1) (to_formula f2)
    | Var (V x) -> Formula.Var (x, `Pos)
    | _ -> assert false
  in to_formula <<< Fpat.Formula.term_of

(* Utility *)

let ( ==> ) : Formula.t -> Formula.t -> bool =
  fun f1 f2 ->
    Fpat.SMTProver.is_valid_dyn
      (Fpat.Formula.imply (of_formula f1) (of_formula f2))

let ( <=> ) : Formula.t -> Formula.t -> bool =
  fun f1 f2 -> f1 ==> f2 && f2 ==> f1

let is_valid : Formula.t -> bool =
  fun f -> Formula.Bool true ==> f

let is_consistent_set : Formula.t list -> bool =
  fun fs -> not (Formula.mk_ands fs ==> Formula.Bool false)

(* phiをpredsのみで（否定を使わずに）近似．弱い方に倒す *)
let weakest_pre_cond' : Formula.t -> Formula.t list -> bformula =
  fun phi preds ->
    let env = [] in
    let pbs =
      List.mapi preds ~f:begin fun i pred ->
        let p = of_formula pred in
        let x = Fpat.(Formula.of_term
                      @@ Term.mk_var (Idnt.make ("x"^string_of_int i))) in
                      (* NOTE: ith predicate is named "xi" *)
        (p, x)
      end
    in
    phi
    |> of_formula
    |> Fpat.PredAbst.weakest env pbs
    |> fst
    |> to_bformula


(* phiをpredsのみで（否定を使わずに）近似．強い方に倒す *)
(* TODO:
 *  phi=true; preds={n<0; n>=0}のとき，trueが返ってくるが，
 *  n<0 \/ n>=0 が返ってきてくれたほうがabstractionの結果は良くなる
 *  誤差の範囲かも知れないけど（要検証）
 * *)
let strongest_post_cond' : Formula.t -> Formula.t list -> bformula =
  fun phi preds ->
    Formula.mk_not' negate_var
      @@ weakest_pre_cond'
          (Formula.mk_not phi)
          (List.map preds ~f:Formula.mk_not)

let aux_in_DNF : bformula -> int list list =
  fun phi ->
    List.map (Formula.to_DNF phi) ~f:begin
      List.map ~f:begin function
        | Formula.Var (x, `Neg) ->
            int_of_string @@ String.lstrip ~drop:(fun c -> c='x') x
        | _ -> assert false
      end
    end
let weakest_pre_cond : Formula.t -> Formula.t list -> int list list =
  fun phi preds -> aux_in_DNF @@ weakest_pre_cond' phi preds
let strongest_post_cond : Formula.t -> Formula.t list -> int list list =
  fun phi preds -> aux_in_DNF @@ strongest_post_cond' phi preds

