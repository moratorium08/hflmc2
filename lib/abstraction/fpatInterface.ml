
open Hflmc2_util
open Hflmc2_syntax

module Log = (val Logs.src_log @@ Logs.Src.create "FpatInterface")

(* Initialize *)

let () =
  let _ = Fpat.Z3Interface.z3 in
  let _ = Fpat.CSIsatInterface.interpolate in
  Fpat.FPATConfig.set_default();
  Fpat.PredAbst.incomplete_opt := false

(* Conversion *)

(* Boolean formula *)
type bvar = (string * [`Pos|`Neg])
  [@@deriving eq,ord,show,iter,map,fold,sexp]
let negate_var (x, p) : bvar = match p with
  | `Pos -> (x, `Neg)
  | `Neg -> (x, `Pos)
type bformula = (bvar, Void.t) Formula.gen_t
  [@@deriving eq,ord,show,iter,map,fold,sexp]

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
let is_unsat : Formula.t -> bool =
  fun f -> f ==> Formula.Bool false

let is_consistent_set : Formula.t list -> bool =
  fun fs -> not (Formula.mk_ands fs ==> Formula.Bool false)

let simplify = Trans.Simplify.formula ~is_true:is_valid ~is_false:is_unsat

module FpatReImpl = struct
  type def =
    { pred : Formula.t
    ; bvar : bvar }
    [@@deriving show,iter,map,fold,sexp]
  let equal_def   def1 def2 = String.equal   (fst def1.bvar) (fst def2.bvar)
  let compare_def def1 def2 = String.compare (fst def1.bvar) (fst def2.bvar)

  type defs = def array

  module type ConjunctionSig = sig
    type t
    val sexp_of_t : t -> Sexp.t
    val t_of_sexp : Sexp.t -> t
    val compare   : t -> t -> int
    val pp        : defs:defs -> Format.formatter -> t -> unit
    val size      : t -> int
    val singleton : len:int -> int -> t
    val true_     : len:int -> t
    val conj      : t -> t -> t
    val value     : defs -> t -> Formula.t
    val bvalue    : defs -> t -> bformula
    val (=~>)     : t -> t -> bool
  end
  module ConjArray : ConjunctionSig = struct
    (* represents conjunction of predicates 
     * If defs=[|p1;p2;p3|], [|true;false;true|] represents p1/\p3 *)
    type t = bool array
    let sexp_of_t  = Array.sexp_of_t Bool.sexp_of_t
    let t_of_sexp  = Array.t_of_sexp Bool.t_of_sexp
    let compare    = Array.compare Bool.compare
    let size pbs   = Array.count pbs ~f:Fn.id
    let pp ~defs:_ = Print.(array bool)

    let true_ ~len = Array.create ~len false
    let singleton ~len i =
      let pbs = Array.create ~len false in
      pbs.(i) <- true;
      pbs
    let conj pbs pbs' =
      Array.map2_exn pbs pbs' ~f:begin fun b1 b2 -> b1 || b2 end

    let value : defs -> t -> Formula.t =
      fun defs elt ->
        Array.fold2_exn defs elt ~init:(Formula.Bool true) ~f:begin fun acc pb b ->
          if b
          then Formula.mk_and acc pb.pred
          else acc
        end

    let bvalue : defs -> t -> bformula =
      fun defs elt ->
        Array.fold2_exn defs elt ~init:(Formula.Bool true) ~f:begin fun acc pb b ->
          if b
          then Formula.mk_and acc (Formula.mk_var pb.bvar)
          else acc
        end

    let (=~>) _ _ = Fn.todo()
  end
  module ConjInt : ConjunctionSig = struct
    (* represents conjunction of predicates
     * If defs=[|p1;p2;p3|], 0b101 represents p1/\p3 *)
    type t = int
      [@@deriving eq,ord,sexp]
    let _ = equal (* supress warning *)
    let pp ~defs =
      let bin_of_int d =
        if d < 0 then invalid_arg "bin_of_int" else
        let string_of_int = function
          | 0 -> "f"
          | 1 -> "t"
          | _ -> assert false
        in
        let rec aux acc d =
          if d = 0 then acc else
          aux (string_of_int (d land 1) :: acc) (d lsr 1)
        in
        let body =
          if d = 0 then "f" else
          String.concat (aux [] d) in
        let pudding = String.(init (Array.length defs - length body) ~f:(Fn.const 'f')) in
        pudding ^ body
      in fun ppf x ->
        Print.pf ppf "%2s" (bin_of_int x)

    let size pbs = Core.Int.popcount pbs

    let conj x y = x lor y

    let (=~>) x y = lnot ((lnot y) lor x) = 0 (* trivially x ⇒ y *)

    let true_ ~len:_ = 0
    let singleton ~len:_ i = 1 lsl i

    let value : defs -> t -> Formula.t =
      fun defs elt ->
        Formula.mk_ands @@ List.init (Array.length defs) ~f:begin fun i ->
          if elt land (1 lsl i) <> 0
          then defs.(i).pred
          else Formula.Bool true
        end

    let bvalue : defs -> t -> bformula =
      fun defs elt ->
        Formula.mk_ands @@ List.init (Array.length defs) ~f:begin fun i ->
          if elt land (1 lsl i) <> 0
          then Formula.mk_var defs.(i).bvar
          else Formula.Bool true
        end
  end
  module Conj = ConjInt

  let imply defs env elt phi =
    Formula.mk_and env (Conj.value defs elt) ==> phi
  let valid defs env elt =
    env ==> Conj.value defs elt

   let (=~>) pbs1 pbs2 = (* trivially pbs1 ⇒ pbs2 *)
     Array.for_all2_exn pbs1 pbs2 ~f:begin fun b1 b2 ->
       (not b2 || b1)
     end

  module Pbss = Set.Make'(struct
    include Conj
    include Core.Comparable.Make(Conj)
  end)
  module PbssAsKey = struct
    include Pbss
    include Core.Comparable.Make(Pbss)
  end

  type pbss = Pbss.t

  type guard = Formula.t

  let pp_pbss ~defs ppf pbss =
    Print.pf ppf "%a" Print.(list_set (Conj.pp ~defs)) @@ Pbss.to_list pbss

  let min_unsat_cores env defs : bformula list =
    let rec go unsat_pbss' sat_pbss' pbss =
      let unsat_pbss, sat_pbss =
        Pbss.partition_tf pbss ~f:begin fun pbs ->
          imply defs env pbs (Formula.Bool false)
        end
      in
      let unsat_pbss, sat_pbss =
        Pbss.union unsat_pbss unsat_pbss',
        Pbss.union sat_pbss   sat_pbss'
      in
        Set.map (module PbssAsKey) sat_pbss ~f:begin fun pbs ->
          Pbss.map sat_pbss ~f:begin fun pbs' ->
            Conj.conj pbs pbs'
          end
        end
        |> Set.to_list
        |> Pbss.union_list
        |> Set.diff -$- sat_pbss
        |> Pbss.filter ~f:begin fun pbs ->
             Conj.size pbs <= !Hflmc2_options.Abstraction.max_ands
           end
        |> Pbss.filter ~f:begin fun pbs -> (* これは停止性に必須っぽい *)
             (* satなやつより弱いのは当然satだから考えなくて良い *)
             not (Pbss.exists ~f:Conj.(fun pbs' -> pbs' =~> pbs) sat_pbss) &&
             (* unsatなやつより強いのは当然unsat *)
             not (Pbss.exists ~f:Conj.(fun pbs' -> pbs =~> pbs') unsat_pbss) &&
             true
           end
        |> begin fun pbss ->
            if Pbss.is_empty pbss
            then unsat_pbss
            else go unsat_pbss sat_pbss pbss
           end
    in
    let len = Array.length defs in
    let unsat_pbss = go
          Pbss.empty
          Pbss.empty
          (Pbss.of_list (List.init len ~f:(Conj.singleton ~len)))
    in
    Pbss.to_list unsat_pbss
    |> List.map ~f:(Conj.bvalue defs)
end

(* phiをpredsのみで（否定を使わずに）近似．弱い方に倒す *)
(* P => φ を満たすPのlistを返す *)
let weakest_pre_cond' : Formula.t -> Formula.t array -> bformula list =
  fun phi preds ->
    let defs =
      Array.mapi preds ~f:begin fun i pred ->
        let bvar = ("x"^string_of_int i, `Pos) in
        FpatReImpl.{pred; bvar}
      end
    in
    FpatReImpl.min_unsat_cores (Formula.mk_not phi) defs

(* phiをpredsのみで（否定を使わずに）近似．強い方に倒す *)
(* φ => Pを満たすPのlistを返す *)
let strongest_post_cond' : Formula.t -> Formula.t array -> bformula list =
  fun phi preds ->
    List.map ~f:(Formula.mk_not' negate_var)
      @@ weakest_pre_cond'
          (Formula.mk_not phi)
          (Array.map preds ~f:Formula.mk_not)

let to_index_repr : bformula -> int list list =
  fun phi ->
    List.map (Formula.to_DNF phi) ~f:begin
      List.map ~f:begin function
        | Formula.Var (x, `Neg) ->
            int_of_string @@ String.lstrip ~drop:(fun c -> c='x') x
        | _ -> assert false
      end
      >>> List.remove_duplicates ~equal:(=)
    end
    |> List.maximals' (Fn.flip List.subset)

let strongest_post_cond : Formula.t -> Formula.t array -> int list list =
  fun phi preds ->
    let bs = strongest_post_cond' phi preds in
    Log.debug begin fun m -> m ~header:"strongest_post_cond" "%a"
      Print.(list pp_bformula) bs
    end;
    to_index_repr @@ Formula.mk_ands bs

let min_valid_cores : Formula.t array -> int list list =
  strongest_post_cond (Bool true)

