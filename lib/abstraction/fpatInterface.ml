
open Hflmc2_util
open Hflmc2_syntax

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
  | Bool true ->
      Fpat.Formula.mk_true
  | Bool false ->
      Fpat.Formula.mk_false
  (* | Var x -> *)
  (*     let x' = Fpat.Idnt.make (Id.to_string x) in *)
  (*     Fpat.Formula.mk_var x' [] *)
  | Or(f1,f2) ->
      Fpat.Formula.mk_or (of_formula f1) (of_formula f2)
  | And(f1,f2) ->
      Fpat.Formula.mk_and (of_formula f1) (of_formula f2)
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

let ( ==> ) : Formula.t -> Formula.t -> bool =
  fun f1 f2 -> Fpat.Z3Interface.z3#is_valid [] (Fpat.Formula.imply (of_formula f1) (of_formula f2))

let ( <=> ) : Formula.t -> Formula.t -> bool =
  fun f1 f2 -> f1 ==> f2 && f2 ==> f1

let is_valid : Formula.t -> bool =
  fun f -> Formula.Bool true ==> f

let is_consistent_set : Formula.t list -> bool =
  fun fs -> not (Formula.mk_ands fs ==> Formula.Bool false)

