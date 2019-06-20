open Hflmc2.Util
open Hflmc2.Syntax
open Type

let () as _setup_logger =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level ~all:true (Some Debug)

let n = Id.gen ~name:"n" TyInt
let z = Id.gen ~name:"z" TyInt
let _X = Id.gen ~name:"X" @@ TyArrow(z, TyBool ())

(* empty *)
(* let _X_ty = TyArrow(z, TyBool []) *)
(* let _X_ty = TyArrow(z, TyBool Formula.[Pred(Ge, Arith.[mk_var z; mk_int 0])]) *)
(* let _X_ty = TyArrow(z, TyBool Formula.[Pred(Eq, Arith.[mk_var z; mk_int 0])]) *)
let _X_ty = TyArrow(z, TyBool
              Formula.[ Pred(Eq, Arith.[mk_var z; mk_int 0])
                      ; Pred(Eq, Arith.[mk_var z; mk_int 1])
                      (* ; Pred(Eq, Arith.[mk_var z; mk_int 2]) *)
                      ])
(* let _X_ty = (TyArrow(z, TyBool *)
(*                 Formula.[ Pred(Eq, Arith.[mk_var z; mk_int 0]) *)
(*                         ; Pred(Ge, Arith.[mk_var z; mk_int 1]) *)
(*                         ])) *)

let gamma = IdMap.singleton _X _X_ty

(* example 1 *)
(* S   = X n || n < 0
 * X y = y = 0 || y >= 1 && X (y - 1)
 *)

let psi =
  let open Hflz in
  let y = Id.gen ~name:"y" TyInt in
  let y_eq_0 = Pred(Eq , Arith.[mk_var y; mk_int 0]) in
  let y_ge_1 = Pred(Ge, Arith.[mk_var y; mk_int 1]) in
  let rest   = App(Var _X, Arith(Arith.(mk_op Sub [mk_var y; mk_int 1]))) in
  Or(App(Fix( _X, Abs(y,
                      Or( y_eq_0
                        , And( y_ge_1
                             , rest)))
            , Fixpoint.Greatest),
         Arith(Arith.mk_var n)),
     Pred(Lt, Arith.[mk_var n; mk_int 0]))

let phi = Simplify.hfl @@ Hflmc2.Abstraction.abstract gamma psi

let () =
  Logs.info @@ fun m -> m "abstracted formula:@ %a" Format_.hfl phi;
  match Hflmc2.Modelcheck.run phi with
  | Ok() -> Fmt.pr "Sat"
  | Error cex ->
      let open Hflmc2.Modelcheck in
      Format_.pr "Counterexample: %a@."
        Sexp.pp_hum (sexp_of_counterexample cex);
      Format_.pr "Counterexample: %a@."
        Sexp.pp_hum (sexp_of_counterexample (simplify cex));
      ()

