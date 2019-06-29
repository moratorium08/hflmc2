open Hflmc2
open Util
open Syntax
open Type

(*============================================================================*)

module Log = (val Logs.src_log @@ Logs.Src.create ~doc:"Main" "Main")
let _ = Hflmc2.Option.parse()

(*============================================================================*)

let _ = Hflmc2.Option.parse()

let n = Id.gen ~name:"n" TyInt
let z = Id.gen ~name:"z" TyInt
let _S = Id.gen ~name:"S" @@ TyBool()
let _S_ty = TyBool []
let _X = Id.gen ~name:"X" @@ TyArrow(z, TyBool ())
let _X_ty = TyArrow(z, TyBool Formula.[Pred(Ge, Arith.[mk_var z; mk_int 0])])
(* let _X_ty = TyArrow(z, TyBool Formula.[Pred(Eq, Arith.[mk_var z; mk_int 0])]) *)
(* let _X_ty = TyArrow(z, TyBool *)
(*               Formula.[ Pred(Eq, Arith.[mk_var z; mk_int 0]) *)
(*                       ; Pred(Eq, Arith.[mk_var z; mk_int 1]) *)
(*                       (* ; Pred(Eq, Arith.[mk_var z; mk_int 2]) *) *)
(*                       ]) *)
(* let _X_ty = (TyArrow(z, TyBool *)
(*                 Formula.[ Pred(Eq, Arith.[mk_var z; mk_int 0]) *)
(*                         ; Pred(Ge, Arith.[mk_var z; mk_int 1]) *)
(*                         ])) *)

let gamma = IdMap.of_list [ (_S, _S_ty); (_X, _X_ty) ]

let psi =
  let open Hflz in
  let y = Id.gen ~name:"y" TyInt in
  let y_eq_0 = Pred(Eq , Arith.[mk_var y; mk_int 0]) in
  let y_ge_1 = Pred(Ge, Arith.[mk_var y; mk_int 1]) in
  let rest = App(Var _X, Arith(Arith.(mk_op Sub [mk_var y; mk_int 1]))) in
  let abs = Abs(y, Or[ y_eq_0
                     ; And [ y_ge_1
                           ; rest]
                     ])
  in
  [ { var  = _S ; body = Or [ App (mk_var _X, Arith(Arith.mk_var n))
                            ; Pred(Lt, Arith.[mk_var n; mk_int 0]) ]
    ; fix  = Greatest
    }
  ; { var  = _X ; body = abs ; fix = Greatest }
  ]


let phi = Hflmc2.Abstraction.abstract gamma psi

let () =
  Log.app @@ fun m -> m ~header:"AbstractedFormula" "%a"
    Format.hfl_hes phi

let () =
  match Hflmc2.Modelcheck.run phi with
  | Ok() ->
      Fmt.pr "Sat@."
  | Error cex ->
      let open Hflmc2.Modelcheck in
      Format.pr "@[<v 2>Counterexample:@ = %a@ → %a@]@."
        Sexp.pp_hum (sexp_of_counterexample cex)
        Sexp.pp_hum (sexp_of_counterexample (simplify cex))
