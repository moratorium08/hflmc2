open Hflmc2
open Util
open Syntax
open Type

(*============================================================================*)

module Log = (val Logs.src_log @@ Logs.Src.create __MODULE__)
let _ = Hflmc2.Options.parse ~argv:(Array.append [|"dummy_file"|] Sys.argv) ()

(*============================================================================*)

let n = Id.gen ~name:"n" TyInt
let z = Id.gen ~name:"z" TyInt
let _S = Id.gen ~name:"S" @@ TyBool()
let _S_ty = TyBool []
let _X = Id.gen ~name:"X" @@ TyArrow(z, TyBool ())
(* let _X_ty = TyArrow(z, TyBool []) *)
(* let _X_ty = TyArrow(z, TyBool Formula.[Pred(Ge, Arith.[mk_var z; mk_int 0])]) *)
let _X_ty = TyArrow(z, TyBool Formula.[Pred(Ge, Arith.[mk_var z; mk_int 0])])
(* let _X_ty = TyArrow(z, TyBool Formula.[Pred(Eq, Arith.[mk_var z; mk_int 0])]) *)
(* let _X_ty = TyArrow(z, TyBool *)
(*               Formula.[ Pred(Eq, Arith.[mk_var z; mk_int 0]) *)
(*                       ; Pred(Eq, Arith.[mk_var z; mk_int 1]) *)
(*                       ; Pred(Eq, Arith.[mk_var z; mk_int 2]) *)
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
                            (* ; Pred(Lt, Arith.[mk_var n; mk_int 0]) *)
                            ; App (mk_var _X, Arith(Arith.(mk_op Sub [mk_int 0; mk_var n])))
                            ]
    ; fix  = Greatest
    }
  ; { var  = _X ; body = abs ; fix = Greatest }
  ]

let () =
    begin Log.app @@ fun m -> m ~header:"Predicate" "@[<v>%a@]@."
      Print.(list @@ fun ppf -> pf ppf "@[<2>%a@]" @@ pair ~sep:(fun ppf () -> pf ppf " :@ ")
        id
        abstraction_ty)
        (IdMap.to_alist gamma)
    end

let phi = Hflmc2.Abstraction.abstract gamma psi

let () =
  Log.app begin fun m -> m ~header:"AbstractedFormula" "%a"
    Print.hfl_hes phi
  end

let () =
  match Hflmc2.Modelcheck.run phi with
  | Ok() ->
      Fmt.pr "Sat@."
  | Error cex ->
      let open Hflmc2.Modelcheck in
      Print.pr "@[<v 2>Counterexample:@ = %a@ → %a@]@."
        Sexp.pp_hum
          Counterexample.(sexp_of_t cex)
        (Print.list Sexp.pp_hum)
          Counterexample.(List.map ~f:sexp_of_normalized (normalize (simplify cex)))
