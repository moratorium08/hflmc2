open Hflmc2.Util
open Hflmc2.Syntax
open Type

let _change_log_level_of_specified_src () =
  let quiet = ["Abstraction"] in
  let logs = Logs.Src.list() in
  List.iter logs ~f:begin fun src ->
    if List.mem quiet (Logs.Src.name src) ~equal:String.equal
    then Logs.Src.set_level src None
    else ()
  end

let () as _setup_log =
  let setup style_renderer level =
    Format.set_margin 100;
    Fmt_tty.setup_std_outputs ?style_renderer ();
    let pp_header ppf (src, level, header) =
      let src_str =
        if Logs.Src.(equal src Logs.default)
        then None
        else Some (Logs.Src.name src)
      in
      let level_str, style = match (level : Logs.level) with
        | App     -> "App"     , Logs_fmt.app_style
        | Error   -> "Error"   , Logs_fmt.err_style
        | Warning -> "Warning" , Logs_fmt.warn_style
        | Info    -> "Info"    , Logs_fmt.info_style
        | Debug   -> "Debug"   , Logs_fmt.debug_style
      in
      let (<+) x y = match x with None -> y | Some x -> x ^ ":" ^ y in
      let (+>) x y = match y with None -> x | Some y -> x ^ ":" ^ y in
      let str = src_str <+ level_str +> header in
      Fmt.pf ppf "@[<v 2>[%a]@ @]" Fmt.(styled style string) str
    in
    let reporter =
      { Logs.report = fun src level ~over k msgf ->
          let k _ = over (); k () in
          msgf @@ fun ?header ?tags:_ fmt ->
            let ppf = Fmt.stdout in
            Format.kfprintf k ppf ("%a@[" ^^ fmt ^^ "@]@.") pp_header (src, level, header)
      }
    in
    Logs.set_reporter reporter;
    Logs.set_level level
  in
  let open Cmdliner in
  let setup_log =
    Term.(const setup
          $ Fmt_cli.style_renderer ()
          $ Logs_cli.level ())
  in
  match Term.(eval (setup_log, info "setup_log")) with
  | `Ok ()        -> ()
  | `Error `Parse -> assert false
  | `Error `Term  -> assert false
  | `Error `Exn   -> assert false
  | `Version      -> assert false
  | `Help         -> assert false

let n = Id.gen ~name:"n" TyInt
let z = Id.gen ~name:"z" TyInt
let _S = Id.gen ~name:"S" @@ TyBool()
let _S_ty = TyBool []
let _X = Id.gen ~name:"X" @@ TyArrow(z, TyBool ())
(* let _X_ty = TyArrow(z, TyBool []) *)
let _X_ty = TyArrow(z, TyBool Formula.[Pred(Ge, Arith.[mk_var z; mk_int 0])])
(* let _X_ty = TyArrow(z, TyBool Formula.[Pred(Eq, Arith.[mk_var z; mk_int 0])]) *)
(* let _X_ty = TyArrow(z, TyBool *)
(*               Formula.[ Pred(Eq, Arith.[mk_var z; mk_int 0]) *)
(*                       ; Pred(Eq, Arith.[mk_var z; mk_int 1]) *)
(*                       (* ; Pred(Eq, Arith.[mk_var z; mk_int 2]) *) *)
(*                       ]) *)
let _X_ty = (TyArrow(z, TyBool
                Formula.[ Pred(Eq, Arith.[mk_var z; mk_int 0])
                        ; Pred(Ge, Arith.[mk_var z; mk_int 1])
                        ]))

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
  Logs.app @@ fun m -> m ~header:"AbstractedFormula" "%a"
    Format_.hfl_hes phi

let () =
  match Hflmc2.Modelcheck.run phi with
  | Ok() ->
      Fmt.pr "Sat@."
  | Error cex ->
      let open Hflmc2.Modelcheck in
      Format_.pr "@[<2>Counterexample: %a@]@."
        Sexp.pp_hum (sexp_of_counterexample cex);
      Format_.pr "@[<2>Counterexample: %a@]@."
        Sexp.pp_hum (sexp_of_counterexample (simplify cex))

