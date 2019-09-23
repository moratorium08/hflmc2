module Util        = Hflmc2_util
module Options     = Hflmc2_options
module Syntax      = Hflmc2_syntax
module Abstraction = Hflmc2_abstraction
module Modelcheck  = Hflmc2_modelcheck
module Refine      = Hflmc2_refine

open Util
open Syntax

module Log = (val Logs.src_log @@ Logs.Src.create "Main")

type result = [ `Valid | `Invalid | `NoProgress ]

let show_result = function
  | `Valid      -> "Valid"
  | `Invalid    -> "Invalid"
  | `NoProgress -> "NoProgress"

module CexSet = Set.Make(Modelcheck.Counterexample)

let rec cegar_loop prev_cexs loop_count psi gamma =
  Log.app begin fun m -> m ~header:"TopOfLoop" "Loop count: %d"
      loop_count
  end;
  Log.app begin fun m -> m ~header:"Environmet" "%a"
    Abstraction.pp_env gamma
  end;
  (* Abstract *)
  let phi = Abstraction.Int_base.abstract gamma psi in
  Log.app begin fun m -> m ~header:"AbstractedProg" "%a"
    Print.hfl_hes phi
  end;
  (* Modelcheck *)
  match Modelcheck.run phi with
  | Ok() ->
      `Valid
  | Error cex ->
      let module C = Modelcheck.Counterexample in
      let cex = C.simplify cex in
      Log.app begin fun m -> m ~header:"Counterexample" "@[<2>%a@]"
        Sexp.pp_hum (C.sexp_of_t cex)
      end;
      if CexSet.mem prev_cexs cex then
        `NoProgress
      else
        (* Refine *)
        let ncexs = C.normalize cex in
        let rec loop gamma ncexs =
          match ncexs with
          | [] ->
              if !Options.oneshot then failwith "oneshot";
              cegar_loop (CexSet.add prev_cexs cex) (loop_count+1) psi gamma
          | ncex::ncexs ->
              begin match Refine.run psi ncex gamma with
              | `Refined new_gamma -> loop new_gamma ncexs;
              | `Feasible -> `Invalid
              end
        in
        loop gamma ncexs

let main file =
  let psi, gamma = Syntax.parse_file file in
  Log.app begin fun m -> m ~header:"Input" "%a"
    Print.(hflz_hes simple_ty_) psi
  end;
  cegar_loop CexSet.empty 1 psi gamma

