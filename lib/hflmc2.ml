module Util        = Hflmc2_util
module Options     = Hflmc2_options
module Syntax      = Hflmc2_syntax
module Abstraction = Hflmc2_abstraction
module Modelcheck  = Hflmc2_modelcheck
module Refine      = Hflmc2_refine

open Util
open Syntax

let log_src = Logs.Src.create "Main"
module Log = (val Logs.src_log @@ log_src)

type result = [ `Valid | `Invalid ]

let show_result = function
  | `Valid      -> "Valid"
  | `Invalid    -> "Invalid"

module CexSet = Set.Make'(Modelcheck.Counterexample.Normalized)
(* module CexSet = Set.Make'(Modelcheck.Counterexample) *)

let measure_time f =
  let start  = Unix.gettimeofday () in
  let result = f () in
  let stop   = Unix.gettimeofday () in
  result, stop -. start

let times = Hashtbl.create (module String)
let add_mesure_time tag f =
  let r, time = measure_time f in
  let if_found t = Hashtbl.set times ~key:tag ~data:(t+.time) in
  let if_not_found _ = Hashtbl.set times ~key:tag ~data:time in
  Hashtbl.find_and_call times tag ~if_found ~if_not_found;
  r
let all_start = Unix.gettimeofday ()
let report_times () =
  let total = Unix.gettimeofday() -. all_start in
  let kvs = Hashtbl.to_alist times @ [("total", total)] in
  match List.max_elt ~compare (List.map kvs ~f:(String.length<<<fst)) with
  | None -> Print.pr "no time records"
  | Some max_len ->
      Print.pr "Profiling:@.";
      List.iter kvs ~f:begin fun (k,v) ->
        let s =
          let pudding = String.(init (max_len - length k) ~f:(Fn.const ' ')) in
          "  " ^ k ^ ":" ^ pudding
        in Print.pr "%s %f sec@." s v
      end

let rec cegar_loop prev_cexs loop_count psi gamma =
  Log.app begin fun m -> m ~header:"TopOfLoop" "Loop count: %d"
      loop_count
  end;
  Log.app begin fun m -> m ~header:"Environmet" "%a"
    Abstraction.pp_env gamma
  end;
  (* Abstract *)
  let phi = add_mesure_time "Abstraction" @@ fun () ->
    Abstraction.abstract gamma psi
  in
  Log.app begin fun m -> m ~header:"AbstractedProg" "%a"
    Print.hfl_hes phi
  end;
  (* Modelcheck *)
  match add_mesure_time "Modelcheck" @@ fun () -> Modelcheck.run phi with
  | Ok() ->
      `Valid
  | Error cex ->
      let module C = Modelcheck.Counterexample in
      let cex = C.simplify cex in
      Log.app begin fun m -> m ~header:"Counterexample" "@[<2>%a@]"
        Sexp.pp_hum (C.sexp_of_t cex)
      end;
      (* Refine *)
      let new_cexs = CexSet.(diff (of_list (C.normalize cex)) prev_cexs) in
      if CexSet.is_empty new_cexs then
        Fn.fatal "NoProgress"
      else
        let new_gamma, next_cexs =
          if false then
            let next_cexs = CexSet.union prev_cexs new_cexs in
            let new_gamma =
              let rec loop gamma ncexs =
                match ncexs with
                | [] ->
                    Some gamma
                | ncex::ncexs ->
                    Log.info begin fun m -> m ~header:"Refine:cex" "%a"
                      C.pp_hum_normalized ncex
                    end;
                    begin match add_mesure_time "Refine" @@ fun () ->
                      Refine.run psi ncex gamma
                    with
                    | `Refined new_gamma -> loop new_gamma ncexs
                    | `Feasible -> None
                    end
              in loop gamma (CexSet.to_list new_cexs)
            in new_gamma, next_cexs
          else
            let ncex = List.hd_exn @@ CexSet.to_list new_cexs in
            let next_cexs = CexSet.add prev_cexs ncex in
            let new_gamma =
              Log.info begin fun m -> m ~header:"Refine:cex" "%a"
                C.pp_hum_normalized ncex
              end;
              begin match add_mesure_time "Refine" @@ fun () ->
                Refine.run psi ncex gamma
              with
              | `Refined new_gamma -> Some new_gamma
              | `Feasible -> None
              end
            in new_gamma, next_cexs
        in
          if !Options.oneshot then failwith "oneshot";
          match new_gamma with
          | Some new_gamma ->
              cegar_loop next_cexs (loop_count+1) psi new_gamma
          | None ->
              `Invalid

let main file =
  let psi, gamma = Syntax.parse_file file in
  Log.app begin fun m -> m ~header:"Input" "%a"
    Print.(hflz_hes simple_ty_) psi
  end;
  let psi = Syntax.Trans.Simplify.hflz_hes psi in
  Log.app begin fun m -> m ~header:"Simplified" "%a"
    Print.(hflz_hes simple_ty_) psi
  end;
  cegar_loop CexSet.empty 1 psi gamma

