
open Hflmc2_util

(******************************************************************************)
(* Options                                                                    *)
(******************************************************************************)

let oneshot = ref false

module Abstraction = struct
  (* NOTE Actual value is set by Cmdliner *)
  let max_ors           = ref 0
  let max_ands          = ref 0
  let cartesian         = ref true
  let exhaustive_search = ref true
end

(******************************************************************************)
(* Util(?)                                                                    *)
(******************************************************************************)

let set_ref ref x = ref := x
let set_ref_opt ref x = match x with None -> () | Some x -> ref := x
let set_debug_modules modules =
  let logs = Logs.Src.list() in
  List.iter logs ~f:begin fun src ->
    if List.mem modules (Logs.Src.name src) ~equal:String.equal
    then begin
      Logs.Src.set_level src (Some Debug)
    end
  end

(******************************************************************************)
(* Parser                                                                     *)
(******************************************************************************)

type params =
  { input : string [@pos 0] [@docv "FILE"]
  (* { input : string option [@docv "FILE"] *)

  (* Logging *)
  ; debug : string list [@default []] [@docv "MODULE,..."]
    (** Enable debug log of modules *)

  (* Whole procedure *)
  ; oneshot : bool [@default false]
    (** Do not loop *)

  (* Abstraction *)
  ; abst_max_ors : int [@default 10]
    (** Maximum number of disjunction in predicate abstraction *)

  ; abst_max_ands : int [@default 1]
    (** Maximum number of conjunction in predicate abstraction *)

  ; abst_exhaustive_search : bool [@default false]
    (** Do exhaustive search in predicate abstraction *)

  ; abst_no_cartesian : bool [@default false]
    (** Do cartesian search in predicate abstraction
        `--abst-exhaustive-search` is preferred when both are present *)
  }
  [@@deriving cmdliner,show]

let set_up_params params =
  set_debug_modules params.debug;
  set_ref Abstraction.max_ors           params.abst_max_ors;
  set_ref Abstraction.max_ands          params.abst_max_ands;
  set_ref Abstraction.exhaustive_search params.abst_exhaustive_search;
  set_ref Abstraction.cartesian         (not params.abst_no_cartesian);
  set_ref oneshot                       params.oneshot;
  params.input

(******************************************************************************)
(* Term                                                                       *)
(******************************************************************************)

let term_set_up_params () =
  Cmdliner.Term.(const set_up_params $ params_cmdliner_term ())

(* Log *)
let term_setup_log () =
  (*{{{*)
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
            Format.kfprintf k ppf ("%a@[" ^^ fmt ^^ "@]@.")
              pp_header (src, level, header)
      }
    in
    Logs.set_reporter reporter;
    Logs.set_level level
  in
    Cmdliner.Term.(const setup $ Fmt_cli.style_renderer () $ Logs_cli.level ())
(*}}}*)

let parse ?argv () : string option =
  let term () =
    let open Cmdliner.Term in
    const (fun _ file -> file)
      $ term_setup_log () (* NOTE order matters *)
      $ term_set_up_params ()
  in match Cmdliner.Term.(eval ?argv (term (), info "hflmc2")) with
  | `Ok file -> Some file
  | _     -> None

