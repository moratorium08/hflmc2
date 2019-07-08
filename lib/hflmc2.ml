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

let rec cegar_loop ?prev_cex loop_count psi gamma =
  (* Abstract *)
  let phi = Abstraction.abstract gamma psi in
  begin Log.app @@ fun m -> m ~header:"AbstractedProg" "@[<v>Loop %d@,%a@]"
    loop_count
    Print.hfl_hes phi
  end;
  (* Modelcheck *)
  match Modelcheck.run phi with
  | Ok() ->
      `Valid
  | Error cex ->
      let module C = Modelcheck.Counterexample in
      let cex = C.simplify cex in
      begin Log.app @@ fun m -> m ~header:"Counterexample" "@[<2>%a@]"
        Sexp.pp_hum (C.sexp_of_t cex)
      end;
      if Option.equal C.equal prev_cex (Some cex) then
        `NoProgress
      else
        (* Refine *)
        match Refine.run psi (List.hd_exn (C.normalize cex)) gamma with
        | `Refined new_gamma ->
            begin Log.app @@ fun m -> m ~header:"Predicate" "@[<v>%a@]@."
              Print.(list @@ fun ppf -> pf ppf "@[<2>%a@]" @@ pair ~sep:(fun ppf () -> pf ppf " :@ ")
                id
                abstraction_ty)
                (IdMap.to_alist new_gamma)
            end;
            cegar_loop ~prev_cex:cex (loop_count+1) psi new_gamma
        | `Feasible ->
            `Invalid

let main file =
  let psi = Syntax.parse_file file in
  begin Log.app @@ fun m -> m ~header:"Input" "%a@."
    Print.(hflz_hes simple_ty_) psi
  end;
  let gamma =
    IdMap.of_list @@ List.map psi ~f:begin fun { var; _ } ->
      var, Type.map_ty (fun () -> []) var.ty
    end
  in
  cegar_loop 1 psi gamma

