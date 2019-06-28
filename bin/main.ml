
open Hflmc2
open Util
open Syntax

module Log = (val Logs.src_log @@ Logs.Src.create ~doc:"Main" "Main")

let cegar_loop psi gamma =
  let phi = Abstraction.abstract gamma psi in
  match Modelcheck.run phi with
  | Ok() ->
      Fmt.pr "Sat@."
  | Error cex ->
      let open Hflmc2.Modelcheck in
      begin Log.app @@ fun m ->
        m "@[<2>Counterexample: %a@]@."
          Sexp.pp_hum (sexp_of_counterexample (simplify cex))
      end;
      Fmt.pf Fmt.stdout "Unimplemented@."

let main () =
  match Hflmc2.Option.parse() with
  | None ->
      Fmt.pr "No input specified. try `--help`@."
  | Some input_file ->
      let psi = Parser.parse_file input_file in
      begin Log.app @@ fun m -> m ~header:"Input" "%a"
        Format.(hflz_hes simple_ty_) psi
      end;
      let gamma =
        IdMap.of_list @@ List.map psi ~f:begin fun { var; _ } ->
          var, Type.map_ty (fun () -> []) var.ty
        end
      in
      cegar_loop psi gamma

let () = main ()
