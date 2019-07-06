
open Hflmc2
open Util
open Syntax

module Log = (val Logs.src_log @@ Logs.Src.create __MODULE__)


(* TODO move *)
let merge_env : Hflmc2_abstraction.env -> Hflmc2_abstraction.env -> Hflmc2_abstraction.env =
  fun gamma1 gamma2 -> IdMap.merge gamma1 gamma2 ~f:begin fun ~key:_ -> function
    | `Left l -> Some l
    | `Right r -> Some r
    | `Both (l, r) -> Some (Type.merge (@) l r)
    end

let rec cegar_loop ?prev_cex psi gamma =
  let phi = Abstraction.abstract gamma psi in
  begin Log.app @@ fun m -> m ~header:"Prog" "%a"
    Print.hfl_hes phi
  end;
  match Modelcheck.run phi with
  | Ok() ->
      Log.app @@ fun m -> m ~header:"Result" "Sat@."
  | Error cex ->
      let module C = Modelcheck.Counterexample in
      let cex = C.simplify cex in
      begin Log.app @@ fun m -> m ~header:"Counterexample" "@[<2>%a@]"
        Sexp.pp_hum (C.sexp_of_t cex)
      end;
      if match prev_cex with
         | None -> false
         | Some prev -> C.equal cex prev
      then begin
        Log.app @@ fun m -> m ~header:"Result" "No Progress"
      end else begin
        let gamma' = Refine.run psi (List.hd_exn (C.normalize cex)) in
        begin Log.app @@ fun m -> m ~header:"Predicate" "@[<v>%a@]@."
          Print.(list @@ fun ppf -> pf ppf "@[<2>%a@]" @@ pair ~sep:(fun ppf () -> pf ppf " :@ ")
            id
            abstraction_ty)
            (IdMap.to_alist gamma')
        end;
        let new_gamma = merge_env gamma gamma' in
        cegar_loop ~prev_cex:cex psi new_gamma
      end

let main () =
  match Hflmc2.Option.parse() with
  | None ->
      Fmt.pr "No input specified. try `--help`@."
  | Some input_file ->
      let psi =
        try
          Syntax.parse_file input_file
        with Syntax.ParseError e ->
          Fmt.pr "%s@." e; assert false
      in
      begin Log.app @@ fun m -> m ~header:"Input" "%a@."
        Print.(hflz_hes simple_ty_) psi
      end;
      let gamma =
        IdMap.of_list @@ List.map psi ~f:begin fun { var; _ } ->
          var, Type.map_ty (fun () -> []) var.ty
        end
      in
      cegar_loop psi gamma

let () = main ()
