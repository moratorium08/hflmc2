let () =
  match Hflmc2.Options.parse() with
  | Some file ->
      begin match Hflmc2.main file with
      | r ->
          Fmt.pr "@[<v 2>Verification Result:@,%s@]@." @@ Hflmc2.show_result r;
          if Logs.Src.level Hflmc2.log_src <> None
            then Hflmc2.report_times()
      | exception
          ( Hflmc2.Util.Fn.Fatal e
          | Hflmc2.Syntax.ParseError e
          | Hflmc2.Syntax.LexingError e
          ) -> print_endline e; exit 1
      end;
  | None -> ()
