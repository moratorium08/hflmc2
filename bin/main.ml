let () =
  match Hflmc2.Options.parse() with
  | Some file ->
      Fmt.pr "@[<v 2>Verification Result:@,%s@]@." @@
        begin match Hflmc2.main file with
        | r -> Hflmc2.show_result r
        | exception
            ( Hflmc2.Util.Fn.Fatal e
            | Hflmc2.Syntax.ParseError e
            | Hflmc2.Syntax.LexingError e
            ) -> print_endline e; "Fail"
        end
  | None -> ()
