let () =
  let file =
    match Hflmc2.Options.parse() with
    | Some (`File file) -> file
    | Some `Stdin ->
        let tmp_file = Filename.temp_file "stdin-" ".in" in
        let contents = Hflmc2_util.In_channel.(input_all stdin) in
        Hflmc2_util.Out_channel.with_file tmp_file ~f:begin fun ch ->
          Hflmc2_util.Out_channel.output_string ch contents
        end;
        tmp_file
    | None -> exit 1
  in
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
