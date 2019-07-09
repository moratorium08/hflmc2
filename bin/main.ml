let () =
  match Hflmc2.Options.parse() with
  | Some file ->
      Fmt.pr "@[<v 2>Verification Result:@,%s@]@." @@
        begin match Hflmc2.main file with
        | `Valid      -> "Valid"
        | `Invalid    -> "Invalid"
        | `NoProgress -> "NoProgress"
        | exception (Hflmc2.Util.Fn.Fatal e) -> print_endline e; "Fail"
        end
  | None -> ()
