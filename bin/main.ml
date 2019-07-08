let () =
  match Hflmc2.Options.parse() with
  | Some file ->
      let result = Hflmc2.main file in
      Fmt.pr "@[<v 2>Verification Result:@,%s@]@." @@
        begin match result with
        | `Valid      -> "Valid"
        | `Invalid    -> "Invalid"
        | `NoProgress -> "NoProgress"
        end
  | None -> ()
