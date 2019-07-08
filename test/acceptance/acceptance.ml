open Core

(* TODO duneのrootを手に入れる方法はないものか *)
let input_dir = "../../../../input/ok/"

let check_valid_inputs() =
  let dir   = input_dir ^ "valid/" in
  let files = Sys.ls_dir dir in
  let count = ref 0 in
  List.iter files ~f:begin fun file ->
    match Hflmc2.main (dir ^ file) with
    | `Valid -> ()
    | `Invalid ->
        count := !count + 1;
        Fmt.pf Fmt.stderr "input/ok/valid/%s judeged as Invalid@." file
    | `NoProgress ->
        count := !count + 1;
        Fmt.pf Fmt.stdout "input/ok/valid/%s failed with NoProgress@." file
  end;
  Fmt.pf Fmt.stdout "[valid  ] %d of %d inputs failed@." !count (List.length files);
  !count <> 0

let check_invalid_inputs() =
  let dir   = input_dir ^ "invalid/" in
  let files = Sys.ls_dir dir in
  let count = ref 0 in
  List.iter files ~f:begin fun file ->
    match Hflmc2.main (dir ^ file) with
    | `Invalid -> ()
    | `Valid ->
        count := !count + 1;
        Fmt.pf Fmt.stderr "input/ok/valid/%s judeged as Valid@." file
    | `NoProgress ->
        count := !count + 1;
        Fmt.pf Fmt.stdout "input/ok/valid/%s failed with NoProgress@." file
  end;
  Fmt.pf Fmt.stdout "[invalid] %d of %d inputs failed@." !count (List.length files);
  !count <> 0

let () =
  let failed1 = check_valid_inputs() in
  let failed2 = check_invalid_inputs() in
  if failed1 || failed2 then exit 1

