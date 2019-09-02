open Core
open Hflmc2_util

let args = [| "dummy_file"
            ; "--quiet"
            ; "--abst-max-ands=2"
            ; "--abst-no-cartesian"
            |]
let _ = Hflmc2.Options.parse ~argv:(Array.append args Sys.argv) ()

(* TODO duneのrootを手に入れる方法はないものか．
 * Sys.getenv_exn "OWD" がそれっぽいけどドキュメントにはなってなさそう
 * *)
let input_base_dir = "../../../../input/ok/"

let measure_time f =
  let start  = Unix.gettimeofday () in
  let result = f () in
  let stop   = Unix.gettimeofday () in
  result, stop -. start

type test_sort =
  { name     : string
  ; dir      : string
  ; succsess : Hflmc2.result
  }

let check : test_sort -> bool =
  fun sort ->
    let dir   = input_base_dir ^ sort.dir in
    let files = List.sort ~compare @@ Sys.ls_dir dir in
    let max_len =
      List.map ~f:String.length files
      |> Fn.maximals' (fun a b -> a <= b)
      |> List.hd_exn
    in
    let count = ref 0 in
    List.iter files ~f:begin fun file ->
      let result, time =
        measure_time begin fun () ->
          try Ok (Hflmc2.main (dir ^ "/" ^ file)) with e -> Error e
        end
      in
      let path_to_show =
        let pudding = String.(init (max_len - length file) ~f:(Fn.const ' ')) in
        sort.dir ^ "/" ^ file ^ pudding
      in
      match result with
      (* succsess *)
      | Ok res when res = sort.succsess ->
          Fmt.pf Fmt.stdout "input/ok/%s %f sec@." path_to_show time
      (* failure *)
      | Ok res ->
          count := !count + 1;
          Fmt.pf Fmt.stderr "input/ok/%s %s@."
            path_to_show (Hflmc2.show_result res)
      | Error e ->
          count := !count + 1;
          Fmt.pf Fmt.stdout "@[<2>input/ok/%s failed with error:@ %s@]@."
            path_to_show (Exn.to_string e)
    end;
    Fmt.pf Fmt.stdout "[%s] %d of %d inputs failed@."
      sort.name !count (List.length files);
    !count = 0

let () =
  let succsess = List.for_all ~f:Fn.id
      [ check { name = "invalid"; succsess = `Invalid; dir = "invalid" }
      ; check { name = "  valid"; succsess = `Valid  ; dir = "valid"   }
      ]
  in if not succsess then exit 1
