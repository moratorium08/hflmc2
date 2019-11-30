
open Core

type [@warning "-39"] params =
  { suzuki_san : bool        [@default false]
  ; timeout    : int         [@default 20]
  ; options    : string list [@default []]
  ; case_set   : string      [@pos 0] [@docv "CASE"]
  ; save_file  : string option
  }
  [@@deriving cmdliner]

let params =
  match Cmdliner.Term.(eval (params_cmdliner_term (), info "hflmc2-benchmark")) with
  | `Ok p -> p
  | _     -> exit 1

let dune_root =
  let rec go dir =
    if List.mem ~equal:String.equal (Sys.ls_dir dir) "dune-project"
    then dir
    else go (dir ^ "/..")
  in
  Filename.realpath (go (Sys.getcwd())) ^ "/"

let cases case_set =
  In_channel.(with_file (dune_root^"benchmark/lists/"^case_set) ~f:input_all)
  |> String.split_lines

let run_command ?(timeout=20.0) cmd =
  let read_fd ?(len=255) fd =
    let buf = Bytes.make len ' ' in
    let len = Unix.read ~buf fd in
    Unix.close fd;
    String.sub ~pos:0 ~len @@ Bytes.to_string buf
  in
  let r_fd, w_fd = Unix.pipe() in
  let e_r_fd, e_w_fd = Unix.pipe() in
  let process_status = Lwt_main.run @@
    Lwt_process.exec
      ~timeout
      ~stdout:(`FD_move w_fd)
      ~stderr:(`FD_move e_w_fd)
      ("", cmd)
  in
  let stdout = read_fd r_fd in
  let stderr = read_fd e_r_fd in
  (process_status, stdout, stderr)

let command params file =
  Array.of_list @@ List.concat @@
    [ if params.suzuki_san
      then [ "hflmc"
           ; "--hc-solver"; "rcaml"
           ; "--hc-solver-path"; "/home/hogeyama/.local/bin/rcaml"
           ]
      else [ "hflmc2"
           ; "--quiet"
           ]
    ; params.options
    ; [ file ]
    ]

type time = float
  [@@deriving yojson]
type success =
  { tag  : [`Valid | `Invalid]
  ; time : time
  } [@@deriving yojson]
type failure =
  { stdout : string
  ; stderr : string
  } [@@deriving yojson]
type result =
  | Success of success
  | Failure of failure
  | Timeout
  [@@deriving yojson]
type case_result =
  { file : string
  ; result : result
  } [@@deriving yojson]

let run_hflmc2 params dir file =
  let cmd         = command params (dir^file) in
  let timeout     = float_of_int params.timeout in
  let (p, out, err), time =
    let start = Unix.gettimeofday () in
    let r = run_command ~timeout cmd in
    let stop = Unix.gettimeofday () in
    r, stop-.start
  in
  begin match p with
  | WEXITED _ ->
      let result =
        if String.is_prefix out ~prefix:"Sat" ||
           String.is_prefix out ~prefix:"Verification Result:\n  Valid"
        then Success {tag = `Valid ; time} else
        if String.is_prefix out ~prefix:"Unsat" ||
           String.is_prefix out ~prefix:"Verification Result:\n  Invalid"
        then Success {tag = `Invalid ; time}
        else Failure { stdout = out; stderr = err}
      in { file; result }
  | _ ->
      { file ; result = Timeout }
  end

type meta =
  { command    : string
  ; timeout    : int
  ; git_status : string option
  } [@@deriving yojson]

type whole_result =
  { meta : meta
  ; results: case_result list
  } [@@deriving yojson]

let run_bench params =
  let files = cases params.case_set in
  let max_len =
    files
    |> List.map ~f:String.length
    |> List.fold ~init:0 ~f:max
  in
  let git_status =
    if params.suzuki_san then None else
    let _, commit_hash, _ = run_command [|"git";"describe";"--always" |] in
    let dirty = match run_command [|"git";"describe";"--always" |] with
      | WEXITED 0,_,_ -> ""
      | _ -> "(dirty)"
    in
    Some (commit_hash^dirty)
  in
  let meta =
    { command    = String.concat_array ~sep:" " (command params "")
    ; timeout    = params.timeout
    ; git_status = git_status
    }
  in
  let results =
    List.map files ~f:begin fun file ->
      let path_to_show =
        let pudding = String.(init (max_len - length file) ~f:(Fn.const ' ')) in
        file ^ pudding
      in
      print_string (path_to_show^": ");
      flush stdout;
      let res = run_hflmc2 params (dune_root^"benchmark/inputs/") file in
      print_endline @@ begin match res.result with
        | Success s -> Format.sprintf "Success %7.3f" s.time
        | Failure _ -> "Failure"
        | Timeout   -> "Timeout"
      end;
      res
    end
  in
  { meta; results }

let () =
  let result = run_bench params in
  let json : Yojson.Safe.t = whole_result_to_yojson result in
  let save_file = Option.value ~default:"/tmp/hflmc2-bench" params.save_file in
  Yojson.Safe.to_file ~std:true save_file json

