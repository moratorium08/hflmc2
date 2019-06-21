open Hflmc2_util
open Hflmc2_syntax

type counterexample =
  | False
  | And of int * int * counterexample (** (n,i,_) ith branch in n. 0-indexed *)
  | Or  of counterexample list
  | Nd  of counterexample list (* or_inserted *)
  [@@deriving eq,ord,show,iter,map,fold]
let rec sexp_of_counterexample : counterexample -> Sexp.t =
  function
  | False -> Sexp.Atom "t_false"
  | And (n,i,c) ->
      let head = Sexp.Atom ("t_and" ^ string_of_int n) in
      let rest = List.init n ~f:begin fun j ->
          if i = 0 && 0 = j
          then sexp_of_counterexample c
          else Sexp.Atom "_"
        end
      in List (head::rest)
  | Or cs ->
      let n    = List.length cs in
      let head = Sexp.Atom ("t_or" ^ string_of_int n) in
      let rest = List.map ~f:sexp_of_counterexample cs in
      List (head::rest)
  | Nd cs ->
      let n    = List.length cs in
      let head = Sexp.Atom ("t_or_inserted" ^ string_of_int n) in
      let rest = List.map ~f:sexp_of_counterexample cs in
      List (head::rest)
let rec counterexample_of_sexp : Sexp.t -> counterexample =
  let error s = Sexp.Of_sexp_error((Failure "counterexample_of_sexp"), s) in
  let open Sexp in
  function
  | Atom "t_false" -> False
  | List (Atom a :: ss) when String.is_prefix ~prefix:"t_and_inserted" a ->
      let s = List.find_exn ss ~f:(fun s -> s <> Atom "_") in
      counterexample_of_sexp s
  | List (Atom a :: ss) when String.is_prefix ~prefix:"t_or_inserted" a ->
      Nd(List.map ~f:counterexample_of_sexp ss)
  | List (Atom a :: ss) when String.is_prefix ~prefix:"t_and" a ->
      let n = List.length ss in
      let s,i = List.find_with_index ss ~f:(fun s -> s <> Atom "_") in
      And (n, i, counterexample_of_sexp s)
  | List (Atom a :: ss) when String.is_prefix ~prefix:"t_or" a ->
      Or(List.map ~f:counterexample_of_sexp ss)
  | s -> raise (error s)
let rec simplify : counterexample -> counterexample = function
  | False       -> False
  | And (n,i,c) -> And (n,i,simplify c)
  | Or cs       -> Or (List.map ~f:simplify cs)
  | Nd cs       ->
      let rec (<=) c1 c2 = match c1, c2 with
        | False, _     -> true
        | And (n1,i1,c1), And (n2,i2,c2)
            when n1 = n2 && i1 = i2 -> c1 <= c2
        | Or cs1, Or cs2 ->
            begin match List.zip_exn cs1 cs2 with
            | x -> List.for_all ~f:(Fn.uncurry (<=)) x
            | exception _ -> false
            end
        | _ -> false
      in
      match Fn.maximals' (<=) @@ List.map ~f:simplify cs with
      | [x] -> x
      | xs -> Nd xs

let print_hors : Hfl.hes Fmt.t =
  fun ppf hes' ->
    let or_set           = ref IntSet.empty in
    let and_set          = ref IntSet.empty in
    let or_inserted_set  = ref IntSet.empty in
    let and_inserted_set = ref IntSet.empty in
    let rec term : Hfl.t Fmt.t =
      fun ppf phi -> match phi with
      | Bool true -> Fmt.string ppf "t_true"
      | Bool false -> Fmt.string ppf "t_false"
      | Var x ->
          Fmt.string ppf @@ Id.to_string x
      | Or (phis, `Inserted) ->
          let n = List.length phis in
          or_inserted_set := IntSet.add !or_inserted_set n;
          Fmt.pf ppf "(t_or_inserted%d %a)"
            n
            Fmt.(list ~sep:sp term) phis
      | And(phis, `Inserted) ->
          let n = List.length phis in
          and_inserted_set := IntSet.add !and_inserted_set n;
          Fmt.pf ppf "(t_and_inserted%d %a)"
            n
            Fmt.(list ~sep:sp term) phis
      | Or (phis, `Original) ->
          let n = List.length phis in
          or_set := IntSet.add !or_set n;
          Fmt.pf ppf "(t_or%d %a)"
            n
            Fmt.(list ~sep:sp term) phis
      | And (phis, `Original) ->
          let n = List.length phis in
          and_set := IntSet.add !and_set n;
          Fmt.pf ppf "(t_and%d %a)"
            n
            Fmt.(list ~sep:sp term) phis
      | Abs _ ->
          let args, phi = Hfl.decompose_lambda phi in
          Fmt.pf ppf "(_fun %a -> %a)"
            Fmt.(list ~sep:sp string) (List.map ~f:Id.to_string args)
            term phi
      | App _ ->
          let phi, args = Hfl.decompose_app phi in
          Fmt.pf ppf "(%a)" Fmt.(list ~sep:sp term) (phi::args)
      | _ -> assert false
    in
    let hes_rule : Hfl.hes_rule Fmt.t =
      fun ppf { var; body; fix=_fix } ->
        let args, body = Hfl.decompose_lambda body in
        Fmt.pf ppf "%s %a -> %a.@."
          (Id.to_string var)
          Fmt.(list ~sep:sp string) (List.map ~f:Id.to_string args)
          term body
    in
    let hes : Hfl.hes Fmt.t =
      fun ppf hes ->
        Fmt.pf ppf "%s@." "%BEGING";
        List.iter hes ~f:(hes_rule ppf);
        Fmt.pf ppf "%s@." "%ENDG"
    in
    let automaton : unit Fmt.t =
      fun ppf () ->
        let mk_name : [`And | `Or] -> [`Original | `Inserted] -> int -> string =
          fun ope kind n ->
            begin match ope, kind with
            | `And, `Original -> "t_and"
            | `Or , `Original -> "t_or"
            | `And, `Inserted -> "t_and_inserted"
            | `Or , `Inserted -> "t_or_inserted"
            end ^ string_of_int n
        in
        let rank : unit Fmt.t =
          fun ppf () ->
            let pp_rank ope kind n = Fmt.pf ppf "%s -> %d.@." (mk_name ope kind n) n in
            Fmt.pf ppf "%s@." "%BEGINR";
            Fmt.pf ppf "%s@." "t_true -> 0.";
            Fmt.pf ppf "%s@." "t_false -> 0.";
            IntSet.iter !or_set           ~f:(pp_rank `Or  `Original);
            IntSet.iter !and_set          ~f:(pp_rank `And `Original);
            IntSet.iter !or_inserted_set  ~f:(pp_rank `Or  `Inserted);
            IntSet.iter !and_inserted_set ~f:(pp_rank `And `Inserted);
            Fmt.pf ppf "%s@." "%ENDR"
        in
        let transition : unit Fmt.t = 
          fun ppf () ->
            let pp_trans ope kind n =
              let sep ppf () =
                Fmt.string ppf @@ match ope with `And -> " /\\ " | `Or  -> " \\/ "
              in
              let pp_arg ppf k =
                Fmt.pf ppf "(%d, q0)" k
              in
              Fmt.pf ppf "q0 %s -> %a.@." (mk_name ope kind n)
                Fmt.(list ~sep pp_arg) (List.init n ~f:(fun i -> i + 1))
            in
            Fmt.pf ppf "%s@." "%BEGINATA";
            Fmt.pf ppf "%s@." "q0 t_true -> true.";
            Fmt.pf ppf "%s@." "q0 t_false -> false.";
            IntSet.iter !or_set           ~f:(pp_trans `Or  `Original);
            IntSet.iter !and_set          ~f:(pp_trans `And `Original);
            IntSet.iter !or_inserted_set  ~f:(pp_trans `Or  `Inserted);
            IntSet.iter !and_inserted_set ~f:(pp_trans `And `Inserted);
            Fmt.pf ppf "%s@." "%ENDATA"
        in
        rank ppf ();
        transition ppf ()
    in
    hes ppf hes';
    automaton ppf ()

module Parse = struct
  let counterexample : string -> counterexample =
    Fn.(counterexample_of_sexp <<< Sexp.of_string)

  let result : string -> (unit, counterexample) result =
    fun result_file ->
      let content = String.split_on_chars ~on:['\n'] @@ Fn.read_file result_file in
      let result_lines = List.drop_while content
          ~f:Fn.(not <<< String.is_prefix ~prefix:"The property is")
      in
      match result_lines with
      | "The property is NOT satisfied."::_::cex::_ ->
          if true then begin Logs.debug @@ fun m ->
            m "@[<2>raw counterexample:@ %a@]" Sexp.pp_hum @@ Sexp.of_string cex
          end;
          Error (counterexample cex);
      | "The property is satisfied."::_ ->
          Ok()
      | _ -> assert false
end

let run : Hfl.hes -> (unit, counterexample) result =
  fun hes ->
    let file = "/tmp/in" in
    let () as _write_file =
      let ch = open_out file in
      output_string ch @@ Format.asprintf "%a" print_hors hes;
      close_out ch
    in
    let exit = Sys.command @@ "horsat2 " ^ file ^ " > /tmp/out 2> /tmp/err" in
    if exit = 0
    then Parse.result "/tmp/out"
    else Fn.fatal "error occurred. `cat /tmp/out /tmp/err`"

