open Hflmc2_util
open Hflmc2_syntax

module Log = (val Logs.src_log @@ Logs.Src.create "Modelcheck")

module Counterexample = struct
  type t =
    | False
    | AndL of t
    | AndR of t
    | Or  of t * t
    | Nd  of t list (* or_inserted *)
    [@@deriving eq,ord,show,iter,map,fold]
  let rec sexp_of_t : t -> Sexp.t =
    function
    | False -> Sexp.Atom "t_false"
    | AndL c ->
        List [Atom "t_and"; sexp_of_t c; Atom "_"]
    | AndR c ->
        List [Atom "t_and"; Atom "_"; sexp_of_t c]
    | Or (c1,c2) ->
        List [Atom "t_or" ; sexp_of_t c1; sexp_of_t c2]
    | Nd cs ->
        let n    = List.length cs in
        let head = Sexp.Atom ("t_or_inserted" ^ string_of_int n) in
        let rest = List.map ~f:sexp_of_t cs in
        List (head::rest)
  let rec t_of_sexp : Sexp.t -> t = function
    | Atom "t_false" -> False
    | List (Atom a :: ss) when String.is_prefix ~prefix:"t_and_inserted" a ->
        let s = List.find_exn ss ~f:(fun s -> s <> Atom "_") in
        t_of_sexp s
    | List (Atom a :: ss) when String.is_prefix ~prefix:"t_or_inserted" a ->
        Nd(List.map ~f:t_of_sexp ss)
    | List [Atom "t_and"; s1; Atom "_"] -> AndL (t_of_sexp s1)
    | List [Atom "t_and"; Atom "_"; s2] -> AndR (t_of_sexp s2)
    | List [Atom "t_or"; s1; s2] -> Or (t_of_sexp s1, t_of_sexp s2)
    | s -> raise @@ Sexp.Of_sexp_error((Failure "Counterexample.t_of_sexp"), s)
  let rec simplify : t -> t = function
    | False       -> False
    | AndL c      -> AndL (simplify c)
    | AndR c      -> AndR (simplify c)
    | Or (c1,c2)  -> Or (simplify c1, simplify c2)
    | Nd cs       ->
        let rec (<=) c1 c2 = match c1, c2 with
          | False, _     -> true
          | AndL c1, AndL c2 -> c1 <= c2
          | AndR c1, AndR c2 -> c1 <= c2
          | Or (c11,c12)
          , Or (c21,c22) -> c11<=c21 && c12<=c22
          | _ -> false
        in
        match List.maximals' (<=) @@ List.map ~f:simplify cs with
        | [x] -> x
        | xs -> Nd xs

  type normalized =
    | False
    | AndL of normalized
    | AndR of normalized
    | Or   of normalized * normalized
    [@@deriving eq,ord,show,iter,map,fold,sexp]

  let pp_hum_normalized ppf x =
    let rec to_t : normalized -> t = function
      | False -> False
      | Or (c1,c2) -> Or (to_t c1, to_t c2)
      | AndL c -> AndL (to_t c)
      | AndR c -> AndR (to_t c)
    in
    Sexp.pp_hum ppf (sexp_of_t @@ to_t x)

  let rec normalize : t -> normalized list = function
    | False  -> [False]
    | AndL c -> List.map (normalize c) ~f:(fun c' -> AndL c')
    | AndR c -> List.map (normalize c) ~f:(fun c' -> AndR c')
    | Or (c1,c2) ->
        List.map
          (List.cartesian_product (normalize c1) (normalize c2))
          ~f:(fun (c1,c2) -> Or (c1,c2))
    | Nd cs -> List.concat_map cs ~f:normalize
end


let print_hors : Hfl.hes Fmt.t =
  fun ppf hes' ->
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
      | Or ([phi1;phi2], `Original) ->
          Fmt.pf ppf "(t_or %a %a)" term phi1 term phi2
      | And ([phi1;phi2], `Original) ->
          Fmt.pf ppf "(t_and %a %a)" term phi1 term phi2
      | Abs _ ->
          let args, phi = Hfl.decompose_abs phi in
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
        let args, body = Hfl.decompose_abs body in
        let arity = Type.arity_of_abstracted_ty (Hfl.type_of body) in
        let eta_vars = List.init arity ~f:(Print.strf "eta%d") in
        Fmt.pf ppf "@[%s %a -> %a %a.@]@."
          (Id.to_string var)
          Fmt.(list ~sep:sp string)
            (List.map ~f:Id.to_string args @ eta_vars)
          term body
          Fmt.(list ~sep:sp string) eta_vars
    in
    let hes : Hfl.hes Fmt.t =
      fun ppf hes ->
        Fmt.pf ppf "%s@." "%BEGING";
        List.iter hes ~f:(hes_rule ppf);
        Fmt.pf ppf "%s@." "%ENDG"
    in
    let automaton : unit Fmt.t =
      fun ppf () ->
        let mk_name : [`And | `Or] -> int -> string =
          fun ope n -> match ope with
            | `And -> "t_and_inserted" ^ string_of_int n
            | `Or  -> "t_or_inserted" ^ string_of_int n
          in
        let rank : unit Fmt.t =
          fun ppf () ->
            let pp_rank ope n =
              Fmt.pf ppf "%s -> %d.@." (mk_name ope n) n
            in
            Fmt.pf ppf "%s@." "%BEGINR";
            Fmt.pf ppf "t_true  -> 0.@.";
            Fmt.pf ppf "t_false -> 0.@.";
            Fmt.pf ppf "t_and   -> 2.@.";
            Fmt.pf ppf "t_or    -> 2.@.";
            IntSet.iter !or_inserted_set  ~f:(pp_rank `Or);
            IntSet.iter !and_inserted_set ~f:(pp_rank `And);
            Fmt.pf ppf "%s@." "%ENDR"
        in
        let transition : unit Fmt.t =
          fun ppf () ->
            let pp_trans ope n =
              let sep ppf () =
                Fmt.string ppf @@ match ope with
                  | `And -> " /\\ "
                  | `Or  -> " \\/ "
              in
              let pp_arg ppf k =
                Fmt.pf ppf "(%d, q0)" k
              in
              Fmt.pf ppf "q0 %s -> %a.@." (mk_name ope n)
                Fmt.(list ~sep pp_arg) (List.init n ~f:(fun i -> i + 1))
            in
            Fmt.pf ppf "%s@." "%BEGINATA";
            Fmt.pf ppf "q0 t_true  -> true.@.";
            Fmt.pf ppf "q0 t_false -> false.@.";
            Fmt.pf ppf "q0 t_and   -> (1,q0) /\\ (2,q0).@.";
            Fmt.pf ppf "q0 t_or    -> (1,q0) \\/ (2,q0).@.";
            IntSet.iter !or_inserted_set  ~f:(pp_trans `Or);
            IntSet.iter !and_inserted_set ~f:(pp_trans `And);
            Fmt.pf ppf "%s@." "%ENDATA"
        in
        rank ppf ();
        transition ppf ()
    in
    hes ppf hes';
    automaton ppf ()

module Parse = struct
  let counterexample : string -> Counterexample.t =
    Fn.(Counterexample.t_of_sexp <<< Sexp.of_string)

  let result : string -> (unit, Counterexample.t) result =
    fun result_file ->
      let content =
        String.split_on_chars ~on:['\n'] @@ Fn.read_file result_file
      in
      let result_lines =
        List.drop_while content
          ~f:Fn.(not <<< String.is_prefix ~prefix:"The property is")
      in
      match result_lines with
      | "The property is NOT satisfied."::_::cex::_ ->
          Log.debug begin fun m -> m "@[<2>raw counterexample:@ %a@]"
            Sexp.pp_hum @@ Sexp.of_string cex
          end;
          Error (counterexample cex);
      | "The property is satisfied."::_ ->
          Ok()
      | _ -> assert false
end

let run : Hfl.hes -> (unit, Counterexample.t) result =
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
    else Fn.fatal @@
      Print.strf
        ("@[<v>Error occurred during model checking." ^^
         "HorSat2 output@,[stdout]@,%s[stderr]@,%s@]")
        (Fn.read_file "/tmp/out")
        (Fn.read_file "/tmp/err")

