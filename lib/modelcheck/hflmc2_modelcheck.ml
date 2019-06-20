open Hflmc2_util
open Hflmc2_syntax
module Hoge = Horsat2

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

(* from Horsat2 *)
type head = Horsat2.Syntax.head
  [@@deriving show]
type term = Horsat2.Syntax.preterm
  [@@deriving show]
type rule = (string * string list * term)
  [@@deriving show]
type hors = rule list
  [@@deriving show]
type automaton = Horsat2.Syntax.automaton
  [@@deriving show]

(* TODO いらん *)
module ToHOMC = struct
  (* TODO α変換 *)
  let nt_start = "S"
  let q_true = "q_true"
  let t_true = "t_true"
  let t_false = "t_false"
  let t_or           n = "t_or"           ^ string_of_int n
  let t_and          n = "t_and"          ^ string_of_int n
  let t_or_inserted  n = "t_or_inserted"  ^ string_of_int n
  let t_and_inserted n = "t_and_inserted" ^ string_of_int n

  let to_hors : Hfl.t -> hors =
    fun phi ->
      let nts   = ref IdSet.empty in
      let rules = ref ([] : Horsat2.Syntax.prerules) in
      let add_nt x = nts := IdSet.add !nts x in
      let add_rule rule = rules := rule :: !rules in

      let rec term (phi : Hfl.t) : term = match phi with
        | Bool true  -> PTapp(Name t_true,  [])
        | Bool false -> PTapp(Name t_false, [])
        | Or (phis,`Original) -> PTapp(Name (t_or           (List.length phis)), List.map ~f:term phis)
        | And(phis,`Original) -> PTapp(Name (t_and          (List.length phis)), List.map ~f:term phis)
        | Or (phis,`Inserted) -> PTapp(Name (t_or_inserted  (List.length phis)), List.map ~f:term phis)
        | And(phis,`Inserted) -> PTapp(Name (t_and_inserted (List.length phis)), List.map ~f:term phis)
        | Abs(x,phi)     -> PTapp(FUN ([Id.to_string x], term phi), [])
        | App(phi1,phi2) ->
            let Horsat2.Syntax.PTapp(head, args) = term phi1 in
            PTapp(head, args @ [term phi2])
        | Var x ->
            let name = Id.to_string x in
            if IdSet.mem !nts x
              then PTapp(NT name, [])
              else PTapp(Name name, [])
        | Fix(x,phi,Greatest) ->
            add_nt x;
            add_rule (rule x phi);
            PTapp(NT (Id.to_string x),  [])
        | Exists _
        | Forall _
        | Fix(_,_,Least) -> assert false
      and rule v phi =
        let args, body = Hfl.decompose_lambda phi in
        (* TODO bodyがbool型じゃない場合．
         * 難しい訳ではないが気分が乗らないので後回し *)
        (Id.to_string v,
         List.map ~f:Id.to_string args,
         term body)
      in
        let s = { Id.name = "S"; id = 0; ty = Type.ATyBool } in
        add_rule (rule s phi);
        List.remove_consecutive_duplicates !rules ~equal:(=)

  (* let to_automaton : unit -> automaton = fun _ -> *)
  (*   let ranks = *)
  (*       [ t_true, 0 *)
  (*       ; t_false, 0 *)
  (*       ; t_or, 2 *)
  (*       ; t_and, 2 *)
  (*       ] *)
  (*   in *)
  (*   let rules : Horsat2.Syntax.ata_trans list = *)
  (*     [ ((q_true, t_true) , FConst "true") *)
  (*     ; ((q_true, t_false), FConst "false") *)
  (*     ; ((q_true, t_and)  , FAnd(FVar(0, q_true), FVar(1, q_true))) *)
  (*     ; ((q_true, t_or)   , FOr (FVar(0, q_true), FVar(1, q_true))) *)
  (*     ] *)
  (*   in *)
  (*   Alternating(ranks, rules) *)
  (*  *)
  (* let to_homc : Hfl.t -> hors * automaton = fun phi -> *)
  (*   to_hors phi, to_automaton () *)
end

module Print = struct
  let rec head : head Fmt.t =
    fun ppf head ->
      match head with
      | Name s | NT s ->
          Fmt.pf ppf "%s" s
      | FUN (args, body) ->
          Fmt.pf ppf "(_fun %a -> %a)" Fmt.(list ~sep:Fmt.sp string) args term body
      | _ -> assert false
  and [@warning "-27"] term : term Fmt.t =
    fun ppf t ->
      let open Horsat2.Syntax in
      let open Format_ in
      let PTapp(h, args) = t in
      match args with
      | [] -> Fmt.pf ppf "%a" head h
      | _  -> Fmt.pf ppf "(%a %a)" head h Fmt.(list ~sep:Fmt.sp term) args

  let [@warning "-27"] rule : rule Fmt.t =
    fun ppf (f, args, body) ->
      match args with
      | [] -> Fmt.pf ppf "@[<h>%s = %a.@.@]" f term body
      | _  -> Fmt.pf ppf "@[<h>%s %a = %a.@.@]" f (Fmt.list ~sep:Fmt.sp Fmt.string) args term body

  let hors : hors Fmt.t =
    fun ppf rules ->
      Fmt.pf ppf "%%BEGING@.";
      List.iter rules ~f:(rule ppf);
      Fmt.pf ppf "%%ENDG@."

  let homc : hors Fmt.t =
    fun ppf rules ->
      hors ppf rules;
      Fmt.string ppf @@ String.concat ~sep:"\n"
        [ ""
        ; "%BEGINR"
        ; "t_true -> 0."
        ; "t_false -> 0."
        ; "t_or2 -> 2."
        ; "t_and2 -> 2."
        ; "t_or_inserted2 -> 2."
        ; "t_and_inserted2 -> 2."
        ; "t_or3 -> 3."
        ; "t_and3 -> 3."
        ; "t_or_inserted3 -> 3."
        ; "t_and_inserted3 -> 3."
        ; "t_or4 -> 4."
        ; "t_and4 -> 4."
        ; "t_or_inserted4 -> 4."
        ; "t_and_inserted4 -> 4."
        ; "%ENDR"
        ; ""
        ; "%BEGINATA"
        ; "q0 t_true          -> true."
        ; "q0 t_false         -> false."
        ; "q0 t_or2           -> (1, q0) \\/ (2, q0)."
        ; "q0 t_and2          -> (1, q0) /\\ (2, q0)."
        ; "q0 t_or_inserted2  -> (1, q0) \\/ (2, q0)."
        ; "q0 t_and_inserted2 -> (1, q0) /\\ (2, q0)."
        ; "q0 t_or3           -> (1, q0) \\/ (2, q0) \\/ (3, q0)."
        ; "q0 t_and3          -> (1, q0) /\\ (2, q0) /\\ (3, q0)."
        ; "q0 t_or_inserted3  -> (1, q0) \\/ (2, q0) \\/ (3, q0)."
        ; "q0 t_and_inserted3 -> (1, q0) /\\ (2, q0) /\\ (3, q0)."
        ; "q0 t_or4           -> (1, q0) \\/ (2, q0) \\/ (3, q0) \\/ (4, q0)."
        ; "q0 t_and4          -> (1, q0) /\\ (2, q0) /\\ (3, q0) /\\ (4, q0)."
        ; "q0 t_or_inserted4  -> (1, q0) \\/ (2, q0) \\/ (3, q0) \\/ (4, q0)."
        ; "q0 t_and_inserted4 -> (1, q0) /\\ (2, q0) /\\ (3, q0) /\\ (4, q0)."
        ; "%ENDATA"
        ]
  let counterexample : counterexample Fmt.t =
    fun ppf cex ->
     (* Fmt.pf ppf "%a" Sexp.pp_hum (sexp_of_counterexample cex) *)
     Fmt.pf ppf "%a" pp_counterexample cex
end

module Parse = struct
  let counterexample : string -> counterexample =
    Fn.(counterexample_of_sexp <<< Sexp.of_string)

  let result : string -> (unit, counterexample) result =
    fun result_file ->
      let content =
        let ch = open_in result_file in
        let rec go acc =
          match input_line ch with
          | line -> go (line :: acc)
          | exception End_of_file -> List.rev acc
        in
        let res = go [] in
        close_in ch;
        res
      in
      let result_lines = List.drop_while content
          ~f:Fn.(not <<< String.is_prefix ~prefix:"The property is")
      in
      match result_lines with
      | "The property is NOT satisfied."::_::cex::_ ->
          if true then begin Logs.debug @@ fun m ->
            m "raw counterexample: %s" cex
          end;
          Error (counterexample cex);
      | "The property is satisfied."::_ ->
          Ok()
      | _ -> assert false
end

let run : Hfl.t -> (unit, counterexample) result =
  fun phi ->
    let file = "/tmp/in" in
    let () as _write_file =
      let ch = open_out file in
      output_string ch @@ Format.asprintf "%a" Print.homc @@ ToHOMC.to_hors phi;
      close_out ch
    in
    let exit = Sys.command @@ "horsat2 " ^ file ^ " > /tmp/out 2> /tmp/err" in
    if exit = 0
    then Parse.result "/tmp/out"
    else Fn.fatal "error occurred. `cat /tmp/out /tmp/err`"

