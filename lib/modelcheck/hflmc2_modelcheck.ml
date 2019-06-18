open Hflmc2_util
open Hflmc2_syntax
module Hoge = Horsat2

(*
  e.g.
  (t_or t_false (t_and _ (t_or t_false t_false)))
   => Or (False, AndR (Or False False))
*)
type counterexample =
  | False
  | AndL of counterexample
  | AndR of counterexample
  | Or   of counterexample * counterexample
  | Nd   of counterexample list
  [@@deriving eq,ord,show,iter,map,fold]
let rec sexp_of_counterexample : counterexample -> Sexp.t = function
  | False -> Atom "t_false"
  | AndR c -> List [ Atom "t_and"; Atom "_"; sexp_of_counterexample c ]
  | AndL c -> List [ Atom "t_and"; sexp_of_counterexample c; Atom "_" ]
  | Or (c1,c2) -> List [ Atom "t_or"
                       ; sexp_of_counterexample c1
                       ; sexp_of_counterexample c2 ]
  | Nd [] -> assert false
  | Nd (c0::cs) ->
      let s0 = sexp_of_counterexample c0 in
      List.fold_left cs ~init:s0 ~f:begin fun s c ->
        let open Sexp in
        List [Atom "t_or_inserted"; s; sexp_of_counterexample c]
      end
let rec counterexample_of_sexp : Sexp.t -> counterexample =
  let open Sexp in
  function
  | Atom "t_false" -> False
  | List [Atom "t_and"; Atom "_"; s] -> AndR (counterexample_of_sexp s)
  | List [Atom "t_and"; s; Atom "_"] -> AndL (counterexample_of_sexp s)
  | List [Atom "t_or"; s1; s2]       -> Or ( counterexample_of_sexp s1
                                           , counterexample_of_sexp s2 )
  | List [Atom "t_and_inserted"; Atom "_"; s] -> counterexample_of_sexp s
  | List [Atom "t_and_inserted"; s; Atom "_"] -> counterexample_of_sexp s
  | List [Atom "t_or_inserted"; s1; s2] ->
      let rec go acc = function
        | List [Atom "t_or_inserted"; s1; s2] ->
            go (counterexample_of_sexp s2::acc) s1
        | s -> Nd (counterexample_of_sexp s :: acc)
      in go [counterexample_of_sexp s2] s1
  | _ -> assert false

let rec simplify : counterexample -> counterexample = function
  | False      -> False
  | AndL c     -> AndL (simplify c)
  | AndR c     -> AndR (simplify c)
  | Or (c1,c2) -> Or (simplify c1, simplify c2)
  | Nd cs      ->
      let rec cmp c1 c2 = match c1, c2 with
        | False, False -> Some 0
        | False, _     -> Some (-1)
        | _,     False -> Some 1
        | AndL c1, AndL c2 -> cmp c1 c2
        | AndR c1, AndR c2 -> cmp c1 c2
        | Or(c11,c12), Or(c21,c22) ->
            begin match cmp c11 c21, cmp c12 c22 with
            | Some n, Some n' when n = n' -> Some n
            | Some n, Some 0
            | Some 0, Some n -> Some n
            | _ -> None
            end
        | _ -> None (* Ndのときはこれでいいんか *)
      in
      Nd (Fn.maximals ~compare:cmp @@ List.map ~f:simplify cs)

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
  let t_or = "t_or"
  let t_and = "t_and"
  let t_or_inserted = "t_or_inserted"
  let t_and_inserted = "t_and_inserted"

  let to_hors : Hfl.t -> hors =
    fun phi ->
      let nts   = ref IdSet.empty in
      let rules = ref ([] : Horsat2.Syntax.prerules) in
      let add_nt x = nts := IdSet.add !nts x in
      let add_rule rule = rules := rule :: !rules in

      let rec term (phi : Hfl.t) : term = match phi with
        | Bool true  -> PTapp(Name t_true,  [])
        | Bool false -> PTapp(Name t_false, [])
        | Or (phi1,phi2,`Original) -> PTapp(Name t_or,  [term phi1; term phi2])
        | And(phi1,phi2,`Original) -> PTapp(Name t_and, [term phi1; term phi2])
        | Or (phi1,phi2,`Inserted) -> PTapp(Name t_or_inserted,  [term phi1; term phi2])
        | And(phi1,phi2,`Inserted) -> PTapp(Name t_and_inserted, [term phi1; term phi2])
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

  let to_automaton : unit -> automaton = fun _ ->
    let ranks =
        [ t_true, 0
        ; t_false, 0
        ; t_or, 2
        ; t_and, 2
        ]
    in
    let rules : Horsat2.Syntax.ata_trans list =
      [ ((q_true, t_true) , FConst "true")
      ; ((q_true, t_false), FConst "false")
      ; ((q_true, t_and)  , FAnd(FVar(0, q_true), FVar(1, q_true)))
      ; ((q_true, t_or)   , FOr (FVar(0, q_true), FVar(1, q_true)))
      ]
    in
    Alternating(ranks, rules)

  let to_homc : Hfl.t -> hors * automaton = fun phi ->
    to_hors phi, to_automaton ()
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
        ; "t_or_inserted -> 2."
        ; "t_and_inserted -> 2."
        ; "t_or -> 2."
        ; "t_and -> 2."
        ; "t_true -> 0."
        ; "t_false -> 0."
        ; "%ENDR"
        ; ""
        ; "%BEGINATA"
        ; "q0 t_or_inserted -> (1, q0) \\/ (2, q0)."
        ; "q0 t_and_inserted -> (1, q0) /\\ (2, q0)."
        ; "q0 t_or -> (1, q0) \\/ (2, q0)."
        ; "q0 t_and -> (1, q0) /\\ (2, q0)."
        ; "q0 t_true -> true."
        ; "q0 t_false -> false."
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

