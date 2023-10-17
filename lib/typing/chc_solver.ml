open Hflmc2_syntax
open Hflmc2_options
open Chc
open Rtype
open Smt2

type solver = [`Spacer | `Hoice | `Fptprove | `Eldarica | `Liu]

let fptprove_path_env = "fptprove"

type unsat_proof_node = 
  {
   id: int; 
   name: Rid.id; 
   args: int list; 
   nodes: int list }
type unsat_proof = unsat_proof_node list
  
let name_of_solver = function
  | `Spacer -> "spacer"
  | `Hoice -> "hoice"
  | `Fptprove -> "fptprove"
  | `Eldarica -> "eldarica"
  | `Liu      -> "liu"

let auto = `Auto(`Hoice, [])

let selected_solver size = 
  let sv = !Typing.solver in
  if size > 1 then `Fptprove
  else if sv = "auto" then auto
  else if sv = "z3" || sv = "spacer" then `Spacer
  else if sv = "hoice" then `Hoice
  else if sv = "fptprove" then `Fptprove
  else failwith ("Unknown solver: " ^ sv)

(* set of template *)
let call_template cmd timeout = 
    let open Hflmc2_util in
    fun file -> 
    let _, out, _ = Fn.run_command ~timeout:timeout (Array.concat [cmd; [|file|]]) in
    String.lsplit2 out ~on:'\n'

let call_fptprove timeout file = 
  let open Hflmc2_util in
  let fptprove_path = 
    try Sys.getenv "fptprove" with
    | Not_found -> Filename.concat (Sys.getenv "HOME") "bitbucket.org/uhiro/fptprove"
  in
  Sys.chdir fptprove_path;
  let _, out, _ = Fn.run_command ~timeout:timeout (Array.concat [[|"./script/hflmc3.sh"|]; [|file|]]) in
  let l = String.split out ~on:',' in
  match List.nth l 1 with
    | Some(x) -> Some(x, "")
    | None -> None

let selected_cmd timeout = function
  | `Spacer -> call_template [|"z3"; "fp.engine=spacer"|] timeout
  | `Hoice -> call_template [|"hoice"|] timeout
  | `Fptprove -> call_fptprove timeout
  | _ -> failwith "you cannot use this"
  
let selected_cex_cmd = function
  | `Eldarica -> 
    [|"eld"; "-cex";  "-hsmt"|]
  | _ -> failwith "you cannot use this"

let prologue = "(set-logic HORN)
"

let get_epilogue = 
  function 
  | `Spacer ->
    "\
    (check-sat-using (then propagate-values qe-light horn))
    (get-model)
    "
  | `Fptprove -> 
    "\
    (check-sat)
    "
  | `Hoice ->
    "\
    (check-sat)
    (get-model)
    "
  | `Eldarica ->
    "\
    (check-sat)
    "

let rec collect_preds chcs m = 
  let rec inner rt m = match rt with 
  | RTemplate (p, l) -> Rid.M.add p (List.length l) m
  | RAnd(x, y) | ROr(x, y) ->
    m |> inner x |> inner y
  | _ -> m
  in
  match chcs with
  | [] -> m
  | chc::chcs ->
    m |> inner chc.body |> inner chc.head |> collect_preds chcs

let collect_vars chc = 
  let collect_from_arith a m =
    let fvs = Arith.fvs a in
    List.fold_left IdSet.add m fvs
  in
  let rec collect_from_ariths ars m = match ars with
    | [] -> m
    | x::xs -> 
      m |> collect_from_arith x |> collect_from_ariths xs
  in
  let rec inner rt m = match rt with
  | RTemplate(_, l) | RPred(_, l) -> 
    collect_from_ariths l m
  | RAnd(x, y) | ROr(x, y) -> 
    m |> inner x |> inner y
  | _ -> m
  in 
  IdSet.empty |> inner chc.head |> inner chc.body


let gen_assert solver chc =
  let vars = collect_vars chc in
  let vars_s = vars |> IdSet.to_list |> List.map var_def |> List.fold_left (^) "" in
  let body = ref2smt2 chc.body in
  let head = ref2smt2 chc.head in
  let s = Printf.sprintf "(=> %s %s)" body head in
  if vars_s = "" && (solver = `Spacer || solver = `Fptprove || solver = `Eldarica) then
    Printf.sprintf "(assert %s)\n" s
  else
    Printf.sprintf "(assert (forall (%s) %s))\n" vars_s s

let chc2smt2 chcs solver = 
  let preds = collect_preds chcs Rid.M.empty in
  let def = preds |> Rid.M.bindings |> List.map pred_def |> List.fold_left (^) "" in
  let body = chcs |> List.map (gen_assert solver) |> List.fold_left (^) "" in
  prologue ^ def ^ body ^ (get_epilogue solver)


let parse_model model = 
  let open Hflmc2_util in
  (* Ported from Iwayama san's parser 
     https://github.com/Hogeyama/hflmc2/blob/0c29b0b3a8aacb2496615244b3d93e98370c6eee/lib/refine/hornClauseSolver.ml#L215-L280
  *)
  let open Sexp in
  let fail f s = invalid_arg @@ f ^ ": " ^ Sexp.to_string s in
  let mk_var name =
     Id.{ name; id=0; ty=`Int }
  in
  let parse_arg = function
    | List [Atom v; Atom "Int" ] -> mk_var v
    | s -> fail "parse_arg" s
  in
  let rec parse_arith = function
    | Atom s ->
        begin match int_of_string s with
        | n -> Arith.mk_int n
        | exception _ -> Arith.mk_var' (mk_var s)
        end
    | List (Atom op :: ss) ->
        let op = match op with
          | "+" -> Arith.Add
          | "-" -> Arith.Sub
          | "*" -> Arith.Mult
          | s   -> fail "parse_arith:op" (Atom s)
        in
          begin
          match ss with
          | [] -> failwith "program error(parse_arith)"
          | [x] -> begin
              let e = 
              match op with 
              | Arith.Add | Arith.Sub -> 0
              | Arith.Mult | Arith.Div | Arith.Mod -> 1
              in
              Arith.mk_op op [Arith.Int(e); parse_arith x]
            end
          | _ -> 
            let [@warning "-8"] a::as' = List.map ss ~f:parse_arith in
              List.fold_left ~init:a as' ~f:begin fun a b ->
                Arith.mk_op op [a; b]
              end
            end
    | s -> fail "parse_arith" s
  in
  let parse_predicate_name s = 
    let tail = String.sub s 1 (String.length s - 1) in
    int_of_string tail
  in
  let rec parse_formula = function
    | Atom "true"  -> RTrue
    | Atom "false" -> RFalse
    | List (Atom a :: ss) ->
        let a = match a with
          | "="   -> `Pred Formula.Eq
          | "!="  -> `Pred Formula.Neq
          | "<="  -> `Pred Formula.Le
          | ">="  -> `Pred Formula.Ge
          | "<"   -> `Pred Formula.Lt
          | ">"   -> `Pred Formula.Gt
          | "and" -> `And 
          | "or"  -> `Or 
          | "not" -> `Not 
          | var -> `Var var
          | s     -> fail "parse_formula:list" (Atom s)
        in
        begin match a with
        | `Pred pred ->
            RPred (pred, (List.map ~f:parse_arith ss))
        | `And ->
            let  [@warning "-8"] a::as' = List.map ss ~f:parse_formula in
            List.fold_left ~init:a as' ~f:(fun x y -> RAnd(x, y))
        | `Or -> 
            let  [@warning "-8"] a::as' = List.map ss ~f:parse_formula in
            List.fold_left ~init:a as' ~f:(fun x y -> ROr(x, y))
        | `Not -> 
            let [@warning "-8"] [f] = List.map ss ~f:parse_formula in
            negate_ref f
        | `Var var -> 
          RTemplate ((Rid.from_string var , List.map ~f:parse_arith ss))
        end
    | s -> fail "parse_formula" s
  in
  let parse_def = function
    | List [Atom "define-fun"; Atom id; List args; Atom "Bool"; body] ->
        let args = List.map ~f:parse_arg args in
        let body = parse_formula body in
        let id = Rid.from_string id in
        (id, args, body)
    | s -> fail "parse_def" s
  in
  let simplify defs = 
    let rec subst_arg vars args form = match (vars, args) with
      | ([], []) -> form
      | (v::vars, x::xs) -> subst_arg vars xs (subst_refinement v (RArith x) form)
      | _ -> failwith "program error"
    in
    let rec simplify_def x = match x with
      | RAnd(x, y) -> RAnd(simplify_def x, simplify_def y)
      | ROr(x, y) -> ROr(simplify_def x, simplify_def y)
      | RTemplate((name, args)) -> 
        let (_, vars, form) = List.find_exn defs ~f:(fun (name', _, _) -> (Rid.eq name name')) in
        subst_arg vars args form
      | RPred _ | RFalse | RTrue -> x
    in
    let rec inner xs = match xs with
      | [] -> []
      | (name, args, x)::xs -> (name, args, simplify_def x) :: inner xs
    in inner defs
  in
  print_string model;
  match Sexplib.Sexp.parse model with
  | Done(model, _) -> begin 
    match model with
    | List (Atom "model" :: sol) ->
        let defs = List.map ~f:parse_def sol in
        Ok(simplify defs)
    | _ -> Error "parse_model" 
    end
  | _ -> Error "failed to parse model"

let save_chc_to_smt2 chcs solver = 
    let smt2 = chc2smt2 chcs solver in
    Random.self_init ();
    let r = Random.int 0x10000000 in
    let file = Printf.sprintf "/tmp/%s-%d.smt2" (name_of_solver solver) r in
    let oc = open_out file in
    Printf.fprintf oc "%s" smt2;
    close_out oc;
    file

let check_sat ?(timeout=100000.0) chcs solver = 
  let check_sat_inner timeout solver = 
    let file = save_chc_to_smt2 chcs solver in
    let open Hflmc2_util in
    let f = selected_cmd timeout solver in
    match f file with
    | Some ("unsat", _) -> `Unsat
    | Some ("sat", model) ->
      let open Hflmc2_options in
      if !Typing.show_refinement then
        `Sat(parse_model model)
      else
        `Sat(Error "did not calculate refinement. Use --show-refinement")
    | Some ("unknown", _) -> `Unknown
    | Some(x, _) -> (Printf.printf "Failed to handle the result of chc solver: %s\n\n" x; `Fail)
    | _ -> (Printf.printf "Failed to handle the result of chc solver\n\n" ; `Fail)
  in 
  match solver with
  | `Auto(mainly, tries) ->
    let rec loop = function 
      | [] -> check_sat_inner timeout mainly
      | x::xs -> 
        begin
          let ret = check_sat_inner 1.0 x in
          match ret with
          | `Sat(_) | `Unsat -> ret
          | _ -> loop xs
        end
    in loop tries
  | `Spacer | `Hoice | `Fptprove as sv -> check_sat_inner timeout sv

(* usp: unsat proof *)
let rec unsat_proof_of_eldarica_cex nodes = 
  let open Eldarica in
  match nodes with
  | [] -> []
  | x::xs -> {id=Dag.(x.id); 
              name=if x.head="FALSE" then 
                Rid.false_id 
               else 
                Rid.from_string Dag.(x.head);
              args=Dag.(x.args);
              nodes=[];}::(unsat_proof_of_eldarica_cex xs) (* TODO *)
let get_unsat_proof ?(timeout=100.0) chcs solver = 
  let open Hflmc2_util in
  let file = save_chc_to_smt2 chcs solver in
  let cmd = selected_cex_cmd solver in
  let _, out, _ = Fn.run_command ~timeout:timeout (Array.concat [cmd; [|file|]]) in
  let p = Eldarica.parse_string out in
  unsat_proof_of_eldarica_cex p
