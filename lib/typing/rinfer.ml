open Rhflz 
open Rtype
open Hflmc2_syntax
open Chc

(* check whether t <= t' holds *)
let rec rty = function
  | RArrow(RInt(_), t) -> rty t
  | RArrow(_, s) -> rty s
  | RBool(phi) -> phi
  | _ -> failwith "program error(rty)"

let rec _subtype t t' lenv renv m = 
  match (t, t') with
 | RBool(p), RBool(p') -> 
   {body=conjoin lenv (conjoin renv p'); head=p} :: m
 | RArrow(RInt(x), t), RArrow(RInt(y), t')  ->
   let x' = rint2arith x in
   let y' = rint2arith y in
   _subtype t t' (conjoin lenv (RPred(Formula.Eq, [x'; y'])))  renv m
 | RArrow(t, s), RArrow(t', s') ->
   let m' = _subtype t' t lenv (conjoin renv (rty t')) m in
   _subtype s s' lenv renv m' 
 | _, _ -> 
  print_rtype t;
  Printf.printf "=";
  print_rtype t';
  print_newline ();
 failwith "program error(subtype)"

let subtype t t' m = _subtype t t' RTrue RTrue m

(* Appで制約を生成 *)
let rec infer_formula formula env m = 
  (*print_formula formula;
  print_newline ();*)
  match formula with
  | Bool b when b -> (RBool(RTrue), m)
  | Bool _ -> (RBool(RFalse), m)
  | Var id -> 
    begin
    match IdMap.find env id with
    | Some(t) -> (t, m)
    | None -> failwith "no var(infer_formula)"
    end
  | Abs (arg, body) -> 
    let env' = IdMap.add env arg arg.ty in
    let (body_t, l) = infer_formula body env' m in
    (RArrow(arg.ty, body_t), l)
  | Pred (f, args) -> (RBool(RPred(f, args)), m)
  | Arith x -> (RInt (RArith x), m)
  | Or (x, y) | And (x, y) -> 
    let (x', mx) = infer_formula x env m in
    let (y', m') = infer_formula y env mx in
    let (rx, ry) = match (x', y') with
      | (RBool(rx), RBool(ry)) -> (rx, ry)
      | _ -> failwith "type is not correct"
    in begin
    match formula with 
    | Or _ -> (RBool(ROr(rx, ry)), m')
    | And _ -> (RBool(conjoin rx ry), m')
    | _ -> failwith "program error(1)"
    end
  | App(x, y) -> 
    let (x', mx) = infer_formula x env m in
    let (y', m') = infer_formula y env mx in
    let (arg, body, tau) = match (x', y') with
      | (RArrow(arg, body), tau) -> (arg, body, tau)
      | _ -> failwith "type is not correct"
    in begin
      match (arg, tau) with
       | RInt(RId(id)), RInt m -> 
        print_rtype arg; print_string " =? "; print_rtype tau; 
        print_string "->"; print_rtype body; print_newline();
         (subst id m body, m')
       | _ ->
        let m'' = subtype arg tau m' in
        (body, m'')
      end
  
let infer_rule (rule: hes_rule) env (chcs: (refinement, refinement) chc list): (refinement, refinement) chc list = 
  (*
  print_string "uo\n";
  print_constraints chcs;
  print_string "hoge\n";
  *)
  let (t, m) = infer_formula rule.body env chcs in
  (*
  print_string "piyo\n";
  print_constraints m;
  print_string "nyan\n";
  *)
  (*print_rtype rule.var.ty;
  print_newline ();
  print_rtype t;
  print_newline ();*)
  subtype t rule.var.ty m 
 
let rec infer_hes (hes: hes) env (accum: (refinement, refinement) chc list): (refinement, refinement) chc list = match hes with
  | [] -> accum
  | rule::xs -> 
    (*Print.printf "uo%d\n" (List.length hes);*)
    infer_rule rule env accum |> infer_hes xs env 

let infer hes env top = 
  let constraints = infer_hes hes env [] in
  let constraints = {head=RTemplate(top); body=RTrue} :: constraints in
  let simplified = List.map subst_chc constraints in
  (*print_string "generated CHC\n";
  print_constraints simplified;
  print_string "expanded CHC\n";*)
  let simplified' = List.map expand_head_exact simplified in
  (* print_string (Chc_solver.chc2smt2 simplified')*)
  let (@!) x y = match (x, y) with
    | Some(x), Some(y) -> Some(x @ y)
    | _ -> None
  in
  let rec divide_chcs = function
    | [] -> Some([])
    | x::xs -> divide_chc x @! divide_chcs xs
  in
  let divided = divide_chcs simplified' in
  match divided with
    | Some(divided) -> 
      begin
      print_string (Chc_solver.chc2smt2 simplified');
      print_newline ();
      print_newline ();
      print_string (Chc_solver.chc2smt2 divided);
      Chc_solver.check_sat divided = `Sat
      end
    | None ->
      begin
      Printf.printf "Some definite clause has or-head\n";
      Chc_solver.check_sat simplified' = `Sat
      end
