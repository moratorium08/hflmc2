open Hflmc2_util
open Hflmc2_syntax
open Id
open Rtype

type t =
  | Bool   of bool
  | Var    of Rtype.t Id.t
  (* template is used for tracking counterexample. *)
  | Or     of t * t * template * template
  | And    of t * t * template * template
  | Abs    of Rtype.t Id.t * t
  | App    of t * t * template
  | Forall of Rtype.t Id.t * t * template
  (* constructers only for hflz *)
  | Arith  of Arith.t
  | Pred   of Formula.pred * Arith.t list

let rec print_formula = function
  | Bool x when x -> Printf.printf "tt"
  | Bool _ -> Printf.printf "ff"
  | Var x -> Printf.printf "%s" (Id.to_string x)
  | Or (x, y, _, _) -> 
    Printf.printf "(";
    print_formula x;
    Printf.printf " || ";
    print_formula y;
    Printf.printf ")";
  | And (x, y, tx, ty) -> 
    Printf.printf "(";
    print_formula x;
    print_string ":";
    print_template tx;
    Printf.printf " && ";
    print_formula y;
    print_string ":";
    print_template ty;
    Printf.printf ")";
  | Abs (x, y) -> 
    Printf.printf "(";
    Printf.printf "\\";
    print_rtype x.ty;
    Printf.printf ".";
    print_formula y;
    Printf.printf ")"
  | Forall (x, y, _) -> 
    Printf.printf "(";
    Printf.printf "∀";
    print_rtype x.ty;
    Printf.printf ".";
    print_formula y;
    Printf.printf ")"
  | App (x, y, template) -> 
    Printf.printf "(";
    print_formula x;
    Printf.printf " ";
    print_formula y;
    Printf.printf ")";
  | Arith x ->
    Print.arith Fmt.stdout x;
    Fmt.flush Fmt.stdout () 
  | Pred (x,[f1; f2]) -> 
    Print.arith Fmt.stdout f1;
    Print.pred Fmt.stdout x;
    Print.arith Fmt.stdout f2;
    Fmt.flush Fmt.stdout () ;
  | Pred (x,_) -> 
    Print.pred Fmt.stdout x;
    Fmt.flush Fmt.stdout () 

let rec is_simple p = match p with
  | And(x, y, _, _) | Or(x, y, _, _) -> (is_simple x && is_simple y)
  | Arith(_) | Var(_) | App(_) | Abs(_) | Forall(_) -> false
  | _ -> true

exception TriedToNegateApp
let rec negate p = match p with
  | Arith(_) | Var(_) | App(_) | Abs(_) | Forall(_) -> raise TriedToNegateApp
  | Or(x, y, t1, t2) -> And(negate x, negate y, t1, t2)
  | And(x, y, t1, t2) -> Or(negate x, negate y, t1, t2)
  | Bool x -> Bool (not x)
  | Pred(p, l) -> Pred(Formula.negate_pred p, l)

let rec translate_if hflz = match hflz with
  | Or(And(a, b, s1, s2), And(a', b', s1',s2'), t1, t2) ->
    let fa = is_simple a in
    let fa' = is_simple a' in
    let fb = is_simple b in
    let fb' = is_simple b' in
    if fa && fa' && negate a = a' then
      And(Or(a', translate_if b, s1, s2), Or(a, translate_if b', s1', s2'), t1, t2)
    else if fa && fb' && negate a = b' then
      And(Or(b', translate_if b, s1, s2), Or(a, translate_if a', s1', s2'), t1, t2)
    else if fb && fa' && negate b = a' then
      And(Or(a', translate_if a, s1, s2), Or(b, translate_if b', s1', s2'), t1, t2)
   else if fb && fb' && negate b = b' then
      And(Or(b', translate_if a, s1, s2), Or(b, translate_if a', s1', s2'), t1, t2)
    else 
      Or(And(translate_if a, translate_if b, s1, s2), And(translate_if a', translate_if b', s1', s2'), t1, t2)
  | Or(x, y, t1, t2) -> Or(translate_if x, translate_if y, t1, t2)
  | And(x, y, t1, t2) -> And(translate_if x, translate_if y, t1, t2)
  | Abs (x, t) -> Abs(x, translate_if t)
  | x -> x

type hes_rule =
  { var  : Rtype.t Id.t
  ; body : t
  ; fix  : Fixpoint.t
  }

let lookup_rule f hes =
  List.find_exn hes ~f:(fun r -> Id.eq r.var f)

type hes = hes_rule list

let main_symbol = function
  | [] -> failwith "empty hes"
  | s::_ -> s.var
let main hes = Var(main_symbol hes)
