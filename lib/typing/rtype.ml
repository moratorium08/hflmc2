open Hflmc2_syntax
open Rid
open Rresult



let id_source = ref 0
let id_top = 0
let created = ref false
let generate_id () = id_source := !id_source + 1; !id_source
let generate_template args = (generate_id (), List.map (fun x -> Arith.Var(x)) args)
let generate_top_template args  = 
  if !created then
    failwith "You attempted to create top template twice"
  else
    created := true;
    (id_top, args)
  
let rec print_ariths = function
  | [] -> ()
  | [x] -> 
    Print.arith Fmt.stdout x;
    Fmt.flush Fmt.stdout () ;
  | x::xs ->
    Print.arith Fmt.stdout x;
    Fmt.flush Fmt.stdout () ;
    print_string ",";
    print_ariths xs

let print_template (id, l) = 
  Printf.printf "X%d(" id;
  print_ariths l;
  print_string ")"

type rint =
  | RId of [`Int] Id.t
  | RArith of Arith.t
and t 
  = RBool of refinement
  | RArrow of t * t
  | RInt of rint
and refinement
  = RTrue
   | RFalse
   | RPred of Formula.pred * Arith.t list
   | RAnd of refinement * refinement
   | ROr of refinement * refinement
   | RTemplate of template
and template = id * Arith.t list (* template prdicate name and its args *)

let generate_rtemplate args = RTemplate(generate_id(), args)

(* clone *)
let rec clone_type_with_new_pred ints = function
  | RBool(RTemplate(_, _)) -> RBool(RTemplate(generate_id (), ints))
  | RArrow(RInt(RId(id)), y) ->
    RArrow(RInt(RId(id)), clone_type_with_new_pred (Arith.Var(id)::ints) y) 
  | RArrow(x, y) -> 
    RArrow(clone_type_with_new_pred ints x, clone_type_with_new_pred ints y)
  | x -> x

let print_rint = function
  | RId x -> 
    Print.id Fmt.stdout x;
    Fmt.flush Fmt.stdout () 
  | RArith x -> 
    Print.arith Fmt.stdout x;
    Fmt.flush Fmt.stdout () 

let rec print_refinement = function
  | RTrue -> Printf.printf "tt"
  | RFalse -> Printf.printf "ff"
  | RPred (x,[f1; f2]) -> 
    Print.arith Fmt.stdout f1;
    Print.pred Fmt.stdout x;
    Print.arith Fmt.stdout f2;
    Fmt.flush Fmt.stdout () ;
  | RPred (x,_) -> 
    Print.pred Fmt.stdout x;
    Fmt.flush Fmt.stdout () ;
  | RAnd(x, y) -> 
    print_string "(";
    print_refinement x; 
    Printf.printf " /\\ "; 
    print_refinement y;
    print_string ")";
  | ROr(x, y) -> 
    print_string "(";
    print_refinement x; 
    Printf.printf " \\/ "; 
    print_refinement y;
    print_string ")";
  | RTemplate t -> print_template t

let rec print_rtype = function
  | RBool r -> Printf.printf "*["; print_refinement r; Printf.printf "]"
  | RArrow(x, y) ->
    print_string "(";
    print_rtype x;
    Printf.printf " -> ";
    print_rtype y;
    print_string ")";
  | RInt x -> print_rint x; Printf.printf ": int"

  
let rint2arith = function
  | RId x -> Arith.Var(x)
  | RArith x -> x

let conjoin x y =
  if x = RTrue then y
  else if y = RTrue then x
  else if x = RFalse then RFalse
  else if y = RFalse then RFalse
  else RAnd(x, y)

let disjoin x y =
  if x = RFalse then y
  else if y = RFalse then x
  else if x = RTrue then RTrue
  else if y = RTrue then RTrue
  else ROr(x, y)

let subst_ariths id rint l = match rint with 
  | RId id' -> 
    List.map (Trans.Subst.Arith.arith id (Arith.Var(id'))) l
  | RArith a ->
    List.map (Trans.Subst.Arith.arith id a) l

let rec subst_refinement id rint = function
  | RPred (p, l) -> RPred(p, subst_ariths id rint l)
  | RAnd(x, y) -> conjoin (subst_refinement id rint x) (subst_refinement id rint y)
  | ROr(x, y) -> ROr(subst_refinement id rint x, subst_refinement id rint y)
  | RTemplate(id', l) -> RTemplate(id', subst_ariths id rint l)
  | x -> x

let rec subst id rint = function
  | RBool r -> RBool(subst_refinement id rint r)
  | RArrow(x, y) -> RArrow(subst id rint x, subst id rint y)
  | RInt x -> RInt x

(* tuple of ids of substitution *)
let rec subst_refinement_with_ids body l = match l with
  | [] -> body
  | (x, y):: xs -> 
    subst_refinement_with_ids (subst_refinement x y body) xs

(* check if refinement contains template *)
let rec does_contain_pred = function 
  | RTemplate _ -> true
  | RAnd(x, y) | ROr(x, y) -> does_contain_pred x || does_contain_pred y
  | _ -> false
  
let rec count_preds = function 
  | RTemplate _ -> 1
  | RAnd(x, y) | ROr(x, y) -> count_preds x + count_preds y
  | _ -> 0


(* returns not formula. Negating template is illegal, so throws execption *)
exception TriedToNegateTemplate
let rec negate_ref = function
  | RTemplate _ -> raise TriedToNegateTemplate
  | RAnd(x, y) -> ROr(negate_ref x, negate_ref y)
  | ROr(x, y) -> RAnd(negate_ref x, negate_ref y)
  | RTrue -> RFalse
  | RFalse -> RTrue
  | RPred(p, l) -> RPred(Formula.negate_pred p, l)

let rec dual = function
  | RTemplate x -> RTemplate x
  | RAnd(x, y) -> ROr(dual x, dual y)
  | ROr(x, y) -> RAnd(dual x, dual y)
  | RTrue -> RFalse
  | RFalse -> RTrue
  | RPred(p, l) -> RPred(Formula.negate_pred p, l)

(* This is an adhoc optimization of formulas. The reason why this function is required is
that consider following program and its safety property problem.

[Program]
(* the definition of f and g is omitted *)
let h x = if x >= 0 then g x else f x
let m n = assert(h n)
[HES Formula]
H x =v (x >= 0 /\ G x) \/ (x < 0 /\ F x)
S n =v H n

Then this formula will generate chc formulas, at least one of which has a head which contains 
more than one or.
To remedy this problem, the above "gadget" of formula can automatically be translated to the following.
H x =v (x < 0 \/ G x) /\ (x >= 0 /\ F x)
S n =v H n
And this is what The following function does.

And for the speed of translation, I did not use the complete algorithm for this, just checking 
the negation of one formula is equal to the other.
*)

let rec translate_if = 
  function
  | ROr(RAnd(a, b), RAnd(a', b')) ->
    let fa = does_contain_pred a |> not in
    let fb = does_contain_pred b |> not in
    let fa' = does_contain_pred a' |> not in
    let fb' = does_contain_pred b' |> not in
    if fa && fa' && negate_ref a = a' then
      RAnd(ROr(a', translate_if b), ROr(a, translate_if b'))
    else if fa && fb' && negate_ref a = b' then
      RAnd(ROr(b', translate_if b), ROr(a, translate_if a'))
    else if fb && fa' && negate_ref b = a' then
      RAnd(ROr(a', translate_if a), ROr(b, translate_if b'))
   else if fb && fb' && negate_ref b = b' then
      RAnd(ROr(b', translate_if a), ROr(b, translate_if a'))
    else 
      ROr(RAnd(translate_if a, translate_if b), RAnd(translate_if a', translate_if b'))
  | ROr(x, y) -> ROr(translate_if x, translate_if y)
  | RAnd(x, y) -> RAnd(translate_if x, translate_if y)
  | x -> x


let rec to_bottom = function 
  | RArrow(x, y) -> RArrow(to_top x, to_bottom y)
  | RBool _ -> RBool RFalse
  | RInt(x) -> RInt(x)
and to_top = function
  | RArrow(x, y) -> RArrow(to_bottom x, to_top y)
  | RBool _ -> RBool RTrue
  | RInt(x) -> RInt(x)

let rec get_top = function
  | RBool(RTemplate(x)) -> x
  | RArrow(_, s) -> get_top s
  | _ -> failwith "program error" (* should not occur int *)

let rec simplify x = match x with
  | RPred(p, l) -> begin match Formula.simplify_pred p l with 
    | Some(true) -> RTrue
    | Some(false) -> RFalse
    | None -> x
    end
  | RAnd(x, y) -> 
    let x' = simplify x in
    let y' = simplify y in
    conjoin x' y'
  | ROr(x, y) -> 
    let x' = simplify x in
    let y' = simplify y in
    disjoin x' y'
  | x -> x