open Hflmc2_syntax
open Rid

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
    print_string ")";
    Printf.printf " /\\ "; 
    print_string "(";
    print_refinement y;
    print_string ")";
  | ROr(x, y) -> 
    print_string "(";
    print_refinement x; 
    print_string ")";
    Printf.printf " \\/ "; 
    print_string "(";
    print_refinement y;
    print_string ")";
  | RTemplate t -> print_template t

let rec print_rtype = function
  | RBool r -> Printf.printf "*["; print_refinement r; Printf.printf "]"
  | RArrow(x, y) ->
    print_rtype x;
    Printf.printf " -> ";
    print_rtype y
  | RInt x -> Printf.printf "int("; print_rint x; Printf.printf ")"

  
let rint2arith = function
  | RId x -> Arith.Var(x)
  | RArith x -> x

let conjoin x y =
  if x = RTrue then y
  else if y = RTrue then x
  else RAnd(x, y)

let rec subst_ariths id rint l = match rint with 
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