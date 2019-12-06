open Hflmc2_syntax
open Rid

let rec print_ariths = function
  | [] -> ()
  | [x] -> 
    Print.print Print.arith x
  | x::xs ->
    Print.print Print.arith x;
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
  | RId x -> print_string "id"
  | RArith x -> Print.print Print.arith x

let rec print_refinement = function
  | RTrue -> Printf.printf "tt"
  | RFalse -> Printf.printf "ff"
  | RPred (x,[f1; f2]) -> 
    Print.print Print.arith f1;
    Print.print Print.pred x;
    Print.print Print.arith f2;
  | RPred (x,_) -> 
    Print.print Print.pred x;
  | RAnd(x, y) -> 
    print_refinement x; 
    Printf.printf " /\\ "; 
    print_refinement y
  | ROr(x, y) -> 
    print_refinement x; 
    Printf.printf " \\/ "; 
    print_refinement y
  | RTemplate t -> print_template t

let rec print_rtype = function
  | RBool r -> Printf.printf "*["; print_refinement r; Printf.printf "]"
  | RArrow(x, y) ->
    print_rtype x;
    Printf.printf " -> ";
    print_rtype y
  | RInt x -> Printf.printf "int("; print_rint x; Printf.printf ")"

  

