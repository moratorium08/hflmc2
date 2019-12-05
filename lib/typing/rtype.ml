open Hflmc2_syntax

type id = int

type template = id * id list (* template prdicate name and its args *)


let print_template (id, _) = Printf.printf "X%d" id

type refinement
  = RTrue
   | RFalse
   | RPred of Formula.pred * Arith.t list
   | RAnd of refinement * refinement
   | ROr of refinement * refinement
   | RTemplate of template

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
  
type rint =
  | RId of id
  | RArith of Arith.t

let print_rint = function
  | RId x -> print_string "id"
  | RArith x -> Print.print Print.arith x

type t 
  = RBool of refinement
  | RArrow of t * t
  | RInt of rint

let rec print_rtype = function
  | RBool r -> Printf.printf "*["; print_refinement r; Printf.printf "]"
  | RArrow(x, y) ->
    print_rtype x;
    Printf.printf " -> ";
    print_rtype y
  | RInt _ -> Printf.printf "int"