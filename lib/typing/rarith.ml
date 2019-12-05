open Hflmc2_util
open Rid

type op =
  | Add
  | Sub
  | Mult

type t =
  | Int of int
  | Var of id
  | Op  of op * t list

let rec print_op' x1 s x2 = 
  print_string "(";
  print_arith x1;
  print_string s;
  print_arith x2;
  print_string ")"
and print_op = function
  | Add -> 
  begin
    function 
    | [x1; x2] -> print_op' x1 "+" x2
    | l -> print_ariths l
  end
  | Sub -> 
  begin
    function 
    | [x1; x2] -> print_op' x1 "-" x2
    | l -> print_ariths l
  end
  | Mult -> 
  begin
    function 
    | [x1; x2] -> print_op' x1 "*" x2
    | l -> print_ariths l
  end
and print_arith = function
  | Int x -> print_int x
  | Var id -> print_id id
  | Op (op, args) -> print_op op args
and print_ariths = function
  | [] -> ()
  | [x] -> print_arith x
  | x::xs -> 
    print_arith x;
    print_string ", ";
    print_ariths xs

