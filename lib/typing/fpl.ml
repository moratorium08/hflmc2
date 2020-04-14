open Rtype
open Hflmc2_syntax

type t =
  | Bool   of bool
  (* template is used for tracking counterexample. *)
  | Or     of t * t 
  | And    of t * t 
  | Forall of [`Int] Id.t * t 
  | Pred   of Formula.pred * Arith.t list


let rec print = function
  | Bool x when x -> Printf.printf "tt"
  | Bool _ -> Printf.printf "ff"
  | Or (x, y) -> 
    Printf.printf "(";
    print x;
    Printf.printf " || ";
    print y;
    Printf.printf ")";
  | And (x, y) -> 
    Printf.printf "(";
    print x;
    Printf.printf " && ";
    print y;
    Printf.printf ")";
  | Forall (x, y) -> 
    Printf.printf "(";
    Printf.printf "∀";
    Printf.printf "%s" @@ Id.to_string x;
    Printf.printf ".";
    print y;
    Printf.printf ")"
  | Pred (x,[f1; f2]) -> 
    Print.arith Fmt.stdout f1;
    Print.pred Fmt.stdout x;
    Print.arith Fmt.stdout f2;
    Fmt.flush Fmt.stdout () ;
  | Pred (x,l) -> 
    Print.pred Fmt.stdout x;
    Fmt.flush Fmt.stdout () 