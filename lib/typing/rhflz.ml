open Hflmc2_util
open Hflmc2_syntax
open Id
open Rtype

type t =
  | Bool   of bool
  | Var    of Rtype.t Id.t
  | Or     of t * t
  (* template is used for tracking counterexample. *)
  | And    of t * t * template
  | Abs    of Rtype.t Id.t * t
  | App    of t * t
  | Forall of Rtype.t Id.t * t * template
  (* constructers only for hflz *)
  | Arith  of Arith.t
  | Pred   of Formula.pred * Arith.t list

let rec print_formula = function
  | Bool x when x -> Printf.printf "tt"
  | Bool _ -> Printf.printf "ff"
  | Var x -> Printf.printf "%s" (Id.to_string x)
  | Or (x, y) -> 
    Printf.printf "(";
    print_formula x;
    Printf.printf " || ";
    print_formula y;
    Printf.printf ")";
  | And (x, y, _) -> 
    Printf.printf "(";
    print_formula x;
    Printf.printf " && ";
    print_formula y;
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
  | App (x, y) -> 
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
    Fmt.flush Fmt.stdout () ;


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
