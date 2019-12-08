open Hflmc2_syntax
open Rtype

type ('head, 'body) chc = {head: 'head; body: 'body}

let print_chc chc = 
  print_refinement chc.body;
  Printf.printf " => ";
  print_refinement chc.head

let rec print_constraints = function
  | [] -> ()
  | x::xs -> print_chc x; print_newline(); print_constraints xs

(* find x=e in the toplevel of CHC's body, and then replace it by True *)
let rec find_and_cut_substs rt ids = match rt with 
  | RAnd(x, y) ->
    let (x', ids') = find_and_cut_substs x ids in
    let (y', ids'') = find_and_cut_substs y ids' in
    (RAnd(x', y'), ids'')
  | ROr(x, y) -> 
    (ROr(x, y), ids)
  | RPred(Formula.Eq, [Arith.Var(x); y]) ->
    (RTrue, (x, RArith(y)) :: ids)
  | x -> (x, ids)

let subst_chc chc = 
  let (body', substs) = find_and_cut_substs chc.body [] in
  let rec inner l rt = match l with
    | [] -> rt
    | (x, y)::xs ->
      subst_refinement x y rt |> inner xs
  in 
  let head = inner substs chc.head in
  let body = inner substs body' in
  {head=head; body=body}

  (*
type dnf = 

(* disjunction normal form *)
let translate_to_dnf (head: refinemet): = 
  *)