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

(* refinemenet listではなくandのないrefinementを定義したいが、きれいにやる方法がよく分からないので、とりあえず、書く *)
type dnf = refinement list

let rec cross l r = 
  let rec cross_inner l item = match l with
    | [] -> []
    | x::xs -> RAnd(x, item) :: cross_inner xs item
  in
  match r with
  | [] -> []
  | x::xs -> 
    cross_inner l x @ cross l xs
(* dnf: disjunction normal form *)
let rec translate_to_dnf (head: refinement): dnf = match head with
  | ROr(x, y) -> 
    translate_to_dnf x @ translate_to_dnf y
  | RAnd(x, y) -> 
    let left = translate_to_dnf x in
    let right = translate_to_dnf y in
    cross left right
  | x -> [x]

let rec split_dnf preds non_preds = function
  | [] -> (preds, non_preds)
  | x::xs when does_contain_pred x -> 
    split_dnf (x::preds) non_preds xs
  | x::xs -> 
    split_dnf preds (x::non_preds) xs

let rec dnf2ref (head:dnf): refinement = match head with
  | [] -> RFalse 
  | [x] -> x
  | x::xs -> List.fold_left (fun accum elem -> ROr(accum, elem)) x xs

let rec cnf2ref (head:dnf): refinement = match head with
  | [] -> RTrue
  | [x] -> x
  | x::xs -> List.fold_left (fun accum elem -> RAnd(accum, elem)) x xs

(* Move non predicate or-concatted clause to body *)
let rec expand_head_exact chc = 
  let (preds, non_preds) = chc.head |> translate_to_dnf |> split_dnf [] [] in
  let negated_non_preds = non_preds |> List.map negate_ref |> cnf2ref in
  let preds' = dnf2ref preds in
  {head=preds'; body=conjoin chc.body negated_non_preds}
