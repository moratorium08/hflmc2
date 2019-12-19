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
type cnf = refinement list

let rec cross_and l r = 
  let rec cross_and_inner l item = match l with
    | [] -> []
    | x::xs -> RAnd(x, item) :: cross_and_inner xs item
  in
  match r with
  | [] -> []
  | x::xs -> 
    cross_and_inner l x @ cross_and l xs

let rec cross_or l r = 
  let rec cross_or_inner l item = match l with
    | [] -> []
    | x::xs -> ROr(x, item) :: cross_or_inner xs item
  in
  match r with
  | [] -> []
  | x::xs -> 
    cross_or_inner l x @ cross_or l xs

(* dnf: disjunction normal form *)
let rec ref2dnf (head: refinement): dnf = match head with
  | ROr(x, y) -> 
    ref2dnf x @ ref2dnf y
  | RAnd(x, y) -> 
    let left = ref2dnf x in
    let right = ref2dnf y in
    cross_and left right
  | x -> [x]
  
(* cnf: conjunction normal form *)
let rec ref2cnf (head: refinement): cnf = match head with
  | RAnd(x, y) -> 
    ref2cnf x @ ref2cnf y
  | ROr(x, y) -> 
    let left = ref2cnf x in
    let right = ref2cnf y in
    cross_or left right
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
  let (preds, non_preds) = chc.head |> ref2dnf |> split_dnf [] [] in
  let negated_non_preds = non_preds |> List.map negate_ref |> cnf2ref in
  let preds' = dnf2ref preds in
  {head=preds'; body=conjoin chc.body negated_non_preds}

let rec split_head_by_and_when_possible head = 
  let preds = ref2dnf head in
  match preds with
  | [] -> Some([head])
  | [pred] ->
    Some(ref2cnf pred)
  | _ -> None

let divide_chc chc = 
  let rec inner heads = match heads with
    | [] -> []
    | head::xs -> {chc with head=head} :: inner xs
  in
  chc.head |> ref2cnf |> inner

let dual chc = {head=Rtype.dual chc.body; body=Rtype.dual chc.head}


let rec normalize chcs = 
  let rec divide_chcs = function
  | [] -> []
  | x::xs -> divide_chc x @ divide_chcs xs
in
(* args: template's arguments 
  current_vars: occurred variable set which is reused
  *)
let rec rename args current_vars accum = match args with
  | [] -> [], accum
  | Arith.Var(n)::xs when not (IdSet.mem current_vars n) -> 
    let (l, ret) = rename xs (IdSet.add current_vars n) accum in
    Arith.Var(n) :: l, ret 
  | x::xs ->
    let new_id = Id.gen ~name:"tmp" `Int in
    let accum' = conjoin accum (RPred(Formula.Eq, [Arith.Var(new_id); x])) in
    let (l, ret) = rename xs current_vars accum' in
    Arith.Var(new_id) :: l, ret
in
let rec rename_rty rty = match rty with
  | ROr(x, y) -> 
    let (x, a) = rename_rty x in
    let (y, b) = rename_rty y in
    ROr(x, y), (conjoin a b)
  | RTemplate(p, l) -> 
      let (l, ret) = rename l IdSet.empty RTrue in
      RTemplate(p, l), ret
  | RFalse -> RFalse, RTrue
  | _ -> failwith "program error(normalize)"
in
let rename_head chc = 
  (*let (h, ret) = match chc.head with
  | ROr _ -> rename_rty chc.head 
  | _ -> chc.head, RTrue
  in*)
  let h, ret = rename_rty chc.head in
  {body=conjoin ret chc.body; head=h}
in
let divided_chc = divide_chcs chcs in
let simplified' = List.map expand_head_exact divided_chc in
let renamed = List.map rename_head simplified' in
renamed

let rec underapproximate chcs = 
  (* heuristic........ *)
  let rec good_bye_or rty = match rty with
    | ROr(_, x) -> good_bye_or x
    | x -> x
  in
  match chcs with
  | [] -> []
  | chc::xs -> 
    {chc with head=good_bye_or chc.head}::underapproximate xs

(* expand iterator にして、順に調べられるようにする *)
let expand chcs = 
  let rec gen_map chcs m = match chcs with
    | [] -> m
    | {head=RTemplate(p, l); body=body}::xs -> 
      let cnt' = count_preds body in
      begin
        match Rid.M.find_opt p m with
        | Some((_, _, cnt)) when cnt <= cnt' -> 
          gen_map xs m
        | _ -> 
          m |> Rid.M.add p (l, body, cnt') |> gen_map xs
      end
    | _::xs -> 
      m |> gen_map xs
  in

  (* first, normalize chcs and create maps from pred to chc *)
  let chcs = normalize chcs in
  let m = gen_map chcs Rid.M.empty in

  (* auxiliary function *)
  let rec expand_one_step' head = 
    let rec arith_var_list_to_id_list l = match l with
    | [] -> []
    | Arith.Var(x)::xs -> x::arith_var_list_to_id_list xs
    | _ -> failwith "program error(expand_one_step')"
    in
    let rec zip l l' = match (l, l') with
      | ([], []) -> []
      | (x::xs, y::ys) -> (x, y)::zip xs ys
      | _ -> failwith "program error(expand_one_step' zip)"
    in
    match head with
    | ROr(x, y) -> ROr(expand_one_step' x, expand_one_step' y)
    | RTemplate(p, l) when Rid.M.mem p m ->
      let (l', body, _) = Rid.M.find p m in
      (* subst l' -> l of body *)
      let l'' = arith_var_list_to_id_list l' in
      let l''' = List.map (fun x -> RArith x) l in
      let sl = zip l'' l''' in
      let body' = subst_refinement_with_ids body sl in
      body'
    | x -> x
  in
  let rec expand_one_step chcs = match chcs with
    | [] -> []
    | chc::xs -> 
    begin
      match chc.head with
      | ROr _ -> 
        {chc with head=expand_one_step' chc.head} :: expand_one_step xs
      | _ -> chc::expand_one_step xs
    end
  in
  let chcs = expand_one_step chcs in
  let chcs = underapproximate chcs in
  chcs