open Hflmc2_util
open Id

type pred =
  | Eq
  | Neq
  | Le
  | Ge
  | Lt
  | Gt
  [@@deriving eq,ord,show,iter,map,fold,sexp]

type t
  = Bool of bool
  | Var  of string * [`Pos|`Neg] (* negate or not *)
  | Or   of t * t
  | And  of t * t
  | Pred of pred * Arith.t list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let mk_var x = Var (x, `Pos)

let mk_and a b = And(a,b)

let mk_ands = function
  | [] -> Bool true
  | x::xs -> List.fold_left xs ~init:x ~f:mk_and

let mk_or a b = Or(a,b)

let mk_ors = function
  | [] -> Bool false
  | x::xs -> List.fold_left xs ~init:x ~f:mk_or

let rec mk_not = function
  | Bool b -> Bool (not b)
  | Var (x, `Neg) -> Var(x, `Pos)
  | Var (x, `Pos) -> Var(x, `Neg)
  | Or (f1,f2) -> And(mk_not f1, mk_not f2)
  | And(f1,f2) -> Or (mk_not f1, mk_not f2)
  | Pred(pred, as') ->
      let pred' = match pred with
        | Eq  -> Neq
        | Neq -> Eq
        | Le  -> Gt
        | Gt  -> Le
        | Lt  -> Ge
        | Ge  -> Lt
      in Pred(pred', as')

let mk_implies a b = mk_or (mk_not a) b

let rec to_DNF : t -> t list list =
  fun f -> match f with
  | Var _ | Pred _ ->  [[f]]
  | Bool true -> [[]]
  | Bool false -> []
  | Or (f1, f2) -> to_DNF f1 @ to_DNF f2
  | And (f1, f2) ->
      let f1' = to_DNF f1 in
      let f2' = to_DNF f2 in
      List.concat_map f1' ~f:begin fun x ->
        List.concat_map f2' ~f:begin fun y ->
          [x @ y] (* 効率的にはList.rev_appendのほうが良いがrevが入ると見難くなるかなと思って *)
        end
      end

