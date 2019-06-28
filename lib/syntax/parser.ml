
open Hflmc2_util
open Angstrom

module P = struct
  let is_space =
    function | ' ' | '\t' | '\n' -> true | _ -> false

  let is_eol =
    function | '\r' | '\n' -> true | _ -> false

  let is_hex =
    function | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true | _ -> false

  let is_digit =
    function '0' .. '9' -> true | _ -> false

  let is_separator =
    function
      | ')' | '(' | '<' | '>' | '@' | ',' | ';' | ':' | '\\' | '"'
      | '/' | '[' | ']' | '?' | '=' | '{' | '}' | ' ' | '\t' -> true
      | _ -> false

  let is_token =
    function
      | '\000' .. '\031' | '\127'
      | ')' | '(' | '<' | '>' | '@' | ',' | ';' | ':' | '\\' | '"'
      | '/' | '[' | ']' | '?' | '=' | '{' | '}' | ' ' -> false
      | _ -> true

  let is_alphanum =
    function
      | 'a' .. 'z'
      | 'A' .. 'Z'
      | '0' .. '9' -> true
      | _ -> false

  let is_upper =
    function
      | 'A' .. 'Z' -> true
      | _ -> false

  let is_lower =
    function
      | 'a' .. 'z' -> true
      | _ -> false

  let is_alpha =
    function
      | 'a' .. 'z'
      | 'A' .. 'Z' -> true
      | _ -> false
end

let ($^) c s = Char.escaped c ^ s
let (^$) s c = s ^ Char.escaped c

let token  = take_while1 P.is_token
let digits = take_while1 P.is_digit
let spaces = skip_while P.is_space

(* combinator *)
let lex p = p <* spaces
let chainl1 e op =
  let rec go acc =
    (lift2 (fun f x -> f acc x) op e >>= go) <|> return acc in
  e >>= go
let parens p =
  lex (skip (fun c -> c = '(')) *> p <* lex (skip (fun c -> c = ')'))

let ident  = lex @@ lift2 ($^) (satisfy P.is_alpha) (take_while P.is_alphanum) <?> "ident"
let lident = lex @@ lift2 ($^) (satisfy P.is_lower) (take_while P.is_alphanum) <?> "lident"
let uident = lex @@ lift2 ($^) (satisfy P.is_upper) (take_while P.is_alphanum) <?> "uident"

let symbol s = lex (string s) <?> "symbol `" ^ s ^ "`"

let int : int t = choice ~failure_msg:"int"
  [ lex @@ char '-' *> digits >>| Fn.(int_of_string >>> neg)
  ; lex @@ digits >>| int_of_string
  ] <?> "int"

let bool : bool t = choice ~failure_msg:"bool"
    [ symbol "true"  *> return true
    ; symbol "false" *> return false
    ] <?> "bool"

let var : unit Id.t t =
  (ident >>| fun x -> Id.{ name = x; id = 0; ty = () }) <?> "var"
let arg_var : unit Type.arg Id.t t =
  (ident >>| fun x -> Id.{ name = x; id = 0; ty = Type.TySigma () }) <?> "var"

let arith : Arith.t t =
  let mk_bin op = fun a1 a2 -> Arith.mk_op op [a1;a2] in
  let add  = lex (char '+') *> return (mk_bin Add) in
  let sub  = lex (char '-') *> return (mk_bin Sub) in
  let mult = lex (char '*') *> return (mk_bin Mult) in
  fix @@ fun arith ->
    let atom = choice ~failure_msg:"arith:atom"
          [ lift Arith.mk_int int
          ; lift Arith.mk_var var
          ; parens arith
          ] <?> "arith:atom"
    in
    let term = chainl1 atom mult <?> "arith:term" in
    chainl1 term (add <|> sub) <?> "arith"

let hflz : unit Hflz.t t =
    fix @@ fun hflz ->
      let atom = choice ~failure_msg:"atom"
        [ lift Hflz.mk_bool bool
        ; lift Hflz.mk_var var
        ; lift Hflz.mk_arith arith
        ; parens hflz
        ] <?> "hflz:atom"
      in
      let app_expr =
        begin many1 atom >>| function
        | [] -> assert false
        | x::xs -> Hflz.mk_apps x xs
        end <?> "app_expr"
      in
      let pred_expr =
        let open Formula in
        let eq  = symbol "="  *> return Eq in
        let neq = symbol "<>" *> return Neq in
        let le  = symbol "<=" *> return Le in
        let ge  = symbol ">=" *> return Ge in
        let lt  = symbol "<"  *> return Lt in
        let gt  = symbol ">"  *> return Gt in
        arith >>= fun a1 ->
        choice ~failure_msg:"pred" [eq;neq;le;ge;lt;gt] >>= fun pred ->
        arith >>= fun a2 ->
        return (Hflz.mk_pred pred a1 a2)
      in
      let pred_expr' = choice [pred_expr; app_expr] in
      let modal_expr = choice ~failure_msg:"modal_expr"
        [ lift2 Hflz.mk_forall (* TODO この辺promptが使える *)
            (char '[' *> ident <* char ']')
            pred_expr'
        ; lift2 Hflz.mk_exists
            (char '<' *> ident <* char '>')
            pred_expr'
        ; pred_expr'
        ] <?> "modal_expr"
      in
      let and_expr =
        chainl1 pred_expr'
          (symbol "/\\" *> return (fun x y -> Hflz.mk_ands [x;y]) <|>
           symbol "&&"  *> return (fun x y -> Hflz.mk_ands [x;y]))
        <?> "and_expr"
      in
      let or_expr =
        chainl1 and_expr
          (symbol "\\/" *> return (fun x y -> Hflz.mk_ors [x;y]) <|>
           symbol "||"  *> return (fun x y -> Hflz.mk_ors [x;y]))
        <?> "or_expr"
      in
      let lambda = lex @@ (symbol "\\" <|> symbol "λ") *> return () in
      let abs_expr =
        many (lambda *> arg_var <* lex (char '.')) >>= fun xs ->
        or_expr >>= fun t ->
        return (Hflz.mk_abss xs t)
      in
      abs_expr

let fix =
  (symbol "=v" <|> symbol "=ν") *> return Fixpoint.Greatest <|>
  (symbol "=μ" <|> symbol "=m") *> return Fixpoint.Least

let hes_rule : unit Hflz.hes_rule t =
  var         >>= fun _X ->
  many var    >>= fun args ->
  fix         >>= fun fix  ->
  hflz        >>= fun body ->
  symbol "."  *>
  let args' = (List.map args ~f:(fun x -> { x with ty = Type.TySigma()})) in
  let body' = Hflz.mk_abss args' body in
  return
    Hflz.{ var  = _X
         ; body = body'
         ; fix  = fix
         }

let hes = symbol "%HES" *> many1 hes_rule

(* Annotate Id to each variable *)
module Alpha = struct
  type env = int StrMap.t

  let hes : unit Hflz.hes -> unit Hflz.hes =
    fun rhes ->
      let global : env ref = ref StrMap.empty in (* free variable in outermost scope *)

      let rec arith : env -> Arith.t -> Arith.t =
        fun env a -> match a with
        | Int n -> Int n
        | Var x ->
            begin match StrMap.find env x.name, StrMap.find !global x.name with
            | None, None ->
                let id = Id.gen_id() in
                global := StrMap.add_exn !global ~key:x.name ~data:id;
                Var { x with id }
            | Some id, _ | _, Some id  ->
                Var { x with id }
            end
        | Op (op, as') -> Op (op, List.map ~f:(arith env) as')
      in

      let rec term : env -> unit Hflz.t -> unit Hflz.t =
        fun env psi -> match psi with
          | Bool _ -> psi
          | Var v ->
              begin match StrMap.find env v.name with
              | None ->
                  let id = Id.gen_id() in
                  global := StrMap.add_exn !global ~key:v.name ~data:id;
                  Var { v with id }
              | Some id ->
                  Var { v with id }
              end
          | Or  psis -> Or  (List.map ~f:(term env) psis)
          | And psis -> And (List.map ~f:(term env) psis)
          | Exists (l, psi) -> Exists (l, term env psi)
          | Forall (l, psi) -> Exists (l, term env psi)
          | App (psi1, psi2) -> App (term env psi1, term env psi2)
          | Abs(x, psi) ->
              let id = Id.gen_id() in
              let x = { x with id } in
              let env = StrMap.add_exn env ~key:x.name ~data:id in
              Abs(x, term env psi)
          | Arith a -> Arith (arith env a)
          | Pred (pred,as') -> Pred(pred, List.map ~f:(arith env) as')
      in

      let env =
        List.fold_left rhes ~init:StrMap.empty ~f:begin fun env rule ->
          StrMap.add_exn env ~key:rule.var.name ~data:(Id.gen_id())
        end
      in

      let rule : unit Hflz.hes_rule -> unit Hflz.hes_rule =
        fun r ->
          let var = { r.var with id = StrMap.find_exn env r.var.name } in
          let body = term env r.body in
          Hflz.{ var; fix = r.fix; body = body }
      in

      List.map rhes ~f:rule
end

module Typing = struct
  open Type

  type tyvar =
    | TvRef of tyvar option ref
    | TvInt
    | TvBool
    | TvArrow of tyvar * tyvar

  type env = tyvar IdMap.t
  let gen_tyvar : unit -> tyvar = fun () -> TvRef (ref None)

  let rec occur : tyvar option ref -> tyvar -> bool =
    fun r tv -> match tv with
      | TvInt | TvBool -> false
      | TvArrow(tv1, tv2) -> occur r tv1 || occur r tv2
      | TvRef({contents=None}) -> false
      | TvRef({contents=Some tv}) -> occur r tv

  let rec unify : tyvar -> tyvar -> unit =
    fun tv1 tv2 -> match tv1, tv2 with
      | TvInt, TvInt -> ()
      | TvBool, TvBool -> ()
      | TvArrow(tv11,tv12),  TvArrow(tv21,tv22) ->
          unify tv11 tv21; unify tv12 tv22
      | TvRef r1, TvRef r2 when r1 = r2 ->
          ()
      | TvRef ({contents = None} as r1), _ ->
          if occur r1 tv2 then Fn.fatal "occur check";
          r1 := Some tv2
      | _, TvRef ({contents = None} as r2) ->
          if occur r2 tv1 then Fn.fatal "occur check";
          r2 := Some tv1
      | TvRef ({contents = Some tv1'} as r1), _ ->
          r1 := Some tv2;
          unify tv1' tv2
      | _, TvRef ({contents = Some tv2'} as r2) ->
          r2 := Some tv1;
          unify tv1 tv2'
      | _, _ -> Fn.fatal "ill-typed"

  let annot_hes : unit Hflz.hes -> tyvar Hflz.hes =
    fun hes ->
      let rec annot_term : env -> unit Hflz.t -> tyvar * tyvar Hflz.t =
        fun env psi -> match psi with
          | Bool b ->
              TvBool, Bool b
          | Var x ->
              begin match IdMap.find env x with
              | None ->
                  let tv = gen_tyvar() in
                  tv, Var { x with ty = tv }
              | Some tv' ->
                  tv', Var { x with ty = tv' }
              end
          | Or psis ->
              let tvs, psis = List.unzip @@ List.map psis ~f:(annot_term env) in
              List.iter tvs ~f:(fun tv -> unify tv TvBool);
              TvBool, Or psis
          | And psis ->
              let tvs, psis = List.unzip @@ List.map psis ~f:(annot_term env) in
              List.iter tvs ~f:(fun tv -> unify tv TvBool);
              TvBool, And psis
          | Exists (l, psi) ->
              let tv, psi = annot_term env psi in
              unify tv TvBool;
              TvBool, Exists (l, psi)
          | Forall (l, psi) ->
              let tv, psi = annot_term env psi in
              unify tv TvBool;
              TvBool, Forall (l, psi)
          | App (psi1, psi2) -> (* tv_argがTvIntの場合困るな．derefでやるか *)
              let tv_fun, psi1 = annot_term env psi1 in
              let tv_arg, psi2 = annot_term env psi2 in
              let tv_ret = gen_tyvar() in
              unify (TvArrow(tv_arg, tv_ret)) tv_fun;
              tv_ret, App (psi1, psi2)
          | Abs(x, psi) ->
              let tv = gen_tyvar() in
              let x = { x with ty = TySigma tv } in
              let env = IdMap.add env x tv in
              let ret, psi = annot_term env psi in
              TvArrow(tv, ret), Abs(x, psi)
          | Arith a -> TvInt, Arith a
          | Pred (pred,as') -> TvBool, Pred(pred, as')
      in
      let env =
        List.fold_left hes ~init:IdMap.empty ~f:begin fun env rule ->
          IdMap.add env rule.var (gen_tyvar())
        end
      in
      let annot_rule : unit Hflz.hes_rule -> tyvar Hflz.hes_rule =
        fun rule ->
          let tv   = IdMap.find_exn env rule.var in
          let var  = { rule.var with ty = tv } in
          let tv', body = annot_term env rule.body in
          unify tv tv';
          { var; body; fix = rule.fix }
      in
      List.map hes ~f:annot_rule

  let rec deref' : tyvar -> simple_ty arg = function
    | TvInt  -> TyInt
    | TvBool -> TySigma (TyBool())
    | TvRef {contents=None} -> TySigma (TyBool())
    | TvRef {contents=Some tv} -> deref' tv
    | TvArrow (tv1, tv2) ->
        let x = Id.gen ~name:"t" (deref' tv1) in
        TySigma (TyArrow (x, deref tv2))
  and deref tv = match deref' tv with
    | TyInt -> assert false
    | TySigma ty -> ty

  let deref_hes : tyvar Hflz.hes -> simple_ty Hflz.hes =
    fun hes ->
      let rec deref_term : tyvar Hflz.t -> simple_ty Hflz.t = function
        | Bool b -> Bool b
        | Var x ->
            begin match deref' x.ty  with
            | TyInt -> Arith (Arith.mk_var x)
            | TySigma ty -> Var { x with ty }
            end
        | Or  psis -> Or  (List.map ~f:deref_term psis)
        | And psis -> And (List.map ~f:deref_term psis)
        | Exists (l, psi) -> Exists (l, deref_term psi)
        | Forall (l, psi) -> Forall (l, deref_term psi)
        | App (psi1, psi2) -> App (deref_term psi1, deref_term psi2)
        | Abs(x, psi) ->
            let [@warning "-8"] TySigma x_ty = x.ty in
            let x = { x with ty = deref' x_ty } in
            Abs (x, deref_term psi)
        | Arith a -> Arith a
        | Pred (pred,as') -> Pred(pred, as')
      in
      let deref_rule : tyvar Hflz.hes_rule -> simple_ty Hflz.hes_rule =
        fun rule ->
          let var  = { rule.var with ty = deref rule.var.ty } in
          let body = deref_term rule.body in
          { var; body; fix = rule.fix }
      in
      List.map hes ~f:deref_rule

  let hes hes' =
    let ahes = annot_hes hes' in
    deref_hes ahes
end

exception ParseError of string
let parse_string s =
  let rhes = match Angstrom.parse_string hes s with
    | Ok rhes -> rhes
    | Error s -> raise (ParseError s)
  in
  rhes
  |> Alpha.hes
  |> Typing.hes

let parse_file file = parse_string @@ Fn.read_file file

