
open Hflmc2_util
include Angstrom

module P = struct
  let is_space =
    function | ' ' | '\t' -> true | _ -> false

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

type hes_rule =
  { var  : unit Id.t
  ; args : unit Id.t list
  ; body : unit Hflz.t
  }
  [@@deriving eq,ord,show,iter,map,fold,sexp]
type hes = hes_rule list
  [@@deriving eq,ord,show,iter,map,fold,sexp]

let hflz : unit Hflz.t t =
    fix @@ fun hflz ->
      let atom = choice ~failure_msg:"atom"
        [ lift Hflz.mk_bool bool
        ; lift Hflz.mk_var var
        ; lift Hflz.mk_arith arith
        ; choice ~failure_msg:"pred" @@
            List.map Formula.[Eq; Le; Ge; Lt; Gt] ~f:begin fun pred ->
              lift2 (Hflz.mk_pred pred) arith arith
            end
        ; parens hflz
        ] <?> "hflz:atom"
      in
      let app_expr = many1 atom >>| function
        | [] -> assert false
        | x::xs -> Hflz.mk_apps x xs
      in
      let app_expr = app_expr <?> "app_expr" in
      let modal_expr = choice ~failure_msg:"modal"
        [ lift2 Hflz.mk_forall
            (char '[' *> ident <* char ']')
            app_expr
        ; lift2 Hflz.mk_exists
            (char '<' *> ident <* char '>')
            app_expr
        ] <?> "modal_expr"
      in
      let and_expr =
        chainl1 app_expr
          (symbol "/\\" *> return (fun x y -> Hflz.mk_ands [x;y]))
        <?> "and_expr"
      in
      let or_expr =
        chainl1 and_expr
          (symbol "\\/" *> return (fun x y -> Hflz.mk_ors [x;y]))
        <?> "or_expr"
      in
      choice ~failure_msg:"hflz"
        [ or_expr
        ; lex (char '\\') >>= fun _ ->
          lident          >>= fun x ->
          let v = Id.{ name = x; id = 0; ty = () } in
          lex (char '.')  >>= fun _ ->
          hflz            >>= fun psi ->
          return (Hflz.mk_abs { v with ty = TySigma () } psi)
        ] <?> "hes_body"

let hes_rule =
  var         >>= fun _X ->
  many var    >>= fun args ->
  symbol "=v" *>
  hflz        >>= fun body ->
  return { var  = _X
         ; args = args
         ; body = body
         }

let hes =
  symbol "%HES" *>
  many1 hes_rule

