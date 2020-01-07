module Parser = Parser
module Dag = Dag

let parse_file in_name =
  let f = open_in in_name in
  let lexbuf = Lexing.from_channel f in
  try
    Parser.graph Lexer.read lexbuf
  with
    | Parser.Error ->
    failwith @@ Printf.sprintf "Parse error "
    | Failure _ ->
      failwith @@ Printf.sprintf "Lexing error "


