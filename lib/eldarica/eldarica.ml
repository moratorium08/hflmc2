module Parser = Parser
module Dag = Dag


let parse lexbuf = 
  try
    Parser.graph Lexer.read lexbuf
  with
    | Parser.Error ->
    failwith @@ Printf.sprintf "Parse error "
  | Failure _ ->
      failwith @@ Printf.sprintf "Lexing error "

let parse_file in_name =
  in_name |> open_in |> Lexing.from_channel |> parse

let parse_string data =
  data |> Lexing.from_string |> parse