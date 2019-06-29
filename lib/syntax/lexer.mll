{
open Parser
exception Error of string
let line_no = ref 1
let end_of_previousline = ref 0
}

let space = ['\t' '\n' '\r' ' ']
let newline = ['\n']
let digit = ['0'-'9']
let lower = ['a'-'z' '_']
let upper = ['A'-'Z']
let alphanum = ['0'-'9' 'a'-'z' 'A'-'Z' '_']

rule token = parse
| "\n"   { Lexing.new_line lexbuf; token lexbuf }
| space+ { token lexbuf }
| newline
    { end_of_previousline := Lexing.lexeme_end lexbuf
    ; line_no := !line_no+1
    ; token lexbuf
    }
| "/*"            { comment lexbuf; token lexbuf }
| eof             { EOF }
| "%HES"          { START_HES }
| "("             { LPAREN    }
| ")"             { RPAREN    }
| "["             { LSQUARE   }
| "]"             { RSQUARE   }
| "<"             { LANGRE    }
| ">"             { RANGRE    }
| "true"          { TRUE      }
| "false"         { FALSE     }
| ("\\"|"λ")      { LAMBDA    }
| "."             { DOT       }
| ("=v"|"=ν")     { DEF_G     }
| ("=m"|"=μ")     { DEF_L     }
| "+"             { PLUS      }
| "-"             { MINUS     }
| "*"             { STAR      }
| "="             { EQ        }
| "<>"            { NEQ       }
| "<="            { LE        }
| ">="            { GE        }
| ("&&"|"/\\")    { AND       }
| ("||"|"\\/")    { OR        }
| digit digit*    { INT (int_of_string (Lexing.lexeme lexbuf)) }
| upper alphanum* { UIDENT (Lexing.lexeme lexbuf) }
| lower alphanum* { LIDENT (Lexing.lexeme lexbuf) }

and comment = parse
| "*/"
    { () }
| "/*"
    { comment lexbuf;
      comment lexbuf }
| eof
    { raise (Error "unterminated comment") }
| _
    { comment lexbuf }

{
  (* This part is inserted into the end of the generated file. *)
}
