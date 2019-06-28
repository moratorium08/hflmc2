module Arith    = Arith
module Fixpoint = Fixpoint
module Format   = Format_
module Formula  = Formula
module Hfl      = Hfl
module Hflz     = Hflz
module Id       = Id
module Type     = Type
module Lexer    = Lexer
module Mparser  = Mparser
module Parser   = Parser
module Raw_hflz = Raw_hflz
module Simplify = Simplify
module Subst    = Subst
module IdMap    = IdMap
module IdSet    = IdSet

module P = struct
  module I = Mparser.MenhirInterpreter

  (* -------------------------------------------------------------------------- *)

  (* The loop which drives the parser. At each iteration, we analyze a
     checkpoint produced by the parser, and act in an appropriate manner.
     [lexbuf] is the lexing buffer. [checkpoint] is the last checkpoint produced
     by the parser. *)

  (* let rec loop lexbuf (checkpoint : Raw_hflz.raw_hflz_hes I.checkpoint) = *)
  (*   match checkpoint with *)
  (*   | I.InputNeeded _env -> *)
  (*       (* The parser needs a token. Request one from the lexer, *)
  (*          and offer it to the parser, which will produce a new *)
  (*          checkpoint. Then, repeat. *) *)
  (*       let token = Lexer.token lexbuf in *)
  (*       let startp = lexbuf.lex_start_p *)
  (*       and endp = lexbuf.lex_curr_p in *)
  (*       let checkpoint = I.offer checkpoint (token, startp, endp) in *)
  (*       loop lexbuf checkpoint *)
  (*   | I.Shifting _ *)
  (*   | I.AboutToReduce _ -> *)
  (*       let checkpoint = I.resume checkpoint in *)
  (*       loop lexbuf checkpoint *)
  (*   | I.HandlingError _env -> *)
  (*       (* The parser has suspended itself because of a syntax error. Stop. *) *)
  (*       Printf.fprintf stderr *)
  (*         "At offset %d: syntax error.\n%!" *)
  (*         (Lexing.lexeme_start lexbuf) *)
  (*   | I.Accepted v -> *)
  (*       (* The parser has succeeded and produced a semantic value. Print it. *) *)
  (*       Format.printf "%a\n%!" Raw_hflz.pp_raw_hflz_hes v *)
  (*   | I.Rejected -> *)
  (*       (* The parser rejects this input. This cannot happen, here, because *)
  (*          we stop as soon as the parser reports [HandlingError]. *) *)
  (*       assert false *)

  (* -------------------------------------------------------------------------- *)

  (* The above loop is shown for explanatory purposes, but can in fact be
     replaced with the following code, which exploits the functions
     [lexer_lexbuf_to_supplier] and [loop_handle] offered by Menhir. *)

  let succeed (v : Raw_hflz.raw_hflz_hes) =
    (* The parser has succeeded and produced a semantic value. Print it. *)
    Format.printf "%a@." Raw_hflz.pp_raw_hflz_hes v

  let fail lexbuf (_ : Raw_hflz.raw_hflz_hes I.checkpoint) =
    (* The parser has suspended itself because of a syntax error. Stop. *)
    Printf.fprintf stderr
      "At offset %d: syntax error.\n%!"
      (Lexing.lexeme_start lexbuf)

  let loop lexbuf result =
    let supplier = I.lexer_lexbuf_to_supplier Lexer.token lexbuf in
    I.loop_handle succeed (fail lexbuf) supplier result

  (* -------------------------------------------------------------------------- *)

  (* Initialize the lexer, and catch any exception raised by the lexer. *)

  let process (line : string) =
    let lexbuf = Lexing.from_string line in
    try
      loop lexbuf (Mparser.Incremental.hes lexbuf.lex_curr_p)
    with
    | Lexer.Error msg -> Printf.fprintf stderr "%s%!" msg

  (* -------------------------------------------------------------------------- *)

  (* The rest of the code is as in the [calc] demo. *)

  (* let process (optional_line : string option) = *)
  (*   match optional_line with *)
  (*   | None -> *)
  (*       () *)
  (*   | Some line -> *)
  (*       process line *)
  (*  *)
  (* let rec repeat channel = *)
  (*   (* Attempt to read one line. *) *)
  (*   let optional_line, continue = Lexer.token channel in *)
  (*   process optional_line; *)
  (*   if continue then *)
  (*     repeat channel *)
  (*  *)
  (* let () = *)
  (*   repeat (Lexing.from_channel stdin) *)

end
