let init (lexbuf : Lexing.lexbuf) (fname : string) : unit =
  let open Lexing in
  lexbuf.lex_curr_p <- {
      pos_fname = fname;
      pos_lnum  = 1;
      pos_bol   = 0;
      pos_cnum  = 0;
    }

let parse prt theories_out input split =
  let inch   = open_in input in
  let lexbuf = Lexing.from_channel inch in
  let _      = init lexbuf input in
  let terms  = NuprlAsciiParse.terms NuprlAsciiLex.token lexbuf theories_out in
  let _      = close_in inch in
  terms

let parseString prt theories_out str =
  let lexbuf = Lexing.from_string str in
  let terms  = NuprlAsciiParse.terms NuprlAsciiLex.token lexbuf theories_out in
  terms
