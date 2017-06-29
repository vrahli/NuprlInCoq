let parse prt theories_out input split =
  let inch   = open_in input in
  let lexbuf = Lexing.from_channel inch in
  let terms  = NuprlAsciiParse.terms NuprlAsciiLex.token lexbuf theories_out in
  let _      = close_in inch in
  terms

let parseString prt theories_out str =
  let lexbuf = Lexing.from_string str in
  let terms  = NuprlAsciiParse.terms NuprlAsciiLex.token lexbuf theories_out in
  terms
