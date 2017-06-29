type token =
  | EOL
  | EOF
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | COLON
  | COMMA
  | SEMICOLON
  | OPID
  | SEP
  | ID of (string)

val terms :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> string list -> NuprlTerms.nuprl_term list
