
(* The type of tokens. *)

type token = 
  | SEP
  | SEMICOLON
  | RPAREN
  | RBRACE
  | LPAREN
  | LBRACE
  | ID of (string)
  | EOF
  | COMMA
  | COLON

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val terms: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (string list -> NuprlTerms.nuprl_term list)
