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

open Parsing;;
let _ = parse_error;;
# 2 "nuprlAsciiParse.mly"
module E = NuprlTerms

type 'a t  = unit -> 'a
type 'a u  = string list -> 'a

let isin_str str lst = List.exists (fun (s : string) -> s = str) lst
# 25 "nuprlAsciiParse.ml"
let yytransl_const = [|
  257 (* EOL *);
    0 (* EOF *);
  258 (* LPAREN *);
  259 (* RPAREN *);
  260 (* LBRACE *);
  261 (* RBRACE *);
  262 (* COLON *);
  263 (* COMMA *);
  264 (* SEMICOLON *);
  265 (* OPID *);
  266 (* SEP *);
    0|]

let yytransl_block = [|
  267 (* ID *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\003\000\003\000\004\000\004\000\005\000\005\000\
\006\000\006\000\002\000\002\000\007\000\010\000\010\000\011\000\
\011\000\008\000\008\000\012\000\013\000\013\000\009\000\009\000\
\000\000"

let yylen = "\002\000\
\001\000\002\000\001\000\003\000\000\000\001\000\000\000\001\000\
\000\000\001\000\010\000\006\000\001\000\003\000\002\000\001\000\
\003\000\000\000\002\000\001\000\001\000\003\000\000\000\001\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\025\000\000\000\000\000\013\000\000\000\
\002\000\000\000\000\000\000\000\006\000\000\000\000\000\010\000\
\000\000\000\000\000\000\000\000\004\000\008\000\012\000\000\000\
\000\000\000\000\019\000\000\000\015\000\000\000\000\000\000\000\
\014\000\017\000\020\000\000\000\000\000\024\000\000\000\000\000\
\011\000\022\000"

let yydgoto = "\002\000\
\004\000\005\000\013\000\014\000\023\000\015\000\025\000\020\000\
\036\000\026\000\027\000\037\000\038\000"

let yysindex = "\003\000\
\001\255\000\000\254\254\000\000\001\255\006\255\000\000\009\255\
\000\000\001\255\002\255\008\255\000\000\014\255\011\255\000\000\
\001\255\010\255\000\255\016\255\000\000\000\000\000\000\002\255\
\013\255\017\255\000\000\023\255\000\000\002\255\000\255\001\255\
\000\000\000\000\000\000\024\255\018\255\000\000\010\255\001\255\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\028\000\000\000\000\000\000\000\
\000\000\028\255\007\255\029\255\000\000\000\000\030\255\000\000\
\000\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\031\255\000\000\000\000\000\000\000\000\000\000\034\255\
\000\000\000\000\000\000\000\000\035\255\000\000\001\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\029\000\246\255\016\000\000\000\002\000\000\000\255\255\000\000\
\000\000\000\000\008\000\000\000\004\000"

let yytablesize = 265
let yytable = "\012\000\
\007\000\008\000\006\000\001\000\003\000\024\000\012\000\010\000\
\007\000\016\000\007\000\009\000\007\000\009\000\011\000\017\000\
\018\000\019\000\030\000\022\000\028\000\035\000\029\000\031\000\
\032\000\040\000\039\000\001\000\033\000\035\000\005\000\003\000\
\021\000\009\000\018\000\016\000\023\000\021\000\034\000\000\000\
\041\000\000\000\000\000\042\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\007\000\007\000\000\000\000\000\000\000\
\007\000"

let yycheck = "\010\000\
\000\000\003\000\005\001\001\000\004\001\006\001\017\000\002\001\
\011\001\011\000\011\001\005\001\011\001\007\001\006\001\008\001\
\003\001\007\001\006\001\010\001\005\001\032\000\024\000\007\001\
\002\001\008\001\003\001\000\000\030\000\040\000\003\001\003\001\
\017\000\005\000\005\001\005\001\003\001\003\001\031\000\255\255\
\039\000\255\255\255\255\040\000\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\003\001\004\001\255\255\255\255\255\255\
\008\001"

let yynames_const = "\
  EOL\000\
  EOF\000\
  LPAREN\000\
  RPAREN\000\
  LBRACE\000\
  RBRACE\000\
  COLON\000\
  COMMA\000\
  SEMICOLON\000\
  OPID\000\
  SEP\000\
  "

let yynames_block = "\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 29 "nuprlAsciiParse.mly"
      (fun lst ->
	match _1 lst with
	  Some t -> [t]
	| None -> [])
# 189 "nuprlAsciiParse.ml"
               : string list -> NuprlTerms.nuprl_term list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string list -> NuprlTerms.nuprl_term list) in
    Obj.repr(
# 34 "nuprlAsciiParse.mly"
      (fun lst ->
	let term  = _1  lst in
	let terms = _2 lst in
	match term with
	  Some t -> t :: terms
	| None -> terms)
# 202 "nuprlAsciiParse.ml"
               : string list -> NuprlTerms.nuprl_term list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 43 "nuprlAsciiParse.mly"
      (fun () ->
	match _1 [] with
	  Some t -> [t]
	| None -> [])
# 212 "nuprlAsciiParse.ml"
               : 'terms2))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'terms2) in
    Obj.repr(
# 48 "nuprlAsciiParse.mly"
      (fun () ->
	let term  = _1 [] in
	let terms = _3 () in
	match term with
	  Some t -> t :: terms
	| None -> terms)
# 225 "nuprlAsciiParse.ml"
               : 'terms2))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "nuprlAsciiParse.mly"
           (fun () -> [])
# 231 "nuprlAsciiParse.ml"
               : 'terms1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'terms2) in
    Obj.repr(
# 57 "nuprlAsciiParse.mly"
           (_1)
# 238 "nuprlAsciiParse.ml"
               : 'terms1))
; (fun __caml_parser_env ->
    Obj.repr(
# 60 "nuprlAsciiParse.mly"
        (fun () -> ())
# 244 "nuprlAsciiParse.ml"
               : 'sep_op))
; (fun __caml_parser_env ->
    Obj.repr(
# 61 "nuprlAsciiParse.mly"
        (fun () -> ())
# 250 "nuprlAsciiParse.ml"
               : 'sep_op))
; (fun __caml_parser_env ->
    Obj.repr(
# 64 "nuprlAsciiParse.mly"
    (fun () -> E.mk_tag "")
# 256 "nuprlAsciiParse.ml"
               : 'tag))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ident) in
    Obj.repr(
# 66 "nuprlAsciiParse.mly"
      (fun () ->
	let itag = _1 () in
	if itag = E.default_dtag
	then E.dtag
	else E.mk_tag itag)
# 267 "nuprlAsciiParse.ml"
               : 'tag))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 8 : 'ident) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : 'tag) in
    let _5 = (Parsing.peek_val __caml_parser_env 5 : 'parameters1) in
    let _8 = (Parsing.peek_val __caml_parser_env 2 : 'bound_terms1) in
    let _10 = (Parsing.peek_val __caml_parser_env 0 : 'sep_op) in
    Obj.repr(
# 84 "nuprlAsciiParse.mly"
      (fun lst ->
	let opid = _2 () in
	if isin_str opid lst
	then None
	else
	  let tag      = _4  () in
	  let params   = _5  () in
	  let b_terms  = _8  () in
	  let _        = _10 () in
	  Some (E.mk_term opid tag params b_terms))
# 287 "nuprlAsciiParse.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'terms1) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'sep_op) in
    Obj.repr(
# 95 "nuprlAsciiParse.mly"
      (fun lst ->
	let terms = _4 () in
	let _     = _6 () in
	Some (E.mk_nuprl_iwf_lemmas_term terms))
# 298 "nuprlAsciiParse.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 101 "nuprlAsciiParse.mly"
       (fun () -> _1)
# 305 "nuprlAsciiParse.ml"
               : 'ident))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'ident) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'ident) in
    Obj.repr(
# 105 "nuprlAsciiParse.mly"
      (fun () ->
	let id1 = _1 () in
	let id2 = _3 () in
	(id1, id2))
# 316 "nuprlAsciiParse.ml"
               : 'parameter))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ident) in
    Obj.repr(
# 110 "nuprlAsciiParse.mly"
      (fun () -> ("", _2 ()))
# 323 "nuprlAsciiParse.ml"
               : 'parameter))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parameter) in
    Obj.repr(
# 114 "nuprlAsciiParse.mly"
      (fun () -> [_1 ()])
# 330 "nuprlAsciiParse.ml"
               : 'parameters))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'parameter) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'parameters) in
    Obj.repr(
# 116 "nuprlAsciiParse.mly"
      (fun () -> (_1 ()) :: (_3 ()))
# 338 "nuprlAsciiParse.ml"
               : 'parameters))
; (fun __caml_parser_env ->
    Obj.repr(
# 119 "nuprlAsciiParse.mly"
    (fun () -> [])
# 344 "nuprlAsciiParse.ml"
               : 'parameters1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'parameters) in
    Obj.repr(
# 120 "nuprlAsciiParse.mly"
                     (_2)
# 351 "nuprlAsciiParse.ml"
               : 'parameters1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 124 "nuprlAsciiParse.mly"
      (fun () ->
	match (_1 []) with
	  Some (E.TERM ((("bound_id", _), params), [E.B_TERM ([], b_term)])) ->
	    let b_vars = List.map (fun (v, _) -> v) params in
	    E.B_TERM (b_vars, b_term)
	| Some (E.TERM ((("bound_id", _), _), _)) -> failwith "nuprl_ascii_parse_bound_term_1"
	| Some term -> E.B_TERM ([], E.mk_rterm term)
	| None -> failwith "nuprl_ascii_parse_bound_term_2")
# 365 "nuprlAsciiParse.ml"
               : 'bound_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bound_term) in
    Obj.repr(
# 134 "nuprlAsciiParse.mly"
               (fun () -> [_1 ()])
# 372 "nuprlAsciiParse.ml"
               : 'bound_terms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'bound_term) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'bound_terms) in
    Obj.repr(
# 135 "nuprlAsciiParse.mly"
                                     (fun () -> (_1 ()) :: (_3 ()))
# 380 "nuprlAsciiParse.ml"
               : 'bound_terms))
; (fun __caml_parser_env ->
    Obj.repr(
# 138 "nuprlAsciiParse.mly"
    (fun () -> [])
# 386 "nuprlAsciiParse.ml"
               : 'bound_terms1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bound_terms) in
    Obj.repr(
# 139 "nuprlAsciiParse.mly"
                (_1)
# 393 "nuprlAsciiParse.ml"
               : 'bound_terms1))
(* Entry terms *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let terms (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : string list -> NuprlTerms.nuprl_term list)
;;
