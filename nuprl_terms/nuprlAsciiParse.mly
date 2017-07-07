%{
module E = NuprlTerms

type 'a t  = unit -> 'a
type 'a u  = string list -> 'a

(*let _ = Parsing.set_trace true*)

let isin_str str lst = List.exists (fun (s : string) -> s = str) lst
%}

%token EOF
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token COLON
%token COMMA
%token SEMICOLON
%token SEP
%token <string> ID

%start terms

%type <string list -> NuprlTerms.nuprl_term list> terms
%%

terms :
  | EOF  {fun lst -> []}
  | term terms
      {fun lst ->
	let term  = $1 lst in
	let terms = $2 lst in
	match term with
	  Some t -> t :: terms
	| None -> terms}

terms2 :
  | term
      {fun () ->
	match $1 [] with
	  Some t -> [t]
	| None -> []}
  | term SEMICOLON terms2
      {fun () ->
	let term  = $1 [] in
	let terms = $3 () in
	match term with
	  Some t -> t :: terms
	| None -> terms}

terms1 :
  |        {fun () -> []}
  | terms2 {$1}

sep_op :
  |     {fun () -> ()}
  | SEP {fun () -> ()}

tag :
  | {fun () -> E.mk_tag ""}
  | ident
      {fun () ->
	let itag = $1 () in
	if itag = E.default_dtag
	then E.dtag
	else E.mk_tag itag}

/*tag :
   (fn () => E.get_dtag ())
| ident
   (fn () =>
       let val itag = ident ()
       in if itag = E.default_dtag
	  then E.get_dtag ()
	  else E.mk itag
       end)*/

term :
  | LBRACE ident COLON tag parameters1 RBRACE LPAREN bound_terms1 RPAREN sep_op
           {
             fun lst ->
             (* This is just for debugging to get the position of the term in the file.
                Note that when it's turned on, two alpha-equal terms won't match anymore if
                they have different positions.
             *)
             (*let pos = ($startpos).pos_lnum in*)
             let opid = $2 () in
	     if isin_str opid lst
	     then None
	     else
	       let tag      = $4  () in
	       let params   = $5  () in
	       let b_terms  = $8  () in
	       let _        = $10 () in
	       Some (E.mk_term opid tag 0 params b_terms)
           }
  | LBRACE RBRACE LPAREN terms1 RPAREN sep_op
           {
             fun lst ->
	     let terms = $4 () in
	     let _     = $6 () in
	     Some (E.mk_nuprl_iwf_lemmas_term terms)
           }

ident :
  | ID {fun () -> $1}

parameter :
  | ident COLON ident
      {fun () ->
	let id1 = $1 () in
	let id2 = $3 () in
	(id1, id2)}
  | COLON ident
      {fun () -> ("", $2 ())}

parameters :
  | parameter
      {fun () -> [$1 ()]}
  | parameter COMMA parameters
      {fun () -> ($1 ()) :: ($3 ())}

parameters1 :
  | {fun () -> []}
  | COMMA parameters {$2}

bound_term :
  | term
      {fun () ->
	match ($1 []) with
	| Some (E.TERM ((("bound_id",_,_), params), [E.B_TERM ([], b_term)])) ->
           let b_vars = List.map (fun (v, _) -> v) params in
	   E.B_TERM (b_vars, b_term)
	| Some (E.TERM ((("bound_id",_,_), _), _)) -> failwith "nuprl_ascii_parse_bound_term_1"
	| Some term -> E.B_TERM ([], E.mk_rterm term)
	| None -> failwith "nuprl_ascii_parse_bound_term_2"}

bound_terms :
  | bound_term {fun () -> [$1 ()]}
  | bound_term SEMICOLON bound_terms {fun () -> ($1 ()) :: ($3 ())}

bound_terms1 :
  | {fun () -> []}
  | bound_terms {$1}
%%
