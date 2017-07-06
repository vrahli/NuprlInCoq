{
 open NuprlAsciiParse
 let line = ref 1
}

let escape     = ['\t' ' ']+
let digitDec   = ['0' - '9']
let letter     = ['a' - 'z' 'A' - 'Z']
let symbol     = ['!' '%' '&' '$' '#' '+' '/' '<' '=' '>' '?' '@' '\\' '~' '`' '^' '|' '*' '-']
let prime      = "'"
let alphadigit = letter | digitDec | '_' | prime | symbol
               | "\\{" | "\\}" | "\\(" | "\\)" | "\\[" | "\\]" | "\\:" | "\\," | "\\ " | "\\."
let ident      = alphadigit*

rule token = parse
  | "\n"       {line := !line + 1; Lexing.new_line lexbuf; token lexbuf}
  | escape     {token lexbuf}
  | "\000"     {token lexbuf}
  | "\004"     {SEP}
  | "("        {LPAREN}
  | ")"        {RPAREN}
  | "{"        {LBRACE}
  | "}"        {RBRACE}
  | ":"        {COLON}
  | ";"        {SEMICOLON}
  | ","        {COMMA}
  | ident as i {ID (i)}
  | _          {failwith ((Lexing.lexeme lexbuf) ^ ": mistake at line " ^ string_of_int !line)}
  | eof        {EOF}
