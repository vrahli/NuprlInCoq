val parse : bool (* true to print debug info *)
  -> string list (* theories to filter out *)
    -> string    (* file to parse *)
      -> bool    (* true if ones wants to split the file into smaller files *)
	-> NuprlTerms.nuprl_term list

val parseString : bool (* true to print debug info *)
  -> string list       (* theories to filter out *)
    -> string          (* string to parse *)
      -> NuprlTerms.nuprl_term list
