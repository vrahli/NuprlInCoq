module PN = ParserNuprlAscii
module NT = NuprlTerms

let ref_default_input  = ref ""
let ref_default_output = ref "output.v"

let print_terms terms =
  List.iter
    (fun term -> print_string (NT.toStringTerm term ^ "\n"))
    terms

type abstraction =
    {
     stamp : string;
     lhs   : NT.nuprl_term ;
     rhs   : NT.nuprl_term
   }

let get_abstraction_name (abs : abstraction) : string =
  match abs with
  | {stamp;lhs;rhs} -> NT.opid_of_term lhs

let rec get_abstraction_names labs : string list =
  match labs with
  | [] -> []
  | abs :: labs -> get_abstraction_name abs :: get_abstraction_names labs

let is_primitive_abstraction (t : NT.nuprl_term) : bool =
  match t with
  | NT.TERM ((("!primitive",_,_),_),_) -> true
  | _ -> false

let destruct_abstraction_abs stamp (t : NT.nuprl_term) : abstraction option =
  match t with
  | NT.TERM ((("!abstraction",_,_),[]),[_;NT.B_TERM([],rtl);NT.B_TERM([],rtr)]) ->
     let t1 = NT.rterm2term rtl in
     let t2 = NT.rterm2term rtr in
     if is_primitive_abstraction t2 then None
     else
       Some { stamp = stamp
            ; lhs = t1
            ; rhs = t2
            }
  | _ -> failwith "destruct_abstraction_abs:wrong format"

let destruct_abstraction (term : NT.nuprl_term) : abstraction option =
  match term with
  | NT.TERM ((("ABS",_,_),[(stamp,"o");(name,"t")]),[NT.B_TERM([],rt)]) -> (* the stamp *)
    (
      match NT.rterm2term rt with
      | NT.TERM ((("source",_,_),_),[NT.B_TERM([],rt)]) -> destruct_abstraction_abs stamp (NT.rterm2term rt)
      | t -> destruct_abstraction_abs stamp t
    )

  | NT.TERM (((stamp,_,_),[]),[NT.B_TERM([],rt)]) -> (* the stamp *)
    (
      match NT.rterm2term rt with
      | NT.TERM ((("source",_,_),_),[NT.B_TERM([],rt)]) -> destruct_abstraction_abs stamp (NT.rterm2term rt)
      | t -> destruct_abstraction_abs stamp t
    )

  | _ -> failwith "cannot destruct abstraction: wrong format"

let rec destruct_abstractions_bs (bterms : NT.nuprl_bound_term list) : abstraction list =
  match bterms with
  | [] -> []
  | (NT.B_TERM([],rt)) :: bterms ->
     (
       match destruct_abstraction (NT.rterm2term rt) with
       | Some abs -> abs :: destruct_abstractions_bs bterms
       | None -> destruct_abstractions_bs bterms
     )
  | _ -> failwith "cannot destruct abstraction: wrong format"

let rec destruct_abstractions (terms : NT.nuprl_term list) : abstraction list =
  match terms with
  | [] -> []
  | t :: ts ->
     match destruct_abstraction t with
     | Some abs -> abs :: destruct_abstractions ts
     | None -> destruct_abstractions ts

type statement =
    {
     stamp : string;
     stmt  : NT.nuprl_term
   }

let destruct_statement term : statement =
  match term with
  | NT.TERM (((stamp,_,_),[]),[NT.B_TERM([],rt)]) -> (* the stamp *)
    (
     { stamp = stamp
     ; stmt  = NT.rterm2term rt
     }
    )
  | _ -> failwith "cannot destruct statement: wrong format"

let rec destruct_statements_bs (bterms : NT.nuprl_bound_term list) : statement list =
  match bterms with
  | [] -> []
  | (NT.B_TERM([],rt)) :: bterms ->
    destruct_statement (NT.rterm2term rt)
    :: destruct_statements_bs bterms
  | _ -> failwith "cannot destruct statement: wrong format"

type rule =
    {
     stamp    : string;
     goal     : NT.nuprl_term;
     name     : string;
     subgoals : NT.nuprl_term list
   }

let get_rule_name (rule : rule) : string =
  match rule with
  | {stamp;goal;name;subgoals} -> name

let rec get_rule_names (rules : rule list) : string list =
  match rules with
  | [] -> []
  | rule :: rules -> get_rule_name rule :: get_rule_names rules

let get_name (term : NT.nuprl_term) : string =
  match term with
(* Do something with the subterms *)
  | NT.TERM ((("!rule",_,_),[param]),bs) -> NT.value_of_parameter param
  | _ -> failwith "cannot get name: wrong format"

let rec get_subgoals (term : NT.nuprl_term) : NT.nuprl_term list =
  match term with
  | NT.TERM ((("!subgoal_cons",_,_),[]),[NT.B_TERM([],rt1);NT.B_TERM([],rt2)]) ->
      NT.rterm2term rt1 :: get_subgoals (NT.rterm2term rt2)
  | _ -> [term]

let destruct_rule_rule (stamp : string) (t : NT.nuprl_term) : rule =
  (* TODO: do something with rtl *)
  match t with
  | NT.TERM ((("!rule_definition",_,_),[]),[NT.B_TERM([],rtg);NT.B_TERM([],rtn);NT.B_TERM([],rtl);NT.B_TERM([],rtsg)]) ->
     (
       { stamp = stamp
       ; goal  = NT.rterm2term rtg
       ; name  = get_name (NT.rterm2term rtn)
       ; subgoals = get_subgoals (NT.rterm2term rtsg)
       }
     )
  | NT.TERM ((("!rule_definition",_,_),[]),[NT.B_TERM([],rtg);NT.B_TERM([],rtn);NT.B_TERM([],rtsg)]) ->
     (
       { stamp = stamp
       ; goal  = NT.rterm2term rtg
       ; name  = get_name (NT.rterm2term rtn)
       ; subgoals = get_subgoals (NT.rterm2term rtsg)
       }
     )
  | _ -> failwith "cannot destruct rule: wrong format"


let destruct_rule (term : NT.nuprl_term) : rule =
  match term with
  | NT.TERM ((("RULE",_,_),[(stamp,"o");(name,"t")]),[NT.B_TERM([],rt)]) -> (* the stamp *)
    (
      match NT.rterm2term rt with
      | NT.TERM ((("source",_,_),_),[NT.B_TERM([],rt)]) -> destruct_rule_rule stamp (NT.rterm2term rt)
      | t -> destruct_rule_rule stamp t
    )

  | NT.TERM (((stamp,_,_),[]),[NT.B_TERM([],rt)]) -> (* the stamp *)
    (
      match NT.rterm2term rt with
      | NT.TERM ((("source",_,_),_),[NT.B_TERM([],rt)]) -> destruct_rule_rule stamp (NT.rterm2term rt)
      | t -> destruct_rule_rule stamp t
    )

  | _ -> failwith "cannot destruct rule: wrong format"

let rec destruct_rules_bs (bterms : NT.nuprl_bound_term list) : rule list =
  match bterms with
  | [] -> []
  | (NT.B_TERM([],rt)) :: bterms ->
    destruct_rule (NT.rterm2term rt)
    :: destruct_rules_bs bterms
  | _ -> failwith "cannot destruct rule: wrong format"

let destruct_rules (terms : NT.nuprl_term list) : rule list =
  List.map destruct_rule terms

type goal =
  { sequent : NT.nuprl_term
  ; stamp : string
  ; parameters : NT.nuprl_term list
  }

type inf_tree = INF_NODE of goal * inf_tree list

let inf_tree2goal (tree : inf_tree) : goal =
  match tree with
  | INF_NODE (goal,_) -> goal

let rec rule_arg_cons_to_list (term : NT.nuprl_term) : NT.nuprl_term list =
  match term with
  | NT.TERM((("!rule_arg_cons",_,_),[]),[NT.B_TERM([],rt1);NT.B_TERM([],rt2)]) ->
    NT.rterm2term rt1 :: rule_arg_cons_to_list (NT.rterm2term rt2)
  | NT.TERM((("!rule_arg_cons",_,_),[]),[]) -> []
  | _ -> failwith "rule_arg_cons_to_list: wrong format"

let rec inf_tree_cons_to_list (term : NT.nuprl_term) : NT.nuprl_term list =
  match term with
  | NT.TERM((("!inf_tree_cons",_,_),[]),[NT.B_TERM([],rt1);NT.B_TERM([],rt2)]) ->
    NT.rterm2term rt1 :: inf_tree_cons_to_list (NT.rterm2term rt2)
  | NT.TERM((("!inf_tree_cons",_,_),[]),[]) -> []
  | _ -> failwith "inf_tree_cons_to_list: wrong format"

let dest_goal (term : NT.nuprl_term) : NT.nuprl_term =
  match term with
  | NT.TERM ((("!inf_goal",_,_),[]),[NT.B_TERM([],rtgoal);_]) -> NT.rterm2term rtgoal

  | _ -> failwith "dest_goal:wrong_format"

let rec destruct_inf_tree (term : NT.nuprl_term) : inf_tree =
  match term with
  | NT.TERM ((("!inf_tree",_,_),[]),[ NT.B_TERM([],rtgoal)
				    ; NT.B_TERM([],rtruleinst)
				    ; NT.B_TERM([],rtsubgoals)
				    ; NT.B_TERM([],rtannotations)
	    ]) ->
     let goal = dest_goal (NT.rterm2term rtgoal) in
     let ruleinst = NT.rterm2term rtruleinst in
     let subgoals = NT.rterm2term rtsubgoals in

     destruct_inf_tree_aux term goal ruleinst subgoals
                          
  | NT.TERM ((("!inf_tree",_,_),[]),[ NT.B_TERM([],rtgoal)
				    ; NT.B_TERM([],rtruleinst)
				    ; NT.B_TERM([],rtsubgoals)
	    ]) ->
     let goal = dest_goal (NT.rterm2term rtgoal) in
     let ruleinst = NT.rterm2term rtruleinst in
     let subgoals = NT.rterm2term rtsubgoals in
     
     (*let _ = print_string (NT.opid_of_term ruleinst ^ "-\n") in*)
     destruct_inf_tree_aux term goal ruleinst subgoals

  | _ ->
     let _ = print_string (NT.toStringTerm term ^ "\n") in
     failwith "destruct_inf_tree:cannot destruct inf_tree: wrong format"

and destruct_inf_tree_aux infTree goal ruleinst subgoals =
  (
    match ruleinst with
    | NT.TERM((("!inf_primitive_actual",_,_),[]),[NT.B_TERM([],rt)]) ->
       (
	 match NT.rterm2term rt with
	 | NT.TERM((("!rule_instance",_,_),[(stamp,_)]),[NT.B_TERM([],rtparams)]) ->
	    INF_NODE ({ sequent = goal
		      ; stamp = stamp
		      ; parameters = rule_arg_cons_to_list (NT.rterm2term rtparams)
		      },
		      List.map destruct_inf_tree (inf_tree_cons_to_list subgoals))
	 | _ ->
	    let _ = print_string (NT.toStringTerm ruleinst ^ "\n") in
	    failwith "destruct_inf_tree_aux:cannot destruct rule_instance: wrong format"
       )

    | NT.TERM((("!inf_primitive_actual",_,_),_),_) ->
       (*let _ = print_string (NT.toStringTerm ruleinst ^ "\n") in*)
       failwith "destruct_inf_tree_aux:cannot destruct inf_primitive_instance: different format"

    | _ ->
       (*let _ = print_string (NT.toStringTerm infTree ^ "\n") in*)
       let _ = print_string (NT.opid_of_term ruleinst ^ "\n") in
       let _ = print_string (NT.toStringOperatorPos (NT.operator_of_term infTree) ^ "\n") in
       failwith "destruct_inf_tree_aux:cannot destruct inf_primitive_instance: wrong format"
  )

type b_signature = string * int

type signature = b_signature list

let b_signature2string (b : b_signature) : string =
  match b with
  | (s, n) -> "(nvar \"" ^ s ^ "\"," ^ string_of_int n ^ ")"

let b_signature_nat2string (b : b_signature) : string =
  match b with
  | (s, n) -> string_of_int n

let bound_term2signature b : b_signature =
  match b with
  | NT.B_TERM (vs, t) ->
     (NT.dest_variable 0 (NT.rterm2term t), List.length vs)

let rec bound_terms2signature bs : signature =
  match bs with
  | [] -> []
  | b :: bs -> bound_term2signature b :: bound_terms2signature bs

let rec list2string_aux (sep : string) (f : 'a -> string) (l : 'a list) : string =
  match l with
  | [] -> ""
  | [x] -> f x
  | x :: xs -> f x ^ sep ^ list2string_aux sep f xs

let list2string (b : string) (e : string) (sep : string) (f : 'a -> string) (l : 'a list) : string =
  b ^ list2string_aux sep f l ^ e

let signature_nat2string (sign : signature) = list2string "[" "]" "," b_signature_nat2string sign

let signature2string (sign : signature) = list2string "[" "]" "," b_signature2string sign

let operator2string (op : NT.operator) (bs : NT.nuprl_bound_term list) : string =
  match op with
  | ((opid,tag,pos),params) ->
     let strparams = "[]" in
     let sign = List.map (fun b -> match b with | NT.B_TERM (vs,t) -> List.length vs) bs in
     let strsign = list2string "[" "]" "," string_of_int sign in
     "(Build_opabs \"" ^ opid ^ "\" " ^ strparams ^ " " ^ strsign ^ ")"

let operator2opid (opr : NT.operator) : NT.opid =
  match opr with
  | ((opid,tag,pos),params) -> opid

let rec nuprl_term2so (abs_names : string list) (t : NT.nuprl_term) : string =
  match t with
  | NT.TERM ((("isect",tag,pos), params), [NT.B_TERM ([], rt1); NT.B_TERM ([v], rt2)]) ->
     let t1 = NT.rterm2term rt1 in
     let t2 = NT.rterm2term rt2 in
     "(mk_so_isect " ^ nuprl_term2so abs_names t1 ^ " (nvar \"" ^ v ^ "\") " ^ nuprl_term2so abs_names t2 ^ ")"

  | NT.TERM ((("function",tag,pos), params), [NT.B_TERM ([], rt1); NT.B_TERM ([v], rt2)]) ->
     let t1 = NT.rterm2term rt1 in
     let t2 = NT.rterm2term rt2 in
     "(mk_so_function " ^ nuprl_term2so abs_names t1 ^ " (nvar \"" ^ v ^ "\") " ^ nuprl_term2so abs_names t2 ^ ")"

  | NT.TERM ((("lambda",tag,pos), params), [NT.B_TERM ([v1], rt1)]) ->
     let t1 = NT.rterm2term rt1 in
     "(mk_so_lambda " ^ " (nvar \"" ^ v1 ^ "\") " ^ nuprl_term2so abs_names t1 ^ ")"

  | NT.TERM ((("variable",tag,pos), params), bs) ->
     let (var,ts) = NT.dest_so_variable t in
     let str_ts   = list2string "[" "]" "," (nuprl_term2so abs_names) ts in
     "(sovar (nvar \"" ^ var ^ "\") " ^  str_ts ^ ")"

  (* TODO: do something sensible for universe levels *)
  | NT.TERM ((("universe",tag,pos), params), bs) ->
     "(mk_so_uni " ^ string_of_int 0 ^ ")"
    
  | NT.TERM ((("equal",tag,pos), params), [NT.B_TERM ([], rt1); NT.B_TERM ([], rt2); NT.B_TERM ([], rt3)]) ->
     let t1 = NT.rterm2term rt1 in
     let t2 = NT.rterm2term rt2 in
     let t3 = NT.rterm2term rt3 in
     "(mk_so_equality " ^ nuprl_term2so abs_names t2 ^ " " ^ nuprl_term2so abs_names t3 ^ " " ^ nuprl_term2so abs_names t1 ^ ")"

  | NT.LAM_TERM (v1, rt1) ->
     let t1 = NT.rterm2term rt1 in
     "(mk_so_lambda " ^ " (nvar \"" ^ v1 ^ "\") " ^ nuprl_term2so abs_names t1 ^ ")"

  | NT.APP_TERM (rt1, rt2) ->
     let t1 = NT.rterm2term rt1 in
     let t2 = NT.rterm2term rt2 in
     "(mk_so_apply " ^ nuprl_term2so abs_names t1 ^ " " ^ nuprl_term2so abs_names t2 ^ ")"

  | NT.VAR_TERM var ->
     "(sovar (nvar \"" ^ var ^ "\") [])"

  | NT.NAT_TERM n ->
     "(mk_so_nat " ^ NT.nuprl_nat_to_string n ^ ")"

  | NT.INT_TERM ->
     "(mk_so_int)"

  | NT.TERM (op, bs) ->
     if List.exists (fun name -> name = operator2opid op) abs_names
     then (* the term is an abstraction *)
       let opabs = operator2string op bs in
       let strbs = list2string "[" "]" "," (nuprl_bound_term2so abs_names) bs in	    
       "(mk_so_abs " ^ opabs ^ " " ^ strbs ^ " )"
     else (* the term is not an abstracton *)
       failwith ("nuprl_term2so:TERM(" ^ NT.toStringTerm t ^ ")")

  | _ -> failwith ("nurpl_term2so:non_supported_term(" ^ NT.toStringTerm t ^ ")")

and nuprl_bound_term2so (abs_names : string list) (b : NT.nuprl_bound_term) : string =
  match b with
  | NT.B_TERM (vs,rt) ->
     let strvs = list2string "[" "]" "," (fun x -> "nvar \"" ^ x ^ "\"") vs in
     "(sobterm " ^ strvs ^ " " ^ nuprl_term2so abs_names (NT.rterm2term rt) ^ ")"

let rec nuprl_term2fo (abs_names : string list) (t : NT.nuprl_term) : string =
  match t with
  | NT.TERM ((("isect",tag,pos), params), [NT.B_TERM ([], rt1); NT.B_TERM ([v], rt2)]) ->
     let t1 = NT.rterm2term rt1 in
     let t2 = NT.rterm2term rt2 in
     "(mk_isect " ^ nuprl_term2fo abs_names t1 ^ " (nvar \"" ^ v ^ "\") " ^ nuprl_term2fo abs_names t2 ^ ")"

  | NT.TERM ((("function",tag,pos), params), [NT.B_TERM ([], rt1); NT.B_TERM ([v], rt2)]) ->
     let t1 = NT.rterm2term rt1 in
     let t2 = NT.rterm2term rt2 in
     "(mk_function " ^ nuprl_term2fo abs_names t1 ^ " (nvar \"" ^ v ^ "\") " ^ nuprl_term2fo abs_names t2 ^ ")"

  | NT.TERM ((("variable",tag,pos), [(var,"v")]), []) ->
     "(mk_var (nvar \"" ^ var ^ "\"))"

  (* TODO: Do something sensible for universe levels! *)
  | NT.TERM ((("universe",tag,pos), params), bs) ->
     "(mk_uni " ^ string_of_int 0 ^ ")"
    
  | NT.TERM ((("equal",tag,pos), params), [NT.B_TERM ([], rt1); NT.B_TERM ([], rt2); NT.B_TERM ([], rt3)]) ->
     let t1 = NT.rterm2term rt1 in
     let t2 = NT.rterm2term rt2 in
     let t3 = NT.rterm2term rt3 in
     "(mk_equality " ^ nuprl_term2fo abs_names t2 ^ " " ^ nuprl_term2fo abs_names t3 ^ " " ^ nuprl_term2fo abs_names t1 ^ ")"
    
  | NT.TERM ((("sqequal",tag,pos), params), [NT.B_TERM ([], rt1); NT.B_TERM ([], rt2)]) ->
     let t1 = NT.rterm2term rt1 in
     let t2 = NT.rterm2term rt2 in
     "(mk_cequiv " ^ nuprl_term2fo abs_names t1 ^ " " ^ nuprl_term2fo abs_names t2 ^ ")"

  | NT.APP_TERM (rt1, rt2) ->
     let t1 = NT.rterm2term rt1 in
     let t2 = NT.rterm2term rt2 in
     "(mk_apply " ^ nuprl_term2fo abs_names t1 ^ " " ^ nuprl_term2fo abs_names t2 ^ ")"

  | NT.VAR_TERM var ->
     "(mk_var (nvar \"" ^ var ^ "\"))"

  | NT.AXM_TERM -> "(mk_axiom)"

  | NT.TERM (op, bs) ->
     if List.exists (fun name -> name = operator2opid op) abs_names
     then (* the term is an abstraction *)
       let opabs = operator2string op bs in
       let strbs = list2string "[" "]" "," (nuprl_bound_term2fo abs_names) bs in	    
       "(mk_abs " ^ opabs ^ " " ^ strbs ^ " )"
     else (* the term is not an abstracton *)
       failwith ("nuprl_term2fo:TERM(" ^ NT.toStringTerm t ^ ")")

  | _ -> failwith ("nurpl_term2fo:non_supported_term(" ^ NT.toStringTerm t ^ ")")

and nuprl_bound_term2fo (abs_names : string list) (b : NT.nuprl_bound_term) : string =
  match b with
  | NT.B_TERM (vs,rt) ->
     let strvs = list2string "[" "]" "," (fun x -> "nvar \"" ^ x ^ "\"") vs in
     "(bterm " ^ strvs ^ " " ^ nuprl_term2fo abs_names (NT.rterm2term rt) ^ ")"

let print_abstraction (abs_names : string list) (abs : abstraction) out =
  match abs with
  | {stamp;lhs;rhs} ->
     match lhs with
     | NT.TERM (opr,bs) ->
	let sign          = bound_terms2signature bs in
	let str_nat_sign  = signature_nat2string sign in
	let str_name_sign = signature2string sign in
	let name          = get_abstraction_name abs in
	let str_params    = "[]" in
	let str_soterm    = nuprl_term2so abs_names rhs in

	output_string out ("    COM_add_def\n");
	output_string out ("      (Build_opabs \"" ^ name ^ "\" " ^ str_params ^ " " ^ str_nat_sign ^ ")\n");
	output_string out ("      " ^ str_name_sign ^ "\n");
	output_string out ("      " ^ str_soterm ^ "\n");
	output_string out ("      " ^ "(eq_refl, (eq_refl, (eq_refl, (eq_refl, eq_refl))))");

(*	print_string "****************\n";
	print_terms [lhs];
	print_string "-----------------\n";
	print_terms [rhs];
	print_string "****************\n";*)
	()

     | _ -> failwith "print_abstraction:NOT_TERM"

let rec print_abstractions_aux (abs_names : string list) (abstractions : abstraction list) out =
  match abstractions with
  | [] -> ()
  | [abs] ->
     print_abstraction abs_names abs out;
     output_string out ("\n")
  | abs :: rest ->
     print_abstraction abs_names abs out;
     output_string out (",\n");
     print_abstractions_aux (get_abstraction_name abs :: abs_names) rest out

let print_abstractions cmdabs abstractions out =
  output_string out ("Definition " ^ cmdabs ^ " {o} : @commands o :=\n");
  output_string out ("  [\n");
  print_abstractions_aux [] abstractions out;
  output_string out ("  ].\n")

let start_proof lemma_name abs_names inf_tree out =
  match inf_tree with
  | INF_NODE ({sequent;stamp;parameters}, subgoals) ->
     let str_seq = nuprl_term2fo abs_names sequent in
     output_string out ("    COM_start_proof\n");
     output_string out ("      \"" ^ lemma_name ^ "\"\n");
     output_string out ("      " ^ str_seq ^ "\n");
     output_string out ("      " ^ "(eq_refl, eq_refl),\n")

let rec find_rule (stmp : string) (rules : rule list) : rule =
  match rules with
  | [] -> failwith ("find_rule:couldn't find " ^ stmp)
  | ({stamp;goal;name;subgoals} as rule) :: rules ->
     if stamp = stmp then rule
     else find_rule stmp rules

let pos2string (pos : int list) : string = list2string "[" "]" "," string_of_int pos

let rec opid_append (l1 : NT.opid list) (l2 : NT.opid list) : NT.opid list =
  match l1 with
  | [] -> l2
  | x :: xs ->
     let l = opid_append xs l2 in
     if List.exists (fun n -> n = x) l then l
     else x :: l

let rec find_tagged_names_in_term (t : NT.nuprl_term) : NT.opid list =
  match t with
  | NT.TERM ((("tag",tag,pos),params),[NT.B_TERM ([], rt)]) ->
     let u = NT.rterm2term rt in
     let l = find_tagged_names_in_term u in
     let name = NT.opid_of_term u in
     if List.exists (fun n -> n = name) l then l
     else name :: l

  | NT.TERM (((opid,tag,pos),params),bs) ->
     List.fold_left (fun a b -> opid_append a (find_tagged_names_in_bterm b)) [] bs

  | NT.VAR_TERM _ -> []

  | NT.APP_TERM (t1,t2) ->
     opid_append
       (find_tagged_names_in_term (NT.rterm2term t1))
       (find_tagged_names_in_term (NT.rterm2term t2))

  | NT.AXM_TERM -> []

  | _ -> failwith ("find_tagged_names_in_term:non_supported_term(" ^ NT.toStringTerm t ^ ")")
     
and find_tagged_names_in_bterm (b : NT.nuprl_bound_term) : NT.opid list =
  match b with
  | NT.B_TERM (vs, rt) -> find_tagged_names_in_term (NT.rterm2term rt)

let find_tagged_names_in_terms (l : NT.nuprl_term list) : NT.opid list =
  match l with
  | [t] -> find_tagged_names_in_term t
  | _ -> failwith ("find_tagged_names_in_terms:more than 1 term or none")

let rec get_assumption_index (t : NT.nuprl_term) : string =
  match t with
  | NT.TERM ((("assumption-index",tag,pos),[(n,"n")]),[]) -> n
  | _ -> failwith ("get_assumption_index:wrong kind of term")

let dest_function_term (t : NT.nuprl_term) : NT.nuprl_term * NT.variable * NT.nuprl_term =
  match t with
  | NT.TERM ((("function",tag,pos), params),
	  [NT.B_TERM ([],  term1);
	   NT.B_TERM ([v], term2)]) -> (NT.rterm2term term1, v, NT.rterm2term term2)
  | _ -> failwith "dest_function_term"

let rec remove_tags (t : NT.nuprl_term) : NT.nuprl_term =
  match t with
  | NT.TERM ((("tag",tag,pos), params), [NT.B_TERM ([], rt)]) -> remove_tags (NT.rterm2term rt)

  | NT.TERM ((("isect",tag,pos), params), [NT.B_TERM ([], rt1); NT.B_TERM ([v], rt2)]) ->
     let t1 = NT.mk_rterm (remove_tags (NT.rterm2term rt1)) in
     let t2 = NT.mk_rterm (remove_tags (NT.rterm2term rt2)) in
     NT.TERM ((("isect",tag,pos), params), [NT.B_TERM ([], t1); NT.B_TERM ([v], t2)])

  | NT.TERM ((("function",tag,pos), params), [NT.B_TERM ([], rt1); NT.B_TERM ([v], rt2)]) ->
     let t1 = NT.mk_rterm (remove_tags (NT.rterm2term rt1)) in
     let t2 = NT.mk_rterm (remove_tags (NT.rterm2term rt2)) in
     NT.TERM ((("function",tag,pos), params), [NT.B_TERM ([], t1); NT.B_TERM ([v], t2)])

  | NT.TERM ((("variable",tag,pos), [(var,"v")]), []) -> t

  | NT.TERM ((("universe",tag,pos), params), bs) -> t
    
  | NT.TERM ((("equal",tag,pos), params), [NT.B_TERM ([], rt1); NT.B_TERM ([], rt2); NT.B_TERM ([], rt3)]) ->
     let t1 = NT.mk_rterm (remove_tags (NT.rterm2term rt1)) in
     let t2 = NT.mk_rterm (remove_tags (NT.rterm2term rt2)) in
     let t3 = NT.mk_rterm (remove_tags (NT.rterm2term rt3)) in
     NT.TERM ((("equal",tag,pos), params), [NT.B_TERM ([], t1); NT.B_TERM ([], t2); NT.B_TERM ([], t3)])

  | NT.APP_TERM (rt1, rt2) ->
     let t1 = NT.mk_rterm (remove_tags (NT.rterm2term rt1)) in
     let t2 = NT.mk_rterm (remove_tags (NT.rterm2term rt2)) in
     NT.APP_TERM (t1, t2)

  | NT.VAR_TERM var -> t

  | NT.AXM_TERM -> t

  | NT.TERM (op, bs) -> NT.TERM (op, List.map remove_tags_b bs)

  | _ -> failwith ("remove_tags:non_supported_term(" ^ NT.toStringTerm t ^ ")")

and remove_tags_b (b : NT.nuprl_bound_term) : NT.nuprl_bound_term =
  match b with
  | NT.B_TERM (vs, rt) -> NT.B_TERM (vs, NT.mk_rterm (remove_tags (NT.rterm2term rt)))

let dest_cequiv (t : NT.nuprl_term) : NT.nuprl_term * NT.nuprl_term =
  match t with
  | NT.TERM ((("sqequal",_,_), _), [NT.B_TERM ([],rt1); NT.B_TERM ([], rt2)]) -> (NT.rterm2term rt1, NT.rterm2term rt2)
  | _ -> failwith ("dest_cequiv:" ^ NT.opid_of_term t)

let dest_bound_id (t : NT.nuprl_term) : NT.variable * NT.nuprl_term =
  match t with
  | NT.TERM ((("!bound_id",_,_), _), [NT.B_TERM ([v],rt1)]) -> (v, NT.rterm2term rt1)
  | _ -> failwith ("dest_bound_id:" ^ NT.opid_of_term t)

let rec abstractions_append (l1 : abstraction list) (l2 : abstraction list) : abstraction list =
  match l1 with
  | [] -> l2
  | x :: xs ->
     let l = abstractions_append xs l2 in
     if List.exists (fun n -> get_abstraction_name n = get_abstraction_name x) l then l
     else x :: l

let rec find_abstraction (abs : abstraction list) (op : NT.opid) : abstraction option =
  match abs with
  | [] -> None
  | x :: xs ->
     if op = get_abstraction_name x then Some x
     else find_abstraction xs op

let rec check_whether_unfoldable
      (abs : abstraction list)
      (a   : NT.nuprl_term)
      (b   : NT.nuprl_term) : (NT.opid list) option =
  match a, b with
  | NT.TERM (((op1,_,_),ps1),bs1), NT.TERM (((op2,_,_),ps2),bs2) ->
     (
       if op1 = op2 && ps1 = ps2 then
         (
           if List.length bs1 = List.length bs2 then
             check_whether_unfoldable_bs abs bs1 bs2
           else
             (
               print_endline ("WARNING: lists of subterms have different lengths");
               None
             )
         )
       else
         let op = NT.opid_of_term a in
         match find_abstraction abs op with
         | Some abs ->
            (
              try
                (
                  let u = NT.unfold_ab None a abs.lhs abs.rhs in
                  if NT.alpha_equal_terms u b then Some [op]
                  else
                    (
                      print_terms [a;u;b];
                      print_endline ("WARNING: left-hand-side does not unfold to right-hand-side");
                      None
                    )
                )
              with
                _ ->
                print_endline ("WARNING: unfolding failed");
                None
            )
         | None ->
            print_endline ("WARNING: opids don't match and couldn't find an abstraction to unfold left-hand-side");
            None
     )

  | NT.VAR_TERM v1, NT.VAR_TERM v2 ->
     if v1 = v2 then Some []
     else
       (
         print_terms [a;b];
         print_endline ("WARNING: variables don't match");
         None
       )

  | NT.AXM_TERM, NT.AXM_TERM -> Some []

  | _, _ ->
     print_terms [a;b];
     print_endline ("WARNING: wrong kinds of terms");
     None

and check_whether_unfoldable_bs
      (abs : abstraction list)
      (bs1 : NT.nuprl_bound_term list)
      (bs2 : NT.nuprl_bound_term list) : (NT.opid list) option =
  match bs1, bs2 with
  | [], [] -> Some []
  | NT.B_TERM(l1,rt1) :: bs1, NT.B_TERM(l2,rt2) :: bs2 ->
     (
       if l1 = l2 then

         (
           let t1 = NT.rterm2term rt1 in
           let t2 = NT.rterm2term rt2 in
           match check_whether_unfoldable abs t1 t2, check_whether_unfoldable_bs abs bs1 bs2 with
           | Some a, Some b -> Some (opid_append a b)
           | _, _ -> None
         )

       else None
     )
  | _, _ -> None

let rec dest_cequiv_in_concl_seq (t : NT.nuprl_term) : NT.nuprl_term * NT.nuprl_term =
  match t with
  | NT.TERM ((("!inf_sequent",_,_), _), [NT.B_TERM ([],rt1); NT.B_TERM ([v], rt2)]) ->

     dest_cequiv_in_concl_seq (NT.rterm2term rt2)

  | NT.TERM ((("sqequal",_,_), _), [NT.B_TERM ([],rt1); NT.B_TERM ([], rt2)]) ->

     (NT.rterm2term rt1, NT.rterm2term rt2)

  | _ -> failwith ("dest_cequiv:" ^ NT.opid_of_term t)

let rec print_proof_tree lemma_name abs abs_names inf_tree rules out pos =
  match inf_tree with
  | INF_NODE ({sequent;stamp;parameters}, subgoals) ->

     match find_rule stamp rules with

     (* TODO: We get the tagged abstractions and we unfold those.  This is not always going to be enough though
          because sometimes the tagged terms are to beta-reduce *)
     | {stamp = _; goal = _; name = "direct_computation"; subgoals = _} ->

	let strpos = pos2string pos in
        let names = find_tagged_names_in_terms parameters in
        let str_names  = list2string "[" "]" ","  (fun s -> "\"" ^ s ^ "\"") names in 

	output_string out ("    COM_update_proof\n");
	output_string out ("      \"" ^ lemma_name ^ "\"\n");
	output_string out ("      " ^ strpos ^ "\n");
	output_string out ("      " ^ "(proof_step_unfold_abstractions " ^ str_names ^ "),\n");

        List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

     | {stamp = _; goal = _; name = "reverse_direct_computation"; subgoals = _} ->

        (
          match parameters with
          | [t] ->

	     let strpos = pos2string pos in
             let names = find_tagged_names_in_terms parameters in
             let str_names  = list2string "[" "]" ","  (fun s -> "\"" ^ s ^ "\"") names in 
             let stt = nuprl_term2fo abs_names (remove_tags t) in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_rev_unfold_abstractions " ^ str_names ^ " " ^ stt ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:reverse_direct_computation:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "isect_memberFormation"; subgoals = _} ->

        (
          match parameters with
          | [i;v] ->

             (* TODO: Do something sensible with levels (i) *)

	     let strpos = pos2string pos in
             let lvl = 0 in
             let vn = NT.dest_variable 0 v in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_isect_member_formation (nvar \"" ^ vn ^ "\") " ^ string_of_int lvl ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:isect_memberFormation:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "introduction"; subgoals = _} ->

        (
          match parameters with
          | [t] ->

	     let strpos = pos2string pos in
             let stt = nuprl_term2fo abs_names t in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_introduction " ^ stt ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:introduction:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "cut"; subgoals = _} ->

        (
          match parameters with
          | [_;t;v] ->

	     let strpos = pos2string pos in
             let stt = nuprl_term2fo abs_names t in
             let vn = NT.dest_variable 0 v in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_cut (nvar \"" ^ vn ^ "\")" ^ " " ^ stt ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:cut:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "isectEquality"; subgoals = _} ->

        (
          match parameters with
          | [v] ->

	     let strpos = pos2string pos in
             let vn = NT.dest_variable 0 v in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_isect_equality (nvar \"" ^ vn ^ "\")),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:isectEquality:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "hypothesisEquality"; subgoals = _} ->

	let strpos = pos2string pos in

	output_string out ("    COM_update_proof\n");
	output_string out ("      \"" ^ lemma_name ^ "\"\n");
	output_string out ("      " ^ strpos ^ "\n");
	output_string out ("      " ^ "proof_step_maybe_hidden_hypothesis_equality,\n");

        List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

     | {stamp = _; goal = _; name = "axiomEquality"; subgoals = _} ->

	let strpos = pos2string pos in

	output_string out ("    COM_update_proof\n");
	output_string out ("      \"" ^ lemma_name ^ "\"\n");
	output_string out ("      " ^ strpos ^ "\n");
	output_string out ("      " ^ "proof_step_axiom_equality,\n");

        List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

     | {stamp = _; goal = _; name = "thin"; subgoals = _} ->

        (
          match parameters with
          | [n] ->

	     let strpos = pos2string pos in
             let sn = get_assumption_index n in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_thin_num " ^ sn ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:thin:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "functionEquality"; subgoals = _} ->

        (
          match parameters with
          | [v] ->

	     let strpos = pos2string pos in
             let vn = NT.dest_variable 0 v in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_function_equality (nvar \"" ^ vn ^ "\")),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:functionEquality:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "applyEquality"; subgoals = _} ->

        (
          match parameters with
          | [arg] ->

	     let strpos = pos2string pos in
             let (a,v,b) = dest_function_term arg in
             let tA = nuprl_term2fo abs_names a in
             let tB = nuprl_term2fo abs_names b in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_apply_equality (nvar \"" ^ v ^ "\") " ^ tA ^ " " ^ tB ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:applyEquality:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "isectElimination"; subgoals = _} ->

        (
          match parameters with
          | [n;a;v;w] ->

	     let strpos = pos2string pos in
             let sn = get_assumption_index n in
             let tA = nuprl_term2fo abs_names a in
             let vn = NT.dest_variable 0 v in
             let wn = NT.dest_variable 0 w in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_isect_elimination2 " ^ sn ^ " " ^ tA ^ " (nvar \"" ^ vn ^ "\") (nvar \"" ^ wn ^ "\")),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:isectElimination:wrong number of parameters")
        )

     (* TODO: do something sensible for universe levels: *)
     | {stamp = _; goal = _; name = "isect_memberEquality"; subgoals = _} ->

        (
          match parameters with
          | [i;v] ->

	     let strpos = pos2string pos in
             let lvl = 0 in
             let vn = NT.dest_variable 0 v in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_isect_member_equality (nvar \"" ^ vn ^ "\") " ^ string_of_int lvl ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:isect_memberEquality:wrong number of parameters")
        )

     (* TODO: do something sensible for universe levels: *)
     | {stamp = _; goal = _; name = "cumulativity"; subgoals = _} ->

        (
          match parameters with
          | [i] ->

	     let strpos = pos2string pos in
             let lvl = 0 in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_cumulativity " ^ string_of_int lvl ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:cumulativity:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "universeEquality"; subgoals = _} ->

        (
          match parameters with
          | [] ->

	     let strpos = pos2string pos in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_universe_equality),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:universeEquality:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "equalitySymmetry"; subgoals = _} ->

        (
          match parameters with
          | [] ->

	     let strpos = pos2string pos in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_equality_symmetry),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:equalitySymmetry:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "equalityTransitivity"; subgoals = _} ->

        (
          match parameters with
          | [t] ->

	     let strpos = pos2string pos in
             let stt = nuprl_term2fo abs_names t in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_equality_transitivity " ^ stt ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:equalityTransitivity:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "sqequalReflexivity"; subgoals = _} ->

        (
          match parameters with
          | [] ->

	     let strpos = pos2string pos in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_cequiv_refl),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:sqequalReflexivity:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "sqequalTransitivity"; subgoals = _} ->

        (
          match parameters with
          | [t] ->

	     let strpos = pos2string pos in
             let stt = nuprl_term2fo abs_names t in

	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_cequiv_transitivity " ^ stt ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:sqequalTransitivity:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "sqequalSubstitution"; subgoals = _} ->

        (
          match parameters with
          | [ceq;xt] ->

	     let strpos = pos2string pos in
             let (a,b) = dest_cequiv ceq in
             let (nv,t) = dest_bound_id xt in
             let stt = nuprl_term2fo abs_names t in
             let sta = nuprl_term2fo abs_names a in
             let stb = nuprl_term2fo abs_names b in
 
	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_cequiv_subst_concl (nvar \"" ^ nv ^ "\") " ^ stt ^ " " ^ sta ^ " " ^ stb ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:sqequalSubstitution:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "hypothesis"; subgoals = _} ->

        (
          match parameters with
          | [n] ->

	     let strpos = pos2string pos in
             let sn = get_assumption_index n in
 
	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_hypothesis_num " ^ sn ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:hypothesis:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "computationStep"; subgoals = _} ->

        (
          match parameters with
          | [] ->

	     let strpos = pos2string pos in
 
	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_cequiv_computation_aeq " ^ string_of_int 1 ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:computationStep:wrong number of parameters")
        )

     | {stamp = _; goal = _; name = "sqequalHypSubstitution"; subgoals = _} ->

        (
          match parameters with
          | [n;ceq;xt] ->

	     let strpos = pos2string pos in
             let (a,b) = dest_cequiv ceq in
             let (nv,t) = dest_bound_id xt in
             let stt = nuprl_term2fo abs_names t in
             let sta = nuprl_term2fo abs_names a in
             let stb = nuprl_term2fo abs_names b in
             let sn = get_assumption_index n in
 
	     output_string out ("    COM_update_proof\n");
	     output_string out ("      \"" ^ lemma_name ^ "\"\n");
	     output_string out ("      " ^ strpos ^ "\n");
	     output_string out ("      " ^ "(proof_step_cequiv_subst_hyp_num " ^ sn ^ " (nvar \"" ^ nv ^ "\") " ^ stt ^ " " ^ sta ^ " " ^ stb ^ "),\n");

             List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals

          | _ -> failwith ("print_proof_tree:sqequalHypSubstitution:wrong number of parameters")
        )

     (* TODO: This is just a temporary hack.
          We check whether the lhs unfolds to the rhs.
          We eventually have to prove the sqequal rule.
      *)
     | {stamp = _; goal = _; name = "sqequal"; subgoals = _} ->

        (*print_string (NT.toStringTerm sequent ^ "\n");
        print_string ("--------\n");
        (*List.iter (fun t -> print_string (NT.toStringTerm ((inf_tree2goal t).sequent) ^ "\n--------\n")) subgoals;*)
        print_string "----missing *sqequal*\n"(*;
        List.iteri (fun i sg -> print_proof_tree lemma_name abs_names sg rules out (List.append pos [i + 1])) subgoals*)*)

        (
          match parameters with
          | [] ->

	     let strpos = pos2string pos in
	     let next_strpos = pos2string (List.append pos [1]) in
             let (a,b) = dest_cequiv_in_concl_seq sequent in

             (
               match check_whether_unfoldable abs a b with
               | Some names ->
                  let str_names  = list2string "[" "]" ","  (fun s -> "\"" ^ s ^ "\"") names in 

	          output_string out ("    COM_update_proof\n");
	          output_string out ("      \"" ^ lemma_name ^ "\"\n");
	          output_string out ("      " ^ strpos ^ "\n");
	          output_string out ("      " ^ "(proof_step_unfold_abstractions " ^ str_names ^ "),\n");

	          output_string out ("    COM_update_proof\n");
	          output_string out ("      \"" ^ lemma_name ^ "\"\n");
	          output_string out ("      " ^ next_strpos ^ "\n");
	          output_string out ("      " ^ "(proof_step_cequiv_alpha_eq),\n")

               (*;List.iteri (fun i sg -> print_proof_tree lemma_name abs abs_names sg rules out (List.append pos [i + 1])) subgoals*)

               | _ -> failwith ("print_proof_tree:sqequal:could not unfold left-hand-side to right-hand-side of squiggle term")
             )

          | _ -> failwith ("print_proof_tree:sqequal:wrong number of parameters")
        )



(*     (* TODO: do something sensible for this one: *)
     | {stamp = _; goal = _; name = "direct_computation_hypothesis"; subgoals = _} ->
        print_string "----missing *direct_computation_hypothesis*\n";
        List.iteri (fun i sg -> print_proof_tree lemma_name abs_names sg rules out (List.append pos [i + 1])) subgoals

     (* TODO: do something sensible for this one: *)
     | {stamp = _; goal = _; name = "equality"; subgoals = _} ->
        print_string "----missing *equality*\n";
        List.iteri (fun i sg -> print_proof_tree lemma_name abs_names sg rules out (List.append pos [i + 1])) subgoals

     (* TODO: do something sensible for this one: *)
     | {stamp = _; goal = _; name = "equalityEquality"; subgoals = _} ->
        print_string "----missing *equalityEquality*\n";
        List.iteri (fun i sg -> print_proof_tree lemma_name abs_names sg rules out (List.append pos [i + 1])) subgoals

     (* TODO: do something sensible for this one: *)
     (* sucks! *)
     | {stamp = _; goal = _; name = "because_Cache"; subgoals = _} ->
        List.iteri (fun i sg -> print_proof_tree lemma_name abs_names sg rules out (List.append pos [i + 1])) subgoals*)

     | {stamp = stmp; goal = g; name = n; subgoals = subs} ->

	print_string "****************\n";
	print_terms parameters;
	print_string "****************\n";

	failwith ("print_proof_tree:unknown proof step (" ^ n ^ ")")

let finish_proof lemma_name out =
  output_string out ("    COM_finish_proof \"" ^ lemma_name ^ "\"\n")

let print_proof cmdprf lemma_name abs abs_names inf_tree rules out =
  output_string out ("Definition " ^ cmdprf ^ " {o} : @commands o :=\n");
  output_string out ("  [\n");
  start_proof lemma_name abs_names inf_tree out;
  print_proof_tree lemma_name abs abs_names inf_tree rules out [];
  finish_proof lemma_name out;
  (* TODO : finish printing the proof *)
  output_string out ("  ].\n")

let export_primitive_proof_to_coq
      (lemma_name : string)
      (output     : string)
      (abs        : abstraction list)
      (rules      : rule list)
      (inf_tree   : inf_tree) =
  let cmdabs = "abstractions" in
  let cmdprf = "proof" in
  let abs_names = get_abstraction_names abs in
  let out = open_out output in

  (* we print necessary exports *)
  let _ = output_string out ("Require Export proof_with_lib.\n") in
  let _ = output_string out ("\n\n") in

  (* we create the commands to add abstractions *)
  let _ = print_abstractions cmdabs abs out in

  let _ = print_string "[" in
  let _ = List.iter (fun s -> print_string ("-" ^ s)) abs_names in
  let _ = print_string "]\n" in
  let _ = print_endline ("[getting statements]") in
  let _ = print_endline ("[getting rules]") in
  let rule_names = get_rule_names rules in
  let _ = print_string "[" in
  let _ = List.iter (fun s -> print_string ("-" ^ s)) rule_names in
  let _ = print_string "]\n" in

  let _ = output_string out ("\n\n") in
  let _ = print_proof cmdprf lemma_name abs abs_names inf_tree rules out in

  (* TODO: print proof to coq output file *)

  let _ = output_string out ("\n\n") in
  let _ = output_string out ("Time Eval compute in (update_list_from_init (" ^ cmdabs ^ " ++ " ^ cmdprf ^ ")).\n") in

  (* NEXT: display the inference tree *)
  ()

let destruct_term term lemma_name output =
  match term with
  | NT.TERM (((opid,tag,pos),params),bs) ->
    let n = List.length bs in
    let _ = print_endline ("[number of subterms: " ^ string_of_int n ^ "]") in
    (
      match bs with
      | [ NT.B_TERM ([],rt1)
	; NT.B_TERM ([],rt2)
	; NT.B_TERM ([],rt3)
	; NT.B_TERM ([],rt4)
	] ->
	let t1 = NT.rterm2term rt1 in
	let t2 = NT.rterm2term rt2 in
	let t3 = NT.rterm2term rt3 in
	let t4 = NT.rterm2term rt4 in

        (
          match t1, t2, t3 with
          | NT.TERM (((("ABS",tag1,pos1)),params1),bs1)
          , NT.TERM (((("STM",tag2,pos2)),params2),bs2)
          , NT.TERM (((("RULE",tag3,pos3)),params3),bs3)
            -> let _ = print_endline ("[got the right kinds of subterms, i.e., first 3 are ABS, STM, RULE]") in
               let _ = print_endline ("[getting abstractions]") in

               let abs      = destruct_abstractions_bs bs1 in
               (*let stmts    = destruct_statements_bs bs2 in*)
               let rules    = destruct_rules_bs bs3 in
               let inf_tree = destruct_inf_tree t4 in

               (* we don't care about the statement because it's at the top of the tree *)

               export_primitive_proof_to_coq lemma_name output abs rules inf_tree

          | _ -> failwith "wrong kinds of subterms"
        )

      | _ -> failwith "wrong number of subterms, expecting 4"
    )
  | _ -> failwith "top term is not a generic term"

let rec list_opids (terms : NT.nuprl_term list) =
  match terms with
  | [] -> ()
  | t :: ts ->
     print_endline ("----" ^ NT.opid_of_term t);
     list_opids ts

let rec split_terms (ts : NT.nuprl_term list) : NT.nuprl_term list * NT.nuprl_term list * NT.nuprl_term list =
  match ts with
  | [] -> ([], [], [])
  | t :: ts ->
     let (abs,rules,stmts) = split_terms ts in
     let op = NT.opid_of_term t in
     if op = "ABS" then (t :: abs, rules, stmts)
     else if op = "RULE" then (abs, t :: rules, stmts)
     else if op = "STM" then (abs, rules, t :: stmts)
     else failwith ("split_terms:unexpected opid " ^ op)

let destruct_terms terms lemma_name output =
  match terms with
  | [term] -> destruct_term term lemma_name output
  | _ ->

     (
       let (abs_ts,rules_ts,stmts_ts) = split_terms terms in
       match stmts_ts with
       | [NT.TERM (((("STM",tag1,pos1)),params1),[NT.B_TERM([],source);NT.B_TERM([],proof)])] ->

          (
            match NT.rterm2term proof with
            | NT.TERM (((("proof",tag1,pos1)),params1),[NT.B_TERM([],rt_inf_tree)]) ->

               let abs      = destruct_abstractions abs_ts in
               let rules    = destruct_rules rules_ts in
               let inf_tree = destruct_inf_tree (NT.rterm2term rt_inf_tree) in

               export_primitive_proof_to_coq lemma_name output abs rules inf_tree

            | _ -> failwith ("destruct_terms:not a proof term")
          )

       | [NT.TERM (((("STM",_,_)),_),_)] -> failwith ("destruct_terms:wrong kind of STM term")

       | _ -> failwith ("destruct_terms:not a STM term")
     )

(*  |  _ -> 
      list_opids terms;
      failwith ("destruct_terms:trying to destruct more than one term(" ^ string_of_int (List.length terms) ^ ")")*)

let main =
  let _ =
    Arg.parse [("--i", Arg.Set_string ref_default_input, "");
	       ("--o", Arg.Set_string ref_default_output, "")]
      (fun str -> ())
      "EventML arguments" in
  let input  = !ref_default_input  in
  let output = !ref_default_output in
  let prt   = false in
  let split = false in
  let theories_out = [] in
  let _ = print_endline ("[parsing input file: " ^ input ^ "]") in
  let terms = PN.parse prt theories_out input split in
  let _ = print_endline ("[done parsing]") in
  let lemma_name = input in
  (*let _ = print_terms terms in*)
  let _ = destruct_terms terms lemma_name output in
  ()


(* ./parse --i uall_wf_primitive.term --o output.v *)
