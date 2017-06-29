(*#load "nums.cma";;
#load "str.cma";;*)

module type TOREF =
  sig
    type 'a t
    val get : 'a t -> 'a
    val mk  : 'a -> 'a t
    val set : 'a t -> 'a -> unit
  end

module ToRefRef : TOREF =
  struct
    type 'a t = 'a ref
    let get x = !x
    let mk x = ref x
    let set x y = (x := y)
  end

module ToRefId : TOREF =
  struct
    type 'a t = 'a
    let get x = x
    let mk x = x
    let set x y = ()
  end

module ToRefFun : TOREF =
  struct
    type 'a t = unit -> 'a
    let get x = x ()
    let mk x = fun () -> x
    let set x y = ()
  end

module SML_Option =
  struct
    let isSome opt =
      match opt with
	Some _ -> true
      | None   -> false

    let valOf opt =
      match opt with
	Some x -> x
      | None -> failwith "valOf"

    let map f opt =
      match opt with
	Some x -> Some (f x)
      | None -> None
  end

module type SML_LIST_PAIR =
  sig
    exception UnequalLengths
    val zip: 'a list * 'b list -> ('a * 'b) list 
    val zipEq: 'a list * 'b list -> ('a * 'b) list 
    val unzip: ('a * 'b) list -> 'a list * 'b list
    val app: ('a * 'b -> unit) -> 'a list * 'b list -> unit 
    val appEq: ('a * 'b -> unit) -> 'a list * 'b list -> unit 
    val map: ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list 
    val mapEq: ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list 
    val foldl: ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c 
    val foldr: ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c 
    val foldlEq: ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c 
    val foldrEq: ('a * 'b * 'c -> 'c) -> 'c -> 'a list * 'b list -> 'c 
    val all: ('a * 'b -> bool) -> 'a list * 'b list -> bool 
    val exists: ('a * 'b -> bool) -> 'a list * 'b list -> bool 
    val allEq: ('a * 'b -> bool) -> 'a list * 'b list -> bool 
  end

module SML_ListPair : SML_LIST_PAIR =
  struct
    exception UnequalLengths

    let id x = x

    let ul _ = raise UnequalLengths

    let unzip l =
      List.fold_right (fun (x, y) (xs, ys) -> (x :: xs, y :: ys)) l ([], [])

    let foldl' w f b (l1, l2) =
      let rec loop (l1, l2, b) =
        match (l1, l2) with
          ([], []) -> b
        | (x1 :: l1, x2 :: l2) -> loop (l1, l2, f (x1, x2, b))
        | _ -> w b
      in
      loop (l1, l2, b)

    let foldl f = foldl' id f

    let foldlEq f = foldl' ul f

    let foldr' w f b (l1, l2) =
      let rec loop (l1, l2) =
        match (l1, l2) with
          ([], []) -> b
        | (x1 :: l1, x2 :: l2) -> f (x1, x2, loop (l1, l2))
        | _ -> w b
      in
      loop (l1, l2)

    let foldr f = foldr' id f

    let foldrEq f = foldr' ul f

    let zip' w (l1, l2) =
      List.rev (foldl' w (fun (x, x', l) -> (x, x') :: l) [] (l1, l2))

    let zip (l1, l2) = zip' id (l1, l2)

    let zipEq (l1, l2) = zip' ul (l1, l2)

    let map' w f x = List.rev ((foldl' w (fun (x1, x2, l) -> f (x1, x2) :: l) []) x)

    let map f = map' id f

    let mapEq f = map' ul f

    let app' w f = foldl' w (fun (x1, x2, ()) -> f (x1, x2)) ()

    let app f = app' id f

    let appEq f = app' ul f

    let exists p (l1, l2) =
      let rec loop (l1, l2) =
        match (l1, l2) with
          (x1 :: l1, x2 :: l2) -> p (x1, x2) || loop (l1, l2)
        | _ -> false
      in
      loop (l1, l2)

    let all p ls = not (exists (fun x -> not (p x)) ls)

    let allEq p =
      let rec loop (l1, l2) =
        match (l1, l2) with
          ([], []) -> true
        | (x1 :: l1, x2 :: l2) -> p (x1, x2) && loop (l1, l2)
        | _ -> false
      in
      loop
  end

type 'a rec_fmt = {init : string; sep : string; final : string; fmt : 'a -> string}

module ListFormat =
  struct
    let fmt {init; sep; final; fmt} lst =
      init ^
      let (x,_) =
	List.fold_right
	  (fun x (str,s) -> (fmt x ^ s ^ str,sep))
	  lst
	  (final, "")
      in x
  end

module EML_Int =
  struct
    type t = int

    let to_string = string_of_int
    let of_string = int_of_string
    let zero = 0
    let to_int x = x
    let of_int x = x
    let add x y = x + y
    let sub x y = x - y
    let mul x y = x * y
    let div x y = x / y
    let rem x y = x mod y
    let lt x y = x < y
    let compare = compare
  end

(* --------- Beginning of the NuprlTerms module --------- *)

module TR   = ToRefRef
module II   = EML_Int
module Int  = Pervasives
module T    = ListFormat
module KEY  = struct type t = string let compare = String.compare end
module VARS = Set.Make(KEY)
module MAP  = Map.Make(KEY)
module SUB  = MAP

module ENV_MAP1 = Map.Make(KEY)

(*
module HT =
  struct
    type t = int
    let equal x1 x2 = (x1 = x2)
    let hash x = Hashtbl.hash x
  end
module ENV_MAP2 =
  struct
    module M = Hashtbl.Make(HT)
    type 'a t = (string * 'a) M.t
    let empty m : = M.length m = 0
  end*)

(*open Batteries_uni*)

module ENV_MAP = ENV_MAP1 (*BatMap.StringMap*)
type 'a env_map_type = 'a ENV_MAP.t

type 'a toref             = 'a TR.t

type nuprl_nat            = II.t

type variable             = string

type opid                 = string

type parameter_kind       = string (* such as: "token", "nat", "level-expression" *)
type parameter_value      = string

type tag                  = string toref

type opid_tag             = opid * tag
type parameter            = parameter_value * parameter_kind

type operator             = opid_tag * parameter list

type nuprl_term =
    TERM     of operator * nuprl_bound_term list (* generic term    *)
  | AXM_TERM                                     (* bottom          *)
  | BOT_TERM                                     (* bottom          *)
  | INT_TERM                                     (* int type        *)
  | ATM_TERM of int option                       (* atom type       *)
  | TOK_TERM of parameter                        (* token           *)
  | NAT_TERM of nuprl_nat                        (* natural number  *)
  | VAR_TERM of variable                         (* variable        *)
  | INL_TERM of nuprl_ref_term                   (* left injection  *)
  | INR_TERM of nuprl_ref_term                   (* right injection *)
  | FIX_TERM of nuprl_ref_term                   (* fixpoint        *)
  | CLO_TERM of nuprl_ref_term * env             (* closure         *)
  | LAM_TERM of variable * nuprl_ref_term        (* lambda          *)
  | WAI_TERM of nuprl_ref_term * nuprl_ref_term  (* wait            *)
  | APP_TERM of nuprl_ref_term * nuprl_ref_term  (* application     *)
  | PAI_TERM of nuprl_ref_term * nuprl_ref_term  (* pair            *)
  | IAX_TERM of nuprl_ref_term * nuprl_ref_term * nuprl_ref_term                        (* isaxiom *)
  | IPA_TERM of nuprl_ref_term * nuprl_ref_term * nuprl_ref_term                        (* ispair  *)
  | IEQ_TERM of nuprl_ref_term * nuprl_ref_term * nuprl_ref_term * nuprl_ref_term       (* int_eq  *)
  | AEQ_TERM of nuprl_ref_term * nuprl_ref_term * nuprl_ref_term * nuprl_ref_term       (* atom_eq *)
  | SPR_TERM of nuprl_ref_term * variable * variable * nuprl_ref_term                   (* spread  *)
  | DEC_TERM of nuprl_ref_term * variable * nuprl_ref_term * variable * nuprl_ref_term  (* decide  *)
and nuprl_bound_term = B_TERM of variable list * nuprl_ref_term
and nuprl_ref_term   = R_TERM of nuprl_term toref
and env              = ENV    of nuprl_ref_term env_map_type

type sign = (parameter_value option * parameter_kind) list * int list

(* An item is as follows:
*   - string:   name of the abstraction (and not of the term)
*   - sign:     signature of the term (lhs) (e.g., foo(0;1;0) -> [0;1;0] + parameters)
*   - string:   object identifier
*   - term:     left-hand-side of abstration
*   - term:     right-hand-side of abstration
*)
type item     = {id   : string;
		 sign : sign;
		 obid : string;
		 lhs  : nuprl_ref_term;
		 rhs  : nuprl_ref_term;
		 wfs  : nuprl_ref_term list}
type abs_lib  = item toref list MAP.t ref
type tof_lib  = nuprl_term toref MAP.t ref
type lib      = {abs : abs_lib; (* abstractions *)
		 tof : tof_lib} (* TERMOFs      *)

type lib_kind =
    ABS of string * item
  | TOF of string * nuprl_term

type ran_sub =
    FO of nuprl_term
  | SO of variable list * nuprl_term

type alpha = NEXT of string * (unit -> alpha)


(* ------ a few useful functions ------ *)

let null lst = (try List.hd lst; false with _ -> true)

let get = TR.get
let mk  = TR.mk
let set = TR.set


(* ------ REF TERMS ------ *)

let rterm2term (R_TERM rt) = TR.get rt

let mk_rterm term = R_TERM (TR.mk term)

let set_rterm (R_TERM rt) term = TR.set rt term


(* ------ TAGS ------ *)

let mk_tag  = mk
let get_tag = get
let set_tag = set

let default_dtag = "OPID"
let dummy_dtag   = ""
let dtag         = mk_tag default_dtag

let get_dtag () = dtag
let set_dtag v  = set_tag dtag v

let set_dummy_dtag () = set_dtag dummy_dtag
let reset_dtag     () = set_dtag default_dtag


(* ------ BASIC CONSTRUCTORS ------ *)

let mk_nuprl_variable_parameter  tok    = (tok,              "v")
let mk_nuprl_natural_parameter   tag    = (II.to_string tag, "n")
let mk_nuprl_token_parameter     token  = (token,            "t")
let mk_nuprl_string_parameter    string = (string,           "s")
let mk_nuprl_level_exp_parameter level  = (level,            "l")
let mk_nuprl_obid_parameter      obid   = (obid,             "o")
let mk_nuprl_ut2_parameter       id     = (id,               "ut2")
let mk_nuprl_bool_parameter      bool   = ((if bool then "T" else "F"), "b")

let mk_nuprl_parameter (param : parameter) = param

let mk_term opid tag params brterms =
  match opid, params, brterms with
    "axiom",  _, [] -> AXM_TERM
  | "bottom", _, [] -> BOT_TERM
  | "int",    _, [] -> INT_TERM
  | "natural_number", ((n,kind) :: params), [] ->
      NAT_TERM (try II.of_string n with Failure "int_of_string" -> II.zero)
  | "atom", [], [] -> ATM_TERM None
  | "atom", [(i,kind)], [] ->
      (
       try ATM_TERM (Some (int_of_string i))
       with _ -> TERM ((("atom", tag), [(i,kind)]), [])
      )
  | "token", [(i,kind)], [] -> TOK_TERM (i,kind)
  | "variable", ((var,kind) :: params), [] -> VAR_TERM var
  | "inl", _, [B_TERM ([], term)] -> INL_TERM term
  | "inr", _, [B_TERM ([], term)] -> INR_TERM term
  | "fix", _, [B_TERM ([], term)] -> FIX_TERM term
  | "lambda", _, [B_TERM ([var], body)] -> LAM_TERM (var,  body)
  | "!wait", _, [B_TERM ([], time); B_TERM ([], exp)]   -> WAI_TERM (time, exp)
  | "apply", _, [B_TERM ([], func); B_TERM ([], arg)]   -> APP_TERM (func, arg)
  | "pair",  _, [B_TERM ([], left); B_TERM ([], right)] -> PAI_TERM (left, right)
  | "isaxiom", _, [B_TERM ([], a); B_TERM ([], t1); B_TERM ([], t2)] -> IAX_TERM (a, t1, t2)
  | "ispair",  _, [B_TERM ([], a); B_TERM ([], t1); B_TERM ([], t2)] -> IPA_TERM (a, t1, t2)
  | "decide", _, [B_TERM ([], d);    B_TERM ([v1], t1); B_TERM ([v2], t2)] -> DEC_TERM (d, v1, t1, v2, t2)
  | "spread", _, [B_TERM ([], pair); B_TERM ([v1; v2], term)] -> SPR_TERM (pair, v1, v2, term)
  | "int_eq", _, [B_TERM ([], a); B_TERM ([], b); B_TERM ([], t1); B_TERM ([], t2)] -> IEQ_TERM (a, b, t1, t2)
  | "atom_eq", [], [B_TERM ([], a); B_TERM ([], b); B_TERM ([], t1); B_TERM ([], t2)] -> AEQ_TERM (a, b, t1, t2)
  | _, _, _ -> TERM (((opid, tag), params), brterms)

let mk_nuprl_ref_term (opid, params) b_rterms =
  let subs = List.map (fun (vars, rterm) -> B_TERM (vars, rterm)) b_rterms
  in mk_term opid dtag params subs

let mk_nuprl_term (opid, params) b_terms =
  let subs = List.map (fun (vars, term) -> B_TERM (vars, mk_rterm term)) b_terms
  in mk_term opid dtag params subs

let mk_nuprl_ref_simple_term opid ref_term_list =
  let subs = List.map (fun term -> B_TERM ([], term)) ref_term_list
  in mk_term opid dtag [] subs

let mk_nuprl_simple_term opid term_list =
  let subs = List.map (fun term -> B_TERM ([], mk_rterm term)) term_list
  in mk_term opid dtag [] subs

let make_term opid tag params brterms = TERM (((opid, tag), params), brterms)

let make_nuprl_ref_term (opid, params) b_rterms =
  let subs = List.map (fun (vars, rterm) -> B_TERM (vars, rterm)) b_rterms
  in make_term opid dtag params subs

let make_nuprl_term (opid, params) b_terms =
  let subs = List.map (fun (vars, term) -> B_TERM (vars, mk_rterm term)) b_terms
  in make_term opid dtag params subs

let make_nuprl_ref_simple_term opid ref_term_list =
  let subs = List.map (fun term -> B_TERM ([], term)) ref_term_list
  in make_term opid dtag [] subs

let make_nuprl_simple_term opid term_list =
  let subs = List.map (fun term -> B_TERM ([], mk_rterm term)) term_list
  in make_term opid dtag [] subs


(* ------ A FEW USEFUL FUNCTIONS ------ *)

let opid_of_term term =
  match term with
    TERM (((opid, _), _), _) -> opid
  | AXM_TERM                 -> "axiom"
  | BOT_TERM                 -> "bottom"
  | INT_TERM                 -> "int"
  | ATM_TERM _               -> "atom"
  | TOK_TERM _               -> "token"
  | NAT_TERM _               -> "natural_number"
  | VAR_TERM _               -> "variable"
  | LAM_TERM _               -> "lambda"
  | WAI_TERM _               -> "!wait"
  | APP_TERM _               -> "apply"
  | PAI_TERM _               -> "pair"
  | INL_TERM _               -> "inl"
  | INR_TERM _               -> "inr"
  | FIX_TERM _               -> "fix"
  | IAX_TERM _               -> "isaxiom"
  | IPA_TERM _               -> "ispair"
  | DEC_TERM _               -> "decide"
  | SPR_TERM _               -> "spread"
  | IEQ_TERM _               -> "int_eq"
  | AEQ_TERM _               -> "atom_eq"
  | CLO_TERM _               -> "!!closure"

let is_nuprl_variable_term term =
  match term with
    TERM ((("variable", _), _), _) -> true
  | VAR_TERM _                     -> true
  | _                              -> false

let is_nuprl_token_term term =
  match term with
    TERM ((("token", _), _), _) -> true
  | TOK_TERM _                  -> true
  | _                           -> false

let is_nuprl_lambda_term term =
  match term with
    TERM ((("lambda", _), _), _) -> true
  | LAM_TERM _                   -> true
  | _                            -> false

let is_nuprl_wait_term term =
  match term with
    TERM ((("!wait", _), _), _) -> true
  | WAI_TERM _                  -> true
  | _                           -> false

let is_nuprl_apply_term term =
  match term with
    TERM ((("apply", _), _), _) -> true
  | APP_TERM _                  -> true
  | _                           -> false

let is_nuprl_natural_number_term term =
  match term with
    TERM ((("natural_number", _), _), _) -> true
  | NAT_TERM _                           -> true
  | _                                    -> false

let is_nuprl_pair_term term =
  match term with
    TERM ((("pair", _), _), _) -> true
  | PAI_TERM _                 -> true
  | _                          -> false

let is_nuprl_inl_term term =
  match term with
    TERM ((("inl", _), _), _) -> true
  | INL_TERM _                -> true
  | _                         -> false

let is_nuprl_inr_term term =
  match term with
    TERM ((("inr", _), _), _) -> true
  | INR_TERM _                -> true
  | _                         -> false

let is_nuprl_bottom_term term =
  match term with
    TERM ((("bottom", _), _), _) -> true
  | BOT_TERM                     -> true
  | _                            -> false

let is_nuprl_axiom_term term =
  match term with
    TERM ((("axiom", _), _), _) -> true
  | AXM_TERM                    -> true
  | _                           -> false

let is_nuprl_int_term term =
  match term with
    TERM ((("int", _), _), _) -> true
  | INT_TERM                  -> true
  | _                         -> false

let is_nuprl_atom_term term =
  match term with
    TERM ((("atom", _), _), _) -> true
  | ATM_TERM _                 -> true
  | _                          -> false

let is_nuprl_fix_term term =
  match term with
    TERM ((("fix", _), _), _) -> true
  | FIX_TERM _                -> true
  | _                         -> false

let is_canonical_term term =
  is_nuprl_lambda_term              term
  || is_nuprl_pair_term           term
  || is_nuprl_inl_term            term
  || is_nuprl_inr_term            term
  || is_nuprl_axiom_term          term
  || is_nuprl_natural_number_term term
  || opid_of_term term = "token"


let dest_variable n term =
  match term with
    TERM ((("variable", _), [(var, "v")]), _) -> var
  | VAR_TERM var                              -> var
  | _                                         ->
      failwith ("dest_variable(" ^ string_of_int n ^ "," ^ opid_of_term term ^ ")")

let dest_ref_lambda n term =
  match term with
    TERM ((("lambda", _), _), [B_TERM ([var], body)]) -> (var, body)
  | LAM_TERM (var, body)                              -> (var, body)
  | _                                                 ->
      failwith ("dest_lambda(" ^ string_of_int n ^ "):" ^ opid_of_term term)

let dest_lambda n term =
  let (var, body) = dest_ref_lambda n term in
  (var, rterm2term body)

let dest_wait term =
  match term with
    TERM ((("!wait", _), _), [B_TERM ([], time); B_TERM ([], exp)]) -> (rterm2term time, rterm2term exp)
  | WAI_TERM (time, exp)                                            -> (rterm2term time, rterm2term exp)
  | _                                                               -> failwith ("dest_wait:" ^ opid_of_term term)

let dest_apply term =
  match term with
    TERM ((("apply", _), _), [B_TERM ([], rterm1); B_TERM ([], rterm2)]) -> (rterm2term rterm1, rterm2term rterm2)
  | APP_TERM (rterm1, rterm2)                                            -> (rterm2term rterm1, rterm2term rterm2)
  | _                                                                    -> failwith ("dest_apply:" ^ opid_of_term term)

let dest_pair n term =
  match term with
    TERM ((("pair", _), _), [B_TERM ([], rt1); B_TERM ([], rt2)]) -> (rterm2term rt1, rterm2term rt2)
  | PAI_TERM (rterm1, rterm2)                                     -> (rterm2term rterm1, rterm2term rterm2)
  | _                                                             -> failwith ("dest_pair(" ^ Int.string_of_int n ^ ")")

let dest_natural_number term =
  match term with
    TERM ((("natural_number", tag), ((n, kind) :: params)), []) -> (try II.of_string n with Failure "int_of_string" -> II.zero)
  | NAT_TERM n                                                  -> n
  | _                                                           -> failwith "dest_natural_number"

let dest_token term =
  match term with
    TERM ((("token",_), [(t,k)]), []) -> (t,k)
  | TOK_TERM (t,k) -> (t,k)
  | _ -> failwith "dest_natural_number"

let dest_id term =
  match dest_token term with
   (t,"ut2") -> t
  | _ -> failwith "dest_id"

let dest_inl term =
  match term with
    TERM ((("inl", _), _), [B_TERM ([], rterm)]) -> rterm2term rterm
  | INL_TERM rterm                               -> rterm2term rterm
  | _                                            -> failwith ("dest_inl")

let dest_inr term =
  match term with
    TERM ((("inr", _), _), [B_TERM ([], rterm)]) -> rterm2term rterm
  | INR_TERM rterm                               -> rterm2term rterm
  | _                                            -> failwith ("dest_inr")

let dest_fix term =
  match term with
    TERM ((("fix", _), _), [B_TERM ([], rterm)]) -> rterm2term rterm
  | FIX_TERM rterm                               -> rterm2term rterm
  | _                                            -> failwith ("dest_fix")


(* variable *)
let make_nuprl_variable_term tok = make_nuprl_term ("variable", [mk_nuprl_variable_parameter tok]) []
let mk_variable_term tok = VAR_TERM tok

(* apply *)
let make_nuprl_apply_ref_term func arg =
  make_nuprl_ref_simple_term "apply" [func; arg]
let mk_apply_term func arg = APP_TERM (mk_rterm func, mk_rterm arg)
let mk_apply_ref_term func arg = APP_TERM (func, arg)

(* lambda *)
let make_nuprl_lambda_ref_term var rterm = make_nuprl_ref_term ("lambda", []) [([var], rterm)]
let mk_lambda_term var term = LAM_TERM (var, mk_rterm term)

(* wait *)
let make_nuprl_wait_ref_term time exp = make_nuprl_ref_simple_term "!wait" [time; exp]
let mk_wait_term time exp = WAI_TERM (mk_rterm time, mk_rterm exp)

(* pair *)
let make_nuprl_pair_ref_term left right = make_nuprl_ref_simple_term "pair" [left; right]
let mk_pair_term left right = PAI_TERM (mk_rterm left, mk_rterm right)

(* axiom *)
let make_nuprl_axiom_term = make_nuprl_ref_simple_term "axiom" []
let mk_axiom_term = AXM_TERM

(* bottom *)
let make_nuprl_bottom_term = make_nuprl_ref_simple_term "bottom" []
let mk_bottom_term = BOT_TERM

(* bottom *)
let make_nuprl_int_term = make_nuprl_ref_simple_term "int" []
let mk_int_term = INT_TERM

(* atom *)
let make_nuprl_atom_term x =
  match x with
    Some n -> make_nuprl_ref_term ("atom", [mk_nuprl_natural_parameter (II.of_int n)]) []
  | None   -> make_nuprl_ref_simple_term "atom" []
let mk_atom_term nop = ATM_TERM nop

(* token *)
let make_nuprl_token_term (t,k) =
  TERM ((("token", dtag), [(t,k)]), [])
let mk_token_term (t,k) = TOK_TERM (t,k)
let mk_regular_token_term tok = mk_token_term (mk_nuprl_token_parameter tok)
let mk_mkid_term id = mk_token_term (mk_nuprl_ut2_parameter id)

(* natural number *)
let make_nuprl_natural_number_term nat =
  make_nuprl_term ("natural_number", [mk_nuprl_natural_parameter nat]) []
let mk_natural_number_term nat = NAT_TERM nat

(* injections *)
let make_nuprl_inl_ref_term term = make_nuprl_ref_simple_term "inl" [term]
let make_nuprl_inr_ref_term term = make_nuprl_ref_simple_term "inr" [term]
let mk_inl_term term = INL_TERM (mk_rterm term)
let mk_inr_term term = INR_TERM (mk_rterm term)

(* fix *)
let make_nuprl_fix_ref_term term = make_nuprl_ref_simple_term "fix" [term]
let mk_fix_term term = FIX_TERM (mk_rterm term)

(* decide *)
let make_nuprl_decide_ref_term dec (var1, bterm1) (var2, bterm2) =
  make_nuprl_ref_term ("decide", []) [([], dec); ([var1], bterm1); ([var2], bterm2)]
let mk_decide_term dec (var1, term1) (var2, term2) =
  DEC_TERM (mk_rterm dec, var1, mk_rterm term1, var2, mk_rterm term2)

(* spread *)
let make_nuprl_spread_ref_term  pair (v1, v2, bterm) =
  make_nuprl_ref_term ("spread", []) [([], pair); ([v1; v2], bterm)]
let mk_spread_term pair (var1, var2, term) =
  SPR_TERM (mk_rterm pair, var1, var2, mk_rterm term)

(* int_eq *)
let make_nuprl_int_eq_ref_term a b rterm1 rterm2 =
  make_nuprl_ref_simple_term "int_eq" [a; b; rterm1; rterm2]
let mk_int_eq_term a b term1 term2 =
  IEQ_TERM (mk_rterm a, mk_rterm b, mk_rterm term1, mk_rterm term2)

(* atom_eq *)
let make_nuprl_atom_eq_ref_term a b rterm1 rterm2 =
  make_nuprl_ref_simple_term "atom_eq" [a; b; rterm1; rterm2]
let mk_atom_eq_term a b term1 term2 =
  AEQ_TERM (mk_rterm a, mk_rterm b, mk_rterm term1, mk_rterm term2)

(* isaxiom *)
let make_nuprl_isaxiom_ref_term ax rterm1 rterm2 =
  make_nuprl_ref_simple_term "isaxiom" [ax; rterm1; rterm2]
let mk_isaxiom_term ax term1 term2 =
  IAX_TERM (mk_rterm ax, mk_rterm term1, mk_rterm term2)

(* ispair *)
let make_nuprl_ispair_ref_term pair rterm1 rterm2 =
  make_nuprl_ref_simple_term "ispair" [pair; rterm1; rterm2]
let mk_ispair_term pair term1 term2 =
  IPA_TERM (mk_rterm pair, mk_rterm term1, mk_rterm term2)


(* ------ CLOSURES ------ *)

let em_env = ENV ENV_MAP.empty

let is_empty_env (ENV env) = ENV_MAP.is_empty env
let is_em_env = is_empty_env

let mk_ct (rterm, env) =
  if is_em_env env
  then rterm2term rterm
  else CLO_TERM (rterm, env)

let mk_rct (term, env) = mk_ct (mk_rterm term, env)

let mk_rctr (rterm, env) =
  if is_em_env env
  then rterm
  else mk_rterm (CLO_TERM (rterm, env))

let is_ct term =
  match term with
    CLO_TERM _ -> true
  | _          -> false

let get_ct term =
  match term with
    CLO_TERM (rterm, env) -> (rterm, env)
  | _ -> failwith "get_ct"

let dest_clos (rterm, env) = (rterm2term rterm, env)

let dest_ct term =
  match term with
    CLO_TERM (rterm, env) -> dest_clos (rterm, env)
  | _ -> failwith "dest_ct"

let lookup_clos (ENV env) var =
  try Some (ENV_MAP.find var env)
  with Not_found -> None

let lookup env var =
  match lookup_clos env var with
    Some rterm ->
      (match rterm2term rterm with
	CLO_TERM (rterm, e) -> Some (rterm2term rterm, e)
      | term -> Some (term, em_env))
  | None -> None

let get_bterms term =
  match term with
    TERM (_, bterms)          -> bterms
  | AXM_TERM                  -> []
  | BOT_TERM                  -> []
  | INT_TERM                  -> []
  | ATM_TERM _                -> []
  | TOK_TERM _                -> []
  | NAT_TERM _                -> []
  | VAR_TERM _                -> []
  | LAM_TERM (var, rterm)     -> [B_TERM ([var], rterm)]
  | WAI_TERM (rterm1, rterm2) -> [B_TERM ([], rterm1); B_TERM ([], rterm2)]
  | APP_TERM (rterm1, rterm2) -> [B_TERM ([], rterm1); B_TERM ([], rterm2)]
  | PAI_TERM (rterm1, rterm2) -> [B_TERM ([], rterm1); B_TERM ([], rterm2)]
  | INL_TERM rterm            -> [B_TERM ([], rterm)]
  | INR_TERM rterm            -> [B_TERM ([], rterm)]
  | FIX_TERM rterm            -> [B_TERM ([], rterm)]
  | AEQ_TERM (a, b, t1, t2)   -> [B_TERM ([], a); B_TERM ([], b); B_TERM ([], t1); B_TERM ([], t2)]
  | IEQ_TERM (a, b, t1, t2)   -> [B_TERM ([], a); B_TERM ([], b); B_TERM ([], t1); B_TERM ([], t2)]
  | IPA_TERM (a, t1, t2)      -> [B_TERM ([], a); B_TERM ([], t1); B_TERM ([], t2)]
  | IAX_TERM (a, t1, t2)      -> [B_TERM ([], a); B_TERM ([], t1); B_TERM ([], t2)]
  | DEC_TERM (dec, var1, rterm1, var2, rterm2) -> [B_TERM ([], dec); B_TERM ([var1], rterm1); B_TERM ([var2], rterm2)]
  | SPR_TERM (pair, var1, var2, rterm)         -> [B_TERM ([], pair); B_TERM ([var1; var2], rterm)]
  | CLO_TERM _ -> failwith "get_brterms"


(* -- free variables -- *)
let domain_set (ENV m) =
  ENV_MAP.fold (fun i  _ set -> VARS.add i set)
    m
    VARS.empty

let addListVARS lst set = List.fold_right VARS.add lst set

let fromListVARS lst = addListVARS lst VARS.empty

let empty_vars = VARS.empty

let rec fo_free_vars bounds term =
  match term with
    TERM (operator, bterms) ->
      if is_nuprl_variable_term term
      then
	let v = dest_variable 1 term in
	if VARS.mem v bounds
	then VARS.empty
	else VARS.singleton v
      else
	List.fold_right (fun bterm vars -> VARS.union vars (fo_free_vars_bterm bounds bterm))
	  bterms
	  empty_vars
  | AXM_TERM                  -> VARS.empty
  | BOT_TERM                  -> VARS.empty
  | INT_TERM                  -> VARS.empty
  | ATM_TERM _                -> VARS.empty
  | TOK_TERM _                -> VARS.empty
  | NAT_TERM _                -> VARS.empty
  | VAR_TERM var ->
      if VARS.mem var bounds
      then VARS.empty
      else VARS.singleton var
  | CLO_TERM (rterm, env)     -> fo_free_vars_clos bounds (rterm, env)
  | LAM_TERM (var, rterm)     -> fo_free_vars_rterm (VARS.add var bounds) rterm
  | WAI_TERM (rterm1, rterm2) -> VARS.union (fo_free_vars_rterm bounds rterm1) (fo_free_vars_rterm bounds rterm2)
  | APP_TERM (rterm1, rterm2) -> VARS.union (fo_free_vars_rterm bounds rterm1) (fo_free_vars_rterm bounds rterm2)
  | PAI_TERM (rterm1, rterm2) -> VARS.union (fo_free_vars_rterm bounds rterm1) (fo_free_vars_rterm bounds rterm2)
  | INL_TERM rterm            -> fo_free_vars_rterm bounds rterm
  | INR_TERM rterm            -> fo_free_vars_rterm bounds rterm
  | FIX_TERM rterm            -> fo_free_vars_rterm bounds rterm
  | DEC_TERM (dec, var1, rterm1, var2, rterm2) ->
      VARS.union
	(fo_free_vars_rterm bounds dec)
	(VARS.union
	   (fo_free_vars_rterm (VARS.add var1 bounds) rterm1)
	   (fo_free_vars_rterm (VARS.add var2 bounds) rterm2))
  | SPR_TERM (pair, var1, var2, rterm) ->
      VARS.union
	(fo_free_vars_rterm bounds pair)
	(fo_free_vars_rterm (VARS.add var1 (VARS.add var2 bounds)) rterm)
  | IAX_TERM (ax, rterm1, rterm2) ->
      VARS.union
	(fo_free_vars_rterm bounds ax)
	(VARS.union
	   (fo_free_vars_rterm bounds rterm1)
	   (fo_free_vars_rterm bounds rterm2))
  | IPA_TERM (pair, rterm1, rterm2) ->
      VARS.union
	(fo_free_vars_rterm bounds pair)
	(VARS.union
	   (fo_free_vars_rterm bounds rterm1)
	   (fo_free_vars_rterm bounds rterm2))
  | IEQ_TERM (a, b, rterm1, rterm2) ->
      VARS.union
	(fo_free_vars_rterm bounds a)
	(VARS.union
	   (fo_free_vars_rterm bounds b)
	   (VARS.union
	      (fo_free_vars_rterm bounds rterm1)
	      (fo_free_vars_rterm bounds rterm2)))
  | AEQ_TERM (a, b, rterm1, rterm2) ->
      VARS.union
	(fo_free_vars_rterm bounds a)
	(VARS.union
	   (fo_free_vars_rterm bounds b)
	   (VARS.union
	      (fo_free_vars_rterm bounds rterm1)
	      (fo_free_vars_rterm bounds rterm2)))

and fo_free_vars_clos bounds (rterm, env) =
 fo_free_vars_rterm (VARS.union bounds (domain_set env)) rterm

and fo_free_vars_rterm bounds rterm = fo_free_vars bounds (rterm2term rterm)

and fo_free_vars_bterm bounds (B_TERM (vars, rterm)) =
 let bounds' = addListVARS vars bounds in
 fo_free_vars_rterm bounds' rterm

let free_vars = fo_free_vars VARS.empty


(* -- simple closure: (v, [v -> t]) *)
let is_simple_closure (rterm, env) =
 let term = rterm2term rterm in
 is_nuprl_variable_term term
   &&
 SML_Option.isSome (lookup_clos env (dest_variable 2 term))

(* shallow term: op(v1,..,vn) *)
let is_shallow_term term =
 match term with
   TERM (_, bterms) ->
     List.fold_right
       (fun bterm varsopt ->
	 match bterm, varsopt with
	   B_TERM ([], rterm), Some vars ->
	     let t = rterm2term rterm in
	     if is_nuprl_variable_term t
	     then Some (VARS.add (dest_variable 3 t) vars)
	     else None
	 | _, _ -> None)
       bterms
       (Some VARS.empty)
 | _ -> None

let prune_clos (term, ENV env) =
  let frees = free_vars term in
  let env' = ENV_MAP.filter (fun v _ -> VARS.mem v frees) env in
  mk_rct (term, ENV env')

(*val prune_clos = mk_rclos*)

let rec add2env_one (ENV env) (v,t,e) =
 if v = ""
 then ENV env
 else if is_nuprl_variable_term t
 then
   match lookup_clos e (dest_variable 4 t) with
     Some c -> ENV (ENV_MAP.add v c env)
   | None   -> failwith "add2env_one"
 else if is_ct t
 then
   let (t',e') = dest_ct t in
   add2env_one (ENV env) (v,t',e')
 else if null (get_bterms t)
 then ENV (ENV_MAP.add v (mk_rterm t) env)
 else ENV (ENV_MAP.add v (mk_rterm (prune_clos (t, e))) env)

and add2env env lst =
 match lst with
   []      -> env
 | x :: xs -> add2env (add2env_one env x) xs

let rec term2env term =
 match term with
   TERM (opr, [B_TERM ([v], thunk); B_TERM ([], env)]) ->
     let (t,e) = dest_pair 20 (rterm2term thunk) in
     let (ENV env') = rterm2env env in
     ENV (ENV_MAP.add v (mk_rterm (mk_rct (t, term2env e))) env')
 | _ -> failwith "term2env"

and rterm2env rterm = term2env (rterm2term rterm)

let close term env =
 let rec aux term bounds env =
   match term with
     CLO_TERM (rterm, env) -> aux (rterm2term rterm) bounds env
   | AXM_TERM -> AXM_TERM
   | BOT_TERM -> BOT_TERM
   | INT_TERM -> INT_TERM
   | ATM_TERM x -> ATM_TERM x
   | TOK_TERM x -> TOK_TERM x
   | NAT_TERM n -> NAT_TERM n
   | LAM_TERM (var, rterm) ->
       let bs = VARS.add var bounds in
       let t  = aux (rterm2term rterm) bs env in
       LAM_TERM (var, mk_rterm t)
   | WAI_TERM (rterm1, rterm2) ->
       let t1 = aux (rterm2term rterm1) bounds env in
       let t2 = aux (rterm2term rterm2) bounds env in
       WAI_TERM (mk_rterm t1, mk_rterm t2)
   | APP_TERM (rterm1, rterm2) ->
       let t1 = aux (rterm2term rterm1) bounds env in
       let t2 = aux (rterm2term rterm2) bounds env in
       APP_TERM (mk_rterm t1, mk_rterm t2)
   | PAI_TERM (rterm1, rterm2) ->
       let t1 = aux (rterm2term rterm1) bounds env in
       let t2 = aux (rterm2term rterm2) bounds env in
       PAI_TERM (mk_rterm t1, mk_rterm t2)
   | INL_TERM rterm ->
       let t = aux (rterm2term rterm) bounds env in
       INL_TERM (mk_rterm t)
   | INR_TERM rterm ->
       let t = aux (rterm2term rterm) bounds env in
       INR_TERM (mk_rterm t)
   | FIX_TERM rterm ->
       let t = aux (rterm2term rterm) bounds env in
       FIX_TERM (mk_rterm t)
   | DEC_TERM (dec, var1, rterm1, var2, rterm2) ->
	let d  = aux (rterm2term dec) bounds env in
	let b1 = VARS.add var1 bounds in
	let t1 = aux (rterm2term rterm1) b1 env in
	let b2 = VARS.add var2 bounds in
	let t2 = aux (rterm2term rterm2) b2 env in
	DEC_TERM (mk_rterm d, var1, mk_rterm t1, var2, mk_rterm t2)
   | SPR_TERM (pair, var1, var2, rterm) ->
       let p  = aux (rterm2term pair) bounds env in
       let bs = addListVARS [var1; var2] bounds in
       let t  = aux (rterm2term rterm) bs env in
       SPR_TERM (mk_rterm p, var1, var2, mk_rterm t)
   | IAX_TERM (ax, rterm1, rterm2) ->
       let a  = aux (rterm2term ax)     bounds env in
       let t1 = aux (rterm2term rterm1) bounds env in
       let t2 = aux (rterm2term rterm2) bounds env in
       IAX_TERM (mk_rterm a, mk_rterm t1, mk_rterm t2)
   | IPA_TERM (pair, rterm1, rterm2) ->
       let p  = aux (rterm2term pair)   bounds env in
       let t1 = aux (rterm2term rterm1) bounds env in
       let t2 = aux (rterm2term rterm2) bounds env in
       IPA_TERM (mk_rterm p, mk_rterm t1, mk_rterm t2)
   | IEQ_TERM (a, b, rterm1, rterm2) ->
       let a  = aux (rterm2term a)      bounds env in
       let b  = aux (rterm2term b)      bounds env in
       let t1 = aux (rterm2term rterm1) bounds env in
       let t2 = aux (rterm2term rterm2) bounds env in
       IEQ_TERM (mk_rterm a, mk_rterm b, mk_rterm t1, mk_rterm t2)
   | AEQ_TERM (a, b, rterm1, rterm2) ->
       let a  = aux (rterm2term a)      bounds env in
       let b  = aux (rterm2term b)      bounds env in
       let t1 = aux (rterm2term rterm1) bounds env in
       let t2 = aux (rterm2term rterm2) bounds env in
       AEQ_TERM (mk_rterm a, mk_rterm b, mk_rterm t1, mk_rterm t2)
   | VAR_TERM var ->
       if VARS.mem var bounds
       then term
       else
	 (match lookup env var with
	   Some (t,e) -> aux t bounds e
	 | None -> term)
   | TERM (((opid, tag), params) as opr, bterms) ->
       if opid = "variable"
       then
	 let v = dest_variable 5 term in
	 if VARS.mem v bounds
	 then term
	 else
	   (match lookup env v with
	     Some (t,e) -> aux t bounds e
	   | None -> term)
       else
	 let bterms' =
	   List.map
	     (fun (B_TERM (vs, rt)) ->
	       let t1 = rterm2term rt in
	       let bs = addListVARS vs bounds in
	       let t2 = aux t1 bs env in
	       B_TERM (vs, mk_rterm t2))
	     bterms in
	 TERM (opr, bterms')
 in aux term VARS.empty env


(* ------ TO STRING ------ *)

let toStringOpid  opid  = opid
let toStringTag   tag   = get_tag tag
let toStringValue value = value
let toStringKind  kind  = kind

let toStringParameter (value, kind) = toStringValue value ^ ":" ^ toStringKind kind

let toStringParameters params =
 T.fmt {init  = "";
	final = "";
	sep   = ",";
	fmt   = toStringParameter}
   params

let toStringOpidTag (opid, tag) = toStringOpid opid ^ ":" ^ toStringTag tag

let toStringOperator operator =
 match operator with
   (opid_tag, []) -> toStringOpidTag opid_tag
 | (opid_tag, parameters) ->
     toStringOpidTag opid_tag ^ "," ^ toStringParameters parameters

let toStringVars vars =
 T.fmt {init  = "";
	final = "";
	sep   = ",";
	fmt   = fun v -> v ^ ":v"}
   vars

let rec toStringTerm term ind space newline =
 match term with
   TERM (operator, []) -> "{" ^ toStringOperator operator ^ "}()"
 | TERM (operator, bterms) ->
     let ind' = ind ^ space in
     "{" ^ toStringOperator operator ^ "}" ^ newline ^ ind ^
     "(" ^ toStringBTerms bterms ind' space newline ^ ")"
 | AXM_TERM                  -> toStringTerm make_nuprl_axiom_term  ind space newline
 | BOT_TERM                  -> toStringTerm make_nuprl_bottom_term ind space newline
 | INT_TERM                  -> toStringTerm make_nuprl_int_term    ind space newline
 | ATM_TERM x                -> toStringTerm (make_nuprl_atom_term  x)                 ind space newline
 | TOK_TERM x                -> toStringTerm (make_nuprl_token_term x)                 ind space newline
 | NAT_TERM nat              -> toStringTerm (make_nuprl_natural_number_term nat)      ind space newline
 | VAR_TERM var              -> toStringTerm (make_nuprl_variable_term var)            ind space newline
 | LAM_TERM (var, rterm)     -> toStringTerm (make_nuprl_lambda_ref_term var rterm)    ind space newline
 | WAI_TERM (rterm1, rterm2) -> toStringTerm (make_nuprl_wait_ref_term rterm1 rterm2)  ind space newline
 | APP_TERM (rterm1, rterm2) -> toStringTerm (make_nuprl_apply_ref_term rterm1 rterm2) ind space newline
 | PAI_TERM (rterm1, rterm2) -> toStringTerm (make_nuprl_pair_ref_term rterm1 rterm2)  ind space newline
 | INL_TERM rterm            -> toStringTerm (make_nuprl_inl_ref_term rterm)           ind space newline
 | INR_TERM rterm            -> toStringTerm (make_nuprl_inr_ref_term rterm)           ind space newline
 | FIX_TERM rterm            -> toStringTerm (make_nuprl_fix_ref_term rterm)           ind space newline
 | DEC_TERM (dec, var1, rterm1, var2, rterm2) -> toStringTerm (make_nuprl_decide_ref_term dec (var1, rterm1) (var2, rterm2)) ind space newline
 | SPR_TERM (pair, var1, var2, rterm)         -> toStringTerm (make_nuprl_spread_ref_term pair (var1, var2, rterm))          ind space newline
 | IEQ_TERM (a, b, rterm1, rterm2)            -> toStringTerm (make_nuprl_int_eq_ref_term  a b  rterm1 rterm2)               ind space newline
 | AEQ_TERM (a, b, rterm1, rterm2)            -> toStringTerm (make_nuprl_atom_eq_ref_term a b  rterm1 rterm2)               ind space newline
 | IAX_TERM (ax,   rterm1, rterm2)            -> toStringTerm (make_nuprl_isaxiom_ref_term ax   rterm1 rterm2)               ind space newline
 | IPA_TERM (pair, rterm1, rterm2)            -> toStringTerm (make_nuprl_ispair_ref_term  pair rterm1 rterm2)               ind space newline
 | CLO_TERM (rterm, env)                      -> toStringClos (rterm, env) ind space newline

and toStringClos (rterm, env) ind space newline =
  if is_empty_env env
  then toStringRTerm rterm ind space newline
  else
    let ind' = ind ^ space in
    "{!closure:OPID}" ^ newline ^ ind ^
    "(" ^ toStringRTerm rterm ind' space newline ^ ";" ^ newline ^ ind'
    ^ toStringEnv env ind' space newline ^ ")"

and toStringEnv (ENV m) ind space newline =
  let (a,_) =
    ENV_MAP.fold
      (fun var rterm (str, ind) ->
	let ind1 = ind ^ space in
	("{env:OPID}" ^ newline
	 ^ ind
	 ^ "({bound_id:OPID," ^ toStringVars [var] ^ "}" ^ newline
	 ^ ind1
	 ^ toStringRTerm rterm ind1 space newline ^ ";" ^ newline
	 ^ ind1
	 ^ str ^ ")",
	 ind1))
      m
      ("", ind)
  in a

and toStringRTerm ref_term = toStringTerm (rterm2term ref_term)

and toStringBTerm bterm ind space newline =
  match bterm with
    B_TERM ([],   rterm) -> toStringRTerm rterm ind space newline
  | B_TERM (vars, rterm) ->
      let str = toStringVars vars in
      "{bound_id:OPID," ^ str ^ "}" ^ newline ^ ind ^
      "(" ^ toStringRTerm rterm (ind ^ space) space newline ^ ")"

and toStringBTerms bterms ind space newline =
 T.fmt {init  = "";
	final = "";
	sep   = ";" ^ newline ^ ind;
	fmt   = fun bterm -> toStringBTerm bterm ind space newline}
   bterms

and toStringTerms terms ind space newline =
 T.fmt {init  = "";
	final = "";
	sep   = ";" ^ newline ^ ind;
	fmt   = fun term -> toStringTerm term ind space newline}
   terms

let to_string_space   = " "
let to_string_newline = "\n"

let toStringTerm   = fun term  -> toStringTerm  term  "" to_string_space to_string_newline
and toStringRTerm  = fun rterm -> toStringRTerm rterm "" to_string_space to_string_newline
and toStringEnv    = fun env   -> toStringEnv   env   "" to_string_space to_string_newline
and spToStringTerm = fun term  -> toStringTerm  term  "" "" ""


(* -- write to file while traversing the tree *)

let outputIO out str = output_string out str

let rec toStringTerm_stream out term ind =
 match term with
   TERM (operator, []) ->
     outputIO out ("{" ^ toStringOperator operator ^ "}()")
 | TERM (operator, bterms) ->
     let ind' = ind ^ " " in
     let opr  = toStringOperator operator in
     outputIO out ("{" ^ opr ^ "}\n" ^ ind ^ "(");
     toStringBTerms_stream out bterms ind';
     outputIO out ")"
 | AXM_TERM                  -> toStringTerm_stream out make_nuprl_axiom_term  ind
 | BOT_TERM                  -> toStringTerm_stream out make_nuprl_bottom_term ind
 | INT_TERM                  -> toStringTerm_stream out make_nuprl_int_term    ind
 | ATM_TERM x                -> toStringTerm_stream out (make_nuprl_atom_term  x)                 ind
 | TOK_TERM x                -> toStringTerm_stream out (make_nuprl_token_term x)                 ind
 | NAT_TERM nat              -> toStringTerm_stream out (make_nuprl_natural_number_term nat)      ind
 | VAR_TERM var              -> toStringTerm_stream out (make_nuprl_variable_term var)            ind
 | LAM_TERM (var, rterm)     -> toStringTerm_stream out (make_nuprl_lambda_ref_term var rterm)    ind
 | WAI_TERM (rterm1, rterm2) -> toStringTerm_stream out (make_nuprl_wait_ref_term rterm1 rterm2)  ind
 | APP_TERM (rterm1, rterm2) -> toStringTerm_stream out (make_nuprl_apply_ref_term rterm1 rterm2) ind
 | PAI_TERM (rterm1, rterm2) -> toStringTerm_stream out (make_nuprl_pair_ref_term rterm1 rterm2)  ind
 | INL_TERM rterm            -> toStringTerm_stream out (make_nuprl_inl_ref_term rterm)           ind
 | INR_TERM rterm            -> toStringTerm_stream out (make_nuprl_inr_ref_term rterm)           ind
 | FIX_TERM rterm            -> toStringTerm_stream out (make_nuprl_fix_ref_term rterm)           ind
 | DEC_TERM (dec, var1, rterm1, var2, rterm2) -> toStringTerm_stream out (make_nuprl_decide_ref_term dec (var1, rterm1) (var2, rterm2)) ind
 | SPR_TERM (pair, var1, var2, rterm)         -> toStringTerm_stream out (make_nuprl_spread_ref_term pair (var1, var2, rterm))          ind
 | IEQ_TERM (a, b, rterm1, rterm2)            -> toStringTerm_stream out (make_nuprl_int_eq_ref_term  a b  rterm1 rterm2)               ind
 | AEQ_TERM (a, b, rterm1, rterm2)            -> toStringTerm_stream out (make_nuprl_atom_eq_ref_term a b  rterm1 rterm2)               ind
 | IAX_TERM (ax,   rterm1, rterm2)            -> toStringTerm_stream out (make_nuprl_isaxiom_ref_term ax   rterm1 rterm2)               ind
 | IPA_TERM (pair, rterm1, rterm2)            -> toStringTerm_stream out (make_nuprl_ispair_ref_term  pair rterm1 rterm2)               ind
 | CLO_TERM (rterm, env)                      -> toStringClos_stream out (rterm, env) ind

and toStringClos_stream out (rterm, env) ind =
 let ind' = ind ^ " " in
 outputIO out ("{!closure:OPID}\n" ^ ind ^ "(");
 toStringRTerm_stream out rterm ind';
 outputIO out (";\n" ^ ind');
 toStringEnv_stream out env ind';
 outputIO out ")"

and toStringEnv_stream out (ENV m) ind =
  let _ =
    ENV_MAP.fold
      (fun var rterm ind ->
	let ind1 = ind  ^ " " in
	outputIO out ("{env:OPID}\n" ^ ind);
	outputIO out ("({bound_id:OPID," ^ toStringVars [var] ^ "}\n" ^ ind1);
	toStringRTerm_stream out rterm ind1;
	outputIO out ("\n" ^ ind1);
	ind1)
      m
      ind
  in ()

and toStringRTerm_stream out ref_term =
 toStringTerm_stream out (rterm2term ref_term)

and toStringBTerm_stream out bterm ind =
 match bterm with
   B_TERM ([],   rterm) -> toStringRTerm_stream out rterm ind
 | B_TERM (vars, rterm) ->
     let str = toStringVars vars in
     outputIO out ("{bound_id:OPID," ^ str ^ "}\n" ^ ind ^ "(");
     toStringRTerm_stream out rterm (ind ^ " ");
     outputIO out ")"

and toStringBTerms_stream out lst ind =
 match lst with
   []        -> ()
 | [x]       -> toStringBTerm_stream out x ind
 | (x :: xs) ->
     (toStringBTerm_stream out x ind;
      outputIO out (";\n" ^ ind);
      toStringBTerms_stream out xs ind)

let toStringTermStream term file =
 let out = open_out file in
 let _   = toStringTerm_stream out term "" in
 let _   = close_out out in
 ()


(* -- pretty printer -- *)

let rec ppTerm term =
 match term with
   TERM ((("apply",          _), []),          [B_TERM ([], f);
						B_TERM ([], a)])      -> "(" ^ ppRTerm f ^ ")(" ^ ppRTerm a ^ ")"
 | TERM ((("int_eq",         _), []),          [B_TERM ([], x);
						B_TERM ([], y);
						B_TERM ([], w);
						B_TERM ([], z)])      -> "if " ^ ppRTerm x ^ " = " ^ ppRTerm y ^ " then " ^ ppRTerm w ^ " else " ^ ppRTerm z
 | TERM ((("subtract",       _), []),          [B_TERM ([], x);
						B_TERM ([], y)])      -> ppRTerm x ^ "-" ^ ppRTerm y
 | TERM ((("add",            _), []),          [B_TERM ([], x);
						B_TERM ([], y)])      -> ppRTerm x ^ "+" ^ ppRTerm y
 | TERM ((("pair",           _), []),          [B_TERM ([], x);
						B_TERM ([], y)])      -> "(" ^ ppRTerm x ^ "," ^ ppRTerm y ^ ")"
 | TERM ((("variable",       _), [(v,vkind)]), [])                    -> v
 | TERM ((("natural_number", _), [(n,nkind)]), [])                    -> n
 | TERM ((("ycomb",          _), []),          [])                    -> "Y"
 | TERM ((("fix",            _), []),          [B_TERM ([], x)])      -> "fix(" ^ ppRTerm x ^ ")"
 | TERM ((("lambda",         _), []),          [B_TERM ([x], f)])     -> "\\" ^ x ^ ". " ^ ppRTerm f
 | TERM ((("inr",            _), []),          [B_TERM ([], t)])      -> "inr(" ^ ppRTerm t ^ ")"
 | TERM ((("inl",            _), []),          [B_TERM ([], t)])      -> "inl(" ^ ppRTerm t ^ ")"
 | TERM ((("decide",         _), []),          [B_TERM ([], dec);
						B_TERM ([v1], t1);
						B_TERM ([v2], t2)])   -> "case " ^ ppRTerm dec ^ " of inl("^ v1 ^ ") => " ^ ppRTerm t1 ^ " | inr(" ^ v2 ^ ") => " ^ ppRTerm t2
 | TERM ((("spread",         _), []),          [B_TERM ([], pair);
						B_TERM ([x1;x2], t)]) -> "let " ^ x1 ^ "," ^ x2 ^ " = " ^ ppRTerm pair ^ " in " ^ ppRTerm t
 | TERM ((("list_ind",       _), []),          [B_TERM ([], lst);
						B_TERM ([], base);
						B_TERM ([x;xs], r)])  -> "rec-case " ^ ppRTerm lst ^ " of [] => " ^ ppRTerm base ^ " | " ^ x ^ "." ^ xs ^ " => " ^ ppRTerm r
 | TERM ((("callbyvalueall", _), []),          [B_TERM ([], arg);
						B_TERM ([x], b)])     -> "let " ^ x ^ " := " ^ ppRTerm arg ^ " in " ^ ppRTerm b
 | term -> toStringTerm term

and ppRTerm ref_term = ppTerm (rterm2term ref_term)


(* ------ ACCESSORS ------ *)

 let opr_of_term term =
   match term with
     TERM (((opid, _), params), _) -> (opid,             params)
   | BOT_TERM                      -> ("bottom",         [])
   | AXM_TERM                      -> ("axiom",          [])
   | INT_TERM                      -> ("int",            [])
   | NAT_TERM n                    -> ("natural_number", [(II.to_string n, "n")])
   | ATM_TERM x                    -> ("atom",           match x with Some n -> [(string_of_int n,"n")] | None -> [])
   | TOK_TERM x                    -> ("token",          [x])
   | VAR_TERM v                    -> ("variable",       [(v, "v")])
   | LAM_TERM _                    -> ("lambda",         [])
   | WAI_TERM _                    -> ("!wait",          [])
   | APP_TERM _                    -> ("apply",          [])
   | PAI_TERM _                    -> ("pair",           [])
   | INL_TERM _                    -> ("inl",            [])
   | INR_TERM _                    -> ("inr",            [])
   | FIX_TERM _                    -> ("fix",            [])
   | DEC_TERM _                    -> ("decide",         [])
   | SPR_TERM _                    -> ("spread",         [])
   | IAX_TERM _                    -> ("isaxiom",        [])
   | IPA_TERM _                    -> ("ispair",         [])
   | IEQ_TERM _                    -> ("int_eq",         [])
   | AEQ_TERM _                    -> ("atom_eq",        [])
   | CLO_TERM _                    -> failwith "opr_of_term"

let parameters_of_term term =
 match term with
   TERM (((_, _), params), _) -> params
 | BOT_TERM                   -> []
 | AXM_TERM                   -> []
 | INT_TERM                   -> []
 | ATM_TERM x                 -> (match x with Some n -> [(string_of_int n,"n")] | None -> [])
 | TOK_TERM x                 -> [x]
 | NAT_TERM n                 -> [(II.to_string n,"n")]
 | VAR_TERM v                 -> [(v,"v")]
 | LAM_TERM _                 -> []
 | WAI_TERM _                 -> []
 | APP_TERM _                 -> []
 | PAI_TERM _                 -> []
 | INL_TERM _                 -> []
 | INR_TERM _                 -> []
 | FIX_TERM _                 -> []
 | DEC_TERM _                 -> []
 | SPR_TERM _                 -> []
 | IAX_TERM _                 -> []
 | IPA_TERM _                 -> []
 | IEQ_TERM _                 -> []
 | AEQ_TERM _                 -> []
 | CLO_TERM _                 -> failwith "parameters_of_term"

let bterms_of_term term =
 match term with
   TERM (_, bterms)          -> List.map (fun (B_TERM (vars, rterm)) -> (vars, rterm)) bterms
 | BOT_TERM                  -> []
 | AXM_TERM                  -> []
 | INT_TERM                  -> []
 | ATM_TERM _                -> []
 | TOK_TERM _                -> []
 | NAT_TERM _                -> []
 | VAR_TERM _                -> []
 | LAM_TERM (var, rterm)     -> [([var],rterm)]
 | WAI_TERM (rterm1, rterm2) -> [([],rterm1); ([],rterm2)]
 | APP_TERM (rterm1, rterm2) -> [([],rterm1); ([],rterm2)]
 | PAI_TERM (rterm1, rterm2) -> [([],rterm1); ([],rterm2)]
 | INL_TERM rterm            -> [([],rterm)]
 | INR_TERM rterm            -> [([],rterm)]
 | FIX_TERM rterm            -> [([],rterm)]
 | IAX_TERM (ax,   rterm1, rterm2) -> [([],ax);   ([],rterm1); ([],rterm2)]
 | IPA_TERM (pair, rterm1, rterm2) -> [([],pair); ([],rterm1); ([],rterm2)]
 | IEQ_TERM (a, b, rterm1, rterm2) -> [([],a);    ([],b);      ([],rterm1); ([],rterm2)]
 | AEQ_TERM (a, b, rterm1, rterm2) -> [([],a);    ([],b);      ([],rterm1); ([],rterm2)]
 | DEC_TERM (dec, var1, rterm1, var2, rterm2) -> [([],dec); ([var1],rterm1); ([var2],rterm2)]
 | SPR_TERM (pair, var1, var2, rterm)         -> [([],pair); ([var1;var2],rterm)]
 | CLO_TERM _ -> failwith "bterms_of_term"

let brterms_of_term term =
 match term with
   TERM (_, bterms)          -> List.map (fun (B_TERM (vars, rterm)) -> (vars, rterm2term rterm)) bterms
 | BOT_TERM                  -> []
 | AXM_TERM                  -> []
 | INT_TERM                  -> []
 | ATM_TERM _                -> []
 | TOK_TERM _                -> []
 | NAT_TERM _                -> []
 | VAR_TERM _                -> []
 | LAM_TERM (var, rterm)     -> [([var],rterm2term rterm)]
 | WAI_TERM (rterm1, rterm2) -> [([],rterm2term rterm1); ([],rterm2term rterm2)]
 | APP_TERM (rterm1, rterm2) -> [([],rterm2term rterm1); ([],rterm2term rterm2)]
 | PAI_TERM (rterm1, rterm2) -> [([],rterm2term rterm1); ([],rterm2term rterm2)]
 | INL_TERM rterm            -> [([],rterm2term rterm)]
 | INR_TERM rterm            -> [([],rterm2term rterm)]
 | FIX_TERM rterm            -> [([],rterm2term rterm)]
 | IAX_TERM (ax,   rterm1, rterm2) -> [([],rterm2term ax);   ([],rterm2term rterm1); ([],rterm2term rterm2)]
 | IPA_TERM (pair, rterm1, rterm2) -> [([],rterm2term pair); ([],rterm2term rterm1); ([],rterm2term rterm2)]
 | IEQ_TERM (a, b, rterm1, rterm2) -> [([],rterm2term a);    ([],rterm2term b);      ([],rterm2term rterm1); ([],rterm2term rterm2)]
 | AEQ_TERM (a, b, rterm1, rterm2) -> [([],rterm2term a);    ([],rterm2term b);      ([],rterm2term rterm1); ([],rterm2term rterm2)]
 | DEC_TERM (dec, var1, rterm1, var2, rterm2) -> [([],rterm2term dec); ([var1],rterm2term rterm1); ([var2],rterm2term rterm2)]
 | SPR_TERM (pair, var1, var2, rterm)         -> [([],rterm2term pair); ([var1;var2],rterm2term rterm)]
 | CLO_TERM _ -> failwith "brterms_of_term"

let subterms term =
  match term with
    TERM (_, bterms)          -> List.map (fun (B_TERM (_, rterm)) -> rterm) bterms
  | BOT_TERM                  -> []
  | AXM_TERM                  -> []
  | INT_TERM                  -> []
  | ATM_TERM _                -> []
  | TOK_TERM _                -> []
  | NAT_TERM _                -> []
  | VAR_TERM _                -> []
  | LAM_TERM (var, rterm)     -> [rterm]
  | WAI_TERM (rterm1, rterm2) -> [rterm1; rterm2]
  | APP_TERM (rterm1, rterm2) -> [rterm1; rterm2]
  | PAI_TERM (rterm1, rterm2) -> [rterm1; rterm2]
  | INL_TERM rterm            -> [rterm]
  | INR_TERM rterm            -> [rterm]
  | FIX_TERM rterm            -> [rterm]
  | IAX_TERM (ax,   rterm1, rterm2) -> [ax;   rterm1; rterm2]
  | IPA_TERM (pair, rterm1, rterm2) -> [pair; rterm1; rterm2]
  | IEQ_TERM (a, b, rterm1, rterm2) -> [a; b; rterm1; rterm2]
  | AEQ_TERM (a, b, rterm1, rterm2) -> [a; b; rterm1; rterm2]
  | DEC_TERM (dec, var1, rterm1, var2, rterm2) -> [dec; rterm1; rterm2]
  | SPR_TERM (pair, var1, var2, rterm)         -> [pair; rterm]
  | CLO_TERM _ -> failwith "subterms"

let subtermn n term =
  match term with
    TERM (_, bterm_list) ->
      (try
	(match List.nth bterm_list (n - 1) with
	  B_TERM ([], t) -> rterm2term t
	| _ -> failwith "subtermn")
      with _ -> failwith "subtermn")
  | BOT_TERM   -> failwith "subtermn:BOT_TERM"
  | AXM_TERM   -> failwith "subtermn:AXM_TERM"
  | INT_TERM   -> failwith "subtermn:INT_TERM"
  | ATM_TERM _ -> failwith "subtermn:ATM_TERM"
  | TOK_TERM _ -> failwith "subtermn:TOK_TERM"
  | NAT_TERM _ -> failwith "subtermn:NAT_TERM"
  | VAR_TERM var -> failwith "subtermn:VAR_TERM"
  | LAM_TERM (var, rterm) -> failwith "subtermn:LAM_TERM"
  | WAI_TERM (rterm1, rterm2) ->
      if n = 1
      then rterm2term rterm1
      else if n = 2
      then rterm2term rterm2
      else failwith "subtermn:WAI_TERM"
  | APP_TERM (rterm1, rterm2) ->
      if n = 1
      then rterm2term rterm1
      else if n = 2
      then rterm2term rterm2
      else failwith "subtermn:APP_TERM"
  | PAI_TERM (rterm1, rterm2) ->
      if n = 1
      then rterm2term rterm1
      else if n = 2
      then rterm2term rterm2
      else failwith "subtermn:PAI_TERM"
  | INL_TERM rterm ->
      if n = 1
      then rterm2term rterm
      else failwith "subtermn:INL_TERM"
  | INR_TERM rterm ->
      if n = 1
      then rterm2term rterm
      else failwith "subtermn:INR_TERM"
  | FIX_TERM rterm ->
      if n = 1
      then rterm2term rterm
      else failwith "subtermn:FIX_TERM"
  | IAX_TERM (ax, rterm1, rterm2) ->
      if n = 1
      then rterm2term ax
      else if n = 2
      then rterm2term rterm1
      else if n = 3
      then rterm2term rterm2
      else failwith "subtermn:IAX_TERM"
  | IPA_TERM (pair, rterm1, rterm2) ->
      if n = 1
      then rterm2term pair
      else if n = 2
      then rterm2term rterm1
      else if n = 3
      then rterm2term rterm2
      else failwith "subtermn:IPA_TERM"
  | IEQ_TERM (a, b, rterm1, rterm2) ->
      if n = 1
      then rterm2term a
      else if n = 2
      then rterm2term b
      else if n = 3
      then rterm2term rterm1
      else if n = 4
      then rterm2term rterm2
      else failwith "subtermn:IEQ_TERM"
  | AEQ_TERM (a, b, rterm1, rterm2) ->
      if n = 1
      then rterm2term a
      else if n = 2
      then rterm2term b
      else if n = 3
      then rterm2term rterm1
      else if n = 4
      then rterm2term rterm2
      else failwith "subtermn:AEQ_TERM"
  | DEC_TERM (dec, var1, rterm1, var2, rterm2) ->
      if n = 1
      then rterm2term dec
      else failwith "subtermn:DEC_TERM"
  | SPR_TERM (pair, var1, var2, rterm) ->
      if n = 1
      then rterm2term pair
      else failwith "subtermn:SPR_TERM"
  | CLO_TERM _ -> failwith "subtermn:CLO_TERM"

let subterms_n n bterms =
 try
   (let (vars, rt) = List.nth bterms n in
   rterm2term rt)
 with _ -> failwith "subtermns_n"

let type_of_parameter  (_, kind)  = kind
let value_of_parameter (value, _) = value

let destruct_natural_parameter (value, kind) =
 match kind with
   "n" -> (try (Int.int_of_string value) with _ -> failwith "destruct_natural_parameter")
 | _   -> failwith "destruct_natural_parameter"

let firstnat term = destruct_natural_parameter (List.hd (parameters_of_term term))

let rec get_obid_parameters lst =
 match lst with
   [] -> None
 | ((p,k) :: xs) ->
     if k = "o"
     then Some p
     else get_obid_parameters xs

let sign_to_string (lst1, lst2) =
  "("
  ^ (T.fmt {init  = "[";
	    final = "]";
	    sep   = ",";
	    fmt   =
	    fun (vop, k) ->
	      (match vop with
		Some v -> toStringValue v ^ ":" ^ toStringKind k
	      | None -> "-:" ^ toStringKind k)}
       lst1)
  ^ ","
  ^ (T.fmt {init  = "[";
	    final = "]";
	    sep   = ",";
	    fmt   = string_of_int}
       lst2)
  ^ ")"

let is_abstract_metavar v = Str.string_match (Str.regexp "%a.*") v 0

let getSignature term =
  match term with
    TERM (_, lst) ->
      let params = parameters_of_term term in
      let types  =
	List.map
	  (fun (v, k) ->
	    if is_abstract_metavar v
	    then (None, k)
	    else (Some v, k))
	  params in
      let subs   = List.map (fun (B_TERM (vs, _)) -> List.length vs) lst in
      (types, subs)
  | BOT_TERM   -> failwith "getSignature:BOT_TERM"
  | AXM_TERM   -> failwith "getSignature:AXM_TERM"
  | INT_TERM   -> failwith "getSignature:INT_TERM"
  | ATM_TERM _ -> failwith "getSignature:ATM_TERM"
  | TOK_TERM _ -> failwith "getSignature:TOK_TERM"
  | NAT_TERM _ -> failwith "getSignature:NAT_TERM"
  | VAR_TERM _ -> failwith "getSignature:VAR_TERM"
  | LAM_TERM _ -> failwith "getSignature:LAM_TERM"
  | WAI_TERM _ -> failwith "getSignature:WAI_TERM"
  | APP_TERM _ -> failwith "getSignature:APP_TERM"
  | PAI_TERM _ -> failwith "getSignature:PAI_TERM"
  | INL_TERM _ -> failwith "getSignature:INL_TERM"
  | INR_TERM _ -> failwith "getSignature:INR_TERM"
  | FIX_TERM _ -> failwith "getSignature:FIX_TERM"
  | DEC_TERM _ -> failwith "getSignature:DEC_TERM"
  | SPR_TERM _ -> failwith "getSignature:SPR_TERM"
  | IAX_TERM _ -> failwith "getSignature:IAX_TERM"
  | IPA_TERM _ -> failwith "getSignature:IPA_TERM"
  | IEQ_TERM _ -> failwith "getSignature:IEQ_TERM"
  | AEQ_TERM _ -> failwith "getSignature:AEQ_TERM"
  | CLO_TERM _ -> failwith "getSignature:CLO_TERM"

let eq_kinds (k1, k2) =
  (k1 = "t" && k2 = "token")
|| (k2 = "t" && k1 = "token")
|| k1 = k2

let eq_sign_kinds ((v1, k1), (v2, k2)) =
 (match (v1, v2) with
   (Some a, Some b) -> (a : parameter_value) = b
 | _ -> true)
   &&
 eq_kinds (k1, k2)

let test_bool n b =
  if b
  then true
  else (print_endline ("[BOOL:" ^ string_of_int n ^ "]"); false)

let eq_signs ((kinds1, subs1) : sign) ((kinds2, subs2) : sign) =
  try
    List.for_all eq_sign_kinds (SML_ListPair.zipEq (kinds1, kinds2))
      &&
    subs1 = subs2
  with _ -> false

let string_of_sign (plst, ilst) =
  "("
  ^ T.fmt {init  = "(";
	   final = ")";
	   sep   = ",";
	   fmt   =
	   fun (pvop, pk) ->
	     "("
	     ^ (match pvop with Some pv -> toStringValue pv | None -> "")
	     ^ ","
	     ^ toStringKind pk
	     ^ ")"}
      plst
  ^ ","
  ^ T.fmt {init  = "(";
	   final = ")";
	   sep   = ",";
	   fmt   = string_of_int}
      ilst
  ^ ")"

(* size of a term -- number of nodes *)
let rec size term =
 match term with
   TERM (opr, bterms) ->
     List.fold_right
       (fun bterm n -> n + size_bterm bterm)
       bterms
       1
 | BOT_TERM                  -> 1
 | AXM_TERM                  -> 1
 | INT_TERM                  -> 1
 | ATM_TERM _                -> 1
 | TOK_TERM _                -> 1
 | NAT_TERM _                -> 1
 | VAR_TERM var              -> 1
 | LAM_TERM (var, rterm)     -> 1 + size_rterm rterm
 | WAI_TERM (rterm1, rterm2) -> 1 + size_rterm rterm1 + size_rterm rterm2
 | APP_TERM (rterm1, rterm2) -> 1 + size_rterm rterm1 + size_rterm rterm2
 | PAI_TERM (rterm1, rterm2) -> 1 + size_rterm rterm1 + size_rterm rterm2
 | INL_TERM rterm            -> 1 + size_rterm rterm
 | INR_TERM rterm            -> 1 + size_rterm rterm
 | FIX_TERM rterm            -> 1 + size_rterm rterm
 | IAX_TERM (ax,   rterm1, rterm2) -> 1 + size_rterm ax   + size_rterm rterm1 + size_rterm rterm2
 | IPA_TERM (pair, rterm1, rterm2) -> 1 + size_rterm pair + size_rterm rterm1 + size_rterm rterm2
 | IEQ_TERM (a, b, rterm1, rterm2) -> 1 + size_rterm a    + size_rterm b      + size_rterm rterm1 + size_rterm rterm2
 | AEQ_TERM (a, b, rterm1, rterm2) -> 1 + size_rterm a    + size_rterm b      + size_rterm rterm1 + size_rterm rterm2
 | DEC_TERM (dec, var1, rterm1, var2, rterm2) -> 1 + size_rterm dec + size_rterm rterm1 + size_rterm rterm2
 | SPR_TERM (pair, var1, var2, rterm)         -> 1 + size_rterm pair + size_rterm rterm
 | CLO_TERM (rterm, env)                      -> size_clos (rterm, env)

and size_rterm rterm = size (rterm2term rterm)

and size_bterm (B_TERM (vars, rterm)) = size_rterm rterm

and size_clos (rterm, env) = size_rterm rterm + size_env env

and size_env (ENV env) = ENV_MAP.fold (fun i rterm n -> size_rterm rterm + n) env 0


(* size of a term -- number of nodes -- uses IntInf *)
let rec large_size term =
 match term with
   TERM (opr, bterms) ->
     List.fold_right
       (fun bterm n -> Big_int.add_big_int n (large_size_bterm bterm))
       bterms
       Big_int.unit_big_int
 | BOT_TERM                  -> Big_int.unit_big_int
 | AXM_TERM                  -> Big_int.unit_big_int
 | INT_TERM                  -> Big_int.unit_big_int
 | ATM_TERM _                -> Big_int.unit_big_int
 | TOK_TERM _                -> Big_int.unit_big_int
 | NAT_TERM _                -> Big_int.unit_big_int
 | VAR_TERM var              -> Big_int.unit_big_int
 | LAM_TERM (var, rterm)     -> Big_int.add_big_int Big_int.unit_big_int (large_size_rterm rterm)
 | WAI_TERM (rterm1, rterm2) -> Big_int.add_big_int Big_int.unit_big_int (Big_int.add_big_int (large_size_rterm rterm1) (large_size_rterm rterm2))
 | APP_TERM (rterm1, rterm2) -> Big_int.add_big_int Big_int.unit_big_int (Big_int.add_big_int (large_size_rterm rterm1) (large_size_rterm rterm2))
 | PAI_TERM (rterm1, rterm2) -> Big_int.add_big_int Big_int.unit_big_int (Big_int.add_big_int (large_size_rterm rterm1) (large_size_rterm rterm2))
 | INL_TERM rterm            -> Big_int.add_big_int Big_int.unit_big_int (large_size_rterm rterm)
 | INR_TERM rterm            -> Big_int.add_big_int Big_int.unit_big_int (large_size_rterm rterm)
 | FIX_TERM rterm            -> Big_int.add_big_int Big_int.unit_big_int (large_size_rterm rterm)
 | IAX_TERM (ax,   rterm1, rterm2) -> Big_int.add_big_int Big_int.unit_big_int (Big_int.add_big_int (large_size_rterm ax)   (Big_int.add_big_int (large_size_rterm rterm1) (large_size_rterm rterm2)))
 | IPA_TERM (pair, rterm1, rterm2) -> Big_int.add_big_int Big_int.unit_big_int (Big_int.add_big_int (large_size_rterm pair) (Big_int.add_big_int (large_size_rterm rterm1) (large_size_rterm rterm2)))
 | IEQ_TERM (a, b, rterm1, rterm2) -> Big_int.add_big_int Big_int.unit_big_int (Big_int.add_big_int (large_size_rterm a) (Big_int.add_big_int (large_size_rterm b) (Big_int.add_big_int (large_size_rterm rterm1) (large_size_rterm rterm2))))
 | AEQ_TERM (a, b, rterm1, rterm2) -> Big_int.add_big_int Big_int.unit_big_int (Big_int.add_big_int (large_size_rterm a) (Big_int.add_big_int (large_size_rterm b) (Big_int.add_big_int (large_size_rterm rterm1) (large_size_rterm rterm2))))
 | DEC_TERM (dec, var1, rterm1, var2, rterm2) -> Big_int.add_big_int Big_int.unit_big_int (Big_int.add_big_int (large_size_rterm dec) (Big_int.add_big_int (large_size_rterm rterm1) (large_size_rterm rterm2)))
 | SPR_TERM (pair, var1, var2, rterm)         -> Big_int.add_big_int Big_int.unit_big_int (Big_int.add_big_int (large_size_rterm pair) (large_size_rterm rterm))
 | CLO_TERM (rterm, env)                      -> large_size_clos (rterm, env)

and large_size_rterm rterm = large_size (rterm2term rterm)

and large_size_bterm (B_TERM (vars, rterm)) = large_size_rterm rterm

and large_size_clos (rterm, env) =
  Big_int.add_big_int (large_size_rterm rterm) (large_size_env env)

and large_size_env (ENV env) =
 ENV_MAP.fold
    (fun i rterm n -> Big_int.add_big_int (large_size_rterm rterm) n)
    env
    Big_int.zero_big_int


(* size of the environment of a term term *)
let rec env_size term =
 match term with
   TERM (opr, bterms)        -> List.fold_right (fun bterm n -> n + env_size_bterm bterm) bterms 0
 | BOT_TERM                  -> 0
 | AXM_TERM                  -> 0
 | INT_TERM                  -> 0
 | ATM_TERM _                -> 0
 | TOK_TERM _                -> 0
 | NAT_TERM _                -> 0
 | VAR_TERM var              -> 0
 | LAM_TERM (var, rterm)     -> env_size_rterm rterm
 | WAI_TERM (rterm1, rterm2) -> env_size_rterm rterm1 + env_size_rterm rterm2
 | APP_TERM (rterm1, rterm2) -> env_size_rterm rterm1 + env_size_rterm rterm2
 | PAI_TERM (rterm1, rterm2) -> env_size_rterm rterm1 + env_size_rterm rterm2
 | INL_TERM rterm            -> env_size_rterm rterm
 | INR_TERM rterm            -> env_size_rterm rterm
 | FIX_TERM rterm            -> env_size_rterm rterm
 | IAX_TERM (ax,   rterm1, rterm2) -> env_size_rterm ax   + env_size_rterm rterm1 + env_size_rterm rterm2
 | IPA_TERM (pair, rterm1, rterm2) -> env_size_rterm pair + env_size_rterm rterm1 + env_size_rterm rterm2
 | IEQ_TERM (a, b, rterm1, rterm2) -> env_size_rterm a + env_size_rterm b + env_size_rterm rterm1 + env_size_rterm rterm2
 | AEQ_TERM (a, b, rterm1, rterm2) -> env_size_rterm a + env_size_rterm b + env_size_rterm rterm1 + env_size_rterm rterm2
 | DEC_TERM (dec, var1, rterm1, var2, rterm2) -> env_size_rterm dec + env_size_rterm rterm1 + env_size_rterm rterm2
 | SPR_TERM (pair, var1, var2, rterm)         -> env_size_rterm pair + env_size_rterm rterm
 | CLO_TERM (rterm, env)                      -> env_size_clos (rterm, env)

and env_size_rterm rterm = env_size (rterm2term rterm)

and env_size_bterm (B_TERM (vars, rterm)) = env_size_rterm rterm

and env_size_clos (rterm, env) = env_size_rterm rterm + size_env env


(* depth of a term *)
let rec env_depth term =
 match term with
   TERM (opr, bterms)        ->
     List.fold_right (fun bterm n -> Int.max n (env_depth_bterm bterm)) bterms 0
 | AXM_TERM                  -> 0
 | BOT_TERM                  -> 0
 | INT_TERM                  -> 0
 | NAT_TERM _                -> 0
 | ATM_TERM _                -> 0
 | TOK_TERM _                -> 0
 | VAR_TERM var              -> 0
 | LAM_TERM (var, rterm)     -> env_depth_rterm rterm
 | WAI_TERM (rterm1, rterm2) -> env_depth_rterm rterm1 + env_depth_rterm rterm2
 | APP_TERM (rterm1, rterm2) -> env_depth_rterm rterm1 + env_depth_rterm rterm2
 | PAI_TERM (rterm1, rterm2) -> env_depth_rterm rterm1 + env_depth_rterm rterm2
 | INL_TERM rterm            -> env_depth_rterm rterm
 | INR_TERM rterm            -> env_depth_rterm rterm
 | FIX_TERM rterm            -> env_depth_rterm rterm
 | DEC_TERM (dec, var1, rterm1, var2, rterm2) -> env_depth_rterm dec + env_depth_rterm rterm1 + env_depth_rterm rterm2
 | SPR_TERM (pair, var1, var2, rterm)         -> env_depth_rterm pair + env_depth_rterm rterm
 | IAX_TERM (ax,   rterm1, rterm2) -> env_depth_rterm ax   + env_depth_rterm rterm1 + env_depth_rterm rterm2
 | IPA_TERM (pair, rterm1, rterm2) -> env_depth_rterm pair + env_depth_rterm rterm1 + env_depth_rterm rterm2
 | IEQ_TERM (a, b, rterm1, rterm2) -> env_depth_rterm a + env_depth_rterm b + env_depth_rterm rterm1 + env_depth_rterm rterm2
 | AEQ_TERM (a, b, rterm1, rterm2) -> env_depth_rterm a + env_depth_rterm b + env_depth_rterm rterm1 + env_depth_rterm rterm2
 | CLO_TERM (rterm, env)           -> env_depth_clos (rterm, env)

and env_depth_rterm rterm = env_depth (rterm2term rterm)

and env_depth_bterm (B_TERM (vars, rterm)) = env_depth_rterm rterm

and env_depth_clos (rterm, env) =
 Int.max (env_depth_rterm rterm) (env_depth_env env + 1)

and env_depth_env (ENV env) =
 ENV_MAP.fold (fun i rterm n -> Int.max (env_depth_rterm rterm) n) env 0


(* ------ CHECKERS ------ *)

let is_nuprl_term token term = (opid_of_term term = token)
let is_nuprl_ref_term token rterm = is_nuprl_term token (rterm2term rterm)

let is_nuprl_minus_term          = is_nuprl_term "minus"
let is_nuprl_type_term           = is_nuprl_term "universe"
let is_nuprl_function_term       = is_nuprl_term "function"
let is_nuprl_iwf_lemmas_term     = is_nuprl_term "!wf"
let is_nuprl_iabstraction_term   = is_nuprl_term "!abstraction"
let is_nuprl_int_term            = is_nuprl_term "int"
let is_nuprl_loc_term            = is_nuprl_term "Id"
let is_nuprl_atom_term           = is_nuprl_term "atom"
let is_nuprl_list_term           = is_nuprl_term "list"
let is_nuprl_bool_term           = is_nuprl_term "bool"
let is_nuprl_unit_term           = is_nuprl_term "unit"
let is_nuprl_product_term        = is_nuprl_term "product"
let is_nuprl_select_term         = is_nuprl_term "select"
let is_nuprl_iclosure_term       = is_nuprl_term "!closure"
let is_nuprl_eclass_term         = is_nuprl_term "eclass"
let is_nuprl_iabstraction_term   = is_nuprl_term "!abstraction"
let is_nuprl_all_term            = is_nuprl_term "all"
let is_nuprl_uall_term           = is_nuprl_term "uall"
let is_nuprl_bag_term            = is_nuprl_term "bag"
let is_nuprl_eqof_term           = is_nuprl_term "eqof"
let is_nuprl_eq_int_term         = is_nuprl_term "eq_int"
let is_nuprl_eq_id_term          = is_nuprl_term "eq_id"
let is_nuprl_cons_term           = is_nuprl_term "cons"
let is_nuprl_nil_term            = is_nuprl_term "nil"
let is_nuprl_it_term             = is_nuprl_term "it"

let is_nuprl_iwftheorem_term term =
 match term with
   TERM ((("!theorem", _), [(name, "t")]), [B_TERM ([], theorem)]) ->
     Str.string_match (Str.regexp ".*_wf") name 0
 | _ -> false

let equal_parameters param1 param2 = (param1 : parameter) = param2


(* ------ LIBRARY HANDLING ------ *)

let to_keep =
  ["NI_Auto";
   "isect_1";
   "core_2";
   "well_fnd";
   "int_1";
   "bool_1";
   "union";
   "subtype_0";
   "sqequal_1";
   "fun_1";
   "rfunction_1";
   "rel_1";
   "quot_1";
   "int_2";
   "list_1";
   "prog_1";
   "subtype_1";
   "num_thy_1";
   "basic";
   "tree_1";
   "nat_extra";
   "list+";
   "sets_1";
   "list_2";
   "list_3";
   "call by value";
   "general";
   "atoms";
   "decidable-equality";
   "event-ordering";
   "process-model";
   "event-logic-applications";
   "event-structures2";
   "event-system"]

let to_filter_out =
  ["test";
   "DivA";
   "ppcc";
   "gen_algebra_1";
   "groups_1";
   "rings_1";
   "algebras_1";
   "perms_1";
   "perms_2";
   "factor_1";
   "mset";
   "basic-tactics";
   "tactics";
   "polynom_1";
   "polynom_2";
   "polynom_3";
   "polynom_4";
   "rationals";
   "reals";
   "better\\ polynomials";
   "polynomials";
   "randomness";
   "realizability";
   "FullyIntensional";
   "concrete-message-automata";
   "dependent\\ intersection";
   "message-automata"]


let isin_str str lst = List.exists (fun s -> s = str) lst

let rec filter_library lst terms =
  match terms with
    [] -> []
  | (TERM (((opid, tag), []), b_terms) as term) :: terms ->
      if get_tag tag = "t"
      then if isin_str opid lst
      then filter_library lst terms
      else term :: filter_library lst terms
      else failwith "filter_library"
  | _ -> failwith "filter_library"

let emlib () : lib = {abs = ref MAP.empty; tof = ref MAP.empty}

let union_libs ({abs = abs1; tof = tof1} : lib) ({abs = abs2; tof = tof2} : lib) =
  {abs = ref (MAP.merge
		(fun id x y ->
		  (match x, y with
		    Some lst1, Some lst2 -> Some (lst1 @ lst2)
		  | Some lst,  None      -> Some lst
		  | None,      Some lst  -> Some lst
		  | None,      None      -> None))
		(!abs1)
		(!abs2));
   tof = ref (MAP.merge
		(fun id x y ->
		  (match x, y with
		    Some lst1, Some lst2 -> Some lst2
		  | Some lst,  None      -> Some lst
		  | None,      Some lst  -> Some lst
		  | None,      None      -> None))
		(!tof1)
		(!tof2))}

let mk_item id sign obid lhs rhs wfs =
  {id  = id;
   sign = sign;
   obid = obid;
   lhs  = lhs;
   rhs  = rhs;
   wfs  = wfs}

let item_to_string {id; sign; obid; lhs; rhs; wfs} =
  "{"
  ^ id
  ^ ";"
  ^ sign_to_string sign
  ^ "}"

let items_to_string items =
    T.fmt {init  = "[";
	   sep   = "; ";
	   final = "]";
	   fmt   = fun x -> item_to_string (TR.get x)}
    items

let insert_abs ({abs; tof} as lib) id info =
  let a = !abs in
  let _ =
    try (abs := MAP.add id ((TR.mk info) :: (MAP.find id a)) a)
    with _ -> abs := MAP.add id [TR.mk info] a
  in lib

let insert_tof ({abs; tof} as lib) obid rhs =
  (tof := MAP.add obid (TR.mk rhs) (!tof); lib)

let rec term2map term =
  match term with
    TERM (((id, tag), [(obid, "o")]),
	  [B_TERM ([], lhs);
	   B_TERM ([], rhs);
	   B_TERM ([], wfs)]) ->
	     if get_tag tag = "t"
	     then
	       let trhs  = rterm2term rhs in
	       if is_nuprl_term "!primitive" trhs
	       then None
	       else
		 let tlhs = rterm2term lhs    in
		 let twfs = rterm2term wfs    in
		 let opid = opid_of_term tlhs in
		 let sign = getSignature tlhs in
		 let subs = subterms twfs     in
		 let item = mk_item id sign obid lhs rhs subs in
		 Some (ABS (opid, item))
	     else failwith "wrong format:term2map:abs"
  | TERM (((id, tag), [(obid, "o")]),
	  [B_TERM ([], termof);
	   B_TERM ([], extract)]) ->
	     if get_tag tag = "t"
	     then
	       let ttermof = rterm2term termof in
	       if is_nuprl_term "TERMOF" ttermof
	       then
		 match get_obid_parameters (parameters_of_term ttermof) with
		   Some oid ->
		     if oid = obid
		     then Some (TOF (oid, rterm2term extract))
		     else failwith "wrong object identifier"
		 | None -> None
	       else None
	     else failwith "wrong format:term2map:termof"
  | _ -> failwith "wrong format:term2map"

and b_terms2map bterms =
 match bterms with
   [] -> emlib ()
 | (B_TERM ([], term)) :: b_terms ->
     (match term2map (rterm2term term) with
       Some (ABS (opid, item)) ->
	 insert_abs (b_terms2map b_terms) opid item
     | Some (TOF (oid, rhs)) ->
	 insert_tof (b_terms2map b_terms) oid rhs
     | None -> b_terms2map b_terms)
 | _ -> failwith "wrong format:b_terms2map"

and terms2map terms =
 match terms with
   [] -> emlib ()
 |  (TERM (((opid, tag), []), b_terms)) :: terms ->
     if get_tag tag = "t"
     then
       (*let _    = print_string ("[loading " ^ opid ^ " theory]\n") in*)
       let map1 = b_terms2map b_terms in
       let map2 = terms2map terms in
       union_libs map1 map2
     else failwith ("wrong format:terms2map:lib" ^ get_tag tag ^ "-")
 | _ -> failwith "wrong format:terms2map"

and terms2map' terms =
 match terms with
   [] -> emlib ()
 | (TERM (((opid, tag), []), b_terms)) :: terms ->
     if get_tag tag = "t"
     then if isin_str opid to_filter_out
     then ((*print_string ("[not loading " ^ opid ^ " theory]\n");*) terms2map' terms)
     else
       let map1 = b_terms2map b_terms in
       let map2 = terms2map' terms in
       union_libs map1 map2
     else failwith "wrong format:terms2map':lib"
 | _ -> failwith "wrong format:terms2map'"

let find_sign abs term =
 let sign = getSignature term in
 let opid = opid_of_term term in
 let aux ritem =
   let {id; sign = sign'; obid; lhs; rhs; wfs} = TR.get ritem in
   not (is_nuprl_ref_term "!primitive" rhs)
     &&
   eq_signs sign sign' in
 try TR.get (List.find aux (MAP.find opid (!abs)))
 with _ -> failwith ("find_sign:" ^ opid ^ "-not-in-lib-or-wrong-signature")

let find_sign_tup abs term =
 let {id; sign; obid; lhs; rhs; wfs} = find_sign abs term in
 (id, sign, obid, lhs, rhs, wfs)

(* ------ DESTRUCTORS ------ *)

let dest_simple_term term =
 let opid  = opid_of_term term in
 let terms =
   List.map
     (fun (lst, rterm) ->
       match lst with
	 [] -> rterm
       | _  -> (print_string (toStringRTerm rterm); failwith "dest_simple_term"))
     (bterms_of_term term) in
 (opid, terms)

let dest_simple_null_term term =
 let opid  = opid_of_term term in
 let terms =
   List.map
     (fun (lst, rterm) ->
       match lst with
	 []   -> rterm
       | [""] -> rterm
       | _    -> (print_string (toStringRTerm rterm); failwith "dest_simple_null_term"))
     (bterms_of_term term) in
 (opid, terms)

let dest_term term =
 ((opid_of_term term, parameters_of_term term), bterms_of_term term)

let full_dest_term term =
 match term with
   TERM (((opid, _), params), bterms) ->
     ((opid, params), List.map (fun (B_TERM (vars, rterm)) -> (vars, rterm2term rterm)) bterms)
 | AXM_TERM                  -> failwith "full_dest_term:AXM_TERM"
 | BOT_TERM                  -> failwith "full_dest_term:BOT_TERM"
 | INT_TERM                  -> failwith "full_dest_term:INT_TERM"
 | NAT_TERM _                -> failwith "full_dest_term:NAT_TERM"
 | ATM_TERM _                -> failwith "full_dest_term:ATM_TERM"
 | TOK_TERM _                -> failwith "full_dest_term:TOK_TERM"
 | VAR_TERM var              -> failwith "full_dest_term:VAR_TERM"
 | LAM_TERM (var, rterm)     -> failwith "full_dest_term:LAM_TERM"
 | WAI_TERM (rterm1, rterm2) -> failwith "full_dest_term:WAI_TERM"
 | APP_TERM (rterm1, rterm2) -> failwith "full_dest_term:APP_TERM"
 | PAI_TERM (rterm1, rterm2) -> failwith "full_dest_term:PAI_TERM"
 | INL_TERM rterm            -> failwith "full_dest_term:INL_TERM"
 | INR_TERM rterm            -> failwith "full_dest_term:INR_TERM"
 | FIX_TERM rterm            -> failwith "full_dest_term:FIX_TERM"
 | DEC_TERM (dec, v1, rterm1, v2, rterm2) -> failwith "full_dest_term:DEC_TERM"
 | SPR_TERM (pair, v1, v2, rterm)         -> failwith "full_dest_term:SPR_TERM"
 | IAX_TERM (ax,   rterm1, rterm2) -> failwith "full_dest_term:IAX_TERM"
 | IPA_TERM (pair, rterm1, rterm2) -> failwith "full_dest_term:IPA_TERM"
 | IEQ_TERM (a, b, rterm1, rterm2) -> failwith "full_dest_term:IEQ_TERM"
 | AEQ_TERM (a, b, rterm1, rterm2) -> failwith "full_dest_term:AEQ_TERM"
 | CLO_TERM _                      -> failwith "full_dest_term:CLO_TERM"

let rec dest_lambdas term =
 if is_nuprl_lambda_term term
 then
   match bterms_of_term term with
     [([x], b)] ->
       let (bounds, body) = dest_lambdas (rterm2term b)
       in (x :: bounds, body)
   | _ -> failwith "dest_lambdas"
 else ([], term)

let rec dest_alls_ualls term =
 let b = is_nuprl_all_term term in
 if b || is_nuprl_uall_term term
 then
   match bterms_of_term term with
     [([], typ); ([x], body)] ->
       let (bounds, body) = dest_alls_ualls (rterm2term body)
       in ((x, rterm2term typ, b) :: bounds, body)
   | _ -> failwith "dest_alls_ualls"
 else ([], term)

let dest_so_variable term =
 match term with
   TERM ((("variable", _), [(var, "v")]), bterms) ->
     (var,
      List.map
	(fun (B_TERM (vars, rt)) ->
	  match vars with
	    [] -> rterm2term rt
	  | _  -> failwith "dest_so_variable")
	bterms)
 | _ -> failwith "dest_so_variable"

let dest_eclass term =
 match term with
   TERM ((("eclass", tag), params),
	 [B_TERM ([],      info);
	  B_TERM ([es; e], x)]) -> (rterm2term info, es, e, rterm2term x)
 | _ -> failwith "dest_eclass"

let dest_let term =
 match term with
   TERM ((("let", tag), params),
	 [B_TERM ([],  exp1);
	  B_TERM ([v], exp2)]) -> (rterm2term exp1, v, rterm2term exp2)
 | _ -> failwith "dest_let"

let dest_function term =
 match term with
   TERM ((("function", tag), params),
	 [B_TERM ([],   term1);
	  B_TERM ([""], term2)]) -> (rterm2term term1, rterm2term term2)
 | _ -> failwith "dest_function"

let rec dest_functions term =
 if is_nuprl_function_term term
 then
   let (t1, t2) = dest_function term in
   let (lst, t) = dest_functions t2 in
   (t1 :: lst, t)
 else ([], term)

let dest_product term =
 match term with
   TERM ((("product", tag), params),
	 [B_TERM ([],   term1);
	  B_TERM ([""], term2)]) -> (rterm2term term1, rterm2term term2)
 | _ -> failwith "dest_product"

let dest_iabstraction term =
 match term with
   TERM ((("!abstraction", tag), []),
	 [B_TERM ([], t1);
	  B_TERM ([], t2);
	  B_TERM ([], t3)]) -> (t1, t2, t3)
 | _ -> failwith "dest_iabstraction"

let dest_iwftheorem term =
 match term with
   TERM ((("!theorem", _), [(name, "t")]),
	 [B_TERM ([], theorem)]) -> rterm2term theorem
 | _ -> failwith "dest_iwftheorem"

let gen_dest_single term str msg =
 match term with
   TERM (((opid, tag), parms), [B_TERM ([], term)]) ->
     if opid = str
     then rterm2term term
     else failwith msg
 | _ -> failwith msg

let dest_minus        term = gen_dest_single term "minus"        "dest_minus"
let dest_bnot         term = gen_dest_single term "bnot"         "dest_bnot"
let dest_bag          term = gen_dest_single term "bag"          "dest_bag"
let dest_type_list    term = gen_dest_single term "list"         "dest_type_list"
let dest_eqof         term = gen_dest_single term "eqof"         "dest_eqof"
let dest_primed_class term = gen_dest_single term "primed-class" "dest_primed_class"
let dest_es_eq        term = gen_dest_single term "es-eq"        "dest_es_eq"

let dest_integer m term =
 try
   (if is_nuprl_natural_number_term term
   then dest_natural_number term
   else if is_nuprl_minus_term term
   then - (dest_natural_number (dest_minus term))
   else failwith "dest_integer")
 with Failure str -> failwith ("dest_integer:not-int-"
			       ^ Int.string_of_int m
			       ^ "("
			       ^ toStringTerm term
			       ^ ")"
			       ^ str)

let dest_small_integer term = II.to_int (dest_integer 1 term)

let dest_iport term =
 match term with
   TERM ((("!port", tag), [(str, "n")]), []) ->
     (try II.to_int (II.of_string str)
     with _ -> failwith ("dest_integer:not-int-in-string(" ^ str ^ ")"))
 | _ -> failwith "dest_iport"

let dest_ihost term =
 match term with
   TERM ((("!host", tag), [(x, "s")]), []) -> x
 | _ -> failwith "dest_ihost"

let dest_rec_comb term =
 match term with
   TERM ((("rec-comb", tag), []),
	 [B_TERM ([], xs);
	  B_TERM ([], f);
	  B_TERM ([], init)]) -> (rterm2term xs, rterm2term f, rterm2term init)
 | _ -> failwith "dest_rec_comb"

let gen_dest_pair term str msg =
 match term with
   TERM (((opid, tag), params),
	 [B_TERM ([], term1);
	  B_TERM ([], term2)]) ->
	    if opid = str
	    then (rterm2term term1, rterm2term term2)
	    else failwith msg
 | _ -> failwith msg

let dest_select    term = gen_dest_pair term "select"    "dest_select"
let dest_prior_prc term = gen_dest_pair term "prior-prc" "dest_prior_prc"
let dest_iclosure  term = gen_dest_pair term "!closure"  "dest_iclosure"
let dest_lt_int    term = gen_dest_pair term "lt_int"    "dest_lt_int"
let dest_le_int    term = gen_dest_pair term "le_int"    "dest_le_int"
let dest_eq_int    term = gen_dest_pair term "eq_int"    "dest_eq_int"
let dest_eq_id     term = gen_dest_pair term "eq_id"     "dest_eq_id"
let dest_band      term = gen_dest_pair term "band"      "dest_band"
let dest_member    term = gen_dest_pair term "member"    "dest_member"
let dest_cons      term = gen_dest_pair term "cons"      "dest_cons"

let rec dest_list term =
 if is_nuprl_cons_term term
 then
   let (h,t) = dest_cons term
   in h :: (dest_list t)
 else if is_nuprl_pair_term term
 then
   let (h,t) = dest_pair 21 term
   in h :: (dest_list t)
 else
   if is_nuprl_nil_term term
     || is_nuprl_it_term term
     || is_nuprl_axiom_term term
   then []
   else failwith "dest_list"

let rec dest_applies term =
 match term with
   TERM ((("apply", tag), []),
	 [B_TERM ([], f);
	  B_TERM ([], arg)]) ->
	    let (x, xs) = dest_applies (rterm2term f)
	    in (x, xs @ [rterm2term arg])
 | _ -> (term, [])

let is_nuprl_minus_natural_number_term term =
 is_nuprl_minus_term term
   &&
 is_nuprl_natural_number_term (dest_minus term)

let is_nuprl_integer_term term =
 is_nuprl_natural_number_term term
|| is_nuprl_minus_natural_number_term term

let is_nuprl_event_orderingp_term lvl term =
 match term with
   TERM ((("event-ordering+", tag), [(l,_)]), [B_TERM ([], info)]) -> (l = lvl)
 | _ -> false

let is_nuprl_prop_term lvl term =
 match term with
   TERM ((("prop", tag), [(l,_)]), []) -> (l = lvl)
 | _ -> false


(* ------ CONSTRUCTORS ------ *)

let mk_nuprl_small_natural_number_term int = mk_natural_number_term (II.of_int int)

let mk_nuprl_minus_term term = mk_nuprl_simple_term "minus" [term]

let mk_nuprl_df_program_meaning_term term =
 mk_nuprl_simple_term "df-program-meaning" [term]

let mk_nuprl_axiom_term = mk_nuprl_simple_term "axiom" []

let mk_nuprl_ihost_term host =
 TERM ((("!host", dtag), [mk_nuprl_string_parameter host]), [])

let mk_nuprl_iport_term port =
 TERM ((("!port", dtag), [mk_nuprl_natural_parameter (II.of_int port)]), [])

let mk_nuprl_integer_term i =
 if II.to_int i < 0
 then mk_nuprl_minus_term (mk_natural_number_term i)
 else mk_natural_number_term i

let mk_nuprl_int_from_string str =
 try mk_nuprl_integer_term (II.of_string str)
 with _ -> failwith "mk_nuprl_int_from_string"

(*
(* This is a crude hack!! *)
let mk_nuprl_real_from_string str =
case Real.fromString str of
    None   => raise Fail "mk_nuprl_real_from_string"
  | Some r => mk_nuprl_integer_term (Real.toLargeInt (IEEEReal.getRoundingMode ()) r)
*)

let mk_nuprl_small_integer_term int = mk_nuprl_integer_term (II.of_int int)

let mk_nuprl_applies_term func args =
 List.fold_left
   (fun f arg -> mk_nuprl_simple_term "apply" [f; arg])
   func
   args

let mk_nuprl_let_term var pat body =
 mk_nuprl_term ("let", []) [([], pat); ([var], body)]

let mk_nuprl_rec_term var term = mk_nuprl_term ("rec", []) [([var], term)]

let mk_nuprl_lambdas_term vars term =
  List.fold_right
    mk_lambda_term
    vars
    term

let mk_nuprl_spreadn_term pair (vars, bterm) =
 match vars with
   []       -> failwith "mk_nuprl_spreadn_term:empty_bvars"
 | [_]      -> failwith ""
 | [v1; v2] -> mk_spread_term pair (v1, v2, bterm)
 | _        -> mk_nuprl_term ("spreadn", []) [([], pair); (vars, bterm)]

let mk_nuprl_isl_term  term = mk_nuprl_simple_term "isl"  [term]
let mk_nuprl_isr_term  term = mk_nuprl_simple_term "isr"  [term]
let mk_nuprl_outl_term term = mk_nuprl_simple_term "outl" [term]
let mk_nuprl_outr_term term = mk_nuprl_simple_term "outr" [term]

let mk_nuprl_ycomb_term = mk_nuprl_simple_term "ycomb" []

let mk_nuprl_genrec_term (n, r, b) =
 mk_nuprl_term ("genrec", []) [([n; r], b)]

let mk_nuprl_bind_class_term f (x, g) =
 mk_nuprl_term ("bind-class", []) [([], f); ([x], g)]

let mk_nuprl_combined_class_term         f lst = mk_nuprl_simple_term "simple-comb"            [f; lst]
let mk_nuprl_rec_combined_class_term     f lst = mk_nuprl_simple_term "rec-combined-class"     [lst; f]
let mk_nuprl_combined_loc_class_term     f lst = mk_nuprl_simple_term "simple-loc-comb"        [f; lst]
let mk_nuprl_rec_combined_loc_class_term f lst = mk_nuprl_simple_term "rec-combined-loc-class" [lst; f]

let mk_nuprl_rec_comb_term f classes init = mk_nuprl_simple_term "rec-comb" [classes; f; init]

let mk_nuprl_so_apply1_term f x     = mk_nuprl_simple_term "so_apply" [f; x]
let mk_nuprl_so_apply2_term f x y   = mk_nuprl_simple_term "so_apply" [f; x; y]
let mk_nuprl_so_apply3_term f x y z = mk_nuprl_simple_term "so_apply" [f; x; y; z]

let mk_nuprl_combined0_class_term bag =
 mk_nuprl_simple_term "simple-comb-0" [bag]
let mk_nuprl_combined1_class_term f cls =
 mk_nuprl_simple_term "simple-comb-1" [f; cls]
let mk_nuprl_combined2_class_term f cls1 cls2 =
 mk_nuprl_simple_term "simple-comb-2" [f; cls1; cls2]
let mk_nuprl_combined3_class_term f cls1 cls2 cls3 =
 mk_nuprl_simple_term "simple-comb-3" [f; cls1; cls2; cls3]

let mk_nuprl_combined0_loc_class_term bag =
 mk_nuprl_simple_term "simple-loc-comb-0" [bag]
let mk_nuprl_combined1_loc_class_term f cls =
 mk_nuprl_simple_term "simple-loc-comb-1" [f; cls]
let mk_nuprl_combined2_loc_class_term f cls1 cls2 =
 mk_nuprl_simple_term "simple-loc-comb-2" [f; cls1; cls2]
let mk_nuprl_combined3_loc_class_term f cls1 cls2 cls3 =
 mk_nuprl_simple_term "simple-loc-comb-3" [f; cls1; cls2; cls3]

let mk_nuprl_rec_combined0_class_term bag =
 mk_nuprl_simple_term "rec-combined-class-0" [bag]
let mk_nuprl_rec_combined1_class_term f cls =
 mk_nuprl_simple_term "rec-combined-class-1" [f; cls]
let mk_nuprl_rec_combined2_class_term f cls1 cls2 =
 mk_nuprl_simple_term "rec-combined-class-2" [f; cls1; cls2]
let mk_nuprl_rec_combined3_class_term f cls1 cls2 cls3 =
 mk_nuprl_simple_term "rec-combined-class-3" [f; cls1; cls2; cls3]

let mk_nuprl_rec_combined0_class_opt_term opt bag =
 mk_nuprl_simple_term "rec-combined-class-opt-0" [bag; opt]
let mk_nuprl_rec_combined1_class_opt_term opt f cls =
 mk_nuprl_simple_term "rec-combined-class-opt-1" [f; opt; cls]
let mk_nuprl_rec_combined2_class_opt_term opt f cls1 cls2 =
 mk_nuprl_simple_term "rec-combined-class-opt-2" [f; opt; cls1; cls2]
let mk_nuprl_rec_combined3_class_opt_term opt f cls1 cls2 cls3 =
 mk_nuprl_simple_term "rec-combined-class-opt-3" [f; opt; cls1; cls2; cls3]

let mk_nuprl_rec_combined0_loc_class_term bag =
 mk_nuprl_simple_term "rec-combined-loc-class-0" [bag]
let mk_nuprl_rec_combined1_loc_class_term f cls =
 mk_nuprl_simple_term "rec-combined-loc-class-1" [f; cls]
let mk_nuprl_rec_combined2_loc_class_term f cls1 cls2 =
 mk_nuprl_simple_term "rec-combined-loc-class-2" [f; cls1; cls2]
let mk_nuprl_rec_combined3_loc_class_term f cls1 cls2 cls3 =
 mk_nuprl_simple_term "rec-combined-loc-class-3" [f; cls1; cls2; cls3]

let mk_nuprl_rec_combined0_loc_class_opt_term opt bag =
 mk_nuprl_simple_term "rec-combined-loc-class-opt-0" [bag; opt]
let mk_nuprl_rec_combined1_loc_class_opt_term opt f cls =
 mk_nuprl_simple_term "rec-combined-loc-class-opt-1" [f; opt; cls]
let mk_nuprl_rec_combined2_loc_class_opt_term opt f cls1 cls2 =
 mk_nuprl_simple_term "rec-combined-loc-class-opt-2" [f; opt; cls1; cls2]
let mk_nuprl_rec_combined3_loc_class_opt_term opt f cls1 cls2 cls3 =
 mk_nuprl_simple_term "rec-combined-loc-class-opt-3" [f; opt; cls1; cls2; cls3]

let mk_nuprl_lifting0_term f = mk_nuprl_simple_term "lifting-0" [f]
let mk_nuprl_lifting1_term f = mk_nuprl_simple_term "lifting-1" [f]
let mk_nuprl_lifting2_term f = mk_nuprl_simple_term "lifting-2" [f]
let mk_nuprl_lifting3_term f = mk_nuprl_simple_term "lifting-3" [f]
let mk_nuprl_lifting4_term f = mk_nuprl_simple_term "lifting-4" [f]

let mk_nuprl_lifting_gen_term n f = mk_nuprl_simple_term "lifting-gen" [n; f]

let mk_nuprl_lifting_loc0_term f = mk_nuprl_simple_term "lifting-loc-0" [f]
let mk_nuprl_lifting_loc1_term f = mk_nuprl_simple_term "lifting-loc-1" [f]
let mk_nuprl_lifting_loc2_term f = mk_nuprl_simple_term "lifting-loc-2" [f]
let mk_nuprl_lifting_loc3_term f = mk_nuprl_simple_term "lifting-loc-3" [f]
let mk_nuprl_lifting_loc4_term f = mk_nuprl_simple_term "lifting-loc-4" [f]

let mk_nuprl_lifting_loc_gen_term n f = mk_nuprl_simple_term "lifting-loc-gen" [n; f]

let mk_nuprl_concat_lifting0_term f = mk_nuprl_simple_term "concat-lifting-0" [f]
let mk_nuprl_concat_lifting1_term f = mk_nuprl_simple_term "concat-lifting-1" [f]
let mk_nuprl_concat_lifting2_term f = mk_nuprl_simple_term "concat-lifting-2" [f]
let mk_nuprl_concat_lifting3_term f = mk_nuprl_simple_term "concat-lifting-3" [f]
let mk_nuprl_concat_lifting4_term f = mk_nuprl_simple_term "concat-lifting-4" [f]

let mk_nuprl_concat_lifting_gen_term n f = mk_nuprl_simple_term "concat-lifting-gen" [n; f]

let mk_nuprl_concat_lifting_loc0_term f = mk_nuprl_simple_term "concat-lifting-loc-0" [f]
let mk_nuprl_concat_lifting_loc1_term f = mk_nuprl_simple_term "concat-lifting-loc-1" [f]
let mk_nuprl_concat_lifting_loc2_term f = mk_nuprl_simple_term "concat-lifting-loc-2" [f]
let mk_nuprl_concat_lifting_loc3_term f = mk_nuprl_simple_term "concat-lifting-loc-3" [f]
let mk_nuprl_concat_lifting_loc4_term f = mk_nuprl_simple_term "concat-lifting-loc-4" [f]

let mk_nuprl_concat_lifting_loc_gen_term n f = mk_nuprl_simple_term "concat-lifting-loc-gen" [n; f]

let mk_nuprl_make_msg_term hdr typ v = mk_nuprl_simple_term "make-Msg" [hdr; typ; v]

let mk_nuprl_classrel_term es t x e v = mk_nuprl_simple_term "classrel" [es; t; x; e; v]

let mk_nuprl_es_locl_term es e1 e2 = mk_nuprl_simple_term "es-locl" [es; e1; e2]
let mk_nuprl_es_le_term   es e1 e2 = mk_nuprl_simple_term "es-le"   [es; e1; e2]

let mk_nuprl_fun_term   term1 term2 =
 mk_nuprl_term ("function", []) [([], term1); ([""], term2)]

let mk_nuprl_prod_term  term1 term2 =
 mk_nuprl_term ("product", []) [([], term1); ([""], term2)]

let mk_nuprl_type_term i = mk_nuprl_term ("universe", [mk_nuprl_level_exp_parameter i]) []
let mk_nuprl_msg_term  i = mk_nuprl_term ("Message",  [mk_nuprl_level_exp_parameter i]) []

let mk_nuprl_event_orderingp_term i = mk_nuprl_term ("event-ordering+", [mk_nuprl_level_exp_parameter (i ^ "'")]) [([], mk_nuprl_msg_term i)]

let mk_nuprl_valuealltype_term i = mk_nuprl_term ("vatype", [mk_nuprl_level_exp_parameter i]) []

let mk_nuprl_class_term term =
 mk_nuprl_term ("eclass", [mk_nuprl_level_exp_parameter "i'"])
   [([], mk_nuprl_msg_term "i");
    (["es"; "e"], term)]

let mk_nuprl_normal_locally_programmable_term typ cls =
 mk_nuprl_term ("normal-locally-programmable", [mk_nuprl_level_exp_parameter "i'"])
   [([], mk_nuprl_msg_term "i");
    ([], typ);
    ([], cls)]

let mk_nuprl_nlp_term = mk_nuprl_normal_locally_programmable_term

let mk_nuprl_single_valued_classrel_term es cls typ =
 mk_nuprl_term ("single-valued-classrel", [])
   [([], es);
    ([], cls);
    ([], typ)]

let mk_nuprl_programmable_term typ cls =
 mk_nuprl_term ("programmable", [mk_nuprl_level_exp_parameter "i'"])
   [([], mk_nuprl_msg_term "i");
    ([], typ);
    ([], cls)]

let mk_nuprl_std_ma_term eo cls headers =
 mk_nuprl_term ("std-ma", [mk_nuprl_level_exp_parameter "i"])
   [([], eo);
    ([], cls);
    ([], headers)]

let mk_nuprl_message_constraint_term eo cls headers =
 mk_nuprl_term ("message-constraint", [mk_nuprl_level_exp_parameter "i"])
   [([], eo);
    ([], cls);
    ([], headers)]

let mk_nuprl_messages_delivered_term eo cls =
 mk_nuprl_term ("messages-delivered", [mk_nuprl_level_exp_parameter "i"])
   [([], eo);
    ([], cls)]

let mk_nuprl_event_ordering_p_term =
 mk_nuprl_term ("event-ordering+", [mk_nuprl_level_exp_parameter "i'"])
   [([], mk_nuprl_msg_term "i")]

let mk_nuprl_prop_term i =
 mk_nuprl_term ("prop", [mk_nuprl_level_exp_parameter i]) []

let mk_nuprl_int_term            = mk_nuprl_simple_term "int"             []
let mk_nuprl_real_term           = mk_nuprl_simple_term "real"            []
let mk_nuprl_bool_term           = mk_nuprl_simple_term "bool"            []
let mk_nuprl_unit_term           = mk_nuprl_simple_term "unit"            []
let mk_nuprl_atom_term           = mk_nuprl_simple_term "atom"            []
let mk_nuprl_top_term            = mk_nuprl_simple_term "top"             []
let mk_nuprl_nat_term            = mk_nuprl_simple_term "nat"             []
let mk_nuprl_loc_term            = mk_nuprl_simple_term "Id"              []
let mk_nuprl_name_term           = mk_nuprl_simple_term "name"            [] (* Atom List *)
let mk_nuprl_empty_env_term      = mk_nuprl_simple_term "env"             []
let mk_nuprl_inewline_term       = mk_nuprl_simple_term "!newline"        []
let mk_nuprl_empty_bag_term      = mk_nuprl_simple_term "empty-bag"       []
let mk_nuprl_icons_nil_term      = mk_nuprl_simple_term "!cons"           []
let mk_nuprl_itext_nil_term      = mk_nuprl_simple_term "!text_cons"      []
let mk_nuprl_bool_deq_term       = mk_nuprl_simple_term "bool-deq"        []
let mk_nuprl_int_deq_term        = mk_nuprl_simple_term "int-deq"         []
let mk_nuprl_atom_deq_term       = mk_nuprl_simple_term "atom-deq"        []
let mk_nuprl_nat_deq_term        = mk_nuprl_simple_term "nat-deq"         []
let mk_nuprl_loc_deq_term        = mk_nuprl_simple_term "id-deq"          []
let mk_nuprl_unit_deq_term       = mk_nuprl_simple_term "unit-deq"        []
let mk_nuprl_btrue_term          = mk_nuprl_simple_term "btrue"           []
let mk_nuprl_bfalse_term         = mk_nuprl_simple_term "bfalse"          []
let mk_nuprl_condition_cons_term = mk_nuprl_simple_term "!condition_cons" []
let mk_nuprl_it_term             = mk_nuprl_simple_term "it"              []
let mk_nuprl_nil_term            = mk_nuprl_simple_term "nil"             []

let mk_nuprl_once_class_term          cls   = mk_nuprl_simple_term "once-class"          [cls]
let mk_nuprl_send_once_class_term     cls   = mk_nuprl_simple_term "send-once-class"     [cls]
let mk_nuprl_send_once_loc_class_term cls   = mk_nuprl_simple_term "send-once-loc-class" [cls]
let mk_nuprl_on_loc_class_term        cls   = mk_nuprl_simple_term "on-loc-class"        [cls]
let mk_nuprl_but_first_class_term     cls   = mk_nuprl_simple_term "but-first-class"     [cls]
let mk_nuprl_skip_first_class_term    cls   = mk_nuprl_simple_term "skip-first-class"    [cls]
let mk_nuprl_primed_class_term        cls   = mk_nuprl_simple_term "primed-class"        [cls]
let mk_nuprl_single_bag_term          elt   = mk_nuprl_simple_term "single-bag"          [elt]
let mk_nuprl_bnot_term                term  = mk_nuprl_simple_term "bnot"                [term]
let mk_nuprl_not_term                 term  = mk_nuprl_simple_term "not"                 [term]
let mk_nuprl_pi1_term                 term  = mk_nuprl_simple_term "pi1"                 [term]
let mk_nuprl_pi2_term                 term  = mk_nuprl_simple_term "pi2"                 [term]
let mk_nuprl_hd_term                  term  = mk_nuprl_simple_term "hd"                  [term]
let mk_nuprl_tl_term                  term  = mk_nuprl_simple_term "tl"                  [term]
let mk_nuprl_es_eq_term               es    = mk_nuprl_simple_term "es-eq"               [es]
let mk_nuprl_list_deq_term            term  = mk_nuprl_simple_term "list-deq"            [term]
let mk_nuprl_eqof_term                term  = mk_nuprl_simple_term "eqof"                [term]
let mk_nuprl_valueall_type_term       typ   = mk_nuprl_simple_term "valueall-type"       [typ]
let mk_nuprl_list_term                term  = mk_nuprl_simple_term "list"                [term]
let mk_nuprl_bag_term                 term  = mk_nuprl_simple_term "bag"                 [term]
let mk_nuprl_deq_term                 term  = mk_nuprl_simple_term "deq"                 [term]
let mk_nuprl_esE_term                 es    = mk_nuprl_simple_term "es-E"                [es]
let mk_nuprl_assert_term              b     = mk_nuprl_simple_term "assert"              [b]
let mk_nuprl_msg_header_term          term  = mk_nuprl_simple_term "msg-header"          [term]
let mk_nuprl_msg_type_term            term  = mk_nuprl_simple_term "msg-type"            [term]
let mk_nuprl_msg_body_term            term  = mk_nuprl_simple_term "msg-body"            [term]
let mk_nuprl_bag_null_term            bag   = mk_nuprl_simple_term "bag-null"            [bag]
let mk_nuprl_bag_only_term            bag   = mk_nuprl_simple_term "bag-only"            [bag]
let mk_nuprl_bag_size_term            bag   = mk_nuprl_simple_term "bag-size"            [bag]
let mk_nuprl_evalall_term             term  = mk_nuprl_simple_term "evalall"             [term]

let mk_nuprl_class_at_term             cls    locs   = mk_nuprl_simple_term "class-at"             [cls;    locs]
let mk_nuprl_base_locs_headers_term    term1  term2  = mk_nuprl_simple_term "base-locs-headers"    [term1;  term2]
let mk_nuprl_general_base_class_term   term1  term2  = mk_nuprl_simple_term "general-base-class"   [term1;  term2]
let mk_nuprl_base_headers_msg_val_term term1  term2  = mk_nuprl_simple_term "base-headers-msg-val" [term1;  term2]
let mk_nuprl_concat_term               list1  list2  = mk_nuprl_simple_term "append"               [list1;  list2]
let mk_nuprl_select_term               ind    list   = mk_nuprl_simple_term "select"               [ind;    list]
let mk_nuprl_parallel_class_term       class1 class2 = mk_nuprl_simple_term "parallel-class"       [class1; class2]
let mk_nuprl_until_class_term          class1 class2 = mk_nuprl_simple_term "until-class"          [class1; class2]
let mk_nuprl_primed_class_opt_term     cls    bag    = mk_nuprl_simple_term "primed-class-opt"     [cls;    bag]
let mk_nuprl_class_opt_term            cls    bag    = mk_nuprl_simple_term "class-opt"            [cls;    bag]
let mk_nuprl_class_opt_class_term      class1 class2 = mk_nuprl_simple_term "class-opt-class"      [class1; class2]
let mk_nuprl_base_prc_term             name   typ    = mk_nuprl_simple_term "base-prc"             [name;   typ]
let mk_nuprl_once_prc_term             typ    cls    = mk_nuprl_simple_term "once-prc"             [typ;    cls]
let mk_nuprl_send_once_loc_prc_term    typ    bag    = mk_nuprl_simple_term "send-once-loc-prc"    [typ;    bag]
let mk_nuprl_on_loc_prc_term           typ    fX     = mk_nuprl_simple_term "on-loc-prc"           [typ;    fX]
let mk_nuprl_but_first_prc_term        typ    cls    = mk_nuprl_simple_term "but-first-prc"        [typ;    cls]
let mk_nuprl_skip_first_prc_term       typ    cls    = mk_nuprl_simple_term "skip-first-prc"       [typ;    cls]
let mk_nuprl_prior_prc_term            typ    cls    = mk_nuprl_simple_term "prior-prc"            [typ;    cls]
let mk_nuprl_or_term                   term1  term2  = mk_nuprl_simple_term "or"                   [term1;  term2]
let mk_nuprl_and_term                  term1  term2  = mk_nuprl_simple_term "and"                  [term1;  term2]
let mk_nuprl_rec_bind_class_term       x      y      = mk_nuprl_simple_term "rec-bind-class"       [x;      y]
let mk_nuprl_member_term               term1  term2  = mk_nuprl_simple_term "member"               [term1;  term2]
let mk_nuprl_eq_atom_term              nt1    nt2    = mk_nuprl_simple_term "eq_atom"              [nt1;    nt2]
let mk_nuprl_eq_bool_term              nt1    nt2    = mk_nuprl_simple_term "eq_bool"              [nt1;    nt2]
let mk_nuprl_eq_int_term               nt1    nt2    = mk_nuprl_simple_term "eq_int"               [nt1;    nt2]
let mk_nuprl_eq_id_term                nt1    nt2    = mk_nuprl_simple_term "eq_id"                [nt1;    nt2]
let mk_nuprl_eq_loc_term               nt1    nt2    = mk_nuprl_simple_term "eq_id"                [nt1;    nt2]
let mk_nuprl_bor_term                  term1  term2  = mk_nuprl_simple_term "bor"                  [term1;  term2]
let mk_nuprl_band_term                 term1  term2  = mk_nuprl_simple_term "band"                 [term1;  term2]
let mk_nuprl_iff_term                  term1  term2  = mk_nuprl_simple_term "iff"                  [term1;  term2]
let mk_nuprl_uiff_term                 term1  term2  = mk_nuprl_simple_term "uiff"                 [term1;  term2]
let mk_nuprl_implies_term              term1  term2  = mk_nuprl_simple_term "implies"              [term1;  term2]
let mk_nuprl_uimplies_term             term1  term2  = mk_nuprl_simple_term "uimplies"             [term1;  term2]
let mk_nuprl_proddeq_term              term1  term2  = mk_nuprl_simple_term "proddeq"              [term1;  term2]
let mk_nuprl_sumdeq_term               term1  term2  = mk_nuprl_simple_term "sumdeq"               [term1;  term2]
let mk_nuprl_add_term                  term1  term2  = mk_nuprl_simple_term "add"                  [term1;  term2]
let mk_nuprl_subtract_term             term1  term2  = mk_nuprl_simple_term "subtract"             [term1;  term2]
let mk_nuprl_multiply_term             term1  term2  = mk_nuprl_simple_term "multiply"             [term1;  term2]
let mk_nuprl_remainder_term            term1  term2  = mk_nuprl_simple_term "remainder"            [term1;  term2]
let mk_nuprl_divide_term               term1  term2  = mk_nuprl_simple_term "divide"               [term1;  term2]
let mk_nuprl_lt_int_term               term1  term2  = mk_nuprl_simple_term "lt_int"               [term1;  term2]
let mk_nuprl_le_int_term               term1  term2  = mk_nuprl_simple_term "le_int"               [term1;  term2]
let mk_nuprl_less_than_term            term1  term2  = mk_nuprl_simple_term "less_than"            [term1;  term2]
let mk_nuprl_le_term                   term1  term2  = mk_nuprl_simple_term "le"                   [term1;  term2]
let mk_nuprl_es_pred_term              es     e      = mk_nuprl_simple_term "es-pred"              [es;     e]
let mk_nuprl_union_term                term1  term2  = mk_nuprl_simple_term "union"                [term1;  term2]
let mk_nuprl_msg_has_type_term         term1  term2  = mk_nuprl_simple_term "msg-has-type"         [term1;  term2]
let mk_nuprl_name_eq_term              term1  term2  = mk_nuprl_simple_term "name_eq"              [term1;  term2]
let mk_nuprl_icons_cons_term           term1  term2  = mk_nuprl_simple_term "!cons"                [term1;  term2]
let mk_nuprl_itext_cons_term           term1  term2  = mk_nuprl_simple_term "!text_cons"           [term1;  term2]
let mk_nuprl_iclosure_term             term   env    = mk_nuprl_simple_term "!closure"             [term;   env]
let mk_nuprl_iinclude_properties_term  prop   term   = mk_nuprl_simple_term "!include_properties"  [prop;   term]
let mk_nuprl_cons_bag_term             head   tail   = mk_nuprl_simple_term "cons-bag"             [head;   tail]
let mk_nuprl_bag_map_term              f      bag    = mk_nuprl_simple_term "bag-map"              [f;      bag]
let mk_nuprl_eq_term_term              term1  term2  = mk_nuprl_simple_term "eq_term"              [term1;  term2]
let mk_nuprl_cons_term                 term1  term2  = mk_nuprl_simple_term "cons"                 [term1;  term2]

let mk_nuprl_base_headers_msg_val_loc_term term1 term2 term3 = mk_nuprl_simple_term "base-headers-msg-val-loc" [term1; term2; term3]
let mk_nuprl_base_at_prc_term              name  typ   locs  = mk_nuprl_simple_term "base-at-prc"              [name;  typ;   locs]
let mk_nuprl_until_prc_term                typ   x1    x2    = mk_nuprl_simple_term "until-prc"                [typ;   x1;    x2]
let mk_nuprl_at_prc_term                   typ   x     locs  = mk_nuprl_simple_term "at-prc"                   [typ;   x;     locs]
let mk_nuprl_parallel_prc_term             typ   x     y     = mk_nuprl_simple_term "parallel-prc"             [typ;   x;     y]
let mk_nuprl_prior_init_prc_term           typ   x     init  = mk_nuprl_simple_term "prior-init-prc"           [typ;   x;     init]
let mk_nuprl_ite_term                      term1 term2 term3 = mk_nuprl_simple_term "ifthenelse"               [term1; term2; term3]
let mk_nuprl_equal_term                    term1 term2 ty    = mk_nuprl_simple_term "equal"                    [ty;    term1; term2]
let mk_nuprl_reduce_term                   term1 term2 term3 = mk_nuprl_simple_term "reduce"                   [term1; term2; term3]
let mk_nuprl_es_eq_E_term                  es    term1 term2 = mk_nuprl_simple_term "es-eq-E"                  [es;    term1; term2]
let mk_nuprl_es_causl_term                 es    term1 term2 = mk_nuprl_simple_term "es-causl"                 [es;    term1; term2]
let mk_nuprl_es_functional_class_term      es    typ   cls   = mk_nuprl_simple_term "es-functional-class"      [es;    typ;   cls]
let mk_nuprl_classfun_term                 es    cls   e     = mk_nuprl_simple_term "classfun"                 [es;    cls;   e]
let mk_nuprl_eq_bag_term                   deq   term1 term2 = mk_nuprl_simple_term "bag-eq"                   [deq;   term1; term2]

let mk_nuprl_product_deq_term                 typ1 typ2 deq1 deq2 = mk_nuprl_simple_term "product-deq"                 [typ1; typ2; deq1; deq2]
let mk_nuprl_union_deq_term                   typ1 typ2 deq1 deq2 = mk_nuprl_simple_term "union-deq"                   [typ1; typ2; deq1; deq2]
let mk_nuprl_bind_prc_term                    typA typB x    y    = mk_nuprl_simple_term "bind-prc"                    [typA; typB; x;    y]
let mk_nuprl_loc_comb1_prc_term               typ  n    xprs f    = mk_nuprl_simple_term "loc-comb1-prc"               [typ;  n;    xprs; f]
let mk_nuprl_rec_combined_loc_class1_prc_term typ  n    xprs f    = mk_nuprl_simple_term "rec-combined-loc-class1-prc" [typ;  n;    xprs; f]

let mk_nuprl_eq_prod_term deq1 deq2 nt1 nt2 =
  let bdeq = mk_nuprl_proddeq_term deq1 deq2 in
  let app1 = mk_apply_term bdeq nt1 in
  let app2 = mk_apply_term app1 nt2 in
  app2

let mk_nuprl_eq_union_term deq1 deq2 nt1 nt2 =
  let bdeq = mk_nuprl_sumdeq_term deq1 deq2 in
  let app1 = mk_apply_term bdeq nt1 in
  let app2 = mk_apply_term app1 nt2 in
  app2

let mk_nuprl_eq_list_term deq nt1 nt2 =
  let bdeq = mk_nuprl_list_deq_term deq   in
  let app1 = mk_apply_term bdeq nt1 in
  let app2 = mk_apply_term app1 nt2 in
  app2

let rec mk_nuprl_itext_list_term lst =
 match lst with
   [] -> mk_nuprl_itext_nil_term
 | (x :: xs) -> mk_nuprl_itext_cons_term x (mk_nuprl_itext_list_term xs)

let mk_nuprl_all_term term1 (var, term2) =
 mk_nuprl_term ("all", []) [([], term1); ([var], term2)]

let mk_nuprl_uall_term term1 (var, term2) =
 mk_nuprl_term ("uall", []) [([], term1); ([var], term2)]

let mk_nuprl_exists_term term1 (var, term2) =
 mk_nuprl_term ("exists", []) [([], term1); ([var], term2)]

let mk_nuprl_isect_term term1 (var, term2) =
 mk_nuprl_term ("isect", []) [([], term1); ([var], term2)]

let mk_nuprl_list_ind_term l nilcase (x, xs, r, conscase) =
 mk_nuprl_term ("list_ind", [])
   [([], l);
    ([], nilcase);
    ([x; xs; r], conscase)]

let mk_nuprl_list_ind_ref_term l nilcase (x, xs, r, conscase) =
 mk_nuprl_ref_term ("list_ind", [])
   [([], mk_rterm l);
    ([], nilcase);
    ([x; xs; r], conscase)]

let mk_nuprl_ind_term i (x, rd, downcase) basecase (y, ru, upcase) =
 mk_nuprl_term ("ind", [])
   [([], i);
    ([x; rd], downcase);
    ([], basecase);
    ([y; ru], upcase)]

let mk_nuprl_ind_ref_term i (x, rd, downcase) basecase (y, ru, upcase) =
 mk_nuprl_ref_term ("ind", [])
   [([], mk_rterm i);
    ([x; rd], downcase);
    ([], basecase);
    ([y; ru], upcase)]

let mk_nuprl_rec_ind_term arg (f, x, b) =
 mk_nuprl_term ("rec_ind", []) [([], arg); ([f; x], b)]

let mk_nuprl_rec_ind_ref_term arg (f, x, b) =
 mk_nuprl_ref_term ("rec_ind", []) [([], mk_rterm arg); ([f; x], b)]

let mk_nuprl_finite_list_term list =
 List.fold_right
    (fun elt list -> mk_nuprl_cons_term elt list)
    list
    mk_nuprl_nil_term

let mk_nuprl_rec_comb_prc_term typ n xprs init f strict =
 mk_nuprl_simple_term "rec-comb-prc" [typ; n; xprs; init; f; strict]

let mk_nuprl_rec_bind_prc_term a b x y arg =
 mk_nuprl_simple_term "rec-bind-prc" [a; b; x; y; arg]

let mk_nuprl_iabstraction_term t1 t2 =
 mk_nuprl_simple_term "!abstraction" [mk_nuprl_condition_cons_term; t1; t2]

let mk_nuprl_itheorem_term name term =
 mk_nuprl_term ("!theorem", [mk_nuprl_token_parameter name]) [([], term)]

let mk_nuprl_iupdate_term name term =
 mk_nuprl_term ("!update", [mk_nuprl_token_parameter name]) [([], term)]

let mk_nuprl_iinsert_object_term term =
 mk_nuprl_simple_term "!insert_object_id_in_operator" [term]

let mk_nuprl_iinsert_object_p_term name term =
 mk_nuprl_term ("!insert_object_id_in_operator",
		[mk_nuprl_token_parameter name; mk_nuprl_natural_parameter (II.of_int 0)])
   [([], term)]

let mk_nuprl_ioid_term = mk_nuprl_simple_term "!oid" []

let mk_nuprl_iproperty_term name value =
 mk_nuprl_term ("!property", [mk_nuprl_token_parameter name]) [([], value)]

let mk_nuprl_istring_term string =
 mk_nuprl_term ("!string", [mk_nuprl_string_parameter string]) []

let mk_nuprl_ibool_term bool =
 mk_nuprl_term ("!bool", [mk_nuprl_bool_parameter bool]) []

let rec mk_nuprl_ilist_term lst =
 match lst with
   [] -> mk_nuprl_icons_nil_term
 | (term :: terms) -> mk_nuprl_icons_cons_term term (mk_nuprl_ilist_term terms)

let mk_nuprl_itext_term str =
 mk_nuprl_term  ("!text", [mk_nuprl_string_parameter str]) []

let mk_nuprl_iwf_lemmas_term wf_lemmas = mk_nuprl_simple_term "!wf" wf_lemmas

let mk_nuprl_icomment_term name comment =
 mk_nuprl_term ("!comment", [mk_nuprl_string_parameter name]) [([], comment)]

let mk_nuprl_cons_env_term v pair env =
 mk_nuprl_term ("env", []) [([v], pair); ([], env)]

let mk_nuprl_callbyvalue_term arg (x, b) =
 mk_nuprl_term ("callbyvalue", []) [([], arg); ([x], b)]

let mk_nuprl_callbyvalueall_term arg (x, b) =
 mk_nuprl_term ("callbyvalueall", []) [([], arg); ([x], b)]

(*fun mk_nuprl_mlnk_term term = mk_nuprl_simple_term "mlnk" [term]
fun mk_nuprl_mtag_term term = mk_nuprl_simple_term "mtag" [term]
fun mk_nuprl_mval_term term = mk_nuprl_simple_term "mval" [term]*)

(*
let build_primitive_value term params =
 let opid = opid_of_term term in
 if List.exists (fun x -> x = opid) ["inl"; "inr"; "pair"; "cons"]
 then mk_nuprl_simple_term opid params
 else term
*)

let rec toDeq term =
  if is_nuprl_int_term term
  then mk_nuprl_int_deq_term
  else if is_nuprl_bool_term term
  then mk_nuprl_bool_deq_term
  else if is_nuprl_unit_term term
  then mk_nuprl_unit_deq_term
  else if is_nuprl_loc_term term
  then mk_nuprl_loc_deq_term
  else if is_nuprl_atom_term term
  then mk_nuprl_atom_deq_term
  else if is_nuprl_list_term term
  then mk_nuprl_list_deq_term (toDeq (dest_type_list term))
  else if is_nuprl_product_term term
  then
    let (t1, t2) = dest_product term in
    mk_nuprl_proddeq_term (toDeq t1) (toDeq t2)
  else failwith "toDeq"

let do_primitive_int_op opid value1 value2 =
  let n1 = dest_integer 2 value1 in
  let n2 = dest_integer 3 value2 in
  let n  =
    match opid with
      "add"       -> II.add n1 n2
    | "subtract"  -> II.sub n1 n2
    | "multiply"  -> II.mul n1 n2
    | "divide"    -> II.div n1 n2
    | "remainder" -> II.rem n1 n2
    | _           -> failwith "wrong term" in
  mk_nuprl_integer_term n

let do_primitive_wait value exp =
  let n = dest_integer 4 value in
  let _ = print_string ("[---------sleeping for " ^ II.to_string n ^ "s---------]\n") in
  let _ = Unix.sleep n in
  exp

let do_primitive_minus value =
  let n = dest_integer 4 value
  in mk_nuprl_integer_term (II.sub II.zero n)

let do_primitive_cmp cmp value1 value2 =
 if cmp = "int_eq" || cmp = "less"
 then
   let n1 = dest_integer 5 value1 in
   let n2 = dest_integer 6 value2 in
   if cmp = "less"
   then II.lt n1 n2
   else n1 = n2
 else failwith "unknown primitive comparison"

let is_zero term = II.compare (dest_integer 7 term) 0

let inc_integer term = mk_nuprl_integer_term (II.add (dest_integer 8 term) 1)
let dec_integer term = mk_nuprl_integer_term (II.sub (dest_integer 9 term) 1)

(* ------ LIB ------ *)

let union_stats_term map1 map2 =
  MAP.merge
    (fun id x y ->
      (match x, y with
	Some n, Some m -> Some (n + m)
      | Some n, None   -> Some n
      | None,   Some m -> Some m
      | None,   None   -> None))
    map1
    map2

let rec get_stats_term term =
  match term with
    TERM (((opid, _), _), bterms) ->
      union_stats_term
	(MAP.singleton opid 1)
	(get_stats_bterms bterms)
  | AXM_TERM -> MAP.singleton "axiom"  1
  | BOT_TERM -> MAP.singleton "bottom" 1
  | INT_TERM -> MAP.singleton "int"    1
  | ATM_TERM _ -> MAP.singleton "atom" 1
  | TOK_TERM _ -> MAP.singleton "token" 1
  | NAT_TERM _ -> MAP.singleton "natural_number" 1
  | VAR_TERM _ -> MAP.empty
  | LAM_TERM (var, rterm) ->
      union_stats_term
	(MAP.singleton "lambda" 1)
	(get_stats_rterm rterm)
  | WAI_TERM (rterm1, rterm2) ->
      union_stats_term
	(MAP.singleton "wait" 1)
	(union_stats_term
	   (get_stats_rterm rterm1)
	   (get_stats_rterm rterm2))
  | APP_TERM (rterm1, rterm2) ->
      union_stats_term
	(MAP.singleton "apply" 1)
	(union_stats_term
	   (get_stats_rterm rterm1)
	   (get_stats_rterm rterm2))
  | PAI_TERM (rterm1, rterm2) ->
      union_stats_term
	(MAP.singleton "pair" 1)
	(union_stats_term
	   (get_stats_rterm rterm1)
	   (get_stats_rterm rterm2))
  | INL_TERM rterm ->
      union_stats_term
	(MAP.singleton "inl" 1)
	(get_stats_rterm rterm)
  | INR_TERM rterm ->
      union_stats_term
	(MAP.singleton "inr" 1)
	(get_stats_rterm rterm)
  | FIX_TERM rterm ->
      union_stats_term
	(MAP.singleton "fix" 1)
	(get_stats_rterm rterm)
  | SPR_TERM (pair, var1, var2, rterm) ->
      union_stats_term
	(MAP.singleton "spread" 1)
	(union_stats_term
	   (get_stats_rterm pair)
	   (get_stats_rterm rterm))
  | DEC_TERM (dec, var1, rterm1, var2, rterm2) ->
      union_stats_term
	(MAP.singleton "decide" 1)
	(union_stats_term
	   (get_stats_rterm dec)
	   (union_stats_term
	      (get_stats_rterm rterm1)
	      (get_stats_rterm rterm2)))
  | IAX_TERM (ax, rterm1, rterm2) ->
      union_stats_term
	(MAP.singleton "isaxiom" 1)
	(union_stats_term
	   (get_stats_rterm ax)
	   (union_stats_term
	      (get_stats_rterm rterm1)
	      (get_stats_rterm rterm2)))
  | IPA_TERM (pair, rterm1, rterm2) ->
      union_stats_term
	(MAP.singleton "ispair" 1)
	(union_stats_term
	   (get_stats_rterm pair)
	   (union_stats_term
	      (get_stats_rterm rterm1)
	      (get_stats_rterm rterm2)))
  | IEQ_TERM (a, b, rterm1, rterm2) ->
    union_stats_term
      (MAP.singleton "int_eq" 1)
      (union_stats_term
	 (get_stats_rterm a)
	 (union_stats_term
	    (get_stats_rterm b)
	    (union_stats_term
	       (get_stats_rterm rterm1)
	       (get_stats_rterm rterm2))))
  | AEQ_TERM (a, b, rterm1, rterm2) ->
    union_stats_term
      (MAP.singleton "atom_eq" 1)
      (union_stats_term
	 (get_stats_rterm a)
	 (union_stats_term
	    (get_stats_rterm b)
	    (union_stats_term
	       (get_stats_rterm rterm1)
	       (get_stats_rterm rterm2))))
  | CLO_TERM _ -> failwith "get_stats_term:CLO_TERM"

and get_stats_bterms bterms =
  List.fold_right
    (fun bterm m -> union_stats_term (get_stats_bterm bterm) m)
    bterms
    MAP.empty

and get_stats_bterm (B_TERM (vars, rterm)) = get_stats_rterm rterm

and get_stats_rterm rterm = get_stats_term (rterm2term rterm)

let stats_term_to_string term =
  MAP.fold
    (fun opid n str -> opid ^ "(" ^ string_of_int n ^ ")" ^ str)
    (get_stats_term term)
    ""

let print_lib_stats {abs; tof} =
  let n1 = MAP.cardinal (!abs) in
  let n2 = MAP.cardinal (!tof) in
  print_string ("[library size: "
		^ string_of_int n1
		^ " abstractions, "
		^ string_of_int n2
		^ " extracts"
		^ "]\n")

let is_in_lib {abs; tof} id = MAP.mem id (!abs)

let dump_lib_termofs file {abs; tof} =
  let out = open_out file in
  let _   =
    MAP.iter
      (fun k rterm ->
	output_string out (k ^ "\n" ^ toStringTerm (get rterm) ^ "\n"))
      (!tof) in
  let _   = close_out out in
  ()



(* ------ FREE VARS and SUBSTITUTIONS ------ *)

let remove_list vars lst =
 List.fold_right
   (fun var vars -> VARS.remove var vars)
   lst
   vars

let rec new_free_var frees var =
 let var' = var ^ "'" in
 if VARS.mem var' frees
 then new_free_var frees var'
 else var'

let isin_var_list = isin_str

let filter_sub vars = SUB.filter (fun v _ -> not (isin_var_list v vars))

let filter_ren vars = SUB.filter (fun v _ -> not (isin_var_list v vars))

let insert_sub sub (v, t) = SUB.add v (FO t) sub

let insert_ren ren (v, t) = SUB.add v t ren

let insert_list_sub sub list =
  List.fold_right
    (fun x sub -> insert_sub sub x)
    list
    sub

let insert_list_ren ren list =
  List.fold_right
    (fun x ren -> insert_ren ren x)
    list
    ren

let empty_sub : ran_sub SUB.t = SUB.empty

let empty_ren : variable SUB.t = SUB.empty

let gen_sub = insert_list_sub empty_sub

let gen_ren = insert_list_ren empty_ren

let apply_ren ren v =
  try SUB.find v ren
  with _ -> v

let rename_operator (opid_tag, params) ren =
  let params' =
    List.map
      (fun (v, k) ->
	try (SUB.find v ren, k)
	with _ -> (v,  k))
      params
  in (opid_tag, params')

let domain (ENV m) =
  ENV_MAP.fold
    (fun i _ lst -> i :: lst)
    m
    []

let rec fo_subst_aux (sub, ren) term =
  match term with
    TERM (operator, bterms) ->
      if is_nuprl_variable_term term
      then
	let (v, ts) = dest_so_variable term in
	apply_sub (sub, ren) (v, ts) term
      else
	let operator' = rename_operator operator ren in
	let bterms'   = List.map (fo_subst_bterm (sub, ren)) bterms in
	TERM (operator', bterms')
  | CLO_TERM (rterm, env) ->
      let (rterm', env') = fo_subst_clos (sub, ren) (rterm, env) in
      CLO_TERM (rterm', env')
  | BOT_TERM -> term
  | AXM_TERM -> term
  | INT_TERM -> term
  | NAT_TERM _ -> term
  | ATM_TERM _ -> term
  | TOK_TERM _ -> term
  | VAR_TERM var -> apply_sub (sub, ren) (var, []) term
  | LAM_TERM (var, rterm) ->
      let (vars, t) = fo_rename (sub, ren) ([var], rterm2term rterm) in
      (match vars with
	[v] -> LAM_TERM (v, mk_rterm t)
      | _   -> failwith "fo_subst_aux:LAM_TERM")
  | WAI_TERM (rterm1, rterm2) ->
      WAI_TERM (fo_subst_rterm (sub, ren) rterm1,
		fo_subst_rterm (sub, ren) rterm2)
  | APP_TERM (rterm1, rterm2) ->
      APP_TERM (fo_subst_rterm (sub, ren) rterm1,
		fo_subst_rterm (sub, ren) rterm2)
  | PAI_TERM (rterm1, rterm2) ->
      PAI_TERM (fo_subst_rterm (sub, ren) rterm1,
		fo_subst_rterm (sub, ren) rterm2)
  | INL_TERM rterm -> INL_TERM (fo_subst_rterm (sub, ren) rterm)
  | INR_TERM rterm -> INR_TERM (fo_subst_rterm (sub, ren) rterm)
  | FIX_TERM rterm -> FIX_TERM (fo_subst_rterm (sub, ren) rterm)
  | IAX_TERM (ax, rterm1, rterm2) ->
      IAX_TERM (fo_subst_rterm (sub, ren) ax,
		fo_subst_rterm (sub, ren) rterm1,
		fo_subst_rterm (sub, ren) rterm2)
  | IPA_TERM (pair, rterm1, rterm2) ->
      IPA_TERM (fo_subst_rterm (sub, ren) pair,
		fo_subst_rterm (sub, ren) rterm1,
		fo_subst_rterm (sub, ren) rterm2)
  | IEQ_TERM (a, b, rterm1, rterm2) ->
      IEQ_TERM (fo_subst_rterm (sub, ren) a,
		fo_subst_rterm (sub, ren) b,
		fo_subst_rterm (sub, ren) rterm1,
		fo_subst_rterm (sub, ren) rterm2)
  | AEQ_TERM (a, b, rterm1, rterm2) ->
      AEQ_TERM (fo_subst_rterm (sub, ren) a,
		fo_subst_rterm (sub, ren) b,
		fo_subst_rterm (sub, ren) rterm1,
		fo_subst_rterm (sub, ren) rterm2)
  | DEC_TERM (dec, var1, rterm1, var2, rterm2) ->
      let d = fo_subst_aux (sub, ren) (rterm2term dec) in
      let (vars1, t1) = fo_rename (sub, ren) ([var1], rterm2term rterm1) in
      let (vars2, t2) = fo_rename (sub, ren) ([var2], rterm2term rterm2) in
      (match vars1, vars2 with
	[v1], [v2] -> DEC_TERM (mk_rterm d, v1, mk_rterm t1, v2, mk_rterm t2)
      | _   -> failwith "fo_subst_aux:DEC_TERM")
  | SPR_TERM (pair, var1, var2, rterm) ->
      let p = fo_subst_aux (sub, ren) (rterm2term pair) in
      let (vars, t) = fo_rename (sub, ren) ([var1; var2], rterm2term rterm) in
      (match vars with
	[v1;v2] -> SPR_TERM (mk_rterm p, v1, v2, mk_rterm t)
      | _   -> failwith "fo_subst_aux:DEC_TERM")

and fo_subst_rterm (sub, ren) rterm =
  mk_rterm (fo_subst_aux (sub, ren) (rterm2term rterm))

and fo_subst_clos (sub, ren) (rterm, env) =
  let term  = rterm2term rterm   in
  let dom   = domain env         in
  let sub'  = filter_sub dom sub in
  let ren'  = filter_ren dom ren in
  let term' = fo_subst_aux (sub', ren') term in
  let env'  = fo_subst_env (sub', ren') env  in
  (mk_rterm term', env')

and fo_subst_env (sub, ren) (ENV m) =
  ENV (ENV_MAP.map (fo_subst_rterm (sub, ren)) m)

and fo_subst_bterm (sub, ren) (B_TERM (vars, term)) =
  let (vars', term') = fo_rename (sub, ren) (vars, rterm2term term)
  in B_TERM (vars', mk_rterm term')

and apply_sub (sub, ren) (v, ts) t =
  try
    (
     match SUB.find v sub with
       FO t' -> t'
     | SO (vars, t') ->
	 (
	  try
	    let lst =
	      List.map
		(fun (v1, t2) -> (v1, fo_subst_aux (sub, empty_ren) t2))
		(SML_ListPair.zipEq (vars, ts))
	    in fo_subst_aux (gen_sub lst, empty_ren) t'
	  with _ -> failwith "apply_sub"
	 )
    )
  with _ -> t

(* renames the variables in vars (and term) that occur in the
* range of sub, and also remove the part of sub such that its
* domain is in vars. *)
and fo_rename (sub, ren) (vars, term) =
 let sub' = filter_sub vars sub in
 (* freesSub is the free variable list of sub's range.
  * In the (SO (vars, t)) case, we only need to get the free variables
  * in t that are not in vars. *)
 let freesSub =
   SUB.fold
     (fun i v vars ->
       match v with
	 SO (vs, t) -> VARS.union vars (fo_free_vars (fromListVARS vs) t)
       | FO t -> VARS.union vars (free_vars t))
     sub'
     empty_vars in
 let freesTerm = free_vars term in
 let getNewFreeVar = new_free_var (VARS.union freesSub freesTerm) in
 let (vars', sub'') =
   List.fold_right
     (fun var (vars, sub) ->
       if VARS.mem var freesSub
	   (* then the bound variable would capture one of
	    * the free variables of the substitution. *)
       then
	 let var' = getNewFreeVar var in
	 let tvar' = mk_variable_term var' in
	 (var' :: vars, insert_sub sub (var, tvar'))
       else (var :: vars, sub))
     vars
     ([], sub') in
 (vars', fo_subst_aux (sub'', ren) term)

let fo_subst list term = fo_subst_aux (gen_sub list, empty_ren) term

let correct_lhs (vars, rterm) =
 try
   (let term = rterm2term rterm in
   if null vars
   then
     if is_nuprl_variable_term term
     then dest_variable 7 term
     else failwith "correct_lhs"
   else
     let (v, ts) = dest_so_variable term in
     if List.for_all
	 (fun (v,t) -> try (v = dest_variable 7 t) with _ -> false)
	 (SML_ListPair.zipEq (vars, ts))
     then v
     else failwith "correct_lhs")
 with _ -> failwith "correct_lhs"

let matching term1 (*term*) term2 (*lhs*) =
 let ((opid1, params1), bterms1) = dest_term term1 in
 let ((opid2, params2), bterms2) = dest_term term2 in
 let (sub_subterms, is_fo_sub) =
   if opid1 = opid2 && List.length bterms1 = List.length bterms2
   then
     List.fold_right
       (fun ((vs1, t1), bterm2) (sub, is_fo_sub) ->
	 let b = is_fo_sub && null vs1 in
	 let v = correct_lhs bterm2 in
	 (SUB.add v (SO (vs1, rterm2term t1)) sub, b))
       (SML_ListPair.zip (bterms1, bterms2))
       (empty_sub, true)
   else failwith "matching" in
 let (ren_params, is_em_ren) =
   if List.length params1 = List.length params2
   then
     List.fold_right
       (fun ((v1, k1), (v2, k2)) (ren, is_em_ren) ->
	 if eq_kinds (k1, k2)
	     &&
	   not (is_abstract_metavar v1)
	 then
	   if is_abstract_metavar v2
	   then (insert_ren ren (v2, v1), false)
	   else if v1 = v2
	   then (ren, is_em_ren)
	   else failwith "matching"
	 else failwith "matching")
       (SML_ListPair.zip (params1, params2))
       (empty_ren, true)
   else failwith "matching" in
 ((sub_subterms, is_fo_sub), (ren_params, is_em_ren))

(* ------ UNFOLDING ------ *)

let unfold_ab clos term lhs rhs =
 let ((sub_t, is_fo_sub), (ren_p, is_em_ren)) = matching term lhs in
 if is_fo_sub && is_em_ren && SML_Option.isSome clos
 then
   let e = SML_Option.valOf clos in
   let env =
     SUB.fold
       (fun v vt env ->
	 match vt with
	   FO t ->
	     let pair = mk_pair_term t e in
	     mk_nuprl_cons_env_term v pair env
	 | SO ([], t) ->
	     let pair = mk_pair_term t e in
	     mk_nuprl_cons_env_term v pair env
	 | _ -> failwith "unfold:closure")
       sub_t
       e in
   mk_nuprl_iclosure_term rhs env
 else fo_subst_aux (sub_t, ren_p) rhs

let ct_unfold_ab clos term lhs rhs =
 let ((sub_t, is_fo_sub), (ren_p, is_em_ren)) = matching term lhs in
 if is_fo_sub && is_em_ren && SML_Option.isSome clos
 then
   let env1 = SML_Option.valOf clos in
   let env2 =
     SUB.fold
       (fun v vt env ->
	 match vt with
	   FO t -> add2env_one env (v,t,env1)
	 | SO ([], t) -> add2env_one env (v,t,env1)
	 | _ -> failwith "unfold:closure")
       sub_t
       env1 in
   mk_rct (rhs, env2)
 else fo_subst_aux (sub_t, ren_p) rhs

let rec unfold_all ({abs; tof} as lib) term =
 match term with
   TERM (operator, bterms) ->
     (try
       (
	(*let _ =
	  let opid = opid_of_term term in
	  if opid = "list_ind"
	  then print_endline ("[----looking for " ^ opid ^ "'s sign]")
	  else () in*)
	let {id; sign; obid; lhs; rhs; wfs} = find_sign abs term in
	(*let _ =
	  if id = "list_ind"
	  then print_endline ("[------found sign for " ^ id ^ "]")
	  else () in*)
	let t =
	  (*try*)
	    unfold_ab None term (rterm2term lhs) (rterm2term rhs)
	  (*with Failure str ->
	    (print_endline ("[------couldn't unfold " ^ id ^ ": " ^ str ^ "]");
	     raise (Failure str))*) in
	(*let x =*) unfold_all lib t (*in
	let _ = if id = "list_ind" then print_endline ("[--------unfolded " ^ id ^ "]") else () in
	x*)
       )
     with _ ->
       if is_nuprl_term "TERMOF" term
       then
	 match get_obid_parameters (parameters_of_term term) with
	   Some obid ->
	     (
	      (*print_endline  ("[TERMOF:" ^ obid ^ "]");*)
	      try
		let x = get (MAP.find obid (!tof)) in
		(*let _ = print_endline ("[TERMOF found:" ^ obid ^ "]");
		in*) unfold_all lib x
	      with (*exc ->
		match exc with
		  Failure str ->
		    (print_endline ("[TERMOF(" ^ str ^ ")]"); failwith str)
		|*) _ ->
		    (print_endline ("[TERMOF not found:" ^ obid ^ "]");
		     failwith "unfold_all:not_found")
	     )
	 | None -> failwith "unfold_all:wrong_format"
       else 
	 (*let opid = opid_of_term term in
	 let _ =
	   if opid = "aneris_Replica-program"
	   then
	     let _ = print_endline ("[----couldn't unfold " ^ opid ^ "]") in
	     let _ = print_lib_stats lib in
	     let _ =
	       if is_in_lib lib opid
	       then
		 let sign  = getSignature term in
		 let _ =
		   print_endline
		     ("[----"
		      ^ opid
		      ^ "'s signature: "
		      ^ sign_to_string sign
		      ^ "]") in
		 let items = MAP.find opid (!abs) in
		 let _ =
		   print_endline
		     ("[----"
		      ^ opid
		      ^ "'s signature in library: "
		      ^ items_to_string items
		      ^ "]") in
		 ()
	       else print_endline ("[----" ^ opid ^ "not in lib]")
	     in ()
	   else () in*)
	 TERM (operator, List.map (unfold_all_bterm lib) bterms))
     | VAR_TERM _ -> term
     | LAM_TERM (var, rterm) -> LAM_TERM (var, unfold_all_rterm lib rterm)
     | WAI_TERM (rterm1, rterm2) ->
	 WAI_TERM (unfold_all_rterm lib rterm1,
		   unfold_all_rterm lib rterm2)
     | APP_TERM (rterm1, rterm2) ->
	 APP_TERM (unfold_all_rterm lib rterm1,
		   unfold_all_rterm lib rterm2)
     | PAI_TERM (rterm1, rterm2) ->
	 PAI_TERM (unfold_all_rterm lib rterm1,
		   unfold_all_rterm lib rterm2)
     | AXM_TERM -> term
     | BOT_TERM -> term
     | INT_TERM -> term
     | NAT_TERM _ -> term
     | ATM_TERM _ -> term
     | TOK_TERM _ -> term
     | INL_TERM rterm -> INL_TERM (unfold_all_rterm lib rterm)
     | INR_TERM rterm -> INR_TERM (unfold_all_rterm lib rterm)
     | FIX_TERM rterm -> FIX_TERM (unfold_all_rterm lib rterm)
     | IAX_TERM (ax, rterm1, rterm2) ->
	 IAX_TERM (unfold_all_rterm lib ax,
		   unfold_all_rterm lib rterm1,
		   unfold_all_rterm lib rterm2)
     | IPA_TERM (pair, rterm1, rterm2) ->
	 IPA_TERM (unfold_all_rterm lib pair,
		   unfold_all_rterm lib rterm1,
		   unfold_all_rterm lib rterm2)
     | IEQ_TERM (a, b, rterm1, rterm2) ->
	 IEQ_TERM (unfold_all_rterm lib a,
		   unfold_all_rterm lib b,
		   unfold_all_rterm lib rterm1,
		   unfold_all_rterm lib rterm2)
     | AEQ_TERM (a, b, rterm1, rterm2) ->
	 AEQ_TERM (unfold_all_rterm lib a,
		   unfold_all_rterm lib b,
		   unfold_all_rterm lib rterm1,
		   unfold_all_rterm lib rterm2)
     | DEC_TERM (dec, var1, rterm1, var2, rterm2) ->
	 DEC_TERM (unfold_all_rterm lib dec,
		   var1,
		   unfold_all_rterm lib rterm1,
		   var2,
		   unfold_all_rterm lib rterm2)
     | SPR_TERM (pair, var1, var2, rterm) ->
       SPR_TERM (unfold_all_rterm lib pair,
		 var1,
		 var2,
		 unfold_all_rterm lib rterm)
     | CLO_TERM (rterm, env) ->
	 let (rterm', env') = unfold_all_clos lib (rterm, env) in
	 CLO_TERM (rterm', env')

and unfold_all_clos lib (rterm, env) =
  (unfold_all_rterm lib rterm, unfold_all_env lib env)

and unfold_all_env lib (ENV m) =
  ENV (ENV_MAP.map (unfold_all_rterm lib) m)

and unfold_all_rterm lib rterm = mk_rterm (unfold_all lib (rterm2term rterm))

and unfold_all_bterm lib (B_TERM (vars, term)) =
 B_TERM (vars, unfold_all_rterm lib term)

(* ------ PARTIAL EVALUATION & STRICTNESS ANALYSIS ------ *)

let partial_ev_opt term = term

(* ------ ALPHA EQUIVALENCE ------ *)

let rec alpha_equal_bterms_aux ren (vars1, term1) (vars2, term2) =
 List.length vars1 = List.length vars2
   &&
 let list = SML_ListPair.zip (vars1,vars2) in
 let ren' = insert_list_ren ren list in
 alpha_equal_terms_aux ren' (rterm2term term1) (rterm2term term2)

and alpha_equal_terms_aux ren term1 term2 =
 (is_nuprl_variable_term term1
    &&
  is_nuprl_variable_term term2
    &&
  let v1 = dest_variable 8 term1 in
  let v2 = dest_variable 9 term2 in
  apply_ren ren v1 = v2)
||
 (let (opr1,bterms1) = dest_term term1 in
 let (opr2,bterms2) = dest_term term2 in
 opr1 = opr2
   &&
 List.length bterms1 = List.length bterms2
   &&
 List.for_all
   (fun (bterm1, bterm2) -> alpha_equal_bterms_aux ren bterm1 bterm2)
   (SML_ListPair.zip (bterms1, bterms2)))

let alpha_equal_terms = alpha_equal_terms_aux empty_ren

let mct (term, env) =
 if alpha_equal_terms env mk_nuprl_empty_env_term
 then term
 else mk_nuprl_iclosure_term term env

(* environments *)
let dest_env env =
 match dest_term env with
   (opr,[([w], thunk);([], e)]) -> (w, rterm2term thunk, rterm2term e)
 | _ -> failwith "dest_env"

let rec lookup_binding env var =
 try
   let (w,thunk,e) = dest_env env in
   if w = var
   then Some (dest_pair 6 thunk)
   else lookup_binding e var
 with _ -> None

let rec length_env env =
  try let (_,_,e) = dest_env env in 1 + length_env e
  with _ -> 0

let rec domain env =
  try let (w,thunk,e) = dest_env env in w :: domain e
  with _ -> []

let print_first_env env =
  try let (w,thunk,e) = dest_env env in w ^ ":" ^ toStringTerm thunk
  with _ -> ""

let rec clean_env env vars =
 try
   let (w,thunk,e) = dest_env env in
   if VARS.mem w vars
   then clean_env e vars
   else mk_nuprl_cons_env_term w thunk (clean_env e vars)
 with _ -> env

let rec add_env_bindings' env lst =
 match lst with
   [] -> env
 | (var, term, env') :: bindings ->
     if var = ""
     then add_env_bindings' env bindings
     else
       let (t,e) =
	 if is_nuprl_variable_term term
	 then
	   match lookup_binding env' (dest_variable 10 term) with
	     Some p -> p
	   | None -> (term, env')
	 else (term, env') in
       let pair = mk_pair_term t e in
       let new_env = mk_nuprl_cons_env_term var pair env in
       add_env_bindings' new_env bindings

let add_env_bindings env bindings =
let (vars, bindings') =
  List.fold_right
    (fun ((var, _, _) as b) (vars, bindings) ->
      if var = ""
      then (vars, bindings)
      else (VARS.add var vars, b :: bindings))
    bindings
    (VARS.empty, []) in
add_env_bindings' (clean_env env vars) bindings'

let closure2term' term env =
 let rec aux term bounds env =
   if is_nuprl_iclosure_term term
   then let (t,e) = dest_iclosure term in aux t bounds e
   else if is_nuprl_variable_term term
   then
     let v = dest_variable 11 term in
     if VARS.mem v bounds
     then term
     else
       match lookup_binding env v with
	 Some (t,e) -> aux t bounds e
       | None -> term
   else
     let (opr,bterms) = dest_term term in
     let addBounds vs = addListVARS vs bounds in
     let bterms' = List.map (fun (vs, t) -> (vs, aux (rterm2term t) (addBounds vs) env)) bterms in
     mk_nuprl_term opr bterms' in
 aux term VARS.empty env

let closure2term term env =
 let rec aux term env =
   if is_nuprl_iclosure_term term
   then let (t,e) = dest_iclosure term in aux t e
   else if is_nuprl_variable_term term
   then
     let v = dest_variable 12 term in
     match lookup_binding env v with
       Some (t,e) -> aux t e
     | None -> term
   else
     let (opr,bterms) = dest_term term in
     let bterms' = List.map (fun (vs, t) -> (vs, aux (rterm2term t) (clean_env env (fromListVARS vs)))) bterms in
     mk_nuprl_term opr bterms' in
 aux term env


(* ------ NUPRL TO EventML ------ *)

let lstAlpha =
  ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
   "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w"; "x"; "y"; "z"]

let rec streamId lst pref () =
  match lst with
    [] -> streamId lstAlpha (pref ^ "a") ()
  | x :: xs -> let f = streamId xs pref in NEXT (pref ^ x, f)

let rec is_list term =
 match term with
   TERM ((("cons", _), []), [B_TERM ([], x); B_TERM ([], xs)]) ->
     SML_Option.map (fun lst -> x :: lst) (is_ref_list xs)
 | TERM ((("nil", _), []), []) -> Some []
 | _ -> None

and is_ref_list rterm = is_list (rterm2term rterm)

let isAtomic t =
 let opid = opid_of_term t in
 let lst  = ["variable"; "int"; "pair"; "natural_number"; "prop"; "universe"] in
 List.exists (fun x -> x = opid) lst

let printUkn t n = "-"
   (*(print (toStringTerm t ^ "\n"); "---" ^ Int.toString n)*)

let rec nuprl2eml_term sub term =
 match term with
   TERM ((("apply", _), []), [B_TERM ([], f); B_TERM ([], a)]) ->
     nuprl2eml_ref_atm sub f ^ " " ^ nuprl2eml_ref_atm sub a
 | TERM ((("cons", _), []), [B_TERM ([], x); B_TERM ([], xs)]) ->
     (match is_ref_list xs with
       Some lst -> T.fmt {init = "["; sep = "; "; final = "]"; fmt = nuprl2eml_ref_term sub} (x :: lst)
     | None -> nuprl2eml_ref_term sub x ^ " . " ^ nuprl2eml_ref_term sub xs)
 | TERM ((("subtract", _), []), [B_TERM ([], x); B_TERM ([], y)]) ->
     nuprl2eml_ref_term sub x ^ " - " ^ nuprl2eml_ref_term sub y
 | TERM ((("add", _), []), [B_TERM ([], x); B_TERM ([], y)]) ->
     nuprl2eml_ref_term sub x ^ " + " ^ nuprl2eml_ref_term sub y
 | TERM ((("pair", _), []), [B_TERM ([], x); B_TERM ([], y)]) ->
     "(" ^ nuprl2eml_ref_term sub x ^ "," ^ nuprl2eml_ref_term sub y ^ ")"
 | TERM ((("variable", _), [(v,vkind)]), []) ->
     (try SUB.find v sub with _ -> v)
 | TERM ((("natural_number", _), [(n,nkind)]), []) -> n
 | TERM ((("token", _), [(t,tkind)]), []) -> "`" ^ t ^ "`"
 | TERM ((("lambda", _), []), [B_TERM ([x], f)]) -> printUkn term 0
 | TERM ((("inr", _), []), [B_TERM ([], t)]) ->
     if is_nuprl_ref_term "axiom" t
     then "false" (* NOTE: Arghh, this can be bad because inr(axiom) is not actually equal to false in EML. *)
     else "inr(" ^ nuprl2eml_ref_term sub t ^ ")"
 | TERM ((("inl", _), []), [B_TERM ([], t)]) ->
     if is_nuprl_ref_term "axiom" t
     then "true"
     else "inl(" ^ nuprl2eml_ref_term sub t ^ ")"
 | TERM ((("minus", _), []), [B_TERM ([], t)]) ->
     "~" ^ nuprl2eml_ref_term sub t
 | TERM ((("it", _),   []), []) -> "it"
 | TERM ((("int", _),  []), []) -> "Int"
 | TERM ((("bool", _), []), []) -> "Bool"
 | TERM ((("real", _), []), []) -> "Real"
 | TERM ((("atom", _), []), []) -> "Atom"
 | TERM ((("universe", _), params), []) -> "Type"
 | TERM ((("prop", _), params), []) -> "Prop"
 | TERM ((("list", _), []), [B_TERM ([], t)]) ->
     nuprl2eml_ref_term sub t ^ " List"
				  (* NOTE: This is just a crude hack. For class we should check that the level expression
				   * is 'correct', that the Info is a Msg and that es and e don't occur in t. *)
 | TERM ((("eclass", _), [lvl_exp]), [B_TERM ([], info); B_TERM ([es; e], t)]) ->
     nuprl2eml_ref_term sub t ^ " Class"
 | TERM ((("product", _), []), [B_TERM ([], t1); B_TERM ([""], t2)]) ->
     nuprl2eml_ref_atm sub t1 ^ " * " ^ nuprl2eml_ref_atm sub t2
 | TERM ((("union", _), []), [B_TERM ([], t1); B_TERM ([], t2)]) ->
     nuprl2eml_ref_atm sub t1 ^ " + " ^ nuprl2eml_ref_atm sub t2
 | TERM ((("function", _), []), [B_TERM ([], t1); B_TERM ([""], t2)]) ->
     nuprl2eml_ref_atm sub t1 ^ " -> " ^ nuprl2eml_ref_term sub t2
 | TERM ((("nil", _), []), []) -> "[]"
 | TERM ((("make-Msg", _), []), [B_TERM ([], header); B_TERM ([], typ); B_TERM ([], body)]) ->
     "(" ^ nuprl2eml_ref_term sub header ^ "," ^ nuprl2eml_ref_term sub typ ^ "," ^ nuprl2eml_ref_term sub body ^ ")"
 | VAR_TERM v -> (match SUB.find v sub with _ -> v)
 | LAM_TERM _ -> printUkn term 0
 | WAI_TERM (t, e) -> "wait(" ^ nuprl2eml_ref_atm sub t ^ ", " ^ nuprl2eml_ref_atm sub e ^ ")"
 | APP_TERM (f, a) -> nuprl2eml_ref_atm sub f ^ " " ^ nuprl2eml_ref_atm sub a
 | PAI_TERM (x, y) -> "(" ^ nuprl2eml_ref_term sub x ^ "," ^ nuprl2eml_ref_term sub y ^ ")"
 | NAT_TERM n -> II.to_string n
 | INR_TERM t ->
     if is_nuprl_ref_term "axiom" t
     then "false" (* NOTE: Arghh, this can be bad because inr(axiom) is not actually equal to false in EML. *)
     else "inr(" ^ nuprl2eml_ref_term sub t ^ ")"
 | INL_TERM t ->
     if is_nuprl_ref_term "axiom" t
     then "true"
     else "inl(" ^ nuprl2eml_ref_term sub t ^ ")"
 | DEC_TERM _ -> printUkn term 0
 | SPR_TERM _ -> printUkn term 0
 | _ -> (*printUkn term 1*)
     let ((opid, params), bterms) = dest_term term in
     if null bterms && null params
     then opid
     else printUkn term 1
(*let val ((opid, params), bterms) = dest_term term
in if List.all (fn (vars, t) => List.null vars) bterms
   then foldl (fn ((vars, t), str) => str ^ " " ^ nuprl2eml' t)
	      opid
	      bterms
   else toStringTerm term
end*)

and nuprl2eml_ref_term sub rterm = nuprl2eml_term sub (rterm2term rterm)

and nuprl2eml_atm sub t =
 let str = nuprl2eml_term sub t
 in if isAtomic t then str else "(" ^ str ^ ")"

and nuprl2eml_ref_atm sub rterm = nuprl2eml_atm sub (rterm2term rterm)

let rec nuprl2eml_isect sub stream term =
 match term with
   TERM ((("isect", _), []), [B_TERM ([],  t1); B_TERM ([v], t2)]) ->
     if is_nuprl_ref_term "universe" t1
     then if SUB.exists (fun i _ -> i = v) sub
     then nuprl2eml_ref_isect sub stream t2
     else
       let NEXT (tv, str) = stream () in
       let sub' = SUB.add v tv sub in
       nuprl2eml_ref_isect sub' str t2
     else printUkn term 9
 | _ -> nuprl2eml_term sub term

and nuprl2eml_ref_isect sub stream rterm =
 nuprl2eml_isect sub stream (rterm2term rterm)

let rec nuprl2eml_all id sub stream term =
 match term with
   TERM ((("all", _), []), [B_TERM ([], t1); B_TERM ([v], t2)]) ->
     if is_nuprl_ref_term "universe" t1
     then if SUB.exists (fun i _ -> i = v) sub
     then nuprl2eml_ref_all id sub stream t2
     else
       let NEXT (tv, str) = stream () in
       let sub' = SUB.add v tv sub in
       nuprl2eml_ref_all id sub' str t2
     else printUkn term 2
 | TERM ((("uall", _), []), [B_TERM ([], t1); B_TERM ([v], t2)]) ->
     if is_nuprl_ref_term "universe" t1
     then if SUB.exists (fun i _ -> i = v) sub
     then nuprl2eml_ref_all id sub stream t2
     else
       let NEXT (tv, str) = stream () in
       let sub' = SUB.add v tv sub in
       nuprl2eml_ref_all id sub' str t2
     else printUkn term 3
 | TERM ((("member", _), []), [B_TERM ([], t1); B_TERM ([], t2)]) ->
     if is_nuprl_ref_term id t2
     then nuprl2eml_ref_isect sub stream t1
     else printUkn term 4
 | term -> printUkn term 5

and nuprl2eml_ref_all id sub stream rterm =
 nuprl2eml_all id sub stream (rterm2term rterm)

let nuprl2eml_wf id term =
 match term with
   TERM ((("!theorem", _), [name]), [B_TERM ([], t)]) ->
     nuprl2eml_ref_all id
       (SUB.empty : string SUB.t)
       (streamId lstAlpha "'")
       t
 | term -> printUkn term 6

let nuprl2eml_abs id term =
 match term with
   TERM ((("!abstraction", _), []), [B_TERM ([], cond); B_TERM ([], t1); B_TERM ([], t2)]) ->
     if is_nuprl_ref_term id t1
     then nuprl2eml_ref_term SUB.empty t2
     else printUkn term 7
 | term -> printUkn term 8

let nuprlTerm2eml term = nuprl2eml_term (SUB.empty : string SUB.t) term

(*
(* ------ Nuprl to Haskell ------ *)
let rec nuprl2haskell_term sub term =
 match term with
   TERM ((("apply", _), []), [B_TERM ([], f); B_TERM ([], a)]) ->
     nuprl2haskell_ref_atm sub f ^ " " ^ nuprl2haskell_ref_atm sub a
 | TERM ((("cons", _), []), [B_TERM ([], x); B_TERM ([], xs)]) ->
     (match is_ref_list xs with
       Some lst -> T.fmt {init = "["; sep = ", "; final = "]"; fmt = nuprl2haskell_ref_term sub} (x :: lst)
     | None -> nuprl2haskell_ref_term sub x ^ " : " ^ nuprl2haskell_ref_term sub xs)
 | TERM ((("subtract", _), []), [B_TERM ([], x); B_TERM ([], y)]) ->
     nuprl2haskell_ref_term sub x ^ " - " ^ nuprl2haskell_ref_term sub y
 | TERM ((("add", _), []), [B_TERM ([], x); B_TERM ([], y)]) ->
     nuprl2haskell_ref_term sub x ^ " + " ^ nuprl2haskell_ref_term sub y
 | TERM ((("pair", _), []), [B_TERM ([], x); B_TERM ([], y)]) ->
     "(" ^ nuprl2haskell_ref_term sub x ^ "," ^ nuprl2haskell_ref_term sub y ^ ")"
 | TERM ((("variable", _), [(v,vkind)]), []) ->
     (try SUB.find v sub with _ -> v)
 | TERM ((("natural_number", _), [(n,nkind)]), []) -> n
 | TERM ((("token", _), [(t,tkind)]), []) -> "\"" ^ t ^ "\""
 | TERM ((("lambda", _), []), [B_TERM ([x], f)]) -> printUkn term 0
 | TERM ((("inr", _), []), [B_TERM ([], t)]) ->
     if is_nuprl_ref_term "axiom" t
     then "False" (* NOTE: Arghh, this can be bad because inr(axiom) is not actually equal to false in EML. *)
     else "Inr(" ^ nuprl2haskell_ref_term sub t ^ ")"
 | TERM ((("inl", _), []), [B_TERM ([], t)]) ->
     if is_nuprl_ref_term "axiom" t
     then "True"
     else "Inl(" ^ nuprl2haskell_ref_term sub t ^ ")"
 | TERM ((("minus", _), []), [B_TERM ([], t)]) ->
     "-" ^ nuprl2haskell_ref_term sub t
 | TERM ((("it", _),   []), []) -> "()"
 | TERM ((("int", _),  []), []) -> "NInt"
 | TERM ((("bool", _), []), []) -> "NBool"
 | TERM ((("real", _), []), []) -> "NReal"
 | TERM ((("atom", _), []), []) -> "NAtom"
 | TERM ((("universe", _), params), []) -> "NType"
 | TERM ((("prop", _), params), []) -> "NProp"
 | TERM ((("list", _), []), [B_TERM ([], t)]) ->
     "NList(" ^ nuprl2haskell_ref_term sub t ^ ")"
 | TERM ((("eclass", _), [lvl_exp]), [B_TERM ([], info); B_TERM ([es; e], t)]) ->
     "NClass(" ^ nuprl2haskell_ref_term sub t ^ ")"
 | TERM ((("product", _), []), [B_TERM ([], t1); B_TERM ([""], t2)]) ->
     "NProd (" ^ nuprl2haskell_ref_atm sub t1 ^ ") (" ^ nuprl2haskell_ref_atm sub t2 ^ ")"
 | TERM ((("union", _), []), [B_TERM ([], t1); B_TERM ([], t2)]) ->
     "NUnion (" ^ nuprl2haskell_ref_atm sub t1 ^ ") (" ^ nuprl2haskell_ref_atm sub t2 ^ ")"
 | TERM ((("function", _), []), [B_TERM ([], t1); B_TERM ([""], t2)]) ->
     "NFun (" ^ nuprl2haskell_ref_atm sub t1 ^ ") (" ^ nuprl2haskell_ref_term sub t2 ^ ")"
 | TERM ((("nil", _), []), []) -> "[]"
 | TERM ((("make-Msg", _), []), [B_TERM ([], header); B_TERM ([], typ); B_TERM ([], body)]) ->
     "(" ^ nuprl2haskell_ref_term sub header ^ "," ^ nuprl2haskell_ref_term sub typ ^ "," ^ nuprl2haskell_ref_term sub body ^ ")"
 | VAR_TERM v -> (match SUB.find v sub with _ -> v)
 | LAM_TERM _ -> printUkn term 0
 | APP_TERM (f, a) -> nuprl2haskell_ref_atm sub f ^ " " ^ nuprl2haskell_ref_atm sub a
 | PAI_TERM (x, y) -> "(" ^ nuprl2haskell_ref_term sub x ^ "," ^ nuprl2haskell_ref_term sub y ^ ")"
 | NAT_TERM n -> II.to_string n
 | INR_TERM t ->
     if is_nuprl_ref_term "axiom" t
     then "False" (* NOTE: Arghh, this can be bad because inr(axiom) is not actually equal to false in EML. *)
     else "Inr(" ^ nuprl2haskell_ref_term sub t ^ ")"
 | INL_TERM t ->
     if is_nuprl_ref_term "axiom" t
     then "True"
     else "Inl(" ^ nuprl2haskell_ref_term sub t ^ ")"
 | DEC_TERM _ -> printUkn term 0
 | SPR_TERM _ -> printUkn term 0
 | _ -> raise Failwith "nuprl2haskell"
*)
