(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

  This file is part of VPrl (the Verified Nuprl project).

  VPrl is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  VPrl is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export BinInt.
Require Export Coq.ZArith.ZArith_dec.
Require Export list.
(** printing Z  $\mathbb{Z}$ #Z# *)



(**

  Terms are parametrized by various entities such as atoms ([DSet])
  and propositions ([DProp]) which we use to model Mendler's constants
  in his proof of Nuprl's soundness when adding rec types.

*)

Definition FreshFun (T : Type) :=
  forall (l : list T), {x : T & !LIn x l}.

Record DSet :=
  {
    dsetT : Set;
    dsetDeq : Deq dsetT;
    dsetFresh : FreshFun dsetT
  }.

Definition dset (p : DSet) : Set := dsetT p.

Record POpid :=
  {
    patom   : DSet;
    pconstP : Prop;
    pconstT : Type
  }.

Definition get_patom_set (p : POpid) : Set := dset (patom p).
Definition get_pconstP (p : POpid) : Set := pconstP p.
Definition get_pconstT (p : POpid) : Type := pconstT p.

Definition mk_dset (s : Set) (d : Deq s) (f : FreshFun s) : DSet :=
  {| dsetT := s; dsetDeq := d; dsetFresh := f |}.

Definition get_patom_deq (o : POpid) : Deq (get_patom_set o).
Proof.
  destruct o.
  destruct patom0.
  unfold get_patom_set; simpl; auto.
Defined.

Definition fresh_atom (o : POpid) : FreshFun (get_patom_set o) :=
  dsetFresh (patom o).

(**

  replaces the various parts of a POpid

 *)
Definition set_patom (p : POpid) (d : DSet) : POpid :=
  {| patom := d; pconstP := pconstP p; pconstT := pconstT p|}.

Definition set_pconstP (p : POpid) (d : Prop) : POpid :=
  {| patom := patom p; pconstP := d; pconstT := pconstT p|}.

Definition set_pconstT (p : POpid) (d : Type) : POpid :=
  {| patom := patom p; pconstP := pconstP p; pconstT := d|}.


(* Strings *)

Fixpoint append_string_list (l : list String.string) : String.string :=
  match l with
    | [] => ""
    | s :: l => String.append s (append_string_list l)
  end.

Lemma string_append_assoc :
  forall s1 s2 s3,
    String.append s1 (String.append s2 s3)
    = String.append (String.append s1 s2) s3.
Proof.
  induction s1; introv; allsimpl; auto.
  rw IHs1; auto.
Qed.

Lemma string_length_append :
  forall s1 s2,
    String.length (String.append s1 s2)
    = String.length s1 + String.length s2.
Proof.
  induction s1; introv; allsimpl; auto.
Qed.

Lemma fresh_string : FreshFun String.string.
Proof.
  unfold FreshFun.
  introv.

  exists (String.append "x" (append_string_list l)).
  remember ("x") as extra.
  assert (0 < String.length extra) as len by (subst; simpl; auto).
  clear Heqextra.
  revert dependent extra.
  induction l; introv s; allsimpl; tcsp.
  rw string_append_assoc.
  rw not_over_or; dands; auto;[|apply IHl;rw string_length_append; omega].

  intro k.
  assert (String.length a
          = String.length
              (String.append
                 (String.append extra a)
                 (append_string_list l))) as e by (rw <- k; auto).
  allrw string_length_append.
  omega.
Defined.

Definition dset_string : DSet :=
  mk_dset String.string String.string_dec fresh_string.

Definition set_dset_string (p : POpid) : POpid :=
  set_patom p dset_string.

Definition dec_pconstP (p : POpid) := Deq (pconstP p).
Definition dec_pconstT (p : POpid) := Deq (pconstT p).

Definition dec_consts (p : POpid) := dec_pconstP p # dec_pconstT p.

Definition get_dp {p} (d : dec_consts p) : dec_pconstP p := fst d.
Definition get_dt {p} (d : dec_consts p) : dec_pconstT p := snd d.

Definition nseq := nat -> nat.

Inductive CanInj :=
| NInl : CanInj
| NInr : CanInj.

(* ------ operators ------ *)
(** Here are the Canonical [Opid]s of Nuprl:

*)
Inductive CanonicalOp {p : POpid} : tuniv :=
 (**  %\noindent \\*% Firstly, here are the ones that can be thought
  of data constructors. [NInl], [NInr], [NPair]
  [Nint] correspond to fairly standard
  data constructors in Martin
  Lof's theories. [NAxiom] is the unique canonical
  inhabitant logically fundamental types
  of Nuprl's type system that denote true propositions and for which no
  evidence is required.
  [NSup] is the canonical form representing
  members of the W types of Nuprl.
    %\bigskip%



  *)
 | NLambda    : CanonicalOp
 | NAxiom     : CanonicalOp
 | NInj       : CanInj -> CanonicalOp
 | NPair      : CanonicalOp
 | NSup       : CanonicalOp
 | NRefl      : CanonicalOp
 | Nint       : Z -> CanonicalOp
 | Nseq       : nseq -> CanonicalOp
 | NTok       : String.string -> CanonicalOp
 | NUTok      : get_patom_set p -> CanonicalOp (* Unguessable tokens *)
 (** %\noindent \\*% Like Martin Lof's theories, types are also
  first class terms and can be computed with.
  There is a [CanonicalOp] for each type constructor.
  Here are the [CanonicalOp]s that correspond to
  type constructors. The meanings of most of these types
  will be formally defined in the Chapter %\ref{chapter:type_system}%
  A few of these type-constructors are not currently in use
  (e.g. \coqdocconstructor{NRec}), but they are there for the
  possibility of future experimentation.
    %\bigskip%


  *)
 | NUni           : nat -> CanonicalOp
 | NFreeFromAtom  : CanonicalOp
 | NEFreeFromAtom : CanonicalOp
 | NFreeFromAtoms : CanonicalOp
 | NEquality      : CanonicalOp
 | NREquality     : CanonicalOp
 | NTEquality     : CanonicalOp
 | NInt           : CanonicalOp
 | NAtom          : CanonicalOp
 | NUAtom         : CanonicalOp (* Unguessable atoms *)
 | NBase          : CanonicalOp
 | NFunction      : CanonicalOp
 | NProduct       : CanonicalOp
 | NSet           : CanonicalOp
 | NQuotient      : CanonicalOp
 | NIsect         : CanonicalOp
 | NDIsect        : CanonicalOp
 | NEIsect        : CanonicalOp
 | NW             : CanonicalOp
 | NM             : CanonicalOp
 | NPW            : CanonicalOp
 | NPM            : CanonicalOp
 | NEPertype      : CanonicalOp (* extensional *)
 | NIPertype      : CanonicalOp (* intensional *)
 | NSPertype      : CanonicalOp (* intensional with a strong equality *)
 | NPartial       : CanonicalOp
 | NTExc          : CanonicalOp
 | NUnion         : CanonicalOp
 | NEUnion        : CanonicalOp
 | NUnion2        : CanonicalOp
 | NTUnion        : CanonicalOp
 | NApprox        : CanonicalOp
 | NCequiv        : CanonicalOp
 | NCompute       : CanonicalOp
 | NRec           : CanonicalOp
 | NImage         : CanonicalOp
 | NAdmiss        : CanonicalOp
 | NMono          : CanonicalOp
 | NOmega         : CanonicalOp
 | NConstP        : get_pconstP p -> CanonicalOp
 | NConstT        : get_pconstT p -> CanonicalOp.
(* | NEsquash  : CanonicalOp (* extensional squash *)*)

(* Omega and constants are used in Mendler's thesis (Section 5.1) *)

Definition opsign := list nat.

(** %\noindent \\*% Now we define the binding structure for each
    [CanonicalOp]. Recall that the the length of
    [OpBindingsCan c] represents
    the number of arguments([BTerm]s) required
    to form an [NTerm] using this the [CanonicalOp] [c].
    The $i^{th}$ element [OpBindingsCan c] represents
    the number of bound variables in the $i^{th}$ argument.

*)
Definition OpBindingsCan {p} (c : @CanonicalOp p) : opsign :=
  match c with
  | NLambda        => [1]
  | NAxiom         => []
  | NInj _         => [0]
  | NPair          => [0,0]
  | NSup           => [0,0]
  | NRefl          => [0]
  | Nint _         => []
  | Nseq _         => []
  | NUni _         => []
  | NTok _         => []
  | NUTok _        => []
  | NFreeFromAtom  => [0,0,0]
  | NEFreeFromAtom => [0,0,0]
  | NFreeFromAtoms => [0,0]
  | NEquality      => [0,0,0]
  | NREquality     => [0,0,0]
  | NTEquality     => [0,0]
  | NInt           => []
  | NBase          => []
  | NAtom          => []
  | NUAtom         => []
  | NFunction      => [0,1]
  | NProduct       => [0,1]
  | NSet           => [0,1]
  | NIsect         => [0,1]
  | NDIsect        => [0,1]
  | NEIsect        => [0,1]
  | NW             => [0,1]
  | NM             => [0,1]
  | NPW            => [0,1,2,3,0]
  | NPM            => [0,1,2,3,0]
  | NEPertype      => [0]
  | NIPertype      => [0]
  | NSPertype      => [0]
  | NPartial       => [0]
  | NTExc          => [0,0]
  | NUnion         => [0,0]
  | NEUnion        => [0,0]
  | NUnion2        => [0,0]
  | NTUnion        => [0,1]
  | NApprox        => [0,0]
  | NCequiv        => [0,0]
  | NCompute       => [0,0,0]
  | NRec           => [1]
  | NImage         => [0,0]
  | NQuotient      => [0,2]
  | NAdmiss        => [0]
  | NMono          => [0]
  | NOmega         => []
  | NConstP _      => []
  | NConstT _      => []
  end.
(*  | NEsquash  => [0]*)

(** %\noindent \\*% Now, we will define non-canonical [Opid]s of Nuprl.
    Intuitively, these represent the elimination forms
    corresponding to some of the canonical terms of Nuprl.
    For example, [NApply] represents the elimination form
    for the [CanonicalOp] [NLambda].
    Notably, there are no elimination forms
    for the [CanonicalOp]s that represent
    type constructors. We also have some arithmetic
    and comparison operators on numbers.
    We will define 3 more parameters for defining
    the type [NonCanonicalOp].

 *)

Inductive ArithOp : Set :=
 | ArithOpAdd : ArithOp
 | ArithOpMul : ArithOp
 | ArithOpSub : ArithOp
 | ArithOpDiv : ArithOp
 | ArithOpRem : ArithOp.



Inductive ComparisonOp : Set :=
 | CompOpLess : ComparisonOp
 | CompOpEq   : ComparisonOp.

(*
  This is repeating CanonicalOp, can't we just use CanonicalOp.
  If we were to use CanonicalOp, one issue might be that there will
  be a infinite number of ways to build isint: isint (int 0),
  isint (int 1)...
*)

(** %\noindent \\*% The following type parametrizes some [NonCanonicalOp]s
    that test the head normal form of a term.

 *)

Inductive CanonicalTest : Set :=
 | CanIspair   : CanonicalTest
 | CanIssup    : CanonicalTest
 | CanIsaxiom  : CanonicalTest
 | CanIslambda : CanonicalTest
 | CanIsint    : CanonicalTest
 | CanIsinl    : CanonicalTest
 | CanIsinr    : CanonicalTest
 | CanIsatom   : CanonicalTest
 | CanIsuatom  : CanonicalTest.

Definition exc_name {p} := option (get_patom_set p).

Definition deq_exc_name {p} : Deq (@exc_name p).
Proof.
  introv.
  destruct x, y; tcsp; try (destruct (get_patom_deq p g g0); subst; tcsp);
  right; introv k; ginv; tcsp.
Defined.

(** %\noindent \\*% Finally, here are the noncanonical [Opid]s of Nuprl:


 *)

Inductive NonCanonicalOp : Set :=
 | NApply     : NonCanonicalOp
 | NEApply    : NonCanonicalOp
(* | NApseq     : nseq -> NonCanonicalOp*)
 | NFix       : NonCanonicalOp
 | NSpread    : NonCanonicalOp
 | NDsup      : NonCanonicalOp
 | NDecide    : NonCanonicalOp
 | NCbv       : NonCanonicalOp
 | NSleep     : NonCanonicalOp
 | NTUni      : NonCanonicalOp
 | NMinus     : NonCanonicalOp
 | NFresh     : NonCanonicalOp
 | NTryCatch  : NonCanonicalOp (* named try/catch *)
 | NParallel  : NonCanonicalOp
 | NCompOp    : ComparisonOp  -> NonCanonicalOp
 | NArithOp   : ArithOp       -> NonCanonicalOp
 | NCanTest   : CanonicalTest -> NonCanonicalOp.

Fixpoint list_of_i (i : nat) (n : nat) :=
  match n with
    | 0 => []
    | S m => i :: list_of_i i m
  end.

Definition OpBindingsNCan (nc : NonCanonicalOp) : opsign :=
  match nc with
  | NApply       => [0,0]
  | NEApply      => [0,0]
(*  | NApseq _     => [0]*)
  | NFix         => [0]
  | NSpread      => [0,2]
  | NDsup        => [0,2]
  | NDecide      => [0,1,1]
  | NCbv         => [0,1]
  | NSleep       => [0]
  | NTUni        => [0]
  | NMinus       => [0]
  | NFresh       => [1] (* fresh(x.e[x]) generates a fresh atom "a" and subst x for "a" in "e" *)
  | NTryCatch    => [0,0,1] (* 1: try part; 2: name; 3: catch part*)
  | NParallel    => [0,0]
  | NCompOp    _ => [0,0,0,0]
  | NArithOp   _ => [0,0]
  | NCanTest   _ => [0,0,0]
  end.

(**  %\noindent \\*% [NFix] represents the fixpoint combinator.
    [NSpread] is the elimination form for [NPair].
    The first argument of [NSpread] is supposed to be
    a [BTerm] with no bound variables such that the underlying
    [NTerm] converges to something with head [Opid] as [NPair].
    The second argument is a [BTerm] with two bound
    variables. These variables indicate the positions
    where the two components of the pair will be
    substituted in. The binding structure of the other
    [NonCanonicalOp]s can be understood similarly.
    More details will be available later when we define
    the computation system in the next chapter.

    [NDecide] is the elimination form for [NInl] and [NInr].
    [NCbv] the call-by-value variant of application.
    It evaluates its first argument down to a value before
    substituting it into the second argument that is a bound
    term with one bound variable.

*)

(* begin hide *)

Definition marker := String.string.

(* end hide *)

Inductive ptype : tuniv :=
| pt_utoken : ptype
| pt_int : ptype
| pt_var : ptype
| pt_level : ptype.

(* Theses could also be variables & add atoms *)
Inductive pvalue : ptype -> tuniv :=
| pv_int : Z -> pvalue pt_int
| pv_level : nat -> pvalue pt_level.

Inductive parameter : tuniv :=
| param : forall pt : ptype, pvalue pt -> parameter.

Definition opname := String.string.

Record opabs :=
  {
    opabs_name : opname;
    opabs_params : list parameter;
    opabs_sign : opsign
  }.

Definition dum_opabs : opabs :=
  {|
    opabs_name := "" ;
    opabs_params := [] ;
    opabs_sign := []
  |}.

Inductive Opid {p} : tuniv :=
| Can  : @CanonicalOp p -> Opid
| NCan : NonCanonicalOp -> Opid
| Exc  : Opid
| Abs  : opabs -> Opid.

(** %\noindent \\*% The following function defines
    the binding structure of any [Opid].
    It was used in the definition of
    [nt_wf].


*)
Definition OpBindings {p} (op : @Opid p) : opsign :=
  match op with
    | Can c     => OpBindingsCan c
    | NCan nc   => OpBindingsNCan nc
    | Exc       => [0,0] (* 1: name; 2: value *)
    | Abs opabs => opabs_sign opabs
  end.

(* begin hide *)

Lemma eq_can {p} :
  forall (c1 c2 : @CanonicalOp p), c1 = c2 -> Can c1 = Can c2.
Proof.
  introv e; subst; auto.
Qed.

Tactic Notation "dopid" ident(o) "as" simple_intropattern(I) ident(c) :=
  destruct o as I;
  [ Case_aux c "Can"
  | Case_aux c "NCan"
  | Case_aux c "Exc"
  | Case_aux c "Abs"
  ].


Tactic Notation "dopid_noncan" ident(onc) ident(c) :=
  destruct onc;
  [ Case_aux c "NApply"
  | Case_aux c "NEApply"
(*  | Case_aux c "NApseq"*)
  | Case_aux c "NFix"
  | Case_aux c "NSpread"
  | Case_aux c "NDsup"
  | Case_aux c "NDecide"
  | Case_aux c "NCbv"
  | Case_aux c "NSleep"
  | Case_aux c "NTUni"
  | Case_aux c "NMinus"
  | Case_aux c "NFresh"
  | Case_aux c "NTryCatch"
  | Case_aux c "NParallel"
  | Case_aux c "NCompOp"
  | Case_aux c "NArithOp"
  | Case_aux c "NCanTest"
  ].



(* end hide *)

(** The only requirement for defining [CanonicalOp]
    and [NonCanonicalOp] is that equality
    must be decidable in these types.
    We prove the folowing lemma by straightforward
    case analysis.

 *)

Definition no_seq_can {o} (c : @CanonicalOp o) :=
  match c with
    | Nseq _ => false
    | _ => true
  end.

(*
Definition no_seq_ncan (nc : NonCanonicalOp) :=
  match nc with
    | NApseq _ => false
    | _ => true
  end.
*)

Definition no_seq_o {o} (op : @Opid o) :=
  match op with
    | Can c => no_seq_can c
(*    | NCan c => no_seq_ncan c*)
    | _ => true
  end.

Definition can_inj_deq : Deq CanInj.
Proof.
  introv.
  destruct x, y; tcsp; right; intro h; ginv.
Defined.

Lemma canonical_dec {o} :
  dec_consts o
  -> forall x y : @CanonicalOp o,
       assert (no_seq_can x)
       -> {x = y} + {x <> y}.
Proof.
  introv dc ns.
  destruct x; destruct y;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).

  - destruct (can_inj_deq c c0) as [d|d]; subst; tcsp.
    right; intro k; ginv; tcsp.

  - destruct (Z_noteq_dec z z0) as [d|d]; subst; tcsp.
    right; intro k; ginv; tcsp.

  - destruct (String.string_dec s s0) as [d|d]; subst; tcsp.
    right; intro k; ginv; tcsp.

  - assert (Deq (get_patom_set o)) as d by (destruct o; destruct patom0; auto).
    pose proof (d g g0) as h; dorn h; subst; sp.
    right; intro k; inversion k; sp.

  - destruct (deq_nat n n0) as [d|d]; subst; tcsp.
    right; intro k; ginv; tcsp.

  - destruct (get_dp dc g g0) as [d|d]; subst; tcsp.
    right; intro k; ginv; tcsp.

  - destruct (get_dt dc g g0) as [d|d]; subst; tcsp.
    right; intro k; ginv; tcsp.
Qed.

Lemma parameter_dec : Deq parameter.
Proof.
  introv.
  destruct x, y.
  destruct pt, pt0;
  try (complete (right; intro k; inversion k; sp));
  destruct p, p0;
  try (complete (right; intro k; inversion k; sp));
  try (complete (pose proof (Z_noteq_dec z z0) as h;
                 dorn h; subst; tcsp;
                 right; intro k; inversion k; subst; omega));
  try (complete (assert (Deq (get_patom_set p)) as d by (destruct p; destruct patom0; auto);
                 pose proof (d g g0) as h; dorn h; subst; sp;
                 right; intro k; inversion k; sp));
  try (complete (pose proof (deq_nat n n0) as h;
                 dorn h; subst; tcsp;
                 right; intro k; inversion k; subst; omega)).
Defined.

Lemma parameters_dec : Deq (list parameter).
Proof.
  apply deq_list.
  apply parameter_dec.
Defined.

Lemma opsign_dec : Deq opsign.
Proof.
  apply deq_list.
  introv; apply deq_nat.
Defined.

Lemma opid_dec {o} :
  dec_consts o
  -> forall x y : @Opid o,
       assert (no_seq_o x)
       -> {x = y} + {x <> y}.
Proof.
  introv dc ns.
  introv.
  dopid x as [can1|ncan1|exc1|abs1] Case;
  dopid y as [can2|ncan2|exc2|abs2] SCase;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).

  - Case "Can"; SCase "Can".
    pose proof (canonical_dec dc can1 can2) as h; destruct h as [h|h]; subst;
    tcsp;
    try (right; intro k; inversion k; subst; sp; fail).

  - destruct ncan1; destruct ncan2;
    try (left; auto; fail);
    try (right; sp; inversion H; fail).
    + try destruct c; try destruct c0;
      try (left; auto; fail);
      try (right; sp; inversion H; fail).
    + try destruct a; try destruct a0;
      try (left; auto; fail);
      try (right; sp; inversion H; fail).
    + try destruct c; try destruct c0;
      try (left; auto; fail);
      try (right; sp; inversion H; fail).

  - destruct abs1, abs2.
    pose proof (String.string_dec opabs_name0 opabs_name1) as h.
    dorn h; subst; tcsp; try (complete (right; intro x; inversion x; sp)).
    pose proof (parameters_dec opabs_params0 opabs_params1) as h.
    dorn h; subst; tcsp; try (complete (right; intro x; inversion x; sp)).
    pose proof (opsign_dec opabs_sign0 opabs_sign1) as h.
    dorn h; subst; tcsp; try (complete (right; intro x; inversion x; sp)).
Qed.

(* begin hide *)

Definition no_const_c {o} (c : @CanonicalOp o) :=
  match c with
    | NConstP _ => false
    | NConstT _ => false
    | _ => true
  end.

Definition no_const_o {o} (op : @Opid o) :=
  match op with
    | Can c => no_const_c c
    | _ => true
  end.

Lemma canonical_dec_no_const {p} :
  forall x y : @CanonicalOp p,
    assert (no_const_c x)
    -> assert (no_seq_can x)
    -> {x = y} + {x <> y}.
Proof.
  introv nc ns.
  destruct x; destruct y; allsimpl;
  try (left; auto; fail);
  try (right; sp; inversion H; fail);
  try (complete (inversion nc)).

  - destruct (can_inj_deq c c0) as [d|d]; subst; tcsp.
    right; intro k; ginv; tcsp.

  - destruct (Z_noteq_dec z z0) as [d|d]; subst; tcsp.
    right; intro k; ginv; tcsp.

  - destruct (String.string_dec s s0) as [d|d]; subst; tcsp.
    right; intro k; ginv; tcsp.

  - assert (Deq (get_patom_set p)) as d by (destruct p; destruct patom0; auto).
    pose proof (d g g0) as h; dorn h; subst; sp.
    right; intro k; inversion k; sp.

  - destruct (deq_nat n n0) as [d|d]; subst; tcsp.
    right; intro k; ginv; tcsp.
Qed.

Lemma opid_dec_no_const {p} :
  forall x y : @Opid p,
    assert (no_const_o x)
    -> assert (no_seq_o x)
    -> {x = y} + {x <> y}.
Proof.
  introv nc ns.
  dopid x as [can1|ncan1|exc1|abs1] Case;
  dopid y as [can2|ncan2|exc2|abs2] SCase;
  try (left; auto; fail);
  try (right; sp; inversion H; fail).

  - pose proof (canonical_dec_no_const can1 can2 nc) as h; destruct h as [h|h]; subst;
    tcsp;
    try (right; intro k; inversion k; subst; sp; fail).

  - destruct ncan1; destruct ncan2;
    try (left; auto; fail);
    try (right; sp; inversion H; fail).
    + try destruct c; try destruct c0;
      try (left; auto; fail);
      try (right; sp; inversion H; fail).
    + try destruct a; try destruct a0;
      try (left; auto; fail);
      try (right; sp; inversion H; fail).
    + try destruct c; try destruct c0;
      try (left; auto; fail);
      try (right; sp; inversion H; fail).

  - destruct abs1, abs2.
    pose proof (String.string_dec opabs_name0 opabs_name1) as h.
    dorn h; subst; tcsp; try (complete (right; intro x; inversion x; sp)).
    pose proof (parameters_dec opabs_params0 opabs_params1) as h.
    dorn h; subst; tcsp; try (complete (right; intro x; inversion x; sp)).
    pose proof (opsign_dec opabs_sign0 opabs_sign1) as h.
    dorn h; subst; tcsp; try (complete (right; intro x; inversion x; sp)).
Qed.

Lemma decidable_eq_opabs_name :
  forall oa1 oa2, decidable (opabs_name oa1 = opabs_name oa2).
Proof.
  introv.
  destruct oa1, oa2; simpl.
  pose proof (String.string_dec opabs_name0 opabs_name1); sp.
Qed.
Hint Immediate decidable_eq_opabs_name.

Lemma decidable_eq_opabs_sign :
  forall oa1 oa2, decidable (opabs_sign oa1 = opabs_sign oa2).
Proof.
  introv.
  destruct oa1, oa2; simpl.
  pose proof (opsign_dec opabs_sign0 opabs_sign1); sp.
Qed.
Hint Immediate decidable_eq_opabs_sign.

Lemma dec_op_eq_axiom {o} :
  forall (op : @Opid o),
    decidable (op = Can NAxiom).
Proof.
  introv; unfold decidable.
  destruct op; try (complete (right; sp; ginv)).
  destruct c; tcsp; try (complete (right; sp; ginv)).
Qed.

(* end hide *)
