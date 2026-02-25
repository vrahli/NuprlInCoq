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


(*Set Universe Polymorphism.*)
Require Export cequiv.
Require Export universe2.
Require Export atoms.
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ #⪯# *)
(** printing ~=~  $\sim$ #~# *)
(* printing ===>  $\longmapsto$ *)
(** printing ===>  $\Downarrow$ #⇓# *)
(** printing ===e>  $\Downarrow$ #⇓_{e}# *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)
(** printing <=2=> $\Leftarrow\!\!{\scriptstyle{2}}\!\!\Rightarrow$ *)
(* begin hide *)


(* Prop/Type exists depending on the switch universe2-type.v/universe2-prop.v *)
Notation "{ a , b : T , P }" :=
  {a : T , {b : T , P}}
    (at level 0, a at level 99, b at level 99).
Notation "{ a , b , c : T , P }" :=
  {a : T , {b : T , {c : T , P}}}
    (at level 0, a at level 99, b at level 99, c at level 99).
Notation "{ a , b , c , d : T , P }" :=
  {a : T , {b : T , {c : T , {d : T , P}}}}
    (at level 0, a at level 99, b at level 99, c at level 99, d at level 99).
Notation "{ a , b , c , d , e : T , P }" :=
  {a : T , {b : T , {c : T , {d : T , {e : T , P}}}}}
    (at level 0, a at level 99, b at level 99, c at level 99, d at level 99, e at level 99).
Notation "{ a , b , c , d , e , f : T , P }" :=
  {a : T , {b : T , {c : T , {d : T , {e : T , {f : T , P}}}}}}
    (at level 0, a at level 99, b at level 99, c at level 99, d at level 99, e at level 99, f at level 99).



(* ==================================================================
 *
 * This is like per_type.v but I changed the definition of function
 * types, i.e., per_func.
 *)



(*
We can't define that per type because the PER_lambda case contains a
non-strictly positive occurrence of the type we're defining.

Inductive per : NTerm -> NTerm -> NTerm -> Prop :=
  | PER_int : forall n1 n2 : nat, n1 = n2 -> per (mk_nat n1) (mk_nat n2) mk_int
  | PER_inl : forall a a' A B : NTerm,
                per_type (mk_union A B) (mk_union A B)
                -> per a a' A
                -> per (mk_inl a) (mk_inl a') (mk_union A B)
  | PER_inr : forall b b' A B : NTerm,
                per_type (mk_union A B) (mk_union A B)
                -> per b b' B
                -> per (mk_inr b) (mk_inr b') (mk_union A B)
  | PER_pair : forall v : NVar,
               forall a b a' b' A B A' B' : NTerm,
                 per_type (mk_product A v B) (mk_product A' v B')
                 -> per a a' A
                 -> per b b' (substitute v a B)
                 -> per (mk_pair a b) (mk_pair a' b') (mk_product A v B)
  | PER_lambda : forall v : NVar,
                 forall a b a' b' A B A' B' : NTerm,
                   per_type (mk_function A v B) (mk_function A' v B')
                   -> (forall a a' : NTerm, per a a' A
                                            -> per (substitute v a b)
                                                   (substitute v a' b')
                                                   (substitute v a B))
                   -> per (mk_lam v b) (mk_lam v b') (mk_product A v B)
with per_type : NTerm -> NTerm -> Prop :=
  | PERT_union : forall A B A' B' : NTerm,
                   per_type A A'
                   -> per_type B B'
                   -> per_type (mk_union A B) (mk_union A' B').
*)

(*
Fixpoint per  (t1 t2 T:NTerm): Prop :=
 (exists n1, (NuprlComput t1 (mk_nat n1))
              /\ (NuprlComput t2 (mk_nat n1))
              /\ (NuprlComput T mk_int) )

      \/
  (exists v1, exists  b1, exists v2, exists b2, exists A, exists B , exists v,
               NuprlComput t1 (mk_lam v1 b1)
                /\ NuprlComput t2 (mk_lam v2 b2)
                /\ NuprlComput T (mk_function A v B)
                /\ forall a1 a2, per a1 a2 A
                   -> per b1 b2 B )
.
Error: Cannot guess decreasing argument of fix.
*)

(* the following definition works when no more computation is to be done
   everything is a value which neednot be evaluated further.
   dependent types have lambdas which need to be evaluated further
   we close perf under computation in perfcc.
   perfcc works for non-dependent types
  (does it work for bar tyes?
   theoretically it might be possible to define complexity ordering
    and then incorporating computation inside perf as in per above
   and prove that complexity does not change with computation .
  )
  *)

(*
Inductive per_semantics : term_equality -> NTerm -> NTerm -> Prop :=
  | PEReq : forall eq eqa : term_equality,
            forall T1 T2 a1 a2 b1 b2 A B : NTerm,
               NuprlComput T1 (mk_equality a1 a2 A)
            -> NuprlComput T2 (mk_equality b1 b2 B)
            -> per_semantics eqa A B
            -> eqa a1 b1
            -> eqa a2 b2
            -> (forall t t' : NTerm,
                   eq t t'
                   <->
                   (NuprlComput t mk_axiom
                    /\ NuprlComput t' mk_axiom
                    /\ eqa a1 a2))
            -> per_semantics eq T1 T2.
*)

(* ------ These definitions come from Crary's thesis ------ *)

(* end hide *)

(**

  After that brief excursion to Agda, we come back to the Coq world
  where there is no induction-recursion, but there is a powerful
  tactic language to probably more than offset the inconveniences
  caused by the lack of induction-recursion.

  We follow Allen's PER semantics method%~\cite{Allen:1987b}% and use
  pure induction to define Nuprl's types as partial equivalence
  relations on closed terms.

 *)

(* begin hide *)

Definition term_equality {p} := @CTerm p -> @CTerm p -> [U].

(* end hide *)

(**

  A type is a partial equivalence relation that specifies which pairs
  of closed terms are equal in the types.  Therefore, a partial
  equivalence relation can be seen as a type and vice-versa.

 *)

Notation per := (CTerm -> CTerm -> [U]).
Notation "per( p )" := (@CTerm p -> @CTerm p -> [U]).

(**

  Note that [[U]] here can either be [Prop] or [Type].  This allows us
  to have a uniform notation and to easily switch between our Nuprl
  impredicative meta-theory that uses Coq's [Prop] where we can define
  Nuprl's full hierarchy of universes, and our predicative meta-theory
  that uses Coq's [Type] hierarchy of types to define $n$ Nuprl
  universes using $n+1$ Coq [Type] levels.  This issue will be further
  discussed below when defining Nuprl's universes of types.  Also,
  because everything so far has been defined using [Type], in the case
  where [[U]] is [Prop], we need to cast into [Prop] the types we need
  in order to define the Nuprl type system.  For example [capproxc t1
  t2] is [Cast (approxc t1 t2)] in the [Prop] case and [approxc t1 t2]
  in the [Type] case, where [Cast] casts types in [Type] into
  propositions in [Prop], and where the first [c] stands for ``cast''.
  Note that we do not currently use the same type system definitions
  for both our meta-theories because of Coq's lack of universe
  polymorphism and the fact that we currently have to duplicate our
  code at each level of our hierarchy of Nuprl types in our
  predicative meta-theory.  Only the sequents and rules definitions
  and lemmas are shared by both meta-theories.  However, we anticipate
  that we will be able to share this code when Coq will have universe
  polymorphism.

  We also introduce the following useful notation:

[Notation "a ~<~ b" := (capproxc a b) (at level 0).]

[Notation "a ~=~ b" := (ccequivc a b) (at level 0).]

[Notation "a ===> b" := (ccomputes_to_valc a b) (at level 0).]

*)

(**

  We say that two term equalities are equal if they define the same
  relation.

 *)

Definition eq_term_equals {p} (eq1 eq2 : per) :=
  forall t1 t2 : @CTerm p, eq1 t1 t2 <=> eq2 t1 t2.

Notation "eq1 <=2=> eq2" := (eq_term_equals eq1 eq2) (at level 0).

(* begin hide *)

Lemma eq_term_equals_refl {p} :
  forall eq : per(p), eq <=2=> eq.
Proof.
  unfold eq_term_equals; sp.
Qed.
Hint Immediate eq_term_equals_refl.

Lemma eq_term_equals_sym {p} :
  forall eq1 eq2 : per(p),
    (eq1 <=2=> eq2) <=> (eq2 <=2=> eq1).
Proof.
  unfold eq_term_equals; repeat (sp; split; sp); allrw; sp; allrw <-; sp.
Qed.

Lemma eq_term_equals_trans {p} :
  forall eq1 eq2 eq3 : per(p),
    (eq1 <=2=> eq2) -> (eq2 <=2=> eq3) -> (eq1 <=2=> eq3).
Proof.
  unfold eq_term_equals.
  introv h1 h2; split; intro h.
  - apply h2; apply h1; auto.
  - apply h1; apply h2; auto.
Qed.

Lemma fold_eq_term_equals {p} :
  forall (eq1 eq2 : per(p)),
    (forall t1 t2, eq1 t1 t2 <=> eq2 t1 t2)
      <=> (eq1 <=2=> eq2).
Proof. sp. Qed.

(* end hide *)

(* begin hide *)

Definition candidate_type_system {p} := @CTerm p -> @CTerm p -> per(p) -> [U].

(* end hide *)

(**

  A candidate type system is a ternary relation that, intuitively,
  holds of the triple $(T_1,T_2,R)$ if $T_1$ and $T_2$ are equal types
  and $R$ is their equality relation.  As we explain below, a type
  system is a [candidate-type-system] (or [cts] for short) that
  satisfies properties such as symmetry and transitivity.

 *)

Notation "candidate-type-system" :=
  (CTerm -> CTerm -> per -> [U]).

Notation cts := (CTerm -> CTerm -> per -> [U]).
Notation "cts( p )" := (@CTerm p -> @CTerm p -> per(p) -> [U]).

(* begin hide *)

Notation "a ~<~ b" := (capproxc a b) (at level 0).
Notation "a ~<~( lib ) b" := (capproxc lib a b) (at level 0).
Notation "a ~=~ b" := (ccequivc a b) (at level 0).
Notation "a ~=~( lib ) b" := (ccequivc lib a b) (at level 0).
Notation "a ===> b" := (ccomputes_to_valc a b) (at level 0).
Notation "a ===>( lib ) b" := (ccomputes_to_valc lib a b) (at level 0).
Notation "a ===e>( lib , e ) b" := (ccomputes_to_excc lib e a b) (at level 0).
Notation "T [[ v \\ a ]]" := (substc a v T) (at level 0).

(* end hide *)


(* begin hide *)


(* ------ types definitions ------ *)

(* end hide *)

(**
    For a [cts] [c], [c T1 T2 eq] asserts that [T1] and [T2] are
    equal types in the type system [c] and that [eq] is the
    PER of this type.

   For each type constructor of the form [mkc_TyCons],
   we define a monotone operator [per_TyCons] on candidate type systems.
   Intuitively,
   each constructor [per_TyCons] takes a
   candidate type system [ts] and returns a new candidate type system
   where all the types are of the form [TyCons(T1,...,Tn)] where [T1],
   ..., [Tn] are types from [ts] (n could be 0, as in the case of Integer type).

   Once we have defined all the type constructors of the theory, we
   can define an operator that takes a candidate type system [ts] and
   builds the least fixed point of the closure of [ts] under the
   various type constructors of the theory.  This operator is the
   [close] operator defined below, which is the $\mu$ operator defined
   by Allen in his thesis%~\cite[section~4.2,page~52]{Allen:1987b}%
   and the ``CLOSE'' operator defined by Crary in his
   thesis%~\cite[section~4.8,page~52]{Crary:1998}%

   The integer type is defined as follows: The two types have to
   compute to the integer type [mkc_int] and two terms are equal in
   the integer type if they both compute to the same integer
   [mkc_integer n] for some Coq integer n.

 *)

Definition equality_of_int {p} lib (n m : @CTerm p) :=
  {k : Z , n ===>(lib) (mkc_integer k)
         # m ===>(lib) (mkc_integer k)}.

Definition per_int {p} lib (ts : cts(p)) (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  T1 ===>(lib) mkc_int
  # T2 ===>(lib) mkc_int
  # forall t t', eq t t' <=> equality_of_int lib t t'.

(**

  Nuprl has two kinds of atom types.  One that is similar to strings
  and one that is similar to ur-elements.

*)

Definition equality_of_atom {p} lib (a b : @CTerm p) :=
  {s : String.string , a ===>(lib) (mkc_token s)
                     # b ===>(lib) (mkc_token s)}.

Definition per_atom {p} lib (ts : cts(p)) (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  T1 ===>(lib) mkc_atom
  # T2 ===>(lib) mkc_atom
  # eq <=2=> (equality_of_atom lib).


Definition equality_of_uatom {p} lib (a b : @CTerm p) :=
  {u : get_patom_set p , a ===>(lib) (mkc_utoken u)
                       # b ===>(lib) (mkc_utoken u)}.

Definition per_uatom {p} lib (ts : cts(p)) (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  T1 ===>(lib) mkc_uatom
  # T2 ===>(lib) mkc_uatom
  # eq <=2=> (equality_of_uatom lib).


(**

  The ``free from atom`` type expresses that an equivalence class
  w.r.t. a type does not contain a given atom.

*)

Definition per_ffatom_eq {p}
           lib
           (eqa : per)
           (u : get_patom_set p)
           (x t1 t2 : @CTerm p) :=
    t1 ===>(lib) mkc_axiom
  # t2 ===>(lib) mkc_axiom
  # {y : CTerm , eqa x y # !LIn u (getc_utokens y)}.

Definition per_ffatom {p} lib (ts : cts(p)) (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
   {A1 , A2 , x1 , x2 , a1 , a2 : CTerm
   , {eqa : per
   , {u : get_patom_set p
      , T1 ===>(lib) (mkc_free_from_atom A1 x1 a1)
      # T2 ===>(lib) (mkc_free_from_atom A2 x2 a2)
      # ts A1 A2 eqa
      # eqa x1 x2
      # a1 ===>(lib) (mkc_utoken u)
      # a2 ===>(lib) (mkc_utoken u)
      # eq <=2=> (per_ffatom_eq lib eqa u x1)}}}.

Definition name_not_in_upto {o} lib (a x : @CTerm o) (eqa : per) :=
  {u : get_patom_set o
   , {y : CTerm
   , a ===>(lib) (mkc_utoken u)
   # eqa x y
   # !LIn u (getc_utokens y)}}.

Definition per_effatom_eq {p}
           lib
           (eqa : per)
           (a x t1 t2 : @CTerm p) :=
    t1 ===>(lib) mkc_axiom
  # t2 ===>(lib) mkc_axiom
  # name_not_in_upto lib a x eqa.

Definition per_effatom {p} lib (ts : cts(p)) (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
   {A1 , A2 , x1 , x2 , a1 , a2 : CTerm
   , {eqa : per
      , T1 ===>(lib) (mkc_efree_from_atom A1 x1 a1)
      # T2 ===>(lib) (mkc_efree_from_atom A2 x2 a2)
      # ts A1 A2 eqa
      # (name_not_in_upto lib a1 x1 eqa <=> name_not_in_upto lib a2 x2 eqa)
      # eq <=2=> (per_effatom_eq lib eqa a1 x1)}}.

Definition noutokensc {o} (t : @CTerm o) := noutokens (get_cterm t).

Definition per_ffatoms_eq {p}
           lib
           (eqa : per)
           (x t1 t2 : @CTerm p) :=
    t1 ===>(lib) mkc_axiom
  # t2 ===>(lib) mkc_axiom
  # {y : @CTerm p , eqa x y # noutokensc y}.

Definition per_ffatoms {p} lib (ts : cts(p)) (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
   {A1 , A2 , x1 , x2 : CTerm
   , {eqa : per
      , T1 ===>(lib) (mkc_free_from_atoms A1 x1)
      # T2 ===>(lib) (mkc_free_from_atoms A2 x2)
      # ts A1 A2 eqa
      # eqa x1 x2
      # eq <=2=> (per_ffatoms_eq lib eqa x1)}}.


(*
Set Printing Universes.
Print per_int.
Print Universes.
*)

(**

  The Base type as suggested by Howe in 1989%~\cite{Howe:1989}% is
  defined as follows: The two types have to compute to the closed
  canonical form [mkc_base] and two terms are equal in the Base type
  if they are computationally equivalent.

*)

Definition per_base {p} lib (ts : cts(p)) (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  T1 ===>(lib) mkc_base
  # T2 ===>(lib) mkc_base
  # forall t t', eq t t' <=> t ~=~(lib) t'.

(**

  The approximation type was introduced in Nuprl in 2013 in order to
  reason about computations%~\cite{Rahli+Bickford+Anand:2013}%.  It is
  a way to reason directly in the type theory about the approximation
  meta-relation introduced by Howe%~\cite{Howe:1989}% directly in the
  type theory.  It is defined as follows: The two types have to
  compute to closed canonical forms of the form [mkc_approx a b] and
  [mkc_approx c d] where [a ~<~ b] iff [c ~<~ d], and two terms are
  equal in that type if they both compute to [mkc_axiom] and [a ~<~ b]
  is true; so these types have no computational content.

  Therefore, two approximation types are equal if they are either both
  true or both false.  We need this for technical reasons: In the end,
  we want to be able to prove that [mkc_approx a a] is true in any
  context.  Because of the way the truth of the Nuprl sequents is
  formulated, this means that for any two substitutions [s1] and [s2]
  over the free variables of [a], the types [mkc_approx (s1(a))
  (s1(a))] and [mkc_approx (s2(a)) (s2(a))] have to be equal.  Because
  our context can be arbitrary, [s1] and [s2] can substitute anything
  at all for the free variables of [a].  By stipulating that any two
  true approximation types are equal allows us to prove such
  equalities.  The same is true about the computational equivalence
  type presented below.

*)

Definition per_approx {p}
           lib
           (ts : cts(p))
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {a, b, c, d : CTerm
   , T1 ===>(lib) (mkc_approx a b)
   # T2 ===>(lib) (mkc_approx c d)
   # (a ~<~(lib) b <=> c ~<~(lib) d)
   # (forall t t',
        eq t t' <=> (t ===>(lib) mkc_axiom
                       # t' ===>(lib) mkc_axiom
                       # a ~<~(lib) b)) }.

(**

  The computational equivalence type was also recently added to Nuprl,
  as a way to reason in the type theory about the computational
  equivalence meta-relation introduced by Howe%~\cite{Howe:1989}%.  It
  is defined as follows: The two types have to compute to closed
  canonical forms of the form [mkc_cequiv a b] and [mkc_cequiv c d]
  where [a ~=~ b] iff [c ~=~ d], and two terms are equal in that type
  if they both compute to [mkc_axiom] and [a ~=~ b] is true.

*)

Definition per_cequiv {p}
           lib
           (ts : cts(p))
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {a, b, c, d : CTerm
   , T1 ===>(lib) (mkc_cequiv a b)
   # T2 ===>(lib) (mkc_cequiv c d)
   # (a ~=~(lib) b <=> c ~=~(lib) d)
   # (forall t t',
        eq t t' <=> (t ===>(lib) mkc_axiom
                       # t' ===>(lib) mkc_axiom
                       # a ~=~(lib) b)) }.

(* begin hide *)

Definition per_compute {p} lib (ts : cts(p)) (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  {a, b, n, m : CTerm
   , T1 ===>(lib) (mkc_compute a b n)
   # T2 ===>(lib) (mkc_compute a b m)
   # ccequivc lib n m
   # (forall t t', eq t t'
                      <=>
                      t ===>(lib) mkc_axiom
                      # t' ===>(lib) mkc_axiom
                      # compute_1step lib a b) }.

(* end hide *)

(**

  We define the [eqorceq eq] binary relation as being either [eq] or [~=~].

 *)

Definition eqorceq {p} lib (eq : per(p)) a b : [U] := eq a b {+} a ~=~(lib) b.
Definition eqindomain {p}  (eq : per(p)) a b : [U] := 
   ((eq a a) <=> (eq b b)) #
   ((eq a a) -> (eq a b)).

(**

  The equality type allows one to express when two term are equal in a
  type directly in the type theory.  The equality type is defined as
  follows:

  - The two types have to compute to closed canonical forms of the
  form [mkc_equality a1 a2 A] and [mkc_equality b1 b2 B]

  - such [A] and [B] are equal in the candidate type system [ts] with
  equality [eqa],

  - [a1] and [b1] are either equal in [A] or computationally
  equivalent,

  - [a2] and [b2] are also either equal in [A] or computationally
  equivalent,

  - and two terms are equal in that type if they both compute to
  [mkc_axiom] and [a1] is equal to [a2] in [A] is true.

  These types have recently changed: [eqorceq eqa a1 b1] and [eqorceq
  eqa a2 b2] used to be [eqa a1 b1] and [eqa a2 b2].  Therefore an
  equality type could be well-formed only if it was true.  This issue
  is for example discussed in section 4.1.4 of Crary's
  thesis%~\cite{Crary:1998}%.  This change had several interesting
  repercussions.  For example, $\NUPRLsubtypeSYMB$, the relations
  saying that one type is a subtype of another, originally had to be a
  primitive of the system, because it could not be defined.  One could
  not, in general, prove that $\NUPRLall{x}{A}{\NUPRLmember{B}{x}}$
  was a proposition.  Now it can be defined as follows (as suggested
  by %Nogin~\cite[pp.~51]{Nogin:2002}%):
  $\NUPRLmember{\NUPRLfun{A}{B}}{\NUPRLlam{x}{x}}$, because
  $\NUPRLlam{x}{x}$ is a closed term.

  An another example, for any term $\NUPRLmember{T}{t}$, we can define
  the concept of begin greater than $T$ w.r.t.  [approx] as follows:
  $\NUPRLmember{\NUPRLbase}{u}$ is greater than $t$ if
  $\NUPRLexists{z}{\NUPRLbase}{\NUPRLand{\NUPRLequality{T}{z}{t}}{\NUPRLsqle{z}{u}}}$,
  where the $\NUPRLsqle{t_1}{t_2}$ is a type only if $t_1$ and $t_2$
  are in $\NUPRLbase$.  This definition is especially useful to reason
  about partial types by allowing us to define Crary's $\NUPRLmono$
  type%~\cite{Crary:1998}%.

 *)

Definition per_eq {p} lib (ts : cts(p)) T1 T2 (eq : per(p)) : [U] :=
  {A, B, a1, a2, b1, b2 : CTerm
   , {eqa : per
      , T1 ===>(lib) (mkc_equality a1 a2 A)
      # T2 ===>(lib) (mkc_equality b1 b2 B)
      # ts A B eqa
      # eqindomain  eqa a1 b1
      # eqindomain  eqa a2 b2
      # (forall t t',
            eq t t' <=> (t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom # eqa a1 a2)) }}.

Definition per_req_eq {o} lib (a1 a2 : @CTerm o) (eqa : per) (t t' : @CTerm o) :=
  { x1 , x2 : CTerm
  , (t ===>(lib) (mkc_refl x1))
  # (t' ===>(lib) (mkc_refl x2))
  # eqa a1 a2
  # eqa a1 x1
  # eqa a2 x2}.

Definition per_req {p} lib (ts : cts(p)) T1 T2 (eq : per(p)) : [U] :=
  {A, B, a1, a2, b1, b2 : CTerm
   , {eqa : per
   , T1 ===>(lib) (mkc_requality a1 a2 A)
   # T2 ===>(lib) (mkc_requality b1 b2 B)
   # ts A B eqa
   # eqorceq lib eqa a1 b1
   # eqorceq lib eqa a2 b2
   # eq <=2=> (per_req_eq lib a1 a2 eqa) }}.

(**

  [per_teq] is an experiment.  Can we have a type that represents
  equality between types ([tequality] defined later) as we have
  [mkc_equality] a type which allows one to reason about equalities of
  types.

 *)

Definition true_per {p} (t t' : @CTerm p) := True.

Definition per_teq {p} lib (ts : cts(p)) T1 T2 (eq : per(p)) : [U] :=
  {a1, a2, b1, b2 : CTerm
   , {eqa : per
      , T1 ===>(lib) (mkc_tequality a1 a2)
      # T2 ===>(lib) (mkc_tequality b1 b2)
      # ts a1 b1 eqa
      # ts a2 b2 eqa
      # ts a1 a2 eqa
      # eq <=2=> true_per}}.

(**

  We now define the concept of a type family.  This is going to be
  useful for defining several types such as dependent functions and
  products (called dependents products and sums in Coq).  In that
  definition [C] is a type constructor.  It takes a closed terms which
  is the domain of the type, a variable [v], and a term that does not
  have any free variable except [v], i.e., it is a type family
  constructor.  The equality [eqa] is the equality of the domain and
  [eqb] is the equality of the co-domain.

 *)

Notation "per-fam ( eqa )" :=
  (forall a a' (p : eqa a a'), per) (at level 0).

Definition type_family {p} lib TyCon (ts : cts(p)) (T1 T2 : @CTerm p) eqa eqb : [U]:=
  {A, A' : CTerm , {v, v' : NVar , {B : CVTerm [v] , {B' : CVTerm [v'] ,
     T1 ===>(lib) (TyCon A v B)
     # T2 ===>(lib) (TyCon A' v' B')
     # ts A A' eqa
     # (forall a a', forall e : eqa a a',
          ts (B[[v\\a]]) (B'[[v'\\a']]) (eqb a a' e))}}}}.

(**

  Intersection types were introduced in Nuprl by Kopylov in
  2004%~\cite{Kopylov:2004}%.  An intersection type is a type family.
  Two terms [t] and [t'] are equal in an intersection type of the form
  $\NUPRLisect{x}{A}{\NUPRLsuba{B}{z}{x}}$ if for any two elements [a]
  and [a'] equal in $A$, [t] and [t'] are equal in
  $\NUPRLsuba{B}{z}{a}$.

 *)

Definition per_isect {p}
           lib
           (ts : cts(p))
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family lib mkc_isect ts T1 T2 eqa eqb
      # (forall t t',
           eq t t'
              <=>
              (forall a a', forall e : eqa a a', eqb a a' e t t')) }}.

(**

  Dependent intersection types were invented by Kopylov in
  2003%~\cite{Kopylov:2003,Kopylov:2004}%, and were used among other
  things to define records, structures, and signatures.  A dependent
  intersection type is a type family.  Two terms [t] and [t'] are
  equal in a dependent intersection type of the form
  $\NUPRLdisect{x}{A}{\NUPRLsuba{B}{z}{x}}$ if [t] and [t'] are equal
  in $A$ and also in $\NUPRLsuba{B}{z}{t}$.

 *)

Definition per_disect {p}
           lib
           (ts : cts(p))
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family lib mkc_disect ts T1 T2 eqa eqb
      # (forall t t', eq t t' <=> {e : eqa t t' , eqb t t' e t t'}) }}.

(**

  Function types are also type families.  Two terms [t] and [t'] are
  equal in a function type of the form
  $\NUPRLfunction{x}{A}{\NUPRLsuba{B}{z}{x}}$ if for all [a] and [a']
  equal in $A$, [(mkc_apply t a)] and [(mkc_apply t' a')] are equal in
  $\NUPRLsuba{B}{z}{a}$.  Therefore, members of function types do not
  have to be lambda terms.  For example, function types that have an
  empty domain are all inhabited by diverging terms.

 *)

Definition per_func {p} lib (ts : cts(p)) T1 T2 (eq : per(p)) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family lib mkc_function ts T1 T2 eqa eqb
      # (forall t t',
           eq t t'
           <=>
           (forall a a' (e : eqa a a'),
              (eqb a a' e) (mkc_apply t a) (mkc_apply t' a')))}}.

(**

  We call products the types of pairs.  The product type is defined as
  follows:

 *)

Definition per_product_eq {p}
           lib
           (eqa : per(p))
           (eqb : per-fam(eqa))
           t t' : [U] :=
  {a, a', b, b' : CTerm
   , {e : eqa a a'
      , t ===>(lib) (mkc_pair a b)
      # t' ===>(lib) (mkc_pair a' b')
      # eqa a a'
      # eqb a a' e b b'}}.

Definition per_product {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family lib mkc_product ts T1 T2 eqa eqb
      # eq <=2=> (per_product_eq lib eqa eqb)}}.


(** Union type *)

Inductive per_tunion_eq {p}
          (eqa : per(p))
          (eqb : per-fam(eqa))
          (t1 t2 : @CTerm p) : [U] :=
| tunion_eq_cl :
    forall t,
      per_tunion_eq eqa eqb t1 t
      -> per_tunion_eq eqa eqb t t2
      -> per_tunion_eq eqa eqb t1 t2
| tunion_eq_eq :
    forall a1 a2 (e : eqa a1 a2),
      eqb a1 a2 e t1 t2
      -> per_tunion_eq eqa eqb t1 t2.

Definition per_tunion {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family lib mkc_tunion ts T1 T2 eqa eqb
      # eq <=2=> (per_tunion_eq eqa eqb)}}.


(**

  Equal members of [mk_texc N E] are exceptions such that the names
  are equal in [N] and the "values" are equal in [E].  Exception types
  are defined as follows:

 *)

Definition per_texc_eq {p} lib (eqn eqe : per(p)) t t' : [U] :=
  {n1, n2, e1, e2 : CTerm
   , t ===e>(lib,n1) e1
   # t' ===e>(lib,n2) e2
   # eqn n1 n2
   # eqe e1 e2 }.

Definition per_texc {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {eqn, eqe : per
   , {N1, N2, E1, E2 : CTerm
      , T1 ===>(lib) (mkc_texc N1 E1)
      # T2 ===>(lib) (mkc_texc N2 E2)
      # ts N1 N2 eqn
      # ts E1 E2 eqe
      # eq <=2=> (per_texc_eq lib eqn eqe)}}.

(* See [with_exc] to add exceptions to types in terms_union. *)

(**

  We will often want to talk about named exceptions, i.e.,

 *)


(**

  Disjoint unions are defined as follows:

 *)

Definition per_union_eq_L {p} lib (eq : per(p)) t t' : [U] :=
  {x, y : CTerm
   , t ===>(lib) (mkc_inl x)
     # t' ===>(lib) (mkc_inl y)
     # eq x y}.

Definition per_union_eq_R {p} lib (eq : per(p)) t t' : [U] :=
  {x, y : CTerm
   , t ===>(lib) (mkc_inr x)
     # t' ===>(lib) (mkc_inr y)
     # eq x y}.

Definition per_union_eq {p} lib (eqa eqb : per) (t t' : @CTerm p) : [U] :=
  per_union_eq_L lib eqa t t' {+} per_union_eq_R lib eqb t t'.

Definition per_union {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {eqa, eqb : per
   , {A1, A2, B1, B2 : CTerm
      , T1 ===>(lib) (mkc_union A1 B1)
      # T2 ===>(lib) (mkc_union A2 B2)
      # ts A1 A2 eqa
      # ts B1 B2 eqb
      # eq <=2=> (per_union_eq lib eqa eqb)}}.


(* extensional union type *)

Definition per_or {p} (eq1 eq2 : per) : per :=
  fun t1 t2 : @CTerm p => eq1 t1 t2 {+} eq2 t1 t2.

Notation "eq1 +2+ eq2" := (per_or eq1 eq2) (at level 0).

Definition per_eunion {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {eqa1, eqa2, eqb1, eqb2 : per
   , {A1, A2, B1, B2 : CTerm
   , T1 ===>(lib) (mkc_eunion A1 B1)
   # T2 ===>(lib) (mkc_eunion A2 B2)
   # ((eqa1 +2+ eqb1) <=2=> (eqa2 +2+ eqb2))
   # ts A1 A1 eqa1
   # ts A2 A2 eqa2
   # ts B1 B1 eqb1
   # ts B2 B2 eqb2
   # eq <=2=> (per_union_eq lib eqa1 eqb1)}}.

(* begin hide *)

Definition per_union2_eq_L {o} lib (ts : cts(o)) T1 T2 t t' : [U] :=
  {x, y : CTerm
   , {eq : per(o)
   , ts T1 T2 eq
   # t ===>(lib) (mkc_inl x)
   # t' ===>(lib) (mkc_inl y)
   # eq x y}}.

Definition per_union2_eq_R {o} lib (ts : cts(o)) T1 T2 t t' : [U] :=
  {x, y : CTerm
   , {eq : per(o)
   , ts T1 T2 eq
   # t ===>(lib) (mkc_inr x)
   # t' ===>(lib) (mkc_inr y)
   # eq x y}}.

Definition per_union2_eq {p} lib (ts : cts(p)) A1 A2 B1 B2 t1 t2 :=
  per_union2_eq_L lib ts A1 A2 t1 t2 {+} per_union2_eq_R lib ts B1 B2 t1 t2.

Definition per_union2 {o}
           lib
           (ts : cts)
           (T1 T2 : @CTerm o)
           (eq : per(o)) : [U] :=
   {eqa : per(o)
   , {A1, A2, B1, B2 : CTerm
   , T1 ===>(lib) (mkc_union2 A1 B1)
   # T2 ===>(lib) (mkc_union2 A2 B2)
   # eq <=2=> (per_union2_eq lib ts A1 A2 B1 B2)
  }}.

(* end hide *)

(**

  Image types were introduced by Kopylov and Nogin in
  2006%~\cite{Nogin+Kopylov:2006}%.  It turns out that refinement and
  union types can be defined using image types.  An image is defined
  by a type [A] and a function [f] with [A] as its domain, and
  contains any term computationally equivalent to [mkc_apply f a] for
  some [a] in [A].  Its equality is defined as the smallest partial
  equivalence relation such that [f a] and [f b] are equals in
  [mkc_image A f] whenever [a] anb [b] are equal in [A] that respects
  the computational equivalence relation.

 *)

(*
Definition per_image_eq1 (eqa : per(p)) (f t1 t2 : @CTerm p) : [U] :=
  {a1, a2 : CTerm
   , eqa a1 a2
   # t1 ~=~ (mkc_apply f a1)
   # t2 ~=~ (mkc_apply f a2)}.
*)

Inductive per_image_eq {p} lib (eqa : per(p)) (f t1 t2 : @CTerm p) : [U] :=
| image_eq_cl :
    forall t,
      per_image_eq lib eqa f t1 t
      -> per_image_eq lib eqa f t t2
      -> per_image_eq lib eqa f t1 t2
| image_eq_eq :
    forall a1 a2,
      eqa a1 a2
      -> t1 ~=~(lib) (mkc_apply f a1)
      -> t2 ~=~(lib) (mkc_apply f a2)
      -> per_image_eq lib eqa f t1 t2.

Definition per_image {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {eqa : per
   , {A1, A2, f1, f2 : CTerm
      , T1 ===>(lib) (mkc_image A1 f1)
      # T2 ===>(lib) (mkc_image A2 f2)
      # ts A1 A2 eqa
      # f1 ~=~(lib) f2
      # eq <=2=> (per_image_eq lib eqa f1)}}.


(**

   We introduce the concept of an extensional type family.  The
   difference with a type family is that domains do not have to be
   equal anymore.  Two families [C A v B] and [C A' v' B'] are equal
   if forall [a] in [A] there exists an [a'] in [A'] such that [substc
   a v B] and [substc a' v' B'] are equal, and vice-versa.  This is
   useful to define intersection types that are slightly more
   extensional than the ones defined above.  Extensional intersection
   types can be used, for example, to define computational equivalence
   types from approximation types.

 *)

Notation "per-efam ( eqa , eqa' )" :=
  (forall a a' (e : eqa a a) (e' : eqa' a' a'), per) (at level 0).

Definition eisect_eq {p} (eqa eqa' : per(p)) (eqb : per-efam(eqa,eqa')) : per(p) :=
  fun t t' =>
    forall a a' (e : eqa a a) (e' : eqa' a' a'),
      eqb a a' e e' t t'.

(* begin hide *)

Definition etype_family1 {p}
           lib
           (C   : CTerm -> forall (v : NVar), CVTerm [v] -> CTerm)
           (ts  : cts)
           (T1 T2 : @CTerm p)
           (eqa eqa' : per(p))
           (eqb : per-efam(eqa,eqa')) : [U] :=
  {A, A' : CTerm
   , {v, v' : NVar
   , {B : CVTerm [v]
   , {B' : CVTerm [v']
      , T1 ===>(lib) (C A v B)
      # T2 ===>(lib) (C A' v' B')
      # ts A A eqa
      # ts A' A' eqa'
      # (forall a (e : eqa a a),
           {a' : CTerm , {e' : eqa' a' a'
            , ts (substc a v B) (substc a' v' B') (eqb a a' e e')}})
      # (forall a' (e' : eqa' a' a'),
           {a : CTerm , {e : eqa a a
            , ts (substc a v B) (substc a' v' B') (eqb a a' e e')}}) }}}}.

Definition per_eisect1 {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {eqa, eqa' : per , {eqb : per-efam(eqa,eqa')
      , etype_family1 lib mkc_eisect ts T1 T2 eqa eqa' eqb
      # eq <=2=> (eisect_eq eqa eqa' eqb) }}.

(*
Definition mk_eqb
             (ts )
             (eqa eqa' : per(p))
             (eqb : forall a a', eqa a a -> eqa' a' a' -> per)
             (f : forall a (e : eqa a a), {a' : CTerm , eqa' a' a'})
             (a : @CTerm p)
             (e : eqa a a) : per :=
  match f a e with
      | ex_intro a' e' =>
          eqb a a' e e'
  end.
*)

(* end hide *)

(** term selector *)
Notation "t-sel ( eqa )" :=
  (forall a (e : eqa a a), CTerm) (at level 0).

(** equality selector *)
Notation "e-sel ( eqa , eqa' , f )" :=
  (forall a (e : eqa a a), eqa' (f a e) (f a e)) (at level 0).

Definition etype_family {p}
           lib
           (C   : CTerm -> forall (v : NVar), CVTerm [v] -> CTerm)
           (ts  : cts)
           (T1 T2 : @CTerm p)
           (eqa eqa' : per(p))
           (eqb : per-efam(eqa,eqa')) : [U] :=
  {A, A' : CTerm
   , {v, v' : NVar
   , {B  : CVTerm [v]
   , {B' : CVTerm [v']
   , {f  : t-sel(eqa)
   , {g  : e-sel(eqa,eqa',f)
   , {f' : t-sel(eqa')
   , {g' : e-sel(eqa',eqa,f')
      , T1 ===>(lib) (C A v B)
      # T2 ===>(lib) (C A' v' B')
      # ts A A eqa
      # ts A' A' eqa'
      # (forall a (e : eqa a a),
           ts (substc a v B)
              (substc (f a e) v' B')
              (eqb a (f a e) e (g a e)))
      # (forall a' (e' : eqa' a' a'),
           ts (substc (f' a' e') v B)
              (substc a' v' B')
              (eqb (f' a' e') a' (g' a' e') e')) }}}}}}}}.

(**

  Extensional intersection types are similar to intersection types but
  they use the concept of extensional type families instead of type
  families.

  An intuitive way of defining computational equivalence types from
  approximation types would be to define them using intersection types
  as follows:
  $\NUPRLsqequalty{a}{b}=\NUPRLbisect{\NUPRLsqlety{a}{b}}{\NUPRLsqlety{b}{a}}$.
  We need the equality between computational equivalence types to be
  extensional, i.e., $\NUPRLsqequalty{a}{b}$ is
  equal to $\NUPRLsqequalty{c}{d}$ iff
  $\NUPRLmetaiff{\NUPRLsqequal{a}{b}}{\NUPRLsqequal{c}{d}}$, i.e.,
  $\NUPRLmetaiff
  {(\NUPRLmetaand
    {\NUPRLsqle{a}{b}}
    {\NUPRLsqle{b}{a}})
  }
  {(\NUPRLmetaand
    {\NUPRLsqle{c}{d}}
    {\NUPRLsqle{d}{c}})
  }$.
  This comes from the fact that we wish to have a rule that says that
  $\NUPRLsqequalty{a}{a}$ is provable in any context and from the
  semantics of Nuprl's sequents as discussed above.
  Now, if we were to define $\NUPRLsqequalty{a}{b}$ as
  $\NUPRLbisect{\NUPRLsqlety{a}{b}}{\NUPRLsqlety{b}{a}}$ then we would
  obtain that $\NUPRLsqequalty{a}{b}$ is equal to
  $\NUPRLsqequalty{c}{d}$ iff
  $\NUPRLbisect{\NUPRLsqlety{a}{b}}{\NUPRLsqlety{b}{a}}$ is equal to
  $\NUPRLbisect{\NUPRLsqlety{c}{d}}{\NUPRLsqlety{d}{c}}$.
  By definition of the intersection types, we would obtain that
  $\NUPRLsqequalty{a}{b}$ is equal to $\NUPRLsqequalty{c}{d}$ iff
  $\NUPRLsqlety{a}{b}$ is equal to $\NUPRLsqlety{c}{d}$ and
  $\NUPRLsqlety{b}{a}$ is equal to $\NUPRLsqlety{d}{c}$.
  For example, we want to have $\NUPRLsqequalty{a}{b}$ and
  $\NUPRLsqequalty{b}{a}$ be equal types.
  With our definition using intersection types, we would have to prove
  that $\NUPRLsqlety{a}{b}$ is equal to $\NUPRLsqlety{b}{a}$ and
  $\NUPRLsqlety{c}{d}$ is equal to $\NUPRLsqlety{d}{c}$ which are not
  provable in general.  Therefore, we cannot define computation
  equivalence types using intersection types.

  However, if we were to define computational equivalence types using
  our new extensional intersection types, we would have that
  $\NUPRLsqequalty{a}{b}$ is equal to $\NUPRLsqequalty{c}{d}$ iff
  $\NUPRLbeisect{\NUPRLsqlety{a}{b}}{\NUPRLsqlety{b}{a}}$ is equal to
  $\NUPRLbeisect{\NUPRLsqlety{c}{d}}{\NUPRLsqlety{d}{c}}$ (where
  $\NUPRLeisectSYMB$ is the symbol we use for extensional intersection
  types, as opposed to $\NUPRLisectSYMB$ which we use for
  ``intensional intersection types'').  By definition of the
  extensional intersection types, we would obtain that
  $\NUPRLsqequalty{a}{b}$ is equal to $\NUPRLsqequalty{c}{d}$ iff
  $\NUPRLsqlety{a}{b}$ is equal to $\NUPRLsqlety{c}{d}$ or
  $\NUPRLsqlety{d}{c}$ and $\NUPRLsqlety{b}{a}$ is equal to
  $\NUPRLsqlety{c}{d}$ or $\NUPRLsqlety{d}{c}$.  With that definition,
  we can now easily prove, e.g., that $\NUPRLsqlety{a}{b}$ is equal to
  $\NUPRLsqlety{b}{a}$.

 *)

Definition per_eisect {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {eqa, eqa' : per , {eqb : per-efam(eqa,eqa')
      , etype_family lib mkc_eisect ts T1 T2 eqa eqa' eqb
      # eq <=2=> (eisect_eq eqa eqa' eqb) }}.

(**

  We now define the PER type constructor.  PER types have been added
  to Nuprl in 2013 as a way to minimize the number of primitive type
  constructors needed to express the Nuprl type theory by directly
  defining new types as partial equivalence relations in the type
  theory (and not the meta-theory).  Because the Nuprl types are
  partial equivalence relations on closed terms, the idea is that most
  of Nuprl's types can be defined as partial equivalence relations on
  Base using the PER type constructor.

  The idea of introducing such a PER type constructor in the theory is
  not new.  Stuart Allen mentions in his
  thesis%~\cite[page~15]{Allen:1987b}% that ``The set type and
  quotient type constructors could have been unified in a single
  constructor $x,y\in{A}/E_{x,y}$ which is like quotient except that,
  rather than requiring (the inhabitation of) $E_{x,y}$ to be an
  equivalence relation, we require only that it be transitive and
  symmetric over $A$, i.e., its restriction to $A$ should be a partial
  equivalence relation.  The equal members are the members of $A$ that
  make $E_{x,y}$ inhabited.''

  We say that a term equality [R] is [inhabited] if there is at least
  one term [t] such that [R t t].  If a type [T] has equality [R] and
  [R] is inhabited, this means that [T] is not empty.

  As specified by [is_per], in the type system, a relation on terms is
  a partial equivalence relation if it is symmetric and transitive.

 *)

Definition inhabited {p} (R : per(p)) := { t : CTerm , R t t }.

Definition is_per {p} (R : @CTerm p -> @CTerm p -> per(p)) :=
  (forall x y, inhabited (R x y) -> inhabited (R y x))
    # (forall x y z, inhabited (R x y)
                      -> inhabited (R y z)
                      -> inhabited (R x z)).


(**

  A PER type is defined by a binary relation (i.e., a function from
  terms to terms to types) on terms.  Two PER types are equal if the
  two corresponding relations are equivalent partial equivalence
  relations.  Two terms [t] and [t'] are equal in a PER type if they
  are in the corresponding relation.

 *)

Definition per_pertype {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {R1, R2 : CTerm
   , {eq1, eq2 : CTerm -> CTerm -> per
      , T1 ===>(lib) (mkc_pertype R1)
      # T2 ===>(lib) (mkc_pertype R2)
      # (forall x y, ts (mkc_apply2 R1 x y)
                        (mkc_apply2 R1 x y)
                        (eq1 x y))
      # (forall x y, ts (mkc_apply2 R2 x y)
                        (mkc_apply2 R2 x y)
                        (eq2 x y))
      # (forall x y, inhabited (eq1 x y) <=> inhabited (eq2 x y))
      # is_per eq1
      # forall t t', eq t t' <=> inhabited (eq1 t t') }}.

(**

 An intensional version of [per_pertype]:

 *)

Definition pertype_eq {p} (eq : @CTerm p -> @CTerm p -> per(p)) t t' :=
  inhabited (eq t t').

Definition per_ipertype {p} lib (ts : cts) (T1 T2 : @CTerm p) (eq : per) :=
  {R1, R2 : CTerm
   , {eq1 : CTerm -> CTerm -> per
      , T1 ===>(lib) (mkc_ipertype R1)
      # T2 ===>(lib) (mkc_ipertype R2)
      # (forall x y, ts (mkc_apply2 R1 x y)
                        (mkc_apply2 R2 x y)
                        (eq1 x y))
      # is_per eq1
      # eq <=2=> (pertype_eq eq1) }}.

(**

 Yet another intensional version of [per_pertype]:

 *)

Definition per_spertype {p} lib (ts : cts) (T1 T2 : @CTerm p) (eq : per) :=
  {R1, R2 : CTerm
   , {eq1 : CTerm -> CTerm -> per
      , T1 ===>(lib) (mkc_spertype R1)
      # T2 ===>(lib) (mkc_spertype R2)
      # (forall x y,
           ts (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (eq1 x y))
      # (forall x y z,
           inhabited (eq1 x z)
           -> ts (mkc_apply2 R1 x y) (mkc_apply2 R1 z y) (eq1 x y))
      # (forall x y z,
           inhabited (eq1 y z)
           -> ts (mkc_apply2 R1 x y) (mkc_apply2 R1 x z) (eq1 x y))
      # is_per eq1
      # eq <=2=> (pertype_eq eq1) }}.

(**

  We define quotient types as follows:

 *)

Definition quot_rel_eq {p} (eqa : per) :=
  forall (a1 a2 : @CTerm p)
         (ea : eqa a1 a2)
         (b1 b2 : @CTerm p)
         (eb : eqa b1 b2),
    per(p).

Definition per_quotient_eq {p}
           (eqa : per)
           (eqe : quot_rel_eq eqa)
           (t t' : @CTerm p) :=
  {e : eqa t t , {e' : eqa t' t' , inhabited (eqe t t e t' t' e')}}.

Definition per_quotient {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {A1, A2 : CTerm
   , {x1, x2, y1, y2 : NVar
   , {E1 : CVTerm [x1,y1]
   , {E2 : CVTerm [x2,y2]
   , {eqa : per
   , {eqe1, eqe2 : quot_rel_eq eqa
      , T1 ===>(lib) (mkc_quotient A1 x1 y1 E1)
      # T2 ===>(lib) (mkc_quotient A2 x2 y2 E2)
      # ts A1 A2 eqa
      # (forall a1 a2 b1 b2 (ea : eqa a1 a2) (eb : eqa b1 b2),
           ts (lsubstc2 x1 a1 y1 b1 E1)
              (lsubstc2 x1 a2 y1 b2 E1)
              (eqe1 a1 a2 ea b1 b2 eb))
      # (forall a1 a2 b1 b2 (ea : eqa a1 a2) (eb : eqa b1 b2),
           ts (lsubstc2 x2 a1 y2 b1 E2)
              (lsubstc2 x2 a2 y2 b2 E2)
              (eqe2 a1 a2 ea b1 b2 eb))
      # (forall a1 a2 b1 b2 (ea : eqa a1 a2) (eb : eqa b1 b2),
           inhabited (eqe1 a1 a2 ea b1 b2 eb)
           <=> inhabited (eqe2 a1 a2 ea b1 b2 eb))
      # (forall a1 a2 (ea : eqa a1 a2) (ea1 : eqa a1 a1) (ea2 : eqa a2 a2),
           inhabited (eqe1 a1 a1 ea1 a2 a2 ea2))
      # (forall a1 a2 (ea1 : eqa a1 a1) (ea2 : eqa a2 a2),
           inhabited (eqe1 a1 a1 ea1 a2 a2 ea2)
           -> inhabited (eqe1 a2 a2 ea2 a1 a1 ea1))
      # (forall a1 a2 a3 (ea1 : eqa a1 a1) (ea2 : eqa a2 a2) (ea3 : eqa a3 a3),
           inhabited (eqe1 a1 a1 ea1 a2 a2 ea2)
           -> inhabited (eqe1 a2 a2 ea2 a3 a3 ea3)
           -> inhabited (eqe1 a1 a1 ea1 a3 a3 ea3))
      # eq <=2=> (per_quotient_eq eqa eqe1) }}}}}}.

(**

  Refinement types (also called set or subset types) are defined as
  follows (note that Crary%~\cite{Crary:1998}% as a slightly more
  extensional definition, but here we chose to define refinment types
  as they are currently implemented in Nuprl):

 *)

Definition per_set {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family lib mkc_set ts T1 T2 eqa eqb
      # (forall t t', eq t t' <=> {e : eqa t t' , inhabited (eqb t t' e)})}}.

(**

  We define partial types as they are introduced in Crary's
  thesis%~\cite{Crary:1998}%.  Partial types were invented to provide
  meaning to partial functions.  Intuitively, if [eqa] is the equality
  of the type [A] [per_partial_eq eqa] gives the equality of the
  partial type [mk_partial T]

 *)

Definition per_partial_eq {p} lib (eqa : per) (t t' : @CTerm p) : [U] :=
  (chaltsc lib t <=> chaltsc lib t')
  # (chaltsc lib t -> eqa t t').

Definition per_partial {p} lib (ts : cts) T1 T2 (eq : per(p)) : [U] :=
  {A1, A2 : @CTerm p , {eqa : per
      , T1 ===>(lib) (mkc_partial A1)
      # T2 ===>(lib) (mkc_partial A2)
      # ts A1 A2 eqa
      # (forall a, eqa a a -> chaltsc lib a)
      # eq <=2=> (per_partial_eq lib eqa) }}.

(** %\noindent% One of the main ways to prove membership
    in a partial type is the fixpoint induction rule.
    Intuitively, it says that [mk_fix f] is is a member
    of [mk_partial T] whenever
    [f] is in [mk_partial T -> mk_partial T ].
    This rules only does not hold for all types.
    Crary introduced 2 sufficient conditions to characterize
    the types for which this property holds.
    He reflects these conditions to the type theory
    by defining two types [mk_mono T]
    and [mk_admiss T] which assert
    that the type [T] has the above mentioned property.
    [mk_mono T] is more intuitive, but weaker.
    We will prove that [mk_mono T] implies [mk_admiss T].
    We will first define the closed version of
    finite approximations of [mkc_fix f].
    [fix_approxc] is similar to [fix_approx] that we
    defined in %\ref{sec:comp:domain}%

*)

Fixpoint fix_approxc {p} (n : nat) (f : @CTerm p) : CTerm :=
  match n with
    | 0 => mkc_bot
    | S n => mkc_apply f (fix_approxc n f)
  end.

Definition subst_fapproxc {p} {v:NVar}
           (e : CVTerm [v]) (f : @CTerm p) (n : nat) : CTerm :=
  substc (fix_approxc n f) v e.

Definition subst_fixc {p} {v:NVar}
           (e : CVTerm [v]) (f : @CTerm p) : CTerm :=
  substc (mkc_fix f) v e.

(** %\noindent%
  First, we define the Crary's more inuitive Mono-hood property. Intuitively,
  a type [T] is a Mono type if its equality satisfies the following
  condition.
  The following predicate charecterizes the PERs of types
  that are Mono *)

Definition mono_equality {p} lib (eq : per) :=
  forall (t t' : @CTerm p),
    eq t t
    -> approxc lib t t'
    -> eq t t'.

(** %\noindent% Crary the defined a stronger condition called
    admissibility. It is defined below *)

Definition per_mono_eq {p} lib (eqa : per(p)) (t t' : @CTerm p) : [U] :=
  t ===>(lib) mkc_axiom
  # t' ===>(lib) mkc_axiom
  # mono_equality lib eqa.

Definition per_mono {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {A1, A2 : CTerm ,
    {eqa : per ,
        T1 ===>(lib) (mkc_mono A1)
        # T2 ===>(lib) (mkc_mono A2)
        # ts A1 A2 eqa
        # eq <=2=> (per_mono_eq lib eqa)}}.

Definition cofinite_subst_fapprox_eqc {p}
           (eq : per)
           {v: NVar}
           (e e' : CVTerm [v])
           (f : @CTerm p) :=
    {j : nat
     , forall (k :nat),
         k>j -> eq (subst_fapproxc e f k) (subst_fapproxc e' f k)}.

Definition subst_fix_eqc {p}
           (eq : per)
           {v: NVar}
           (e e' : CVTerm [v])
           (f : @CTerm p) :=
  eq (subst_fixc e f)  (subst_fixc e' f).

Definition admissible_equality {p} (eq : per) :=
  forall v (e e' : CVTerm [v]) (f : @CTerm p),
    cofinite_subst_fapprox_eqc eq e e' f
    -> subst_fix_eqc eq e e' f.

Definition per_admiss_eq {p} lib (eqa : per(p)) (t t' : @CTerm p) : [U] :=
  t ===>(lib) mkc_axiom
  # t' ===>(lib) mkc_axiom
  # admissible_equality eqa.

Definition per_admiss {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {A1, A2 : CTerm ,
    {eqa : per ,
        T1 ===>(lib) (mkc_admiss A1)
      # T2 ===>(lib) (mkc_admiss A2)
      # ts A1 A2 eqa
      # eq <=2=> (per_admiss_eq lib eqa)}}.

(*
Definition per_esquash (ts : cts) (T1 T2 : @CTerm p) (eq : per(p)) :=
  {A1, A2 : CTerm
   $ {eq1, eq2 : per
      $ ccomputes_to_valc T1 (mkc_esquash A1)
      # ccomputes_to_valc T2 (mkc_esquash A2)
      # ts A1 A1 eq1
      # ts A2 A2 eq2
      # (inhabited eq1 <=> inhabited eq2)
      # forall t t', eq t t'
                        <=>
                        ccomputes_to_valc t mkc_axiom
                        # ccomputes_to_valc t' mkc_axiom
                        # inhabited eq1 }}.
*)


(**

  W types are defined using the [Inductive] feature of Coq.

 *)

Inductive weq {p}
          lib
          (eqa : per)
          (eqb : per-fam(eqa))
          (t t' : @CTerm p) : [U] :=
| weq_cons :
    forall a f a' f' : CTerm,
    forall e : eqa a a',
      t ===>(lib) (mkc_sup a f)
      -> t' ===>(lib) (mkc_sup a' f')
      -> (forall b b',
            eqb a a' e b b'
            -> weq lib eqa eqb (mkc_apply f b) (mkc_apply f' b'))
      -> weq lib eqa eqb t t'.

Definition per_w {p} lib (ts : cts) T1 T2 (eq : per(p)) : [U] :=
  {eqa : per , {eqb : per-fam(eqa) ,
   type_family lib mkc_w ts T1 T2 eqa eqb
   # eq <=2=> (weq lib eqa eqb)}}.

(**

  M types%~\cite{Berg+Marchi:2007,Abbott+Altenkirch+Ghani:2005}% are
  defined using the [CoInductive] feature of Coq.

 *)

CoInductive meq {p}
            lib
            (eqa : per)
            (eqb : per-fam(eqa))
            (t t' : @CTerm p) : [U] :=
| meq_cons :
    forall a f a' f' : CTerm,
    forall e : eqa a a',
      t ===>(lib) (mkc_sup a f)
      -> t' ===>(lib) (mkc_sup a' f')
      -> (forall b b',
            eqb a a' e b b'
            -> meq lib eqa eqb (mkc_apply f b) (mkc_apply f' b'))
      -> meq lib eqa eqb t t'.

Definition per_m {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family lib mkc_m ts T1 T2 eqa eqb
      # eq <=2=> (meq lib eqa eqb)}}.

(**

  We now define the concept of parameterized type families, which we
  use to define parameterized W and M types.  In a parameterized W
  type of the form [mkc_pw P ap A bp ba B cp ca cb B p]: [P] is the
  parameter type; [p] is the initial parameter; the [A] describes the
  non inductive parts of the constructors of the corresponding
  inductive type, and might depend on the parameter ([ap]); the [B]
  part describes the inductive parts of the constructors of the
  corresponding inductive type, and might depend on the parameter
  ([bp]) and a [A] ([ba]); finally, [C] describes how to build the
  parameters for each of the inductive calls, and might depend on a
  [P], an [A], and a [B].

 *)

Definition pfam_type {pp} :=
  forall P : @CTerm pp,
  forall ap : NVar,
  forall A : @CVTerm pp [ap],
  forall bp ba : NVar,
  forall B : @CVTerm pp [bp,ba],
  forall cp ca cb : NVar,
  forall C : @CVTerm pp [cp,ca,cb],
  forall p : @CTerm pp,
    @CTerm pp.

Notation "per-fam-fam ( eqp , eqa )" :=
  (forall p p' : CTerm,
   forall ep : eqp p p',
   forall a a' : CTerm,
   forall ea : eqa p p' ep a a',
     per)
    (at level 0).

Definition type_pfamily {p}
           lib
           (Cons : pfam_type)
           (ts  : cts)
           (T1 T2 : @CTerm p)
           (eqp : per(p))
           (eqa : per-fam(eqp))
           (eqb : per-fam-fam(eqp,eqa))
           (cp1 ca1 cb1 : NVar)
           (C1 : CVTerm [cp1;ca1;cb1])
           (cp2 ca2 cb2 : NVar)
           (C2 : CVTerm [cp2;ca2;cb2])
           (p1 p2 : @CTerm p): [U] :=
  {P1, P2 : CTerm
   , {ap1, ap2 : NVar
   , {A1 : CVTerm [ap1]
   , {A2 : CVTerm [ap2]
   , {bp1, bp2 : NVar
   , {ba1, ba2 : NVar
   , {B1 : CVTerm [bp1, ba1]
   , {B2 : CVTerm [bp2, ba2]
      , T1 ===>(lib) (Cons P1 ap1 A1 bp1 ba1 B1 cp1 ca1 cb1 C1 p1)
      # T2 ===>(lib) (Cons P2 ap2 A2 bp2 ba2 B2 cp2 ca2 cb2 C2 p2)
      # ts P1 P2 eqp
      # (forall p1 p2,
         forall ep : eqp p1 p2,
           ts (substc p1 ap1 A1) (substc p2 ap2 A2) (eqa p1 p2 ep))
      # (forall p1 p2,
         forall ep : eqp p1 p2,
         forall a1 a2,
         forall ea : eqa p1 p2 ep a1 a2,
           ts (lsubstc2 bp1 p1 ba1 a1 B1)
              (lsubstc2 bp2 p2 ba2 a2 B2)
              (eqb p1 p2 ep a1 a2 ea))
      # (forall p1 p2,
         forall ep : eqp p1 p2,
         forall a1 a2,
         forall ea : eqa p1 p2 ep a1 a2,
         forall b1 b2,
         forall eb : eqb p1 p2 ep a1 a2 ea b1 b2,
           eqp (lsubstc3 cp1 p1 ca1 a1 cb1 b1 C1)
               (lsubstc3 cp2 p2 ca2 a2 cb2 b2 C2))
      # eqp p1 p2
       }}}}}}}}.

(**

  Using the concept of parameterized type families, we define
  parameterized W types as follows:

 *)

Inductive pweq {pp}
          lib
          (eqp : per)
          (eqa : per-fam(eqp))
          (eqb : per-fam-fam(eqp,eqa))
          (cp ca cb : NVar)
          (C : CVTerm [cp;ca;cb])
          (p : CTerm)
          (t1 t2 : @CTerm pp) : [U] :=
| pweq_cons :
    forall ep : eqp p p,
    forall a1 f1 a2 f2 : CTerm,
    forall ea : eqa p p ep a1 a2,
      t1 ===>(lib) (mkc_sup a1 f1)
      -> t2 ===>(lib) (mkc_sup a2 f2)
      -> (forall b1 b2,
            eqb p p ep a1 a2 ea b1 b2
            -> pweq lib eqp eqa eqb
                    cp ca cb C
                    (lsubstc3 cp p ca a1 cb b1 C)
                    (mkc_apply f1 b1)
                    (mkc_apply f2 b2))
      -> pweq lib eqp eqa eqb cp ca cb C p t1 t2.

Definition per_pw {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {eqp : per
   , {eqa : per-fam(eqp)
   , {eqb : per-fam-fam(eqp,eqa)
   , {p1, p2 : CTerm
   , {cp1, cp2, ca1, ca2, cb1, cb2 : NVar
   , {C1 : CVTerm [cp1, ca1, cb1]
   , {C2 : CVTerm [cp2, ca2, cb2]
      , type_pfamily lib mkc_pw ts T1 T2 eqp eqa eqb
                     cp1 ca1 cb1
                     C1
                     cp2 ca2 cb2
                     C2
                     p1 p2
      # eq <=2=> (pweq lib eqp eqa eqb cp1 ca1 cb1 C1 p1)
       }}}}}}}.

(**

  Let us now illustrate how one can use parametrized W types to define
  parametrized inductive types such as the following vector type:

*)

Inductive vec (T : Type) (n : nat) :=
| vnil : n = 0 -> vec T n
| vcons : 0 < n -> T -> vec T (n - 1) -> vec T n.

(**

  The P part is the type of parameters.  For our [vec] example, it is
  the product of a type and a nat.

 *)

Definition pw_vec_P {p} i := @mk_prod p (mk_uni i) mk_tnat.

(**

  The A part is the type of labels.  For our [vec] example, a label is
  either (1) a proof that the natural number in the current parameter
  is 0, or (2) a pair of a proof that the natural number in the
  current parameter is less than 0 and the type in the current
  parameter.

 *)

Definition pw_vec_A {pp} (p : NVar) :=
  @mk_spread pp
    (mk_var p) nvara nvarb
    (mk_union (mk_equality (mk_var nvarb) mk_zero mk_tnat)
              (mk_prod (mk_less_than mk_zero (mk_var nvarb))
                       (mk_var nvara))).

(**

  The B part is the part that specifies the recursive calls.  For our
  [vec] example, in the [vnil] branch there is no recursive calls
  therefore we return [mk_void], and in the [vcons] branch there is
  one recursive call therefore we return [mk_unit].

 *)

Definition pw_vec_B {pp} (p a : NVar) :=
  @mk_decide pp (mk_var a) nvarx mk_void nvary mk_unit.

(**

  The C part provide the parameters from the recursive calls.  For our
  [vec] example, in the [vnil] branch because there is no recursive
  calls, we can return anything, and in the [vcons] branch, we have to
  build one parameter from the current parameter: the type does not
  change and we subtract 1 to the nat.

*)

Definition pw_vec_C {pp} (p a b : NVar) :=
  @mk_spread pp
    (mk_var p) nvara nvarb
    (mk_decide
       (mk_var a)
       nvarx (mk_var p)
       nvary (mk_pair (mk_var nvara) (mk_sub (mk_var nvarb) mk_one))
    ).

(**

  We now define [vec] as follow where [i] is [T]'s level.

*)

Definition pw_vec {pp} i T n :=
  @mk_pw pp
    (pw_vec_P i)
    nvarx (pw_vec_A nvarx)
    nvary nvarz (pw_vec_B nvary nvarz)
    nvara nvarb nvarc (pw_vec_C nvara nvarb nvarc)
    (mk_pair T n).


(**

  Using the concept of parameterized type families, we define
  parameterized M types as follows:

 *)

CoInductive pmeq {pp}
            lib
            (eqp : per)
            (eqa : per-fam(eqp))
            (eqb : per-fam-fam(eqp,eqa))
            (cp ca cb : NVar)
            (C : CVTerm [cp;ca;cb])
            (p : @CTerm pp)
            (t1 t2 : @CTerm pp) : [U] :=
| pmeq_cons :
    forall ep : eqp p p,
    forall a1 f1 a2 f2 : CTerm,
    forall ea : eqa p p ep a1 a2,
      t1 ===>(lib) (mkc_sup a1 f1)
      -> t2 ===>(lib) (mkc_sup a2 f2)
      -> (forall b1 b2,
            eqb p p ep a1 a2 ea b1 b2
            -> pmeq lib eqp eqa eqb
                    cp ca cb C
                    (lsubstc3 cp p ca a1 cb b1 C)
                    (mkc_apply f1 b1)
                    (mkc_apply f2 b2))
      -> pmeq lib eqp eqa eqb cp ca cb C p t1 t2.

Definition per_pm {p}
           lib
           (ts : cts)
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {eqp : per
   , {eqa : per-fam(eqp)
   , {eqb : per-fam-fam(eqp,eqa)
   , {p1, p2 : CTerm
   , {cp1, cp2, ca1, ca2, cb1, cb2 : NVar
   , {C1 : CVTerm [cp1, ca1, cb1]
   , {C2 : CVTerm [cp2, ca2, cb2]
      , type_pfamily lib mkc_pm ts T1 T2 eqp eqa eqb
                     cp1 ca1 cb1
                     C1
                     cp2 ca2 cb2
                     C2
                     p1 p2
      # eq <=2=> (pmeq lib eqp eqa eqb cp1 ca1 cb1 C1 p1)
       }}}}}}}.

(*
Definition per_rec (ts : cts) (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  {v1, v2 : NVar
   , {F1 : CVTerm [v1]
   , {F2 : CVTerm [v2]
   , {eqc : per
   , {eqb : forall a1 a2 : CTerm,
            forall eqa : per,
            forall e : ts a1 a2 eqa,
              per
      , ccomputes_to_valc T1 (mkc_rec v1 F1)
      # ccomputes_to_valc T2 (mkc_rec v2 F2)
      # (forall A1 A2 eqa,
         forall p : ts A1 A2 eqa,
           ts (substc A1 v1 F1) (substc A2 v2 F2) (eqb A1 A2 eqa p))
      # ts (substc (mkc_rec v1 F1) v1 F1) (substc (mkc_rec v1 F1) v1 F1) eqc
      # (forall t t', eq t t' <=> eqc t t')}}}}}.
*)

(* begin hide *)

(* --- now we define the Nuprl type system: nuprl_lia *)

(** close the different constructors with that and remove ccomputes_to_valc
 * from the per definitions *)
Definition close_compute {p} lib (ts : cts) (T1 T2 : @CTerm p) (eq : per(p)) :=
  {T3, T4 : CTerm
   $ ccomputes_to_valc lib T1 T3
   # ccomputes_to_valc lib T2 T4
   # ts T3 T4 eq}.

(* end hide *)

(**

  The [close] operator takes a candidate type system and returns a
  candidate type system closed under the type constructor defined
  above (except the ones for extensional intersection types and
  quotient types which are not yet in the system because we have not
  yet had time to prove that these types preserve the type system
  properties presented below).

 *)

Inductive close {p} lib (ts : cts) (T T' : @CTerm p) (eq : per(p)) : [U] :=
  | CL_init     : ts T T' eq -> close lib ts T T' eq
  | CL_int      : per_int      lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_atom     : per_atom     lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_uatom    : per_uatom    lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_base     : per_base     lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_approx   : per_approx   lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_cequiv   : per_cequiv   lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_eq       : per_eq       lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_req      : per_req      lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_teq      : per_teq      lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_isect    : per_isect    lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_func     : per_func     lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_disect   : per_disect   lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_pertype  : per_pertype  lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_ipertype : per_ipertype lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_spertype : per_spertype lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_w        : per_w        lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_m        : per_m        lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_pw       : per_pw       lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_pm       : per_pm       lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_texc     : per_texc     lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_union    : per_union    lib (close lib ts) T T' eq -> close lib ts T T' eq
(*  | CL_eunion   : per_eunion   lib (close lib ts) T T' eq -> close lib ts T T' eq*)
(*  | CL_union2   : per_union2   lib (close lib ts) T T' eq -> close lib ts T T' eq*)
  | CL_image    : per_image    lib (close lib ts) T T' eq -> close lib ts T T' eq
 (* | CL_eisect   : per_eisect   lib (close lib ts) T T' eq -> close lib ts T T' eq*)
  | CL_partial  : per_partial  lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_admiss   : per_admiss   lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_mono     : per_mono     lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_ffatom   : per_ffatom   lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_effatom  : per_effatom  lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_ffatoms  : per_ffatoms  lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_set      : per_set      lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_tunion   : per_tunion   lib (close lib ts) T T' eq -> close lib ts T T' eq
  | CL_product  : per_product  lib (close lib ts) T T' eq -> close lib ts T T' eq.
Hint Constructors close.

Arguments CL_init     {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_int      {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_atom     {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_uatom    {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_base     {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_approx   {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_cequiv   {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_eq       {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_req      {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_teq      {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_isect    {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_func     {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_disect   {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_pertype  {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_ipertype {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_spertype {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_w        {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_m        {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_pw       {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_pm       {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_texc     {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_union    {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_image    {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_partial  {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_admiss   {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_mono     {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_ffatom   {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_effatom  {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_ffatoms  {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_set      {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_tunion   {p} [lib] [ts] [T] [T'] [eq] _.
Arguments CL_product  {p} [lib] [ts] [T] [T'] [eq] _.

(* begin hide *)


Tactic Notation "close_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CL_init"
  | Case_aux c "CL_int"
  | Case_aux c "CL_atom"
  | Case_aux c "CL_uatom"
  | Case_aux c "CL_base"
  | Case_aux c "CL_approx"
  | Case_aux c "CL_cequiv"
  | Case_aux c "CL_eq"
  | Case_aux c "CL_req"
  | Case_aux c "CL_teq"
  | Case_aux c "CL_isect"
  | Case_aux c "CL_func"
  | Case_aux c "CL_disect"
  | Case_aux c "CL_pertype"
  | Case_aux c "CL_ipertype"
  | Case_aux c "CL_spertype"
  | Case_aux c "CL_w"
  | Case_aux c "CL_m"
  | Case_aux c "CL_pw"
  | Case_aux c "CL_pm"
  | Case_aux c "CL_texc"
  | Case_aux c "CL_union"
(*  | Case_aux c "CL_eunion"*)
(*  | Case_aux c "CL_union2"*)
  | Case_aux c "CL_image"
(*  | Case_aux c "CL_eisect"*)
  | Case_aux c "CL_partial"
  | Case_aux c "CL_admiss"
  | Case_aux c "CL_mono"
  | Case_aux c "CL_ffatom"
  | Case_aux c "CL_effatom"
  | Case_aux c "CL_ffatoms"
  | Case_aux c "CL_set"
  | Case_aux c "CL_tunion"
  | Case_aux c "CL_product"
  ].

Definition close_ind' {pp}
           lib
  (P : cts -> cts)
  (init : forall (ts : cts)
                 (T T' : @CTerm pp)
                 (eq : per),
            ts T T' eq -> P ts T T' eq)
  (int  : forall (ts : cts)
                 (T T' : @CTerm pp)
                 (eq : per)
                 (per : per_int lib (close lib ts) T T' eq),
            P ts T T' eq)
  (atom : forall (ts : cts)
                 (T T' : @CTerm pp)
                 (eq : per)
                 (per : per_atom lib (close lib ts) T T' eq),
            P ts T T' eq)
  (uatom : forall (ts : cts)
                 (T T' : @CTerm pp)
                 (eq : per)
                 (per : per_uatom lib (close lib ts) T T' eq),
            P ts T T' eq)
  (base : forall (ts : cts)
                 (T T' : @CTerm pp)
                 (eq : per)
                 (per : per_base lib (close lib ts) T T' eq),
            P ts T T' eq)
  (aprx : forall (ts : cts)
                 (T T' : @CTerm pp)
                 (eq : per)
                 (per : per_approx lib (close lib ts) T T' eq),
              P ts T T' eq)
  (ceq : forall (ts : cts)
                (T T' : @CTerm pp)
                (eq : per)
                (per : per_cequiv lib (close lib ts) T T' eq),
           P ts T T' eq)
  (equ  : forall (ts : cts)
                 (T T' : @CTerm pp)
                 (eq : per)
                 (A B a1 a2 b1 b2 : @CTerm pp)
                 (eqa : per)
                 (c1 : T ===>(lib) (mkc_equality a1 a2 A))
                 (c2 : T' ===>(lib) (mkc_equality b1 b2 B))
                 (cla : close lib ts A B eqa)
                 (reca : P ts A B eqa)
                 (eos1 : eqindomain eqa a1 b1)
                 (eos2 : eqindomain eqa a2 b2)
                 (eqiff : forall t t',
                            eq t t'
                               <=> t ===>(lib) mkc_axiom
                               # t' ===>(lib) mkc_axiom
                               # eqa a1 a2)
                 (per : per_eq lib (close lib ts) T T' eq),
            P ts T T' eq)
  (requ : forall (ts : cts)
                 (T T' : @CTerm pp)
                 (eq : per)
                 (A B a1 a2 b1 b2 : @CTerm pp)
                 (eqa : per)
                 (c1 : T ===>(lib) (mkc_requality a1 a2 A))
                 (c2 : T' ===>(lib) (mkc_requality b1 b2 B))
                 (cla : close lib ts A B eqa)
                 (reca : P ts A B eqa)
                 (eo1 : eqorceq lib eqa a1 b1)
                 (eo2 : eqorceq lib eqa a2 b2)
                 (eqiff : eq <=2=> (per_req_eq lib a1 a2 eqa))
                 (per : per_req lib (close lib ts) T T' eq),
            P ts T T' eq)
  (tequ : forall (ts : cts)
                 (T T' : @CTerm pp)
                 (eq : per)
                 (a1 a2 b1 b2 : @CTerm pp)
                 (eqa : per)
                 (c1 : T ===>(lib) (mkc_tequality a1 a2))
                 (c2 : T' ===>(lib) (mkc_tequality b1 b2))
                 (cl1  : close lib ts a1 b1 eqa)
                 (rec1 : P ts a1 b1 eqa)
                 (cl2  : close lib ts a2 b2 eqa)
                 (rec2 : P ts a2 b2 eqa)
                 (cl3  : close lib ts a1 a2 eqa)
                 (rec3 : P ts a1 a2 eqa)
                 (eqiff : eq <=2=> (fun t t' => True))
                 (per : per_teq lib (close lib ts) T T' eq),
            P ts T T' eq)
  (isect : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' : @CTerm pp)
                  (v v' : NVar)
                  (B : CVTerm [v])
                  (B' : CVTerm [v'])
                  (eqa : per)
                  (eqb : forall a a' : CTerm, forall e : eqa a a', per)
                  (c1 : T ===>(lib) (mkc_isect A v B))
                  (c2 : T' ===>(lib) (mkc_isect A' v' B'))
                  (cla : close lib ts A A' eqa)
                  (reca : P ts A A' eqa)
                  (clb : forall a a', forall e : eqa a a', close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
                  (recb : forall a a', forall e : eqa a a', P ts (substc a v B) (substc a' v' B') (eqb a a' e))
                  (eqiff : forall t t', eq t t' <=> (forall a a', forall e : eqa a a', eqb a a' e t t'))
                  (per : per_isect lib (close lib ts) T T' eq),
             P ts T T' eq)
  (func : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' : @CTerm pp)
                  (v v' : NVar)
                  (B : CVTerm [v])
                  (B' : CVTerm [v'])
                  (eqa : per)
                  (eqb : forall a a' : CTerm, forall e : eqa a a', per)
                  (c1 : T ===>(lib) (mkc_function A v B))
                  (c2 : T' ===>(lib) (mkc_function A' v' B'))
                  (cla : close lib ts A A' eqa)
                  (reca : P ts A A' eqa)
                  (clb : forall a a', forall e : eqa a a', close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
                  (recb : forall a a', forall e : eqa a a', P ts (substc a v B) (substc a' v' B') (eqb a a' e))
                  (eqiff : forall t t', eq t t'
                                           <=>
                                           (forall a a',
                                            forall e : eqa a a',
                                              (eqb a a' e)
                                                (mkc_apply t a)
                                                (mkc_apply t' a')))
                  (per : per_func lib (close lib ts) T T' eq),
            P ts T T' eq)
  (disect : forall (ts : cts)
                   (T T' : @CTerm pp)
                   (eq : per)
                   (A A' : @CTerm pp)
                   (v v' : NVar)
                   (B : CVTerm [v])
                   (B' : CVTerm [v'])
                   (eqa : per)
                   (eqb : forall a a' : CTerm, forall e : eqa a a', per)
                   (c1 : T ===>(lib) (mkc_disect A v B))
                   (c2 : T' ===>(lib) (mkc_disect A' v' B'))
                   (cla : close lib ts A A' eqa)
                   (reca : P ts A A' eqa)
                   (clb : forall a a', forall e : eqa a a', close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
                   (recb : forall a a', forall e : eqa a a', P ts (substc a v B) (substc a' v' B') (eqb a a' e))
                   (eqiff : forall t t', eq t t' <=> {e : eqa t t' , eqb t t' e t t'})
                   (per : per_disect lib (close lib ts) T T' eq),
              P ts T T' eq)
  (pertype : forall (ts : cts)
                    (T T' : @CTerm pp)
                    (eq : per)
                    (R1 R2 : @CTerm pp)
                    (eq1 eq2 : CTerm -> CTerm -> per)
                    (c1 : T ===>(lib) (mkc_pertype R1))
                    (c2 : T' ===>(lib) (mkc_pertype R2))
                    (cl1 : forall x y, close lib ts
                                             (mkc_apply2 R1 x y)
                                             (mkc_apply2 R1 x y)
                                             (eq1 x y))
                    (rec1 : forall x y, P ts
                                          (mkc_apply2 R1 x y)
                                          (mkc_apply2 R1 x y)
                                          (eq1 x y))
                    (cl2 : forall x y, close lib ts
                                             (mkc_apply2 R2 x y)
                                             (mkc_apply2 R2 x y)
                                             (eq2 x y))
                    (rec2 : forall x y, P ts
                                          (mkc_apply2 R2 x y)
                                          (mkc_apply2 R2 x y)
                                          (eq2 x y))
                    (inh : forall x y, inhabited (eq1 x y) <=> inhabited (eq2 x y))
                    (isper : is_per eq1)
                    (eqiff : forall t t', eq t t' <=> inhabited (eq1 t t'))
                    (per : per_pertype lib (close lib ts) T T' eq),
               P ts T T' eq)
  (ipertype : forall (ts : cts)
                     (T T' : @CTerm pp)
                     (eq : per)
                     (R1 R2 : @CTerm pp)
                     (eq1 : CTerm -> CTerm -> per)
                     (c1 : T ===>(lib) (mkc_ipertype R1))
                     (c2 : T' ===>(lib) (mkc_ipertype R2))
                     (cl1 : forall x y, close lib ts
                                              (mkc_apply2 R1 x y)
                                              (mkc_apply2 R2 x y)
                                              (eq1 x y))
                     (rec1 : forall x y, P ts
                                           (mkc_apply2 R1 x y)
                                           (mkc_apply2 R2 x y)
                                           (eq1 x y))
                     (isper : is_per eq1)
                     (eqiff : eq <=2=> (pertype_eq eq1))
                     (per : per_ipertype lib (close lib ts) T T' eq),
                P ts T T' eq)
  (spertype : forall (ts : cts)
                     (T T' : @CTerm pp)
                     (eq : per)
                     (R1 R2 : @CTerm pp)
                     (eq1 : CTerm -> CTerm -> per)
                     (c1 : T ===>(lib) (mkc_spertype R1))
                     (c2 : T' ===>(lib) (mkc_spertype R2))
                     (cl1 : forall x y,
                              close lib ts (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (eq1 x y))
                     (rec1 : forall x y,
                               P ts (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (eq1 x y))
                     (cl2 : forall x y z,
                              inhabited(eq1 x z)
                              -> close lib ts (mkc_apply2 R1 x y) (mkc_apply2 R1 z y) (eq1 x y))
                     (rec2 : forall x y z,
                               inhabited(eq1 x z)
                               -> P ts (mkc_apply2 R1 x y) (mkc_apply2 R1 z y) (eq1 x y))
                     (cl3 : forall x y z,
                              inhabited(eq1 y z)
                              -> close lib ts (mkc_apply2 R1 x y) (mkc_apply2 R1 x z) (eq1 x y))
                     (rec3 : forall x y z,
                               inhabited(eq1 y z)
                               -> P ts (mkc_apply2 R1 x y) (mkc_apply2 R1 x z) (eq1 x y))
                     (isper : is_per eq1)
                     (eqiff : eq <=2=> (pertype_eq eq1))
                     (per : per_spertype lib (close lib ts) T T' eq),
                P ts T T' eq)
  (w     : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' : @CTerm pp)
                  (v v' : NVar)
                  (B : CVTerm [v])
                  (B' : CVTerm [v'])
                  (eqa : per)
                  (eqb : forall a a' : CTerm, forall e : eqa a a', per)
                  (c1 : T ===>(lib) (mkc_w A v B))
                  (c2 : T' ===>(lib) (mkc_w A' v' B'))
                  (cla : close lib ts A A' eqa)
                  (reca : P ts A A' eqa)
                  (clb : forall a a', forall e : eqa a a', close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
                  (recb : forall a a', forall e : eqa a a', P ts (substc a v B) (substc a' v' B') (eqb a a' e))
                  (eqiff : forall t t', eq t t' <=> weq lib eqa eqb t t')
                  (per : per_w lib (close lib ts) T T' eq),
            P ts T T' eq)
  (m     : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' : @CTerm pp)
                  (v v' : NVar)
                  (B : CVTerm [v])
                  (B' : CVTerm [v'])
                  (eqa : per)
                  (eqb : forall a a' : CTerm, forall e : eqa a a', per)
                  (c1 : T ===>(lib) (mkc_m A v B))
                  (c2 : T' ===>(lib) (mkc_m A' v' B'))
                  (cla : close lib ts A A' eqa)
                  (reca : P ts A A' eqa)
                  (clb : forall a a', forall e : eqa a a', close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
                  (recb : forall a a', forall e : eqa a a', P ts (substc a v B) (substc a' v' B') (eqb a a' e))
                  (eqiff : forall t t', eq t t' <=> meq lib eqa eqb t t')
                  (per : per_m lib (close lib ts) T T' eq),
            P ts T T' eq)
  (pw    : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (Pr Pr' : @CTerm pp)
                  (ap ap' : NVar)
                  (A : CVTerm [ap])
                  (A' : CVTerm [ap'])
                  (bp bp' ba ba' : NVar)
                  (B : CVTerm [bp,ba])
                  (B' : CVTerm [bp',ba'])
                  (cp cp' ca ca' cb cb' : NVar)
                  (C : CVTerm [cp,ca,cb])
                  (C' : CVTerm [cp',ca',cb'])
                  (p p' : @CTerm pp)
                  (eqp : per)
                  (eqa : forall p p' : CTerm, forall e : eqp p p', per)
                  (eqb : forall p p' : CTerm,
                         forall ep : eqp p p',
                         forall a a' : CTerm,
                         forall ea : eqa p p' ep a a',
                           per)
                  (c1 : T ===>(lib) (mkc_pw Pr ap A bp ba B cp ca cb C p))
                  (c2 : T' ===>(lib) (mkc_pw Pr' ap' A' bp' ba' B' cp' ca' cb' C' p'))
                  (clp : close lib ts Pr Pr' eqp)
                  (recp : P ts Pr Pr' eqp)
                  (cla : forall p p',
                         forall ep : eqp p p',
                           close lib ts (substc p ap A) (substc p' ap' A') (eqa p p' ep))
                  (reca : forall p p',
                          forall ep : eqp p p',
                            P ts (substc p ap A) (substc p' ap' A') (eqa p p' ep))
                  (clb : forall p p',
                         forall ep : eqp p p',
                         forall a a',
                         forall ea : eqa p p' ep a a',
                           close lib ts
                                 (lsubstc2 bp p ba a B)
                                 (lsubstc2 bp' p' ba' a' B')
                                 (eqb p p' ep a a' ea))
                  (recb : forall p p',
                          forall ep : eqp p p',
                          forall a a',
                          forall ea : eqa p p' ep a a',
                            P ts
                              (lsubstc2 bp p ba a B)
                              (lsubstc2 bp' p' ba' a' B')
                              (eqb p p' ep a a' ea))
                  (eqc : forall p p',
                         forall ep : eqp p p',
                         forall a a',
                         forall ea : eqa p p' ep a a',
                         forall b b',
                         forall eb : eqb p p' ep a a' ea b b',
                           eqp (lsubstc3 cp p ca a cb b C)
                               (lsubstc3 cp' p' ca' a' cb' b' C'))
                  (peq : eqp p p')
                  (eqiff : forall t t', eq t t' <=> pweq lib eqp eqa eqb cp ca cb C p t t')
                  (per : per_pw lib (close lib ts) T T' eq),
            P ts T T' eq)
  (pm    : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (Pr Pr' : @CTerm pp)
                  (ap ap' : NVar)
                  (A : CVTerm [ap])
                  (A' : CVTerm [ap'])
                  (bp bp' ba ba' : NVar)
                  (B : CVTerm [bp,ba])
                  (B' : CVTerm [bp',ba'])
                  (cp cp' ca ca' cb cb' : NVar)
                  (C : CVTerm [cp,ca,cb])
                  (C' : CVTerm [cp',ca',cb'])
                  (p p' : @CTerm pp)
                  (eqp : per)
                  (eqa : forall p p' : CTerm, forall e : eqp p p', per)
                  (eqb : forall p p' : CTerm,
                         forall ep : eqp p p',
                         forall a a' : CTerm,
                         forall ea : eqa p p' ep a a',
                           per)
                  (c1 : T ===>(lib) (mkc_pm Pr ap A bp ba B cp ca cb C p))
                  (c2 : T' ===>(lib) (mkc_pm Pr' ap' A' bp' ba' B' cp' ca' cb' C' p'))
                  (clp : close lib ts Pr Pr' eqp)
                  (recp : P ts Pr Pr' eqp)
                  (cla : forall p p',
                         forall ep : eqp p p',
                           close lib ts (substc p ap A) (substc p' ap' A') (eqa p p' ep))
                  (reca : forall p p',
                          forall ep : eqp p p',
                            P ts (substc p ap A) (substc p' ap' A') (eqa p p' ep))
                  (clb : forall p p',
                         forall ep : eqp p p',
                         forall a a',
                         forall ea : eqa p p' ep a a',
                           close lib ts
                                 (lsubstc2 bp p ba a B)
                                 (lsubstc2 bp' p' ba' a' B')
                                 (eqb p p' ep a a' ea))
                  (recb : forall p p',
                          forall ep : eqp p p',
                          forall a a',
                          forall ea : eqa p p' ep a a',
                            P ts
                              (lsubstc2 bp p ba a B)
                              (lsubstc2 bp' p' ba' a' B')
                              (eqb p p' ep a a' ea))
                  (eqc : forall p p',
                         forall ep : eqp p p',
                         forall a a',
                         forall ea : eqa p p' ep a a',
                         forall b b',
                         forall eb : eqb p p' ep a a' ea b b',
                           eqp (lsubstc3 cp p ca a cb b C)
                               (lsubstc3 cp' p' ca' a' cb' b' C'))
                  (peq : eqp p p')
                  (eqiff : forall t t', eq t t' <=> pmeq lib eqp eqa eqb cp ca cb C p t t')
                  (per : per_pm lib (close lib ts) T T' eq),
            P ts T T' eq)
  (texc : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (N N' E E' : @CTerm pp)
                  (eqn eqe : per)
                  (c1 : T ===>(lib) (mkc_texc N E))
                  (c2 : T' ===>(lib) (mkc_texc N' E'))
                  (cln : close lib ts N N' eqn)
                  (recn : P ts N N' eqn)
                  (cle : close lib ts E E' eqe)
                  (rece : P ts E E' eqe)
                  (eqiff : forall t t', eq t t' <=> per_texc_eq lib eqn eqe t t')
                  (per : per_texc lib (close lib ts) T T' eq),
            P ts T T' eq)
  (union : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' B B' : @CTerm pp)
                  (eqa eqb : per)
                  (c1 : T ===>(lib) (mkc_union A B))
                  (c2 : T' ===>(lib) (mkc_union A' B'))
                  (cla : close lib ts A A' eqa)
                  (reca : P ts A A' eqa)
                  (clb : close lib ts B B' eqb)
                  (recb : P ts B B' eqb)
                  (eqiff : forall t t', eq t t' <=> per_union_eq lib eqa eqb t t')
                  (per : per_union lib (close lib ts) T T' eq),
            P ts T T' eq)
(*  (eunion : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' B B' : @CTerm pp)
                  (eqa1 eqa2 eqb1 eqb2 : per)
                  (c1 : T ===>(lib) (mkc_eunion A B))
                  (c2 : T' ===>(lib) (mkc_eunion A' B'))
                  (iffa : eqa1 <=2=> eqa2)
                  (iffb : eqb1 <=2=> eqb2)
                  (cla1  : close lib ts A A eqa1)
                  (reca1 : P ts A A eqa1)
                  (cla2  : close lib ts A' A' eqa2)
                  (reca2 : P ts A' A' eqa2)
                  (clb1  : close lib ts B B eqb1)
                  (recb1 : P ts B B eqb1)
                  (clb2  : close lib ts B' B' eqb2)
                  (recb2 : P ts B' B' eqb2)
                  (eqiff : eq <=2=> (per_union_eq lib eqa1 eqb1))
                  (per : per_eunion lib (close lib ts) T T' eq),
            P ts T T' eq)*)
(*  (union2 : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' B B' : @CTerm pp)
                  (eqa : per)
                  (c1 : T ===>(lib) (mkc_union2 A B))
                  (c2 : T' ===>(lib) (mkc_union2 A' B'))
                  (cla : close lib ts A A' eqa)
                  (reca : P ts A A' eqa)
                  (clb : close lib ts B B' eqb)
                  (recb : P ts B B' eqb)
                  (eqiff : forall t t', eq t t' <=> per_union_eq lib eqa eqb t t')
                  (per : per_union2 lib (close lib ts) T T' eq),
            P ts T T' eq)*)
  (image : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' f f' : @CTerm pp)
                  (eqa : per)
                  (c1 : T ===>(lib) (mkc_image A f))
                  (c2 : T' ===>(lib) (mkc_image A' f'))
                  (cla : close lib ts A A' eqa)
                  (reca : P ts A A' eqa)
                  (ceq : ccequivc lib f f')
                  (eqiff : forall t t', eq t t' <=> per_image_eq lib eqa f t t')
                  (per : per_image lib (close lib ts) T T' eq),
            P ts T T' eq)
(*  (eisect : forall (ts : cts)
                   (T T' : @CTerm pp)
                   (eq : per)
                   (eqa : per)
                   (eqa' : per)
                   (eqb : per-efam(eqa,eqa'))
                   (A A' : @CTerm pp)
                   (v v' : NVar)
                   (B : CVTerm [v])
                   (B' : CVTerm [v'])
                   (f  : t-sel(eqa))
                   (g  : e-sel(eqa,eqa',f))
                   (f' : t-sel(eqa'))
                   (g' : e-sel(eqa',eqa,f'))
                   (c1 : T ===>(lib) (mkc_eisect A v B))
                   (c2 : T' ===>(lib) (mkc_eisect A' v' B'))
                   (cla : close ts A A eqa)
                   (reca : P ts A A eqa)
                   (cla' : close ts A' A' eqa')
                   (reca' : P ts A' A' eqa')
                   (clb : forall a (e : eqa a a),
                            close ts
                                  (substc a v B)
                                  (substc (f a e) v' B')
                                  (eqb a (f a e) e (g a e)))
                   (recb : forall a (e : eqa a a),
                             P ts
                               (substc a v B)
                               (substc (f a e) v' B')
                               (eqb a (f a e) e (g a e)))
                   (clb' : forall a' (e' : eqa' a' a'),
                             close ts
                                   (substc (f' a' e') v B)
                                   (substc a' v' B')
                                   (eqb (f' a' e') a' (g' a' e') e'))
                   (recb' : forall a' (e' : eqa' a' a'),
                              P ts
                                (substc (f' a' e') v B)
                                (substc a' v' B')
                                (eqb (f' a' e') a' (g' a' e') e'))
                   (eqiff : eq <=2=> (eisect_eq eqa eqa' eqb))
                   (per : per_eisect lib (close lib ts) T T' eq),
              P ts T T' eq)*)
  (partial : forall (ts : cts)
                    (T T' : @CTerm pp)
                    (eq : per)
                    (A1 A2 : @CTerm pp)
                    (eqa : per)
                    (c1 : T ===>(lib) (mkc_partial A1))
                    (c2 : T' ===>(lib) (mkc_partial A2))
                    (cla : close lib ts A1 A2 eqa)
                    (reca : P ts A1 A2 eqa)
                    (hv : forall a, eqa a a -> chaltsc lib a)
                    (eqiff : forall t t', eq t t' <=> per_partial_eq lib eqa t t')
                    (per : per_partial lib (close lib ts) T T' eq),
               P ts T T' eq)
  (admiss : forall (ts : cts)
                    (T T' : @CTerm pp)
                    (eq : per)
                    (A1 A2 : @CTerm pp)
                    (eqa : per)
                    (c1 : T ===>(lib) (mkc_admiss A1))
                    (c2 : T' ===>(lib) (mkc_admiss A2))
                    (cla : close lib ts A1 A2 eqa)
                    (reca : P ts A1 A2 eqa)
                    (eqiff : (forall t t' : CTerm,
                      eq t t' <=>
                        (t) ===>(lib) (mkc_axiom) # (t') ===>(lib) (mkc_axiom) # admissible_equality eqa))
                    (per : per_admiss lib (close lib ts) T T' eq),
               P ts T T' eq)
  (mono : forall (ts : cts)
                    (T T' : @CTerm pp)
                    (eq : per)
                    (A1 A2 : @CTerm pp)
                    (eqa : per)
                    (c1 : T ===>(lib) (mkc_mono A1))
                    (c2 : T' ===>(lib) (mkc_mono A2))
                    (cla : close lib ts A1 A2 eqa)
                    (reca : P ts A1 A2 eqa)
                    (eqiff : (forall t t' : CTerm,
                      eq t t' <=>
                        (t) ===>(lib) (mkc_axiom) # (t') ===>(lib) (mkc_axiom) # mono_equality lib eqa))
                    (per : per_mono lib (close lib ts) T T' eq),
               P ts T T' eq)
  (ffatom : forall (ts : cts)
                    (T T' : @CTerm pp)
                    (eq : per)
                    (A1 A2 x1 x2 a1 a2 : @CTerm pp)
                    (eqa : per)
                    (u : get_patom_set pp)
                    (c1 : T ===>(lib) (mkc_free_from_atom A1 x1 a1))
                    (c2 : T' ===>(lib) (mkc_free_from_atom A2 x2 a2))
                    (cla : close lib ts A1 A2 eqa)
                    (reca : P ts A1 A2 eqa)
                    (ex : eqa x1 x2)
                    (ca1 : a1 ===>(lib) (mkc_utoken u))
                    (ca2 : a2 ===>(lib) (mkc_utoken u))
                    (eqiff : eq <=2=> (per_ffatom_eq lib eqa u x1))
                    (per : per_ffatom lib (close lib ts) T T' eq),
               P ts T T' eq)
  (effatom : forall (ts : cts)
                    (T T' : @CTerm pp)
                    (eq : per)
                    (A1 A2 x1 x2 a1 a2 : @CTerm pp)
                    (eqa : per)
                    (c1 : T ===>(lib) (mkc_efree_from_atom A1 x1 a1))
                    (c2 : T' ===>(lib) (mkc_efree_from_atom A2 x2 a2))
                    (cla : close lib ts A1 A2 eqa)
                    (reca : P ts A1 A2 eqa)
                    (niff : name_not_in_upto lib a1 x1 eqa <=> name_not_in_upto lib a2 x2 eqa)
                    (eqiff : eq <=2=> (per_effatom_eq lib eqa a1 x1))
                    (per : per_effatom lib (close lib ts) T T' eq),
               P ts T T' eq)
  (ffatoms : forall (ts : cts)
                    (T T' : @CTerm pp)
                    (eq : per)
                    (A1 A2 x1 x2 : @CTerm pp)
                    (eqa : per)
                    (c1 : T ===>(lib) (mkc_free_from_atoms A1 x1))
                    (c2 : T' ===>(lib) (mkc_free_from_atoms A2 x2))
                    (cla : close lib ts A1 A2 eqa)
                    (reca : P ts A1 A2 eqa)
                    (ex : eqa x1 x2)
                    (eqiff : eq <=2=> (per_ffatoms_eq lib eqa x1))
                    (per : per_ffatoms lib (close lib ts) T T' eq),
               P ts T T' eq)
  (subset : forall (ts : cts)
                   (T T' : @CTerm pp)
                   (eq : per)
                   (A A' : @CTerm pp)
                   (v v' : NVar)
                   (B : CVTerm [v])
                   (B' : CVTerm [v'])
                   (eqa : per)
                   (eqb : forall a a' : CTerm, forall e : eqa a a', per)
                   (c1 : T ===>(lib) (mkc_set A v B))
                   (c2 : T' ===>(lib) (mkc_set A' v' B'))
                   (cla : close lib ts A A' eqa)
                   (reca : P ts A A' eqa)
                   (clb : forall a a', forall e : eqa a a', close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
                   (recb : forall a a', forall e : eqa a a', P ts (substc a v B) (substc a' v' B') (eqb a a' e))
                   (eqiff : forall t t', eq t t' <=> {e : eqa t t' , inhabited (eqb t t' e)})
                   (per : per_set lib (close lib ts) T T' eq),
              P ts T T' eq)
  (tunion : forall (ts : cts)
                   (T T' : @CTerm pp)
                   (eq : per)
                   (A A' : @CTerm pp)
                   (v v' : NVar)
                   (B : CVTerm [v])
                   (B' : CVTerm [v'])
                   (eqa : per)
                   (eqb : forall a a' : CTerm, forall e : eqa a a', per)
                   (c1 : T ===>(lib) (mkc_tunion A v B))
                   (c2 : T' ===>(lib) (mkc_tunion A' v' B'))
                   (cla : close lib ts A A' eqa)
                   (reca : P ts A A' eqa)
                   (clb : forall a a', forall e : eqa a a', close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
                   (recb : forall a a', forall e : eqa a a', P ts (substc a v B) (substc a' v' B') (eqb a a' e))
                   (eqiff : forall t t', eq t t' <=> per_tunion_eq eqa eqb t t')
                   (per : per_tunion lib (close lib ts) T T' eq),
              P ts T T' eq)
  (product : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' : @CTerm pp)
                  (v v' : NVar)
                  (B : CVTerm [v])
                  (B' : CVTerm [v'])
                  (eqa : per)
                  (eqb : forall a a' : CTerm, forall e : eqa a a', per)
                  (c1 : T ===>(lib) (mkc_product A v B))
                  (c2 : T' ===>(lib) (mkc_product A' v' B'))
                  (cla : close lib ts A A' eqa)
                  (reca : P ts A A' eqa)
                  (clb : forall a a', forall e : eqa a a', close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
                  (recb : forall a a', forall e : eqa a a', P ts (substc a v B) (substc a' v' B') (eqb a a' e))
                  (eqiff : forall t t', eq t t' <=> per_product_eq lib eqa eqb t t')
                  (per : per_product lib (close lib ts) T T' eq),
            P ts T T' eq)
(*  (esquash : forall (ts : cts)
                    (T T' : @CTerm pp)
                    (eq : per)
                    (A1 A2 : @CTerm pp)
                    (eq1 eq2 : per)
                    (c1 : ccomputes_to_valc T  (mkc_esquash A1))
                    (c2 : ccomputes_to_valc T' (mkc_esquash A2))
                    (cl1 : close ts A1 A1 eq1)
                    (rec1 : P ts A1 A1 eq1)
                    (cl2 : close ts A2 A2 eq2)
                    (rec2 : P ts A2 A2 eq2)
                    (inh : inhabited eq1 <=> inhabited eq2)
                    (eqiff : forall t t', eq t t'
                                             <=>
                                             ccomputes_to_valc t mkc_axiom
                                             # ccomputes_to_valc t' mkc_axiom
                                             # inhabited eq1)
                    (per : per_esquash lib (close lib ts) T T' eq),
               P ts T T' eq)*)
   : forall (ts : cts)
            (T T' : @CTerm pp)
            (eq : per)
            (t : close lib ts T T' eq),
            P ts T T' eq :=
 fix rec (ts : cts)
         (T T' : @CTerm pp)
         (eq : per)
         (t : close lib ts T T' eq)
         : P ts T T' eq :=
   match t in close _ _ _ _ _ return P ts T T' eq with
   | CL_init   pts => init  ts T T' eq pts
   | CL_int    pts => int   ts T T' eq pts
   | CL_atom   pts => atom  ts T T' eq pts
   | CL_uatom  pts => uatom ts T T' eq pts
   | CL_base   pts => base  ts T T' eq pts
   | CL_approx pts => aprx  ts T T' eq pts
   | CL_cequiv pts => ceq   ts T T' eq pts
   | CL_eq pts =>
       let (A,    x) := pts in
       let (B,    x) := x in
       let (a1,   x) := x in
       let (a2,   x) := x in
       let (b1,   x) := x in
       let (b2,   x) := x in
       let (eqa,  x) := x in
       let (cT1,  x) := x in
       let (cT2,  x) := x in
       let (tsa,  x) := x in
       let (eqa1, x) := x in
       let (eqa2, x) := x in
         equ ts T T' eq A B a1 a2 b1 b2 eqa
             cT1
             cT2
             tsa
             (rec ts A B eqa tsa)
             eqa1
             eqa2
             x
             pts
   | CL_req pts =>
       let (A,    x) := pts in
       let (B,    x) := x in
       let (a1,   x) := x in
       let (a2,   x) := x in
       let (b1,   x) := x in
       let (b2,   x) := x in
       let (eqa,  x) := x in
       let (cT1,  x) := x in
       let (cT2,  x) := x in
       let (tsa,  x) := x in
       let (eo1,  x) := x in
       let (eo2, eqiff) := x in
         requ ts T T' eq A B a1 a2 b1 b2 eqa
              cT1
              cT2
              tsa
              (rec ts A B eqa tsa)
              eo1 eo2
              eqiff
              pts
   | CL_teq pts =>
       let (a1,   x) := pts in
       let (a2,   x) := x in
       let (b1,   x) := x in
       let (b2,   x) := x in
       let (eqa,  x) := x in
       let (cT1,  x) := x in
       let (cT2,  x) := x in
       let (ts1,  x) := x in
       let (ts2,  x) := x in
       let (ts3, eqiff) := x in
       tequ ts T T' eq a1 a2 b1 b2 eqa
            cT1
            cT2
            ts1
            (rec ts a1 b1 eqa ts1)
            ts2
            (rec ts a2 b2 eqa ts2)
            ts3
            (rec ts a1 a2 eqa ts3)
            eqiff
            pts
   | CL_isect pts =>
       let (eqa, x)   := pts in
       let (eqb, x)   := x in
       let (tf,  teq) := x in
       let (A,   x)   := tf in
       let (A',  x)   := x in
       let (v,   x)   := x in
       let (v',  x)   := x in
       let (B,   x)   := x in
       let (B',  x)   := x in
       let (ctv1, x)  := x in
       let (ctv2, x)  := x in
       let (tsa, ftsb) := x in
         isect ts T T' eq A A' v v' B B' eqa eqb
               ctv1
               ctv2
               tsa
               (rec ts A A' eqa tsa)
               ftsb
               (fun a a' eqa => rec ts
                                    (substc a v B)
                                    (substc a' v' B')
                                    (eqb a a' eqa)
                                    (ftsb a a' eqa))
               teq
               pts
   | CL_func pts =>
       let (eqa, x) := pts in
       let (eqb, x) := x in
       let (tf, teq) := x in
       let (A,   x) := tf in
       let (A',  x) := x in
       let (v,   x) := x in
       let (v',  x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, tsb) := x in
         func ts T T' eq A A' v v' B B' eqa eqb
               c1
               c2
               tsa
               (rec ts A A' eqa tsa)
               tsb
               (fun a a' eqa =>
                  rec ts
                      (substc a v B)
                      (substc a' v' B')
                      (eqb a a' eqa)
                      (tsb a a' eqa))
               teq
               pts
   | CL_disect pts =>
       let (eqa, x)   := pts in
       let (eqb, x)   := x in
       let (tf,  teq) := x in
       let (A,   x)   := tf in
       let (A',  x)   := x in
       let (v,   x)   := x in
       let (v',  x)   := x in
       let (B,   x)   := x in
       let (B',  x)   := x in
       let (ctv1, x)  := x in
       let (ctv2, x)  := x in
       let (tsa, ftsb) := x in
         disect ts T T' eq A A' v v' B B' eqa eqb
                ctv1
                ctv2
                tsa
                (rec ts A A' eqa tsa)
                ftsb
                (fun a a' eqa => rec ts
                                     (substc a v B)
                                     (substc a' v' B')
                                     (eqb a a' eqa)
                                     (ftsb a a' eqa))
                teq
                pts
   | CL_pertype pts =>
       let (R1,  x) := pts in
       let (R2,  x) := x in
       let (eq1, x) := x in
       let (eq2, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (F1,  x) := x in
       let (F2,  x) := x in
       let (inh, x) := x in
       let (isp, eqt)  := x in
         pertype ts T T' eq R1 R2 eq1 eq2
               c1
               c2
               F1
               (fun x y => rec ts
                               (mkc_apply2 R1 x y)
                               (mkc_apply2 R1 x y)
                               (eq1 x y)
                               (F1 x y))
               F2
               (fun x y => rec ts
                               (mkc_apply2 R2 x y)
                               (mkc_apply2 R2 x y)
                               (eq2 x y)
                               (F2 x y))
               inh
               isp
               eqt
               pts
   | CL_ipertype pts =>
       let (R1,  x) := pts in
       let (R2,  x) := x in
       let (eq1, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (F1,  x) := x in
       let (isp, eqt)  := x in
         ipertype ts T T' eq R1 R2 eq1
               c1
               c2
               F1
               (fun x y => rec ts
                               (mkc_apply2 R1 x y)
                               (mkc_apply2 R2 x y)
                               (eq1 x y)
                               (F1 x y))
               isp
               eqt
               pts
   | CL_spertype pts =>
       let (R1,  x) := pts in
       let (R2,  x) := x in
       let (eq1, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (F1,  x) := x in
       let (F2,  x) := x in
       let (F3,  x) := x in
       let (isp, eqt)  := x in
       spertype ts T T' eq R1 R2 eq1
                c1
                c2
                F1
                (fun x y =>
                   rec ts
                       (mkc_apply2 R1 x y)
                       (mkc_apply2 R2 x y)
                       (eq1 x y)
                       (F1 x y))
                F2
                (fun x y z inh =>
                   rec ts
                       (mkc_apply2 R1 x y)
                       (mkc_apply2 R1 z y)
                       (eq1 x y)
                       (F2 x y z inh))
                F3
                (fun x y z inh =>
                   rec ts
                       (mkc_apply2 R1 x y)
                       (mkc_apply2 R1 x z)
                       (eq1 x y)
                       (F3 x y z inh))
                isp
                eqt
                pts
   | CL_w pts =>
       let (eqa, x) := pts in
       let (eqb, x) := x in
       let (tf, teq) := x in
       let (A,   x) := tf in
       let (A',  x) := x in
       let (v,   x) := x in
       let (v',  x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, tsb) := x in
         w ts T T' eq A A' v v' B B' eqa eqb
               c1
               c2
               tsa
               (rec ts A A' eqa tsa)
               tsb
               (fun a a' eqa =>
                  rec ts
                      (substc a v B)
                      (substc a' v' B')
                      (eqb a a' eqa)
                      (tsb a a' eqa))
               teq
               pts
   | CL_m pts =>
       let (eqa, x) := pts in
       let (eqb, x) := x in
       let (tf, teq) := x in
       let (A,   x) := tf in
       let (A',  x) := x in
       let (v,   x) := x in
       let (v',  x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, tsb) := x in
         m ts T T' eq A A' v v' B B' eqa eqb
               c1
               c2
               tsa
               (rec ts A A' eqa tsa)
               tsb
               (fun a a' eqa =>
                  rec ts
                      (substc a v B)
                      (substc a' v' B')
                      (eqb a a' eqa)
                      (tsb a a' eqa))
               teq
               pts
   | CL_pw pts =>
       let (eqp, x) := pts in
       let (eqa, x) := x in
       let (eqb, x) := x in
       let (p,   x) := x in
       let (p',  x) := x in
       let (cp,  x) := x in
       let (cp', x) := x in
       let (ca,  x) := x in
       let (ca', x) := x in
       let (cb,  x) := x in
       let (cb', x) := x in
       let (C,   x) := x in
       let (C',  x) := x in
       let (tf, teq) := x in
       let (Pr,  x) := tf in
       let (Pr', x) := x in
       let (ap,  x) := x in
       let (ap', x) := x in
       let (A,   x) := x in
       let (A',  x) := x in
       let (bp,  x) := x in
       let (bp', x) := x in
       let (ba,  x) := x in
       let (ba', x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsp, x) := x in
       let (tsa, x) := x in
       let (tsb, x) := x in
       let (tsc, peq) := x in
         pw ts T T' eq
            Pr Pr'
            ap ap' A A'
            bp bp' ba ba' B B'
            cp cp' ca ca' cb cb' C C'
            p p'
            eqp eqa eqb
            c1 c2
            tsp
            (rec ts Pr Pr' eqp tsp)
            tsa
            (fun p p' eqp =>
               rec ts
                   (substc p ap A)
                   (substc p' ap' A')
                   (eqa p p' eqp)
                   (tsa p p' eqp))
            tsb
            (fun p p' eqp a a' eqa =>
               rec ts
                   (lsubstc2 bp p ba a B)
                   (lsubstc2 bp' p' ba' a' B')
                   (eqb p p' eqp a a' eqa)
                   (tsb p p' eqp a a' eqa))
            tsc
            peq
            teq
            pts
   | CL_pm pts =>
       let (eqp, x) := pts in
       let (eqa, x) := x in
       let (eqb, x) := x in
       let (p,   x) := x in
       let (p',  x) := x in
       let (cp,  x) := x in
       let (cp', x) := x in
       let (ca,  x) := x in
       let (ca', x) := x in
       let (cb,  x) := x in
       let (cb', x) := x in
       let (C,   x) := x in
       let (C',  x) := x in
       let (tf, teq) := x in
       let (Pr,  x) := tf in
       let (Pr', x) := x in
       let (ap,  x) := x in
       let (ap', x) := x in
       let (A,   x) := x in
       let (A',  x) := x in
       let (bp,  x) := x in
       let (bp', x) := x in
       let (ba,  x) := x in
       let (ba', x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsp, x) := x in
       let (tsa, x) := x in
       let (tsb, x) := x in
       let (tsc, peq) := x in
         pm ts T T' eq
            Pr Pr'
            ap ap' A A'
            bp bp' ba ba' B B'
            cp cp' ca ca' cb cb' C C'
            p p'
            eqp eqa eqb
            c1 c2
            tsp
            (rec ts Pr Pr' eqp tsp)
            tsa
            (fun p p' eqp =>
               rec ts
                   (substc p ap A)
                   (substc p' ap' A')
                   (eqa p p' eqp)
                   (tsa p p' eqp))
            tsb
            (fun p p' eqp a a' eqa =>
               rec ts
                   (lsubstc2 bp p ba a B)
                   (lsubstc2 bp' p' ba' a' B')
                   (eqb p p' eqp a a' eqa)
                   (tsb p p' eqp a a' eqa))
            tsc
            peq
            teq
            pts
   | CL_texc pts =>
       let (eqn, x) := pts in
       let (eqe, x) := x in
       let (N,   x) := x in
       let (N',  x) := x in
       let (E,   x) := x in
       let (E',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsn, x) := x in
       let (tse, eqiff) := x in
         texc ts T T' eq N N' E E' eqn eqe
              c1
              c2
              tsn
              (rec ts N N' eqn tsn)
              tse
              (rec ts E E' eqe tse)
              eqiff
              pts
   | CL_union pts =>
       let (eqa, x) := pts in
       let (eqb, x) := x in
       let (A,   x) := x in
       let (A',  x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, x) := x in
       let (tsb, eqiff) := x in
         union ts T T' eq A A' B B' eqa eqb
               c1
               c2
               tsa
               (rec ts A A' eqa tsa)
               tsb
               (rec ts B B' eqb tsb)
               eqiff
               pts
(*   | CL_eunion pts =>
       let (eqa1, x) := pts in
       let (eqa2, x) := x in
       let (eqb1, x) := x in
       let (eqb2, x) := x in
       let (A,    x) := x in
       let (A',   x) := x in
       let (B,    x) := x in
       let (B',   x) := x in
       let (c1,   x) := x in
       let (c2,   x) := x in
       let (iffa, x) := x in
       let (iffb, x) := x in
       let (tsa1, x) := x in
       let (tsa2, x) := x in
       let (tsb1, x) := x in
       let (tsb2, eqiff) := x in
         eunion ts T T' eq A A' B B' eqa1 eqa2 eqb1 eqb2
                c1
                c2
                iffa
                iffb
                tsa1
                (rec ts A A eqa1 tsa1)
                tsa2
                (rec ts A' A' eqa2 tsa2)
                tsb1
                (rec ts B B eqb1 tsb1)
                tsb2
                (rec ts B' B' eqb2 tsb2)
                eqiff
                pts*)
   | CL_image pts =>
       let (eqa, x) := pts in
       let (A,   x) := x in
       let (A',  x) := x in
       let (f,   x) := x in
       let (f',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, x) := x in
       let (ceq, eqiff) := x in
         image ts T T' eq A A' f f' eqa
               c1
               c2
               tsa
               (rec ts A A' eqa tsa)
               ceq
               eqiff
               pts
(*   | CL_eisect pts =>
       let (eqa,  x)   := pts in
       let (eqa', x)   := x in
       let (eqb,  x)   := x in
       let (tf,   teq) := x in
       let (A,    x)   := tf in
       let (A',   x)   := x in
       let (v,    x)   := x in
       let (v',   x)   := x in
       let (B,    x)   := x in
       let (B',   x)   := x in
       let (f,    x)   := x in
       let (g,    x)   := x in
       let (f',   x)   := x in
       let (g',   x)   := x in
       let (ctv1, x)   := x in
       let (ctv2, x)   := x in
       let (tsa,  x)   := x in
       let (tsa', x)   := x in
       let (ftsb, ftsb') := x in
         eisect ts T T' eq eqa eqa' eqb A A' v v' B B'
                f g f' g'
                ctv1
                ctv2
                tsa
                (rec ts A A eqa tsa)
                tsa'
                (rec ts A' A' eqa' tsa')
                ftsb
                (fun a e =>
                   (rec ts
                        (substc a v B)
                        (substc (f a e) v' B')
                        (eqb a (f a e) e (g a e))
                        (ftsb a e)))
                ftsb'
                (fun a' e' =>
                   (rec ts
                        (substc (f' a' e') v B)
                        (substc a' v' B')
                        (eqb (f' a' e') a' (g' a' e') e')
                        (ftsb' a' e')))
                teq
                pts*)
   | CL_partial pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (eqa, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, x) := x in
       let (hv,  eqt) := x in
         partial ts T T' eq A1 A2 eqa
               c1
               c2
               cla
               (rec ts A1 A2 eqa cla)
               hv
               eqt
               pts
   | CL_admiss pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (eqa, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, eqt) := x in
         admiss ts T T' eq A1 A2 eqa
               c1
               c2
               cla
               (rec ts A1 A2 eqa cla)
               eqt
               pts
   | CL_mono pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (eqa, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, eqt) := x in
         mono ts T T' eq A1 A2 eqa
               c1
               c2
               cla
               (rec ts A1 A2 eqa cla)
               eqt
               pts
   | CL_ffatom pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (x1,  x) := x in
       let (x2,  x) := x in
       let (a1,  x) := x in
       let (a2,  x) := x in
       let (eqa, x) := x in
       let (u,   x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, x) := x in
       let (ex,  x) := x in
       let (ca1, x) := x in
       let (ca2, eqt) := x in
         ffatom ts T T' eq A1 A2 x1 x2 a1 a2 eqa u
                c1
                c2
                cla
                (rec ts A1 A2 eqa cla)
                ex ca1 ca2
                eqt
                pts
   | CL_effatom pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (x1,  x) := x in
       let (x2,  x) := x in
       let (a1,  x) := x in
       let (a2,  x) := x in
       let (eqa, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, x) := x in
       let (ni,  eqt) := x in
         effatom ts T T' eq A1 A2 x1 x2 a1 a2 eqa
                 c1
                 c2
                 cla
                 (rec ts A1 A2 eqa cla)
                 ni
                 eqt
                 pts
   | CL_ffatoms pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (x1,  x) := x in
       let (x2,  x) := x in
       let (eqa, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, x) := x in
       let (ex,  eqt) := x in
         ffatoms ts T T' eq A1 A2 x1 x2 eqa
                c1
                c2
                cla
                (rec ts A1 A2 eqa cla)
                ex
                eqt
                pts
   | CL_set pts =>
       let (eqa, x) := pts in
       let (eqb, x) := x in
       let (tf, teq) := x in
       let (A,   x) := tf in
       let (A',  x) := x in
       let (v,   x) := x in
       let (v',  x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, tsb) := x in
         subset ts T T' eq A A' v v' B B' eqa eqb
                c1
                c2
                tsa
                (rec ts A A' eqa tsa)
                tsb
                (fun a a' eqa =>
                   rec ts
                       (substc a v B)
                       (substc a' v' B')
                       (eqb a a' eqa)
                       (tsb a a' eqa))
                teq
                pts
   | CL_tunion pts =>
       let (eqa, x) := pts in
       let (eqb, x) := x in
       let (tf, teq) := x in
       let (A,   x) := tf in
       let (A',  x) := x in
       let (v,   x) := x in
       let (v',  x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, tsb) := x in
         tunion ts T T' eq A A' v v' B B' eqa eqb
                c1
                c2
                tsa
                (rec ts A A' eqa tsa)
                tsb
                (fun a a' eqa =>
                   rec ts
                       (substc a v B)
                       (substc a' v' B')
                       (eqb a a' eqa)
                       (tsb a a' eqa))
                teq
                pts
   | CL_product pts =>
       let (eqa, x) := pts in
       let (eqb, x) := x in
       let (tf, teq) := x in
       let (A,   x) := tf in
       let (A',  x) := x in
       let (v,   x) := x in
       let (v',  x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, tsb) := x in
         product ts T T' eq A A' v v' B B' eqa eqb
               c1
               c2
               tsa
               (rec ts A A' eqa tsa)
               tsb
               (fun a a' eqa =>
                  rec ts
                      (substc a v B)
                      (substc a' v' B')
                      (eqb a a' eqa)
                      (tsb a a' eqa))
               teq
               pts
(*   | CL_esquash pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (eq1, x) := x in
       let (eq2, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (E1,  x) := x in
       let (E2,  x) := x in
       let (inh, eqt) := x in
         esquash ts T T' eq A1 A2 eq1 eq2
               c1
               c2
               E1
               (rec ts A1 A1 eq1 E1)
               E2
               (rec ts A2 A2 eq2 E2)
               inh
               eqt
               pts*)
   end.

Ltac dest_per_fam h eqa eqb A A' v v' B B' c1 c2 tsa tsb eqt :=
  (unfold per_func in h
          || unfold per_product in h
          || unfold per_set     in h
          || unfold per_tunion  in h
          || unfold per_isect   in h
          || unfold per_disect  in h
          || unfold per_eisect  in h
          || unfold per_w       in h
          || unfold per_m       in h
          || unfold per_pw      in h
          || unfold per_pm      in h);
  (unfold type_family in h
          || unfold type_pfamily in h
          || unfold etype_family in h);
  destruct h as [eqa h];
  destruct h as [eqb h];
  destruct h as [h eqt];
  destruct h as [A h];
  destruct h as [A' h];
  destruct h as [v h];
  destruct h as [v' h];
  destruct h as [B h];
  destruct h as [B' h];
  destruct h as [c1 h];
  destruct h as [c2 h];
  destruct h as [tsa tsb].

Ltac one_dest_per_fam eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt :=
  match goal with
    | [ H : _ |- _ ] => dest_per_fam H eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt
  end.

Ltac one_unfold_per :=
  match goal with
    | [ H : per_int      _ _ _ _ _ |- _ ] => unfold per_int      in H; exrepd
    | [ H : per_atom     _ _ _ _ _ |- _ ] => unfold per_atom     in H; exrepd
    | [ H : per_uatom    _ _ _ _ _ |- _ ] => unfold per_uatom    in H; exrepd
    | [ H : per_base     _ _ _ _ _ |- _ ] => unfold per_base     in H; exrepd
    | [ H : per_approx   _ _ _ _ _ |- _ ] => unfold per_approx   in H; exrepd
    | [ H : per_cequiv   _ _ _ _ _ |- _ ] => unfold per_cequiv   in H; exrepd
    | [ H : per_eq       _ _ _ _ _ |- _ ] => unfold per_eq       in H; exrepd
    | [ H : per_req      _ _ _ _ _ |- _ ] => unfold per_req      in H; exrepd
    | [ H : per_teq      _ _ _ _ _ |- _ ] => unfold per_teq      in H; exrepd
    | [ H : per_isect    _ _ _ _ _ |- _ ] => unfold per_isect    in H; exrepd
    | [ H : per_func     _ _ _ _ _ |- _ ] => unfold per_func     in H; exrepd
    | [ H : per_disect   _ _ _ _ _ |- _ ] => unfold per_disect   in H; exrepd
    | [ H : per_pertype  _ _ _ _ _ |- _ ] => unfold per_pertype  in H; exrepd
    | [ H : per_ipertype _ _ _ _ _ |- _ ] => unfold per_ipertype in H; exrepd
    | [ H : per_spertype _ _ _ _ _ |- _ ] => unfold per_spertype in H; exrepd
    | [ H : per_w        _ _ _ _ _ |- _ ] => unfold per_w        in H; exrepd
    | [ H : per_m        _ _ _ _ _ |- _ ] => unfold per_m        in H; exrepd
    | [ H : per_pw       _ _ _ _ _ |- _ ] => unfold per_pw       in H; exrepd
    | [ H : per_pm       _ _ _ _ _ |- _ ] => unfold per_pm       in H; exrepd
    | [ H : per_texc     _ _ _ _ _ |- _ ] => unfold per_texc     in H; exrepd
    | [ H : per_union    _ _ _ _ _ |- _ ] => unfold per_union    in H; exrepd
(*    | [ H : per_eunion   _ _ _ _ _ |- _ ] => unfold per_eunion   in H; exrepd
    | [ H : per_union2   _ _ _ _ _ |- _ ] => unfold per_union2   in H; exrepd*)
    | [ H : per_image    _ _ _ _ _ |- _ ] => unfold per_image    in H; exrepd
    | [ H : per_eisect   _ _ _ _ _ |- _ ] => unfold per_eisect   in H; exrepd
    | [ H : per_partial  _ _ _ _ _ |- _ ] => unfold per_partial  in H; exrepd
    | [ H : per_admiss   _ _ _ _ _ |- _ ] => unfold per_admiss   in H; exrepd
    | [ H : per_mono     _ _ _ _ _ |- _ ] => unfold per_mono     in H; exrepd
    | [ H : per_ffatom   _ _ _ _ _ |- _ ] => unfold per_ffatom   in H; exrepd
    | [ H : per_effatom  _ _ _ _ _ |- _ ] => unfold per_effatom  in H; exrepd
    | [ H : per_ffatoms  _ _ _ _ _ |- _ ] => unfold per_ffatoms  in H; exrepd
    | [ H : per_set      _ _ _ _ _ |- _ ] => unfold per_set      in H; exrepd
    | [ H : per_tunion   _ _ _ _ _ |- _ ] => unfold per_tunion   in H; exrepd
    | [ H : per_product  _ _ _ _ _ |- _ ] => unfold per_product  in H; exrepd
(*    | [ H : per_esquash  _ _ _ _ _ |- _ ] => unfold per_esquash  in H; exrepd*)
    | [ H : type_family  _ _ _ _ _ _ _ |- _ ] => unfold type_family in H; exrepd
    | [ H : etype_family _ _ _ _ _ _ _ _ |- _ ] => unfold etype_family in H; exrepd
    | [ H : type_pfamily _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => unfold type_pfamily in H; exrepd
  end.

Ltac allunfold_per := repeat one_unfold_per.

Ltac computes_to_valc_diff :=
  match goal with
    | [ H1 : computes_to_valc ?lib ?T ?T1,
        H2 : computes_to_valc ?lib ?T ?T2
                               |- _ ] =>
        let name := fresh "eq" in
          (assert (T1 = T2) as name
                  by (apply (computes_to_valc_eq lib T); auto);
           dest_cterms name;
           inversion name;
           fail)
  end.

(* end hide *)
