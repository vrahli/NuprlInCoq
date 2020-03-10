(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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
Require Export bar.
Require Export ebar.
Require Export nat_type.
Require Export csname_type.
Require Export raise_bar.


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

Notation cts := (library -> CTerm -> CTerm -> per -> [U]).
Notation "cts( p )" := (@library p -> @CTerm p -> @CTerm p -> per(p) -> [U]).

(* begin hide *)

Definition ccomputes_to_valc_ext {o} (lib : @library o) (a b : @CTerm o) :=
  in_ext lib (fun lib => exists c, ccomputes_to_valc lib a c /\ ciscvalue b /\ ccequivc lib b c).

Definition ccomputes_to_excc_ext {o} (lib : @library o) (e a b : @CTerm o) :=
  in_ext lib (fun lib => ccomputes_to_excc lib e a b).

Notation "a ~<~ b" := (capproxc a b) (at level 0).
Notation "a ~<~( lib ) b" := (capproxc lib a b) (at level 0).
Notation "a ~=~ b" := (ccequivc a b) (at level 0).
Notation "a ~=~( lib ) b" := (ccequivc lib a b) (at level 0).
(*Notation "a ===> b" := (ccomputes_to_valc a b) (at level 0).*)
Notation "a ===>( lib ) b" := (ccomputes_to_valc_ext lib a b) (at level 0).
Notation "a ===e>( lib , e ) b" := (ccomputes_to_excc_ext lib e a b) (at level 0).
Notation "T [[ v \\ a ]]" := (substc a v T) (at level 0).

Lemma ccomputes_to_valc_ext_monotone {o} :
  forall lib lib' (a b : @CTerm o),
    lib_extends lib' lib
    -> a ===>(lib) b
    -> a ===>(lib') b.
Proof.
  introv ext comp xt.
  eapply comp; eauto 3 with slow.
Qed.
Hint Resolve ccomputes_to_valc_ext_monotone : slow.

(* end hide *)


(* begin hide *)

Definition ccequivc_ext {o} (lib : @library o) (t t' : @CTerm o) :=
  in_ext lib (fun lib => t ~=~(lib) t').



Notation "ext-per( lib , o )" :=
  (forall (lib' : @library o), lib_extends lib' lib -> per(o)).

Definition ext_per_preserves_lib_extends {o} {lib} (eqa : ext-per(lib,o)) :=
  in_ext_ext
    lib
    (fun lib' x =>
       forall (y : lib_extends lib' lib),
         (eqa lib' x) <=2=> (eqa lib' y)).

Record lib_per {o} (lib : @library o) :=
  MkLibPer
    {
      lib_per_per  :> ext-per(lib,o);
      lib_per_cond : ext_per_preserves_lib_extends lib_per_per;
    }.

Notation "lib-per( lib , o )" := (@lib_per o lib).


Notation "ext-per-fam ( lib , eqa )" :=
  (forall lib' (ext : lib_extends lib' lib) a a' (p : eqa lib' ext a a'), per) (at level 0).

Notation "ext-per-fam ( lib , eqa , o )" :=
  (forall (lib' : @library o) (ext : @lib_extends o lib' lib) a a' (p : eqa lib' ext a a'), per(o)) (at level 0).

Definition ext_per_fam_preserves_lib_extends
           {o} {lib} {eqa : ext-per(lib,o)}
           (eqb : ext-per-fam(lib,eqa,o)) :=
  in_ext_ext
    lib
    (fun lib' x =>
       forall (y : lib_extends lib' lib)
              (a b : CTerm)
              (p : eqa lib' x a b)
              (q : eqa lib' y a b),
         (eqb lib' x a b p) <=2=> (eqb lib' y a b q)).

Record lib_per_fam {o} {lib : @library o} (eqa : lib-per(lib,o)) :=
  MkLibPerFam
    {
      lib_per_fam_per  :> ext-per-fam(lib,eqa,o);
      lib_per_fam_cond : ext_per_fam_preserves_lib_extends lib_per_fam_per;
    }.

Notation "lib-per-fam ( lib , eqa )" := (lib_per_fam eqa).

Notation "lib-per-fam ( lib , eqa , o )" := (@lib_per_fam o lib eqa).

Definition sub_per {o} (per1 per2 : per(o)) :=
  forall a b, per1 a b -> per2 a b.

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






Definition equality_of_int_bar {o} lib (t t' : @CTerm o) :=
  in_open_bar lib (fun lib => equality_of_int lib t t').

Definition per_int {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  T1 ===>(lib) mkc_int
  # T2 ===>(lib) mkc_int
  # eq <=2=> (equality_of_int_bar lib).

Definition per_int_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  in_open_bar lib (fun lib => T1 ===>(lib) mkc_int)
  # in_open_bar lib (fun lib => T2 ===>(lib) mkc_int)
  # eq <=2=> (equality_of_int_bar lib).



Definition equality_of_nat {o} lib (t t' : @CTerm o) :=
  {n : nat
  , t ===>(lib) (mkc_nat n)
  # t' ===>(lib) (mkc_nat n)}.

(* This is just for testing, we've also defined nat using int and the set type *)
Definition equality_of_nat_bar {o} lib (t t' : @CTerm o) :=
  in_open_bar lib (fun lib => equality_of_nat lib t t').

Definition per_nat {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  T1 ===>(lib) mkc_Nat
  # T2 ===>(lib) mkc_Nat
  # eq <=2=> (equality_of_nat_bar lib).

Definition per_nat_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  in_open_bar lib (fun lib => T1 ===>(lib) mkc_Nat)
  # in_open_bar lib (fun lib => T2 ===>(lib) mkc_Nat)
  # eq <=2=> (equality_of_nat_bar lib).




Definition equality_of_qnat {o} lib (t t' : @CTerm o) :=
  {n : nat , ccomputes_to_valc lib t (mkc_nat n)}
  # {n : nat , ccomputes_to_valc lib t' (mkc_nat n)}.

Definition equality_of_qnat_bar {o} lib (t t' : @CTerm o) :=
  in_open_bar lib (fun lib => equality_of_qnat lib t t').

Definition per_qnat {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  T1 ===>(lib) mkc_qnat
  # T2 ===>(lib) mkc_qnat
  # eq <=2=> (equality_of_qnat_bar lib).

Definition per_qnat_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  in_open_bar lib (fun lib => T1 ===>(lib) mkc_qnat)
  # in_open_bar lib (fun lib => T2 ===>(lib) mkc_qnat)
  # eq <=2=> (equality_of_qnat_bar lib).



(* When using [ccequivc], we cannot prove that [per_qtime_eq_bar] is transitive *)
Definition per_qtime_eq {p} (lib : library) (eqa : per) (t t' : @CTerm p) : [U] :=
  {x, y : CTerm
  , ccequivc lib t x
  # ccequivc lib t' y
  # ccequivc_ext lib t t'
  # eqa x y}.

Definition per_qtime_eq_bar {o}
           (lib  : library)
           (eqa  : lib-per(lib,o))
           (t t' : @CTerm o) : [U] :=
  in_open_bar_ext lib (fun lib' x => per_qtime_eq lib' (eqa lib' x) t t').

Definition per_qtime {o}
           (ts : cts)
           lib
           (T1 T2 : @CTerm o)
           (eq : per(o)) : [U] :=
  {eqa : lib-per(lib,o)
   , {A, B : CTerm
   , T1 ===>(lib) (mkc_qtime A)
   # T2 ===>(lib) (mkc_qtime B)
   # in_ext_ext lib (fun lib' x => ts lib' A B (eqa lib' x))
   # eq <=2=> (per_qtime_eq_bar lib eqa)}}.



Definition compatible_cs_kind (n : nat) (k : cs_kind) :=
  if deq_nat n 0 then
    match k with
    | cs_kind_nat m => m = 0
    | cs_kind_seq _ => False
                         (* ******* *)
                         (* I've disabled that for now because it gets complicated in LS3 *)
                         (* True *)
    end
  else if deq_nat n 1 then
         match k with
         | cs_kind_nat m => m = 1
         | cs_kind_seq _ => False
         end
       else True.

Definition compatible_choice_sequence_name (n : nat) (name : choice_sequence_name) :=
  compatible_cs_kind n (csn_kind name).

Definition equality_of_csname {o} lib n (t t' : @CTerm o) :=
  {name : choice_sequence_name
  , compatible_choice_sequence_name n name
  # t ===>(lib) (mkc_choice_seq name)
  # t' ===>(lib) (mkc_choice_seq name)}.

Definition equality_of_csname_bar {o} lib n (t t' : @CTerm o) :=
  in_open_bar lib (fun lib => equality_of_csname lib n t t').

Definition per_csname {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  {n : nat
  , T1 ===>(lib) (mkc_csname n)
  # T2 ===>(lib) (mkc_csname n)
  # eq <=2=> (equality_of_csname_bar lib n) }.

Definition per_csname_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  {n : nat
  , in_open_bar lib (fun lib => T1 ===>(lib) (mkc_csname n))
  # in_open_bar lib (fun lib => T2 ===>(lib) (mkc_csname n))
  # eq <=2=> (equality_of_csname_bar lib n) }.


(**

  Nuprl has two kinds of atom types.  One that is similar to strings
  and one that is similar to ur-elements.

*)

Definition equality_of_atom {p} lib (a b : @CTerm p) :=
  {s : String.string , a ===>(lib) (mkc_token s)
                     # b ===>(lib) (mkc_token s)}.

Definition equality_of_atom_bar {o} lib (t t' : @CTerm o) :=
  in_open_bar lib (fun lib => equality_of_atom lib t t').

Definition per_atom {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  T1 ===>(lib) mkc_atom
  # T2 ===>(lib) mkc_atom
  # eq <=2=> (equality_of_atom_bar lib).

Definition per_atom_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  in_open_bar lib (fun lib => T1 ===>(lib) mkc_atom)
  # in_open_bar lib (fun lib => T2 ===>(lib) mkc_atom)
  # eq <=2=> (equality_of_atom_bar lib).



Definition equality_of_uatom {p} lib (a b : @CTerm p) :=
  {u : get_patom_set p , a ===>(lib) (mkc_utoken u)
                       # b ===>(lib) (mkc_utoken u)}.

Definition equality_of_uatom_bar {o} lib (t t' : @CTerm o) :=
  in_open_bar lib (fun lib => equality_of_uatom lib t t').

Definition per_uatom {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  T1 ===>(lib) mkc_uatom
  # T2 ===>(lib) mkc_uatom
  # eq <=2=> (equality_of_uatom_bar lib).

Definition per_uatom_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  in_open_bar lib (fun lib => T1 ===>(lib) mkc_uatom)
  # in_open_bar lib (fun lib => T2 ===>(lib) mkc_uatom)
  # eq <=2=> (equality_of_uatom_bar lib).


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

Definition per_ffatom {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
   {A1 , A2 , x1 , x2 , a1 , a2 : CTerm
   , {eqa : per
   , {u : get_patom_set p
      , T1 ===>(lib) (mkc_free_from_atom A1 x1 a1)
      # T2 ===>(lib) (mkc_free_from_atom A2 x2 a2)
      # ts lib A1 A2 eqa
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

Definition per_effatom {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
   {A1 , A2 , x1 , x2 , a1 , a2 : CTerm
   , {eqa : per
      , T1 ===>(lib) (mkc_efree_from_atom A1 x1 a1)
      # T2 ===>(lib) (mkc_efree_from_atom A2 x2 a2)
      # ts lib A1 A2 eqa
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

Definition per_ffatoms {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
   {A1 , A2 , x1 , x2 : CTerm
   , {eqa : per
      , T1 ===>(lib) (mkc_free_from_atoms A1 x1)
      # T2 ===>(lib) (mkc_free_from_atoms A2 x2)
      # ts lib A1 A2 eqa
      # eqa x1 x2
      # eq <=2=> (per_ffatoms_eq lib eqa x1)}}.





(* ****** free from definition type ****** *)

Inductive def_kind :=
| defk_abs (a : opabs)
| defk_cs  (c : choice_sequence_name).

Definition def_kinds := list def_kind.

Definition get_defs_c {p} (c : @CanonicalOp p) : def_kinds :=
  match c with
  | Ncseq c => [defk_cs c]
  | _ => []
  end.

Definition get_defs_nfo (nfo : SwapCsNfo) : def_kinds :=
  match nfo with
  | MkSwapCsNfo n1 n2 => [defk_cs n1, defk_cs n2]
  end.

Definition get_defs_n (n : NonCanonicalOp) : def_kinds :=
  match n with
  | NSwapCs2 nfo => get_defs_nfo nfo
  | _ => []
  end.

Definition get_defs_o {p} (o : @Opid p) : def_kinds :=
  match o with
  | Can c => get_defs_c c
  | NCan n => get_defs_n n
  | Abs a => [defk_abs a]
  | _ => []
  end.

Fixpoint get_defs {p} (t : @NTerm p) : def_kinds :=
  match t with
  | vterm _ => []
  | oterm o bterms => (get_defs_o o) ++ (flat_map get_defs_b bterms)
  end
with get_defs_b {p} (bt : @BTerm p) : def_kinds :=
       match bt with
       | bterm _ t => get_defs t
       end.

Definition nodefs {o} (t : @NTerm o) := get_defs t = [].

Definition nodefsc {o} (t : @CTerm o) := nodefs (get_cterm t).

Definition ex_nodefsc {o} (eqa : per(o)) (t : @CTerm o) :=
  {u : @CTerm o , eqa t u # nodefsc u}.

Definition per_ffdefs_eq {p}
           lib
           (eqa : per(p))
           (t t1 t2 : @CTerm p) :=
  t1 ===>(lib) mkc_axiom
  # t2 ===>(lib) mkc_axiom
  # ex_nodefsc eqa t.

Definition per_ffdefs_eq_bar {p}
           lib
           (eqa : lib-per(lib,p))
           (t t1 t2 : @CTerm p) :=
  in_open_bar_ext lib (fun lib' x => per_ffdefs_eq lib' (eqa lib' x) t t1 t2).

Definition per_ffdefs {o} (ts : cts(o)) lib (T1 T2 : @CTerm o) (eq : per(o)) : [U] :=
   {A1 , A2, x1 , x2 : CTerm
   , {eqa : lib-per(lib,o)
   , T1 ===>(lib) (mkc_free_from_defs A1 x1)
   # T2 ===>(lib) (mkc_free_from_defs A2 x2)
   # in_ext_ext lib (fun lib' x => ts lib' A1 A2 (eqa lib' x))
   # in_ext_ext lib (fun lib' x => eqa lib' x x1 x2)
   # eq <=2=> (per_ffdefs_eq_bar lib eqa x1) }}.

(* ****** ****** *)


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

Definition per_base_eq {o} lib (t t' : @CTerm o) :=
  in_open_bar lib (fun lib => t ~=~(lib) t').

Definition per_base {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  T1 ===>(lib) mkc_base
  # T2 ===>(lib) mkc_base
  # eq <=2=> (per_base_eq lib).

Definition per_base_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  in_open_bar lib (fun lib => T1 ===>(lib) mkc_base)
  # in_open_bar lib (fun lib => T2 ===>(lib) mkc_base)
  # eq <=2=> (per_base_eq lib).

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

(*Definition computes_to_valc_ceq_bar {o} {lib} (bar : @BarLib o lib) (t1 t2 : @CTerm o) :=
  e_all_in_bar bar (fun lib => {t : CTerm , t1 ===>(lib) t # ccequivc (*ccequivc_ext*) lib t t2}).
Notation "t1 ==b==>( bar ) t2" := (computes_to_valc_ceq_bar bar t1 t2) (at level 0).*)

Definition computes_to_valc_ceq_open {o} (lib : @library o) (t1 t2 : @CTerm o) :=
  in_open_bar lib (fun lib => {t : CTerm , t1 ===>(lib) t # ccequivc (*ccequivc_ext*) lib t t2}).
Notation "t1 ==o==>( lib ) t2" := (computes_to_valc_ceq_open lib t1 t2) (at level 0).

(*Definition computes_to_valc_bar {o} {lib} (bar : @BarLib o lib) (a b : @CTerm o) :=
  e_all_in_bar bar (fun lib => a ===>(lib) b).
Notation "a =b==>( bar ) b" := (computes_to_valc_bar bar a b) (at level 0).
(*Notation "a ==e==>( , lib ) b" := (computes_to_valc_ext lib a b) (at level 0).*)
*)


Definition per_approx_eq {o} lib a b (t t' : @CTerm o) :=
  t ===>(lib) mkc_axiom
  # t' ===>(lib) mkc_axiom
  # a ~<~(lib) b.

Definition per_approx_eq_bar {o} lib a b (t t' : @CTerm o) :=
  in_open_bar lib (fun lib => per_approx_eq lib a b t t').

Definition per_approx {p}
           (ts : cts(p))
           (lib : library)
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {a, b, c, d : CTerm
   , T1 ===>(lib) (mkc_approx a b)
   # T2 ===>(lib) (mkc_approx c d)
   # in_ext lib (fun lib => a ~<~(lib) b <=> c ~<~(lib) d)
   # eq <=2=> (per_approx_eq_bar lib a b) }.

Definition per_approx_bar {p}
           (ts    : cts(p))
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per(p)) : [U] :=
 {a, b, c, d : CTerm
  , T1 ==o==>(lib) (mkc_approx a b)
  # T2 ==o==>(lib) (mkc_approx c d)
  # in_open_bar lib (fun lib => (a ~<~(lib) b <=> c ~<~(lib) d))
  # eq <=2=> (per_approx_eq_bar lib a b) }.


(**

  The computational equivalence type was also recently added to Nuprl,
  as a way to reason in the type theory about the computational
  equivalence meta-relation introduced by Howe%~\cite{Howe:1989}%.  It
  is defined as follows: The two types have to compute to closed
  canonical forms of the form [mkc_cequiv a b] and [mkc_cequiv c d]
  where [a ~=~ b] iff [c ~=~ d], and two terms are equal in that type
  if they both compute to [mkc_axiom] and [a ~=~ b] is true.

*)

Definition per_cequiv_eq {o} lib a b (t t' : @CTerm o) :=
  t ===>(lib) mkc_axiom
  # t' ===>(lib) mkc_axiom
  # a ~=~(lib) b.

Definition per_cequiv_eq_bar {o} lib a b (t t' : @CTerm o) :=
  in_open_bar lib (fun lib => per_cequiv_eq lib a b t t').

Definition per_cequiv {p}
           (ts : cts(p))
           lib
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {a, b, c, d : CTerm
   , T1 ===>(lib) (mkc_cequiv a b)
   # T2 ===>(lib) (mkc_cequiv c d)
   # in_ext lib (fun lib => a ~=~(lib) b <=> c ~=~(lib) d)
   # eq <=2=> (per_cequiv_eq_bar lib a b) }.

Definition per_cequiv_bar {p}
           (ts    : cts(p))
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per(p)) : [U] :=
 {a, b, c, d : CTerm
  , T1 ==o==>(lib) (mkc_cequiv a b)
  # T2 ==o==>(lib) (mkc_cequiv c d)
  # in_open_bar lib (fun lib => (a ~=~(lib) b <=> c ~=~(lib) d))
  # eq <=2=> (per_cequiv_eq_bar lib a b) }.



(* begin hide *)

Definition per_compute {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
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

(*Definition eqorceq {p} lib (eq : per(p)) a b : [U] := eq a b {+} a ~=~(lib) b.*)

Definition eqorceq {p} lib (eq : per(p)) a b : [U] :=
  eq a b {+} ccequivc_ext lib a b.

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

Definition eq_per_eq {o}
           (lib   : library)
           (a1 a2 : @CTerm o)
           (eqa   : per(o))
           (t t'  : @CTerm o) : [U] :=
  t ===>(lib) mkc_axiom
  /\ t' ===>(lib) mkc_axiom
  /\ eqa a1 a2.

Definition eq_per_eq_bar {o} lib a b (eqa : lib-per(lib,o)) (t t' : @CTerm o) :=
  in_open_bar_ext lib (fun lib' x => eq_per_eq lib' a b (eqa lib' x) t t').

Definition eqorceq_ext {o} lib (eqa : lib-per(lib,o)) a b :=
  in_ext_ext lib (fun lib' x => eqorceq lib' (eqa lib' x) a b).

Definition per_eq {o} (ts : cts(o)) lib T1 T2 (eq : per(o)) : [U] :=
  {A, B, a1, a2, b1, b2 : CTerm
   , {eqa : lib-per(lib,o)
      , T1 ===>(lib) (mkc_equality a1 a2 A)
      # T2 ===>(lib) (mkc_equality b1 b2 B)
      # in_ext_ext lib (fun lib' x => ts lib' A B (eqa lib' x))
      # eqorceq_ext lib eqa a1 b1
      # eqorceq_ext lib eqa a2 b2
      # eq <=2=> (eq_per_eq_bar lib a1 a2 eqa) }}.

Definition per_eq_bar {o} (ts : cts(o)) lib (T1 T2 : @CTerm o) (eq : per(o)) : [U] :=
  {A, B, a1, a2, b1, b2 : CTerm
  , {eqa : lib-per(lib,o)
  , T1 ==o==>(lib) (mkc_equality a1 a2 A)
  # T2 ==o==>(lib) (mkc_equality b1 b2 B)
  # in_open_bar_ext lib (fun lib' x => ts lib' A B (eqa lib' x))
  # in_open_bar_ext lib (fun lib' x => eqorceq lib' (eqa lib' x) a1 b1)
  # in_open_bar_ext lib (fun lib' x => eqorceq lib' (eqa lib' x) a2 b2)
  # eq <=2=> (eq_per_eq_bar lib a1 a2 eqa) }}.



Definition per_req_eq {o} lib (a1 a2 : @CTerm o) (eqa : per) (t t' : @CTerm o) :=
  { x1 , x2 : CTerm
  , (t ===>(lib) (mkc_refl x1))
  # (t' ===>(lib) (mkc_refl x2))
  # eqa a1 a2
  # eqa a1 x1
  # eqa a2 x2}.

Definition per_req {p} (ts : cts(p)) lib T1 T2 (eq : per(p)) : [U] :=
  {A, B, a1, a2, b1, b2 : CTerm
   , {eqa : per
   , T1 ===>(lib) (mkc_requality a1 a2 A)
   # T2 ===>(lib) (mkc_requality b1 b2 B)
   # ts lib A B eqa
   # eqorceq lib eqa a1 b1
   # eqorceq lib eqa a2 b2
   # eq <=2=> (per_req_eq lib a1 a2 eqa) }}.

(*Definition per_req_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  in_bar lib (fun lib' => per_req ts lib' T1 T2 eq).*)

(**

  [per_teq] is an experiment.  Can we have a type that represents
  equality between types ([tequality] defined later) as we have
  [mkc_equality] a type which allows one to reason about equalities of
  types.

 *)

Definition true_per {p} (t t' : @CTerm p) := True.

Definition per_teq {p} (ts : cts(p)) lib T1 T2 (eq : per(p)) : [U] :=
  {a1, a2, b1, b2 : CTerm
   , {eqa : per
      , T1 ===>(lib) (mkc_tequality a1 a2)
      # T2 ===>(lib) (mkc_tequality b1 b2)
      # ts lib a1 b1 eqa
      # ts lib a2 b2 eqa
      # ts lib a1 a2 eqa
      # eq <=2=> true_per}}.

(*Definition per_teq_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  in_bar lib (fun lib' => per_teq ts lib' T1 T2 eq).*)

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

Definition type_family {p} TyCon (ts : cts(p)) lib (T1 T2 : @CTerm p) eqa eqb : [U]:=
  {A, A' : CTerm , {v, v' : NVar , {B : CVTerm [v] , {B' : CVTerm [v'] ,
     T1 ===>(lib) (TyCon A v B)
     # T2 ===>(lib) (TyCon A' v' B')
     # ts lib A A' eqa
     # (forall a a', forall e : eqa a a',
          ts lib (B[[v\\a]]) (B'[[v'\\a']]) (eqb a a' e))}}}}.

(**

  Intersection types were introduced in Nuprl by Kopylov in
  2004%~\cite{Kopylov:2004}%.  An intersection type is a type family.
  Two terms [t] and [t'] are equal in an intersection type of the form
  $\NUPRLisect{x}{A}{\NUPRLsuba{B}{z}{x}}$ if for any two elements [a]
  and [a'] equal in $A$, [t] and [t'] are equal in
  $\NUPRLsuba{B}{z}{a}$.

 *)

Definition per_isect {p}
           (ts    : cts(p))
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per(p)) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family mkc_isect ts lib T1 T2 eqa eqb
      # (forall t t',
           eq t t'
              <=>
              (forall a a', forall e : eqa a a', eqb a a' e t t')) }}.

Definition per_isect_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  in_ext lib (fun lib' => per_isect ts lib' T1 T2 eq).

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
           (ts    : cts(p))
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per(p)) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family mkc_disect ts lib T1 T2 eqa eqb
      # (forall t t', eq t t' <=> {e : eqa t t' , eqb t t' e t t'}) }}.

Definition per_disect_bar {p} (ts : cts(p)) lib (T1 T2 : @CTerm p) (eq : per(p)) : [U] :=
  in_ext lib (fun lib' => per_disect ts lib' T1 T2 eq).

(**

  Function types are also type families.  Two terms [t] and [t'] are
  equal in a function type of the form
  $\NUPRLfunction{x}{A}{\NUPRLsuba{B}{z}{x}}$ if for all [a] and [a']
  equal in $A$, [(mkc_apply t a)] and [(mkc_apply t' a')] are equal in
  $\NUPRLsuba{B}{z}{a}$.  Therefore, members of function types do not
  have to be lambda terms.  For example, function types that have an
  empty domain are all inhabited by diverging terms.

 *)


Definition per_func_eq {o}
           (eqa  : per(o))
           (eqb  : per-fam(eqa))
           (t t' : @CTerm o) :=
  forall a a' (e : eqa a a'),
    (eqb a a' e) (mkc_apply t a) (mkc_apply t' a').

Definition per_func {p} (ts : cts(p)) lib T1 T2 (eq : per(p)) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family mkc_function ts lib T1 T2 eqa eqb
      # eq <=2=> (per_func_eq eqa eqb)}}.

Definition TyConType {o} :=
  @CTerm o -> forall v : NVar, @CVTerm o [v] -> @CTerm o.


Definition type_family_ext {o}
           (tycon : TyConType)
           (ts    : cts(o))
           (lib   : library)
           (T1 T2 : @CTerm o)
           (eqa   : lib-per(lib,o))
           (eqb   : lib-per-fam(lib,eqa)) : [U]:=
  {A, A' : CTerm
  , {v, v' : NVar
  , {B : CVTerm [v]
  , {B' : CVTerm [v']
  , T1 ===>(lib) (tycon A v B)
  # T2 ===>(lib) (tycon A' v' B')
  # in_ext_ext lib (fun lib' x => ts lib' A A' (eqa lib' x))
  # in_ext_ext
      lib
      (fun lib' x =>
         forall a a' (e : eqa lib' x a a'),
           ts lib' (B[[v\\a]]) (B'[[v'\\a']]) (eqb lib' x a a' e))
  }}}}.

Definition per_func_ext_eq {o}
           (lib  : library)
           (eqa  : lib-per(lib,o))
           (eqb  : lib-per-fam(lib,eqa))
           (t t' : @CTerm o) :=
  in_open_bar_ext lib (fun lib' x => per_func_eq (eqa lib' x) (eqb lib' x) t t').

Definition per_func_ext {o} (ts : cts(o)) lib T1 T2 (eq : per(o)) : [U] :=
  {eqa : lib-per(lib,o)
  , {eqb : lib-per-fam(lib,eqa)
  , type_family_ext mkc_function ts lib T1 T2 eqa eqb
  # eq <=2=> (per_func_ext_eq lib eqa eqb) }}.



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
      # eqb a a' e b b'}}.

Definition per_product {p}
           (ts : cts)
           lib
           (T1 T2 : @CTerm p)
           (eq : per) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
   , type_family mkc_product ts lib T1 T2 eqa eqb
   # eq <=2=> (per_product_eq lib eqa eqb)}}.

Definition per_product_eq_bar {o}
           (lib  : library)
           (eqa  : lib-per(lib,o))
           (eqb  : lib-per-fam(lib,eqa))
           (t t' : CTerm) : [U] :=
  in_open_bar_ext lib (fun lib' x => per_product_eq lib' (eqa lib' x) (eqb lib' x) t t').

(* I was using [type_family_bar] here before but then it doesn't make
   sense because the elements of the sum type could use a lower bar than
   then bar of the family in which case we don't know if the PERs that are
   supposed to be the ones of A and B are actually the ones of A and B...

   One thing we could do though is enforce that the bar of the equality is
   at least higher than the one of the family *)
Definition per_product_bar {o}
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm o)
           (eq    : per) : [U] :=
  {eqa : lib-per(lib,o)
  , {eqb : lib-per-fam(lib,eqa)
  , type_family_ext mkc_product ts lib T1 T2 eqa eqb
  # eq <=2=> (per_product_eq_bar lib eqa eqb) }}.



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
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family mkc_tunion ts lib T1 T2 eqa eqb
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
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per(p)) : [U] :=
  {eqn, eqe : per
   , {N1, N2, E1, E2 : CTerm
      , T1 ===>(lib) (mkc_texc N1 E1)
      # T2 ===>(lib) (mkc_texc N2 E2)
      # ts lib N1 N2 eqn
      # ts lib E1 E2 eqe
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

Definition per_union_eq_bar {o}
           (lib     : library)
           (eqa eqb : lib-per(lib,o))
           (t t'    : @CTerm o) : [U] :=
  in_open_bar_ext lib (fun lib' x => per_union_eq lib' (eqa lib' x) (eqb lib' x) t t').

Definition eq_per_union_bar {o}
           (lib     : library)
           (eqa eqb : per(o))
           (t t'    : @CTerm o) : [U] :=
  in_open_bar lib (fun lib' => per_union_eq lib' eqa eqb t t').

Definition per_union {o}
           (ts : cts)
           lib
           (T1 T2 : @CTerm o)
           (eq : per(o)) : [U] :=
  {eqa, eqb : lib-per(lib,o)
   , {A1, A2, B1, B2 : CTerm
   , T1 ===>(lib) (mkc_union A1 B1)
   # T2 ===>(lib) (mkc_union A2 B2)
   # in_ext_ext lib (fun lib' x => ts lib' A1 A2 (eqa lib' x))
   # in_ext_ext lib (fun lib' x => ts lib' B1 B2 (eqb lib' x))
   # eq <=2=> (per_union_eq_bar lib eqa eqb)}}.


(* extensional union type *)

Definition per_or {p} (eq1 eq2 : per) : per :=
  fun t1 t2 : @CTerm p => eq1 t1 t2 {+} eq2 t1 t2.

Notation "eq1 +2+ eq2" := (per_or eq1 eq2) (at level 0).

Definition per_eunion {p}
           (ts : cts)
           lib
           (T1 T2 : @CTerm p)
           (eq : per(p)) : [U] :=
  {eqa1, eqa2, eqb1, eqb2 : per
   , {A1, A2, B1, B2 : CTerm
   , T1 ===>(lib) (mkc_eunion A1 B1)
   # T2 ===>(lib) (mkc_eunion A2 B2)
   # ((eqa1 +2+ eqb1) <=2=> (eqa2 +2+ eqb2))
   # ts lib A1 A1 eqa1
   # ts lib A2 A2 eqa2
   # ts lib B1 B1 eqb1
   # ts lib B2 B2 eqb2
   # eq <=2=> (per_union_eq lib eqa1 eqb1)}}.

(* begin hide *)

Definition per_union2_eq_L {o} (ts : cts(o)) lib T1 T2 t t' : [U] :=
  {x, y : CTerm
   , {eq : per(o)
   , ts lib T1 T2 eq
   # t ===>(lib) (mkc_inl x)
   # t' ===>(lib) (mkc_inl y)
   # eq x y}}.

Definition per_union2_eq_R {o} (ts : cts(o)) lib T1 T2 t t' : [U] :=
  {x, y : CTerm
   , {eq : per(o)
   , ts lib T1 T2 eq
   # t ===>(lib) (mkc_inr x)
   # t' ===>(lib) (mkc_inr y)
   # eq x y}}.

Definition per_union2_eq {p} (ts : cts(p)) lib A1 A2 B1 B2 t1 t2 :=
  per_union2_eq_L ts lib A1 A2 t1 t2 {+} per_union2_eq_R ts lib B1 B2 t1 t2.

Definition per_union2 {o}
           (ts : cts)
           lib
           (T1 T2 : @CTerm o)
           (eq : per(o)) : [U] :=
   {eqa : per(o)
   , {A1, A2, B1, B2 : CTerm
   , T1 ===>(lib) (mkc_union2 A1 B1)
   # T2 ===>(lib) (mkc_union2 A2 B2)
   # eq <=2=> (per_union2_eq ts lib A1 A2 B1 B2)
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
      -> ccequivc_ext lib t1 (mkc_apply f a1)
      -> ccequivc_ext lib t2 (mkc_apply f a2)
      -> per_image_eq lib eqa f t1 t2.

Definition per_image_eq_bar {o}
           (lib  : library)
           (eqa  : lib-per(lib,o))
           (f    : CTerm)
           (t t' : CTerm) : [U] :=
  in_open_bar_ext lib (fun lib' x => per_image_eq lib' (eqa lib' x) f t t').

Definition per_image {o}
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm o)
           (eq    : per) : [U] :=
  {eqa : lib-per(lib,o)
   , {A1, A2, f1, f2 : CTerm
      , T1 ===>(lib) (mkc_image A1 f1)
      # T2 ===>(lib) (mkc_image A2 f2)
      # in_ext_ext lib (fun lib' x => ts lib' A1 A2 (eqa lib' x))
      # ccequivc_ext lib f1 f2
      # eq <=2=> (per_image_eq_bar lib eqa f1)}}.


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
      # ts lib A A eqa
      # ts lib A' A' eqa'
      # (forall a (e : eqa a a),
           {a' : CTerm , {e' : eqa' a' a'
            , ts lib (substc a v B) (substc a' v' B') (eqb a a' e e')}})
      # (forall a' (e' : eqa' a' a'),
           {a : CTerm , {e : eqa a a
            , ts lib (substc a v B) (substc a' v' B') (eqb a a' e e')}}) }}}}.

Definition per_eisect1 {p}
           (ts : cts)
           lib
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
      # ts lib A A eqa
      # ts lib A' A' eqa'
      # (forall a (e : eqa a a),
            ts lib
               (substc a v B)
               (substc (f a e) v' B')
               (eqb a (f a e) e (g a e)))
      # (forall a' (e' : eqa' a' a'),
            ts lib
               (substc (f' a' e') v B)
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
           (ts : cts)
           lib
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
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per) : [U] :=
  {R1, R2 : CTerm
   , {eq1, eq2 : CTerm -> CTerm -> per
      , T1 ===>(lib) (mkc_pertype R1)
      # T2 ===>(lib) (mkc_pertype R2)
      # (forall x y, ts lib
                        (mkc_apply2 R1 x y)
                        (mkc_apply2 R1 x y)
                        (eq1 x y))
      # (forall x y, ts lib
                        (mkc_apply2 R2 x y)
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

Definition per_ipertype {p} (ts : cts) lib (T1 T2 : @CTerm p) (eq : per) :=
  {R1, R2 : CTerm
   , {eq1 : CTerm -> CTerm -> per
      , T1 ===>(lib) (mkc_ipertype R1)
      # T2 ===>(lib) (mkc_ipertype R2)
      # (forall x y, ts lib
                        (mkc_apply2 R1 x y)
                        (mkc_apply2 R2 x y)
                        (eq1 x y))
      # is_per eq1
      # eq <=2=> (pertype_eq eq1) }}.

(**

 Yet another intensional version of [per_pertype]:

 *)

Definition per_spertype {p} (ts : cts) lib (T1 T2 : @CTerm p) (eq : per) :=
  {R1, R2 : CTerm
   , {eq1 : CTerm -> CTerm -> per
      , T1 ===>(lib) (mkc_spertype R1)
      # T2 ===>(lib) (mkc_spertype R2)
      # (forall x y,
           ts lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (eq1 x y))
      # (forall x y z,
           inhabited (eq1 x z)
           -> ts lib (mkc_apply2 R1 x y) (mkc_apply2 R1 z y) (eq1 x y))
      # (forall x y z,
           inhabited (eq1 y z)
           -> ts lib (mkc_apply2 R1 x y) (mkc_apply2 R1 x z) (eq1 x y))
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
           (ts : cts)
           lib
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
      # ts lib A1 A2 eqa
      # (forall a1 a2 b1 b2 (ea : eqa a1 a2) (eb : eqa b1 b2),
            ts lib
               (lsubstc2 x1 a1 y1 b1 E1)
               (lsubstc2 x1 a2 y1 b2 E1)
               (eqe1 a1 a2 ea b1 b2 eb))
      # (forall a1 a2 b1 b2 (ea : eqa a1 a2) (eb : eqa b1 b2),
            ts lib
               (lsubstc2 x2 a1 y2 b1 E2)
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


Definition per_set_eq {o} (eqa : per(o)) (eqb : per-fam(eqa)) (t t' : @CTerm o) :=
  {e : eqa t t' , @inhabited o (eqb t t' e)}.

Definition per_set_eq_bar {o}
           (lib  : library)
           (eqa  : lib-per(lib,o))
           (eqb  : lib-per-fam(lib,eqa))
           (t t' : CTerm) : [U] :=
  in_open_bar_ext lib (fun lib' x => per_set_eq (eqa lib' x) (eqb lib' x) t t').

Definition per_set {o}
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm o)
           (eq    : per) : [U] :=
  {eqa : lib-per(lib,o)
  , {eqb : lib-per-fam(lib,eqa,o)
  , type_family_ext mkc_set ts lib T1 T2 eqa eqb
  # eq <=2=> (per_set_eq_bar lib eqa eqb)}}.

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

Definition per_partial {p} (ts : cts) lib T1 T2 (eq : per(p)) : [U] :=
  {A1, A2 : @CTerm p , {eqa : per
      , T1 ===>(lib) (mkc_partial A1)
      # T2 ===>(lib) (mkc_partial A2)
      # ts lib A1 A2 eqa
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
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per(p)) : [U] :=
  {A1, A2 : CTerm ,
    {eqa : per ,
        T1 ===>(lib) (mkc_mono A1)
        # T2 ===>(lib) (mkc_mono A2)
        # ts lib A1 A2 eqa
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
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per(p)) : [U] :=
  {A1, A2 : CTerm ,
    {eqa : per ,
        T1 ===>(lib) (mkc_admiss A1)
      # T2 ===>(lib) (mkc_admiss A2)
      # ts lib A1 A2 eqa
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

Definition per_w {p} (ts : cts) lib T1 T2 (eq : per(p)) : [U] :=
  {eqa : per , {eqb : per-fam(eqa) ,
   type_family mkc_w ts lib T1 T2 eqa eqb
   # eq <=2=> (weq lib eqa eqb)}}.

(**

  types%~\cite{Berg+Marchi:2007,Abbott+Altenkirch+Ghani:2005}% are
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
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per) : [U] :=
  {eqa : per
   , {eqb : per-fam(eqa)
      , type_family mkc_m ts lib T1 T2 eqa eqb
      # eq <=2=> (meq lib eqa eqb)}}.

(**

  We now define the concept of parameterized type families, which we
  use to define parameterized W and types.  In a parameterized W
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
      # ts lib P1 P2 eqp
      # (forall p1 p2,
         forall ep : eqp p1 p2,
           ts lib (substc p1 ap1 A1) (substc p2 ap2 A2) (eqa p1 p2 ep))
      # (forall p1 p2,
         forall ep : eqp p1 p2,
         forall a1 a2,
         forall ea : eqa p1 p2 ep a1 a2,
           ts lib
              (lsubstc2 bp1 p1 ba1 a1 B1)
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
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per) : [U] :=
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
  parameterized types as follows:

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
           (ts    : cts)
           (lib   : library)
           (T1 T2 : @CTerm p)
           (eq    : per) : [U] :=
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

(* --- now we define the Nuprl type system: nuprl_omega *)

(** close the different constructors with that and remove ccomputes_to_valc
 * from the per definitions *)
Definition close_compute {p} (ts : cts) lib (T1 T2 : @CTerm p) (eq : per(p)) :=
  {T3, T4 : CTerm
   $ T1 ===>(lib) T3
   # T2 ===>(lib) T4
   # ts lib T3 T4 eq}.

(* end hide *)



(*Definition bar_per_type {o} {lib} (bar : @BarLib o lib) :=
  forall (lib1 : library) (br : bar_lib_bar bar lib1)
         (lib2 : library) (ext : lib_extends lib2 lib1),
    per(o).

Definition bar_per_preserves {o} {lib} {bar : @BarLib o lib}
           (eqa : bar_per_type bar) :=
  forall lib1 lib2
         (b1 : bar_lib_bar bar lib1)
         (b2 : bar_lib_bar bar lib2)
         lib3
         (ext1 : lib_extends lib3 lib1)
         (ext2 : lib_extends lib3 lib2),
    (eqa lib1 b1 lib3 ext1) <=2=> (eqa lib2 b2 lib3 ext2).

Record bar_per {o} {lib} (bar : @BarLib o lib) :=
  MkBarPer
    {
      bar_per_per  :> bar_per_type bar;
      bar_per_cond : bar_per_preserves bar_per_per;
    }.

Notation "bar-per( lib , bar , o )" := (@bar_per o lib bar).

(*Notation "bar-lib-per( lib , bar , o )" :=
  (forall (lib1 : library) (br : bar_lib_bar bar lib1)
          (lib2 : library) (ext : lib_extends lib2 lib1),
      lib-per(lib2,o)).*)

Definition e_all_in_bar_ext2 {o} {lib}
           (bar : @BarLib o lib)
           (F : forall (lib1 : library) (br : bar_lib_bar bar lib1)
                       (lib2 : library) (ext : lib_extends lib2 lib1),
               Prop) :=
  forall (lib' : library) (b : bar_lib_bar bar lib'),
    in_ext_ext lib' (F lib' b).


Lemma implies_computes_to_valc_seq_bar_raise_bar {o} :
  forall {lib lib'} (bar : @BarLib o lib) (ext : lib_extends lib' lib) t v,
    t ==b==>(bar) v
    -> t ==b==>(raise_bar bar ext) v.
Proof.
  introv comp br e.
  simpl in *; exrepnd.
  apply (comp lib1 br1); eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_valc_seq_bar_raise_bar : slow.
*)

Definition raise_ext_per {o} {lib lib'}
           (per : ext-per(lib,o))
           (ext : lib_extends lib' lib) : ext-per(lib',o) :=
  fun lib'' x => per lib'' (lib_extends_trans x ext).

Definition raise_lib_per {o} {lib lib'}
           (per : lib-per(lib,o))
           (ext : lib_extends lib' lib) : lib-per(lib',o).
Proof.
  exists (raise_ext_per per ext).
  introv; apply per.
Defined.

(*Definition sub_bar {o} {lib} (bar1 bar2 : @BarLib o lib) :=
  forall lib1,
    bar_lib_bar bar1 lib1
    -> exists lib2, bar_lib_bar bar2 lib2 # lib_extends lib2 lib1.

Definition bar_per_type_change_bar
           {o} {lib} {bar : @BarLib o lib}
           (per : bar_per_type bar)
           (bar' : @BarLib o lib) : bar_per_type bar'.
Proof.
  introv br ext.
  exact (fun t1 t2 =>
           exists (lib' : library),
             exists (br' : bar_lib_bar bar lib'),
               exists (ext : lib_extends lib2 lib'),
                     per lib' br' lib2 ext t1 t2).
Defined.

Definition bar_per_change_bar
           {o} {lib} {bar : @BarLib o lib}
           (per : bar-per(lib,bar,o))
           (bar' : @BarLib o lib) : bar-per(lib,bar',o).
Proof.
  exists (bar_per_type_change_bar per bar').

  repeat introv; simpl.
  unfold bar_per_type_change_bar.
  split; introv h; exrepnd.

  { exists lib' br' ext; eapply (bar_per_cond _ per); eauto. }

  { exists lib' br' ext; eapply (bar_per_cond _ per); eauto. }
Defined.

Definition bar_per_type_intersect_left
           {o} {lib} {bar : @BarLib o lib}
           (per : bar_per_type bar)
           (bar' : @BarLib o lib) : bar_per_type (intersect_bars bar bar').
Proof.
  introv br ext x; introv.
  simpl in *; exrepnd.

Abort.


(*(* raise eqa *)
Definition per_bar_eq {o}
           {lib}
           (bar : @BarLib o lib)
           (eqa : bar-per(lib,bar,o))
           (t1 t2 : CTerm) :=
  {bar' : BarLib lib
  , forall lib1 (br : bar_lib_bar bar lib1)
           lib2 (br' : bar_lib_bar bar' lib2)
           lib3 (ext1 : lib_extends lib3 lib1) (ext2 : lib_extends lib3 lib2),
       bar_per_per _ eqa lib1 br lib3 ext1 t1 t2 }.
*)

Definition per_bar {o}
           (ts    : cts(o))
           (lib   : library)
           (T1 T2 : CTerm)
           (eq    : per(o)) : [U] :=
  {bar : BarLib lib
  , {eqa : lib-per(lib,bar,o)
  , e_all_in_bar_ext2 bar (fun lib1 br lib2 ext => ts lib2 T1 T2 (bar_per_per _ eqa lib1 br lib2 ext))
  # eq <=2=> (per_bar_eq bar eqa) }}.*)

Definition per_bar_eq {o}
           (lib : @library o)
           (eqa : lib-per(lib,o))
           (t1 t2 : CTerm) :=
  in_open_bar_ext
    lib
    (fun lib' (y : lib_extends lib' lib) => eqa lib' y t1 t2).

Definition per_bar {o}
           (ts    : cts(o))
           (lib   : library)
           (T1 T2 : CTerm)
           (eq    : per(o)) : [U] :=
  {eqa : lib-per(lib,o)
  , in_open_bar_ext lib (fun lib' x => ts lib' T1 T2 (eqa lib' x))
  # eq <=2=> (per_bar_eq lib eqa) }.


(**

  The [close] operator takes a candidate type system and returns a
  candidate type system closed under the type constructor defined
  above (except the ones for extensional intersection types and
  quotient types which are not yet in the system because we have not
  yet had time to prove that these types preserve the type system
  properties presented below).

 *)

Inductive close {p} (ts : cts) lib (T T' : @CTerm p) (eq : per(p)) : [U] :=
  | CL_init     : ts lib T T' eq -> close ts lib T T' eq
  | CL_bar      : per_bar          (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_int      : per_int          (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_nat      : per_nat          (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_qnat     : per_qnat         (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_csname   : per_csname       (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_atom     : per_atom         (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_uatom    : per_uatom        (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_base     : per_base         (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_approx   : per_approx       (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_cequiv   : per_cequiv       (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_eq       : per_eq           (close ts) lib T T' eq -> close ts lib T T' eq
(*  | CL_req      : per_req      (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_teq      : per_teq      (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_isect    : per_isect    (close ts) lib T T' eq -> close ts lib T T' eq*)
  | CL_qtime    : per_qtime        (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_func     : per_func_ext     (close ts) lib T T' eq -> close ts lib T T' eq
(*  | CL_disect   : per_disect   (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_pertype  : per_pertype  (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_ipertype : per_ipertype (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_spertype : per_spertype (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_w        : per_w        (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_m        : per_m        (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_pw       : per_pw       (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_pm       : per_pm       (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_texc     : per_texc     (close ts) lib T T' eq -> close ts lib T T' eq*)
  | CL_union    : per_union        (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_image    : per_image        (close ts) lib T T' eq -> close ts lib T T' eq
(*  | CL_partial  : per_partial  (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_admiss   : per_admiss   (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_mono     : per_mono     (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_ffatom   : per_ffatom   (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_effatom  : per_effatom  (close ts) lib T T' eq -> close ts lib T T' eq*)
(*  | CL_ffatoms  : per_ffatoms  (close ts) lib T T' eq -> close ts lib T T' eq*)
  | CL_ffdefs   : per_ffdefs   (close ts) lib T T' eq -> close ts lib T T' eq
  | CL_set      : per_set      (close ts) lib T T' eq -> close ts lib T T' eq
(*  | CL_tunion   : per_tunion   (close ts) lib T T' eq -> close ts lib T T' eq*)
  | CL_product  : per_product_bar  (close ts) lib T T' eq -> close ts lib T T' eq.
Hint Constructors close.

(*  | CL_eunion   : per_eunion   lib (close lib ts) T T' eq -> close ts lib T T' eq*)
(*  | CL_union2   : per_union2   lib (close lib ts) T T' eq -> close ts lib T T' eq*)
(*  | CL_eisect   : per_eisect   lib (close lib ts) T T' eq -> close lib ts T T' eq*)

Arguments CL_init     {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_bar      {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_int      {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_nat      {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_qnat     {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_csname   {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_atom     {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_uatom    {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_base     {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_approx   {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_cequiv   {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_eq       {p} [ts] [lib] [T] [T'] [eq] _.
(*Arguments CL_req      {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_teq      {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_isect    {p} [ts] [lib] [T] [T'] [eq] _.*)
Arguments CL_qtime    {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_func     {p} [ts] [lib] [T] [T'] [eq] _.
(*Arguments CL_disect   {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_pertype  {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_ipertype {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_spertype {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_w        {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_m        {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_pw       {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_pm       {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_texc     {p} [ts] [lib] [T] [T'] [eq] _.*)
Arguments CL_union    {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_image    {p} [ts] [lib] [T] [T'] [eq] _.
(*Arguments CL_partial  {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_admiss   {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_mono     {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_ffatom   {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_effatom  {p} [ts] [lib] [T] [T'] [eq] _.*)
(*Arguments CL_ffatoms  {p} [ts] [lib] [T] [T'] [eq] _.*)
Arguments CL_ffdefs   {p} [ts] [lib] [T] [T'] [eq] _.
Arguments CL_set      {p} [ts] [lib] [T] [T'] [eq] _.
(*Arguments CL_tunion   {p} [ts] [lib] [T] [T'] [eq] _.*)
Arguments CL_product  {p} [ts] [lib] [T] [T'] [eq] _.

(* begin hide *)


Tactic Notation "close_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CL_init"
  | Case_aux c "CL_bar"
  | Case_aux c "CL_int"
  | Case_aux c "CL_nat"
  | Case_aux c "CL_qnat"
  | Case_aux c "CL_csname"
  | Case_aux c "CL_atom"
  | Case_aux c "CL_uatom"
  | Case_aux c "CL_base"
  | Case_aux c "CL_approx"
  | Case_aux c "CL_cequiv"
  | Case_aux c "CL_eq"
(*  | Case_aux c "CL_req"*)
(*  | Case_aux c "CL_teq"*)
(*  | Case_aux c "CL_isect"*)
  | Case_aux c "CL_qtime"
  | Case_aux c "CL_func"
(*  | Case_aux c "CL_disect"*)
(*  | Case_aux c "CL_pertype"*)
(*  | Case_aux c "CL_ipertype"*)
(*  | Case_aux c "CL_spertype"*)
(*  | Case_aux c "CL_w"*)
(*  | Case_aux c "CL_m"*)
(*  | Case_aux c "CL_pw"*)
(*  | Case_aux c "CL_pm"*)
(*  | Case_aux c "CL_texc"*)
  | Case_aux c "CL_union"
(*(*  | Case_aux c "CL_eunion"*)*)
(*(*  | Case_aux c "CL_union2"*)*)
  | Case_aux c "CL_image"
(*(*  | Case_aux c "CL_eisect"*)*)
(*  | Case_aux c "CL_partial"*)
(*  | Case_aux c "CL_admiss"*)
(*  | Case_aux c "CL_mono"*)
(*  | Case_aux c "CL_ffatom"*)
(*  | Case_aux c "CL_effatom"*)
(*  | Case_aux c "CL_ffatoms"*)
  | Case_aux c "CL_ffdefs"
  | Case_aux c "CL_set"
(*  | Case_aux c "CL_tunion"*)
  | Case_aux c "CL_product"
  ].

Definition close_ind' {pp}
  (P : cts -> cts)
  (init : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per),
            ts lib T T' eq -> P ts lib T T' eq)

  (pbar : forall (ts    : cts)
                 (lib   : library)
                 (T T'  : @CTerm pp)
                 (eq    : per)
                 (eqa   : lib-per(lib,pp))
                 (cla   : in_open_bar_ext lib (fun lib' x => close ts lib' T T' (eqa lib' x)))
                 (reca  : in_open_bar_ext lib (fun lib' x => P ts lib' T T' (eqa lib' x)))
                 (eqiff : eq <=2=> (per_bar_eq lib eqa))
                 (per   : per_bar (close ts) lib T T' eq),
      P ts lib T T' eq)

  (int  : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per)
                 (per  : per_int (close ts) lib T T' eq),
      P ts lib T T' eq)

  (nat  : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per)
                 (per  : per_nat (close ts) lib T T' eq),
      P ts lib T T' eq)

  (qnat  : forall (ts   : cts)
                  (lib  : library)
                  (T T' : @CTerm pp)
                  (eq   : per)
                  (per  : per_qnat (close ts) lib T T' eq),
      P ts lib T T' eq)

  (csname : forall (ts   : cts)
                   (lib  : library)
                   (T T' : @CTerm pp)
                   (eq   : per)
                   (per  : per_csname (close ts) lib T T' eq),
      P ts lib T T' eq)

  (atom : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per)
                 (per  : per_atom (close ts) lib T T' eq),
            P ts lib T T' eq)
  (uatom : forall (ts   : cts)
                  (lib  : library)
                  (T T' : @CTerm pp)
                  (eq   : per)
                  (per  : per_uatom (close ts) lib T T' eq),
            P ts lib T T' eq)
  (base : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per)
                 (per  : per_base (close ts) lib T T' eq),
            P ts lib T T' eq)
  (aprx : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per)
                 (per  : per_approx (close ts) lib T T' eq),
              P ts lib T T' eq)
  (ceq : forall (ts   : cts)
                (lib  : library)
                (T T' : @CTerm pp)
                (eq   : per)
                (per   : per_cequiv (close ts) lib T T' eq),
      P ts lib T T' eq)

  (equ : forall (ts    : cts)
                (lib   : library)
                (T T'  : @CTerm pp)
                (eq    : per)
                (A B a1 a2 b1 b2 : @CTerm pp)
                (eqa   : lib-per(lib,pp))
                (c1    : T ===>(lib) (mkc_equality a1 a2 A))
                (c2    : T' ===>(lib) (mkc_equality b1 b2 B))
                (cla   : in_ext_ext lib (fun lib' x => close ts lib' A B (eqa lib' x)))
                (reca  : in_ext_ext lib (fun lib' x => P ts lib' A B (eqa lib' x)))
                (eos1  : eqorceq_ext lib eqa a1 b1)
                (eos2  : eqorceq_ext lib eqa a2 b2)
                (eqiff : eq <=2=> (eq_per_eq_bar lib a1 a2 eqa))
                (per   : per_eq (close ts) lib T T' eq),
      P ts lib T T' eq)

(*  (equ  : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per)
                 (A B a1 a2 b1 b2 : @CTerm pp)
                 (eqa  : per)
                 (c1 : T ===>(lib) (mkc_equality a1 a2 A))
                 (c2 : T' ===>(lib) (mkc_equality b1 b2 B))
                 (cla  : close ts lib A B eqa)
                 (reca : P ts lib A B eqa)
                 (eos1 : eqorceq lib eqa a1 b1)
                 (eos2 : eqorceq lib eqa a2 b2)
                 (eqiff : forall t t',
                            eq t t'
                               <=> t ===>(lib) mkc_axiom
                               # t' ===>(lib) mkc_axiom
                               # eqa a1 a2)
                 (per : per_eq_bar (close ts) lib T T' eq),
            P ts lib T T' eq)*)

(*  (requ : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per)
                 (A B a1 a2 b1 b2 : @CTerm pp)
                 (eqa  : per)
                 (c1   : T ===>(lib) (mkc_requality a1 a2 A))
                 (c2   : T' ===>(lib) (mkc_requality b1 b2 B))
                 (cla  : close ts lib A B eqa)
                 (reca : P ts lib A B eqa)
                 (eo1  : eqorceq lib eqa a1 b1)
                 (eo2  : eqorceq lib eqa a2 b2)
                 (eqiff : eq <=2=> (per_req_eq lib a1 a2 eqa))
                 (per  : per_req (close ts) lib T T' eq),
            P ts lib T T' eq)*)

(*  (tequ : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per)
                 (a1 a2 b1 b2 : @CTerm pp)
                 (eqa  : per)
                 (c1   : T ===>(lib) (mkc_tequality a1 a2))
                 (c2   : T' ===>(lib) (mkc_tequality b1 b2))
                 (cl1  : close ts lib a1 b1 eqa)
                 (rec1 : P ts lib a1 b1 eqa)
                 (cl2  : close ts lib a2 b2 eqa)
                 (rec2 : P ts lib a2 b2 eqa)
                 (cl3  : close ts lib a1 a2 eqa)
                 (rec3 : P ts lib a1 a2 eqa)
                 (eqiff : eq <=2=> (fun t t' => True))
                 (per : per_teq (close ts) lib T T' eq),
            P ts lib T T' eq)*)

(*  (isect : forall (ts   : cts)
                  (lib  : library)
                  (T T' : @CTerm pp)
                  (eq   : per)
                  (A A' : @CTerm pp)
                  (v v' : NVar)
                  (B    : CVTerm [v])
                  (B'   : CVTerm [v'])
                  (eqa  : per)
                  (eqb  : forall a a' : CTerm, forall e : eqa a a', per)
                  (c1   : T ===>(lib) (mkc_isect A v B))
                  (c2   : T' ===>(lib) (mkc_isect A' v' B'))
                  (cla  : close ts lib A A' eqa)
                  (reca : P ts lib A A' eqa)
                  (clb  : forall a a', forall e : eqa a a', close ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                  (recb : forall a a', forall e : eqa a a', P ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                  (eqiff : forall t t', eq t t' <=> (forall a a', forall e : eqa a a', eqb a a' e t t'))
                  (per  : per_isect (close ts) lib T T' eq),
             P ts lib T T' eq)*)

  (qtime : forall (ts    : cts)
                  (lib   : library)
                  (T T'  : @CTerm pp)
                  (eq    : per)
                  (A B   : @CTerm pp)
                  (eqa   : lib-per(lib,pp))
                  (c1    : T ===>(lib) (mkc_qtime A))
                  (c2    : T' ===>(lib) (mkc_qtime B))
                  (cla   : in_ext_ext lib (fun lib' x => close ts lib' A B (eqa lib' x)))
                  (reca  : in_ext_ext lib (fun lib' x => P ts lib' A B (eqa lib' x)))
                  (eqiff : eq <=2=> (per_qtime_eq_bar lib eqa))
                  (per   : per_qtime (close ts) lib T T' eq),
      P ts lib T T' eq)

  (func : forall (ts    : cts)
                 (lib   : library)
                 (T T'  : @CTerm pp)
                 (eq    : per)
                 (A A'  : @CTerm pp)
                 (v v'  : NVar)
                 (B     : CVTerm [v])
                 (B'    : CVTerm [v'])
                 (eqa   : lib-per(lib,pp))
                 (eqb   : lib-per-fam(lib,eqa))
                 (c1    : T ===>(lib) (mkc_function A v B))
                 (c2    : T' ===>(lib) (mkc_function A' v' B'))
                 (cla   : in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x)))
                 (reca  : in_ext_ext lib (fun lib' x => P ts lib' A A' (eqa lib' x)))
                 (clb   : in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e)))
                 (recb  : in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), P ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e)))
                 (eqiff : eq <=2=> (per_func_ext_eq lib eqa eqb))
                 (per   : per_func_ext (close ts) lib T T' eq),
            P ts lib T T' eq)

(*  (func : forall (ts    : cts)
                 (lib   : library)
                 (T T'  : @CTerm pp)
                 (eq    : per)
                 (A A'  : @CTerm pp)
                 (v v'  : NVar)
                 (B     : CVTerm [v])
                 (B'    : CVTerm [v'])
                 (eqa   : per)
                 (eqb   : per-fam(eqa))
                 (c1    : T ===>(lib) (mkc_function A v B))
                 (c2    : T' ===>(lib) (mkc_function A' v' B'))
                 (cla   : close ts lib A A' eqa)
                 (reca  : P ts lib A A' eqa)
                 (clb   : forall a a' (e : eqa a a'), close ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                 (recb  : forall a a' (e : eqa a a'), P ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                 (eqiff : eq <=2=> (per_func_eq eqa eqb))
                 (per   : per_func (close ts) lib T T' eq),
            P ts lib T T' eq)*)

(*  (disect : forall (ts   : cts)
                   (lib  : library)
                   (T T' : @CTerm pp)
                   (eq   : per)
                   (A A' : @CTerm pp)
                   (v v' : NVar)
                   (B    : CVTerm [v])
                   (B'   : CVTerm [v'])
                   (eqa  : per)
                   (eqb  : forall a a' : CTerm, forall e : eqa a a', per)
                   (c1   : T ===>(lib) (mkc_disect A v B))
                   (c2   : T' ===>(lib) (mkc_disect A' v' B'))
                   (cla  : close ts lib A A' eqa)
                   (reca : P ts lib A A' eqa)
                   (clb  : forall a a', forall e : eqa a a', close ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                   (recb : forall a a', forall e : eqa a a', P ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                   (eqiff : forall t t', eq t t' <=> {e : eqa t t' , eqb t t' e t t'})
                   (per : per_disect (close ts) lib T T' eq),
              P ts lib T T' eq)*)

(*  (pertype : forall (ts   : cts)
                    (lib  : library)
                    (T T' : @CTerm pp)
                    (eq   : per)
                    (R1 R2 : @CTerm pp)
                    (eq1 eq2 : CTerm -> CTerm -> per)
                    (c1   : T ===>(lib) (mkc_pertype R1))
                    (c2   : T' ===>(lib) (mkc_pertype R2))
                    (cl1  : forall x y, close ts lib
                                              (mkc_apply2 R1 x y)
                                              (mkc_apply2 R1 x y)
                                              (eq1 x y))
                    (rec1 : forall x y, P ts lib
                                          (mkc_apply2 R1 x y)
                                          (mkc_apply2 R1 x y)
                                          (eq1 x y))
                    (cl2 : forall x y, close ts lib
                                             (mkc_apply2 R2 x y)
                                             (mkc_apply2 R2 x y)
                                             (eq2 x y))
                    (rec2 : forall x y, P ts lib
                                          (mkc_apply2 R2 x y)
                                          (mkc_apply2 R2 x y)
                                          (eq2 x y))
                    (inh : forall x y, inhabited (eq1 x y) <=> inhabited (eq2 x y))
                    (isper : is_per eq1)
                    (eqiff : forall t t', eq t t' <=> inhabited (eq1 t t'))
                    (per : per_pertype (close ts) lib T T' eq),
               P ts lib T T' eq)*)

(*  (ipertype : forall (ts   : cts)
                     (lib  : library)
                     (T T' : @CTerm pp)
                     (eq   : per)
                     (R1 R2 : @CTerm pp)
                     (eq1  : CTerm -> CTerm -> per)
                     (c1   : T ===>(lib) (mkc_ipertype R1))
                     (c2   : T' ===>(lib) (mkc_ipertype R2))
                     (cl1  : forall x y, close ts lib
                                               (mkc_apply2 R1 x y)
                                               (mkc_apply2 R2 x y)
                                               (eq1 x y))
                     (rec1 : forall x y, P ts lib
                                           (mkc_apply2 R1 x y)
                                           (mkc_apply2 R2 x y)
                                           (eq1 x y))
                     (isper : is_per eq1)
                     (eqiff : eq <=2=> (pertype_eq eq1))
                     (per : per_ipertype (close ts) lib T T' eq),
      P ts lib T T' eq)*)

(*  (spertype : forall (ts   : cts)
                     (lib  : library)
                     (T T' : @CTerm pp)
                     (eq   : per)
                     (R1 R2 : @CTerm pp)
                     (eq1 : CTerm -> CTerm -> per)
                     (c1 : T ===>(lib) (mkc_spertype R1))
                     (c2 : T' ===>(lib) (mkc_spertype R2))
                     (cl1 : forall x y,
                              close ts lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (eq1 x y))
                     (rec1 : forall x y,
                               P ts lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (eq1 x y))
                     (cl2 : forall x y z,
                              inhabited(eq1 x z)
                              -> close ts lib (mkc_apply2 R1 x y) (mkc_apply2 R1 z y) (eq1 x y))
                     (rec2 : forall x y z,
                               inhabited(eq1 x z)
                               -> P ts lib (mkc_apply2 R1 x y) (mkc_apply2 R1 z y) (eq1 x y))
                     (cl3 : forall x y z,
                              inhabited(eq1 y z)
                              -> close ts lib (mkc_apply2 R1 x y) (mkc_apply2 R1 x z) (eq1 x y))
                     (rec3 : forall x y z,
                               inhabited(eq1 y z)
                               -> P ts lib (mkc_apply2 R1 x y) (mkc_apply2 R1 x z) (eq1 x y))
                     (isper : is_per eq1)
                     (eqiff : eq <=2=> (pertype_eq eq1))
                     (per : per_spertype (close ts) lib T T' eq),
                P ts lib T T' eq)*)

(*  (w     : forall (ts   : cts)
                  (lib  : library)
                  (T T' : @CTerm pp)
                  (eq   : per)
                  (A A' : @CTerm pp)
                  (v v' : NVar)
                  (B    : CVTerm [v])
                  (B'   : CVTerm [v'])
                  (eqa  : per)
                  (eqb  : forall a a' : CTerm, forall e : eqa a a', per)
                  (c1   : T ===>(lib) (mkc_w A v B))
                  (c2   : T' ===>(lib) (mkc_w A' v' B'))
                  (cla  : close ts lib A A' eqa)
                  (reca : P ts lib A A' eqa)
                  (clb  : forall a a', forall e : eqa a a', close ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                  (recb : forall a a', forall e : eqa a a', P ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                  (eqiff : forall t t', eq t t' <=> weq lib eqa eqb t t')
                  (per : per_w (close ts) lib T T' eq),
            P ts lib T T' eq)*)

(*  (m     : forall (ts   : cts)
                  (lib  : library)
                  (T T' : @CTerm pp)
                  (eq   : per)
                  (A A' : @CTerm pp)
                  (v v' : NVar)
                  (B    : CVTerm [v])
                  (B'   : CVTerm [v'])
                  (eqa  : per)
                  (eqb  : forall a a' : CTerm, forall e : eqa a a', per)
                  (c1   : T ===>(lib) (mkc_m A v B))
                  (c2   : T' ===>(lib) (mkc_m A' v' B'))
                  (cla  : close ts lib A A' eqa)
                  (reca : P ts lib A A' eqa)
                  (clb  : forall a a', forall e : eqa a a', close ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                  (recb : forall a a', forall e : eqa a a', P ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                  (eqiff : forall t t', eq t t' <=> meq lib eqa eqb t t')
                  (per : per_m (close ts) lib T T' eq),
            P ts lib T T' eq)*)

(*  (pw    : forall (ts   : cts)
                  (lib  : library)
                  (T T' : @CTerm pp)
                  (eq   : per)
                  (Pr Pr' : @CTerm pp)
                  (ap ap' : NVar)
                  (A  : CVTerm [ap])
                  (A' : CVTerm [ap'])
                  (bp bp' ba ba' : NVar)
                  (B  : CVTerm [bp,ba])
                  (B' : CVTerm [bp',ba'])
                  (cp cp' ca ca' cb cb' : NVar)
                  (C  : CVTerm [cp,ca,cb])
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
                  (clp : close ts lib Pr Pr' eqp)
                  (recp : P ts lib Pr Pr' eqp)
                  (cla : forall p p',
                         forall ep : eqp p p',
                           close ts lib (substc p ap A) (substc p' ap' A') (eqa p p' ep))
                  (reca : forall p p',
                          forall ep : eqp p p',
                            P ts lib (substc p ap A) (substc p' ap' A') (eqa p p' ep))
                  (clb : forall p p',
                         forall ep : eqp p p',
                         forall a a',
                         forall ea : eqa p p' ep a a',
                           close ts lib
                                 (lsubstc2 bp p ba a B)
                                 (lsubstc2 bp' p' ba' a' B')
                                 (eqb p p' ep a a' ea))
                  (recb : forall p p',
                          forall ep : eqp p p',
                          forall a a',
                          forall ea : eqa p p' ep a a',
                            P ts lib
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
                  (per : per_pw (close ts) lib T T' eq),
            P ts lib T T' eq)*)

(*  (pm    : forall (ts   : cts)
                  (lib  : library)
                  (T T' : @CTerm pp)
                  (eq   : per)
                  (Pr Pr' : @CTerm pp)
                  (ap ap' : NVar)
                  (A  : CVTerm [ap])
                  (A' : CVTerm [ap'])
                  (bp bp' ba ba' : NVar)
                  (B  : CVTerm [bp,ba])
                  (B' : CVTerm [bp',ba'])
                  (cp cp' ca ca' cb cb' : NVar)
                  (C  : CVTerm [cp,ca,cb])
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
                  (clp : close ts lib Pr Pr' eqp)
                  (recp : P ts lib Pr Pr' eqp)
                  (cla : forall p p',
                         forall ep : eqp p p',
                           close ts lib (substc p ap A) (substc p' ap' A') (eqa p p' ep))
                  (reca : forall p p',
                          forall ep : eqp p p',
                            P ts lib (substc p ap A) (substc p' ap' A') (eqa p p' ep))
                  (clb : forall p p',
                         forall ep : eqp p p',
                         forall a a',
                         forall ea : eqa p p' ep a a',
                           close ts lib
                                 (lsubstc2 bp p ba a B)
                                 (lsubstc2 bp' p' ba' a' B')
                                 (eqb p p' ep a a' ea))
                  (recb : forall p p',
                          forall ep : eqp p p',
                          forall a a',
                          forall ea : eqa p p' ep a a',
                            P ts lib
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
                  (per : per_pm (close ts) lib T T' eq),
            P ts lib T T' eq)*)

(*  (texc : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per)
                 (N N' E E' : @CTerm pp)
                 (eqn eqe : per)
                 (c1 : T ===>(lib) (mkc_texc N E))
                 (c2 : T' ===>(lib) (mkc_texc N' E'))
                 (cln : close ts lib N N' eqn)
                 (recn : P ts lib N N' eqn)
                 (cle : close ts lib E E' eqe)
                 (rece : P ts lib E E' eqe)
                 (eqiff : forall t t', eq t t' <=> per_texc_eq lib eqn eqe t t')
                 (per : per_texc (close ts) lib T T' eq),
            P ts lib T T' eq)*)

  (union : forall (ts    : cts)
                  (lib   : library)
                  (T T'  : @CTerm pp)
                  (eq    : per)
                  (A A'  : CTerm)
                  (B B'  : @CTerm pp)
                  (eqa   : lib-per(lib,pp))
                  (eqb   : lib-per(lib,pp))
                  (c1    : T ===>(lib) (mkc_union A B))
                  (c2    : T' ===>(lib) (mkc_union A' B'))
                  (cla   : in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x)))
                  (reca  : in_ext_ext lib (fun lib' x => P ts lib' A A' (eqa lib' x)))
                  (clb   : in_ext_ext lib (fun lib' x => close ts lib' B B' (eqb lib' x)))
                  (recb  : in_ext_ext lib (fun lib' x => P ts lib' B B' (eqb lib' x)))
                  (eqiff : eq <=2=> (per_union_eq_bar lib eqa eqb))
                  (per   : per_union (close ts) lib T T' eq),
      P ts lib T T' eq)

(*  (union : forall (ts    : cts)
                  (lib   : library)
                  (T T'  : @CTerm pp)
                  (eq    : per)
                  (bar   : BarLib lib)
                  (A A'  : CTerm)
                  (B B'  : @CTerm pp)
                  (eqa   : lib-per(lib,pp))
                  (eqb   : lib-per(lib,pp))
                  (c1    : T ==b==>(bar) (mkc_union A B))
                  (c2    : T' ==b==>(bar) (mkc_union A' B'))
                  (cla   : e_all_in_bar_ext bar (fun lib' x => close ts lib' A A' (eqa lib' x)))
                  (reca  : e_all_in_bar_ext bar (fun lib' x => P ts lib' A A' (eqa lib' x)))
                  (clb   : e_all_in_bar_ext bar (fun lib' x => close ts lib' B B' (eqb lib' x)))
                  (recb  : e_all_in_bar_ext bar (fun lib' x => P ts lib' B B' (eqb lib' x)))
                  (eqiff : eq <=2=> (per_union_eq_bar lib eqa eqb))
                  (per   : per_union_bar (close ts) lib T T' eq),
      P ts lib T T' eq)*)

  (*  (eunion : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' B B' : @CTerm pp)
                  (eqa1 eqa2 eqb1 eqb2 : per)
                  (c1 : T ===>(lib) (mkc_eunion A B))
                  (c2 : T' ===>(lib) (mkc_eunion A' B'))
                  (iffa : eqa1 <=2=> eqa2)
                  (iffb : eqb1 <=2=> eqb2)
                  (cla1  : close ts lib A A eqa1)
                  (reca1 : P ts A A eqa1)
                  (cla2  : close ts lib A' A' eqa2)
                  (reca2 : P ts A' A' eqa2)
                  (clb1  : close ts lib B B eqb1)
                  (recb1 : P ts B B eqb1)
                  (clb2  : close ts lib B' B' eqb2)
                  (recb2 : P ts B' B' eqb2)
                  (eqiff : eq <=2=> (per_union_eq lib eqa1 eqb1))
                  (per : per_eunion (close ts) lib T T' eq),
            P ts lib T T' eq)*)
(*  (union2 : forall (ts : cts)
                  (T T' : @CTerm pp)
                  (eq : per)
                  (A A' B B' : @CTerm pp)
                  (eqa : per)
                  (c1 : T ===>(lib) (mkc_union2 A B))
                  (c2 : T' ===>(lib) (mkc_union2 A' B'))
                  (cla : close ts lib A A' eqa)
                  (reca : P ts A A' eqa)
                  (clb : close ts lib B B' eqb)
                  (recb : P ts B B' eqb)
                  (eqiff : forall t t', eq t t' <=> per_union_eq lib eqa eqb t t')
                  (per : per_union2 (close ts) lib T T' eq),
            P ts lib T T' eq)*)

  (image : forall (ts    : cts)
                  (lib   : library)
                  (T T'  : @CTerm pp)
                  (eq    : per(pp))
                  (A A'  : CTerm)
                  (f f'  : @CTerm pp)
                  (eqa   : lib-per(lib,pp))
                  (c1    : T ===>(lib) (mkc_image A f))
                  (c2    : T' ===>(lib) (mkc_image A' f'))
                  (cla   : in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x)))
                  (reca  : in_ext_ext lib (fun lib' x => P ts lib' A A' (eqa lib' x)))
                  (ceq   : ccequivc_ext lib f f')
                  (eqiff : eq <=2=> (per_image_eq_bar lib eqa f))
                  (per   : per_image (close ts) lib T T' eq),
            P ts lib T T' eq)

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
                   (per : per_eisect (close ts) lib T T' eq),
              P ts lib T T' eq)*)

(*  (partial : forall (ts   : cts)
                    (lib  : library)
                    (T T' : @CTerm pp)
                    (eq   : per)
                    (A1 A2 : @CTerm pp)
                    (eqa  : per)
                    (c1   : T ===>(lib) (mkc_partial A1))
                    (c2   : T' ===>(lib) (mkc_partial A2))
                    (cla  : close ts lib A1 A2 eqa)
                    (reca : P ts lib A1 A2 eqa)
                    (hv   : forall a, eqa a a -> chaltsc lib a)
                    (eqiff : forall t t', eq t t' <=> per_partial_eq lib eqa t t')
                    (per  : per_partial (close ts) lib T T' eq),
      P ts lib T T' eq)*)

(*  (admiss : forall (ts   : cts)
                   (lib  : library)
                   (T T' : @CTerm pp)
                   (eq   : per)
                   (A1 A2 : @CTerm pp)
                   (eqa  : per)
                   (c1   : T ===>(lib) (mkc_admiss A1))
                   (c2   : T' ===>(lib) (mkc_admiss A2))
                   (cla  : close ts lib A1 A2 eqa)
                   (reca : P ts lib A1 A2 eqa)
                   (eqiff : (forall t t' : CTerm,
                                eq t t' <=>
                                   (t) ===>(lib) (mkc_axiom) # (t') ===>(lib) (mkc_axiom) # admissible_equality eqa))
                   (per : per_admiss (close ts) lib T T' eq),
      P ts lib T T' eq)*)

(*  (mono : forall (ts   : cts)
                 (lib  : library)
                 (T T' : @CTerm pp)
                 (eq   : per)
                 (A1 A2 : @CTerm pp)
                 (eqa : per)
                 (c1 : T ===>(lib) (mkc_mono A1))
                 (c2 : T' ===>(lib) (mkc_mono A2))
                 (cla : close ts lib A1 A2 eqa)
                 (reca : P ts lib A1 A2 eqa)
                 (eqiff : (forall t t' : CTerm,
                              eq t t' <=>
                                 (t) ===>(lib) (mkc_axiom) # (t') ===>(lib) (mkc_axiom) # mono_equality lib eqa))
                 (per : per_mono (close ts) lib T T' eq),
      P ts lib T T' eq)*)

(*  (ffatom : forall (ts   : cts)
                   (lib  : library)
                   (T T' : @CTerm pp)
                   (eq   : per)
                   (A1 A2 x1 x2 a1 a2 : @CTerm pp)
                   (eqa : per)
                   (u : get_patom_set pp)
                   (c1 : T ===>(lib) (mkc_free_from_atom A1 x1 a1))
                   (c2 : T' ===>(lib) (mkc_free_from_atom A2 x2 a2))
                   (cla : close ts lib A1 A2 eqa)
                   (reca : P ts lib A1 A2 eqa)
                   (ex : eqa x1 x2)
                   (ca1 : a1 ===>(lib) (mkc_utoken u))
                   (ca2 : a2 ===>(lib) (mkc_utoken u))
                   (eqiff : eq <=2=> (per_ffatom_eq lib eqa u x1))
                   (per : per_ffatom (close ts) lib T T' eq),
      P ts lib T T' eq)*)

(*  (effatom : forall (ts   : cts)
                    (lib  : library)
                    (T T' : @CTerm pp)
                    (eq   : per)
                    (A1 A2 x1 x2 a1 a2 : @CTerm pp)
                    (eqa : per)
                    (c1 : T ===>(lib) (mkc_efree_from_atom A1 x1 a1))
                    (c2 : T' ===>(lib) (mkc_efree_from_atom A2 x2 a2))
                    (cla : close ts lib A1 A2 eqa)
                    (reca : P ts lib A1 A2 eqa)
                    (niff : name_not_in_upto lib a1 x1 eqa <=> name_not_in_upto lib a2 x2 eqa)
                    (eqiff : eq <=2=> (per_effatom_eq lib eqa a1 x1))
                    (per : per_effatom (close ts) lib T T' eq),
      P ts lib T T' eq)*)

(*  (ffatoms : forall (ts   : cts)
                    (lib  : library)
                    (T T' : @CTerm pp)
                    (eq   : per)
                    (A1 A2 x1 x2 : @CTerm pp)
                    (eqa : per)
                    (c1 : T ===>(lib) (mkc_free_from_atoms A1 x1))
                    (c2 : T' ===>(lib) (mkc_free_from_atoms A2 x2))
                    (cla : close ts lib A1 A2 eqa)
                    (reca : P ts lib A1 A2 eqa)
                    (ex : eqa x1 x2)
                    (eqiff : eq <=2=> (per_ffatoms_eq lib eqa x1))
                    (per : per_ffatoms (close ts) lib T T' eq),
               P ts lib T T' eq)*)

  (ffdefs : forall (ts    : cts)
                   (lib   : library)
                   (T T'  : @CTerm pp)
                   (eq    : per)
                   (A1 A2 : @CTerm pp)
                   (x1 x2 : @CTerm pp)
                   (eqa   : lib-per(lib,pp))
                   (c1    : T ===>(lib) (mkc_free_from_defs A1 x1))
                   (c2    : T' ===>(lib) (mkc_free_from_defs A2 x2))
                   (cla   : in_ext_ext lib (fun lib' x => close ts lib' A1 A2 (eqa lib' x)))
                   (reca  : in_ext_ext lib (fun lib' x => P ts lib' A1 A2 (eqa lib' x)))
                   (ex    : in_ext_ext lib (fun lib' x => eqa lib' x x1 x2))
                   (eqiff : eq <=2=> (per_ffdefs_eq_bar lib eqa x1))
                   (per   : per_ffdefs (close ts) lib T T' eq),
      P ts lib T T' eq)

  (subset : forall (ts   : cts)
                   (lib  : library)
                   (T T' : @CTerm pp)
                   (eq   : per)
                   (A A' : @CTerm pp)
                   (v v' : NVar)
                   (B    : CVTerm [v])
                   (B'   : CVTerm [v'])
                   (eqa  : lib-per(lib,pp))
                   (eqb  : lib-per-fam(lib,eqa,pp))
                   (c1   : T ===>(lib) (mkc_set A v B))
                   (c2   : T' ===>(lib) (mkc_set A' v' B'))
                   (cla  : in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x)))
                   (reca : in_ext_ext lib (fun lib' x => P ts lib' A A' (eqa lib' x)))
                   (clb  : in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e)))
                   (recb : in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), P ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e)))
                   (eqiff : eq <=2=> (per_set_eq_bar lib eqa eqb))
                   (per  : per_set (close ts) lib T T' eq),
              P ts lib T T' eq)

(*  (tunion : forall (ts   : cts)
                   (lib  : library)
                   (T T' : @CTerm pp)
                   (eq   : per)
                   (A A' : @CTerm pp)
                   (v v' : NVar)
                   (B    : CVTerm [v])
                   (B'   : CVTerm [v'])
                   (eqa  : per)
                   (eqb  : forall a a' : CTerm, forall e : eqa a a', per)
                   (c1   : T ===>(lib) (mkc_tunion A v B))
                   (c2   : T' ===>(lib) (mkc_tunion A' v' B'))
                   (cla  : close ts lib A A' eqa)
                   (reca : P ts lib A A' eqa)
                   (clb  : forall a a', forall e : eqa a a', close ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                   (recb : forall a a', forall e : eqa a a', P ts lib (substc a v B) (substc a' v' B') (eqb a a' e))
                   (eqiff : forall t t', eq t t' <=> per_tunion_eq eqa eqb t t')
                   (per : per_tunion (close ts) lib T T' eq),
              P ts lib T T' eq)*)

  (product : forall (ts    : cts)
                    (lib   : library)
                    (T T'  : @CTerm pp)
                    (eq    : per)
                    (A A'  : @CTerm pp)
                    (v v'  : NVar)
                    (B     : CVTerm [v])
                    (B'    : CVTerm [v'])
                    (eqa   : lib-per(lib,pp))
                    (eqb   : lib-per-fam(lib,eqa))
                    (c1    : T ===>(lib) (mkc_product A v B))
                    (c2    : T' ===>(lib) (mkc_product A' v' B'))
                    (cla   : in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x)))
                    (reca  : in_ext_ext lib (fun lib' x => P ts lib' A A' (eqa lib' x)))
                    (clb   : in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e)))
                    (recb  : in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), P ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e)))
                    (eqiff : eq <=2=> (per_product_eq_bar lib eqa eqb))
                    (per   : per_product_bar (close ts) lib T T' eq),
      P ts lib T T' eq)

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
                    (per : per_esquash (close ts) lib T T' eq),
               P ts lib T T' eq)*)
  : forall (ts   : cts)
           (lib  : library)
           (T T' : @CTerm pp)
           (eq   : per)
           (t : close ts lib T T' eq),
    P ts lib T T' eq :=
  fix rec (ts   : cts)
          (lib  : library)
          (T T' : @CTerm pp)
          (eq   : per)
          (t    : close ts lib T T' eq)
         : P ts lib T T' eq :=
   match t in close _ _ _ _ _ return P ts lib T T' eq with
   | CL_init   pts => init   ts lib T T' eq pts

   | CL_bar    pts =>
     let (eqa,  x) := pts in
     let (alla, eqiff) := x in
     pbar ts lib T T' eq
          eqa
          alla
          (fun (lib1 : library) (ext1 : lib_extends lib1 lib) =>
             let (lib2, xx) := alla lib1 ext1 in
             let (ext2, xx) := xx in
             ex_intro
               _
               lib2
               (ex_intro
                  _
                  ext2
                  (fun lib3 (y : lib_extends lib3 lib2) (x : lib_extends lib3 lib) =>
                     rec ts _ T T' (eqa _ x) (xx lib3 y x))))
          eqiff
          pts

   | CL_int    pts => int    ts lib T T' eq pts
   | CL_nat    pts => nat    ts lib T T' eq pts
   | CL_qnat   pts => qnat   ts lib T T' eq pts
   | CL_csname pts => csname ts lib T T' eq pts
   | CL_atom   pts => atom   ts lib T T' eq pts
   | CL_uatom  pts => uatom  ts lib T T' eq pts
   | CL_base   pts => base   ts lib T T' eq pts
   | CL_approx pts => aprx   ts lib T T' eq pts
   | CL_cequiv pts => ceq    ts lib T T' eq pts

(*   | CL_eq pts =>
     let (A,    x) := pts in
     let (B,    x) := x in
     let (a1,   x) := x in
     let (a2,   x) := x in
     let (b1,   x) := x in
     let (b2,   x) := x in
     let (eqa,  x) := x in
     let (x,    eqiff) := x in
     let (bar,  x) := x in
     let (c1,   x) := x in
     let (c2 ,  x) := x in
     let (Ftsa, x) := x in
     let (eqa1, eqa2) := x in
     equ ts lib T T' eq
         bar
         A B a1 a2 b1 b2 eqa
         c1
         c2
         Ftsa
         (fun (lib'  : library)
              (p     : bar_lib_bar bar lib')
              (lib'' : library)
              (i     : lib_extends lib'' lib')
              (x     : lib_extends lib'' lib) =>
            rec ts lib'' A B
                (eqa lib'' x(*(lib_extends_trans i (bar_lib_ext bar lib' p))*))
                (Ftsa lib' p lib'' i x))
         eqa1
         eqa2
         eqiff
         pts*)

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
         equ ts lib T T' eq A B a1 a2 b1 b2 eqa
             cT1
             cT2
             tsa
             (fun lib' x => rec ts lib' A B (eqa lib' x) (tsa lib' x))
             eqa1
             eqa2
             x
             pts

(*   | CL_req pts =>
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
         requ ts lib T T' eq A B a1 a2 b1 b2 eqa
              cT1
              cT2
              tsa
              (rec ts lib A B eqa tsa)
              eo1 eo2
              eqiff
              pts*)

(*   | CL_teq pts =>
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
       tequ ts lib T T' eq a1 a2 b1 b2 eqa
            cT1
            cT2
            ts1
            (rec ts lib a1 b1 eqa ts1)
            ts2
            (rec ts lib a2 b2 eqa ts2)
            ts3
            (rec ts lib a1 a2 eqa ts3)
            eqiff
            pts*)

(*   | CL_isect pts =>
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
         isect ts lib T T' eq A A' v v' B B' eqa eqb
               ctv1
               ctv2
               tsa
               (rec ts lib A A' eqa tsa)
               ftsb
               (fun a a' eqa => rec ts lib
                                    (substc a v B)
                                    (substc a' v' B')
                                    (eqb a a' eqa)
                                    (ftsb a a' eqa))
               teq
               pts*)

   | CL_qtime pts =>
       let (eqa, x) := pts in
       let (A,   x) := x in
       let (B,   x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, eqiff) := x in
         qtime ts lib T T' eq A B eqa
               c1
               c2
               tsa
               (fun (lib' : library) (i : lib_extends lib' lib) =>
                  rec ts lib' A B (eqa lib' i) (tsa lib' i))
               eqiff
               pts

   | CL_func pts =>
       let (eqa, x) := pts in
       let (eqb, x) := x in
       let (tf, eqiff) := x in
       let (A,   x) := tf in
       let (A',  x) := x in
       let (v,   x) := x in
       let (v',  x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, tsb) := x in
         func ts lib T T' eq A A' v v' B B' eqa eqb
              c1
              c2
              tsa
              (fun (lib' : library) (i : lib_extends lib' lib) =>
                 rec ts lib' A A' (eqa lib' i) (tsa lib' i))
              tsb
              (fun (lib' : library) (i : lib_extends lib' lib)
                   a a' (e : eqa lib' i a a') =>
                 rec ts lib'
                     (substc a v B)
                     (substc a' v' B')
                     (eqb lib' i a a' e)
                     (tsb lib' i a a' e))
              eqiff
              pts

(*   | CL_func pts =>
       let (eqa, x) := pts in
       let (eqb, x) := x in
       let (tf, eqiff) := x in
       let (A,   x) := tf in
       let (A',  x) := x in
       let (v,   x) := x in
       let (v',  x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, tsb) := x in
         func ts lib T T' eq A A' v v' B B' eqa eqb
              c1
              c2
              tsa
              (rec ts lib A A' eqa tsa)
              tsb
              (fun a a' (e : eqa a a') =>
                 rec ts lib
                     (substc a v B)
                     (substc a' v' B')
                     (eqb a a' e)
                     (tsb a a' e))
              eqiff
              pts*)

(*   | CL_disect pts =>
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
         disect ts lib T T' eq A A' v v' B B' eqa eqb
                ctv1
                ctv2
                tsa
                (rec ts lib A A' eqa tsa)
                ftsb
                (fun a a' eqa => rec ts lib
                                     (substc a v B)
                                     (substc a' v' B')
                                     (eqb a a' eqa)
                                     (ftsb a a' eqa))
                teq
                pts*)

(*   | CL_pertype pts =>
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
       pertype ts lib T T' eq R1 R2 eq1 eq2
               c1
               c2
               F1
               (fun x y => rec ts lib
                               (mkc_apply2 R1 x y)
                               (mkc_apply2 R1 x y)
                               (eq1 x y)
                               (F1 x y))
               F2
               (fun x y => rec ts lib
                               (mkc_apply2 R2 x y)
                               (mkc_apply2 R2 x y)
                               (eq2 x y)
                               (F2 x y))
               inh
               isp
               eqt
               pts*)

(*   | CL_ipertype pts =>
     let (R1,  x) := pts in
     let (R2,  x) := x in
     let (eq1, x) := x in
     let (c1,  x) := x in
     let (c2,  x) := x in
     let (F1,  x) := x in
     let (isp, eqt)  := x in
     ipertype ts lib T T' eq R1 R2 eq1
              c1
              c2
              F1
              (fun x y => rec ts lib
                              (mkc_apply2 R1 x y)
                              (mkc_apply2 R2 x y)
                              (eq1 x y)
                              (F1 x y))
              isp
              eqt
              pts*)

(*   | CL_spertype pts =>
     let (R1,  x) := pts in
     let (R2,  x) := x in
     let (eq1, x) := x in
     let (c1,  x) := x in
     let (c2,  x) := x in
     let (F1,  x) := x in
     let (F2,  x) := x in
     let (F3,  x) := x in
     let (isp, eqt)  := x in
     spertype ts lib T T' eq R1 R2 eq1
              c1
              c2
              F1
              (fun x y =>
                 rec ts lib
                     (mkc_apply2 R1 x y)
                     (mkc_apply2 R2 x y)
                     (eq1 x y)
                     (F1 x y))
              F2
              (fun x y z inh =>
                 rec ts lib
                     (mkc_apply2 R1 x y)
                     (mkc_apply2 R1 z y)
                     (eq1 x y)
                     (F2 x y z inh))
              F3
              (fun x y z inh =>
                 rec ts lib
                     (mkc_apply2 R1 x y)
                     (mkc_apply2 R1 x z)
                     (eq1 x y)
                     (F3 x y z inh))
              isp
              eqt
              pts*)

(*   | CL_w pts =>
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
       w ts lib T T' eq A A' v v' B B' eqa eqb
         c1
         c2
         tsa
         (rec ts lib A A' eqa tsa)
         tsb
         (fun a a' eqa =>
            rec ts lib
                (substc a v B)
                (substc a' v' B')
                (eqb a a' eqa)
                (tsb a a' eqa))
         teq
         pts*)

(*   | CL_m pts =>
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
     m ts lib T T' eq A A' v v' B B' eqa eqb
       c1
       c2
       tsa
       (rec ts lib A A' eqa tsa)
       tsb
       (fun a a' eqa =>
          rec ts lib
              (substc a v B)
              (substc a' v' B')
              (eqb a a' eqa)
              (tsb a a' eqa))
       teq
       pts*)

(*   | CL_pw pts =>
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
     pw ts lib T T' eq
        Pr Pr'
        ap ap' A A'
        bp bp' ba ba' B B'
        cp cp' ca ca' cb cb' C C'
        p p'
        eqp eqa eqb
        c1 c2
        tsp
        (rec ts lib Pr Pr' eqp tsp)
        tsa
        (fun p p' eqp =>
           rec ts lib
               (substc p ap A)
               (substc p' ap' A')
               (eqa p p' eqp)
               (tsa p p' eqp))
        tsb
        (fun p p' eqp a a' eqa =>
           rec ts lib
               (lsubstc2 bp p ba a B)
               (lsubstc2 bp' p' ba' a' B')
               (eqb p p' eqp a a' eqa)
               (tsb p p' eqp a a' eqa))
        tsc
        peq
        teq
        pts*)

(*   | CL_pm pts =>
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
         pm ts lib T T' eq
            Pr Pr'
            ap ap' A A'
            bp bp' ba ba' B B'
            cp cp' ca ca' cb cb' C C'
            p p'
            eqp eqa eqb
            c1 c2
            tsp
            (rec ts lib Pr Pr' eqp tsp)
            tsa
            (fun p p' eqp =>
               rec ts lib
                   (substc p ap A)
                   (substc p' ap' A')
                   (eqa p p' eqp)
                   (tsa p p' eqp))
            tsb
            (fun p p' eqp a a' eqa =>
               rec ts lib
                   (lsubstc2 bp p ba a B)
                   (lsubstc2 bp' p' ba' a' B')
                   (eqb p p' eqp a a' eqa)
                   (tsb p p' eqp a a' eqa))
            tsc
            peq
            teq
            pts*)

(*   | CL_texc pts =>
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
         texc ts lib T T' eq N N' E E' eqn eqe
              c1
              c2
              tsn
              (rec ts lib N N' eqn tsn)
              tse
              (rec ts lib E E' eqe tse)
              eqiff
              pts*)

(*   | CL_union pts =>
       let (eqa, x) := pts in
       let (eqb, x) := x in
       let (A,   x) := x in
       let (A',  x) := x in
       let (B,   x) := x in
       let (B',  x) := x in
       let (x,   eqiff) := x in
       let (bar, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (tsa, tsb) := x in
       union ts lib T T' eq bar
             A A' B B' eqa eqb
             c1
             c2
             tsa
             (fun (lib' : library) (p : bar_lib_bar bar lib') (lib'' : library) (i : lib_extends lib'' lib') x =>
                rec ts lib'' A A' (eqa lib'' x) (tsa lib' p lib'' i x))
             tsb
             (fun (lib' : library) (p : bar_lib_bar bar lib') (lib'' : library) (i : lib_extends lib'' lib') x =>
                rec ts lib'' B B' (eqb lib'' x) (tsb lib' p lib'' i x))
             eqiff
             pts*)

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
       union ts lib T T' eq
             A A' B B' eqa eqb
             c1
             c2
             tsa
             (fun lib' x => rec ts lib' A A' (eqa lib' x) (tsa lib' x))
             tsb
             (fun lib' x => rec ts lib' B B' (eqb lib' x) (tsb lib' x))
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
         image ts lib T T' eq A A' f f' eqa
               c1
               c2
               tsa
               (fun lib' x => rec ts lib' A A' (eqa lib' x) (tsa lib' x))
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

(*   | CL_partial pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (eqa, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, x) := x in
       let (hv,  eqt) := x in
       partial ts lib T T' eq A1 A2 eqa
               c1
               c2
               cla
               (rec ts lib A1 A2 eqa cla)
               hv
               eqt
               pts*)

(*   | CL_admiss pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (eqa, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, eqt) := x in
       admiss ts lib T T' eq A1 A2 eqa
              c1
              c2
              cla
              (rec ts lib A1 A2 eqa cla)
              eqt
              pts*)

(*   | CL_mono pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (eqa, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, eqt) := x in
       mono ts lib T T' eq A1 A2 eqa
            c1
            c2
            cla
            (rec ts lib A1 A2 eqa cla)
            eqt
            pts*)

(*   | CL_ffatom pts =>
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
       ffatom ts lib T T' eq A1 A2 x1 x2 a1 a2 eqa u
              c1
              c2
              cla
              (rec ts lib A1 A2 eqa cla)
              ex ca1 ca2
              eqt
              pts*)

(*   | CL_effatom pts =>
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
       effatom ts lib T T' eq A1 A2 x1 x2 a1 a2 eqa
               c1
               c2
               cla
               (rec ts lib A1 A2 eqa cla)
               ni
               eqt
               pts*)

(*   | CL_ffatoms pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (x1,  x) := x in
       let (x2,  x) := x in
       let (eqa, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, x) := x in
       let (ex,  eqt) := x in
       ffatoms ts lib T T' eq A1 A2 x1 x2 eqa
               c1
               c2
               cla
               (rec ts lib A1 A2 eqa cla)
               ex
               eqt
               pts*)

   | CL_ffdefs pts =>
       let (A1,  x) := pts in
       let (A2,  x) := x in
       let (x1,  x) := x in
       let (x2,  x) := x in
       let (eqa, x) := x in
       let (c1,  x) := x in
       let (c2,  x) := x in
       let (cla, x) := x in
       let (ex,  eqt) := x in
       ffdefs ts lib T T' eq A1 A2 x1 x2 eqa
              c1
              c2
              cla
              (fun lib' x => rec ts lib' A1 A2 (eqa lib' x) (cla lib' x))
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
       subset ts lib T T' eq A A' v v' B B' eqa eqb
              c1
              c2
              tsa
              (fun lib' (i : lib_extends lib' lib) => rec ts lib' A A' (eqa lib' i) (tsa lib' i))
              tsb
              (fun lib' (i : lib_extends lib' lib)  a a' (e : eqa lib' i a a') =>
                 rec ts lib'
                     (substc a v B)
                     (substc a' v' B')
                     (eqb lib' i a a' e)
                     (tsb lib' i a a' e))
              teq
              pts

(*   | CL_tunion pts =>
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
       tunion ts lib T T' eq A A' v v' B B' eqa eqb
              c1
              c2
              tsa
              (rec ts lib A A' eqa tsa)
              tsb
              (fun a a' eqa =>
                 rec ts lib
                     (substc a v B)
                     (substc a' v' B')
                     (eqb a a' eqa)
                     (tsb a a' eqa))
              teq
              pts*)

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
       product ts lib T T' eq A A' v v' B B' eqa eqb
               c1
               c2
               tsa
               (fun (lib' : library) (i : lib_extends lib' lib) =>
                  rec ts lib' A A' (eqa lib' i) (tsa lib' i))
               tsb
               (fun (lib' : library) (i : lib_extends lib' lib)
                    a a' (e : eqa lib' i a a') =>
                  rec ts lib'
                      (substc a v B)
                      (substc a' v' B')
                      (eqb lib' i a a' e)
                      (tsb lib' i a a' e))
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
    | [ H : per_int         _ _ _ _ _ |- _ ] => unfold per_int         in H; exrepd
    | [ H : per_int_bar     _ _ _ _ _ |- _ ] => unfold per_int_bar     in H; exrepd
    | [ H : per_bar         _ _ _ _ _ |- _ ] => unfold per_bar         in H; exrepd
    | [ H : per_nat         _ _ _ _ _ |- _ ] => unfold per_nat         in H; exrepd
    | [ H : per_nat_bar     _ _ _ _ _ |- _ ] => unfold per_nat_bar     in H; exrepd
    | [ H : per_qnat        _ _ _ _ _ |- _ ] => unfold per_qnat        in H; exrepd
    | [ H : per_qnat_bar    _ _ _ _ _ |- _ ] => unfold per_qnat_bar    in H; exrepd
    | [ H : per_csname      _ _ _ _ _ |- _ ] => unfold per_csname      in H; exrepd
    | [ H : per_csname_bar  _ _ _ _ _ |- _ ] => unfold per_csname_bar  in H; exrepd
    | [ H : per_atom        _ _ _ _ _ |- _ ] => unfold per_atom        in H; exrepd
    | [ H : per_atom_bar    _ _ _ _ _ |- _ ] => unfold per_atom_bar    in H; exrepd
    | [ H : per_uatom       _ _ _ _ _ |- _ ] => unfold per_uatom       in H; exrepd
    | [ H : per_uatom_bar   _ _ _ _ _ |- _ ] => unfold per_uatom_bar   in H; exrepd
    | [ H : per_base        _ _ _ _ _ |- _ ] => unfold per_base        in H; exrepd
    | [ H : per_base_bar    _ _ _ _ _ |- _ ] => unfold per_base_bar    in H; exrepd
    | [ H : per_approx      _ _ _ _ _ |- _ ] => unfold per_approx      in H; exrepd
    | [ H : per_approx_bar  _ _ _ _ _ |- _ ] => unfold per_approx_bar  in H; exrepd
    | [ H : per_cequiv      _ _ _ _ _ |- _ ] => unfold per_cequiv      in H; exrepd
    | [ H : per_cequiv_bar  _ _ _ _ _ |- _ ] => unfold per_cequiv_bar  in H; exrepd
    | [ H : per_eq          _ _ _ _ _ |- _ ] => unfold per_eq          in H; exrepd
    | [ H : per_eq_bar      _ _ _ _ _ |- _ ] => unfold per_eq_bar      in H; exrepd
    | [ H : per_req         _ _ _ _ _ |- _ ] => unfold per_req         in H; exrepd
    | [ H : per_teq         _ _ _ _ _ |- _ ] => unfold per_teq         in H; exrepd
    | [ H : per_isect       _ _ _ _ _ |- _ ] => unfold per_isect       in H; exrepd
    | [ H : per_qtime       _ _ _ _ _ |- _ ] => unfold per_qtime       in H; exrepd
    | [ H : per_func        _ _ _ _ _ |- _ ] => unfold per_func        in H; exrepd
    | [ H : per_func_ext    _ _ _ _ _ |- _ ] => unfold per_func_ext    in H; exrepd
    | [ H : per_disect      _ _ _ _ _ |- _ ] => unfold per_disect      in H; exrepd
    | [ H : per_pertype     _ _ _ _ _ |- _ ] => unfold per_pertype     in H; exrepd
    | [ H : per_ipertype    _ _ _ _ _ |- _ ] => unfold per_ipertype    in H; exrepd
    | [ H : per_spertype    _ _ _ _ _ |- _ ] => unfold per_spertype    in H; exrepd
    | [ H : per_w           _ _ _ _ _ |- _ ] => unfold per_w           in H; exrepd
    | [ H : per_m           _ _ _ _ _ |- _ ] => unfold per_m           in H; exrepd
    | [ H : per_pw          _ _ _ _ _ |- _ ] => unfold per_pw          in H; exrepd
    | [ H : per_pm          _ _ _ _ _ |- _ ] => unfold per_pm          in H; exrepd
    | [ H : per_texc        _ _ _ _ _ |- _ ] => unfold per_texc        in H; exrepd
    | [ H : per_union       _ _ _ _ _ |- _ ] => unfold per_union       in H; exrepd
    | [ H : per_image       _ _ _ _ _ |- _ ] => unfold per_image       in H; exrepd
    | [ H : per_eisect      _ _ _ _ _ |- _ ] => unfold per_eisect      in H; exrepd
    | [ H : per_partial     _ _ _ _ _ |- _ ] => unfold per_partial     in H; exrepd
    | [ H : per_admiss      _ _ _ _ _ |- _ ] => unfold per_admiss      in H; exrepd
    | [ H : per_mono        _ _ _ _ _ |- _ ] => unfold per_mono        in H; exrepd
    | [ H : per_ffatom      _ _ _ _ _ |- _ ] => unfold per_ffatom      in H; exrepd
    | [ H : per_effatom     _ _ _ _ _ |- _ ] => unfold per_effatom     in H; exrepd
    | [ H : per_ffatoms     _ _ _ _ _ |- _ ] => unfold per_ffatoms     in H; exrepd
    | [ H : per_ffdefs      _ _ _ _ _ |- _ ] => unfold per_ffdefs      in H; exrepd
    | [ H : per_set         _ _ _ _ _ |- _ ] => unfold per_set         in H; exrepd
    | [ H : per_tunion      _ _ _ _ _ |- _ ] => unfold per_tunion      in H; exrepd
    | [ H : per_product     _ _ _ _ _ |- _ ] => unfold per_product     in H; exrepd
    | [ H : per_product_bar _ _ _ _ _ |- _ ] => unfold per_product_bar in H; exrepd
    | [ H : type_family     _ _ _ _ _ _ _ |- _ ] => unfold type_family in H; exrepd
    | [ H : type_family_ext _ _ _ _ _ _ _ |- _ ] => unfold type_family_ext in H; exrepd
    | [ H : etype_family    _ _ _ _ _ _ _ |- _ ] => unfold etype_family in H; exrepd
    | [ H : type_pfamily    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => unfold type_pfamily in H; exrepd
  end.
(*    | [ H : per_eunion   _ _ _ _ _ |- _ ] => unfold per_eunion     in H; exrepd
    | [ H : per_union2   _ _ _ _ _ |- _ ] => unfold per_union2     in H; exrepd*)
(*    | [ H : per_esquash  _ _ _ _ _ |- _ ] => unfold per_esquash    in H; exrepd*)

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

Definition per_approx_eq_bar_lib_per {o}
           (lib : @library o)
           (a b: @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => per_approx_eq_bar lib' a b).
  introv x y; introv; tcsp.
Defined.

Definition per_cequiv_eq_bar_lib_per {o}
           (lib : @library o)
           (a b: @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => per_cequiv_eq_bar lib' a b).
  introv x y; introv; tcsp.
Defined.

Definition equality_of_nat_bar_lib_per {o}
           (lib : @library o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => equality_of_nat_bar lib').
  introv x y; tcsp.
Defined.

Definition equality_of_qnat_bar_lib_per {o}
           (lib : @library o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => equality_of_qnat_bar lib').
  introv x y; tcsp.
Defined.

Definition equality_of_int_bar_lib_per {o}
           (lib : @library o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => equality_of_int_bar lib').
  introv x y; tcsp.
Defined.

Definition equality_of_csname_bar_lib_per {o}
           (lib : @library o) (n : nat) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => equality_of_csname_bar lib' n).
  introv x y; tcsp.
Defined.

Definition equality_of_atom_bar_lib_per {o}
           (lib : @library o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => equality_of_atom_bar lib').
  introv x y; tcsp.
Defined.

Definition equality_of_uatom_bar_lib_per {o}
           (lib : @library o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => equality_of_uatom_bar lib').
  introv x y; tcsp.
Defined.

Definition per_base_eq_lib_per {o}
           (lib : @library o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => per_base_eq lib').
  introv x y; tcsp.
Defined.
