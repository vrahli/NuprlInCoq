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


Require Export per.
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ #⪯# *)
(** printing ~=~  $\sim$ #~# *)
(** printing ===>  $\Downarrow$ #⇓# *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)
(** printing mkc_uni $\mathbb{U}$ *)
(* begin hide *)



(** Empty candidate type system *)
Definition cts_bot {p} (T T' : @CTerm p) (eq : @CTerm p -> @CTerm p -> Type) : Set := False.

Definition univ_def {p}
           lib
           (ts : cts)
           (uni T T' : @cterm p)
           (eq : per) : [U] :=
     (T ===>(lib) uni
     # T' ===>(lib) uni
     # forall A A',
         eq A A' <=> {eqa : per , close lib ts A A' eqa})
    {+} ts T T' eq.

Definition univ0 {p} (lib : @library p) (T T' : @cterm p) (eq : per(p)) := False.
Definition univ1 {p} lib (T T' : @cterm p) eq := close lib (univ_def lib (univ0 lib) (mkcn_uni 0)) T T' eq.
Definition univ2 {p} lib (T T' : @cterm p) eq := close lib (univ_def lib (univ1 lib) (mkcn_uni 1)) T T' eq.
Definition univ3 {p} lib (T T' : @cterm p) eq := close lib (univ_def lib (univ2 lib) (mkcn_uni 2)) T T' eq.

Definition univ' {p} lib (T T' : @cterm p) eq :=
  univ0 lib T T' eq [+] univ1 lib T T' eq [+] univ2 lib T T' eq [+] univ3 lib T T' eq.

(* end hide *)

(**

  We now define Nuprl's universes of types, the Nuprl type system
  and various useful abstractions such as the equality
  meta-theoretical relation which expresses when two terms are equal
  in a type.

 *)


(**

  [univi i] is a candidate type system that contains all the types at
  level i.  [univi 0] is the empty type system.  [univi 1] contains
  all the types that do not mention universes.  [univi 2] contains all
  the types of [univi 1] plus all the types that mention universes no
  higher than [mkc_uni 0]%\dots%.  Two types [A] and [A'] are equal in
  a universe at level [S i] if there exists an equality [eqa] such
  that [A] and [A'] are equal with PER [eqa] in the closed type system
  [close (univi i)].  For simplicity, the universe [univi (S i)] is
  denoted by [mkc_uni i].

 *)

Fixpoint univi {p} lib (i : nat) (T T' : @cterm p) (eq : per(p)) : [U] :=
  match i with
  | 0 => False
  | S n =>
    (T ===>(lib) (mkcn_uni n)
     # T' ===>(lib) (mkcn_uni n)
     # forall A A',
         eq A A' <=> {eqa : per , close lib (univi lib n) A A' eqa})
    {+} univi lib n T T' eq
  end.

(**

  Even though we can define [univi] in [Type] as a fixpoint, this
  definition is not useful to define more than one universe.  As a
  matter of fact, we can prove prove that [mkc_uni 0] is a member of
  [mkc_uni 1], but we cannot prove that [mkc_uni i] is a member of
  [mkc_uni (S i)] when [i] is greater than [0].  Intuitively this is
  because we cannot fit all the universes of Nuprl into one universe
  of Coq, and [univi i] cannot be at different levels for different
  [i]s.

  More precisely, the problem in [univi (S i)]'s definition is that if
  [eqa] is a relation at the Coq level $l$ then [univi (S i)] is at
  least at level $l+1$, and in general to be able to prove the double
  implication, [eq] must also be at level $l+1$.  However, because
  [eqa] is at level $l$, in the recursive call, in the case where
  [close (univi i) A A' eqa] is [univi i A A' eqa], we end up having
  to prove that our relation at level $l$ is equivalent to a relation
  at level $l+1$, which in general is not possible.

  One alternative approach is to put [univi] in Prop instead of
  [Type].  Another approach is to define instead a finite number of
  universes and add more as needed.

*)

(* begin hide *)

(*
Set Printing Universes.
Print close.
Print univi.
Print Universes.
Check (fun T T' => univi 1 T T' (fun A A' => {eqa : per & close (univi 0) A A' eqa})).
*)


Lemma univi_mkc_uni {p} :
  forall lib (i : nat),
    univi lib
          (S i)
          (mkcn_uni i)
          (mkcn_uni i)
          (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}).
Proof.
  intros.
  simpl.
  left.
  dands; try (spcast; apply computes_to_valcn_refl; eauto 3 with slow).
  sp.
Qed.

Lemma univi_exists {p} :
  forall lib i (T T' : @cterm p) eq,
    univi lib i T T' eq
    -> {j : nat
        , j < i
         # T ===>(lib) (mkcn_uni j)
         # T' ===>(lib) (mkcn_uni j)
         # forall A A',
              eq A A' <=> {eqa : per , close lib (univi lib j) A A' eqa}}.
Proof.
  induction i; simpl; sp.
  exists i; sp; omega.
  discover; sp.
  exists j; sp; omega.
Qed.

Lemma univi_exists_iff {p} :
  forall lib i (T T' : @cterm p) eq,
    univi lib i T T' eq
    <=> {j : nat
          , j < i
          # T ===>(lib) (mkcn_uni j)
          # T' ===>(lib) (mkcn_uni j)
          # forall A A',
               eq A A' <=> {eqa : per , close lib (univi lib j) A A' eqa}}.
Proof.
  sp; split; intro k.
  apply univi_exists; auto.
  revert T T' eq k.
  induction i; simpl; sp.
  destruct (eq_nat_dec j i); subst; sp.
  right.
  apply IHi with (T := T) (T' := T') (eq := eq); sp.
  exists j; sp; omega.
Qed.


Definition nuprli {p} lib (i : nat) := @close p lib (univi lib i).

Lemma fold_nuprli {p} :
  forall lib i, close lib (univi lib i) = @nuprli p lib i.
Proof.
  sp.
Qed.

(*
(*Polymorphic*) Definition univ (T T' : cterm) (eq : per) :=
  {n : nat
    & computes_to_valc T (mkcn_uni n)
    # computes_to_valc T' (mkcn_uni n)
    # forall A A',
         eq A A' <=> {eqa : per & nuprli n A A' eqa}}.
*)

(* end hide *)

(**

  The [univ] operator is a candidate type system that contains all the
  universes.

 *)

Definition univ {p} lib (T T' : @cterm p) (eq : per) :=
  {i : nat , univi lib i T T' eq}.

(**

  We say that a candidate type system defines only universes if all
  its types are of the forms [mkcn_uni i].  For example, we can prove
  that [univ] defines only universes.

*)

Definition defines_only_universes {p} lib (ts : cts(p)) :=
  forall T eq, ts T T eq -> {i : nat , T ===>(lib) (mkcn_uni i)}.

(* begin hide *)

Lemma univi_iff_univ {p} :
  forall lib (a b : @cterm p) eq,
    univ lib a b eq <=> {i : nat , univi lib i a b eq}.
Proof.
  sp; split; sp.
Qed.

(* end hide *)

(**

  Finally, the Nuprl type system is defined by closing the [univ]
  candidate type system.

 *)

Definition nuprl {p} lib := @close p lib (univ lib).

(* begin hide *)


(* ============ Extension of the type system with a new universe of types ============ *)
Inductive closep {p} lib (ts : cts) (T T' : @cterm p) (eq : per) : [U] :=
  | CLp_init    : ts T T' eq -> closep lib ts T T' eq
  | CLp_int     : per_int     lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_base    : per_base    lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_sqle    : per_approx  lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_sqeq    : per_cequiv  lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_eq      : per_eq      lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_isect   : per_isect   lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_func    : per_func    lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_disect  : per_disect  lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_pertype : per_pertype lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_w       : per_w       lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_m       : per_m       lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_pw      : per_pw      lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_pm      : per_pm      lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_union   : per_union   lib (closep lib ts) T T' eq -> closep lib ts T T' eq
  | CLp_image   : per_image   lib (closep lib ts) T T' eq -> closep lib ts T T' eq
(*  | CLp_compute : per_compute lib (closep lib ts) T T' eq -> closep lib ts T T' eq*).
Hint Constructors closep.

Fixpoint univip {p} lib (i : nat) (T T' : @cterm p) (eq : per(p)) : [U] :=
  match i with
  | 0 => False
  | S n =>
    (T ===>(lib) (mkcn_uni n)
     # T' ===>(lib) (mkcn_uni n)
     # forall A A',
         eq A A' <=> {eqa : per , closep lib (univip lib n) A A' eqa})
    {+} univip lib n T T' eq
  end.

Definition univp {p} lib (T T' : @cterm p) (eq : per) :=
  {i : nat , univip lib i T T' eq}.

Definition nuprlp {p} lib := @closep p lib (univp lib).

Definition Nuprl {p} lib (T T' : @cterm p) (eq : per) :=
  nuprl lib T T' eq [+] univp lib T T' eq.
(* ==================================================================================*)


Lemma typable_in_higher_univ {pp} :
  forall lib i (T T' : @cterm pp) eq,
    nuprli lib i T T' eq
    -> forall k, nuprli lib (k + i) T T' eq.
Proof.
  unfold nuprli; introv cl; induction k; simpl; sp.

  remember (univi lib (k + i)) as u; revert Hequ.
  clear cl.
  close_cases (induction IHk using @close_ind') Case; sp; subst.

  - Case "CL_eq".
    apply CL_eq; unfold per_eq; sp.
    exists A B a1 a2 b1 b2 eqa; sp.

  - Case "CL_req".
    apply CL_req; unfold per_req; sp.
    exists A B a1 a2 b1 b2 eqa; sp.

  - Case "CL_teq".
    apply CL_teq; unfold per_teq; sp.
    exists a1 a2 b1 b2 eqa; sp.

  - Case "CL_isect".
    apply CL_isect; unfold per_isect; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_func".
    apply CL_func; unfold per_func; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_disect".
    apply CL_disect; unfold per_disect; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_pertype".
    apply CL_pertype; unfold per_pertype; sp.
    exists R1 R2 eq1 eq2; sp.

  - Case "CL_ipertype".
    apply CL_ipertype; unfold per_ipertype; sp.
    exists R1 R2 eq1; sp.

  - Case "CL_spertype".
    apply CL_spertype; unfold per_spertype; sp.
    exists R1 R2 eq1; sp.

  - Case "CL_w".
    apply CL_w; unfold per_w; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_m".
    apply CL_m; unfold per_m; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_pw".
    apply CL_pw; unfold per_pw; sp.
    exists eqp eqa eqb p p' cp cp' ca ca'.
    exists cb cb' C C'; sp.
    unfold type_pfamily.
    exists Pr Pr' ap ap' A A' bp bp'.
    exists ba ba' B B'; sp.

  - Case "CL_pm".
    apply CL_pm; unfold per_pm; sp.
    exists eqp eqa eqb p p' cp cp' ca ca'.
    exists cb cb' C C'; sp.
    unfold type_pfamily.
    exists Pr Pr' ap ap' A A' bp bp'.
    exists ba ba' B B'; sp.

  - Case "CL_texc".
    apply CL_texc; unfold per_texc; sp.
    exists eqn eqe N N' E E'; sp.

  - Case "CL_union".
    apply CL_union; unfold per_union; sp.
    exists eqa eqb A A' B B'; sp.

    (*
  - Case "CL_eunion".
    apply CL_eunion; unfold per_eunion; sp.
    exists eqa1 eqa2 eqb1 eqb2 A A' B B'; sp.
     *)

  - Case "CL_image".
    apply CL_image; unfold per_image; sp.
    exists eqa A A' f f'; sp.

(*
  - Case "CL_eisect".
    apply CL_eisect; unfold per_eisect; sp.
    exists eqa eqa' eqb; sp.
    exists A A' v v' B B'.
    exists f g f' g'; sp.
*)

  - Case "CL_partial".
    apply CL_partial; unfold per_partial; sp.
    exists A1 A2 eqa; sp.

  - Case "CL_admiss".
    apply CL_admiss; unfold per_partial; sp.
    exists A1 A2 eqa; sp.

  - Case "CL_mono".
    apply CL_mono; unfold per_partial; sp.
    exists A1 A2 eqa; sp.

(*  - Case "CL_ffatom".
    apply CL_ffatom; unfold per_ffatom; sp.
    exists A1 A2 x1 x2 a1 a2 eqa u; sp.*)

(*  - Case "CL_effatom".
    apply CL_effatom; unfold per_effatom; sp.
    exists A1 A2 x1 x2 a1 a2 eqa; sp.*)

(*  - Case "CL_ffatoms".
    apply CL_ffatoms; unfold per_ffatoms; sp.
    exists A1 A2 x1 x2 eqa; sp.*)

  - Case "CL_set".
    apply CL_set; unfold per_set; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_tunion".
    apply CL_tunion; unfold per_tunion; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.

  - Case "CL_product".
    apply CL_product; unfold per_product; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.
Qed.

Lemma typable_in_higher_univ_r {p} :
  forall lib i (T T' : @cterm p) eq,
    nuprli lib i T T' eq
    -> forall k, nuprli lib (i + k) T T' eq.
Proof.
  unfold nuprli; introv n; sp.
  generalize (typable_in_higher_univ lib i T T' eq n k); sp.
  assert (k + i = i + k) as e by omega.
  rww e; sp.
Qed.

Lemma minus_plus_n :
  forall n k : nat,
    n <= k -> (k - n) + n = k.
Proof.
  induction n; simpl; sp.
  omega.
  destruct k; simpl; sp.
  omega.
  rw <- plus_n_Sm.
  rw IHn; sp; omega.
Qed.

Lemma typable_in_higher_univ_max {p} :
  forall lib i1 i2 (A1 B1 A2 B2 : @cterm p) eq1 eq2,
    nuprli lib i1 A1 B1 eq1
    -> nuprli lib i2 A2 B2 eq2
    -> nuprli lib (Peano.max i1 i2) A1 B1 eq1
       # nuprli lib (Peano.max i1 i2) A2 B2 eq2.
Proof.
  introv n1 n2.
  generalize (typable_in_higher_univ
                lib i1 A1 B1 eq1 n1 ((Peano.max i1 i2) - i1));
    intro k1.
  generalize (typable_in_higher_univ
                lib i2 A2 B2 eq2 n2 ((Peano.max i1 i2) - i2));
    intro k2.
  assert (((Peano.max i1 i2) - i1) + i1 = Peano.max i1 i2) as max1.
  apply minus_plus_n; sp.
  apply max_prop1.
  assert (((Peano.max i1 i2) - i2) + i2 = Peano.max i1 i2) as max2.
  apply minus_plus_n; sp.
  apply max_prop2.
  rw max1 in k1.
  rw max2 in k2.
  sp.
Qed.

Lemma uni_in_higher_univ {p} :
  forall lib i (T T' : @cterm p) eq,
    univi lib i T T' eq
    -> forall k, univi lib (k + i) T T' eq.
Proof.
  induction k; simpl; sp.
Qed.

Lemma uni_in_higher_univ_r {p} :
  forall lib i (T T' : @cterm p) eq,
    univi lib i T T' eq
    -> forall k, univi lib (i + k) T T' eq.
Proof.
  introv u; sp.
  generalize (uni_in_higher_univ lib i T T' eq u k); sp.
  assert (k + i = i + k) as e by omega.
  rww e; sp.
Qed.

(*
Definition Nuprl T T' eq := {n : nat & Nuprli n T T' eq}.
*)

(*
Lemma univi_implies_univ :
  forall i a b eq,
    univi i a b eq
    -> univ a b eq.
Proof.
  induction i; simpl; sp.
  unfold univ.
  exists i; sp.
Qed.
*)

(*
(*Error: Universe inconsistency.*)

Lemma mkcn_uni_in_nuprl :
  forall i : nat,
    nuprl (mkcn_uni i)
          (mkcn_uni i)
          (fun A A' => {eqa : per & close (univi i) A A' eqa}).
Proof.
  intro.
  apply CL_init.
  exists (S i); simpl.
  left; sp; apply computes_to_valc_refl; sp.
Qed.

Lemma nuprl_mkcn_uni :
  forall i : nat,
    {eq : per & nuprl (mkcn_uni i) (mkcn_uni i) eq}.
Proof.
  intros.
  exists (fun A A' => {eqa : per & close (univi i) A A' eqa}).
  apply mkcn_uni_in_nuprl.
Qed.
*)

(*
Lemma univ_exists :
  forall T T' eq,
    univ T T' eq -> {i : nat & univi i T T' eq}.
Proof.
  unfold univ; sp.
  exists (S n).
  apply univi_exists_iff.
  exists n; sp; omega.
Qed.
*)

(*
Lemma univ_type_system : type_system univ.
Proof.
  unfold type_system; sp.

  - unfold uniquely_valued, eq_term_equals; sp.
    allunfold univ; sp.
    computes_to_eqval.
    trewrite p0 t1 t2; trewrite p t1 t2; split; sp.

  - unfold type_extensionality; sp.
    allunfold univ; sp.
    exists n; sp.
    trewrite <- p A A'.
    symm; sp.

  - unfold type_symmetric; sp.
    allunfold univ; sp.
    exists n; sp.

  - unfold type_transitive; sp.
    allunfold univ; sp.
    computes_to_eqval.
    exists n0; sp.

  - unfold type_value_respecting; sp.
    allunfold univ; sp.
    exists n; sp.
    apply cequivc_uni with (t := T); auto.

  - unfold term_symmetric, term_equality_symmetric; sp.
    allunfold univ; sp.
    apply p in X0; sp.
    apply p.
    exists eqa; auto.
    generalize (nuprli_type_system n); sp.
    inversion X; sp.

  - unfold term_transitive, term_equality_transitive; sp.
    allunfold univ; sp.
    apply p in X0; apply p in X1; sp; apply p.
    generalize (nuprli_type_system n); sp.
    inversion X; sp.
    exists eqa.
    apply uniquely_valued_trans4 with (T2 := t2) (eq1 := eqa0); sp.

  - unfold term_value_respecting, term_equality_respecting; sp.
    allunfold univ; sp.
    apply p in X0; sp; apply p.
    exists eqa.
    generalize (nuprli_type_system n); sp.
    inversion X; sp.
Qed.
*)

Lemma nuprli_implies_nuprl {pp} :
  forall lib (a b : @cterm pp) i eq,
    nuprli lib i a b eq
    -> nuprl lib a b eq.
Proof.
  unfold nuprli, nuprl; introv n.
  remember (univi lib i) as k.
  revert i Heqk.
  close_cases (induction n using @close_ind') Case; sp; subst.

  - Case "CL_init".
    apply CL_init.
    exists i; sp.

  - Case "CL_eq".
    apply CL_eq.
    unfold per_eq; sp.
    exists A B a1 a2 b1 b2 eqa; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_req".
    apply CL_req.
    unfold per_req; sp.
    exists A B a1 a2 b1 b2 eqa; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_teq".
    apply CL_teq.
    unfold per_teq; sp.
    exists a1 a2 b1 b2 eqa; sp.
    apply IHn1 with (i0 := i); sp.
    apply IHn2 with (i0 := i); sp.
    apply IHn3 with (i0 := i); sp.

  - Case "CL_isect".
    apply CL_isect.
    unfold per_isect, type_family; sp.
    exists eqa eqb; sp.
    exists A A' v v' B B'; sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_func".
    apply CL_func.
    unfold per_func, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_disect".
    apply CL_disect.
    unfold per_disect, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_pertype".
    apply CL_pertype.
    unfold per_pertype; sp.
    exists R1 R2 eq1 eq2; sp.
    apply rec1 with (i0 := i); sp.
    apply rec2 with (i0 := i); sp.

  - Case "CL_ipertype".
    apply CL_ipertype.
    unfold per_ipertype; sp.
    exists R1 R2 eq1; sp.
    apply rec1 with (i0 := i); sp.

  - Case "CL_spertype".
    apply CL_spertype.
    unfold per_spertype; sp.
    exists R1 R2 eq1; sp.
    apply rec1 with (i0 := i); sp.
    apply rec2 with (i0 := i); sp.
    apply rec3 with (i0 := i); sp.

  - Case "CL_w".
    apply CL_w.
    unfold per_w, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_m".
    apply CL_m.
    unfold per_m, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_pw".
    apply CL_pw.
    unfold per_pw, type_pfamily; sp.
    exists eqp eqa eqb.
    exists p p' cp cp' ca ca' cb cb'.
    exists C C'; sp.
    exists Pr Pr' ap ap' A A' bp bp'.
    exists ba ba' B B'; sp.
    apply IHn with (i0 := i); sp.
    apply reca with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_pm".
    apply CL_pm.
    unfold per_pm, type_pfamily; sp.
    exists eqp eqa eqb.
    exists p p' cp cp' ca ca' cb cb'.
    exists C C'; sp.
    exists Pr Pr' ap ap' A A' bp bp'.
    exists ba ba' B B'; sp.
    apply IHn with (i0 := i); sp.
    apply reca with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_texc".
    apply CL_texc.
    unfold per_texc; sp.
    exists eqn eqe N N' E E'; sp.
    { apply IHn1 with (i0 := i); sp. }
    { apply IHn2 with (i0 := i); sp. }

  - Case "CL_union".
    apply CL_union.
    unfold per_union; sp.
    exists eqa eqb A A' B B'; sp.
    + apply IHn1 with (i0 := i); sp.
    + apply IHn2 with (i0 := i); sp.

      (*
  - Case "CL_eunion".
    apply CL_eunion.
    unfold per_eunion; sp.
    exists eqa1 eqa2 eqb1 eqb2 A A' B B'; sp.
    + apply IHn1 with (i0 := i); sp.
    + apply IHn2 with (i0 := i); sp.
    + apply IHn3 with (i0 := i); sp.
    + apply IHn4 with (i0 := i); sp.*)

  - Case "CL_image".
    apply CL_image.
    unfold per_image; sp.
    exists eqa A A' f f'; sp.
    apply IHn with (i0 := i); sp.

(*
  - Case "CL_eisect".
    apply CL_eisect.
    unfold per_eisect, etype_family; sp.
    exists eqa eqa' eqb; sp.
    exists A A' v v' B B'.
    exists f g f' g'; sp.
    apply IHn1 with (i0 := i); sp.
    apply IHn2 with (i0 := i); sp.
    apply recb with (i0 := i); sp.
    apply recb' with (i0 := i); sp.
*)

  - Case "CL_partial".
    apply CL_partial.
    unfold per_partial; sp.
    exists A1 A2 eqa; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_admiss".
    apply CL_admiss.
    unfold per_admiss; sp.
    exists A1 A2 eqa; sp.
    apply IHn with (i0 := i); sp.

  - Case "CL_mono".
    apply CL_mono.
    unfold per_mono; sp.
    exists A1 A2 eqa; sp.
    apply IHn with (i0 := i); sp.

(*  - Case "CL_ffatom".
    apply CL_ffatom.
    unfold per_ffatom; sp.
    exists A1 A2 x1 x2 a1 a2 eqa u; sp.
    apply IHn with (i0 := i); sp.*)

(*  - Case "CL_effatom".
    apply CL_effatom.
    unfold per_effatom; sp.
    exists A1 A2 x1 x2 a1 a2 eqa; sp.
    apply IHn with (i0 := i); sp.*)

(*  - Case "CL_ffatoms".
    apply CL_ffatoms.
    unfold per_ffatoms; sp.
    exists A1 A2 x1 x2 eqa; sp.
    apply IHn with (i0 := i); sp.*)

  - Case "CL_set".
    apply CL_set.
    unfold per_set, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_tunion".
    apply CL_tunion.
    unfold per_tunion, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.

  - Case "CL_product".
    apply CL_product.
    unfold per_product, type_family; sp.
    exists eqa eqb; sp; try (exists A A' v v' B B'); sp.
    apply IHn with (i0 := i); sp.
    apply recb with (i0 := i); sp.
Qed.


(* --- a few useful abstractions *)

(* end hide *)

(**

  The predicate [tequality T1 T2] is true if [T1] and [T2] are equal
  types of the Nuprl type system.

 *)

Definition tequality {p} lib (T1 T2 : @cterm p) :=
  { eq : per , nuprl lib T1 T2 eq }.

(**

  The predicate [type T] is true if [T] is a type of the Nuprl type
  system.

 *)

Definition type {p} lib (T : @cterm p) := tequality lib T T.

(**

  The predicate [equality t1 t2 T] is true if [t1] and [t2] are equal
  members of the type [T].

 *)

Definition equality {p} lib (t1 t2 T : @cterm p) :=
  { eq : per , nuprl lib T T eq # eq t1 t2 }.

(**

  [member t T] is true if [t] is a member of the type [T].

 *)

Definition member {p} lib (t T : @cterm p) := equality lib t t T.

(**

  The predicate [tequalityi i T1 T2] is true if [T1] and [T2] are
  equal types of the Nuprl type system at level i.

 *)

Definition tequalityi {p} lib i (T1 T2 : @cterm p) := equality lib T1 T2 (mkcn_uni i).

(**

  The predicate [typei i T] is true if [T] is a type of the Nuprl type
  system at level i.

 *)

Definition typei {p} lib i (T : @cterm p) := tequalityi lib i T T.

(* begin hide *)

(** This is similar to eqorsq but using 'equality' instead of 'eq' *)
Definition equorsq {p} lib (t1 t2 T : @cterm p) := equality lib t1 t2 T {+} ccequivcn lib t1 t2.
Definition equorsq2 {p} lib (t1 t2 t3 t4 T : @cterm p) := equorsq lib t1 t2 T # equorsq lib t3 t4 T.

Lemma fold_equorsq {p} :
  forall lib (t1 t2 T : @cterm p),
    (equality lib t1 t2 T {+} ccequivcn lib t1 t2) = equorsq lib t1 t2 T.
Proof. sp. Qed.

Lemma fold_equorsq2 {p} :
  forall lib (t1 t2 t3 t4 T : @cterm p),
    (equorsq lib t1 t2 T # equorsq lib t3 t4 T) = equorsq2 lib t1 t2 t3 t4 T.
Proof. sp. Qed.

(*
Definition cequorsq t1 t2 T := equality t1 t2 T {+} ccequivc t1 t2.
Definition cequorsq2 t1 t2 t3 t4 T := cequorsq t1 t2 T # cequorsq t3 t4 T.
*)

(*
(* Whichever the second one is, it fails with a universe error *)

Lemma tequality_sym :
  forall t1 t2,
    tequality t1 t2 -> tequality t2 t1.
Proof.
  unfold tequality; sp.
  exists eq.
  apply nuprl_sym; sp.
Qed.

Lemma tequality_mkcn_uni :
  forall i : nat, tequality (mkcn_uni i) (mkcn_uni i).
Proof.
  generalize nuprl_mkcn_uni; sp.
Qed.
*)


(* end hide *)

(**

  Because it is sometime useful to remember the levels of types, we
  define the following abstractions.  When we do not want to remember
  levels we will use [tequality] and when we want to remember levels,
  we will use [tequalityi].  Therefore, we use [eqtypes nolvl] when we
  do not to remember levels and we use [eqtypes (atlvl i)] we we do
  want to remember levels.

*)

Inductive lvlop : Type :=
| nolvl : lvlop
| atlvl : nat -> lvlop.

Definition eqtypes {p} lib lvl (T1 T2 : @cterm p) :=
  match lvl with
    | nolvl => tequality lib T1 T2
    | atlvl l => tequalityi lib l T1 T2
  end.

Definition ltype {p} lib l (T : @cterm p) := eqtypes lib l T T.

(* begin hide *)

(* end hide *)
