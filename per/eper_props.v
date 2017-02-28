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


Require Export enuprl_props.
Require Export echoice.
Require Export cvterm.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ #⪯# *)
(** printing ~=~  $\sim$ #~# *)
(* printing ===>  $\longmapsto$ *)
(** printing ===>  $\Downarrow$ #⇓# *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)

(* begin hide *)


(* =============== Some general properties ================= *)

Lemma eequality_in_uni {p} :
  forall lib a b i,
    @eequality p lib a b (mkc_uni i)
    -> etequality lib a b.
Proof.
  unfold etequality, eequality, enuprl; introv e; exrepnd.

  inversion e1 as [e e']; GC; clear e1.
  inversion e; clear e; subst; try not_univ.
  duniv j h.
  induction j; allsimpl; sp; GC.
  computes_to_value_isvalue.
  match goal with
  | [ H : _ <=2=> _ |- _ ] => apply H in e0; clear H
  end.
  unfold eunivi_eq in e0; exrepnd.
  allapply @enuprli_implies_enuprl; auto.
  exists eqa; auto.
Qed.

Lemma emember_in_uni {p} :
  forall lib a i, @emember p lib a (mkc_uni i) -> etype lib a.
Proof.
  unfold emember, etype; introv e.
  apply eequality_in_uni in e; sp.
Qed.

(*
(* This is not provable, because in general we can't find the type level
 * of a type family. *)
Lemma eequality_in_uni_iff {p} :
  forall lib a b,
    {i : nat , @eequality p lib a b (mkc_uni i)}
    <=> etequality lib a b.
Proof.
  sp; split; introv e; exrepnd.
  apply equality_in_uni in e0; sp.

  allunfold @tequality; allunfold @equality; exrepnd.
  unfold nuprl in e0; sp.
  remember (univ lib) as T.
  generalize HeqT; clear HeqT.
  close_cases (induction e0 using @close_ind') Case; intros HeqT; subst.

  - Case "CL_init".
    duniv i h.
    exists i (fun A A' => {eqa : per(p) , close lib (univi lib i) A A' eqa}); sp.
    unfold nuprl.
    apply CL_init; unfold univ.
    exists (S i); simpl; left; sp; try (spcast; computes_to_value_refl).
    exists eq; sp.

  - Case "CL_int".
    exists 1 (fun A A' => {eqa : per(p) , close lib (univi lib 1) A A' eqa}); sp.
    unfold nuprl, univ.
    apply CL_init.
    exists 2; left; sp; try (spcast; computes_to_value_refl).
    exists eq; apply CL_int.
    allunfold @per_int; sp.

  - Case "CL_atom".
    admit.

  - Case "CL_uatom".
    admit.

  - Case "CL_base".
    admit.

  - Case "CL_approx".
    admit.

  - Case "CL_cequiv".
    admit.

  - Case "CL_aeq".
    dest_imp IHe0 hyp; exrepnd.
    admit.

  - Case "CL_eq".
    dest_imp IHe0 hyp; exrepnd.
    admit.

  - Case "CL_teq".
    admit.

  - Case "CL_isect".
    dest_imp IHe0 hyp; exrepnd.
    admit.

  - Case "CL_func".
    admit.

  - Case "CL_disect".
    admit.

  - Case "CL_pertype".
    admit.
(*Error: Universe inconsistency.*)
Abort.
*)



(* =============== More specific properties ================= *)

Lemma enuprl_same :
  forall {o} lib (A : @CTerm o) eq,
    enuprl lib A A eq <=> close lib (euniv lib) A A eq.
Proof.
  introv; split; intro h.
  - inversion h; auto.
  - constructor; auto.
Qed.

Lemma enuprl_int {p} :
  forall lib, @enuprl p lib mkc_int mkc_int (equality_of_int lib).
Proof.
  introv.
  apply enuprl_same.
  apply CL_int.
  unfold per_int; sp; spcast; try computes_to_value_refl.
Qed.

(*
Lemma eequality_of_int_xxx {p} :
  forall lib, @close p lib (univ lib) mkc_int mkc_int (equality_of_int lib).
Proof.
  apply enuprl_int.
Qed.
*)

Lemma etequality_int {p} : forall lib, @etequality p lib mkc_int mkc_int.
Proof.
  introv.
  exists (@equality_of_int p lib).
  apply enuprl_int.
Qed.

Lemma enat_in_int {p} : forall lib (n : nat), @emember p lib (mkc_nat n) mkc_int.
Proof.
  unfold emember, eequality; introv.
  exists (@equality_of_int p lib).
  dands;[apply enuprl_int|].
  exists (Z_of_nat n); sp;
  unfold mkc_nat, mkc_integer, isprog_mk_nat, isprog_mk_integer, mk_nat;
    spcast; computes_to_value_refl.
Qed.

(*

The -> shouldn't be true anymore because, e.g.,

 False -> Bool and Nat -> Top

are equal types

================================================

(* This is basically 'functionEquality' *)
Lemma etequality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    etequality
      lib
      (mkc_function A1 v1 B1)
      (mkc_function A2 v2 B2)
    <=>
    (etequality lib A1 A2
     # forall a a', eequality lib a a' A1 -> etequality lib (substc a v1 B1) (substc a' v2 B2)).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intro teq.
    unfold etequality, enuprl in teq; exrepnd.
    destruct teq0 as [teq1 teq2].
    inversion teq1; subst; try not_univ.
    match goal with
    | [ H : per_func _ _ _ _ _ |- _ ] => rename H into perf1
    end.
    inversion teq2; subst; try not_univ.
    match goal with
    | [ H : per_func _ _ _ _ _ |- _ ] => rename H into perf2
    end.
    clear teq1 teq2.
    allunfold_per.
    computes_to_value_isvalue.
    unfold etequality; dands.

    {
      exists eqa; sp.

    assert (eqa a a') as xa
      by (generalize (equality_eq1 lib A A' a a' eqa); intro e;
          dest_imp e hyp;
          try (exists i; auto);
          apply e; auto).
    exists (eqb a a' xa); sp.
    apply c2.

  - Case "<-".
    introv e; exrepnd.
    rename e0 into teqa; rename e into teqb.
    unfold tequality in teqa; exrepnd.
    rename eq into eqa.
    generalize (choice_teq lib A1 v1 B1 v2 B2 teqb); intro n; exrepnd.

    exists (fun t1 t2 =>
              forall a1 a2 : CTerm,
              forall e : eqa a1 a2,
                f a1
                  a2
                  (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)
                  (mkc_apply t1 a1)
                  (mkc_apply t2 a2)).
    apply CL_func; fold (@nuprl p lib).
    unfold per_func.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).
Qed.
 *)


Lemma implies_etequality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    etequality lib A1 A2
    -> (forall a a', eequality lib a a' A1 -> etequality lib (substc a v1 B1) (substc a' v2 B2))
    -> etequality lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2).
Proof.
  introv teqa teqb.

  unfold etequality in teqa; exrepnd.
  rename eq into eqa.

  pose proof (echoice_teq lib A1 v1 B1 v2 B2 teqb) as fteqb; exrepnd.
  clear teqb.

  exists (fun t1 t2 =>
            forall (a1 a2 : CTerm) (e : eqa a1 a2),
              f a1
                a2
                (eq_eequality2 lib a1 a2 A1 A2 eqa e teqa0)
                (mkc_apply t1 a1)
                (mkc_apply t2 a2)).
  split.

  - apply CL_func; fold (@enuprl p lib).
    unfold per_func.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_eequality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A1 A1 v1 v1 B1 B1; dands;  tcsp;
      try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).

    { destruct teqa0 as [t1 t2]; auto. }

    introv.

    dup e as e1.
    eapply eequality_eq_refl in e1;[|eauto].

    dup e as e2.
    eapply eequality_eq_sym in e2;[|eauto].
    eapply eequality_eq_refl in e2;[|eauto].

    pose proof (fteqb0 a a' (eq_eequality2 lib a a' A1 A2 eqa e teqa0)) as q.
    destruct q as [q1 q2]; auto.

    pose proof (fteqb0 a a (eq_eequality2 lib a a A1 A2 eqa e1 teqa0)) as h.
    destruct h as [h1 h2]; auto.

    pose proof (fteqb0 a' a' (eq_eequality2 lib a' a' A1 A2 eqa e2 teqa0)) as z.
    destruct z as [z1 z2]; auto.

    remember (f a a' (eq_eequality2 lib a a' A1 A2 eqa e teqa0)) as eqb1; clear Heqeqb1.
    remember (f a a (eq_eequality2 lib a a A1 A2 eqa e1 teqa0)) as eqb2; clear Heqeqb2.
    remember (f a' a' (eq_eequality2 lib a' a' A1 A2 eqa e2 teqa0)) as eqb3; clear Heqeqb3.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).
Qed.


Definition get_per_of {p} lib (T t1 t2: @CTerm p) :=
  equality lib t1 t2 T.

Lemma tequality_admiss {p} :
  forall lib (A1 A2 : @CTerm p),
    tequality lib (mkc_admiss A1) (mkc_admiss A2)
    <=> tequality lib A1 A2.
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.
    allunfold @per_admiss; exrepnd.
    computes_to_value_isvalue.
    allfold @nuprl.
    dands.
    exists eqa; auto.

  - Case "<-".
    intro teq.
    unfold tequality in teq; destruct teq as [eqa n].
    exists (per_admiss_eq lib eqa).
    apply CL_admiss.
    unfold per_admiss.
    exists A1 A2 eqa; dands; fold @nuprl; auto;
    try (complete (spcast; apply computes_to_valc_refl; apply_iscvalue)).
Qed.


Lemma if_member_function {p} :
  forall lib (f : @CTerm p) A v B,
    member lib f (mkc_function A v B)
    -> forall x y,
         equality lib x y A
         -> equality lib (mkc_apply f x) (mkc_apply f y) (substc x v B).
Proof.
  unfold member, equality, nuprl; introv m e; exrepnd.
  inversion m1; subst; try not_univ.

  allunfold_per; spcast; computes_to_eqval.
  allfold (@nuprl p lib).
  computes_to_value_isvalue.
  discover.

  generalize (nuprl_uniquely_valued lib A0 eqa eq); intro k; repeat (dest_imp k hyp).
  rw <- k in e0.

  exists (eqb x y e0); sp.

  apply nuprl_refl with (t2 := substc y v0 B0); sp.
Qed.

(* This is 'functionExtensionality' *)
Lemma implies_member_function {p} :
  forall lib (f : @CTerm p) g A v B,
    type lib A
    -> (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
    -> (forall a a',
          equality lib a a' A
          -> equality lib (mkc_apply f a) (mkc_apply g a') (substc a v B))
    -> equality lib f g (mkc_function A v B).
Proof.
  introv ty teq eqap.
  unfold member, equality.
  unfold type, tequality in ty; exrepnd.
  rename eq into eqa.

  generalize (choice_eq lib A v B (fun a => mkc_apply f a) (fun a => mkc_apply g a) eqap);
    intro n; exrepnd.

  exists (fun t1 t2 =>
            forall a1 a2 : CTerm,
            forall e : eqa a1 a2,
              f0 a1
                 a2
                 (eq_equality1 lib a1 a2 A eqa e ty0)
                 (mkc_apply t1 a1)
                 (mkc_apply t2 a2)); sp.

  unfold nuprl; apply CL_func; fold @nuprl; unfold per_func.
  exists eqa.

  exists (fun a1 a2 e => f0 a1 a2 (eq_equality1 lib a1 a2 A eqa e ty0)); sp.

  unfold type_family.
  exists A A v v B B; sp;
  try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).

  generalize (n0 a a' (eq_equality1 lib a a' A eqa e ty0)); intro n; repnd.

  generalize (choice_teq lib A v B v B teq); intro m; exrepnd.
  generalize (m0 a a' (eq_equality1 lib a a' A eqa e ty0)); intro m.

  apply nuprl_trans with (t2 := substc a v B)
                           (eq2 := f1 a a' (eq_equality1 lib a a' A eqa e ty0)); sp.

  generalize (n0 a1 a2 (eq_equality1 lib a1 a2 A eqa e ty0)); sp.
Qed.

Ltac one_dest_per_fam eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt :=
  match goal with
    | [ H : _ |- _ ] => dest_per_fam H eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt
  end.

(* end hide *)

(**

  As another example, we can prove that two terms [f] and [g] are
  equal in the function type [mkc_function A v B] if and only if [A]
  is a type, [B] is functional over [A], and forall [a] and [a'] equal
  in [A], [mkc_apply f a] and [mkc_apply g a'] are equals in [substc a
  v B].

  This is one of the lemmas where we need the [FunctionalChoice_on]
  axiom. Let us explain that issue.  Let us assume that we want to
  prove the left-hand-side of [<=>] from its right-hand-side.  To
  prove that [f] and [g] are equal in [mkc_function A v B], we have to
  provide the equality of the function type, and in particular, we
  have to provide the equality of its co-domain.  We obtain that
  equality from the third clause in the right-hand-side of the [<=>].
  However, in our current [Prop] metatheory, that clause is (roughly)
  a [forall] of a propositional [exists].  From such a formula, we
  need to build a [per-fam] function (the equality of the co-domain),
  which is exactly what [FunctionalChoice_on] gives us.  This axiom is
  necessary because in general we cannot access the witness of a
  propositional existential.

 *)

(* This is the <=> verison of 'implies_member_function' *)
Lemma equality_in_function {p} :
  forall lib (f : @CTerm p) g A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # (forall a a',
          equality lib a a' A
          -> equality lib (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv; sp_iff Case; introv e; try (complete (apply implies_member_function; sp)).

  unfold equality in e; exrepnd.
  inversion e1; subst; try not_univ.

  one_dest_per_fam eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt.
  allunfold_per; spcast; computes_to_eqval; allfold (@nuprl p lib).
  computes_to_value_isvalue; dands.

  exists eqa; sp.

  introv e.
  unfold equality in e; exrepnd.
  generalize (nuprl_uniquely_valued lib A1 eqa eq0); intro k; repeat (dest_imp k hyp).
  rw <- k in e2.
  generalize (tsb a a' e2); intro n.
  exists (feqb a a' e2); sp.

  introv e.
  discover.
  unfold equality in e; exrepnd.
  generalize (nuprl_uniquely_valued lib A1 eqa eq0); intro k; repeat (dest_imp k hyp).
  rw <- k in e2.
  generalize (tsb a a' e2); intro n.
  exists (feqb a a' e2); sp.
  allapply @nuprl_refl; sp.
Qed.

(* begin hide *)

Lemma tequality_isect {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib (mkc_isect A1 v1 B1)
              (mkc_isect A2 v2 B2)
    <=>
    (tequality lib A1 A2
     # forall a a', equality lib a a' A1 -> tequality lib (substc a v1 B1) (substc a' v2 B2)).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.

    one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
    computes_to_value_isvalue.
    allfold (@nuprl p lib).
    dands.

    unfold tequality.
    exists eqa; sp.

    introv e.
    unfold tequality.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib A3 eqa eq0);
      intro k; repeat (dest_imp k hyp); try (complete (allapply @nuprl_refl; sp)).
    rw <- k in e0.
    generalize (tsb a a' e0); intro n.
    exists (feqb a a' e0); sp.

  - Case "<-".
    introv eqs.
    destruct eqs as [teqa teqb].
    unfold tequality in teqa; exrepnd.
    rename eq into eqa.

    generalize (choice_teq lib A1 v1 B1 v2 B2 teqb); intro n; exrepnd.

    exists (fun t1 t2 =>
              forall a1 a2 : CTerm,
              forall e : eqa a1 a2,
                f a1 a2
                  (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)
                  t1 t2).
    apply CL_isect; fold (@nuprl p lib).
    unfold per_isect.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_isect))).
Qed.

Lemma equality_isect {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib (mkc_isect A1 v1 B1)
             (mkc_isect A2 v2 B2)
             (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
     # forall a a',
         equality lib a a' A1
         -> equality lib (substc a v1 B1) (substc a' v2 B2) (mkc_uni i)).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold equality, nuprl in teq; exrepnd.
    inversion teq1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    rename eqa into eqi.
    ioneclose; subst; try not_univ.

    one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
    computes_to_value_isvalue; GC.
    dands.

    exists eq; sp.
    allrw.
    exists eqa; sp.

    introv e.
    exists eq; sp.
    allfold (@nuprli p lib j0).
    allrw.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib A3 eqa eq0);
      intro k; repeat (dest_imp k hyp);
      try (complete (apply nuprli_implies_nuprl with (i := j0); sp;
                     allapply @nuprli_refl; sp)).
    rw <- k in e0.
    generalize (tsb a a' e0); intro n.
    exists (feqb a a' e0); sp.

  - Case "<-".
    intro eqs.
    destruct eqs as [eqa eqb].
    unfold equality in eqa; exrepnd.
    inversion eqa1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli p lib j0).

    exists eq; sp.
    allrw.

    generalize (choice_teqi lib j0 A1 v1 B1 v2 B2 eqb); intro n; exrepnd.

    exists (fun t1 t2 =>
              forall a1 a2 : CTerm,
              forall e : eqa a1 a2,
                f a1 a2
                  (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)
                  t1 t2).
    apply CL_isect; fold (@nuprli p lib j0).
    unfold per_isect.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_isect))).
Qed.

Lemma equality_in_isect {p} :
  forall lib (t u : @CTerm p) A v B,
    equality lib t u (mkc_isect A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # (forall a a',
          equality lib a a' A
          -> equality lib t u (substc a v B))).
Proof.
  sp; sp_iff Case; introv e.

  - Case "->".
    unfold equality in e; exrepd.
    inversion n; subst; try not_univ.
    one_dest_per_fam eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt.
    computes_to_value_isvalue.
    allfold (@nuprl p lib).
    dands.

    exists eqa; sp.

    introv ea.
    unfold equality in ea; exrepnd.
    assert (eq_term_equals eq0 eqa) as eqta
      by (apply (nuprl_uniquely_valued lib) with (t := A1); sp).
    unfold eq_term_equals in eqta.
    discover.
    generalize (tsb a a' h); sp.
    exists (feqb a a' h); sp.

    introv ea.
    unfold equality in ea; exrepnd.
    assert (eq_term_equals eq0 eqa) as eqta
      by (apply (nuprl_uniquely_valued lib) with (t := A1); sp).
    unfold eq_term_equals in eqta.
    discover.
    assert (eqa a a) as eqaa
      by (apply term_equality_refl with (t2 := a'); sp;
          try (complete (nts; apply nts_tes with (T := A1) (T' := A1); auto));
          try (complete (nts; apply nts_tet with (T := A1) (T' := A1); auto))).
    exists (feqb a a eqaa); sp.

  - Case "<-".
    repnd.
    unfold equality.
    unfold type, tequality in e0; exrepnd.
    rename eq into eqa.

    generalize (choice_eq lib A v B (fun a => t) (fun a => u) e);
      intro n; exrepnd.

    exists (fun t1 t2 =>
              forall a1 a2 : CTerm,
              forall e : eqa a1 a2,
                f a1 a2
                  (eq_equality1 lib a1 a2 A eqa e e2)
                  t1 t2); sp.

    unfold nuprl; apply CL_isect; fold @nuprl; unfold per_isect.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality1 lib a1 a2 A eqa e e2)); sp.

    unfold type_family.
    exists A A v v B B; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_isect))).

    generalize (n0 a a' (eq_equality1 lib a a' A eqa e0 e2)); intro n; repnd.

    generalize (choice_teq lib A v B v B e1); intro m; exrepnd.
    generalize (m0 a a' (eq_equality1 lib a a' A eqa e0 e2)); intro m.

    apply nuprl_trans with (t2 := substc a v B)
                             (eq2 := f0 a a' (eq_equality1 lib a a' A eqa e0 e2)); sp.

    generalize (n0 a1 a2 (eq_equality1 lib a1 a2 A eqa e0 e2)); sp.
Qed.

(* end hide *)

(**

  As we proved a relation between the [equality] relation and the
  [mkc_equality] type, we can prove the followig result that relates
  the computational equality relation to the [mkc_cequiv] type.

 *)

(* begin hide *)

Lemma eqorceq_commutes_nuprl {p} :
  forall lib (a b c d : @CTerm p) eq A B,
    nuprl lib A B eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq c d
    -> eq a c
    -> eq b d.
Proof.
  introv n e1 e2 e3.
  apply (eqorceq_commutes lib) with (a := a) (c := c); sp.

  nts.
  unfold term_value_respecting in nts_tev.
  apply nts_tev with (T := A).
  allapply @nuprl_refl; sp.

  nts.
  unfold term_symmetric in nts_tes.
  apply nts_tes with (T := A) (T' := B); sp.

  nts.
  unfold term_transitive in nts_tet.
  apply nts_tet with (T := A) (T' := B); sp.
Qed.

Lemma eqorceq_sym_trans {p} :
  forall lib eq (a b A B : @CTerm p),
    nuprl lib A B eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq b a.
Proof.
  introv n e.
  apply eqorceq_sym; sp.
  nts.
  unfold term_symmetric in nts_tes.
  apply nts_tes with (T := A) (T' := B); sp.
Qed.

Lemma nuprl_refl2 {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    nuprl lib t1 t2 eq -> nuprl lib t2 t2 eq.
Proof.
  introv n.
  apply nuprl_sym in n.
  apply nuprl_refl in n; sp.
Qed.

Lemma nuprl_uniquely_eq_ext {p} :
  forall lib (t1 t2 : @CTerm p) eq1 eq2,
    nuprl lib t1 t2 eq1
    -> eq_term_equals eq1 eq2
    -> nuprl lib t1 t2 eq2.
Proof.
  introv n e; nts.
  apply nts_ext with (T := t1) (T' := t2) (eq := eq1); sp.
Qed.

Lemma equality_or_cequivc_eqorceq {p} :
  forall lib (A a b : @CTerm p) eq,
    nuprl lib A A eq
    -> (eqorceq lib eq a b <=> (equality lib a b A {+} ccequivc lib a b)).
Proof.
  unfold eqorceq; introv n; split; intro e; repdors; try (complete sp);
  left;
  apply @equality_eq with (a := a) (b := b) in n;
  allrw <-; sp;
  allrw; sp.
Qed.

Lemma eqorceq_implies_equality_or_cequivc {p} :
  forall lib (A a b : @CTerm p) eq,
    nuprl lib A A eq
    -> eqorceq lib eq a b
    -> (equality lib a b A {+} ccequivc lib a b).
Proof.
  introv n e.
  generalize (equality_or_cequivc_eqorceq lib A a b eq); sp.
  allrw <-; sp.
Qed.

Lemma false_not_inhabited {p} :
  forall lib (t : @CTerm p), !member lib t mkc_false.
Proof.
  introv m.
  rewrite mkc_false_eq in m.
  unfold member, equality, nuprl in m; exrepnd.
  inversion m1; subst; try not_univ.
  allunfold @per_approx; exrepnd.
  computes_to_value_isvalue.
  discover; sp; GC.
  spcast; allapply @not_axiom_approxc_bot; sp.
Qed.

Lemma equality3_implies_equorsq2 {p} :
  forall lib (a b c d T : @CTerm p),
    equality lib a c T
    -> equality lib b d T
    -> equality lib a b T
    -> equorsq2 lib a b c d T.
Proof.
  sp.
  unfold equorsq2, equorsq; sp.
  left.
  apply equality_trans with (t2 := b); auto.
  apply equality_trans with (t2 := a); auto.
  apply equality_sym; auto.
Qed.


Definition inhabited_type {p} lib (T : @CTerm p) := {t : CTerm , member lib t T}.

Definition sym_type {p} lib (R : @CTerm p) :=
  forall x y,
    inhabited_type lib (mkc_apply2 R x y)
    -> inhabited_type lib (mkc_apply2 R y x).

Definition trans_type {p} lib (R : @CTerm p) :=
  forall x y z,
    inhabited_type lib (mkc_apply2 R x y)
    -> inhabited_type lib (mkc_apply2 R y z)
    -> inhabited_type lib (mkc_apply2 R x z).

Definition is_per_type {p} lib (R : @CTerm p) :=
  sym_type lib R # trans_type lib R.

Lemma is_per_type_iff {p} :
  forall lib R1 R2,
    (forall x y : @CTerm p,
       inhabited_type lib (mkc_apply2 R1 x y)
       <=>
       inhabited_type lib (mkc_apply2 R2 x y))
    -> is_per_type lib R1
    -> is_per_type lib R2.
Proof.
  unfold is_per_type, sym_type, trans_type; introv iff per; dands; introv.

  intro inh.
  rw <- iff; rw <- iff in inh; sp.

  intros inh1 inh2.
  rw <- iff; rw <- iff in inh1; rw <- iff in inh2.
  apply per with (y := y); sp.
Qed.

Lemma inhabited_type_if_equality {p} :
  forall lib (a b R : @CTerm p), equality lib a b R -> inhabited_type lib R.
Proof.
  introv eq.
  unfold inhabited_type; exists a.
  apply equality_refl in eq; sp.
Qed.

Lemma inhabited_if_inhabited_type {p} :
  forall lib (T U : @CTerm p) eq,
    inhabited_type lib T
    -> nuprl lib T U eq
    -> inhabited eq.
Proof.
  introv inh neq.
  unfold inhabited_type in inh; exrepnd.
  unfold member, equality in inh0; exrepnd.
  generalize (nuprl_uniquely_valued lib T eq0 eq); intro i.
  repeat (dest_imp i hyp); try (complete (apply nuprl_refl with (t2 := U); sp)).
  rw i in inh1.
  clear inh0 i eq0.
  unfold nuprl in neq.
  unfold inhabited; exists t; sp.
Qed.

Lemma inhabited_type_if_inhabited {p} :
  forall lib (T U : @CTerm p) eq,
    nuprl lib T U eq
    -> inhabited eq
    -> inhabited_type lib T.
Proof.
  introv neq inh.
  unfold inhabited_type.
  unfold inhabited in inh; exrepnd.
  exists t.
  unfold member, equality.
  exists eq; sp.
  apply nuprl_refl with (t2 := U); sp.
Qed.

Lemma inhabited_type_iff_inhabited {p} :
  forall lib (T U : @CTerm p) eq,
    nuprl lib T U eq
    -> (inhabited eq <=> inhabited_type lib T).
Proof.
  introv neq; split; intro i.
  apply @inhabited_type_if_inhabited with (U := U) (eq := eq); sp.
  eapply inhabited_if_inhabited_type; eauto.
Qed.

Lemma inhabited_if_inhabited_type_i {p} :
  forall lib (T U : @CTerm p) eq i,
    inhabited_type lib T
    -> nuprli lib i T U eq
    -> inhabited eq.
Proof.
  introv inh neq.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_if_inhabited_type in neq; auto.
Qed.

Lemma inhabited_type_if_inhabited_i {p} :
  forall lib (T U : @CTerm p) eq i,
    nuprli lib i T U eq
    -> inhabited eq
    -> inhabited_type lib T.
Proof.
  introv neq inh.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_type_if_inhabited in neq; auto.
Qed.

Lemma inhabited_type_iff_inhabited_i {p} :
  forall lib (T U : @CTerm p) eq i,
    nuprli lib i T U eq
    -> (inhabited eq <=> inhabited_type lib T).
Proof.
  introv neq.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_type_iff_inhabited in neq; auto.
Qed.

Lemma is_per_type_iff_is_per {p} :
  forall lib R eq,
    (forall x y : @CTerm p, nuprl lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq x y))
    -> (is_per eq <=> is_per_type lib R).
Proof.
  introv n.
  split; intro isper.

  - destruct isper as [sym trans].
    unfold is_per_type, sym_type, trans_type; dands; introv.

    + intro inh.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y x) (mkc_apply2 R y x) (eq y x)).
      intro iff2; dest_imp iff2 hyp.
      rw <- iff2.
      apply sym.
      rw iff1; sp.

    + intros inh1 inh2.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y z) (mkc_apply2 R y z) (eq y z)).
      intro iff2; dest_imp iff2 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x z) (mkc_apply2 R x z) (eq x z)).
      intro iff3; dest_imp iff3 hyp.
      rw <- iff3.
      apply trans with (y := y).
      rw iff1; sp.
      rw iff2; sp.

  - destruct isper as [sym trans].
    unfold sym_type in sym.
    unfold trans_type in trans.
    unfold is_per; dands; introv.

    + intro inh.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y x) (mkc_apply2 R y x) (eq y x)).
      intro iff2; dest_imp iff2 hyp.
      rw iff2.
      apply sym.
      rw <- iff1; sp.

    + intros inh1 inh2.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y z) (mkc_apply2 R y z) (eq y z)).
      intro iff2; dest_imp iff2 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x z) (mkc_apply2 R x z) (eq x z)).
      intro iff3; dest_imp iff3 hyp.
      rw iff3.
      apply trans with (y := y).
      rw <- iff1; sp.
      rw <- iff2; sp.
Qed.

Lemma is_per_type_iff_is_per1 {p} :
  forall lib R1 R2 eq,
    (forall x y : @CTerm p, nuprl lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (eq x y))
    -> (is_per eq <=> is_per_type lib R1).
Proof.
  introv n.
  apply is_per_type_iff_is_per; introv.
  generalize (n x y); intro k.
  apply nuprl_refl in k; auto.
Qed.

Lemma inhabited_type_iff {p} :
  forall lib (T1 T2 : @CTerm p) eq1 eq2,
    nuprl lib T1 T1 eq1
    -> nuprl lib T2 T2 eq2
    -> ((inhabited eq1 <=> inhabited eq2)
        <=> (inhabited_type lib T1 <=> inhabited_type lib T2)).
Proof.
  introv n1 n2.
  generalize (inhabited_type_iff_inhabited lib T1 T1 eq1); intro i1.
  dest_imp i1 hyp.
  generalize (inhabited_type_iff_inhabited lib T2 T2 eq2); intro i2.
  dest_imp i2 hyp.
  allrw; sp.
Qed.


Ltac dest_per :=
  match goal with
      [ H : per_pertype ?lib ?ts ?T1 ?T2 ?eq |- _ ] =>
      let R1     := fresh "R1"     in
      let R2     := fresh "R2"     in
      let eq1    := fresh "eq1"    in
      let eq2    := fresh "eq2"    in
      let c1     := fresh "c1"     in
      let c2     := fresh "c2"     in
      let typ1   := fresh "typ1"   in
      let typ2   := fresh "typ2"   in
      let inhiff := fresh "inhiff" in
      let pereq  := fresh "pereq"  in
      unfold per_pertype in H;
        destruct H as [ R1     H ];
        destruct H as [ R2     H ];
        destruct H as [ eq1    H ];
        destruct H as [ eq2    H ];
        destruct H as [ c1     H ];
        destruct H as [ c2     H ];
        destruct H as [ typ1   H ];
        destruct H as [ typ2   H ];
        destruct H as [ inhiff H ];
        destruct H as [ isper  pereq ]
    | [ H : per_ipertype ?lib ?ts ?T1 ?T2 ?eq |- _ ] =>
      let R1     := fresh "R1"     in
      let R2     := fresh "R2"     in
      let eq1    := fresh "eq1"    in
      let c1     := fresh "c1"     in
      let c2     := fresh "c2"     in
      let typ1   := fresh "eqtyps" in
      let pereq  := fresh "pereq"  in
      unfold per_ipertype in H;
        destruct H as [ R1    H ];
        destruct H as [ R2    H ];
        destruct H as [ eq1   H ];
        destruct H as [ c1    H ];
        destruct H as [ c2    H ];
        destruct H as [ typ1  H ];
        destruct H as [ isper pereq ]
    | [ H : per_spertype ?lib ?ts ?T1 ?T2 ?eq |- _ ] =>
      let R1     := fresh "R1"      in
      let R2     := fresh "R2"      in
      let eq1    := fresh "eq1"     in
      let c1     := fresh "c1"      in
      let c2     := fresh "c2"      in
      let typ1   := fresh "eqtyps1" in
      let typ2   := fresh "eqtyps2" in
      let typ3   := fresh "eqtyps3" in
      let pereq  := fresh "pereq"   in
      unfold per_spertype in H;
        destruct H as [ R1    H ];
        destruct H as [ R2    H ];
        destruct H as [ eq1   H ];
        destruct H as [ c1    H ];
        destruct H as [ c2    H ];
        destruct H as [ typ1  H ];
        destruct H as [ typ2  H ];
        destruct H as [ typ3  H ];
        destruct H as [ isper pereq ]
  end.

Lemma tequality_mkc_pertype {p} :
  forall lib (R1 R2 : @CTerm p),
    tequality lib (mkc_pertype R1) (mkc_pertype R2)
    <=> (forall x y, type lib (mkc_apply2 R1 x y))
      # (forall x y, type lib (mkc_apply2 R2 x y))
      # (forall x y,
           inhabited_type lib (mkc_apply2 R1 x y)
           <=>
           inhabited_type lib (mkc_apply2 R2 x y))
      # is_per_type lib R1.
Proof.
  introv.
  split; intro i.

  - unfold tequality, nuprl in i; exrepnd.
    inversion i0; subst; try not_univ.
    dest_per; allfold (@nuprl p lib).
    computes_to_value_isvalue.

    dands; intros.

    unfold type, tequality; exists (eq1 x y); sp.
    unfold type, tequality; exists (eq2 x y); sp.

    generalize (inhabited_type_iff lib (mkc_apply2 R0 x y) (mkc_apply2 R3 x y) (eq1 x y) (eq2 x y)); intro iff; repeat (dest_imp iff hyp).
    rw <- iff; sp.

    generalize (is_per_type_iff_is_per lib R0 eq1); introv iff.
    dest_imp iff hyp.
    rw <- iff; sp.

  - repnd.
    unfold tequality, nuprl.
    generalize (i0 mkc_axiom mkc_axiom); intro k.

    generalize (choice_spteq lib (mkc_apply2 R1) (mkc_apply2 R1)); intro fn1.
    generalize (choice_spteq lib (mkc_apply2 R2) (mkc_apply2 R2)); intro fn2.
    dest_imp fn1 hyp; exrepnd.
    dest_imp fn2 hyp; exrepnd.
    exists (fun t t' => inhabited (f t t')).
    apply CL_pertype.
    unfold per_pertype.
    exists R1 R2 f f0; sp;
    try (spcast; computes_to_value_refl);
    try (fold nuprl).

    generalize (inhabited_type_iff lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (f x y) (f0 x y)); intro iff; repeat (dest_imp iff hyp).
    rw iff; sp.

    generalize (is_per_type_iff_is_per lib R1 f); introv iff.
    dest_imp iff hyp.
    rw iff; sp.
Qed.

Lemma tequality_mkc_ipertype {p} :
  forall lib (R1 R2 : @CTerm p),
    tequality lib (mkc_ipertype R1) (mkc_ipertype R2)
    <=> (forall x y, tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y))
        # is_per_type lib R1.
Proof.
  introv.
  split; intro i.

  - unfold tequality, nuprl in i; exrepnd.
    inversion i0; subst; try not_univ.
    dest_per; allfold (@nuprl p lib).
    computes_to_value_isvalue.

    dands; intros.

    generalize (eqtyps x y); intro i.
    apply tequality_if_nuprl in i; sp.

    generalize (is_per_type_iff_is_per1 lib R0 R3 eq1 eqtyps); intro k; apply k; auto.

  - repnd.
    generalize (i0 mkc_axiom mkc_axiom); intro k.

    generalize (choice_spteq lib (mkc_apply2 R1) (mkc_apply2 R2)); intro fn.
    dest_imp fn hyp; exrepnd.
    exists (fun t t' => inhabited (f t t')).
    apply CL_ipertype.
    unfold per_ipertype.
    exists R1 R2 f; sp;
    try (spcast; computes_to_value_refl);
    try (fold nuprl).

    generalize (is_per_type_iff_is_per1 lib R1 R2 f fn0); introv iff.
    rw iff; sp.
Qed.

Lemma tequality_mkc_spertype {p} :
  forall lib (R1 R2 : @CTerm p),
    tequality lib (mkc_spertype R1) (mkc_spertype R2)
    <=> (forall x y, tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y))
        # (forall x y z,
             inhabited_type lib (mkc_apply2 R1 x z)
             -> tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R1 z y))
        # (forall x y z,
             inhabited_type lib (mkc_apply2 R1 y z)
             -> tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R1 x z))
        # is_per_type lib R1.
Proof.
  introv.
  split; intro i.

  - unfold tequality, nuprl in i; exrepnd.
    inversion i0; subst; try not_univ.
    dest_per; allfold (@nuprl p lib).
    computes_to_value_isvalue.

    dands; intros.

    generalize (eqtyps1 x y); intro i.
    apply tequality_if_nuprl in i; sp.

    generalize (eqtyps2 x y z); intro i; autodimp i hyp.
    eapply inhabited_if_inhabited_type with (T := mkc_apply2 R0 x z) (U := mkc_apply2 R3 x z); eauto.
    apply tequality_if_nuprl in i; sp.

    generalize (eqtyps3 x y z); intro i; autodimp i hyp.
    eapply inhabited_if_inhabited_type with (T := mkc_apply2 R0 y z) (U := mkc_apply2 R3 y z); eauto.
    apply tequality_if_nuprl in i; sp.

    generalize (is_per_type_iff_is_per1 lib R0 R3 eq1 eqtyps1); intro k; apply k; auto.

  - repnd.
    generalize (i0 mkc_axiom mkc_axiom); intro k.

    generalize (choice_spteq lib (mkc_apply2 R1) (mkc_apply2 R2)); intro fn.
    dest_imp fn hyp; exrepnd.
    exists (fun t t' => inhabited (f t t')).
    apply CL_spertype.
    unfold per_spertype.
    exists R1 R2 f; dands; spcast; introv;
    try (spcast; computes_to_value_refl);
    try (fold (@nuprl p lib)); try (complete sp).

    introv inh.
    generalize (fn0 x z); intro e.
    apply inhabited_type_if_inhabited in e; auto.
    apply i1 with (y := y) in e.
    rw <- @tequality_iff_nuprl in e; exrepnd.
    generalize (fn0 x y); intro n.
    generalize (nuprl_uniquely_valued lib (mkc_apply2 R1 x y) eq (f x y));
      intro eqs; repeat (autodimp eqs hyp).
    apply nuprl_refl in e0; auto.
    apply nuprl_refl in n; auto.
    apply nuprl_ext with (eq1 := eq); auto.

    introv inh.
    generalize (fn0 y z); intro e.
    apply inhabited_type_if_inhabited in e; auto.
    apply i2 with (x := x) in e.
    rw <- @tequality_iff_nuprl in e; exrepnd.
    generalize (fn0 x y); intro n.
    generalize (nuprl_uniquely_valued lib (mkc_apply2 R1 x y) eq (f x y));
      intro eqs; repeat (autodimp eqs hyp).
    apply nuprl_refl in e0; auto.
    apply nuprl_refl in n; auto.
    apply nuprl_ext with (eq1 := eq); auto.

    generalize (is_per_type_iff_is_per1 lib R1 R2 f fn0); introv iff.
    rw iff; sp.
Qed.

(*
Lemma mkc_ipertype_equality_in_uni :
  forall R1 R2 i,
    equality lib (mkc_ipertype R1) (mkc_ipertype R2) (mkc_uni i)
    <=> (forall x y, equality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (mkc_uni i))
      # is_per_type lib R1.
Proof.
  introv; split; intro equ; repnd.

  - unfold equality, nuprl in equ; exrepnd.
    inversion equ1; subst; try not_univ.
    inversion X; exrepd.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rename x into i.
    rw X1 in equ0; exrepnd.
    inversion equ2; subst; try not_univ.
    allunfold per_ipertype; exrepnd.
    allfold nuprl; allfold (nuprli j).
    computes_to_value_isvalue.

    dands; intros.

    generalize (X5 x y); intro k.
    unfold member, equality.
    exists eq; sp.
    rw X1.
    exists (eq1 x y); sp.

    allunfold is_per; repnd; allunfold is_per_type; dands.

    unfold sym_type; introv inh.
    apply inhabited_type_if_inhabited with (U := mkc_apply2 R0 y x) (eq := eq1 y x); sp.
    generalize (X5 y x); intro p; apply nuprli_implies_nuprl in p; sp; allapply nuprl_refl; sp.
    apply X2.
    apply inhabited_if_inhabited_type with (U := mkc_apply2 R0 x y) (T := mkc_apply2 R0 x y); sp.
    generalize (X5 x y); intro p; apply nuprli_implies_nuprl in p; sp; allapply nuprl_refl; sp.

    unfold trans_type; introv inh1 inh2.
    apply inhabited_type_if_inhabited with (U := mkc_apply2 R0 x z) (eq := eq1 x z); sp.
    generalize (X5 x z); intro p; apply nuprli_implies_nuprl in p; sp; allapply nuprl_refl; sp.
    apply X6 with (y := y).
    apply inhabited_if_inhabited_type with (U := mkc_apply2 R0 x y) (T := mkc_apply2 R0 x y); sp.
    generalize (X5 x y); intro p; apply nuprli_implies_nuprl in p; sp; allapply nuprl_refl; sp.
    apply inhabited_if_inhabited_type with (U := mkc_apply2 R0 y z) (T := mkc_apply2 R0 y z); sp.
    generalize (X5 y z); intro p; apply nuprli_implies_nuprl in p; sp; allapply nuprl_refl; sp.

  - repnd.
    unfold equality, nuprl.

    exists (fun A A' => {eqa : term-equality & close (univi i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp; try computes_to_value_refl.

    fold (nuprli i).

    assert (forall x y : CTerm,
              {eq : term-equality
               & nuprli i (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) eq}) as f1.
    intros.
    unfold member, equality in equ0.
    generalize (equ0 x y); intro k; exrepnd.
    inversion k1; try not_univ.
    inversion X.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rename x0 into i.
    rw X1 in k0; exrepnd.
    allfold (nuprli j).
    exists eqa; sp.
    (* end of proof of the assert *)

    exists (fun t t' => inhabited (projT1 (f1 t t'))).
    apply CL_ipertype.
    fold (nuprli i).
    unfold per_ipertype.
    exists R1 R2
           (fun t t' => projT1 (f1 t t'));
      sp; try (computes_to_value_refl); try (fold nuprl).

    generalize (f1 x y); intro h; exrepnd; allsimpl; sp.

    unfold is_per_type in equ; unfold sym_type, trans_type in equ; repnd.
    unfold is_per; dands; introv.

    generalize (f1 x y); generalize (f1 y x); intros h1 h2 inh; exrepnd; allsimpl.
    apply inhabited_if_inhabited_type with (U := mkc_apply2 R1 y x) (T := mkc_apply2 R1 y x); sp;
    try (complete (allapply nuprli_implies_nuprl; sp; allapply nuprl_refl; sp)).
    apply equ1.
    apply inhabited_type_if_inhabited with (U := mkc_apply2 R1 x y) (eq := eq); sp;
    try (complete (allapply nuprli_implies_nuprl; sp; allapply nuprl_refl; sp)).

    generalize (f1 x y); generalize (f1 y z); generalize (f1 x z); intros h1 h2 h3 inh1 inh2; exrepnd; allsimpl.
    apply inhabited_if_inhabited_type with (U := mkc_apply2 R1 x z) (T := mkc_apply2 R1 x z); sp;
    try (complete (allapply nuprli_implies_nuprl; sp; allapply nuprl_refl; sp)).
    apply equ with (y := y).
    apply inhabited_type_if_inhabited with (U := mkc_apply2 R1 x y) (eq := eq); sp;
    try (complete (allapply nuprli_implies_nuprl; sp; allapply nuprl_refl; sp)).
    apply inhabited_type_if_inhabited with (U := mkc_apply2 R1 y z) (eq := eq0); sp;
    try (complete (allapply nuprli_implies_nuprl; sp; allapply nuprl_refl; sp)).
(*Error: Universe inconsistency.*)
[Admitted.]
*)

Lemma type_mkc_pertype {p} :
  forall lib (R : @CTerm p),
    type lib (mkc_pertype R)
    <=> (forall x y, type lib (mkc_apply2 R x y))
      # is_per_type lib R.
Proof.
  introv.
  unfold type.
  rw @tequality_mkc_pertype; split; sp.
  rw @fold_type; sp.
  unfold type; sp.
  unfold type; sp.
Qed.

Lemma type_mkc_ipertype {p} :
  forall lib (R : @CTerm p),
    type lib (mkc_ipertype R)
    <=> (forall x y, type lib (mkc_apply2 R x y))
      # is_per_type lib R.
Proof.
  introv.
  unfold type.
  rw @tequality_mkc_ipertype; split; sp.
Qed.

Lemma type_mkc_spertype {p} :
  forall lib (R : @CTerm p),
    type lib (mkc_spertype R)
    <=> (forall x y, type lib (mkc_apply2 R x y))
        # (forall x y z,
             inhabited_type lib (mkc_apply2 R x z)
             -> tequality lib (mkc_apply2 R x y) (mkc_apply2 R z y))
        # (forall x y z,
             inhabited_type lib (mkc_apply2 R y z)
             -> tequality lib (mkc_apply2 R x y) (mkc_apply2 R x z))
        # is_per_type lib R.
Proof.
  introv.
  unfold type.
  rw @tequality_mkc_spertype; split; sp.
Qed.

Lemma inhabited_type_cequivc {p} :
  forall lib (a b : @CTerm p),
    cequivc lib a b
    -> inhabited_type lib a
    -> inhabited_type lib b.
Proof.
  introv ceq inh.
  allunfold @inhabited_type; exrepnd.
  allunfold @member.
  exists t.
  apply cequivc_preserving_equality with (A := a); sp.
Qed.

Lemma inhabited_type_respects_cequivc {p} :
  forall lib, respects1 (@cequivc p lib) (inhabited_type lib).
Proof.
  introv; introv.
  apply inhabited_type_cequivc.
Qed.
Hint Resolve inhabited_type_respects_cequivc : respects.

Lemma inhabited_type_tequality {p} :
  forall lib (a b : @CTerm p),
    tequality lib a b
    -> inhabited_type lib a
    -> inhabited_type lib b.
Proof.
  introv teq inh.
  allunfold @inhabited_type; exrepnd.
  allunfold @tequality; exrepnd.
  allunfold @member.
  allunfold @equality; exrepnd.
  exists t.
  generalize (nuprl_uniquely_valued lib a eq eq0); intro i; repeat (dest_imp i hyp).
  apply nuprl_refl with (t2 := b); sp.
  exists eq; sp.
  apply nuprl_refl with (t2 := a); sp.
  apply nuprl_sym; sp.
  rw i; sp.
Qed.

Lemma iff_inhabited_type_if_pertype_eq_or_ceq {p} :
  forall lib (R1 R2 : @CTerm p) i,
    (equality lib (mkc_pertype R1) (mkc_pertype R2) (mkc_uni i)
     [+] cequivc lib (mkc_pertype R1) (mkc_pertype R2))
    -> forall x y,
         inhabited_type lib (mkc_apply2 R1 x y)
          <=> inhabited_type lib (mkc_apply2 R2 x y).
Proof.
  introv or.
  introv.
  split; intro inh; repdors.

  apply equality_in_uni in or0.
  rw @tequality_mkc_pertype in or0; repnd.
  rw <- or3; sp.

  generalize (cequivc_mkc_pertype lib (mkc_pertype R1) (mkc_pertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  apply inhabited_type_cequivc with (a := mkc_apply2 R1 x y); sp.

  apply equality_in_uni in or0.
  rw @tequality_mkc_pertype in or0; repnd.
  rw or3; sp.

  generalize (cequivc_mkc_pertype lib (mkc_pertype R1) (mkc_pertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  apply inhabited_type_cequivc with (a := mkc_apply2 b x y); sp.
  apply cequivc_sym; sp.
Qed.

(*
Lemma tequality_mkc_apply2_if_pertype_eq_or_ceq :
  forall R1 R2 i,
    (equality lib (mkc_ipertype R1) (mkc_ipertype R2) (mkc_uni i)
     [+] cequivc (mkc_ipertype R1) (mkc_ipertype R2))
    -> forall x y : CTerm,
         (type lib (mkc_apply2 R1 x y) [+] type lib (mkc_apply2 R2 x y))
         -> tequality lib (mkc_apply2 R1 x y)
                      (mkc_apply2 R2 x y).
Proof.
  introv eq.
  introv typ.
  destruct eq.

  apply equality_in_uni in e.
  rw tequality_mkc_ipertype in e; sp.

  generalize (cequivc_mkc_ipertype lib (mkc_ipertype R1) (mkc_ipertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  destruct typ.
  apply type_respects_cequivc_right; sp.
  apply type_respects_cequivc_left; sp.
  apply cequivc_sym; sp.
Qed.
*)


Lemma equality_in_mkc_pertype {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_pertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2)
         # is_per_type lib R
         # (forall x y, type lib (mkc_apply2 R x y))).
Proof.
  intros; unfold inhabited_type; split; intro i; exrepnd.

  - unfold equality, nuprl in i; exrepnd.
    inversion i1; subst; try not_univ.
    dest_per.
    allfold (@nuprl p lib).
    computes_to_value_isvalue.
    rw pereq in i0.
    clear typ2 inhiff eq2.
    unfold inhabited in i0; exrepnd.
    dands.

    exists t; unfold member, equality; exists (eq1 t1 t2); sp.

    generalize (is_per_type_iff_is_per lib R1 eq1); introv iff.
    dest_imp iff hyp.
    rw <- iff; sp.

    introv.
    unfold type, tequality.
    exists (eq1 x y); sp.

  - unfold member, equality in i2; exrepnd.
    generalize (choice_spteq lib (mkc_apply2 R) (mkc_apply2 R)); intro fn.
    dest_imp fn hyp; exrepnd.
    generalize (fn0 t1 t2); intro n.
    pose proof (nuprl_uniquely_valued lib (mkc_apply2 R t1 t2) eq (f t1 t2)) as eqt.
    repeat (dest_imp eqt hyp).

    exists (fun a b => inhabited (f a b)); sp;
    try (complete (rw eqt in i0; exists t; sp)).

    apply CL_pertype; unfold per_pertype.
    allfold (@nuprl p lib).
    exists R R f f; sp;
    try (spcast; complete computes_to_value_refl).

    generalize (is_per_type_iff_is_per lib R f); introv iff.
    dest_imp iff hyp.
    rw iff; sp.
Qed.

Lemma equality_in_mkc_pertype2 {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_pertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2) # type lib (mkc_pertype R)).
Proof.
  introv.
  rw @equality_in_mkc_pertype.
  rw @type_mkc_pertype; split; sp.
Qed.

Lemma equality_in_mkc_ipertype {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_ipertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2)
         # is_per_type lib R
         # (forall x y, type lib (mkc_apply2 R x y))).
Proof.
  intros; unfold inhabited_type; split; intro i; exrepnd.

  - unfold equality, nuprl in i; exrepnd.
    inversion i1; subst; try not_univ.
    dest_per.
    allfold (@nuprl p lib).
    computes_to_value_isvalue.
    rw pereq in i0.
    unfold pertype_eq, inhabited in i0; exrepnd.
    dands.

    exists t; unfold member, equality; exists (eq1 t1 t2); sp.

    generalize (is_per_type_iff_is_per lib R1 eq1 eqtyps); introv iff.
    apply iff; auto.

    introv; exists (eq1 x y); sp.

  - unfold member, equality, nuprl in i2; exrepnd.
    allfold (@nuprl p lib).
    generalize (choice_spteq lib (mkc_apply2 R) (mkc_apply2 R) i); intro fn; exrepnd.
    generalize (fn0 t1 t2); intro n.
    pose proof (nuprl_uniquely_valued lib (mkc_apply2 R t1 t2) eq (f t1 t2)) as eqt.
    repeat (autodimp eqt hyp).

    exists (fun a b => inhabited (f a b)); sp;
    try (complete (rw eqt in i0; exists t; sp)).

    apply CL_ipertype; unfold per_ipertype.
    allfold (@nuprl p lib).
    exists R R f; sp;
    try (spcast; complete computes_to_value_refl).

    generalize (is_per_type_iff_is_per lib R f fn0); introv iff.
    rw iff; sp.
Qed.

Lemma equality_in_mkc_ipertype2 {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_ipertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2) # type lib (mkc_ipertype R)).
Proof.
  introv.
  rw @equality_in_mkc_ipertype.
  rw @type_mkc_ipertype; split; sp.
Qed.

Lemma equality_in_mkc_spertype {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_spertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2)
         # (forall x y, type lib (mkc_apply2 R x y))
         # (forall x y z,
              inhabited_type lib (mkc_apply2 R x z)
              -> tequality lib (mkc_apply2 R x y) (mkc_apply2 R z y))
         # (forall x y z,
              inhabited_type lib (mkc_apply2 R y z)
              -> tequality lib (mkc_apply2 R x y) (mkc_apply2 R x z))
         # is_per_type lib R).
Proof.
  intros.
  rw <- @type_mkc_spertype.
  split; intro i; exrepnd.

  - applydup @inhabited_implies_tequality in i as ty; dands; auto.
    unfold equality, nuprl in i; exrepnd.
    inversion i1; subst; try not_univ.
    dest_per.
    allfold (@nuprl p lib).
    computes_to_value_isvalue.
    rw pereq in i0.
    unfold pertype_eq, inhabited in i0; exrepnd.

    exists t; unfold member, equality; exists (eq1 t1 t2); sp.

  - rw @type_mkc_spertype in i; repnd.
    unfold inhabited_type in i0; exrepnd.
    unfold member, equality, nuprl in i4; exrepnd.
    allfold (@nuprl p lib).
    generalize (choice_spteq lib (mkc_apply2 R) (mkc_apply2 R) i1); intro fn; exrepnd.
    generalize (fn0 t1 t2); intro n.
    pose proof (nuprl_uniquely_valued lib (mkc_apply2 R t1 t2) eq (f t1 t2)) as eqt.
    repeat (autodimp eqt hyp).

    exists (fun a b => inhabited (f a b)); sp;
    try (complete (rw eqt in i0; exists t; sp)).

    apply CL_spertype; unfold per_spertype.
    allfold (@nuprl p lib).
    exists R R f; dands; introv;
    try (spcast; complete computes_to_value_refl);
    try (complete sp).

    introv inh.
    generalize (fn0 x z); intro e.
    apply inhabited_type_if_inhabited in e; auto.
    apply i2 with (y := y) in e.
    rw <- @tequality_iff_nuprl in e; exrepnd.
    generalize (fn0 x y); intro nu.
    generalize (nuprl_uniquely_valued lib (mkc_apply2 R x y) eq0 (f x y));
      intro eqs; repeat (autodimp eqs hyp).
    apply nuprl_refl in e0; auto.
    apply nuprl_ext with (eq1 := eq0); auto.

    introv inh.
    generalize (fn0 y z); intro e.
    apply inhabited_type_if_inhabited in e; auto.
    apply i3 with (x := x) in e.
    rw <- @tequality_iff_nuprl in e; exrepnd.
    generalize (fn0 x y); intro nu.
    generalize (nuprl_uniquely_valued lib (mkc_apply2 R x y) eq0 (f x y));
      intro eqs; repeat (autodimp eqs hyp).
    apply nuprl_refl in e0; auto.
    apply nuprl_ext with (eq1 := eq0); auto.

    generalize (is_per_type_iff_is_per lib R f fn0); introv iff.
    rw iff; sp.
Qed.

Lemma equality_in_mkc_spertype2 {p} :
  forall lib (t1 t2 R : @CTerm p),
    equality lib t1 t2 (mkc_spertype R)
    <=> (inhabited_type lib (mkc_apply2 R t1 t2)
         # type lib (mkc_spertype R)).
Proof.
  intros.
  rw @equality_in_mkc_spertype.
  rw @type_mkc_spertype; sp.
Qed.



(*
Lemma equality_in_mkc_esquash :
  forall T a b,
    equality lib a b (mkc_esquash T)
    <=> (computes_to_valc a mkc_axiom
         # computes_to_valc b mkc_axiom
         # inhabited_type lib T).
Proof.
  introv; split; intro i.

  - unfold equality, nuprl in i; exrepnd.
    inversion i1; subst; try not_univ.
    allunfold per_esquash; exrepnd.
    allfold nuprl.
    computes_to_value_isvalue.
    rw X1 in i0; exrepnd; sp.
    apply inhabited_type_if_inhabited with (U := A1) (eq := eq1); sp.

  - repnd.
    unfold inhabited_type in i; exrepnd.
    unfold member, equality, nuprl in i2; exrepnd.
    allfold nuprl.
    unfold equality, nuprl.
    exists (fun t t' => computes_to_valc t mkc_axiom
                        # computes_to_valc t' mkc_axiom
                        # inhabited eq); sp.
    apply CL_esquash.
    unfold per_esquash.
    exists T T eq eq; sp; computes_to_value_refl.
    unfold inhabited; exists t; sp.
Qed.
*)

(*
Lemma tequality_mkc_esquash :
  forall T1 T2,
    tequality lib (mkc_esquash T1) (mkc_esquash T2)
    <=> (type T1
         # type T2
         # (inhabited_type lib T1 <=> inhabited_type lib T2)).
Proof.
  introv; split; intro i; repnd.

  - unfold tequality, nuprl in i; exrepnd.
    inversion i0; subst; try not_univ.
    allunfold per_esquash; exrepnd.
    allfold nuprl.
    computes_to_value_isvalue; sp.

    unfold type, tequality.
    exists eq1; sp.

    unfold type, tequality.
    exists eq2; sp.

    allapply inhabited_type_iff_inhabited.
    rw <- X3; rw <- X4; sp.

  - unfold tequality, nuprl.
    exists (fun t t' => computes_to_valc t mkc_axiom
                        # computes_to_valc t' mkc_axiom
                        # inhabited (projT1 i0)).
    apply CL_esquash; unfold per_esquash.
    fold nuprl.
    exists T1 T2 (projT1 i0) (projT1 i1).
    unfold type, tequality in i0, i1; exrepnd; simpl.
    sp; try computes_to_value_refl.
    allapply inhabited_type_iff_inhabited.
    allrw; sp.
Qed.
*)

(*
Lemma mkc_esquash_equality_in_uni :
  forall T1 T2 i,
    equality lib (mkc_esquash T1) (mkc_esquash T2) (mkc_uni i)
    <=> member T1 (mkc_uni i)
      # member T2 (mkc_uni i)
      # (inhabited_type lib T1
         <=>
         inhabited_type lib T2).
Proof.
  introv; split; intro equ; repnd.

  - unfold equality, nuprl in equ; exrepnd.
    inversion equ1; subst; try not_univ.
    inversion X; exrepd.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rename x into i.
    rw X1 in equ0; exrepnd.
    inversion equ2; subst; try not_univ.
    allunfold per_esquash; exrepnd.
    allfold nuprl; allfold (nuprli j).
    computes_to_value_isvalue.

    dands; intros.

    unfold member, equality.
    exists eq; sp.
    rw X1.
    exists eq1; sp.

    unfold member, equality.
    exists eq; sp.
    rw X1.
    exists eq2; sp.

    split; intro l.

    apply inhabited_type_if_inhabited with (U := A2) (eq := eq2); sp.
    apply nuprli_implies_nuprl in X6; sp.
    rw <- X7.
    apply inhabited_if_inhabited_type with (U := A1) (T := A1); sp.
    apply nuprli_implies_nuprl in X5; sp.

    apply inhabited_type_if_inhabited with (U := A1) (eq := eq1); sp.
    apply nuprli_implies_nuprl in X5; sp.
    rw X7.
    apply inhabited_if_inhabited_type with (U := A2) (T := A2); sp.
    apply nuprli_implies_nuprl in X6; sp.

  - repnd.
    unfold equality, nuprl.

    exists (fun A A' => {eqa : term-equality & close (univi i) A A' eqa}); sp.
    apply CL_init.
    exists (S i); simpl; left; sp; try computes_to_value_refl.

    fold (nuprli i).

    assert {eq : term-equality & nuprli i T1 T1 eq} as f1.
    intros.
    unfold member, equality in equ0; exrepnd.
    inversion equ0; try not_univ.
    inversion X.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rename x into i.
    rw X1 in equ2; exrepnd.
    allfold (nuprli j).
    exists eqa; sp.
    (* end of proof of the assert *)

    assert {eq : term-equality & nuprli i T2 T2 eq} as f2.
    intros.
    unfold member, equality in equ1; exrepnd.
    inversion equ1; try not_univ.
    inversion X.
    allrw univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    rename x into i.
    rw X1 in equ2; exrepnd.
    allfold (nuprli j).
    exists eqa; sp.
    (* end of proof of the assert *)

    exrepnd.
    exists (fun t t' => computes_to_valc t mkc_axiom
                        # computes_to_valc t' mkc_axiom
                        # inhabited eq0).
    apply CL_esquash.
    fold (nuprli i).
    unfold per_esquash.
    exists T1 T2 eq0 eq;
      sp; try (computes_to_value_refl); try (fold nuprl).

    split; intro p.

    apply inhabited_if_inhabited_type with (U := T2) (T := T2); sp;
    try (complete (allapply nuprli_implies_nuprl; sp)).
    rw <- equ.
    apply inhabited_type_if_inhabited with (U := T1) (eq := eq0); sp;
    try (complete (allapply nuprli_implies_nuprl; sp)).

    apply inhabited_if_inhabited_type with (U := T1) (T := T1); sp;
    try (complete (allapply nuprli_implies_nuprl; sp)).
    rw equ.
    apply inhabited_type_if_inhabited with (U := T2) (eq := eq); sp;
    try (complete (allapply nuprli_implies_nuprl; sp)).
(*Error: Universe inconsistency.*)
[Admitted.]
*)

(*
Lemma tequality_esquash_apply2_if_tequality_pertype :
  forall R1 R2 t1 t2 t3 t4,
    tequality
      (mkc_equality t1 t2 (mkc_pertype R1))
      (mkc_equality t3 t4 (mkc_pertype R2))
    -> tequality
         (mkc_esquash (mkc_apply2 R1 t1 t2))
         (mkc_esquash (mkc_apply2 R2 t3 t4)).
Proof.
  introv teq.
  allrw tequality_mkc_equality; repnd.
  allrw tequality_mkc_pertype; repnd.
  allrw equality_in_mkc_pertype; repnd.
  rw tequality_mkc_esquash; dands; try (complete sp).
  destruct teq1.
  split; intro i.

  dest_imp p hyp.

  dest_imp p0 hyp.
  dands; try (complete sp).
  apply is_per_type_iff with (R1 := R1); sp.
Qed.
*)

(*
Lemma member_in_mkc_esquash :
  forall a T,
    member a (mkc_esquash T)
    <=> (computes_to_valc a mkc_axiom
         # inhabited_type lib T).
Proof.
  intros.
  unfold member.
  rw equality_in_mkc_esquash; split; sp.
Qed.
*)

(*
Lemma member_esquash_iff :
  forall T,
    inhabited_type lib T <=> member lib mkc_axiom (mkc_esquash T).
Proof.
  intros.
  rw member_in_mkc_esquash; split; sp.
  computes_to_value_refl.
Qed.
*)

Lemma equality_in_w {p} :
  forall lib (s1 s2 : @CTerm p) A v B,
    equality lib s1 s2 (mkc_w A v B)
    <=>
    {eqa : term-equality
     , {eqb : (forall a a' : CTerm, forall e : eqa a a', term-equality)
        , nuprl lib A A eqa
        # (forall a a' : CTerm,
           forall e : eqa a a',
             nuprl lib (substc a v B) (substc a' v B) (eqb a a' e))
        # weq lib eqa eqb s1 s2}}.
Proof.
  introv; sp_iff Case; introv e.

  - unfold equality in e; exrepnd.
    unfold nuprl in e1.
    inversion e1; try not_univ.
    allunfold @per_w; allunfold @type_family; exrepnd.
    computes_to_value_isvalue.
    allfold (@nuprl p lib).
    exists eqa eqb; sp.
    allunfold @eq_term_equals; discover; sp.

  - exrepnd.
    exists (weq lib eqa eqb); sp.
    apply CL_w.
    exists eqa eqb; sp.
    exists A A v v B B; sp; spcast; computes_to_value_refl.
Qed.

Lemma iff_inhabited_type_if_pertype_cequorsq {p} :
  forall lib (R1 R2 : @CTerm p) i,
    equorsq lib (mkc_pertype R1) (mkc_pertype R2) (mkc_uni i)
    -> forall x y,
         inhabited_type lib (mkc_apply2 R1 x y)
          <=> inhabited_type lib (mkc_apply2 R2 x y).
Proof.
  unfold equorsq; introv or.
  introv.
  split; intro inh; repdors.

  apply equality_in_uni in or0.
  rw @tequality_mkc_pertype in or0; repnd.
  rw <- or3; sp.

  spcast.
  generalize (cequivc_mkc_pertype lib (mkc_pertype R1) (mkc_pertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  apply inhabited_type_cequivc with (a := mkc_apply2 R1 x y); sp.

  apply equality_in_uni in or0.
  rw @tequality_mkc_pertype in or0; repnd.
  rw or3; sp.

  spcast.
  generalize (cequivc_mkc_pertype lib (mkc_pertype R1) (mkc_pertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  apply inhabited_type_cequivc with (a := mkc_apply2 b x y); sp.
  apply cequivc_sym; sp.
Qed.

Lemma iff_inhabited_type_if_ipertype_cequorsq {p} :
  forall lib (R1 R2 : @CTerm p) i,
    (forall x y : CTerm, type lib (mkc_apply2 R1 x y))
    -> equorsq lib (mkc_ipertype R1) (mkc_ipertype R2) (mkc_uni i)
    -> forall x y, tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y).
Proof.
  unfold equorsq; introv istype or; introv.
  repdors.

  apply equality_in_uni in or0.
  rw @tequality_mkc_ipertype in or0; repnd; sp.

  spcast.
  generalize (cequivc_mkc_ipertype lib (mkc_ipertype R1) (mkc_ipertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  generalize (istype x y); intro t.
  apply cequivc_sym in ceq; rwg ceq; sp.
Qed.

Lemma iff_inhabited_type_if_spertype_cequorsq {p} :
  forall lib (R1 R2 : @CTerm p) i,
    (forall x y : CTerm, type lib (mkc_apply2 R1 x y))
    -> equorsq lib (mkc_spertype R1) (mkc_spertype R2) (mkc_uni i)
    -> forall x y, tequality lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y).
Proof.
  unfold equorsq; introv istype or; introv.
  repdors.

  apply equality_in_uni in or0.
  rw @tequality_mkc_spertype in or0; repnd; sp.

  spcast.
  generalize (cequivc_mkc_spertype lib (mkc_spertype R1) (mkc_spertype R2) R1);
    intro j; repeat (dest_imp j hyp); try (complete computes_to_value_refl); exrepnd.
  computes_to_value_isvalue.
  assert (cequivc lib (mkc_apply2 R1 x y) (mkc_apply2 b x y))
         as ceq
         by (repeat (rw @mkc_apply2_eq); repeat (apply sp_implies_cequivc_apply); sp).
  generalize (istype x y); intro t.
  apply cequivc_sym in ceq; rwg ceq; sp.
Qed.

Lemma equality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib (mkc_function A1 v1 B1)
             (mkc_function A2 v2 B2)
             (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
     # forall a a',
         equality lib a a' A1
         -> equality lib (substc a v1 B1) (substc a' v2 B2) (mkc_uni i)).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold equality, nuprl in teq; exrepnd.
    inversion teq1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    rename eqa into eqi.
    ioneclose; subst; try not_univ.

    one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
    computes_to_value_isvalue; GC.
    dands.

    exists eq; sp.
    allrw.
    exists eqa; sp.

    introv e.
    exists eq; sp.
    allfold (@nuprli p lib j0).
    allrw.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib A3 eqa eq0);
      intro k; repeat (dest_imp k hyp);
      try (complete (apply nuprli_implies_nuprl with (i := j0); sp;
                     allapply @nuprli_refl; sp)).
    rw <- k in e0.
    generalize (tsb a a' e0); intro n.
    exists (feqb a a' e0); sp.

  - Case "<-".
    intro eqs.
    destruct eqs as [eqa eqb].
    unfold equality in eqa; exrepnd.
    inversion eqa1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli p lib j0).

    exists eq; sp.
    allrw.

    generalize (choice_teqi lib j0 A1 v1 B1 v2 B2 eqb); intro n; exrepnd.

    exists (fun t1 t2 =>
              forall a1 a2 : CTerm,
              forall e : eqa a1 a2,
                f a1 a2
                  (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)
                  (mkc_apply t1 a1) (mkc_apply t2 a2)).
    unfold nuprli.
    apply CL_func; fold (@nuprli p lib j0).
    unfold per_func.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).
Qed.

Lemma equality_in_function2 {p} :
  forall lib (f g : @CTerm p) A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib (mkc_function A v B)
     # (forall a a',
          equality lib a a' A
          -> equality lib (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv.
  rw @equality_in_function; split; intro k; repnd; dands; try (complete sp).

  unfold type; rw @tequality_function; sp.

  rw @tequality_function in k0; sp.

  rw @tequality_function in k0; sp.
Qed.

(* end hide *)

(**

  Using the Coq induction principle we obtain for [weq], we can prove
  the following induction principle for our W types.  The then use
  this principle to prove the [rule_w_induction] rule below.

*)

Lemma w_ind_eq {p} :
  forall lib (A : @CTerm p) va B (Q : CTerm -> CTerm -> [U]),
    (forall t1 t2 t3 t4, cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q t1 t2 -> Q t3 t4)
    -> (forall a1 a2 f1 f2,
          equality lib a1 a2 A
          -> equality lib f1 f2 (mkc_fun (substc a1 va B) (mkc_w A va B))
          -> (forall b1 b2,
                equality lib b1 b2 (substc a1 va B)
                -> Q (mkc_apply f1 b1) (mkc_apply f2 b2))
          -> Q (mkc_sup a1 f1) (mkc_sup a2 f2))
    -> (forall w1 w2, equality lib w1 w2 (mkc_w A va B) -> Q w1 w2).
Proof.
  introv ceq ind e.
  rw @equality_in_w in e; exrepnd.
  induction e1; spcast.
  apply ceq with (t1 := mkc_sup a f) (t2 := mkc_sup a' f');
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa a' a')
         as e'
         by (eapply equality_eq_refl; eauto;
             eapply equality_eq_sym; eauto).

  apply ind; try (complete (exists eqa; sp)).

  rw <- @fold_mkc_fun.
  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb a a' e); sp.
  generalize (e2 a a' e); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  introv eq.
  allrw @substc_cnewvar.
  exists (weq lib eqa eqb); sp.
  apply CL_w; unfold per_w; unfold type_family.
  exists eqa eqb; sp.
  exists A A va va B B; sp; spcast; apply computes_to_valc_refl; apply iscvalue_mkc_w.

  (* 3 *)
  introv eq.
  allrw @substc_cnewvar.
  rw @equality_in_w.
  exists eqa eqb; sp.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e2 a a' e); intro n.
  assert (eq_term_equals eq0 (eqb a a' e)) as eqt;
    try (complete (eapply nuprl_uniquely_valued; eauto;
                   allapply @nuprl_refl; sp)).

  (* 4 *)
  introv eq.
  apply_hyp; sp.
  unfold equality in eq; exrepnd.
  generalize (e2 a a' e); intro n.
  assert (eq_term_equals eq0 (eqb a a' e)) as eqt;
    try (complete (eapply nuprl_uniquely_valued; eauto;
                   allapply @nuprl_refl; sp)).
Qed.

(* begin hide *)

Lemma w_ind_eq2 {p} :
  forall lib (A : @CTerm p) va B (Q : CTerm -> [U]),
    (forall t1 t2, cequivc lib t1 t2 -> Q t1 -> Q t2)
    -> (forall a1 a2 f1 f2,
          equality lib a1 a2 A
          -> equality lib f1 f2 (mkc_fun (substc a1 va B) (mkc_w A va B))
          -> (forall b1 b2,
                equality lib b1 b2 (substc a1 va B)
                -> Q (mkc_apply f1 b1))
          -> Q (mkc_sup a1 f1))
    -> (forall w1 w2, equality lib w1 w2 (mkc_w A va B) -> Q w1).
Proof.
  introv ceq ind e.
  generalize (w_ind_eq lib A va B (fun t1 t2 => Q t1)).
  intro h.
  dest_imp h hyp.
  introv c1 c2 q1.
  apply ceq with (t1 := t1); sp.
  apply h with (w2 := w2); sp.
Qed.

Lemma w_ind {p} :
  forall lib (A : @CTerm p) va B (Q : CTerm -> Prop),
    (forall t t', cequivc lib t t' -> Q t -> Q t')
    -> (forall a f,
          member lib a A
          -> member lib f (mkc_fun (substc a va B) (mkc_w A va B))
          -> Q (mkc_sup a f))
    -> (forall w, member lib w (mkc_w A va B) -> Q w).
Proof.
  introv ceq ind m.
  generalize (w_ind_eq lib A va B (fun t1 t2 => Q t1)); intro i.
  apply i with (w2 := w); sp.
  apply ceq with (t := t1); sp.
  apply ind; allapply @equality_refl; sp.
Qed.

Lemma equality_in_pw {o} :
  forall lib (s1 s2 : @CTerm o) P ap A bp ba B cp ca cb C p,
    equality lib s1 s2 (mkc_pw P ap A bp ba B cp ca cb C p)
    <=>
    {eqp : term-equality
     , {eqa : (forall p p' : CTerm, forall ep : eqp p p', term-equality)
     , {eqb : (forall p p' : CTerm,
               forall ep : eqp p p',
               forall a a' : CTerm,
               forall ea : eqa p p' ep a a',
                 term-equality)
        , nuprl lib P P eqp
        # (forall p p' : CTerm,
           forall ep : eqp p p',
             nuprl lib (substc p ap A) (substc p' ap A) (eqa p p' ep))
        # (forall p p' : CTerm,
           forall ep : eqp p p',
           forall a a' : CTerm,
           forall ea : eqa p p' ep a a',
             nuprl lib (lsubstc2 bp p ba a B)
                   (lsubstc2 bp p' ba a' B)
                   (eqb p p' ep a a' ea))
        # (forall p p',
           forall ep : eqp p p',
           forall a a',
           forall ea : eqa p p' ep a a',
           forall b b',
           forall eb : eqb p p' ep a a' ea b b',
             eqp (lsubstc3 cp p ca a cb b C)
                 (lsubstc3 cp p' ca a' cb b' C))
        # eqp p p
        # pweq lib eqp eqa eqb cp ca cb C p s1 s2}}}.
Proof.
  introv; sp_iff Case; introv e.

  - unfold equality in e; exrepnd.
    unfold nuprl in e1.
    inversion e1; try not_univ.
    allunfold @per_pw; allunfold @type_pfamily; exrepnd.
    computes_to_value_isvalue.
    allfold (@nuprl o).
    exists eqp eqa eqb; sp.
    allunfold @eq_term_equals; discover; sp.

  - exrepnd.
    exists (pweq lib eqp eqa eqb cp ca cb C p); sp.
    apply CL_pw.
    exists eqp eqa eqb p p; sp.
    exists cp cp ca ca cb cb C C; sp.
    exists P P ap ap A A bp bp.
    exists ba ba B B; sp; spcast; computes_to_value_refl.
Qed.

Lemma isprog_vars_lsubstc3v3 {p} :
  forall v1 u1 v2 u2 v3 u3 (t : @CVTerm p [v1,v2,v3]),
    isprog_vars
      [u3]
      (lsubst (get_cvterm [v1;v2;v3] t)
              [(v1,get_cterm u1),(v2,get_cterm u2),(v3,mk_var u3)]).
Proof.
  introv.
  destruct_cterms.
  rw @isprog_vars_eq; simpl; dands.

  generalize (eqvars_free_vars_disjoint x1 [(v1, x0), (v2, x), (v3, mk_var u3)]);
    introv eqv.
  rw eqvars_prop in eqv.
  rw subvars_prop; introv k.
  rw in_single_iff.
  apply eqv in k; clear eqv.
  apply isprog_vars_eq in i1; repnd.
  rw in_app_iff in k; rw in_remove_nvars in k; repdors; repnd.

  simpl in k0; repeat (rw not_over_or in k0); repnd.
  rw subvars_prop in i2.
  apply i2 in k1; simpl in k1; sp.

  revert k; simpl; boolvar; simpl;
  allrw in_app_iff; allrw in_single_iff; allrw in_remove_nvar; repnd;
  allrw @isprog_eq; allunfold @isprogram; repnd; allrw; simpl;
  intro k; repdors; try (complete sp).

  apply isprog_vars_eq in i1; repnd.
  apply lsubst_wf_iff; sp.
  unfold wf_sub, sub_range_sat; simpl; introv k; repdors; cpx;
  allrw @isprog_eq; allunfold @isprogram; sp.
Qed.

Definition lsubstc3v3 {p} (v1 : NVar) (u1 : @CTerm p)
                      (v2 : NVar) (u2 : CTerm)
                      (v3 : NVar) (u3 : NVar)
                      (t : CVTerm [v1;v2;v3]) : CVTerm [u3] :=
  exist (isprog_vars [u3])
        (lsubst (get_cvterm [v1;v2;v3] t)
                [(v1,get_cterm u1),(v2,get_cterm u2),(v3,mk_var u3)])
        (isprog_vars_lsubstc3v3 v1 u1 v2 u2 v3 u3 t).

Lemma lsubst_mk_pw {o} :
  forall (P : @NTerm o) ap A bp ba B cp ca cb C p sub,
    prog_sub sub
    -> isprog P
    -> isprog_vars [ap] A
    -> isprog_vars [bp;ba] B
    -> isprog_vars [cp;ca;cb] C
    -> isprog_vars (dom_sub sub) p
    -> lsubst (mk_pw P ap A bp ba B cp ca cb C p) sub
       = mk_pw P ap A bp ba B cp ca cb C (lsubst p sub).
Proof.
  introv ps iP iA iB iC ip.
  change_to_lsubst_aux4.
  simpl.
  allrw @fold_nobnd.
  rw @fold_pw; simpl.
  allrw @sub_filter_nil_r.

  assert (lsubst_aux P sub = P) as eqP.
  apply lsubst_aux_trivial; introv i; discover; dands; try (complete sp).
  intro j.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  rw iP0 in j; sp.
  rw eqP.

  assert (lsubst_aux A (sub_filter sub [ap]) = A) as eqA.
  apply lsubst_aux_trivial; introv i.
  apply in_sub_filter in i; repnd; discover; dands; try (complete sp).
  intro j.
  rw @isprog_vars_eq in iA; repnd.
  rw subvars_prop in iA0; apply iA0 in j; sp.
  rw eqA.

  assert (lsubst_aux B (sub_filter sub [bp,ba]) = B) as eqB.
  apply lsubst_aux_trivial; introv i.
  apply in_sub_filter in i; repnd; discover; dands; try (complete sp).
  intro j.
  rw @isprog_vars_eq in iB; repnd.
  rw subvars_prop in iB0; apply iB0 in j; sp.
  rw eqB.

  assert (lsubst_aux C (sub_filter sub [cp,ca,cb]) = C) as eqC.
  apply lsubst_aux_trivial; introv i.
  apply in_sub_filter in i; repnd; discover; dands; try (complete sp).
  intro j.
  rw @isprog_vars_eq in iC; repnd.
  rw subvars_prop in iC0; apply iC0 in j; sp.
  rw eqC.

  sp.
Qed.

Ltac cpx2 :=
  match goal with
    | [ H1 : closed ?x, H2 : LIn ?v (free_vars ?x) |- _ ] =>
        rewrite H1 in H2; simpl in H2; complete (destruct H2)
  end.

Lemma substc_mkc_pw_vs {o} :
  forall (p : @CTerm o) a b v P ap A bp ba B cp ca cb C,
    !LIn v (bound_vars (get_cvterm [cp;ca;cb] C))
    -> substc b v
              (mkc_pw_vs [v] P ap A bp ba B cp ca cb C
                         (lsubstc3v3 cp p ca a cb v C))
       = mkc_pw P ap A bp ba B cp ca cb C (lsubstc3 cp p ca a cb b C).
Proof.
  introv niv.
  destruct_cterms; simpl.
  apply cterm_eq; simpl.
  unfold csubst, subst; simpl.
  rw @lsubst_mk_pw;
    try (complete sp);
    try (complete (unfold prog_sub, sub_range_sat; simpl; sp; cpx; rw @isprogram_eq; sp)).

  rw @simple_lsubst_lsubst; simpl.

  assert (lsubst x2 [(v, x0)] = x2) as eq.
  rw @lsubst_trivial; allsimpl; try (complete sp); introv k; repdors; cpx.
  allrw @isprog_eq; dands; try (complete sp); allunfold @isprogram; repnd; allrw; sp.
  rw eq; clear eq.

  assert (lsubst x1 [(v, x0)] = x1) as eq.
  rw @lsubst_trivial; allsimpl; try (complete sp); introv k; repdors; cpx.
  allrw @isprog_eq; dands; try (complete sp); allunfold @isprogram; repnd; allrw; sp.
  rw eq; clear eq.

  assert (lsubst (mk_var v) [(v, x0)] = x0) as eq.
  change_to_lsubst_aux4; simpl; boolvar; sp.
  rw eq; clear eq.

  assert (lsubst x3 [(cp, x2), (ca, x1), (cb, x0), (v, x0)]
          = lsubst x3 [(cp, x2), (ca, x1), (cb, x0)]) as eq.
  clear niv.
  generalize (in_deq NVar deq_nvar v [cp,ca,cb]); intro k; destruct k as [k | k]; simpl in k.
  (* v in list *)
  assert ([(cp, x2), (ca, x1), (cb, x0), (v, x0)] = snoc [(cp, x2), (ca, x1), (cb, x0)] (v, x0)) as e by sp.
  rw e; clear e.
  rw @lsubst_snoc_dup; try (complete sp).
  introv j; simpl in j; repdors; cpx; allrw @isprog_eq; sp.
  allrw @isprog_eq; sp.
  (* v not in list *)
  allrw not_over_or; repnd.
  allrw @isprog_vars_eq; repnd.
  allrw subvars_prop; allsimpl.
  rw @simple_lsubst_trim.
  symmetry.
  rw @simple_lsubst_trim.
  simpl; boolvar; try (complete sp); discover; repdors; try subst; try (complete sp).
  introv j; simpl in j; repdors; cpx; allrw @isprog_eq; allunfold @isprogram; repnd; allrw; simpl; try (complete sp).
  introv j; simpl in j; repdors; cpx; allrw @isprog_eq; allunfold @isprogram; repnd; allrw; simpl; try (complete sp).
  rw eq; sp.

  introv k; repdors; cpx; try (complete sp);
  allrw @isprog_eq; allunfold @isprogram; repnd; allrw; sp; simpl.
  rw disjoint_singleton_l.
  exact niv.

  introv k; repdors; cpx; try (complete sp); allrw @isprog_eq; sp.

  clear niv; simpl; rw @isprog_vars_eq; simpl; sp.

  rw @isprog_vars_eq in i3; repnd.
  rw subvars_prop in i6.
  generalize (eqvars_free_vars_disjoint x3 [(cp, x2), (ca, x1), (cb, mk_var v)]); intro eqv.
  rw subvars_prop; introv j; rw eqvars_prop in eqv; apply eqv in j.
  rw in_single_iff.
  rw in_app_iff in j; rw in_remove_nvars in j; repdors; repnd.
  simpl in j0; repeat (rw not_over_or in j0); repnd; discover; allsimpl; sp.
  apply in_sub_free_vars in j; exrepnd.
  revert j0; simpl; boolvar; simpl; introv k; repdors; cpx;
  allrw @isprog_eq; allunfold @isprogram; repnd; try cpx2.

  allrw @isprog_eq; allrw @isprog_vars_eq; allunfold @isprogram; repnd.
  apply lsubst_wf_iff; sp.
  unfold wf_sub, sub_range_sat; simpl; introv k; repdors; cpx.
Qed.

Lemma param_w_ind {o} :
  forall lib (P : @CTerm o) ap A bp ba B cp ca cb C (Q : CTerm -> CTerm -> CTerm -> [U]),
    (forall p t1 t2 t3 t4, cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q p t1 t2 -> Q p t3 t4)
    -> (forall p a1 a2 f1 f2 vb,
       equality lib a1 a2 (substc p ap A)
       -> equality lib f1 f2 (mkc_function
                            (lsubstc2 bp p ba a1 B)
                            vb
                            (mkc_pw_vs [vb]
                                       P ap A bp ba B cp ca cb C
                                       (lsubstc3v3 cp p ca a1 cb vb C)))
       -> (forall b1 b2,
             equality lib b1 b2 (lsubstc2 bp p ba a1 B)
             -> Q (lsubstc3 cp p ca a1 cb b1 C)
                  (mkc_apply f1 b1)
                  (mkc_apply f2 b2))
       -> Q p
            (mkc_sup a1 f1)
            (mkc_sup a2 f2))
    -> (forall p w1 w2,
          equality lib w1 w2 (mkc_pw P ap A bp ba B cp ca cb C p)
          -> Q p w1 w2).
Proof.
  introv ceq ind e.
  apply equality_in_pw in e; exrepnd.
  induction e0; spcast.
  apply ceq with (t1 := mkc_sup a1 f1) (t2 := mkc_sup a2 f2);
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa p p ep a2 a2)
         as ea2
         by (generalize (e2 p p ep); intro na;
             apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a1); sp;
             apply (equality_eq_sym lib) with (A := substc p ap A) (B := substc p ap A); sp).

  assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp, ca, cb] C))})
         as ev
         by (exists (fresh_var (bound_vars (get_cvterm [cp, ca, cb] C)));
             apply fresh_var_not_in); exrepnd.

  apply ind with (vb := v); try (complete (exists (eqa p p ep); sp)).

  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb p p ep a1 a2 ea); sp.
  generalize (e3 p p ep a1 a2 ea); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  exists (pweq lib eqp eqa eqb cp ca cb C (lsubstc3 cp p ca a1 cb b C)); sp.
  apply CL_pw; unfold per_pw; unfold type_pfamily.
  exists eqp eqa eqb (lsubstc3 cp p ca a1 cb b C) (lsubstc3 cp p ca a1 cb b' C).
  exists cp cp ca ca cb cb C C; sp.
  exists P P ap ap A A.
  exists bp bp ba ba B B; sp; spcast; try (apply computes_to_valc_refl; apply iscvalue_mkc_pw).
  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (apply (nuprl_uniquely_valued lib) with (t := lsubstc2 bp p ba a1 B); sp;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.

  (* 3 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (apply (nuprl_uniquely_valued lib) with (t := lsubstc2 bp p ba a1 B); sp;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  (* 4 *)
  intros b b' eq.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.
Qed.

(* Not as useful as 3 because we don't have any constraint on vb *)
Lemma param_w_ind2 {o} :
  forall lib (P : @CTerm o) ap A bp ba B cp ca cb C (Q : CTerm -> CTerm -> CTerm -> CTerm -> [U]),
    (forall p1 p2 t1 t2 t3 t4,
       cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q p1 p2 t1 t2 -> Q p1 p2 t3 t4)
    -> (forall p1 p2 a1 a2 f1 f2 vb,
       equality lib p1 p2 P
       -> equality lib a1 a2 (substc p1 ap A)
       -> equality lib f1 f2 (mkc_function
                            (lsubstc2 bp p1 ba a1 B)
                            vb
                            (mkc_pw_vs [vb]
                                       P ap A bp ba B cp ca cb C
                                       (lsubstc3v3 cp p1 ca a1 cb vb C)))
       -> (forall b1 b2,
             equality lib b1 b2 (lsubstc2 bp p1 ba a1 B)
             -> Q (lsubstc3 cp p1 ca a1 cb b1 C)
                  (lsubstc3 cp p2 ca a2 cb b2 C)
                  (mkc_apply f1 b1)
                  (mkc_apply f2 b2))
       -> Q p1
            p2
            (mkc_sup a1 f1)
            (mkc_sup a2 f2))
    -> (forall p1 p2 w1 w2,
          equality lib p1 p2 P
          -> equality lib w1 w2 (mkc_pw P ap A bp ba B cp ca cb C p1)
          -> Q p1 p2 w1 w2).
Proof.
  introv ceq ind eqip e.
  apply equality_in_pw in e; exrepnd.
  revert_dependents p2.
  induction e0; spcast.
  introv eqip.
  apply ceq with (t1 := mkc_sup a1 f1) (t2 := mkc_sup a2 f2);
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa p p ep a2 a2)
         as ea2
         by (generalize (e2 p p ep); intro na;
             apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a1); sp;
             eapply equality_eq_sym; eauto).

  assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp, ca, cb] C))})
         as ev
         by (exists (fresh_var (bound_vars (get_cvterm [cp, ca, cb] C)));
             apply fresh_var_not_in); exrepnd.

  apply ind with (vb := v); try (complete sp); try (complete (exists (eqa p p ep); sp)).

  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb p p ep a1 a2 ea); sp.
  generalize (e3 p p ep a1 a2 ea); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  exists (pweq lib eqp eqa eqb cp ca cb C (lsubstc3 cp p ca a1 cb b C)); sp.
  apply CL_pw; unfold per_pw; unfold type_pfamily.
  exists eqp eqa eqb (lsubstc3 cp p ca a1 cb b C) (lsubstc3 cp p ca a1 cb b' C).
  exists cp cp ca ca cb cb C C; sp.
  exists P P ap ap A A.
  exists bp bp ba ba B B; sp; spcast; try (apply computes_to_valc_refl; apply iscvalue_mkc_pw).
  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.

  (* 3 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  (* 4 *)
  intros b b' eq.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  generalize (equality_eq lib P p p2 eqp); intro ip.
  dest_imp ip hyp.
  apply ip in eqip; clear ip.

  assert (eqa p p2 eqip a1 a2) as eqia.
  generalize (e2 p p2 eqip); intro n1.
  generalize (e2 p p ep); intro n2.
  apply nuprl_uniquely_valued with (eq1 := eqa p p2 eqip) in n2.
  dup ea as eqia.
  rw <- n2 in eqia; sp.
  allapply @nuprl_refl; sp.

  assert (eqb p p2 eqip a1 a2 eqia b b') as eqib.
  generalize (e3 p p2 eqip a1 a2 eqia); intro n.
  apply nuprl_refl in n.
  apply @equality_eq with (a := b) (b := b') in n.
  rw <- n in eq; sp.

  generalize (e4 p p2 eqip a1 a2 eqia b b' eqib); intro e.
  exists eqp; sp.
Qed.

(* This version is the most useful one so far *)
Lemma param_w_ind3 {o} :
  forall lib (P : @CTerm o) ap A bp ba B cp ca cb C (Q : CTerm -> CTerm -> CTerm -> CTerm -> [U]),
    (forall p1 p2 t1 t2 t3 t4,
       cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q p1 p2 t1 t2 -> Q p1 p2 t3 t4)
    -> (forall p1 p2 a1 a2 f1 f2 vb,
          !LIn vb (bound_vars (get_cvterm [cp, ca, cb] C))
          -> equality lib p1 p2 P
          -> equality lib a1 a2 (substc p1 ap A)
          -> equality lib f1 f2 (mkc_function
                               (lsubstc2 bp p1 ba a1 B)
                               vb
                               (mkc_pw_vs [vb]
                                          P ap A bp ba B cp ca cb C
                                          (lsubstc3v3 cp p1 ca a1 cb vb C)))
          -> (forall b1 b2,
                equality lib b1 b2 (lsubstc2 bp p1 ba a1 B)
                -> Q (lsubstc3 cp p1 ca a1 cb b1 C)
                     (lsubstc3 cp p2 ca a2 cb b2 C)
                     (mkc_apply f1 b1)
                     (mkc_apply f2 b2))
          -> Q p1
               p2
               (mkc_sup a1 f1)
               (mkc_sup a2 f2))
    -> (forall p1 p2 w1 w2,
          equality lib p1 p2 P
          -> equality lib w1 w2 (mkc_pw P ap A bp ba B cp ca cb C p1)
          -> Q p1 p2 w1 w2).
Proof.
  introv ceq ind eqip e.
  apply equality_in_pw in e; exrepnd.
  revert_dependents p2.
  induction e0; spcast.
  introv eqip.
  apply ceq with (t1 := mkc_sup a1 f1) (t2 := mkc_sup a2 f2);
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa p p ep a2 a2)
         as ea2
         by (generalize (e2 p p ep); intro na;
             apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a1); sp;
             apply (equality_eq_sym lib) with (A := substc p ap A) (B := substc p ap A); sp).

  assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp, ca, cb] C))})
         as ev
         by (exists (fresh_var (bound_vars (get_cvterm [cp, ca, cb] C)));
             apply fresh_var_not_in); exrepnd.

  apply ind with (vb := v); try (complete sp); try (complete (exists (eqa p p ep); sp)).

  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb p p ep a1 a2 ea); sp.
  generalize (e3 p p ep a1 a2 ea); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  exists (pweq lib eqp eqa eqb cp ca cb C (lsubstc3 cp p ca a1 cb b C)); sp.
  apply CL_pw; unfold per_pw; unfold type_pfamily.
  exists eqp eqa eqb (lsubstc3 cp p ca a1 cb b C) (lsubstc3 cp p ca a1 cb b' C).
  exists cp cp ca ca cb cb C C; sp.
  exists P P ap ap A A.
  exists bp bp ba ba B B; sp; spcast; try (apply computes_to_valc_refl; apply iscvalue_mkc_pw).
  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.

  (* 3 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  (* 4 *)
  intros b b' eq.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  assert (eqa p p ep a1 a1)
         as ea1
         by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto;
             allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  generalize (equality_eq lib P p p2 eqp); intro ip.
  dest_imp ip hyp.
  apply ip in eqip; clear ip.

  assert (eqa p p2 eqip a1 a2) as eqia.
  generalize (e2 p p2 eqip); intro n1.
  generalize (e2 p p ep); intro n2.
  apply nuprl_uniquely_valued with (eq1 := eqa p p2 eqip) in n2.
  dup ea as eqia.
  rw <- n2 in eqia; sp.
  allapply @nuprl_refl; sp.

  assert (eqb p p2 eqip a1 a2 eqia b b') as eqib.
  generalize (e3 p p2 eqip a1 a2 eqia); intro n.
  apply nuprl_refl in n.
  apply @equality_eq with (a := b) (b := b') in n.
  rw <- n in eq; sp.

  generalize (e4 p p2 eqip a1 a2 eqia b b' eqib); intro e.
  exists eqp; sp.
Qed.

(* slightly better than 3 because we can provide a list of variables that
 * v has to be disjoint with *)
Lemma param_w_ind4 {o} :
  forall lib (P : @CTerm o) ap A bp ba B cp ca cb C (Q : CTerm -> CTerm -> CTerm -> CTerm -> [U]) vs,
    (forall p1 p2 t1 t2 t3 t4,
       cequivc lib t1 t3 -> cequivc lib t2 t4 -> Q p1 p2 t1 t2 -> Q p1 p2 t3 t4)
    -> (forall p1 p2 a1 a2 f1 f2 vb,
          !LIn vb vs
          -> equality lib p1 p2 P
          -> equality lib a1 a2 (substc p1 ap A)
          -> equality lib f1 f2 (mkc_function
                               (lsubstc2 bp p1 ba a1 B)
                               vb
                               (mkc_pw_vs [vb]
                                          P ap A bp ba B cp ca cb C
                                          (lsubstc3v3 cp p1 ca a1 cb vb C)))
          -> (forall b1 b2,
                equality lib b1 b2 (lsubstc2 bp p1 ba a1 B)
                -> Q (lsubstc3 cp p1 ca a1 cb b1 C)
                     (lsubstc3 cp p2 ca a2 cb b2 C)
                     (mkc_apply f1 b1)
                     (mkc_apply f2 b2))
          -> Q p1
               p2
               (mkc_sup a1 f1)
               (mkc_sup a2 f2))
    -> (forall p1 p2 w1 w2,
          equality lib p1 p2 P
          -> equality lib w1 w2 (mkc_pw P ap A bp ba B cp ca cb C p1)
          -> Q p1 p2 w1 w2).
Proof.
  introv ceq ind eqip e.
  apply equality_in_pw in e; exrepnd.
  revert_dependents p2.
  induction e0; spcast.
  introv eqip.
  apply ceq with (t1 := mkc_sup a1 f1) (t2 := mkc_sup a2 f2);
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa p p ep a2 a2)
         as ea2
         by (generalize (e2 p p ep); intro na;
             apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a1); sp;
             apply (equality_eq_sym lib) with (A := substc p ap A) (B := substc p ap A); sp).

  assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp, ca, cb] C) ++ vs)})
         as ev
         by (exists (fresh_var (bound_vars (get_cvterm [cp, ca, cb] C) ++ vs));
             apply fresh_var_not_in); exrepnd.

  allrw in_app_iff.

  apply ind with (vb := v);
    try (complete sp);
    try (complete (exists (eqa p p ep); sp)).

  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb p p ep a1 a2 ea); sp.
  generalize (e3 p p ep a1 a2 ea); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  exists (pweq lib eqp eqa eqb cp ca cb C (lsubstc3 cp p ca a1 cb b C)); sp.
  apply CL_pw; unfold per_pw; unfold type_pfamily.
  exists eqp eqa eqb (lsubstc3 cp p ca a1 cb b C) (lsubstc3 cp p ca a1 cb b' C).
  exists cp cp ca ca cb cb C C; sp.
  exists P P ap ap A A.
  exists bp bp ba ba B B; sp; spcast; try (apply computes_to_valc_refl; apply iscvalue_mkc_pw).
  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.

  (* 3 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  (* 4 *)
  intros b b' eq.
  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  generalize (equality_eq lib P p p2 eqp); intro ip.
  dest_imp ip hyp.
  apply ip in eqip; clear ip.

  assert (eqa p p2 eqip a1 a2) as eqia.
  generalize (e2 p p2 eqip); intro n1.
  generalize (e2 p p ep); intro n2.
  apply nuprl_uniquely_valued with (eq1 := eqa p p2 eqip) in n2.
  dup ea as eqia.
  rw <- n2 in eqia; sp.
  allapply @nuprl_refl; sp.

  assert (eqb p p2 eqip a1 a2 eqia b b') as eqib.
  generalize (e3 p p2 eqip a1 a2 eqia); intro n.
  apply nuprl_refl in n.
  apply @equality_eq with (a := b) (b := b') in n.
  rw <- n in eq; sp.

  generalize (e4 p p2 eqip a1 a2 eqia b b' eqib); intro e.
  exists eqp; sp.
Qed.

(* Useless *)
Lemma param_w_ind5 {o} :
  forall lib (P : @CTerm o) ap A bp ba B cp ca cb C (Q : CTerm -> CTerm -> [U]),
    (forall p t1 t2,
       cequivc lib t1 t2 -> Q p t1 -> Q p t2)
    -> (forall p1 p2 a1 a2 f1 f2 vb,
          !LIn vb (bound_vars (get_cvterm [cp, ca, cb] C))
          -> equality lib p1 p2 P
          -> equality lib a1 a2 (substc p1 ap A)
          -> equality lib f1 f2 (mkc_function
                               (lsubstc2 bp p1 ba a1 B)
                               vb
                               (mkc_pw_vs [vb]
                                          P ap A bp ba B cp ca cb C
                                          (lsubstc3v3 cp p1 ca a1 cb vb C)))
          -> (forall b1 b2,
                equality lib b1 b2 (lsubstc2 bp p1 ba a1 B)
                -> equality lib p1 p2 P
                -> Q (lsubstc3 cp p1 ca a1 cb b1 C)
                     (mkc_apply f1 b1))
          -> Q p1
               (mkc_sup a1 f1))
    -> (forall p1 p2 w1 w2,
          equality lib p1 p2 P
          -> equality lib w1 w2 (mkc_pw P ap A bp ba B cp ca cb C p1)
          -> Q p1 w1).
Proof.
  introv ceq ind eqip e.
  apply equality_in_pw in e; exrepnd.
  revert_dependents p2.
  induction e0 as [ p t1 t2 ep a1 f1 a2 f2 ea c1 c2 i r ]; spcast.
  introv eqip.
  apply ceq with (t1 := mkc_sup a1 f1);
    try (complete (apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp)).

  assert (eqa p p ep a2 a2)
         as ea2
         by (generalize (e2 p p ep); intro na;
             apply (equality_eq_refl lib) with (A := substc p ap A) (B := substc p ap A) (b := a1); sp;
             apply (equality_eq_sym lib) with (A := substc p ap A) (B := substc p ap A); sp).

  assert ({v : NVar, !LIn v (bound_vars (get_cvterm [cp, ca, cb] C))})
         as ev
         by (exists (fresh_var (bound_vars (get_cvterm [cp, ca, cb] C)));
             apply fresh_var_not_in); exrepnd.

  apply ind with (vb := v) (p2 := p2) (a2 := a2) (f2 := f2);
    try (complete sp); try (complete (exists (eqa p p ep); sp)).

  rw @equality_in_function.
  dands.

  (* 1 *)
  exists (eqb p p ep a1 a2 ea); sp.
  generalize (e3 p p ep a1 a2 ea); intro n.
  apply nuprl_refl in n; sp.

  (* 2 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  exists (pweq lib eqp eqa eqb cp ca cb C (lsubstc3 cp p ca a1 cb b C)); sp.
  apply CL_pw; unfold per_pw; unfold type_pfamily.
  exists eqp eqa eqb (lsubstc3 cp p ca a1 cb b C) (lsubstc3 cp p ca a1 cb b' C).
  exists cp cp ca ca cb cb C C; sp.
  exists P P ap ap A A.
  exists bp bp ba ba B B; sp; spcast; try (apply computes_to_valc_refl; apply iscvalue_mkc_pw).
  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.

  (* 3 *)
  intros b b' eq.
  rw @substc_mkc_pw_vs; simpl; try (complete sp).
  apply equality_in_pw.
  exists eqp eqa eqb; dands; try (complete sp).

  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  apply_hyp.
  unfold equality in eq; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq0 (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  (* 4 *)
  intros b b' eib eip.
  apply r with (b2 := b') (p2 := lsubstc3 cp p2 ca a2 cb b' C).
  unfold equality in eib; exrepnd.
  generalize (e3 p p ep a1 a2 ea); intro n.
  assert (eq_term_equals eq (eqb p p ep a1 a2 ea))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply @nuprl_refl; sp).
  rw <- eqt; sp.

  assert (eqa p p ep a1 a1)
         as ea1 by (eapply equality_eq_refl; eauto).
  apply e4 with (ep := ep) (ea := ea1).
  unfold equality in eib; exrepnd.
  generalize (e3 p p ep a1 a1 ea1); intro n.
  assert (eq_term_equals eq (eqb p p ep a1 a1 ea1))
         as eqt
         by (eapply nuprl_uniquely_valued; eauto; allapply nuprl_refl; sp).
  rw <- eqt; sp.
  eapply equality_eq_refl; eauto.

  generalize (equality_eq lib P p p2 eqp); intro ip.
  dest_imp ip hyp.
  apply ip in eqip; clear ip.

  assert (eqa p p2 eqip a1 a2) as eqia.
  generalize (e2 p p2 eqip); intro n1.
  generalize (e2 p p ep); intro n2.
  apply nuprl_uniquely_valued with (eq1 := eqa p p2 eqip) in n2.
  dup ea as eqia.
  rw <- n2 in eqia; sp.
  allapply @nuprl_refl; sp.

  assert (eqb p p2 eqip a1 a2 eqia b b') as eqib.
  generalize (e3 p p2 eqip a1 a2 eqia); intro n.
  apply nuprl_refl in n.
  apply @equality_eq with (a := b) (b := b') in n.
  rw <- n in eib; sp.

  generalize (e4 p p2 eqip a1 a2 eqia b b' eqib); intro e.
  exists eqp; sp.
Qed.

Inductive equal_in_image {p} lib (A f t1 t2 : @CTerm p) : [U] :=
| eq_in_image_cl :
    forall t,
      equal_in_image lib A f t1 t
      -> equal_in_image lib A f t t2
      -> equal_in_image lib A f t1 t2
| eq_in_image_eq :
    forall a1 a2,
      equality lib a1 a2 A
      -> t1 ~=~(lib) (mkc_apply f a1)
      -> t2 ~=~(lib) (mkc_apply f a2)
      -> equal_in_image lib A f t1 t2.

Lemma equality_in_mkc_image {p} :
  forall lib (t1 t2 T f : @CTerm p),
    equality lib t1 t2 (mkc_image T f)
    <=> (type lib T # equal_in_image lib T f t1 t2).
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    inversion e1; subst; try not_univ.
    allunfold @per_image; exrepnd; spcast; computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    dands.
    exists eqa; sp.
    induction h.
    apply @eq_in_image_cl with (t := t).
    apply IHh1; allrw; sp.
    apply IHh2; allrw; sp.
    apply @eq_in_image_eq with (a1 := a1) (a2 := a2); sp.
    exists eqa; sp.

  - exrepnd.
    unfold type, tequality in e0; exrepnd.
    exists (per_image_eq lib eq f); dands.
    apply CL_image; unfold per_image.
    exists eq T T f f; sp; spcast; sp;
    try (apply computes_to_valc_refl; apply iscvalue_mkc_image).
    induction e.
    apply @image_eq_cl with (t := t); sp.
    apply @image_eq_eq with (a1 := a1) (a2 := a2); sp.
    allunfold @equality; exrepnd.
    generalize (nuprl_uniquely_valued lib T eq eq0); intro h; repeat (dest_imp h hyp).
    rw h; sp.
Qed.

Lemma equal_in_image_prop {p} :
  forall lib (A f t1 t2 : @CTerm p),
    equal_in_image lib A f t1 t2
    -> {a1, a2 : CTerm
        , t1 ~=~(lib) (mkc_apply f a1)
        # t2 ~=~(lib) (mkc_apply f a2)
        # member lib a1 A
        # member lib a2 A}.
Proof.
  introv e.
  induction e; exrepnd.

  exists a0 a2; sp.

  exists a1 a2; sp.
  allapply @equality_refl; sp.
  apply @equality_refl with (t2 := a1); apply equality_sym; sp.
Qed.

Lemma equality_in_mkc_squash {p} :
  forall lib (t1 t2 T : @CTerm p),
    equality lib t1 t2 (mkc_squash T)
    <=> (t1 ===>(lib) mkc_axiom
         # t2 ===>(lib) mkc_axiom
         # inhabited_type lib T).
Proof.
  intros.
  rw @equality_in_mkc_image; split; intro e; exrepnd; spcast.

  - applydup @equal_in_image_prop in e; exrepnd; spcast.

    generalize (cequivc_beta lib nvarx (mk_cv [nvarx] mkc_axiom) a1); intro c1.
    generalize (cequivc_beta lib nvarx (mk_cv [nvarx] mkc_axiom) a2); intro c2.

    allrw @mk_cv_as_cvterm_var.
    allrw @substc_cvterm_var.

    assert (cequivc lib t1 mkc_axiom) as c3.
    eapply cequivc_trans.
    exact e2.
    sp.

    assert (cequivc lib t2 mkc_axiom) as c4.
    eapply cequivc_trans.
    exact e3.
    sp.

    generalize (cequivc_axiom lib mkc_axiom t1); intro i1.
    dest_imp i1 hyp.
    apply computes_to_valc_refl; apply isvalue_axiom.
    dest_imp i1 hyp.
    apply cequivc_sym; sp.

    generalize (cequivc_axiom lib mkc_axiom t2); intro i2.
    dest_imp i2 hyp.
    apply computes_to_valc_refl; apply isvalue_axiom.
    dest_imp i2 hyp.
    apply cequivc_sym; sp.

    sp; try (complete (spcast; sp)).
    exists a1.
    allapply @equality_refl; sp.

  - unfold inhabited_type in e; exrepnd.
    applydup @inhabited_implies_tequality in e2; dands; auto.
    apply eq_in_image_eq with (a1 := t) (a2 := t); auto; spcast.

    apply cequivc_trans with (b := mkc_axiom).
    apply computes_to_valc_implies_cequivc; sp.
    apply cequivc_sym.
    generalize (cequivc_beta lib nvarx (mk_cv [nvarx] mkc_axiom) t); intro c.
    allrw @mk_cv_as_cvterm_var.
    allrw @substc_cvterm_var; sp.

    apply cequivc_trans with (b := mkc_axiom).
    apply computes_to_valc_implies_cequivc; sp.
    apply cequivc_sym.
    generalize (cequivc_beta lib nvarx (mk_cv [nvarx] mkc_axiom) t); intro c.
    allrw @mk_cv_as_cvterm_var.
    allrw @substc_cvterm_var; sp.
Qed.

Lemma tequality_mkc_image {p} :
  forall lib (T1 T2 f1 f2 : @CTerm p),
    tequality lib (mkc_image T1 f1) (mkc_image T2 f2)
    <=> (tequality lib T1 T2 # ccequivc lib f1 f2).
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    inversion teq0; try not_univ; allunfold @per_image; exrepnd.
    computes_to_value_isvalue; sp; try (complete (spcast; sp)).
    exists eqa; sp.

  - unfold tequality in teq0; exrepnd.
    exists (per_image_eq lib eq f1); apply CL_image; unfold per_image.
    exists eq T1 T2 f1 f2; sp; spcast;
    apply computes_to_valc_refl; apply iscvalue_mkc_image.
Qed.

Lemma tequality_mkc_squash {p} :
  forall lib (T1 T2 : @CTerm p),
    tequality lib (mkc_squash T1) (mkc_squash T2)
    <=> tequality lib T1 T2.
Proof.
  introv.
  rw @tequality_mkc_image; split; sp; spcast.
  apply cequivc_refl.
Qed.

Lemma inhabited_function {p} :
  forall lib (A : @CTerm p) v B,
    inhabited_type lib (mkc_function A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # {f : CTerm
        , forall a a',
            equality lib a a' A
            -> equality lib (mkc_apply f a) (mkc_apply f a') (substc a v B)}).
Proof.
  introv; split; intro k.

  - unfold inhabited_type in k; exrepnd.
    rw @equality_in_function in k0; repnd; dands; try (complete sp).
    exists t; sp.

  - exrepnd.
    exists f.
    rw @equality_in_function; sp.
Qed.

Lemma equality_in_function3 {p} :
  forall lib (f g : @CTerm p) A v B,
    equality lib f g (mkc_function A v B)
    <=>
    (type lib A
     # (forall a a',
          equality lib a a' A
          -> tequality lib (substc a v B) (substc a' v B)
             # equality lib (mkc_apply f a) (mkc_apply g a') (substc a v B))).
Proof.
  introv; rw @equality_in_function; split; sp; discover; sp.
Qed.

Lemma weq_implies {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2,
    eq_term_equals eqa1 eqa2
    -> (forall (a a' : CTerm) (ea1 : eqa1 a a') (ea2 : eqa2 a a'),
          eq_term_equals (eqb1 a a' ea1) (eqb2 a a' ea2))
    -> forall t1 t2,
         weq lib eqa1 eqb1 t1 t2
         -> weq lib eqa2 eqb2 t1 t2.
Proof.
  introv eqia eqib weq1.
  induction weq1.

  assert (eqa2 a a') as ea2 by (allrw <-; sp).

  apply @weq_cons
        with
        (a  := a)
        (f  := f)
        (a' := a')
        (f' := f')
        (e  := ea2);
    try (complete sp).

  introv eia.

  apply_hyp.
  generalize (eqib a a' e ea2); intro eqt; allrw; sp.
Qed.

Lemma eq_term_equals_weq {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2,
    eq_term_equals eqa1 eqa2
    -> (forall (a a' : CTerm) (ea1 : eqa1 a a') (ea2 : eqa2 a a'),
          eq_term_equals (eqb1 a a' ea1) (eqb2 a a' ea2))
    -> eq_term_equals (weq lib eqa1 eqb1)
                      (weq lib eqa2 eqb2).
Proof.
  introv eqia eqib.
  unfold eq_term_equals; introv; split; intro k.
  apply @weq_implies with (eqa1 := eqa1) (eqb1 := eqb1); sp.

  apply @weq_implies with (eqa1 := eqa2) (eqb1 := eqb2); sp;
  apply eq_term_equals_sym; sp.
Qed.

Lemma equality_in_w_v1 {p} :
  forall lib A v B (t1 t2 : @CTerm p),
    equality lib t1 t2 (mkc_w A v B)
    <=> {a1, a2, f1, f2 : CTerm
         , t1 ===>(lib) (mkc_sup a1 f1)
         # t2 ===>(lib) (mkc_sup a2 f2)
         # equality lib a1 a2 A
         # equality lib f1 f2 (mkc_fun (substc a1 v B) (mkc_w A v B))
         # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))}.
Proof.
  introv; split; intro e.

  - unfold equality in e; exrepnd.
    inversion e1; try not_univ.
    allunfold @per_w; exrepnd.
    allunfold @type_family; exrepnd.
    allfold (@nuprl p lib).
    computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    destruct h.
    exists a a' f f'; sp.
    exists eqa; sp.
    rw <- @fold_mkc_fun.
    rw @equality_in_function; dands.

    exists (eqb a a' e).
    apply @nuprl_refl with (t2 := substc a' v0 B0); sp.

    intros b1 b2 eib.
    generalize (equality_eq1 lib (substc a v0 B0) (substc a' v0 B0) b1 b2 (eqb a a' e));
      intro k; repeat (dest_imp k hyp).
    discover.
    allrw @substc_cnewvar.
    exists eq; sp.

    intros b1 b2 eib.
    allrw @substc_cnewvar.
    exists eq; sp.
    allrw.
    apply_hyp.
    generalize (equality_eq1 lib (substc a v0 B0) (substc a' v0 B0) b1 b2 (eqb a a' e));
      intro k; repeat (dest_imp k hyp).
    discover; sp.

    allunfold @equality; exrepnd.
    generalize (nuprl_uniquely_valued lib A0 eq0 eqa); introv k; repeat (dest_imp k hyp).
    assert (eqa a0 a'0) as ea by (allrw <-; sp).
    exists (eqb a0 a'0 ea); sp.

  - exrepnd.
    unfold equality in e3; exrepnd.
    rename eq into eqa.

    generalize (choice_teq lib A v B v B e1); intro n; exrepnd.

    exists (weq lib eqa (fun a a' ea => f a a' (eq_equality1 lib a a' A eqa ea e3))); dands.

    apply CL_w; unfold per_w.
    exists eqa.
    exists (fun a a' ea => f a a' (eq_equality1 lib a a' A eqa ea e3)); sp.
    unfold type_family.
    fold (@nuprl p lib).
    exists A A v v B B; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_w))).

    apply @weq_cons with (a := a1) (f := f1) (a' := a2) (f' := f2) (e := e5); sp.
    generalize (n0 a1 a2 (eq_equality1 lib a1 a2 A eqa e5 e3)); intro n.
    rw <- @fold_mkc_fun in e4.
    rw @equality_in_function in e4; repnd.
    generalize (e4 b b'); intro k.
    dest_imp k hyp.
    exists (f a1 a2 (eq_equality1 lib a1 a2 A eqa e5 e3)); sp.
    allapply @nuprl_refl; sp.
    allrw @substc_cnewvar.
    unfold equality in k; exrepnd.
    inversion k1; try not_univ.
    allunfold @per_w; exrepnd.
    allunfold @type_family; exrepnd; allfold (@nuprl p lib).
    computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.

    assert (eq_term_equals eqa0 eqa)
           as eqta by (eapply nuprl_uniquely_valued; eauto).

    assert (forall (a a' : CTerm) (ea : eqa a a') (ea' : eqa0 a a'),
              eq_term_equals (f a a' (eq_equality1 lib a a' A0 eqa ea e3)) (eqb a a' ea'))
           as eqtb.
    introv.
    generalize (n0 a a' (eq_equality1 lib a a' A0 eqa ea e3)); intro n1.
    assert (nuprl lib (substc a v0 B0) (substc a' v0 B0) (eqb a a' ea')) as n2 by sp.
    apply (nuprl_uniquely_valued lib) with (t := substc a v0 B0); sp; allapply @nuprl_refl; sp.
    apply weq_implies with (eqa1 := eqa0) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.
Qed.

Lemma tequality_mkc_w {p} :
  forall lib (A1 : @CTerm p) v1 B1
         A2 v2 B2,
    tequality lib
      (mkc_w A1 v1 B1)
      (mkc_w A2 v2 B2)
    <=>
    (tequality lib A1 A2
     # (forall a1 a2,
        equality lib a1 a2 A1
        -> tequality lib (substc a1 v1 B1) (substc a2 v2 B2))).
Proof.
  introv; split; intro e; repnd.

  - unfold tequality in e; exrepnd.
    unfold nuprl in e0.
    inversion e0; try not_univ.
    allunfold @per_w; exrepnd.
    allunfold @type_family; exrepnd; spcast; allfold (@nuprl p lib).
    computes_to_value_isvalue.
    dands.

    + allapply @tequality_if_nuprl; sp.

    + introv eia.
      generalize (equality_eq1 lib A A' a1 a2 eqa); intro i; dest_imp i hyp.
      rw <- i in eia.
      exists (eqb a1 a2 eia); sp.

  - unfold tequality.
    unfold tequality in e0; exrepnd.
    rename eq into eqa.

    generalize (choice_teq1 lib A1 eqa v1 B1 v2 B2); intro neqb.
    dest_imp neqb hyp; try (complete (allapply @nuprl_refl; sp)).
    dest_imp neqb hyp; exrepnd.
    rename f into eqb.

    exists (weq lib eqa eqb).
    apply CL_w; unfold per_w.
    exists eqa eqb; sp.
    unfold type_family.
    exists A1 A2 v1 v2 B1 B2; dands;
    try (complete sp);
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_w))).
Qed.

Lemma tequality_function_fun {p} :
  forall lib (A : @CTerm p) v B,
    (type lib (mkc_function A v (mk_cv [v] B)) {+} type lib (mkc_fun A B))
    -> tequality lib (mkc_function A v (mk_cv [v] B))
                 (mkc_fun A B).
Proof.
  introv o; repdors.

  apply tequality_respects_alphaeqc_right with (T2 := mkc_function A v (mk_cv [v] B)); sp.

  apply tequality_respects_alphaeqc_left with (T1 := mkc_fun A B); sp.
  apply alphaeqc_sym; sp.
Qed.

Lemma tequality_mkc_fun_dom {p} :
  forall lib (A1 A2 B : @CTerm p),
    tequality lib A1 A2
    -> type lib (mkc_fun A1 B)
    -> tequality lib (mkc_fun A1 B) (mkc_fun A2 B).
Proof.
  introv teqa teqf.
  allrw <- @fold_mkc_fun.
  allrw @tequality_function; repnd; dands; auto.
Qed.

Lemma tequality_fun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    <=>
    (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  intros.
  allrw <- @fold_mkc_fun.
  rw @tequality_function.
  split; intro teq; repnd; dands; auto; introv e.

  - unfold inhabited_type in e; exrepnd.
    generalize (teq t t); intro k; autodimp k hyp.
    repeat (rw @csubst_mk_cv in k); sp.

  - autodimp teq hyp.
    exists a; allapply @equality_refl; sp.
    repeat (rw @csubst_mk_cv); sp.
Qed.

Lemma tequality_mkc_fun_l {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    -> tequality lib A1 A2.
Proof.
  introv Hpart1.
  rw @tequality_fun in Hpart1; sp.
Qed.

Lemma equality_in_fun {p} :
  forall lib (f g A B : @CTerm p),
    equality lib f g (mkc_fun A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # (forall a a',
          equality lib a a' A
          -> equality lib (mkc_apply f a) (mkc_apply g a') B)).
Proof.
  introv.
  rw <- @fold_mkc_fun.
  rw @equality_in_function.
  split; intro k; repnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k1 t t); intro j; autodimp j hyp.
  repeat (rw @csubst_mk_cv in j); sp.

  introv e.
  apply k in e.
  repeat (rw @csubst_mk_cv in e); sp.

  introv e.
  repeat (rw @csubst_mk_cv); sp.
  autodimp k1 hyp.
  exists a; allapply @equality_refl; sp.

  introv e.
  repeat (rw @csubst_mk_cv); sp.
Qed.

Lemma equality_in_product {p} :
  forall lib (p1 p2 : @CTerm p) A v B,
    equality lib p1 p2 (mkc_product A v B)
    <=>
    (type lib A
     # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
     # {a1, a2, b1, b2 : CTerm
        , p1 ===>(lib) (mkc_pair a1 b1)
        # p2 ===>(lib) (mkc_pair a2 b2)
        # equality lib a1 a2 A
        # equality lib b1 b2 (substc a1 v B)}).
Proof.
  introv; split; intro e; exrepnd.

  - unfold equality in e; exrepnd.
    inversion e1; subst; try not_univ.

    one_dest_per_fam eqa feqb A1 A2 v1 v2 B1 B2 c1 c2 tsa tsb eqt.
    allunfold_per; spcast; computes_to_eqval; allfold (@nuprl p lib).
    computes_to_value_isvalue; dands.

    exists eqa; sp.

    introv e.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib A1 eqa eq0); intro k; repeat (dest_imp k hyp).
    rw <- k in e2.
    generalize (tsb a a' e2); intro n.
    exists (feqb a a' e2); sp.

    rw eqt in e0.
    unfold per_product_eq in e0; exrepnd.
    exists a a' b b'; dands; auto.
    exists eqa; sp.
    exists (feqb a a' e); sp.
    generalize (tsb a a' e); intro n.
    allapply @nuprl_refl; sp.

  - unfold type, tequality in e0; exrepnd.
    rename eq into eqa.

    generalize (choice_teq1 lib A eqa v B v B e6 e1);
      intro n; exrepnd.
    rename f into eqb.

    exists (per_product_eq lib eqa eqb).

    dands.

    apply CL_product; fold (@nuprl p lib); unfold per_product.
    exists eqa eqb.

    dands; sp.

    exists A A v v B B; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_product))).

    unfold equality in e5; exrepnd.
    generalize (nuprl_uniquely_valued lib A eq eqa); intro k; repeat (dest_imp k hyp).
    rw k in e0.

    exists a1 a2 b1 b2 e0; dands; auto.

    generalize (n0 a1 a2 e0); intro n1.
    unfold equality in e3; exrepnd.
    generalize (nuprl_uniquely_valued lib (substc a1 v B) eq0 (eqb a1 a2 e0)); intro j; repeat (dest_imp j hyp).
    allapply @nuprl_refl; auto.
    rw j in e7; auto.
Qed.

Lemma equality_in_prod {p} :
  forall lib (p1 p2 A B : @CTerm p),
    equality lib p1 p2 (mkc_prod A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # {a1, a2, b1, b2 : CTerm
        , p1 ===>(lib) (mkc_pair a1 b1)
        # p2 ===>(lib) (mkc_pair a2 b2)
        # equality lib a1 a2 A
        # equality lib b1 b2 B}).
Proof.
  introv.
  rw <- @fold_mkc_prod.
  rw @equality_in_product.
  split; intro k; exrepnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k1 t t); intro j; autodimp j hyp.
  repeat (rw @csubst_mk_cv in j); sp.

  exists a1 a2 b1 b2; dands; auto.
  allrw @csubst_mk_cv; sp.

  introv e.
  repeat (rw @csubst_mk_cv); sp.
  autodimp k1 hyp.
  exists a; allapply @equality_refl; sp.

  exists a1 a2 b1 b2; dands; auto.
  repeat (rw @csubst_mk_cv); sp.
Qed.

Lemma tequality_product {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib (mkc_product A1 v1 B1)
              (mkc_product A2 v2 B2)
    <=>
    (tequality lib A1 A2
     # forall a a', equality lib a a' A1 -> tequality lib (substc a v1 B1) (substc a' v2 B2)).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.
    allunfold_per.
    computes_to_value_isvalue.
    unfold tequality; sp.

    exists eqa; sp.

    assert (eqa a a') as xa
      by (generalize (equality_eq1 lib A A' a a' eqa); intro h;
          dest_imp h hyp;
          try (exists i; auto);
          apply h; auto).
    exists (eqb a a' xa); sp.
    apply c2.

  - Case "<-".
    introv e; exrepnd.
    rename e0 into teqa; rename e into teqb.
    unfold tequality in teqa; exrepnd.
    rename eq into eqa.
    applydup @nuprl_refl in teqa0.
    generalize (choice_teq1 lib A1 eqa v1 B1 v2 B2 teqa1 teqb); intro n; exrepnd.
    rename f into eqb.

    exists (per_product_eq lib eqa eqb).
    apply CL_product; fold @nuprl.
    unfold per_product.
    exists eqa eqb; dands; sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_product))).
Qed.

Lemma tequality_mkc_fun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
              <=> (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_fun.
  rw @tequality_function.
  split; intro k; repnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k t t i0); intro teq.
  allrw @csubst_mk_cv; auto.

  introv e.
  allrw @csubst_mk_cv; auto.
  apply equality_refl in e.
  autodimp k hyp.
  exists a; auto.
Qed.

Lemma tequality_mkc_prod {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_prod A1 B1) (mkc_prod A2 B2)
              <=> (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_prod.
  rw @tequality_product.
  split; intro k; repnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k t t i0); intro teq.
  allrw @csubst_mk_cv; auto.

  introv e.
  allrw @csubst_mk_cv; auto.
  apply equality_refl in e.
  autodimp k hyp.
  exists a; auto.
Qed.

Lemma type_mkc_fun {p} :
  forall lib (A B : @CTerm p),
    type lib (mkc_fun A B) <=> (type lib A # (inhabited_type lib A -> type lib B)).
Proof.
  introv.
  rw @tequality_mkc_fun; sp.
Qed.

Lemma type_mkc_prod {p} :
  forall lib (A B : @CTerm p),
    type lib (mkc_prod A B) <=> (type lib A # (inhabited_type lib A -> type lib B)).
Proof.
  introv.
  rw @tequality_mkc_prod; sp.
Qed.

Lemma equality_in_iff {p} :
  forall lib (p1 p2 A B : @CTerm p),
    equality lib p1 p2 (mkc_iff A B)
    <=>
    (type lib A
     # type lib B
     # {f1, f2, g1, g2 : CTerm
        , p1 ===>(lib) (mkc_pair f1 g1)
        # p2 ===>(lib) (mkc_pair f2 g2)
        # (forall a1 a2,
             equality lib a1 a2 A
             -> equality lib (mkc_apply f1 a1) (mkc_apply f2 a2) B)
        # (forall b1 b2,
             equality lib b1 b2 B
             -> equality lib (mkc_apply g1 b1) (mkc_apply g2 b2) A)}).
Proof.
  introv.
  rw @equality_in_prod; split; intro e; exrepnd;
  allrw @type_mkc_fun; repnd; dands; auto;
  allrw @equality_in_fun; repnd; auto.

  exists a1 a2 b1 b2; dands; auto.

  exists f1 f2 g1 g2; dands; auto; rw @equality_in_fun; dands; auto.
Qed.

Lemma tequality_mkc_iff {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_iff A1 B1) (mkc_iff A2 B2)
    <=> (tequality lib A1 A2
         # (inhabited_type lib A1 -> tequality lib B1 B2)
         # (inhabited_type lib (mkc_fun A1 B1) -> tequality lib B1 B2)).
Proof.
  introv.
  allrw @tequality_mkc_prod.
  allrw @tequality_mkc_fun.
  split; intro k; repnd; dands; auto.
  intro i; autodimp k hyp; repnd; auto.
Qed.

Lemma tequality_mkc_ufun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_ufun A1 B1) (mkc_ufun A2 B2)
    <=> (tequality lib A1 A2 # (inhabited_type lib A1 -> tequality lib B1 B2)).
Proof.
  introv.
  allrw <- @fold_mkc_ufun.
  rw @tequality_isect.
  split; intro k; repnd; dands; auto.

  introv i.
  unfold inhabited_type in i; exrepnd.
  generalize (k t t i0); intro teq.
  allrw @csubst_mk_cv; auto.

  introv e.
  allrw @csubst_mk_cv; auto.
  apply equality_refl in e.
  autodimp k hyp.
  exists a; auto.
Qed.

(* end hide *)
