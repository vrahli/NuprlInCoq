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


Require Export per_props_uni0.


(*

This is not true anymore because for example
   False -> Nat and Bool -> Top
are equal types.

The <- direction should be true though.

===========================================


(* This is basically 'functionEquality' *)
Lemma tequality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib
              (mkc_function A1 v1 B1)
              (mkc_function A2 v2 B2)
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


Lemma either_computes_to_equality_mkc_function_false {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2,
    !either_computes_to_equality lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2).
Proof.
  introv e.
  unfold either_computes_to_equality, computes_to_equality in e.
  repndors; exrepnd; spcast; computes_to_value_isvalue.
Qed.
Hint Resolve either_computes_to_equality_mkc_function_false : slow.

Lemma equal_equality_types_mkc_function {o} :
  forall lib ts (A1 A2 : @CTerm o) v1 v2 B1 B2,
    equal_equality_types lib ts (mkc_function A1 v1 B1) (mkc_function A2 v2 B2).
Proof.
  introv e.
  apply either_computes_to_equality_mkc_function_false in e; tcsp.
Qed.
Hint Resolve equal_equality_types_mkc_function : slow.

Lemma either_computes_to_equality_mkc_fun_false {o} :
  forall lib (A1 A2 : @CTerm o) B1 B2,
    !either_computes_to_equality lib (mkc_fun A1 B1) (mkc_fun A2 B2).
Proof.
  introv e.
  allrw <- @fold_mkc_fun.
  unfold either_computes_to_equality, computes_to_equality in e.
  repndors; exrepnd; spcast; computes_to_value_isvalue.
Qed.
Hint Resolve either_computes_to_equality_mkc_fun_false : slow.

Lemma equal_equality_types_mkc_fun {o} :
  forall lib ts (A1 A2 : @CTerm o) B1 B2,
    equal_equality_types lib ts (mkc_fun A1 B1) (mkc_fun A2 B2).
Proof.
  introv e.
  apply either_computes_to_equality_mkc_fun_false in e; tcsp.
Qed.
Hint Resolve equal_equality_types_mkc_fun : slow.

(* This is basically 'functionEquality' *)
Lemma implies_tequality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib A1 A2
    -> (forall a a', equality lib a a' A1 -> tequality lib (substc a v1 B1) (substc a' v2 B2))
    -> tequality lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2).
Proof.
  introv teqa teqb.

  unfold tequality in teqa; exrepnd.
  rename eq into eqa.
  generalize (choice_teq lib A1 v1 B1 v2 B2 teqb); intro n; exrepnd.

  exists (per_func_eq eqa (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0))).

  split; eauto 2 with slow; apply CL_func; fold (@nuprl p lib).

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A1 v1 B1; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).

    pose proof (Nuprl_type_family_equality_to_eq lib A1 A2 v1 v2 B1 B2 eqa f teqa0 n0) as imp.
    clear n0.

    pose proof (Nuprl_type_family_equality_to_Nuprl_left
                  lib A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A2 v2 B2; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

    pose proof (Nuprl_type_family_equality_to_eq lib A1 A2 v1 v2 B1 B2 eqa f teqa0 n0) as imp.
    clear n0.

    pose proof (Nuprl_type_family_equality_to_Nuprl_right
                  lib A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

Lemma implies_tequality_function_if_utequality {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib A1 A2
    -> (forall a a', equality lib a a' A1 -> tequality lib (substc a v1 B1) (substc a' v2 B2))
    -> tequality lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2).
Proof.
  introv teqa teqb.

  unfold tequality in teqa; exrepnd.
  rename eq into eqa.
  generalize (choice_teq lib A1 v1 B1 v2 B2 teqb); intro n; exrepnd.

  exists (per_func_eq eqa (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0))).

  split; eauto 2 with slow; apply CL_func; fold (@nuprl p lib).

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A1 v1 B1; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).

    pose proof (Nuprl_type_family_equality_to_eq lib A1 A2 v1 v2 B1 B2 eqa f teqa0 n0) as imp.
    clear n0.

    pose proof (Nuprl_type_family_equality_to_Nuprl_left
                  lib A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A2 v2 B2; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

    pose proof (Nuprl_type_family_equality_to_eq lib A1 A2 v1 v2 B1 B2 eqa f teqa0 n0) as imp.
    clear n0.

    pose proof (Nuprl_type_family_equality_to_Nuprl_right
                  lib A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

Lemma per_func_eq_ext {o} :
  forall (eqa1 eqa2 : per(o)) eqb1 eqb2,
    (eqa1 <=2=> eqa2)
    -> (forall (a1 a2 : CTerm) (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
           (eqb1 a1 a2 e1) <=2=> (eqb2 a1 a2 e2))
    -> (per_func_eq eqa1 eqb1) <=2=> (per_func_eq eqa2 eqb2).
Proof.
  introv eqas eqbs.
  unfold per_func_eq.
  split; introv h; introv.

  - appdup eqas in e.
    apply (eqbs _ _ e0); apply h.

  - appdup eqas in e.
    apply (eqbs _ _ _ e0); apply h.
Qed.
Hint Resolve per_func_eq_ext : slow.

Lemma tequality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2)
    <=>
    (
      type lib A1
      # type lib A2
      # (forall a a', equality lib a a' A1 -> tequality lib (substc a v1 B1) (substc a' v1 B1))
      # (forall a a', equality lib a a' A2 -> tequality lib (substc a v2 B2) (substc a' v2 B2))
      # ext_eq lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2)
    ).
Proof.
  introv; split; intro h; repnd.

  - unfold tequality in h; exrepnd.
    destruct h0 as [h1 h2].
    inversion h1; subst; try not_univ.
    inversion h2; subst; try not_univ.

    allunfold_per; spcast; computes_to_value_isvalue.
    allfold (@nuprl p lib).

    dands.

    + exists eqa0; auto.

    + exists eqa; auto.

    + introv ea.
      eapply nuprl_type_family_members_eq_implies_tequality; try (exact t0); eauto.
      eapply equality_eq; eauto.

    + introv ea.
      eapply nuprl_type_family_members_eq_implies_tequality; try (exact t); eauto.
      eapply equality_eq; eauto.

    + introv.

      split; introv h.

      * unfold equality in *; exrepnd.
        eapply nuprl_uniquely_valued in h3; try (exact h1).
        exists eq0; dands; auto.
        eapply nuprl_ext; eauto.

      * unfold equality in *; exrepnd.
        eapply nuprl_uniquely_valued in h3; try (exact h2).
        exists eq0; dands; auto.
        eapply nuprl_ext; eauto.

  - apply ext_eq_implies_tequality; eauto 2 with slow.

    + generalize (choice_teq lib A1 v1 B1 v1 B1 h2); intro n; exrepnd.

      unfold type in h0; exrepnd.
      rename eq into eqa1.

      pose proof (Nuprl_type_family_equality_to_eq2 lib A1 v1 v1 B1 B1 eqa1 f h4 n0) as imp1.
      clear n0.

      exists (per_func_eq eqa1 (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A1 eqa1 e h4))).

      apply CL_func; fold (@nuprl p lib).

      exists eqa1.
      exists (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A1 eqa1 e h4)); sp.

      exists A1 v1 B1; sp; eauto 3 with slow;
        try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).

      eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.

    + generalize (choice_teq lib A2 v2 B2 v2 B2 h3); intro w; exrepnd.

      unfold type in h1; exrepnd.
      rename eq into eqa2.

      pose proof (Nuprl_type_family_equality_to_eq2 lib A2 v2 v2 B2 B2 eqa2 f h4 w0) as imp2.
      clear w0.

      exists (per_func_eq eqa2 (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A2 eqa2 e h4))).

      apply CL_func; fold (@nuprl p lib).

      exists eqa2.
      exists (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A2 eqa2 e h4)); sp.

      exists A2 v2 B2; sp; eauto 3 with slow;
        try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

      eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

(*
Lemma utequality_function_iff_tequality {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2,
    utequality lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2)
    <=> tequality lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2).
Proof.
  introv.
  unfold utequality, tequality.
  split; intro h; exrepnd; exists eq.

  - destruct h0 as [h1 h2].
    split; auto; eauto 2 with slow.

  - dextts h0 ts1 ts2 ext.
    split; auto.
Qed.

Lemma utequality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    utequality lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2)
    <=>
    (
      type lib A1
      # type lib A2
      # (forall a a', equality lib a a' A1 -> utequality lib (substc a v1 B1) (substc a' v1 B1))
      # (forall a a', equality lib a a' A2 -> utequality lib (substc a v2 B2) (substc a' v2 B2))
      # ext_eq lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2)
    ).
Proof.
  introv.
  rw @utequality_function_iff_tequality.
  apply tequality_function.
Qed.
*)

Lemma if_member_function {p} :
  forall lib (f : @CTerm p) A v B,
    member lib f (mkc_function A v B)
    -> forall x y,
         equality lib x y A
         -> equality lib (mkc_apply f x) (mkc_apply f y) (substc x v B).
Proof.
  unfold member, equality, nuprl; introv m e; exrepnd.
  inversion m1; subst; try not_univ.

  allunfold_per; spcast; computes_to_value_isvalue.
  allfold (@nuprl p lib).

  eapply nuprl_uniquely_valued in e1;[|exact c0].
  apply e1 in e0.

  apply e in m0; clear e.

  exists (eqb x y e0).

  unfold type_family_members_eq in t; repnd.
  dands; tcsp.
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

  unfold tequality in teq; exrepnd.
  generalize (choice_teq lib A v B v B teq); intro n; exrepnd.

  exists (per_func_eq eqa (fun a1 a2 e => f0 a1 a2 (eq_equality0 lib a1 a2 A eqa e ty0)));
    dands; introv; try (complete (apply n0)).

  unfold nuprl; apply CL_func; fold @nuprl; unfold per_func.
  exists eqa.

  exists (fun a1 a2 e => f0 a1 a2 (eq_equality0 lib a1 a2 A eqa e ty0)); sp.

  unfold type_family.
  exists A v B; sp;
    try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

  assert (forall (a1 a2 : CTerm) (e : equality lib a1 a2 A),
             Nuprl lib (B) [[v \\ a1]] (B) [[v \\ a1]] (f0 a1 a2 e)) as h.
  { introv; apply n0. }
  clear n0.

  pose proof (Nuprl_type_family_equality_to_eq3 lib A v v B B eqa f0 f1 ty0) as imp.
  repeat (autodimp imp hyp).
  clear h n1.

  eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

Lemma implies_member_function_if_utequality {p} :
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

  generalize (choice_teq lib A v B v B teq); intro n; exrepnd.

  exists (per_func_eq eqa (fun a1 a2 e => f0 a1 a2 (eq_equality0 lib a1 a2 A eqa e ty0)));
    dands; introv; try (complete (apply n0)).

  unfold nuprl; apply CL_func; fold @nuprl; unfold per_func.
  exists eqa.

  exists (fun a1 a2 e => f0 a1 a2 (eq_equality0 lib a1 a2 A eqa e ty0)); sp.

  unfold type_family.
  exists A v B; sp;
    try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

  assert (forall (a1 a2 : CTerm) (e : equality lib a1 a2 A),
             Nuprl lib (B) [[v \\ a1]] (B) [[v \\ a1]] (f0 a1 a2 e)) as h.
  { introv; apply n0. }
  clear n0.

  pose proof (Nuprl_type_family_equality_to_eq3 lib A v v B B eqa f0 f1 ty0) as imp.
  repeat (autodimp imp hyp).
  clear h n1.

  eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.


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
  introv; sp_iff Case; introv e;
    try (complete (apply implies_member_function_if_utequality; sp));[].

  unfold equality in e; exrepnd.
  inversion e1; subst; try not_univ.

  one_dest_per_fam eqa feqb A1 v1 B1 c1 tsa tsb eqt.
  allunfold_per; spcast; allfold (@nuprl p lib).
  computes_to_value_isvalue.

  apply eqt in e0; clear dependent eq.

  dands.

  { exists eqa; sp. }

  { introv e.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib A1 eqa eq); intro k; repeat (dest_imp k hyp).
    apply k in e1.
    clear dependent eq.
    eapply nuprl_type_family_members_eq_implies_tequality; eauto. }

  { introv e.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib A1 eqa eq); intro k; repeat (dest_imp k hyp).
    apply k in e1.
    clear dependent eq.
    exists (feqb a a' e1); sp.
    apply tsb. }
Qed.

(*

Again -> is not true anymore, but we should prove the other direction though.

=============================================

Lemma equality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality
      lib
      (mkc_function A1 v1 B1)
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
*)

Lemma implies_equality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib A1 A2 (mkc_uni i)
    -> (forall a a',
           equality lib a a' A1
           -> equality lib (substc a v1 B1) (substc a' v2 B2) (mkc_uni i))
    -> equality lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2) (mkc_uni i).
Proof.
  introv eqa eqb.

  unfold equality in eqa; exrepnd.
  inversion eqa1; subst; try not_univ.
  duniv j h.
  allrw @univi_exists_iff; exrepd.
  computes_to_value_isvalue; GC.
  apply e in eqa0.
  unfold univi_eq in eqa0; exrepnd.
  dextts eqa2 ts1 ts2.
  allfold (@nuprli p lib j0).

  exists eq; sp.
  apply e.

  generalize (choice_teqi lib j0 A1 v1 B1 v2 B2 eqb); intro n; exrepnd.

  exists (per_func_eq eqa (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1))).

  split; eauto 2 with slow; apply CL_func; fold (@nuprl p lib);[|].

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1)); sp.

    exists A1 v1 B1; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_function))).

    pose proof (Nuprli_type_family_equality_to_eq lib j0 A1 v1 v2 B1 B2 eqa f ts1 n0) as imp.
    clear n0.

    pose proof (Nuprli_type_family_equality_to_Nuprli_left
                  lib j0 A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply Nuprli_implies_type_family_members_eq; auto; eauto 2 with slow.

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1)); sp.

    exists A2 v2 B2; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

    pose proof (Nuprli_type_family_equality_to_eq lib j0 A1 v1 v2 B1 B2 eqa f ts1 n0) as imp.
    clear n0.

    pose proof (Nuprli_type_family_equality_to_Nuprli_right
                  lib j0 A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply Nuprli_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

Lemma implies_tequalityi_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib A1 A2 (mkc_uni i)
    -> (forall a a',
           equality lib a a' A1
           -> tequalityi lib i (substc a v1 B1) (substc a' v2 B2))
    -> tequalityi lib i (mkc_function A1 v1 B1) (mkc_function A2 v2 B2).
Proof.
  introv eqa eqb.

  unfold equality in eqa; exrepnd.
  inversion eqa1; subst; try not_univ.
  duniv j h.
  allrw @univi_exists_iff; exrepd.
  computes_to_value_isvalue; GC.
  apply e in eqa0.
  unfold univi_eq in eqa0; exrepnd.
  dextts eqa2 ts1 ts2.
  allfold (@nuprli p lib j0).

  exists eq; sp.
  apply e.

  generalize (choice_teqi lib j0 A1 v1 B1 v2 B2 eqb); intro n; exrepnd.

  exists (per_func_eq eqa (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1))).

  split; eauto 2 with slow; apply CL_func; fold (@nuprl p lib).

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1)); sp.

    exists A1 v1 B1; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; eauto 2 with slow)).

    pose proof (Nuprli_type_family_equality_to_eq lib j0 A1 v1 v2 B1 B2 eqa f ts1 n0) as imp.
    clear n0.

    pose proof (Nuprli_type_family_equality_to_Nuprli_left
                  lib j0 A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply Nuprli_implies_type_family_members_eq; auto; eauto 2 with slow.

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1)); sp.

    exists A2 v2 B2; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

    pose proof (Nuprli_type_family_equality_to_eq lib j0 A1 v1 v2 B1 B2 eqa f ts1 n0) as imp.
    clear n0.

    pose proof (Nuprli_type_family_equality_to_Nuprli_right
                  lib j0 A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply Nuprli_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

Lemma nuprli_eq_type_family_members_eq_implies_ext_eq_function_one_direction {o} :
  forall lib i (A1 A2 : @CTerm o) v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    nuprli lib i A1 eqa1
    -> nuprli lib i A2 eqa2
    -> type_family_members_eq (nuprli lib i) v1 B1 eqa1 eqb1
    -> type_family_members_eq (nuprli lib i) v2 B2 eqa2 eqb2
    -> (forall a b, per_func_eq eqa1 eqb1 a b -> per_func_eq eqa2 eqb2 a b)
    -> forall a b, equality lib a b (mkc_function A1 v1 B1)
                   -> equality lib a b (mkc_function A2 v2 B2).
Proof.
  introv na1 na2 tf1 tf2 imp h.

  apply equality_in_function in h; repnd.
  apply equality_in_function.

  dands; eauto 2 with slow.

  {
    introv ea.
    apply (tequalityi_implies_tequality lib i).
    eapply nuprli_type_family_members_eq_implies_tequalityi;[|exact tf2|]; eauto.
    eapply equality_eq;[|exact ea]; eauto 2 with slow.
  }

  {
    introv ea.
    pose proof (imp a b) as q; clear imp.

    assert (eqa2 a0 a') as ea2.
    { eapply equality_eq;[|exact ea]; eauto 2 with slow. }

    unfold per_func_eq in q.
    autodimp q hyp.

    {
      introv.

      pose proof (eq_equality4 lib a1 a'0 A1 eqa1 i e na1) as q.
      applydup h in q.

      destruct tf1 as [tfb famb].
      pose proof (tfb a1 a'0 e) as w.
      eapply nuprli_implies_equality_eq; eauto.
    }

    {
      pose proof (q a0 a' ea2) as w; clear q.
      destruct tf2 as [tfb famb].
      pose proof (tfb a0 a' ea2) as z.
      eapply nuprli_and_eq_implies_equality; eauto.
    }
  }
Qed.

Lemma nuprli_eq_type_family_members_eq_implies_ext_eq_function {o} :
  forall lib i (A1 A2 : @CTerm o) v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    nuprli lib i A1 eqa1
    -> nuprli lib i A2 eqa2
    -> type_family_members_eq (nuprli lib i) v1 B1 eqa1 eqb1
    -> type_family_members_eq (nuprli lib i) v2 B2 eqa2 eqb2
    -> ((per_func_eq eqa1 eqb1) <=2=> (per_func_eq eqa2 eqb2))
    -> ext_eq lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2).
Proof.
  introv na1 na2 tf1 tf2 eqiff.
  split; intro h.

  - eapply nuprli_eq_type_family_members_eq_implies_ext_eq_function_one_direction;
      try (exact h); eauto.
    introv xx; apply eqiff; auto.

  - eapply nuprli_eq_type_family_members_eq_implies_ext_eq_function_one_direction;
      try (exact h); eauto.
    introv xx; apply eqiff; auto.
Qed.

Lemma tequalityi_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    tequalityi
      lib
      i
      (mkc_function A1 v1 B1)
      (mkc_function A2 v2 B2)
    <=>
    (
      member lib A1 (mkc_uni i)
      # member lib A2 (mkc_uni i)
      # (forall a a', equality lib a a' A1 -> tequalityi lib i (substc a v1 B1) (substc a' v1 B1))
      # (forall a a', equality lib a a' A2 -> tequalityi lib i (substc a v2 B2) (substc a' v2 B2))
      # ext_eq lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2)
    ).
Proof.
  introv; split; intro h; repnd.

  - unfold tequalityi, equality, nuprl in h; exrepnd.
    inversion h1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    apply e in h0; unfold univi_eq in h0; exrepnd.

    dextts h2 ts1 ts2.

    cioneclose_eq eqa; subst; try not_univ.
    cioneclose_eq eqa; subst; try not_univ.

    one_dest_per_fam eqa1 feqb1 A3 v3 B3 c1 tsa1 tsb1 eqt1.
    match goal with
    | [ H : per_func _ _ _ _ |- _ ] => dest_per_fam H eqa2 feqb2 A4 v4 B4 c2 tsa2 tsb2 eqt2
    end.
    computes_to_value_isvalue; GC.

    fold (nuprli lib j0) in *.
    fold (nuprl lib) in *.

    dands.

    { exists eq; dands; auto.
      apply e.
      exists eqa1; fold (nuprli lib j0); eauto 2 with slow. }

    { exists eq; dands; auto.
      apply e.
      exists eqa2; fold (nuprli lib j0); eauto 2 with slow. }

    { introv ea.
      eapply nuprli_type_family_members_eq_implies_tequalityi; eauto.
      eapply equality_eq;[|eauto]; eauto 2 with slow. }

    { introv ea.
      eapply nuprli_type_family_members_eq_implies_tequalityi; try (exact tsb2); eauto.
      eapply equality_eq;[|eauto]; eauto 2 with slow. }

    { eapply nuprli_eq_type_family_members_eq_implies_ext_eq_function; eauto.
      eapply eq_term_equals_trans;[|eauto].
      apply eq_term_equals_sym; auto. }

  - apply (ext_eq_implies_tequalityi lib i) in h; auto; clear h; eauto 2 with slow;
      try (apply implies_tequalityi_function; auto).
Qed.

(*

(* This is not true anymore, the one that's true is [tequalityi_function] above
   where for the family we use utequalityi instead of tequalityi,
   but we don't have a way to taking about the unconstrained equality
   with [equality], so we use [utequalityi] instead. *)

Lemma equality_function {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality
      lib
      (mkc_function A1 v1 B1)
      (mkc_function A2 v2 B2)
      (mkc_uni i)
    <=>
    (
      member lib A1 (mkc_uni i)
      # member lib A2 (mkc_uni i)
      # (forall a a', equality lib a a' A1 -> equality lib (substc a v1 B1) (substc a' v1 B1) (mkc_uni i))
      # (forall a a', equality lib a a' A2 -> equality lib (substc a v2 B2) (substc a' v2 B2) (mkc_uni i))
      # ext_eq lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2)
    ).
Proof.
  introv; split; intro h; repnd.

  - unfold equality, nuprl in h; exrepnd.
    inversion h1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    apply e in h0; unfold univi_eq in h0; exrepnd.

    cioneclose_eq eqa; subst; try not_univ.
    cioneclose_eq eqa; subst; try not_univ.

    one_dest_per_fam eqa1 feqb1 A3 v3 B3 c1 tsa1 tsb1 eqt1.
    match goal with
    | [ H : per_func _ _ _ _ |- _ ] => dest_per_fam H eqa2 feqb2 A4 v4 B4 c2 tsa2 tsb2 eqt2
    end.
    computes_to_value_isvalue; GC.

    fold (nuprli lib j0) in *.
    fold (nuprl lib) in *.

    dands.

    { exists eq; dands; auto.
      apply e.
      exists eqa1; split; auto. }

    { exists eq; dands; auto.
      apply e.
      exists eqa2; split; auto. }

    { introv ea.
      rewrite @equality_in_uni_as_tequalityi.
      eapply nuprli_type_family_members_eq_implies_tequalityi; eauto.

      eapply equality_eq;[|eauto]; eauto 2 with slow. }

    { introv ea.
      rewrite @equality_in_uni_as_tequalityi.
      eapply nuprli_type_family_members_eq_implies_tequalityi; try (exact tsb2); eauto.

      eapply equality_eq;[|eauto]; eauto 2 with slow. }

    { eapply nuprli_eq_type_family_members_eq_implies_ext_eq_function; eauto.
      eapply eq_term_equals_trans;[|eauto].
      apply eq_term_equals_sym; auto. }

  - apply (ext_eq_implies_tequalityi lib i) in h; auto; clear h;
      apply implies_equality_function; auto.
Qed.
*)

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
  split; intro h.

  - dup h as q; rw @equality_in_function in h; repnd; dands; tcsp.
    apply inhabited_implies_tequality in q; auto.

  - repnd.
    apply fold_type in h0.
    rw @tequality_function in h0; repnd; GC.
    apply equality_in_function; dands; auto.
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

Lemma tequality_function_fun {p} :
  forall lib (A : @CTerm p) v B,
    (type lib (mkc_function A v (mk_cv [v] B)) {+} type lib (mkc_fun A B))
    -> tequality lib (mkc_function A v (mk_cv [v] B))
                 (mkc_fun A B).
Proof.
  introv o; repdors.

  - apply tequality_respects_alphaeqc_right with (T2 := mkc_function A v (mk_cv [v] B));
      tcsp; eauto 2 with slow.

  - apply tequality_respects_alphaeqc_left with (T1 := mkc_fun A B);
      sp; eauto 2 with slow.
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
  apply fold_type in teqf.
  apply tequality_function in teqf; repnd.
  apply implies_tequality_function_if_utequality; auto.
Qed.

(*
Again, this is not true anymore:

========================================

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
*)

(*
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
 *)

Lemma tequality_fun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    <=>
    (
      type lib A1
      # type lib A2
      # (inhabited_type lib A1 -> type lib B1)
      # (inhabited_type lib A2 -> type lib B2)
      # ext_eq lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    ).
Proof.
  introv.
  allrw <- @fold_mkc_fun.
  rw @tequality_function.
  split; intro teq; repnd; dands; auto; introv e.

  - unfold inhabited_type in e; exrepnd.
    generalize (teq2 t t); intro k; autodimp k hyp.
    repeat (rw @csubst_mk_cv in k); sp; eauto 2 with slow.

  - unfold inhabited_type in e; exrepnd.
    generalize (teq3 t t); intro k; autodimp k hyp.
    repeat (rw @csubst_mk_cv in k); sp; eauto 2 with slow.

  - autodimp teq2 hyp.
    { exists a; allapply @equality_refl; sp. }
    repeat (rw @csubst_mk_cv); sp; eauto 2 with slow.

  - autodimp teq3 hyp.
    { exists a; allapply @equality_refl; sp. }
    repeat (rw @csubst_mk_cv); sp; eauto 2 with slow.
Qed.

(*
Lemma utequality_fun_iff_tequality {o} :
  forall lib (A1 A2 : @CTerm o) B1 B2,
    utequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    <=> tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2).
Proof.
  introv.
  unfold utequality, tequality.
  split; intro h; exrepnd; exists eq.

  - destruct h0 as [h1 h2].
    split; auto; eauto 2 with slow.

  - dextts h0 ts1 ts2 ext.
    split; auto.
Qed.

Lemma utequality_fun {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    utequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    <=>
    (
      type lib A1
      # type lib A2
      # (inhabited_type lib A1 -> type lib B1)
      # (inhabited_type lib A2 -> type lib B2)
      # ext_eq lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    ).
Proof.
  introv.
  rw @utequality_fun_iff_tequality.
  apply tequality_fun.
Qed.
*)

(*
Lemma tequality_mkc_fun_l {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_fun A1 B1) (mkc_fun A2 B2)
    -> tequality lib A1 A2.
Proof.
  introv Hpart1.
  rw @tequality_fun in Hpart1; sp.
Qed.
*)

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

  { introv i.
    unfold inhabited_type in i; exrepnd.
    generalize (k1 t t); intro j; autodimp j hyp.
    repeat (rw @csubst_mk_cv in j); sp; eauto 2 with slow. }

  { introv e.
    apply k in e.
    repeat (rw @csubst_mk_cv in e); sp. }

  { introv e.
    repeat (rw @csubst_mk_cv); sp.
    autodimp k1 hyp; eauto 2 with slow.
    exists a; allapply @equality_refl; sp. }

  { introv e.
    repeat (rw @csubst_mk_cv); sp. }
Qed.

Lemma type_mkc_fun {p} :
  forall lib (A B : @CTerm p),
    type lib (mkc_fun A B) <=> (type lib A # (inhabited_type lib A -> type lib B)).
Proof.
  introv.
  split; intro h.
  - apply fold_type in h.
    rw @tequality_fun in h; tcsp.
  - apply fold_type.
    apply tequality_fun; repnd; dands; tcsp; eauto 2 with slow.
Qed.
