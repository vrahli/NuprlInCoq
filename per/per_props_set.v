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
Lemma tequality_set {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality
      lib
      (mkc_set A1 v1 B1)
      (mkc_set A2 v2 B2)
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
    allfold (@nuprl p).
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
              {e : eqa t1 t2
               , inhabited (f t1 t2 (eq_equality2 lib t1 t2 A1 A2 eqa e teqa0))}).
    apply CL_set; fold (@nuprl p lib).
    unfold per_set.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_set))).
Qed.
*)

Hint Resolve iscvalue_mkc_set : slow.

Lemma either_computes_to_equality_mkc_set_false {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2,
    !either_computes_to_equality lib (mkc_set A1 v1 B1) (mkc_set A2 v2 B2).
Proof.
  introv e.
  unfold either_computes_to_equality, computes_to_equality in e.
  repndors; exrepnd; spcast; computes_to_value_isvalue.
Qed.
Hint Resolve either_computes_to_equality_mkc_set_false : slow.

Lemma equal_equality_types_mkc_set {o} :
  forall lib ts (A1 A2 : @CTerm o) v1 v2 B1 B2,
    equal_equality_types lib ts (mkc_set A1 v1 B1) (mkc_set A2 v2 B2).
Proof.
  introv e.
  apply either_computes_to_equality_mkc_set_false in e; tcsp.
Qed.
Hint Resolve equal_equality_types_mkc_set : slow.

Lemma tequality_set {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib (mkc_set A1 v1 B1) (mkc_set A2 v2 B2)
    <=>
    (
      type lib A1
      # type lib A2
      # (forall a a', equality lib a a' A1 -> utequality lib (substc a v1 B1) (substc a' v1 B1))
      # (forall a a', equality lib a a' A2 -> utequality lib (substc a v2 B2) (substc a' v2 B2))
      # ext_eq lib (mkc_set A1 v1 B1) (mkc_set A2 v2 B2)
    ).
Proof.
  introv; split; intro h; repnd.

  - unfold tequality in h; exrepnd.
    destruct h0 as [h1 h2 ext].
    clear ext.

    inversion h1; subst; try not_univ.
    inversion h2; subst; try not_univ.

    allunfold_per; spcast; computes_to_value_isvalue.
    allfold (@nuprl p lib).

    dands.

    + exists eqa0; auto.

    + exists eqa; auto.

    + introv ea.

      eapply nuprl_type_family_members_eq_implies_utequality; try (exact t0); eauto.
      eapply equality_eq; eauto.

    + introv ea.
      eapply nuprl_type_family_members_eq_implies_utequality; try (exact t); eauto.
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

    + generalize (choice_uteq lib A1 v1 B1 v1 B1 h2); intro n; exrepnd.

      unfold type in h0; exrepnd.
      rename eq into eqa1.

      pose proof (uNuprl_type_family_equality_to_eq2 lib A1 v1 v1 B1 B1 eqa1 f h4 n0) as imp1.
      clear n0.

      exists (per_set_eq eqa1 (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A1 eqa1 e h4))).

      apply CL_set; fold (@nuprl p lib).

      exists eqa1.
      exists (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A1 eqa1 e h4)); sp.

      exists A1 v1 B1; sp; eauto 3 with slow;
        try (complete (spcast; apply computes_to_valc_refl; eauto 2 with slow)).

      eapply uNuprl_implies_type_family_members_eq; auto; eauto 2 with slow.

    + generalize (choice_uteq lib A2 v2 B2 v2 B2 h3); intro w; exrepnd.

      unfold type in h1; exrepnd.
      rename eq into eqa2.

      pose proof (uNuprl_type_family_equality_to_eq2 lib A2 v2 v2 B2 B2 eqa2 f h4 w0) as imp2.
      clear w0.

      exists (per_set_eq eqa2 (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A2 eqa2 e h4))).

      apply CL_set; fold (@nuprl p lib).

      exists eqa2.
      exists (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A2 eqa2 e h4)); sp.

      exists A2 v2 B2; sp; eauto 3 with slow;
        try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

      eapply uNuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

(*
Lemma equality_set {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality
      lib
      (mkc_set A1 v1 B1)
      (mkc_set A2 v2 B2)
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
              {e : eqa t1 t2
               , inhabited (f t1 t2 (eq_equality3 lib t1 t2 A1 A2 eqa j0 e h0))}).
    apply CL_set; fold (@nuprli p lib j0).
    unfold per_set.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_set))).
Qed.
 *)

Lemma implies_equality_set {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib A1 A2 (mkc_uni i)
    -> (forall a a',
           equality lib a a' A1
           -> equality lib (substc a v1 B1) (substc a' v2 B2) (mkc_uni i))
    -> equality lib (mkc_set A1 v1 B1) (mkc_set A2 v2 B2) (mkc_uni i).
Proof.
  introv eqa eqb.

  unfold equality in eqa; exrepnd.
  inversion eqa1; subst; try not_univ.
  duniv j h.
  allrw @univi_exists_iff; exrepd.
  computes_to_value_isvalue; GC.
  apply e in eqa0.
  unfold univi_eq in eqa0; exrepnd.
  dextts eqa2 ts1 ts2 ext.
  allfold (@nuprli p lib j0).

  exists eq; sp.
  apply e.

  generalize (choice_teqi lib j0 A1 v1 B1 v2 B2 eqb); intro n; exrepnd.

  exists (per_set_eq eqa (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1))).

  split; eauto 2 with slow; apply CL_set; fold (@nuprl p lib).

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

Lemma implies_tequalityi_set {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib A1 A2 (mkc_uni i)
    -> (forall a a',
           equality lib a a' A1
           -> utequalityi lib i (substc a v1 B1) (substc a' v2 B2))
    -> tequalityi lib i (mkc_set A1 v1 B1) (mkc_set A2 v2 B2).
Proof.
  introv eqa eqb.

  unfold equality in eqa; exrepnd.
  inversion eqa1; subst; try not_univ.
  duniv j h.
  allrw @univi_exists_iff; exrepd.
  computes_to_value_isvalue; GC.
  apply e in eqa0.
  unfold univi_eq in eqa0; exrepnd.
  dextts eqa2 ts1 ts2 ext.
  allfold (@nuprli p lib j0).

  exists eq; sp.
  apply e.

  generalize (choice_uteqi lib j0 A1 v1 B1 v2 B2 eqb); intro n; exrepnd.

  exists (per_set_eq eqa (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1))).

  split; eauto 2 with slow; apply CL_set; fold (@nuprl p lib).

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1)); sp.

    exists A1 v1 B1; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; eauto 2 with slow)).

    pose proof (uNuprli_type_family_equality_to_eq lib j0 A1 v1 v2 B1 B2 eqa f ts1 n0) as imp.
    clear n0.

    pose proof (uNuprli_type_family_equality_to_uNuprli_left
                  lib j0 A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply uNuprli_implies_type_family_members_eq; auto; eauto 2 with slow.

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1)); sp.

    exists A2 v2 B2; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

    pose proof (uNuprli_type_family_equality_to_eq lib j0 A1 v1 v2 B1 B2 eqa f ts1 n0) as imp.
    clear n0.

    pose proof (uNuprli_type_family_equality_to_uNuprli_right
                  lib j0 A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e ts1))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply uNuprli_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

Lemma implies_member_set_if_utequality {p} :
  forall lib (t u : @CTerm p) A v B,
    (forall a a', equality lib a a' A -> utequality lib (substc a v B) (substc a' v B))
    -> equality lib t u A
    -> inhabited_type lib (substc t v B)
    -> equality lib t u (mkc_set A v B).
Proof.
  introv teqb teqa inha.
  unfold member, equality.
  unfold equality in teqa; exrepnd.
  rename eq into eqa.

  pose proof (choice_uteq lib A v B v B teqb) as n; exrepnd.
  clear teqb.

  exists (per_set_eq eqa (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A eqa e teqa1)));
    dands; introv; try (complete (apply n0)).

  {
    unfold nuprl; apply CL_set; fold @nuprl; unfold per_set.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A eqa e teqa1)); sp.

    unfold type_family.
    exists A v B; sp;
      try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

    pose proof (uNuprl_type_family_equality_to_eq2 lib A v v B B eqa f teqa1) as imp.
    repeat (autodimp imp hyp).
    clear n0.

    eapply uNuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
  }

  {
    unfold per_set_eq.

    unfold inhabited_type, member, equality in inha; exrepnd.

    exists teqa0.
    exists t0.
    pose proof (n0 t u (eq_equality0 lib t u A eqa teqa0 teqa1)) as h.
    clear n0.
    destruct h as [h1 h2].
    eapply nuprl_uniquely_valued in h1;[|exact inha0]; apply h1; auto.
  }
Qed.

Lemma equality_in_set {p} :
  forall lib (t u : @CTerm p) A v B,
    equality lib t u (mkc_set A v B)
    <=>
    ((forall a a', equality lib a a' A -> utequality lib (substc a v B) (substc a' v B))
     # equality lib t u A
     # inhabited_type lib (substc t v B)).
Proof.
  introv; sp_iff Case; introv e;
    try (complete (apply implies_member_set_if_utequality; sp)).

  unfold equality in e; exrepnd.
  inversion e1; subst; try not_univ.

  one_dest_per_fam eqa feqb A1 v1 B1 c1 tsa tsb eqt.
  allunfold_per; spcast; allfold (@nuprl p lib).
  computes_to_value_isvalue.

  apply eqt in e0; clear dependent eq.

  dands.

  { introv e.
    unfold equality in e; exrepnd.
    generalize (nuprl_uniquely_valued lib A1 eqa eq); intro k; repeat (dest_imp k hyp).
    apply k in e1.
    clear dependent eq.
    eapply nuprl_type_family_members_eq_implies_utequality; eauto. }

  { unfold per_set_eq in e0; exrepnd.
    exists eqa; sp. }

  { unfold per_set_eq in e0; exrepnd.
    eapply inhabited_type_if_inhabited;[|eauto].
    apply tsb. }
Qed.

Lemma nuprli_eq_type_family_members_eq_implies_ext_eq_set_one_direction {o} :
  forall lib i (A1 A2 : @CTerm o) v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    nuprli lib i A1 eqa1
    -> nuprli lib i A2 eqa2
    -> type_family_members_eq (nuprli lib i) v1 B1 eqa1 eqb1
    -> type_family_members_eq (nuprli lib i) v2 B2 eqa2 eqb2
    -> (forall a b, per_set_eq eqa1 eqb1 a b -> per_set_eq eqa2 eqb2 a b)
    -> forall a b, equality lib a b (mkc_set A1 v1 B1)
                   -> equality lib a b (mkc_set A2 v2 B2).
Proof.
  introv na1 na2 tf1 tf2 imp h.

  apply equality_in_set in h; repnd.
  apply equality_in_set.

  pose proof (imp a b) as q; clear imp.

  unfold per_set_eq in q.
  autodimp q hyp.

  { assert (eqa1 a b) as ea.
    { pose proof (equality_eq lib A1 a b eqa1) as q.
      autodimp q hyp; eauto 2 with slow; apply q; auto. }
    exists ea.
    eapply inhabited_if_inhabited_type;[eauto|].
    eapply nuprli_implies_nuprl; apply tf1. }
  exrepnd.

  dands; eauto 2 with slow.

  {
    introv ea.
    apply (utequalityi_implies_utequality lib i).
    eapply nuprli_type_family_members_eq_implies_utequalityi;[|exact tf2|]; eauto.
    eapply equality_eq;[|exact ea]; eauto 2 with slow.
  }

  { eapply eq_equality0;[|eapply nuprli_implies_nuprl;eauto]; auto. }

  { eapply inhabited_type_if_inhabited;[|eauto].
    eapply nuprli_implies_nuprl; apply tf2. }
Qed.

Lemma nuprli_eq_type_family_members_eq_implies_ext_eq_set {o} :
  forall lib i (A1 A2 : @CTerm o) v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    nuprli lib i A1 eqa1
    -> nuprli lib i A2 eqa2
    -> type_family_members_eq (nuprli lib i) v1 B1 eqa1 eqb1
    -> type_family_members_eq (nuprli lib i) v2 B2 eqa2 eqb2
    -> ((per_set_eq eqa1 eqb1) <=2=> (per_set_eq eqa2 eqb2))
    -> ext_eq lib (mkc_set A1 v1 B1) (mkc_set A2 v2 B2).
Proof.
  introv na1 na2 tf1 tf2 eqiff.
  split; intro h.

  - eapply nuprli_eq_type_family_members_eq_implies_ext_eq_set_one_direction;
      try (exact h); eauto.
    introv xx; apply eqiff; auto.

  - eapply nuprli_eq_type_family_members_eq_implies_ext_eq_set_one_direction;
      try (exact h); eauto.
    introv xx; apply eqiff; auto.
Qed.

Lemma type_set {p} :
  forall lib (A : @CTerm p) v B,
    type lib (mkc_set A v B)
    <=>
    (
      type lib A
      # (forall a a', equality lib a a' A -> utequality lib (substc a v B) (substc a' v B))
    ).
Proof.
  introv.
  rw <- @fold_type.
  rw @tequality_set.
  split; intro h; repnd; dands; auto; eauto 2 with slow.
Qed.

Lemma tequalityi_set {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    tequalityi
      lib
      i
      (mkc_set A1 v1 B1)
      (mkc_set A2 v2 B2)
    <=>
    (
      member lib A1 (mkc_uni i)
      # member lib A2 (mkc_uni i)
      # (forall a a', equality lib a a' A1 -> utequalityi lib i (substc a v1 B1) (substc a' v1 B1))
      # (forall a a', equality lib a a' A2 -> utequalityi lib i (substc a v2 B2) (substc a' v2 B2))
      # ext_eq lib (mkc_set A1 v1 B1) (mkc_set A2 v2 B2)
    ).
Proof.
  introv; split; intro h; repnd.

  - unfold tequalityi, equality, nuprl in h; exrepnd.
    inversion h1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    apply e in h0; unfold univi_eq in h0; exrepnd.

    dextts h2 ts1 ts2 ext.

    cioneclose_eq eqa; subst; try not_univ.
    cioneclose_eq eqa; subst; try not_univ.

    one_dest_per_fam eqa1 feqb1 A3 v3 B3 c1 tsa1 tsb1 eqt1.
    match goal with
    | [ H : per_set _ _ _ _ |- _ ] => dest_per_fam H eqa2 feqb2 A4 v4 B4 c2 tsa2 tsb2 eqt2
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
      eapply nuprli_type_family_members_eq_implies_utequalityi; eauto.
      eapply equality_eq;[|eauto]; eauto 2 with slow. }

    { introv ea.
      eapply nuprli_type_family_members_eq_implies_utequalityi; try (exact tsb2); eauto.
      eapply equality_eq;[|eauto]; eauto 2 with slow. }

    { eapply nuprli_eq_type_family_members_eq_implies_ext_eq_set; eauto.
      eapply eq_term_equals_trans;[|eauto].
      apply eq_term_equals_sym; auto. }

  - apply (ext_eq_implies_tequalityi lib i) in h; auto; clear h; eauto 2 with slow;
      apply implies_tequalityi_set; auto.
Qed.

(*

(* This is not true anymore, the one that's true is [tequalityi_set] above
   where for the family we use utequalityi instead of tequalityi,
   but we don't have a way to taking about the unconstrained equality
   with [equality], so we use [utequalityi] instead. *)

Lemma equality_set {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality
      lib
      (mkc_set A1 v1 B1)
      (mkc_set A2 v2 B2)
      (mkc_uni i)
    <=>
    (
      member lib A1 (mkc_uni i)
      # member lib A2 (mkc_uni i)
      # (forall a a', equality lib a a' A1 -> equality lib (substc a v1 B1) (substc a' v1 B1) (mkc_uni i))
      # (forall a a', equality lib a a' A2 -> equality lib (substc a v2 B2) (substc a' v2 B2) (mkc_uni i))
      # ext_eq lib (mkc_set A1 v1 B1) (mkc_set A2 v2 B2)
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
    | [ H : per_set _ _ _ _ |- _ ] => dest_per_fam H eqa2 feqb2 A4 v4 B4 c2 tsa2 tsb2 eqt2
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

    { eapply nuprli_eq_type_family_members_eq_implies_ext_eq_set; eauto.
      eapply eq_term_equals_trans;[|eauto].
      apply eq_term_equals_sym; auto. }

  - apply (ext_eq_implies_tequalityi lib i) in h; auto; clear h;
      apply implies_equality_set; auto.
Qed.
 *)
