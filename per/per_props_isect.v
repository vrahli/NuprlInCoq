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
    one_dest_per_fam eqa feqb A1 v1 B1 c1 tsa tsb eqt.
    computes_to_value_isvalue.
    allfold (@nuprl p lib).

    apply eqt in e.
    unfold per_isect_eq in e.

    dands; eauto 2 with slow.

    { introv ea.
      unfold equality in ea; exrepnd.
      pose proof (nuprl_uniquely_valued lib A1 eqa eq0) as k; repeat (autodimp k hyp).
      apply k in ea0.
      clear dependent eq0.
      eapply nuprl_type_family_members_eq_implies_tequality; try (exact tsb); eauto. }

    { introv ea.
      unfold equality in ea; exrepnd.
      generalize (nuprl_uniquely_valued lib A1 eqa eq0); intro k; repeat (dest_imp k hyp).
      apply k in ea0.
      clear dependent eq0.
      exists (feqb a a' ea0); sp.
      apply tsb. }

  - Case "<-".
    repnd.
    unfold type in e0; exrepnd.
    rename eq into eqa.

    pose proof (choice_eq lib A v B (fun a => t) (fun a => u) e) as n; exrepnd.
    clear e.

    pose proof (choice_teq lib A v B v B e1) as m; exrepnd.
    clear e1.

    exists (per_isect_eq eqa (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A eqa e e2)));
      dands; introv; try (complete (apply n0)).

    apply CL_isect; fold @nuprl; unfold per_isect.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A eqa e e2)); sp.

    exists A v B; sp;
      try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

    assert (forall (a1 a2 : CTerm) (e : equality lib a1 a2 A),
               Nuprl lib (B) [[v \\ a1]] (B) [[v \\ a1]] (f a1 a2 e)) as h.
    { introv; apply n0. }
    clear n0.

    pose proof (Nuprl_type_family_equality_to_eq3 lib A v v B B eqa f f0 e2) as imp.
    repeat (autodimp imp hyp).
    clear m0 h.

    eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

Lemma member_in_isect {o} :
  forall lib (t : @CTerm o) A v B,
    member lib t (mkc_isect A v B)
    <=>
    (type lib A
     # forall a a',
         equality lib a a' A
         -> (member lib t (substc a v B) # tequality lib (substc a v B) (substc a' v B))).
Proof.
  sp; rw @equality_in_isect; split; sp; discover; sp.
Qed.

Lemma equality_in_isect2 {o} :
  forall lib (t u : @CTerm o) A v B,
    equality lib t u (mkc_isect A v B)
    <=>
    (type lib A
     # forall a a',
         equality lib a a' A
         -> (equality lib t u (substc a v B) # tequality lib (substc a v B) (substc a' v B))).
Proof.
  sp; rw @equality_in_isect; split; sp; discover; sp.
Qed.

(*
Lemma tequality_isect {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality
      lib
      (mkc_isect A1 v1 B1)
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
 *)


Lemma tequality_isect {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib (mkc_isect A1 v1 B1) (mkc_isect A2 v2 B2)
    <=>
    (
      type lib A1
      # type lib A2
      # (forall a a', equality lib a a' A1 -> tequality lib (substc a v1 B1) (substc a' v1 B1))
      # (forall a a', equality lib a a' A2 -> tequality lib (substc a v2 B2) (substc a' v2 B2))
      # ext_eq lib (mkc_isect A1 v1 B1) (mkc_isect A2 v2 B2)
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

  - apply ext_eq_implies_tequality; auto.

    + generalize (choice_teq lib A1 v1 B1 v1 B1 h2); intro n; exrepnd.

      unfold type in h0; exrepnd.
      rename eq into eqa1.

      pose proof (Nuprl_type_family_equality_to_eq2 lib A1 v1 v1 B1 B1 eqa1 f h4 n0) as imp1.
      clear n0.

      exists (per_isect_eq eqa1 (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A1 eqa1 e h4))).

      apply CL_isect; fold (@nuprl p lib).

      exists eqa1.
      exists (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A1 eqa1 e h4)); sp.

      exists A1 v1 B1; sp; eauto 3 with slow;
        try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_isect))).

      eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.

    + generalize (choice_teq lib A2 v2 B2 v2 B2 h3); intro w; exrepnd.

      unfold type in h1; exrepnd.
      rename eq into eqa2.

      pose proof (Nuprl_type_family_equality_to_eq2 lib A2 v2 v2 B2 B2 eqa2 f h4 w0) as imp2.
      clear w0.

      exists (per_isect_eq eqa2 (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A2 eqa2 e h4))).

      apply CL_isect; fold (@nuprl p lib).

      exists eqa2.
      exists (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A2 eqa2 e h4)); sp.

      exists A2 v2 B2; sp; eauto 3 with slow;
        try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

      eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

(*
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
 *)


Lemma implies_equality_isect {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib A1 A2 (mkc_uni i)
    -> (forall a a',
           equality lib a a' A1
           -> equality lib (substc a v1 B1) (substc a' v2 B2) (mkc_uni i))
    -> equality lib (mkc_isect A1 v1 B1) (mkc_isect A2 v2 B2) (mkc_uni i).
Proof.
  introv eqa eqb.

  unfold equality in eqa; exrepnd.
  inversion eqa1; subst; try not_univ.
  duniv j h.
  allrw @univi_exists_iff; exrepd.
  computes_to_value_isvalue; GC.
  apply e in eqa0.
  unfold univi_eq, extts in eqa0; exrepnd.
  allfold (@nuprli p lib j0).

  exists eq; sp.
  apply e.

  generalize (choice_teqi lib j0 A1 v1 B1 v2 B2 eqb); intro n; exrepnd.

  exists (per_isect_eq eqa (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e eqa0))).

  split; apply CL_isect; fold (@nuprl p lib).

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e eqa0)); sp.

    exists A1 v1 B1; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_isect))).

    pose proof (Nuprli_type_family_equality_to_eq lib j0 A1 v1 v2 B1 B2 eqa f eqa0 n0) as imp.
    clear n0.

    pose proof (Nuprli_type_family_equality_to_Nuprli_left
                  lib j0 A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e eqa0))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply Nuprli_implies_type_family_members_eq; auto; eauto 2 with slow.

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e eqa0)); sp.

    exists A2 v2 B2; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

    pose proof (Nuprli_type_family_equality_to_eq lib j0 A1 v1 v2 B1 B2 eqa f eqa0 n0) as imp.
    clear n0.

    pose proof (Nuprli_type_family_equality_to_Nuprli_right
                  lib j0 A1 v1 v2 B1 B2 eqa
                  (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e eqa0))) as imp1.
    simpl in imp1; repeat (autodimp imp1 hyp); clear imp; eauto 3 with slow;[].

    eapply Nuprli_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

Lemma nuprli_eq_type_family_members_eq_implies_ext_eq_isect_one_direction {o} :
  forall lib i (A1 A2 : @CTerm o) v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    nuprli lib i A1 eqa1
    -> nuprli lib i A2 eqa2
    -> type_family_members_eq (nuprli lib i) v1 B1 eqa1 eqb1
    -> type_family_members_eq (nuprli lib i) v2 B2 eqa2 eqb2
    -> (forall a b, per_isect_eq eqa1 eqb1 a b -> per_isect_eq eqa2 eqb2 a b)
    -> forall a b, equality lib a b (mkc_isect A1 v1 B1)
                   -> equality lib a b (mkc_isect A2 v2 B2).
Proof.
  introv na1 na2 tf1 tf2 imp h.

  apply equality_in_isect in h; repnd.
  apply equality_in_isect.

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

    unfold per_isect_eq in q.
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

Lemma nuprli_eq_type_family_members_eq_implies_ext_eq_isect {o} :
  forall lib i (A1 A2 : @CTerm o) v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    nuprli lib i A1 eqa1
    -> nuprli lib i A2 eqa2
    -> type_family_members_eq (nuprli lib i) v1 B1 eqa1 eqb1
    -> type_family_members_eq (nuprli lib i) v2 B2 eqa2 eqb2
    -> ((per_isect_eq eqa1 eqb1) <=2=> (per_isect_eq eqa2 eqb2))
    -> ext_eq lib (mkc_isect A1 v1 B1) (mkc_isect A2 v2 B2).
Proof.
  introv na1 na2 tf1 tf2 eqiff.
  split; intro h.

  - eapply nuprli_eq_type_family_members_eq_implies_ext_eq_isect_one_direction;
      try (exact h); eauto.
    introv xx; apply eqiff; auto.

  - eapply nuprli_eq_type_family_members_eq_implies_ext_eq_isect_one_direction;
      try (exact h); eauto.
    introv xx; apply eqiff; auto.
Qed.

Lemma equality_isect {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality
      lib
      (mkc_isect A1 v1 B1)
      (mkc_isect A2 v2 B2)
      (mkc_uni i)
    <=>
    (
      member lib A1 (mkc_uni i)
      # member lib A2 (mkc_uni i)
      # (forall a a', equality lib a a' A1 -> equality lib (substc a v1 B1) (substc a' v1 B1) (mkc_uni i))
      # (forall a a', equality lib a a' A2 -> equality lib (substc a v2 B2) (substc a' v2 B2) (mkc_uni i))
      # ext_eq lib (mkc_isect A1 v1 B1) (mkc_isect A2 v2 B2)
    ).
Proof.
  introv; split; intro h; repnd.

  - unfold equality, nuprl in h; exrepnd.
    inversion h1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    apply e in h0; unfold univi_eq, extts in h0; exrepnd.

    cioneclose_eq eqa; subst; try not_univ.
    cioneclose_eq eqa; subst; try not_univ.

    one_dest_per_fam eqa1 feqb1 A3 v3 B3 c1 tsa1 tsb1 eqt1.
    match goal with
    | [ H : per_isect _ _ _ _ |- _ ] => dest_per_fam H eqa2 feqb2 A4 v4 B4 c2 tsa2 tsb2 eqt2
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

    { eapply nuprli_eq_type_family_members_eq_implies_ext_eq_isect; eauto.
      eapply eq_term_equals_trans;[|eauto].
      apply eq_term_equals_sym; auto. }

  - apply (ext_eq_implies_tequalityi lib i) in h; auto; clear h;
      apply implies_equality_isect; auto.
Qed.

Lemma type_isect {p} :
  forall lib (A : @CTerm p) v B,
    type lib (mkc_isect A v B)
    <=>
    (
      type lib A
      # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
    ).
Proof.
  introv.
  rw <- @fold_type.
  rw @tequality_isect.
  split; intro h; repnd; dands; auto; eauto 2 with slow.
Qed.
