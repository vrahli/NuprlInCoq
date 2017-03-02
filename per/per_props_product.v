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

    one_dest_per_fam eqa feqb A1 v1 B1 c1 tsa tsb eqt.
    allunfold_per; spcast; try (computes_to_eqval); allfold (@nuprl p lib).
    computes_to_value_isvalue; dands.

    + exists eqa; sp.

    + introv e.
      unfold equality in e; exrepnd.
      generalize (nuprl_uniquely_valued lib A1 eqa eq0); intro k; repeat (dest_imp k hyp).
      rw <- k in e2.
      eapply nuprl_type_family_members_eq_implies_tequality; try (exact tsb); eauto.

    + rw eqt in e0.
      unfold per_product_eq in e0; exrepnd.
      exists a a' b b'; dands; auto.
      { exists eqa; sp. }
      exists (feqb a a' e); sp.
      apply tsb.

  - unfold type, tequality in e0; exrepnd.
    rename eq into eqa.

    pose proof (choice_teq1 lib A eqa v B v B) as n.
    repeat (autodimp n hyp); exrepnd; eauto 2 with slow.
    rename f into eqb.

    exists (per_product_eq lib eqa eqb).

    dands.

    {
      apply CL_product; fold (@nuprl p lib); unfold per_product.
      exists eqa eqb.

      dands; sp.

      exists A v B; sp;
        try (complete (spcast; apply computes_to_valc_refl; eauto 2 with slow)).

      eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
    }

    {
      assert (eqa a1 a2) as ea.
      { pose proof (equality_eq lib A a1 a2 eqa) as q; apply q; auto. }
      exists a1 a2 b1 b2 ea; dands; spcast; auto.
      pose proof (equality_eq lib (B)[[v\\a1]] b1 b2 (eqb a1 a2 ea)) as q.
      apply q; auto.
      apply n0.
    }
Qed.

Hint Rewrite @csubst_mk_cv : slow.

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
  split; intro k; exrepnd; dands; auto; eauto 3 with slow;
    autorewrite with slow in *.

  { introv i.
    unfold inhabited_type in i; exrepnd.
    generalize (k1 t t); intro j; autodimp j hyp.
    repeat (rw @csubst_mk_cv in j); sp; eauto 2 with slow. }

  { exists a1 a2 b1 b2; dands; auto. }

  { introv e.
    repeat (rw @csubst_mk_cv); sp.
    autodimp k1 hyp; eauto 2 with slow.
    exists a; allapply @equality_refl; sp. }

  { exists a1 a2 b1 b2; dands; auto; autorewrite with slow in *; auto. }
Qed.

(*
Lemma tequality_product {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality
      lib
      (mkc_product A1 v1 B1)
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
 *)


Lemma tequality_product {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib (mkc_product A1 v1 B1) (mkc_product A2 v2 B2)
    <=>
    (
      type lib A1
      # type lib A2
      # (forall a a', equality lib a a' A1 -> tequality lib (substc a v1 B1) (substc a' v1 B1))
      # (forall a a', equality lib a a' A2 -> tequality lib (substc a v2 B2) (substc a' v2 B2))
      # ext_eq lib (mkc_product A1 v1 B1) (mkc_product A2 v2 B2)
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

      exists (per_product_eq lib eqa1 (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A1 eqa1 e h4))).

      apply CL_product; fold (@nuprl p lib).

      exists eqa1.
      exists (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A1 eqa1 e h4)); sp.

      exists A1 v1 B1; sp; eauto 3 with slow;
        try (complete (spcast; apply computes_to_valc_refl; eauto 2 with slow)).

      eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.

    + generalize (choice_teq lib A2 v2 B2 v2 B2 h3); intro w; exrepnd.

      unfold type in h1; exrepnd.
      rename eq into eqa2.

      pose proof (Nuprl_type_family_equality_to_eq2 lib A2 v2 v2 B2 B2 eqa2 f h4 w0) as imp2.
      clear w0.

      exists (per_product_eq lib eqa2 (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A2 eqa2 e h4))).

      apply CL_product; fold (@nuprl p lib).

      exists eqa2.
      exists (fun a1 a2 e => f a1 a2 (eq_equality0 lib a1 a2 A2 eqa2 e h4)); sp.

      exists A2 v2 B2; sp; eauto 3 with slow;
        try (complete (spcast; apply computes_to_valc_refl; eauto 3 with slow)).

      eapply Nuprl_implies_type_family_members_eq; auto; eauto 2 with slow.
Qed.

(*
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
 *)


Lemma tequality_mkc_prod {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p),
    tequality lib (mkc_prod A1 B1) (mkc_prod A2 B2)
    <=>
    (
      type lib A1
      # type lib A2
      # (inhabited_type lib A1 -> type lib B1)
      # (inhabited_type lib A2 -> type lib B2)
      # ext_eq lib (mkc_prod A1 B1) (mkc_prod A2 B2)
    ).
Proof.
  introv.
  allrw <- @fold_mkc_prod.
  rw @tequality_product.
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

Lemma type_mkc_prod {p} :
  forall lib (A B : @CTerm p),
    type lib (mkc_prod A B)
    <=> (type lib A # (inhabited_type lib A -> type lib B)).
Proof.
  introv.
  repeat (rw <- @fold_type).
  rw @tequality_mkc_prod; split; intro h; repnd; dands; auto; eauto 2 with slow; GC.

  - intro x; apply h2 in x; eauto 2 with slow.

  - intro x; apply h in x; eauto 2 with slow.

  - intro x; apply h in x; eauto 2 with slow.
Qed.

(*
Lemma equality_product {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib (mkc_product A1 v1 B1)
             (mkc_product A2 v2 B2)
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

    exists ( per_product_eq lib eqa 
                         (fun a1 a2 (e:eqa a1 a2) => 
                           f a1 a2 
                           (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)
                         )).
    unfold nuprli.
    apply CL_product; fold (@nuprli p lib j0).
    unfold per_product.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality3 lib a1 a2 A1 A2 eqa j0 e h0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_product))).
Qed.
 *)


Lemma implies_equality_product {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality lib A1 A2 (mkc_uni i)
    -> (forall a a',
           equality lib a a' A1
           -> equality lib (substc a v1 B1) (substc a' v2 B2) (mkc_uni i))
    -> equality lib (mkc_product A1 v1 B1) (mkc_product A2 v2 B2) (mkc_uni i).
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

  exists (per_product_eq lib eqa (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e eqa0))).

  split; apply CL_product; fold (@nuprl p lib).

  - exists eqa.
    exists (fun a1 a2 e => f a1 a2 (eq_equality4 lib a1 a2 A1 eqa j0 e eqa0)); sp.

    exists A1 v1 B1; sp; eauto 3 with slow;
      try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_product))).

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

Lemma nuprli_eq_type_family_members_eq_implies_ext_eq_product_one_direction {o} :
  forall lib i (A1 A2 : @CTerm o) v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    nuprli lib i A1 eqa1
    -> nuprli lib i A2 eqa2
    -> type_family_members_eq (nuprli lib i) v1 B1 eqa1 eqb1
    -> type_family_members_eq (nuprli lib i) v2 B2 eqa2 eqb2
    -> (forall a b, per_product_eq lib eqa1 eqb1 a b -> per_product_eq lib eqa2 eqb2 a b)
    -> forall a b, equality lib a b (mkc_product A1 v1 B1)
                   -> equality lib a b (mkc_product A2 v2 B2).
Proof.
  introv na1 na2 tf1 tf2 imp h.

  apply equality_in_product in h; repnd.
  apply equality_in_product.

  dands; eauto 2 with slow.

  {
    introv ea.
    apply (tequalityi_implies_tequality lib i).
    eapply nuprli_type_family_members_eq_implies_tequalityi;[|exact tf2|]; eauto.
    eapply equality_eq;[|exact ea]; eauto 2 with slow.
  }

  {
    exrepnd.

    assert (eqa1 a1 a2) as ea1.
    { eapply equality_eq;[|exact h5]; eauto 2 with slow. }

    pose proof (imp a b) as q; clear imp.
    autodimp q hyp.

    {
      unfold per_product_eq.
      exists a1 a2 b1 b2 ea1; dands; auto.

      destruct tf1 as [tfb famb].
      pose proof (tfb a1 a2 ea1) as w.
      eapply nuprli_implies_equality_eq; eauto.
    }

    unfold per_product_eq in q; exrepnd.
    spcast; repeat computes_to_eqval.
    exists a1 a2 b1 b2; dands; spcast; auto.

    { apply (eq_equality4 lib a1 a2 A2 eqa2 i); auto. }

    {
      destruct tf2 as [tfb famb].
      pose proof (tfb a1 a2 e) as w.
      eapply nuprli_and_eq_implies_equality; eauto.
    }
  }
Qed.

Lemma nuprli_eq_type_family_members_eq_implies_ext_eq_product {o} :
  forall lib i (A1 A2 : @CTerm o) v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    nuprli lib i A1 eqa1
    -> nuprli lib i A2 eqa2
    -> type_family_members_eq (nuprli lib i) v1 B1 eqa1 eqb1
    -> type_family_members_eq (nuprli lib i) v2 B2 eqa2 eqb2
    -> ((per_product_eq lib eqa1 eqb1) <=2=> (per_product_eq lib eqa2 eqb2))
    -> ext_eq lib (mkc_product A1 v1 B1) (mkc_product A2 v2 B2).
Proof.
  introv na1 na2 tf1 tf2 eqiff.
  split; intro h.

  - eapply nuprli_eq_type_family_members_eq_implies_ext_eq_product_one_direction;
      try (exact h); eauto.
    introv xx; apply eqiff; auto.

  - eapply nuprli_eq_type_family_members_eq_implies_ext_eq_product_one_direction;
      try (exact h); eauto.
    introv xx; apply eqiff; auto.
Qed.

Lemma equality_product {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2 i,
    equality
      lib
      (mkc_product A1 v1 B1)
      (mkc_product A2 v2 B2)
      (mkc_uni i)
    <=>
    (
      member lib A1 (mkc_uni i)
      # member lib A2 (mkc_uni i)
      # (forall a a', equality lib a a' A1 -> equality lib (substc a v1 B1) (substc a' v1 B1) (mkc_uni i))
      # (forall a a', equality lib a a' A2 -> equality lib (substc a v2 B2) (substc a' v2 B2) (mkc_uni i))
      # ext_eq lib (mkc_product A1 v1 B1) (mkc_product A2 v2 B2)
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
    | [ H : per_product _ _ _ _ |- _ ] => dest_per_fam H eqa2 feqb2 A4 v4 B4 c2 tsa2 tsb2 eqt2
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

    { eapply nuprli_eq_type_family_members_eq_implies_ext_eq_product; eauto.
      eapply eq_term_equals_trans;[|eauto].
      apply eq_term_equals_sym; auto. }

  - apply (ext_eq_implies_tequalityi lib i) in h; auto; clear h;
      apply implies_equality_product; auto.
Qed.
