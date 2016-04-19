(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Export per_props.
Require Export terms_union.
Require Export cequiv_props.
Require Export per_props_cequiv.


Lemma tequality_mkc_union {p} :
  forall lib (A1 B1 A2 B2 : @CTerm p),
    tequality lib (mkc_union A1 B1) (mkc_union A2 B2)
    <=> (tequality lib A1 A2 # tequality lib B1 B2).
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    inversion teq0; try not_univ; allunfold @per_union; exrepnd.
    computes_to_value_isvalue; sp; try (complete (spcast; sp)).
    exists eqa; sp.
    exists eqb; sp.

  - unfold tequality in teq0; exrepnd.
    rename eq into eqa.
    unfold tequality in teq; exrepnd.
    rename eq into eqb.
    exists (per_union_eq lib eqa eqb); apply CL_union; unfold per_union.
    exists eqa eqb A1 A2 B1 B2; sp; spcast;
    try (apply computes_to_valc_refl; apply iscvalue_mkc_union).
Qed.

Lemma tequality_mkc_or {p} :
  forall lib (A1 B1 A2 B2 : @CTerm p),
    tequality lib (mkc_or A1 B1) (mkc_or A2 B2)
    <=> (tequality lib A1 A2 # tequality lib B1 B2).
Proof.
  introv; rw @tequality_mkc_union; sp.
Qed.

Lemma equality_mkc_union {p} :
  forall lib (t1 t2 A B : @CTerm p),
    equality lib t1 t2 (mkc_union A B)
    <=> (type lib A
         # type lib B
         # ({a1, a2 : CTerm
             , t1 ===>(lib) (mkc_inl a1)
             # t2 ===>(lib) (mkc_inl a2)
             # equality lib a1 a2 A}
            {+}
            {b1, b2 : CTerm
             , t1 ===>(lib) (mkc_inr b1)
             # t2 ===>(lib) (mkc_inr b2)
             # equality lib b1 b2 B})).
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    inversion e1; subst; try not_univ.
    allunfold @per_union; exrepnd; spcast; computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    dands.
    exists eqa; sp.
    exists eqb; sp.
    allunfold @per_union_eq; repdors.

    left.
    allunfold @per_union_eq_L; exrepnd.
    exists x y; sp.
    exists eqa; sp.

    right.
    allunfold @per_union_eq_R; exrepnd.
    exists x y; sp.
    exists eqb; sp.

  - exrepnd.
    unfold type, tequality in e0; exrepnd.
    rename eq into eqa.
    unfold type, tequality in e1; exrepnd.
    rename eq into eqb.
    exists (per_union_eq lib eqa eqb); dands.
    apply CL_union; unfold per_union.
    exists eqa eqb A A B B; sp; spcast; sp;
    try (apply computes_to_valc_refl; apply iscvalue_mkc_union).
    unfold per_union_eq.
    repdors; exrepnd.

    left.
    unfold per_union_eq_L.
    exists a1 a2; sp.
    allunfold @equality; exrepnd.
    generalize (nuprl_uniquely_valued lib A eqa eq); intro h; repeat (dest_imp h hyp).
    rw h; sp.

    right.
    unfold per_union_eq_R.
    exists b1 b2; sp.
    allunfold @equality; exrepnd.
    generalize (nuprl_uniquely_valued lib B eqb eq); intro h; repeat (dest_imp h hyp).
    rw h; sp.
Qed.

Lemma equality_mkc_or {p} :
  forall lib (t1 t2 A B : @CTerm p),
    equality lib t1 t2 (mkc_or A B)
    <=> (type lib A
         # type lib B
         # ({a1, a2 : CTerm
             , t1 ===>(lib) (mkc_inl a1)
             # t2 ===>(lib) (mkc_inl a2)
             # equality lib a1 a2 A}
            {+}
            {b1, b2 : CTerm
             , t1 ===>(lib) (mkc_inr b1)
             # t2 ===>(lib) (mkc_inr b2)
             # equality lib b1 b2 B})).
Proof.
  introv; rw @equality_mkc_union; sp.
Qed.

Lemma tequality_tunion {p} :
  forall lib (A1 A2 : @CTerm p) v1 v2 B1 B2,
    tequality lib (mkc_tunion A1 v1 B1)
              (mkc_tunion A2 v2 B2)
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

    exists (per_tunion_eq eqa (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0))).
    apply CL_tunion; fold (@nuprl p lib).
    unfold per_tunion.
    exists eqa.

    exists (fun a1 a2 e => f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e teqa0)); sp.

    exists A1 A2 v1 v2 B1 B2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_tunion))).
Qed.

Lemma tequality_bool {o} :
  forall lib, @tequality o lib mkc_bool mkc_bool.
Proof.
  introv.
  allrw <- @fold_mkc_bool.
  rw @tequality_mkc_union; dands; auto; apply tequality_unit.
Qed.

Lemma equality_in_bool {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_bool
    <=>
    (
      (a ~=~(lib) tt # b ~=~(lib) tt)
      {+}
      (a ~=~(lib) ff # b ~=~(lib) ff)
    ).
Proof.
  introv.
  allrw <- @fold_mkc_bool.
  rw @equality_mkc_union; split; intro k; repnd.

  - dorn k; exrepnd.

    + allrw @equality_in_unit; repnd.
      left; dands; spcast.

      * allapply @computes_to_valc_implies_cequivc.
        apply (cequivc_trans lib a (mkc_inl a1) tt); auto.
        apply cequivc_mkc_inl_if; auto.

      * allapply @computes_to_valc_implies_cequivc.
        apply (cequivc_trans lib b (mkc_inl a2) tt); auto.
        apply cequivc_mkc_inl_if; auto.

    + allrw @equality_in_unit; repnd.
      right; dands; spcast.

      * allapply @computes_to_valc_implies_cequivc.
        apply (cequivc_trans lib a (mkc_inr b1) ff); auto.
        apply cequivc_mkc_inr_if; auto.

      * allapply @computes_to_valc_implies_cequivc.
        apply (cequivc_trans lib b (mkc_inr b2) ff); auto.
        apply cequivc_mkc_inr_if; auto.

  - dands; auto.
    dorn k; repnd.

    + left.
      spcast.
      apply cequivc_sym in k0.
      apply cequivc_sym in k.
      apply cequivc_mkc_inl_implies in k0.
      apply cequivc_mkc_inl_implies in k.
      exrepnd.
      exists b1 b0; dands; auto; spcast; sp.
      apply equality_in_unit; sp; spcast; sp; apply cequivc_axiom_implies; sp.

    + right.
      spcast.
      apply cequivc_sym in k0.
      apply cequivc_sym in k.
      apply cequivc_mkc_inr_implies in k0.
      apply cequivc_mkc_inr_implies in k.
      exrepnd.
      exists b1 b0; dands; auto; spcast; sp.
      apply equality_in_unit; sp; spcast; sp; apply cequivc_axiom_implies; sp.
Qed.


Lemma substc_mkcv_ite {o} :
  forall v (t a b : @CTerm o),
    substc t v (mkcv_ite [v] (mkc_var v) (mk_cv [v] a) (mk_cv [v] b))
    = mkc_ite t a b.
Proof.
  introv.
  apply cterm_eq; simpl.
  destruct_cterms; simpl.
  unfold mk_ite, subst.
  change_to_lsubst_aux4; simpl.
  pose proof (newvar_prog x1 i1) as e1.
  pose proof (newvar_prog x0 i0) as e2.
  pose proof (newvar_prog x i) as e3.
  rw e2; rw e3.
  boolvar; allrw @lsubst_aux_nil; sp.
  allrw @lsubst_aux_trivial; auto.

  introv k; simpl in k; dorn k; cpx.
  dands; auto.
  apply isprogram_eq; sp.
  intro k.
  rw @isprog_eq in i.
  destruct i as [c w]; rw c in k; allsimpl; sp.

  introv k; simpl in k; dorn k; cpx.
  dands; auto.
  apply isprogram_eq; sp.
  intro k.
  rw @isprog_eq in i0.
  destruct i0 as [c w]; rw c in k; allsimpl; sp.

  allrw app_nil_r.
  rw @isprog_eq in i1.
  destruct i1 as [c w]; rw c; sp.
Qed.

Lemma mkc_ite_ceq_tt {o} :
  forall lib (a A B : @CTerm o),
    cequivc lib a tt
    -> cequivc lib (mkc_ite a A B) A.
Proof.
  introv ceq.
  destruct_cterms; allunfold @cequivc; allsimpl.
  apply cequiv_trans with (b := mk_decide (mk_inl mk_axiom) nvarx x0 nvarx x).

  allunfold @mk_decide.
  applydup @cequiv_isprogram in ceq; repnd.
  repeat(prove_cequiv); auto.

  unfold blift; exists [nvarx] x0 x0; dands; auto.
  apply olift_approx_cequiv; sp;apply approx_open_refl;
  rw @isprog_eq in i0; destruct i0 as [c w]; sp.

  unfold blift; exists [nvarx] x x; dands; auto.
  apply olift_approx_cequiv; sp;apply approx_open_refl;
  rw @isprog_eq in i; destruct i as [c w]; sp.

  constructor; unfold closed_bt; simpl.
  rw @isprog_eq in i0; destruct i0 as [c w]; rw c; rw remove_nvars_nil_r; sp.
  constructor.
  rw @isprog_eq in i0; destruct i0 as [c w]; sp.

  constructor; unfold closed_bt; simpl.
  rw @isprog_eq in i; destruct i as [c w]; rw c; rw remove_nvars_nil_r; sp.
  constructor.
  rw @isprog_eq in i; destruct i as [c w]; sp.

  constructor; unfold closed_bt; simpl.
  rw @isprog_eq in i0; destruct i0 as [c w]; rw c; rw remove_nvars_nil_r; sp.
  constructor.
  rw @isprog_eq in i0; destruct i0 as [c w]; sp.

  constructor; unfold closed_bt; simpl.
  rw @isprog_eq in i; destruct i as [c w]; rw c; rw remove_nvars_nil_r; sp.
  constructor.
  rw @isprog_eq in i; destruct i as [c w]; sp.

  apply reduces_to_implies_cequiv.
  apply isprogram_decide; sp.
  apply isprogram_inl; sp.
  rw @isprog_eq in i0; destruct i0 as [c w]; rw c; sp.
  rw @isprog_eq in i0; destruct i0 as [c w]; sp.
  rw @isprog_eq in i; destruct i as [c w]; rw c; sp.
  rw @isprog_eq in i; destruct i as [c w]; sp.
  apply reduces_to_if_step; simpl.
  csunf; simpl.
  unfold apply_bterm; simpl.
  rw @lsubst_trivial; auto.
  introv k; simpl in k; dorn k; cpx.
  rw @isprog_eq in i0; destruct i0 as [c w]; rw c; sp.
Qed.

Lemma mkc_ite_ceq_ff {o} :
  forall lib (a A B : @CTerm o),
    cequivc lib a ff
    -> cequivc lib (mkc_ite a A B) B.
Proof.
  introv ceq.
  destruct_cterms; allunfold @cequivc; allsimpl.
  apply cequiv_trans with (b := mk_decide (mk_inr mk_axiom) nvarx x0 nvarx x).

  allunfold @mk_decide.
  applydup @cequiv_isprogram in ceq; repnd.
  repeat(prove_cequiv); auto.

  unfold blift; exists [nvarx] x0 x0; dands; auto.
  apply olift_approx_cequiv; sp;apply approx_open_refl;
  rw @isprog_eq in i0; destruct i0 as [c w]; sp.

  unfold blift; exists [nvarx] x x; dands; auto.
  apply olift_approx_cequiv; sp;apply approx_open_refl;
  rw @isprog_eq in i; destruct i as [c w]; sp.

  constructor; unfold closed_bt; simpl.
  rw @isprog_eq in i0; destruct i0 as [c w]; rw c; rw remove_nvars_nil_r; sp.
  constructor.
  rw @isprog_eq in i0; destruct i0 as [c w]; sp.

  constructor; unfold closed_bt; simpl.
  rw @isprog_eq in i; destruct i as [c w]; rw c; rw remove_nvars_nil_r; sp.
  constructor.
  rw @isprog_eq in i; destruct i as [c w]; sp.

  constructor; unfold closed_bt; simpl.
  rw @isprog_eq in i0; destruct i0 as [c w]; rw c; rw remove_nvars_nil_r; sp.
  constructor.
  rw @isprog_eq in i0; destruct i0 as [c w]; sp.

  constructor; unfold closed_bt; simpl.
  rw @isprog_eq in i; destruct i as [c w]; rw c; rw remove_nvars_nil_r; sp.
  constructor.
  rw @isprog_eq in i; destruct i as [c w]; sp.

  apply reduces_to_implies_cequiv.
  apply isprogram_decide; sp.
  apply isprogram_inr; sp.
  rw @isprog_eq in i0; destruct i0 as [c w]; rw c; sp.
  rw @isprog_eq in i0; destruct i0 as [c w]; sp.
  rw @isprog_eq in i; destruct i as [c w]; rw c; sp.
  rw @isprog_eq in i; destruct i as [c w]; sp.
  apply reduces_to_if_step; simpl.
  csunf; simpl.
  unfold apply_bterm; simpl.
  rw @lsubst_trivial; auto.
  introv k; simpl in k; dorn k; cpx.
  rw @isprog_eq in i; destruct i as [c w]; rw c; sp.
Qed.

Lemma mkc_ite_tt {o} :
  forall lib (A B : @CTerm o),
    cequivc lib (mkc_ite tt A B) A.
Proof.
  introv.
  apply mkc_ite_ceq_tt; sp.
Qed.

Lemma mkc_ite_ff {o} :
  forall lib (A B : @CTerm o),
    cequivc lib (mkc_ite ff A B) B.
Proof.
  introv.
  apply mkc_ite_ceq_ff; sp.
Qed.

Lemma tequality_bunion {o} :
  forall lib (A B C D : @CTerm o),
    tequality lib (mkc_bunion A B) (mkc_bunion C D)
    <=> (tequality lib A C # tequality lib B D).
Proof.
  introv.
  allrw <- @fold_mkc_bunion.
  rw @tequality_tunion.

  split; intro k; repnd.

  - pose proof (k tt tt) as h1.
    autodimp h1 hyp.
    apply equality_in_bool; left; sp; spcast; sp.

    pose proof (k ff ff) as h2.
    autodimp h2 hyp.
    apply equality_in_bool; right; sp; spcast; sp.

    allrw @substc_mkcv_ite.
    pose proof (mkc_ite_tt lib A B) as c1.
    pose proof (mkc_ite_ff lib A B) as c2.
    pose proof (mkc_ite_tt lib C D) as c3.
    pose proof (mkc_ite_ff lib C D) as c4.
    apply tequality_respects_cequivc_left with (T3 := A) in h1; auto.
    apply tequality_respects_cequivc_left with (T3 := B) in h2; auto.
    apply tequality_respects_cequivc_right with (T3 := C) in h1; auto.
    apply tequality_respects_cequivc_right with (T3 := D) in h2; auto.

  - dands; auto.
    apply tequality_bool.
    introv e.
    rw @equality_in_bool in e; dorn e; repnd; spcast.

    + allrw @substc_mkcv_ite.
      pose proof (mkc_ite_ceq_tt lib a A B e0) as c1.
      pose proof (mkc_ite_ceq_tt lib a' C D e) as c2.
      apply tequality_respects_cequivc_left with (T1 := A); auto.
      apply cequivc_sym; auto.
      apply tequality_respects_cequivc_right with (T2 := C); auto.
      apply cequivc_sym; auto.

    + allrw @substc_mkcv_ite.
      pose proof (mkc_ite_ceq_ff lib a A B e0) as c1.
      pose proof (mkc_ite_ceq_ff lib a' C D e) as c2.
      apply tequality_respects_cequivc_left with (T1 := B); auto.
      apply cequivc_sym; auto.
      apply tequality_respects_cequivc_right with (T2 := D); auto.
      apply cequivc_sym; auto.
Qed.



Inductive equal_in_tunion {p} lib A v B (t1 t2 : @CTerm p) : [U] :=
| eq_in_tunion_cl :
    forall t,
      equal_in_tunion lib A v B t1 t
      -> equal_in_tunion lib A v B t t2
      -> equal_in_tunion lib A v B t1 t2
| eq_in_tunion_eq :
    forall a,
      member lib a A
      -> equality lib t1 t2 (substc a v B)
      -> equal_in_tunion lib A v B t1 t2.

Lemma equality_in_mkc_tunion {p} :
  forall lib A v B (t1 t2 : @CTerm p),
    equality lib t1 t2 (mkc_tunion A v B)
    <=> (type lib A
         # (forall a a', equality lib a a' A -> tequality lib (substc a v B) (substc a' v B))
         # equal_in_tunion lib A v B t1 t2).
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    inversion e1; subst; try not_univ.
    one_dest_per_fam eqa feqb A3 A4 v3 v4 B3 B4 c1 c2 tsa tsb eqt.
    computes_to_value_isvalue.
    allfold (@nuprl p).
    dands.

    + apply tequality_if_nuprl in tsa; auto.

    + introv ea.
      assert (eqa a a')
        as xa
          by (generalize (equality_eq1 lib A3 A3 a a' eqa); intro e;
              dest_imp e hyp;
              try (exists i; auto);
              apply e; auto).
      pose proof (tsb a a' xa) as h.
      apply tequality_if_nuprl in h; auto.

    + rw eqt in e0.
      induction e0.
      apply @eq_in_tunion_cl with (t := t); auto.
      apply @eq_in_tunion_eq with (a := a1); sp.

      * dup e as e'.
        rw (equality_eq lib A3 a1 a2 _ tsa) in e'.
        apply equality_refl in e'; auto.

      * pose proof (tsb a1 a2 e) as h.
        apply (equality_eq1 lib
              (substc a1 v3 B3) (substc a2 v3 B3)
              t1 t2 (feqb a1 a2 e) h); auto.

  - repnd.

    unfold type, tequality in e0; exrepnd.
    rename eq into eqa.

    pose proof (choice_teq1 lib A eqa v B v B e2 e1) as h.
    exrepnd.
    rename f into eqb.

    exists (per_tunion_eq eqa eqb).
    dands.

    + apply CL_tunion.
      exists eqa eqb; dands; auto.
      exists A A v v B B; dands; spcast; auto;
      try (apply computes_to_valc_refl; apply iscvalue_mkc_tunion).

    + induction e.
      apply @tunion_eq_cl with (t := t); sp.
      pose proof (equality_eq lib A a a _ e2).
      assert (eqa a a) as e by (allrw; sp).
      apply @tunion_eq_eq with (a1 := a) (a2 := a) (e := e); sp.
      pose proof (h0 a a e) as t.
      pose proof (equality_eq lib (substc a v B) t1 t2 _ t).
      allrw; auto.
Qed.

Lemma member_in_bool {o} :
  forall lib (a : @CTerm o),
    member lib a mkc_bool
    <=>
    (a ~=~(lib) tt {+} a ~=~(lib) ff).
Proof.
  introv.
  rw @equality_in_bool; split; sp.
Qed.

Inductive equal_in_bunion {p} lib (A B t1 t2 : @CTerm p) : [U] :=
| eq_in_bunion_cl :
    forall t,
      equal_in_bunion lib A B t1 t
      -> equal_in_bunion lib A B t t2
      -> equal_in_bunion lib A B t1 t2
| eq_in_bunion_eq1 :
    equality lib t1 t2 A
    -> equal_in_bunion lib A B t1 t2
| eq_in_bunion_eq2 :
    equality lib t1 t2 B
    -> equal_in_bunion lib A B t1 t2.

Lemma equality_in_mkc_bunion {p} :
  forall lib (A B t1 t2 : @CTerm p),
    equality lib t1 t2 (mkc_bunion A B)
    <=> (type lib A # type lib B
         # equal_in_bunion lib A B t1 t2).
Proof.
  introv.
  rw <- @fold_mkc_bunion.
  rw @equality_in_mkc_tunion.
  split; intro k; repnd.

  - pose proof (k1 tt tt) as h1.
    autodimp h1 hyp.
    apply equality_in_bool; left; sp; spcast; sp.

    pose proof (k1 ff ff) as h2.
    autodimp h2 hyp.
    apply equality_in_bool; right; sp; spcast; sp.

    allrw @substc_mkcv_ite.
    pose proof (mkc_ite_tt lib A B) as c1.
    pose proof (mkc_ite_ff lib A B) as c2.
    apply tequality_respects_cequivc_left with (T3 := A) in h1; auto.
    apply tequality_respects_cequivc_left with (T3 := B) in h2; auto.
    apply tequality_respects_cequivc_right with (T3 := A) in h1; auto.
    apply tequality_respects_cequivc_right with (T3 := B) in h2; auto.

    dands; auto.

    induction k.
    apply @eq_in_bunion_cl with (t := t); auto.
    allrw @substc_mkcv_ite.
    allrw @member_in_bool; sp; spcast.

    pose proof (mkc_ite_ceq_tt lib a A B) as c3; autodimp c3 hyp.
    eapply cequivc_preserving_equality in c3; eauto.
    apply @eq_in_bunion_eq1; auto.

    pose proof (mkc_ite_ceq_ff lib a A B) as c3; autodimp c3 hyp.
    eapply cequivc_preserving_equality in c3; eauto.
    apply @eq_in_bunion_eq2; auto.

  - dands; auto.

    + apply tequality_bool.

    + introv e.
      rw @equality_in_bool in e.
      allrw @substc_mkcv_ite.
      dorn e; repnd; spcast.

      * pose proof (mkc_ite_ceq_tt lib a A B e0) as c1.
        pose proof (mkc_ite_ceq_tt lib a' A B e) as c2.
        apply tequality_respects_cequivc_left with (T1 := A); auto.
        apply cequivc_sym; auto.
        apply tequality_respects_cequivc_right with (T2 := A); auto.
        apply cequivc_sym; auto.

      * pose proof (mkc_ite_ceq_ff lib a A B e0) as c1.
        pose proof (mkc_ite_ceq_ff lib a' A B e) as c2.
        apply tequality_respects_cequivc_left with (T1 := B); auto.
        apply cequivc_sym; auto.
        apply tequality_respects_cequivc_right with (T2 := B); auto.
        apply cequivc_sym; auto.

    + induction k.

      * apply @eq_in_tunion_cl with (t := t); auto.

      * apply @eq_in_tunion_eq with (a := tt).
        apply member_in_bool; left; spcast; sp.
        rw @substc_mkcv_ite.
        pose proof (mkc_ite_tt lib A B) as c.
        eapply cequivc_preserving_equality; eauto.
        apply cequivc_sym; auto.

      * apply @eq_in_tunion_eq with (a := ff).
        apply member_in_bool; right; spcast; sp.
        rw @substc_mkcv_ite.
        pose proof (mkc_ite_ff lib A B) as c.
        eapply cequivc_preserving_equality; eauto.
        apply cequivc_sym; auto.
Qed.


Lemma equality_in_bunion_left {o} :
  forall lib (a b A B : @CTerm o),
    equality lib a b A
    -> type lib B
    -> equality lib a b (mkc_bunion A B).
Proof.
  introv e t.
  applydup @inhabited_implies_tequality in e.
  apply equality_in_mkc_bunion; dands; auto.
  apply eq_in_bunion_eq1; auto.
Qed.

Lemma equality_in_bunion_right {o} :
  forall lib (a b A B : @CTerm o),
    equality lib a b B
    -> type lib A
    -> equality lib a b (mkc_bunion A B).
Proof.
  introv e t.
  applydup @inhabited_implies_tequality in e.
  apply equality_in_mkc_bunion; dands; auto.
  apply eq_in_bunion_eq2; auto.
Qed.

Lemma equorsq_in_bunion_left {o} :
  forall lib (a b A B : @CTerm o),
    equorsq lib a b A
    -> type lib B
    -> equorsq lib a b (mkc_bunion A B).
Proof.
  introv e t.
  allunfold @equorsq.
  dorn e; sp.
  left.
  apply equality_in_bunion_left; auto.
Qed.

Lemma equorsq_in_bunion_right {o} :
  forall lib (a b A B : @CTerm o),
    equorsq lib a b B
    -> type lib A
    -> equorsq lib a b (mkc_bunion A B).
Proof.
  introv e t.
  allunfold @equorsq.
  dorn e; sp.
  left.
  apply equality_in_bunion_right; auto.
Qed.

Lemma equal_in_bunion_change {o} :
  forall lib (A1 B1 a1 b1 A2 B2 a2 b2 : @CTerm o),
    equal_in_bunion lib A1 B1 a1 b1
    -> tequality lib A1 A2
    -> tequality lib B1 B2
    -> equorsq lib a1 a2 A1
    -> equorsq lib b1 b2 B1
    -> equal_in_bunion lib A2 B2 a2 b2.
Proof.
  introv eb teq1 teq2 o1 o2.
  revert dependent b2.
  revert dependent a2.
  revert dependent B2.
  revert dependent A2.
  induction eb; introv teq1 teq2 o1 o2.
  - apply @eq_in_bunion_cl with (t := t); auto.
    apply IHeb1; auto.
    right; spcast; sp.
    apply IHeb2; auto.
    right; spcast; sp.
  - dorn o1; dorn o2; spcast.
    + apply @eq_in_bunion_cl with (t := t1).
      apply @eq_in_bunion_eq1.
      apply equality_sym.
      eapply tequality_preserving_equality; eauto.
      apply @eq_in_bunion_cl with (t := t2).
      apply @eq_in_bunion_eq1.
      eapply tequality_preserving_equality; eauto.
      apply @eq_in_bunion_eq2.
      eapply tequality_preserving_equality; eauto.
    + apply @eq_in_bunion_eq1.
      eapply equality_respects_cequivc_right; eauto.
      eapply tequality_preserving_equality; eauto.
      apply (equality_trans lib a2 t1 t2); auto.
      apply equality_sym; auto.
    + apply @eq_in_bunion_cl with (t := t2).
      apply @eq_in_bunion_eq1.
      eapply tequality_preserving_equality; eauto.
      eapply equality_respects_cequivc_left; eauto.
      apply @eq_in_bunion_eq2.
      eapply tequality_preserving_equality; eauto.
    + apply @eq_in_bunion_eq1.
      eapply tequality_preserving_equality; eauto.
      eapply equality_respects_cequivc_left; eauto.
      eapply equality_respects_cequivc_right; eauto.
  - dorn o1; dorn o2; spcast.
    + apply @eq_in_bunion_cl with (t := t1).
      apply @eq_in_bunion_eq1.
      apply equality_sym.
      eapply tequality_preserving_equality; eauto.
      apply @eq_in_bunion_cl with (t := t2).
      apply @eq_in_bunion_eq2.
      eapply tequality_preserving_equality; eauto.
      apply @eq_in_bunion_eq2.
      eapply tequality_preserving_equality; eauto.
    + apply @eq_in_bunion_cl with (t := t1).
      apply @eq_in_bunion_eq1.
      eapply tequality_preserving_equality; eauto.
      apply equality_sym; auto.
      apply @eq_in_bunion_eq2.
      eapply tequality_preserving_equality; eauto.
      eapply equality_respects_cequivc_right; eauto.
    + apply @eq_in_bunion_eq2.
      eapply equality_respects_cequivc_left; eauto.
      eapply tequality_preserving_equality; eauto.
      apply (equality_trans lib t1 t2 b2); auto.
    + apply @eq_in_bunion_eq2.
      eapply tequality_preserving_equality; eauto.
      eapply equality_respects_cequivc_left; eauto.
      eapply equality_respects_cequivc_right; eauto.
Qed.

Lemma equal_in_bunion_change2 {o} :
  forall lib (A1 B1 a1 b1 A2 B2 a2 b2 : @CTerm o),
    equal_in_bunion lib A1 B1 a1 b1
    -> tequality lib A1 A2
    -> tequality lib B1 B2
    -> equorsq lib a1 a2 A1
    -> equorsq lib b1 b2 A2
    -> equal_in_bunion lib A2 B2 a2 b2.
Proof.
  introv eb teq1 teq2 o1 o2.
  revert dependent b2.
  revert dependent a2.
  revert dependent B2.
  revert dependent A2.
  induction eb; introv teq1 teq2 o1 o2.
  - apply @eq_in_bunion_cl with (t := t); auto.
    apply IHeb1; auto.
    right; spcast; sp.
    apply IHeb2; auto.
    right; spcast; sp.
  - apply @eq_in_bunion_eq1.
    apply (equality_trans lib a2 t1 b2).
    apply equality_sym.
    eapply tequality_preserving_equality; eauto.
    dorn o1; auto; spcast.
    eapply equality_respects_cequivc_right; eauto.
    allapply @equality_refl; auto.
    apply (equality_trans lib t1 t2 b2).
    eapply tequality_preserving_equality; eauto.
    dorn o2; auto; spcast.
    eapply equality_respects_cequivc_right; eauto.
    eapply tequality_preserving_equality; eauto.
    apply (equality_trans lib t2 t1 t2); auto.
    apply equality_sym; auto.
  - dorn o1; dorn o2; spcast.
    + apply @eq_in_bunion_cl with (t := t1).
      apply @eq_in_bunion_eq1.
      apply equality_sym.
      eapply tequality_preserving_equality; eauto.
      apply @eq_in_bunion_cl with (t := t2).
      apply @eq_in_bunion_eq2.
      eapply tequality_preserving_equality; eauto.
      apply @eq_in_bunion_eq1; auto.
    + apply @eq_in_bunion_cl with (t := t1).
      apply @eq_in_bunion_eq1.
      eapply tequality_preserving_equality; eauto.
      apply equality_sym; auto.
      apply @eq_in_bunion_eq2.
      eapply tequality_preserving_equality; eauto.
      eapply equality_respects_cequivc_right; eauto.
    + apply @eq_in_bunion_cl with (t := t2).
      apply @eq_in_bunion_eq2.
      eapply tequality_preserving_equality; eauto.
      eapply equality_respects_cequivc_left; eauto.
      apply @eq_in_bunion_eq1; auto.
    + apply @eq_in_bunion_eq2.
      eapply tequality_preserving_equality; eauto.
      eapply equality_respects_cequivc_left; eauto.
      eapply equality_respects_cequivc_right; eauto.
Qed.

Definition disjoint_types {o} lib (T U : @CTerm o) :=
  forall t, !(member lib t T # member lib t U).

Lemma equality_in_disjoint_bunion {o} :
  forall lib (a b T U : @CTerm o),
    disjoint_types lib T U
    -> (equality lib a b (mkc_bunion T U)
        <=> (type lib T # type lib U # (equality lib a b T {+} equality lib a b U))).
Proof.
  introv disj.
  rw @equality_in_mkc_bunion.
  split; intro h; repnd.
  - dands; auto.
    induction h; tcsp.
    repndors; eauto 3 with nequality;
    provefalse;
    pose proof (disj t) as k; destruct k; dands; eauto with nequality.
  - dands; auto.
    repndors.
    + apply eq_in_bunion_eq1; auto.
    + apply eq_in_bunion_eq2; auto.
Qed.



(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/")
*** End:
*)
