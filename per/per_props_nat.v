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


  Websites : http://nuprl.org/html/verification/
             http://nuprl.org/html/Nuprl2Coq
             https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.

Require Export alphaeq5.
Require Export cvterm.
Require Export nat_defs.
Require Export cequiv_props4.
Require Export types_converge.

Require Export sequents_tacs.
Require Import cequiv_tacs.
Require Import subst_tacs.

Require Export per_props_set.
Require Export per_props_union.
Require Export per_props3.

Require Export subst_per.

Require Export list.  (* ??? *)


Lemma nuprl_int {p} :
  forall lib, @nuprl p lib mkc_int (equality_of_int lib).
Proof.
  sp.
  apply CL_int.
  unfold per_int; sp; spcast; try computes_to_value_refl.
Qed.
Hint Resolve nuprl_int : slow.

Lemma equality_of_int_xxx {p} :
  forall lib, @close p lib (univ lib) mkc_int (equality_of_int lib).
Proof.
  apply nuprl_int.
Qed.

Lemma nat_in_int {p} : forall lib (n : nat), @member p lib (mkc_nat n) mkc_int.
Proof.
  unfold member, equality; sp.
  exists (@equality_of_int p lib).
  sp;[apply equality_of_int_xxx|].
  exists (Z_of_nat n); sp;
  unfold mkc_nat, mkc_integer, isprog_mk_nat, isprog_mk_integer, mk_nat;
    spcast; computes_to_value_refl.
Qed.


Lemma equality_in_less {o} :
  forall lib (u v a b c d : @CTerm o),
    equality lib u v (mkc_less a b c d)
    <=>
    {ka : Z
     , {kb : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # (
            ((ka < kb)%Z # equality lib u v c)
            {+}
            ((kb <= ka)%Z # equality lib u v d)
          )}}.
Proof.
  introv.

  split; intro k; exrepnd.

  - applydup @inhabited_implies_tequality in k.
    apply types_converge in k0.
    spcast.
    apply hasvaluec_mkc_less in k0.
    exrepnd.

    exists k1 k0; dands; spcast; eauto with slow;
    try (complete (apply computes_to_valc_iff_reduces_toc; dands; eauto with slow)).

    assert (cequivc lib
                    (mkc_less a b c d)
                    (mkc_less (mkc_integer k1) (mkc_integer k0) c d)) as c1.
    { apply reduces_toc_implies_cequivc.
      destruct_cterms; allunfold @reduces_toc; allunfold @computes_to_valc; allsimpl.
      apply reduce_to_prinargs_comp; eauto with slow.
      allunfold @computes_to_value; sp; eauto with slow. }

    repndors; repnd.

    + left; dands; auto.

      assert (cequivc lib
                      (mkc_less (mkc_integer k1) (mkc_integer k0) c d)
                      c) as c2.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      rwg c2.
      rwg c1; auto.

    + right; dands; auto.

      assert (cequivc lib
                      (mkc_less (mkc_integer k1) (mkc_integer k0) c d)
                      d) as c2.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      rwg c2.
      rwg c1; auto.

  - spcast.
    assert (cequivc lib
                    (mkc_less a b c d)
                    (mkc_less (mkc_integer ka) (mkc_integer kb) c d)) as c1.
    { apply reduces_toc_implies_cequivc.
      destruct_cterms; allunfold @reduces_toc; allunfold @computes_to_valc; allsimpl.
      apply reduce_to_prinargs_comp; eauto with slow. }

    rwg c1.

    repndors; repnd.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      c) as c2.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c2; auto.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      d) as c2.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c2; auto.
Qed.

Lemma equality_in_less_than {o} :
  forall lib (u v a b : @CTerm o),
    equality lib u v (mkc_less_than a b)
    <=>
    {ka : Z
     , {kb : Z
        , u ===>(lib) mkc_axiom
        # v ===>(lib) mkc_axiom
        # a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # (ka < kb)%Z}}.
Proof.
  introv.
  rw @mkc_less_than_eq.
  rw @equality_in_less.
  split; intro k; exrepnd; spcast.
  - repndors; repnd.
    + apply equality_in_true in k1; repnd; spcast.
      exists ka kb; dands; spcast; auto.
    + apply equality_in_false in k1; sp.
  - exists ka kb; dands; spcast; auto.
    left; dands; auto.
    apply equality_in_true; dands; spcast; auto.
Qed.

Lemma inhabited_less_than {o} :
  forall lib (a b : @CTerm o),
    inhabited_type lib (mkc_less_than a b)
    <=>
    {ka : Z
     , {kb : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # (ka < kb)%Z}}.
Proof.
  introv.
  unfold inhabited_type; split; intro k; exrepnd; spcast.
  - rw @equality_in_less_than in k0; exrepnd; spcast.
    exists ka kb; dands; spcast; auto.
  - exists (@mkc_axiom o).
    apply equality_in_less_than.
    exists ka kb; dands; spcast; auto;
    apply computes_to_valc_refl; eauto with slow.
Qed.

Lemma type_mkc_true {o} :
  forall (lib : @library o), type lib mkc_true.
Proof.
  introv; rw @mkc_true_eq.
  apply tequality_mkc_approx; sp.
Qed.

Lemma equality_in_le {o} :
  forall lib (u v a b : @CTerm o),
    equality lib u v (mkc_le a b)
    <=>
    {ka : Z
     , {kb : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # (ka <= kb)%Z}}.
Proof.
  introv.
  rw @mkc_le_eq.
  rw @equality_in_not.
  rw @tequality_mkc_less_than.
  rw @inhabited_less_than.
  split; intro k; exrepnd; spcast; dands.
  - repeat computes_to_eqval.
    exists kb ka; dands; spcast; auto.
    repndors; repnd; tcsp.
    destruct k.
    exists ka kb; dands; spcast; auto.
  - exists kb ka kb ka; dands; spcast; auto.
  - intro h; exrepnd; spcast.
    repeat computes_to_eqval.
    omega.
Qed.

Lemma inhabited_le {o} :
  forall lib (a b : @CTerm o),
    inhabited_type lib (mkc_le a b)
    <=>
    {ka : Z
     , {kb : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # (ka <= kb)%Z}}.
Proof.
  introv.
  unfold inhabited_type; split; intro k; exrepnd; spcast.
  - apply equality_in_le in k0; exrepnd; spcast.
    exists ka kb; dands; spcast; auto.
  - exists (@mkc_axiom o).
    apply equality_in_le.
    exists ka kb; dands; spcast; auto.
Qed.

Lemma tequality_mkc_natk {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib (mkc_natk t1) (mkc_natk t2)
    <=> {k1 : Z , {k2 : Z
         , t1 ===>(lib) (mkc_integer k1)
         # t2 ===>(lib) (mkc_integer k2)
         # (forall (k : Z), (0 <= k)%Z -> ((k < k1)%Z # (k < k2)%Z){+}(k1 <= k)%Z # (k2 <= k)%Z) }}.
Proof.
  introv.
  allrw @mkc_natk_eq.
  allrw @tequality_set.

  split; intro k; repnd.

  - clear k0.

    assert (forall a a' : CTerm,
              equality lib a a' mkc_int
              -> tequality
                   lib
                   (mkc_prod (mkc_le mkc_zero a) (mkc_less_than a t1))
                   (mkc_prod (mkc_le mkc_zero a') (mkc_less_than a' t2))) as h1.
    { introv ei.
      applydup k in ei.
      eapply tequality_respects_alphaeqc_left in ei0;[|apply mkcv_prod_substc].
      eapply tequality_respects_alphaeqc_right in ei0;[|apply mkcv_prod_substc].
      allrw @mkcv_le_substc2.
      allrw @mkcv_zero_substc.
      allrw @mkcv_less_than_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      auto. }
    clear k.

    assert (forall (k : Z),
              (0 <= k)%Z
              -> {k1 : Z , {k2 : Z
                  , t1 ===>(lib) (mkc_integer k1)
                  # t2 ===>(lib) (mkc_integer k2)
                  # ((k < k1)%Z # (k < k2)%Z){+}(k1 <= k)%Z # (k2 <= k)%Z }}) as h2.
    { introv le0k.
      pose proof (h1 (mkc_integer k) (mkc_integer k)) as h.
      autodimp h hyp.
      { apply equality_in_int; unfold equality_of_int; exists k; dands; spcast; auto;
        apply computes_to_valc_refl; eauto with slow. }
      allrw @tequality_mkc_prod; repnd.
      allrw @inhabited_le.
      allrw @tequality_mkc_less_than.
      clear h0 (* trivial *).
      autodimp h hyp.
      { exists 0%Z k; dands; auto; spcast; tcsp; allrw @mkc_zero_eq; allrw @mkc_nat_eq;
        allsimpl; apply computes_to_valc_refl; eauto with slow. }
      exrepnd; spcast.
      apply computes_to_valc_isvalue_eq in h0; eauto with slow; ginv.
      apply computes_to_valc_isvalue_eq in h4; eauto with slow; ginv.
      exists kb kd; dands; spcast; auto. }
    clear h1.

    pose proof (h2 0%Z) as h; autodimp h hyp; tcsp; exrepnd; spcast.
    exists k1 k2; dands; spcast; tcsp.
    introv i.
    apply h2 in i; exrepnd; spcast.
    repeat computes_to_eqval; auto.

  - dands.
    { apply tequality_int. }
    introv ei.
    exrepnd; spcast.

    apply equality_in_int in ei.
    apply equality_of_int_imp_tt in ei.
    unfold equality_of_int_tt in ei; exrepnd.

    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    allrw @mkcv_le_substc2.
    allrw @mkcv_less_than_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_zero_substc.
    allrw @csubst_mk_cv.

    apply tequality_mkc_prod; dands.
    { apply tequality_mkc_le.
      exists 0%Z k 0%Z k.
      dands; tcsp; spcast; auto;
      try (rw @mkc_zero_eq; rw @mkc_nat_eq; simpl;
           apply computes_to_valc_refl; eauto with slow).
      destruct (Z_lt_le_dec k 0); tcsp. }

    introv inh.
    allrw @inhabited_le; exrepnd; spcast.
    apply computes_to_valc_isvalue_eq in inh0; eauto with slow.
    rw @mkc_zero_eq in inh0; rw @mkc_nat_eq in inh0; ginv.
    computes_to_eqval.
    apply tequality_mkc_less_than.
    exists k k1 k k2; dands; spcast; tcsp.
Qed.

Lemma type_mkc_natk {o} :
  forall lib (t : @CTerm o),
    type lib (mkc_natk t)
    <=> {k : Z , t ===>(lib) (mkc_integer k)}.
Proof.
  introv.
  rw @tequality_mkc_natk; split; introv h; exrepnd; spcast; repeat computes_to_eqval.
  - exists k1; spcast; auto.
  - exists k k; dands; spcast; auto.
    introv i.
    destruct (Z_lt_le_dec k0 k); tcsp.
Qed.

Lemma type_mkc_le {o} :
  forall lib (a b : @CTerm o),
  type lib (mkc_le a b) <=>
       (exists ka kb
        , (a) ===>( lib)(mkc_integer ka)
        # (b) ===>( lib)(mkc_integer kb)).
Proof.
  introv.
  rw @tequality_mkc_le; split; intro h; exrepnd; spcast; repeat computes_to_eqval.
  - exists ka kb; dands; spcast; auto.
  - exists ka kb ka kb; dands; spcast; auto.
    destruct (Z_lt_le_dec kb ka); tcsp.
Qed.

Lemma type_mkc_less_than {o} :
  forall lib (a b : @CTerm o),
    type lib (mkc_less_than a b) <=>
         (exists ka kb
          , (a) ===>( lib)(mkc_integer ka)
          # (b) ===>( lib)(mkc_integer kb)).
Proof.
  introv.
  rw @tequality_mkc_less_than; split; intro h; exrepnd; spcast; repeat computes_to_eqval.
  - exists ka kb; dands; spcast; auto.
  - exists ka kb ka kb; dands; spcast; auto.
    destruct (Z_lt_le_dec ka kb); tcsp.
Qed.

Lemma inhabited_prod {p} :
  forall lib (A B : @CTerm p),
    inhabited_type lib (mkc_prod A B)
    <=>
    (type lib A
     # type lib B
     # inhabited_type lib A
     # inhabited_type lib B).
Proof.
  introv.
  unfold inhabited_type; split; intro k; exrepnd.

  - apply equality_in_prod in k0; exrepnd; spcast.
    autodimp k2 hyp.
    { allapply @inhabited_type_if_equality; auto. }
    allapply @equality_refl.
    dands; auto; eexists; eauto.

  - exists (mkc_pair t0 t).
    apply equality_in_prod; dands; auto.
    exists t0 t0 t t; dands; spcast; tcsp;
    apply computes_to_valc_refl; eauto with slow.
Qed.

Lemma inhabited_prod2 {p} :
  forall lib (A B : @CTerm p),
    inhabited_type lib (mkc_prod A B)
    <=>
    (type lib A
     # inhabited_type lib A
     # type lib B
     # inhabited_type lib B).
Proof.
  introv.
  rw @inhabited_prod; split; sp.
Qed.

Lemma equality_in_natk {o} :
  forall lib (a b t : @CTerm o),
    equality lib a b (mkc_natk t)
    <=> {m : nat , {k : Z
         , a ===>(lib) (mkc_nat m)
         # b ===>(lib) (mkc_nat m)
         # t ===>(lib) (mkc_integer k)
         # (Z.of_nat m < k)%Z }} .
Proof.
  introv.
  rw @mkc_natk_eq.
  rw @equality_in_set.

  split; intro h; exrepnd; dands.

  - allrw @equality_in_int.
    unfold equality_of_int in h1; exrepnd; spcast.
    eapply inhabited_type_respects_alphaeqc in h;[|apply mkcv_prod_substc].
    allrw @mkcv_le_substc2.
    allrw @mkcv_less_than_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_zero_substc.
    allrw @csubst_mk_cv.
    allrw @inhabited_prod; repnd.
    allrw @inhabited_le; exrepnd; spcast.
    apply computes_to_valc_isvalue_eq in h6; eauto with slow.
    rw @mkc_zero_eq in h6; rw @mkc_nat_eq in h6; ginv.
    computes_to_eqval.
    allrw @inhabited_less_than; exrepnd; spcast.
    computes_to_eqval.
    exists (Z.to_nat k) kb; dands; spcast; tcsp;
    try (complete (rw @mkc_nat_eq; rw Znat.Z2Nat.id; auto)).
    rw Znat.Z2Nat.id; auto.

  - introv ei.
    allrw @equality_in_int.
    unfold equality_of_int in ei; exrepnd; spcast.
    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    allrw @mkcv_le_substc2.
    allrw @mkcv_less_than_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_zero_substc.
    allrw @csubst_mk_cv.
    allrw @tequality_mkc_prod; dands.

    + allrw @tequality_mkc_le.
      exists 0%Z k0 0%Z k0.
      dands; tcsp; spcast; auto;
      try (rw @mkc_zero_eq; rw @mkc_nat_eq; simpl;
           apply computes_to_valc_refl; eauto with slow).
      destruct (Z_lt_le_dec k0 0); tcsp.

    + introv inh.
      allrw @inhabited_le; exrepnd; spcast.
      computes_to_eqval.
      apply computes_to_valc_isvalue_eq in inh0; eauto with slow.
      rw @mkc_zero_eq in inh0; rw @mkc_nat_eq in inh0; ginv.
      apply tequality_mkc_less_than.
      exists k0 k k0 k; dands; spcast; auto.
      destruct (Z_lt_le_dec k0 k); tcsp.

  - spcast.
    apply equality_in_int; unfold equality_of_int.
    exists (Z.of_nat m); dands; spcast; auto.

  - spcast.
    eapply inhabited_type_respects_alphaeqc;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    allrw @mkcv_le_substc2.
    allrw @mkcv_less_than_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_zero_substc.
    allrw @csubst_mk_cv.
    apply inhabited_prod.
    allrw @type_mkc_le.
    allrw @type_mkc_less_than.
    allrw @inhabited_le.
    allrw @inhabited_less_than.
    dands.

    + exists 0%Z (Z.of_nat m); dands; spcast.
      * rw @mkc_zero_eq; rw @mkc_nat_eq; simpl; apply computes_to_valc_refl; eauto with slow.
      * allrw @mkc_nat_eq; auto.

    + exists (Z.of_nat m) k; dands; spcast; auto.

    + exists 0%Z (Z.of_nat m); dands; spcast; tcsp; try omega.
      rw @mkc_zero_eq; rw @mkc_nat_eq; simpl; apply computes_to_valc_refl; eauto with slow.

    + exists (Z.of_nat m) k; dands; spcast; auto.
Qed.

Lemma cequivc_mkc_isl {o} :
  forall lib (t u : @CTerm o),
    cequivc lib t u
    -> cequivc lib (mkc_isl t) (mkc_isl u).
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  unfold mk_isl, mk_ite.
  apply cequiv_congruence; fold_terms.
  - unfold cequiv_bts, lblift; simpl; dands; auto.
    introv k.
    repeat (destruct n; tcsp; try omega); clear k; unfold selectbt; simpl;
    try (fold (bcequiv lib)); eauto with slow.
    + apply bcequiv_nobnd; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
Qed.

Lemma cequivc_mkc_assert {o} :
  forall lib (t u : @CTerm o),
    cequivc lib t u
    -> cequivc lib (mkc_assert t) (mkc_assert u).
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  unfold mk_assert, mk_ite.
  apply cequiv_congruence; fold_terms.
  - unfold cequiv_bts, lblift; simpl; dands; auto.
    introv k.
    repeat (destruct n; tcsp; try omega); clear k; unfold selectbt; simpl;
    try (fold (bcequiv lib)); eauto with slow.
    + apply bcequiv_nobnd; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
Qed.

Lemma computes_to_valc_inl_implies_cequivc_isl_tt {o} :
  forall lib (t u : @CTerm o),
    computes_to_valc lib t (mkc_inl u)
    -> cequivc lib (mkc_isl t) tt.
Proof.
  introv comp.
  eapply cequivc_trans;
    [apply cequivc_mkc_isl;
      apply computes_to_valc_implies_cequivc;
      exact comp|].
  apply computes_to_valc_implies_cequivc; clear comp t.
  destruct_cterms.
  unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
Qed.

Lemma computes_to_valc_inr_implies_cequivc_isl_ff {o} :
  forall lib (t u : @CTerm o),
    computes_to_valc lib t (mkc_inr u)
    -> cequivc lib (mkc_isl t) ff.
Proof.
  introv comp.
  eapply cequivc_trans;
    [apply cequivc_mkc_isl;
      apply computes_to_valc_implies_cequivc;
      exact comp|].
  apply computes_to_valc_implies_cequivc; clear comp t.
  destruct_cterms.
  unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
Qed.

Lemma implies_isl_in_bool {o} :
  forall lib (A B a b : @CTerm o),
    equality lib a b (mkc_union A B)
    -> equality lib (mkc_isl a) (mkc_isl b) mkc_bool.
Proof.
  introv e.
  apply equality_mkc_union in e; exrepnd.
  apply equality_in_bool.
  repndors; exrepnd; spcast;[left|right]; dands; spcast.
  - eapply computes_to_valc_inl_implies_cequivc_isl_tt; eauto.
  - eapply computes_to_valc_inl_implies_cequivc_isl_tt; eauto.
  - eapply computes_to_valc_inr_implies_cequivc_isl_ff; eauto.
  - eapply computes_to_valc_inr_implies_cequivc_isl_ff; eauto.
Qed.

Lemma tt_not_approx_ff {o} :
  forall (lib : @library o), !approx lib mk_btrue mk_bfalse.
Proof.
  introv apr.
  inversion apr as [cl]; clear apr.
  unfold close_comput in cl; repnd.
  unfold close_compute_val in cl2.
  pose proof (cl2 (NInj NInl) [nobnd mk_axiom]) as h; fold_terms.
  autodimp h hyp; eauto 3 with slow.
  exrepnd.
  apply computes_to_value_isvalue_eq in h1; ginv; eauto 3 with slow.
Qed.

Lemma tt_not_cequiv_ff {o} :
  forall (lib : @library o), !cequiv lib mk_btrue mk_bfalse.
Proof.
  introv ceq.
  apply cequiv_le_approx in ceq.
  apply tt_not_approx_ff in ceq; sp.
Qed.

Lemma tt_not_cequivc_ff {o} :
  forall (lib : @library o), !cequivc lib tt ff.
Proof.
  introv.
  unfold cequivc; simpl.
  apply tt_not_cequiv_ff.
Qed.

Lemma equality_tt_in_bool_implies_cequiv {o} :
  forall lib (t : @CTerm o),
    equality lib t tt mkc_bool
    -> ccequivc lib t tt.
Proof.
  introv e.
  apply equality_in_bool in e; repndors; repnd; spcast; eauto with slow.
  apply tt_not_cequivc_ff in e; sp.
Qed.

Lemma isprogram_mk_assert {o} :
  forall (t : @NTerm o),
    isprogram (mk_assert t) <=> isprogram t.
Proof.
  introv.
  unfold mk_assert.
  rw @isprogram_decide_iff2; split; intro k; repnd; tcsp; dands; auto;
  apply isprog_vars_isprogrambt;
  apply isprog_vars_if_isprog; eauto 3 with slow.
Qed.

Lemma mkc_assert_tt {o} :
  forall (lib : @library o), cequivc lib (mkc_assert tt) mkc_unit.
Proof.
  introv.
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_mk_assert.
  apply isprogram_inl; eauto with slow.
Qed.

Lemma inhabited_type_mkc_unit {o} :
  forall (lib : @library o), inhabited_type lib mkc_unit.
Proof.
  introv.
  unfold inhabited_type.
  exists (@mkc_axiom o).
  apply equality_in_unit; dands; spcast;
  apply computes_to_valc_refl; eauto with slow.
Qed.
Hint Resolve inhabited_type_mkc_unit : slow.

Lemma equality_mkc_inl_implies {o} :
  forall lib (t1 t2 A B : @CTerm o),
    equality lib (mkc_inl t1) (mkc_inl t2) (mkc_union A B)
    -> equality lib t1 t2 A.
Proof.
  introv e.
  apply equality_mkc_union in e; repnd.
  repndors; exrepnd; spcast;
  apply computes_to_valc_isvalue_eq in e2; eauto 3 with slow;
  apply computes_to_valc_isvalue_eq in e4; eauto 3 with slow;
  eqconstr e2; eqconstr e4; auto.
Qed.

Lemma type_tnat {o} :
  forall (lib : @library o), type lib mkc_tnat.
Proof.
  introv.
  rw @mkc_tnat_eq.
  apply tequality_set; dands; auto.
  { apply tequality_int. }

  introv e.
  allrw @substc_mkcv_le.
  allrw @substc_mkcv_zero.
  allrw @mkc_var_substc.
  apply equality_in_int in e.
  unfold equality_of_int in e; exrepnd; spcast.

  apply tequality_mkc_le.
  exists (0%Z) k (0%Z) k; dands; spcast; tcsp.

  - unfold computes_to_valc; simpl.
    unfold computes_to_value; dands; eauto with slow.

  - unfold computes_to_valc; simpl.
    unfold computes_to_value; dands; eauto with slow.

  - destruct (Z_le_gt_dec 0 k); tcsp.
    right; dands; omega.
Qed.
Hint Resolve type_tnat : slow.

Definition equality_of_nat {p} lib (n m : @CTerm p) :=
  {k : nat , n ===>(lib) (mkc_nat k)
           # m ===>(lib) (mkc_nat k)}.

Lemma equality_in_tnat {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_tnat
    <=> equality_of_nat lib a b.
Proof.
  introv.
  rw @mkc_tnat_eq.
  rw @equality_in_set.
  rw @equality_in_int.
  unfold equality_of_int, equality_of_nat.
  rw @substc_mkcv_le.
  rw @substc_mkcv_zero.
  rw @mkc_var_substc.
  rw @inhabited_le.
  split; introv k; exrepnd; spcast; dands;
  repeat computes_to_eqval;
  computes_to_value_isvalue; ginv.
  - inversion k2; subst.
    apply Wf_Z.Z_of_nat_complete in k3; exrepnd; subst.
    exists n; dands; spcast; auto.
  - introv e.
    allrw @substc_mkcv_le.
    allrw @substc_mkcv_zero.
    allrw @mkc_var_substc.
    apply equality_in_int in e.
    unfold equality_of_int in e; exrepnd; spcast.
    apply tequality_mkc_le.
    exists (0%Z) k (0%Z) k; dands; spcast; auto;
    try (complete (unfold computes_to_valc; simpl;
                   unfold computes_to_value; dands;
                   eauto with slow)).
    destruct (Z_le_gt_dec 0 k); sp.
    right; sp; omega.
  - exists (Z.of_nat k0); dands; spcast; auto.
  - exists (0%Z) (Z.of_nat k0); dands; spcast; auto;
    try omega;
    try (complete (unfold computes_to_valc; simpl;
                   unfold computes_to_value; dands;
                   eauto with slow)).
Qed.

Lemma equality_in_int_and_inhabited_le_implies_equality_in_nat {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_int
    -> inhabited_type lib (mkc_le mkc_zero a)
    -> equality lib a b mkc_tnat.
Proof.
  introv e inh.
  apply equality_in_tnat.
  apply equality_in_int in e.
  apply inhabited_le in inh.
  unfold equality_of_nat.
  unfold equality_of_int in e.
  exrepnd; spcast.
  repeat computes_to_eqval.
  computes_to_value_isvalue; ginv.
  inversion inh0; subst.
  apply Wf_Z.Z_of_nat_complete in inh1; exrepnd; subst.
  exists n; dands; spcast; auto.
Qed.

Lemma equality_of_nat_implies_equality_of_int {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat lib t1 t2
    -> equality_of_int lib t1 t2.
Proof.
  introv e.
  unfold equality_of_nat in e; exrepnd; spcast.
  unfold equality_of_int.
  allrw @mkc_nat_eq.
  exists (Z.of_nat k); dands; spcast; auto.
Qed.

Lemma equality_in_int_implies_cequiv {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_int
    -> cequivc lib a b.
Proof.
  introv e.
  apply equality_in_int in e.
  apply equality_of_int_imp_tt in e.
  unfold equality_of_int_tt in e; exrepnd.
  destruct_cterms; allunfold @computes_to_valc; allunfold @cequivc; allsimpl.
  allunfold @computes_to_value; repnd.
  apply (cequiv_trans _ _ (mk_integer k)).
  - apply reduces_to_implies_cequiv; auto.
    apply isprogram_eq; auto.
  - apply cequiv_sym.
    apply reduces_to_implies_cequiv; auto.
    apply isprogram_eq; auto.
Qed.

Lemma member_product2 {o} :
  forall lib (p : @CTerm o) A v B,
    member lib p (mkc_product A v B)
    <=>
    (type lib (mkc_product A v B)
     # {a, b : CTerm
        , p ===>(lib) (mkc_pair a b)
        # member lib a A
        # member lib b (substc a v B)}).
Proof.
  introv.
  rw @equality_in_product; split; intro k; exrepnd.
  - dands; auto.
    + apply tequality_product; auto.
    + allapply @equality_refl.
      exists a1 b1; dands; auto.
  - apply @tequality_product in k0; repnd.
    dands; auto.
    exists a a b b; dands; auto.
Qed.

Lemma equality_in_ufun {p} :
  forall lib (f g A B : @CTerm p),
    equality lib f g (mkc_ufun A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # (inhabited_type lib A -> equality lib f g B)).
Proof.
  introv.
  rw <- @fold_mkc_ufun.
  rw @equality_in_isect.
  split; intro k; repnd; dands; auto.

  - introv i.
    unfold inhabited_type in i; exrepnd.
    generalize (k1 t t); intro j; autodimp j hyp.
    repeat (rw @csubst_mk_cv in j); sp.

  - introv e.
    unfold inhabited_type in e; exrepnd.
    unfold member in e0.
    apply k in e0.
    repeat (rw @csubst_mk_cv in e0); sp.

  - introv e.
    repeat (rw @csubst_mk_cv); sp.
    autodimp k1 hyp.
    exists a; apply equality_refl in e; auto.

  - introv e.
    repeat (rw @csubst_mk_cv); sp.
    apply k.
    exists a; apply equality_refl in e; auto.
Qed.
