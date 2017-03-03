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

  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export per_props_image.


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

Hint Resolve equality_refl : slow.
Hint Rewrite @csubst_mk_cv : slow.

Lemma equal_in_image_squash_fun_iff_inhabited_type {o} :
  forall lib (T : @CTerm o) a b,
    type lib T
    -> (equal_in_image lib T (mkc_lam nvarx (mk_cv [nvarx] mkc_axiom)) a b
        <=> (inhabited_type lib T # ccequivc lib a mkc_axiom # ccequivc lib b mkc_axiom)).
Proof.
  introv ty; split; intro h; repnd.

  - induction h; auto; spcast; repnd; dands; auto.
    { exists a1; eauto 2 with slow. }
    { match goal with
      | [ H1 : cequivc _ _ _, H2 : cequivc _ _ _ |- _ ] => rename H1 into ceq1; rename H2 into ceq2
      end.
      apply cequivc_sym in ceq1.
      eapply cequivc_trans in ceq1;[|apply cequivc_sym;apply cequivc_beta].
      autorewrite with slow in *.
      spcast; apply cequivc_sym; auto. }
    { match goal with
      | [ H1 : cequivc _ _ _, H2 : cequivc _ _ _ |- _ ] => rename H1 into ceq1; rename H2 into ceq2
      end.
      apply cequivc_sym in ceq2.
      eapply cequivc_trans in ceq2;[|apply cequivc_sym;apply cequivc_beta].
      autorewrite with slow in *.
      spcast; apply cequivc_sym; auto. }

  - spcast.
    unfold inhabited_type in h0; exrepnd.
    eapply eq_in_image_eq; try (exact h2); spcast.
    + eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_beta].
      autorewrite with slow; auto.
    + eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_beta].
      autorewrite with slow; auto.
Qed.

Lemma equal_in_image_squash_fun_iff_inhabited_type_ax {o} :
  forall lib (T : @CTerm o),
    type lib T
    -> (equal_in_image lib T (mkc_lam nvarx (mk_cv [nvarx] mkc_axiom)) mkc_axiom mkc_axiom
        <=> inhabited_type lib T).
Proof.
  introv ty.
  split; intro h.
  - apply equal_in_image_squash_fun_iff_inhabited_type in h; tcsp.
  - apply equal_in_image_squash_fun_iff_inhabited_type; dands; spcast; auto.
Qed.

Lemma tequality_mkc_squash {o} :
  forall lib (T1 T2 : @CTerm o),
    tequality lib (mkc_squash T1) (mkc_squash T2)
    <=>
    (
      type lib T1
      # type lib T2
      # (inhabited_type lib T1 <=> inhabited_type lib T2)
    ).
Proof.
  introv.
  rw @tequality_mkc_image; split; intro h; repnd; dands; auto.

  - pose proof (h (@mkc_axiom o) (@mkc_axiom o)) as q; clear h.
    split; intro h; apply equal_in_image_squash_fun_iff_inhabited_type_ax; auto;
      apply q; apply equal_in_image_squash_fun_iff_inhabited_type_ax; auto.

  - introv; split; intro q; apply equal_in_image_squash_fun_iff_inhabited_type in q; auto;
      apply equal_in_image_squash_fun_iff_inhabited_type; repnd; dands; auto; apply h; auto.
Qed.

Lemma type_mkc_squash {o} :
  forall lib (T : @CTerm o),
    type lib (mkc_squash T)
    <=>
    type lib T.
Proof.
  introv.
  rw <- @fold_type.
  rw @tequality_mkc_squash; split; intro h; repnd; dands; auto.
Qed.

Hint Resolve inhabited_type_tequality : slow.

Lemma implies_tequality_equality_mkc_squash {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib t1 t2
    -> inhabited_type lib t1
    -> (tequality lib (mkc_squash t1) (mkc_squash t2)
        # equality lib mkc_axiom mkc_axiom (mkc_squash t1)).
Proof.
  introv teq inh.
  rw @equality_in_mkc_squash.
  rw @tequality_mkc_squash.
  dands; auto; spcast; eauto 2 with slow;
    try (apply computes_to_valc_refl; eauto 3 with slow).
  split; intro h; auto; eauto 2 with slow.
Qed.

Lemma implies_tequality_equality_mkc_squash_and {o} :
  forall lib (t1 t2 : @CTerm o),
    (tequality lib t1 t2 # inhabited_type lib t1)
    -> (tequality lib (mkc_squash t1) (mkc_squash t2)
        # equality lib mkc_axiom mkc_axiom (mkc_squash t1)).
Proof.
  introv h.
  apply implies_tequality_equality_mkc_squash; sp.
Qed.

Lemma equality_in_mkc_squash_ax {o} :
  forall lib (t : @CTerm o),
    equality lib mkc_axiom mkc_axiom (mkc_squash t)
    <=> inhabited_type lib t.
Proof.
  introv.
  rw @equality_in_mkc_squash; split; intro h; repnd; dands; auto; spcast;
    apply computes_to_valc_refl; eauto 3 with slow.
Qed.
