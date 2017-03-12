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

  Authors: Vincent Rahli

 *)


Require Export per_props_uni0.
Require Export per_props_nat.


Lemma computes_to_valc_tuni_implies {o} :
  forall lib (t : @CTerm o) v,
    computes_to_valc lib (mkc_tuni t) v
    -> {k : nat
        & computes_to_valc lib t (mkc_nat k)
        # v = mkc_uni k}.
Proof.
  introv comp.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd.
  unfold reduces_to in comp0; exrepnd.
  rename x0 into t.
  revert dependent t.
  induction k; introv isp r.
  - allrw @reduces_in_atmost_k_steps_0; subst.
    inversion comp; subst; allsimpl; tcsp.
  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf r1; allsimpl.
    destruct t as [v|f|op bs]; allsimpl; ginv.
    dopid op as [can|ncan|exc|abs] Case; allsimpl; ginv.
    + apply compute_step_tuni_success in r1; exrepnd; subst; GC; fold_terms.
      exists n; dands; eauto 3 with slow.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto 3 with slow; subst.
      apply cterm_eq; simpl; auto.
    + remember (compute_step lib (oterm (NCan ncan) bs)) as c; destruct c; allsimpl; ginv.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; eauto 3 with slow.
      apply IHk in r0; clear IHk; eauto 3 with slow; exrepnd.
      inversion r1; subst.
      exists k0; dands; eauto 3 with slow.
      eapply reduces_to_if_split2; eauto.
    + apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto 3 with slow; subst.
      inversion comp; subst; allsimpl; tcsp.
    + remember (compute_step lib (oterm (Abs abs) bs)) as c; destruct c; allsimpl; ginv.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; eauto 3 with slow.
      apply IHk in r0; clear IHk; eauto 3 with slow; exrepnd.
      inversion r1; subst.
      exists k0; dands; eauto 3 with slow.
      eapply reduces_to_if_split2; eauto.
Qed.

Lemma nuprli_mkc_uni_le_false {o} :
  forall lib (k1 k2 : nat) (eq : per(o)),
    nuprli lib k1 (mkc_uni k2) eq
    -> k1 <= k2
    -> False.
Proof.
  induction k1 as [? ind] using comp_ind.

  introv n.
  unfold nuprli in n.
  remember (univi lib k1) as u.
  remember (mkc_uni k2) as T.
  revert Hequ HeqT.
  close_cases (induction n using @close_ind') Case; introv Hequ HeqT lek; subst;
    try (complete (allunfold_per; spcast; computes_to_value_isvalue)).

  Case "CL_init".
  destruct k1; simpl in *; tcsp.
  repndors; repnd; spcast; computes_to_value_isvalue; try omega.

  pose proof (ind k1) as q; autodimp q hyp.
  pose proof (q k2 eq) as h; clear q.
  repeat (autodimp h hyp); try omega.
  apply CL_init; auto.
Qed.

Lemma eq_univi_eq_lt_level_implies_false {o} :
  forall (lib : @library o) k1 k2,
    ((univi_eq lib (univi lib k1)) <=2=> (univi_eq lib (univi lib k2)))
    -> k1 < k2
    -> False.
Proof.
  introv eqiff ltk.

  pose proof (eqiff (mkc_uni (pred k2)) (mkc_uni (pred k2))) as q; clear eqiff.
  destruct q as [q' q]; clear q'.
  autodimp q hyp.

  {
    unfold univi_eq.
    exists (univi_eq lib (univi lib (pred k2))).
    apply extts_nuprli_refl.
    apply CL_init.
    destruct k2; try omega.
    allrw @Nat.pred_succ.
    apply univi_mkc_uni.
  }

  unfold univi_eq in q; exrepnd.

  destruct q0 as [q1 q2]; GC.
  fold (nuprli lib k1) in *.

  destruct k2; try omega; simpl in *.

  assert (k1 <= k2) as lek by omega.
  clear ltk.

  apply nuprli_mkc_uni_le_false in q1; auto.
Qed.

Lemma eq_univi_eq_iff_eq_level {o} :
  forall (lib : @library o) (k1 k2 : nat),
    ((univi_eq lib (univi lib k1)) <=2=> (univi_eq lib (univi lib k2)))
      <=> k1 = k2.
Proof.
  introv; split; intro h; subst; tcsp;[].

  destruct (le_lt_dec k1 k2) as [d|d];
    [apply le_lt_eq_dec in d; destruct d as [d|d];auto|];
    assert False; tcsp.

  - apply eq_univi_eq_lt_level_implies_false in h; auto.

  - apply eq_term_equals_sym in h.
    apply eq_univi_eq_lt_level_implies_false in h; auto.
Qed.

Lemma implies_cequivc_mkc_tuni {o} :
  forall lib (a b : @CTerm o),
    cequivc lib a b
    -> cequivc lib (mkc_tuni a) (mkc_tuni b).
Proof.
  introv ceq.
  destruct_cterms; allunfold @cequivc; allsimpl.
  destruct ceq.
  split; repeat prove_approx; eauto 3 with slow.
Qed.

Lemma tequality_mkc_tuni {o} :
  forall lib (a b : @CTerm o),
    tequality lib (mkc_tuni a) (mkc_tuni b)
    <=> equality_of_nat lib a b.
Proof.
  introv.
  split; intro k.

  - unfold tequality in k; exrepnd.
    destruct k0 as [k1 k2].
    inversion k1; subst; try not_univ;
      try (complete (allunfold_per; computes_to_value_isvalue; allfold (@nuprl o);
                     allapply @computes_to_valc_tuni_implies; exrepnd; ginv;
                     match goal with [ H : _ |- _ ] => complete (eqconstr H) end)).
    inversion k2; subst; try not_univ;
      try (complete (allunfold_per; computes_to_value_isvalue; allfold (@nuprl o);
                     allapply @computes_to_valc_tuni_implies; exrepnd; ginv;
                     match goal with [ H : _ |- _ ] => complete (eqconstr H) end)).

    clear k1 k2.

    duniv j h.
    duniv i q.
    allrw @univi_exists_iff; exrepd; spcast.
    allapply @computes_to_valc_tuni_implies; exrepnd; ginv.
    clear dependent i.
    clear dependent j.

    eapply eq_term_equals_trans in e0;[|apply eq_term_equals_sym;exact e].
    apply eq_univi_eq_iff_eq_level in e0; subst.

    exists k0; dands; spcast; auto.

  - unfold equality_of_nat in k; exrepnd; spcast.
    apply type_respects_cequivc_right;
      [apply implies_cequivc_mkc_tuni;
       eapply cequivc_trans;
       [apply computes_to_valc_implies_cequivc;eauto
       |apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto]
      |].

    clear dependent b.

    pose proof (computes_to_valc_tuni lib a (Z.of_nat k0)) as c.
    allrw @Znat.Nat2Z.id; fold_terms.
    repeat (autodimp c hyp); try omega.

    exists (univi_eq lib (univi lib k0)).
    apply CL_init.
    exists (S k0).
    left.
    dands; spcast; auto.
Qed.
