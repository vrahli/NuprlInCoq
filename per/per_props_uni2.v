(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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



Require Export per_props_util.
Require Export per_props_uni.
Require Export types_converge.


Lemma tequality_converge_left {o} :
  forall lib (t1 t2 : @CTerm o), tequality lib t1 t2 -> chaltsc_bar lib t1.
Proof.
  introv teq.
  apply tequality_refl in teq.
  apply types_converge in teq; auto.
Qed.

Lemma tequality_converge_right {o} :
  forall lib (t1 t2 : @CTerm o), tequality lib t1 t2 -> chaltsc_bar lib t2.
Proof.
  introv teq.
  apply tequality_sym in teq.
  apply tequality_refl in teq.
  apply types_converge in teq; auto.
Qed.

Lemma nuprl_converge_left {o} :
  forall lib (t1 t2 : @CTerm o) eq, nuprl lib t1 t2 eq -> chaltsc_bar lib t1.
Proof.
  introv teq.
  eapply tequality_converge_left; exists eq; eauto.
Qed.

Lemma nuprl_converge_right {o} :
  forall lib (t1 t2 : @CTerm o) eq, nuprl lib t1 t2 eq -> chaltsc_bar lib t2.
Proof.
  introv teq.
  eapply tequality_converge_right; exists eq; eauto.
Qed.


(*(* This is not provable, because in general we can't find the type level
 * of a type family. *)
Lemma equality_in_uni_iff {p} :
  forall lib a b,
    {i : nat , @equality p lib a b (mkc_uni i)}
    <=> tequality lib a b.
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

  - Case "CL_eq".
    dest_imp IHe0 hyp; exrepnd.
    admit.

  - Case "CL_req".
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
Abort.*)

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
    destruct t as [v|op bs]; allsimpl; ginv.
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

Lemma hasvaluec_implies_computes_to_valc {o} :
  forall lib (a : @CTerm o),
    hasvaluec lib a -> {b : CTerm $ computes_to_valc lib a b }.
Proof.
  introv hv; destruct_cterms.
  unfold hasvaluec in *; simpl in *.
  unfold hasvalue in *; exrepnd.
  applydup @computes_to_value_implies_isprogram in hv0.
  exists (mk_cterm t' hv1); unfold computes_to_valc; simpl; auto.
Qed.

Lemma dest_nuprl_uni_diff {o} :
  forall (lib : @library o) i j eq,
    nuprl lib (mkc_uni i) (mkc_uni j) eq
    -> univ lib  (mkc_uni i) (mkc_uni j) eq.
Proof.
  introv cl.
  eapply dest_close_per_uni_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.


Lemma univ_implies_univi_bar_diff {o} :
  forall lib i1 i2 (eq : per(o)),
    univ lib (mkc_uni i1) (mkc_uni i2) eq
    -> i1 = i2 # exists k, i1 < k # univi_bar k lib (mkc_uni i1) (mkc_uni i1) eq.
Proof.
  introv u.
  dands.

  {
    unfold univ, univi_bar, per_bar in *; exrepnd.
    pose proof (bar_non_empty bar) as q; exrepnd.
    assert (lib_extends lib' lib) as ext by eauto 3 with slow.
    pose proof (u0 _ q0 _ (lib_extends_refl lib') ext) as u0; simpl in *.
    unfold univ_ex in u0; exrepnd.
    allrw @univi_exists_iff; exrepnd; spcast.
    computes_to_value_isvalue.
  }

  exists (S i1); dands; try lia.
  unfold univ, univi_bar, per_bar in *; exrepnd.
  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (u0 _ br _ ext x) as u0; simpl in *.
  unfold univ_ex in u0; exrepnd.
  allrw @univi_exists_iff; exrepnd; spcast.
  computes_to_value_isvalue.
  left; dands; spcast; auto; eauto 3 with slow.
Qed.

Lemma univ_implies_univi_bar2_diff {o} :
  forall lib i1 i2 (eq : per(o)),
    univ lib (mkc_uni i1) (mkc_uni i2) eq
    ->
    i1 = i2 #
    exists (bar : BarLib lib) (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq bar eqa))
        # all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (univi_eq (univi_bar i2) lib')).
Proof.
  introv u.
  unfold univ, univi_bar, per_bar in u; exrepnd.

  dands.

  {
    pose proof (bar_non_empty bar) as q; exrepnd.
    assert (lib_extends lib' lib) as ext by eauto 3 with slow.
    pose proof (u0 _ q0 _ (lib_extends_refl lib') ext) as u0; simpl in *.
    unfold univ_ex in u0; exrepnd.
    allrw @univi_exists_iff; exrepnd; spcast.
    computes_to_value_isvalue.
  }

  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (u0 _ br _ ext x) as u0; simpl in *.
  unfold univ_ex in u0; exrepnd.
  allrw @univi_exists_iff; exrepnd; spcast.
  computes_to_value_isvalue.
Qed.

Lemma univ_implies_univi_bar3_diff {o} :
  forall lib i1 i2 (eq : per(o)),
    univ lib (mkc_uni i1) (mkc_uni i2) eq
    ->
    i1 = i2 #
    exists (bar : BarLib lib),
      eq <=2=> (per_bar_eq bar (univi_eq_lib_per lib i1)).
Proof.
  introv u.
  apply univ_implies_univi_bar2_diff in u; exrepnd; subst.
  dands; auto.
  exists bar.
  eapply eq_term_equals_trans;[eauto|].
  apply implies_eq_term_equals_per_bar_eq.
  apply all_in_bar_ext_intersect_bars_same; simpl; auto.
Qed.

Lemma dest_nuprl_tuni_sub_per {o} :
  forall (lib : @library o) a b eq,
    nuprl lib (mkc_tuni a) (mkc_tuni b) eq
    ->
    all_in_ex_bar
      lib
      (fun lib =>
         exists i,
           ccomputes_to_valc lib a (mkc_nat i)
           /\ ccomputes_to_valc lib b (mkc_nat i)
           /\ exists (bar : BarLib lib), sub_per eq (per_bar_eq bar (univi_eq_lib_per lib i))).
Proof.
  introv cl.
  applydup @nuprl_converge_left in cl.
  applydup @nuprl_converge_right in cl.
  eapply all_in_ex_bar_modus_ponens2;[|exact cl0|exact cl1]; clear cl0 cl1; introv x cl0 cl1; exrepnd; spcast.

  apply hasvaluec_implies_computes_to_valc in cl0; exrepnd.
  apply hasvaluec_implies_computes_to_valc in cl1; exrepnd.

  apply nuprl_monotone_func2 in cl; exrepnd.
  pose proof (cl1 _ x) as cl1; repnd.

  eapply nuprl_value_respecting_left in cl3;
    [|apply computes_to_valc_implies_ccequivc_ext;eauto].
  eapply nuprl_value_respecting_right in cl3;
    [|apply computes_to_valc_implies_ccequivc_ext;eauto].

  apply computes_to_valc_tuni_implies in cl2.
  apply computes_to_valc_tuni_implies in cl0.
  exrepnd; subst.
  apply dest_nuprl_uni_diff in cl3.
  apply univ_implies_univi_bar3_diff in cl3; repnd; subst.
  exists k; dands; spcast; auto.
  exrepnd.
  exists bar.
  introv h.
  apply cl4 in h; apply cl5 in h; auto.
Qed.

Lemma tequality_mkc_tuni {o} :
  forall lib (a b : @CTerm o),
    tequality lib (mkc_tuni a) (mkc_tuni b)
    <=> equality_of_nat_bar lib a b.
Proof.
  introv.
  split; intro k.

  - unfold tequality in k; exrepnd.
    apply dest_nuprl_tuni_sub_per in k0.
    eapply all_in_ex_bar_modus_ponens1;[|exact k0]; clear k0; introv x k0; exrepnd; spcast.
    exists i; dands; spcast; auto.

  - apply all_in_ex_bar_tequality_implies_tequality.
    eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k; introv x k; exrepnd; spcast.
    unfold equality_of_nat in k; exrepnd; spcast.
    pose proof (computes_to_valc_tuni lib' a (Z.of_nat n)) as c1.
    pose proof (computes_to_valc_tuni lib' b (Z.of_nat n)) as c2.
    allrw @Znat.Nat2Z.id; fold_terms.
    allrw <- @mkc_nat_eq.
    repeat (autodimp c1 hyp); try lia.
    repeat (autodimp c2 hyp); try lia.
    eapply tequality_respects_cequivc_left;
      [apply ccequivc_ext_sym; apply computes_to_valc_implies_ccequivc_ext;eauto|].
    eapply tequality_respects_cequivc_right;
      [apply ccequivc_ext_sym; apply computes_to_valc_implies_ccequivc_ext;eauto|].
    apply tequality_mkc_uni.
Qed.
