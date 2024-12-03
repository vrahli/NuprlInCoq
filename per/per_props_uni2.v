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



Require Export per_props_tacs.
Require Export per_props_util.
Require Export per_props_uni.
Require Export types_converge.


Lemma tequality_converge_left {o} :
  forall uk lib (t1 t2 : @CTerm o), tequality uk lib t1 t2 -> chaltsc_bar lib t1.
Proof.
  introv teq.
  apply tequality_refl in teq.
  apply types_converge in teq; auto.
Qed.

Lemma tequality_converge_right {o} :
  forall uk lib (t1 t2 : @CTerm o), tequality uk lib t1 t2 -> chaltsc_bar lib t2.
Proof.
  introv teq.
  apply tequality_sym in teq.
  apply tequality_refl in teq.
  apply types_converge in teq; auto.
Qed.

Lemma nuprl_converge_left {o} :
  forall uk lib (t1 t2 : @CTerm o) eq, nuprl uk lib t1 t2 eq -> chaltsc_bar lib t1.
Proof.
  introv teq.
  eapply tequality_converge_left; exists eq; eauto.
Qed.

Lemma nuprl_converge_right {o} :
  forall uk lib (t1 t2 : @CTerm o) eq, nuprl uk lib t1 t2 eq -> chaltsc_bar lib t2.
Proof.
  introv teq.
  eapply tequality_converge_right; exists eq; eauto.
Qed.


(*(* This is not provable, because in general we can't find the type level
 * of a type family. *)
Lemma equality_in_uni_iff {p} :
  forall lib a b,
    {i : nat , @equality p lib a b (mkc_uni i)}
    <=> tequality uk lib a b.
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
        # v = mkc_uni 0 k}.
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
  forall uk (lib : @library o) i j eq,
    nuprl uk lib (mkc_uni uk i) (mkc_uni uk j) eq
    -> univ uk lib  (mkc_uni uk i) (mkc_uni uk j) eq.
Proof.
  introv cl.
  eapply dest_close_per_uni_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.


Lemma univ_implies_univi_bar_diff {o} :
  forall uk lib i1 i2 (eq : per(o)),
    univ uk lib (mkc_uni uk i1) (mkc_uni uk i2) eq
    -> i1 = i2 # exists k, i1 < k # univi_bar k uk lib (mkc_uni uk i1) (mkc_uni uk i1) eq.
Proof.
  introv u.
  dands.

  {
    unfold univ, univi_bar, per_bar in *; exrepnd.
    apply (in_open_bar_ext_const lib).
    eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
    unfold univ_ex in u1; exrepnd.
    allrw @univi_exists_iff; exrepnd; spcast.
    repeat ccomputes_to_valc_ext_val; auto.
  }

  exists (S i1); dands; try lia.
  unfold univ, univi_bar, per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
  unfold univ_ex in u1; exrepnd.
  allrw @univi_exists_iff; exrepnd; spcast.
  repeat ccomputes_to_valc_ext_val; auto.
  exists j; dands; eauto 3 with slow.
Qed.

Lemma univ_implies_univi_bar2_diff {o} :
  forall uk lib i1 i2 (eq : per(o)),
    univ uk lib (mkc_uni uk i1) (mkc_uni uk i2) eq
    ->
    i1 = i2 #
    exists (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq lib eqa))
        # in_open_bar_ext lib (fun lib' x => (eqa lib' x) <=2=> (univi_eq (univi_bar i2) uk lib')).
Proof.
  introv u.
  unfold univ, univi_bar, per_bar in u; exrepnd.

  dands.

  {
    apply (in_open_bar_ext_const lib).
    eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
    unfold univ_ex in u1; exrepnd.
    allrw @univi_exists_iff; exrepnd; spcast.
    repeat ccomputes_to_valc_ext_val; auto.
  }

  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
  unfold univ_ex in u1; exrepnd.
  allrw @univi_exists_iff; exrepnd; spcast.
  repeat ccomputes_to_valc_ext_val; auto.
 Qed.

Lemma univ_implies_univi_bar3_diff {o} :
  forall uk lib i1 i2 (eq : per(o)),
    univ uk lib (mkc_uni uk i1) (mkc_uni uk i2) eq
    ->
    i1 = i2 # eq <=2=> (per_bar_eq lib (univi_eq_lib_per uk lib i1)).
Proof.
  introv u.
  apply univ_implies_univi_bar2_diff in u; exrepnd; subst.
  dands; auto.
  eapply eq_term_equals_trans;[eauto|].
  apply implies_eq_term_equals_per_bar_eq; auto.
Qed.


Lemma implies_cequivc_tuni {o} :
  forall lib (a b : @CTerm o),
    cequivc lib a b
    -> cequivc lib (mkc_tuni a) (mkc_tuni b).
Proof.
  unfold cequivc; introv ceq; destruct_cterms; simpl in *.
  repnud ceq.
  split; apply approx_congruence; fold_terms;
    try (apply isprogram_tuni; apply isprog_implies; auto).

  { unfold lblift; simpl; dands; auto; introv w.
    repeat (destruct n; try lia); unfold selectbt; simpl;
      apply blift_approx_open_nobnd2; eauto 2 with slow. }

  { unfold lblift; simpl; dands; auto; introv w.
    repeat (destruct n; try lia); unfold selectbt; simpl;
      apply blift_approx_open_nobnd2; eauto 2 with slow. }
Qed.

Lemma implies_ccequivc_ext_tuni {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_tuni a) (mkc_tuni b).
Proof.
  introv ceq ext; apply ceq in ext; spcast.
  apply implies_cequivc_tuni; auto.
Qed.

Lemma ccequivc_ext_mkc_tuni_mkc_nat_implies_ccequivc_mkc_uni {o} :
  forall lib (a : @CTerm o) i,
    ccequivc_ext lib a (mkc_tuni (mkc_nat i))
    -> ccequivc_ext lib a (mkc_uni 0 i).
Proof.
  introv ceq ext; apply ceq in ext; clear ceq; spcast.
  eapply cequivc_trans;[eauto|]; clear ext.
  apply computes_to_valc_implies_cequivc; eauto 2 with slow.
  pose proof (computes_to_valc_tuni lib' (mkc_nat i) (Z.of_nat i)) as xx.
  autorewrite with slow in xx; apply xx; try lia.
  rewrite <- mkc_nat_eq; eauto 3 with slow.
Qed.

Lemma dest_nuprl_tuni_sub_per {o} :
  forall (lib : @library o) a b eq i,
    ccomputes_to_valc_ext lib a (mkc_nat i)
    -> ccomputes_to_valc_ext lib b (mkc_nat i)
    -> nuprl uk0 lib (mkc_tuni a) (mkc_tuni b) eq
    -> (eq) <=2=> (per_bar_eq lib (univi_eq_lib_per uk0 lib i)).
Proof.
  introv compa compb cl.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in compa.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in compb.
  apply implies_ccequivc_ext_tuni in compa.
  apply implies_ccequivc_ext_tuni in compb.
  apply ccequivc_ext_mkc_tuni_mkc_nat_implies_ccequivc_mkc_uni in compa.
  apply ccequivc_ext_mkc_tuni_mkc_nat_implies_ccequivc_mkc_uni in compb.

  eapply nuprl_value_respecting_left  in cl;[|eauto].
  eapply nuprl_value_respecting_right in cl;[|eauto].
  clear dependent a.
  clear dependent b.

  apply dest_nuprl_uni_diff in cl.
  apply univ_implies_univi_bar3_diff in cl; repnd; subst; GC; auto.
Qed.

Lemma tequality_mkc_tuni {o} :
  forall lib (a b : @CTerm o) i,
    ccomputes_to_valc_ext lib a (mkc_nat i)
    -> ccomputes_to_valc_ext lib b (mkc_nat i)
    -> tequality uk0 lib (mkc_tuni a) (mkc_tuni b).
Proof.
  introv compa compb.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in compa.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in compb.
  apply implies_ccequivc_ext_tuni in compa.
  apply implies_ccequivc_ext_tuni in compb.
  apply ccequivc_ext_mkc_tuni_mkc_nat_implies_ccequivc_mkc_uni in compa.
  apply ccequivc_ext_mkc_tuni_mkc_nat_implies_ccequivc_mkc_uni in compb.
  eapply tequality_respects_cequivc_left;[apply ccequivc_ext_sym;eauto|].
  eapply tequality_respects_cequivc_right;[apply ccequivc_ext_sym;eauto|].
  apply tequality_mkc_uni.
Qed.
Hint Resolve tequality_mkc_tuni : slow.

Lemma equality_of_nat_bar_implies_tequality_mkc_uni {o} :
  forall lib (a b : @CTerm o),
    equality_of_nat_bar lib a b
    -> tequality uk0 lib (mkc_tuni a) (mkc_tuni b).
Proof.
  introv e.
  apply all_in_ex_bar_tequality_implies_tequality.
  eapply all_in_ex_bar_modus_ponens1;[|exact e]; clear e; introv x e.
  unfold equality_of_nat in *; exrepnd; eauto 3 with slow.
Qed.
Hint Resolve equality_of_nat_bar_implies_tequality_mkc_uni : slow.
