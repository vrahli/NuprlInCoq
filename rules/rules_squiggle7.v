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


Require Export sequents2.
Require Export sequents_lib.
Require Export sequents_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export lsubst_hyps.
Require Export per_can.


Lemma reduces_to_implies_approx_open1 {o} :
  forall lib (t x : @NTerm o),
    wf_term t
    -> wf_term x
    -> reduces_to lib t x
    -> approx_open lib t x.
Proof.
  introv wt wx rtx.
  apply approx_open_simpler_equiv.
  unfold simpl_olift.
  dands; eauto 2 with slow.
  introv wfs isp1 isp2.
  pose proof (reduces_to_lsubst_aux lib t x sub) as h.
  repeat (autodimp h hyp); eauto 3 with slow;[|].

  {
    apply isprogram_lsubst_iff in isp1; repnd.
    rw subvars_eq; introv i.
    apply isp1 in i; exrepnd.
    apply sub_find_some in i1.
    apply in_sub_eta in i1; sp.
  }

  exrepnd.

  rw <- @cl_lsubst_lsubst_aux in h1; eauto 2 with slow.
  rw <- @cl_lsubst_lsubst_aux in h0; eauto 2 with slow.
  eapply approx_trans;
    [apply reduces_to_implies_approx2;eauto
    |].
  apply alpha_implies_approx2; auto.
Qed.

Lemma reduces_to_implies_approx_open2 {o} :
  forall lib (t x : @NTerm o),
    wf_term t
    -> wf_term x
    -> reduces_to lib t x
    -> approx_open lib x t.
Proof.
  introv wt wx rtx.
  apply approx_open_simpler_equiv.
  unfold simpl_olift.
  dands; eauto 2 with slow.
  introv wfs isp1 isp2.
  pose proof (reduces_to_lsubst_aux lib t x sub) as h.
  repeat (autodimp h hyp); eauto 3 with slow;[|].

  {
    apply isprogram_lsubst_iff in isp2; repnd.
    rw subvars_eq; introv i.
    apply isp2 in i; exrepnd.
    apply sub_find_some in i1.
    apply in_sub_eta in i1; sp.
  }

  exrepnd.

  rw <- @cl_lsubst_lsubst_aux in h1; eauto 2 with slow.
  rw <- @cl_lsubst_lsubst_aux in h0; eauto 2 with slow.
  apply alpha_eq_sym in h0.
  applydup @reduces_to_preserves_program in h1; auto.
  eapply approx_trans;
    [apply alpha_implies_approx2;[|eauto];auto
    |].
  apply reduces_to_implies_approx1;auto.
Qed.

Lemma reduces_to_implies_cequiv_open {o} :
  forall lib (t x : @NTerm o),
    wf_term t
    -> wf_term x
    -> reduces_to lib t x
    -> cequiv_open lib t x.
Proof.
  introv wt wx rtx.
  apply olift_approx_cequiv;
    try (complete (apply (reduces_to_implies_approx_open1);auto));
    try (complete (apply (reduces_to_implies_approx_open2);auto)).
Qed.

Lemma reduces_to_preserves_cover_vars {o} :
  forall lib (t u : @NTerm o) sub,
    wf_term t
    -> reduces_to lib t u
    -> cover_vars t sub
    -> cover_vars u sub.
Proof.
  introv wt r cov.
  apply  reduces_to_preserves in r; auto; repnd.
  apply cover_vars_eq.
  allrw @subvars_eq; auto.
Qed.

Lemma reduces_to_implies_cequiv_lsubst {o} :
  forall lib (t x : @NTerm o) sub,
    wf_term t
    -> wf_term x
    -> cover_vars t sub
    -> reduces_to lib t x
    -> cequiv lib (csubst t sub) (csubst x sub).
Proof.
  introv wt wx cov rtx.
  applydup (reduces_to_preserves_cover_vars lib t x sub) in rtx; auto.
  apply reduces_to_implies_cequiv_open in rtx; auto.
  apply lsubst_cequiv_congr; eauto 2 with slow;
  apply isprogram_lsubst_prog_sub; eauto 2 with slow;
  try (rw @dom_csub_eq); auto.
Qed.

Lemma reduces_to_implies_ccequiv_ext_lsubst {o} :
  forall lib (t x : @NTerm o) sub wt wx ct cx,
    reduces_to lib t x
    -> ccequivc_ext lib (lsubstc t wt sub ct) (lsubstc x wx sub cx).
Proof.
  introv rtx ext; spcast.
  eapply lib_extends_preserves_reduces_to in rtx;[|eauto|];auto;[].
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv_lsubst; auto.
Qed.

Lemma ccequivc_ext_implies_all_in_ex_bar_ccequivc {o} :
  forall lib lib' (a b : @CTerm o),
    lib_extends lib' lib
    -> ccequivc_ext lib a b
    -> all_in_ex_bar lib' (fun lib => a ~=~(lib) b).
Proof.
  introv ext ceq.
  apply in_ext_implies_all_in_ex_bar; introv xt.
  apply ceq; eauto 3 with slow.
Qed.
Hint Resolve ccequivc_ext_implies_all_in_ex_bar_ccequivc : slow.

Lemma implies_all_in_ex_bar_iff_if_both_true {o} :
  forall (lib : @library o) F G,
    all_in_ex_bar lib F
    -> all_in_ex_bar lib G
    -> all_in_ex_bar lib (fun lib => (F lib) <=> (G lib)).
Proof.
  introv alla allb.
  eapply all_in_ex_bar_modus_ponens2;[|exact alla|exact allb]; clear alla allb; introv ext alla allb; tcsp.
Qed.



(**

<<
   H |- a ~ b

     By Computation ()

     if a reduces to b
>>
 *)

Definition rule_cequiv_computation_concl {o} a b (H : @bhyps o) :=
  mk_baresequent H (mk_conclax (mk_cequiv a b)).

Definition rule_cequiv_computation {o}
           (a b : NTerm)
           (H : @barehypotheses o) :=
  mk_rule
    (rule_cequiv_computation_concl a b H)
    []
    [].

Lemma rule_cequiv_computation_true3 {o} :
  forall lib (a b : NTerm) (H : @barehypotheses o)
         (red : reduces_to lib a b),
    rule_true3 lib (rule_cequiv_computation a b H).
Proof.
  unfold rule_cequiv_computation, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  assert (wf_csequent (rule_cequiv_computation_concl a b H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  allrw @member_eq.
  rw @tequality_mkc_cequiv.
  rw <- @member_cequiv_iff.

  pose proof (reduces_to_implies_ccequiv_ext_lsubst lib a b s1 w1 w2 c1 c2 red) as h.
  pose proof (reduces_to_implies_ccequiv_ext_lsubst lib a b s2 w1 w2 c0 c3 red) as q.

  dands; spcast; eauto 2 with slow;[].
  apply implies_all_in_ex_bar_iff_if_both_true; eauto 3 with slow.
Qed.

Lemma rule_cequiv_computation_wf2 {o} :
  forall (a b : NTerm) (H : @barehypotheses o),
    wf_rule2 (rule_cequiv_computation a b H).
Proof.
  introv wf j.

  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq;
  allrw <- @wf_approx_iff; repnd; auto;
  allrw @covered_approx; repnd; auto.
Qed.

Lemma rule_cequiv_computation_atmost_true3 {o} :
  forall lib
         (a b : NTerm)
         (n : nat)
         (H : @barehypotheses o)
         (r : reduces_in_atmost_k_steps lib a b n),
    rule_true3 lib (rule_cequiv_computation a b H).
Proof.
  introv r.
  apply rule_cequiv_computation_true3.
  apply reduces_in_atmost_k_steps_implies_reduces_to in r; auto.
Qed.


Hint Resolve alpha_eq_sym : slow.

Lemma alpha_eq_preserves_cover_vars {o} :
  forall (a b : @NTerm o) s,
    alpha_eq a b
    -> cover_vars a s
    -> cover_vars b s.
Proof.
  introv aeq cov.
  unfold cover_vars, over_vars in *.
  apply alphaeq_preserves_free_vars in aeq; allrw <-; auto.
Qed.
Hint Resolve alpha_eq_preserves_cover_vars : slow.

Lemma alpha_eq_implies_ccequivc_ext {o} :
  forall lib (a b : @NTerm o) wa wb s ca cb,
    alpha_eq a b
    -> ccequivc_ext lib (lsubstc a wa s ca) (lsubstc b wb s cb).
Proof.
  introv aeq ext; spcast.
  unfold cequivc; simpl.
  eapply cequiv_rw_r_eauto;[|apply cequiv_refl].
  { apply lsubst_alpha_congr2; auto. }
  { apply isprogram_csubst; eauto 3 with slow. }
Qed.


(**

<<
   H |- a ~ b

     By Computation ()

     if a reduces to a term alpha-eq to b
>>
 *)

Lemma rule_cequiv_computation_aeq_true3 {o} :
  forall lib (a b c : NTerm) (H : @barehypotheses o)
         (red : reduces_to lib a b)
         (aeq : alpha_eq b c),
    rule_true3 lib (rule_cequiv_computation a c H).
Proof.
  unfold rule_cequiv_computation, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc by prove_seq
  end.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  allrw @member_eq.
  rw @tequality_mkc_cequiv.
  rw <- @member_cequiv_iff.

  applydup @reduces_to_preserves_wf in red; auto.

  assert (cover_vars b s1) as covb1 by eauto 3 with slow.
  assert (cover_vars b s2) as covb2 by eauto 3 with slow.

  pose proof (reduces_to_implies_ccequiv_ext_lsubst lib a b s1 w1 red0 c1 covb1 red) as h.
  pose proof (reduces_to_implies_ccequiv_ext_lsubst lib a b s2 w1 red0 c0 covb2 red) as q.

  pose proof (alpha_eq_implies_ccequivc_ext lib b c red0 w2 s1 covb1 c2 aeq) as z.
  pose proof (alpha_eq_implies_ccequivc_ext lib b c red0 w2 s2 covb2 c3 aeq) as w.

  eapply ccequivc_ext_trans in w;[|eauto].
  eapply ccequivc_ext_trans in z;[|eauto].
  clear h q.

  dands; spcast; eauto 3 with slow.
  apply implies_all_in_ex_bar_iff_if_both_true; eauto 3 with slow.
Qed.

Lemma rule_cequiv_computation_aeq_wf2 {o} :
  forall (a b : NTerm) (H : @barehypotheses o),
    wf_rule2 (rule_cequiv_computation a b H).
Proof.
  introv wf j.
  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq.
Qed.
