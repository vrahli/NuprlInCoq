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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export sequents2.
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


(**

<<
   H |- a ~ b

     By Computation ()

     if a reduces to b
>>
 *)

Definition rule_cequiv_concl {o} a b (H : @bhyps o) :=
  mk_baresequent H (mk_conclax (mk_cequiv a b)).

Definition rule_cequiv {o}
           (a b : NTerm)
           (H : @barehypotheses o) :=
  mk_rule
    (rule_cequiv_concl a b H)
    []
    [].

Lemma rule_cequiv_computation_true3 {o} :
  forall lib (a b : NTerm) (H : @barehypotheses o)
         (red : reduces_to lib a b),
    rule_true3 lib (rule_cequiv a b H).
Proof.
  unfold rule_cequiv, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  assert (wf_csequent (rule_cequiv_concl a b H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  allrw @member_eq.
  rw @tequality_mkc_cequiv.
  rw <- @member_cequiv_iff.

  pose proof (reduces_to_implies_cequiv_lsubst lib a b s1) as h.
  repeat (autodimp h hyp).

  pose proof (reduces_to_implies_cequiv_lsubst lib a b s2) as q.
  repeat (autodimp q hyp).

  dands; spcast; auto;[].

  split; intro z; spcast; eauto 3 with slow.
Qed.

Lemma rule_cequiv_computation_wf2 {o} :
  forall (a b : NTerm) (H : @barehypotheses o),
    wf_rule2 (rule_cequiv a b H).
Proof.
  introv wf j.

  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq;
  allrw <- @wf_approx_iff; repnd; auto;
  allrw @covered_approx; repnd; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
