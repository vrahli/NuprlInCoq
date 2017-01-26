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

  Authors: Vincent Rahli

*)


Require Export computation_injections.
Require Export approx_props2.
Require Export sequents2.
Require Export sequents_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_top.
Require Export per_props_union.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)


(**

  The following rule states that if [mk_decide f x a y b] computes to
  a value then [p] must compute to an injection:

<<
  H |- d in Top + Top

    By haltDecide

    H |- halts(mk_decide d x a y b)
    H |- d in Base
>>

*)

Definition rule_halt_decide {o}
           (H : barehypotheses)
           (x y : NVar)
           (d a b : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member d (mk_union mk_top mk_top))))
    [
      mk_baresequent H (mk_conclax (mk_halts (mk_decide d x a y b))),
      mk_baresequent H (mk_conclax (mk_member d mk_base))
    ]
    [].

Lemma rule_halt_decide_true3 {o} :
  forall lib (H  : barehypotheses)
         (x y : NVar)
         (d a b : @NTerm o),
    rule_true3 lib (rule_halt_decide H x y d a b).
Proof.
  intros.
  unfold rule_halt_decide, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [ ws1 hyp1].
  destruct Hyp0 as [ ws2 hyp2].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (H) ||- (mk_conclax (mk_member d (mk_union mk_top mk_top)))) as wfc.
  { clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp.
    introv xx; allrw in_app_iff; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  rw <- @member_member_iff.
  pose proof (teq_and_member_if_member lib (mk_union mk_top mk_top) d s1 s2 H wT wt ct1 ct2 cT cT0) as q.
  lsubst_tac.
  apply q; auto.

  { apply tequality_mkc_union; dands; apply type_mkc_top. }
  clear dependent s1; clear dependent s2.
  introv hf sim.

  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 hf sim) as q; clear hyp1; exrepnd.
  pose proof (hyp2 s1 s2 hf sim) as h; clear hyp2; exrepnd.
  lsubst_tac.

  allrw @member_eq.
  clear h1.
  allrw @tequality_mkc_member_base; spcast.
  allrw <- @member_halts_iff.
  allrw @tequality_mkc_halts.
  applydup q0 in q1; clear q0.
  spcast.
  apply hasvaluec_mkc_decide in q1.
  apply hasvaluec_mkc_decide in q2.
  exrepnd.

  apply equality_mkc_union; dands; auto; try (apply type_mkc_top).

  repndors.

  - left.
    exists a1 a0; dands; spcast; auto.
    apply equality_mkc_top.

  - apply cequivc_sym in h0; eapply cequivc_mkc_inl in h0;eauto.
    exrepnd.
    eapply computes_to_valc_eq in q2; try (exact h0).
    apply mkc_inl_inr_eq in q2; tcsp.

  - eapply cequivc_mkc_inl in h0;eauto.
    exrepnd.
    eapply computes_to_valc_eq in q0; try (exact h0).
    apply mkc_inl_inr_eq in q0; tcsp.

  - right.
    exists a1 a0; dands; spcast; auto.
    apply equality_mkc_top.
Qed.
