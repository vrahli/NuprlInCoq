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


Require Export sequents2.
Require Export sequents_lib.
Require Export sequents_tacs.
Require Export sequents_equality.
Require Export per_props_uni.
Require Export per_props_cequiv2.


(*
   H |- f a in Base

     By baseApply

     H |- f in Base
     H |- a in Base
 *)
Definition rule_base_apply {o}
           (H : @bhyps o)
           (f a : NTerm) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member (mk_apply f a) mk_base)))
    [
      mk_baresequent H (mk_conclax (mk_member f mk_base)),
      mk_baresequent H (mk_conclax (mk_member a mk_base))
    ]
    [].

Lemma rule_base_apply_true3 {o} :
  forall lib (H : @bhyps o) f a,
    rule_true3 lib (rule_base_apply H f a).
Proof.
  intros.
  unfold rule_base_apply, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (H) ||- (mk_conclax (mk_member (mk_apply f a) mk_base))) as wfc.
  { clear hyp1.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp.
    introv xx; allrw in_app_iff; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw <- @member_member_iff.
  pose proof (teq_and_member_if_member lib mk_base (mk_apply f a) s1 s2 H wT wt ct1 ct2 cT cT0) as q.
  lsubst_tac.
  apply q; auto.
  clear dependent s1; clear dependent s2.

  introv hf sim.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 hf sim) as q1; clear hyp1; exrepnd.
  pose proof (hyp2 s1 s2 hf sim) as q2; clear hyp2; exrepnd.
  lsubst_tac.
  allrw <- @member_member_iff.
  allrw @tequality_mkc_member_base.
  apply equality_in_base_iff; spcast.
  apply implies_cequivc_apply; auto.
Qed.



Definition rule_base_closed_concl {o} (t : @NTerm o) :=
  mk_baresequent [] (mk_conclax (mk_member t mk_base)).

(*
   |- t in Base

     By baseClosed

 *)
Definition rule_base_closed {o}
           (t : @NTerm o) :=
  mk_rule
    (rule_base_closed_concl t)
    []
    [].

Lemma rule_base_closed_true {o} :
  forall lib (t : @NTerm o),
    rule_true lib (rule_base_closed t).
Proof.
  intros.
  unfold rule_base_closed, rule_true, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs hyps.

  (* We prove the well-formedness of things *)
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract [] (mk_conclax (mk_member t mk_base))) as ce.
  { unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq; tcsp. }

  exists ce.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw <- @member_member_iff.
  apply similarity_length in sim; repnd; simphyps; cpx; proof_irr.
  dands; try (apply member_base).
  allrw @tequality_mkc_member_base; spcast; auto.
Qed.

Lemma rule_base_closed_true_ext_lib {o} :
  forall lib (t : @NTerm o),
    rule_true_ext_lib lib (rule_base_closed t).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib; introv.
  apply rule_true_implies_rule_true3;[|apply rule_base_closed_true].
  introv h; apply @wf_axiom.
Qed.

Lemma rule_base_closed_wf2 {o} :
  forall (t : @NTerm o),
    wf_rule2 (rule_base_closed t).
Proof.
  introv wf m; allsimpl; tcsp.
Qed.



Definition rule_base_equality_concl {o} (H : @bhyps o) i :=
  mk_baresequent H (mk_conclax (mk_member mk_base (mk_uni i))).

(*
   |- Base = Base in U(i)

     By baseEquality

 *)
Definition rule_base_equality {o}
           (H : @bhyps o) i :=
  mk_rule
    (rule_base_equality_concl H i)
    []
    [].

Lemma rule_base_equality_true3 {o} :
  forall lib (H : @bhyps o) i,
    rule_true3 lib (rule_base_equality H i).
Proof.
  intros.
  unfold rule_base_closed, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs hyps.

  (* We prove the well-formedness of things *)
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent H ||- (mk_conclax (mk_member mk_base (mk_uni i)))) as wfs.
  { unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp. }
  exists wfs.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw <- @member_member_iff.
  rw @tequality_mkc_member.
  dands; auto;
    try (apply tequality_mkc_uni);
    try (complete (right; spcast; auto));
    try (apply base_in_uni); tcsp.
Qed.

Lemma rule_base_equality_true_ext_lib {o} :
  forall lib (H : @barehypotheses o) i,
    rule_true_ext_lib lib (rule_base_equality H i).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_base_equality_true3.
Qed.

Lemma rule_base_equality_wf2 {o} :
  forall (H : @barehypotheses o) i,
    wf_rule2 (rule_base_equality H i).
Proof.
  introv wf m; allsimpl; tcsp.
Qed.
