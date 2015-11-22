(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export sequents2.
Require Export sequents_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export lsubst_hyps.
Require Export per_can.


(**

<<
   H |- (a1 <= b1) = (a2 <= b2) in Type(i)

     By ApproxEq ()

     H |- a1 = a2 in Base
     H |- b1 = b2 in Base
>>
 *)

Definition rule_approx_eq_concl {o} a1 a2 b1 b2 i (H : @bhyps o) :=
  mk_baresequent
    H
    (mk_concleq
       (mk_approx a1 b1)
       (mk_approx a2 b2)
       (mk_uni i)).

Definition rule_approx_eq_hyp {o} a1 a2 (H : @bhyps o) :=
  mk_baresequent H (mk_concleq a1 a2 mk_base).

Definition rule_approx_eq {o}
           (a1 a2 b1 b2 : NTerm)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (rule_approx_eq_concl a1 a2 b1 b2 i H)
    [ rule_approx_eq_hyp a1 a2 H,
      rule_approx_eq_hyp b1 b2 H
    ]
    [].

Lemma rule_approx_eq_true3 {o} :
  forall lib (a1 a2 b1 b2 : NTerm) (i : nat) (H : @barehypotheses o),
    rule_true3 lib (rule_approx_eq a1 a2 b1 b2 i H).
Proof.
  unfold rule_approx_eq, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (rule_approx_eq_concl a1 a2 b1 b2 i H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  teq_and_eq (@mk_uni o i) (mk_approx a1 b1) (mk_approx a2 b2) s1 s2 H.
  { apply tequality_mkc_uni. }

  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2.
  exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  rw @tequality_mkc_equality_base_iff in hyp3; repnd; spcast.
  rw @tequality_mkc_equality_base_iff in hyp0; repnd; spcast.
  allrw @equality_in_base_iff; spcast.
  apply mkc_approx_equality_in_uni.
  split; intro h; spcast; auto.

  { eapply approxc_cequivc_trans;[|eauto].
    eapply cequivc_approxc_trans;[apply cequivc_sym; eauto|].
    eapply approxc_cequivc_trans;[|eauto].
    eapply cequivc_approxc_trans;[apply cequivc_sym; eauto|].
    auto. }

  { eapply approxc_cequivc_trans;[|apply cequivc_sym; eauto].
    eapply cequivc_approxc_trans;[eauto|].
    eapply approxc_cequivc_trans;[|apply cequivc_sym; eauto].
    eapply cequivc_approxc_trans;[eauto|].
    auto. }
Qed.

Lemma rule_approx_eq_wf2 {o} :
  forall (a1 a2 b1 b2 : NTerm) (i : nat) (H : @barehypotheses o),
    wf_rule2 (rule_approx_eq a1 a2 b1 b2 i H).
Proof.
  introv wf j.

  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq;
  allrw <- @wf_approx_iff; repnd; auto;
  allrw @covered_approx; repnd; auto.
Qed.

(**

<<
   H |- ax = ax in (a <= b)

     By ApproxMemberEq ()

     H |- a <= b
>>
 *)

Definition rule_approx_member_eq_concl {o} a b (H : @bhyps o) :=
  mk_baresequent H (mk_concleq mk_axiom mk_axiom (mk_approx a b)).

Definition rule_approx_member_eq_hyp {o} a b (H : @bhyps o) :=
  mk_baresequent H (mk_conclax (mk_approx a b)).

Definition rule_approx_member_eq {o}
           (a b : NTerm)
           (H : @barehypotheses o) :=
  mk_rule (rule_approx_member_eq_concl a b H)
          [ rule_approx_member_eq_hyp a b H ]
          [].

Lemma rule_approx_member_eq_true3 {o} :
  forall lib (a b : NTerm) (H : @barehypotheses o),
    rule_true3 lib (rule_approx_member_eq a b H).
Proof.
  unfold rule_approx_member_eq, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (rule_approx_member_eq_concl a b H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.

  dup pt1 as cv1.
  dup pt2 as cv2.
  dup wfce as wax.
  teq_and_eq (mk_approx a b) (@mk_axiom o) (@mk_axiom o) s1 s2 H.

  { vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 eqh sim) as h; clear hyp1; exrepnd.
    lsubst_tac; auto. }

  { vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac; auto. }
Qed.

Lemma rule_approx_member_eq_wf2 {o} :
  forall (a b : NTerm) (H : @barehypotheses o),
    wf_rule2 (rule_approx_member_eq a b H).
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
