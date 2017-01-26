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
Require Export sequents_tacs.
Require Export sequents_equality.
Require Export per_props_equality2.


(*
   H |- a = b in T

     By equalitySymmetry

     H |- b = a in T
 *)
Definition rule_equality_symmetry {o}
           (H : @bhyps o) a b T :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b T)))
    [ mk_baresequent H (mk_conclax (mk_equality b a T)) ]
    [].

Lemma rule_equality_symmetry_true3 {o} :
  forall lib (H : @bhyps o) a b T,
    rule_true3 lib (rule_equality_symmetry H a b T).
Proof.
  intros.
  unfold rule_equality_symmetry, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (H) ||- (mk_conclax (mk_equality a b T))) as wfc.
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
  rw <- @member_equality_iff.
  teq_and_eq T a b s1 s2 H.

  {
    vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 eqh sim) as q; clear hyp1; exrepnd.
    lsubst_tac.
    apply tequality_mkc_equality_sp in q0; sp.
  }

  {
    vr_seq_true in hyp1.
    pose proof (hyp1 s2 s1) as q; clear hyp1; exrepnd.
    repeat (autodimp q hyp).
    { eapply similarity_hyps_functionality_trans; eauto. }
    { apply similarity_sym; auto. }
    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in q1.
    applydup @equality_commutes4 in q0; auto.
    apply equality_sym; auto.
    apply tequality_mkc_equality_sp in q0; repnd.
    eapply tequality_preserving_equality;[exact q2|]; auto.
  }
Qed.


(*
   H |- a = b in T

     By equalityTransitivity

     H |- a = c in T
     H |- c = b in T
 *)
Definition rule_equality_transitivity {o}
           (H : @bhyps o) a b c T :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b T)))
    [
      mk_baresequent H (mk_conclax (mk_equality a c T)),
      mk_baresequent H (mk_conclax (mk_equality c b T))
    ]
    [].

Lemma rule_equality_transitivity_true3 {o} :
  forall lib (H : @bhyps o) a b c T,
    rule_true3 lib (rule_equality_transitivity H a b c T).
Proof.
  intros.
  unfold rule_equality_transitivity, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (H) ||- (mk_conclax (mk_equality a b T))) as wfc.
  { clear hyp1 hyp2.
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
  rw <- @member_equality_iff.
  teq_and_eq T a b s1 s2 H.

  {
    vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 eqh sim) as q; clear hyp1; exrepnd.
    lsubst_tac.
    apply tequality_mkc_equality_sp in q0; sp.
  }

  {
    vr_seq_true in hyp1.
    vr_seq_true in hyp2.
    pose proof (hyp1 s1 s2 hf sim) as q; clear hyp1; exrepnd.
    pose proof (hyp2 s1 s2 hf sim) as h; clear hyp2; exrepnd.
    lsubst_tac.
    allrw <- @member_equality_iff.
    eapply equality_trans;[exact q1|].
    applydup @equality_commutes4 in h0; auto.
  }
Qed.
