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
Require Export per_props_uni.


(*
   H |- a <= b

     By approxTrans c

     H |- a <= c
     H |- c <= b
 *)
Definition rule_approx_trans {o}
           (H : @bhyps o)
           (a b c : NTerm) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx a b)))
    [
      mk_baresequent H (mk_conclax (mk_approx a c)),
      mk_baresequent H (mk_conclax (mk_approx c b))
    ]
    [].

Lemma rule_approx_trans_true3 {o} :
  forall lib (H : @bhyps o) a b c,
    rule_true3 lib (rule_approx_trans H a b c).
Proof.
  intros.
  unfold rule_approx_trans, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
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
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 eqh sim) as h; clear hyp1; exrepnd.
  pose proof (hyp2 s1 s2 eqh sim) as q; clear hyp2; exrepnd.
  lsubst_tac.

  allrw <- @equality_in_approx.
  allrw @tequality_mkc_approx.
  repnd.
  clear h1 h3 q1 q3.
  applydup h0 in h2; clear h0.
  applydup q0 in q2; clear q0.
  spcast.

  dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow).

  { split; intro q; spcast; eapply approxc_trans; eauto. }

  { eapply approxc_trans; eauto. }
Qed.



(*
   H |- a ~ b

     By cequivTrans c

     H |- a ~ c
     H |- c ~ b
 *)
Definition rule_cequiv_trans {o}
           (H : @bhyps o)
           (a b c : NTerm) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_cequiv a b)))
    [
      mk_baresequent H (mk_conclax (mk_cequiv a c)),
      mk_baresequent H (mk_conclax (mk_cequiv c b))
    ]
    [].

Lemma rule_cequiv_trans_true3 {o} :
  forall lib (H : @bhyps o) a b c,
    rule_true3 lib (rule_cequiv_trans H a b c).
Proof.
  intros.
  unfold rule_cequiv_trans, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
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
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 eqh sim) as h; clear hyp1; exrepnd.
  pose proof (hyp2 s1 s2 eqh sim) as q; clear hyp2; exrepnd.
  lsubst_tac.

  allrw @equality_in_mkc_cequiv.
  allrw @tequality_mkc_cequiv.
  repnd.
  clear h2 h3 q2 q3.
  applydup h0 in h1; clear h0.
  applydup q0 in q1; clear q0.
  spcast.

  dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow).

  { split; intro q; spcast; eapply cequivc_trans; eauto. }

  { eapply cequivc_trans; eauto. }
Qed.
