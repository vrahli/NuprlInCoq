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
Require Export per_props_cequiv3.



(*
   H |- isint(z;a;b) ~ a

     By isintReduceTrue

     H |- z in Int
 *)
Definition rule_isint_reduce_true {o}
           (H : @bhyps o)
           (z a b : NTerm) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_cequiv (mk_isint z a b) a)))
    [
      mk_baresequent H (mk_conclax (mk_member z mk_int))
    ]
    [].

Lemma rule_isint_reduce_true_true3 {o} :
  forall lib (H : @bhyps o) z a b,
    rule_true3 lib (rule_isint_reduce_true H z a b).
Proof.
  intros.
  unfold rule_isint_reduce_true, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
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

  rw @equality_in_mkc_cequiv_ax.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as h; clear hyp1; exrepnd.
  lsubst_tac.
  apply member_if_inhabited in h1.

  repeat (rw <- @fold_mkc_member in h0).
  apply equality_commutes in h0; auto.
  clear h1.
  apply equality_in_int in h0.
  unfold equality_of_int in h0; exrepnd; spcast.

  pose proof (teq_and_eq_if_cequiv
                lib (mk_isint z a b) a s1 s2 H
                w1 w2 c1 c3 c2 c5) as q.
  lsubst_tac.
  apply q; clear q; auto.

  { rewrite mkc_isint_as_can_test.
    spcast.
    eapply cequivc_trans;
      [apply implies_cequivc_can_test;
       [apply computes_to_valc_implies_cequivc;exact h0
       |apply cequivc_refl
       |apply cequivc_refl]
      |].
    rewrite <- mkc_isint_as_can_test.
    apply cequivc_mkc_int_integer. }

  { rewrite mkc_isint_as_can_test.
    spcast.
    eapply cequivc_trans;
      [apply implies_cequivc_can_test;
       [apply computes_to_valc_implies_cequivc;exact h1
       |apply cequivc_refl
       |apply cequivc_refl]
      |].
    rewrite <- mkc_isint_as_can_test.
    apply cequivc_mkc_int_integer. }
Qed.
