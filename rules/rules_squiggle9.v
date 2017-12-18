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


Require Export cequiv_bind.
Require Export sequents2.
Require Export sequents_lib.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export per_can.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.


(**

<<
   H |- a ~ b
     no subgoals

     if alpha_eq(a,b)
>>
 *)

Definition rule_cequiv_alpha_eq_concl {o} (H : @bhyps o) a b :=
  mk_baresequent H (mk_conclax (mk_cequiv a b)).

Definition rule_cequiv_alpha_eq {o}
           (H : @barehypotheses o)
           (a b : NTerm) :=
  mk_rule (rule_cequiv_alpha_eq_concl H a b) [] [].

Lemma rule_cequiv_alpha_eq_true3 {o} :
  forall lib (H  : @barehypotheses o) (a b : NTerm) (aeq : alpha_eq a b),
    rule_true3 lib (rule_cequiv_alpha_eq H a b).
Proof.
  intros.
  unfold rule_cequiv_alpha_eq, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs hyps.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc by prove_seq
  end.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_cequiv_iff; sp.

  - apply tequality_mkc_cequiv; split; intro h; spcast.

    + apply alphaeqc_implies_cequivc.
      unfold alphaeqc; simpl.
      apply lsubst_alpha_congr2; auto.

    + apply alphaeqc_implies_cequivc.
      unfold alphaeqc; simpl.
      apply lsubst_alpha_congr2; auto.

  - spcast.
    apply alphaeqc_implies_cequivc.
    unfold alphaeqc; simpl.
    apply lsubst_alpha_congr2; auto.
Qed.

Lemma rule_cequiv_alpha_eq_true_ext_lib {o} :
  forall lib (H  : @barehypotheses o) (a b : NTerm) (aeq : alpha_eq a b),
    rule_true_ext_lib lib (rule_cequiv_alpha_eq H a b).
Proof.
  introv aeq.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_cequiv_alpha_eq_true3; auto.
Qed.

Lemma rule_cequiv_alpha_eq_wf2 {o} :
  forall (H  : @barehypotheses o) (a b : NTerm),
    wf_rule2 (rule_cequiv_alpha_eq H a b).
Proof.
  introv wf j; allsimpl; repndors; subst; tcsp;
    allunfold @wf_bseq; repnd; allsimpl; wfseq.
Qed.
