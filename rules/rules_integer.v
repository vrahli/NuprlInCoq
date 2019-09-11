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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export sequents2.
Require Export sequents_lib.
Require Export rules_useful.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export per_props_equality.
Require Export sequents_equality.



(**

<<
   H |- n in Z

     By integer_equality(n)
>>
 *)

Definition rule_integer_equality_concl {o} (H : @bhyps o) (n : Z) :=
  mk_baresequent H (mk_conclax (mk_member (mk_integer n) mk_int)).

Definition rule_integer_equality {o}
             (H : @barehypotheses o)
             (n : Z) :=
  mk_rule
    (rule_integer_equality_concl H n)
    [ ]
    [ ].

Lemma rule_integer_equality_true3 {o} :
  forall lib
         (H : @barehypotheses o)
         (n : Z),
    rule_true3 lib (rule_integer_equality H n).
Proof.
  intros.
  unfold rule_integer_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs hyps.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.

  assert (wf_csequent (rule_integer_equality_concl H n)) as wfc.
  { unfold wf_csequent, wf_sequent, wf_concl; simpl.
    allrw @vswf_hypotheses_nil_eq.
    dands; auto.
    apply covered_axiom. }
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; repnd; allsimpl; proof_irr; GC.

  vr_seq_true.
  lsubst_tac.
  rw @tequality_mkc_member_sp.
  rw @equality_in_member.
  dands; auto;
    try (apply tequality_int);
    try (complete (right; spcast; auto));
    try (complete (spcast; apply computes_to_valc_refl; eauto 2 with slow));
    try (complete (apply equality_in_int; exists n; dands;
                   spcast; apply computes_to_valc_refl; eauto 2 with slow)).
Qed.

Lemma rule_integer_equality_true_ext_lib {o} :
  forall lib
         (H : @barehypotheses o)
         (n : Z),
    rule_true_ext_lib lib (rule_integer_equality H n).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_integer_equality_true3.
Qed.

Lemma rule_integer_equality_true {o} :
  forall lib
         (H : @barehypotheses o)
         (n : Z),
    rule_true lib (rule_integer_equality H n).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_integer_equality_true3.
Qed.
