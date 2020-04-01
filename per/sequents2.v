(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Require Export sequents.


Definition wf_bseq {o} (s : @baresequent o) :=
  vswf_hypotheses [] (hyps s)
  # wf_term (ctype (concl s))
  # closed_type_baresequent s.

(* This is a variant of [rule_true2] (which is equivalent to [rule_true])
   that only needs [wf_bseq] and not [pwf_sequent].
 *)
Definition rule_true3 {o} uk lib (R : @rule o) : Type :=
  forall wf    : wf_bseq (goal R),
  forall cargs : args_constraints (sargs R) (hyps (goal R)),
  forall hyps  : (forall s, LIn s (subgoals R) -> sequent_true2 uk lib s),
    sequent_true2 uk lib (goal R).

Lemma pwf_sequent_implies_wf_bseq {o} :
  forall (seq : @baresequent o),
    pwf_sequent seq -> wf_bseq seq.
Proof.
  introv wf.
  unfold pwf_sequent, wf_sequent, wf_concl in wf; unfold wf_bseq; repnd; dands; auto.
Qed.
Hint Resolve pwf_sequent_implies_wf_bseq : slow.

(* The other direction is not true because [rule_true] and [rule_true2] assume
   that the extract is well-formed. *)
Lemma rule_true3_implies_rule_true2 {o} :
  forall uk lib (R : @rule o), rule_true3 uk lib R -> rule_true2 uk lib R.
Proof.
  introv rt wf args imp.
  unfold rule_true3 in rt.
  repeat (autodimp rt hyp); eauto 3 with slow.
Qed.
Hint Resolve rule_true3_implies_rule_true2 : slow.

Lemma rule_true3_implies_rule_true {o} :
  forall uk lib (R : @rule o), rule_true3 uk lib R -> rule_true uk lib R.
Proof.
  introv rt.
  rw @rule_true_iff_rule_true2; eauto 3 with slow.
Qed.
Hint Resolve rule_true3_implies_rule_true : slow.

Definition wf_subgoals2 {o} (R : @rule o) :=
  forall s, LIn s (subgoals R) -> wf_bseq s.

Lemma fold_wf_subgoals2 {o} :
  forall R : @rule o,
    (forall s, LIn s (subgoals R) -> wf_bseq s) = wf_subgoals2 R.
Proof. sp. Qed.

(* This is a variant of [wf_rule] that uses [wf_bseq] instead of [pwf_sequent] *)
Definition wf_rule2 {o} (R : @rule o) :=
  wf_bseq (goal R) -> wf_subgoals2 R.
