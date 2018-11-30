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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export sequents_lib.
Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_union.
Require Export subst_tacs.


(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)


Definition rule_equality_to_extract_concl {o} (H : @bhyps o) t T :=
  mk_baresequent H (mk_conclax (mk_member t T)).

Definition rule_equality_to_extract_hyp {o} (H : @bhyps o) t T :=
  mk_baresequent H (mk_concl T t).

Definition rule_equality_to_extract {o}
           (T t : @NTerm o)
           (H : barehypotheses) :=
    mk_rule
      (rule_equality_to_extract_concl H t T)
      [ rule_equality_to_extract_hyp H t T ]
      [].

Lemma rule_equality_to_extract_true {p} :
  forall lib
         (T t : NTerm)
         (H : @barehypotheses p),
    rule_true lib (rule_equality_to_extract T t H).
Proof.
  unfold rule_equality_to_extract, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  exists (@covered_axiom p (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as h; exrepnd; clear hyp1.

  lsubst_tac.
  split.
  - apply tequality_mkc_member_if_equal; split; auto.
  - apply equality_in_member. apply equality_refl in h1; dands; auto; spcast;
    apply computes_to_valc_refl; eauto 3 with slow.

Qed.

Lemma rule_equality_to_extract_true_ext_lib {p} :
  forall lib
         (T t : NTerm)
         (H : @barehypotheses p),
    rule_true_ext_lib lib (rule_equality_to_extract T t H).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_true_implies_rule_true3; auto;[|apply rule_equality_to_extract_true].
  introv h; apply @wf_axiom.
Qed.
