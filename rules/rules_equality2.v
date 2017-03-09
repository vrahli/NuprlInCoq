(*

  Copyright 2014 Cornell University

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


Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_union.
Require Export subst_tacs.


(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)


Definition rule_equality_to_extract {o}
           (T t : @NTerm o)
           (H : barehypotheses) :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_member t T)))
      [ mk_baresequent H (mk_concl T t) ]
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

  allrw @tequality_mkc_member_sp.
  allrw @equality_in_member.

  dands; auto; spcast;
  try (apply computes_to_valc_refl; eauto 3 with slow).
  apply equality_refl in h1; auto.
Qed.
