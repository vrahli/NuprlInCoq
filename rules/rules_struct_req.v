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
Require Export rules_useful.
Require Export sequents_useful.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export per_props_requality.

(*

  We'll use == for the equality that's inhabited by refl terms as opposed to =,
  which we use for the equality that's inhabited by axiom.

 *)


(* !!MOVE that somewhere else *)
Definition mk_concl_req {o} (a b T : @NTerm o) : conclusion :=
  mk_concl (mk_requality a b T) (mk_refl a).

(* !!MOVE that somewhere else *)
Definition mk_concl_rmem {o} (a T : @NTerm o) : conclusion :=
  mk_concl (mk_rmember a T) (mk_refl a).


(**

  The following rule says that to prove a conclusion [C] one can
  always provide an evidence [t] for that type and prove instead that
  [t] is a member of [C]:
<<
   H |- C ext t

     By introduction t

     H |- t == t in C ext refl(t)
>>
 *)

Definition rule_introduction_req_concl {o} (H : @bhyps o) C t :=
  mk_baresequent H (mk_concl C t).

Definition rule_introduction_req_hyp {o} (H : @bhyps o) C t :=
  mk_baresequent H (mk_concl_rmem t C).

Definition rule_introduction_req {o}
           (H : @barehypotheses o)
           (C t : NTerm) :=
  mk_rule
    (rule_introduction_req_concl H C t)
    [ rule_introduction_req_hyp H C t ]
    [ sarg_term t ].

Lemma rule_introduction_req_true3 {o} :
  forall lib
         (H : @barehypotheses o)
         (C t : NTerm),
    rule_true3 lib (rule_introduction_req H C t).
Proof.
  intros.
  unfold rule_introduction_req, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.

  unfold args_constraints in cargs; allsimpl.
  generalize (cargs (sarg_term t) (inl eq_refl)); clear cargs; intro arg1.
  unfold arg_constraints in arg1.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp as [ws1 hyp1].
  destseq; allsimpl; clear_irr; GC.

  assert (wf_csequent (rule_introduction_req_concl H C t)) as wfc.
  { clear hyp1.
    unfold wf_csequent, wf_sequent, wf_concl; simpl; dands; auto.
    allrw <- @wf_equality_iff; sp. }
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; repnd; allsimpl; proof_irr; GC.

  vr_seq_true.

  vr_seq_true in hyp1.

  pose proof (hyp1 s1 s2) as hyp1.
  repeat (autodimp hyp1 h).
  exrepd.

  lsubst_tac.
  rw @tequality_mkc_rmember in t0; repnd.
  apply equality_in_mkc_rmember in e; exrepnd; computes_to_value_isvalue.
Qed.

Lemma rule_introduction_req_true {o} :
  forall lib
         (H : @barehypotheses o)
         (C t : NTerm),
    rule_true lib (rule_introduction_req H C t).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_introduction_req_true3.
Qed.

Lemma rule_introduction_req_wf2 {o} :
  forall (H : @barehypotheses o) (C t : NTerm),
    wf_term t
    -> covered t (vars_hyps H)
    -> wf_rule2 (rule_introduction_req H C t).
Proof.
  introv wt cov wf m; allsimpl.
  repndors; subst; tcsp.
  allunfold @wf_bseq; allsimpl; repnd; dands; auto.
  - apply wf_equality; auto.
  - allunfold @closed_type_baresequent; allsimpl.
    allunfold @closed_type; allsimpl.
    apply covered_equality; dands; auto.
Qed.



(**
<<
   H |- a = b in C ext axiom

     By introduction t

     H |- a == b in C ext e
>>
 *)

Definition rule_squash_equality_concl {o} (H : @bhyps o) a b C :=
  mk_baresequent H (mk_conclax (mk_equality a b C)).

Definition rule_squash_equality_hyp {o} (H : @bhyps o) a b C e :=
  mk_baresequent H (mk_concl (mk_requality a b C) e).

Definition rule_squash_equality {o}
           (H : @barehypotheses o)
           (a b C e : NTerm) :=
  mk_rule
    (rule_squash_equality_concl H a b C)
    [ rule_squash_equality_hyp H a b C e ]
    [ ].

Lemma rule_squash_equality_true3 {o} :
  forall lib
         (H : @barehypotheses o)
         (a b C e : NTerm),
    rule_true3 lib (rule_squash_equality H a b C e).
Proof.
  intros.
  unfold rule_squash_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp as [ws1 hyp1].
  destseq; allsimpl; clear_irr; GC.

  assert (wf_csequent (rule_squash_equality_concl H a b C)) as wfc.
  { clear hyp1.
    unfold wf_csequent, wf_sequent, wf_concl; simpl; dands; auto; eauto 3 with slow.
    unfold closed_extract; simpl.
    apply covered_axiom. }
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; repnd; allsimpl; proof_irr; GC.

  vr_seq_true.

  vr_seq_true in hyp1.

  pose proof (hyp1 s1 s2) as hyp1.
  repeat (autodimp hyp1 h).
  exrepd.

  lsubst_tac.
  rw @tequality_mkc_requality in t; repnd.
  rw @equality_in_mkc_requality in e0; exrepnd; computes_to_value_isvalue.

  rw @tequality_mkc_equality_sp.
  rw <- @member_equality_iff.
  dands; auto.
Qed.



(**
<<
   H |- a == b in C ext refl(a)

     By introduction t

     H |- a = b in C ext e
>>
 *)

Definition rule_unsquash_equality_concl {o} (H : @bhyps o) a b C :=
  mk_baresequent H (mk_concl_req a b C).

Definition rule_unsquash_equality_hyp {o} (H : @bhyps o) a b C e :=
  mk_baresequent H (mk_concl (mk_equality a b C) e).

Definition rule_unsquash_equality {o}
           (H : @barehypotheses o)
           (a b C e : NTerm) :=
  mk_rule
    (rule_unsquash_equality_concl H a b C)
    [ rule_unsquash_equality_hyp H a b C e ]
    [ sarg_term a ].

Lemma rule_unsquash_equality_true3 {o} :
  forall lib
         (H : @barehypotheses o)
         (a b C e : NTerm),
    rule_true3 lib (rule_unsquash_equality H a b C e).
Proof.
  intros.
  unfold rule_unsquash_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.

  unfold args_constraints in cargs; allsimpl.
  generalize (cargs (sarg_term a) (inl eq_refl)); clear cargs; intro arg1.
  unfold arg_constraints in arg1.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp as [ws1 hyp1].
  destseq; allsimpl; clear_irr; GC.

  assert (wf_csequent (rule_unsquash_equality_concl H a b C)) as wfc.
  { clear hyp1.
    allrw @wf_equality_iff2; repnd.
    unfold wf_csequent, wf_sequent, wf_concl; simpl; dands; auto;
      try (apply wf_requality); try (apply wf_refl); auto.
    unfold closed_extract; simpl.
    unfold covered; simpl; autorewrite with slow; auto. }
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; repnd; allsimpl; proof_irr; GC.

  vr_seq_true.

  vr_seq_true in hyp1.

  pose proof (hyp1 s1 s2) as hyp1.
  repeat (autodimp hyp1 h).
  exrepd.

  lsubst_tac.
  rw @equality_in_mkc_equality in e0; exrepnd; computes_to_value_isvalue.
  clear e0 e2.
  apply tequality_mkc_equality_sp_eq in t; auto; repnd.

  rw @tequality_mkc_requality.
  rw @equality_in_mkc_requality.
  dands; auto; try (complete (left; auto)).
  eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_refl; eauto 3 with slow));
    auto; try (complete (eapply equality_refl; eauto)).
  eapply equality_trans;[|eauto].
  apply equality_sym; auto.
Qed.
