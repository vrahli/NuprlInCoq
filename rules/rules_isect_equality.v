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
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export per_props_isect.
Require Export rules_tyfam.
Require Export rules_tyfam2.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.



(* end hide *)

(* [8] ============ ISECT EQUALITY ============ *)

(**

  We can state the intersection equality rule as follows:
<<
   H |- isect x1:a1. b1 = isect x2:a2.b2 in Type(i)

     By isectEquality y ()

     H |- a1 = a2 in Type(i)
     H y : a1 |- subst b1 x1 y = subst b2 x2 y in Type(i)
>>
 *)

Definition rule_isect_equality_concl {o} a1 a2 x1 x2 b1 b2 i (H : @bhyps o) :=
  mk_baresequent
    H
    (mk_concleq
       (mk_isect a1 x1 b1)
       (mk_isect a2 x2 b2)
       (mk_uni i)).

Definition rule_isect_equality_hyp1 {o} a1 a2 i (H : @bhyps o) :=
  mk_baresequent H (mk_concleq a1 a2 (mk_uni i)).

Definition rule_isect_equality_hyp2 {o} a1 b1 b2 x1 x2 y i (H : @bhyps o) :=
  mk_baresequent
    (snoc H (mk_hyp y a1))
    (mk_concleq
       (subst b1 x1 (mk_var y))
       (subst b2 x2 (mk_var y))
       (mk_uni i)).

Definition rule_isect_equality {o}
           (a1 a2 b1 b2 : NTerm)
           (x1 x2 y : NVar)
           (i   : nat)
           (H   : @barehypotheses o) :=
  mk_rule
    (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
    [ rule_isect_equality_hyp1 a1 a2 i H,
      rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H
    ]
    [ sarg_var y ].

Lemma rule_isect_equality_true3 {o} :
  forall lib (a1 a2 b1 b2 : NTerm),
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses o,
    rule_true3 lib (rule_isect_equality
                      a1 a2 b1 b2
                      x1 x2 y
                      i
                      H).
Proof.
  intros.
  apply (rule_tyfam_equality_true3 _ _ mkc_isect); auto.

  - introv; simpl; allrw remove_nvars_nil_l; allrw app_nil_r; auto.

  - introv; apply lsubstc_mk_isect_ex.

  - introv; apply equality_isect.
Qed.

Lemma rule_isect_equality_true_ext_lib {o} :
  forall lib (a1 a2 b1 b2 : NTerm),
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses o,
    rule_true_ext_lib lib (rule_isect_equality
                             a1 a2 b1 b2
                             x1 x2 y
                             i
                             H).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_isect_equality_true3.
Qed.

Lemma rule_isect_equality_true {o} :
  forall lib (a1 a2 b1 b2 : NTerm),
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses o,
    rule_true lib (rule_isect_equality
                     a1 a2 b1 b2
                     x1 x2 y
                     i
                     H).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_isect_equality_true3.
Qed.

(* begin hide *)

Lemma rule_isect_equality_true_ex {o} :
  forall lib y i a1 a2 b1 b2 x1 x2 H,
    @rule_true_if o lib (rule_isect_equality a1 a2 b1 b2 x1 x2 y i H).
Proof.
  intros.
  generalize (rule_isect_equality_true lib a1 a2 b1 b2 x1 x2 y i H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Lemma rule_isect_equality_true2 {o} :
  forall lib (y : NVar),
  forall i : nat,
  forall a1 a2 b1 b2 : NTerm,
  forall x1 x2 : NVar,
  forall H   : @barehypotheses o,
    rule_true2 lib (rule_isect_equality
                  a1 a2 b1 b2
                  x1 x2 y
                  i
                  H).
Proof.
  introv.
  apply rule_true_iff_rule_true2; auto.
  apply rule_isect_equality_true; auto.
Qed.

Lemma rule_isect_equality_wf {o} :
  forall y : NVar,
  forall i : nat,
  forall a1 a2 b1 b2 : NTerm,
  forall x1 x2 : NVar,
  forall H   : @barehypotheses o,
  forall c1  : !LIn y (vars_hyps H),
    wf_rule (rule_isect_equality
               a1 a2 b1 b2
               x1 x2 y
               i
               H).
Proof.
  introv c1.
  introv pwf m.

  allsimpl; repdors; sp; subst; allunfold @pwf_sequent; wfseq;
  allapply @wf_isect_iff; repnd; auto;
  allrw @covered_isect; repnd; auto;
  try (apply subst_preserves_wf_term; auto);
  try (apply @covered_subst; try (apply @covered_var; rw in_snoc; sp));
  try (complete (rw cons_snoc; apply @covered_snoc_weak; auto)).

  allrw @vswf_hypotheses_nil_eq.
  apply wf_hypotheses_snoc; simpl; dands; auto.
  apply isprog_vars_eq; dands; auto.
  apply nt_wf_eq; auto.
Qed.

Lemma rule_isect_equality_wf2 {o} :
  forall y : NVar,
  forall i : nat,
  forall a1 a2 b1 b2 : NTerm,
  forall x1 x2 : NVar,
  forall H   : @barehypotheses o,
  forall c1  : !LIn y (vars_hyps H),
    wf_rule2 (rule_isect_equality
                a1 a2 b1 b2
                x1 x2 y
                i
                H).
Proof.
  introv c1 pwf m.

  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq;
  allapply @wf_isect_iff; repnd; auto;
  allrw @covered_isect; repnd; auto;
  try (apply subst_preserves_wf_term; auto);
  try (apply @covered_subst; try (apply @covered_var; rw in_snoc; sp));
  try (complete (rw cons_snoc; apply @covered_snoc_weak; auto)).

  allrw @vswf_hypotheses_nil_eq.
  apply wf_hypotheses_snoc; simpl; dands; auto.
  apply isprog_vars_eq; dands; auto.
  apply nt_wf_eq; auto.
Qed.


(* Another version that doesn't force the subgoals to have a given extract (axiom here) *)

Definition rule_isect_equality2_hyp1 {o} a1 a2 e1 i (H : @bhyps o) :=
  mk_baresequent H (mk_concl (mk_equality a1 a2 (mk_uni i)) e1).

Definition rule_isect_equality2_hyp2 {o} a1 b1 b2 e2 x1 x2 y i (H : @bhyps o) :=
  mk_baresequent
    (snoc H (mk_hyp y a1))
    (mk_concl
       (mk_equality
          (subst b1 x1 (mk_var y))
          (subst b2 x2 (mk_var y))
          (mk_uni i))
       e2).

Definition rule_isect_equality2 {o}
           (a1 a2 b1 b2 : @NTerm o)
           (e1 e2 : NTerm)
           (x1 x2 y : NVar)
           (i   : nat)
           (H   : barehypotheses) :=
  mk_rule
    (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
    [ rule_isect_equality2_hyp1 a1 a2 e1 i H,
      rule_isect_equality2_hyp2 a1 b1 b2 e2 x1 x2 y i H
    ]
    [ sarg_var y ].

Lemma rule_isect_equality2_true3 {o} :
  forall lib (a1 a2 b1 b2 : NTerm) e1 e2,
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses o,
    rule_true3 lib (rule_isect_equality2
                      a1 a2 b1 b2
                      e1 e2
                      x1 x2 y
                      i
                      H).
Proof.
  intros.
  apply (rule_tyfam_equality2_true3 _ _ mkc_isect); auto.

  - introv; simpl; allrw remove_nvars_nil_l; allrw app_nil_r; auto.

  - introv; apply lsubstc_mk_isect_ex.

  - introv; apply equality_isect.
Qed.

Lemma rule_isect_equality2_true_ext_lib {o} :
  forall lib (a1 a2 b1 b2 : NTerm) e1 e2,
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses o,
    rule_true_ext_lib lib (rule_isect_equality2
                             a1 a2 b1 b2
                             e1 e2
                             x1 x2 y
                             i
                             H).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_isect_equality2_true3.
Qed.

Lemma rule_isect_equality2_true {o} :
  forall lib (a1 a2 b1 b2 : NTerm) e1 e2,
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses o,
    rule_true lib (rule_isect_equality2
                     a1 a2 b1 b2
                     e1 e2
                     x1 x2 y
                     i
                     H).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_isect_equality2_true3.
Qed.

Lemma rule_isect_equality2_true_ex {o} :
  forall lib y i a1 a2 b1 b2 e1 e2 x1 x2 H,
    @rule_true_if o lib (rule_isect_equality2 a1 a2 b1 b2 e1 e2 x1 x2 y i H).
Proof.
  intros.
  generalize (rule_isect_equality2_true lib a1 a2 b1 b2 e1 e2 x1 x2 y i H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Lemma rule_isect_equality2_true2 {o} :
  forall lib (y : NVar),
  forall i : nat,
  forall a1 a2 b1 b2 : NTerm,
  forall e1 e2,
  forall x1 x2 : NVar,
  forall H   : @barehypotheses o,
    rule_true2 lib (rule_isect_equality2
                      a1 a2 b1 b2
                      e1 e2
                      x1 x2 y
                      i
                      H).
Proof.
  introv.
  apply rule_true_iff_rule_true2; auto.
  apply rule_isect_equality2_true; auto.
Qed.

Lemma rule_isect_equality2_wf {o} :
  forall y : NVar,
  forall i : nat,
  forall a1 a2 b1 b2 : NTerm,
  forall e1 e2,
  forall x1 x2 : NVar,
  forall H   : @barehypotheses o,
  forall c1  : !LIn y (vars_hyps H),
  forall w1  : wf_term e1,
  forall w2  : wf_term e2,
    wf_rule (rule_isect_equality2
               a1 a2 b1 b2
               e1 e2
               x1 x2 y
               i
               H).
Proof.
  introv c1 w1 w2 pwf m.

  allsimpl; repdors; sp; subst; allunfold @pwf_sequent; wfseq;
  allapply @wf_isect_iff; repnd; auto;
  allrw @covered_isect; repnd; auto;
  try (apply subst_preserves_wf_term; auto);
  try (apply @covered_subst; try (apply @covered_var; rw in_snoc; sp));
  try (complete (rw cons_snoc; apply @covered_snoc_weak; auto)).

  allrw @vswf_hypotheses_nil_eq.
  apply wf_hypotheses_snoc; simpl; dands; auto.
  apply isprog_vars_eq; dands; auto.
  apply nt_wf_eq; auto.
Qed.

Lemma rule_isect_equality2_wf2 {o} :
  forall y : NVar,
  forall i : nat,
  forall a1 a2 b1 b2 : NTerm,
  forall e1 e2,
  forall x1 x2 : NVar,
  forall H   : @barehypotheses o,
  forall c1  : !LIn y (vars_hyps H),
    wf_rule2 (rule_isect_equality2
                a1 a2 b1 b2
                e1 e2
                x1 x2 y
                i
                H).
Proof.
  introv c1 pwf m.

  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq;
  allapply @wf_isect_iff; repnd; auto;
  allrw @covered_isect; repnd; auto;
  try (apply subst_preserves_wf_term; auto);
  try (apply @covered_subst; try (apply @covered_var; rw in_snoc; sp));
  try (complete (rw cons_snoc; apply @covered_snoc_weak; auto)).

  allrw @vswf_hypotheses_nil_eq.
  apply wf_hypotheses_snoc; simpl; dands; auto.
  apply isprog_vars_eq; dands; auto.
  apply nt_wf_eq; auto.
Qed.

(* end hide *)
