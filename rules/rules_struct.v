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

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)




(* end hide *)

(**

  We now prove the truth of several structural rules.

*)

(* [1] ============ THIN HYPS ============ *)

(**

  The following rule says that we can always thin any tail of a list of hypotheses:
<<
   H, J |- C ext t

     By thinHyps ()

     H |- C ext t
>>
 *)
Definition rule_thin_hyps {o}
           (H J  : @barehypotheses o)
           (C t  : NTerm) :=
  mk_rule
    (mk_baresequent (H ++ J) (mk_concl C t))
    [ mk_baresequent H (mk_concl C t) ]
    [].

Lemma rule_thin_hyps_true {o} :
  forall lib (H J  : @barehypotheses o)
         (C t  : NTerm),
    rule_true lib (rule_thin_hyps H J C t).
Proof.
  intros.
  unfold rule_thin_hyps, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  duplicate wfh as wfh'.
  allapply @vswf_hypotheses_nil_implies.
  allrw @wf_hypotheses_app.
  destruct wfh as [ wfh wfj ].
  generalize (hyps (mk_baresequent H (mk_concl C t)) (inl eq_refl));
    intro hyp1; clear hyps.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl.
  proof_irr.

  assert (closed_extract (H ++ J) (mk_concl C t)) as ws
         by (wfseq; apply covered_app_weak_l; auto).
  exists ws.

  (* We prove some simple facts on our sequents *)
  assert (covered C (vars_hyps H)
          # covered t (nh_vars_hyps H)
          # disjoint (free_vars C) (vars_hyps J)
          # disjoint (free_vars t) (vars_hyps J)) as vhyps.

  clear hyp1.
  dwfseq; sp;
  try (complete (rw fold_subset in ct;
                 apply subset_disjoint with (l3 := vars_hyps J) in ct; sp)).
  try (complete (rw fold_subset in ce;
                 apply subset_disjoint with (l1 := nh_vars_hyps H) in wfj0; sp;
                 apply subset_disjoint with (l3 := vars_hyps J) in ce; sp)).

  destruct vhyps as [ cch vhyps ].
  destruct vhyps as [ cth vhyps ].
  destruct vhyps as [ dcj dtj ].
  (* done with proving these simple facts *)

  (* we can now start proving that the rule is true *)
  vr_seq_true.

  vr_seq_true in hyp1.

  allrw @similarity_app; exrepd; subst.

  generalize (hyp1 s1a s2a); clear hyp1; intro hyp1.

  autodimp hyp1 hyp.
  intros s2 sim.
  apply @hyps_functionality_init_seg with (s1b := s1b) (J := J) (s3 := s2b) in sim; auto.

  autodimp hyp1 hyp; exrepd.

  assert (disjoint (free_vars C) (dom_csub s1b)) as d1
         by (allapply @similarity_dom; sp;
             rterm (dom_csub s1b); rewrite vars_hyps_substitute_hyps; sp).
  assert (disjoint (free_vars C) (dom_csub s2b)) as d2
         by (allapply @similarity_dom; sp;
             rterm (dom_csub s2b); rewrite vars_hyps_substitute_hyps; sp).

  assert (disjoint (free_vars t) (dom_csub s1b)) as dt1
         by (allapply @similarity_dom; sp;
             rterm (dom_csub s1b); rewrite vars_hyps_substitute_hyps; sp).
  assert (disjoint (free_vars t) (dom_csub s2b)) as dt2
         by (allapply @similarity_dom; sp;
             rterm (dom_csub s2b); rewrite vars_hyps_substitute_hyps; sp).

  generalize (subset_free_vars_lsubstc_app_ex C s1a s1b wfct pC1 d1); intro; exrepd; clear_irr.
  rewrite e0; clear e0.

  generalize (subset_free_vars_lsubstc_app_ex C s2a s2b wfct pC2 d2); intro; exrepd; clear_irr.
  rewrite e0; clear e0.

  generalize (subset_free_vars_lsubstc_app_ex t s1a s1b wfce pt1 dt1); intro; exrepd; clear_irr.
  rewrite e0; clear e0.

  generalize (subset_free_vars_lsubstc_app_ex t s2a s2b wfce pt2 dt2); intro; exrepd; clear_irr.
  rewrite e0; clear e0.

  auto.
Qed.

(* begin hide *)

Lemma rule_thin_hyps_true_ex {o} :
  forall lib (H : @bhyps o) J c t,
    rule_true_if lib (rule_thin_hyps H J c t).
Proof.
  intros.
  generalize (rule_thin_hyps_true lib H J c t); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Lemma rule_thin_hyps_true2 {o} :
  forall lib (H : @bhyps o) J c t,
    rule_true2 lib (rule_thin_hyps H J c t).
Proof.
  intros.
  generalize (rule_thin_hyps_true lib H J c t); intro rt.
  apply rule_true_iff_rule_true2; sp.
Qed.

Lemma rule_thin_hyps_wf {o} :
  forall (H : @bhyps o) J c t,
    covered c (vars_hyps H)
    -> wf_rule (rule_thin_hyps H J c t).
Proof.
  intros.
  introv pwf m; allsimpl; repdors; subst; sp.
  allunfold @pwf_sequent; wfseq; sp.
  allapply @vswf_hypotheses_nil_implies.
  allrw @wf_hypotheses_app; sp.
  allapply @vswf_hypotheses_nil_if; sp.
Qed.


(* end hide *)

(* [2] ============ UNHIDE EQUALITY ============ *)

(**

  The following rule says that we can always unhide an hypothesis if
  the conclusion is an equality (in general this is true if the
  conclusion has a trivial extract):
<<
   H [x : A] J |- t1 = t2 in C

     By equalityUnhide hyp(i) ()

     H x : A J |- t1 = t2 in C
>>
 *)

Definition rule_unhide_equality {o}
           (H J  : @barehypotheses o)
           (A C t1 t2 : NTerm)
           (x    : NVar) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hhyp x A) ++ J)
       (mk_conclax (mk_equality t1 t2 C)))
    [ mk_baresequent
        (snoc H (mk_hyp x A) ++ J)
        (mk_conclax (mk_equality t1 t2 C)) ]
    [].

Lemma rule_unhide_equality_true {o} :
  forall (lib : library)
         (H J  : @barehypotheses o)
         (A C t1 t2 : NTerm)
         (x    : NVar),
    rule_true lib (rule_unhide_equality H J A C t1 t2 x).
Proof.
  intros.
  unfold rule_unhide_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  duplicate wfh as wfh'.
  allapply @vswf_hypotheses_nil_implies.
  allrw @wf_hypotheses_app; allrw @wf_hypotheses_snoc; allsimpl.
  destruct wfh as [ wfh wfj ].
  destruct wfh as [ ipa wfh ].
  destruct wfh as [ nixh wfh ].
  allrw @vars_hyps_snoc; allsimpl.
  generalize (hyps (mk_baresequent (snoc H (mk_hyp x A) ++ J)
                                  (mk_conclax (mk_equality t1 t2 C)))
                   (inl eq_refl));
    clear hyps; allsimpl; intro hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr.

  exists (@covered_axiom o (nh_vars_hyps (snoc H (mk_hhyp x A) ++ J))).

  (* We prove some simple facts on our sequents *)
  assert (covered (mk_equality t1 t2 C) (snoc (vars_hyps H) x ++ vars_hyps J))
    as vhyps.

  clear hyp1.
  dwfseq; sp.
  allrw in_app_iff; allrw in_snoc; sp;
  apply_in_hyp p; allrw in_app_iff; allrw in_snoc; sp.
  (* done with proving these simple facts *)

  (* we can now start proving that the rule is true *)
  vr_seq_true.

  vr_seq_true in hyp1.

  generalize (hyp1 s1 s2); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  intros s3 sim3.
  rw @similarity_hhyp in sim3; rw @eq_hyps_hhyp.
  apply eqh; sp.

  autodimp hyp1 hyp; exrepd; clear_irr; auto.
  rw @similarity_hhyp; auto.
Qed.

(* begin hide *)



(* end hide *)

(* [4] ============ HYPOTHESIS EQUALITY ============ *)

(**

  The following rule is the standard ``hypothesis'' rule:
<<
   G, x : A, J |- x = x in A

     By hypothesisEquality hyp(i) ()

     no subgoals
>>
 *)

Definition rule_hypothesis_equality {o}
             (G J : @barehypotheses o)
             (A   : NTerm)
             (x   : NVar) :=
  mk_rule
    (mk_baresequent
       (snoc G (mk_hyp x A) ++ J)
       (mk_concl_eq (mk_var x) (mk_var x) A))
    []
    [].

Lemma rule_hypothesis_equality_true {o} :
  forall lib (G J : @barehypotheses o)
         (A : NTerm)
         (x : NVar),
    rule_true lib (rule_hypothesis_equality G J A x).
Proof.
  intros.
  unfold rule_hypothesis_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  clear hyps.
  destseq; allsimpl.
  duplicate wfh as wfh'.
  allunfold @closed_type; allunfold @closed_extract; allsimpl.
  allapply @vswf_hypotheses_nil_implies.
  allrw @wf_hypotheses_app.
  destruct wfh as [ wfh wfj ].
  allrw @wf_hypotheses_snoc.
  destruct wfh as [ ispvg wfh ].
  destruct wfh as [ nixg wfg ].
  allrw @nh_vars_hyps_snoc; allsimpl.
  allrw @vars_hyps_snoc; allsimpl.
  duplicate cg as ceq.
  allrw @covered_equality.
  destruct cg as [ cx ct ].
  destruct ct as [ cx2 ca ]; GC.
  allrw @vars_hyps_app; allsimpl.
  allrw @vars_hyps_snoc; allsimpl.
  duplicate wfct as wfct'.
  rw <- @wf_equality_iff in wfct.
  destruct wfct as [ wa wtt ].
  destruct wtt as [ wb wtA ].

  match goal with
  | [ |- context[covered ?a ?b] ] => assert (covered a b) as cov
  end.
  { apply covered_refl.
    apply covered_var; simpl.
    rw @nh_vars_hyps_app.
    rw @nh_vars_hyps_snoc; simpl.
    rw in_app_iff.
    rw in_snoc; tcsp. }
  exists cov.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars A)
          # !LIn x (vars_hyps J)
          # subset (free_vars A) (vars_hyps G)
          # disjoint (free_vars A) (vars_hyps J)) as vhyps.

  {
    dwfseq.
    sp;
      try (complete (apply subset_disjoint with (l1 := free_vars A) in wfj2; auto;
                     apply subset_snoc_r; sp)).
  }

  destruct vhyps as [ nixa vhyps ].
  destruct vhyps as [ nixj vhyps ].
  destruct vhyps as [ sag daj ].
  (* done with proving these simple facts *)

  vr_seq_true.

  lift_lsubst.

  repeat (rewrite fold_mkc_member).
  rw @equality_in_member.
  rw @tequality_mkc_member.

  applydup eqh in sim; clear eqh.
  allrw @similarity_app; exrepd; subst; cpx.
  allrw @similarity_snoc; exrepd; subst; cpx.
  revert c1 cT c0 cT0; rewrite hvar_mk_hyp; intros.
  allrw @eq_hyps_app; exrepd; simphyps; cpx.
  apply app_split in e; repd; subst; allrewrite length_snoc; try omega; cpx; GC.
  apply app_split in e0; repd; subst; allrewrite length_snoc; try omega; cpx; GC.
  allrw @eq_hyps_snoc; exrepd; cpx; simphyps; cpx; GC; clear_irr.

  assert (disjoint (free_vars (@mk_var o x)) (dom_csub s1b0)) as dxs1
         by (simpl; rw disjoint_singleton_l;
             allapply @similarity_dom; repd; rterm (dom_csub s1b0);
             rewrite vars_hyps_substitute_hyps; auto).

  assert (disjoint (free_vars (@mk_var o x)) (dom_csub s2b0)) as dxs2
         by (simpl; rw disjoint_singleton_l;
             allapply @similarity_dom; repd; rterm (dom_csub s2b0);
             rewrite vars_hyps_substitute_hyps; auto).

  assert (disjoint (free_vars A) (dom_csub s1b0)) as das1
         by (allapply @similarity_dom; repd; rterm (dom_csub s1b0);
             rewrite vars_hyps_substitute_hyps; auto).

  assert (disjoint (free_vars A) (dom_csub s2b0)) as das2
         by (allapply @similarity_dom; repd; rterm (dom_csub s2b0);
             rewrite vars_hyps_substitute_hyps; auto).

  generalize (subset_free_vars_lsubstc_app_ex
                (mk_var x)
                (snoc s1a (x, t0)) s1b0
                w1 c1 dxs1); intro; exrepd; rewrite e; clear e.

  generalize (subset_free_vars_lsubstc_app_ex
                (mk_var x)
                (snoc s2a (x, t3)) s2b0
                w1 c0 dxs2); intro; exrepd; rewrite e; clear e.

  generalize (subset_free_vars_lsubstc_app_ex
                A
                (snoc s1a (x, t0)) s1b0
                wtA cT das1); intro; exrepd; rewrite e; clear e.

  generalize (subset_free_vars_lsubstc_app_ex
                A
                (snoc s2a (x, t3)) s2b0
                wtA cT0 das2); intro; exrepd; rewrite e; clear e.

  lsubst_tac.

  sp; eauto 2 with slow.

  { apply tequality_implies_eq_members_upto; auto. }

  exists t0 t3; dands; spcast; try (apply computes_to_valc_refl; eauto 2 with slow);
    eauto 3 with slow nequality.
Qed.

(* begin hide *)



(* end hide *)

(* [5] ============ INTRODUCTION ============ *)

(**

  The following rule says that to prove a conclusion [C] one can
  always provide an evidence [t] for that type and prove instead that
  [t] is a member of [C]:
<<
   H |- C ext t

     By introduction t

     H |- t = t in C
>>
 *)

Definition rule_introduction_concl {o} (H : @bhyps o) C t :=
  mk_baresequent H (mk_concl C t).

Definition rule_introduction_hyp {o} (H : @bhyps o) C t :=
  mk_baresequent H (mk_concl_eq t t C).

Definition rule_introduction {o}
             (H : @barehypotheses o)
             (C t : NTerm) :=
  mk_rule
    (rule_introduction_concl H C t)
    [ rule_introduction_hyp H C t ]
    [ sarg_term t ].

Lemma rule_introduction_true3 {o} :
  forall lib
         (H : @barehypotheses o)
         (C t : NTerm),
    rule_true3 lib (rule_introduction H C t).
Proof.
  intros.
  unfold rule_introduction, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
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

  assert (wf_csequent (rule_introduction_concl H C t)) as wfc.
  { clear hyp1.
    unfold wf_csequent, wf_sequent, wf_concl; simpl; dands; auto.
    allrw <- @wf_equality_iff; sp. }
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; repnd; allsimpl; proof_irr; GC.

  vr_seq_true.

  vr_seq_true in hyp1.

  generalize (hyp1 s1 s2); clear hyp1; intro hyp1.
  autodimp hyp1 h.
  autodimp hyp1 h.
  exrepd.

  lift_lsubst in t0; lift_lsubst in e; clear_irr.

  rw @tequality_mkc_equality in t0; repnd.
  apply equality_mkc_equality_implies in e; exrepnd.
  spcast; computes_to_value_isvalue.

  dands; auto.

  apply tequality_iff_ext_eq; dands; auto.
  introv.

XXXXXXXXXX

  allrewrite @lsubstc_mk_axiom.
  allrewrite @member_eq.
  allrewrite @fold_mkc_member.
  rw <- @member_member_iff in e.

  spcast; apply @equality_respects_cequivc_right with (t2 := lsubstc t wfc0 s1 pt1); sp.
Qed.

Lemma rule_introduction_true {o} :
  forall lib
         (H : @barehypotheses o)
         (C t : NTerm),
    rule_true lib (rule_introduction H C t).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_introduction_true3.
Qed.

Lemma rule_introduction_wf2 {o} :
  forall (H : @barehypotheses o) (C t : NTerm),
    wf_term t
    -> covered t (vars_hyps H)
    -> wf_rule2 (rule_introduction H C t).
Proof.
  introv wt cov wf m; allsimpl.
  repndors; subst; tcsp.
  allunfold @wf_bseq; allsimpl; repnd; dands; auto.
  - apply wf_equality; auto.
  - allunfold @closed_type_baresequent; allsimpl.
    allunfold @closed_type; allsimpl.
    apply covered_equality; dands; auto.
Qed.

(* begin hide *)



(* end hide *)

(* [6] ============ HYPOTHESIS ============ *)

(**

  The following rule is another form of the standard ``hypothesis''
  rule:
<<
   G, x : A, J |- A ext x

     By hypothsis hyp(i) ()

     no subgoals
>>
 *)

Definition rule_hypothesis_concl {o} (G J : @bhyps o) A x :=
  mk_baresequent (snoc G (mk_hyp x A) ++ J) (mk_concl A (mk_var x)).

Definition rule_hypothesis {o}
             (G J : @barehypotheses o)
             (A   : NTerm)
             (x   : NVar) :=
  mk_rule (rule_hypothesis_concl G J A x) [] [].

Lemma rule_hypothesis_true3 {o} :
  forall lib (G J : @barehypotheses o)
         (A : NTerm)
         (x : NVar),
    rule_true3 lib (rule_hypothesis G J A x).
Proof.
  intros.
  unfold rule_hypothesis, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs hyps.
  destseq; allsimpl.

  assert (wf_csequent (rule_hypothesis_concl G J A x)) as wfc.
  { unfold wf_csequent, wf_sequent, wf_concl; simpl; dands; eauto 3 with slow.
    - apply vswf_hypotheses_nil_eq; auto.
    - unfold closed_extract; simpl.
      rw @nh_vars_hyps_app.
      rw @nh_vars_hyps_snoc; simpl.
      unfold covered.
      rw subvars_eq; simpl.
      apply subset_cons_l; dands; auto.
      rw in_app_iff; rw in_snoc; tcsp. }
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; repnd; allsimpl; proof_irr; GC.

  vr_seq_true.

  pose proof (eqh s2 sim) as h.
  apply eq_hyps_app in h; exrepnd; subst.
  apply eq_hyps_snoc in h5; exrepnd; subst.
  allrw length_snoc; cpx.
  allsimpl.

  applydup @wf_hypotheses_disj in wf0; repnd.

  assert (disjoint (free_vars A) (dom_csub s1b)) as d1.
  { applydup @sub_eq_hyps_dom in h1; repnd.
    rw h5; auto. }

  assert (disjoint (free_vars A) (dom_csub s2b)) as d2.
  { applydup @sub_eq_hyps_dom in h1; repnd.
    rw h2; auto. }

  lsubst_tac.
  dands; auto;[].

  applydup @eq_hyps_length in h6; repnd.

  apply similarity_app in sim; exrepnd.
  apply app_split in sim0; allrw length_snoc; auto; try omega.
  apply app_split in sim2; allrw length_snoc; auto; try omega.
  repnd; subst.

  apply similarity_snoc in sim5; exrepnd; cpx; allsimpl.
  ginv; proof_irr; auto.
Qed.

Lemma rule_hypothesis_true {o} :
  forall lib (G J : @barehypotheses o)
         (A : NTerm)
         (x : NVar),
    rule_true lib (rule_hypothesis G J A x).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_hypothesis_true3.
Qed.

Lemma rule_hypothesis_wf2 {o} :
  forall (G J : @barehypotheses o)
         (A : NTerm)
         (x : NVar),
    wf_rule (rule_hypothesis G J A x).
Proof.
  introv wf i; allsimpl; tcsp.
Qed.


(* begin hide *)



(* end hide *)

(* [7] ============ THIN ============ *)

(**

  The following rule says that one can always delete (or thin) an
  hypothesis (as long as [J] does not depend on [x], because [H, J]
  has to be well-formed):

<<
   H, x : A, J |- C ext t

     By thin hyp(i) ()

     H, J |- C ext t
>>

 *)

Definition rule_thin {o}
           (G J : @barehypotheses o)
           (A C t : NTerm)
           (x   : NVar) :=
  mk_rule
    (mk_baresequent (snoc G (mk_hyp x A) ++ J) (mk_concl C t))
    [ mk_baresequent (G ++ J) (mk_concl C t) ]
    [].

Lemma rule_thin_true {o} :
  forall lib (G J : @barehypotheses o)
         (A C t : NTerm)
         (x   : NVar),
    rule_true lib (rule_thin G J A C t x).
Proof.
  intros.
  unfold rule_thin, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  duplicate wfh as wfh'.
  allapply @vswf_hypotheses_nil_implies.
  allrw @wf_hypotheses_app.
  destruct wfh as [ wfh wfj ].
  allrw @wf_hypotheses_snoc.
  destruct wfh as [ ispvg wfh ].
  destruct wfh as [ nixg wfg ].
  allrw @vars_hyps_app; allsimpl.
  allrw @vars_hyps_snoc; allsimpl; GC.

  generalize (hyps (mk_baresequent (G ++ J) (mk_concl C t)) (inl (eq_refl)));
    clear hyps; intro hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (covered t (nh_vars_hyps (snoc G (mk_hyp x A) ++ J))) as ws
         by (clear hyp1; prove_seq; apply covered_snoc_app_weak; auto).
  exists ws; GC.

  (* We prove some simple facts on our sequents *)
  assert (! LIn x (free_vars C)
          # ! LIn x (free_vars t)
          # ! LIn x (vars_hyps J)
          # ! LIn x (free_vars_hyps J)
          # ! LIn x (hyps_free_vars J)) as vhyps.

  clear hyp1.
  dwfseq.
  sp;
    try (complete (apply ct in X; allrw in_app_iff; sp));
    try (complete (apply ce in X; allrw in_app_iff; sp;
                   generalize (subvars_hs_vars_hyps G); intro sv1; allrw subvars_prop;
                   generalize (subvars_hs_vars_hyps J); intro sv2; allrw subvars_prop; sp));
    try (complete (apply wfh in X; allrw in_app_iff; sp)).

  destruct vhyps as [ nixc vhyps ].
  destruct vhyps as [ nixt vhyps ].
  destruct vhyps as [ nixj1 vhyps ].
  destruct vhyps as [ nixj2 nixj3 ].
  (* done with proving these simple facts *)

  vr_seq_true.

  rw @similarity_app in sim; exrepd; subst; cpx.
  rw @similarity_snoc in s; exrepd; subst; allsimpl; cpx.

  vr_seq_true in hyp1.

  generalize (hyp1 (s1a0 ++ s1b) (s2a0 ++ s2b)); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  intros s3 sim3.
  rw @similarity_app in sim3; exrepnd; subst.
  apply app_split in sim0; sp; subst;
  try (complete (allapply @similarity_length; sp; omega)).
  generalize (eqh (snoc s2a (x, t1) ++ s2b0)); intro h.
  autodimp h hyp.

  rw @similarity_app.
  exists (snoc s1a (x, t1)) s1b0 (snoc s2a (x, t1)) s2b0; simpl; sp;
  allrewrite length_snoc; sp.

  rw @similarity_snoc; simpl.
  exists s1a s2a t1 t1 w p; sp.
  rewrite member_eq.
  allapply @equality_refl; sp.

  rewrite substitute_hyps_snoc_sub_weak; sp.

  rw @eq_hyps_app in h; exrepnd.
  apply app_split in h0; apply app_split in h2; sp; subst;
  allrewrite length_snoc; sp;
  try (complete (allapply @similarity_length; sp; omega)).
  allrw @eq_hyps_snoc; exrepnd; allsimpl; cpx; GC.

  rw @eq_hyps_app.
  exists s1a0 s1b s2a1 s2b1; sp.
  apply sub_eq_hyps_snoc_weak_iff in h1; sp.

  clear_irr.
  autodimp hyp1 hyp.
  rw @similarity_app.
  exists s1a0 s1b s2a0 s2b; sp.
  rewrite substitute_hyps_snoc_sub_weak in s0; sp.
  exrepd; clear_irr.

  assert (lsubstc C wfct (snoc s1a0 (x, t1) ++ s1b) pC1
          = lsubstc C wfct (s1a0 ++ s1b) pC0) as eq1;
    try (rewrite eq1).

  apply lsubstc_eq_if_csubst; sp.
  apply subset_free_vars_csub_snoc_app; sp.

  assert (lsubstc C wfct (snoc s2a0 (x, t2) ++ s2b) pC2
          = lsubstc C wfct (s2a0 ++ s2b) pC3) as eq2;
    try (rewrite eq2).

  apply lsubstc_eq_if_csubst; sp.
  apply subset_free_vars_csub_snoc_app; sp.

  assert (lsubstc t wfce (snoc s1a0 (x, t1) ++ s1b) pt1
          = lsubstc t wfce (s1a0 ++ s1b) pt0) as eq3;
    try (rewrite eq3).

  apply lsubstc_eq_if_csubst; sp.
  apply subset_free_vars_csub_snoc_app; sp.

  assert (lsubstc t wfce (snoc s2a0 (x, t2) ++ s2b) pt2
          = lsubstc t wfce (s2a0 ++ s2b) pt3) as eq4;
    try (rewrite eq4).

  apply lsubstc_eq_if_csubst; sp.
  apply subset_free_vars_csub_snoc_app; sp.

  sp.
Qed.

(* begin hide *)



(* end hide *)

(* [13] ============ WIDENING ============ *)

(**

  The following rule state that if we are trying to prove a goal under
  the assumption that [x] has type [T], then it suffices to prove the
  goal under the hypothesis that [x] has type [U], as long as we can
  prove that [T] is a subtype of [U], and [T] respects the equality of
  [U] on the elements of [T]:

<<
  H, x : T, J |- C ext t

     By widening y z i

     H, x : U, J |- C ext t
     H, x : T, y : U, z : x = y in U |- x = y in T
     H, x : T |- x in U
>>
 *)

Definition rule_widening {o}
           (T U C t : @NTerm o)
           (x y z : NVar)
           (i : nat)
           (H J : barehypotheses) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x T) ++ J)
       (mk_concl C t))
    [ mk_baresequent (snoc H (mk_hyp x U) ++ J)
                    (mk_concl C t),
      mk_baresequent (snoc (snoc (snoc H (mk_hyp x T))
                                (mk_hyp y U))
                          (mk_hyp z (mk_equality (mk_var x) (mk_var y) U)))
                    (mk_conclax (mk_equality (mk_var x) (mk_var y) T)),
      mk_baresequent (snoc H (mk_hyp x T))
                    (mk_conclax (mk_member (mk_var x) U))
    ]
    [sarg_var y, sarg_var z].

Lemma rule_widening_true {o} :
  forall lib (T U C t : NTerm)
         (x y z : NVar)
         (i : nat)
         (H J : @barehypotheses o),
    rule_true lib
              (rule_widening
                 T U C t
                 x y z
                 i
                 H J).
Proof.
  unfold rule_widening, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent
                      (snoc H (mk_hyp x U) ++ J)
                      (mk_concl C t))
                   (inl eq_refl))
             (hyps (mk_baresequent
                      (snoc (snoc (snoc H (mk_hyp x T)) (mk_hyp y U))
                            (mk_hyp z (mk_equality (mk_var x) (mk_var y) U)))
                      (mk_conclax (mk_equality (mk_var x) (mk_var y) T)))
                   (inr (inl eq_refl)))
             (hyps (mk_baresequent
                      (snoc H (mk_hyp x T))
                      (mk_conclax (mk_member (mk_var x) U)))
                   (inr (inr (inl eq_refl))));
    simpl; intros hyp1 hyp2 hyp3.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destruct hyp3 as [ ws3 hyp3 ].
  destseq; allsimpl; proof_irr; GC.
  clear hyps.

  assert (covered t (nh_vars_hyps (snoc H (mk_hyp x T) ++ J)))
    as co
      by (duplicate ce1 as ce2;
          allrw @nh_vars_hyps_app;
          allrw @nh_vars_hyps_snoc;
          allsimpl; sp).

  exists co; GC.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps H)
           # !LIn x (free_vars T)
           # !LIn x (free_vars U)
           # !(x = y)
           # !LIn y (vars_hyps H)
           # !LIn y (free_vars T)
           # !LIn y (free_vars U)
           # !LIn z (vars_hyps H)
           # !LIn z (free_vars T)
           # !LIn z (free_vars U)
           # wf_term U
           # covered T (vars_hyps H)
           # covered U (vars_hyps H)) as vhyps.

  clear hyp1 hyp2 hyp3.
  dwfseq.

  sp; try (complete (unfold covered; rw subvars_prop; sp)).

  destruct vhyps as [ nixH vhyps ].
  destruct vhyps as [ nixT vhyps ].
  destruct vhyps as [ nixU vhyps ].
  destruct vhyps as [ nixy vhyps ].
  destruct vhyps as [ niyH vhyps ].
  destruct vhyps as [ niyT vhyps ].
  destruct vhyps as [ niyU vhyps ].
  destruct vhyps as [ nizH vhyps ].
  destruct vhyps as [ nizT vhyps ].
  destruct vhyps as [ nizU vhyps ].
  destruct vhyps as [ wfu vhyps ].
  destruct vhyps as [ covTH covUH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  (* we split s1 and s2 *)
  allrw @similarity_app; exrepd; subst; cpx.
  allrw @similarity_snoc; exrepd; subst; cpx.
  allsimpl.

  (* we use our 1st subgoal to prove that tequality *)
  vr_seq_true in hyp1.

  generalize (hyp1 (snoc s1a0 (x, t1) ++ s1b)
                   (snoc s2a0 (x, t2) ++ s2b));
    clear hyp1; intro hyp1.

  autodimp hyp1 h.

  introv sim.
  allrw @similarity_app; exrepd; subst; allsimpl; cpx.
  apply app_split in e; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  repeat (allrw @similarity_snoc; exrepd; subst; allsimpl; cpx; GC).

  rw @eq_hyps_app; simpl.
  exists (snoc s1a (x, t0)) s1b0 (snoc s2a1 (x, t3)) s2b0;
    allrw length_snoc; allrw; sp.

  assert (cover_vars U s2a1)
         as c2
         by (apply @cover_vars_dom_csub_eq with (s1 := s1a); sp;
             allrw @dom_csub_snoc; simpl;
             allapply @similarity_dom; repd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists s1a s2a1 t0 t3 w0 p0 c2; sp.

  generalize (eqh (snoc s2a1 (x, t2) ++ s2b)); intro imp.
  autodimp imp hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a (x, t0)) s1b0 (snoc s2a1 (x, t2)) s2b; repeat (rw length_snoc); sp.
  rw @similarity_snoc; simpl.
  exists s1a s2a1 t0 t2 w p; sp.

  rw @eq_hyps_app in imp; exrepnd.
  apply app_split in imp0; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  apply app_split in imp2; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  rw @eq_hyps_snoc in imp5; exrepnd; sp; cpx.

  generalize (eqh (snoc s2a1 (x, t2) ++ s2b)); intro imp.
  autodimp imp hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a (x, t0)) s1b0 (snoc s2a1 (x, t2)) s2b; repeat (rw length_snoc); sp.
  rw @similarity_snoc; simpl.
  exists s1a s2a1 t0 t2 w p; sp.

  rw @eq_hyps_app in imp; exrepnd.
  apply app_split in imp0; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  apply app_split in imp2; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  rw @eq_hyps_snoc in imp5; exrepnd; sp; cpx; allsimpl; cpx; clear_irr.

  (* from imp0 and sequent 3 *)
  generalize (subtype_tequality lib s1a0 s2a H T U x t1 t4 w w0 p1 p0 c2 (wfh0, (wfct0, wfce1), (ct, ce)));
    intro j; repeat (autodimp j hyp).
  apply hyps_functionality_init_seg with (s3 := s2b1) in eqh; sp.

  assert (cover_vars T s2a1)
    as c2
      by (apply @cover_vars_dom_csub_eq with (s1 := s1a); sp;
          allrw @dom_csub_snoc; simpl;
          allapply @similarity_dom; repd; allrw; sp).

  generalize (eqh (snoc s2a1 (x, t3) ++ s2b0)); intro j; autodimp j hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a (x, t0)) s1b0 (snoc s2a1 (x, t3)) s2b0; allrw length_snoc; sp.
  rw @similarity_snoc; simpl.
  exists s1a s2a1 t0 t3 w p; sp.

  generalize (strong_subtype_equality lib s1a s2a1 t0 t2 t3 T U w w0 p p0 c2 H x y z
                                      (wfh0, (wfct0, wfce1), (ct, ce))
                                      (wfh1, (wfct1, wfce1), (ct0, ce0)));
    intro q; repeat (destimp q hyp).
  repnd.
  apply hyps_functionality_init_seg with (s3 := s2b) in eqh; sp.
  apply @equality_commutes4 with (U := lsubstc T w s2a1 c2) (a2 := t0) (a3 := t2); sp.

  rw @eq_hyps_app in j; exrepnd.
  apply app_split in j0; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
  apply app_split in j2; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.

  (* we're done proving the hyps_functionality part for sequent 1 *)

  (* we now have to prove the similarity part *)

  autodimp hyp1 h.

  rw @similarity_app; simpl.
  exists (snoc s1a0 (x, t1)) s1b (snoc s2a0 (x, t2)) s2b; allrw length_snoc; sp.
  rw @similarity_snoc; simpl.

  assert (cover_vars U s1a0)
    as c1 by (allrw @cover_vars_covered; allapply @similarity_dom; exrepnd; allrw; sp).

  exists s1a0 s2a0 t1 t2 wfu c1; sp.

  generalize (subtype_equality lib t1 t2 T U  s1a0 s2a0 w wfu p c1 H x
                               (wfh0, (wfct0, wfce1), (ct, ce)));
    intro j; repeat (autodimp j hyp).
  apply hyps_functionality_init_seg with (s3 := s2b) in eqh; sp.

  exrepnd; clear_irr; sp.
Qed.

(* begin hide *)



(* end hide *)

(* [18] ============ CUT ============ *)

(**

  The following rule is the standard cut rule:
<<
   H |- C ext t[x\u]

     By cut x B

     H |- B ext u
     H, x : B |- C ext t
>>
 *)

Definition rule_cut_concl {o} (H : @bhyps o) C t x u :=
  mk_baresequent H (mk_concl C (subst t x u)).

Definition rule_cut_hyp1 {o} (H : @bhyps o) B u :=
  mk_baresequent H (mk_concl B u).

Definition rule_cut_hyp2 {o} (H : @bhyps o) x B C t :=
  mk_baresequent (snoc H (mk_hyp x B)) (mk_concl C t).

Definition rule_cut {o}
             (H : @barehypotheses o)
             (B C t u : NTerm)
             (x   : NVar) :=
  mk_rule
    (rule_cut_concl H C t x u)
    [ rule_cut_hyp1 H B u,
      rule_cut_hyp2 H x B C t
    ]
    [sarg_var x].

Lemma rule_cut_true3 {o} :
  forall lib (H : @barehypotheses o)
         (B C t u : NTerm)
         (x : NVar),
    rule_true3 lib (rule_cut H B C t u x).
Proof.
  unfold rule_cut, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  rename Hyp0 into hyp2.
  destruct hyp1 as [ws1 hyp1].
  destruct hyp2 as [ws2 hyp2].
  destseq; allsimpl; clear_irr; GC.

  assert (covered (subst t x u) (vars_hyps (filter is_nh H))) as cv.
  { clear hyp1 hyp2.
    dwfseq.
    introv i.
    pose proof (eqvars_free_vars_disjoint t [(x,u)]) as eqv.
    rw eqvars_prop in eqv.
    rw @fold_subst in eqv.
    rw eqv in i.
    rw in_app_iff in i; rw in_remove_nvars in i; allsimpl; sp.
    - apply not_over_or in p; sp.
      apply ce in p0.
      apply in_snoc in p0; sp.
    - allapply @in_sub_free_vars; sp.
      destruct (memvar x (free_vars t)); allsimpl; sp; cpx.
  }

  assert (wf_csequent (rule_cut_concl H C t x u)) as wfc.
  { unfold wf_csequent, wf_sequent, wf_concl; simpl; dands; auto.
    apply wf_term_subst; auto.
  }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  assert (! LIn x (free_vars B)
          # ! LIn x (free_vars C)
          # ! LIn x (free_vars u)
          # ! LIn x (vars_hyps H)
          # wf_term u
          # wf_term B
          # covered u (nh_vars_hyps H)
          # covered B (vars_hyps H)) as vhyps.

  { clear hyp1 hyp2.
    dwfseq.
    sp;
      try (complete (generalize (ce0 x); sp;
                     generalize (subset_hs_vars_hyps H); intro k;
                     apply k in X0; sp));
      try (complete (rw subvars_eq; unfold subset; sp)).
  }

  destruct vhyps as [ nixb vhyps ].
  destruct vhyps as [ nixc vhyps ].
  destruct vhyps as [ nixu vhyps ].
  destruct vhyps as [ nixh vhyps ].
  destruct vhyps as [ wu vhyps ].
  destruct vhyps as [ wb vhyps ].
  destruct vhyps as [ cuh cbh ].
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp2.

  assert (cover_vars u s1)
         as cu1
         by (rw @cover_vars_eq;
             unfold covered in ce0;
             insub;
             apply subvars_trans with (vs2 := nh_vars_hyps H); sp).

  assert (cover_vars u s2)
         as cu2
         by (rw @cover_vars_eq;
             unfold covered in ce0;
             insub;
             apply subvars_trans with (vs2 := nh_vars_hyps H); sp).

  generalize (hyp2
                (snoc s1 (x, lsubstc u wfce0 s1 cu1))
                (snoc s2 (x, lsubstc u wfce0 s2 cu2))); clear hyp2; intro hyp2.

  autodimp hyp2 hyp.
  { apply hyps_functionality_snoc2; simpl; auto.
    introv eq sim'; allsimpl.

    vr_seq_true in hyp1.
    generalize (hyp1 s1 s'); clear hyp1; intro hyp1.
    repeat (autodimp hyp1 hyp); exrepnd; clear_irr; sp.
  }

  assert (cover_vars B s1) as cvbs1 by (rw @cover_vars_eq; insub).

  autodimp hyp2 hyp.
  { sim_snoc; dands; auto.
    vr_seq_true in hyp1.
    generalize (hyp1 s1 s2); clear hyp1; intro hyp1.
    repeat (autodimp hyp1 hyp); exrepnd; clear_irr; sp.
  }

  exrepnd.
  lsubst_tac.
  dands; auto.

  repeat lsubstc_subst_aeq2.
  repeat substc_lsubstc_vars3.
  proof_irr.

  pose proof (lsubstc_snoc_move t s1 [] x (lsubstc u wfce0 s1 cu1) wfce) as e1.
  pose proof (lsubstc_snoc_move t s2 [] x (lsubstc u wfce0 s2 cu2) wfce) as e2.
  allrw app_nil_r.
  pose proof (e1 pt0) as k1; clear e1.
  pose proof (e2 pt3) as k2; clear e2.
  autodimp k1 hyp.
  { apply similarity_dom in sim; repnd; rw sim0; auto. }
  autodimp k2 hyp.
  { apply similarity_dom in sim; repnd; rw sim; auto. }
  exrepnd.
  proof_irr.
  rw <- k2; rw <- k0; auto.
Qed.

(* begin hide *)

Lemma rule_cut_true {o} :
  forall lib (H : @barehypotheses o)
         (B C t u : NTerm)
         (x : NVar),
    rule_true lib (rule_cut H B C t u x).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_cut_true3.
Qed.

Lemma rule_cut_true_ex {o} :
  forall lib (H : @bhyps o) B C t u x,
    rule_true_if lib (rule_cut H B C t u x).
Proof.
  intros.
  generalize (rule_cut_true lib H B C t u x); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Lemma rule_cut_true2 {o} :
  forall lib (H : @barehypotheses o)
         (B C t u : NTerm)
         (x : NVar),
    rule_true2 lib (rule_cut H B C t u x).
Proof.
  introv.
  apply rule_true_iff_rule_true2; sp.
  apply rule_cut_true.
Qed.

Lemma rule_cut_wf {o} :
  forall (H : @barehypotheses o)
         (B C t u : NTerm)
         (x : NVar),
    wf_term B
    -> wf_term u
    -> covered B (vars_hyps H)
    -> !LIn x (vars_hyps H)
    -> wf_rule (rule_cut H B C t u x).
Proof.
  introv wB wu covB nixH pwf m; allsimpl; repndors; subst; tcsp;
  allunfold @pwf_sequent; wfseq; tcsp.

  - apply vswf_hypotheses_snoc; dands; simpl; auto.
    apply isprog_vars_eq; dands; auto.
    apply nt_wf_eq; auto.

  - apply lsubst_wf_term in pwf0; auto.

  - apply covered_snoc_weak; auto.
Qed.

Lemma rule_cut_wf2 {o} :
  forall (H : @barehypotheses o)
         (B C t u : NTerm)
         (x : NVar),
    wf_term B
    -> covered B (vars_hyps H)
    -> !LIn x (vars_hyps H)
    -> wf_rule2 (rule_cut H B C t u x).
Proof.
  introv wB covB nixH pwf m; allsimpl; repndors; subst; tcsp;
  allunfold @wf_bseq; wfseq; tcsp.

  - apply vswf_hypotheses_snoc; dands; simpl; auto.
    apply isprog_vars_eq; dands; auto.
    apply nt_wf_eq; auto.

  - apply covered_snoc_weak; auto.
Qed.



(* end hide *)

(* [19] ============ CUTH ============ *)

(**

  This rule is similar to the cut rule, but is valid only if [x] is
  not free in the extract:

<<
   H |- C ext t

     By cutH x B

     H |- B ext u
     H, [x : B] |- C ext t
>>
 *)

Definition rule_cutH {o}
             (H : @barehypotheses o)
             (B C t u : NTerm)
             (x   : NVar) :=
  mk_rule
    (mk_baresequent H (mk_concl C t))
    [ mk_baresequent H (mk_concl B u),
      mk_baresequent (snoc H (mk_hhyp x B)) (mk_concl C t)
    ]
    [sarg_var x].

Lemma rule_cutH_true {o} :
  forall lib (H : @barehypotheses o)
         (B C t u : NTerm)
         (x : NVar),
    rule_true lib (rule_cutH H B C t u x).
Proof.
  unfold rule_cutH, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent H (mk_concl B u))
                   (inl eq_refl))
             (hyps (mk_baresequent (snoc H (mk_hhyp x B)) (mk_concl C t))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2; clear hyps.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (covered t (vars_hyps (filter is_nh H))) as cv.
  clear hyp1 hyp2.
  dwfseq.
  introv i.
  apply ce in i; sp.

  exists cv.

  (* We prove some simple facts on our sequents *)
  assert (! LIn x (free_vars B)
          /\ ! LIn x (free_vars C)
          /\ ! LIn x (free_vars u)
          /\ ! LIn x (vars_hyps H)
          /\ ! LIn x (free_vars t)
          /\ wf_term u
          /\ wf_term B
          /\  covered u (nh_vars_hyps H)
          /\  covered B (vars_hyps H)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp;
  try (complete (generalize (ce0 x); sp;
                 generalize (subset_hs_vars_hyps H); intro k;
                 apply k in X0; sp));
  try (complete (generalize (ce x); sp;
                 generalize (subset_hs_vars_hyps H); intro k;
                 apply k in X0; sp));
  try (complete (rw subvars_eq; unfold subset; sp)).

  destruct vhyps as [ nixb vhyps ].
  destruct vhyps as [ nixc vhyps ].
  destruct vhyps as [ nixu vhyps ].
  destruct vhyps as [ nixh vhyps ].
  destruct vhyps as [ nixt vhyps ].
  destruct vhyps as [ wu vhyps ].
  destruct vhyps as [ wb vhyps ].
  destruct vhyps as [ cuh cbh ].
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp2.

  assert (cover_vars u s1)
         as cu1
         by (rw @cover_vars_eq;
             unfold covered in ce0;
             insub;
             apply subvars_trans with (vs2 := nh_vars_hyps H); sp).

  assert (cover_vars u s2)
         as cu2
         by (rw @cover_vars_eq;
             unfold covered in ce0;
             insub;
             apply subvars_trans with (vs2 := nh_vars_hyps H); sp).

  generalize (hyp2
                (snoc s1 (x, lsubstc u wfce1 s1 cu1))
                (snoc s2 (x, lsubstc u wfce1 s2 cu2))); clear hyp2; intro hyp2.

  autodimp hyp2 hyp.
  generalize (hyps_functionality_snoc lib H (mk_hhyp x B) s1 (lsubstc u wfce1 s1 cu1)).
  intro imp; apply imp; thin imp; try (complete auto).
  introv eq sim'; allsimpl.

  vr_seq_true in hyp1.
  generalize (hyp1 s1 s'); clear hyp1; intro hyp1.
  repeat (autodimp hyp1 hyp); exrepnd; clear_irr; sp.

  assert (cover_vars B s1) as cvbs1 by (rw @cover_vars_eq; insub).

  autodimp hyp2 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s2 (lsubstc u wfce1 s1 cu1) (lsubstc u wfce1 s2 cu2) wfct1 cvbs1; sp.

  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2); clear hyp1; intro hyp1.
  repeat (autodimp hyp1 hyp); exrepnd; clear_irr; sp.

  exrepnd.
  lsubst_tac; sp.
Qed.

(* begin hide *)

Lemma rule_cutH_true_ex {o} :
  forall lib (H : @bhyps o) B C t u x,
    rule_true_if lib (rule_cutH H B C t u x).
Proof.
  intros.
  generalize (rule_cutH_true lib H B C t u x); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.


(* end hide *)
