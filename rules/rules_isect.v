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

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)



(* end hide *)

(**

  We now prove the truth of several rules about the intersection type.

*)

(* [3] ============ ISECT MEMBER FORMATION ============ *)

(**

  We can state the intersection member formation rule as follows:

<<
   H |- isect x:A. B ext b

     By isect_memberFormation lvl(i) z ()

     H [z : A] |- subst B x z ext b
     H |- A = A in Type(i)
>>

 *)

Definition rule_isect_member_formation_concl {o} A x B b (H : @bhyps o) :=
  mk_baresequent H (mk_concl (mk_isect A x B) b).

Definition rule_isect_member_formation_hyp1 {o} z A x B b (H : @bhyps o) :=
  mk_baresequent
    (snoc H (mk_hhyp z A))
    (mk_concl (subst B x (mk_var z)) b).

Definition rule_isect_member_formation_hyp2 {o} A e i (H : @bhyps o) :=
  mk_baresequent H (mk_concl (mk_equality A A (mk_uni i)) e).

Definition rule_isect_member_formation {o}
           (A B b e : NTerm)
           (x z  : NVar)
           (i    : nat)
           (H    : @barehypotheses o) :=
  mk_rule
    (rule_isect_member_formation_concl A x B b H)
    [ rule_isect_member_formation_hyp1 z A x B b H,
      rule_isect_member_formation_hyp2 A e i H ]
    [sarg_var z].

Lemma rule_isect_member_formation_true3 {o} :
  forall lib (A B b e : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o),
    rule_true3 lib (rule_isect_member_formation A B b e x z i H).
Proof.
  intros.
  unfold rule_isect_member_formation, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  rename Hyp0 into hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H) ||- (mk_concl (mk_isect A x B) b))) as wfc.
  { clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; auto.
    introv j.
    rw in_app_iff in j; repndors; tcsp.
  }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  assert (covered b (nh_vars_hyps H)
          # (z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars b)
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)
          # @wf_term o (mk_var z)) as vhyps.

  { clear hyp1 hyp2.
    dwfseq.
    sp;
      try (complete (generalize (wfc1 z); sp;
                     allrw in_remove_nvars; allsimpl;
                     autodimp X0 h; sp));
      try (complete (apply_in_hyp p;
                     generalize (subvars_hs_vars_hyps H); intro sv;
                     rw subvars_prop in sv;
                     apply sv in p; sp)).
  }

  destruct vhyps as [ bcH vhyps ].
  destruct vhyps as [ nzB vhyps ].
  destruct vhyps as [ nzb vhyps ].
  destruct vhyps as [ nzA vhyps ].
  destruct vhyps as [ nzH wfz ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  (* We prove our first subgoal *)
  assert (forall s2 pC2,
            similarity lib s1 s2 H
            -> tequality lib (lsubstc (mk_isect A x B) wf1 s1 pC1)
                         (lsubstc (mk_isect A x B) wf1 s2 pC2)) as tfb.

  { clear s2 pC2 pt2 sim.
    intros s2 pC2 sim.
    lift_lsubst.
    rw @tequality_isect.

    (* we have to prove that A is a type and B is a type family *)
    split.

    - (* we use our 2nd hypothesis to prove that A is a type *)
      vr_seq_true in hyp2.
      generalize (hyp2 s1 s2); clear hyp2; intro hyp2.
      autodimp hyp2 h.
      autodimp hyp2 h; exrepd.
      lsubst_tac.
      apply equality_in_mkc_equality in e0; repnd.
      clear e0 e2.
      apply equality_commutes in t; auto.
      apply equality_in_uni in t; auto.

    - (* we use our 1st hypothesis to prove that B is a type family *)
      intros.
      vr_seq_true in hyp1.
      generalize (hyp1 (snoc s1 (z, a)) (snoc s2 (z, a'))); clear hyp1; intro hyp1.
      autodimp hyp1 h.

      + (* To use our 1st hyp, we first have to prove that the hypotheses are functional *)
        intros s3 sim3.
        inversion sim3; cpx; allsimpl; cpx; clear_irr.
        assert (cover_vars A s4) as c4
            by (apply similarity_cover_vars with (t := A) in sim0; auto).
        (* we use our hyp (coming from proving that our sequent is true) that says that H is functional *)
        rw @eq_hyps_snoc; simpl.

        exists s1 s4 a t2 w1 c1 c4; sp.
        (* now to prove that functionality statement on A, we use our 2nd hyp *)
        vr_seq_true in hyp2.
        generalize (hyp2 s1 s4); clear hyp2; intro hyp2.
        autodimp hyp2 hyp.
        autodimp hyp2 hyp; exrepd.
        lsubst_tac.
        apply equality_in_mkc_equality in e1; repnd.
        clear e1 e3.
        apply equality_commutes in t; auto.
        apply equality_in_uni in t; auto.
        (* and we're done proving that the hypotheses are functional *)

      + (* now we can keep using our 1st hypothesis *)
        autodimp hyp1 hyp.

        { (* For that we have to prove that the two terms we picked to be equal in A are actually equal in A *)
          sim_snoc; dands; auto. }

        { (* and again, we keep on using our 1st hypothesis *)
          exrepd. (* we prove that from t *)

          assert (cover_vars (mk_var z) (snoc s1 (z, a))) as cov1.
          { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; sp. }

          assert (cover_vars (mk_var z) (snoc s2 (z, a'))) as cov2.
          { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; sp. }

          repeat (lsubstc_subst_aeq2;[]).
          repeat (substc_lsubstc_vars3;[]).
          revert c c4 t.
          lsubst_tac.
          introv t.
          repeat (lsubstc_snoc2;[]).
          proof_irr; auto.
          (* and we're done proving our 1st subgoal (the tequality) *)
        }
  }

  (* We now prove our second subgoal *)
  dands; auto.
  lsubst_tac_c.
  applydup @similarity_refl in sim.
  rw @equality_in_isect.

  dands.
  (* We have to prove 3 goals *)

  { (* 1) we have to prove that A is a type *)
    generalize (tfb s1 pC1 sim0); sp.
    lsubst_tac.
    allrw @tequality_isect; sp. }

  { (* 2) we have to prove that B is a type family *)
    generalize (tfb s1 pC1 sim0); sp.
    lsubst_tac.
    allrw @tequality_isect; sp. }

  { (* 3) we have to prove that b is a member B *)
    introv equ.
    vr_seq_true in hyp1.
    generalize (hyp1 (snoc s1 (z, a)) (snoc s2 (z, a'))); clear hyp1; intro hyp1.
    autodimp hyp1 hyp.

    - (* first we have to prove that the hypotheses are functional *)
      intros s3 sim3.
      inversion sim3; cpx; allsimpl; cpx; clear_irr.
      assert (cover_vars A s4) as c4
          by (apply @similarity_cover_vars with (t := A) in sim1; auto).
      (* we use our hyp (coming from proving that our sequent is true) that says that H is functional *)
      allapplydup eqh.
      rw @eq_hyps_snoc; simpl.
      exists s1 s4 a t2 w1 c1 c4; sp.
      (* now to prove that functionality statement on A, we use our 2nd hyp (from tfb) *)
      assert (cover_vars (mk_isect A x B) s4) as c5.
      { eapply similarity_cover_vars; eauto. }
      pose proof (tfb s4 c5 sim1) as hh.
      lsubst_tac.
      allrw @tequality_isect; sp.
      (* and we're done proving that the hypotheses are functional *)

    - (* now we can keep using our 1st hypothesis *)
      autodimp hyp1 hyp.

      + (* For that we have to prove that the two terms we picked to be equal in A are actually equal in A *)
        sim_snoc; dands; auto.
        (* easy enough *)

      + (* and again, we keep on using our 1st hypothesis *)
        exrepd. (* we prove that from e *)
        clear t; clear_irr.

        assert (cover_vars (mk_var z) (snoc s1 (z, a))) as cov1.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; sp. }

        lsubstc_subst_aeq2.
        repeat (substc_lsubstc_vars3;[]).
        revert c0 e0.
        lsubst_tac.
        introv e0.
        lsubstc_snoc2.
        proof_irr; auto.
  }
Qed.

Lemma rule_isect_member_formation_true_ext_lib {o} :
  forall lib (A B b e : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o),
    rule_true_ext_lib lib (rule_isect_member_formation A B b e x z i H).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_isect_member_formation_true3.
Qed.


(* begin hide *)

Lemma rule_isect_member_formation_true {o} :
  forall lib (A B b e : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o),
    rule_true lib (rule_isect_member_formation A B b e x z i H).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_isect_member_formation_true3.
Qed.

Lemma rule_isect_member_formation_true_ex {o} :
  forall lib i z e A B b x H,
    @rule_true_if o lib (rule_isect_member_formation A B b e x z i H).
Proof.
  intros.
  generalize (rule_isect_member_formation_true lib A B b e x z i H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Lemma rule_isect_member_formation_true2 {o} :
  forall lib i z e A B b x H,
    @rule_true2 o lib (rule_isect_member_formation A B b e x z i H).
Proof.
  intros.
  generalize (rule_isect_member_formation_true lib A B b e x z i H); intro rt.
  apply rule_true_iff_rule_true2; sp.
Qed.

Lemma rule_isect_member_formation_wf {o} :
  forall i z e A B b x H,
    !LIn z (vars_hyps H)
    -> wf_term e
    -> @wf_rule o (rule_isect_member_formation A B b e x z i H).
Proof.
  introv niz wfe.

  introv pwf m; allsimpl; repdors; subst; sp;
    allunfold @pwf_sequent; wfseq; sp;
      allrw @covered_isect; repnd; auto;
        allrw <- @wf_isect_iff; repnd; auto.

  { allrw @vswf_hypotheses_nil_eq.
    apply wf_hypotheses_snoc; simpl; sp.
    apply isprog_vars_eq; sp.
    apply nt_wf_eq; sp. }

  { apply subst_preserves_wf_term; sp. }

  { apply @covered_subst; sp;
      try (apply @covered_var; rw in_snoc; sp);
      try (complete (rw cons_snoc; apply @covered_snoc_weak; auto)). }
Qed.

Lemma rule_isect_member_formation_wf2 {o} :
  forall i z A B b e x H,
    !LIn z (vars_hyps H)
    -> @wf_rule2 o (rule_isect_member_formation A B b e x z i H).
Proof.
  introv niz wf j; allsimpl; repndors; subst; tcsp;
    allunfold @wf_bseq; repnd; allsimpl; wfseq;
      allrw @covered_isect; repnd; auto;
        allrw <- @wf_isect_iff; repnd; auto.

  - allrw @vswf_hypotheses_nil_eq.
    apply wf_hypotheses_snoc; simpl; sp.
    apply isprog_vars_eq; sp.
    apply nt_wf_eq; sp.

  - apply subst_preserves_wf_term; sp.

  - apply @covered_subst; sp;
    try (apply @covered_var; rw in_snoc; sp);
    try (complete (rw cons_snoc; apply @covered_snoc_weak; auto)).
Qed.




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
