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


Require Export rules_isect_member_equality.
Require Export rules_typehood.

Hint Rewrite @nh_vars_hyps_app : slow.
Hint Rewrite @nh_vars_hyps_snoc : slow.


(**

<<

   H |- t1 = t2 in isect(x:A;B)

     By isect_memberEquality_alt lvl(i) z ()

     H z : A |- t1 = t2 in B[x\z]
     H |- istype(A)
>>
 *)


Definition rule_isect_member_equality_alt {o}
           (A B t1 t2 e1 e2 : NTerm)
           (x z : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (rule_isect_member_equality_concl H t1 t2 A x B)
    [ rule_isect_member_equality_hyp1 H z A t1 t2 B x e1,
      mk_baresequent H (mk_concl (mk_istype A) e2)]
    [].

Lemma rule_isect_member_equality_alt_true3 {o} :
  forall lib (A B t1 t2 e1 e2 : NTerm)
         (x z : NVar)
         (H   : @barehypotheses o),
    rule_true3 lib (rule_isect_member_equality_alt A B t1 t2 e1 e2 x z H).
Proof.
  intros.
  unfold rule_isect_member_equality_alt, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  rename Hyp0 into hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    prove_seq; eauto 3 with slow.
  }
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars t1)
          # !LIn z (free_vars t2)
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)) as vhyps.

  {
    clear hyp1 hyp2.
    dwfseq.
    sp;
      try (complete (pose proof (wfc1 z) as q; allrw in_remove_nvars;
                     allrw in_single_iff; autodimp q hyp)).
  }

  destruct vhyps as [ nzB  vhyps ].
  destruct vhyps as [ nzt1 vhyps ].
  destruct vhyps as [ nzt2 vhyps ].
  destruct vhyps as [ nzA nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.
  allrw <- @member_equality_iff.
  teq_and_eq (mk_isect A x B) t1 t2 s1 s2 H.

  - apply tequality_isect; dands.

    + vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 eqh sim) as hyp2; exrepnd.
      lsubst_tac.
      rw @tequality_mkc_istype in hyp0; repnd. auto.
      

    + introv eqa.

      vr_seq_true in hyp1.
      pose proof (hyp1 (snoc s1 (z,a)) (snoc s2 (z,a'))) as hyp1.
      repeat (autodimp hyp1 xxx).

      {
        apply hyps_functionality_snoc2; simpl; auto.
        introv equ sim'.

        vr_seq_true in hyp2.
        pose proof (hyp2 s1 s' eqh sim') as hyp2; exrepnd.
        lsubst_tac.
        rw @tequality_mkc_istype in hyp0; auto.
      }

      {
        sim_snoc; dands; auto.
      }

      exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality in hyp0; repnd.
      clear hyp0 hyp4.

      assert (cover_vars (mk_var z) (snoc s1 (z, a))) as covz1.
      { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

      assert (cover_vars (mk_var z) (snoc s2 (z, a'))) as covz2.
      { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).

      revert c13 c14 hyp3.
      lsubst_tac.
      introv t.
      repeat (lsubstc_snoc2;[]).
      clear_irr.
      auto.

  - apply equality_in_isect2; dands.

    + vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as hyp2; exrepnd.
      lsubst_tac.
      rw @tequality_mkc_istype in hyp0; auto.
      apply tequality_implies_type_left in hyp0. auto.
    + introv eqa.

      dands.

      * vr_seq_true in hyp1.
        pose proof (hyp1 (snoc s1 (z,a)) (snoc s2 (z,a'))) as hyp1.
        repeat (autodimp hyp1 xxx).

        {
          apply hyps_functionality_snoc2; simpl; auto.
          introv equ sim'.

          vr_seq_true in hyp2.
          pose proof (hyp2 s1 s' hf sim') as hyp2; exrepnd.
          lsubst_tac.
          rw @tequality_mkc_istype in hyp0; auto.

        }

        {
          sim_snoc; dands; auto.
        }

        exrepnd.
        lsubst_tac.

        apply equality_in_mkc_equality in hyp1; repnd.
        clear hyp1 hyp4.

        apply equality_commutes4 in hyp0; auto.
        clear hyp3.

        assert (cover_vars (mk_var z) (snoc s1 (z, a))) as covz1.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

        assert (cover_vars (mk_var z) (snoc s2 (z, a'))) as covz2.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

        repeat (lsubstc_subst_aeq2;[]).
        repeat (substc_lsubstc_vars3;[]).

        revert c8 hyp0.
        lsubst_tac.
        introv t.
        repeat (lsubstc_snoc2;[]).
        clear_irr.
        auto.

      * vr_seq_true in hyp1.
        pose proof (hyp1 (snoc s1 (z,a)) (snoc s1 (z,a'))) as hyp1.
        repeat (autodimp hyp1 xxx).

        {
          apply hyps_functionality_snoc2; simpl; auto.
          introv equ sim'.

          vr_seq_true in hyp2.
          pose proof (hyp2 s1 s' hf sim') as hyp2; exrepnd.
          lsubst_tac.
          rw @tequality_mkc_istype in hyp0; auto.

        }

        {
          sim_snoc; dands; auto.
          eapply similarity_refl; eauto.
        }

 
        exrepnd.
        lsubst_tac.

        apply tequality_mkc_equality in hyp0; repnd.
        clear hyp0 hyp4.

        assert (cover_vars (mk_var z) (snoc s1 (z, a))) as covz1.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

        assert (cover_vars (mk_var z) (snoc s1 (z, a'))) as covz2.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

        repeat (lsubstc_subst_aeq2;[]).
        repeat (substc_lsubstc_vars3;[]).

        revert c8 c9 hyp3.
        lsubst_tac.
        introv t.
        repeat (lsubstc_snoc2;[]).
        clear_irr.
        auto.
Qed.

Lemma rule_isect_member_equality_alt_true_ext_lib {o} :
  forall lib (A B t1 t2 e1 e2 : NTerm)
         (x z : NVar)
         (H   : @barehypotheses o),
    rule_true_ext_lib lib (rule_isect_member_equality_alt A B t1 t2 e1 e2 x z H).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_isect_member_equality_alt_true3.
Qed.

Lemma rule_isect_member_equality_alt_wf2 {o} :
  forall (A B t1 t2 e1 e2 : NTerm)
         (x z : NVar)
         (H   : @barehypotheses o),
    !LIn z (vars_hyps H)
    -> wf_rule2 (rule_isect_member_equality_alt A B t1 t2 e1 e2 x z H).
Proof.
  introv nizH  wf j; allsimpl; repndors; subst; tcsp;
    allunfold @wf_bseq; repnd; allsimpl. wfseq;
      allrw @covered_isect; repnd; auto;
        allrw <- @wf_isect_iff; repnd; auto.

  - allrw @vswf_hypotheses_nil_eq.
    allrw @wf_hypotheses_snoc.
    dands; auto; simpl.
    apply isprog_vars_iff_covered; dands; auto.

  - apply wf_term_subst; eauto 2 with slow.

  - apply covered_snoc_weak; auto.

  - apply covered_snoc_weak; auto.

  - apply covered_subst; auto.

    + rewrite cons_snoc.
      apply covered_snoc_weak; auto.

    + apply covered_var; rw in_snoc; tcsp.
  -  split.
     + wfseq.
     + split.
       rw @wf_mk_istype. wfseq. allrw <- @wf_isect_iff; repnd; auto.
       wfseq; allrw @covered_isect; repnd; auto.
       apply implies_covered_cons_weak. auto.
Qed.

(* [3] ============ ISECT MEMBER FORMATION (ALT) ============ *)

(**

  We can state the intersection member formation rule as follows:

<<
   H |- isect x:A. B ext b

     By isect_memberFormation_alt z ()

     H [z : A] |- subst B x z ext b
     H |- istype(A)
>>

 *)




Definition rule_isect_member_formation_alt {o}
           (A B b e : NTerm)
           (x z  : NVar)
           (H    : @barehypotheses o) :=
  mk_rule
    (rule_isect_member_formation_concl A x B b H)
    [ rule_isect_member_formation_hyp1 z A x B b H,
       mk_baresequent H (mk_concl (mk_istype A) e)]
    [sarg_var z].

Lemma rule_isect_member_formation_alt_true3 {o} :
  forall lib (A B b e : NTerm)
         (x z : NVar)
         (H   : @barehypotheses o),
    rule_true3 lib (rule_isect_member_formation_alt A B b e x z H).
Proof.
  intros.
  unfold rule_isect_member_formation_alt, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
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
      rw @tequality_mkc_istype in t.
      auto.

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
        rw @tequality_mkc_istype in t.
        auto.
        
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

Lemma rule_isect_member_formation_alt_true_ext_lib {o} :
  forall lib (A B b e : NTerm)
         (x z : NVar)
         (H   : @barehypotheses o),
    rule_true_ext_lib lib (rule_isect_member_formation_alt A B b e x z H).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_isect_member_formation_alt_true3.
Qed.


(* begin hide *)

Lemma rule_isect_member_formation_alt_true {o} :
  forall lib (A B b e : NTerm)
         (x z : NVar)
         (H   : @barehypotheses o),
    rule_true lib (rule_isect_member_formation_alt A B b e x z H).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_isect_member_formation_alt_true3.
Qed.

Lemma rule_isect_member_formation_alt_true_ex {o} :
  forall lib z e A B b x H,
    @rule_true_if o lib (rule_isect_member_formation_alt A B b e x z H).
Proof.
  intros.
  generalize (rule_isect_member_formation_alt_true lib A B b e x z H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Lemma rule_isect_member_formation_alt_true2 {o} :
  forall lib z e A B b x H,
    @rule_true2 o lib (rule_isect_member_formation_alt A B b e x z H).
Proof.
  intros.
  generalize (rule_isect_member_formation_alt_true lib A B b e x z H); intro rt.
  apply rule_true_iff_rule_true2; sp.
Qed.

Lemma rule_isect_member_formation__alt_wf {o} :
  forall z e A B b x H,
    !LIn z (vars_hyps H)
    -> wf_term e
    -> @wf_rule o (rule_isect_member_formation_alt A B b e x z H).
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
  rw @wf_fun_iff; split; auto.
  apply implies_covered_cons_weak. auto. 
Qed.

Lemma rule_isect_member_formation_alt_wf2 {o} :
  forall z A B b e x H,
    !LIn z (vars_hyps H)
    -> @wf_rule2 o (rule_isect_member_formation_alt A B b e x z  H).
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
  - rw @wf_fun_iff; split; auto.
  - apply implies_covered_cons_weak. auto. 
Qed.

