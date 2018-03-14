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
Require Export sequents_equality.
Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_isect.
Require Export rules_tyfam.
Require Export rules_tyfam2.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export lsubstc_weak.
Require Export rules_elimination.


Hint Rewrite @nh_vars_hyps_app : slow.
Hint Rewrite @nh_vars_hyps_snoc : slow.


(*
<<
   H, f : isect(A;x.B[x]), J |- C ext e[z\axiom]

     By isectElimination s z

     H, f : isect(A;x.B[x]), J |- a in A
     H, f : isect(A;x.B[x]), J, z : f in B[a] |- C ext e
>>

 *)

Definition rule_isect_elimination_concl {o}
           (A : @NTerm o) B C e f x z H J :=
  mk_baresequent
    (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
    (mk_concl C (subst e z mk_axiom)).

Definition rule_isect_elimination_hyp1 {o}
           (A : @NTerm o) B a ea f x H J :=
  mk_baresequent
    (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
    (mk_concl (mk_member a A) ea).

Definition rule_isect_elimination_hyp2 {o}
           (A : @NTerm o) B C a e f x z H J :=
  mk_baresequent
    (snoc (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
          (mk_hyp z (mk_member (mk_var f) (subst B x a))))
    (mk_concl C e).

Definition rule_isect_elimination {p}
           (A B C a e : NTerm) ea
           (f x z : NVar)
           (H J : @barehypotheses p) :=
  mk_rule
    (rule_isect_elimination_concl A B C e f x z H J)
    [
      rule_isect_elimination_hyp1 A B a ea f x H J,
      rule_isect_elimination_hyp2 A B C a e f x z H J
    ]
    [(*sarg_term a, sarg_var z*)].

Lemma rule_isect_elimination_true3 {p} :
  forall lib (A B C a e ea : NTerm) (f x z : NVar) (H J : @barehypotheses p),
    rule_true3 lib (rule_isect_elimination
                      A B C a e ea
                      f x z
                      H J).
Proof.
  unfold rule_isect_elimination, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  rename Hyp0 into hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
                      ||- (mk_concl C (subst e z mk_axiom))) as wfc.
  {
    clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    prove_seq; eauto 3 with slow.
    apply covered_subst; eauto 2 with slow.
    eapply covered_subvars;[|eauto].
    autorewrite with slow; simpl.
    rw subvars_eq; introv i; simpl.
    repeat (allrw @in_snoc; allrw @in_app_iff).
    repndors; tcsp.
  }
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  assert (disjoint (free_vars A) (vars_hyps J)
          # disjoint (remove_nvars [x] (free_vars B)) (vars_hyps J)
          # subvars (free_vars a) (snoc (vars_hyps H) f ++ vars_hyps J)
          # wf_term a
          # !LIn z (free_vars C)
          # !LIn z (vars_hyps H)
          # !LIn z (vars_hyps J)
          # (z <> f)
          # !LIn f (vars_hyps H)
          # !LIn f (vars_hyps J)
          # !LIn f (free_vars A)
          # (x <> f -> !LIn f (free_vars B))) as vhyps.
  {
    clear hyp1 hyp2.
    dwfseq.
    sp;
      try (complete (introv i; discover; allunfold @disjoint; discover; auto));
      try (complete (assert (LIn f (remove_nvars [x] (free_vars B)))
                      by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; auto));
      try (complete (apply wf_member_iff in wfct0; sp));
      try (complete (generalize (wfh10 z); rw in_app_iff; rw in_snoc; sp));
      try (complete (generalize (wfh10 f); rw in_remove_nvars; simpl; intro i;
                     dest_imp i hyp));
      try complete (pose proof (wfc1 z) as xx; autodimp xx hyp;
                    rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp).
  }

  destruct vhyps as [ daj vhyps ].
  destruct vhyps as [ dbj vhyps ].
  destruct vhyps as [ sva vhyps ].
  destruct vhyps as [ wa vhyps ].
  destruct vhyps as [ nizc vhyps ].
  destruct vhyps as [ nizh vhyps ].
  destruct vhyps as [ nizj vhyps ].
  destruct vhyps as [ nzf vhyps ].
  destruct vhyps as [ nifh vhyps ].
  destruct vhyps as [ nifj vhyps ].
  destruct vhyps as [ nifa nifb ].
  (* done with proving these simple facts *)

  vr_seq_true.

  duplicate sim as simapp.

  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx.
  lsubst_tac.
  rw @equality_in_isect in sim2; repnd.

  vr_seq_true in hyp2.
  generalize (hyp2 (snoc (snoc s1a0 (f, t1) ++ s1b) (z, mkc_axiom))
                   (snoc (snoc s2a0 (f, t2) ++ s2b) (z, mkc_axiom)));
    clear hyp2; intros hyp2.
  repeat (autodimp hyp2 h); exrepnd.

  {
    (* hyps_functionality *)

    pose proof (hyps_functionality_snoc
                  lib
                  (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
                  (mk_hyp z (mk_member (mk_var f) (subst B x a)))
                  (snoc s1a0 (f, t1) ++ s1b)
                  mkc_axiom) as k; simpl in k.
    apply k; try (complete auto); clear k.
    introv eq sim; GC; lsubst_tac.
    rw @tequality_mkc_member_sp.
    apply equality_refl in eq.
    rw <- @member_member_iff in eq.

    vr_seq_true in hyp1.
    generalize (hyp1 (snoc s1a0 (f, t1) ++ s1b) s'); clear hyp1; intros hyp1.
    repeat (autodimp hyp1 h); exrepnd.
    lsubst_tac.
    allapply @member_if_inhabited.
    rw @tequality_mkc_member_sp in hyp0; repnd.

    assert (equality lib (lsubstc a wa (snoc s1a0 (f, t1) ++ s1b) ct3)
                     (lsubstc a wa s' ct4)
                     (lsubstc A w1 s1a0 c1)) as eqa.
    {
      sp.
      unfold member in hyp1.
      spcast; apply @equality_respects_cequivc_right with (t2 := lsubstc a wa (snoc s1a0 (f, t1) ++ s1b) ct3); sp.
    }

    applydup sim5 in eqa.

    duplicate sim as sim'.
    apply eqh in sim'.

    rw @eq_hyps_app in sim'; simpl in sim'; exrepnd; subst; cpx.
    apply app_split in sim'0; repnd; allrw length_snoc;
    try (complete (allrw; sp)); subst; cpx.

    rw @eq_hyps_snoc in sim'5; simpl in sim'5; exrepnd; subst; cpx.
    lsubst_tac.
    rw @tequality_isect in sim'0; repnd.

    applydup sim'0 in eqa as teq.

    assert (disjoint (remove_nvars [x] (free_vars B)) (dom_csub s1b0)) as disj1.
    {
      apply similarity_dom in sim1; repnd.
      rw sim7.
      rewrite vars_hyps_substitute_hyps; auto.
    }

    assert (disjoint (remove_nvars [x] (free_vars B)) (dom_csub s2b0)) as disj2.
    {
      apply sub_eq_hyps_dom in sim'1; repnd.
      rw sim'1; auto.
    }

    repeat (substc_lsubstc_vars3;[]).

    dands.

    {
      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).
      repeat (lsubstc_weak;[]).
      proof_irr.
      auto.
    }

    rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
    apply app_split in sim7; repnd; allrw length_snoc;
    try (complete (allrw; sp)); subst; cpx.
    apply app_split in sim9; repnd; allrw length_snoc;
    try (complete (allrw; sp)); subst; cpx.
    rw @similarity_snoc in sim12; simpl in sim12; exrepnd; subst; cpx.
    lsubst_tac.
    rw @equality_in_isect in sim9; repnd.
    applydup sim9 in eqa as eqf.

    left.
    repeat (lsubstc_subst_aeq2;[]).
    repeat (substc_lsubstc_vars3;[]).
    repeat (lsubstc_weak;[]).
    proof_irr.
    auto.
  }


  {
    (* similarity *)

    assert (wf_term (mk_member (mk_var f) (subst B x a))) as wm.
    {
      apply wf_member; sp.
      apply subst_preserves_wf_term; sp.
    }

    assert (cover_vars (mk_member (mk_var f) (subst B x a))
                       (snoc s1a0 (f, t1) ++ s1b)) as cm.
    {
      apply cover_vars_member; sp.
      apply cover_vars_var.
      { rw @dom_csub_app; rw @dom_csub_snoc; rw in_app_iff; rw in_snoc; simpl; sp. }
      (* begin proof of last cover_vars *)
      rw @cover_vars_eq; rw @cover_vars_covered; apply covered_subst; sp.
      rw @dom_csub_app; rw @dom_csub_snoc; simpl.
      rw cons_app; apply covered_app_weak_l.
      clear sim2 sim5; unfold cover_vars_upto in c2; unfold covered.
      prove_subvars c2; allsimpl; sp.
      rw @dom_csub_csub_filter in l; rw in_remove_nvars in l; rw in_single_iff in l.
      rw in_snoc; sp.
      clear hyp1; rw @covered_equality in ct0; repnd.
      unfold covered; unfold covered in ct1.
      rw @vars_hyps_app in ct1; rw @vars_hyps_snoc in ct1; simpl in ct1.
      rw @dom_csub_app; rw @dom_csub_snoc; simpl.
      allapply @similarity_dom; repnd; allrw; rw @vars_hyps_substitute_hyps; sp.
      (* end proof of last cover_vars *)
    }

    sim_snoc.
    dands; auto.
    lsubst_tac.
    rw @member_eq.
    rw <- @member_member_iff.

    vr_seq_true in hyp1.
    generalize (hyp1 (snoc s1a0 (f, t1) ++ s1b)
                     (snoc s2a0 (f, t2) ++ s2b));
      clear hyp1; intros hyp1.
    repeat (autodimp hyp1 h); exrepnd.
    lsubst_tac.
    allapply @member_if_inhabited.
    rw @tequality_mkc_member_sp in hyp0; repnd.
    unfold member in hyp1.
    apply sim2 in hyp1.

    assert (disjoint (remove_nvars [x] (free_vars B)) (dom_csub s1b)) as disj1.
    {
      apply similarity_dom in sim1; repnd.
      rw sim7.
      rewrite vars_hyps_substitute_hyps; auto.
    }

    apply equality_refl in hyp1.
    unfold member in *.
    repeat (lsubstc_subst_aeq2;[]).
    repeat (substc_lsubstc_vars3;[]).
    repeat (lsubstc_weak;[]).
    proof_irr.
    auto.
  }

  (* conclusion *)

  lsubst_tac; sp.

  assert (wf_term (@mk_axiom p)) as wfax by eauto 2 with slow.

  repeat (lsubstc_subst_aeq2;[]).
  allrw @lsubstc_mk_axiom.
  repeat (substc_lsubstc_vars3;[]).
  proof_irr.

  pose proof (lsubstc_snoc_move
                e
                (snoc s1a0 (f, t1) ++ s1b)
                []
                z
                mkc_axiom
                wfce) as xx1.
  allrw app_nil_r.
  allrw @dom_csub_app.
  allrw @dom_csub_snoc.
  allsimpl.
  pose proof (xx1 pt0) as xx2; clear xx1.
  autodimp xx2 hyp.
  { apply similarity_dom in sim6; repnd.
    rewrite sim7.
    apply similarity_dom in sim1; repnd.
    rewrite sim8.
    rewrite vars_hyps_substitute_hyps; auto.
    rw in_app_iff; rw in_snoc; intro i; repndors; tcsp.
  }
  exrepnd.
  proof_irr.
  rewrite <- xx0; clear xx0.

  pose proof (lsubstc_snoc_move
                e
                (snoc s2a0 (f, t2) ++ s2b)
                []
                z
                mkc_axiom
                wfce) as xx1.
  allrw app_nil_r.
  allrw @dom_csub_app.
  allrw @dom_csub_snoc.
  allsimpl.
  pose proof (xx1 pt3) as xx2; clear xx1.
  autodimp xx2 hyp.
  { apply similarity_dom in sim6; repnd.
    rewrite sim6.
    apply similarity_dom in sim1; repnd.
    rewrite sim1.
    rewrite vars_hyps_substitute_hyps; auto.
    rw in_app_iff; rw in_snoc; intro i; repndors; tcsp.
  }
  exrepnd.
  proof_irr.
  rewrite <- xx0; clear xx0.

  auto.
Qed.

(* begin hide *)

Lemma rule_isect_elimination_true {p} :
  forall lib (A B C a e ea : NTerm) (f x z : NVar) (H J : @barehypotheses p),
    rule_true lib (rule_isect_elimination
                     A B C a e
                     ea
                     f x z
                     H J).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_isect_elimination_true3.
Qed.

Lemma rule_isect_elimination_true2 {o} :
  forall lib A B C a e ea f x z H J,
    @rule_true2 o lib (rule_isect_elimination A B C a e ea f x z H J).
Proof.
  intros.
  apply rule_true_iff_rule_true2.
  apply rule_isect_elimination_true.
Qed.

Lemma rule_isect_elimination_true_ext_lib {o} :
  forall lib (A B C a e ea : @NTerm o) f x z H J,
    rule_true_ext_lib lib (rule_isect_elimination A B C a e ea f x z H J).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_isect_elimination_true3.
Qed.

Lemma rule_isect_elimination_wf2 {o} :
  forall (A B C a e : @NTerm o) ea f x z H J,
    wf_term a
    -> covered a (snoc (vars_hyps H) f ++ vars_hyps J)
    -> !LIn z (vars_hyps H)
    -> !LIn z (vars_hyps J)
    -> z <> f
    -> wf_rule2 (rule_isect_elimination A B C a e ea f x z H J).
Proof.
  introv wa cova nizH nizJ dzf wf j.
  allsimpl; repndors; subst; tcsp;
  allunfold @wf_bseq; repnd; allsimpl; wfseq.

  - allrw @vswf_hypotheses_nil_eq.
    allrw @wf_hypotheses_app; repnd.
    allrw @wf_hypotheses_snoc; repnd.
    allapply @isprog_vars_implies_wf.
    simpl in *.
    allrw <- @wf_isect_iff; tcsp.

  - allrw @vswf_hypotheses_nil_eq.
    allrw @wf_hypotheses_app; repnd.
    allrw @wf_hypotheses_snoc; repnd.
    allapply @isprog_vars_implies_covered.
    allrw @covered_function; repnd.
    apply covered_snoc_app_weak.
    apply covered_app_weak_l; auto.

  - allrw @vswf_hypotheses_nil_eq.
    rw @wf_hypotheses_snoc; simpl; dands; tcsp.
    { apply isprog_vars_member; dands.
      + apply isprog_vars_var_iff.
        rw @vars_hyps_app.
        rw @vars_hyps_snoc; simpl.
        rw in_app_iff.
        rw in_snoc; tcsp.
      + apply isprog_vars_subst2; auto.
        * allrw @wf_hypotheses_app; repnd.
          allrw @wf_hypotheses_snoc; repnd.
          allsimpl.
          allapply @isprog_vars_implies_wf.
          allrw <- @wf_isect_iff; tcsp.
        * rw @isprog_vars_iff_covered; dands; auto.
          rw @vars_hyps_app.
          rw @vars_hyps_snoc; simpl; auto.
        * allrw @wf_hypotheses_app; repnd.
          allrw @wf_hypotheses_snoc; repnd.
          allsimpl.
          allrw <- @isprog_vars_function_iff; repnd.
          allrw @vars_hyps_app.
          allrw @vars_hyps_snoc; simpl.
          eapply isprog_vars_subvars;[|eauto].
          rw subvars_eq; introv i; allsimpl.
          allrw in_app_iff; allrw in_snoc; tcsp.
    }
    { intro i.
      allrw @vars_hyps_app.
      allrw @vars_hyps_snoc; allsimpl.
      allrw in_app_iff; allrw in_snoc.
      repndors; tcsp.
    }

  - apply covered_snoc_weak; auto.
Qed.



(*

<<
   H, f : isect(A;x.B[x]), J |- C ext e[z\axiom][y\f]

     By isectElimination s z

     H, f : isect(A;x.B[x]), J |- a in A
     H, f : isect(A;x.B[x]), J, y : B[a], z : y = f in B[a] |- C ext e
>>

 *)


Definition rule_isect_elimination2_hyp2 {o}
           (A : @NTerm o) B C a e f x y z H J :=
  mk_baresequent
    (snoc (snoc (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
                (mk_hyp y (subst B x a)))
          (mk_hyp z (mk_equality (mk_var y) (mk_var f) (subst B x a))))
    (mk_concl C e).

Definition rule_isect_elimination2_concl {o}
           (A : @NTerm o) B C e f x y z H J :=
  mk_baresequent
    (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
    (mk_concl C (subst (subst e y (mk_var f)) z mk_axiom)).

Definition rule_isect_elimination2 {p}
           (A B C a e : NTerm) ea
           (f x y z : NVar)
           (H J : @barehypotheses p) :=
  mk_rule
    (rule_isect_elimination2_concl A B C e f x y z H J)
    [
      rule_isect_elimination_hyp1 A B a ea f x H J,
      rule_isect_elimination2_hyp2 A B C a e f x y z H J
    ]
    [(*sarg_term a, sarg_var z*)].

Lemma rule_isect_elimination2_true_ext_lib {o} :
  forall lib (A B C a e ea : @NTerm o) f x y z H J,
    rule_true_ext_lib lib (rule_isect_elimination2 A B C a e ea f x y z H J).
Proof.
  introv wf args imp.
  apply (rule_isect_elimination_true_ext_lib lib A B C a (subst e y (mk_var f)) ea); auto.

  introv xx; simpl in xx; repndors; subst; tcsp.

  - apply imp; simpl; tcsp.

  - apply rule_elimination_true_ext_lib; simpl in *; auto.

    + allrw @nh_vars_hyps_app.
      allrw @nh_vars_hyps_snoc; simpl.
      apply covered_var.
      rw in_app_iff; rw in_snoc; tcsp.

    + simpl in *.
      revert wf.
      unfold rule_isect_elimination2_concl.
      unfold rule_elimination_concl.

      clear args.

      dLin_hyp; exrepnd.
      rename Hyp into hyp1.
      rename Hyp0 into hyp2.
      destruct hyp1 as [ ws1 hyp1 ].
      destruct hyp2 as [ ws2 hyp2 ].
      destseq; allsimpl; proof_irr; GC.

      clear hyp1 hyp2.

      introv wf.
      unfold wf_bseq, closed_type_baresequent, closed_extract_baresequent in *; simpl in *; repnd.
      destseq; allsimpl.
      dands; auto.

      * apply vswf_hypotheses_nil_eq.
        allrw @wf_hypotheses_snoc.
        allrw @wf_hypotheses_app.
        allrw @wf_hypotheses_snoc.
        repnd; simpl in *.
        dands; auto.

        {
          allrw @vars_hyps_app.
          allrw @vars_hyps_snoc.
          simpl in *.
          allrw <- @isprog_vars_isect_iff; repnd.
          allrw @isprog_vars_member; dands.

          - apply isprog_vars_var_if.
            apply in_app_iff; rw in_snoc; tcsp.

          - apply isprog_vars_subst2; eauto 3 with slow.

            + allrw @covered_member; repnd; tcsp.
              allrw @wf_member_iff2; repnd.
              apply isprog_vars_iff_covered; dands; auto.

            + eapply isprog_vars_subvars;[|eauto].
              rw subvars_eq; introv i; simpl in *.
              allrw in_app_iff; allrw in_snoc; tcsp.
        }

        {
          introv i.
          allrw @vars_hyps_app.
          allrw @vars_hyps_snoc.
          allrw @vars_hyps_app.
          allrw @vars_hyps_snoc.
          simpl in *.
          destruct wfh2.
          allrw in_app_iff.
          allrw in_snoc.
          allrw in_app_iff.
          allrw in_snoc.
          repndors; subst; tcsp.
        }

      * unfold closed_type; simpl.
        eapply covered_subvars;[|exact wf].
        rw subvars_eq.
        allrw @vars_hyps_app.
        allrw @vars_hyps_snoc.
        allrw @vars_hyps_app.
        allrw @vars_hyps_snoc.
        simpl.
        introv i.
        allrw in_app_iff.
        allrw in_snoc.
        allrw in_app_iff.
        allrw in_snoc.
        repndors; subst; tcsp.
Qed.

Lemma rule_isect_elimination2_wf2 {o} :
  forall (A B C a e : @NTerm o) ea f x y z H J,
    wf_term a
    -> covered a (snoc (vars_hyps H) f ++ vars_hyps J)
    -> !LIn z (vars_hyps H)
    -> !LIn z (vars_hyps J)
    -> !LIn y (vars_hyps H)
    -> !LIn y (vars_hyps J)
    -> z <> f
    -> z <> y
    -> y <> f
    -> wf_rule2 (rule_isect_elimination2 A B C a e ea f x y z H J).
Proof.
  introv wa cova nizH nizJ niyH niyJ dzf dzy dyf; introv wf j.
  allsimpl; repndors; subst; tcsp;
  allunfold @wf_bseq; repnd; allsimpl; wfseq.

  - allrw @vswf_hypotheses_nil_eq.
    allrw @wf_hypotheses_app; repnd.
    allrw @wf_hypotheses_snoc; repnd.
    allapply @isprog_vars_implies_wf.
    allrw <- @wf_isect_iff; tcsp.

  - allrw @vswf_hypotheses_nil_eq.
    allrw @wf_hypotheses_app; repnd.
    allrw @wf_hypotheses_snoc; repnd.
    allapply @isprog_vars_implies_covered.
    allrw @covered_function; repnd.
    apply covered_snoc_app_weak.
    apply covered_app_weak_l; auto.

  - allrw @vswf_hypotheses_nil_eq.
    rw @wf_hypotheses_snoc; simpl; dands; tcsp.

    {
      apply isprog_vars_equality; dands.

      - apply isprog_vars_var_iff.
        rw @vars_hyps_snoc; simpl.
        rw @vars_hyps_app.
        rw @vars_hyps_snoc; simpl.
        rw in_snoc.
        rw in_app_iff.
        rw in_snoc; tcsp.

      - apply isprog_vars_var_iff.
        rw @vars_hyps_snoc; simpl.
        rw @vars_hyps_app.
        rw @vars_hyps_snoc; simpl.
        rw in_snoc.
        rw in_app_iff.
        rw in_snoc; tcsp.

      - apply isprog_vars_subst2; auto.

        + allrw @wf_hypotheses_app; repnd.
          allrw @wf_hypotheses_snoc; repnd.
          allsimpl.
          allapply @isprog_vars_implies_wf.
          allrw <- @wf_isect_iff; tcsp.

        + rw @isprog_vars_iff_covered; dands; auto.
          rw @vars_hyps_snoc; simpl; auto.
          rw @vars_hyps_app.
          rw @vars_hyps_snoc; simpl; auto.
          apply covered_snoc_weak; auto.

        + allrw @wf_hypotheses_app; repnd.
          allrw @wf_hypotheses_snoc; repnd.
          allsimpl.
          allrw <- @isprog_vars_function_iff; repnd.
          allrw @vars_hyps_app.
          allrw @vars_hyps_snoc; simpl.
          allrw @vars_hyps_app.
          allrw @vars_hyps_snoc; simpl.
          eapply isprog_vars_subvars;[|eauto].
          rw subvars_eq; introv i; allsimpl.
          allrw in_app_iff; allrw in_snoc; allrw in_app_iff; allrw in_snoc; tcsp.
    }

    {
      intro i.
      allrw @vars_hyps_app.
      allrw @vars_hyps_snoc; allsimpl.
      allrw @vars_hyps_app.
      allrw @vars_hyps_snoc; allsimpl.
      allrw in_app_iff; allrw in_snoc.
      allrw in_app_iff; allrw in_snoc.
      repndors; tcsp.
    }

    {
      apply wf_hypotheses_snoc; simpl; dands; auto.

      - apply isprog_vars_subst2; auto.

        + allrw @wf_hypotheses_app; repnd.
          allrw @wf_hypotheses_snoc; repnd.
          allsimpl.
          allapply @isprog_vars_implies_wf.
          allrw <- @wf_isect_iff; tcsp.

        + rw @isprog_vars_iff_covered; dands; auto.
          rw @vars_hyps_app.
          rw @vars_hyps_snoc; simpl; auto.

        + allrw @wf_hypotheses_app; repnd.
          allrw @wf_hypotheses_snoc; repnd.
          allsimpl.
          allrw <- @isprog_vars_function_iff; repnd.
          allrw @vars_hyps_app.
          allrw @vars_hyps_snoc; simpl.
          allrw @vars_hyps_app.
          allrw @vars_hyps_snoc; simpl.
          eapply isprog_vars_subvars;[|eauto].
          rw subvars_eq; introv i; allsimpl.
          allrw in_app_iff; allrw in_snoc; allrw in_app_iff; allrw in_snoc; tcsp.

      - allrw @vars_hyps_app; allrw @vars_hyps_snoc; simpl.
        rw in_app_iff; rw in_snoc; tcsp.
    }

  - apply covered_snoc_weak; auto.
    apply covered_snoc_weak; auto.
Qed.
