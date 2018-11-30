(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export continuity_roadmap.
Require Export sequents_equality.
Require Export seq_util.
Require Export subst_tacs_aeq.
Require Export per_props_ffatom.
Require Export cequiv_fresh2.


(*
   H |- fresh(v.t) in T

     By freshMember a z

     H, a : Name, z : fresh(v.t)#a |- t[v\a] in T
     H, a : Name, z : fresh(v.t)#a |- t[v\a]#a
     H |- fresh(v.t) in Base

 *)
Definition rule_fresh_member {o}
           (H : barehypotheses)
           (t T : @NTerm o)
           (v z a : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member (mk_fresh v t) T) ))
    [ mk_baresequent
        (snoc (snoc H (mk_hyp a mk_uatom)) (mk_hyp z (mk_free_from_atom mk_base (mk_fresh v t) (mk_var a))))
        (mk_conclax (mk_member (subst t v (mk_var a)) T)),
      mk_baresequent
        (snoc (snoc H (mk_hyp a mk_uatom)) (mk_hyp z (mk_free_from_atom mk_base (mk_fresh v t) (mk_var a))))
        (mk_conclax (mk_free_from_atom mk_base (subst t v (mk_var a)) (mk_var a))),
      mk_baresequent H (mk_conclax (mk_member (mk_fresh v t) mk_base))
    ]
    [].

Lemma rule_fresh_member_true {o} :
  forall lib (H : barehypotheses)
         (t T : @NTerm o)
         (v z a : NVar),
    rule_true lib (rule_fresh_member H t T v z a).
Proof.
  unfold rule_fresh_member, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  assert ((a <> v -> !LIn a (free_vars t))
          # (z <> v -> !LIn z (free_vars t))
          # a <> z
          # !LIn a (vars_hyps H)
          # !LIn z (vars_hyps H)
          # !LIn a (free_vars T)
          # !LIn z (free_vars T)) as vhyps.

  {
    clear hyp1 hyp2 hyp3.
    dwfseq.
    sp;
      try (complete (pose proof (ct2 a) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp));
      try (complete (pose proof (ct2 z) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp)).
  }

  destruct vhyps as [ nat vhyps ].
  destruct vhyps as [ nzt vhyps ].
  destruct vhyps as [ daz vhyps ].
  destruct vhyps as [ naH vhyps ].
  destruct vhyps as [ nzH vhyps ].
  destruct vhyps as [ naT nzT ].

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_member_iff.

  pose proof (teq_and_member_if_member
                lib T (mk_fresh v t) s1 s2 H wT wt ct2 ct3 cT cT0)
    as teq.
  repeat (autodimp teq hyp); auto;[| |lsubst_tac; auto].

  - destruct (fresh_atom o (get_utokens t ++ get_utokens_csub s1)) as [ua fa].
    rw in_app_iff in fa; rw not_over_or in fa; repnd.

    vr_seq_true in hyp1.
    pose proof (hyp1
                  (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom))
                  (snoc (snoc s2 (a,mkc_utoken ua)) (z,mkc_axiom)))
      as hyp; clear hyp1.
    repeat (autodimp hyp hh).

    + apply hyps_functionality_snoc2; simpl; auto.

      * introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
        allsimpl.
        lsubst_tac.
        apply tequality_free_from_atom; dands; eauto 3 with slow.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1a a (mkc_utoken ua) [v] c4) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s2a a t2 [v] c7) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        vr_seq_true in hyp3.
        pose proof (hyp3 s1a s2a eqh sim'3) as hyp; clear hyp3; exrepnd.
        lsubst_tac.
        apply tequality_mkc_member_base in hyp0; spcast.
        apply equality_in_base_iff; spcast; auto.

      * apply hyps_functionality_snoc2; simpl; auto.
        introv equ' sim'.
        lsubst_tac.
        apply tequality_uatom.

    + sim_snoc2.

      { apply wf_free_from_atom; eauto 2 with slow. }

      { apply cover_vars_free_from_atom; dands; eauto 3 with slow;
        try (complete (apply cover_vars_snoc_weak; auto)).
        apply cover_vars_var_iff; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

      dands; auto.

      * sim_snoc2.
        dands; auto.

        lsubst_tac.
        apply equality_in_uatom_iff.
        exists ua; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.

      * lsubst_tac.
        apply equality_in_free_from_atom.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1 a (mkc_utoken ua) [v] c4) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        exists (mkc_fresh v (lsubstc_vars t w1 (csub_filter s1 [v]) [v] cv')) ua.
        dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
        try (apply tequality_base).

        { apply equality_in_base_iff; spcast; eauto 3 with slow. }

        unfold getc_utokens; simpl; autorewrite with slow.
        intro i.
        apply atoms2.get_utokens_lsubst_subset in i.
        rw in_app_iff in i; repndors; tcsp;[].
        rw @get_utokens_csub_as in fa.
        rw <- @sub_filter_csub2sub in i.
        allrw @in_get_utokens_sub.
        exrepnd.
        apply in_sub_filter in i0; repnd.
        destruct fa.
        exists v0 t0; dands; auto.

    + exrepnd.
      lsubst_tac.
      apply tequality_mkc_member in hyp0; repnd; auto.

  - clear dependent s1.
    clear dependent s2.

    introv hf sim.
    lsubst_tac.

    assert (!LIn a (dom_csub s1)) as nias1.
    { allapply @similarity_dom; repnd; allrw; auto. }

    assert (!LIn z (dom_csub s1)) as nizs1.
    { allapply @similarity_dom; repnd; allrw; auto. }

    destruct (fresh_atom o (get_utokens t ++ get_utokens_csub s1 ++ get_utokens_csub s2)) as [ua fa].
    repeat (rw in_app_iff in fa); repeat (rw not_over_or in fa); repnd.

    vr_seq_true in hyp1.
    pose proof (hyp1
                  (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom))
                  (snoc (snoc s2 (a,mkc_utoken ua)) (z,mkc_axiom)))
      as hyp; clear hyp1.
    repeat (autodimp hyp hh).

    + apply hyps_functionality_snoc2; simpl; auto.

      * introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
        allsimpl.
        lsubst_tac.
        apply tequality_free_from_atom; dands; eauto 3 with slow.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1a a (mkc_utoken ua) [v] c4) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s2a a t2 [v] c7) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        vr_seq_true in hyp3.
        pose proof (hyp3 s1a s2a hf sim'3) as hyp; clear hyp3; exrepnd.
        lsubst_tac.
        apply tequality_mkc_member_base in hyp0; spcast.
        apply equality_in_base_iff; spcast; auto.

      * apply hyps_functionality_snoc2; simpl; auto.
        introv equ' sim'.
        lsubst_tac.
        apply tequality_uatom.

    + sim_snoc2.

      { apply wf_free_from_atom; eauto 2 with slow. }

      { apply cover_vars_free_from_atom; dands; eauto 3 with slow;
        try (complete (apply cover_vars_snoc_weak; auto)).
        apply cover_vars_var_iff; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

      dands; auto.

      * sim_snoc2; eauto 3 with slow.
        dands; auto.

        lsubst_tac.
        apply equality_in_uatom_iff.
        exists ua; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.

      * lsubst_tac.
        apply equality_in_free_from_atom.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1 a (mkc_utoken ua) [v] c4) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        exists (mkc_fresh v (lsubstc_vars t w1 (csub_filter s1 [v]) [v] cv')) ua.
        dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
        try (apply tequality_base).

        { apply equality_in_base_iff; spcast; eauto 3 with slow. }

        unfold getc_utokens; simpl; autorewrite with slow.
        intro i.
        apply atoms2.get_utokens_lsubst_subset in i.
        rw in_app_iff in i; repndors; tcsp;[].
        rw @get_utokens_csub_as in fa1.
        rw <- @sub_filter_csub2sub in i.
        allrw @in_get_utokens_sub.
        exrepnd.
        apply in_sub_filter in i0; repnd.
        destruct fa1.
        exists v0 t0; dands; auto.

    + exrepnd.
      lsubst_tac.
      allrw <- @member_member_iff.

      vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as hyp; exrepnd.
      clear hyp5.
      lsubst_tac.
      apply tequality_mkc_member_base in hyp4; spcast.
      eapply equality_respects_cequivc_right;[eauto|].
      rw @member_eq.

      apply similarity_refl in sim.
      clear dependent s2.

      assert (cover_vars (mk_var a) (snoc (snoc s1 (a, mkc_utoken ua)) (z, mkc_axiom))) as cova.
      { apply cover_vars_var; allrw @dom_csub_snoc; simpl.
        allrw in_snoc; tcsp. }

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      repeat (lsubstc_snoc2;[]).
      GC; proof_irr; auto.

      eapply member_respects_cequivc;[|eauto].
      apply cequivc_sym.
      apply cequiv_stable.

      vr_seq_true in hyp2.
      pose proof (hyp2
                    (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom))
                    (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom)))
        as hyp; clear hyp1.
      repeat (autodimp hyp hh).

      * apply hyps_functionality_snoc2; simpl; auto.

        { introv equ' sim'.
          apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
          allsimpl.
          lsubst_tac.
          apply tequality_free_from_atom; dands; eauto 3 with slow.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1a a (mkc_utoken ua) [v] c8) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s2a a t2 [v] c11) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          pose proof (hyp3 s1a s2a hf sim'3) as hyp; clear hyp3; exrepnd.
          lsubst_tac.
          apply tequality_mkc_member_base in hyp0; spcast.
          apply equality_in_base_iff; spcast; auto.
        }

        { apply hyps_functionality_snoc2; simpl; auto.
          introv equ' sim'.
          lsubst_tac.
          apply tequality_uatom.
        }

      * sim_snoc2.

        { apply wf_free_from_atom; eauto 2 with slow. }

        { apply cover_vars_free_from_atom; dands; eauto 3 with slow;
          try (complete (apply cover_vars_snoc_weak; auto)).
        }

        dands; auto.

        { sim_snoc2; eauto 3 with slow.
          dands; auto.

          lsubst_tac.
          apply equality_in_uatom_iff.
          exists ua; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.
        }

        { lsubst_tac.
          apply equality_in_free_from_atom.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1 a (mkc_utoken ua) [v] c8) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          exists (mkc_fresh v (lsubstc_vars t w1 (csub_filter s1 [v]) [v] cv')) ua.
          dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
          try (apply tequality_base).

          { apply equality_in_base_iff; spcast; eauto 3 with slow. }

          unfold getc_utokens; simpl; autorewrite with slow.
          intro i.
          apply atoms2.get_utokens_lsubst_subset in i.
          rw in_app_iff in i; repndors; tcsp;[].
          rw @get_utokens_csub_as in fa1.
          rw <- @sub_filter_csub2sub in i.
          allrw @in_get_utokens_sub.
          exrepnd.
          apply in_sub_filter in i0; repnd.
          destruct fa1.
          exists v0 t0; dands; auto.
        }

      * exrepnd.
        lsubst_tac.
        allrw <- @member_member_iff.
        clear hyp0.
        apply equality_in_free_from_atom in hyp1; exrepnd.
        clear hyp0 hyp4.
        apply equality_in_base_iff in hyp7.
        spcast.
        apply computes_to_valc_isvalue_eq in hyp5;[eqconstr hyp5|eauto 3 with slow].

        repeat (lsubstc_subst_aeq2;[]).
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        repeat (lsubstc_snoc2;[]).
        GC; proof_irr; auto.

        eapply cequivc_trans.

        apply (cequivc_fresh_subst_gen _ _ _ u y); auto.

        { unfold getcv_utokens; simpl.
          intro i.
          apply atoms2.get_utokens_lsubst_subset in i.
          rw in_app_iff in i; repndors; tcsp;[].
          rw @get_utokens_csub_as in fa1.
          rw <- @sub_filter_csub2sub in i.
          allrw @in_get_utokens_sub.
          exrepnd.
          apply in_sub_filter in i0; repnd.
          destruct fa1.
          exists v0 t0; dands; auto.
        }

        { repeat (substc_lsubstc_vars3;[]); auto. }

        { repeat (lsubstc_subst_aeq2;[]).
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          repeat (lsubstc_snoc2;[]).
          GC; proof_irr; auto. }
Qed.



Definition rule_fresh_equality_concl {o} (H : @bhyps o) t1 t2 T v1 v2 :=
  mk_baresequent H (mk_conclax (mk_equality (mk_fresh v1 t1) (mk_fresh v2 t2) T)).

Definition rule_fresh_equality_hyp_eq {o} (H : @bhyps o) t1 t2 T v1 v2 z w a :=
  mk_baresequent
    (snoc (snoc (snoc H (mk_hyp a mk_uatom))
                (mk_hyp z (mk_free_from_atom mk_base (mk_fresh v1 t1) (mk_var a))))
          (mk_hyp w (mk_free_from_atom mk_base (mk_fresh v2 t2) (mk_var a))))
    (mk_conclax (mk_equality (subst t1 v1 (mk_var a)) (subst t2 v2 (mk_var a)) T)).

Definition rule_fresh_equality_hyp_free {o} (H : @bhyps o) t v z a :=
  mk_baresequent
    (snoc (snoc H (mk_hyp a mk_uatom)) (mk_hyp z (mk_free_from_atom mk_base (mk_fresh v t) (mk_var a))))
    (mk_conclax (mk_free_from_atom mk_base (subst t v (mk_var a)) (mk_var a))).

Definition rule_fresh_equality_hyp_base {o} (H : @bhyps o) t v :=
  mk_baresequent H (mk_conclax (mk_member (mk_fresh v t) mk_base)).

(*
   H |- fresh(v1.t1) = fresh(v2.t2)in T

     By freshEquality a z

     H, a : Name, z : fresh(v1.t1)#a, w : fresh(v2.t2)#a |- t1[v1\a]=t2[v2\a] in T
     H, a : Name, z : fresh(v1.t1)#a |- t1[v1\a]#a
     H, a : Name, w : fresh(v2.t2)#a |- t2[v2\a]#a
     H |- fresh(v1.t1) in Base
     H |- fresh(v2.t2) in Base

 *)
Definition rule_fresh_equality {o}
           (H : barehypotheses)
           (t1 t2 T : @NTerm o)
           (v1 v2 z w a : NVar) :=
  mk_rule
    (rule_fresh_equality_concl H t1 t2 T v1 v2)
    [ rule_fresh_equality_hyp_eq H t1 t2 T v1 v2 z w a,
      rule_fresh_equality_hyp_free H t1 v1 z a,
      rule_fresh_equality_hyp_free H t2 v2 w a,
      rule_fresh_equality_hyp_base H t1 v1,
      rule_fresh_equality_hyp_base H t2 v2
    ]
    [].

Lemma rule_fresh_equality_true3 {o} :
  forall lib (H : barehypotheses)
         (t1 t2 T : @NTerm o)
         (v1 v2 z w a : NVar),
    rule_true3 lib (rule_fresh_equality H t1 t2 T v1 v2 z w a).
Proof.
  unfold rule_fresh_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ws1 hyp1].
  destruct Hyp0 as [ws2 hyp2].
  destruct Hyp1 as [ws3 hyp3].
  destruct Hyp2 as [ws4 hyp4].
  destruct Hyp3 as [ws5 hyp5].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (rule_fresh_equality_concl H t1 t2 T v1 v2)) as wfs.
  { clear hyp1 hyp2 hyp3 hyp4 hyp5.
    prove_seq. }
  exists wfs.
  unfold wf_csequent, wf_sequent, wf_concl in wfs; allsimpl; repnd; proof_irr; GC.

  assert ((a <> v1 -> !LIn a (free_vars t1))
          # (z <> v1 -> !LIn z (free_vars t1))
          # (w <> v1 -> !LIn w (free_vars t1))
          # (a <> v2 -> !LIn a (free_vars t2))
          # (z <> v2 -> !LIn z (free_vars t2))
          # (w <> v2 -> !LIn w (free_vars t2))
          # a <> z
          # a <> w
          # z <> w
          # !LIn a (vars_hyps H)
          # !LIn z (vars_hyps H)
          # !LIn w (vars_hyps H)
          # !LIn a (free_vars T)
          # !LIn z (free_vars T)
          # !LIn w (free_vars T)) as vhyps.

  {
    clear hyp1 hyp2 hyp3 hyp4 hyp5.
    dwfseq.
    sp;
      try (complete (pose proof (wfs0 a) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp));
      try (complete (pose proof (wfs0 z) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp));
      try (complete (pose proof (wfs0 w) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp));
      try (complete (pose proof (wfs2 a) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp));
      try (complete (pose proof (wfs2 z) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp));
      try (complete (pose proof (wfs2 w) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp)).
  }

  destruct vhyps as [ nat1 vhyps ].
  destruct vhyps as [ nzt1 vhyps ].
  destruct vhyps as [ nwt1 vhyps ].
  destruct vhyps as [ nat2 vhyps ].
  destruct vhyps as [ nzt2 vhyps ].
  destruct vhyps as [ nwt2 vhyps ].
  destruct vhyps as [ daz vhyps ].
  destruct vhyps as [ daw vhyps ].
  destruct vhyps as [ dzw vhyps ].
  destruct vhyps as [ naH vhyps ].
  destruct vhyps as [ nzH vhyps ].
  destruct vhyps as [ nwH vhyps ].
  destruct vhyps as [ naT vhyps ].
  destruct vhyps as [ nzT nwT ].

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.

  pose proof (teq_and_eq_if_equality
                lib T (mk_fresh v1 t1) (mk_fresh v2 t2) s1 s2 H wT w1 w2 c1 c0 c2 c3 cT cT0)
    as teq.
  repeat (autodimp teq hyp); auto;[| |lsubst_tac; auto];[|].

  - destruct (fresh_atom o (get_utokens t1 ++ get_utokens t2 ++ get_utokens_csub s1)) as [ua fa].
    repeat (rw in_app_iff in fa); repeat (rw not_over_or in fa); repnd.

    vr_seq_true in hyp1.
    pose proof (hyp1
                  (snoc (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom)) (w,mkc_axiom))
                  (snoc (snoc (snoc s2 (a,mkc_utoken ua)) (z,mkc_axiom)) (w,mkc_axiom)))
      as hyp; clear hyp1.
    repeat (autodimp hyp hh).

    + apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
        apply similarity_snoc in sim'3; simpl in sim'3; exrepnd; cpx; GC; ginv.
        allsimpl.
        lsubst_tac.
        apply tequality_free_from_atom; dands; eauto 3 with slow;[].

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 (snoc s1a (a,mkc_utoken ua)) z mkc_axiom [v2] c13) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 s1a a (mkc_utoken ua) [v2] cv') as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 (snoc s2a0 (a,t4)) z t3 [v2] c16) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 s2a0 a t4 [v2] cv'1) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        vr_seq_true in hyp5.
        pose proof (hyp5 s1a s2a0 eqh sim'4) as hyp; clear hyp5; exrepnd.
        lsubst_tac.
        apply tequality_mkc_member_base in hyp0; spcast.
        apply equality_in_base_iff; spcast; auto. }

      apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
        allsimpl.
        lsubst_tac.
        apply tequality_free_from_atom; dands; eauto 3 with slow;[].

        pose proof (lsubstc_vars_csub_filter_snoc_ex t1 w0 s1a a (mkc_utoken ua) [v1] c10) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t1 w0 s2a a t3 [v1] c13) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        vr_seq_true in hyp4.
        pose proof (hyp4 s1a s2a eqh sim'3) as hyp; clear hyp4; exrepnd.
        lsubst_tac.
        apply tequality_mkc_member_base in hyp0; spcast.
        apply equality_in_base_iff; spcast; auto. }

      apply hyps_functionality_snoc2; simpl; auto.
      introv equ' sim'.
      lsubst_tac.
      apply tequality_uatom.

    + sim_snoc2.

      { apply wf_free_from_atom; eauto 2 with slow. }

      { apply cover_vars_free_from_atom; dands; eauto 3 with slow;
        try (complete (repeat (apply cover_vars_snoc_weak); auto)).
        apply cover_vars_var_iff; repeat (rw @dom_csub_snoc; simpl; rw in_snoc; tcsp). }

      dands; auto.

      * sim_snoc2.

        { apply wf_free_from_atom; eauto 2 with slow. }

        { apply cover_vars_free_from_atom; dands; eauto 3 with slow;
          try (complete (repeat (apply cover_vars_snoc_weak); auto)).
          apply cover_vars_var_iff; repeat (rw @dom_csub_snoc; simpl; rw in_snoc; tcsp). }

        dands; auto.

        { sim_snoc2.
          dands; auto.
          lsubst_tac.
          apply equality_in_uatom_iff.
          exists ua; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow. }

        lsubst_tac.
        apply equality_in_free_from_atom.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t1 w0 s1 a (mkc_utoken ua) [v1] c11) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        exists (mkc_fresh v1 (lsubstc_vars t1 w0 (csub_filter s1 [v1]) [v1] cv')) ua.
        dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
        try (apply tequality_base).

        { apply equality_in_base_iff; spcast; eauto 3 with slow. }

        unfold getc_utokens; simpl; autorewrite with slow.
        intro i.
        apply atoms2.get_utokens_lsubst_subset in i.
        rw in_app_iff in i; repndors; tcsp;[].
        rw @get_utokens_csub_as in fa.
        rw <- @sub_filter_csub2sub in i.
        allrw @in_get_utokens_sub.
        exrepnd.
        apply in_sub_filter in i0; repnd.
        destruct fa.
        exists v t; dands; auto.

      * lsubst_tac.
        apply equality_in_free_from_atom.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 (snoc s1 (a,mkc_utoken ua)) z mkc_axiom [v2] c10) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 s1 a (mkc_utoken ua) [v2] cv') as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        exists (mkc_fresh v2 (lsubstc_vars t2 w3 (csub_filter s1 [v2]) [v2] cv'0)) ua.
        dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
        try (apply tequality_base).

        { apply equality_in_base_iff; spcast; eauto 3 with slow. }

        unfold getc_utokens; simpl; autorewrite with slow.
        intro i.
        apply atoms2.get_utokens_lsubst_subset in i.
        rw in_app_iff in i; repndors; tcsp;[].
        rw @get_utokens_csub_as in fa.
        rw <- @sub_filter_csub2sub in i.
        allrw @in_get_utokens_sub.
        exrepnd.
        apply in_sub_filter in i0; repnd.
        destruct fa.
        exists v t; dands; auto.

    + exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in hyp0; repnd; auto.

  - clear dependent s1.
    clear dependent s2.

    introv hf sim.
    lsubst_tac.

    assert (!LIn a (dom_csub s1)) as nias1.
    { allapply @similarity_dom; repnd; allrw; auto. }

    assert (!LIn z (dom_csub s1)) as nizs1.
    { allapply @similarity_dom; repnd; allrw; auto. }

    assert (!LIn w (dom_csub s1)) as niws1.
    { allapply @similarity_dom; repnd; allrw; auto. }

    assert (cover_vars (mk_fresh v2 t2) s1) as cov21.
    { eapply similarity_cover_vars; try apply similarity_sym; eauto. }

    assert (cover_vars (mk_fresh v1 t1) s2) as cov12.
    { eapply similarity_cover_vars; eauto. }

    destruct (fresh_atom o (get_utokens t1 ++ get_utokens t2 ++ get_utokens_csub s1 ++ get_utokens_csub s2)) as [ua fa].
    repeat (rw in_app_iff in fa); repeat (rw not_over_or in fa); repnd.

    vr_seq_true in hyp1.
    pose proof (hyp1
                  (snoc (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom)) (w,mkc_axiom))
                  (snoc (snoc (snoc s2 (a,mkc_utoken ua)) (z,mkc_axiom)) (w,mkc_axiom)))
      as hyp; clear hyp1.
    repeat (autodimp hyp hh).

    + apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
        apply similarity_snoc in sim'3; simpl in sim'3; exrepnd; cpx; GC; ginv.
        allsimpl.
        lsubst_tac.
        apply tequality_free_from_atom; dands; eauto 3 with slow;[].

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 (snoc s1a (a,mkc_utoken ua)) z mkc_axiom [v2] c7) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 s1a a (mkc_utoken ua) [v2] cv') as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 (snoc s2a0 (a,t4)) z t3 [v2] c10) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 s2a0 a t4 [v2] cv'1) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        vr_seq_true in hyp5.
        pose proof (hyp5 s1a s2a0 hf sim'4) as hyp; clear hyp5; exrepnd.
        lsubst_tac.
        apply tequality_mkc_member_base in hyp0; spcast.
        apply equality_in_base_iff; spcast; auto. }

      apply hyps_functionality_snoc2; simpl; auto.

      { introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
        allsimpl.
        lsubst_tac.
        apply tequality_free_from_atom; dands; eauto 3 with slow;[].

        pose proof (lsubstc_vars_csub_filter_snoc_ex t1 w0 s1a a (mkc_utoken ua) [v1] c4) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t1 w0 s2a a t3 [v1] c7) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd;[].
        rw equ0; clear equ0.

        vr_seq_true in hyp4.
        pose proof (hyp4 s1a s2a hf sim'3) as hyp; clear hyp4; exrepnd.
        lsubst_tac.
        apply tequality_mkc_member_base in hyp0; spcast.
        apply equality_in_base_iff; spcast; auto. }

      apply hyps_functionality_snoc2; simpl; auto.
      introv equ' sim'.
      lsubst_tac.
      apply tequality_uatom.

    + sim_snoc2.

      { apply wf_free_from_atom; eauto 2 with slow. }

      { apply cover_vars_free_from_atom; dands; eauto 3 with slow;
        try (complete (repeat (apply cover_vars_snoc_weak); auto)).
        apply cover_vars_var_iff; repeat (rw @dom_csub_snoc; simpl; rw in_snoc; tcsp). }

      dands; auto.

      * sim_snoc2.

        { apply wf_free_from_atom; eauto 2 with slow. }

        { apply cover_vars_free_from_atom; dands; eauto 3 with slow;
          try (complete (repeat (apply cover_vars_snoc_weak); auto)).
          apply cover_vars_var_iff; repeat (rw @dom_csub_snoc; simpl; rw in_snoc; tcsp). }

        dands; auto.

        { sim_snoc2; eauto 3 with slow.
          dands; auto.
          lsubst_tac.
          apply equality_in_uatom_iff.
          exists ua; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow. }

        lsubst_tac.
        apply equality_in_free_from_atom.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t1 w0 s1 a (mkc_utoken ua) [v1] c5) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        exists (mkc_fresh v1 (lsubstc_vars t1 w0 (csub_filter s1 [v1]) [v1] cv')) ua.
        dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
        try (apply tequality_base).

        { apply equality_in_base_iff; spcast; eauto 3 with slow. }

        unfold getc_utokens; simpl; autorewrite with slow.
        intro i.
        apply atoms2.get_utokens_lsubst_subset in i.
        rw in_app_iff in i; repndors; tcsp;[].
        rw @get_utokens_csub_as in fa2.
        rw <- @sub_filter_csub2sub in i.
        allrw @in_get_utokens_sub.
        exrepnd.
        apply in_sub_filter in i0; repnd.
        destruct fa2.
        exists v t; dands; auto.

      * lsubst_tac.
        apply equality_in_free_from_atom.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 (snoc s1 (a,mkc_utoken ua)) z mkc_axiom [v2] c4) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 s1 a (mkc_utoken ua) [v2] cv') as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        exists (mkc_fresh v2 (lsubstc_vars t2 w3 (csub_filter s1 [v2]) [v2] cv'0)) ua.
        dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
        try (apply tequality_base).

        { apply equality_in_base_iff; spcast; eauto 3 with slow. }

        unfold getc_utokens; simpl; autorewrite with slow.
        intro i.
        apply atoms2.get_utokens_lsubst_subset in i.
        rw in_app_iff in i; repndors; tcsp;[].
        rw @get_utokens_csub_as in fa2.
        rw <- @sub_filter_csub2sub in i.
        allrw @in_get_utokens_sub.
        exrepnd.
        apply in_sub_filter in i0; repnd.
        destruct fa2.
        exists v t; dands; auto.

    + exrepnd.
      lsubst_tac.
      allrw <- @member_equality_iff.

      assert (cover_vars (mk_var a) (snoc (snoc (snoc s1 (a, mkc_utoken ua)) (z, mkc_axiom)) (w,mkc_axiom))) as cova1.
      { apply cover_vars_var; allrw @dom_csub_snoc; simpl.
        repeat (rw in_snoc); tcsp. }

      assert (cover_vars (mk_var a) (snoc (snoc (snoc s2 (a, mkc_utoken ua)) (z, mkc_axiom)) (w,mkc_axiom))) as cova2.
      { apply cover_vars_var; allrw @dom_csub_snoc; simpl.
        repeat (rw in_snoc); tcsp. }

      apply equality_commutes4 in hyp0; auto;[]; clear hyp1.

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      repeat (lsubstc_snoc2;[]).
      GC; proof_irr; auto.

      vr_seq_true in hyp2.
      pose proof (hyp2
                    (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom))
                    (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom)))
        as hyp; clear hyp2.
      repeat (autodimp hyp hh).

      { apply hyps_functionality_snoc2; simpl; auto.

        { introv equ' sim'.
          apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
          allsimpl.
          lsubst_tac.
          apply tequality_free_from_atom; dands; eauto 3 with slow.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t1 w0 s1a a (mkc_utoken ua) [v1] c25) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t1 w0 s2a a t3 [v1] c28) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          vr_seq_true in hyp4.
          pose proof (hyp4 s1a s2a hf sim'3) as hyp; clear hyp4; exrepnd.
          lsubst_tac.
          apply tequality_mkc_member_base in hyp1; spcast.
          apply equality_in_base_iff; spcast; auto.
        }

        { apply hyps_functionality_snoc2; simpl; auto.
          introv equ' sim'.
          lsubst_tac_c.
          apply tequality_uatom.
        }
      }

      { sim_snoc2.

        { apply wf_free_from_atom; eauto 2 with slow. }

        { apply cover_vars_free_from_atom; dands; eauto 3 with slow;
          try (complete (apply cover_vars_snoc_weak; auto)).
        }

        dands; auto.

        { sim_snoc2; eauto 3 with slow.
          dands; auto; [|].
          { eapply similarity_refl; eauto. }

          lsubst_tac_c.
          apply equality_in_uatom_iff.
          exists ua; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.
        }

        { lsubst_tac.
          apply equality_in_free_from_atom.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t1 w0 s1 a (mkc_utoken ua) [v1] c25) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          exists (mkc_fresh v1 (lsubstc_vars t1 w0 (csub_filter s1 [v1]) [v1] cv')) ua.
          dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
          try (apply tequality_base).

          { apply equality_in_base_iff; spcast; eauto 3 with slow. }

          unfold getc_utokens; simpl; autorewrite with slow.
          intro i.
          apply atoms2.get_utokens_lsubst_subset in i.
          rw in_app_iff in i; repndors; tcsp;[].
          rw @get_utokens_csub_as in fa2.
          rw <- @sub_filter_csub2sub in i.
          allrw @in_get_utokens_sub.
          exrepnd.
          apply in_sub_filter in i0; repnd.
          destruct fa2.
          exists v t; dands; auto.
        }
      }

      exrepnd.
      lsubst_tac.
      clear hyp1.
      apply equality_in_free_from_atom in hyp2; exrepnd.
      clear hyp1 hyp6.
      apply equality_in_base_iff in hyp9.
      spcast.
      apply computes_to_valc_isvalue_eq in hyp7;[eqconstr hyp7|eauto 3 with slow].

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      repeat (lsubstc_snoc2;[]).
      GC; proof_irr; auto.

      pose proof (cequivc_fresh_subst_gen
                    lib v1
                    (lsubstc_vars t1 w0 (csub_filter s1 [v1]) [v1] c1)
                    u y
                 ) as ceq1.

      repeat (autodimp ceq1 hyp).

      { unfold getcv_utokens; simpl.
        intro i.
        apply atoms2.get_utokens_lsubst_subset in i.
        rw in_app_iff in i; repndors; tcsp;[].
        rw @get_utokens_csub_as in fa2.
        rw <- @sub_filter_csub2sub in i.
        allrw @in_get_utokens_sub.
        exrepnd.
        apply in_sub_filter in i0; repnd.
        destruct fa2.
        exists v t; dands; auto.
      }

      { repeat (substc_lsubstc_vars3;[]); auto. }

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      repeat (lsubstc_snoc2;[]).
      GC; proof_irr; auto.

      eapply equality_respects_cequivc_left;[apply cequivc_sym;eauto|].
      clear ceq1.
      clear dependent y.
      rename u into ua.

      vr_seq_true in hyp3.
      pose proof (hyp3
                    (snoc (snoc s2 (a,mkc_utoken ua)) (w,mkc_axiom))
                    (snoc (snoc s2 (a,mkc_utoken ua)) (w,mkc_axiom)))
        as hyp; clear hyp3.
      repeat (autodimp hyp hh).

      { apply hyps_functionality_snoc2; simpl; auto.

        { introv equ' sim'.
          apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
          allsimpl.
          lsubst_tac.
          apply tequality_free_from_atom; dands; eauto 3 with slow.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 s1a a (mkc_utoken ua) [v2] c26) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 s2a a t3 [v2] c29) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          pose proof (similarity_hyps_functionality_trans lib s1 s1a H sim hf) as hf2.

          vr_seq_true in hyp5.
          pose proof (hyp5 s1a s2a hf2 sim'3) as hyp; clear hyp4; exrepnd.
          lsubst_tac.
          apply tequality_mkc_member_base in hyp1; spcast.
          apply equality_in_base_iff; spcast; auto.
        }

        { apply hyps_functionality_snoc2; simpl; auto;
          [|eapply similarity_hyps_functionality_trans; eauto].
          introv equ' sim'.
          lsubst_tac_c.
          apply tequality_uatom.
        }
      }

      { sim_snoc2.

        { apply wf_free_from_atom; eauto 2 with slow. }

        { apply cover_vars_free_from_atom; dands; eauto 3 with slow;
          try (complete (apply cover_vars_snoc_weak; auto)).
        }

        dands; auto.

        { sim_snoc2; eauto 3 with slow.
          dands; auto; [|].
          { eapply similarity_refl; apply similarity_sym; eauto. }

          lsubst_tac_c.
          apply equality_in_uatom_iff.
          exists ua; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.
        }

        { lsubst_tac.
          apply equality_in_free_from_atom.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t2 w3 s2 a (mkc_utoken ua) [v2] c26) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          exists (mkc_fresh v2 (lsubstc_vars t2 w3 (csub_filter s2 [v2]) [v2] cv')) ua.
          dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
          try (apply tequality_base).

          { apply equality_in_base_iff; spcast; eauto 3 with slow. }

          unfold getc_utokens; simpl; autorewrite with slow.
          intro i.
          apply atoms2.get_utokens_lsubst_subset in i.
          rw in_app_iff in i; repndors; tcsp;[].
          rw @get_utokens_csub_as in fa.
          rw <- @sub_filter_csub2sub in i.
          allrw @in_get_utokens_sub.
          exrepnd.
          apply in_sub_filter in i0; repnd.
          destruct fa.
          exists v t; dands; auto.
        }
      }

      exrepnd.
      lsubst_tac.
      clear hyp1.
      apply equality_in_free_from_atom in hyp2; exrepnd.
      clear hyp1 hyp3.
      apply equality_in_base_iff in hyp9.
      spcast.
      apply computes_to_valc_isvalue_eq in hyp6;[eqconstr hyp6|eauto 3 with slow].

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      repeat (lsubstc_snoc2;[]).
      GC; proof_irr; auto.

      pose proof (cequivc_fresh_subst_gen
                    lib v2
                    (lsubstc_vars t2 w3 (csub_filter s2 [v2]) [v2] c0)
                    u y
                 ) as ceq1.

      repeat (autodimp ceq1 hyp).

      { unfold getcv_utokens; simpl.
        intro i.
        apply atoms2.get_utokens_lsubst_subset in i.
        rw in_app_iff in i; repndors; tcsp;[].
        rw @get_utokens_csub_as in fa.
        rw <- @sub_filter_csub2sub in i.
        allrw @in_get_utokens_sub.
        exrepnd.
        apply in_sub_filter in i0; repnd.
        destruct fa.
        exists v t; dands; auto.
      }

      { repeat (substc_lsubstc_vars3;[]); auto. }

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      repeat (lsubstc_snoc2;[]).
      GC; proof_irr; auto.

      eapply equality_respects_cequivc_right;[apply cequivc_sym;eauto|].
      auto.
Qed.



(*
   H |- fresh(v.t) in T

     By freshMember2 a z B

     H, a : Name, z : lam(v.t)#a in a:Name -> B[a] |- t[v\a] in T
     H, a : Name, z : lam(v.t)#a in a:Name -> B[a] |- t[v\a]#a in B[a]
     H |- lam(v.t) in a:Name -> B[a]

 *)
Definition rule_fresh_member2 {o}
           (H : barehypotheses)
           (t T B : @NTerm o)
           (v z a : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member (mk_fresh v t) T) ))
    [ mk_baresequent
        (snoc (snoc H (mk_hyp a mk_uatom))
              (mk_hyp z (mk_free_from_atom (mk_function mk_uatom a B) (mk_lam v t) (mk_var a))))
        (mk_conclax (mk_member (subst t v (mk_var a)) T)),
      mk_baresequent
        (snoc (snoc H (mk_hyp a mk_uatom))
              (mk_hyp z (mk_free_from_atom (mk_function mk_uatom a B) (mk_lam v t) (mk_var a))))
        (mk_conclax (mk_free_from_atom B (subst t v (mk_var a)) (mk_var a))),
      mk_baresequent H (mk_conclax (mk_member (mk_lam v t) (mk_function mk_uatom a B)))
    ]
    [].

Lemma rule_fresh_member2_true {o} :
  forall lib (H : barehypotheses)
         (t T B : @NTerm o)
         (v z a : NVar),
    rule_true lib (rule_fresh_member2 H t T B v z a).
Proof.
  unfold rule_fresh_member2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  assert ((a <> v -> !LIn a (free_vars t))
          # (z <> v -> !LIn z (free_vars t))
          # a <> z
          # !LIn a (vars_hyps H)
          # !LIn z (vars_hyps H)
          # !LIn a (free_vars T)
          # !LIn z (free_vars T)) as vhyps.

  {
    clear hyp1 hyp2 hyp3.
    dwfseq.
    sp;
      try (complete (pose proof (ct2 a) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp));
      try (complete (pose proof (ct2 z) as xx;
                     allrw in_remove_nvars; allsimpl;
                     autodimp xx hyp; tcsp)).
  }

  destruct vhyps as [ nat vhyps ].
  destruct vhyps as [ nzt vhyps ].
  destruct vhyps as [ daz vhyps ].
  destruct vhyps as [ naH vhyps ].
  destruct vhyps as [ nzH vhyps ].
  destruct vhyps as [ naT nzT ].

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_member_iff.

  pose proof (teq_and_member_if_member
                lib T (mk_fresh v t) s1 s2 H wT wt ct2 ct3 cT cT0)
    as teq.
  repeat (autodimp teq hyp); auto;[| |lsubst_tac; auto].

  - destruct (fresh_atom o (get_utokens t ++ get_utokens_csub s1)) as [ua fa].
    rw in_app_iff in fa; rw not_over_or in fa; repnd.

    assert (!LIn a (dom_csub s1)) as nias1.
    { allapply @similarity_dom; repnd; allrw; auto. }

    vr_seq_true in hyp1.
    pose proof (hyp1
                  (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom))
                  (snoc (snoc s2 (a,mkc_utoken ua)) (z,mkc_axiom)))
      as hyp; clear hyp1.
    repeat (autodimp hyp hh).

    + apply hyps_functionality_snoc2; simpl; auto.

      * introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
        allsimpl.
        lsubst_tac.

        assert (!LIn a (dom_csub s2a)) as nias2.
        { allapply @similarity_dom; repnd; allrw; auto. }

        revert dependent c5.
        rw (csub_filter_snoc s1a a (mkc_utoken ua) [a]).
        rw memvar_singleton; boolvar; introv eqf.

        revert dependent c10.
        rw (csub_filter_snoc s2a a t2 [a]).
        rw memvar_singleton; boolvar; introv.

        apply tequality_free_from_atom; dands; eauto 3 with slow.

        { vr_seq_true in hyp3.
          pose proof (hyp3 s1a s2a eqh sim'3) as hyp; clear hyp3; exrepnd.
          clear hyp1.
          lsubst_tac.
          apply tequality_mkc_member in hyp0; repnd; auto. }

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1a a (mkc_utoken ua) [v] c6) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s2a a t2 [v] c11) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        vr_seq_true in hyp3.
        pose proof (hyp3 s1a s2a eqh sim'3) as hyp; clear hyp3; exrepnd.
        lsubst_tac.
        allrw <- @member_member_iff.
        apply tequality_mkc_member_implies_sp in hyp0; auto.

      * apply hyps_functionality_snoc2; simpl; auto.
        introv equ' sim'.
        lsubst_tac.
        apply tequality_uatom.

    + sim_snoc2.

      { clear hyp2 hyp3.
        allrw @wf_free_from_atom_iff2; repnd; dands; eauto 2 with slow. }

      { clear hyp2 hyp3.
        allrw @cover_vars_free_from_atom; repnd; dands; eauto 3 with slow;
        try (complete (apply cover_vars_snoc_weak; auto));
        try (apply cover_vars_var_iff; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp).
        eapply s_cover_typ1 in ct;[|eauto].
        allrw @cover_vars_member; repnd.
        apply cover_vars_snoc_weak; auto. }

      dands; auto.

      * sim_snoc2.
        dands; auto.

        lsubst_tac.
        apply equality_in_uatom_iff.
        exists ua; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.

      * lsubst_tac.
        apply equality_in_free_from_atom.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1 a (mkc_utoken ua) [v] c6) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        exists (mkc_lam v (lsubstc_vars t w1 (csub_filter s1 [v]) [v] cv')) ua.

        revert dependent c5.
        rw @csub_filter_snoc; rw memvar_singleton; boolvar; tcsp.
        introv; proof_irr.

        dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
        try (apply tequality_base).

        { vr_seq_true in hyp3.
          pose proof (hyp3 s1 s2 eqh sim) as hyp; clear hyp3; exrepnd.
          apply inhabited_implies_tequality in hyp1.
          clear hyp0.
          lsubst_tac.
          apply type_mkc_member in hyp1; auto. }

        { vr_seq_true in hyp3.
          pose proof (hyp3 s1 s2 eqh sim) as hyp; clear hyp3; exrepnd.
          lsubst_tac.
          allrw <- @member_member_iff.
          apply tequality_mkc_member_implies_sp in hyp0; auto. }

        unfold getc_utokens; simpl; autorewrite with slow.
        intro i.
        apply atoms2.get_utokens_lsubst_subset in i.
        rw in_app_iff in i; repndors; tcsp;[].
        rw @get_utokens_csub_as in fa.
        rw <- @sub_filter_csub2sub in i.
        allrw @in_get_utokens_sub.
        exrepnd.
        apply in_sub_filter in i0; repnd.
        destruct fa.
        exists v0 t0; dands; auto.

    + exrepnd.
      lsubst_tac.
      apply tequality_mkc_member in hyp0; repnd; auto.

  - clear dependent s1.
    clear dependent s2.

    introv hf sim.
    lsubst_tac.

    assert (!LIn a (dom_csub s1)) as nias1.
    { allapply @similarity_dom; repnd; allrw; auto. }

    assert (!LIn z (dom_csub s1)) as nizs1.
    { allapply @similarity_dom; repnd; allrw; auto. }

    destruct (fresh_atom o (get_utokens t ++ get_utokens_csub s1 ++ get_utokens_csub s2)) as [ua fa].
    repeat (rw in_app_iff in fa); repeat (rw not_over_or in fa); repnd.

    vr_seq_true in hyp1.
    pose proof (hyp1
                  (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom))
                  (snoc (snoc s2 (a,mkc_utoken ua)) (z,mkc_axiom)))
      as hyp; clear hyp1.
    repeat (autodimp hyp hh).

    + apply hyps_functionality_snoc2; simpl; auto.

      * introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
        allsimpl.
        lsubst_tac.

        revert dependent c5.
        revert dependent c10.
        repeat (rw @csub_filter_snoc).
        rw memvar_singleton; boolvar; introv;[].

        introv equf.

        apply tequality_free_from_atom; dands; eauto 3 with slow.

        { vr_seq_true in hyp3.
          pose proof (hyp3 s1a s2a hf sim'3) as hyp; clear hyp3; exrepnd.
          clear hyp1.
          lsubst_tac.
          apply tequality_mkc_member in hyp0; repnd; auto. }

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1a a (mkc_utoken ua) [v] c6) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s2a a t2 [v] c11) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        vr_seq_true in hyp3.
        pose proof (hyp3 s1a s2a hf sim'3) as hyp; clear hyp3; exrepnd.
        lsubst_tac.
        allrw <- @member_member_iff.
        apply tequality_mkc_member_implies_sp in hyp0; auto.

      * apply hyps_functionality_snoc2; simpl; auto.
        introv equ' sim'.
        lsubst_tac.
        apply tequality_uatom.

    + sim_snoc2.

      { clear hyp2 hyp3.
        allrw @wf_free_from_atom_iff2; repnd; dands; eauto 2 with slow. }

      { clear hyp2 hyp3.
        allrw @cover_vars_free_from_atom; repnd; dands; eauto 3 with slow;
        try (complete (apply cover_vars_snoc_weak; auto));
        try (apply cover_vars_var_iff; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp).
        eapply s_cover_typ1 in ct;[|eauto].
        allrw @cover_vars_member; repnd.
        apply cover_vars_snoc_weak; auto. }

      dands; auto.

      * sim_snoc2; eauto 3 with slow.
        dands; auto.

        lsubst_tac.
        apply equality_in_uatom_iff.
        exists ua; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.

      * lsubst_tac.
        apply equality_in_free_from_atom.

        pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1 a (mkc_utoken ua) [v] c6) as equ.
        rw in_single_iff in equ.
        autodimp equ hyp; exrepnd.
        rw equ0; clear equ0.

        exists (mkc_lam v (lsubstc_vars t w1 (csub_filter s1 [v]) [v] cv')) ua.

        revert dependent c5.
        rw @csub_filter_snoc; rw memvar_singleton; boolvar; tcsp.
        introv; proof_irr.

        dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
        try (apply tequality_base).

        { vr_seq_true in hyp3.
          pose proof (hyp3 s1 s2 hf sim) as hyp; clear hyp3; exrepnd.
          apply inhabited_implies_tequality in hyp1.
          clear hyp0.
          lsubst_tac.
          apply type_mkc_member in hyp1; auto. }

        { vr_seq_true in hyp3.
          pose proof (hyp3 s1 s2 hf sim) as hyp; clear hyp3; exrepnd.
          lsubst_tac.
          allrw <- @member_member_iff.
          apply tequality_mkc_member_implies_sp in hyp0; auto. }

        unfold getc_utokens; simpl; autorewrite with slow.
        intro i.
        apply atoms2.get_utokens_lsubst_subset in i.
        rw in_app_iff in i; repndors; tcsp;[].
        rw @get_utokens_csub_as in fa1.
        rw <- @sub_filter_csub2sub in i.
        allrw @in_get_utokens_sub.
        exrepnd.
        apply in_sub_filter in i0; repnd.
        destruct fa1.
        exists v0 t0; dands; auto.

    + exrepnd.
      lsubst_tac.
      allrw <- @member_member_iff.

      vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as hyp; exrepnd.
      lsubst_tac.

      allrw <- @member_member_iff.
      apply tequality_mkc_member_implies_sp in hyp4; auto;[].
      apply tequality_mkc_member_implies_sp in hyp0; auto;[].
      clear hyp5 hyp1.

      assert (cover_vars (mk_var a) (snoc (snoc s1 (a, mkc_utoken ua)) (z, mkc_axiom))) as cova1.
      { apply cover_vars_var; allrw @dom_csub_snoc; simpl.
        allrw in_snoc; tcsp. }

      assert (cover_vars (mk_var a) (snoc (snoc s2 (a, mkc_utoken ua)) (z, mkc_axiom))) as cova2.
      { apply cover_vars_var; allrw @dom_csub_snoc; simpl.
        allrw in_snoc; tcsp. }

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.
      repeat (lsubstc_snoc2;[]).
      GC; proof_irr; auto.

      vr_seq_true in hyp2.
      pose proof (hyp2
                    (snoc (snoc s1 (a,mkc_utoken ua)) (z,mkc_axiom))
                    (snoc (snoc s2 (a,mkc_utoken ua)) (z,mkc_axiom)))
        as hyp; clear hyp2.
      repeat (autodimp hyp hh).

      * apply hyps_functionality_snoc2; simpl; auto.

        { introv equ' sim'.
          apply similarity_snoc in sim'; simpl in sim'; exrepnd; cpx; GC; ginv.
          allsimpl.
          lsubst_tac.

          revert dependent c19.
          revert dependent c24.
          repeat (rw @csub_filter_snoc; rw memvar_singleton; boolvar; tcsp).
          introv eqf; proof_irr.

          apply tequality_free_from_atom; dands; eauto 3 with slow.

          { pose proof (hyp3 s1a s2a hf sim'3) as hyp; clear hyp3; exrepnd.
            lsubst_tac.
            apply tequality_mkc_member in hyp1; repnd; auto. }

          pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1a a (mkc_utoken ua) [v] c20) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s2a a t2 [v] c25) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          pose proof (hyp3 s1a s2a hf sim'3) as hyp; clear hyp3; exrepnd.
          lsubst_tac.
          allrw <- @member_member_iff.
          apply tequality_mkc_member_implies_sp in hyp1; auto.
        }

        { apply hyps_functionality_snoc2; simpl; auto.
          introv equ' sim'.
          lsubst_tac.
          apply tequality_uatom.
        }

      * sim_snoc2.

        { clear hyp3 hyp4 hyp0.
          allrw @wf_free_from_atom_iff2; repnd; dands; eauto 2 with slow. }

        { clear hyp3 hyp4 hyp0.
          allrw @cover_vars_free_from_atom; repnd; dands; eauto 3 with slow;
          try (complete (apply cover_vars_snoc_weak; auto));
          try (apply cover_vars_var_iff; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp). }

        dands; auto.

        { sim_snoc2; eauto 3 with slow.
          dands; auto.

          lsubst_tac.
          apply equality_in_uatom_iff.
          exists ua; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow.
        }

        { lsubst_tac.

          revert dependent c20.
          repeat (rw @csub_filter_snoc; rw memvar_singleton; boolvar; tcsp).
          introv; proof_irr.

          pose proof (lsubstc_vars_csub_filter_snoc_ex t w1 s1 a (mkc_utoken ua) [v] c21) as equ.
          rw in_single_iff in equ.
          autodimp equ hyp; exrepnd.
          rw equ0; clear equ0.

          apply equality_in_free_from_atom.

          exists (mkc_lam v (lsubstc_vars t w1 (csub_filter s1 [v]) [v] cv')) ua.
          dands; spcast; try (complete (apply computes_to_valc_refl; eauto 3 with slow));
          try (apply tequality_base).

          { pose proof (hyp3 s1 s2 hf sim) as hyp; clear hyp3; exrepnd.
            apply inhabited_implies_tequality in hyp4.
            clear hyp0.
            lsubst_tac.
            allapply @type_mkc_member; auto. }

          { apply equality_refl in hyp4; proof_irr; auto. }

          unfold getc_utokens; simpl; autorewrite with slow.
          intro i.
          apply atoms2.get_utokens_lsubst_subset in i.
          rw in_app_iff in i; repndors; tcsp;[].
          rw @get_utokens_csub_as in fa1.
          rw <- @sub_filter_csub2sub in i.
          allrw @in_get_utokens_sub.
          exrepnd.
          apply in_sub_filter in i0; repnd.
          destruct fa1.
          exists v0 t0; dands; auto.
        }

      * exrepnd.
        lsubst_tac.
        allrw <- @member_member_iff.
        apply equality_in_free_from_atom in hyp2; exrepnd.
        apply tequality_free_from_atom in hyp1; repnd.
        spcast.
        apply computes_to_valc_isvalue_eq in hyp7;[eqconstr hyp7|eauto 3 with slow].
        clear hyp1.

        repeat (lsubstc_subst_aeq2;[]).
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        repeat (lsubstc_snoc2;[]).
        GC; proof_irr; auto.

        pose proof (cequivc_fresh_subst_gen
                      lib v (lsubstc_vars t w1 (csub_filter s1 [v]) [v] c1) u y) as ceq1; auto.


        (*

        { unfold getcv_utokens; simpl.
          intro i.
          apply atoms2.get_utokens_lsubst_subset in i.
          rw in_app_iff in i; repndors; tcsp;[].
          rw @get_utokens_csub_as in fa1.
          rw <- @sub_filter_csub2sub in i.
          allrw @in_get_utokens_sub.
          exrepnd.
          apply in_sub_filter in i0; repnd.
          destruct fa1.
          exists v0 t0; dands; auto.
        }

        { repeat (substc_lsubstc_vars3;[]); auto. }

        { repeat (lsubstc_subst_aeq2;[]).
          repeat (substc_lsubstc_vars3;[]).
          lsubst_tac.
          repeat (lsubstc_snoc2;[]).
          GC; proof_irr; auto. }
*)
Abort.
