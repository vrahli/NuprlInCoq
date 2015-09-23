(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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

Require Export continuity_stuff.
Require Export sequents_equality.
Require Export seq_util.
Require Export subst_tacs_aeq.
Require Export per_props_ffatom.


(* !!MOVE *)
Definition get_utokens_csub {o} (sub : @CSub o) :=
  flat_map getc_utokens (crange sub).

(* !!MOVE *)
Lemma get_utokens_csub_as {o} :
  forall (s : @CSub o),
    get_utokens_csub s = get_utokens_sub (csub2sub s).
Proof.
  introv.
  unfold get_utokens_csub, get_utokens_sub, crange, range, csub2sub.
  rw map_map; unfold compose; simpl.
  allrw flat_map_map; unfold compose; simpl; tcsp.
Qed.

(* !!MOVE *)
Lemma cover_vars_uatom {o} :
  forall (sub : @CSub o), cover_vars mk_uatom sub.
Proof.
  intro; rw @cover_vars_eq; rw subvars_eq; simpl; sp.
Qed.
Hint Resolve cover_vars_uatom : slow.

(* !!MOVE *)
Lemma respects2_l_alphaeqc_cequivc {o} :
  forall lib, respects2_l alphaeqc (@cequivc o lib).
Proof.
  introv aeq ceq.
  apply (alphaeqc_implies_cequivc lib) in aeq; eauto.
  eapply cequivc_trans;[|eauto]; apply cequivc_sym; auto.
Qed.
Hint Resolve respects2_l_alphaeqc_cequivc : respects.

(* !!MOVE *)
Lemma respects2_r_alphaeqc_cequivc {o} :
  forall lib, respects2_r alphaeqc (@cequivc o lib).
Proof.
  introv aeq ceq.
  apply (alphaeqc_implies_cequivc lib) in aeq; eauto.
  eapply cequivc_trans;[|eauto]; auto.
Qed.
Hint Resolve respects2_r_alphaeqc_cequivc : respects.

(* !!MOVE *)
Lemma approx_fresh_subst_gen1 {o} :
  forall lib (t : @NTerm o) v a y,
    !LIn a (get_utokens t)
    -> !LIn a (get_utokens y)
    -> isprog_vars [v] t
    -> isprog y
    -> cequiv lib (subst t v (mk_utoken a)) y
    -> approx lib (mk_fresh v t) (subst t v (mk_utoken a)).
Proof.
  introv niat niay ispt ispy ceq.

  assert (approx lib (mk_fresh v t) (mk_fresh v y)) as apr1.
  { apply howetheorem1; try (apply isprogram_fresh); eauto 3 with slow.
    apply (apso _ _ _ _ [bterm [v] y]); simpl; auto.
    - unfold lblift_sub; simpl; dands; auto.
      introv k; destruct n; try omega; clear k.
      unfold selectbt; simpl.
      unfold blift_sub.
      exists [v] t y; dands; eauto 3 with slow.
      right.
      exists [(v,mk_utoken a)]; simpl.
      dands; auto.
      + allrw @fold_subst.
        apply le_bin_rel_approx1_eauto.
        eapply approx_trans;[apply cequiv_le_approx;eauto|].
        rw @subst_trivial; eauto 3 with slow.
        apply approx_refl; eauto 3 with slow.
      + constructor.
        * apply ut_sub_cons; simpl; dands; eauto 3 with slow.
          unfold isutoken; eexists; eauto.
        * unfold get_utokens_sub; simpl.
          rw disjoint_singleton_r; rw in_app_iff; rw not_over_or.
          dands; auto.
    - apply approx_open_refl.
      apply nt_wf_fresh; eauto 3 with slow.
  }

  eapply approx_trans;[eauto|].
  eapply approx_trans;[apply approx_shadowed_fresh1;eauto 3 with slow|].
  eapply approx_trans;[|apply cequiv_le_approx;apply cequiv_sym;eauto].
  apply approx_refl; eauto 3 with slow.
Qed.

(* !!MOVE *)
Lemma approx_fresh_subst_gen2 {o} :
  forall lib (t : @NTerm o) v a y,
    !LIn a (get_utokens t)
    -> !LIn a (get_utokens y)
    -> isprog_vars [v] t
    -> isprog y
    -> cequiv lib (subst t v (mk_utoken a)) y
    -> approx lib (subst t v (mk_utoken a)) (mk_fresh v t).
Proof.
  introv niat niay ispt ispy ceq.

  assert (approx lib (mk_fresh v y) (mk_fresh v t)) as apr1.
  { apply howetheorem1; try (apply isprogram_fresh); eauto 3 with slow.
    apply (apso _ _ _ _ [bterm [v] t]); simpl; auto.
    - unfold lblift_sub; simpl; dands; auto.
      introv k; destruct n; try omega; clear k.
      unfold selectbt; simpl.
      unfold blift_sub.
      exists [v] y t; dands; eauto 3 with slow.
      right.
      exists [(v,mk_utoken a)]; simpl.
      dands; auto.
      + allrw @fold_subst.
        apply le_bin_rel_approx1_eauto.
        apply cequiv_sym in ceq.
        eapply approx_trans;[|apply cequiv_le_approx;eauto].
        rw @subst_trivial; eauto 3 with slow.
        apply approx_refl; eauto 3 with slow.
      + constructor.
        * apply ut_sub_cons; simpl; dands; eauto 3 with slow.
          unfold isutoken; eexists; eauto.
        * unfold get_utokens_sub; simpl.
          rw disjoint_singleton_r; rw in_app_iff; rw not_over_or.
          dands; auto.
    - apply approx_open_refl.
      apply nt_wf_fresh; eauto 3 with slow.
  }

  eapply approx_trans;[|eauto].
  eapply approx_trans;[|apply approx_shadowed_fresh2;eauto 3 with slow].
  eapply approx_trans;[apply cequiv_le_approx;eauto|].
  apply approx_refl; eauto 3 with slow.
Qed.

(* !!MOVE *)
Lemma cequivc_fresh_subst_gen {o} :
  forall lib v (t : @CVTerm o [v]) a y,
    !LIn a (getcv_utokens [v] t)
    -> !LIn a (getc_utokens y)
    -> cequivc lib (substc (mkc_utoken a) v t) y
    -> cequivc lib (mkc_fresh v t) (substc (mkc_utoken a) v t).
Proof.
  introv niat niay ispc.
  destruct_cterms; allsimpl.
  allunfold @cequivc; allsimpl.
  unfold getcv_utokens in niat; allsimpl.
  unfold getc_utokens in niay; allsimpl.

  constructor.
  - eapply approx_fresh_subst_gen1; eauto.
  - eapply approx_fresh_subst_gen2; eauto.
Qed.

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
        apply similarity_snoc in sim'; exrepnd; cpx; ginv.
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
      apply tequality_mkc_member_sp in hyp0; repnd; auto.

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
        apply similarity_snoc in sim'; exrepnd; cpx; ginv.
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
          apply similarity_snoc in sim'; exrepnd; cpx; ginv.
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


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
