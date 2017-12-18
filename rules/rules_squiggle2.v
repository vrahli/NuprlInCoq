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


Require Export sequents2.
Require Export sequents_lib.
Require Export sequents_tacs2.
Require Export rules_useful.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export per_can.
Require Export cequiv_util.
Require Export per_props_cequiv.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)


(* !!MOVE *)
Lemma covered_subst_implies {o} :
  forall (t : @NTerm o) x u vs,
    covered (subst t x u) vs
    -> covered t (x :: vs).
Proof.
  introv cov.
  allunfold @covered.
  allrw subvars_eq.
  introv i.
  pose proof (eqset_free_vars_disjoint t [(x,u)]) as h.
  eapply subset_eqset_l in h;[|eauto]; allsimpl.
  rw subset_app in h; repnd.
  rw <- subvars_eq in h0.
  rw subvars_remove_nvars in h0.
  rw subvars_eq in h0.
  apply h0 in i.
  rw in_app_iff in i; allsimpl; repndors; tcsp.
Qed.


(* end hide *)


(**

  The following rule states that we can always replace an [a] for a
  [b] in the conclusion of a sequent if [a] and [b] are
  computationally equivalent:

<<
  H |- C[a] ext t

    By cequivSubstConcl

    H |- C[b] ext t
    H |- a ~ b
>>

 *)

Definition rule_cequiv_subst_hyp1 {o} (H : @bhyps o) x C a t :=
  mk_baresequent H (mk_concl (subst C x a) t).

Definition rule_cequiv_subst_hyp2 {o} (H : @bhyps o) a b :=
  mk_baresequent H (mk_conclax (mk_cequiv a b)).

Definition rule_cequiv_subst_concl {o}
           (H : @barehypotheses o)
           (x : NVar)
           (C a b t  : NTerm) :=
  mk_rule
    (rule_cequiv_subst_hyp1 H x C a t)
    [ rule_cequiv_subst_hyp1 H x C b t,
      rule_cequiv_subst_hyp2 H a b
    ]
    [].

Lemma rule_cequiv_subst_concl_true3 {o} :
  forall lib (H  : @barehypotheses o)
         (x : NVar)
         (C a b t  : NTerm),
    rule_true3 lib (rule_cequiv_subst_concl H x C a b t).
Proof.
  intros.
  unfold rule_cequiv_subst_concl, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [ws1 hyp1].
  destruct Hyp0 as [ws2 hyp2].

  assert (wf_csequent (rule_cequiv_subst_hyp1 H x C a t)) as wfs by prove_seq.
  exists wfs.
  unfold wf_csequent, wf_sequent, wf_bseq in wfs; allsimpl; repnd; proof_irr; GC.
  destseq; allsimpl; proof_irr; GC.

  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.

  pose proof (hyp1 s1 s2 eqh sim) as hh; clear hyp1; exrepnd.

  assert (wf_term a # wf_term b) as wfab.
  { clear hyp2; allrw <- @wf_cequiv_iff; auto. }
  repnd.

  assert (cover_vars a s1 # cover_vars b s1) as cov1.
  { clear hyp2.
    allrw @covered_cequiv; repnd.
    dands; eapply s_cover_typ1; eauto. }

  assert (cover_vars a s2 # cover_vars b s2) as cov2.
  { clear hyp2.
    allrw @covered_cequiv; repnd.
    dands; eapply s_cover_typ2; eauto. }

  repnd.
  dands.

  - repeat (lsubstc_subst_aeq2;[]).
    repeat (substc_lsubstc_vars3;[]).

    eapply tequality_respects_cequivc_left;
      [|eapply tequality_respects_cequivc_right;
         [|exact hh0]
      ].

    + pose proof (hyp2 s1 s1) as qq; clear hyp2.
      repeat (autodimp qq hyp); eauto 3 with slow.
      { apply similarity_refl in sim; auto. }
      exrepnd.
      lsubst_tac.
      allrw <- @member_cequiv_iff.
      apply cequiv_stable; spcast; proof_irr.

      apply cequivc_lsubstc.

      { apply isprogram_csubst; eauto 2 with slow. }
      { apply isprogram_csubst; eauto 2 with slow. }

      apply ceq_csub_cons; eauto 3 with slow.
      apply cequivc_sym; auto.

    + pose proof (hyp2 s2 s2) as qq; clear hyp2.
      repeat (autodimp qq hyp); eauto 3 with slow.
      { eapply similarity_hyps_functionality_trans; eauto. }
      { applydup @similarity_sym in sim as sim'; apply similarity_refl in sim'; auto. }
      exrepnd.
      lsubst_tac.
      allrw <- @member_cequiv_iff.
      apply cequiv_stable; spcast; proof_irr.

      apply cequivc_lsubstc.

      { apply isprogram_csubst; eauto 2 with slow. }
      { apply isprogram_csubst; eauto 2 with slow. }

      apply ceq_csub_cons; eauto 3 with slow.
      apply cequivc_sym; auto.

  - repeat (lsubstc_subst_aeq2;[]).
    repeat (substc_lsubstc_vars3;[]).
    proof_irr.

    eapply cequivc_preserving_equality;[eauto|].

    apply cequivc_lsubstc.

    { apply isprogram_csubst; eauto 2 with slow. }
    { apply isprogram_csubst; eauto 2 with slow. }

    apply ceq_csub_cons; eauto 3 with slow.
    apply cequivc_sym; auto.

    pose proof (hyp2 s1 s1) as qq; clear hyp2.
    repeat (autodimp qq hyp); eauto 3 with slow.
    { apply similarity_refl in sim; auto. }
    exrepnd.
    lsubst_tac.
    allrw <- @member_cequiv_iff.
    apply cequiv_stable; spcast; proof_irr; auto.
Qed.

Lemma rule_cequiv_subst_concl_true {o} :
  forall lib (H  : @barehypotheses o)
         (x : NVar)
         (C a b t  : NTerm),
    rule_true lib (rule_cequiv_subst_concl H x C a b t).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_cequiv_subst_concl_true3.
Qed.

Lemma rule_cequiv_subst_concl_wf2 {o} :
  forall (H  : @barehypotheses o)
         (x : NVar)
         (C a b t  : NTerm),
    wf_term a
    -> wf_term b
    -> covered a (vars_hyps H)
    -> covered b (vars_hyps H)
    -> wf_rule2 (rule_cequiv_subst_concl H x C a b t).
Proof.
  introv wa wb cova covb wf i; allsimpl; repndors; subst; tcsp;
  allunfold @wf_bseq; repnd; wfseq; auto.

  - apply wf_term_subst; auto.
    apply lsubst_wf_term in wf1; auto.

  - apply covered_subst; auto.
    apply covered_subst_implies in wf; auto.

  - apply wf_cequiv; auto.
Qed.

Lemma rule_cequiv_subst_concl_true_ext_lib {o} :
  forall lib (H  : @barehypotheses o)
         (x : NVar)
         (C a b t  : NTerm),
    rule_true_ext_lib lib (rule_cequiv_subst_concl H x C a b t).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_cequiv_subst_concl_true3.
Qed.


(* same as above but we don't force the subgoals to have given extracts *)

Definition rule_cequiv_subst2_hyp2 {o} (H : @bhyps o) a b e :=
  mk_baresequent H (mk_concl (mk_cequiv a b) e).

Definition rule_cequiv_subst_concl2 {o}
           (H : @barehypotheses o)
           (x : NVar)
           (C a b t  : NTerm) e :=
  mk_rule
    (rule_cequiv_subst_hyp1 H x C a t)
    [ rule_cequiv_subst_hyp1 H x C b t,
      rule_cequiv_subst2_hyp2 H a b e
    ]
    [].

Lemma rule_cequiv_subst_concl2_true3 {o} :
  forall lib (H  : @barehypotheses o)
         (x : NVar)
         (C a b t  : NTerm) e,
    rule_true3 lib (rule_cequiv_subst_concl2 H x C a b t e).
Proof.
  intros.
  unfold rule_cequiv_subst_concl2, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [ws1 hyp1].
  destruct Hyp0 as [ws2 hyp2].

  assert (wf_csequent (rule_cequiv_subst_hyp1 H x C a t)) as wfs by prove_seq.
  exists wfs.
  unfold wf_csequent, wf_sequent, wf_bseq in wfs; allsimpl; repnd; proof_irr; GC.
  destseq; allsimpl; proof_irr; GC.

  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.

  pose proof (hyp1 s1 s2 eqh sim) as hh; clear hyp1; exrepnd.

  assert (wf_term a # wf_term b) as wfab.
  { clear hyp2; allrw <- @wf_cequiv_iff; auto. }
  repnd.

  assert (cover_vars a s1 # cover_vars b s1) as cov1.
  { clear hyp2.
    allrw @covered_cequiv; repnd.
    dands; eapply s_cover_typ1; eauto. }

  assert (cover_vars a s2 # cover_vars b s2) as cov2.
  { clear hyp2.
    allrw @covered_cequiv; repnd.
    dands; eapply s_cover_typ2; eauto. }

  repnd.
  dands.

  - repeat (lsubstc_subst_aeq2;[]).
    repeat (substc_lsubstc_vars3;[]).

    eapply tequality_respects_cequivc_left;
      [|eapply tequality_respects_cequivc_right;
         [|exact hh0]
      ].

    + pose proof (hyp2 s1 s1) as qq; clear hyp2.
      repeat (autodimp qq hyp); eauto 3 with slow.
      { apply similarity_refl in sim; auto. }
      exrepnd.
      lsubst_tac.
      allrw @equality_in_mkc_cequiv; repnd.
      apply cequiv_stable; spcast; proof_irr.

      apply cequivc_lsubstc.

      { apply isprogram_csubst; eauto 2 with slow. }
      { apply isprogram_csubst; eauto 2 with slow. }

      apply ceq_csub_cons; eauto 3 with slow.
      apply cequivc_sym; auto.

    + pose proof (hyp2 s2 s2) as qq; clear hyp2.
      repeat (autodimp qq hyp); eauto 3 with slow.
      { eapply similarity_hyps_functionality_trans; eauto. }
      { applydup @similarity_sym in sim as sim'; apply similarity_refl in sim'; auto. }
      exrepnd.
      lsubst_tac.
      allrw @equality_in_mkc_cequiv; repnd.
      apply cequiv_stable; spcast; proof_irr.

      apply cequivc_lsubstc.

      { apply isprogram_csubst; eauto 2 with slow. }
      { apply isprogram_csubst; eauto 2 with slow. }

      apply ceq_csub_cons; eauto 3 with slow.
      apply cequivc_sym; auto.

  - repeat (lsubstc_subst_aeq2;[]).
    repeat (substc_lsubstc_vars3;[]).
    proof_irr.

    eapply cequivc_preserving_equality;[eauto|].

    apply cequivc_lsubstc.

    { apply isprogram_csubst; eauto 2 with slow. }
    { apply isprogram_csubst; eauto 2 with slow. }

    apply ceq_csub_cons; eauto 3 with slow.
    apply cequivc_sym; auto.

    pose proof (hyp2 s1 s1) as qq; clear hyp2.
    repeat (autodimp qq hyp); eauto 3 with slow.
    { apply similarity_refl in sim; auto. }
    exrepnd.
    lsubst_tac.
    allrw @equality_in_mkc_cequiv; repnd.
    apply cequiv_stable; spcast; proof_irr; auto.
Qed.

Lemma rule_cequiv_subst_concl2_true {o} :
  forall lib (H  : @barehypotheses o)
         (x : NVar)
         (C a b t  : NTerm) e,
    rule_true lib (rule_cequiv_subst_concl2 H x C a b t e).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_cequiv_subst_concl2_true3.
Qed.

Lemma rule_cequiv_subst_concl2_wf2 {o} :
  forall (H  : @barehypotheses o)
         (x : NVar)
         (C a b t  : NTerm) e,
    wf_term a
    -> wf_term b
    -> covered a (vars_hyps H)
    -> covered b (vars_hyps H)
    -> wf_rule2 (rule_cequiv_subst_concl2 H x C a b t e).
Proof.
  introv wa wb cova covb wf i; allsimpl; repndors; subst; tcsp;
  allunfold @wf_bseq; repnd; wfseq; auto.

  - apply wf_term_subst; auto.
    apply lsubst_wf_term in wf1; auto.

  - apply covered_subst; auto.
    apply covered_subst_implies in wf; auto.

  - apply wf_cequiv; auto.
Qed.

Lemma rule_cequiv_subst_concl2_true_ext_lib {o} :
  forall lib (H  : @barehypotheses o)
         (x : NVar)
         (C a b t e : NTerm),
    rule_true_ext_lib lib (rule_cequiv_subst_concl2 H x C a b t e).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_cequiv_subst_concl2_true3.
Qed.


(* begin hide *)

(* end hide *)

Lemma alpha_eq_lsubst_aux_trivial {o} :
  forall (t : @NTerm o) sub,
    disjoint (dom_sub sub) (free_vars t)
    -> disjoint (bound_vars t) (sub_free_vars sub)
    -> alpha_eq (lsubst_aux t sub) t.
Proof.
  nterm_ind t as [v|f|op bs ind] Case ; introv disj1 disj2; simpl in *; tcsp.

  - allrw disjoint_singleton_r.
    rewrite sub_find_none_if; auto.

  - apply alpha_eq_oterm_combine; autorewrite with list; dands; auto.
    introv i.
    rewrite combine_map_r in i.
    apply in_map_iff in i; exrepnd; ginv.
    destruct a as [l t]; simpl.
    apply alpha_eq_bterm_congr.
    eapply ind;[eauto| |].

    + rw <- @dom_sub_sub_filter.
      introv i j.
      apply in_remove_nvars in i; repnd.
      applydup disj1 in i0.
      destruct i2.
      apply lin_flat_map.
      eexists; dands; eauto; simpl.
      apply in_remove_nvars; dands; auto.

    + introv i j.
      pose proof (disj2 t0) as q; autodimp q hyp.
      { apply lin_flat_map; eexists; dands; eauto; simpl.
        apply in_app_iff; tcsp. }
      apply subset_sub_free_vars_sub_filter in j; tcsp.
Qed.

Lemma alpha_eq_lsubst_trivial {o} :
  forall (t : @NTerm o) sub,
    disjoint (dom_sub sub) (free_vars t)
    -> alpha_eq (lsubst t sub) t.
Proof.
  introv disj.
  pose proof (unfold_lsubst sub t) as q; exrepnd.
  allrw.
  eapply alpha_eq_trans;[|apply alpha_eq_sym;eauto].
  apply alphaeq_preserves_free_vars in q1.
  rewrite q1 in disj.
  clear dependent t.
  apply alpha_eq_lsubst_aux_trivial; auto.
Qed.

Hint Resolve alphaeq_preserves_wf_term : slow.

Lemma alpha_eq_preserves_cover_vars {o} :
  forall (t u : @NTerm o) s,
    alpha_eq t u
    -> cover_vars t s
    -> cover_vars u s.
Proof.
  introv aeq cov.
  unfold cover_vars, over_vars in *.
  apply alphaeq_preserves_free_vars in aeq.
  allrw <- ; auto.
Qed.
Hint Resolve alpha_eq_preserves_cover_vars : slow.

Lemma alpha_eq_preserves_similarity_middle {o} :
  forall lib s1 s2 H z (T U : @NTerm o) J,
    alpha_eq T U
    -> similarity lib s1 s2 (snoc H (mk_hyp z T) ++ J)
    -> similarity lib s1 s2 (snoc H (mk_hyp z U) ++ J).
Proof.
  introv aeq sim.

  allrw @similarity_app.
  exrepnd; subst.
  allrw length_snoc.

  apply similarity_snoc in sim5; simpl in sim5.
  exrepnd; subst.
  allrw length_snoc; cpx.

  exists (snoc s1a0 (z,t1)) s1b (snoc s2a0 (z,t2)) s2b.
  allrw length_snoc.
  dands; auto.

  assert (wf_term U) as wfu by eauto 2 with slow.

  assert (cover_vars U s1a0) as covu by eauto 2 with slow.

  sim_snoc2; dands; auto.
  eapply alphaeqc_preserving_equality;[eauto|].
  unfold alphaeqc; simpl.
  apply lsubst_alpha_congr2; auto.
Qed.

Lemma alpha_eq_preserves_eq_hyps_middle {o} :
  forall lib s1 s2 H z (T U : @NTerm o) J,
    alpha_eq T U
    -> eq_hyps lib s1 s2 (snoc H (mk_hyp z T) ++ J)
    -> eq_hyps lib s1 s2 (snoc H (mk_hyp z U) ++ J).
Proof.
  introv aeq sim.

  allrw @eq_hyps_app.
  exrepnd; subst.
  allrw length_snoc.

  apply eq_hyps_snoc in sim5; simpl in sim5.
  exrepnd; subst.
  allrw length_snoc; cpx.

  exists (snoc s1a0 (z,t1)) s1b (snoc s2a0 (z,t2)) s2b.
  allrw length_snoc.
  dands; auto.

  assert (wf_term U) as wfu by eauto 2 with slow.
  assert (cover_vars U s1a0) as covu1 by eauto 2 with slow.
  assert (cover_vars U s2a0) as covu2 by eauto 2 with slow.

  apply eq_hyps_snoc.
  exists s1a0 s2a0 t1 t2 wfu covu1 covu2; simpl; dands; auto.

  eapply tequality_respects_alphaeqc_left;
    [|eapply tequality_respects_alphaeqc_right;
      [|eauto] ];
    unfold alphaeqc; simpl;
      apply lsubst_alpha_congr2; auto.
Qed.

Lemma alpha_eq_preserves_hyps_functionality_middle {o} :
  forall lib s1 H z (T U : @NTerm o) J,
    alpha_eq T U
    -> hyps_functionality lib s1 (snoc H (mk_hyp z T) ++ J)
    -> hyps_functionality lib s1 (snoc H (mk_hyp z U) ++ J).
Proof.
  introv aeq hf sim.
  pose proof (hf s') as q.
  autodimp q hyp.

  {
    eapply alpha_eq_preserves_similarity_middle;[|eauto].
    apply alpha_eq_sym; auto.
  }

  {
    eapply alpha_eq_preserves_eq_hyps_middle;[|eauto]; auto.
  }
Qed.


(**

  The following rule states that we can always replace an [a] for a
  [b] in an hypothesis of a sequent if [a] and [b] are computationally
  equivalent:
<<
  H, z : T[a], J |- C ext t

    By cequivSubstHyp

    H, z : T[b], J |- C ext t
    H, z : T[a], J |- a ~ b
>>
 *)

Definition rule_cequiv_subst_hyp_concl {o} (H : @bhyps o) z T x a J C t :=
  mk_baresequent (snoc H (mk_hyp z (subst T x a)) ++ J) (mk_concl C t).

Definition rule_cequiv_subst_hyp_hyp1 {o} (H : @bhyps o) z T x b J C t :=
  mk_baresequent (snoc H (mk_hyp z (subst T x b)) ++ J) (mk_concl C t).

Definition rule_cequiv_subst_hyp_hyp2 {o} (H : @bhyps o) z T x a J b e :=
  mk_baresequent (snoc H (mk_hyp z (subst T x a)) ++ J) (mk_concl (mk_cequiv a b) e).

Definition rule_cequiv_subst_hyp {o}
           (H J : @barehypotheses o)
           (x z : NVar)
           (C T a b t e : NTerm) :=
  mk_rule
    (rule_cequiv_subst_hyp_concl H z T x a J C t)
    [ rule_cequiv_subst_hyp_hyp1 H z T x b J C t,
      rule_cequiv_subst_hyp_hyp2 H z T x a J b e
    ]
    [].

Lemma rule_cequiv_subst_hyp_true3 {o} :
  forall lib (H J : @barehypotheses o)
         (x z : NVar)
         (C T a b t e : NTerm),
    rule_true3 lib (rule_cequiv_subst_hyp H J x z C T a b t e).
Proof.
  intros.
  unfold rule_cequiv_subst_hyp, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
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
  assert (!LIn z (vars_hyps H)
          # !LIn z (vars_hyps J)
          # disjoint (vars_hyps H) (vars_hyps J)) as vhyps.
  {
    clear hyp1 hyp2.
    dwfseq.
    sp.
  }

  destruct vhyps as [ nizH vhyps].
  destruct vhyps as [ nizJ disjHJ ].
  (* done with proving these simple facts *)

  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.

  assert (wf_term T) as wT.
  {
    clear hyp1 hyp2.
    allapply @vswf_hypotheses_nil_implies.
    allrw @wf_hypotheses_app; repnd.
    allrw @wf_hypotheses_snoc; repnd; allsimpl.
    allrw @isprog_vars_eq; repnd.
    allrw @nt_wf_eq.
    allapply @lsubst_wf_term; auto.
  }


  (* first we check whether or not x is in the free variables of T
   * because to know that a and b only depend on H, we first have to
   * know that x is in T.  We don't get that a and b only depend on
   * H from hyp2 because hyp2 can use the other hypotheses too. *)
  generalize (in_deq NVar deq_nvar x (free_vars T)); introv i.
  destruct i as [i | i].

  {
    (* First, we assume that x is in the free variables of T.
     * We can now prove that a and b depend on H only. *)

    assert (covered a (vars_hyps H)) as cvah.
    {
      clear hyp1 hyp2.
      allapply @vswf_hypotheses_nil_implies.
      allrw @wf_hypotheses_app; repnd.
      allrw @wf_hypotheses_snoc; repnd; allsimpl.
      allrw @isprog_vars_eq; repnd.
      unfold covered.
      generalize (eqvars_free_vars_disjoint T [(x,a)]).
      introv xx; rw @fold_subst in xx; simpl in xx.
      apply subvars_eqvars with (s2 := vars_hyps H) in xx; auto.
      rw subvars_prop in xx.
      rw subvars_prop; introv j.
      revert xx; boolvar; try (complete sp); simpl; intro xx.
      apply xx; rw in_app_iff; rw app_nil_r; sp.
    }

    assert (covered b (vars_hyps H)) as cvbh.
    {
      clear hyp1 hyp2.
      allapply @vswf_hypotheses_nil_implies.
      allrw @wf_hypotheses_app; repnd.
      allrw @wf_hypotheses_snoc; repnd; allsimpl.
      allrw @isprog_vars_eq; repnd.
      unfold covered.
      pose proof (eqvars_free_vars_disjoint T [(x,b)]) as xx.
      rw @fold_subst in xx; simpl in xx.
      apply subvars_eqvars with (s2 := vars_hyps H) in xx; auto.
      rw subvars_prop in xx.
      rw subvars_prop; introv j.
      revert xx; boolvar; try (complete sp); simpl; intro xx.
      apply xx; rw in_app_iff; rw app_nil_r; sp.
    }

    assert (covered T (snoc (vars_hyps H) x)) as covT.
    {
      clear hyp1 hyp2.
      allapply @vswf_hypotheses_nil_implies.
      allrw @wf_hypotheses_app; repnd.
      allrw @wf_hypotheses_snoc; repnd; allsimpl.
      allrw @isprog_vars_eq; repnd.
      unfold covered.
      pose proof (eqvars_free_vars_disjoint T [(x,b)]) as xx.
      rw @fold_subst in xx; simpl in xx.
      apply subvars_eqvars with (s2 := vars_hyps H) in xx; auto.
      rw subvars_prop in xx.
      rw subvars_prop; introv j.
      revert xx; boolvar; try (complete sp); simpl; intro xx.
      rw in_snoc.
      destruct (deq_nvar x0 x); subst; sp.
      left; apply xx; rw in_app_iff; rw app_nil_r; rw in_remove_nvars; rw in_single_iff; sp.
    }

    assert (!LIn z (free_vars a))
      as niza
        by (intro j; unfold covered in cvah;
            rw subvars_prop in cvah; apply cvah in j; sp).

    assert (!LIn z (free_vars b))
      as nizb
        by (intro j; unfold covered in cvbh;
            rw subvars_prop in cvbh; apply cvbh in j; sp).

    assert (disjoint (free_vars a) (vars_hyps J))
      as daj
        by (introv j k; unfold covered in cvah;
            rw subvars_prop in cvah; apply cvah in j; sp;
            apply disjHJ in j; sp).

    assert (disjoint (free_vars b) (vars_hyps J))
      as dbj
        by (introv j k; unfold covered in cvbh;
            rw subvars_prop in cvbh; apply cvbh in j; sp;
            apply disjHJ in j; sp).

    assert (subvars (free_vars (subst T x a)) (vars_hyps H)) as svaH.
    {
      pose proof (eqvars_free_vars_disjoint T [(x,a)]) as xx.
      apply eqvars_sym in xx.
      apply subvars_eqvars with (s2 := vars_hyps H) in xx; auto.
      rw subvars_prop; introv; simpl.
      rw in_app_iff; rw in_remove_nvars; rw in_single_iff.
      boolvar; simpl; try (complete sp).
      rw app_nil_r; intro j; repdors; repnd.
      try (complete (unfold covered in covT; rw subvars_prop in covT;
                     apply covT in j1; rw in_snoc in j1; allrw; sp)).
      try (complete (unfold covered in cvah; rw subvars_prop in cvah;
                     apply cvah in j; sp)).
    }

    assert (subvars (free_vars (subst T x b)) (vars_hyps H)) as svbH.
    {
      pose proof (eqvars_free_vars_disjoint T [(x,b)]) as xx.
      apply eqvars_sym in xx.
      apply subvars_eqvars with (s2 := vars_hyps H) in xx; auto.
      rw subvars_prop; introv; simpl.
      rw in_app_iff; rw in_remove_nvars; rw in_single_iff.
      boolvar; simpl; try (complete sp).
      rw app_nil_r; intro j; repdors; repnd.
      try (complete (unfold covered in covT; rw subvars_prop in covT;
                     apply covT in j1; rw in_snoc in j1; allrw; sp)).
      try (complete (unfold covered in cvbh; rw subvars_prop in cvbh;
                     apply cvbh in j; sp)).
    }

    assert (subvars (free_vars T) (x :: vars_hyps H))
      as svTH
        by (rw subvars_prop in covT; rw subvars_prop; introv j;
            apply covT in j; rw in_snoc in j; simpl; sp).

    generalize (hyp1 s1 s2); clear hyp1; intro hyp1.

    autodimp hyp1 hyp.

    {
      (* First, we prove that the hypotheses of the first sequent are functional *)
      introv sim'.
      rw @similarity_app in sim'; simpl in sim'; exrepnd; subst; allrw length_snoc; cpx.
      rw @similarity_snoc in sim'5; simpl in sim'5; exrepnd; subst; allrw length_snoc; cpx.

      rw @eq_hyps_app.
      exists (snoc s1a0 (z, t1)) s1b (snoc s2a0 (z, t2)) s2b.
      allrw length_snoc; dands; try (complete sp).

      {
        assert (cover_vars (subst T x b) s2a0)
          as cov2
            by (apply cover_vars_change_sub with (sub1 := s1a0); sp;
                allapply @similarity_dom; repnd; allrw; sp).

        rw @eq_hyps_snoc; simpl.
        exists s1a0 s2a0 t1 t2 w p cov2.
        dands; try (complete sp).

        {
          assert (wf_term (subst T x a)) as wfsa.
          {
            clear hyp2.
            apply @lsubst_preserves_wf_term; simpl; auto.
            unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp.
            allrw <- @wf_cequiv_iff; tcsp.
          }

          assert (cover_vars (subst T x a) s1a0)
            as cova1 by (rw @cover_vars_eq; allapply @similarity_dom; repnd; allrw; sp).

          dup eqh as hf.

          apply hyps_functionality_init_seg
            with (s3 := s2b) in eqh; auto.
          apply @hyps_functionality_init_seg_snoc2
            with (t' := t2) (w := wfsa) (c := cova1) in eqh.
          apply eqh in sim'6; auto.

          generalize (hyp2 (snoc s1a0 (z,t1) ++ s1b) s2 hf sim); clear hyp2; intro hyp2; exrepnd.
          lsubst_tac.
          apply equality_in_mkc_cequiv in hyp1; repnd.
          clear hyp2 hyp3.
          spcast.

          assert (cover_vars_upto T (csub_filter s1a0 [x]) [x])
            as covT1
              by (unfold cover_vars_upto; unfold covered in covT;
                  rw @dom_csub_csub_filter;
                  rw subvars_app_remove_nvars_r; simpl;
                  allapply @similarity_dom; repnd; allrw; sp).

          repeat (lsubstc_subst_aeq2;[]).

          apply cequivc_preserving_equality
            with (A := substc (lsubstc b wt0 s1a0 c6) x
                              (lsubstc_vars T wT (csub_filter s1a0 [x]) [x] covT1));
            proof_irr; auto;
            try (complete (apply cequivc_sym; eauto with cequivc)).
        }

        {
          (* now we prove the tequality of T[x\b] *)
          assert (wf_term (subst T x a)) as wfsa.
          {
            clear hyp2.
            apply @lsubst_preserves_wf_term; sp.
            unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp.
            allrw <- @wf_cequiv_iff; tcsp.
          }

          assert (cover_vars (subst T x a) s1a0)
            as covsa1 by (rw @cover_vars_eq; allapply @similarity_dom; repnd; allrw; sp).

          generalize (eqh (snoc s2a0 (z,t1) ++ s1b)); intro eqhy.
          autodimp eqhy hyp.
          rw @similarity_app; simpl.
          exists (snoc s1a0 (z, t1)) s1b (snoc s2a0 (z, t1)) s1b; allrw length_snoc; sp.
          rw @similarity_snoc; simpl.
          exists s1a0 s2a0 t1 t1 wfsa covsa1; sp.

          {
            rw @similarity_app in sim; simpl in sim; exrepnd.
            apply app_split in sim0; allrw length_snoc; repnd; subst;
              try (complete (allapply @similarity_dom; repnd; allrw; sp)).
            rw @similarity_snoc in sim5; simpl in sim5; exrepnd; cpx; proof_irr.
            apply equality_refl in sim2; sp.
          }

          {
            apply @similarity_refl in sim'1; sp.
          }

          {
            rw @eq_hyps_app in eqhy; simpl in eqhy; exrepnd.
            apply app_split in eqhy0; allrw length_snoc; repnd; subst; cpx;
              try (complete (allapply @similarity_dom; repnd; allrw; sp)).
            apply app_split in eqhy2; allrw length_snoc; repnd; subst; cpx;
              try (complete (allapply @similarity_dom; repnd; allrw; sp)).
            rw @eq_hyps_snoc in eqhy5; simpl in eqhy5; exrepnd; cpx.

            (* now we prove the tequality from eqhy0 *)

            generalize (hyp2 (snoc s1a (z,t0) ++ s2b0)
                             (snoc s2a (z,t0) ++ s2b0)
                             eqh); clear hyp2; intro hyp2.
            (* before using hyp2 we have to prove a few things *)
            autodimp hyp2 hyp.

            {
              rw @similarity_app; simpl.
              exists (snoc s1a (z,t0)) s2b0 (snoc s2a (z,t0)) s2b0; allrw length_snoc; sp.
              rw @similarity_snoc; simpl.
              exists s1a s2a t0 t0 w0 p1; sp.

              {
                rw @similarity_app in sim; simpl in sim; exrepnd.
                apply app_split in sim0; allrw length_snoc; repnd; subst;
                  try (complete (allapply @similarity_dom; repnd; allrw; sp)).
                rw @similarity_snoc in sim5; simpl in sim5; exrepnd; cpx; proof_irr.
                apply equality_refl in sim2; sp.
              }

              {
                apply @similarity_refl in sim'1; sp.
              }
            }

            (* now we start using hyp2 *)
            exrepnd.
            lsubst_tac.
            rw @tequality_mkc_cequiv in hyp0.
            apply equality_in_mkc_cequiv in hyp1; repnd.
            clear hyp2 hyp3.
            appdup hyp0 hyp1.
            spcast.

            assert (cover_vars_upto T (csub_filter s1a [x]) [x])
              as cvuT1
                by (unfold cover_vars_upto; unfold covered in covT;
                    rw @dom_csub_csub_filter;
                    rw subvars_app_remove_nvars_r; simpl;
                    allapply @similarity_dom; repnd; allrw; sp).

            assert (cover_vars_upto T (csub_filter s2a [x]) [x])
              as cvuT2
                by (unfold cover_vars_upto; unfold covered in covT;
                    rw @dom_csub_csub_filter;
                    rw subvars_app_remove_nvars_r; simpl;
                    allapply @similarity_dom; repnd; allrw; sp).

            repeat (lsubstc_subst_aeq2;[]).
            proof_irr.

            apply tequality_respects_cequivc_left
              with (T1 := substc (lsubstc a wt2 s1a ct4) x
                                 (lsubstc_vars T wT (csub_filter s1a [x]) [x] cb2));
              try (complete (eauto with cequivc)).

            apply tequality_respects_cequivc_right
              with (T2 := substc (lsubstc a wt2 s2a ct5) x
                                 (lsubstc_vars T wT (csub_filter s2a [x]) [x] cb3));
              auto;
              try (complete (eauto with cequivc)).
          }
        }
      }


      (* Now we prove the sub_eq_hyps *)

      assert (wf_term (subst T x a)) as wfsa.
      {
        clear hyp2.
        apply @lsubst_preserves_wf_term; sp.
        unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp.
        allrw <- @wf_cequiv_iff; tcsp.
      }

      assert (cover_vars (subst T x a) s1a0)
        as covsa1 by (rw @cover_vars_eq; allapply @similarity_dom; repnd; allrw; sp).

      generalize (hyp2 (snoc s1a0 (z,t1) ++ s1b)
                       (snoc s2a0 (z,t1) ++ s1b)
                       eqh); clear hyp2; intro hyp2.
      (* before using hyp2 we have to prove a few things *)
      autodimp hyp2 hyp.

      {
        rw @similarity_app; simpl.
        exists (snoc s1a0 (z,t1)) s1b (snoc s2a0 (z,t1)) s1b; allrw length_snoc; sp.

        {
          rw @similarity_snoc; simpl.
          exists s1a0 s2a0 t1 t1 wfsa covsa1; sp.

          rw @similarity_app in sim; simpl in sim; exrepnd.
          apply app_split in sim0; allrw length_snoc; repnd; subst;
            try (complete (allapply @similarity_dom; repnd; allrw; sp)).
          rw @similarity_snoc in sim5; simpl in sim5; exrepnd; cpx; proof_irr.
          apply equality_refl in sim2; sp.
        }

        apply @similarity_refl in sim'1; sp.
      }

      (* now we start using hyp2 *)
      exrepnd.
      lsubst_tac.
      rw @tequality_mkc_cequiv in hyp0.
      apply equality_in_mkc_cequiv in hyp1; repnd.
      clear hyp2 hyp3.
      appdup hyp0 hyp1.
      spcast.

      generalize (eqh (snoc s2a0 (z,t2) ++ s2b)); intro eqhy.
      autodimp eqhy hyp.
      rw @similarity_app; simpl.
      exists (snoc s1a0 (z,t1)) s1b (snoc s2a0 (z,t2)) s2b; allrw length_snoc; sp.

      {
        rw @similarity_snoc; simpl.
        exists s1a0 s2a0 t1 t2 wfsa covsa1; sp.

        assert (cover_vars_upto T (csub_filter s1a0 [x]) [x])
          as cvuT1
            by (unfold cover_vars_upto; unfold covered in covT;
                rw @dom_csub_csub_filter;
                rw subvars_app_remove_nvars_r; simpl;
                allapply @similarity_dom; repnd; allrw; sp).

        repeat (lsubstc_subst_aeq2;[]).
        proof_irr.

        apply cequivc_preserving_equality
          with (A := substc (lsubstc b wt0 s1a0 ct2) x
                            (lsubstc_vars T wT (csub_filter s1a0 [x]) [x] cb0));
          auto;
          try (complete (apply cequivc_sym; eauto with cequivc)).
      }

      rw @eq_hyps_app in eqhy; exrepnd.
      apply app_split in eqhy0; allrw length_snoc; repnd; subst; cpx;
        try (complete (allapply @similarity_dom; repnd; allrw; sp)).
      apply app_split in eqhy2; allrw length_snoc; repnd; subst; cpx;
        try (complete (allapply @similarity_dom; repnd; allrw; sp)).
    }


    (* We're done proving the hyps_functionality part of hyp1.
     * We now prove the similarity part of hyp1 *)
    autodimp hyp1 hyp.

    {
      rw @similarity_app in sim; exrepnd; subst; cpx.
      rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx.

      generalize (hyp2 (snoc s1a0 (z,t1) ++ s1b)
                       (snoc s2a0 (z,t1) ++ s1b)
                       eqh); clear hyp2; intro hyp2.
      (* before using hyp2 we have to prove a few things *)
      autodimp hyp2 hyp.

      {
        rw @similarity_app; simpl.
        exists (snoc s1a0 (z,t1)) s1b (snoc s2a0 (z,t1)) s1b; allrw length_snoc; sp.

        {
          rw @similarity_snoc; simpl.
          exists s1a0 s2a0 t1 t1 w p; sp.

          apply equality_refl in sim2; sp.
        }

        apply @similarity_refl in sim1; sp.
      }

      (* now we start using hyp2 *)
      exrepnd.
      lsubst_tac.
      rw @tequality_mkc_cequiv in hyp0.
      apply equality_in_mkc_cequiv in hyp1; repnd.
      clear hyp2 hyp3.
      appdup hyp0 hyp1.
      spcast.

      assert (wf_term (subst T x b))
        as wfsb
          by (apply @lsubst_preserves_wf_term; sp;
              unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp).

      assert (cover_vars (subst T x b) s1a0)
        as covb1 by (rw @cover_vars_eq; allapply @similarity_dom; repnd; allrw; sp).

      rw @similarity_app.
      exists (snoc s1a0 (z, t1)) s1b (snoc s2a0 (z, t2)) s2b; allrw length_snoc; sp.
      rw @similarity_snoc; simpl.
      exists s1a0 s2a0 t1 t2 wfsb covb1; sp.

      assert (cover_vars_upto T (csub_filter s1a0 [x]) [x])
        as cvuT1
          by (unfold cover_vars_upto; unfold covered in covT;
              rw @dom_csub_csub_filter;
              rw subvars_app_remove_nvars_r; simpl;
              allapply @similarity_dom; repnd; allrw; sp).

      repeat (lsubstc_subst_aeq2;[]).
      proof_irr.

      apply cequivc_preserving_equality
        with (A := substc (lsubstc a wt0 s1a0 ct2) x
                          (lsubstc_vars T wT (csub_filter s1a0 [x]) [x] cb0));
        auto;
        try (complete (eauto with cequivc)).
    }


    (* now we use hyp1 *)
    exrepnd; proof_irr; GC; sp.
  }


  assert (alpha_eq (subst T x a) T) as e1.
  { apply alpha_eq_lsubst_trivial; simpl; apply disjoint_singleton_l; auto. }

  assert (alpha_eq (subst T x b) T) as e2.
  { apply alpha_eq_lsubst_trivial; simpl; apply disjoint_singleton_l; auto. }

  pose proof (hyp1 s1 s2) as hyp1.
  repeat (autodimp hyp1 hyp).

  {
    eapply alpha_eq_preserves_hyps_functionality_middle;[|eauto].
    eapply alpha_eq_trans;[eauto|].
    apply alpha_eq_sym; auto.
  }

  {
    eapply alpha_eq_preserves_similarity_middle;[|eauto].
    eapply alpha_eq_trans;[eauto|].
    apply alpha_eq_sym; auto.
  }

  exrepnd; proof_irr; sp.
Qed.

Lemma rule_cequiv_subst_hyp_true {o} :
  forall lib (H J : @barehypotheses o)
         (x z : NVar)
         (C T a b t e : @NTerm o),
    rule_true lib (rule_cequiv_subst_hyp H J x z C T a b t e).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_cequiv_subst_hyp_true3.
Qed.

Lemma rule_cequiv_subst_hyp_true_ext_lib {o} :
  forall lib (H J : @barehypotheses o)
         (x z : NVar)
         (C T a b t e : NTerm),
    rule_true_ext_lib lib (rule_cequiv_subst_hyp H J x z C T a b t e).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_cequiv_subst_hyp_true3.
Qed.

Lemma rule_cequiv_subst_hyp_wf2 {o} :
  forall (H J : @barehypotheses o)
         (x z : NVar)
         (C T a b t e : NTerm),
    wf_term a
    -> wf_term b
    -> covered a (vars_hyps H)
    -> covered b (vars_hyps H)
    -> wf_rule2 (rule_cequiv_subst_hyp H J x z C T a b t e).
Proof.
  introv wa wb cova covb wf i; allsimpl; repndors; subst; tcsp;
    allunfold @wf_bseq; repnd; wfseq; auto.

  - allrw @vswf_hypotheses_nil_eq.
    allrw @wf_hypotheses_app; repnd.
    allrw @wf_hypotheses_snoc; repnd.
    simpl in *.
    allrw @vars_hyps_snoc; simpl in *.
    dands; auto.

    allrw @isprog_vars_eq; repnd; dands; auto.

    + apply covered_subst_implies in wf5.
      apply covered_subst; auto.

    + allrw @nt_wf_eq.
      apply wf_term_subst; auto.
      apply lsubst_wf_term in wf3; auto.

  - apply wf_cequiv; auto.

  - apply covered_app_weak_l.
    apply covered_snoc_weak; auto.

  - apply covered_app_weak_l.
    apply covered_snoc_weak; auto.
Qed.

(* begin hide *)

(* end hide *)
