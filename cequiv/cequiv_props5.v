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

  Authors: Vincent Rahli

*)


Require Export cequiv_props2.
Require Export compare_cterm.
Require Export cequiv_bind.
Require Export subst_tacs.


Lemma hasvaluec_mkc_try_implies {o} :
  forall lib t n v (c : @CVTerm o [v]),
    hasvaluec lib (mkc_try t n v c)
    ->
    (
      {u : CTerm
       & reduces_toc lib t u
       # iscvalue u
       # reduces_toc lib (mkc_try t n v c) (mkc_atom_eq n n u mkc_bottom)
      }
      [+]
      {m : CTerm
       & {u : CTerm
       & reduces_toc lib t (mkc_exception m u)
       # reduces_toc lib (mkc_try t n v c) (mkc_atom_eq n m (substc u v c) (mkc_exception m u))
      } }
    ).
Proof.
  introv hv.
  destruct_cterms; simpl in *.
  unfold reduces_toc; simpl.
  unfold hasvaluec in *; simpl in *.
  unfold hasvalue in hv; exrepnd.
  unfold computes_to_value in hv0; repnd.
  unfold reduces_to in hv1; exrepnd.
  unfold iscvalue; simpl.

  revert dependent x0.

  induction k; introv ispx0 r.

  {
    allrw @reduces_in_atmost_k_steps_0; subst.
    inversion hv0; subst; simpl in *; tcsp.
  }

  {
    allrw @reduces_in_atmost_k_steps_S; exrepnd.

    csunf r1; simpl in *.

    destruct x0 as [z|F|op bs]; ginv.

    {
      left.
      exists (mk_ct (sterm F) ispx0); simpl.
      dands; eauto 3 with slow.
    }

    {
      dopid op as [can|ncan|exc|abs] Case; simpl; ginv; auto.

      - left.
        exists (mk_ct (oterm (Can can) bs) ispx0); simpl.
        dands; eauto 3 with slow.

      - remember (compute_step lib (oterm (NCan ncan) bs)) as cs.
        destruct cs; simpl in *; ginv.
        symmetry in Heqcs.
        fold_terms.
        applydup @preserve_compute_step in Heqcs; eauto 2 with slow.
        applydup IHk in r0; auto; eauto 2 with slow;[].
        repndors; exrepnd; destruct_cterms; simpl in *.

        + left.
          exists (mk_ct x0 i0); simpl; dands; auto.

          * eapply reduces_to_if_split2; eauto.

          * eapply reduces_to_trans;[|eauto].
            apply reduces_to_prinarg; eauto 2 with slow.

        + right.
          exists (mk_ct x2 i2) (mk_ct x0 i0); simpl; dands; auto.

          * eapply reduces_to_if_split2; eauto.

          * eapply reduces_to_trans;[|eauto].
            apply reduces_to_prinarg; eauto 2 with slow.

      - destruct bs as [|b1 bs]; simpl in *; ginv.
        destruct b1 as [l1 t1]; simpl in *; ginv.
        destruct l1 as [|v1 l1]; simpl in *; ginv.
        destruct bs as [|b2 bs]; simpl in *; ginv.
        destruct b2 as [l2 t2]; simpl in *; ginv.
        destruct l2 as [|v2 l2]; simpl in *; ginv.
        destruct bs as [|]; simpl in *; ginv.
        fold_terms.
        right.

        allrw @isprog_exception_iff; repnd.
        exists (mk_ct t1 ispx1) (mk_ct t2 ispx0); simpl.
        dands; eauto 2 with slow.

      - remember (compute_step lib (oterm (Abs abs) bs)) as cs.
        destruct cs; simpl in *; ginv.
        symmetry in Heqcs.
        fold_terms.
        applydup @preserve_compute_step in Heqcs; eauto 2 with slow.
        applydup IHk in r0; auto; eauto 2 with slow;[].
        repndors; exrepnd; destruct_cterms; simpl in *.

        + left.
          exists (mk_ct x0 i0); simpl; dands; auto.

          * eapply reduces_to_if_split2; eauto.

          * eapply reduces_to_trans;[|eauto].
            apply reduces_to_prinarg; eauto 2 with slow.

        + right.
          exists (mk_ct x2 i2) (mk_ct x0 i0); simpl; dands; auto.

          * eapply reduces_to_if_split2; eauto.

          * eapply reduces_to_trans;[|eauto].
            apply reduces_to_prinarg; eauto 2 with slow.
    }
  }
Qed.

Lemma computes_to_valc_excc_false {o} :
  forall lib (a b n c : @CTerm o),
    computes_to_valc lib a b
    -> computes_to_excc lib n a c
    -> False.
Proof.
  introv compv compe.
  destruct_cterms; simpl in *.
  unfold computes_to_valc in *; unfold computes_to_excc in *; simpl in *.
  destruct compv as [r iv].
  eapply reduces_to_eq_val_like in compe; try (exact r); eauto 3 with slow.
  subst.
  inversion iv; subst; simpl in *; auto.
Qed.

Lemma hasvaluec_mkc_try2_implies {o} :
  forall lib t1 t2 n1 n2 v (c1 c2 : @CVTerm o [v]),
    hasvaluec lib (mkc_try t1 n1 v c1)
    -> hasvaluec lib (mkc_try t2 n2 v c2)
    -> cequivc lib t1 t2
    ->
    (
      {u1 : CTerm
       & {u2 : CTerm
       & reduces_toc lib t1 u1
       # reduces_toc lib t2 u2
       # iscvalue u1
       # iscvalue u2
       # cequivc lib u1 u2
       # reduces_toc lib (mkc_try t1 n1 v c1) (mkc_atom_eq n1 n1 u1 mkc_bottom)
       # reduces_toc lib (mkc_try t2 n2 v c2) (mkc_atom_eq n2 n2 u2 mkc_bottom)
      }}
      [+]
      {m1 : CTerm
       & {m2 : CTerm
       & {u1 : CTerm
       & {u2 : CTerm
       & reduces_toc lib t1 (mkc_exception m1 u1)
       # reduces_toc lib t2 (mkc_exception m2 u2)
       # reduces_toc lib (mkc_try t1 n1 v c1) (mkc_atom_eq n1 m1 (substc u1 v c1) (mkc_exception m1 u1))
       # reduces_toc lib (mkc_try t2 n2 v c2) (mkc_atom_eq n2 m2 (substc u2 v c2) (mkc_exception m2 u2))
      }}}}
    ).
Proof.
  introv hv1 hv2 ceqt.
  apply hasvaluec_mkc_try_implies in hv1.
  apply hasvaluec_mkc_try_implies in hv2.
  repndors; exrepnd.

  - left.
    exists u0 u; dands; auto.
    eapply cequivc_trans;
      [apply cequivc_sym;
       apply reduces_toc_implies_cequivc;
       eauto
      |].
    eapply cequivc_trans;[eauto|].
    apply reduces_toc_implies_cequivc.
    eauto.

  - assert False; tcsp.
    eapply cequivc_trans in ceqt;
      [|apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        eauto].
    apply cequivc_sym in ceqt.
    eapply cequivc_trans in ceqt;
      [|apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        eauto].
    apply cequivc_sym in ceqt.
    apply (cequivc_mkc_exception _ _ _ m u0) in ceqt;
      [|destruct_cterms;
        unfold computes_to_excc; simpl;
        apply computes_to_exception_refl].
    exrepnd.
    apply (computes_to_valc_refl lib) in hv3.

    eapply computes_to_valc_excc_false in ceqt0; eauto.

  - assert False; tcsp.
    eapply cequivc_trans in ceqt;
      [|apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        eauto].
    apply cequivc_sym in ceqt.
    eapply cequivc_trans in ceqt;
      [|apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        eauto].
    apply (cequivc_mkc_exception _ _ _ m u) in ceqt;
      [|destruct_cterms;
        unfold computes_to_excc; simpl;
        apply computes_to_exception_refl].
    exrepnd.
    apply (computes_to_valc_refl lib) in hv4.

    eapply computes_to_valc_excc_false in ceqt0; eauto.

  - right.
    exists m0 m u0 u; dands; auto.
Qed.

Lemma approx_star_bterm_nobnd_iff {o} :
  forall lib op (a b : @NTerm o),
    op <> NCan NFresh
    -> approx_star_bterm lib op (nobnd a) (nobnd b)
       <=> approx_star lib a b.
Proof.
  introv opd.
  unfold approx_star_bterm, blift_sub.
  split; intro h; exrepnd.

  - repndors; repnd; tcsp.
    apply alpha_eq_bterm_nobnd in h2.
    apply alpha_eq_bterm_nobnd in h0.
    exrepnd.
    unfold nobnd in *; ginv.
    eapply approx_star_alpha_fun_l;[|apply alpha_eq_sym;eauto].
    eapply approx_star_alpha_fun_r;[|apply alpha_eq_sym;eauto].
    auto.

  - exists ([] : list NVar) a b.
    dands; auto.
Qed.

Lemma implies_approx_try {o} :
  forall lib a1 a2 b1 b2 v (t1 t2 : @NTerm o),
    isprog a1
    -> isprog a2
    -> isprog b1
    -> isprog b2
    -> isprog_vars [v] t1
    -> isprog_vars [v] t2
    -> cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v u) (subst t2 v u))
    -> approx lib (mk_try a1 b1 v t1) (mk_try a2 b2 v t2).
Proof.
  introv ispa1 ispa2 ispb1 ispb2 isp1 isp2 ceqa ceqb imp.

  apply howetheorem1;
    try (apply isprogram_try);
    eauto 3 with slow;
    try (complete (apply isprog_vars_eq in isp1; tcsp));
    try (complete (apply isprog_vars_eq in isp2; tcsp)).

  apply approx_star_congruence; unfold num_bvars; simpl; auto.

  allrw @approx_starbts_cons.
  dands; auto;
    try (apply approx_star_bterm_nobnd_iff;
         auto; try (complete (intro xx; inversion xx)));
    eauto 3 with slow.

  - apply le_bin_rel_approx1_eauto; auto.
    destruct ceqa; tcsp.

  - apply le_bin_rel_approx1_eauto; auto.
    destruct ceqb; tcsp.

  - unfold approx_star_bterm, blift_sub.
    exists [v] t1 t2; dands; auto.
    left; dands; auto; try (complete (intro xx; inversion xx)).

    apply approx_star_iff_approx_open.
    apply approx_open_simpler_equiv.

    unfold simpl_olift.
    dands; eauto 3 with slow.
    introv ps ispt1 ispt2.

    applydup @isprog_vars_eq in isp1.
    applydup @isprog_vars_eq in isp2.
    repnd.

    pose proof (cl_lsubst_trim_select t1 sub [v] mk_axiom) as q1.
    simpl in q1.
    repeat (autodimp q1 hyp); eauto 3 with slow.

    {
      introv i.
      split; intro q; repndors; subst; tcsp.
      - apply isprogram_lsubst_iff in ispt1; repnd.
        apply ispt1 in i; exrepnd.
        apply sub_find_some in i1.
        apply in_sub_eta in i1; tcsp.
      - apply subvars_eq in isp5; apply isp5 in i; simpl in i; auto.
    }

    pose proof (cl_lsubst_trim_select t2 sub [v] mk_axiom) as q2.
    simpl in q2.
    repeat (autodimp q2 hyp); eauto 3 with slow.

    {
      introv i.
      split; intro q; repndors; subst; tcsp.
      - apply isprogram_lsubst_iff in ispt2; repnd.
        apply ispt2 in i; exrepnd.
        apply sub_find_some in i1.
        apply in_sub_eta in i1; tcsp.
      - apply subvars_eq in isp4; apply isp4 in i; simpl in i; auto.
    }

    rewrite q1, q2.
    pose proof (imp (sub_find_def sub v mk_axiom)) as q.
    autodimp q hyp.

    { apply implies_isprog_sub_find_def; auto. }

    destruct q; tcsp.
Qed.

Lemma implies_approxc_try {o} :
  forall lib a1 a2 b1 b2 v (t1 t2 : @CVTerm o [v]),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> (forall u : CTerm, cequivc lib (substc u v t1) (substc u v t2))
    -> approxc lib (mkc_try a1 b1 v t1) (mkc_try a2 b2 v t2).
Proof.
  introv ceqa ceqb imp.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allunfold @approxc; allsimpl.

  apply implies_approx_try; auto.
  introv isp.
  apply isprogram_eq in isp.
  pose proof (imp (mk_cterm u isp)) as k; allsimpl; auto.
Qed.

Lemma implies_cequivc_try {o} :
  forall lib a1 a2 b1 b2 v (t1 t2 : @CVTerm o [v]),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> (forall u : CTerm, cequivc lib (substc u v t1) (substc u v t2))
    -> cequivc lib (mkc_try a1 b1 v t1) (mkc_try a2 b2 v t2).
Proof.
  introv ceqa ceqb imp.
  apply cequivc_iff_approxc; dands.
  - apply implies_approxc_try; auto.
  - apply implies_approxc_try; auto; introv; apply cequivc_sym; auto.
Qed.

Lemma implies_approx_atom_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    isprog a1
    -> isprog a2
    -> isprog b1
    -> isprog b2
    -> isprog c1
    -> isprog c2
    -> isprog d1
    -> isprog d2
    -> cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib c1 c2
    -> cequiv lib d1 d2
    -> approx lib (mk_atom_eq a1 b1 c1 d1) (mk_atom_eq a2 b2 c2 d2).
Proof.
  introv ispa1 ispa2 ispb1 ispb2 ispc1 ispc2 ispd1 ispd2; introv ceqa ceqb ceqc ceqd.

  apply howetheorem1;
    try (apply isprogram_mk_atom_eq; dands; eauto 2 with slow).

  apply approx_star_congruence; unfold num_bvars; simpl; auto.

  allrw @approx_starbts_cons.
  dands; auto;
    try (apply approx_star_bterm_nobnd_iff;
         auto; try (complete (intro xx; inversion xx)));
    eauto 3 with slow.

  - apply le_bin_rel_approx1_eauto; auto.
    destruct ceqa; tcsp.

  - apply le_bin_rel_approx1_eauto; auto.
    destruct ceqb; tcsp.

  - apply le_bin_rel_approx1_eauto; auto.
    destruct ceqc; tcsp.

  - apply le_bin_rel_approx1_eauto; auto.
    destruct ceqd; tcsp.
Qed.

Lemma implies_approxc_atom_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib c1 c2
    -> cequivc lib d1 d2
    -> approxc lib (mkc_atom_eq a1 b1 c1 d1) (mkc_atom_eq a2 b2 c2 d2).
Proof.
  introv ceqa ceqb ceqc ceqd.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allunfold @approxc; allsimpl.

  apply implies_approx_atom_eq; auto.
Qed.

Lemma implies_cequivc_atom_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib c1 c2
    -> cequivc lib d1 d2
    -> cequivc lib (mkc_atom_eq a1 b1 c1 d1) (mkc_atom_eq a2 b2 c2 d2).
Proof.
  introv ceqa ceqb ceqc ceqd.
  apply cequivc_iff_approxc; dands.
  - apply implies_approxc_atom_eq; auto.
  - apply implies_approxc_atom_eq; auto; introv; apply cequivc_sym; auto.
Qed.

Lemma cover_vars_atom_eq {o} :
  forall (a b c d : @NTerm o) sub,
    cover_vars (mk_atom_eq a b c d) sub
    <=> cover_vars a sub
        # cover_vars b sub
        # cover_vars c sub
        # cover_vars d sub.
Proof.
  sp; repeat (rw cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l); sp; split; sp.
Qed.

Lemma reduces_toc_iscvalue_implies_hasvaluec {o} :
  forall lib (t u : @CTerm o),
    reduces_toc lib t u
    -> iscvalue u
    -> hasvaluec lib t.
Proof.
  introv r i.
  unfold reduces_toc in r.
  unfold iscvalue in i.
  unfold hasvaluec.
  destruct_cterms; simpl in *.
  exists x.
  split; auto.
Qed.

Lemma implies_approx_exception {o} :
  forall lib (a1 a2 b1 b2 : @NTerm o),
    isprog a1
    -> isprog a2
    -> isprog b1
    -> isprog b2
    -> cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> approx lib (mk_exception a1 b1) (mk_exception a2 b2).
Proof.
  introv ispa1 ispa2 ispb1 ispb2 ceqa ceqb.

  apply howetheorem1;
    try (apply isprogram_exception; dands; eauto 2 with slow).

  apply approx_star_congruence; unfold num_bvars; simpl; auto.

  allrw @approx_starbts_cons.
  dands; auto;
    try (apply approx_star_bterm_nobnd_iff;
         auto; try (complete (intro xx; inversion xx)));
    eauto 3 with slow.

  - apply le_bin_rel_approx1_eauto; auto.
    destruct ceqa; tcsp.

  - apply le_bin_rel_approx1_eauto; auto.
    destruct ceqb; tcsp.
Qed.

Lemma implies_approxc_exception {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> approxc lib (mkc_exception a1 b1) (mkc_exception a2 b2).
Proof.
  introv ceqa ceqb.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allunfold @approxc; allsimpl.
  apply implies_approx_exception; auto.
Qed.

Lemma implies_cequivc_exception {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib (mkc_exception a1 b1) (mkc_exception a2 b2).
Proof.
  introv ceqa ceqb.
  apply cequivc_iff_approxc; dands.
  - apply implies_approxc_exception; auto.
  - apply implies_approxc_exception; auto; introv; apply cequivc_sym; auto.
Qed.

Lemma simple_lsubstc_subst_ex2 {p} :
  forall (t : @NTerm p) x B ws s cs wt ct,
    {wb : wf_term B
     & {cb : cover_vars_upto B (csub_filter s [x]) [x]
     & alphaeqc
         (lsubstc (subst B x t) ws s cs)
         (substc (lsubstc t wt s ct) x (lsubstc_vars B wb (csub_filter s [x]) [x] cb))
    }}.
Proof.
  introv.

  pose proof (change_bvars_alpha_wspec (free_vars t) B) as q.
  destruct q as [B' [q1 q2] ].

  assert (wf_term (subst B' x t)) as wf.
  {
    allrw @wf_term_eq.
    unfold subst in *.
    allrw @nt_wf_lsubst_iff; repnd; dands; auto; simpl in *.
    { apply alphaeq_preserves_wf in q2; apply q2; auto. }
    introv i j.
    boolvar; ginv.
    apply alphaeq_preserves_free_vars in q2; rewrite <- q2 in i.
    eapply ws;[eauto|]; boolvar; auto.
  }

  assert (cover_vars (subst B' x t) s) as cov.
  {
    unfold cover_vars in *.
    unfold over_vars in *.

    eapply subvars_eqvars;[|apply eqvars_sym;apply eqvars_free_vars_disjoint].
    eapply subvars_eqvars in cs;[|apply eqvars_free_vars_disjoint].
    simpl in *.
    apply alphaeq_preserves_free_vars in q2; rewrite <- q2.
    auto.
  }

  pose proof (simple_lsubstc_subst_ex t x B' wf s cov wt ct q1) as h.
  exrepnd.

  assert (wf_term B) as wB.
  { apply lsubst_wf_term in ws; auto. }

  assert (cover_vars_upto B (csub_filter s [x]) [x]) as cB.
  {
    rw @cover_vars_eq in cs.
    unfold cover_vars_upto in *.
    apply alphaeq_preserves_free_vars in q2; rewrite q2.
    auto.
  }

  exists wB cB.

  unfold alphaeqc; simpl.

  pose proof (lsubst_alpha_congr2 (subst B x t) (subst B' x t) (csub2sub s)) as q.
  autodimp q hyp.
  { apply lsubst_alpha_congr2; auto. }
  eapply alpha_eq_trans;[exact q|]; clear q.

  assert (get_cterm (lsubstc (subst B' x t) wf s cov)
          = get_cterm (substc (lsubstc t wt s ct) x (lsubstc_vars B' wb (csub_filter s [x]) [x] cb))) as xx.
  { rewrite h1; auto. }
  simpl in xx.
  unfold csubst in xx.
  rewrite xx; clear xx.

  allrw @fold_csubst.
  apply lsubst_alpha_congr2.
  apply lsubst_alpha_congr2.
  apply alpha_eq_sym; auto.
Qed.

Lemma lsubstc_subst_snoc_aeq {o} :
  forall s (b : @NTerm o) x y a w1 w2 c1 c2,
    !LIn y (dom_csub s)
    -> (y <> x -> !LIn y (free_vars b))
    -> alphaeqc
         (lsubstc (subst b x (mk_var y)) w1 (snoc s (y, a)) c1)
         (substc a x (lsubstc_vars b w2 (csub_filter s [x]) [x] c2)).
Proof.
  introv ni d.

  pose proof (change_bvars_alpha_wspec [y] b) as q.
  destruct q as [b' [q1 q2] ].
  allrw disjoint_singleton_l.

  assert (wf_term b') as wfb'.
  {
    allrw @wf_term_eq.
    unfold subst in *.
    allrw @nt_wf_lsubst_iff; repnd; dands; auto; simpl in *.
    apply alphaeq_preserves_wf in q2; apply q2; auto.
  }

  assert (wf_term (subst b' x (mk_var y))) as wsb'.
  {
    allrw @wf_term_eq.
    unfold subst in *.
    allrw @nt_wf_lsubst_iff; repnd; dands; auto; simpl in *.
    introv i j.
    boolvar; ginv.
    eauto 3 with slow.
  }

  assert (cover_vars (subst b' x (mk_var y)) (snoc s (y, a))) as covsb'.
  {
    unfold cover_vars in *.
    unfold over_vars in *.

    eapply subvars_eqvars;[|apply eqvars_sym;apply eqvars_free_vars_disjoint].
    eapply subvars_eqvars in c1;[|apply eqvars_free_vars_disjoint].
    simpl in *.
    apply alphaeq_preserves_free_vars in q2; rewrite <- q2.
    auto.
  }

  assert (cover_vars_upto b' (csub_filter s [x]) [x]) as covub'.
  {
    unfold cover_vars_upto in *.
    apply alphaeq_preserves_free_vars in q2; rewrite <- q2; auto.
  }

  pose proof (lsubstc_subst_snoc_eq s b' x y a wsb' wfb' covsb' covub') as xx.
  repeat (autodimp xx hyp).
  { apply alphaeq_preserves_free_vars in q2; rewrite <- q2; auto. }

  assert (get_cterm (lsubstc (subst b' x (mk_var y)) wsb' (snoc s (y, a)) covsb')
          = get_cterm (substc a x (lsubstc_vars b' wfb' (csub_filter s [x]) [x] covub'))) as yy.
  { rewrite xx; auto. }
  clear xx; simpl in yy.

  destruct_cterms.
  unfold alphaeqc; simpl in *.
  unfold csubst in *; simpl in *.
  allrw @csub2sub_snoc; simpl in *.

  eapply alpha_eq_trans;
    [apply lsubst_alpha_congr2;
     apply lsubst_alpha_congr2;
     exact q2
    |].
  allrw @fold_subst.
  rewrite yy; clear yy.
  apply lsubst_alpha_congr2.
  apply lsubst_alpha_congr2.
  apply alpha_eq_sym; auto.
Qed.

Lemma cequivc_exception_implies {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o),
    cequivc lib (mkc_exception a1 b1) (mkc_exception a2 b2)
    -> cequivc lib a1 a2 # cequivc lib b1 b2.
Proof.
  introv ceq.
  destruct_cterms.
  unfold cequivc in *; simpl in *.
  destruct ceq as [apr1 apr2].

  apply approx_exception in apr1.
  apply approx_exception in apr2.
  exrepnd.
  apply reduces_to_if_isvalue_like in apr4; eauto 3 with slow.
  apply reduces_to_if_isvalue_like in apr0; eauto 3 with slow.
  ginv.
  unfold cequiv.
  dands; auto.
Qed.
