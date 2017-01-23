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


Require Export chalts.
Require Export sequents_tacs2.
Require Export cequiv_props.
Require Export subst_tacs.
Require Export per_props_equality.
Require Export per_can.
Require Export computation_cbv.
Require Export cequiv_props2.


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


(*
   H |- a = b ∈ T

     By haltsTry

     H |- (mk_try(t,n,v.c))↓
     H, x : (t)↓,
        y : mk_try(t,n,v.c) ~ if n=n then t else bottom |- a = b ∈ T
     H, m : Base,
        u : Base,
        x : t ~ exception(m,u),
        y : mk_try(t,n,v.c) ~ if n=m then c[v\u] else exception(m,u) |- a = b ∈ T
     H |- t ∈ Base
     H |- n ∈ Base
     H, v : Base |- c ∈ Base
 *)
Definition rule_halts_try_cases {o}
           (H : barehypotheses)
           (a b T t n c : @NTerm o)
           (v x y u m : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b T)))
    [
      mk_baresequent H (mk_conclax (mk_halts (mk_try t n v c))),
      mk_baresequent
        (snoc (snoc H (mk_hyp x (mk_halts t)))
              (mk_hyp y (mk_cequiv (mk_try t n v c) (mk_atom_eq n n t mk_bottom))))
        (mk_conclax (mk_equality a b T)),
      mk_baresequent
        (snoc (snoc (snoc (snoc H (mk_hyp m mk_base))
                          (mk_hyp u mk_base))
                    (mk_hyp x (mk_cequiv t (mk_exception (mk_var m) (mk_var u)))))
              (mk_hyp y (mk_cequiv (mk_try t n v c) (mk_atom_eq n (mk_var m) (subst c v (mk_var u)) (mk_exception (mk_var m) (mk_var u))))))
        (mk_conclax (mk_equality a b T)),
      mk_baresequent
        H
        (mk_conclax (mk_member t mk_base)),
      mk_baresequent
        H
        (mk_conclax (mk_member n mk_base)),
      mk_baresequent
        (snoc H (mk_hyp v mk_base))
        (mk_conclax (mk_member c mk_base))
    ]
    [].


Lemma rule_halts_try_cases_true {o} :
  forall lib
         (a b T t n c : NTerm)
         (v x y u m : NVar)
         (H : @barehypotheses o),
    rule_true lib (rule_halts_try_cases H a b T t n c v x y u m).
Proof.
  unfold rule_halts_try_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp_halts_try.
  rename Hyp1 into hyp_halts.
  rename Hyp2 into hyp_exc.
  rename Hyp3 into hyp_tbase.
  rename Hyp4 into hyp_nbase.
  rename Hyp5 into hyp_cbase.

  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_equality a b T))) as cs.
  {
    unfold closed_extract; simpl.
    apply covered_axiom.
  }

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars T)
          # !LIn x (free_vars b)
          # !LIn x (free_vars a)
          # !LIn x (free_vars t)
          # !LIn x (free_vars n)
          # (x <> v -> !LIn x (free_vars c))
          # !LIn x (vars_hyps H)
          # !LIn v (vars_hyps H)) as vhyps.

  {
    clear hyp_halts_try hyp_halts hyp_exc hyp_tbase hyp_nbase hyp_cbase.
    dwfseq.
    sp; GC;
      try (complete (discover; allapply @subset_hs_vars_hyps; sp));
      try (complete (pose proof (ct4 x) as q; rw in_remove_nvars in q;
                     simpl in q; autodimp q hyp; tcsp)).
  }

  destruct vhyps as [ nxT vhyps ].
  destruct vhyps as [ nxb vhyps ].
  destruct vhyps as [ nxa vhyps ].
  destruct vhyps as [ nxt vhyps ].
  destruct vhyps as [ nxn vhyps ].
  destruct vhyps as [ nxc vhyps ].
  destruct vhyps as [ nxH nvH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp_halts_try.
  pose proof (hyp_halts_try s1 s2 eqh sim) as hyp_halts_try.
  exrepnd.

  lsubst_tac.

  apply tequality_mkc_halts in hyp_halts_try0.
  apply equality_in_halts in hyp_halts_try1; repnd.
  clear hyp_halts_try3 hyp_halts_try1.
  applydup hyp_halts_try0 in hyp_halts_try2.
  clear hyp_halts_try0.
  spcast.

  pose proof (hasvaluec_mkc_try2_implies
                lib
                (lsubstc t w0 s1 c0)
                (lsubstc t w0 s2 c5)
                (lsubstc n w2 s1 c2)
                (lsubstc n w2 s2 c6)
                v
                (lsubstc_vars c w3 (csub_filter s1 [v]) [v] c3)
                (lsubstc_vars c w3 (csub_filter s2 [v]) [v] c7)
             ) as q.
  repeat (autodimp q hyp).

  {
    vr_seq_true in hyp_tbase.
    pose proof (hyp_tbase s1 s2 eqh sim) as hyp_tbase.
    exrepnd.
    lsubst_tac.
    apply cequiv_stable.
    apply tequality_mkc_member_base in hyp_tbase0; auto.
  }

  repndors; exrepnd;[|].

  {
    vr_seq_true in hyp_halts.
    pose proof (hyp_halts
                  (snoc (snoc s1 (x, mkc_axiom)) (y, mkc_axiom))
                  (snoc (snoc s2 (x, mkc_axiom)) (y, mkc_axiom))
               ) as hyp_halts.

    repeat (autodimp hyp_halts hyp).

    {
      (* hyps_functionality *)
      apply hyps_functionality_snoc2; simpl; auto.

      {
        introv equ' sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; ginv; inj.
        lsubst_tac.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s1a x mkc_axiom [v] c19) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd.
        rewrite lvcs0; clear lvcs0.

        pose proof (lsubstc_vars_csub_filter_snoc_ex c w3 s2a x t2 [v] c24) as lvcs.
        simpl in lvcs; autodimp lvcs hyp.
        exrepnd.
        rewrite lvcs0; clear lvcs0.

        proof_irr.

        apply tequality_mkc_cequiv; split; intro h; auto; spcast;
          try (complete (apply reduces_toc_implies_cequivc; auto)).

        - vr_seq_true in hyp_tbase.
          pose proof (hyp_tbase s1a s2a eqh sim'3) as hyp_tbase.
          exrepnd.
          lsubst_tac.
          clear hyp_tbase1.
          apply tequality_mkc_member_base in hyp_tbase0; auto.
          apply cequiv_stable; spcast.

          vr_seq_true in hyp_nbase.
          pose proof (hyp_nbase s1a s2a eqh sim'3) as hyp_nbase.
          exrepnd.
          lsubst_tac.
          clear hyp_nbase1.
          apply tequality_mkc_member_base in hyp_nbase0; auto.
          apply cequiv_stable; spcast.

          pose proof (implies_cequivc_try
                        lib
                        (lsubstc t w0 s1a c0) (lsubstc t w0 s2a c22)
                        (lsubstc n w2 s1a c2) (lsubstc n w2 s2a c23)
                        v
                        (lsubstc_vars c w3 (csub_filter s1a [v]) [v] c3)
                        (lsubstc_vars c w3 (csub_filter s2a [v]) [v] cv'0)
                     ) as ceqtry1.
          repeat (autodimp ceqtry1 hyp).

          {
            introv.
            repeat substc_lsubstc_vars3.
            vr_seq_true in hyp_cbase.
            pose proof (hyp_cbase (snoc s1a (v,u0)) (snoc s2a (v,u0))) as hyp_cbase.
            repeat (autodimp hyp_cbase hyp).

            {
              apply hyps_functionality_snoc2; simpl; auto.
              introv equ'' sim''.
              lsubst_tac; auto.
            }

            {
              sim_snoc; dands; auto.
              lsubst_tac; auto.
              apply equality_in_base_iff; spcast; eauto 3 with slow.
            }

            exrepnd.
            lsubst_tac.
            clear hyp_cbase1.
            apply tequality_mkc_member_base in hyp_cbase0; auto.
            apply cequiv_stable; spcast.

            pose proof (lsubstc_snoc_move c s1a [] v u0 w3) as e1.
            allrw app_nil_r.
            pose proof (e1 ct5) as e1.
            autodimp e1 hyp.

            {
              apply similarity_dom in sim; repnd.
              rewrite sim0; auto.
            }

            exrepnd; proof_irr; rewrite <- e0; clear e0.

            pose proof (lsubstc_snoc_move c s2a [] v u0 w3) as e2.
            allrw app_nil_r.
            pose proof (e2 ct6) as e2.
            autodimp e2 hyp.

            {
              apply similarity_dom in sim'3; repnd.
              rewrite sim'3; auto.
            }

            exrepnd; proof_irr; rewrite <- e0; clear e0.
            auto.
          }

          eapply cequivc_trans;[apply cequivc_sym;exact ceqtry1|].
          clear ceqtry1.

          (* do the same thing as for mkc_try but for mkc_atom_eq *)


      }

    }

  }

XXXXXXXXXXXXX


  allrw @tequality_mkc_isexc.
  allrw <- @member_isexc_iff.
  applydup hyp0 in hyp1.
  clear hyp0.
  rw <- @member_equality_iff.
  rw @tequality_mkc_equality_sp.

  apply if_raises_exceptionc_cbv in hyp1.
  repndors; exrepnd.

  - (* t raises exception *)
    vr_seq_true in hyp3.
    pose proof (hyp3 (snoc s1 (x,mkc_axiom)) (snoc s2 (x,mkc_axiom))) as hyp.
    clear hyp3.
    repeat (autodimp hyp hyp').

    { apply hyps_functionality_snoc2; simpl; auto;[].
      introv equ' sim'.
      lsubst_tac.
      apply tequality_mkc_isexc.
      split; intro h; auto. GC;[].

      vr_seq_true in hyp4.

      pose proof (hyp4 s1 s') as hyp; clear hyp4.
      repeat (autodimp hyp hyp');[].
      exrepnd.
      lsubst_tac.
      apply tequality_mkc_member_base in hyp0.
      apply cequiv_stable in hyp0.
     eapply raises_exceptionc_preserves_cequivc;[exact hyp0|]; auto.
    }

    { assert (wf_term (mk_isexc t))as wit.
      { apply wf_isexc; auto. }
      assert (cover_vars (mk_isexc t) s1) as cvit.
      { apply cover_vars_isexc; auto. }
      sim_snoc.
      dands; auto.
      lsubst_tac.
      apply member_isexc_iff; auto.
    }

    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in hyp3.
    rw @tequality_mkc_equality_sp in hyp0; repnd.
    sp.

  - (* t has a value,  so we use hyp2 *)
    vr_seq_true in hyp2.
     pose proof (hyp2 (snoc s1 (x,mkc_axiom)) (snoc s2 (x,mkc_axiom))) as hyp.
    clear hyp2.
    repeat (autodimp hyp hyp').
     { (* Hyp Functionality *)
      apply hyps_functionality_snoc2; simpl; auto.
      -  introv equ' sim'.
        lsubst_tac.
     (* because by hyp4, t in Base,  halts(t) is well formed *)

      vr_seq_true in hyp4.

      pose proof (hyp4 s1 s') as hyp; clear hyp4.
      repeat (autodimp hyp hyp');[].
      exrepnd.
      lsubst_tac.
      apply tequality_mkc_member_base in hyp0.
      apply cequiv_stable in hyp0.
      generalize_lsubstc_terms t1.
      generalize_lsubstc_terms t2.
       apply tequality_mkc_halts.
      split; introv hlts.
      apply cequivc_preserves_chaltsc in hyp0; auto.
      apply cequivc_sym in hyp0.
      apply cequivc_preserves_chaltsc in hyp0; auto.
     }

     { (* Similarity *)
       assert (wf_term (mk_halts t)) as wit. apply wf_halts; auto.
       assert (cover_vars (mk_halts t) s1) as cvit.
       { apply cover_vars_halts; dands; auto.
       }
       sim_snoc.
       dands; auto.
       lsubst_tac.
       apply equality_in_halts.
       sp; spcast; try (apply computes_to_valc_refl); eauto 3 with slow.
     }

     { (* Functionality and Truth *)
       exrepnd.
       lsubst_tac.
       rw <- @member_equality_iff in hyp2.
       rw @tequality_mkc_equality_sp in hyp0; repnd.
       sp.
     }
Qed.
