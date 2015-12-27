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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export continuity3_2.
Require Export continuity_defs_ceq.
Require Export list.  (* WTF!! *)


Definition agree_upto_ceq {o} lib b (f g : @NTerm o) :=
  forall (i : Z),
    Z.abs_nat i < b
    -> {v1 : NTerm
       & {v2 : NTerm
        & reduces_to lib (mk_apply f (mk_integer i)) v1
        # reduces_to lib (mk_apply g (mk_integer i)) v2
        # cequiv_open lib v1 v2
        # disjoint (bound_vars v1) (free_vars f)
        # disjoint (bound_vars v2) (free_vars f)
        # disjoint (bound_vars v1) (free_vars g)
        # disjoint (bound_vars v2) (free_vars g)}}.

Definition differ3_ceq {o} lib b f g (t1 t2 : @NTerm o) :=
  {u1 : NTerm
   & {u2 : NTerm
      & cequiv_open lib t1 u1
      # cequiv_open lib t2 u2
      # differ3 b f g u1 u2}}.

Definition differ3_alpha_implies_differ3_ceq {o} :
  forall lib b f g (t1 t2 : @NTerm o),
    nt_wf t1
    -> nt_wf t2
    -> differ3_alpha b f g t1 t2
    -> differ3_ceq lib b f g t1 t2.
Proof.
  introv wf1 wf2 d.
  unfold differ3_alpha in d; exrepnd.
  exists u1 u2; dands; auto;
  apply alpha_implies_cequiv_open; auto;
  eapply alpha_eq_respects_nt_wf; eauto.
Qed.
Hint Resolve differ3_alpha_implies_differ3_ceq : slow.

Lemma cl_olift_iff_olift {o} :
  forall (R : NTerm -> NTerm -> tuniv) (x y : @NTerm o),
    respects_alpha R
    -> (cl_olift R x y <=> olift R x y).
Proof.
  introv resp; split; intro h.
  - apply cl_olift_implies_olift; auto.
  - unfold cl_olift.
    unfold olift in h; repnd; dands; auto.
    introv ps i1 i2; apply h; eauto 2 with slow.
Qed.

Lemma implies_approx_eapply {p} :
  forall lib f g a b,
    approx lib f g
    -> @approx p lib a b
    -> approx lib (mk_eapply f a) (mk_eapply g b).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequiv_eapply {o} :
  forall lib (f g a b : @NTerm o),
    cequiv lib f g
    -> cequiv lib a b
    -> cequiv lib (mk_eapply f a) (mk_eapply g b).
Proof.
  introv H1p H2p.
  allunfold @cequiv; repnd; dands;
  apply implies_approx_eapply; auto.
Qed.

Lemma cequiv_open_eapply {o} :
  forall lib (a1 a2 b1 b2 : @NTerm o),
    cequiv_open lib a1 a2
    -> cequiv_open lib b1 b2
    -> cequiv_open lib (mk_eapply a1 b1) (mk_eapply a2 b2).
Proof.
  introv da1 da2.
  allunfold @cequiv_open.
  apply cl_olift_iff_olift; auto; try (apply respects_alpha_cequiv).
  apply cl_olift_iff_olift in da1; auto; try (apply respects_alpha_cequiv).
  apply cl_olift_iff_olift in da2; auto; try (apply respects_alpha_cequiv).
  allunfold @cl_olift; repnd.
  dands; eauto 2 with slow;
  try (apply nt_wf_eq; apply wf_eapply; eauto 3 with slow).
  introv ps isp1 isp2.

  repeat (rw @lsubst_lsubst_aux_prog_sub; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in isp1; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in isp2; auto).
  allsimpl; fold_terms; autorewrite with slow in *.
  allrw <- @isprogram_eapply_iff; repnd.

  pose proof (da1 sub) as h; repeat (autodimp h hyp);
  try  (complete (repeat (rw @lsubst_lsubst_aux_prog_sub; auto))).

  pose proof (da2 sub) as q; repeat (autodimp q hyp);
  try  (complete (repeat (rw @lsubst_lsubst_aux_prog_sub; auto))).

  repeat (rw @lsubst_lsubst_aux_prog_sub in h; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in q; auto).
  apply implies_cequiv_eapply; auto.
Qed.

Lemma differ3_ceq_mk_eapply {o} :
  forall lib b f g (a1 a2 b1 b2 : @NTerm o),
    differ3_ceq lib b f g a1 a2
    -> differ3_ceq lib b f g b1 b2
    -> differ3_ceq lib b f g (mk_eapply a1 b1) (mk_eapply a2 b2).
Proof.
  introv da1 da2.
  allunfold @differ3_ceq; exrepnd.
  exists (mk_eapply u0 u1) (mk_eapply u3 u2); dands; auto;
  try (apply cequiv_open_eapply; auto).
  constructor; simpl; auto.
  introv i; repndors; cpx; constructor; auto.
Qed.

Lemma implies_approx_compop {o} :
  forall lib c (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib c1 c2
    -> approx lib d1 d2
    -> approx lib (mk_compop c a1 b1 c1 d1) (mk_compop c a2 b2 c2 d2).
Proof.
  introv H1p H2p H3p H4p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  applydup @approx_relates_only_progs in H3p.
  applydup @approx_relates_only_progs in H4p.
  repnd.
  unfold mk_compop.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequiv_compop {o} :
  forall lib c (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib c1 c2
    -> cequiv lib d1 d2
    -> cequiv lib (mk_compop c a1 b1 c1 d1) (mk_compop c a2 b2 c2 d2).
Proof.
  introv H1p H2p H3p H4p.
  allunfold @cequiv; repnd; dands;
  apply implies_approx_compop; auto.
Qed.

Lemma isprogram_compop {o} :
  forall x (a b c d : @NTerm o),
    isprogram (mk_compop x a b c d)
              <=> (isprogram a # isprogram b # isprogram c # isprogram d).
Proof.
  introv; unfold isprogram; allrw @nt_wf_eq.
  rw @wf_compop_iff; unfold closed; simpl; autorewrite with slow.
  repeat (rw app_eq_nil_iff).
  split; intro h; tcsp.
Qed.

Lemma cequiv_open_compop {o} :
  forall lib c (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    cequiv_open lib a1 a2
    -> cequiv_open lib b1 b2
    -> cequiv_open lib c1 c2
    -> cequiv_open lib d1 d2
    -> cequiv_open lib (mk_compop c a1 b1 c1 d1) (mk_compop c a2 b2 c2 d2).
Proof.
  introv da1 da2 da3 da4.
  allunfold @cequiv_open.
  apply cl_olift_iff_olift; auto; try (apply respects_alpha_cequiv).
  apply cl_olift_iff_olift in da1; auto; try (apply respects_alpha_cequiv).
  apply cl_olift_iff_olift in da2; auto; try (apply respects_alpha_cequiv).
  apply cl_olift_iff_olift in da3; auto; try (apply respects_alpha_cequiv).
  apply cl_olift_iff_olift in da4; auto; try (apply respects_alpha_cequiv).
  allunfold @cl_olift; repnd.
  dands; eauto 2 with slow;
  try (apply nt_wf_eq; apply wf_compop; eauto 3 with slow).
  introv ps isp1 isp2.

  repeat (rw @lsubst_lsubst_aux_prog_sub; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in isp1; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in isp2; auto).
  allsimpl; fold_terms; autorewrite with slow in *.
  allrw @isprogram_compop; repnd.

  pose proof (da1 sub) as h; repeat (autodimp h hyp);
  try  (complete (repeat (rw @lsubst_lsubst_aux_prog_sub; auto))).

  pose proof (da2 sub) as q; repeat (autodimp q hyp);
  try  (complete (repeat (rw @lsubst_lsubst_aux_prog_sub; auto))).

  pose proof (da3 sub) as z; repeat (autodimp z hyp);
  try  (complete (repeat (rw @lsubst_lsubst_aux_prog_sub; auto))).

  pose proof (da4 sub) as w; repeat (autodimp w hyp);
  try  (complete (repeat (rw @lsubst_lsubst_aux_prog_sub; auto))).

  repeat (rw @lsubst_lsubst_aux_prog_sub in h; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in q; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in z; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in w; auto).
  apply implies_cequiv_compop; auto.
Qed.

Lemma differ3_ceq_mk_compop {o} :
  forall lib b f g c (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    differ3_ceq lib b f g a1 a2
    -> differ3_ceq lib b f g b1 b2
    -> differ3_ceq lib b f g c1 c2
    -> differ3_ceq lib b f g d1 d2
    -> differ3_ceq lib b f g (mk_compop c a1 b1 c1 d1) (mk_compop c a2 b2 c2 d2).
Proof.
  introv da1 da2 da3 da4.
  allunfold @differ3_ceq; exrepnd.
  exists (mk_compop c u6 u4 u0 u1) (mk_compop c u7 u5 u3 u2); dands; auto;
  try (apply cequiv_open_compop; auto).
  constructor; simpl; auto.
  introv i; repndors; cpx; constructor; auto.
Qed.

Lemma implies_approx_arithop {o} :
  forall lib c (a1 a2 b1 b2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib (mk_arithop c a1 b1) (mk_arithop c a2 b2).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  unfold mk_arithop.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequiv_arithop {o} :
  forall lib c (a1 a2 b1 b2 : @NTerm o),
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib (mk_arithop c a1 b1) (mk_arithop c a2 b2).
Proof.
  introv H1p H2p.
  allunfold @cequiv; repnd; dands;
  apply implies_approx_arithop; auto.
Qed.

Lemma isprogram_arithop {o} :
  forall x (a b : @NTerm o),
    isprogram (mk_arithop x a b)
              <=> (isprogram a # isprogram b).
Proof.
  introv; unfold isprogram; allrw @nt_wf_eq.
  rw @wf_arithop_iff; unfold closed; simpl; autorewrite with slow.
  repeat (rw app_eq_nil_iff).
  split; intro h; tcsp.
Qed.

Lemma cequiv_open_arithop {o} :
  forall lib c (a1 a2 b1 b2 : @NTerm o),
    cequiv_open lib a1 a2
    -> cequiv_open lib b1 b2
    -> cequiv_open lib (mk_arithop c a1 b1) (mk_arithop c a2 b2).
Proof.
  introv da1 da2.
  allunfold @cequiv_open.
  apply cl_olift_iff_olift; auto; try (apply respects_alpha_cequiv).
  apply cl_olift_iff_olift in da1; auto; try (apply respects_alpha_cequiv).
  apply cl_olift_iff_olift in da2; auto; try (apply respects_alpha_cequiv).
  allunfold @cl_olift; repnd.
  dands; eauto 2 with slow;
  try (apply nt_wf_eq; apply wf_arithop; eauto 3 with slow).
  introv ps isp1 isp2.

  repeat (rw @lsubst_lsubst_aux_prog_sub; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in isp1; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in isp2; auto).
  allsimpl; fold_terms; autorewrite with slow in *.
  allrw @isprogram_arithop; repnd.

  pose proof (da1 sub) as h; repeat (autodimp h hyp);
  try  (complete (repeat (rw @lsubst_lsubst_aux_prog_sub; auto))).

  pose proof (da2 sub) as q; repeat (autodimp q hyp);
  try  (complete (repeat (rw @lsubst_lsubst_aux_prog_sub; auto))).

  repeat (rw @lsubst_lsubst_aux_prog_sub in h; auto).
  repeat (rw @lsubst_lsubst_aux_prog_sub in q; auto).
  apply implies_cequiv_arithop; auto.
Qed.

Lemma differ3_ceq_mk_arithop {o} :
  forall lib b f g c (a1 a2 b1 b2 : @NTerm o),
    differ3_ceq lib b f g a1 a2
    -> differ3_ceq lib b f g b1 b2
    -> differ3_ceq lib b f g (mk_arithop c a1 b1) (mk_arithop c a2 b2).
Proof.
  introv da1 da2.
  allunfold @differ3_ceq; exrepnd.
  exists (mk_arithop c u0 u1) (mk_arithop c u3 u2); dands; auto;
  try (apply cequiv_open_arithop; auto).
  constructor; simpl; auto.
  introv i; repndors; cpx; constructor; auto.
Qed.

Lemma comp_force_int_step3_2 {o} :
  forall lib b f g (t1 t2 : @NTerm o) kk u,
    isprog f
    -> isprog g
    -> wf_term t1
    -> wf_term t2
    -> agree_upto_ceq lib b f g
    -> differ3 b f g t1 t2
    -> compute_step lib t1 = csuccess u
    -> has_value_like_k lib kk u
    -> (forall t1 t2 v m, (* induction hypothesis *)
          m < S kk
          -> wf_term t1
          -> wf_term t2
          -> isvalue_like v
          -> reduces_in_atmost_k_steps lib t1 v m
          -> differ3 b f g t1 t2
          -> {v' : NTerm & reduces_to lib t2 v' # differ3_ceq lib b f g v v'})
    -> {t : NTerm
        & {u' : NTerm
           & reduces_to lib t2 t
           # reduces_to lib u u'
           # differ3_ceq lib b f g u' t}}.
Proof.
  nterm_ind1s t1 as [v|s ind|op bs ind] Case;
  introv ispf ispg wt1 wt2 agree d comp hv compind.

  - Case "vterm".
    simpl.
    inversion d; subst; allsimpl; ginv.

  - Case "sterm".
    inversion d; subst; clear d; allsimpl; auto.
    csunf comp; allsimpl; ginv.
    exists (sterm s) (sterm s); dands; eauto 3 with slow.
    apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase; ginv.

    + SCase "Can".
      inversion d; subst.
      csunf comp; allsimpl; ginv.
      exists (oterm (Can can) bs2) (oterm (Can can) bs); dands; eauto 3 with slow.
      apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.

    + SCase "NCan".
      destruct bs as [|b1 bs];
        try (complete (allsimpl; ginv));[].

      destruct b1 as [l1 t1].
      destruct l1; try (complete (csunf comp; simpl in comp; ginv));[|].

      {
      destruct t1 as [v1|f1|op1 bs1].

      * destruct t2 as [v2|f2|op2 bs2]; try (complete (inversion d));[].

        inversion d as [? ? ? ? d1|s|?|? ? ? len imp]; subst; simphyps; cpx; ginv.

      * destruct t2 as [v2|f2|op2 bs2]; try (complete (inversion d));[].
        csunf comp; allsimpl.
        dopid_noncan ncan SSCase; allsimpl; ginv.

        { SSCase "NApply".
          apply compute_step_seq_apply_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d.
          allsimpl.

          pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd arg) y) as d2; autodimp d2 hyp.
          clear imp.

          inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
          inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.
          inversion d3; subst; clear d3.
          fold_terms.

          exists (mk_eapply (sterm f1) t0)
                 (mk_eapply (sterm f1) arg).
          dands; eauto 3 with slow.
          apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.
          apply differ3_implies_differ3_alpha.
          apply differ3_mk_eapply; auto.
        }

        { SSCase "NEApply".
          apply compute_step_eapply_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d.
          rw @wf_term_eq in wt1; rw @nt_wf_eapply_iff in wt1; exrepnd; allunfold @nobnd; subst; ginv.
          simpl in len; repeat cpx.
          simpl in imp.

          pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd b0) y) as d2; autodimp d2 hyp.
          clear imp.

          inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
          inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.
          inversion d3; subst; clear d3.
          fold_terms.
          allrw <- @wf_eapply_iff; repnd.

          repndors; exrepnd; subst.

          - apply compute_step_eapply2_success in comp1; repnd; GC.
            repndors; exrepnd; subst; ginv; allsimpl; GC.
            inversion d4 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl;
            clear d4; cpx; clear imp1; fold_terms.

            exists (f0 n) (f0 n); dands; eauto 3 with slow.
            { apply reduces_to_if_step.
              csunf; simpl.
              dcwf h; simpl; boolvar; try omega.
              rw @Znat.Nat2Z.id; auto. }
            { apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow.
              apply differ3_implies_differ3_alpha.
              allapply @closed_if_isprog.
              apply differ3_refl; simpl; try (rw ispf); try (rw ispg); auto. }

          - apply isexc_implies2 in comp0; exrepnd; subst.
            inversion d4 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl; clear d4.
            exists (oterm Exc bs2) (oterm Exc l); dands; eauto 3 with slow.
            apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.

          - pose proof (ind b0 b0 []) as h; clear ind.
            repeat (autodimp h hyp); eauto 3 with slow.
            pose proof (h t0 kk x) as ih; clear h.
            applydup @preserve_nt_wf_compute_step in comp1; eauto 3 with slow.
            allsimpl; autorewrite with slow in *; auto.
            repeat (autodimp ih hyp); eauto 3 with slow.

            { eapply has_value_k_like_eapply_sterm_implies in hv; auto; exrepnd.
              eapply has_value_like_k_lt; eauto. }

            exrepnd.

            assert (nt_wf u') as wfu'.
            { apply reduces_to_preserves_wf in ih2; eauto 3 with slow. }

            assert (nt_wf t) as wft.
            { apply reduces_to_preserves_wf in ih0; eauto 3 with slow. }

            exists (mk_eapply (sterm f1) t) (mk_eapply (sterm f1) u'); dands; eauto 3 with slow.
            { apply implies_eapply_red_aux; eauto 3 with slow. }
            { apply implies_eapply_red_aux; eauto 3 with slow. }
            { apply differ3_ceq_mk_eapply; eauto 3 with slow. }
        }

        { SSCase "NFix".
          apply compute_step_fix_success in comp; repnd; subst; allsimpl.
          inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl.

          pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
          clear imp.

          inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.
          inversion d2; subst; clear d2.
          fold_terms.

          exists (mk_apply (sterm f1) (mk_fix (sterm f1)))
                 (mk_apply (sterm f1) (mk_fix (sterm f1))).
          dands; eauto 3 with slow.
          apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow;
          apply nt_wf_eq; apply wf_apply; eauto 3 with slow.
        }

        { SSCase "NCbv".
          apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? d1|?|? xxx|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl; fold_terms.

          pose proof (imp (nobnd (sterm f1)) x0) as d1; autodimp d1 hyp.
          pose proof (imp (bterm [v] x) y) as d2; autodimp d2 hyp.
          clear imp.

          inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
          inversion d3; subst; clear d3.
          inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.
          fold_terms.

          exists (subst t2 v (sterm f1))
                 (subst x v (sterm f1)).
          dands; eauto 3 with slow.
          allapply @closed_if_isprog.
          allrw <- @wf_cbv_iff; repnd.
          apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
          try (apply nt_wf_subst; eauto 3 with slow).
          apply differ3_subst; simpl; try (rw ispf); try (rw ispg); simpl; tcsp.
        }

        { SSCase "NTryCatch".
          apply compute_step_try_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? d1|?|? xxx|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl; fold_terms.

          pose proof (imp (nobnd (sterm f1)) x0) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd a) y) as d2; autodimp d2 hyp.
          pose proof (imp (bterm [v] x) z) as d3; autodimp d3 hyp.
          clear imp.

          inversion d1 as [? ? ? dfx dgx d4]; subst; clear d1.
          inversion d4; subst; clear d4.
          inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.
          inversion d3 as [? ? ? df5 dg5 d5]; subst; clear d3.
          fold_terms.

          exists (mk_atom_eq t2 t2 (sterm f1) mk_bot)
                 (mk_atom_eq a a (sterm f1) mk_bot).
          dands; eauto 3 with slow.

          allrw <- @wf_try_iff; repnd.
          apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
          try (apply nt_wf_eq; apply wf_atom_eq; dands; eauto 3 with slow).

          apply differ3_alpha_mk_atom_eq; eauto 3 with slow.
          apply differ3_implies_differ3_alpha.
          allapply @closed_if_isprog.
          apply differ3_refl; simpl; try (rw ispf); try (rw ispg); auto.
        }

        { SSCase "NCanTest".
          apply compute_step_seq_can_test_success in comp; exrepnd; subst; allsimpl.
          inversion d as [? ? ? d1|?|? xxx|? ? ? len imp]; subst; simphyps; cpx; ginv; clear d; allsimpl; fold_terms.

          pose proof (imp (nobnd (sterm f1)) x) as d1; autodimp d1 hyp.
          pose proof (imp (nobnd a) y) as d2; autodimp d2 hyp.
          pose proof (imp (nobnd b0) z) as d3; autodimp d3 hyp.
          clear imp.

          inversion d1 as [? ? ? dfx dgx d4]; subst; clear d1.
          inversion d4; subst; clear d4.
          inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.
          inversion d3 as [? ? ? df5 dg5 d5]; subst; clear d3.
          fold_terms.

          exists t0 b0.
          dands; eauto 3 with slow.

          allrw @wf_can_test_iff; repnd.
          apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
          try (apply nt_wf_eq; apply wf_atom_eq; dands; eauto 3 with slow).
        }

      * (* Now destruct op2 *)
        dopid op1 as [can1|ncan1|exc1|abs1] SSCase; ginv.

        { SSCase "Can".

          (* Because the principal argument is canonical we can destruct ncan *)
          dopid_noncan ncan SSSCase.

          - SSSCase "NApply".
            csunf comp; allsimpl.
            apply compute_step_apply_success in comp; repndors; exrepnd; subst; allsimpl.

            { inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
              destruct bs2; allsimpl; cpx.
              cpx; allsimpl.

              pose proof (imp (bterm [] (oterm (Can NLambda) [bterm [v] b0])) b1) as d1.
              autodimp d1 hyp.
              pose proof (imp (bterm [] arg) x) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
              inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

              inversion d3 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl; GC; clear d3.
              destruct bs2; allsimpl; cpx.
              cpx.

              pose proof (imp1 (bterm [v] b0) b1) as d1.
              autodimp d1 hyp.
              clear imp1.
              inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.

              exists (subst t2 v t0) (subst b0 v arg); dands; eauto 3 with slow.

              fold_terms.
              allrw <- @wf_apply_iff; repnd.
              allrw <- @wf_lam_iff.

              apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
              try (apply nt_wf_subst; eauto 3 with slow).

              apply differ3_subst; simpl; eauto 3 with slow.
            }

            { inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
              destruct bs2; allsimpl; cpx.
              cpx; allsimpl.

              pose proof (imp (nobnd (mk_nseq f0)) b0) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd arg) x) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
              inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.
              GC.

              inversion d3 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; GC; clear d3.
              cpx; clear imp1; fold_terms.

              exists (mk_eapply (mk_nseq f0) t0) (mk_eapply (mk_nseq f0) arg); dands; eauto 3 with slow.

              apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow.

              apply differ3_implies_differ3_alpha.
              apply differ3_oterm; simpl; tcsp.
              introv j; repndors; cpx; repeat (constructor; auto).
              simpl; tcsp.
            }

          - SSSCase "NEApply".
            csunf comp; allsimpl.
            apply compute_step_eapply_success in comp; exrepnd; subst.
            rw @wf_term_eq in wt1; rw @nt_wf_eapply_iff in wt1; exrepnd; allunfold @nobnd; ginv.

            inversion d as [? ? ? ? d1|?|?|? ? ? len imp]; subst; clear d.
            simpl in len; cpx; simpl in imp.

            pose proof (imp (nobnd (oterm (Can can1) bs1)) x) as d1; autodimp d1 hyp.
            pose proof (imp (nobnd b0) y) as d2; autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.
            fold_terms.
            allrw <- @wf_eapply_iff; repnd.
            apply eapply_wf_def_oterm_implies in comp2; exrepnd; ginv; fold_terms.
            destruct comp2 as [comp2|comp2]; exrepnd; ginv; fold_terms.

            { apply differ3_lam_implies in d3; exrepnd; subst; fold_terms.

              repndors; exrepnd; subst.

              + apply compute_step_eapply2_success in comp1; repnd; GC.
                repndors; exrepnd; subst; ginv; allsimpl; GC.
                allunfold @apply_bterm; allsimpl; allrw @fold_subst.

                exists (subst a' v0 t0) (subst b1 v0 b0); dands; eauto 3 with slow.
                { apply eapply_lam_can_implies.
                  apply differ3_preserves_iscan in d4; auto.
                  unfold computes_to_can; dands; eauto 3 with slow. }
                { allrw @nt_wf_eq.
                  allrw <- @wf_lam_iff.
                  apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
                  try (apply nt_wf_subst; eauto 3 with slow).
                  apply differ3_subst; auto; simpl;
                  allapply @closed_if_isprog; try (rw ispf); try (rw ispg); auto. }

              + apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl.
                apply differ3_exception_implies in d4; exrepnd; subst.
                exists (mk_exception a'0 e') (mk_exception a e); dands; eauto 3 with slow.
                apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow.
                apply differ3_alpha_mk_exception; eauto 3 with slow.

              + pose proof (ind b0 b0 []) as h; clear ind.
                repeat (autodimp h hyp); eauto 3 with slow.
                pose proof (h t0 kk x) as ih; clear h.
                applydup @preserve_nt_wf_compute_step in comp1; auto.
                repeat (autodimp ih hyp); eauto 3 with slow.
                { apply has_value_like_k_eapply_lam_implies in hv; auto.
                  exrepnd.
                  eapply has_value_like_k_lt; eauto. }
                exrepnd.

                exists (mk_eapply (mk_lam v a') t1) (mk_eapply (mk_lam v t) u'); dands; eauto 3 with slow.
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply differ3_ceq_mk_eapply; eauto 2 with slow.
                  allrw @nt_wf_eq.
                  allrw <- @wf_lam_iff.
                  apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
                  try (apply nt_wf_eq; apply wf_lam; eauto 2 with slow).
                  apply differ3_alpha_mk_lam; eauto 3 with slow;
                  allapply @closed_if_isprog; try (rw ispf); try (rw ispg); simpl; tcsp. }
            }

            { inversion d3 as [|?|?|? ? ? len imp]; subst; simphyps; clear d3.
              clear imp.
              allsimpl; cpx; allsimpl; fold_terms.
              repndors; exrepnd; subst; allsimpl.

              - destruct b0 as [v|f'|op bs]; ginv;[].
                dopid op as [can|ncan|exc|abs] SSSSCase; ginv;[].
                destruct can; ginv;[].
                destruct bs; allsimpl; ginv; GC.
                boolvar; ginv; try omega; fold_terms.
                inversion d4 as [|?|?|? ? ? len imp]; subst; simphyps; clear d4.
                allsimpl; cpx; fold_terms; allsimpl.
                clear imp.

                exists (@mk_nat o (s (Z.to_nat z))) (@mk_nat o (s (Z.to_nat z)));
                  dands; eauto 3 with slow.

                { apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
                  boolvar; try omega; auto. }

                { apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow. }

              - apply wf_isexc_implies in comp0; auto; exrepnd; subst; allsimpl.
                apply differ3_exception_implies in d4; exrepnd; subst.
                exists (mk_exception a' e') (mk_exception a e); dands; eauto 3 with slow.
                apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.
                apply differ3_alpha_mk_exception; eauto 3 with slow.

              - pose proof (ind b0 b0 []) as h; clear ind.
                repeat (autodimp h hyp); eauto 3 with slow.
                pose proof (h t0 kk x) as ih; clear h.
                applydup @preserve_nt_wf_compute_step in comp1; auto.
                allsimpl; autorewrite with slow in *.
                repeat (autodimp ih hyp); eauto 3 with slow.
                { apply has_value_like_k_eapply_nseq_implies in hv; auto.
                  exrepnd.
                  eapply has_value_like_k_lt; eauto. }
                exrepnd.

                exists (mk_eapply (mk_nseq s) t) (mk_eapply (mk_nseq s) u'); dands; eauto 3 with slow.
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply implies_eapply_red_aux; eauto 3 with slow. }
                { apply differ3_ceq_mk_eapply; eauto 3 with slow.
                  apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow. }
            }

          - SSSCase "NFix".
            csunf comp; allsimpl.
            apply compute_step_fix_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            cpx; GC.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.

            inversion d3 as [?|?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d3.

            exists (mk_apply (oterm (Can can1) bs2)
                             (mk_fix (oterm (Can can1) bs2)))
                   (mk_apply (oterm (Can can1) bs1)
                             (mk_fix (oterm (Can can1) bs1))).
            dands; eauto 3 with slow.

            fold_terms.
            allrw @wf_fix_iff.
            apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
            try (apply nt_wf_eq; apply wf_apply; eauto 2 with slow);
            try (apply wf_fix; auto).
            apply differ3_implies_differ3_alpha.
            apply differ3_oterm; simpl; tcsp.
            introv j; repndors; cpx; tcsp.

            { constructor; auto ; constructor; allsimpl; auto. }

            { constructor; auto; constructor; simpl; tcsp.
              introv j; repndors; cpx; tcsp. }

          - SSSCase "NSpread".
            csunf comp; allsimpl.
            apply compute_step_spread_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can NPair) [bterm [] a, bterm [] b0])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [va,vb] arg) x) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl; GC; clear d3.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp1 (bterm [] a) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp1 (bterm [] b0) x) as d2.
            autodimp d2 hyp.
            clear imp1.
            inversion d1 as [? ? ? df5 dg5 d5]; subst; clear d1.
            inversion d2 as [? ? ? df6 dg6 d6]; subst; clear d2.

            fold_terms.
            allrw @wf_spread; repnd.
            allrw @wf_pair; repnd.

            exists (lsubst t0 [(va,t2),(vb,t3)]) (lsubst arg [(va,a),(vb,b0)]); dands; eauto 3 with slow.
            apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
            try (apply lsubst_wf_if_eauto; eauto 3 with slow).
            apply differ3_subst; simpl; eauto 3 with slow.

          - SSSCase "NDsup".
            csunf comp; allsimpl.
            apply compute_step_dsup_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can NSup) [bterm [] a, bterm [] b0])) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [va,vb] arg) x) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl; GC; clear d3.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp1 (bterm [] a) b1) as d1.
            autodimp d1 hyp.
            pose proof (imp1 (bterm [] b0) x) as d2.
            autodimp d2 hyp.
            clear imp1.
            inversion d1 as [? ? ? df5 dg5 d5]; subst; clear d1.
            inversion d2 as [? ? ? df6 dg6 d6]; subst; clear d2.

            exists (lsubst t0 [(va,t2),(vb,t3)]) (lsubst arg [(va,a),(vb,b0)]); dands; eauto 3 with slow.

            fold_terms.
            allrw @wf_dsup; repnd.
            allrw @wf_sup_iff; repnd.

            apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
            try (apply lsubst_wf_if_eauto; eauto 3 with slow).

            apply differ3_subst; simpl; eauto 3 with slow.

          - SSSCase "NDecide".
            csunf comp; allsimpl.
            apply compute_step_decide_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can can1) [bterm [] d0])) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v1] t1) b1) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [v2] t0) x) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? df4 dg4 d4]; subst; clear d1.
            inversion d2 as [? ? ? df5 dg5 d5]; subst; clear d2.
            inversion d3 as [? ? ? df6 dg6 d6]; subst; clear d3.

            inversion d4 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl; GC; clear d4.
            cpx; allsimpl.

            pose proof (imp1 (bterm [] d0) x) as d1.
            autodimp d1 hyp.
            clear imp1.
            inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.

            fold_terms.
            allrw @wf_decide; repnd.

            dorn comp0; repnd; subst.

            + exists (subst t4 v1 t3) (subst t1 v1 d0); dands; eauto 3 with slow.
              allrw @wf_inl.
              apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
              try (apply lsubst_wf_if_eauto; eauto 3 with slow).
              apply differ3_subst; simpl; eauto 3 with slow.

            + exists (subst t5 v2 t3) (subst t0 v2 d0); dands; eauto 3 with slow.
              allrw @wf_inr.
              apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
              try (apply lsubst_wf_if_eauto; eauto 3 with slow).
              apply differ3_subst; simpl; eauto 3 with slow.

          - SSSCase "NCbv".
            csunf comp; allsimpl.
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [v] x) x0) as d2.
            autodimp d2 hyp.
            clear imp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [?|?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d3.

            exists (subst t0 v (oterm (Can can1) bs2))
                   (subst x v (oterm (Can can1) bs1)); dands; eauto 3 with slow.

            allrw <- @wf_cbv_iff; repnd.
            apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
            try (apply lsubst_wf_if_eauto; eauto 3 with slow).

            apply differ3_subst; simpl; eauto 3 with slow.

          - SSSCase "NSleep".
            csunf comp; allsimpl.
            apply compute_step_sleep_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can (Nint z)) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? df2 sg2 d2]; subst; clear d1.

            inversion d2 as [?|?|?|? ? ? len1 imp1]; subst; allsimpl; GC; clear d2.
            cpx; allsimpl.

            exists (@mk_axiom o)
                   (@mk_axiom o).
            dands; eauto 3 with slow.

            apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.

          - SSSCase "NTUni".
            csunf comp; allsimpl.
            apply compute_step_tuni_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can (Nint (Z.of_nat n))) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.

            inversion d2 as [?|?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d2.
            cpx; allsimpl.

            exists (@mk_uni o n)
                   (@mk_uni o n).
            dands; eauto 3 with slow.
            { apply reduces_to_if_step; simpl.
              csunf; simpl; unfold compute_step_tuni; simpl; boolvar; try omega.
              rw Znat.Nat2Z.id; auto. }

            apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.

          - SSSCase "NMinus".
            csunf comp; allsimpl.
            apply compute_step_minus_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can (Nint z)) [])) x) as d1.
            autodimp d1 hyp.
            clear imp.

            inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.

            inversion d2 as [?|?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d2.
            cpx; allsimpl.

            exists (@mk_integer o (- z))
                   (@mk_integer o (- z)).
            dands; eauto 3 with slow.

            apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.

          - SSSCase "NFresh".
            csunf comp; allsimpl; ginv.

          - SSSCase "NTryCatch".
            csunf comp; allsimpl.
            apply compute_step_try_success in comp; exrepnd; subst; allsimpl.

            inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] a) x0) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [v] x) y) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? df4 dg4 d4]; subst; clear d1.
            inversion d2 as [? ? ? df5 dg5 d5]; subst; clear d2.
            inversion d3 as [? ? ? df6 dg6 d6]; subst; clear d3.
            allrw disjoint_singleton_l.

            inversion d4 as [?|?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d4.

            exists (mk_atom_eq t0 t0 (oterm (Can can1) bs2) mk_bot)
                   (mk_atom_eq a a (oterm (Can can1) bs1) mk_bot);
              dands; eauto 3 with slow.

            allrw <- @wf_try_iff; repnd.
            apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
            try (apply nt_wf_eq; apply wf_atom_eq; dands; eauto 3 with slow).

            apply differ3_implies_differ3_alpha.
            constructor; simpl; auto.
            introv i; repndors; ginv; tcsp; constructor; eauto 3 with slow.
            apply differ3_refl; simpl; allrw disjoint_singleton_l;
            try (rw @isprog_eq in ispf; destruct ispf as [c w]; rw c; simpl; tcsp);
            try (rw @isprog_eq in ispg; destruct ispg as [c w]; rw c; simpl; tcsp).

          - SSSCase "NParallel".
            csunf comp; allsimpl.
            apply compute_step_parallel_success in comp; subst; allsimpl.
            inversion d as [?|?|?|? ? ? len imp]; subst; allsimpl; GC; clear d.
            destruct bs2; allsimpl; cpx.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.
            inversion d2 as [?|?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; GC; clear d2.

            exists (@mk_axiom o) (@mk_axiom o); dands; eauto 3 with slow.
            apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.

          - SSSCase "NCompOp".
            destruct bs; try (complete (csunf comp; allsimpl; dcwf h));[].
            destruct b0 as [l t].
            destruct l; destruct t as [v|f2|op bs2]; try (complete (csunf comp; allsimpl; dcwf h));[].

            inversion d as [?|?|?|? ? ? len imp]; subst; clear d.
            allsimpl.
            destruct bs3; allsimpl; cpx.
            destruct bs3; allsimpl; cpx.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] (oterm op bs2)) b1) as d2.
            autodimp d2 hyp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [|?|?|? ? ? ni1 len1 imp1]; subst; clear d3; cpx.

            dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

            + SSSSCase "Can".
              csunf comp; allsimpl.
              dcwf h.

              inversion d4 as [|?|?|? ? ? len2 imp2]; subst; clear d4; cpx.

              apply compute_step_compop_success_can_can in comp.
              exrepnd; subst.

              allsimpl; cpx.
              clear df3 dg3 df4 dg4 len1 imp2.
              allsimpl.

              pose proof (imp (nobnd t1) x) as d1.
              autodimp d1 hyp.
              pose proof (imp (nobnd t2) y) as d2.
              autodimp d2 hyp.
              clear imp.

              inversion d1 as [? ? ? df33 dg33 d3]; subst; clear d1.
              inversion d2 as [? ? ? df44 dg44 d4]; subst; clear d2.

              allrw @wf_compop_iff; repnd.

              repndors; exrepnd; subst.

              * allapply @get_param_from_cop_pki; subst; allsimpl.
                exists (if Z_lt_le_dec n1 n2 then t3 else t4)
                       (if Z_lt_le_dec n1 n2 then t1 else t2);
                  dands; eauto 3 with slow.
                boolvar; eauto 3 with slow;
                apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.

              * allrw @get_param_from_cop_some; subst; allsimpl.
                exists (if param_kind_deq pk1 pk2 then t3 else t4)
                       (if param_kind_deq pk1 pk2 then t1 else t2);
                  dands; eauto 3 with slow.

                { apply reduces_to_if_step; csunf; simpl.
                  dcwf h; allsimpl.
                  unfold compute_step_comp; allrw @get_param_from_cop_pk2can; auto. }

                boolvar; eauto 3 with slow;
                apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.

            + SSSSCase "NCan".
              rw @compute_step_ncompop_ncan2 in comp.
              dcwf h; allsimpl.
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1.
              destruct comp1; ginv.

              pose proof (ind (oterm (NCan ncan3) bs2) (oterm (NCan ncan3) bs2) []) as h; clear ind.
              repeat (autodimp h hyp); tcsp; eauto 2 with slow.

              pose proof (h t0 kk n) as k; clear h.
              repeat (autodimp k hyp).

              { apply wf_oterm_iff in wt1; allsimpl; repnd.
                pose proof (wt1 (bterm [] (oterm (NCan ncan3) bs2))) as h.
                autodimp h hyp. }

              { apply wf_oterm_iff in wt2; allsimpl; repnd.
                pose proof (wt2 (bterm [] t0)) as h.
                autodimp h hyp. }

              { apply if_has_value_like_k_ncompop_can1 in hv; exrepnd.
                apply (has_value_like_k_lt lib j kk) in hv0; auto. }

              exrepnd.

              apply nt_wf_eq in wt1; apply nt_wf_NCompOp in wt1.
              apply nt_wf_eq in wt2; apply nt_wf_NCompOp in wt2.
              exrepnd; fold_terms; ginv; allsimpl; cpx.

              exists (oterm (NCan (NCompOp c))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: nobnd t
                                   :: nobnd t3
                                   :: nobnd t4
                                   :: []))
                     (oterm (NCan (NCompOp c))
                            (bterm [] (oterm (Can can1) bs1)
                                   :: nobnd u'
                                   :: nobnd t7
                                   :: nobnd t8
                                   :: [])).
              dands; eauto 3 with slow.

              * apply reduce_to_prinargs_comp2; eauto with slow; sp.
                apply co_wf_def_implies_iswfpk.
                eapply co_wf_def_len_implies;[|eauto];auto.

              * apply reduce_to_prinargs_comp2; eauto with slow; sp.

              * apply differ3_ceq_mk_compop; auto;
                apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
                apply differ3_implies_differ3_alpha.

                { pose proof (imp (nobnd (oterm (Can can1) bs1))
                                  (nobnd (oterm (Can can1) bs4))) as xx.
                  autodimp xx hyp. }

                { pose proof (imp (nobnd t7) (nobnd t3)) as xx.
                  autodimp xx hyp; inversion xx; subst; auto. }

                { pose proof (imp (nobnd t8) (nobnd t4)) as xx.
                  autodimp xx hyp; inversion xx; subst; auto. }

            + SSSSCase "Exc".
              csunf comp; allsimpl; ginv.
              dcwf h; ginv; allsimpl.
              inversion d4 as [|?|?|? ? ? len2 imp2]; subst; clear d4; cpx.
              exists (oterm Exc bs5) (oterm Exc bs2); dands; eauto 3 with slow.
              { apply reduces_to_if_step; csunf; allsimpl; dcwf h. }
              { apply wf_term_ncompop_iff in wt1.
                apply wf_term_ncompop_iff in wt2.
                exrepnd; ginv; allsimpl; cpx.
                apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow. }

            + SSSSCase "Abs".
              csunf comp; allsimpl; csunf comp; allsimpl.
              dcwf h.
              unfold on_success in comp.
              remember (compute_step_lib lib abs3 bs2) as comp1.
              symmetry in Heqcomp1; destruct comp1; ginv.
              apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

              inversion d4 as [|?|?|? ? ? ni2 len2 imp2]; subst; simphyps; clear d4.

              assert (differ3_bterms b f g bs2 bs5) as dbs.
              { unfold differ3_bterms, br_bterms, br_list; auto. }

              pose proof (found_entry_change_bs abs3 oa2 vars rhs lib bs2 correct bs5) as fe2.
              repeat (autodimp fe2 hyp).

              { apply differ3_bterms_implies_eq_map_num_bvars in dbs; auto. }

              exists (oterm (NCan (NCompOp c))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: bterm [] (mk_instance vars bs5 rhs)
                                   :: bs3))
              (oterm (NCan (NCompOp c))
                     (bterm [] (oterm (Can can1) bs1)
                            :: bterm [] (mk_instance vars bs2 rhs)
                            :: bs)).

             dands; eauto 3 with slow.

             * apply reduces_to_if_step.
               csunf; simpl; csunf; simpl.
               dcwf h.
               applydup @compute_step_lib_if_found_entry in fe2.
               rw fe0; auto.

             * pose proof (differ3_mk_instance b f g rhs vars bs2 bs5) as h.
               repeat (autodimp h hyp); tcsp; GC.
               { unfold correct_abs in correct; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allunfold @correct_abs; sp. }
               { allunfold @correct_abs; sp. }
               unfold differ3_alpha in h.
               exrepnd.

               apply wf_term_ncompop_iff in wt1.
               apply wf_term_ncompop_iff in wt2.
               exrepnd; ginv; allsimpl; cpx.
               apply wf_oterm_iff in wt4.
               apply wf_oterm_iff in wt8.
               repnd.

               apply differ3_ceq_mk_compop; eauto 2 with slow.

               { apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow. }

               { apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
                 try (apply nt_wf_eq; eapply wf_mk_instance; eauto).
                 exists u1 u2; dands; auto. }

               { apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.
                 pose proof (imp (nobnd c1) (nobnd c0)) as xx; autodimp xx hyp.
                 inversion xx; subst; eauto 3 with slow. }

               { apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.
                 pose proof (imp (nobnd d0) (nobnd d)) as xx; autodimp xx hyp.
                 inversion xx; subst; eauto 3 with slow. }

          - SSSCase "NArithOp".
            destruct bs; try (complete (csunf comp; allsimpl; dcwf h));[].
            destruct b0 as [l t].
            destruct l; destruct t as [v|f2|op bs2]; try (complete (csunf comp; allsimpl; dcwf h));[].

            inversion d as [?|?|?|? ? ? len imp]; subst; clear d.
            simpl in len; GC.

            destruct bs3; simpl in len; cpx.
            destruct bs3; simpl in len; cpx.
            simpl in imp.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] (oterm op bs2)) b1) as d2.
            autodimp d2 hyp.

            inversion d1 as [? ? ? df3 dg3 d3]; subst; clear d1.
            inversion d2 as [? ? ? df4 dg4 d4]; subst; clear d2.

            inversion d3 as [|?|?|? ? ? ni1 len1 imp1]; subst; clear d3; cpx.

            dopid op as [can3|ncan3|exc3|abs3] SSSSCase.

            + SSSSCase "Can".
              csunf comp; simpl in comp.
              dcwf h; allsimpl.

              inversion d4 as [|?|?|? ? ? ni2 len2 imp2]; subst; clear d4; cpx.

              apply compute_step_arithop_success_can_can in comp.
              exrepnd; subst.

              allsimpl; cpx.

              allapply @get_param_from_cop_pki; subst; allsimpl; GC.
              exists (@oterm o (Can (Nint (get_arith_op a n1 n2))) [])
                     (@oterm o (Can (Nint (get_arith_op a n1 n2))) []);
                dands; eauto 3 with slow.
              apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow.

            + SSSSCase "NCan".
              rw @compute_step_narithop_ncan2 in comp.
              dcwf h; allsimpl.
              remember (compute_step lib (oterm (NCan ncan3) bs2)) as comp1;
                symmetry in Heqcomp1.
              destruct comp1; ginv.

              pose proof (ind (oterm (NCan ncan3) bs2) (oterm (NCan ncan3) bs2) []) as h; clear ind.
              repeat (autodimp h hyp); tcsp; eauto 2 with slow.

              pose proof (h t0 kk n) as k; clear h.
              repeat (autodimp k hyp).

              { rw @wf_oterm_iff in wt1; allsimpl; repnd.
                pose proof (wt1 (bterm [] (oterm (NCan ncan3) bs2))) as h.
                autodimp h hyp. }

              { rw @wf_oterm_iff in wt2; allsimpl; repnd.
                pose proof (wt2 (bterm [] t0)) as h.
                autodimp h hyp. }

              { apply if_has_value_like_k_narithop_can1 in hv; exrepnd.
                apply (has_value_like_k_lt lib j kk) in hv0; auto. }

              exrepnd.

              apply nt_wf_eq in wt1; apply nt_wf_NArithOp in wt1.
              apply nt_wf_eq in wt2; apply nt_wf_NArithOp in wt2.
              exrepnd; fold_terms; ginv; allsimpl; cpx.

              exists (oterm (NCan (NArithOp a))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: bterm [] t
                                   :: []))
                     (oterm (NCan (NArithOp a))
                            (bterm [] (oterm (Can can1) bs1)
                                   :: bterm [] u'
                                   :: [])).
              dands; eauto 3 with slow.

              * apply reduce_to_prinargs_arith2; eauto with slow; sp.
                allunfold @ca_wf_def; exrepnd; subst; allsimpl; cpx; fold_terms; eauto 3 with slow.

              * apply reduce_to_prinargs_arith2; eauto with slow; sp.

              * apply differ3_ceq_mk_arithop; auto;
                apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
                apply differ3_implies_differ3_alpha.

                { pose proof (imp (nobnd (oterm (Can can1) bs1))
                                  (nobnd (oterm (Can can1) bs4))) as xx.
                  autodimp xx hyp. }

            + SSSSCase "Exc".
              csunf comp; allsimpl; ginv.
              dcwf h; allsimpl; ginv.
              inversion d4 as [|?|?|? ? ? len2 imp2]; subst; clear d4; cpx.
              exists (oterm Exc bs5) (oterm Exc bs2); dands; eauto 3 with slow.
              { apply reduces_to_if_step; csunf; simpl; dcwf h. }
              { apply wf_term_narithop_iff in wt1.
                apply wf_term_narithop_iff in wt2.
                exrepnd; ginv; allsimpl; cpx.
                apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow. }

            + SSSSCase "Abs".
              csunf comp; allsimpl; csunf comp; allsimpl.
              dcwf h.
              remember (compute_step_lib lib abs3 bs2) as comp1.
              symmetry in Heqcomp1; destruct comp1; ginv.
              apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

              inversion d4 as [|?|?|? ? ? ni2 len2 imp2]; subst; simphyps; clear d4.

              assert (differ3_bterms b f g bs2 bs5) as dbs.
              { unfold differ3_bterms, br_bterms, br_list; auto. }

              pose proof (found_entry_change_bs abs3 oa2 vars rhs lib bs2 correct bs5) as fe2.
              repeat (autodimp fe2 hyp).

              { apply differ3_bterms_implies_eq_map_num_bvars in dbs; auto. }

              exists (oterm (NCan (NArithOp a))
                            (bterm [] (oterm (Can can1) bs4)
                                   :: bterm [] (mk_instance vars bs5 rhs)
                                   :: bs3))
              (oterm (NCan (NArithOp a))
                     (bterm [] (oterm (Can can1) bs1)
                            :: bterm [] (mk_instance vars bs2 rhs)
                            :: bs)).

             dands; eauto 3 with slow.

             * apply reduces_to_if_step.
               csunf; simpl; csunf; simpl.
               dcwf h; allsimpl.
               applydup @compute_step_lib_if_found_entry in fe2.
               rw fe0; auto.

             * pose proof (differ3_mk_instance b f g rhs vars bs2 bs5) as h.
               repeat (autodimp h hyp); tcsp; GC.
               { unfold correct_abs in correct; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allapply @found_entry_implies_matching_entry.
                 allunfold @matching_entry; sp. }
               { allunfold @correct_abs; sp. }
               { allunfold @correct_abs; sp. }
               unfold differ3_alpha in h.
               exrepnd.

               apply wf_term_narithop_iff in wt1.
               apply wf_term_narithop_iff in wt2.
               exrepnd; ginv; allsimpl; cpx.
               apply wf_oterm_iff in wt1.
               apply wf_oterm_iff in wt2.
               repnd.

               apply differ3_ceq_mk_arithop; eauto 2 with slow.

               { apply differ3_alpha_implies_differ3_ceq; eauto 3 with slow. }

               { apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow;
                 try (apply nt_wf_eq; eapply wf_mk_instance; eauto).
                 exists u1 u2; dands; auto. }

          - SSSCase "NCanTest".
            csunf comp; allsimpl.
            apply compute_step_can_test_success in comp; exrepnd; subst; allsimpl.
            inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; clear d.
            destruct bs2; allsimpl; cpx.
            destruct bs2; allsimpl; cpx.
            cpx; allsimpl; GC.

            pose proof (imp (bterm [] (oterm (Can can1) bs1)) b0) as d1.
            autodimp d1 hyp.
            pose proof (imp (bterm [] arg2nt) b1) as d2.
            autodimp d2 hyp.
            pose proof (imp (bterm [] arg3nt) x) as d3.
            autodimp d3 hyp.
            clear imp.

            inversion d1 as [? ? ? df4 dg4 d4]; subst; clear d1.
            inversion d2 as [? ? ? df5 dg5 d5]; subst; clear d2.
            inversion d3 as [? ? ? df6 dg6 d6]; subst; clear d3.

            inversion d4 as [|?|?|? ? ? ni1 len1 imp1]; subst; allsimpl; clear d4.

            allrw @wf_can_test_iff; repnd.

            exists (if canonical_form_test_for c can1 then t0 else t3)
                   (if canonical_form_test_for c can1 then arg2nt else arg3nt).
            dands; eauto 3 with slow.
            destruct (canonical_form_test_for c can1); eauto 3 with slow;
            apply differ3_alpha_implies_differ3_ceq; eauto 2 with slow.
        }

        { SSCase "NCan".
          rw @compute_step_ncan_ncan in comp.
          remember (compute_step lib (oterm (NCan ncan1) bs1)) as comp1;
            symmetry in Heqcomp1.
          destruct comp1; ginv.

          inversion d as [? ? ? ? ? ni1 ni2 d1 aeq1 aeq2|?|?|? ? ? len imp];
            subst; clear d.

          - (* let's prove that t1 computes to an integer in less than kk steps *)
            fold_terms; fold (force_int_bound v b t1 (mk_vbot v)) in Heqcomp1.
            applydup @if_has_value_like_k_cbv_primarg in hv; simpl; tcsp; exrepnd.
            assert (has_value_like_k lib (S j) (force_int_bound v b t1 (mk_vbot v))) as hvf.
            { rw @has_value_like_S; eexists; eauto. }
            apply if_has_value_like_k_force_int_bound in hvf; exrepnd.

            pose proof (compind t1 t0 u j0) as r.
            repeat (autodimp r hyp); try omega; exrepnd.

            { allrw <- @wf_cbv_iff; repnd; auto. }

            { apply wf_force_int_bound_app in wt2; sp. }

            repndors; exrepnd; subst.

            { apply differ3_alpha_integer in r0; subst.
              pose proof (agree z) as ag.
              repeat (autodimp ag hyp); eauto with slow.
              exrepnd.

              pose proof (compute_step_force_int_bound lib v b (mk_vbot v) z j0 t1 n) as rz.
              repeat (autodimp rz hyp); eauto with slow.

              pose proof (reduces_to_force_int_bound_app_z
                            lib v b (mk_vbot v) z t0 ga) as h.
              repeat (autodimp h hyp); tcsp; eauto with slow.
              { apply alphaeq_preserves_free_vars in aeq2; rw <- aeq2; auto. }

              pose proof (reduces_to_prinarg
                            lib NCbv
                            n
                            (mk_integer z)
                            [bterm [v] (mk_apply fa (mk_var v))]) as q.
              fold_terms.
              autodimp q hyp.

              pose proof (reduces_to_alpha
                            lib
                            (mk_apply g (mk_integer z))
                            (mk_apply ga (mk_integer z))
                            v2) as k.
              repeat (autodimp k hyp).

              { apply nt_wf_eq.
                apply wf_apply; eauto 3 with slow. }

              { prove_alpha_eq4.
                introv k; destruct n0;[|destruct n0]; cpx.
                apply alphaeqbt_nilv2; auto. }
              exrepnd.

              pose proof (reduces_to_alpha
                            lib
                            (mk_apply f (mk_integer z))
                            (mk_apply fa (mk_integer z))
                            v1) as r.
              repeat (autodimp r hyp).

              { apply nt_wf_eq.
                apply wf_apply; eauto 3 with slow. }

              { prove_alpha_eq4.
                introv r; destruct n0;[|destruct n0]; cpx.
                apply alphaeqbt_nilv2; auto. }
              exrepnd.

              exists t2' t2'0; dands; auto.

              { eapply reduces_to_trans;[exact h|]; auto. }

              { eapply reduces_to_trans;[exact q|].
                eapply reduces_to_if_split2;[csunf;simpl;auto|].
                unfold apply_bterm; simpl; fold_terms.
                unflsubst; simpl; boolvar; tcsp;[]; fold_terms.
                rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow. }

              { eapply differ3_alpha_l;[apply alpha_eq_sym;exact r0|].
                eapply differ3_alpha_r;[|exact k0].
                eapply differ3_alpha_l;[exact ag3|].
                apply differ3_implies_differ3_alpha.
                apply differ3_refl;auto. }
            }

            { apply isexc_implies2 in hvf1; exrepnd; subst.
              applydup @differ3_alpha_exc in r0; eauto with slow;
              try (complete (simpl; boolvar; tcsp)).
              apply isexc_implies2 in r2; exrepnd; subst.

              pose proof (compute_step_force_int_bound_exc
                            lib v b (mk_vbot v) t1 n (oterm Exc l)) as r.
              repeat (autodimp r hyp); eauto with slow.

              exists (oterm Exc l0) (oterm Exc l); dands; auto.

              - pose proof (reduces_to_prinarg
                              lib NCbv
                              (force_int_bound v b t0 (mk_vbot v))
                              (oterm Exc l0)
                              [bterm [v] (mk_apply ga (mk_var v))]) as h.
                fold_terms.
                autodimp h hyp.
                { pose proof (reduces_to_prinarg
                              lib NCbv
                              t0
                              (oterm Exc l0)
                              [bterm [v] (less_bound b (mk_var v) (mk_vbot v))]) as h.
                  fold_terms.
                  autodimp h hyp.
                  eapply reduces_to_trans; eauto with slow. }
                eapply reduces_to_trans; eauto with slow.

              - pose proof (reduces_to_prinarg
                              lib NCbv
                              n
                              (oterm Exc l)
                              [bterm [v] (mk_apply fa (mk_var v))]) as h.
                fold_terms.
                autodimp h hyp.
                eapply reduces_to_trans; eauto with slow.
            }

          - simpl in len.
            destruct bs2; simpl in len; cpx.
            simpl in imp.
            pose proof (imp (bterm [] (oterm (NCan ncan1) bs1)) b0) as d1.
            autodimp d1 hyp.
            inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.

            pose proof (ind (oterm (NCan ncan1) bs1) (oterm (NCan ncan1) bs1) []) as h; clear ind.
            repeat (autodimp h hyp); tcsp; eauto 2 with slow.

            pose proof (h t2 kk n) as k; clear h.
            repeat (autodimp k hyp); tcsp.

            { rw @wf_oterm_iff in wt1; allsimpl; repnd.
              pose proof (wt1 (bterm [] (oterm (NCan ncan1) bs1))) as h.
              autodimp h hyp. }

            { rw @wf_oterm_iff in wt2; allsimpl; repnd.
              pose proof (wt2 (bterm [] t2)) as h.
              autodimp h hyp. }

            { apply if_has_value_like_k_ncan_primarg in hv; auto.
              exrepnd.
              apply (has_value_like_k_lt lib j kk); auto. }

            exrepnd.

            exists (oterm (NCan ncan) (bterm [] t :: bs2))
                   (oterm (NCan ncan) (bterm [] u' :: bs));
              dands; eauto with slow.

            + apply reduces_to_prinarg; auto.
            + apply reduces_to_prinarg; auto.

            + unfold differ3_alpha in k1; exrepnd.
              exists (oterm (NCan ncan) (bterm [] u1 :: bs))
                     (oterm (NCan ncan) (bterm [] u2 :: bs2));
                dands.

              * prove_alpha_eq4.
                introv j; destruct n0; eauto with slow.

              * prove_alpha_eq4.
                introv j; destruct n0; eauto with slow.

              * apply differ3_oterm; simpl; auto.
                introv j; dorn j; cpx.
        }

        { SSCase "Exc".
          csunf comp; allsimpl.
          apply compute_step_catch_success in comp.

          inversion d as [|?|?|? ? ? len imp]; subst; allsimpl; cpx; clear d.
          destruct bs2; allsimpl; cpx.
          pose proof (imp (bterm [] (oterm Exc bs1)) b0) as d1.
          autodimp d1 hyp.
          inversion d1 as [? ? ? df2 dg2 d2]; subst; clear d1.
          inversion d2 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; cpx; clear d2.

          repndors; exrepnd; subst; allsimpl; cpx; allsimpl.

          - pose proof (imp (bterm [] (oterm Exc [bterm [] a', bterm [] e]))
                            (bterm [] (oterm Exc [x0, y0]))) as d1; autodimp d1 hyp.
            pose proof (imp (bterm [] a) x) as d2; autodimp d2 hyp.
            pose proof (imp (bterm [v] b0) y) as d3; autodimp d3 hyp.
            pose proof (imp1 (bterm [] a') x0) as d4; autodimp d4 hyp.
            pose proof (imp1 (bterm [] e) y0) as d5; autodimp d5 hyp.
            clear imp imp1.

            inversion d1 as [? ? ? df66 dg66 d6]; subst; clear d1.
            inversion d2 as [? ? ? df77 dg77 d7]; subst; clear d2.
            inversion d3 as [? ? ? df88 dg88 d8]; subst; clear d3.
            inversion d4 as [? ? ? df99 dg99 d9]; subst; clear d4.
            inversion d5 as [? ? ? df10 dg10 d10]; subst; clear d5.
            repeat match goal with
                     | [ H : disjoint [] _ |- _ ] => clear H
                   end.

            inversion d6 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; cpx; clear d6.
            pose proof (imp1 (bterm [] a') (bterm [] t3)) as d1; autodimp d1 hyp.
            pose proof (imp1 (bterm [] e) (bterm [] t4)) as d2; autodimp d2 hyp.
            clear imp1.

            inversion d1 as [? ? ? df33 dg33 d3]; subst; clear d1.
            inversion d2 as [? ? ? df44 dg44 d4]; subst; clear d2.
            repeat match goal with
                     | [ H : disjoint [] _ |- _ ] => clear H
                   end.

            exists (mk_atom_eq t2 t3 (subst t0 v t4) (mk_exception t3 t4))
                   (mk_atom_eq a a' (subst b0 v e) (mk_exception a' e));
              dands; eauto with slow.

            apply differ3_alpha_mk_atom_eq; eauto 4 with slow.

            apply differ3_subst; simpl; eauto with slow.

          - exists (oterm Exc bs3) (oterm Exc bs1); dands; eauto with slow.

            apply reduces_to_if_step; csunf; simpl.
            unfold compute_step_catch; destruct ncan; tcsp.
        }

        { SSCase "Abs".
          csunf comp; allsimpl; csunf comp; allsimpl.
          remember (compute_step_lib lib abs1 bs1) as comp1;
            symmetry in Heqcomp1.
          destruct comp1; ginv.

          inversion d as [|?|?|? ? ? len imp]; subst; clear d.
          destruct bs2; allsimpl; cpx.
          pose proof (imp (bterm [] (oterm (Abs abs1) bs1)) b0) as d1.
          autodimp d1 hyp.
          inversion d1 as [? ? ? df2 sg2 d2]; subst; clear d1.
          inversion d2 as [|?|?|? ? ? len1 imp1]; subst; allsimpl; cpx; clear d2.

          apply compute_step_lib_success in Heqcomp1; exrepnd; subst.

          assert (differ3_bterms b f g bs1 bs3) as dbs.
          { unfold differ3_bterms, br_bterms, br_list; auto. }

          pose proof (found_entry_change_bs abs1 oa2 vars rhs lib bs1 correct bs3) as fe2.
          repeat (autodimp fe2 hyp).

          { apply differ3_bterms_implies_eq_map_num_bvars in dbs; auto. }

          exists
          (oterm (NCan ncan)
                 (bterm [] (mk_instance vars bs3 rhs)
                        :: bs2))
          (oterm (NCan ncan)
                 (bterm [] (mk_instance vars bs1 rhs)
                        :: bs)).

          dands; eauto with slow.

          * apply reduces_to_prinarg.
            apply reduces_to_if_step.
            csunf; simpl; unfold on_success.
            applydup @compute_step_lib_if_found_entry in fe2.
            rw fe0; auto.

          * pose proof (differ3_mk_instance b f g rhs vars bs1 bs3) as h.
            repeat (autodimp h hyp); tcsp; GC.
            { unfold correct_abs in correct; sp. }
            { allapply @found_entry_implies_matching_entry.
              allunfold @matching_entry; sp. }
            { allapply @found_entry_implies_matching_entry.
              allunfold @matching_entry; sp. }
            { allunfold @correct_abs; sp. }
            { allunfold @correct_abs; sp. }
            unfold differ3_alpha in h.
            exrepnd.

            exists
              (oterm (NCan ncan) (bterm [] u1 :: bs))
              (oterm (NCan ncan) (bterm [] u2 :: bs2)).
            dands.

            { prove_alpha_eq4.
              introv j; destruct n;[|destruct n]; try omega; cpx.
              apply alphaeqbt_nilv2; auto. }

            { prove_alpha_eq4.
              introv j; destruct n;[|destruct n]; try omega; cpx.
              apply alphaeqbt_nilv2; auto. }

            { apply differ3_oterm; allsimpl; tcsp.
              introv j; repndors; cpx. }
        }
      }

      { (* fresh case *)
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; repnd; subst; allsimpl.

        inversion d as [|?|?|? ? ? len1 imp1]; subst; clear d.
        allsimpl; cpx; allsimpl.
        pose proof (imp1 (bterm [n] t1) x) as d1; autodimp d1 hyp.
        clear imp1.
        inversion d1 as [? ? ? disj11 disj12 d2]; subst; clear d1.
        allrw disjoint_singleton_l.

        repndors; exrepnd; subst; fold_terms.

        - inversion d2; subst.
          apply has_value_like_k_fresh_id in hv; sp.

        - applydup @differ3_preserves_isvalue_like in d2; auto.
          exists (pushdown_fresh n t2) (pushdown_fresh n t1); dands; eauto 3 with slow.
          { apply reduces_to_if_step.
            apply compute_step_fresh_if_isvalue_like; auto. }
          { apply differ3_alpha_pushdown_fresh_isvalue_like; auto. }

        - applydup @differ3_preserves_isnoncan_like in d2; auto;[].
          allrw app_nil_r.

          pose proof (fresh_atom o (get_utokens t1 ++ get_utokens t2 ++ get_utokens f ++ get_utokens g)) as fa; exrepnd.
          allrw in_app_iff; allrw not_over_or; repnd.
          rename x0 into a.

          pose proof (compute_step_subst_utoken lib t1 x [(n,mk_utoken (get_fresh_atom t1))]) as comp'.
          allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
          allrw disjoint_singleton_l.
          repeat (autodimp comp' hyp); try (apply get_fresh_atom_prop).
          { apply wf_fresh_iff in wt1; eauto 2 with slow. }
          { apply nr_ut_sub_cons; eauto with slow.
            intro j; apply get_fresh_atom_prop. }
          exrepnd.
          pose proof (comp'0 [(n,mk_utoken a)]) as comp''; clear comp'0.
          allsimpl.
          allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
          allrw disjoint_singleton_l.
          repeat (autodimp comp'' hyp); exrepnd.

          pose proof (differ3_subst b f g t1 t2 [(n, mk_utoken a)] [(n, mk_utoken a)]) as daeq.
          repeat (autodimp daeq hyp);
            try (complete (simpl; apply disjoint_singleton_r; auto));
            try (complete (apply differ3_subs_refl; simpl; auto));
            eauto 3 with slow.

          unfold differ3_alpha in daeq; exrepnd.

          pose proof (compute_step_alpha lib (lsubst t1 [(n, mk_utoken a)]) u1 s) as comp'''.
          repeat (autodimp comp''' hyp); exrepnd.

          { apply wf_fresh_iff in wt1.
            apply nt_wf_subst; eauto 2 with slow. }

          rename t2' into s'.

          assert (wf_term x) as wfx.
          { eapply compute_step_preserves_wf;[exact comp2|].
            allrw @wf_fresh_iff.
            apply wf_term_subst; eauto 3 with slow. }

          assert (!LIn n (free_vars x)) as ninx.
          { intro i; apply compute_step_preserves in comp2; repnd.
            rw subvars_prop in comp0; apply comp0 in i; clear comp0.
            apply eqset_free_vars_disjoint in i; allsimpl.
            allrw in_app_iff; allrw in_remove_nvars; allsimpl; boolvar; allsimpl; tcsp.
            apply wf_fresh_iff in wt1.
            apply nt_wf_subst; eauto 2 with slow.
          }

          pose proof (ind t1 u1 [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { apply alpha_eq_preserves_osize in daeq0.
            rw <- daeq0; allrw @fold_subst.
            rw @simple_osize_subst; eauto 2 with slow. }
          pose proof (q u2 kk s') as ih; clear q.

          assert (wf_term t1) as wft1.
          { apply wf_fresh_iff in wt1; auto. }

          assert (wf_term t2) as wft2.
          { apply wf_fresh_iff in wt2; auto. }

          assert (wf_term u1) as wfu1.
          { apply alphaeq_preserves_wf_term in daeq0; eauto 2 with slow.
            apply wf_term_subst; eauto 2 with slow. }

          assert (wf_term u2) as wfu2.
          { apply alphaeq_preserves_wf_term in daeq2; eauto 2 with slow.
            apply wf_term_subst; eauto 2 with slow. }

          assert (wf_term s') as wfs'.
          { apply compute_step_preserves_wf in comp'''1; auto. }

          assert (wf_term s) as wfs.
          { apply alpha_eq_sym in comp'''0.
            apply alphaeq_preserves_wf_term in comp'''0; eauto 2 with slow. }

          repeat (autodimp ih hyp); fold_terms.
          { eapply alphaeq_preserves_has_value_like_k;[|exact comp'''0|]; eauto 2 with slow.
            eapply alphaeq_preserves_has_value_like_k;[|apply alpha_eq_sym;exact comp''0|]; eauto 3 with slow.
            pose proof (has_value_like_k_ren_utokens
                          lib
                          kk
                          (lsubst w [(n, mk_utoken (get_fresh_atom t1))])
                          [(get_fresh_atom t1,a)]) as hvl.
            allsimpl.
            allrw disjoint_singleton_l; allrw in_remove.
            repeat (autodimp hvl hyp).
            { apply alphaeq_preserves_wf_term in comp'1; eauto 2 with slow. }
            { intro k; repnd.
              apply get_utokens_lsubst_subset in k; unfold get_utokens_sub in k; allsimpl.
              allrw in_app_iff; allsimpl; repndors; tcsp. }
            { eapply alphaeq_preserves_has_value_like_k;[|exact comp'1|]; eauto 3 with slow.
              apply (has_value_like_k_fresh_implies lib kk (get_fresh_atom t1)) in hv; auto;
              [|apply wf_subst_utokens; eauto 3 with slow
               |intro i; apply get_utokens_subst_utokens_subset in i; allsimpl;
                unfold get_utokens_utok_ren in i; allsimpl; allrw app_nil_r;
                rw in_remove in i; repnd; eauto 3 with slow;
                apply compute_step_preserves_utokens in comp2; apply comp2 in i;
                apply get_utokens_subst in i; allsimpl; boolvar; tcsp].
              pose proof (simple_subst_subst_utokens_aeq x (get_fresh_atom t1) n) as h.
              repeat (autodimp h hyp).
              eapply alphaeq_preserves_has_value_like_k in h;[exact h| |]; auto.
              apply nt_wf_subst; eauto 2 with slow.
              apply nt_wf_eq; apply wf_subst_utokens; eauto 3 with slow.
            }
            rw @lsubst_ren_utokens in hvl; allsimpl; fold_terms.
            unfold ren_atom in hvl; allsimpl; boolvar; tcsp.
            rw @ren_utokens_trivial in hvl; simpl; auto.
            apply disjoint_singleton_l; intro i; apply comp'4 in i; apply get_fresh_atom_prop in i; sp.
          }
          exrepnd.

          pose proof (reduces_to_alpha lib u2 (lsubst t2 [(n, mk_utoken a)]) t) as r1.
          repeat (autodimp r1 hyp); eauto 3 with slow.
          exrepnd.

          pose proof (reduces_to_change_utok_sub
                        lib t2 t2' [(n,mk_utoken a)] [(n,mk_utoken (get_fresh_atom t2))]) as r1'.
          allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allsimpl.
          allrw disjoint_singleton_l.
          repeat (autodimp r1' hyp); try (apply get_fresh_atom_prop); eauto 2 with slow.
          { apply nr_ut_sub_cons; eauto with slow.
            intro j; apply get_fresh_atom_prop. }
          exrepnd.
          allrw disjoint_singleton_l.
          fold_terms; allrw @fold_subst.

          pose proof (reduces_to_fresh lib t2 s0 n) as q; simpl in q.
          repeat (autodimp q hyp).
          exrepnd.

          (* 1st exists *)
          exists (mk_fresh n z).

          assert (!LIn a (get_utokens w)) as niaw.
          { intro k; apply comp'4 in k; sp. }

          pose proof (alpha_eq_subst_utokens
                        x (subst w n (mk_utoken (get_fresh_atom t1)))
                        [(get_fresh_atom t1, mk_var n)]
                        [(get_fresh_atom t1, mk_var n)]) as aeqs.
          repeat (autodimp aeqs hyp); eauto 3 with slow.
          pose proof (simple_alphaeq_subst_utokens_subst
                        w n (get_fresh_atom t1)) as aeqs1.
          autodimp aeqs1 hyp.
          eapply alpha_eq_trans in aeqs1;[|exact aeqs]; clear aeqs.

          pose proof (reduces_to_alpha lib s' (subst w n (mk_utoken a)) u') as raeq.
          repeat (autodimp raeq hyp); eauto 3 with slow; exrepnd;[].
          rename t2'0 into u''.

          assert (wf_term w) as wfw.
          { apply compute_step_preserves_wf in comp2;
              [|apply wf_term_subst;eauto with slow].
            apply alphaeq_preserves_wf_term in comp'1; auto.
            apply lsubst_wf_term in comp'1; auto.
          }

          pose proof (reduces_to_fresh2 lib w u'' n a) as rf.
          repeat (autodimp rf hyp); exrepnd.

          pose proof (reduces_to_alpha
                        lib
                        (mk_fresh n w)
                        (mk_fresh n (subst_utokens x [(get_fresh_atom t1, mk_var n)]))
                        (mk_fresh n z0)) as r'.
          repeat (autodimp r' hyp).
          { apply nt_wf_fresh; eauto 2 with slow. }
          { apply implies_alpha_eq_mk_fresh; eauto with slow. }
          exrepnd.
          rename t2'0 into f'.

          (* 2nd exists *)
          exists f'; dands; auto.
          eapply differ3_alpha_l;[apply alpha_eq_sym; exact r'0|].
          apply differ3_alpha_mk_fresh; auto.
          eapply differ3_alpha_l;[exact rf0|].
          eapply differ3_alpha_r;[|apply alpha_eq_sym; exact q0].
          eapply differ3_alpha_l;[apply alpha_eq_sym;apply alpha_eq_subst_utokens_same;exact raeq0|].
          eapply differ3_alpha_r;[|apply alpha_eq_sym;apply alpha_eq_subst_utokens_same;exact r1'1].

          pose proof (simple_alphaeq_subst_utokens_subst w0 n (get_fresh_atom t2)) as aeqsu.
          autodimp aeqsu hyp.
          { intro j; apply r1'4 in j; apply get_fresh_atom_prop in j; sp. }

          eapply differ3_alpha_r;[|apply alpha_eq_sym;exact aeqsu];clear aeqsu.

          apply (alpha_eq_subst_utokens_same _ _ [(a, mk_var n)]) in r1'0.
          pose proof (simple_alphaeq_subst_utokens_subst w0 n a) as aeqsu.
          autodimp aeqsu hyp.

          eapply differ3_alpha_r;[|exact aeqsu];clear aeqsu.
          eapply differ3_alpha_r;[|exact r1'0].
          eapply differ3_alpha_r;[|apply alpha_eq_subst_utokens_same; exact r0].
          apply differ3_alpha_subst_utokens; simpl; auto; allrw disjoint_singleton_r; auto.
      }

    + SCase "Exc".
      csunf comp; allsimpl; ginv.

      inversion d as [|?|?|? ? ? ni len imp]; subst; allsimpl; cpx; clear d.

      exists (oterm Exc bs2) (oterm Exc bs); dands; eauto with slow.

    + SCase "Abs".
      csunf comp; allsimpl.

      inversion d as [|?|?|? ? ? ni len imp]; subst; clear d.

      apply compute_step_lib_success in comp; exrepnd; subst.

      assert (differ3_bterms b f g bs bs2) as dbs.
      { unfold differ3_bterms, br_bterms, br_list; auto. }

      pose proof (found_entry_change_bs abs oa2 vars rhs lib bs correct bs2) as fe2.
      repeat (autodimp fe2 hyp).

      { apply differ3_bterms_implies_eq_map_num_bvars in dbs; auto. }

      exists (mk_instance vars bs2 rhs) (mk_instance vars bs rhs).

      dands; eauto with slow.

      * apply reduces_to_if_step.
        csunf; simpl; unfold on_success.
        applydup @compute_step_lib_if_found_entry in fe2.
        rw fe0; auto.

      * pose proof (differ3_mk_instance b f g rhs vars bs bs2) as h.
        repeat (autodimp h hyp); tcsp; GC.
        { unfold correct_abs in correct; sp. }
        { allapply @found_entry_implies_matching_entry.
          allunfold @matching_entry; sp. }
        { allapply @found_entry_implies_matching_entry.
          allunfold @matching_entry; sp. }
        { allunfold @correct_abs; sp. }
        { allunfold @correct_abs; sp. }
Qed.

(*
Lemma isvalue_like_except_implies_isvalue_like {o} :
  forall a (t : @NTerm o),
    isvalue_like_except a t
    -> isvalue_like t.
Proof.
  introv isv.
  unfold isvalue_like_except in isv; sp.
Qed.
Hint Resolve isvalue_like_except_implies_isvalue_like : slow.

Lemma alpha_eq_preserves_isvalue_like_except {o} :
  forall a (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> isvalue_like_except a t1
    -> isvalue_like_except a t2.
Proof.
  introv aeq isv.
  allunfold @isvalue_like_except; repnd.
  applydup @alpha_eq_preserves_isvalue_like in aeq; auto.
  dands; auto.
  intro k.
  apply isnexc_implies in k; exrepnd; subst.
  inversion aeq; subst; allsimpl; boolvar; ginv; tcsp.
Qed.
*)

Lemma comp_force_int3_aux_2 {o} :
  forall lib f g (t1 t2 : @NTerm o) b u,
    isprog f
    -> isprog g
    -> wf_term t1
    -> wf_term t2
    -> agree_upto lib b f g
    -> differ3 b f g t1 t2
    -> isvalue_like u
    -> reduces_to lib t1 u
    -> {v : NTerm & reduces_to lib t2 v # differ3_alpha b f g u v}.
Proof.
  introv ispf ispg wt1 wt2 agree d isv comp.
  unfold reduces_to in comp; exrepnd.
  revert t1 t2 u wt1 wt2 d isv comp0.
  induction k as [n ind] using comp_ind_type; introv wt1 wt2 d isv r.
  destruct n as [|k]; allsimpl.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists t2; dands; eauto with slow.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.

    pose proof (comp_force_int_step3_2 lib b f g t1 t2 k u0) as h.
    repeat (autodimp h hyp).

    { exists u; unfold computes_to_val_like_in_max_k_steps; sp. }

    { introv l' w1 w2 i' r' d'.
      apply (ind m l' t0 t3); auto. }

    exrepnd.

    pose proof (reduces_in_atmost_k_steps_if_reduces_to
                  lib k u0 u' u) as h'.
    repeat (autodimp h' hyp); eauto 3 with slow.
    exrepnd.

    unfold differ3_alpha in h1; exrepnd.

    assert (wf_term u0) as wfu0.
    { apply compute_step_preserves_wf in r1; auto. }

    assert (wf_term u') as wfu'.
    { apply reduces_to_preserves_wf in h2; auto. }

    assert (wf_term u1) as wfu1.
    { apply alphaeq_preserves_wf_term in h3; auto. }

    assert (wf_term t) as wft.
    { apply reduces_to_preserves_wf in h0; auto. }

    assert (wf_term u2) as wfu2.
    { apply alphaeq_preserves_wf_term in h4; auto. }

    pose proof (reduces_in_atmost_k_steps_alpha
                  lib u' u1) as h''.
    repeat (autodimp h'' hyp); eauto 3 with slow.

    pose proof (h'' k' u) as h'''; clear h''.
    autodimp h''' hyp; exrepnd.

    pose proof (ind k') as h.
    autodimp h hyp;[omega|].
    pose proof (h u1 u2 t2') as r'; clear h.
    repeat (autodimp r' hyp).

    { eapply alpha_eq_preserves_isvalue_like in h'''0; eauto. }

    exrepnd.

    pose proof (reduces_to_steps_alpha lib u2 t v) as r'.
    repeat (autodimp r' hyp); eauto 3 with slow.
    exrepnd.
    exists u3; dands; eauto 3 with slow.

    { eapply reduces_to_trans; eauto. }

    { allunfold @differ3_alpha; exrepnd.
      exists u4 u5; dands; eauto with slow. }
Qed.

Lemma comp_force_int3_2 {o} :
  forall lib f g (t1 t2 : @NTerm o) b z,
    isprog f
    -> isprog g
    -> wf_term t1
    -> wf_term t2
    -> agree_upto lib b f g
    -> differ3 b f g t1 t2
    -> reduces_to lib t1 (mk_integer z)
    -> reduces_to lib t2 (mk_integer z).
Proof.
  introv ispf ispg wt1 wt2 agree d comp.
  pose proof (comp_force_int3_aux_2 lib f g t1 t2 b (mk_integer z)) as h.
  repeat (autodimp h hyp); eauto 3 with slow.

  exrepnd.
  apply differ3_alpha_integer in h0; subst; auto.
Qed.

Lemma comp_force_int_app_F3_2 {o} :
  forall lib (F f g : @NTerm o) x z b,
    wf_term F
    -> isprog f
    -> isprog g
    -> !LIn x (free_vars f)
    -> !LIn x (free_vars g)
    -> disjoint (bound_vars F) (free_vars f)
    -> disjoint (bound_vars F) (free_vars g)
    -> agree_upto lib b f g
    -> reduces_to
         lib
         (force_int_bound_F x b F f (mk_vbot x))
         (mk_integer z)
    -> reduces_to
         lib
         (force_int_bound_F x b F g (mk_vbot x))
         (mk_integer z).
Proof.
  introv wF wf wg ni1 ni2 df dg agree r.

  apply (comp_force_int3_2 _ f g (force_int_bound_F x b F f (mk_vbot x)) _ b); eauto 4 with slow.

  apply differ_app_F3; auto; allrw; tcsp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
