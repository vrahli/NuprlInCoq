(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export prog.
Require Export cequiv.
Require Export csubst2.
Require Export substc_more.
Require Export terms5.
Require Export computation_exc.
Require Export computation_dec1.
(*Require Export computation_dec.*)
Require Export computation8.


Lemma computes_to_value_if_iscan {o} :
  forall lib (t u : @NTerm o),
    computes_to_value lib t u
    -> iscan t
    -> t = u.
Proof.
  introv comp isc.
  unfold computes_to_value in comp; repnd.
  apply reduces_to_if_isvalue_like in comp0; eauto 3 with slow.
Qed.

Lemma approx_open_implies_approx_open_bterm {o} :
  forall lib vs (t1 t2 : @NTerm o),
    approx_open lib t1 t2
    -> approx_open_bterm lib (bterm vs t1) (bterm vs t2).
Proof.
  introv apr.
  unfold approx_open_bterm, blift.
  exists vs t1 t2; dands; auto.
Qed.

Lemma isvalue_like_mk_function {o} :
  forall (t1 : @NTerm o) v t2,
    isvalue_like (mk_function t1 v t2).
Proof.
  introv.
  unfold isvalue_like; simpl; tcsp.
Qed.
Hint Resolve isvalue_like_mk_function : slow.

Lemma isvalue_like_mk_product {o} :
  forall (t1 : @NTerm o) v t2,
    isvalue_like (mk_product t1 v t2).
Proof.
  introv.
  unfold isvalue_like; simpl; tcsp.
Qed.
Hint Resolve isvalue_like_mk_product : slow.

Lemma isvalue_like_mk_set {o} :
  forall (t1 : @NTerm o) v t2,
    isvalue_like (mk_set t1 v t2).
Proof.
  introv.
  unfold isvalue_like; simpl; tcsp.
Qed.
Hint Resolve isvalue_like_mk_set : slow.

Lemma approx_mk_fun {o} :
  forall lib (t1 t2 u1 u2 : @NTerm o),
    approx lib t1 u1
    -> approx lib t2 u2
    -> approx lib (mk_fun t1 t2) (mk_fun u1 u2).
Proof.
  introv c1 c2.
  destruct (ex_fresh_var (free_vars t2 ++ free_vars u2)) as [v fv].
  allrw in_app_iff; allrw not_over_or; repnd.

  eapply approx_alpha_rw_r_aux;
    [apply (alphaeq_function_fun _ v);
      apply disjoint_singleton_l;auto|].
  eapply approx_alpha_rw_l_aux;
    [apply (alphaeq_function_fun _ v);
      apply disjoint_singleton_l;auto|].

  applydup @approx_isprog in c1.
  applydup @approx_isprog in c2.
  repnd.

  assert (isprogram (mk_function t1 v t2)) as isp1.
  { apply isprogram_eq; rw <- @isprog_function_iff; dands; eauto 2 with slow. }

  assert (isprogram (mk_function u1 v u2)) as isp2.
  { apply isprogram_eq; rw <- @isprog_function_iff; dands; eauto 2 with slow. }

  constructor.
  unfold close_comput.
  dands; auto.

  - introv comp.
    apply computes_to_value_if_iscan in comp; simpl; auto.
    unfold mk_function in comp; ginv.
    exists [nobnd u1, bterm [v] u2]; fold_terms; dands; auto;
    [apply computes_to_value_isvalue_refl; apply isvalue_function; auto|].
    apply clearbot_relbt2.
    unfold lblift; simpl; dands; auto.
    introv i.
    repeat (destruct n; tcsp; try omega); clear i; unfold selectbt; simpl.

    + apply blift_approx_open_nobnd2; eauto 3 with slow.

    + apply approx_open_implies_approx_open_bterm.
      apply approx_implies_approx_open; auto.

  - introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.
Qed.

Lemma alphaeq_product_prod {p} :
  forall A v B,
    disjoint [v] (@free_vars p B)
    -> alpha_eq (mk_product A v B)
             (mk_prod A B).
Proof.
  introv Hdis.

  destruct_cterms.
  unfold alphaeqc; simpl.
  unfold mk_prod, mk_product, nobnd.
  prove_alpha_eq3.
  pose proof (newvar_prop B).
  simpl. apply alpha_eq_bterm_congr2; disjoint_reasoningv.
Qed.

Lemma approx_mk_prod {o} :
  forall lib (t1 t2 u1 u2 : @NTerm o),
    approx lib t1 u1
    -> approx lib t2 u2
    -> approx lib (mk_prod t1 t2) (mk_prod u1 u2).
Proof.
  introv c1 c2.
  destruct (ex_fresh_var (free_vars t2 ++ free_vars u2)) as [v fv].
  allrw in_app_iff; allrw not_over_or; repnd.

  eapply approx_alpha_rw_r_aux;
    [apply (alphaeq_product_prod _ v);
      apply disjoint_singleton_l;auto|].
  eapply approx_alpha_rw_l_aux;
    [apply (alphaeq_product_prod _ v);
      apply disjoint_singleton_l;auto|].

  applydup @approx_isprog in c1.
  applydup @approx_isprog in c2.
  repnd.

  assert (isprogram (mk_product t1 v t2)) as isp1.
  { apply isprogram_eq; rw <- @isprog_product_iff; dands; eauto 2 with slow. }

  assert (isprogram (mk_product u1 v u2)) as isp2.
  { apply isprogram_eq; rw <- @isprog_product_iff; dands; eauto 2 with slow. }

  constructor.
  unfold close_comput.
  dands; auto.

  - introv comp.
    apply computes_to_value_if_iscan in comp; simpl; auto.
    unfold mk_product in comp; ginv.
    exists [nobnd u1, bterm [v] u2]; fold_terms; dands; auto;
    [apply computes_to_value_isvalue_refl; apply isvalue_product; auto|].
    apply clearbot_relbt2.
    unfold lblift; simpl; dands; auto.
    introv i.
    repeat (destruct n; tcsp; try omega); clear i; unfold selectbt; simpl.

    + apply blift_approx_open_nobnd2; eauto 3 with slow.

    + apply approx_open_implies_approx_open_bterm.
      apply approx_implies_approx_open; auto.

  - introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.
Qed.

Lemma isprog_vars_lsubst_prog_sub {o} :
  forall vs (t : @NTerm o) sub,
    prog_sub sub
    -> isprog_vars (vs ++ dom_sub sub) t
    -> isprog_vars vs (lsubst t sub).
Proof.
  introv ps isp.
  apply csubst.isprog_vars_lsubst; auto.
  apply prog_sub_eq; auto.
Qed.

Lemma isprog_vars_lsubst_prog_sub_iff {o} :
  forall vs (t : @NTerm o) sub,
    prog_sub sub
    -> (isprog_vars (vs ++ dom_sub sub) t
        <=> isprog_vars vs (lsubst t sub)).
Proof.
  introv ps.
  split; intro h; try (apply isprog_vars_lsubst_prog_sub; auto).
  allrw @isprog_vars_eq; repnd.
  allrw @nt_wf_lsubst_iff; repnd.
  dands; auto.
  allrw @subvars_eq; introv i; rw in_app_iff.
  destruct (in_deq _ deq_nvar x (dom_sub sub)) as [j|j]; tcsp.
  pose proof (h0 x) as k; autodimp k hyp; tcsp.
  apply eqset_free_vars_disjoint.
  rw in_app_iff; rw in_remove_nvars; tcsp.
Qed.

Lemma approx_open_mk_fun {o} :
  forall lib (t1 t2 u1 u2 : @NTerm o),
    approx_open lib t1 u1
    -> approx_open lib t2 u2
    -> approx_open lib (mk_fun t1 t2) (mk_fun u1 u2).
Proof.
  introv apro1 apro2.
  destruct (ex_fresh_var (free_vars t2 ++ free_vars u2)) as [v fv].
  allrw in_app_iff; allrw not_over_or; repnd.

  eapply approx_open_alpha_rw_r_aux;
    [apply (alphaeq_function_fun _ v);
      apply disjoint_singleton_l;auto|].
  eapply approx_open_alpha_rw_l_aux;
    [apply (alphaeq_function_fun _ v);
      apply disjoint_singleton_l;auto|].

  allrw <- @approx_open_simpler_equiv.
  allunfold @simpl_olift; repnd.
  allrw @nt_wf_eq.
  dands; eauto 3 with slow.
  introv prs ispl1 ispl2.

  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
  repeat (rw @cl_lsubst_lsubst_aux in ispl1; eauto 3 with slow).
  repeat (rw @cl_lsubst_lsubst_aux in ispl2; eauto 3 with slow).
  allsimpl; fold_terms; allrw @sub_filter_nil_r.

  constructor.
  unfold close_comput.
  dands; auto.

  - introv comp.
    apply computes_to_value_if_iscan in comp; simpl; auto.
    unfold mk_function in comp; ginv.
    eexists; dands;
    [apply computes_to_value_isvalue_refl;apply isvalue_function; auto|].
    apply clearbot_relbt2.
    unfold lblift; simpl; dands; auto.
    introv i.
    repeat (destruct n; tcsp; try omega); clear i; unfold selectbt; simpl.

    + apply blift_approx_open_nobnd2; eauto 3 with slow.
      repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
      allrw @isprogram_eq; allrw <- @isprog_function_iff; repnd.
      repeat (rw <- @cl_lsubst_lsubst_aux in ispl3; eauto 3 with slow).
      repeat (rw <- @cl_lsubst_lsubst_aux in ispl0; eauto 3 with slow).
      apply apro1; allrw @isprogram_eq; eauto 3 with slow.

    + apply approx_open_implies_approx_open_bterm.
      apply approx_implies_approx_open; auto.
      repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
      allrw @isprogram_eq; allrw <- @isprog_function_iff; repnd.
      repeat (rw <- @cl_lsubst_lsubst_aux in ispl1; eauto 3 with slow).
      repeat (rw <- @cl_lsubst_lsubst_aux in ispl2; eauto 3 with slow).
      apply apro2; allrw @isprogram_eq; eauto 3 with slow.
      * eapply isprog_vars_disjoint_implies_isprog;[exact ispl1|].
        apply disjoint_singleton_l.
        intro i; apply eqset_free_vars_disjoint in i.
        allrw <- @dom_sub_sub_filter.
        allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff.
        repndors; tcsp.
        allrw @in_sub_free_vars_iff; exrepnd.
        allrw @in_sub_keep_first; repnd.
        allrw @sub_find_sub_filter_eq; allrw memvar_singleton; boolvar; ginv.
        apply sub_find_some in i2.
        assert (cl_sub sub) as cl by eauto with slow.
        rw @cl_sub_eq2 in cl; apply cl in i2; rw i2 in i1; allsimpl; tcsp.
      * eapply isprog_vars_disjoint_implies_isprog;[exact ispl2|].
        apply disjoint_singleton_l.
        intro i; apply eqset_free_vars_disjoint in i.
        allrw <- @dom_sub_sub_filter.
        allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff.
        repndors; tcsp.
        allrw @in_sub_free_vars_iff; exrepnd.
        allrw @in_sub_keep_first; repnd.
        allrw @sub_find_sub_filter_eq; allrw memvar_singleton; boolvar; ginv.
        apply sub_find_some in i2.
        assert (cl_sub sub) as cl by eauto with slow.
        rw @cl_sub_eq2 in cl; apply cl in i2; rw i2 in i1; allsimpl; tcsp.

  - introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.
Qed.

Lemma approx_open_mk_prod {o} :
  forall lib (t1 t2 u1 u2 : @NTerm o),
    approx_open lib t1 u1
    -> approx_open lib t2 u2
    -> approx_open lib (mk_prod t1 t2) (mk_prod u1 u2).
Proof.
  introv apro1 apro2.
  destruct (ex_fresh_var (free_vars t2 ++ free_vars u2)) as [v fv].
  allrw in_app_iff; allrw not_over_or; repnd.

  eapply approx_open_alpha_rw_r_aux;
    [apply (alphaeq_product_prod _ v);
      apply disjoint_singleton_l;auto|].
  eapply approx_open_alpha_rw_l_aux;
    [apply (alphaeq_product_prod _ v);
      apply disjoint_singleton_l;auto|].

  allrw <- @approx_open_simpler_equiv.
  allunfold @simpl_olift; repnd.
  allrw @nt_wf_eq.
  dands; eauto 3 with slow.
  introv prs ispl1 ispl2.

  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
  repeat (rw @cl_lsubst_lsubst_aux in ispl1; eauto 3 with slow).
  repeat (rw @cl_lsubst_lsubst_aux in ispl2; eauto 3 with slow).
  allsimpl; fold_terms; allrw @sub_filter_nil_r.

  constructor.
  unfold close_comput.
  dands; auto.

  - introv comp.
    apply computes_to_value_if_iscan in comp; simpl; auto.
    unfold mk_product in comp; ginv.
    eexists; dands;
    [apply computes_to_value_isvalue_refl;apply isvalue_product; auto|].
    apply clearbot_relbt2.
    unfold lblift; simpl; dands; auto.
    introv i.
    repeat (destruct n; tcsp; try omega); clear i; unfold selectbt; simpl.

    + apply blift_approx_open_nobnd2; eauto 3 with slow.
      repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
      allrw @isprogram_eq; allrw <- @isprog_product_iff; repnd.
      repeat (rw <- @cl_lsubst_lsubst_aux in ispl3; eauto 3 with slow).
      repeat (rw <- @cl_lsubst_lsubst_aux in ispl0; eauto 3 with slow).
      apply apro1; allrw @isprogram_eq; eauto 3 with slow.

    + apply approx_open_implies_approx_open_bterm.
      apply approx_implies_approx_open; auto.
      repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
      allrw @isprogram_eq; allrw <- @isprog_product_iff; repnd.
      repeat (rw <- @cl_lsubst_lsubst_aux in ispl1; eauto 3 with slow).
      repeat (rw <- @cl_lsubst_lsubst_aux in ispl2; eauto 3 with slow).
      apply apro2; allrw @isprogram_eq; eauto 3 with slow.
      * eapply isprog_vars_disjoint_implies_isprog;[exact ispl1|].
        apply disjoint_singleton_l.
        intro i; apply eqset_free_vars_disjoint in i.
        allrw <- @dom_sub_sub_filter.
        allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff.
        repndors; tcsp.
        allrw @in_sub_free_vars_iff; exrepnd.
        allrw @in_sub_keep_first; repnd.
        allrw @sub_find_sub_filter_eq; allrw memvar_singleton; boolvar; ginv.
        apply sub_find_some in i2.
        assert (cl_sub sub) as cl by eauto with slow.
        rw @cl_sub_eq2 in cl; apply cl in i2; rw i2 in i1; allsimpl; tcsp.
      * eapply isprog_vars_disjoint_implies_isprog;[exact ispl2|].
        apply disjoint_singleton_l.
        intro i; apply eqset_free_vars_disjoint in i.
        allrw <- @dom_sub_sub_filter.
        allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff.
        repndors; tcsp.
        allrw @in_sub_free_vars_iff; exrepnd.
        allrw @in_sub_keep_first; repnd.
        allrw @sub_find_sub_filter_eq; allrw memvar_singleton; boolvar; ginv.
        apply sub_find_some in i2.
        assert (cl_sub sub) as cl by eauto with slow.
        rw @cl_sub_eq2 in cl; apply cl in i2; rw i2 in i1; allsimpl; tcsp.

  - introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.
Qed.

Lemma cequiv_mk_fun {o} :
  forall lib (t1 t2 u1 u2 : @NTerm o),
    cequiv lib t1 u1
    -> cequiv lib t2 u2
    -> cequiv lib (mk_fun t1 t2) (mk_fun u1 u2).
Proof.
  introv c1 c2.
  allunfold @cequiv; repnd; dands;
  apply approx_mk_fun; auto.
Qed.

Lemma cequivc_mkc_fun {o} :
  forall lib (t1 t2 u1 u2 : @CTerm o),
    cequivc lib t1 u1
    -> cequivc lib t2 u2
    -> cequivc lib (mkc_fun t1 t2) (mkc_fun u1 u2).
Proof.
  introv c1 c2.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_mk_fun; auto.
Qed.

Lemma approx_open_mk_not {o} :
  forall lib (t u : @NTerm o),
    approx_open lib t u
    -> approx_open lib (mk_not t) (mk_not u).
Proof.
  introv apro.
  unfold mk_not.
  apply approx_open_mk_fun; eauto 3 with slow.
Qed.

Lemma approx_integer_implies_reduces_to {o} :
  forall lib a (t : @NTerm o),
    approx lib (mk_integer a) t
    -> reduces_to lib t (mk_integer a).
Proof.
  introv ap.
  destruct ap as [c].
  unfold close_comput in c; repnd.
  pose proof (c2 (Nint a) []) as h; fold_terms.
  autodimp h hyp.
  { apply computes_to_value_isvalue_refl; eauto with slow. }
  exrepnd.
  unfold lblift in h0; allsimpl; repnd; cpx; fold_terms.
  unfold computes_to_value in h1; repnd; auto.
Qed.

Lemma approx_iscan {o} :
  forall lib (a b x : @NTerm o),
    computes_to_can lib a x
    -> approx lib a b
    -> {z : NTerm & computes_to_can lib b z # approx lib x z}.
Proof.
  introv cc apr.
  allunfold @computes_to_can; repnd.
  eapply approx_comput_functionality_left in apr;[|exact cc0].
  destruct apr as [cl].
  apply iscan_implies in cc; repndors; exrepnd; subst.

  - unfold close_comput,close_compute_val in cl; repnd.
    pose proof (cl2 c bterms) as h.
    autodimp h hyp.
    { apply computes_to_value_isvalue_refl; eauto 3 with slow. }
    exrepnd.
    allunfold @computes_to_value; repnd.
    exists (oterm (Can c) tr_subterms); dands; tcsp.
    apply clearbot_relbt in h0.
    apply approx_canonical_form3; eauto with slow.
Qed.

Lemma approx_open_mk_less {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    approx_open lib a1 a2
    -> approx_open lib b1 b2
    -> approx_open lib c1 c2
    -> approx_open lib d1 d2
    -> approx_open lib (mk_less a1 b1 c1 d1) (mk_less a2 b2 c2 d2).
Proof.
  introv apro1 apro2 apro3 apro4.

  allrw <- @approx_open_simpler_equiv.
  allunfold @simpl_olift; repnd.
  allrw @nt_wf_eq.
  dands; try (apply wf_less; auto).
  introv prs ispl1 ispl2.

  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
  repeat (rw @cl_lsubst_lsubst_aux in ispl1; eauto 3 with slow).
  repeat (rw @cl_lsubst_lsubst_aux in ispl2; eauto 3 with slow).
  allsimpl; fold_terms; allrw @sub_filter_nil_r.

  allrw @isprogram_eq.
  allrw @isprog_less; repnd.

  pose proof (apro1 sub) as h1.
  repeat (rw @cl_lsubst_lsubst_aux in h1; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h1 hyp);[].

  pose proof (apro2 sub) as h2.
  repeat (rw @cl_lsubst_lsubst_aux in h2; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h2 hyp);[].

  pose proof (apro3 sub) as h3.
  repeat (rw @cl_lsubst_lsubst_aux in h3; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h3 hyp);[].

  pose proof (apro4 sub) as h4.
  repeat (rw @cl_lsubst_lsubst_aux in h4; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h4 hyp);[].

  constructor.
  unfold close_comput.
  allrw @isprogram_eq; allrw @isprog_less; dands; auto;[|].

  - introv comp.
    apply computes_to_value_mk_less in comp; exrepnd;
    try (apply lsubst_aux_preserves_wf_term2; eauto 3 with slow);[].

    eapply approx_comput_functionality_left in h1;[|exact comp0].
    eapply approx_comput_functionality_left in h2;[|exact comp2].
    allapply @approx_integer_implies_reduces_to.

    repndors; repnd;[|].

    + eapply approx_canonical_form in h3;[|exact comp1].
      destruct h3 as [tr_subterms apr]; repnd.
      exists tr_subterms; dands; try (apply clearbot_relbt2); auto.
      allunfold @computes_to_value; repnd; dands; tcsp.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
      eapply reduces_to_if_split2;
        [csunf; simpl; dcwf h; allsimpl; unfold compute_step_comp; simpl; auto|];[].
      boolvar;tcsp;try omega.

    + eapply approx_canonical_form in h4;[|exact comp1].
      destruct h4 as [tr_subterms apr]; repnd.
      exists tr_subterms; dands; try (apply clearbot_relbt2); auto.
      allunfold @computes_to_value; repnd; dands; tcsp.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
      eapply reduces_to_if_split2;
        [csunf; simpl; dcwf h; simpl; unfold compute_step_comp; simpl; auto|];[].
      boolvar;tcsp;try omega.

  - introv comp.
    apply computes_to_exception_mk_less in comp; repndors; exrepnd;
    try (apply lsubst_aux_preserves_wf_term2; eauto 3 with slow);[|idtac|].

    + eapply approx_comput_functionality_left in h1;[|exact comp0].
      eapply approx_comput_functionality_left in h2;[|exact comp2].
      allapply @approx_integer_implies_reduces_to.

      repndors; repnd;[|].

      * apply computes_to_exception_implies_approx in comp1; eauto 3 with slow;[]; repnd.
        eapply approx_trans in h3;[|exact comp4].
        apply approx_exception in h3; exrepnd.
        exists x c; dands; tcsp.
        allunfold @computes_to_exception.
        eapply reduces_to_trans;
          [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
        eapply reduces_to_if_split2;
          [csunf; simpl; dcwf h; simpl; unfold compute_step_comp; simpl; auto|];[].
        boolvar;tcsp;try omega.

      * apply computes_to_exception_implies_approx in comp1; eauto 3 with slow;[]; repnd.
        eapply approx_trans in h4;[|exact comp4].
        apply approx_exception in h4; exrepnd.
        exists x c; dands; tcsp.
        allunfold @computes_to_exception.
        eapply reduces_to_trans;
          [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
        eapply reduces_to_if_split2;
          [csunf; simpl; dcwf h; simpl; unfold compute_step_comp; simpl; auto|];[].
        boolvar;tcsp;try omega.

    + apply computes_to_exception_implies_approx in comp; eauto 3 with slow;[]; repnd.
      eapply approx_trans in h1;[|exact comp0].
      apply approx_exception in h1; exrepnd.
      exists x c; dands; tcsp;[].
      allunfold @computes_to_exception.
      unfold mk_less, nobnd.
      eapply reduces_to_trans;[eapply reduces_to_prinarg;exact h0|].
      apply reduces_to_if_step.
      csunf; simpl; auto.

    + apply computes_to_exception_implies_approx in comp0; eauto 3 with slow;[]; repnd.
      eapply approx_trans in h2;[|exact comp2].
      apply approx_exception in h2; exrepnd.

      exists x c; dands; tcsp;[].
      apply reduces_to_implies_approx1 in comp1; eauto 3 with slow;[].
      eapply approx_trans in h1;[|exact comp1].
      apply approx_integer_implies_reduces_to in h1.
      allunfold @computes_to_exception.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|exact h0] |]; eauto 3 with slow.
Qed.

Lemma approx_open_mk_less_than {o} :
  forall lib (t1 t2 u1 u2 : @NTerm o),
    approx_open lib t1 u1
    -> approx_open lib t2 u2
    -> approx_open lib (mk_less_than t1 t2) (mk_less_than u1 u2).
Proof.
  introv apro1 apro2.
  unfold mk_less_than.
  apply approx_open_mk_less; eauto with slow.
Qed.

Lemma approx_open_mk_le {o} :
  forall lib (t1 t2 u1 u2 : @NTerm o),
    approx_open lib t1 u1
    -> approx_open lib t2 u2
    -> approx_open lib (mk_le t1 t2) (mk_le u1 u2).
Proof.
  introv apro1 apro2.
  unfold mk_le.
  apply approx_open_mk_not.
  apply approx_open_mk_less_than; auto.
Qed.

Lemma approx_mk_natk {o} :
  forall lib (t u : @NTerm o),
    approx lib t u
    -> approx lib (mk_natk t) (mk_natk u).
Proof.
  introv apr.
  unfold mk_natk, mk_natk_aux.

  applydup @approx_isprog in apr.
  repnd.

  repeat (rw @newvar_prog; auto).

  constructor.
  unfold close_comput.
  dands; auto; allrw @isprogram_eq.

   - apply isprog_set; auto.
     apply isprog_vars_prod_implies; eauto 3 with slow.
     apply isprog_vars_less_than; dands; eauto 3 with slow.

   - apply isprog_set; auto.
     apply isprog_vars_prod_implies; eauto 3 with slow.
     apply isprog_vars_less_than; dands; eauto 3 with slow.

  - introv comp.
    apply computes_to_value_if_iscan in comp; simpl; auto.
    unfold mk_set in comp; ginv.
    exists [nobnd mk_int, bterm [nvarx] (mk_prod (mk_le mk_zero (mk_var nvarx)) (mk_less_than (mk_var nvarx) u))]; fold_terms; dands; auto.
    { apply computes_to_value_isvalue_refl.
      apply implies_isvalue_set; auto.
      apply isprog_vars_prod_implies; eauto 3 with slow.
      apply isprog_vars_less_than; dands; eauto 3 with slow. }
    apply clearbot_relbt2.
    unfold lblift; simpl; dands; auto.
    introv i.
    repeat (destruct n; tcsp; try omega); clear i; unfold selectbt; simpl.

    + apply blift_approx_open_nobnd2; eauto 3 with slow.

    + apply approx_open_implies_approx_open_bterm.
      apply approx_open_mk_prod.
      * apply approx_open_mk_le; eauto 3 with slow.
      * apply approx_open_mk_less_than;[apply approx_open_refl; eauto 4 with slow|].
        apply approx_implies_approx_open; auto.

  - introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.
Qed.

Lemma cequiv_mk_natk {o} :
  forall lib (t u : @NTerm o),
    cequiv lib t u
    -> cequiv lib (mk_natk t) (mk_natk u).
Proof.
  introv ceq.
  allunfold @cequiv; repnd.
  dands; apply approx_mk_natk; auto.
Qed.

Lemma cequivc_mkc_natk {o} :
  forall lib (t u : @CTerm o),
    cequivc lib t u
    -> cequivc lib (mkc_natk t) (mkc_natk u).
Proof.
  introv ceq.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_mk_natk; auto.
Qed.

Lemma approx_mk_less {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib c1 c2
    -> approx lib d1 d2
    -> approx lib (mk_less a1 b1 c1 d1) (mk_less a2 b2 c2 d2).
Proof.
  introv apra aprb aprc aprd.

  applydup @approx_isprog in apra.
  applydup @approx_isprog in aprb.
  applydup @approx_isprog in aprc.
  applydup @approx_isprog in aprd.
  repnd.

  apply approx_open_approx; allrw @isprogram_eq; try (apply isprog_less_implies); auto.
  apply approx_open_mk_less; apply approx_implies_approx_open; auto.
Qed.

Lemma cequiv_mk_less {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib c1 c2
    -> cequiv lib d1 d2
    -> cequiv lib (mk_less a1 b1 c1 d1) (mk_less a2 b2 c2 d2).
Proof.
  introv ceqa ceqb ceqc ceqd.
  allunfold @cequiv; repnd; dands; apply approx_mk_less; auto.
Qed.

Lemma cequivc_mkc_less {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib c1 c2
    -> cequivc lib d1 d2
    -> cequivc lib (mkc_less a1 b1 c1 d1) (mkc_less a2 b2 c2 d2).
Proof.
  introv ceqa ceqb ceqc ceqd.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_mk_less; auto.
Qed.

Lemma cequivc_mkc_less_int {o} :
  forall lib i1 i2 (t1 t2 : @CTerm o),
    cequivc
      lib
      (mkc_less (mkc_integer i1) (mkc_integer i2) t1 t2)
      (if Z_lt_le_dec i1 i2 then t1 else t2).
Proof.
  introv.
  destruct_cterms.
  unfold cequivc; simpl.
  boolvar; simpl; apply reduces_to_implies_cequiv;
  allrw @isprogram_eq; try (apply isprog_less_implies); eauto 3 with slow;
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl;
  unfold compute_step_comp; simpl;
  boolvar; tcsp; try omega.
Qed.

Lemma computes_to_valc_and_excc_false {o} :
  forall lib (en a v e : @CTerm o),
    computes_to_valc lib a v
    -> computes_to_excc lib en a e
    -> False.
Proof.
  introv comp1 comp2.
  destruct_cterms.
  allunfold @computes_to_valc.
  allunfold @computes_to_excc.
  allsimpl.
  eapply computes_to_value_and_exception_false in comp1; eauto.
Qed.

Lemma iscvalue_mkc_utoken {o} :
  forall a, @iscvalue o (mkc_utoken a).
Proof.
  introv; unfold iscvalue; simpl; eauto with slow.
Qed.
Hint Resolve iscvalue_mkc_utoken : slow.

Lemma mkcv_cequiv_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_cequiv [v] a b)
    = mkc_cequiv (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma mkcv_utoken_substc {o} :
  forall v a (t : @CTerm o),
    substc t v (mkcv_utoken [v] a)
    = mkc_utoken a.
Proof.
  introv.
  unfold mkcv_utoken.
  allrw @csubst_mk_cv; auto.
Qed.

Lemma approx_mk_utoken {o} :
  forall lib (n1 n2 : @get_patom_set o),
    approx lib (mk_utoken n1) (mk_utoken n2) <=> n1 = n2.
Proof.
  introv; split; introv k; subst; eauto 3 with slow.
  eapply approx_canonical_form in k;
    [|apply computes_to_value_isvalue_refl; fold_terms; eauto 3 with slow].
  exrepnd.
  unfold lblift in k0; allsimpl; repnd; cpx; fold_terms.
  apply computes_to_value_if_iscan in k1; ginv; eauto 3 with slow.
Qed.

Lemma cequiv_mk_utoken {o} :
  forall lib (n1 n2 : @get_patom_set o),
    cequiv lib (mk_utoken n1) (mk_utoken n2) <=> n1 = n2.
Proof.
  introv; split; intro k; subst; eauto 3 with slow.
  allunfold @cequiv; repnd.
  allrw @approx_mk_utoken; auto.
Qed.

Lemma cequivc_mkc_utoken {o} :
  forall lib (n1 n2 : @get_patom_set o),
    cequivc lib (mkc_utoken n1) (mkc_utoken n2) <=> n1 = n2.
Proof.
  introv.
  unfold cequivc; simpl.
  apply cequiv_mk_utoken.
Qed.

Lemma cequivc_mkc_less_nat {o} :
  forall lib (i1 i2 : nat) (t1 t2 : @CTerm o),
    cequivc lib
            (mkc_less (mkc_nat i1) (mkc_nat i2) t1 t2)
            (if nat_compare_dec i2 i1 then t1 else t2).
Proof.
  introv.
  allrw @mkc_nat_eq.
  eapply cequivc_trans;[apply cequivc_mkc_less_int|].
  boolvar; tcsp; try omega.
Qed.

Lemma computes_to_exception_implies_cequiv {o} :
  forall lib (a t x : @NTerm o),
    isprogram t
    -> computes_to_exception lib a t x
    -> cequiv lib t (mk_exception a x).
Proof.
  introv isp comp.
  apply reduces_to_implies_cequiv; auto.
Qed.

Lemma computes_to_excc_implies_cequivc {o} :
  forall lib (a t x : @CTerm o),
    computes_to_excc lib a t x -> cequivc lib t (mkc_exception a x).
Proof.
  introv comp; destruct_cterms; allunfold @computes_to_excc; allunfold @cequivc; allsimpl.
  apply computes_to_exception_implies_cequiv; eauto with slow.
Qed.

Lemma cequiv_mk_exception {o} :
  forall lib (a1 a2 b1 b2 : @NTerm o),
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib (mk_exception a1 b1) (mk_exception a2 b2).
Proof.
  introv ceqa ceqb.
  allunfold @cequiv; repnd; dands; apply approx_canonical_form_exc; auto.
Qed.

Lemma cequivc_mkc_exception {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib (mkc_exception a1 b1) (mkc_exception a2 b2).
Proof.
  introv ceqa ceqb.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_mk_exception; auto.
Qed.

Lemma cequiv_exception_implies {o} :
  forall lib (en a b : @NTerm o),
    cequiv lib (mk_exception en a) b
    -> {x, c : NTerm $ (b =e>( x, lib)c) # cequiv lib en x # cequiv lib a c}.
Proof.
  introv ceq.
  allunfold @cequiv; repnd.
  applydup @approx_exception in ceq0; exrepnd.
  applydup @approx_relates_only_progs in ceq; repnd.
  applydup @computes_to_exception_implies_approx in ceq2; repnd; auto.
  eapply approx_trans in ceq;[|exact ceq7].
  apply approx_exception in ceq; exrepnd.
  apply computes_to_exception_exception in ceq8; repnd; subst.
  exists x c; dands; auto.
Qed.

Lemma cequivc_exception_implies {o} :
  forall lib (en a b : @CTerm o),
    cequivc lib (mkc_exception en a) b
    -> {x, c : CTerm $ computes_to_excc lib x b c # cequivc lib en x # cequivc lib a c}.
Proof.
  introv ceq.
  destruct_cterms; allunfold @cequivc; allsimpl.
  applydup @cequiv_exception_implies in ceq; exrepnd.
  applydup @cequiv_isprog in ceq2 as isp1.
  applydup @cequiv_isprog in ceq0 as isp2.
  repnd.
  exists (mk_ct x2 isp1) (mk_ct c isp2); unfold computes_to_excc; simpl; dands; auto.
Qed.

Lemma cequivc_utoken_implies {o} :
  forall lib a (t : @CTerm o),
    cequivc lib (mkc_utoken a) t -> computes_to_valc lib t (mkc_utoken a).
Proof.
  introv ceq.
  eapply cequivc_utoken in ceq; eauto.
  apply computes_to_valc_refl; eauto with slow.
Qed.

Lemma fresh_reduces_to_implies0 {o} :
  forall lib v (t : @NTerm o) x a,
    !LIn a (get_utokens t)
    -> reduces_to lib (mk_fresh v t) x
    -> {u : NTerm
        & reduces_to lib (subst t v (mk_utoken a)) u
        # alpha_eq x (mk_fresh v (subst_utokens u [(a,mk_var v)]))}.
Proof.
  introv nia comp.
  unfold reduces_to in comp; exrepnd.
  revert v t x a nia comp0.
  induction k; introv nia comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists (subst t v (mk_utoken a)); dands; eauto 2 with slow.
    apply implies_alpha_eq_mk_fresh.
    apply alpha_eq_sym; apply simple_alphaeq_subst_utokens_subst; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply compute_step_ncan_bterm_cons_success in comp1; repnd; GC.
    repndors; exrepnd; subst; allsimpl; GC.

    + apply reduces_in_atmost_k_steps_mk_fresh_id in comp0; subst.
      unfsubst; simpl; boolvar; tcsp.
      exists (mk_utoken a); dands; eauto 3 with slow.
      unfold subst_utokens; simpl.
      unfold subst_utok; simpl; boolvar; tcsp.

    + pose proof (isvalue_like_pushdown_fresh v t) as isvp.
      autodimp isvp hyp.
      pose proof (isvalue_like_subst t v (mk_utoken a)) as isvs.
      autodimp isvs hyp.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; auto; subst; GC.
      exists (subst t v (mk_utoken a)).
      dands; eauto 3 with slow.
      eapply alpha_eq_trans;
        [|apply implies_alpha_eq_mk_fresh; apply alpha_eq_sym;
          apply simple_alphaeq_subst_utokens_subst;auto].
Abort.

Lemma implies_alpha_eq_pushdown_fresh_same {o} :
  forall (v : NVar) (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> alpha_eq (pushdown_fresh v t1) (pushdown_fresh v t2).
Proof.
  introv aeq.
  apply implies_alpha_eq_pushdown_fresh.
  apply alpha_eq_bterm_congr; auto.
Qed.

Lemma not_in_get_utokens_lib_implies_not_in_get_utokens {o} :
  forall a lib (t : @NTerm o),
    !LIn a (get_utokens_lib lib t)
    -> !LIn a (get_utokens t).
Proof.
  introv ni i.
  eapply get_utokens_subset_get_utokens_lib in i; apply ni in i; auto.
Qed.
Hint Resolve not_in_get_utokens_lib_implies_not_in_get_utokens : slow.

Lemma fresh_reduces_to_implies {o} :
  forall lib v (t : @NTerm o) x a,
    nt_wf t
    -> !LIn a (get_utokens_lib lib t)
    -> reduces_to lib (mk_fresh v t) x
    -> isvalue_like x
    -> {u : NTerm
        & reduces_to lib (subst t v (mk_utoken a)) u
        # alpha_eq x (pushdown_fresh v (subst_utokens u [(a,mk_var v)]))}.
Proof.
  introv wf nia comp.
  unfold reduces_to in comp; exrepnd.
  revert v t x a wf nia comp0.
  induction k; introv wf nia comp isv.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists (subst t v (mk_utoken a)); dands; eauto 2 with slow.
    unfold isvalue_like in isv; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply compute_step_ncan_bterm_cons_success in comp1; repnd; GC.
    repndors; exrepnd; subst; allsimpl; GC.

    + apply reduces_in_atmost_k_steps_mk_fresh_id in comp0; subst.
      unfsubst; simpl; boolvar; tcsp.
      exists (mk_utoken a); dands; eauto 3 with slow.
      unfold subst_utokens; simpl.
      unfold subst_utok; simpl; boolvar; tcsp.

    + pose proof (isvalue_like_pushdown_fresh v t) as isvp; autodimp isvp hyp.
      pose proof (isvalue_like_subst t v (mk_utoken a)) as isvs; autodimp isvs hyp.
      apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; auto; subst; GC.
      exists (subst t v (mk_utoken a)).
      dands; eauto 3 with slow.
      apply implies_alpha_eq_pushdown_fresh_same.
      apply alpha_eq_sym.
      apply simple_alphaeq_subst_utokens_subst;auto; eauto 3 with slow.

    + repnd; subst.
      remember (get_fresh_atom lib t) as a'.
      pose proof (get_fresh_atom_prop_and_lib lib t) as gfap; rw <- Heqa' in gfap.

      pose proof (compute_step_subst_utoken t x0 lib [(v,mk_utoken a')]) as h.
      allrw @fold_subst.
      allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allrw app_nil_r.
      allsimpl; allrw disjoint_singleton_l.
      repeat (autodimp h hyp); eauto 3 with slow.
      exrepnd; allrw disjoint_singleton_l.

      pose proof (h0 [(v,mk_utoken a)]) as comp'; allsimpl.
      allrw @fold_subst.
      allrw @get_utokens_sub_cons; allrw @get_utokens_sub_nil; allrw app_nil_r.
      allsimpl; allrw disjoint_singleton_l.
      repeat (autodimp comp' hyp).
      exrepnd.

      applydup @preserve_nt_wf_compute_step in comp3 as wfx;[|eauto 4 with slow];[].
      applydup @preserve_nt_wf_compute_step in comp'1 as wfs;[|eauto 4 with slow];[].
      applydup @alphaeq_preserves_wf_r_eauto in comp'0 as wfw; auto;[].
      apply lsubst_nt_wf in wfw.

      eapply (reduces_in_atmost_k_steps_alpha _ _ (mk_fresh v w)) in comp0;
        [|apply nt_wf_fresh;
           apply nt_wf_eq;
           apply wf_subst_utokens;
           eauto 3 with slow
         |apply implies_alpha_eq_mk_fresh;
           eapply alpha_eq_trans;
           [apply alpha_eq_subst_utokens_same; exact h1
           |apply simple_alphaeq_subst_utokens_subst;auto] ];
        eauto 3 with slow;[].
      exrepnd.

      assert (!LIn a (get_utokens_lib lib w)) as niaw.
      { introv j; apply h4 in j; sp. }

      assert (isvalue_like t2') as isvt2'.
      { eapply alpha_eq_preserves_isvalue_like;[exact comp2|]; auto. }

      pose proof (IHk v w t2' a) as q; clear IHk.
      repeat (autodimp q hyp).
      exrepnd.

      pose proof (reduces_to_alpha lib (subst w v (mk_utoken a)) s u) as r.
      repeat (autodimp r hyp); eauto 2 with slow.
      exrepnd.

      exists t2'0.
      dands.
      { eapply reduces_to_if_split2;[exact comp'1|]; auto. }

      eapply alpha_eq_trans;[exact comp2|].
      eapply alpha_eq_trans;[exact q0|].
      apply implies_alpha_eq_pushdown_fresh_same.
      apply alpha_eq_subst_utokens_same; auto.
Qed.

Lemma isvalue_like_pushdown_fresh_implies {o} :
  forall v (t : @NTerm o),
    isvalue_like (pushdown_fresh v t)
    -> isvalue_like t.
Proof.
  introv isv.
  destruct t as [x|op bs]; allsimpl; auto.
Qed.

Lemma combine_implies_approx_bts {o} :
  forall lib (bts1 bts2 : list (@BTerm o)),
    length bts1 = length bts2
    -> (forall b1 b2, LIn (b1,b2) (combine bts1 bts2) -> approx_open_bterm lib b1 b2)
    -> approx_bts lib bts1 bts2.
Proof.
  introv len imp.
  unfold approx_bts, lblift; dands; auto.
  introv i.
  pose proof (imp (bts1 {[n]}) (bts2 {[n]})) as h.
  autodimp h hyp.
  pose proof (select2bts bts1 bts2 n) as h.
  repeat (autodimp h hyp); exrepnd; subst; auto.
Qed.

Lemma covered_mk_utoken {o} :
  forall (a : get_patom_set o) vs,
    covered (mk_utoken a) vs.
Proof.
  introv.
  unfold covered; simpl; auto.
Qed.
Hint Resolve covered_mk_utoken : slow.

Lemma implies_approx_val_like {o} :
  forall lib op (bterms1 bterms2 : list (@BTerm o)),
    iscan_like_op op
    -> isprogram (oterm op bterms1)
    -> isprogram (oterm op bterms2)
    -> approx_bts lib bterms1 bterms2
    -> approx lib (oterm op bterms1) (oterm op bterms2).
Proof.
  introv isc isp1 isp2 aprs.
  unfold iscan_like_op in isc; repndors.
  - unfold iscan_op in isc; exrepnd; subst.
    apply approx_canonical_form3; auto.
  - unfold isexc_op in isc; subst.
    allapply @isprogram_exception_implies; exrepnd; subst.
    unfold approx_bts, lblift in aprs; allsimpl; repnd; GC.
    fold (approx_open_bterm lib) in aprs.
    pose proof (aprs 0) as h1; autodimp h1 hyp.
    pose proof (aprs 1) as h2; autodimp h2 hyp.
    clear aprs.
    allunfold @selectbt; allsimpl.
    apply blift_approx_open_nobnd in h1; auto.
    apply blift_approx_open_nobnd in h2; auto.
    fold_terms.
    apply approx_canonical_form_exc; auto.
Qed.

Lemma isvalue_like_subst_utokens_implies {o} :
  forall (t : @NTerm o) sub,
    isvalue_like (subst_utokens t sub)
    -> isvalue_like t.
Proof.
  introv isv.
  pose proof (unfold_subst_utokens sub t) as h; exrepnd.
  rw h0 in isv.
  destruct t' as [v|op bs]; auto.
  - unfold subst_utokens in isv; allsimpl; auto.
    inversion h1; subst; auto.
  - rw @subst_utokens_aux_oterm in isv.
    apply alpha_eq_sym in h1; apply alpha_eq_oterm_implies_combine2 in h1; exrepnd; subst.
    remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.
    + apply get_utok_some in Heqguo; subst; allsimpl.
      unfold isvalue_like; simpl; tcsp.
    + apply isvalue_like_implies1 in isv; repndors; exrepnd; ginv;
      apply implies_isvalue_like1; auto.
Qed.

Lemma approx_fresh_subst1 {o} :
  forall lib (t : @NTerm o) v a op,
    !LIn a (get_utokens_lib lib t)
    -> isprog_vars [v] t
    -> iscan_op op
    -> reduces_to lib (subst t v (mk_utoken a)) (spoterm op)
    -> approx lib (mk_fresh v t) (subst t v (mk_utoken a)).
Proof.
  introv nia isp iscl rt.

  apply approx_assume_hasvalue.
  { apply isprogram_fresh; auto. }
  { apply isprogram_eq; apply subst_preserves_isprog; eauto 3 with slow. }
  introv hv.
  unfold hasvalue_like in hv; exrepnd.

  eapply approx_trans;
    [apply reduces_to_implies_approx2;[apply isprogram_fresh; auto|exact hv1]|].

  pose proof (fresh_reduces_to_implies lib v t v0 a) as r.
  repeat (autodimp r hyp); eauto 3 with slow.
  exrepnd.

  eapply alpha_eq_preserves_isvalue_like in hv0;[|exact r0].
  dup hv0 as hv.
  apply isvalue_like_pushdown_fresh_implies in hv0.
  apply isvalue_like_subst_utokens_implies in hv0.

  eapply reduces_to_eq_val_like in rt;
    [|exact r1|idtac|apply implies_isvalue_like1;left]; auto.
  subst.

  eapply approx_alpha_rw_l_aux;[apply alpha_eq_sym;exact r0|].
  eapply approx_trans;
    [|apply reduces_to_implies_approx1;
       [apply isprogram_eq; apply subst_preserves_isprog; eauto 3 with slow
       |exact r1] ].

  pose proof (unfold_subst_utokens [(a,mk_var v)] (spoterm op)) as h; exrepnd.
  apply alpha_eq_oterm_implies_combine2 in h1; exrepnd; subst.
  allrw @subst_utokens_aux_oterm.
  unfold alpha_eq_bterms in h3; repnd; allsimpl; cpx; allsimpl.
  allrw h0.
  clear h0 h2 h3.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.
  { apply get_utok_some in Heqguo; subst; allsimpl.
    allunfold @subst_utok; allsimpl; boolvar; subst; allsimpl; tcsp; fold_terms.
    - unfold isvalue_like in hv; allsimpl; tcsp.
    - unfold spoterm; fold_terms; eauto 3 with slow. }
  unfold iscan_op in iscl; exrepnd; subst.
  simpl; unfold spoterm; eauto 3 with slow.
  apply approx_refl.
  eapply reduces_to_preserves_program;[exact r1|].
  apply isprogram_eq; apply subst_preserves_isprog; eauto 3 with slow.
Qed.

Lemma approx_subst_fresh1 {o} :
  forall lib (t : @NTerm o) v a op,
    !LIn a (get_utokens_lib lib t)
    -> isprog_vars [v] t
    -> iscan_op op
    -> !LIn a (get_utokens (spoterm op))
    -> reduces_to lib (subst t v (mk_utoken a)) (spoterm op)
    -> approx lib (subst t v (mk_utoken a)) (mk_fresh v t).
Proof.
  introv nia isp iscl nia' rt.
  pose proof (reduces_to_fresh2 lib t (spoterm op) v a) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
  exrepnd.
  eapply approx_trans;
    [|apply reduces_to_implies_approx1;
       [apply isprogram_fresh; auto|exact h1]
    ].
  eapply approx_trans;
    [apply reduces_to_implies_approx2;
      [|exact rt];
      apply isprogram_eq; apply subst_preserves_isprog; eauto 3 with slow
    |].
  eapply approx_alpha_rw_r_aux;
    [apply implies_alpha_eq_mk_fresh;apply alpha_eq_sym;exact h0|].

  pose proof (unfold_subst_utokens [(a,mk_var v)] (spoterm op)) as q; exrepnd.
  apply alpha_eq_oterm_implies_combine2 in q1; exrepnd; subst.
  allrw @subst_utokens_aux_oterm.
  unfold alpha_eq_bterms in q3; repnd; allsimpl; cpx; allsimpl.
  allrw q0.
  clear q0 q2 q3.
  allrw app_nil_r.
  remember (get_utok op) as guo; symmetry in Heqguo; destruct guo.
  { apply get_utok_some in Heqguo; subst; allsimpl.
    allrw not_over_or; repnd; GC.
    allunfold @subst_utok; allsimpl; boolvar; subst; allsimpl; tcsp; fold_terms.
    allunfold @spoterm; fold_terms.
    apply reduces_to_implies_approx1;
      [apply isprogram_fresh; eauto 3 with slow|].
    apply reduces_to_if_step.
    csunf; simpl; auto. }
  unfold iscan_op in iscl; exrepnd; subst.
  simpl; unfold spoterm; eauto 3 with slow.
  apply reduces_to_implies_approx1;
    [|apply reduces_to_if_step;csunf;simpl;auto].
  eapply reduces_to_preserves_program in h1; allrw @isprogram_fresh; auto.
  eapply alphaeq_preserves_isprog_vars; eauto.
Qed.

Lemma cequiv_fresh_subst1 {o} :
  forall lib op (t : @NTerm o) v a,
    !LIn a (get_utokens_lib lib t)
    -> isprog_vars [v] t
    -> iscan_op op
    -> !LIn a (get_utokens (spoterm op))
    -> reduces_to lib (subst t v (mk_utoken a)) (spoterm op)
    -> cequiv lib (mk_fresh v t) (subst t v (mk_utoken a)).
Proof.
  introv nia isp isc nia' rt.
  split;
    try (eapply approx_fresh_subst1; eauto);
    try (eapply approx_subst_fresh1; eauto).
Qed.

Lemma reduces_in_atmost_k_stepsc_0 {o} :
  forall lib (t u : @CTerm o),
    reduces_in_atmost_k_stepsc lib t u 0 <=> t = u.
Proof.
  introv; destruct_cterms.
  unfold reduces_in_atmost_k_stepsc; simpl.
  rw @reduces_in_atmost_k_steps_0.
  split; intro h; subst; eauto with pi.
  inversion h; auto.
Qed.

Lemma dec_reduces_in_atmost_k_steps {o} :
  forall lib k (t v : @NTerm o),
    (forall x, decidable (x = v))
    -> decidable (reduces_in_atmost_k_steps lib t v k).
Proof.
  introv d.
  remember (compute_at_most_k_steps lib k t) as c; symmetry in Heqc.
  destruct c.
  - destruct (d n) as [h|h]; subst.
    + left; auto.
    + right; intro r; rw r in Heqc; ginv; tcsp.
  - right; intro r; rw r in Heqc; ginv.
Qed.

Lemma decidable_mk_nat {o} :
  forall n (t : @NTerm o), decidable (t = mk_nat n).
Proof.
  introv.
  destruct t as [v|op bs]; try (complete (right; intro e; complete ginv)).
  destruct op; try (complete (right; intro e; complete ginv)).
  destruct c; try (complete (right; intro e; complete ginv)).
  destruct bs; try (complete (right; intro e; complete ginv)).
  destruct (Z_le_dec 0 z) as [h|h].
  - pose proof (Wf_Z.Z_of_nat_complete_inf z h) as q; exrepnd; subst; fold_terms.
    destruct (deq_nat n n0); subst; tcsp.
    right; intro q.
    inversion q as [e]; clear q.
    apply Znat.Nat2Z.inj in e; tcsp.
  - right; introv e.
    inversion e; subst; try omega.
Qed.
Hint Resolve decidable_mk_nat : slow.

Lemma decidable_ex_mk_nat {o} :
  forall (t : @NTerm o), decidable ({n : nat & t = mk_nat n}).
Proof.
  introv.
  destruct t as [v|op bs]; try (complete (right; intro e; exrepnd; complete ginv)).
  destruct op; try (complete (right; intro e; exrepnd; complete ginv)).
  destruct c; try (complete (right; intro e; exrepnd; complete ginv)).
  destruct bs; try (complete (right; intro e; exrepnd; complete ginv)).
  destruct (Z_le_dec 0 z) as [h|h].
  - pose proof (Wf_Z.Z_of_nat_complete_inf z h) as q; exrepnd; subst; fold_terms.
    left; exists n; auto.
  - right; introv e; exrepnd.
    inversion e0; subst; try omega.
Qed.
Hint Resolve decidable_ex_mk_nat : slow.

Definition mkcv_bot {o} (vs : list NVar) : @CVTerm o vs := mk_cv vs mkc_bot.

Lemma mkcv_bot_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_bot [v]) = mkc_bot.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
  simpl.
  allrw memvar_singleton.
  repeat (boolvar; allsimpl; tcsp).
Qed.

Definition mkcv_vbot {o} (vs : list NVar) x : @CVTerm o vs := mk_cv vs (mkc_vbot x).

Lemma mkcv_vbot_substc {o} :
  forall v x (t : @CTerm o),
    substc t v (mkcv_vbot [v] x) = mkc_vbot x.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
  simpl.
  allrw memvar_singleton.
  repeat (boolvar; allsimpl; tcsp).
Qed.

Lemma mkcv_try_substc {o} :
  forall v (a b : @CVTerm o [v]) x (c : CVTerm [x,v]) (t : CTerm),
    x <> v
    -> substc t v (mkcv_try [v] a b x c)
       = mkc_try (substc t v a) (substc t v b) x (substc2 x t v c).
Proof.
  introv d.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
  simpl.
  allrw memvar_singleton; boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma mkcv_cbv_substc {o} :
  forall v (a : @CVTerm o [v]) x (b : CVTerm [x,v]) (t : CTerm),
    x <> v
    -> substc t v (mkcv_cbv [v] a x b)
       = mkc_cbv (substc t v a) x (substc2 x t v b).
Proof.
  introv d.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
  simpl.
  allrw memvar_singleton; boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma mkcv_cbv_substc_same {o} :
  forall v (a : @CVTerm o [v]) (b : CVTerm [v,v]) (t : CTerm),
    substc t v (mkcv_cbv [v] a v b)
    = mkc_cbv (substc t v a) v (mkcv_cont1 v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
  simpl.
  allrw memvar_singleton; boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma mkcv_apply_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_apply [v] a b)
    = mkc_apply (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Definition substc2_mk_cv {o} :
  forall y (u : @CTerm o) x (t : CTerm),
    substc2 y u x (mk_cv [y,x] t) = mk_cv [y] t.
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
  apply subst_trivial; auto.
Qed.

Definition approx_mk_try {o} :
  forall lib (a1 a2 b1 b2 : @NTerm o) v c1 c2,
    isprog_vars [v] c1
    -> isprog_vars [v] c2
    -> approx lib a1 a2
    -> approx lib b1 b2
    -> approx_open lib c1 c2
    -> approx lib (mk_try a1 b1 v c1) (mk_try a2 b2 v c2).
Proof.
  introv ispc1 ispc2 apr1 apr2 apr3.
  applydup @approx_isprog in apr1.
  applydup @approx_isprog in apr2.
  repnd.
  unfold mk_try.
  repeat (prove_approx; tcsp; eauto 2 with slow).
  fold (approx_open_bterm lib).
  apply approx_open_implies_approx_open_bterm; auto.
Qed.

Definition cequiv_mk_try {o} :
  forall lib (a1 a2 b1 b2 : @NTerm o) v c1 c2,
    isprog_vars [v] c1
    -> isprog_vars [v] c2
    -> cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv_open lib c1 c2
    -> cequiv lib (mk_try a1 b1 v c1) (mk_try a2 b2 v c2).
Proof.
  introv isp1 isp2 ceq1 ceq2 ceq3.
  allunfold @cequiv; repnd.
  allapply @olift_cequiv_approx; repnd.
  dands; apply approx_mk_try; auto.
Qed.

Definition simpl_cequivc_mkc_try {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o) v (c : CVTerm [v]),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib (mkc_try a1 b1 v c) (mkc_try a2 b2 v c).
Proof.
  introv ceq1 ceq2.
  destruct_cterms; allunfold @cequivc; allsimpl.
  apply cequiv_mk_try; auto.
  apply cequiv_open_refl; eauto 3 with slow.
Qed.

Definition approx_mk_cbv {o} :
  forall lib (a1 a2 : @NTerm o) v b1 b2,
    isprog_vars [v] b1
    -> isprog_vars [v] b2
    -> approx lib a1 a2
    -> approx_open lib b1 b2
    -> approx lib (mk_cbv a1 v b1) (mk_cbv a2 v b2).
Proof.
  introv ispb1 ispb2 apr1 apr2.
  applydup @approx_isprog in apr1.
  repnd.
  unfold mk_cbv.
  repeat (prove_approx; tcsp; eauto 2 with slow).
  fold (approx_open_bterm lib).
  apply approx_open_implies_approx_open_bterm; auto.
Qed.

Definition cequiv_mk_cbv {o} :
  forall lib (a1 a2 : @NTerm o) v b1 b2,
    isprog_vars [v] b1
    -> isprog_vars [v] b2
    -> cequiv lib a1 a2
    -> cequiv_open lib b1 b2
    -> cequiv lib (mk_cbv a1 v b1) (mk_cbv a2 v b2).
Proof.
  introv isp1 isp2 ceq1 ceq2.
  allunfold @cequiv; repnd.
  allapply @olift_cequiv_approx; repnd.
  dands; apply approx_mk_cbv; auto.
Qed.

Definition simpl_cequivc_mkc_cbv {o} :
  forall lib (a1 a2 : @CTerm o) v (b : CVTerm [v]),
    cequivc lib a1 a2
    -> cequivc lib (mkc_cbv a1 v b) (mkc_cbv a2 v b).
Proof.
  introv ceq.
  destruct_cterms; allunfold @cequivc; allsimpl.
  apply cequiv_mk_cbv; auto.
  apply cequiv_open_refl; eauto 3 with slow.
Qed.

Definition computes_to_pkc {o} lib (t : @CTerm o) pk :=
  computes_to_pk lib (get_cterm t) pk.

Lemma computes_to_valc_mkc_try {o} :
  forall lib (a b : @CTerm o) e c v pk,
    computes_to_valc lib a v
    -> computes_to_pkc lib b pk
    -> computes_to_valc lib (mkc_try a b e c) v.
Proof.
  introv comp1 comp2.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_pkc; allsimpl.
  eapply implies_computes_to_value_trycatch; eauto.
Qed.

Lemma reduces_toc_mkc_try_exc {o} :
  forall lib a (t : @CTerm o) e c,
    reduces_toc lib (mkc_try (mkc_exception (mkc_utoken a) t)
                             (mkc_utoken a)
                             e
                             c)
                (substc t e c).
Proof.
  introv.
  destruct_cterms.
  unfold reduces_toc; simpl.
  eapply reduces_to_if_split2;
    [csunf; simpl; auto
    |].
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf h; simpl.
  unfold compute_step_comp; simpl.
  boolvar; tcsp.
Qed.

Lemma reduces_toc_mkc_cbv_val {o} :
  forall lib (a : @CTerm o) v b,
    iscvalue a
    -> reduces_toc lib (mkc_cbv a v b) (substc a v b).
Proof.
  introv isc.
  destruct_cterms.
  unfold iscvalue in isc; allsimpl.
  unfold reduces_toc; simpl.
  apply isvalue_implies in isc; repnd.
  apply iscan_implies in isc0; repndors; exrepnd; subst;
  apply reduces_to_if_step;
  csunf; simpl; auto.
Qed.

Lemma computes_to_pkc_refl {o} :
  forall lib (t : @CTerm o) pk,
    t = pk2termc pk
    -> computes_to_pkc lib t pk.
Proof.
  introv e.
  subst.
  destruct_cterms.
  unfold computes_to_pkc, computes_to_pk; allsimpl.
  apply computes_to_value_isvalue_refl; eauto 3 with slow.
Qed.

(*
Inductive bc {o} : @NTerm o -> Type :=
| bc_var : forall v, bc (mk_var v)
| bc_oterm :
    forall op bs,
      disjoint (free_vars (oterm op bs)) (bound_vars (oterm op bs))
      -> (forall b, LIn b bs -> bc_b b)
      -> bc (oterm op bs)
with bc_b {o} : @BTerm o -> Type :=
     | bc_bterm : forall l t, bc t -> bc_b (bterm l t).
Hint Constructors bc bc_b.

Lemma ex_bc {o} :
  forall (t : @NTerm o) vs,
    {u : NTerm & alpha_eq t u # bc u # disjoint (bound_vars u) vs}.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv.

  - Case "vterm".
    exists (@vterm o v); simpl; dands; auto.

  - Case "sterm".
    allsimpl.
    exists (sterm (fun n => projT1 (ind n vs))); simpl; dands; eauto 3 with slow.

  - Case "oterm".

    assert {bs' : list BTerm
            & alpha_eq_bterms bs bs'
            # (forall b, LIn b bs' -> bc_b b)
            # disjoint (bound_vars_bterms bs') vs
            # disjoint (bound_vars_bterms bs') (free_vars_bterms bs')} as hbs.
    { revert vs; clear op.
      induction bs; introv; allsimpl.
      - exists ([] : list (@BTerm o)); simpl; dands; tcsp; eauto 3 with slow.
      - autodimp IHbs hyp.
        { introv i; introv; eapply ind; eauto. }
        destruct a as [l t].

        pose proof (IHbs (l ++ free_vars t ++ vs)) as q; clear IHbs.
        exrepnd; allsimpl.
        allrw disjoint_app_r; repnd.

        pose proof (fresh_vars (length l)
                               (l ++ vs
                                  ++ all_vars t
                                  ++ free_vars_bterms bs')) as fvs.
        exrepnd.
        allrw disjoint_app_r; repnd.

        pose proof (ind t (lsubst t (var_ren l lvn)) l) as k; clear ind.
        repeat (autodimp k hyp).
        { rw @lsubst_allvars_preserves_size2; auto. }
        pose proof (k (vs ++ free_vars_bterms bs' ++ free_vars t)) as k'; clear k; exrepnd.
        allrw disjoint_app_r; repnd.

        exists (bterm lvn u :: bs'); simpl.
        allrw disjoint_app_l.
        allrw disjoint_app_r.
        dands; eauto 3 with slow.

        + apply alpha_eq_bterms_cons; dands; auto.
          eapply alpha_eq_bterm_trans;[|apply alpha_eq_bterm_congr;exact k'1].
          apply alpha_bterm_change; auto.
          allrw disjoint_app_l; dands; eauto 3 with slow.

        + introv i; repndors; subst; auto.

        + introv i j.
          rw in_remove_nvars in j; repnd.
          apply alphaeq_preserves_free_vars in k'1; rw <- k'1 in j0.
          apply eqset_free_vars_disjoint in j0.
          rw @dom_sub_var_ren in j0; auto.
          rw in_app_iff in j0; rw in_remove_nvars in j0.
          repndors; repnd.

          * apply k'0 in i; tcsp.

          * apply in_sub_free_vars in j0; exrepnd.
            apply in_sub_keep_first in j1; repnd.
            apply sub_find_some in j2.
            apply in_sub_eta in j2; repnd.
            rw @dom_sub_var_ren in j3; auto.
            rw @range_var_ren in j2; auto.
            rw in_map_iff in j2; exrepnd; subst; allsimpl; repndors; subst; tcsp.

        + introv i j.
          rw in_remove_nvars in j; repnd.
          apply alphaeq_preserves_free_vars in k'1; rw <- k'1 in j0.
          apply eqset_free_vars_disjoint in j0.
          rw @dom_sub_var_ren in j0; auto.
          rw in_app_iff in j0; rw in_remove_nvars in j0.
          repndors; repnd.

          * apply q5 in i; sp.

          * apply in_sub_free_vars in j0; exrepnd.
            apply in_sub_keep_first in j1; repnd.
            apply sub_find_some in j2.
            apply in_sub_eta in j2; repnd.
            rw @dom_sub_var_ren in j3; auto.
            rw @range_var_ren in j2; auto.
            rw in_map_iff in j2; exrepnd; subst; allsimpl; repndors; subst; tcsp.
    }

    exrepnd.
    exists (oterm op bs'); dands; eauto 3 with slow.
    apply alpha_eq_oterm_combine; auto.
Qed.

Lemma bc_apply_iff {o} :
  forall (f a : @NTerm o),
    bc (mk_apply f a)
    <=> (bc f
         # bc a
         # disjoint (free_vars f) (bound_vars a)
         # disjoint (free_vars f) (bound_vars f)
         # disjoint (free_vars a) (bound_vars f)
         # disjoint (free_vars a) (bound_vars a)).
Proof.
  introv.
  split; introv k; repnd.
  - inversion k as [|? ? disj imp]; subst; allsimpl.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    allrw disjoint_app_l; allrw disjoint_app_r; repnd.
    pose proof (imp (nobnd f)) as h1; autodimp h1 hyp.
    pose proof (imp (nobnd a)) as h2; autodimp h2 hyp.
    inversion h1 as [? ? k1]; subst; clear h1.
    inversion h2 as [? ? k2]; subst; clear h2.
    dands; auto.
  - constructor; simpl; allrw remove_nvars_nil_l; allrw app_nil_r;
    allrw disjoint_app_l; allrw disjoint_app_r; dands; auto.
    introv i; repndors; subst; tcsp; constructor; auto.
Qed.
*)

Lemma alpha_eq_mk_less {o} :
  forall (a b c d : @NTerm o) t,
    alpha_eq (mk_less a b c d) t
    -> {a' : NTerm
        & {b' : NTerm
        & {c' : NTerm
        & {d' : NTerm
        & t = mk_less a' b' c' d'
        # alpha_eq a a'
        # alpha_eq b b'
        # alpha_eq c c'
        # alpha_eq d d' }}}}.
Proof.
  introv aeq.
  apply alpha_eq_oterm_implies_combine in aeq.
  exrepnd; subst; allsimpl; cpx; allsimpl.
  pose proof (aeq0 (nobnd a) x) as h1; autodimp h1 hyp.
  pose proof (aeq0 (nobnd b) y) as h2; autodimp h2 hyp.
  pose proof (aeq0 (nobnd c) z) as h3; autodimp h3 hyp.
  pose proof (aeq0 (nobnd d) u) as h4; autodimp h4 hyp.
  clear aeq0.
  allapply @alpha_eq_bterm_nobnd; exrepnd; subst.
  exists u3 u2 u1 u0; dands; auto.
Qed.

Lemma alpha_eq_mk_zero {o} :
  forall (t : @NTerm o),
    alpha_eq mk_zero t -> t = mk_zero.
Proof.
  introv aeq.
  apply alpha_eq_oterm_implies_combine in aeq; exrepnd; allsimpl; cpx.
Qed.

Lemma alpha_eq_mk_lam {o} :
  forall v b (t : @NTerm o),
    alpha_eq (mk_lam v b) t
    -> {v' : NVar
        & {b' : NTerm
        & t = mk_lam v' b'
        # alpha_eq_bterm (bterm [v] b) (bterm [v'] b')}}.
Proof.
  introv aeq.
  apply alpha_eq_oterm_implies_combine in aeq; exrepnd; allsimpl; cpx; allsimpl.
  pose proof (aeq0 (bterm [v] b) x) as h; autodimp h hyp.
  clear aeq0.
  destruct x as [l t].
  applydup @alphaeqbt1v2 in h; exrepnd; subst.
  exists v' t; auto.
Qed.

Lemma alpha_eq_mk_vbot {o} :
  forall v (t : @NTerm o),
    alpha_eq (mk_vbot v) t -> {v' : NVar & t = mk_vbot v'}.
Proof.
  introv aeq.
  apply alpha_eq_oterm_implies_combine in aeq; exrepnd; allsimpl; cpx; allsimpl.
  pose proof (aeq0 (bterm [] (mk_lam v (mk_var v))) x) as h; autodimp h hyp.
  clear aeq0.
  allapply @alpha_eq_bterm_nobnd; exrepnd; subst.
  apply alpha_eq_mk_lam in h0; exrepnd; subst.
  apply alphaeqbt_1v in h0; exrepnd; ginv; allsimpl.
  allrw disjoint_singleton_l; allsimpl; allrw in_app_iff; allrw not_over_or; repnd.
  unfold lsubst in h1; allsimpl; boolvar; allrw disjoint_singleton_r; tcsp.
  apply alpha_eq_mk_var in h1.
  unfold var_ren in h1; allsimpl.
  apply lsubst_aux_eq_vterm_implies in h1; allsimpl.
  repndors; exrepnd; subst; allsimpl; allrw not_over_or; repnd; GC; boolvar; tcsp; ginv.
  exists x; auto.
Qed.

Lemma alphaeq_sub_range_ax_sub {o} :
  forall vs1 vs2,
    length vs1 = length vs2
    -> @alphaeq_sub_range o (ax_sub vs1) (ax_sub vs2).
Proof.
  induction vs1; introv len; allsimpl; cpx.
  destruct vs2; allsimpl; cpx.
  constructor; eauto with slow.
Qed.

Lemma sub_find_ax_sub {o} :
  forall l v,
    @sub_find o (ax_sub l) v
    = if in_deq NVar deq_nvar v l
      then Some mk_axiom
      else None.
Proof.
  induction l; introv; allsimpl; auto.
  boolvar; allrw not_over_or; repndors; tcsp; GC; rw IHl; boolvar; tcsp.
Qed.

Lemma alpha_eq_bterm_mk_zero {o} :
  forall vs (b : @BTerm o),
    alpha_eq_bterm (bterm vs mk_zero) b
    -> {vs' : list NVar
        & b = bterm vs' mk_zero
        # length vs = length vs' }.
Proof.
  introv aeq.
  destruct b as [l t].
  applydup @alpha_eq_bterm_implies_eq_length in aeq.
  apply (lsubst_alpha_congr4 _ _ _ _ (ax_sub vs) (ax_sub l)) in aeq;
    allrw @dom_sub_ax_sub; auto; try (apply alphaeq_sub_range_ax_sub; auto).
  repeat (unflsubst in aeq).
  allsimpl; fold_terms.
  apply alpha_eq_mk_zero in aeq.
  destruct t as [v|op bs]; allsimpl; ginv.
  - rw @sub_find_ax_sub in aeq; boolvar; ginv.
  - inversion aeq; subst.
    destruct bs; allsimpl; cpx; GC; fold_terms; GC.
    exists l; auto.
Qed.

Lemma lsubst_aux_mk_less {o} :
  forall (a b c d : @NTerm o) sub,
    lsubst_aux (mk_less a b c d) sub
    = mk_less (lsubst_aux a sub) (lsubst_aux b sub)
              (lsubst_aux c sub) (lsubst_aux d sub).
Proof.
  introv.
  simpl.
  allrw @sub_filter_nil_r; auto.
Qed.

Lemma lsubst_aux_mk_apply {o} :
  forall (a b : @NTerm o) sub,
    lsubst_aux (mk_apply a b) sub
    = mk_apply (lsubst_aux a sub) (lsubst_aux b sub).
Proof.
  introv.
  simpl.
  allrw @sub_filter_nil_r; auto.
Qed.

Lemma lsubst_aux_mk_try {o} :
  forall (a b c : @NTerm o) v sub,
    lsubst_aux (mk_try a b v c) sub
    = mk_try (lsubst_aux a sub)
             (lsubst_aux b sub)
             v
             (lsubst_aux c (sub_filter sub [v])).
Proof.
  introv.
  simpl.
  allrw @sub_filter_nil_r; auto.
Qed.

Lemma lsubst_aux_mk_vbot {o} :
  forall v (sub : @Sub o),
    lsubst_aux (mk_vbot v) sub
    = mk_vbot v.
Proof.
  introv.
  simpl.
  allrw @sub_filter_nil_r.
  rw @sub_find_sub_filter_eq.
  rw memvar_singleton; boolvar; tcsp.
Qed.

Lemma lsubst_aux_mk_utoken {o} :
  forall a (sub : @Sub o),
    lsubst_aux (mk_utoken a) sub
    = mk_utoken a.
Proof.
  introv.
  simpl; auto.
Qed.

Lemma lsubst_aux_mk_var {o} :
  forall v (sub : @Sub o),
    lsubst_aux (mk_var v) sub
    = match sub_find sub v with
        | Some t => t
        | None => mk_var v
      end.
Proof.
  introv.
  simpl; auto.
Qed.

Lemma lsubst_aux_mk_zero {o} :
  forall (sub : @Sub o),
    lsubst_aux mk_zero sub
    = mk_zero.
Proof.
  introv.
  simpl; auto.
Qed.

Lemma alpha_eq_preserves_isprog {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2 -> isprog t1 -> isprog t2.
Proof.
  introv aeq isp.
  apply alpha_prog_eauto in aeq; allrw @isprogram_eq; auto.
Qed.
Hint Resolve alpha_eq_preserves_isprog : slow.

Definition reduces_to_exc {o} lib (t u : @NTerm o) :=
  {k : nat & reduces_in_atmost_k_steps_exc lib t u k}.

Definition spexc {o} (a : @get_patom_set o) : NTerm := mk_exception (mk_utoken a) mk_axiom.
Definition spexcc {o} (a : @get_patom_set o) : CTerm := mkc_exception (mkc_utoken a) mkc_axiom.

Lemma cequiv_spexc {o} :
  forall lib a (t : @NTerm o),
    cequiv lib t (spexc a)
    -> {n : NTerm
        & {e : NTerm
        & computes_to_exception lib n t e
        # computes_to_value lib n (mk_utoken a)
        # computes_to_value lib e mk_axiom }}.
Proof.
  introv ceq.
  apply cequiv_sym in ceq; apply cequiv_exception_implies in ceq; exrepnd.
  apply cequiv_decomp_axiom0 in ceq1; repnd.
  eapply cequiv_utoken in ceq2;
    [|apply computes_to_value_isvalue_refl; eauto 3 with slow].
  exists x c; dands; auto.
Qed.

Lemma cequiv_spexc_if {o} :
  forall lib (a : get_patom_set o) (t : NTerm),
    isprog t
    -> {n : NTerm
        & {e : NTerm
        & (t =e>(n,lib) e)
        # (n =v>(lib) (mk_utoken a))
        # (e =v>(lib) mk_axiom)}}
    -> cequiv lib t (spexc a).
Proof.
  introv isp h; exrepnd.
  eapply cequiv_trans;
    [apply reduces_to_implies_cequiv;
      [|apply computes_to_exception_as_reduces_to;exact h0]
    |];eauto 3 with slow;[].
  applydup @preserve_program_exc2 in h0; allrw @isprogram_eq; repnd; auto.
  apply cequiv_mk_exception.
  - apply computes_to_value_implies_cequiv; eauto 3 with slow.
  - apply computes_to_value_implies_cequiv; eauto 3 with slow.
Qed.

Lemma reduces_in_atmost_k_steps_exc_decompose {o} :
  forall lib (k : nat) (t a e : @NTerm o),
    isvalue_like a
    -> reduces_in_atmost_k_steps_exc lib t (mk_exception a e) k
    -> {k1 : nat
        & {k2 : nat
        & {k3 : nat
        & {a' : NTerm
        & {e' : NTerm
        & k1 + k2 + k3 <= k
        # reduces_in_atmost_k_steps lib t (mk_exception a' e') k1
        # reduces_in_atmost_k_steps lib a' a k2
        # reduces_in_atmost_k_steps lib e' e k3 }}}}}.
Proof.
  induction k; introv isv r.

  - allrw @reduces_in_atmost_k_steps_exc_0; subst.
    exists 0 0 0 a e; dands; auto;
    allrw @reduces_in_atmost_k_steps_exc_0;
    allrw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_exc_S;
    repndors; exrepnd; repndors; repnd; subst; allsimpl.

    + apply IHk in r1; auto; exrepnd; subst.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r2; eauto 3 with slow; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r5; eauto 3 with slow; subst; GC.
      exists 0 0 (S k3) a' e0; simpl; dands; auto; try omega;
      try (complete (apply reduces_in_atmost_k_steps_refl; eauto 3 with slow)).
      rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.

    + apply IHk in r1; auto; exrepnd; subst.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r2; eauto 3 with slow; ginv.
      exists 0 (S k2) k3 a0 e'; simpl; dands; auto; try omega;
      try (complete (apply reduces_in_atmost_k_steps_refl; eauto 3 with slow)).
      rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.

    + apply IHk in r1; auto; exrepnd; subst.
      exists (S k1) k2 k3 a' e'; dands; auto; simpl; try omega.
      rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_exc_exception_right {o} :
  forall lib k (n e v : @NTerm o),
    isvalue_like n
    -> reduces_in_atmost_k_steps lib e v k
    -> reduces_in_atmost_k_steps_exc lib (mk_exception n e) (mk_exception n v) k.
Proof.
  induction k; introv isv r.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allrw @reduces_in_atmost_k_steps_exc_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    allrw @reduces_in_atmost_k_steps_exc_S; allsimpl; left.
    apply (IHk n) in r0; auto.
    exists n e n u; dands; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_exc_exception {o} :
  forall lib k j (n e v w : @NTerm o),
    isvalue_like v
    -> reduces_in_atmost_k_steps lib n v k
    -> reduces_in_atmost_k_steps lib e w j
    -> {i : nat & i <= k + j # reduces_in_atmost_k_steps_exc lib (mk_exception n e) (mk_exception v w) i}.
Proof.
  induction k; introv isv r1 r2.

  - allrw @reduces_in_atmost_k_steps_0; subst; allsimpl.
    exists j; dands; auto.
    apply reduces_in_atmost_k_steps_exc_exception_right; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd; allsimpl.
    pose proof (nterm_trico_like n) as h; repndors.

    + apply isvariable_implies in h; exrepnd; subst; ginv.

    + rw @compute_step_value_like in r1; auto; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; auto; subst; GC.
      exists j; dands; try omega.
      apply reduces_in_atmost_k_steps_exc_exception_right; auto.

    + apply (IHk j u e v w) in r0; auto; exrepnd.
      exists (S i); dands; try omega.
      allrw @reduces_in_atmost_k_steps_exc_S; allsimpl; left.
      exists n e u e; dands; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_exc_trans {o} :
  forall lib k j (a b c : @NTerm o),
    reduces_in_atmost_k_steps_exc lib a b k
    -> reduces_in_atmost_k_steps_exc lib b c j
    -> reduces_in_atmost_k_steps_exc lib a c (k + j).
Proof.
  induction k; introv r1 r2; allsimpl.

  - allrw @reduces_in_atmost_k_steps_exc_0; subst; auto.

  - allrw @reduces_in_atmost_k_steps_exc_S;
    repndors; exrepnd; subst; repndors; repnd; subst; allsimpl.

    + left.
      exists a' e a' e'; dands; tcsp.
      eapply IHk; eauto.

    + left.
      exists a0 e' a' e'; dands; tcsp.
      eapply IHk; eauto.

    + right; dands; auto.
      eexists; dands; eauto.
Qed.

Lemma dec_isexc {o} :
  forall (t : @NTerm o), decidable (isexc t).
Proof.
  introv.
  destruct t as [v|op bs]; simpl; try (complete (right; sp)).
  dopid op as [can|ncan|nsw|exc|abs] Case; try (complete (right; sp)).
  left; sp.
Qed.

Lemma reduces_in_atmost_k_steps_exc_trans2 {o} :
  forall lib k j (a b c : @NTerm o),
    reduces_in_atmost_k_steps lib a b k
    -> reduces_in_atmost_k_steps_exc lib b c j
    -> {i : nat & i <= k + j # reduces_in_atmost_k_steps_exc lib a c i}.
Proof.
  induction k; introv r1 r2; allsimpl.

  - exists j; dands; try omega.
    allrw @reduces_in_atmost_k_steps_0; subst; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.

    destruct (dec_isexc a) as [d|d].

    + rw @compute_step_value_like in r1; eauto 2 with slow; ginv.
      eapply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto 2 with slow.
      subst.
      apply isexc_implies2 in d; exrepnd; subst; allsimpl.
      exists j; dands; auto; try omega.

    + eapply IHk in r0;[|exact r2].
      exrepnd.
      exists (S i); dands; try omega.
      rw @reduces_in_atmost_k_steps_exc_S.
      right; dands; auto.
      eexists; dands; eauto.
Qed.

Lemma reduces_to_exc_spexc_as_cequiv {o} :
  forall lib (t : @NTerm o) a,
    isprog t
    -> (reduces_to_exc lib t (spexc a) <=> cequiv lib t (spexc a)).
Proof.
  introv isp; split; intro h.
  - unfold reduces_to_exc in h; exrepnd.
    apply reduces_in_atmost_k_steps_exc_decompose in h0; exrepnd; eauto 3 with slow.
    apply cequiv_spexc_if; auto.
    exists a' e'; dands; eauto 3 with slow.
    exists k1; auto.
  - apply cequiv_spexc in h; exrepnd.
    allunfold @computes_to_exception.
    allunfold @computes_to_value; repnd.
    allunfold @reduces_to; exrepnd.
    pose proof (reduces_in_atmost_k_steps_exc_exception
                  lib k0 k n e (mk_utoken a) mk_axiom) as q.
    repeat (autodimp q hyp); eauto 3 with slow; exrepnd.
    try (fold (spexc a) in q0).
    pose proof (reduces_in_atmost_k_steps_exc_trans2
                  lib k1 i t (mk_exception n e) (spexc a)) as l.
    repeat (autodimp l hyp); exrepnd.
    exists i0; auto.
Qed.

Lemma alpha_eq_mk_axiom {o} :
  forall (u : @NTerm o),
    alpha_eq mk_axiom u
    -> u = mk_axiom.
Proof.
  introv aeq.
  inversion aeq; subst; allsimpl; cpx.
Qed.

Lemma reduces_in_atmost_k_steps_excc_decompose {o} :
  forall lib (k : nat) (t a e : @CTerm o),
    isvalue_likec a
    -> reduces_in_atmost_k_steps_excc lib t (mkc_exception a e) k
    -> {k1 : nat
        & {k2 : nat
        & {k3 : nat
        & {a' : CTerm
        & {e' : CTerm
        & k1 + k2 + k3 <= k
        # reduces_in_atmost_k_stepsc lib t (mkc_exception a' e') k1
        # reduces_in_atmost_k_stepsc lib a' a k2
        # reduces_in_atmost_k_stepsc lib e' e k3 }}}}}.
Proof.
  introv isv r; destruct_cterms.
  allunfold @isvalue_likec; allsimpl.
  allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
  allunfold @reduces_in_atmost_k_stepsc; allsimpl.
  apply reduces_in_atmost_k_steps_exc_decompose in r; auto; exrepnd.
  applydup @reduces_atmost_preserves_program in r2;
    allrw @isprogram_exception_iff; allrw @isprogram_eq; repnd; auto.
  exists k1 k2 k3 (mk_ct a' r5) (mk_ct e' r4); dands; auto.
Qed.

Lemma dec_reduces_in_atmost_k_steps_exc {o} :
  forall lib k (t v : @NTerm o),
    (forall x, decidable (x = v))
    -> decidable (reduces_in_atmost_k_steps_exc lib t v k).
Proof.
  introv d.
  remember (compute_at_most_k_steps_exc lib k t) as c; symmetry in Heqc.
  destruct c.
  - destruct (d n) as [h|h]; subst.
    + left; auto.
    + right; intro r; rw r in Heqc; ginv; tcsp.
  - right; intro r; rw r in Heqc; ginv.
Qed.

Lemma dec_reduces_in_atmost_k_steps_excc {o} :
  forall lib k (t v : @CTerm o),
    (forall x, decidable (x = get_cterm v))
    -> decidable (reduces_in_atmost_k_steps_excc lib t v k).
Proof.
  introv d; destruct_cterms; allsimpl.
  unfold reduces_in_atmost_k_steps_excc; simpl.
  apply dec_reduces_in_atmost_k_steps_exc; auto.
Qed.

Lemma decidable_spexc {o} :
  forall a (t : @NTerm o), decidable (t = spexc a).
Proof.
  introv.
  destruct t as [v|op bs]; try (complete (right; intro e; complete ginv)).
  destruct op; try (complete (right; intro e; complete ginv)).
  repeat (destruct bs; try (complete (right; intro e; complete ginv))).
  destruct b as [l1 t1]; destruct b0 as [l2 t2].
  destruct l1; try (complete (right; intro e; complete ginv)).
  destruct l2; try (complete (right; intro e; complete ginv)).
  destruct t1 as [v|op bs]; try (complete (right; intro e; complete ginv)).
  destruct op; try (complete (right; intro e; complete ginv)).
  destruct c; try (complete (right; intro e; complete ginv)).
  destruct bs; try (complete (right; intro e; complete ginv)).
  destruct t2 as [v|op bs]; try (complete (right; intro e; complete ginv)).
  destruct op; try (complete (right; intro e; complete ginv)).
  destruct c; try (complete (right; intro e; complete ginv)).
  destruct bs; try (complete (right; intro e; complete ginv)).
  fold_terms.
  fold (spexc g).
  destruct (get_patom_deq o g a) as [h|h]; subst; tcsp.
  right; intro e; ginv; tcsp.
Qed.
Hint Resolve decidable_spexc : slow.

Lemma dec_spexcc {o} :
  forall (t : @CTerm o) a,
    decidable (t = spexcc a).
Proof.
  introv; destruct_cterms.
  destruct (decidable_spexc a x); subst; simpl.
  - left; apply cterm_eq; simpl; auto.
  - right; intro xx; ginv.
    inversion xx; sp.
Qed.

Lemma get_cterm_mkc_exception {o} :
  forall (a e : @CTerm o),
    get_cterm (mkc_exception a e) = mk_exception (get_cterm a) (get_cterm e).
Proof.
  introv; destruct_cterms; simpl; auto.
Qed.

Lemma dec_reduces_in_atmost_k_steps_exc_nat {o} :
  forall lib k (t : @NTerm o),
    decidable {n : nat & reduces_in_atmost_k_steps_exc lib t (mk_nat n) k}.
Proof.
  introv.
  remember (compute_at_most_k_steps_exc lib k t) as c; symmetry in Heqc.
  destruct c.
  - destruct (decidable_ex_mk_nat n) as [d|d]; exrepnd; subst.
    + left; exists n0; auto.
    + right; intro r; exrepnd.
      rw r0 in Heqc; ginv.
      destruct d; eexists; eauto.
  - right; intro r; exrepnd; rw r0 in Heqc; ginv.
Qed.

Lemma dec_reduces_in_atmost_k_steps_excc_nat {o} :
  forall lib k (t : @CTerm o),
    decidable {n : nat & reduces_in_atmost_k_steps_excc lib t (mkc_nat n) k}.
Proof.
  introv; destruct_cterms; allsimpl.
  unfold reduces_in_atmost_k_steps_excc; simpl.
  apply dec_reduces_in_atmost_k_steps_exc_nat; auto.
Qed.

Lemma reduces_in_atmost_k_steps_exc_can {o} :
  forall lib k (t v : @NTerm o),
    iscan v
    -> reduces_in_atmost_k_steps lib t v k
    -> reduces_in_atmost_k_steps_exc lib t v k.
Proof.
  induction k; introv isc r.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allrw @reduces_in_atmost_k_steps_exc_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    allrw @reduces_in_atmost_k_steps_exc_S.
    applydup IHk in r0; auto.
    destruct t as [x|op bs]; ginv.

    dopid op as [can|ncan|nsw|exc|abs] Case.

    + Case "Can".
      csunf r1; allsimpl; ginv.
      right; dands; tcsp.
      exists (oterm (Can can) bs); csunf; simpl; dands; auto.

    + Case "NCan".
      simpl; right; dands; tcsp.
      exists u; dands; auto.

    + Case "NSwapCs2".
      simpl; right; dands; tcsp.
      exists u; dands; auto.

    + Case "Exc".
      csunf r1; allsimpl; ginv.
      apply reduces_in_atmost_k_steps_if_isvalue_like in r0; eauto 3 with slow; subst.
      allsimpl; tcsp.

    + Case "Abs".
      simpl; right; dands; tcsp.
      exists u; dands; auto.
Qed.

Lemma reduces_in_atmost_k_steps_excc_can {o} :
  forall lib k (t v : @CTerm o),
    iscanc v
    -> reduces_in_atmost_k_stepsc lib t v k
    -> reduces_in_atmost_k_steps_excc lib t v k.
Proof.
  introv isc r; destruct_cterms; allsimpl.
  unfold iscanc in isc; unfold reduces_in_atmost_k_stepsc in r.
  unfold reduces_in_atmost_k_steps_excc; allsimpl.
  apply reduces_in_atmost_k_steps_exc_can; auto.
Qed.

Lemma cequivc_spexcc {o} :
  forall lib a (t : @CTerm o),
    cequivc lib t (spexcc a)
    -> {n : CTerm
        & {e : CTerm
        & computes_to_excc lib n t e
        # computes_to_valc lib n (mkc_utoken a)
        # computes_to_valc lib e mkc_axiom }}.
Proof.
  introv ceq.
  destruct_cterms.
  unfold cequivc in ceq; allsimpl.
  apply cequiv_spexc in ceq; exrepnd.
  applydup @preserve_program_exc2 in ceq0; allrw @isprogram_eq; repnd; auto.
  exists (mk_ct n ceq4) (mk_ct e ceq3).
  unfold computes_to_excc, computes_to_valc; simpl; dands; auto.
Qed.

Lemma computes_to_excc_iff_reduces_toc {o} :
  forall lib (a t e : @CTerm o),
    computes_to_excc lib a t e
    <=> reduces_toc lib t (mkc_exception a e).
Proof.
  introv; destruct_cterms.
  unfold computes_to_excc, reduces_toc; simpl; split; intro k; repnd; tcsp.
Qed.

Lemma computes_to_excc_iff_reduces_in_atmost_k_stepsc {o} :
  forall lib (a t e : @CTerm o),
    computes_to_excc lib a t e
    <=> {k : nat & reduces_in_atmost_k_stepsc lib t (mkc_exception a e) k}.
Proof.
  introv.
  rw @computes_to_excc_iff_reduces_toc.
  rw @reduces_toc_iff_reduces_in_atmost_k_stepsc; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_exc_done {o} :
  forall lib j (a e t : @NTerm o),
    isvalue_like a
    -> isvalue_like e
    -> (reduces_in_atmost_k_steps_exc lib (mk_exception a e) t j
        <=> t = mk_exception a e).
Proof.
  induction j; introv isva isve.
  - allrw @reduces_in_atmost_k_steps_exc_0; split; sp.
  - allrw @reduces_in_atmost_k_steps_exc_S.
    split; intro k; repndors; exrepnd; allsimpl; tcsp.
    + ginv; repndors; exrepnd; tcsp; subst.
      * rw @compute_step_value_like in k3; auto; ginv.
        apply IHj in k1; auto.
      * rw @compute_step_value_like in k3; auto; ginv.
        apply IHj in k1; auto.
    + subst; left.
      exists a e a e; dands; auto.
      * left; dands; auto.
        rw @compute_step_value_like; auto.
      * apply IHj; auto.
Qed.

Lemma reduces_in_atmost_k_steps_exc_le_exc {o} :
  forall lib k j (t a e : @NTerm o),
    k <= j
    -> isvalue_like a
    -> isvalue_like e
    -> reduces_in_atmost_k_steps_exc lib t (mk_exception a e) k
    -> reduces_in_atmost_k_steps_exc lib t (mk_exception a e) j.
Proof.
  induction k; introv lek isva isve r.
  - allrw @reduces_in_atmost_k_steps_exc_0; subst.
    apply reduces_in_atmost_k_steps_exc_done; auto.
  - destruct j; try omega.
    allapply le_S_n.
    allrw @reduces_in_atmost_k_steps_exc_S.
    repndors; exrepnd; subst; repndors; repnd; subst; allsimpl; tcsp.
    + left.
      exists a' e0 a' e'.
      dands; tcsp.
    + left.
      exists a0 e' a' e'.
      dands; tcsp.
    + right; dands; auto.
      eexists; dands; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_excc_le_exc {o} :
  forall lib k j (t a e : @CTerm o),
    k <= j
    -> isvalue_likec a
    -> isvalue_likec e
    -> reduces_in_atmost_k_steps_excc lib t (mkc_exception a e) k
    -> reduces_in_atmost_k_steps_excc lib t (mkc_exception a e) j.
Proof.
  introv lek isva isve r.
  destruct_cterms; allunfold @isvalue_likec.
  allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
  eapply reduces_in_atmost_k_steps_exc_le_exc; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_excc_exception {o} :
  forall lib k j (n e v w : @CTerm o),
    isvalue_likec v
    -> reduces_in_atmost_k_stepsc lib n v k
    -> reduces_in_atmost_k_stepsc lib e w j
    -> {i : nat & i <= k + j # reduces_in_atmost_k_steps_excc lib (mkc_exception n e) (mkc_exception v w) i}.
Proof.
  introv isv r1 r2; destruct_cterms.
  allunfold @isvalue_likec; allsimpl.
  allunfold @reduces_in_atmost_k_stepsc; allsimpl.
  allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
  apply reduces_in_atmost_k_steps_exc_exception; auto.
Qed.

Lemma reduces_in_atmost_k_steps_excc_trans2 {o} :
  forall lib k j (a b c : @CTerm o),
    reduces_in_atmost_k_stepsc lib a b k
    -> reduces_in_atmost_k_steps_excc lib b c j
    -> {i : nat & i <= k + j # reduces_in_atmost_k_steps_excc lib a c i}.
Proof.
  introv r1 r2; destruct_cterms.
  allunfold @reduces_in_atmost_k_stepsc.
  allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
  eapply reduces_in_atmost_k_steps_exc_trans2; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_exc_exception_implies {o} :
  forall lib k (a e u : @NTerm o),
    reduces_in_atmost_k_steps_exc lib (mk_exception a e) u k
    -> isexc u.
Proof.
  induction k; introv r.

  - allrw @reduces_in_atmost_k_steps_exc_0; subst; eauto 3 with slow.

  - allrw @reduces_in_atmost_k_steps_exc_S;
    repndors; exrepnd; repndors; repnd; subst; allsimpl; ginv; tcsp;
    apply IHk in r1; tcsp.
Qed.

Lemma reduces_in_atmost_k_steps_exc_can_implies {o} :
  forall lib k (t u : @NTerm o),
    iscan u
    -> reduces_in_atmost_k_steps_exc lib t u k
    -> reduces_in_atmost_k_steps lib t u k.
Proof.
  induction k; introv isc r.

  - allrw @reduces_in_atmost_k_steps_0.
    allrw @reduces_in_atmost_k_steps_exc_0; auto.

  - allrw @reduces_in_atmost_k_steps_S.
    allrw @reduces_in_atmost_k_steps_exc_S.
    repndors; exrepnd; subst; repndors; repnd; subst.

    + apply reduces_in_atmost_k_steps_exc_exception_implies in r1.
      apply iscan_implies_not_isexc in isc; tcsp.

    + apply reduces_in_atmost_k_steps_exc_exception_implies in r1.
      apply iscan_implies_not_isexc in isc; tcsp.

    + eexists; dands; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_excc_can_implies {o} :
  forall lib k (t u : @CTerm o),
    iscanc u
    -> reduces_in_atmost_k_steps_excc lib t u k
    -> reduces_in_atmost_k_stepsc lib t u k.
Proof.
  introv isc r; destruct_cterms.
  allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
  allunfold @reduces_in_atmost_k_stepsc; allsimpl.
  apply reduces_in_atmost_k_steps_exc_can_implies; auto.
Qed.

Lemma isvalue_like_implies_not_isnoncan_like {o} :
  forall (t : @NTerm o), isvalue_like t -> !isnoncan_like t.
Proof.
  introv isv isn.
  unfold isnoncan_like in isn.
  destruct isv as [isv|isv].
  - apply iscan_implies in isv; repndors; exrepnd; subst; allsimpl; tcsp.
  - apply isexc_implies2 in isv; exrepnd; subst; allsimpl; tcsp.
Qed.
Hint Resolve isvalue_like_implies_not_isnoncan_like : slow.

Lemma reduces_in_atmost_k_steps_exc_iscan {o} :
  forall lib k (t u : @NTerm o),
    iscan t
    -> (reduces_in_atmost_k_steps_exc lib t u k <=> t = u).
Proof.
  induction k; introv isc.

  - allrw @reduces_in_atmost_k_steps_exc_0; tcsp.

  - allrw @reduces_in_atmost_k_steps_exc_S; split; intro h; subst.

    + repndors; exrepnd; subst; repndors; repnd; subst; allsimpl; tcsp.
      rw @compute_step_value_like in h2; eauto 3 with slow; ginv.
      apply IHk in h1; auto.

    + right; dands; eauto 2 with slow.
      exists u.
      rw @compute_step_value_like; eauto 3 with slow; dands; auto.
      apply IHk; auto.
Qed.

Lemma reduces_in_atmost_k_steps_exc_impossible1 {o} :
  forall lib k1 k2 (t : @NTerm o) a n,
    reduces_in_atmost_k_steps_exc lib t (spexc a) k1
    -> reduces_in_atmost_k_steps_exc lib t (mk_nat n) k2
    -> False.
Proof.
  induction k1; introv r1 r2.

  - allrw @reduces_in_atmost_k_steps_exc_0; subst.
    apply reduces_in_atmost_k_steps_exc_done in r2; eauto 3 with slow; ginv.

  - allrw @reduces_in_atmost_k_steps_exc_S;
    repndors; exrepnd; subst; repndors; exrepnd; subst; allsimpl.

    + destruct k2.

      * allrw @reduces_in_atmost_k_steps_exc_0; ginv.

      * allrw @reduces_in_atmost_k_steps_exc_S;
        repndors; exrepnd; subst; repndors; exrepnd; subst; allsimpl; tcsp;
        eauto 3 with slow; ginv.

        { rw r7 in r4; ginv.
          eapply IHk1 in r1; eauto. }

        { apply isvalue_like_implies_not_isnoncan_like in r0; sp. }

    + destruct k2.

      * allrw @reduces_in_atmost_k_steps_exc_0; ginv.

      * allrw @reduces_in_atmost_k_steps_exc_S;
        repndors; exrepnd; subst; repndors; exrepnd; subst; allsimpl; tcsp;
        eauto 3 with slow; ginv.

        { apply isvalue_like_implies_not_isnoncan_like in r6; sp. }

        { rw r7 in r4; ginv.
          eapply IHk1 in r1; eauto. }

    + destruct k2.

      * allrw @reduces_in_atmost_k_steps_exc_0; ginv; subst; allsimpl; tcsp; GC.
        csunf r1; allsimpl; ginv.
        apply reduces_in_atmost_k_steps_exc_iscan in r3; tcsp; ginv.

      * allrw @reduces_in_atmost_k_steps_exc_S;
        repndors; exrepnd; subst; repndors; exrepnd; subst; allsimpl; tcsp;
        eauto 3 with slow; ginv.
        rw r1 in r2; ginv.
        eapply IHk1 in r3; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_excc_impossible1 {o} :
  forall lib k1 k2 (t : @CTerm o) a n,
    reduces_in_atmost_k_steps_excc lib t (spexcc a) k1
    -> reduces_in_atmost_k_steps_excc lib t (mkc_nat n) k2
    -> False.
Proof.
  introv r1 r2; destruct_cterms.
  allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
  eapply reduces_in_atmost_k_steps_exc_impossible1 in r1; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_preserves_wf {o} :
  forall lib (t u : @NTerm o) k,
    reduces_in_atmost_k_steps lib t u k
    -> wf_term t
    -> wf_term u.
Proof.
  introv r w.
  eapply reduces_to_preserves_wf;[|exact w].
  exists k; exact r.
Qed.

Lemma reduces_to_preserves_isprog {o} :
  forall lib (t1 t2 : @NTerm o),
    reduces_to lib t1 t2
    -> isprog t1
    -> isprog t2.
Proof.
  introv r i.
  allrw @isprog_eq.
  eapply reduces_to_preserves_program; eauto.
Qed.

Lemma reduces_to_exc_trans2 {o} :
  forall lib (a b c : @NTerm o),
    reduces_to lib a b
    -> reduces_to_exc lib b c
    -> reduces_to_exc lib a c.
Proof.
  introv r1 r2.
  allunfold @reduces_to; allunfold @reduces_to_exc; exrepnd.
  eapply reduces_in_atmost_k_steps_exc_trans2 in r2;[|exact r0].
  exrepnd.
  exists i; auto.
Qed.

Lemma reduces_to_exc_spexc {o} :
  forall lib (t : @NTerm o) a,
    reduces_to_exc lib t (spexc a)
    -> {n : NTerm
        & {e : NTerm
        & (t =e>(n,lib) e)
        # (n =v>(lib) (mk_utoken a))
        # (e =v>(lib) mk_axiom)}}.
Proof.
  introv r.
  unfold reduces_to_exc in r; exrepnd.
  apply reduces_in_atmost_k_steps_exc_decompose in r0; exrepnd; eauto 3 with slow.
  exists a' e'; dands; eauto 3 with slow.
  exists k1; auto.
Qed.
