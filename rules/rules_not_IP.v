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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)



Require Export rules_choice_util2.


Ltac hide_wf :=
  repeat match goal with
         | [ H : wf_term _ |- _ ] => hide_hyp H
         | [ H : cover_vars _ _ |- _ ] => hide_hyp H
         | [ H : cover_vars_upto _ _ _ |- _ ] => hide_hyp H
         end.

Definition exists_1_choice_fun {o} (a : choice_sequence_name) (n : NVar) : @CTerm o :=
  mkc_lam
    n
    (mkcv_equality
       _
       (mkcv_apply _ (mkcv_choice_seq _ a) (mkc_var n))
       (mkcv_one _)
       (mkcv_tnat _)).

Lemma simple_implies_approx_product {o} :
  forall lib u v1 v2 (t1 t2 : @NTerm o),
    isprogram u
    -> isprog_vars [v1] t1
    -> isprog_vars [v2] t2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v1 u) (subst t2 v2 u))
    -> approx lib (mk_product u v1 t1) (mk_product u v2 t2).
Proof.
  introv ispu isp1 isp2 imp.

  applydup @isprog_vars_eq in isp1.
  applydup @isprog_vars_eq in isp2.
  repnd.

  constructor.
  unfold close_comput; dands;
    try (apply isprogram_product);
    eauto 3 with slow.

  - introv comp.
    apply computes_to_value_isvalue_eq in comp;
      try (apply implies_isvalue_product); eauto 3 with slow.
    unfold mk_product in comp; ginv; fold_terms.
    exists [bterm [] u, bterm [v2] t2]; fold_terms.
    dands.
    { apply computes_to_value_isvalue_refl;
        try (apply implies_isvalue_product); eauto 3 with slow. }

    unfold lblift; simpl; dands; auto.
    introv ltn.
    destruct n; try omega;[|destruct n; try omega]; clear ltn;
      unfold selectbt; simpl;
        unfold blift.

    {
      exists ([] : list NVar) u u; dands; eauto 3 with slow.
      apply clearbots_olift.
      apply cl_olift_implies_olift; eauto 3 with slow.

      pose proof (cl_olift_iff_pv_olift (approx lib) u u []) as xx.
      repeat (autodimp xx hyp); eauto 3 with slow;[].
      apply xx; clear xx.
      introv ps e.
      destruct sub as [|p s]; allsimpl; ginv; autorewrite with slow; eauto 3 with slow.
    }

    exists [v1] t1 (subst t2 v2 (mk_var v1)); dands; eauto 3 with slow.

    + apply clearbots_olift.
      apply cl_olift_implies_olift; eauto 3 with slow.

      pose proof (cl_olift_iff_pv_olift (approx lib) t1 (subst t2 v2 (mk_var v1)) [v1]) as xx.
      repeat (autodimp xx hyp).
      { clear imp; allrw @isprog_vars_eq; repnd; dands.
        - eapply subvars_eqvars;
            [|apply eqvars_sym;apply eqvars_free_vars_disjoint].
          simpl.
          rw subvars_app_l; dands.
          + apply subvars_remove_nvars; simpl.
            eapply subvars_trans;eauto.
            rw subvars_prop; simpl; tcsp.
          + boolvar; simpl; eauto 3 with slow.
        - apply nt_wf_subst; eauto 3 with slow. }
      apply xx; clear xx.
      introv ps e.
      destruct sub as [|p s]; allsimpl; ginv.
      destruct s; ginv.
      destruct p as [z w]; allsimpl.
      allrw @fold_subst.
      allrw @prog_sub_cons; repnd.
      pose proof (imp w) as h; clear imp; allsimpl.
      autodimp h hyp; eauto 3 with slow.
      destruct h; sp.
      eapply approx_trans; eauto;[].

      eapply approx_alpha_rw_r_aux;
        [apply alpha_eq_sym;apply combine_sub_nest|].
      simpl.
      allrw @fold_subst.
      rw @subst_mk_var1.

      destruct (deq_nvar v2 z); subst.

      * pose proof (cl_lsubst_app_sub_filter t2 [(z,w)] [(z,w)]) as h; allsimpl.
        autodimp h hyp; eauto 3 with slow.
        allrw memvar_singleton; boolvar; rw h; eauto 3 with slow.

      * pose proof (lsubst_sub_filter_alpha t2 [(v2, w), (z, w)] [z]) as h.
        allrw disjoint_singleton_r; allsimpl.
        allrw memvar_singleton; boolvar; tcsp.
        autodimp h hyp.
        { allrw @isprog_vars_eq; repnd.
          allrw subvars_eq.
          introv h; apply isp7 in h; allsimpl; tcsp. }

        eapply approx_alpha_rw_r_aux;[exact h|].
        allrw @fold_subst; eauto 3 with slow.

    + pose proof (alpha_eq_bterm_single_change t2 v2) as h.
      allrw subset_singleton_r.
      autodimp h hyp.
      { introv ix.
        clear imp.
        allrw @isprog_vars_eq; repnd.
        allrw subvars_eq.
        apply isp7 in ix; allsimpl; tcsp. }
      apply h.

  - introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.
Qed.

Lemma simple_implies_cequiv_product {o} :
  forall lib u v1 v2 (t1 t2 : @NTerm o),
    isprogram u
    -> isprog_vars [v1] t1
    -> isprog_vars [v2] t2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v1 u) (subst t2 v2 u))
    -> cequiv lib (mk_product u v1 t1) (mk_product u v2 t2).
Proof.
  introv ispu isp1 isp2 imp.
  split; apply simple_implies_approx_product; auto.
  introv isp; apply cequiv_sym; apply imp; auto.
Qed.

Lemma simple_implies_approx_set {o} :
  forall lib u v1 v2 (t1 t2 : @NTerm o),
    isprogram u
    -> isprog_vars [v1] t1
    -> isprog_vars [v2] t2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v1 u) (subst t2 v2 u))
    -> approx lib (mk_set u v1 t1) (mk_set u v2 t2).
Proof.
  introv ispu isp1 isp2 imp.

  applydup @isprog_vars_eq in isp1.
  applydup @isprog_vars_eq in isp2.
  repnd.

  constructor.
  unfold close_comput; dands;
    try (apply isprogram_set);
    eauto 3 with slow.

  - introv comp.
    apply computes_to_value_isvalue_eq in comp;
      try (apply implies_isvalue_set); eauto 3 with slow.
    unfold mk_set in comp; ginv; fold_terms.
    exists [bterm [] u, bterm [v2] t2]; fold_terms.
    dands.
    { apply computes_to_value_isvalue_refl;
        try (apply implies_isvalue_set); eauto 3 with slow. }

    unfold lblift; simpl; dands; auto.
    introv ltn.
    destruct n; try omega;[|destruct n; try omega]; clear ltn;
      unfold selectbt; simpl;
        unfold blift.

    {
      exists ([] : list NVar) u u; dands; eauto 3 with slow.
      apply clearbots_olift.
      apply cl_olift_implies_olift; eauto 3 with slow.

      pose proof (cl_olift_iff_pv_olift (approx lib) u u []) as xx.
      repeat (autodimp xx hyp); eauto 3 with slow;[].
      apply xx; clear xx.
      introv ps e.
      destruct sub as [|p s]; allsimpl; ginv; autorewrite with slow; eauto 3 with slow.
    }

    exists [v1] t1 (subst t2 v2 (mk_var v1)); dands; eauto 3 with slow.

    + apply clearbots_olift.
      apply cl_olift_implies_olift; eauto 3 with slow.

      pose proof (cl_olift_iff_pv_olift (approx lib) t1 (subst t2 v2 (mk_var v1)) [v1]) as xx.
      repeat (autodimp xx hyp).
      { clear imp; allrw @isprog_vars_eq; repnd; dands.
        - eapply subvars_eqvars;
            [|apply eqvars_sym;apply eqvars_free_vars_disjoint].
          simpl.
          rw subvars_app_l; dands.
          + apply subvars_remove_nvars; simpl.
            eapply subvars_trans;eauto.
            rw subvars_prop; simpl; tcsp.
          + boolvar; simpl; eauto 3 with slow.
        - apply nt_wf_subst; eauto 3 with slow. }
      apply xx; clear xx.
      introv ps e.
      destruct sub as [|p s]; allsimpl; ginv.
      destruct s; ginv.
      destruct p as [z w]; allsimpl.
      allrw @fold_subst.
      allrw @prog_sub_cons; repnd.
      pose proof (imp w) as h; clear imp; allsimpl.
      autodimp h hyp; eauto 3 with slow.
      destruct h; sp.
      eapply approx_trans; eauto;[].

      eapply approx_alpha_rw_r_aux;
        [apply alpha_eq_sym;apply combine_sub_nest|].
      simpl.
      allrw @fold_subst.
      rw @subst_mk_var1.

      destruct (deq_nvar v2 z); subst.

      * pose proof (cl_lsubst_app_sub_filter t2 [(z,w)] [(z,w)]) as h; allsimpl.
        autodimp h hyp; eauto 3 with slow.
        allrw memvar_singleton; boolvar; rw h; eauto 3 with slow.

      * pose proof (lsubst_sub_filter_alpha t2 [(v2, w), (z, w)] [z]) as h.
        allrw disjoint_singleton_r; allsimpl.
        allrw memvar_singleton; boolvar; tcsp.
        autodimp h hyp.
        { allrw @isprog_vars_eq; repnd.
          allrw subvars_eq.
          introv h; apply isp7 in h; allsimpl; tcsp. }

        eapply approx_alpha_rw_r_aux;[exact h|].
        allrw @fold_subst; eauto 3 with slow.

    + pose proof (alpha_eq_bterm_single_change t2 v2) as h.
      allrw subset_singleton_r.
      autodimp h hyp.
      { introv ix.
        clear imp.
        allrw @isprog_vars_eq; repnd.
        allrw subvars_eq.
        apply isp7 in ix; allsimpl; tcsp. }
      apply h.

  - introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.
Qed.

Lemma simple_implies_cequiv_set {o} :
  forall lib u v1 v2 (t1 t2 : @NTerm o),
    isprogram u
    -> isprog_vars [v1] t1
    -> isprog_vars [v2] t2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v1 u) (subst t2 v2 u))
    -> cequiv lib (mk_set u v1 t1) (mk_set u v2 t2).
Proof.
  introv ispu isp1 isp2 imp.
  split; apply simple_implies_approx_set; auto.
  introv isp; apply cequiv_sym; apply imp; auto.
Qed.


Lemma cequivc_exists_1_choice_sub {o} :
  forall (lib : @library o) name A B v n w s c (d1 : A <> B) (d2 : B <> n),
    cequivc
      lib
      (exists_1_choice name v)
      (substc2
         B
         (exists_1_choice name nvarx)
         A
         (lsubstc_vars
            (mk_exists mk_tnat n (mk_apply (mk_var B) (mk_var n)))
            w
            (csub_filter (csub_filter s [A]) [B])
            [B, A]
            c))
      [[B \\ exists_1_choice_fun name v]].
Proof.
  introv d1 d2.
  unfold cequivc; simpl.

  rewrite csubst_trivial;
    [|simpl; autorewrite with slow;
      repeat rewrite dom_csub_csub_filter;
      pose proof (remove_nvars_unchanged [n] [B]) as q;
      destruct q as [q q']; clear q'; rewrite q; eauto 3 with slow];[].

  rewrite (cl_subst_trivial (mk_exists _ _ _)); simpl; autorewrite with slow;
    [|rw in_remove_nvars; simpl; intro xx; repnd; repndors; tcsp
     |unfold closed; simpl; autorewrite with slow; auto];[].

  unfsubst;[|unfold closed; simpl; autorewrite with slow; auto];[].
  simpl; autorewrite with slow.

  assert (match
             sub_find
               (if beq_var B nvary
                then []
                else [(B, mk_lam v (mk_equality (mk_apply (mk_choice_seq name) (mk_var v)) mk_one mk_tnat))]) nvary
           with
           | Some t => t
           | None => vterm nvary
           end = @mk_var o nvary) as xx.
  { boolvar; simpl; auto; boolvar; simpl; auto; tcsp. }
  rewrite xx; clear xx.
  repeat (boolvar; simpl; autorewrite with slow; tcsp);[].
  fold_terms.

  apply simple_implies_cequiv_product; eauto 3 with slow; tcsp.

  { split; eauto 3 with slow; tcsp. }

  { apply isprog_vars_eq; dands; tcsp; eauto 3 with slow.
    simpl; autorewrite with slow; auto. }

  introv ispu.
  repeat unfsubst; simpl.
  repeat autorewrite with slow.

  assert (match sub_find (if beq_var v nvary then [] else [(v, u)]) nvary
          with
          | Some t => t
          | None => vterm nvary
          end = mk_var nvary) as xx.
  { boolvar; simpl; auto; boolvar; simpl; tcsp. }
  rewrite xx; clear xx.

  assert (match sub_find (if beq_var n v then [] else [(n, u)]) v
          with
          | Some t => t
          | None => vterm v
          end = mk_var v) as xx.
  { boolvar; simpl; auto; boolvar; simpl; tcsp. }
  rewrite xx; clear xx.
  fold_terms.

  apply cequiv_sym.
  eapply cequiv_trans;[apply cequiv_beta|]; eauto 3 with slow;[].

  unfsubst; simpl.
  autorewrite with slow.

  assert (match sub_find (if beq_var v nvary then [] else [(v, u)]) nvary
          with
          | Some t => t
          | None => vterm nvary
          end = mk_var nvary) as xx.
  { boolvar; simpl; auto; boolvar; simpl; tcsp. }
  rewrite xx; clear xx.
  fold_terms.

  apply cequiv_refl; eauto 3 with slow.
  apply isprogram_equality; eauto 3 with slow.

  { apply isprogram_apply; eauto 3 with slow.
    split; simpl; tcsp; eauto 3 with slow. }

  apply isprogram_set; eauto 3 with slow.
Qed.

Ltac aeq_lsubstc_vars_prod h :=
  match goal with
  | [ |- context[lsubstc_vars (mk_product ?t1 ?v ?t2) ?w ?s ?vs ?c] ] =>
    let w1 := fresh "w1" in
    let w2 := fresh "w2" in
    let c1 := fresh "c1" in
    let c2 := fresh "c2" in
    pose proof (lsubstc_vars_mk_product_as_mkcv t1 v t2 w s vs c) as h;
    destruct h as [w1 h];
    destruct h as [w2 h];
    destruct h as [c1 h];
    destruct h as [c2 h]

  | [ H : context[lsubstc_vars (mk_product ?t1 ?v ?t2) ?w ?s ?vs ?c] |- _ ] =>
    let w1 := fresh "w1" in
    let w2 := fresh "w2" in
    let c1 := fresh "c1" in
    let c2 := fresh "c2" in
    pose proof (lsubstc_vars_mk_product_as_mkcv t1 v t2 w s vs c) as h;
    destruct h as [w1 h];
    destruct h as [w2 h];
    destruct h as [c1 h];
    destruct h as [c2 h]
  end.

Lemma implies_alphaeqc_substc3 {o} :
  forall v (t : @CTerm o) w x u1 u2,
    alphaeqcv [w,v,x] u1 u2
    -> alphaeqcv [w,v] (substc3 w v t x u1) (substc3 w v t x u2).
Proof.
  introv aeq.
  destruct_cterms.
  allunfold @alphaeqcv; allsimpl.
  apply lsubst_alpha_congr2; auto.
Qed.

Lemma substc3_fun {o} :
  forall z v x (w : @CTerm o) (t u : CVTerm [z,v,x]),
    alphaeqcv
      [z,v]
      (substc3 z v w x (mkcv_fun [z,v,x] t u))
      (mkcv_fun [z,v] (substc3 z v w x t) (substc3 z v w x u)).
Proof.
  introv.
  destruct_cterms.
  unfold alphaeqcv; simpl.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).

  simpl.
  autorewrite with slow.

  unfold mk_fun; simpl.

  remember (newvar x1) as nv1.
  pose proof (newvar_prop x1) as p1.
  rewrite <- Heqnv1 in p1.

  remember (newvar (lsubst_aux x1 [(x, x0)])) as nv2.
  pose proof (newvar_prop (lsubst_aux x1 [(x, x0)])) as p2.
  rewrite <- Heqnv2 in p2.

  unfold mk_function, nobnd.
  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (all_vars (lsubst_aux x1 (if beq_var x nv1 then [] else [(x, x0)])) ++
       all_vars (lsubst_aux x1 [(x, x0)]))) as fv.
  exrepnd.

  apply (al_bterm_aux [v0]); auto.
  {
    apply disjoint_singleton_l; auto.
  }

  assert (!LIn nv1 (free_vars (lsubst_aux x1 [(x,x0)]))) as ni1.
  {
    introv h.
    apply free_vars_lsubst_aux_subset in h.
    rewrite sub_free_vars_if_cl_sub in h; eauto 3 with slow.
    autorewrite with slow in h.
    apply in_remove_nvars in h; sp.
  }

  simpl.
  remember (beq_var x nv1) as b1.
  destruct b1; simpl; autorewrite with slow in *.

  {
    apply beq_var_true in Heqb1.
    subst x.
    unfold var_ren; simpl.
    rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v0)]);
      [|simpl;apply disjoint_singleton_r; auto];[].
    rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
      [|simpl;apply disjoint_singleton_r; auto];[].
    rewrite (lsubst_aux_trivial_cl_term _ [(nv1,x0)]);
      [|simpl;apply disjoint_singleton_r; auto];[].
    eauto 3 with slow.
  }

  {
    unfold var_ren; simpl.
    rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
      [|simpl;apply disjoint_singleton_r; auto];[].
    rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v0)]);
      [|simpl;apply disjoint_singleton_r; auto];[].
    eauto 3 with slow.
  }
Qed.

Lemma entry_add_const_extends {o} :
  forall name n k (restr : @ChoiceSeqRestriction o) t,
    entry_extends
      (lib_cs name (MkChoiceSeqEntry _ (ntimes (n + k) t) restr))
      (lib_cs name (MkChoiceSeqEntry _ (ntimes n t) restr)).
Proof.
  introv.
  unfold entry_extends; simpl.
  dands; auto.
  unfold choice_sequence_entry_extend; simpl; dands; eauto 3 with slow.
  unfold choice_sequence_vals_extend.
  exists (ntimes k t); auto.
  rewrite ntimes_plus; auto.
Qed.
Hint Resolve entry_add_const_extends : slow.

Lemma extend_bool_choice_sequence_zero {o} :
  forall (lib : @library o) name n restr k,
    csn_kind name = cs_kind_seq []
    -> same_restrictions restr (csc_seq [])
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)) lib
    -> exists lib',
        map entry2name lib' = map entry2name lib
        /\ lib_extends lib' lib
        /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes (n + k) mkc_zero) restr)) lib'.
Proof.
  induction lib using rev_list_ind; introv csk same i; simpl in *; tcsp.
  apply entry_in_library_snoc_implies in i.
  repndors; repnd; subst.

  - pose proof (IHlib name n restr k) as IHlib.
    repeat (autodimp IHlib hyp); exrepnd; eauto 3 with slow.
    exists (snoc lib' a); dands; eauto 3 with slow.

    { allrw map_snoc; allrw; auto. }

    { apply implies_lib_extends_snoc_lr_same_names; auto. }

  - exists (snoc lib (lib_cs name (MkChoiceSeqEntry _ (ntimes (n + k) mkc_zero) restr))); simpl; dands; tcsp; eauto 3 with slow.

    { allrw map_snoc; allrw; auto. }

    { apply implies_lib_extends_snoc; eauto 3 with slow. }
Qed.

Lemma member_exists_1_choice {o} :
  forall (lib : @library o) name v n restr,
    csn_kind name = cs_kind_seq []
    -> same_restrictions restr (csc_seq [])
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero ++ [mkc_one]) restr)) lib
    -> safe_library lib
    -> member lib (mkc_pair (mkc_nat n) mkc_axiom) (exists_1_choice name v).
Proof.
  introv ck srestr ilib safe.
  unfold exists_1_choice, mkc_exists.
  apply member_product2; dands.

  {
    apply tequality_product; dands; eauto 3 with slow.
    introv xt ea; autorewrite with slow.
    apply equality_int_nat_implies_cequivc in ea.
    apply tequality_mkc_equality2_sp; dands; eauto 3 with slow.
    apply ccequivc_ext_bar_iff_ccequivc_bar in ea.
    unfold ccequivc_ext_bar in ea.
    split; unfold equorsq_bar;
      [eapply all_in_ex_bar_modus_ponens1;[|exact ea]
      |eapply all_in_ex_bar_modus_ponens1;[|exact ea] ];
      clear ea; introv y ea; exrepnd; spcast; right; eauto 3 with slow.
  }

  apply in_ext_implies_all_in_ex_bar; introv xt.
  exists (@mkc_nat o n) (@mkc_axiom o).
  dands; spcast; eauto 3 with slow;[].
  autorewrite with slow.
  rw <- @member_equality_iff.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply computes_to_valc_implies_ccequivc_ext;
     apply (implies_compute_to_valc_apply_choice_seq _ _ _ n mkc_one);
     eauto 3 with slow|];
    [|repeat rewrite mkc_one_eq; eauto 3 with slow];[].

  eapply lib_extends_preserves_find_cs_value_at;[eauto|].
  apply entry_in_library_implies_find_cs_some in ilib.
  unfold find_cs_value_at; allrw; simpl.
  rewrite find_value_of_cs_at_is_select.
  rewrite select_app_r; autorewrite with slow; simpl; auto.
Qed.

Lemma substc3_mkcv_apply {o} :
  forall n u v (t : @CTerm o) a b,
    substc3 n u t v (mkcv_apply [n, u, v] a b)
    = mkcv_apply [n, u] (substc3 n u t v a) (substc3 n u t v b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc3_mkcv_apply : slow.

Lemma lsubstc_vars_mk_var_as_mkcv3_2 {o} :
  forall (v v' v'' : NVar)
         (w : @wf_term o (mk_var v'))
         (s : CSubstitution)
         (c : cover_vars_upto (mk_var v') s [v'', v', v]),
    !LIn v' (dom_csub s)
    -> lsubstc_vars (mk_var v') w s [v'', v', v] c = mk_cv_app_l [v''] [v',v] (mk_cv_app_r [v] [v'] (mkc_var v')).
Proof.
  introv ni.
  apply cvterm_eq; simpl.
  apply csubst_var_not_in; auto.
Qed.

Lemma substc3_mk_cv_app_l_2 {o} :
  forall n u v (t : @CTerm o) x,
    substc3 n u t v (mk_cv_app_l [n] [u, v] x)
    = mk_cv_app_l [n] [u] (substc2 u t v x).
Proof.
  introv; destruct_cterms; apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc3_mk_cv_app_l_2 : slow.

Lemma substc3_mk_cv_app_r_2 {o} :
  forall n u v (t : @CTerm o) x,
    v <> n
    -> substc3 n u t v (mk_cv_app_r [u,v] [n] x)
       = mk_cv_app_r [u] [n] x.
Proof.
  introv d; destruct_cterms; apply cvterm_eq; simpl; auto.
  apply cl_subst_trivial; eauto 3 with slow.
  apply isprog_vars_eq in i0; repnd.
  apply subvars_eq in i1; intro xx; apply i1 in xx; simpl in *; repndors; subst; tcsp.
Qed.

Lemma implies_ccequivc_ext_equality {o} :
  forall lib (f g a b u v : @CTerm o),
    ccequivc_ext lib f g
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib (mkc_equality f a u) (mkc_equality g b v).
Proof.
  introv ceqa ceqb ceqc x.
  pose proof (ceqa _ x) as ceqa.
  pose proof (ceqb _ x) as ceqb.
  pose proof (ceqc _ x) as ceqc.
  simpl in *; spcast.
  apply cequivc_decomp_equality; dands; auto.
Qed.
Hint Resolve implies_ccequivc_ext_equality : slow.

Lemma equality_exists_1_choice_fun_in_fun {o} :
  forall (lib : @library o) name v i,
    equality
      lib
      (exists_1_choice_fun name v)
      (exists_1_choice_fun name v)
      (mkc_fun mkc_tnat (mkc_uni i)).
Proof.
  introv.
  apply equality_in_fun; dands; eauto 3 with slow;[].
  introv xt en.
  unfold exists_1_choice_fun.

  eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym; apply ccequivc_ext_beta|].
  eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym; apply ccequivc_ext_beta|].
  autorewrite with slow.

  apply equality_mkc_equality2_sp_in_uni; dands; eauto 3 with slow;[].
  apply equality_int_nat_implies_cequivc in en.
  apply ccequivc_ext_bar_iff_ccequivc_bar in en.
  unfold ccequivc_ext_bar in en.

  split; unfold equorsq_bar;
    [eapply all_in_ex_bar_modus_ponens1;[|exact en]
    |eapply all_in_ex_bar_modus_ponens1;[|exact en] ];
    clear en; introv y en; exrepnd; spcast; right; eauto 3 with slow.
Qed.
Hint Resolve equality_exists_1_choice_fun_in_fun : slow.

Lemma type_exists_1_choice {o} :
  forall (lib : @library o) name v,
    type lib (exists_1_choice name v).
Proof.
  introv; unfold exists_1_choice, mkc_exists.
  apply tequality_product; dands; eauto 3 with slow.
  introv xt ea; autorewrite with slow.
  apply equality_int_nat_implies_cequivc in ea.
  apply tequality_mkc_equality2_sp; dands; eauto 3 with slow.
  apply ccequivc_ext_bar_iff_ccequivc_bar in ea.
  unfold ccequivc_ext_bar in ea.
  split; unfold equorsq_bar;
    [eapply all_in_ex_bar_modus_ponens1;[|exact ea]
    |eapply all_in_ex_bar_modus_ponens1;[|exact ea] ];
    clear ea; introv y ea; exrepnd; spcast; right; eauto 3 with slow.
Qed.
Hint Resolve type_exists_1_choice : slow.



Definition IP {o} (A B n : NVar) (i : nat) : @NTerm o :=
  mk_all
    (mk_uni i)
    A
    (mk_all
       (mk_fun mk_tnat (mk_uni i))
       B
       (mk_fun
          (mk_fun (mk_var A) (mk_exists mk_tnat n (mk_apply (mk_var B) (mk_var n))))
          (mk_exists mk_tnat n (mk_fun (mk_var A) (mk_apply (mk_var B) (mk_var n)))))).


(* end hide*)

(**

<<
   H |- not IP ext Ax

     By notIP

>>

 *)

Definition rule_not_IP {o}
           (A B n : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_not (IP A B n i))))
    []
    [].

Lemma rule_not_IP_true {o} :
  forall lib (A B n : NVar) (i : nat) (H : @bhyps o) (safe : safe_library lib)
         (d1 : A <> B) (d2 : B <> n) (d3 : A <> n),
    rule_true lib (rule_not_IP A B n i H).
Proof.
  unfold rule_not_IP, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs hyps.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  unfold IP, mk_all.
  lsubst_tac.
  rw @tequality_not.
  rw @equality_in_not.
  rw @tequality_function.

  hide_wf.
  dands; eauto 3 with slow.

  {
    introv xt eu.
    clear dependent lib.
    clear dependent lib'.
    rename lib'0 into lib.

    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.
    repeat (rewrite substc_mkcv_function; tcsp;[]).
    apply tequality_function; dands; eauto 3 with slow; autorewrite with slow.

    { lsubst_tac; autorewrite with slow.
      apply tequality_fun; dands; eauto 3 with slow. }

    introv xt eb.
    repeat rewrite substcv_as_substc2.
    autorewrite with slow in *.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;exact aeq
      |clear aeq].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    apply tequality_sym.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;exact aeq
      |clear aeq].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    eapply equality_monotone in eu;[|eauto].
    clear dependent lib.
    rename lib' into lib.

    apply tequality_fun.
    dands.

    {
      autorewrite with slow in *.

      aeq_lsubstc_vars_not aeq.
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply implies_alphaeqc_substc2;exact aeq
        |clear aeq].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply substc2_fun|].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply mkcv_fun_substc|].

      apply tequality_sym.

      aeq_lsubstc_vars_not aeq.
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply implies_alphaeqc_substc2;exact aeq
        |clear aeq].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply substc2_fun|].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply mkcv_fun_substc|].

      apply tequality_fun.
      dands.

      {
        rewrite lsubstc_vars_mk_var_as_mkcv2;
          [|repeat rewrite dom_csub_csub_filter; intro xx;
            apply in_remove_nvars in xx; simpl in xx; repnd;
            apply in_remove_nvars in xx0; simpl in xx0; repnd;
            apply not_over_or in xx0; repnd; tcsp];[].
        rewrite lsubstc_vars_mk_var_as_mkcv2;
          [|repeat rewrite dom_csub_csub_filter; intro xx;
            apply in_remove_nvars in xx; simpl in xx; repnd;
            apply in_remove_nvars in xx0; simpl in xx0; repnd;
            apply not_over_or in xx0; repnd; tcsp];[].
        autorewrite with slow; eauto 3 with slow.
      }

      introv xt inh.
      hide_wf.
      unfold mk_exists.
      repeat lsubstc_vars_as_mkcv.

      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
      repeat (rewrite mkcv_product_substc; tcsp;[]).
      autorewrite with slow.
      apply tequality_product; dands; eauto 3 with slow;[].

      introv xt' en.
      autorewrite with slow.

      repeat (rewrite lsubstc_vars_mk_var_as_mkcv3_2;
              [|repeat rewrite dom_csub_csub_filter;
                repeat rw in_remove_nvars; simpl;
                intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.
      repeat (rewrite substc3_mk_cv_app_r_2; tcsp;[]).
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.

      lsubst_tac.
      autorewrite with slow in *.
      apply equality_in_fun in eb; repnd.
      clear eb0 eb1.
      apply eb in en; eauto 3 with slow.
    }

    introv xt inh.
    clear inh.
    unfold mk_exists.
    repeat lsubstc_vars_as_mkcv.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
    repeat (rewrite mkcv_product_substc; tcsp;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow;[].

    introv xt' en.
    autorewrite with slow.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply implies_alphaeqc_substc3;exact aeq
      |clear aeq].
    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply implies_alphaeqc_substc3;exact aeq
      |clear aeq].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply substc3_fun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply substc3_fun|].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    repeat (rewrite lsubstc_vars_mk_var_as_mkcv3;
            [|repeat rewrite dom_csub_csub_filter;
              repeat rw in_remove_nvars; simpl;
              intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
    autorewrite with slow.
    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.

    repeat (rewrite lsubstc_vars_mk_var_as_mkcv3_2;
            [|repeat rewrite dom_csub_csub_filter;
              repeat rw in_remove_nvars; simpl;
              intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
    autorewrite with slow.
    repeat (rewrite substc3_mk_cv_app_r_2; tcsp;[]).
    repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
    autorewrite with slow.

    apply tequality_sym.

    assert (lib_extends lib'0 lib) as xt'' by eauto 3 with slow.
    apply tequality_fun; dands; eauto 3 with slow;[].

    introv xt''' inh.

    assert (lib_extends lib'1 lib) as xt'''' by eauto 3 with slow.

    lsubst_tac.
    autorewrite with slow in *.
    apply equality_in_fun in eb; repnd.
    clear eb0 eb1.
    apply equality_sym in en.
    apply eb in en; eauto 3 with slow.
  }

  {
    apply tequality_function; dands; eauto 3 with slow; autorewrite with slow;[].

    introv xtu eu.
    repeat rewrite substcv_as_substc2.
    autorewrite with slow in *.

    repeat lsubstc_vars_as_mkcv.
    repeat (rewrite substc_mkcv_function; tcsp;[]).
    autorewrite with slow.
    apply tequality_function.
    lsubst_tac; autorewrite with slow.
    dands;[apply tequality_fun; dands; eauto 3 with slow|];[].

    hide_wf.

    introv xt ef.
    lsubst_tac; autorewrite with slow in *.
    repeat rewrite substcv_as_substc2.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;exact aeq
      |clear aeq].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    apply tequality_sym.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;exact aeq
      |clear aeq].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    apply tequality_sym.

    eapply equality_monotone in eu;[|eauto].
    clear dependent lib.
    clear dependent lib'0.
    rename lib'1 into lib.

    apply tequality_fun.
    dands.

    {
      autorewrite with slow in *.

      aeq_lsubstc_vars_not aeq.
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply implies_alphaeqc_substc2;exact aeq
        |clear aeq].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply substc2_fun|].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply mkcv_fun_substc|].

      apply tequality_sym.

      aeq_lsubstc_vars_not aeq.
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply implies_alphaeqc_substc2;exact aeq
        |clear aeq].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply substc_alphaeqcv;
         apply substc2_fun|].
      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply mkcv_fun_substc|].

      apply tequality_sym.

      apply tequality_fun.
      dands.

      {
        rewrite lsubstc_vars_mk_var_as_mkcv2;
          [|repeat rewrite dom_csub_csub_filter; intro xx;
            apply in_remove_nvars in xx; simpl in xx; repnd;
            apply in_remove_nvars in xx0; simpl in xx0; repnd;
            apply not_over_or in xx0; repnd; tcsp];[].
        rewrite lsubstc_vars_mk_var_as_mkcv2;
          [|repeat rewrite dom_csub_csub_filter; intro xx;
            apply in_remove_nvars in xx; simpl in xx; repnd;
            apply in_remove_nvars in xx0; simpl in xx0; repnd;
            apply not_over_or in xx0; repnd; tcsp];[].
        autorewrite with slow; eauto 3 with slow.
      }

      introv xt inh.
      hide_wf.
      unfold mk_exists.
      repeat lsubstc_vars_as_mkcv.

      eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
      repeat (rewrite mkcv_product_substc; tcsp;[]).
      autorewrite with slow.
      apply tequality_product; dands; eauto 3 with slow;[].

      introv xt' en.
      autorewrite with slow.

      repeat (rewrite lsubstc_vars_mk_var_as_mkcv3_2;
              [|repeat rewrite dom_csub_csub_filter;
                repeat rw in_remove_nvars; simpl;
                intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.
      repeat (rewrite substc3_mk_cv_app_r_2; tcsp;[]).
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.

      lsubst_tac.
      autorewrite with slow in *.
      apply equality_in_fun in ef; repnd.
      clear ef0 ef1.
      apply ef in en; eauto 3 with slow.
    }

    introv xt inh.
    clear inh.
    unfold mk_exists.
    repeat lsubstc_vars_as_mkcv.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
    repeat (rewrite mkcv_product_substc; tcsp;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow;[].

    introv xt' en.
    autorewrite with slow.

    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply implies_alphaeqc_substc3;exact aeq
      |clear aeq].
    aeq_lsubstc_vars_not aeq.
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply implies_alphaeqc_substc3;exact aeq
      |clear aeq].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply substc3_fun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;
       apply substc3_fun|].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym;apply substc_alphaeqcv;
       apply substc2_fun|].

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].

    repeat (rewrite lsubstc_vars_mk_var_as_mkcv3;
            [|repeat rewrite dom_csub_csub_filter;
              repeat rw in_remove_nvars; simpl;
              intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
    autorewrite with slow.
    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.

    repeat (rewrite lsubstc_vars_mk_var_as_mkcv3_2;
            [|repeat rewrite dom_csub_csub_filter;
              repeat rw in_remove_nvars; simpl;
              intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
    autorewrite with slow.
    repeat (rewrite substc3_mk_cv_app_r_2; tcsp;[]).
    repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
    autorewrite with slow.

    assert (lib_extends lib'0 lib) as xt1' by eauto 3 with slow.
    assert (lib_extends lib'1 lib) as xt2' by eauto 3 with slow.
    apply tequality_fun; dands; eauto 3 with slow;[].

    introv xt''' inh.

    assert (lib_extends lib'2 lib) as xt'''' by eauto 3 with slow.

    lsubst_tac.
    autorewrite with slow in *.
    apply equality_in_fun in ef; repnd.
    clear ef0 ef1.
    apply ef in en; eauto 3 with slow.
  }

  introv ext' inh.
  rw @inhabited_function in inh; exrepnd.
  clear inh0 inh1.

  assert (safe_library lib'0) as safe' by eauto 3 with slow.

  (* WARNING *)
  clear lib lib' ext sim eqh ext' safe.
  rename lib'0 into lib.
  rename safe' into safe.


  pose proof (fresh_choice_seq_name_in_library lib []) as w; exrepnd.
  assert (is_primitive_kind name) as isn by (eauto 3 with slow).

  pose proof (inh2 (choice_sequence_name2entry name :: lib)) as q.
  clear inh2.
  autodimp q hyp; eauto 3 with slow;[].

  pose proof (q (exists_1_choice name nvarx) (exists_1_choice name nvarx)) as q.
  autodimp q hyp.

  {
    unfold exists_1_choice.
    apply equality_product; dands; eauto 3 with slow.
    introv ext ea.
    autorewrite with slow.

    apply equality_int_nat_implies_cequivc in ea.
    apply ccequivc_ext_bar_iff_ccequivc_bar in ea.
    apply all_in_ex_bar_equality_implies_equality.
    eapply all_in_ex_bar_modus_ponens1;[|exact ea]; clear ea; introv y ea; exrepnd; spcast.

    apply equality_mkc_equality2_sp_in_uni; dands; eauto 3 with slow.
    split; exists (trivial_bar lib'0); apply in_ext_implies_all_in_bar_trivial_bar;
      introv ext'; right; eauto 3 with slow.
  }

  repeat lsubstc_vars_as_mkcv.
  autorewrite with slow in q.
  rewrite substc_mkcv_function in q; tcsp;[].
  apply equality_in_function2 in q; repnd.

  clear q0.
  hide_wf.

  remember (choice_sequence_name2entry name :: lib) as lib'.
  assert (entry_in_library (choice_sequence_name2entry name) lib') as eil by (subst; tcsp).
  assert (safe_library lib') as safe' by (subst; eauto 3 with slow).

  clear lib w4 Heqlib' safe.
  rename lib' into lib.
  rename safe' into safe.

  pose proof (q _ (lib_extends_refl _)) as q.

  pose proof (q (exists_1_choice_fun name nvarx) (exists_1_choice_fun name nvarx)) as q.
  autodimp q hyp.

  {
    autorewrite with slow.
    lsubst_tac; autorewrite with slow; eauto 3 with slow.
  }

  repeat rewrite substcv_as_substc2 in q.
  autorewrite with slow in *.

  aeq_lsubstc_vars_not aeq.
  eapply alphaeqc_preserving_equality in q;
    [clear aeq
    |apply substc_alphaeqcv;
     apply implies_alphaeqc_substc2;exact aeq].
  eapply alphaeqc_preserving_equality in q;
    [|apply substc_alphaeqcv;
      apply substc2_fun].
  eapply alphaeqc_preserving_equality in q;
    [|apply mkcv_fun_substc].

  apply equality_in_fun in q; repnd.
  clear q0 q1.

  pose proof (q _ (lib_extends_refl _) mkc_id mkc_id) as q.
  autodimp q hyp.

  {
    aeq_lsubstc_vars_not aeq.
    eapply alphaeqc_preserving_equality;
      [clear aeq
      |apply alphaeqc_sym; apply substc_alphaeqcv;
       apply implies_alphaeqc_substc2;exact aeq].
    eapply alphaeqc_preserving_equality;
      [|apply alphaeqc_sym; apply substc_alphaeqcv;
        apply substc2_fun].
    eapply alphaeqc_preserving_equality;
      [|apply alphaeqc_sym; apply mkcv_fun_substc].

    apply equality_in_fun; dands.

    {
      rewrite lsubstc_vars_mk_var_as_mkcv2;
        [|repeat rewrite dom_csub_csub_filter; intro xx;
          apply in_remove_nvars in xx; simpl in xx; repnd;
          apply in_remove_nvars in xx0; simpl in xx0; repnd;
          apply not_over_or in xx0; repnd; tcsp];[].
      autorewrite with slow; eauto 3 with slow.
    }

    {
      introv xt inh.
      unfold mk_exists.
      repeat lsubstc_vars_as_mkcv.

      eapply type_respects_alphaeqc;
        [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;tcsp|].
      repeat (rewrite mkcv_product_substc; tcsp;[]).
      autorewrite with slow.
      apply tequality_product; dands; eauto 3 with slow;[].

      introv xt' en.
      autorewrite with slow.

      repeat (rewrite lsubstc_vars_mk_var_as_mkcv3_2;
              [|repeat rewrite dom_csub_csub_filter;
                repeat rw in_remove_nvars; simpl;
                intro xx; repnd; allrw not_over_or; repnd; tcsp];[]).
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.
      repeat (rewrite substc3_mk_cv_app_r_2; tcsp;[]).
      repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
      autorewrite with slow.

      lsubst_tac.
      autorewrite with slow in *.

      unfold exists_1_choice_fun.

      eapply tequality_respects_cequivc_left;[apply ccequivc_ext_sym; apply ccequivc_ext_beta|].
      eapply tequality_respects_cequivc_right;[apply ccequivc_ext_sym; apply ccequivc_ext_beta|].
      autorewrite with slow.

      apply tequality_mkc_equality2_sp; dands; eauto 3 with slow;[].
      apply equality_int_nat_implies_cequivc in en.
      apply ccequivc_ext_bar_iff_ccequivc_bar in en.
      unfold ccequivc_ext_bar in en.

      split; unfold equorsq_bar;
        [eapply all_in_ex_bar_modus_ponens1;[|exact en]
        |eapply all_in_ex_bar_modus_ponens1;[|exact en] ];
        clear en; introv y en; exrepnd; spcast; right; eauto 3 with slow.
    }

    introv xt ea.

    eapply equality_respects_cequivc_left;
      [apply ccequivc_ext_sym; introv xt'; spcast; apply cequivc_apply_id|].
    eapply equality_respects_cequivc_right;
      [apply ccequivc_ext_sym; introv xt'; spcast; apply cequivc_apply_id|].

    eapply cequivc_preserving_equality;[eauto|].
    introv xt'; spcast.

    rewrite lsubstc_vars_mk_var_as_mkcv2;
      [|repeat rewrite dom_csub_csub_filter; intro xx;
        apply in_remove_nvars in xx; simpl in xx; repnd;
        apply in_remove_nvars in xx0; simpl in xx0; repnd;
        apply not_over_or in xx0; repnd; tcsp];[].
    autorewrite with slow.

    apply cequivc_exists_1_choice_sub; auto.
  }

  (* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
  (* we don't care about the extract *)
  remember (mkc_apply
              (mkc_apply (mkc_apply f (exists_1_choice name nvarx))
                         (exists_1_choice_fun name nvarx)) mkc_id) as ext; clear Heqext.

  unfold mk_exists in q.

  aeq_lsubstc_vars_prod aeq; rewrite aeq in q; clear aeq.
  eapply alphaeqc_preserving_equality in q;
    [|apply substc_alphaeqcv;
      apply substc2_product;tcsp].
  rewrite mkcv_product_substc in q; tcsp;[].
  apply inhabited_type_if_equality in q.
  apply inhabited_product in q; repnd.
  clear q0 q1.
  exrepnd.
  rename q0 into q.
  autorewrite with slow in q.

  unfold all_in_ex_bar in q; exrepnd.

  assert (exists m restr lib',
             lib_extends lib' lib
             /\ bar_lib_bar bar lib'
             /\ same_restrictions restr (csc_seq [])
             /\ entry_in_library
                  (lib_cs name (MkChoiceSeqEntry _ (ntimes m mkc_zero) restr))
                  lib') as blib.
  {
    pose proof (fresh_choice_seq_name_in_library lib []) as h; exrepnd.
    pose proof (bar_lib_bars bar (library2inf lib (simple_inf_choice_seq name0))) as q.
    autodimp q hyp; eauto 3 with slow;[].
    exrepnd.
    applydup q3 in eil.

    apply entry_in_library_extends_implies_entry_in_library in eil0; exrepnd.
    assert (safe_library_entry entry') as safe' by eauto 3 with slow.

    assert (name <> name0) as dname.
    { introv xx; subst name0.
      apply entry_in_library_implies_find_cs_some in eil.
      rewrite eil in *; ginv. }

    pose proof (entry_extends_choice_sequence_name2entry_implies lib name name0 lib' entry') as q.
    repeat (autodimp q hyp);[].
    exrepnd; subst.
    exists n0 restr lib'; dands; auto.
  }

  exrepnd.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  pose proof (q0 _ blib2 _ (lib_extends_refl lib')) as q0.
  cbv beta in q0.

  exrepnd.
  clear dependent t.

  aeq_lsubstc_vars_not aeq.
  eapply alphaeqc_preserving_equality in q0;
    [clear aeq
    |apply substc_alphaeqcv;
     apply implies_alphaeqc_substc2;
     apply implies_alphaeqc_substc3;exact aeq].
  eapply alphaeqc_preserving_equality in q0;
    [|apply substc_alphaeqcv;
      apply implies_alphaeqc_substc2;
      apply substc3_fun].
  eapply alphaeqc_preserving_equality in q0;
    [|apply substc_alphaeqcv;
      apply substc2_fun].
  eapply alphaeqc_preserving_equality in q0;
    [|apply mkcv_fun_substc].

  apply member_tnat_iff in q2.
  unfold all_in_ex_bar in q2; exrepnd.

  clear dependent lib.
  rename lib' into lib.
  rename bar0 into bar.
  rename safe' into safe.

  assert (exists m restr lib',
             lib_extends lib' lib
             /\ bar_lib_bar bar lib'
             /\ same_restrictions restr (csc_seq [])
             /\ entry_in_library
                  (lib_cs name (MkChoiceSeqEntry _ (ntimes m mkc_zero) restr))
                  lib') as blib.
  {
    pose proof (fresh_choice_seq_name_in_library lib []) as h; exrepnd.
    pose proof (bar_lib_bars bar (library2inf lib (simple_inf_choice_seq name0))) as q.
    autodimp q hyp; eauto 3 with slow;[].
    exrepnd.

    applydup q4 in blib0.

    apply entry_in_library_extends_implies_entry_in_library in blib1; exrepnd.
    assert (safe_library_entry entry') as safe' by eauto 3 with slow.

    assert (name <> name0) as dname.
    { introv xx; subst name0.
      apply entry_in_library_implies_find_cs_some in blib0.
      rewrite blib0 in *; ginv. }

    pose proof (entry_extends_cs_zeros_implies lib name name0 m restr lib' entry') as q.
    repeat (autodimp q hyp);[].
    exrepnd; subst.
    exists n0 restr0 lib'; dands; auto.
  }

  clear m blib0.
  exrepnd.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  pose proof (q1 _ blib2 _ (lib_extends_refl lib')) as q1.
  cbv beta in q1.
  exrepnd; spcast.

  eapply equality_monotone in q0;[|eauto];[].

  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.

  apply equality_in_fun in q0; repnd.
  clear q1 q3.

  pose proof (extend_bool_choice_sequence_zero lib name m restr0 (S k)) as q.
  repeat (autodimp q hyp);[].
  exrepnd.

  assert (k < m + S k) as ltk by omega.
  remember (m + S k) as m'; clear Heqm'.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  eapply lib_extends_preserves_computes_to_valc in q2;[|eauto];[].

  pose proof (entry_cs_zeros_implies_exists_extension_with_one lib' name m' restr0) as q.
  repeat (autodimp q hyp);[].
  exrepnd.
  assert (safe_library lib'0) as safe'' by eauto 3 with slow.
  eapply lib_extends_preserves_computes_to_valc in q2;[|eauto];[].
  assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.

  pose proof (q0 _ xt) as q0.
  clear dependent lib.
  clear dependent lib'.
  rename lib'0 into lib.
  rename safe'' into safe.
  clear dependent m.
  rename m' into m.

  pose proof (q0 (mkc_pair (mkc_nat m) mkc_axiom) (mkc_pair (mkc_nat m) mkc_axiom)) as q0.
  autodimp q0 hyp.

  {
    rewrite lsubstc_vars_mk_var_as_mkcv3;
      [|repeat rewrite dom_csub_csub_filter;
        repeat rw in_remove_nvars; simpl;
        intro xx; repnd; allrw not_over_or; repnd; tcsp];[].
    autorewrite with slow.
    eapply member_exists_1_choice; eauto.
  }

  repeat lsubstc_vars_as_mkcv.
  rewrite substc3_mkcv_apply in q0.
  rewrite substc2_apply in q0.
  autorewrite with slow in q0.
  rewrite lsubstc_vars_mk_var_as_mkcv3_2 in q0;
    [|repeat rewrite dom_csub_csub_filter;
      repeat rw in_remove_nvars; simpl;
      intro xx; repnd; allrw not_over_or; repnd; tcsp];[].
  autorewrite with slow in q0.
  rewrite substc2_mk_cv_app_r in q0; tcsp;[].
  autorewrite with slow in q0.
  rewrite substc3_mk_cv_app_r_2 in q0; tcsp;[].
  rewrite substc2_mk_cv_app_r in q0; tcsp;[].
  autorewrite with slow in q0.

  unfold exists_1_choice_fun in q0.
  eapply cequivc_preserving_equality in q0;[|apply ccequivc_ext_beta].
  autorewrite with slow in q0.
  apply inhabited_type_if_equality in q0.

  eapply inhabited_type_cequivc in q0;
    [|apply implies_ccequivc_ext_equality;
      [|apply ccequivc_ext_refl|apply ccequivc_ext_refl];
      apply computes_to_valc_implies_ccequivc_ext;
      apply (implies_compute_to_valc_apply_choice_seq _ _ _ k mkc_zero);
      eauto 3 with slow;
      apply entry_in_library_implies_find_cs_some in q5;
      unfold find_cs_value_at; allrw; simpl;
      rewrite find_value_of_cs_at_is_select;
      rewrite select_app_l; autorewrite with slow; simpl; auto;
      rewrite select_ntimes; boolvar; tcsp];[].

  apply inhabited_mkc_equality in q0.
  apply equality_int_nat_implies_cequivc in q0.
  apply (all_in_ex_bar_implies_exists_lib_extends (lib_extends_refl lib)) in q0; exrepnd; spcast.
  apply cequivc_nat_implies_computes_to_valc in q1.
  apply computes_to_valc_isvalue_eq in q1; eauto 3 with slow;[].
  inversion q1.
Qed.
