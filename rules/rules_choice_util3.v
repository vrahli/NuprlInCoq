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
  rewrite ntimes_plus; eauto.
Qed.
Hint Resolve entry_add_const_extends : slow.

Lemma same_csc_seq_nil_implies_correct_restriction {o} :
  forall name (restr : @ChoiceSeqRestriction o),
    csn_kind name = cs_kind_seq []
    -> same_restrictions restr (csc_seq [])
    -> correct_restriction name restr.
Proof.
  introv cor same.
  destruct restr, name as [name kind]; simpl in *; repnd; subst; simpl in *;
    unfold correct_restriction; simpl in *; dands; tcsp.
  { introv len; rewrite same; unfold natSeq2restrictionPred; autorewrite with slow; tcsp. }
Qed.
Hint Resolve same_csc_seq_nil_implies_correct_restriction : slow.

Lemma extend_bool_choice_sequence_zero {o} :
  forall (lib : @library o) name n restr k,
    lib_cond_sat_def lib
    -> csn_kind name = cs_kind_seq []
    -> same_restrictions restr (csc_seq [])
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes n mkc_zero) restr)) lib
    -> exists (lib' : library),
        lib_names lib' = lib_names lib
        /\ lib_extends lib' lib
        /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (ntimes (n + k) mkc_zero) restr)) lib'.
Proof.
  introv sat cor same i.
  apply entry_in_library_split in i; exrepnd; subst.
  destruct lib as [lib cond]; simpl in *; subst.
  exists (add_mid_entry (MkLib lib1 cond) (lib_cs name (MkChoiceSeqEntry _ (ntimes (n + k) mkc_zero) restr)) (MkLib lib2 cond)).
  dands; tcsp.

  { unfold lib_names, add_mid_entry; simpl; repeat (rewrite map_app; simpl); tcsp. }

  { apply lib_extends_middle; simpl; dands; eauto 3 with slow;
      try (complete (introv i; apply in_ntimes in i; subst; apply sat)).
    destruct restr; simpl in *; repnd; tcsp.
    introv sel.
    rewrite select_ntimes in sel; boolvar; ginv.
    apply same; eauto 3 with slow.
    unfold natSeq2restrictionPred; autorewrite with slow; eauto 3 with slow. }

  apply implies_entry_in_library_app_right; simpl; tcsp.
  introv i m; simpl in *.
  unfold matching_entries in m; simpl in *.
  destruct i1; unfold in_lib.
  exists e'; dands; tcsp; apply LIn_implies_In; auto.
Qed.

Hint Rewrite length_app : nat.

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
    [apply ccequivc_ext_sym;apply ccomputes_to_valc_ext_implies_ccequivc_ext|];
    [|repeat rewrite mkc_one_eq; eauto 3 with slow];[].

  apply (implies_ccomputes_to_valc_ext_apply_cs lib lib' name (mkc_nat n) n 1); eauto 3 with slow.
  apply entry_in_library_implies_find_cs_some in ilib.
  unfold find_cs_value_at; allrw; simpl.
  eapply lib_extends_preserves_find_cs in ilib; eauto; exrepnd.
  allrw; simpl in *.
  rewrite find_value_of_cs_at_is_select.
  unfold choice_sequence_vals_extend in *; exrepnd; subst.
  rewrite select_app_l; autorewrite with slow nat; simpl; try omega;[].
  rewrite select_app_r; autorewrite with slow; simpl; auto.
  rewrite mkc_one_eq; auto.
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
