(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University
  Copyright 2019 Cornell University

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


Require Export per_props_qtime_nat.
Require Export per_props_qnat.
Require Export rules_choice_util4.

Require Export List.
Require Export list.


Lemma isprog_vars_qtime {p} :
  forall (a : @NTerm p) vs,
    isprog_vars vs (mk_qtime a) <=> isprog_vars vs a.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  allrw <- @wf_term_eq.
  allrw @wf_qtime; split; sp.
Qed.

Lemma isprog_vars_qtime_implies {p} :
  forall (a : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs (mk_qtime a).
Proof.
  introv ispa.
  apply isprog_vars_qtime; sp.
Qed.

Definition mkcv_qtime {o} vs (t : @CVTerm o vs) : CVTerm vs :=
  let (a,x) := t in
  exist (isprog_vars vs) (mk_qtime a) (isprog_vars_qtime_implies a vs x).

Definition mkcv_qtnat {o} vs : @CVTerm o vs :=
  mkcv_qtime _ (mkcv_tnat _).

Lemma isprog_vars_qnat_implies {o} :
  forall vs c, @isprog_vars o vs (mk_qnat c).
Proof.
  introv; repeat constructor; simpl.
  apply assert_sub_vars; simpl; tcsp.
Qed.

Definition mkcv_qnat {o} vs c : @CVTerm o vs :=
  exist (isprog_vars vs) (mk_qnat c) (isprog_vars_qnat_implies vs c).

Definition mkcv_lqnat {o} vs : @CVTerm o vs := mkcv_qnat vs qlt_cond.
Definition mkc_lqnat {o} : @CTerm o := mkc_qnat qlt_cond.
Definition mk_lqnat {o} : @NTerm o := mk_qnat qlt_cond.

Definition mkcv_mqnat {o} vs : @CVTerm o vs := mkcv_qnat vs qnat_inc_cond.
Definition mkc_mqnat {o} : @CTerm o := mkc_qnat qnat_inc_cond.
Definition mk_mqnat {o} : @NTerm o := mk_qnat qnat_inc_cond.

Lemma nt_wf_mk_lib_depth {o} : @nt_wf o mk_lib_depth.
Proof.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve nt_wf_mk_lib_depth : slow.

Lemma isprog_vars_lib_depth {p} :
  forall vs, @isprog_vars p vs mk_lib_depth.
Proof.
  introv; apply isprog_vars_eq; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_lib_depth : slow.

Lemma isprog_lib_depth {o} : @isprog o mk_lib_depth.
Proof.
  repeat constructor.
Qed.

Definition mkcv_lib_depth {o} (vs : list NVar) : @CVTerm o vs :=
  exist (isprog_vars vs) mk_lib_depth (@isprog_vars_lib_depth o vs).

Definition mkc_lib_depth {o} : @CTerm o :=
  exist isprog mk_lib_depth isprog_lib_depth.


Definition mk_qnatk_aux {p} vi n : @NTerm p :=
  mk_set
    mk_tnat
    vi
    (mk_qlt (mk_var vi) n).

Definition mk_qnatk {p} n : @NTerm p :=
  let v := newvar n in mk_qnatk_aux v n.

Lemma isprog_vars_qlt {p} :
  forall (f a : @NTerm p) vs,
    isprog_vars vs (mk_qlt f a) <=> (isprog_vars vs f # isprog_vars vs a).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl); autorewrite with slow.
  rw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw @wf_qlt; split; sp.
Qed.

Lemma isprog_vars_qlt_implies {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_qlt a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_qlt; sp.
Qed.
Hint Resolve isprog_vars_qlt_implies : slow.

Lemma isprog_vars_qnatk {p} :
  forall vs (n : @NTerm p),
    isprog_vars vs n
    -> isprog_vars vs (mk_qnatk n).
Proof.
  introv isp.
  apply isprog_vars_set; eauto 3 with slow.
  apply isprog_vars_qlt_implies; simpl; eauto 3 with slow.
Qed.

Definition mkcv_qnatk {o} vs (n : @CVTerm o vs) : CVTerm vs :=
  let (t,x) := n in
  exist (isprog_vars vs) (mk_qnatk t) (isprog_vars_qnatk vs t x).

Definition mkcv_qnatk2nat {o} vs (t : @CVTerm o vs) :=
  mkcv_fun vs (mkcv_qnatk vs t) (mkcv_tnat vs).

Lemma isprog_qnatk {p} :
  forall (n : @NTerm p),
    isprog n
    -> isprog (mk_qnatk n).
Proof.
  introv isp.
  apply isprog_vars_nil_iff_isprog.
  apply isprog_vars_qnatk.
  apply isprog_vars_nil_iff_isprog; auto.
Qed.

Definition mk_qnatk2nat {o} (t : @NTerm o) : @NTerm o :=
  mk_fun (mk_qnatk t) mk_tnat.

Definition mkc_qnatk {o} (n : @CTerm o) : CTerm :=
  let (t,x) := n in
  exist isprog (mk_qnatk t) (isprog_qnatk t x).

Definition mkc_qnatk2nat {o} (t : @CTerm o) := mkc_fun (mkc_qnatk t) mkc_tnat.

Lemma isprogram_plus1 {o} :
  forall (a : @NTerm o), isprogram a -> isprogram (mk_plus1 a).
Proof.
  introv pa.
  destruct pa as[cl wf].
  repeat constructor; simpl; tcsp.
  { unfold closed in *; simpl; autorewrite with slow; auto. }
  { introv h; repndors; subst; tcsp; apply bt_wf_iff; eauto 3 with slow. }
Qed.
Hint Resolve isprogram_plus1 : slow.

Lemma isprog_plus1 {o} :
  forall a : @NTerm o, isprog a -> isprog (mk_plus1 a).
Proof.
  sp; allrw @isprog_eq; apply isprogram_plus1; sp.
Qed.

Definition mkc_plus1 {o} (t : @CTerm o) : CTerm :=
  let (a,x) := t in exist isprog (mk_plus1 a) (isprog_plus1 a x).

Lemma lsubstc_mk_plus1 {o} :
  forall (t1 : @NTerm o) sub
         (w1 : wf_term t1)
         (w  : wf_term (mk_plus1 t1))
         (c1 : cover_vars t1 sub)
         (c  : cover_vars (mk_plus1 t1) sub),
    lsubstc (mk_plus1 t1) w sub c
    = mkc_plus1 (lsubstc t1 w1 sub c1).
Proof.
  introv.
  unfold mk_plus1; autorewrite with slow.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl; autorewrite with slow; auto.
Qed.

Lemma cover_vars_plus1 {p} :
  forall a sub,
    cover_vars (@mk_plus1 p a ) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl; autorewrite with slow; tcsp.
Qed.

Lemma wf_plus1 {p} :
  forall a : @NTerm p, wf_term (mk_plus1 a) <=> wf_term a.
Proof.
  introv; split; intro w; repnd.
  { rw @wf_term_eq in w.
    inversion w as [| o l bw e]; subst; simpl in *.
    dLin_hyp; allrw @bt_wf_iff.
    apply wf_term_eq; auto. }
  { apply nt_wf_eq.
    constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp. }
Qed.

Lemma lsubstc_mk_plus1_ex {o} :
  forall (t1 : @NTerm o) sub
         (w  : wf_term (mk_plus1 t1))
         (c  : cover_vars (mk_plus1 t1 ) sub),
    {w1 : wf_term t1
     & {c1 : cover_vars t1 sub
     & lsubstc (mk_plus1 t1 ) w sub c
       = mkc_plus1 (lsubstc t1 w1 sub c1)}}.
Proof.
  sp.

  duplicate w.
  rw @wf_plus1 in w; sp.

  duplicate c.
  rw @cover_vars_plus1 in c; sp.

  exists w c.
  apply lsubstc_mk_plus1.
Qed.

Lemma isprog_vars_plus1 {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs (mk_plus1 t) <=> isprog_vars vs t.
Proof.
  introv.
  unfold mk_plus1.
  allrw @isprog_vars_add; split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma implies_isprog_vars_plus1 {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs t -> isprog_vars vs (mk_plus1 t).
Proof.
  introv isp.
  apply isprog_vars_plus1; auto.
Qed.

Definition mkcv_plus1 {p} vs (t : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t in
  exist (isprog_vars vs) (mk_plus1 a) (implies_isprog_vars_plus1 vs a x).

Definition mk_lib_depth1 {o} : @NTerm o := mk_plus1 mk_lib_depth.
Definition mkc_lib_depth1 {o} : @CTerm o := mkc_plus1 mkc_lib_depth.
Definition mkcv_lib_depth1 {o} vs : @CVTerm o vs := mkcv_plus1 _ (mkcv_lib_depth _).

Lemma isvalue_pair_aux1 {o} :
  forall b c,
    @isvalue o (mk_pair mk_lib_depth1 (mk_lam b (mk_lam c mk_axiom))).
Proof.
  introv.
  repeat (repeat constructor; simpl; introv xx; repndors; subst; tcsp).
Qed.
Hint Resolve isvalue_pair_aux1 : slow.

Hint Rewrite @mkcv_le_substc2 : slow.
Hint Rewrite @mkcv_less_than_substc : slow.

Lemma implies_equality_in_int_implies_tequality_mkc_le {o} :
  forall uk lib (a b c d : @CTerm o),
    equality uk lib a b mkc_int
    -> equality uk lib c d mkc_int
    -> tequality uk lib (mkc_le a c) (mkc_le b d).
Proof.
  introv equa equb.
  allrw @equality_in_int.
  apply all_in_ex_bar_tequality_implies_tequality.
  eapply in_open_bar_comb;[|exact equa]; clear equa.
  eapply in_open_bar_pres;[|exact equb]; clear equb.
  introv ext equb eqa.
  unfold equality_of_int in *; exrepnd.
  eapply tequality_mkc_le_aux; eauto.
  destruct (Z_le_gt_dec k k0); [left|right]; dands; auto; try lia.
Qed.

Lemma zero_equal_in_int {o} :
  forall uk (lib : @library o),
    equality uk lib mkc_zero mkc_zero mkc_int.
Proof.
  introv.
  apply equality_in_int.
  apply in_ext_implies_in_open_bar; introv ext.
  exists 0%Z; rewrite mkc_integer_as_mk_zero; dands; eauto 3 with slow.
Qed.
Hint Resolve zero_equal_in_int : slow.

Lemma implies_cequivc_mkc_less_than {o} :
  forall lib (f g a b : @CTerm o),
    cequivc lib f g
    -> cequivc lib a b
    -> cequivc lib (mkc_less_than f a) (mkc_less_than g b).
Proof.
  introv ceqa ceqb.
  repeat rewrite cvterm2.mkc_less_than_eq.
  apply implies_cequivc_less; eauto 3 with slow.
Qed.
Hint Resolve implies_cequivc_mkc_less_than : slow.

Lemma implies_ccequivc_ext_mkc_less_than {o} :
  forall lib (f g a b : @CTerm o),
    ccequivc_ext lib f g
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_less_than f a) (mkc_less_than g b).
Proof.
  introv ceqa ceqb ext.
  applydup ceqa in ext.
  applydup ceqb in ext.
  spcast; eauto 3 with slow.
Qed.
Hint Resolve implies_ccequivc_ext_mkc_less_than : slow.

Lemma implies_alpha_eq_mk_qlt {o} :
  forall f1 f2 a1 a2 : @NTerm o,
    alpha_eq f1 f2
    -> alpha_eq a1 a2
    -> alpha_eq (mk_qlt f1 a1) (mk_qlt f2 a2).
Proof.
  introv aeq1 aeq2.
  apply alpha_eq_oterm_combine; simpl; dands; auto.
  introv i; repndors; tcsp; ginv; apply alphaeqbt_nilv2; auto.
Qed.

Lemma alpha_eq_lsubst_mk_qnatk {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub
    -> alpha_eq (lsubst (mk_qnatk t) sub) (mk_qnatk (lsubst t sub)).
Proof.
  introv cl.
  repeat unflsubst; simpl; autorewrite with slow.
  unfold mk_qnatk, mk_qnatk_aux.
  fold_terms.

  match goal with
  | [ |- alpha_eq (mk_set _ _ ?a) (mk_set _ _ ?b) ] =>
    pose proof (ex_fresh_var ((fresh_var (newvar t :: free_vars t))
                                :: fresh_var (newvar (lsubst_aux t sub) :: free_vars (lsubst_aux t sub))
                                :: all_vars a ++ all_vars b)) as fvv
  end.
  exrepnd.
  rw @in_cons_iff in fvv0;rw @in_cons_iff in fvv0;rw @in_app_iff in fvv0.
  rw not_over_or in fvv0;rw not_over_or in fvv0;rw not_over_or in fvv0.
  repnd.

  apply (alpha_eq_mk_set v); auto;[].
  unfold subst_aux; simpl in *; autorewrite with slow in *; fold_terms.

  repeat (rewrite lsubst_aux_sub_filter;
          [|apply disjoint_singleton_r; eauto 2 with slow];[]).
  repeat (rewrite lsubst_aux_sub_filter in fvv1;
          [|apply disjoint_singleton_r; eauto 2 with slow];[]).

  apply implies_alpha_eq_mk_qlt; eauto 3 with slow.

  {
    rewrite (lsubst_aux_trivial3 (lsubst_aux t sub));
      [|simpl; introv h; repndors; tcsp; ginv; simpl; dands; eauto 3 with slow;
        apply disjoint_singleton_l; intro xx;
        destruct fvv0; right;
        rw in_app_iff; right; simpl; tcsp].

    rewrite (lsubst_aux_trivial3 (lsubst_aux t sub));
      [|simpl; introv h; repndors; tcsp; ginv; simpl; dands; eauto 3 with slow;
        apply disjoint_singleton_l; intro xx;
        destruct fvv0; right;
        rw in_app_iff; right; simpl; tcsp];[].

    auto.
  }
Qed.
Hint Resolve alpha_eq_lsubst_mk_qnatk : slow.

Lemma substc5_mkcv_qnatk {o} :
  forall (t1 t2 t3 : @CTerm o) x v w z a,
    alphaeqcv
      _
      (substc5 x t1 v t2 w t3 z (mkcv_qnatk _ a))
      (mkcv_qnatk _ (substc5 x t1 v t2 w t3 z a)).
Proof.
  introv; destruct_cterms; unfold alphaeqcv; simpl.
  remember [(z, x0), (w, x1), (v, x2)] as sub.
  assert (cl_sub sub) as cl by (subst; repeat (apply cl_sub_cons; dands; eauto 3 with slow)).
  eauto 3 with slow.
Qed.
Hint Resolve substc5_mkcv_qnatk : slow.

Lemma substc5_mkcv_qnatk2nat {o} :
  forall (t1 t2 t3 : @CTerm o) x v w z a,
    alphaeqcv
      _
      (substc5 x t1 v t2 w t3 z (mkcv_qnatk2nat _ a))
      (mkcv_qnatk2nat _ (substc5 x t1 v t2 w t3 z a)).
Proof.
  introv; unfold mkcv_qnatk2nat.
  eapply alphaeqcv_trans;[apply substc5_mkcv_fun|].
  autorewrite with slow; eauto 3 with slow.
Qed.

Definition mkcv_qlt {o} vs (t u : @CVTerm o vs) : CVTerm vs :=
  let (a,x) := t in
  let (b,y) := u in
  exist (isprog_vars vs) (mk_qlt a b) (isprog_vars_qlt_implies a b vs x y).

Lemma mkc_qnatk_eq {o} :
  forall (t : @CTerm o),
    mkc_qnatk t
    = mkc_set
        mkc_tnat
        nvarx
        (mkcv_qlt [nvarx] (mkc_var nvarx) (mk_cv [nvarx] t)).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
  unfold mk_qnatk.
  rw @newvar_prog; auto.
Qed.

Lemma mkcv_qnatk_eq {o} :
  forall vs (t : @CVTerm o vs),
    mkcv_qnatk vs t
    = let v := newvar (get_cvterm vs t) in
      mkcv_set vs (mkcv_tnat vs)
               v
               (mkcv_qlt (v :: vs) (mk_cv_app_r vs [v] (mkc_var v)) (mk_cv_app_l [v] vs t)).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; tcsp.
Qed.

Lemma implies_alpha_eq_mk_set {o} :
  forall x v (a b : @NTerm o),
    alpha_eq a b
    -> alpha_eq (mk_set x v a) (mk_set x v b).
Proof.
  introv aeq.
  constructor; simpl; auto.
  introv len.
  repeat (destruct n; tcsp).
  unfold selectbt; simpl.
  apply alpha_eq_bterm_congr; auto.
Qed.

Lemma implies_alpha_eq_mk_function {o} :
  forall x v (a b : @NTerm o),
    alpha_eq a b
    -> alpha_eq (mk_function x v a) (mk_function x v b).
Proof.
  introv aeq.
  constructor; simpl; auto.
  introv len.
  repeat (destruct n; tcsp).
  unfold selectbt; simpl.
  apply alpha_eq_bterm_congr; auto.
Qed.

Lemma mkcv_qnatk_substc {o} :
  forall v a (t : @CTerm o),
    alphaeqc
      (substc t v (mkcv_qnatk [v] a))
      (mkc_qnatk (substc t v a)).
Proof.
  introv.
  rw @mkc_qnatk_eq.
  rw @mkcv_qnatk_eq.

  destruct_cterms.
  unfold alphaeqc; simpl.

  (* brute force *)

  remember (newvar x0) as nv1.
  pose proof (newvar_prop x0) as nvp1; rw <- Heqnv1 in nvp1.
  clear Heqnv1.
  rw @cl_subst_subst_aux; eauto 2 with slow.
  unfold subst_aux; simpl; allrw @sub_filter_nil_r; allrw memvar_singleton.
  pose proof (newvar_prog (@mk_void o)) as nvv; autodimp nvv hyp; tcsp;eauto 2 with slow;[].
  rw nvv.

  Opaque beq_var.
  repeat (boolvar; allsimpl; tcsp; repndors; subst; tcsp; GC).

  { eapply isprog_vars_disjoint_implies_isprog in i0; allrw disjoint_singleton_l; auto.
    rw @subst_trivial; auto; autorewrite with slow.
    prove_alpha_eq4.
    introv k.
    repeat (destruct n; tcsp);[]; clear k.

    pose proof (ex_fresh_var (nvary :: nvarx
                                    :: bound_vars x0
                                    ++ free_vars x0)) as fv1.
    destruct fv1 as [v1 fv1].
    exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v1]); simpl; auto;[|].

    { apply disjoint_singleton_l; autorewrite with slow; simpl.
      unfold all_vars; simpl; autorewrite with slow.
      repeat (allrw in_app_iff; simpl; autorewrite with slow).
      intro xx; repndors; subst; tcsp. }

    apply implies_alpha_eq_mk_qlt; auto.
    repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow). }

  { prove_alpha_eq4.
    introv k.
    repeat (destruct n; tcsp);[]; clear k.
    fold_terms; autorewrite with slow.

    pose proof (ex_fresh_var (nv1 :: nvary :: nvarx
                                  :: bound_vars x0
                                  ++ free_vars x0
                                  ++ free_vars (lsubst_aux x0 [(nvary, x)])
                                  ++ bound_vars (lsubst_aux x0 [(nvary, x)])
                                  ++ free_vars (subst x0 nvary x)
                                  ++ bound_vars (subst x0 nvary x))) as fv1.
    destruct fv1 as [v1 fv1].
    exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v1]); simpl; auto;[|].

    { apply disjoint_singleton_l; autorewrite with slow; simpl.
      unfold all_vars; simpl; autorewrite with slow.
      repeat (allrw in_app_iff; simpl; autorewrite with slow).
      intro xx; repndors; subst; tcsp. }

    boolvar; tcsp.
    apply implies_alpha_eq_mk_qlt; auto.
    unfsubst.
    repeat (rewrite (lsubst_aux_trivial_cl_term2 (lsubst_aux x0 [(nvary,x)]));
            [|apply closed_lsubst_aux; eauto 3 with slow]); auto. }

  { prove_alpha_eq4.
    introv k.
    repeat (destruct n; tcsp);[]; clear k.
    fold_terms; autorewrite with slow.
    eapply isprog_vars_disjoint_implies_isprog in i0; allrw disjoint_singleton_l; auto.
    rw @subst_trivial; auto. }

  { destruct Heqb1; tcsp. }

  { eapply isprog_vars_disjoint_implies_isprog in i0; allrw disjoint_singleton_l; auto.
    rewrite subst_trivial; eauto 3 with slow; autorewrite with slow.
    prove_alpha_eq4.
    introv k.
    repeat (destruct n; tcsp); clear k; fold_terms; autorewrite with slow.

    pose proof (ex_fresh_var (nv1 :: nvary :: nvarx
                                  :: bound_vars x0
                                  ++ free_vars x0)) as fv1.
    destruct fv1 as [v1 fv1].
    exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v1]); simpl; auto;[|].

    { apply disjoint_singleton_l; autorewrite with slow; simpl.
      unfold all_vars; simpl; autorewrite with slow.
      repeat (allrw in_app_iff; simpl; autorewrite with slow).
      intro xx; repndors; subst; tcsp. }

    apply implies_alpha_eq_mk_qlt; auto; boolvar; tcsp.
    repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow). }

  { prove_alpha_eq4.
    introv k.
    repeat (destruct n; tcsp);[]; clear k.
    fold_terms; autorewrite with slow.

    pose proof (ex_fresh_var (nv1 :: nvary :: nvarx
                                  :: bound_vars x0
                                  ++ free_vars x0
                                  ++ free_vars (lsubst_aux x0 [(nvarx, x)])
                                  ++ bound_vars (lsubst_aux x0 [(nvarx, x)])
                                  ++ free_vars (subst x0 nvarx x)
                                  ++ bound_vars (subst x0 nvarx x))) as fv1.
    destruct fv1 as [v1 fv1].
    exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v1]); simpl; auto;[|].

    { apply disjoint_singleton_l; autorewrite with slow; simpl.
      unfold all_vars; simpl; autorewrite with slow.
      repeat (allrw in_app_iff; simpl; autorewrite with slow).
      intro xx; repndors; subst; tcsp. }

    boolvar; tcsp.
    apply implies_alpha_eq_mk_qlt; auto.
    unfsubst.
    repeat (rewrite (lsubst_aux_trivial_cl_term2 (lsubst_aux x0 [(nvarx,x)]));
            [|apply closed_lsubst_aux; eauto 3 with slow]); auto. }

  { destruct Heqb2; tcsp. }

  { prove_alpha_eq4.
    introv k.
    repeat (destruct n; tcsp);[]; clear k.
    fold_terms; autorewrite with slow.

    pose proof (ex_fresh_var (nv1 :: nvary :: nvarx
                                  :: bound_vars x0
                                  ++ free_vars x0
                                  ++ free_vars (lsubst_aux x0 [(v, x)])
                                  ++ bound_vars (lsubst_aux x0 [(v, x)])
                                  ++ free_vars (subst x0 v x)
                                  ++ bound_vars (subst x0 v x))) as fv1.
    destruct fv1 as [v1 fv1].
    exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v1]); simpl; auto;[|].

    { apply disjoint_singleton_l; autorewrite with slow; simpl.
      unfold all_vars; simpl; autorewrite with slow.
      repeat (allrw in_app_iff; simpl; autorewrite with slow).
      intro xx; repndors; subst; tcsp. }

    boolvar; tcsp.
    apply implies_alpha_eq_mk_qlt; auto.
    unfsubst.
    repeat (rewrite (lsubst_aux_trivial_cl_term2 (lsubst_aux x0 [(v,x)]));
            [|apply closed_lsubst_aux; eauto 3 with slow]); auto. }
Qed.

Lemma substc_mkcv_qnatk2nat {o} :
  forall v (t : @CVTerm o [v]) a,
    alphaeqc
      (substc a v (mkcv_qnatk2nat [v] t))
      (mkc_qnatk2nat (substc a v t)).
Proof.
  introv; unfold mkcv_natk2nat.
  eapply alphaeqc_trans;[apply substc_mkcv_fun|].
  unfold natk2nat.
  autorewrite with slow.
  apply alphaeqc_mkc_fun; eauto 3 with slow.
  eapply alphaeqc_trans;[apply mkcv_qnatk_substc|].
  eauto 3 with slow.
Qed.

Lemma mkcv_qlt_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_qlt [v] a b)
    = mkc_qlt (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @mkcv_qlt_substc : slow.

Lemma type_extensionality_per_qlt_nuprl {o} :
  @type_extensionality o (per_qlt nuprl).
Proof.
  introv per e.
  unfold per_qlt in *; exrepnd.
  eexists; eexists; eexists; eexists; dands; eauto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_qlt_nuprl : slow.

Lemma uniquely_valued_per_qlt_nuprl {o} :
  @uniquely_valued o (per_qlt nuprl).
Proof.
  introv pera perb.
  unfold per_qlt in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  computes_to_eqval_ext.
  hide_hyp pera2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qlt_right in ceq.
  apply cequivc_ext_mkc_qlt_right in ceq0.
  repnd.

  apply implies_eq_term_equals_per_qlt_bar2; eauto 3 with slow.
Qed.
Hint Resolve uniquely_valued_per_qlt_nuprl : slow.

Lemma local_per_bar_per_qlt_nuprl {o} :
  @local_ts o (per_bar (per_qlt nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_qlt_nuprl : slow.

Lemma dest_nuprl_per_qlt_l {o} :
  forall (ts : cts(o)) uk lib T a b T' eq,
    ts = univ
    -> ccomputes_to_valc_ext lib T (mkc_qlt a b)
    -> close ts uk lib T T' eq
    -> per_bar (per_qlt (close ts)) uk lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_qlt_nuprl; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca.
  eapply reca; eauto 3 with slow.
Qed.

Lemma isvalue_qlt {o} :
  forall (a b : @NTerm o), isprogram (mk_qlt a b) -> isvalue (mk_qlt a b).
Proof.
  introv; constructor; tcsp.
Qed.

Lemma implies_isvalue_qlt {o} :
  forall (a b : @NTerm o),
    isprog a
    -> isprog b
    -> isvalue (mk_qlt a b).
Proof.
  introv ispa ispb.
  apply isvalue_qlt.
  apply implies_isprogram_qlt; allrw <- @isprog_eq; auto.
Qed.

Lemma iscvalue_mkc_qlt {o} :
  forall (a b : @CTerm o), iscvalue (mkc_qlt a b).
Proof.
  introv; destruct_cterms; unfold iscvalue; simpl.
  apply implies_isvalue_qlt; tcsp.
Qed.
Hint Resolve iscvalue_mkc_qlt : slow.

Lemma dest_nuprl_qlt {o} :
  forall uk (lib : @library o) (a b c d : @CTerm o) eq,
    nuprl uk lib (mkc_qlt a b) (mkc_qlt c d) eq
    -> per_bar (per_qlt nuprl) uk lib (mkc_qlt a b) (mkc_qlt c d) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_qlt_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprl_qlt2 {o} :
  forall uk lib (eq : per(o)) a b c d,
    nuprl uk lib (mkc_qlt a b) (mkc_qlt c d) eq
    ->
    (eq <=2=> (per_bar_eq lib (equality_of_qlt_bar_lib_per lib a b))
     # equality_of_qnat_bar lib qlt_cond a c
     # equality_of_qnat_bar lib qlt_cond b d).
Proof.
  introv u.
  apply dest_nuprl_qlt in u.
  unfold per_bar in u; exrepnd.

  unfold per_qlt in u1.
  dands.

  { eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_bar_eq.
    eapply in_open_bar_ext_pres; eauto; clear u1; introv h; exrepnd.
    repeat ccomputes_to_valc_ext_val.
    eapply eq_term_equals_trans;[eauto|]; simpl.
    apply implies_eq_term_equals_per_qlt_bar2; eauto 3 with slow. }

  { eapply in_open_bar_comb2; eauto; clear u1; apply in_ext_ext_implies_in_open_bar_ext.
    introv h; exrepnd.
    repeat ccomputes_to_valc_ext_val; eauto 4 with slow. }

  { eapply in_open_bar_comb2; eauto; clear u1; apply in_ext_ext_implies_in_open_bar_ext.
    introv h; exrepnd.
    repeat ccomputes_to_valc_ext_val; eauto 4 with slow. }
Qed.

Lemma tequality_mkc_qlt {o} :
  forall uk (lib : @library o) a b c d,
    tequality uk lib (mkc_qlt a b) (mkc_qlt c d)
    <=>
    (
      equality_of_qnat_bar lib qlt_cond a c
      # equality_of_qnat_bar lib qlt_cond b d
    ).
Proof.
  introv; split; intro h.

  { unfold tequality in h; exrepnd.
    apply dest_nuprl_qlt2 in h0; repnd; auto. }

  { repnd.
    apply all_in_ex_bar_tequality_implies_tequality.
    eapply in_open_bar_comb; try exact h; clear h.
    eapply in_open_bar_pres; try exact h0; clear h0.
    introv ext h q.
    exists (equality_of_qlt_bar lib' a b).
    apply CL_qlt.
    exists a b c d; dands; eauto 3 with slow. }
Qed.

Lemma equality_in_qnat_implies_ccequivc_ext_bar {o} :
  forall uk lib (a b : @CTerm o) c,
    equality uk lib a b (mkc_qnat c)
    -> ccequivc_ext_bar lib a b.
Proof.
  introv equ.
  apply equality_in_qnat in equ.
  eapply in_open_bar_pres; try exact equ; clear equ.
  introv ext h xt.
  apply h in xt; exrepnd; spcast.
  apply computes_to_valc_implies_cequivc in xt1.
  apply computes_to_valc_implies_cequivc in xt0.
  eapply cequivc_trans;[eauto|].
  apply cequivc_sym; auto.
Qed.

Lemma equality_of_nat_implies_are_same_qnats {o} :
  forall (lib : @library o) a b c,
    equality_of_nat lib a b
    -> are_same_qnats lib c a b.
Proof.
  introv equ ext.
  unfold equality_of_nat in *; exrepnd.
  applydup equ1 in ext.
  applydup equ0 in ext.
  exrepnd; spcast.
  apply choiceseq.cequivc_nat_implies_computes_to_valc in ext4.
  apply choiceseq.cequivc_nat_implies_computes_to_valc in ext2.
  apply computes_to_valc_isvalue_eq in ext4; eauto 3 with slow; subst.
  apply computes_to_valc_isvalue_eq in ext2; eauto 3 with slow; subst.
  eexists; dands; spcast; eauto.
Qed.
Hint Resolve equality_of_nat_implies_are_same_qnats : slow.

Lemma equality_of_nat_implies_sat_qnat_cond_left {o} :
  forall (lib : @library o) a b c,
    equality_of_nat lib a b
    -> sat_qnat_cond lib c a.
Proof.
  introv equ h exta extb compa compb; subst.
  unfold equality_of_nat in *; exrepnd.
  pose proof (equ1 _ exta) as equa; simpl in *; exrepnd; spcast.
  pose proof (equ1 _ (lib_extends_trans extb exta)) as equb; simpl in *; exrepnd; spcast.
  allapply @choiceseq.cequivc_nat_implies_computes_to_valc.
  apply computes_to_valc_isvalue_eq in equa0; eauto 3 with slow;subst.
  apply computes_to_valc_isvalue_eq in equb0; eauto 3 with slow;subst.
  repeat computes_to_eqval; auto.
Qed.
Hint Resolve equality_of_nat_implies_sat_qnat_cond_left : slow.

Lemma equality_of_nat_implies_sat_qnat_cond_right {o} :
  forall (lib : @library o) a b c,
    equality_of_nat lib a b
    -> sat_qnat_cond lib c b.
Proof.
  introv equ h exta extb compa compb; subst.
  unfold equality_of_nat in *; exrepnd.
  pose proof (equ0 _ exta) as equa; simpl in *; exrepnd; spcast.
  pose proof (equ0 _ (lib_extends_trans extb exta)) as equb; simpl in *; exrepnd; spcast.
  allapply @choiceseq.cequivc_nat_implies_computes_to_valc.
  apply computes_to_valc_isvalue_eq in equa0; eauto 3 with slow;subst.
  apply computes_to_valc_isvalue_eq in equb0; eauto 3 with slow;subst.
  repeat computes_to_eqval; auto.
Qed.
Hint Resolve equality_of_nat_implies_sat_qnat_cond_right : slow.

Lemma equality_of_nat_implies_equality_of_qnat {o} :
  forall (lib : @library o) a b c,
    equality_of_nat lib a b
    -> equality_of_qnat lib c a b.
Proof.
  introv equ.
  unfold equality_of_qnat; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_of_nat_implies_equality_of_qnat : slow.

Lemma equality_of_nat_bar_implies_equality_of_qnat_bar {o} :
  forall (lib : @library o) a b c,
    equality_of_nat_bar lib a b
    -> equality_of_qnat_bar lib c a b.
Proof.
  introv equ.
  eapply in_open_bar_pres; try exact equ; clear equ; introv ext equ; eauto 3 with slow.
Qed.
Hint Resolve equality_of_nat_bar_implies_equality_of_qnat_bar : slow.

Lemma equality_mkc_qnat_implies_tequality_mkc_natk {o} :
  forall uk lib (a b : @CTerm o),
    equality uk lib a b mkc_lqnat
    -> tequality uk lib (mkc_qnatk a) (mkc_qnatk b).
Proof.
  introv equ.
  repeat rewrite mkc_qnatk_eq.

  apply tequality_set; dands; eauto 3 with slow.
  introv exta equa.
  autorewrite with slow.
  apply tequality_mkc_qlt.

  apply equality_in_tnat in equa.
  apply equality_in_qnat in equ.
  dands; eauto 3 with slow.
Qed.
Hint Resolve equality_mkc_qnat_implies_tequality_mkc_natk : slow.

Lemma equality_in_mkc_qnatk_implies_equality_in_mkc_tnat {o} :
  forall uk lib (a b : @CTerm o) n,
    equality uk lib a b (mkc_qnatk n)
    -> equality uk lib a b mkc_tnat.
Proof.
  introv equ.
  rewrite mkc_qnatk_eq in equ.
  apply equality_in_set in equ; repnd; auto.
Qed.
Hint Resolve equality_in_mkc_qnatk_implies_equality_in_mkc_tnat : slow.

Lemma equality_nat2nat_to_qnatk2nat {o} :
  forall uk lib (n f g : @CTerm o),
    member uk lib n mkc_lqnat
    -> equality uk lib f g nat2nat
    -> equality uk lib f g (mkc_qnatk2nat n).
Proof.
  introv m e.

  apply equality_in_fun; repnd; dands; eauto 3 with slow.

  { apply equality_mkc_qnat_implies_tequality_mkc_natk; auto. }

  introv xt equ.
  apply equality_nat2nat_apply; eauto 3 with slow.
Qed.
Hint Resolve equality_nat2nat_to_qnatk2nat : slow.

Lemma isprog_mqnat {o} : @isprog o mk_mqnat.
Proof.
  repeat constructor.
Qed.
Hint Resolve isprog_qnat : slow.

Lemma substc2_mkcv_mqnat {o} :
  forall v (t : @CTerm o) x,
    substc2 v t x (mkcv_mqnat [v,x]) = mkcv_mqnat [v].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  apply subst_trivial; eauto 2 with slow.
Qed.
Hint Rewrite @substc2_mkcv_mqnat : slow.

Lemma mkcv_mqnat_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_mqnat [v])
    = mkc_mqnat.
Proof.
  introv.
  destruct_cterms; apply cterm_eq; simpl.
  unfsubst.
Qed.
Hint Rewrite @mkcv_mqnat_substc : slow.

Lemma tequality_mqnat {o} :
  forall uk (lib : @library o), tequality uk lib mkc_mqnat mkc_mqnat.
Proof.
  introv; apply tequality_qnat.
Qed.
Hint Resolve tequality_mqnat : slow.

Lemma substc5_mkcv_plus1 {o} :
  forall (t1 t2 t3 : @CTerm o) x v w z a,
    substc5 x t1 v t2 w t3 z (mkcv_plus1 _ a)
    = mkcv_plus1
        _
        (substc5 x t1 v t2 w t3 z a).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat (unflsubst;repeat (apply cl_sub_cons; dands; eauto 3 with slow)).
Qed.
Hint Rewrite @substc5_mkcv_plus1 : slow.

Lemma substc_mkcv_plus1 {o} :
  forall v a (t : @CTerm o),
    substc t v (mkcv_plus1 [v] a) = mkc_plus1 (substc t v a).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc_mkcv_plus1 : slow.

Lemma computes_to_valc_lib_depth {o} :
  forall (lib : @plibrary o),
    computes_to_valc lib mkc_lib_depth (mkc_nat (lib_depth lib)).
Proof.
  introv; unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
Qed.
Hint Resolve computes_to_valc_lib_depth : slow.

Lemma computes_to_valc_lib_depth1 {o} :
  forall (lib : @plibrary o),
    computes_to_valc lib mkc_lib_depth1 (mkc_nat (S (lib_depth lib))).
Proof.
  introv; unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
  eapply reduces_to_if_split2;[csunf;simpl; eauto|].
  apply reduces_to_if_step.
  csunf; simpl; dcwf h; simpl; auto.
  assert (1%Z = Z.of_nat 1) as xx; auto; rewrite xx.
  rewrite <- Znat.Nat2Z.inj_add.
  rewrite Nat.add_1_r; auto.
Qed.
Hint Resolve computes_to_valc_lib_depth1 : slow.

Lemma isinteger_mk_nat {o} :
  forall n, @isinteger o (mk_nat n).
Proof.
  introv.
  unfold isinteger.
  exists (Z.of_nat n); auto.
Qed.
Hint Resolve isinteger_mk_nat : slow.

Lemma plus1_preserves_computes_to_valc {o} :
  forall lib (a : @CTerm o) n,
    computes_to_valc lib a (mkc_nat n)
    -> computes_to_valc lib (mkc_plus1 a) (mkc_nat (S n)).
Proof.
  introv comp.
  destruct_cterms; unfold computes_to_valc in *; simpl in *.
  unfold computes_to_value in *; repnd; dands; eauto 3 with slow.
  eapply reduces_to_trans.
  { apply reduce_to_prinargs_arith_can; eauto; try apply reduces_to_symm; eauto 3 with slow. }
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
  assert (1%Z = Z.of_nat 1) as xx; auto; rewrite xx.
  rewrite <- Znat.Nat2Z.inj_add.
  rewrite Nat.add_1_r; auto.
Qed.
Hint Resolve plus1_preserves_computes_to_valc : slow.

Lemma isvalue_one {o} : @isvalue o mk_one.
Proof.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve isvalue_one : slow.

Lemma mk_integer_eq_implies {o} :
  forall n m, @mk_integer o n = mk_integer m -> n = m.
Proof.
  introv h.
  inversion h as [q]; auto.
Qed.

Lemma plus1_computes_to_valc_implies {o} :
  forall lib (a : @CTerm o) n m,
    computes_to_valc lib a (mkc_nat n)
    -> computes_to_valc lib (mkc_plus1 a) (mkc_nat m)
    -> m = S n.
Proof.
  introv compa compb.
  apply plus1_preserves_computes_to_valc in compa.
  eapply computes_to_valc_eq in compa; try exact compb.
  apply mkc_nat_eq_implies in compa; auto.
Qed.

Lemma plus1_preserves_are_same_qnats {o} :
  forall lib (a b : @CTerm o) c,
    are_same_qnats lib c a b
    -> are_same_qnats lib c (mkc_plus1 a) (mkc_plus1 b).
Proof.
  introv equ ext.
  apply equ in ext; exrepnd.
  exists (S n); dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve plus1_preserves_are_same_qnats : slow.

Definition is_qnat {o} lib (t : @CTerm o) :=
  in_ext lib (fun lib => {n : nat , ccomputes_to_valc lib t (mkc_nat n)}).

Lemma are_same_qnats_implies_is_qnat_left {o} :
  forall lib (a b : @CTerm o) c,
    are_same_qnats lib c a b
    -> is_qnat lib a.
Proof.
  introv h ext; apply h in ext; exrepnd; eauto.
Qed.
Hint Resolve are_same_qnats_implies_is_qnat_left : slow.

Lemma plus1_preserves_sat_qnat_cond {o} :
  forall lib (a : @CTerm o) c,
    is_qnat lib a
    -> sat_qnat_cond lib c a
    -> sat_qnat_cond lib c (mkc_plus1 a).
Proof.
  introv isn sat h exta extb compa compb; subst.
  pose proof (isn _ exta) as isna; simpl in *; exrepnd; spcast.
  pose proof (isn _ (lib_extends_trans extb exta)) as isnb; simpl in *; exrepnd; spcast.
  eapply plus1_computes_to_valc_implies in compa; eauto.
  eapply plus1_computes_to_valc_implies in compb; eauto.
  subst.
  apply Peano.le_n_S.
  apply (sat lib1 lib2); auto.
Qed.
Hint Resolve plus1_preserves_sat_qnat_cond : slow.

Lemma plus1_preserves_equality_in_mqnat {o} :
  forall uk lib (a b : @CTerm o),
    equality uk lib a b mkc_mqnat
    -> equality uk lib (mkc_plus1 a) (mkc_plus1 b) mkc_mqnat.
Proof.
  introv equ.
  unfold mkc_mqnat in *.
  allrw @equality_in_qnat.
  eapply in_open_bar_pres; eauto; clear equ; introv ext equ.
  unfold equality_of_qnat in *; repnd; dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve plus1_preserves_equality_in_mqnat : slow.

Lemma are_same_qnats_depth {o} :
  forall (lib : @library o) c, are_same_qnats lib c mkc_lib_depth mkc_lib_depth.
Proof.
  introv xt.
  exists (lib_depth lib'); dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve are_same_qnats_depth : slow.

Lemma are_same_qnats_depth1 {o} :
  forall (lib : @library o) c, are_same_qnats lib c mkc_lib_depth1 mkc_lib_depth1.
Proof.
  introv xt.
  exists (S (lib_depth lib')); dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve are_same_qnats_depth1 : slow.

Lemma add_choice_monotone_lib_depth {o} :
  forall name v (lib : @plibrary o) n r lib',
    add_choice name v lib = Some (n, r, lib')
    -> lib_depth lib <= lib_depth lib'.
Proof.
  induction lib; introv addc; simpl in *; ginv.
  destruct a; simpl in *; tcsp.

  { destruct entry as [vals restr]; simpl in *; boolvar; subst; tcsp; ginv.
    { inversion addc; subst; simpl in *; clear addc.
      autorewrite with slow.
      apply Nat.max_le_compat_r; auto. }
    { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; tcsp; ginv.
      inversion addc; subst; clear addc; simpl in *.
      apply Nat.max_le_compat_l; eauto. } }

  { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; tcsp; ginv.
    inversion addc; subst; clear addc; simpl in *; eauto. }
Qed.
Hint Resolve add_choice_monotone_lib_depth : slow.

Lemma add_one_choice_monotone_lib_depth {o} :
  forall name v (lib : @library o) n r lib',
    add_one_choice name v lib = Some (n, r, lib')
    -> lib_depth lib <= lib_depth lib'.
Proof.
  introv addc.
  destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc';
    destruct addc'; repnd; tcsp; ginv; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve add_one_choice_monotone_lib_depth : slow.

Lemma lib_extends_monotone_lib_depth {o} :
  forall (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> lib_depth lib1 <= lib_depth lib2.
Proof.
  introv ext.
  lib_ext_ind ext Case; try lia.
Qed.
Hint Resolve lib_extends_monotone_lib_depth : slow.

Lemma sat_qnat_cond_depth {o} :
  forall (lib : @library o) c, sat_qnat_cond lib c mkc_lib_depth.
Proof.
  introv h exta extb compa compb; subst.
  pose proof (computes_to_valc_lib_depth lib1) as ha.
  pose proof (computes_to_valc_lib_depth lib2) as hb.
  repeat computes_to_eqval; eauto 3 with slow.
Qed.
Hint Resolve sat_qnat_cond_depth : slow.

(* This is true about any [qnat] *)
Lemma equality_lib_depth_in_mqnat {o} :
  forall uk (lib : @library o), equality uk lib mkc_lib_depth mkc_lib_depth mkc_mqnat.
Proof.
  introv.
  apply equality_in_qnat.
  apply in_ext_implies_in_open_bar; introv ext.
  unfold equality_of_qnat; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_lib_depth_in_mqnat : slow.

Lemma sat_qnat_cond_depth1 {o} :
  forall (lib : @library o) c, sat_qnat_cond lib c mkc_lib_depth1.
Proof.
  introv h exta extb compa compb; subst.
  pose proof (computes_to_valc_lib_depth1 lib1) as ha.
  pose proof (computes_to_valc_lib_depth1 lib2) as hb.
  repeat computes_to_eqval; eauto 3 with slow.
  apply Peano.le_n_S; eauto 3 with slow.
Qed.
Hint Resolve sat_qnat_cond_depth1 : slow.

(* This is true about any [qnat] *)
Lemma equality_lib_depth1_in_mqnat {o} :
  forall uk (lib : @library o), equality uk lib mkc_lib_depth1 mkc_lib_depth1 mkc_mqnat.
Proof.
  introv.
  apply equality_in_qnat.
  apply in_ext_implies_in_open_bar; introv ext.
  unfold equality_of_qnat; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_lib_depth1_in_mqnat : slow.

Lemma lib_extends_preserves_equality_of_qlt {o} :
  forall (lib' lib : @library o) a b,
    lib_extends lib' lib
    -> equality_of_qlt lib a b
    -> equality_of_qlt lib' a b.
Proof.
  introv ext equ xt; apply equ; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_equality_of_qlt : slow.

Lemma equality_of_qlt_implies_equality_of_qlt_bar {o} :
  forall (lib : @library o) a b t u,
    equality_of_qlt lib a b
    -> equality_of_qlt_bar lib a b t u.
Proof.
  introv equ.
  apply in_ext_implies_in_open_bar.
  introv ext; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qlt_implies_equality_of_qlt_bar : slow.

Lemma equality_of_qlt_implies_are_same_qnats_left {o} :
  forall lib (a b : @CTerm o) c,
    equality_of_qlt lib a b
    -> are_same_qnats lib c a a.
Proof.
  introv equ ext.
  apply equ in ext; exrepnd.
  exists n; auto.
Qed.
Hint Resolve equality_of_qlt_implies_are_same_qnats_left : slow.

(*Lemma equality_of_qlt_implies_sat_qnat_cond {o} :
  forall lib (a b : @CTerm o),
    equality_of_qlt lib a b
    -> sat_qnat_cond lib qnat_mon_cond a.
Proof.
  introv equ h exta extb compa compb; GC.
  pose proof (equ _ exta) as equa; simpl in *; exrepnd; spcast.
  pose proof (equ _ (lib_extends_trans extb exta)) as equb; simpl in *; exrepnd; spcast.
  repeat computes_to_eqval; auto.

Qed.
Hint Resolve equality_of_qlt_implies_are_same_qnats_left : slow.*)

(*Lemma equality_of_qlt_implies_equality_of_qnat_left {o} :
  forall lib (a b : @CTerm o),
    equality_of_qlt lib a b
    -> equality_of_qnat lib qnat_mon_cond a a.
Proof.
  introv equ; unfold equality_of_qnat; dands; eauto 3 with slow.

Qed.
Hint Resolve equality_of_qlt_implies_equality_of_qnat_left : slow.*)

(*Lemma equality_of_qlt_implies_equality_of_qnat_right {o} :
  forall lib (a b : @CTerm o),
    equality_of_qlt lib a b
    -> equality_of_qnat lib b b.
Proof.
  introv equ ext; apply equ in ext; exrepnd.
  exists m; auto.
Qed.
Hint Resolve equality_of_qlt_implies_equality_of_qnat_right : slow.*)

Lemma equality_in_mkc_qlt {o} :
  forall uk (lib : @library o) t u a b,
    equality uk lib t u (mkc_qlt a b)
    <=>
    (in_open_bar lib (fun lib => equality_of_qlt lib a b)
     # equality_of_qnat_bar lib qlt_cond a a
     # equality_of_qnat_bar lib qlt_cond b b).
Proof.
  introv; split; intro equ; repnd.
  { unfold equality in equ; exrepnd.
    apply dest_nuprl_qlt2 in equ1; repnd.
    apply equ2 in equ0; clear equ2.
    apply per_bar_eq_equality_of_qlt_bar_lib_per in equ0; dands; tcsp. }
  { apply all_in_ex_bar_equality_implies_equality.
    eapply in_open_bar_comb; eauto; clear equ.
    eapply in_open_bar_comb; eauto; clear equ1.
    eapply in_open_bar_pres; eauto; clear equ0.
    introv ext equ0 equ1 equ.
    clear dependent lib; rename lib' into lib.
    exists (equality_of_qlt_bar lib a b).
    dands; tcsp; eauto 3 with slow.
    apply CL_qlt.
    exists a b a b; dands; eauto 3 with slow. }
Qed.

Lemma inhabited_type_bar_implies {o} :
  forall uk (lib : @library o) a n,
    inhabited_type_bar uk lib (mkc_qlt a n)
    -> in_open_bar lib (fun lib : library => equality_of_qlt lib a n).
Proof.
  introv h.
  apply collapse_all_in_ex_bar.
  eapply in_open_bar_pres; try exact h; clear h; introv ext h.
  unfold inhabited_type in *; exrepnd.
  apply equality_in_mkc_qlt in h0; repnd; auto.
Qed.

Lemma equality_in_mkc_qnatk_implies {o} :
  forall uk lib (a b : @CTerm o) n,
    equality uk lib a b (mkc_qnatk n)
    -> in_open_bar lib (fun lib : library => equality_of_qlt lib a n).
Proof.
  introv equ.
  rewrite mkc_qnatk_eq in equ.
  apply equality_in_set in equ; repnd; autorewrite with slow in *.
  apply inhabited_type_bar_implies in equ2; auto.
Qed.

Lemma zero_in_nat {o} :
  forall uk (lib : @library o), equality uk lib mkc_zero mkc_zero mkc_tnat.
Proof.
  introv.
  allrw @mkc_zero_eq; eauto 3 with slow.
Qed.
Hint Resolve zero_in_nat : slow.

Definition is_mqnat {o} lib (t : @CTerm o) :=
  is_qnat lib t # sat_qnat_cond lib qlt_cond t.

Definition is_mqnat_bar {o} lib (t : @CTerm o) :=
  in_open_bar lib (fun lib => is_mqnat lib t).

Lemma are_same_qnats_implies_is_qnat_right {o} :
  forall lib (a b : @CTerm o) c,
    are_same_qnats lib c a b
    -> is_qnat lib b.
Proof.
  introv h ext; apply h in ext; exrepnd; eauto.
Qed.
Hint Resolve are_same_qnats_implies_is_qnat_right : slow.

Lemma equality_of_qnat_implies_is_mqnat_left {o} :
  forall (lib : @library o) a b,
    equality_of_qnat lib qlt_cond a b
    -> is_mqnat lib a.
Proof.
  introv h; unfold equality_of_qnat, is_mqnat in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_implies_is_mqnat_left : slow.

Lemma equality_of_qnat_bar_implies_is_qnat_bar_left {o} :
  forall (lib : @library o) a b,
    equality_of_qnat_bar lib qlt_cond a b
    -> is_mqnat_bar lib a.
Proof.
  introv equ.
  eapply in_open_bar_pres; eauto; clear equ.
  introv ext equ; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_bar_implies_is_qnat_bar_left : slow.

Lemma equality_of_qnat_implies_is_qnat_right {o} :
  forall (lib : @library o) a b,
    equality_of_qnat lib qlt_cond a b
    -> is_mqnat lib b.
Proof.
  introv h; unfold equality_of_qnat, is_mqnat in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_implies_is_qnat_right : slow.

Lemma equality_of_qnat_bar_implies_is_qnat_bar_right {o} :
  forall (lib : @library o) a b,
    equality_of_qnat_bar lib qlt_cond a b
    -> is_mqnat_bar lib b.
Proof.
  introv equ.
  eapply in_open_bar_pres; eauto; clear equ.
  introv ext equ; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_bar_implies_is_qnat_bar_right : slow.

Lemma tequality_mkc_qnatk {o} :
  forall uk (lib : @library o) (a b : CTerm),
    tequality uk lib (mkc_qnatk a) (mkc_qnatk b)
    <=> equality_of_qnat_bar lib qlt_cond a b.
Proof.
  introv; repeat rewrite mkc_qnatk_eq.
  rw (@tequality_set o uk).
  dands; split; intro h; repnd.

  { pose proof (h _ (lib_extends_refl lib) mkc_zero mkc_zero) as h; cbv beta in h.
    autorewrite with slow in h.
    autodimp h hyp; eauto 3 with slow.
    allrw @tequality_mkc_qlt; repnd; auto. }

  { dands; eauto 3 with slow.
    introv ext equ.
    autorewrite with slow.
    apply equality_in_tnat in equ.
    apply tequality_mkc_qlt; dands; eauto 3 with slow. }
Qed.

Lemma equality_of_qnat_same {o} :
  forall lib (a : @CTerm o),
    equality_of_qnat lib qlt_cond a a <=> is_mqnat lib a.
Proof.
  introv; split; intro h; eauto 3 with slow.
  unfold equality_of_qnat, is_mqnat in *; repnd; dands; eauto 3 with slow.
  introv ext; apply h0 in ext; exrepnd; eauto.
Qed.

Lemma equality_of_qnat_bar_same {o} :
  forall lib (a : @CTerm o),
    equality_of_qnat_bar lib qlt_cond a a <=> is_mqnat_bar lib a.
Proof.
  introv; split; intro h; eapply in_open_bar_pres; eauto; clear h; introv ext h; eauto 3 with slow.
  apply equality_of_qnat_same; auto.
Qed.

Lemma type_mkc_qnatk {o} :
  forall uk (lib : @library o) (a : CTerm),
    type uk lib (mkc_qnatk a)
    <=> is_mqnat_bar lib a.
Proof.
  introv.
  unfold type.
  rw @tequality_mkc_qnatk.
  rw @equality_of_qnat_bar_same; tcsp.
Qed.

(*Lemma equality_of_qlt_bar_implies_equality_of_qnat_bar_left {o} :
  forall u v (lib : @library o) a b,
    equality_of_qlt_bar lib a b u v
    -> equality_of_qnat_bar lib qnat_mon_cond a a.
Proof.
  introv equ.
  eapply in_open_bar_pres; eauto; clear equ; introv ext equ.

unfold equality_of_qlt in *.
SearchAbout equality_of_qlt.
  eauto 3 with slow.
Qed.*)

(*Lemma equality_of_qlt_implies_equality_of_qnat_right {o} :
  forall (lib : @library o) a b c,
    equality_of_qlt lib a b
    -> equality_of_qnat lib c a a
    -> equality_of_qnat lib c b b.
Proof.
  introv equ h.
  unfold equality_of_qnat, equality_of_qlt in *.
  repnd; dands; eauto 3 with slow.

  { introv ext.
    applydup h0 in ext.
    applydup equ in ext; exrepnd.
    ccomputes_to_eqval.
    exists m; dands; spcast; eauto. }

  { introv q exta extb compa compb; subst.
    pose proof (equ _
Qed.*)

(*Lemma equality_of_qlt_bar_implies_equality_of_qnat_bar_right {o} :
  forall u v (lib : @library o) a b c,
    equality_of_qlt_bar lib a b u v
    -> equality_of_qnat_bar lib c  a a
    -> equality_of_qnat_bar lib c b b.
Proof.
  introv equ h.
  eapply in_open_bar_comb; eauto; clear h.
  eapply in_open_bar_pres; eauto; clear equ; introv ext equ h.


  unfold equality_of_qnat, equality_of_qlt in *.
  eauto 3 with slow.
Qed.*)

Lemma inhabited_type_bar_mkc_qlt {o} :
  forall uk (lib : @library o) a b,
    inhabited_type_bar uk lib (mkc_qlt a b)
    <->
    (in_open_bar lib (fun lib => equality_of_qlt lib a b)
     # equality_of_qnat_bar lib qlt_cond a a
     # equality_of_qnat_bar lib qlt_cond b b).
Proof.
  introv; split; intro equ; repnd.
  { unfold inhabited_type_bar in equ.
    repeat rw <- @in_open_bar_prod.
    apply collapse_all_in_ex_bar.
    eapply in_open_bar_pres; eauto; clear equ; introv ext equ.
    unfold inhabited_type in equ; exrepnd.
    apply equality_in_mkc_qlt in equ0.
    repeat rw <- @in_open_bar_prod in equ0; simpl in *; tcsp. }
  { apply in_ext_implies_in_open_bar; introv ext.
    unfold inhabited_type; exists (@mkc_axiom o).
    apply equality_in_mkc_qlt; dands; eauto 3 with slow. }
Qed.

Lemma equality_of_nat_preserves_equality_of_qnat_left {o} :
  forall (lib : @library o) a b c,
    equality_of_nat lib a b
    -> equality_of_qnat lib c a a.
Proof.
  introv equ.
  eapply equality_of_nat_implies_equality_of_qnat; eauto 3 with slow.
  unfold equality_of_nat in *; exrepnd; eauto.
Qed.
Hint Resolve equality_of_nat_preserves_equality_of_qnat_left : slow.

Lemma equality_of_nat_preserves_equality_of_qnat_right {o} :
  forall (lib : @library o) a b c,
    equality_of_nat lib a b
    -> equality_of_qnat lib c b b.
Proof.
  introv equ.
  eapply equality_of_nat_implies_equality_of_qnat; eauto 3 with slow.
  unfold equality_of_nat in *; exrepnd; eauto.
Qed.
Hint Resolve equality_of_nat_preserves_equality_of_qnat_right : slow.

Lemma equality_in_nat_preserves_equality_of_qnat_bar_left {o} :
  forall uk (lib : @library o) a b c,
    equality uk lib a b mkc_tnat
    -> equality_of_qnat_bar lib c a a.
Proof.
  introv equ h.
  apply equality_in_tnat in equ.
  eapply in_open_bar_comb; eauto; clear h.
  eapply in_open_bar_pres; eauto; clear equ.
  introv ext equ h; eauto 3 with slow.
Qed.
Hint Resolve equality_in_nat_preserves_equality_of_qnat_bar_left : slow.

Lemma equality_in_nat_preserves_equality_of_qnat_bar_right {o} :
  forall uk (lib : @library o) a b c,
    equality uk lib a b mkc_tnat
    -> equality_of_qnat_bar lib c b b.
Proof.
  introv equ h.
  apply equality_in_tnat in equ.
  eapply in_open_bar_comb; eauto; clear h.
  eapply in_open_bar_pres; eauto; clear equ.
  introv ext equ h; eauto 3 with slow.
Qed.
Hint Resolve equality_in_nat_preserves_equality_of_qnat_bar_right : slow.

Lemma equality_in_nat_preserves_equality_of_qnat_bar {o} :
  forall uk (lib : @library o) a b c,
    equality uk lib a b mkc_tnat
    -> equality_of_qnat_bar lib c a b.
Proof.
  introv equ h.
  apply equality_in_tnat in equ.
  eapply in_open_bar_comb; eauto; clear h.
  eapply in_open_bar_pres; eauto; clear equ.
  introv ext equ h; eauto 3 with slow.
Qed.
Hint Resolve equality_in_nat_preserves_equality_of_qnat_bar : slow.

Lemma equality_in_mkc_qnatk {o} :
  forall uk lib (a b : @CTerm o) n,
    equality uk lib a b (mkc_qnatk n)
    <=> (in_open_bar lib (fun lib : library => equality_of_qlt lib a n)
         # equality_of_qnat_bar lib qlt_cond n n
         # equality uk lib a b mkc_tnat).
Proof.
  introv; split; intro equ; repnd; dands; eauto 3 with slow; try (eapply equality_in_mkc_qnatk_implies; eauto).

  { rewrite mkc_qnatk_eq in equ.
    apply equality_in_set in equ; repnd; autorewrite with slow in *.
    apply inhabited_type_bar_mkc_qlt in equ2; repnd; auto. }

  rewrite mkc_qnatk_eq.
  apply equality_in_set; autorewrite with slow; dands; eauto 3 with slow.

  { introv ext eqn; autorewrite with slow.
    apply tequality_mkc_qlt; dands; eauto 3 with slow. }

  { eapply in_ext_implies_in_open_bar; introv ext.
    exists (@mkc_axiom o).
    apply equality_in_mkc_qlt; dands; eauto 3 with slow. }
Qed.

Lemma is_qnat_implies_are_same_qnats {o} :
  forall (lib : @library o) n c,
    is_qnat lib n
    -> are_same_qnats lib c n n.
Proof.
  introv h ext.
  apply h in ext; exrepnd; eauto.
Qed.
Hint Resolve is_qnat_implies_are_same_qnats : slow.

Lemma equality_qnatk2nat_implies {o} :
  forall uk lib (f g : @CTerm o) n,
    member uk lib n mkc_mqnat
    -> equality uk lib f g (mkc_qnatk2nat n)
    -> in_open_bar lib (fun lib => {z : nat
       , ccomputes_to_valc lib n (mkc_nat z)
       # in_open_bar lib (fun lib => forall m, m < z -> {k : nat
       , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
       # ccomputes_to_valc_ext lib (mkc_apply g (mkc_nat m)) (mkc_nat k)})}).
Proof.
  introv mn mem.
  apply equality_in_fun in mem; repnd.
  rw @type_mkc_qnatk in mem0.
  apply equality_in_qnat in mn.
  eapply in_open_bar_comb; try exact mn; clear mn.
  eapply in_open_bar_pres; try exact mem0; clear mem0.
  introv ext mem0 mn.
  unfold is_mqnat in mem0; repnd.
  pose proof (mem2 _ (lib_extends_refl _)) as w; simpl in *; exrepnd.

  exists n0; dands; auto.
  apply nat2in_open_bar2open.
  introv ltn.

  pose proof (mem _ ext (mkc_nat m) (mkc_nat m)) as mem.
  autodimp mem hyp.

  { apply equality_in_mkc_qnatk; dands; eauto 3 with slow.
    { apply in_ext_implies_in_open_bar; introv xta xtb.
      pose proof (mem2 _ (lib_extends_trans xtb xta)) as z; simpl in *; exrepnd.
      exists m n1; dands; spcast; eauto 3 with slow.

      unfold equality_of_qnat in mn; repnd.
      pose proof (mn lib' lib'1 n0 n1) as mn.
      repeat (autodimp mn hyp); eauto 3 with slow; try lia. }
    { apply in_ext_implies_in_open_bar; introv xta.
      unfold equality_of_qnat; dands; eauto 3 with slow. } }

  { eapply equality_in_tnat in mem.
    eapply in_open_bar_pres; try exact mem; clear mem; introv xt mem.
    unfold equality_of_nat in mem; exrepnd; eauto. }
Qed.

Lemma ccequivc_ext_mkc_squash_if {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_squash a) (mkc_squash b).
Proof.
  introv ceq ext.
  apply ceq in ext; spcast.
  apply implies_cequivc_mkc_squash; auto.
Qed.
Hint Resolve ccequivc_ext_mkc_squash_if : slow.
