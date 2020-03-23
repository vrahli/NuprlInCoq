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

Definition mkcv_mqnat {o} vs : @CVTerm o vs := mkcv_qnat vs qnat_mon_cond.
Definition mkc_mqnat {o} : @CTerm o := mkc_qnat qnat_mon_cond.
Definition mk_mqnat {o} : @NTerm o := mk_qnat qnat_mon_cond.

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

Definition ls3 {o} (A a b n : NVar) (i : nat) : @NTerm o :=
  mk_function
    (mk_csprop i)
    A
    (mk_function
       (mk_csname 0)
       a
       (mk_fun
          (mk_free_from_defs (mk_fun (mk_csname 0) (mk_uni i)) (mk_var A))
          (mk_fun
             (mk_apply (mk_var A) (mk_var a))
             (mk_exists
                mk_mqnat
                n
                (mk_function
                   (mk_csname 0)
                   b
                   (mk_fun
                      (mk_equality (mk_var a) (mk_var b) (mk_qnatk2nat (mk_var n)))
                      (mk_squash (mk_apply (mk_var A) (mk_var b))))))))).

Definition ls3c {o} (A a b n : NVar) (i : nat) : @CTerm o :=
  mkc_function
    (mkc_csprop i)
    A
    (mkcv_function
       _
       (mkcv_csname _ 0)
       a
       (mkcv_fun
          _
          (mkcv_free_from_defs
             _
             (mkcv_csprop _ i)
             (mk_cv_app_l [a] _ (mkc_var A)))
          (mkcv_fun
             _
             (mkcv_apply _ (mk_cv_app_l [a] _ (mkc_var A)) (mk_cv_app_r [A] _ (mkc_var a)))
             (mkcv_exists
                _
                (mkcv_mqnat _)
                n
                (mkcv_function
                   _
                   (mkcv_csname _ 0)
                   b
                   (mkcv_fun
                      _
                      (mkcv_equality
                         _
                         (mk_cv_app_r [A] _ (mk_cv_app_l [b,n] _ (mkc_var a)))
                         (mk_cv_app_r [n,a,A] _ (mkc_var b))
                         (mkcv_qnatk2nat _ (mk_cv_app_r [a,A] _ (mk_cv_app_l [b] _ (mkc_var n)))))
                      (mkcv_squash
                         _
                         (mkcv_apply
                            _
                            (mk_cv_app_l [b,n,a] _ (mkc_var A))
                            (mk_cv_app_r [n,a,A] _ (mkc_var b)))))))))).

Definition mk_lib_depth1 {o} : @NTerm o := mk_plus1 mk_lib_depth.
Definition mkc_lib_depth1 {o} : @CTerm o := mkc_plus1 mkc_lib_depth.
Definition mkcv_lib_depth1 {o} vs : @CVTerm o vs := mkcv_plus1 _ (mkcv_lib_depth _).

Definition ls3_extract {o} (A a x y b z : NVar) : @NTerm o :=
  mk_lam A (mk_lam a (mk_lam x (mk_lam y (mk_pair mk_lib_depth1 (mk_lam b (mk_lam z mk_axiom)))))).

Definition ls3c_extract {o} (A a x y b z : NVar) : @CTerm o :=
  mkc_lam A (mkcv_lam _ a (mkcv_lam _ x (mkcv_lam _ y (mkcv_pair _ (mkcv_lib_depth1 _) (mkcv_lam _ b (mkcv_lam _ z (mkcv_ax _))))))).

Lemma lsubstc_ls3_extract_eq {o} :
  forall A a x y b z (w : @wf_term o (ls3_extract A a x y b z)) s c,
    lsubstc (ls3_extract A a x y b z) w s c = ls3c_extract A a x y b z.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls3_extract_eq : slow.

Lemma isvalue_pair_aux1 {o} :
  forall b c,
    @isvalue o (mk_pair mk_lib_depth1 (mk_lam b (mk_lam c mk_axiom))).
Proof.
  introv.
  repeat (repeat constructor; simpl; introv xx; repndors; subst; tcsp).
Qed.
Hint Resolve isvalue_pair_aux1 : slow.

Lemma apply3_ls3c_extract_compute {o} :
  forall lib A a x y b c (u v w z : @CTerm o),
    computes_to_valc
      lib
      (mkc_apply (mkc_apply (mkc_apply (mkc_apply (ls3c_extract A a x y b c) u) v) w) z)
      (mkc_pair mkc_lib_depth1 (mkc_lam b (mkcv_lam _ c (mkcv_ax _)))).
Proof.
  introv; destruct_cterms; unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow;
    try apply isvalue_pair_aux1;[].

  eapply reduces_to_if_split2.
  { csunf; simpl; reflexivity. }

  eapply reduces_to_if_split2.
  { csunf; simpl.
    csunf; simpl.
    unfold apply_bterm; simpl.
    unflsubst; simpl; reflexivity. }

  eapply reduces_to_if_split2.
  { csunf; simpl.
    unfold apply_bterm; simpl.
    unflsubst; simpl; reflexivity. }

  eapply reduces_to_if_split2.
  { csunf; simpl.
    unfold apply_bterm; simpl.
    unflsubst; simpl; reflexivity. }

  unfold apply_bterm; simpl; unflsubst.
Qed.
Hint Resolve apply3_ls3c_extract_compute : slow.

Lemma apply3_ls3c_extract_ccequivc_ext {o} :
  forall lib A a x y b c (u v w z : @CTerm o),
    ccequivc_ext
      lib
      (mkc_apply (mkc_apply (mkc_apply (mkc_apply (ls3c_extract A a x y b c) u) v) w) z)
      (mkc_pair mkc_lib_depth1 (mkc_lam b (mkcv_lam _ c (mkcv_ax _)))).
Proof.
  introv ext; spcast; eauto 3 with slow.
Qed.
Hint Resolve apply3_ls3c_extract_ccequivc_ext : slow.

Lemma lsubstc_ls3_eq {o} :
  forall A a b n i (w : @wf_term o (ls3 A a b n i)) s c,
    lsubstc (ls3 A a b n i) w s c = ls3c A a b n i.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
  repeat rewrite remove_nvars_app_l; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls3_eq : slow.

Hint Rewrite @mkcv_le_substc2 : slow.
Hint Rewrite @mkcv_less_than_substc : slow.

Lemma implies_equality_in_int_implies_tequality_mkc_le {o} :
  forall lib (a b c d : @CTerm o),
    equality lib a b mkc_int
    -> equality lib c d mkc_int
    -> tequality lib (mkc_le a c) (mkc_le b d).
Proof.
  introv equa equb.
  allrw @equality_in_int.
  apply all_in_ex_bar_tequality_implies_tequality.
  eapply in_open_bar_comb;[|exact equa]; clear equa.
  eapply in_open_bar_pres;[|exact equb]; clear equb.
  introv ext equb eqa.
  unfold equality_of_int in *; exrepnd.
  eapply tequality_mkc_le_aux; eauto.
  destruct (Z_le_gt_dec k k0); [left|right]; dands; auto; try omega.
Qed.

Lemma zero_equal_in_int {o} :
  forall (lib : @library o),
    equality lib mkc_zero mkc_zero mkc_int.
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
  forall (ts : cts(o)) lib T a b T' eq,
    ts = univ
    -> ccomputes_to_valc_ext lib T (mkc_qlt a b)
    -> close ts lib T T' eq
    -> per_bar (per_qlt (close ts)) lib T T' eq.
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
  forall (lib : @library o) (a b c d : @CTerm o) eq,
    nuprl lib (mkc_qlt a b) (mkc_qlt c d) eq
    -> per_bar (per_qlt nuprl) lib (mkc_qlt a b) (mkc_qlt c d) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_qlt_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprl_qlt2 {o} :
  forall lib (eq : per(o)) a b c d,
    nuprl lib (mkc_qlt a b) (mkc_qlt c d) eq
    ->
    (eq <=2=> (per_bar_eq lib (equality_of_qlt_bar_lib_per lib a b))
     # equality_of_qnat_bar lib qnat_mon_cond a c
     # equality_of_qnat_bar lib qnat_mon_cond b d).
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
  forall (lib : @library o) a b c d,
    tequality lib (mkc_qlt a b) (mkc_qlt c d)
    <=>
    (
      equality_of_qnat_bar lib qnat_mon_cond a c
      # equality_of_qnat_bar lib qnat_mon_cond b d
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
  forall lib (a b : @CTerm o) c,
    equality lib a b (mkc_qnat c)
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
  forall lib (a b : @CTerm o),
    equality lib a b mkc_mqnat
    -> tequality lib (mkc_qnatk a) (mkc_qnatk b).
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
  forall lib (a b : @CTerm o) n,
    equality lib a b (mkc_qnatk n)
    -> equality lib a b mkc_tnat.
Proof.
  introv equ.
  rewrite mkc_qnatk_eq in equ.
  apply equality_in_set in equ; repnd; auto.
Qed.
Hint Resolve equality_in_mkc_qnatk_implies_equality_in_mkc_tnat : slow.

Lemma equality_nat2nat_to_qnatk2nat {o} :
  forall lib (n f g : @CTerm o),
    member lib n mkc_mqnat
    -> equality lib f g nat2nat
    -> equality lib f g (mkc_qnatk2nat n).
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
  forall (lib : @library o), tequality lib mkc_mqnat mkc_mqnat.
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
  rewrite <- Nat2Z.inj_add.
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
  rewrite <- Nat2Z.inj_add.
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
  forall lib (a b : @CTerm o),
    equality lib a b mkc_mqnat
    -> equality lib (mkc_plus1 a) (mkc_plus1 b) mkc_mqnat.
Proof.
  introv equ.
  unfold mkc_mqnat in *.
  allrw @equality_in_qnat.
  eapply in_open_bar_pres; eauto; clear equ; introv ext equ.
  unfold equality_of_qnat in *; repnd; dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve plus1_preserves_equality_in_mqnat : slow.

Lemma tequality_ls3c_aux7 {o} :
  forall (lib : @library o) a1 a'0 a'1 a2 a'2 a3,
    no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality lib a1 a'0 (mkc_csname 0)
    -> equality lib a2 a'1 mkc_mqnat
    -> equality lib a3 a'2 (mkc_csname 0)
    -> tequality lib (mkc_equality a1 a3 (mkc_qnatk2nat a2)) (mkc_equality a'0 a'2 (mkc_qnatk2nat a'1)).
Proof.
  introv norep safe sat; introv equb eque equf.

  apply tequality_mkc_equality_if_equal; eauto 3 with slow.

  { apply tequality_fun; dands; eauto 3 with slow. }

  { apply equality_refl in eque.
    apply equality_nat2nat_to_qnatk2nat; eauto 3 with slow. }

  { apply equality_refl in eque.
    apply equality_nat2nat_to_qnatk2nat; eauto 3 with slow. }
Qed.

Lemma tequality_ls3c_aux6 {o} :
  forall (lib : @library o) i a0 a' a1 a'0 a'1 a2 a'2 a3,
    no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality lib a0 a' (mkc_csprop i)
    -> equality lib a1 a'0 (mkc_csname 0)
    -> equality lib a2 a'1 mkc_mqnat
    -> equality lib a3 a'2 (mkc_csname 0)
    -> tequality
         lib
         (mkc_fun (mkc_equality a1 a3 (mkc_qnatk2nat a2)) (mkc_squash (mkc_apply a0 a3)))
         (mkc_fun (mkc_equality a'0 a'2 (mkc_qnatk2nat a'1)) (mkc_squash (mkc_apply a' a'2))).
Proof.
  introv norep safe sat; introv equa equb eque equf.

  apply tequality_fun; dands.

  { apply tequality_ls3c_aux7; auto. }

  introv extg equg.
  apply tequality_mkc_squash.
  apply inhabited_mkc_equality in equg.
  apply (equality_in_mkc_csprop_implies_tequality _ _ _ _ _ i); eauto 3 with slow.
Qed.

Lemma tequality_ls3c_aux5 {o} :
  forall (lib : @library o) A a b n i a0 a' a1 a'0 a'1 a2,
    A <> a
    -> n <> A
    -> n <> a
    -> b <> n
    -> b <> A
    -> b <> a
    -> no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality lib a0 a' (mkc_csprop i)
    -> equality lib a1 a'0 (mkc_csname 0)
    -> equality lib a2 a'1 mkc_mqnat
    -> tequality lib
    (mkc_function (mkc_csname 0) b
       (substc5 b a2 n a1 a a0 A
          (mkcv_fun (([b, n] ++ [a]) ++ [A])
             (mkcv_equality (([b, n] ++ [a]) ++ [A])
                (mk_cv_app_r [A] ([b, n] ++ [a])
                   (mk_cv_app_l [b, n] [a] (mkc_var a)))
                (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                (mkcv_qnatk2nat (([b] ++ [n]) ++ [a, A])
                   (mk_cv_app_r [a, A] ([b] ++ [n])
                      (mk_cv_app_l [b] [n] (mkc_var n)))))
             (mkcv_squash ([b, n, a] ++ [A])
             (mkcv_apply ([b, n, a] ++ [A]) (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))
    (mkc_function (mkc_csname 0) b
       (substc5 b a'1 n a'0 a a' A
          (mkcv_fun [b, n, a, A]
             (mkcv_equality (([b, n] ++ [a]) ++ [A])
                (mk_cv_app_r [A] ([b, n] ++ [a])
                   (mk_cv_app_l [b, n] [a] (mkc_var a)))
                (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                (mkcv_qnatk2nat (([b] ++ [n]) ++ [a, A])
                   (mk_cv_app_r [a, A] ([b] ++ [n])
                                (mk_cv_app_l [b] [n] (mkc_var n)))))
             (mkcv_squash ([b, n, a] ++ [A])
             (mkcv_apply [b, n, a, A] (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                (mk_cv_app_r [n, a, A] [b] (mkc_var b))))))).
Proof.
  introv da db dc dd de df norep safe sat; introv equa equb eque.

  apply tequality_function; dands; eauto 3 with slow.

  introv extf equf.
  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc5_mkcv_fun;auto|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc5_mkcv_fun;auto|].
  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_sym; apply mkcv_fun_substc|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_sym; apply mkcv_fun_substc|].
  autorewrite with slow.
  repeat (rewrite substc5_var2; auto;[]).
  repeat (rewrite substc5_var0; auto;[]).
  autorewrite with slow.

  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_mkc_fun;apply alphaeqc_sym;[|apply alphaeqc_refl];
     apply implies_alphaeqc_mkc_equality;[apply alphaeqc_refl|apply alphaeqc_refl|];
     apply substc_alphaeqcv; apply substc5_mkcv_qnatk2nat;auto|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_mkc_fun;apply alphaeqc_sym;[|apply alphaeqc_refl];
     apply implies_alphaeqc_mkc_equality;[apply alphaeqc_refl|apply alphaeqc_refl|];
     apply substc_alphaeqcv; apply substc5_mkcv_qnatk2nat;auto|].
  autorewrite with slow.

  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_mkc_fun;apply alphaeqc_sym;[|apply alphaeqc_refl];
     apply implies_alphaeqc_mkc_equality;[apply alphaeqc_refl|apply alphaeqc_refl|];
     apply substc_mkcv_qnatk2nat;auto|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_mkc_fun;apply alphaeqc_sym;[|apply alphaeqc_refl];
     apply implies_alphaeqc_mkc_equality;[apply alphaeqc_refl|apply alphaeqc_refl|];
     apply substc_mkcv_qnatk2nat;auto|].
  repeat (rewrite substc5_var1; auto;[]).
  autorewrite with slow.

  eapply tequality_ls3c_aux6; eauto 3 with slow.
Qed.

Lemma tequality_ls3c_aux4 {o} :
  forall (lib : @library o) A a b n i a0 a' a1 a'0,
    A <> a
    -> n <> A
    -> n <> a
    -> b <> n
    -> b <> A
    -> b <> a
    -> no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality lib a0 a' (mkc_csprop i)
    -> equality lib a1 a'0 (mkc_csname 0)
    -> tequality lib
    (mkc_product mkc_mqnat n
       (substc2 n a1 a
          (substc3 n a a0 A
             (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                (mkcv_fun (([b, n] ++ [a]) ++ [A])
                   (mkcv_equality (([b, n] ++ [a]) ++ [A])
                      (mk_cv_app_r [A] ([b, n] ++ [a])
                         (mk_cv_app_l [b, n] [a] (mkc_var a)))
                      (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                      (mkcv_qnatk2nat (([b] ++ [n]) ++ [a, A])
                         (mk_cv_app_r [a, A] ([b] ++ [n])
                            (mk_cv_app_l [b] [n] (mkc_var n)))))
                   (mkcv_squash ([b, n, a] ++ [A])
                   (mkcv_apply ([b, n, a] ++ [A])
                      (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                      (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))))
    (mkc_product mkc_mqnat n
       (substc2 n a'0 a
          (substc3 n a a' A
             (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                (mkcv_fun [b, n, a, A]
                   (mkcv_equality (([b, n] ++ [a]) ++ [A])
                      (mk_cv_app_r [A] ([b, n] ++ [a])
                         (mk_cv_app_l [b, n] [a] (mkc_var a)))
                      (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                      (mkcv_qnatk2nat (([b] ++ [n]) ++ [a, A])
                         (mk_cv_app_r [a, A] ([b] ++ [n])
                            (mk_cv_app_l [b] [n] (mkc_var n)))))
                   (mkcv_squash ([b, n, a] ++ [A])
                   (mkcv_apply [b, n, a, A] (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                      (mk_cv_app_r [n, a, A] [b] (mkc_var b))))))))).
Proof.
  introv da db dc dd de df norep safe sat; introv equa equb.

  apply tequality_product; dands; eauto 3 with slow;[].

  introv exte eque.
  repeat rewrite substc2_substc3_eq.
  repeat rewrite substc3_2_substc_eq.
  repeat (rewrite substc4_mkcv_function; tcsp; auto).
  autorewrite with slow.

  eapply tequality_ls3c_aux5; eauto 3 with slow.
Qed.

Lemma tequality_ls3c_aux3 {o} :
  forall (lib : @library o) A a b n i a0 a' a1 a'0,
    A <> a
    -> n <> A
    -> n <> a
    -> b <> n
    -> b <> A
    -> b <> a
    -> no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality lib a0 a' (mkc_csprop i)
    -> equality lib a1 a'0 (mkc_csname 0)
    -> tequality lib
    (mkc_fun (mkc_apply a0 a1)
          (substc2 a a0 A
             (mkcv_exists [a, A] (mkcv_mqnat [a, A]) n
                (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                   (mkcv_fun (([b, n] ++ [a]) ++ [A])
                      (mkcv_equality (([b, n] ++ [a]) ++ [A])
                         (mk_cv_app_r [A] ([b, n] ++ [a])
                            (mk_cv_app_l [b, n] [a] (mkc_var a)))
                         (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                         (mkcv_qnatk2nat (([b] ++ [n]) ++ [a, A])
                            (mk_cv_app_r [a, A] ([b] ++ [n])
                               (mk_cv_app_l [b] [n] (mkc_var n)))))
                      (mkcv_squash ([b, n, a] ++ [A])
                      (mkcv_apply ([b, n, a] ++ [A])
                         (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                         (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))) [[a \\ a1]])
    (mkc_fun (mkc_apply a' a'0)
          (substc2 a a' A
             (mkcv_exists [a, A] (mkcv_mqnat [a, A]) n
                (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                   (mkcv_fun [b, n, a, A]
                      (mkcv_equality (([b, n] ++ [a]) ++ [A])
                         (mk_cv_app_r [A] ([b, n] ++ [a])
                            (mk_cv_app_l [b, n] [a] (mkc_var a)))
                         (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                         (mkcv_qnatk2nat (([b] ++ [n]) ++ [a, A])
                            (mk_cv_app_r [a, A] ([b] ++ [n])
                               (mk_cv_app_l [b] [n] (mkc_var n)))))
                      (mkcv_squash ([b, n, a] ++ [A])
                      (mkcv_apply [b, n, a, A]
                         (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                         (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))) [[a \\ a'0]]).
Proof.
  introv da db dc dd de df norep safe sat; introv equa equb.

  apply tequality_fun; dands.

  { apply (equality_in_mkc_csprop_implies_tequality _ _ _ _ _ i); eauto; eauto 3 with slow. }

  introv extd equd.
  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;auto|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;auto|].
  repeat (rewrite mkcv_product_substc; auto;[]).
  autorewrite with slow.

  eapply tequality_ls3c_aux4; eauto 3 with slow.
Qed.

Lemma tequality_ls3c_aux2 {o} :
  forall (lib : @library o) A a b n i a0 a' a1 a'0,
    A <> a
    -> n <> A
    -> n <> a
    -> b <> n
    -> b <> A
    -> b <> a
    -> no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality lib a0 a' (mkc_csprop i)
    -> equality lib a1 a'0 (mkc_csname 0)
    -> tequality lib
    (mkc_fun
       (substc2 a a0 A
          (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) i)
             (mk_cv_app_l [a] [A] (mkc_var A)))) [[a \\ a1]]
       (substc2 a a0 A
          (mkcv_fun ([a] ++ [A])
             (mkcv_apply ([a] ++ [A]) (mk_cv_app_l [a] [A] (mkc_var A))
                (mk_cv_app_r [A] [a] (mkc_var a)))
                (mkcv_exists [a, A] (mkcv_mqnat [a, A]) n
                   (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                      (mkcv_fun (([b, n] ++ [a]) ++ [A])
                         (mkcv_equality (([b, n] ++ [a]) ++ [A])
                            (mk_cv_app_r [A] ([b, n] ++ [a])
                               (mk_cv_app_l [b, n] [a] (mkc_var a)))
                            (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                            (mkcv_qnatk2nat (([b] ++ [n]) ++ [a, A])
                               (mk_cv_app_r [a, A] ([b] ++ [n])
                                  (mk_cv_app_l [b] [n] (mkc_var n)))))
                         (mkcv_squash ([b, n, a] ++ [A])
                         (mkcv_apply ([b, n, a] ++ [A])
                            (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                            (mk_cv_app_r [n, a, A] [b] (mkc_var b))))))))) [[a \\
       a1]])
    (mkc_fun
       (substc2 a a' A
          (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) i)
             (mk_cv_app_l [a] [A] (mkc_var A)))) [[a \\ a'0]]
       (substc2 a a' A
          (mkcv_fun ([a] ++ [A])
             (mkcv_apply ([a] ++ [A]) (mk_cv_app_l [a] [A] (mkc_var A))
                (mk_cv_app_r [A] [a] (mkc_var a)))
                (mkcv_exists [a, A] (mkcv_mqnat [a, A]) n
                   (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                      (mkcv_fun [b, n, a, A]
                         (mkcv_equality (([b, n] ++ [a]) ++ [A])
                            (mk_cv_app_r [A] ([b, n] ++ [a])
                               (mk_cv_app_l [b, n] [a] (mkc_var a)))
                            (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                            (mkcv_qnatk2nat (([b] ++ [n]) ++ [a, A])
                               (mk_cv_app_r [a, A] ([b] ++ [n])
                                  (mk_cv_app_l [b] [n] (mkc_var n)))))
                         (mkcv_squash ([b, n, a] ++ [A])
                         (mkcv_apply [b, n, a, A]
                            (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                            (mk_cv_app_r [n, a, A] [b] (mkc_var b))))))))) [[a \\
       a'0]]).
Proof.
  introv da db dc dd de df norep safe sat; introv equa equb.

  apply tequality_fun; dands.

  { eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_ffdefs|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_ffdefs|].
    autorewrite with slow.
    apply tequality_mkc_ffdefs; dands; eauto 3 with slow. }

  introv extc equc.
  eapply inhabited_type_respects_alphaeqc in equc;
    [|apply substc_alphaeqcv; apply substc2_ffdefs].
  autorewrite with slow in equc.
  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_fun|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_fun|].
  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_sym; apply mkcv_fun_substc|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_sym; apply mkcv_fun_substc|].
  autorewrite with slow.
  repeat (rewrite substc2_mk_cv_app_r; auto;[]).
  autorewrite with slow.

  eapply tequality_ls3c_aux3; eauto 3 with slow.
Qed.

Lemma tequality_ls3c_aux1 {o} :
  forall (lib : @library o) A a b n i a0 a',
    A <> a
    -> n <> A
    -> n <> a
    -> b <> n
    -> b <> A
    -> b <> a
    -> no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality lib a0 a' (mkc_csprop i)
    -> tequality lib
                 (mkc_function (mkc_csname 0) a
       (substcv [a] a0 A
          (mkcv_fun ([a] ++ [A])
             (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) i)
                (mk_cv_app_l [a] [A] (mkc_var A)))
             (mkcv_fun ([a] ++ [A])
                (mkcv_apply ([a] ++ [A]) (mk_cv_app_l [a] [A] (mkc_var A))
                   (mk_cv_app_r [A] [a] (mkc_var a)))
                   (mkcv_exists [a, A] (mkcv_mqnat [a, A]) n
                      (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                         (mkcv_fun (([b, n] ++ [a]) ++ [A])
                            (mkcv_equality (([b, n] ++ [a]) ++ [A])
                               (mk_cv_app_r [A] ([b, n] ++ [a])
                                  (mk_cv_app_l [b, n] [a] (mkc_var a)))
                               (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                               (mkcv_qnatk2nat (([b] ++ [n]) ++ [a, A])
                                  (mk_cv_app_r [a, A] ([b] ++ [n])
                                     (mk_cv_app_l [b] [n] (mkc_var n)))))
                            (mkcv_squash ([b, n, a] ++ [A])
                            (mkcv_apply ([b, n, a] ++ [A])
                               (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                               (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))))))
    (mkc_function (mkc_csname 0) a
       (substcv [a] a' A
          (mkcv_fun ([a] ++ [A])
             (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) i)
                (mk_cv_app_l [a] [A] (mkc_var A)))
             (mkcv_fun ([a] ++ [A])
                (mkcv_apply ([a] ++ [A]) (mk_cv_app_l [a] [A] (mkc_var A))
                   (mk_cv_app_r [A] [a] (mkc_var a)))
                   (mkcv_exists [a, A] (mkcv_mqnat [a, A]) n
                      (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                         (mkcv_fun [b, n, a, A]
                            (mkcv_equality (([b, n] ++ [a]) ++ [A])
                               (mk_cv_app_r [A] ([b, n] ++ [a])
                                  (mk_cv_app_l [b, n] [a] (mkc_var a)))
                               (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                               (mkcv_qnatk2nat (([b] ++ [n]) ++ [a, A])
                                  (mk_cv_app_r [a, A] ([b] ++ [n])
                                     (mk_cv_app_l [b] [n] (mkc_var n)))))
                            (mkcv_squash ([b, n, a] ++ [A])
                            (mkcv_apply [b, n, a, A]
                               (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                               (mk_cv_app_r [n, a, A] [b] (mkc_var b))))))))))).
Proof.
  introv da db dc dd de df norep safe sat equa.

  apply tequality_function; dands; eauto 3 with slow.
  introv extb equb.
  repeat rewrite substcv_as_substc2.
  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_fun|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_fun|].
  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_sym; apply mkcv_fun_substc|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_sym; apply mkcv_fun_substc|].

  apply tequality_ls3c_aux2; eauto 3 with slow.
Qed.

Lemma tequality_ls3c {o} :
  forall (lib : @library o) A a b n i,
    A <> a
    -> n <> A
    -> n <> a
    -> b <> n
    -> b <> A
    -> b <> a
    -> no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> tequality lib (ls3c A a b n i) (ls3c A a b n i).
Proof.
  introv da db dc dd de df norep safe sat.
  unfold ls3c.

  apply tequality_function; dands; eauto 3 with slow.
  introv exta equa.
  repeat (rewrite substc_mkcv_function; auto); autorewrite with slow.

  apply tequality_ls3c_aux1; eauto 3 with slow.
Qed.

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
  lib_ext_ind ext Case; try omega.
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
  forall (lib : @library o), equality lib mkc_lib_depth mkc_lib_depth mkc_mqnat.
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
  forall (lib : @library o), equality lib mkc_lib_depth1 mkc_lib_depth1 mkc_mqnat.
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
  forall lib (a b : @CTerm o),
    equality_of_qlt lib a b
    -> are_same_qnats lib qnat_mon_cond a a.
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
  forall (lib : @library o) t u a b,
    equality lib t u (mkc_qlt a b)
    <=>
    (in_open_bar lib (fun lib => equality_of_qlt lib a b)
     # equality_of_qnat_bar lib qnat_mon_cond a a
     # equality_of_qnat_bar lib qnat_mon_cond b b).
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
  forall (lib : @library o) a n,
    inhabited_type_bar lib (mkc_qlt a n)
    -> in_open_bar lib (fun lib : library => equality_of_qlt lib a n).
Proof.
  introv h.
  apply collapse_all_in_ex_bar.
  eapply in_open_bar_pres; try exact h; clear h; introv ext h.
  unfold inhabited_type in *; exrepnd.
  apply equality_in_mkc_qlt in h0; repnd; auto.
Qed.

Lemma equality_in_mkc_qnatk_implies {o} :
  forall lib (a b : @CTerm o) n,
    equality lib a b (mkc_qnatk n)
    -> in_open_bar lib (fun lib : library => equality_of_qlt lib a n).
Proof.
  introv equ.
  rewrite mkc_qnatk_eq in equ.
  apply equality_in_set in equ; repnd; autorewrite with slow in *.
  apply inhabited_type_bar_implies in equ; auto.
Qed.

Lemma zero_in_nat {o} :
  forall (lib : @library o), equality lib mkc_zero mkc_zero mkc_tnat.
Proof.
  introv.
  allrw @mkc_zero_eq; eauto 3 with slow.
Qed.
Hint Resolve zero_in_nat : slow.

Definition is_mqnat {o} lib (t : @CTerm o) :=
  is_qnat lib t # sat_qnat_cond lib qnat_mon_cond t.

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
    equality_of_qnat lib qnat_mon_cond a b
    -> is_mqnat lib a.
Proof.
  introv h; unfold equality_of_qnat, is_mqnat in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_implies_is_mqnat_left : slow.

Lemma equality_of_qnat_bar_implies_is_qnat_bar_left {o} :
  forall (lib : @library o) a b,
    equality_of_qnat_bar lib qnat_mon_cond a b
    -> is_mqnat_bar lib a.
Proof.
  introv equ.
  eapply in_open_bar_pres; eauto; clear equ.
  introv ext equ; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_bar_implies_is_qnat_bar_left : slow.

Lemma equality_of_qnat_implies_is_qnat_right {o} :
  forall (lib : @library o) a b,
    equality_of_qnat lib qnat_mon_cond a b
    -> is_mqnat lib b.
Proof.
  introv h; unfold equality_of_qnat, is_mqnat in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_implies_is_qnat_right : slow.

Lemma equality_of_qnat_bar_implies_is_qnat_bar_right {o} :
  forall (lib : @library o) a b,
    equality_of_qnat_bar lib qnat_mon_cond a b
    -> is_mqnat_bar lib b.
Proof.
  introv equ.
  eapply in_open_bar_pres; eauto; clear equ.
  introv ext equ; eauto 3 with slow.
Qed.
Hint Resolve equality_of_qnat_bar_implies_is_qnat_bar_right : slow.

Lemma tequality_mkc_qnatk {o} :
  forall (lib : @library o) (a b : CTerm),
    tequality lib (mkc_qnatk a) (mkc_qnatk b)
    <=> equality_of_qnat_bar lib qnat_mon_cond a b.
Proof.
  introv; repeat rewrite mkc_qnatk_eq.
  rw @tequality_set.
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
    equality_of_qnat lib qnat_mon_cond a a <=> is_mqnat lib a.
Proof.
  introv; split; intro h; eauto 3 with slow.
  unfold equality_of_qnat, is_mqnat in *; repnd; dands; eauto 3 with slow.
  introv ext; apply h0 in ext; exrepnd; eauto.
Qed.

Lemma equality_of_qnat_bar_same {o} :
  forall lib (a : @CTerm o),
    equality_of_qnat_bar lib qnat_mon_cond a a <=> is_mqnat_bar lib a.
Proof.
  introv; split; intro h; eapply in_open_bar_pres; eauto; clear h; introv ext h; eauto 3 with slow.
  apply equality_of_qnat_same; auto.
Qed.

Lemma type_mkc_qnatk {o} :
  forall (lib : @library o) (a : CTerm),
    type lib (mkc_qnatk a)
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

Lemma in_open_bar_prod {o} :
  forall lib (F G : @library o -> Prop),
    in_open_bar lib (fun lib => F lib # G lib)
    <=> (in_open_bar lib F # in_open_bar lib G).
Proof.
  introv; split.
  { introv h; dands; eapply in_open_bar_pres; eauto; clear h; introv ext h; tcsp. }
  { intro h; repnd; eapply in_open_bar_comb; eauto; clear h.
    eapply in_open_bar_pres; eauto; clear h0; introv ext h q; tcsp. }
Qed.

Lemma inhabited_type_bar_mkc_qlt {o} :
  forall (lib : @library o) a b,
    inhabited_type_bar lib (mkc_qlt a b)
    <->
    (in_open_bar lib (fun lib => equality_of_qlt lib a b)
     # equality_of_qnat_bar lib qnat_mon_cond a a
     # equality_of_qnat_bar lib qnat_mon_cond b b).
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
  forall (lib : @library o) a b c,
    equality lib a b mkc_tnat
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
  forall (lib : @library o) a b c,
    equality lib a b mkc_tnat
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
  forall (lib : @library o) a b c,
    equality lib a b mkc_tnat
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
  forall lib (a b : @CTerm o) n,
    equality lib a b (mkc_qnatk n)
    <=> (in_open_bar lib (fun lib : library => equality_of_qlt lib a n)
         # equality_of_qnat_bar lib qnat_mon_cond n n
         # equality lib a b mkc_tnat).
Proof.
  introv; split; intro equ; repnd; dands; eauto 3 with slow; try (eapply equality_in_mkc_qnatk_implies; eauto).

  { rewrite mkc_qnatk_eq in equ.
    apply equality_in_set in equ; repnd; autorewrite with slow in *.
    apply inhabited_type_bar_mkc_qlt in equ; repnd; auto. }

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
  forall lib (f g : @CTerm o) n,
    equality lib f g (mkc_qnatk2nat n)
    -> in_open_bar lib (fun lib => {z : nat
       , ccomputes_to_valc lib n (mkc_nat z)
       # in_open_bar lib (fun lib => forall m, m < z -> {k : nat
       , ccomputes_to_valc_ext lib (mkc_apply f (mkc_nat m)) (mkc_nat k)
       # ccomputes_to_valc_ext lib (mkc_apply g (mkc_nat m)) (mkc_nat k)})}).
Proof.
  introv mem.
  apply equality_in_fun in mem; repnd.
  rw @type_mkc_qnatk in mem0.
  eapply in_open_bar_pres; try exact mem0; clear mem0.
  introv ext mem0.
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
      pose proof (mem0 lib' lib'1 n0 n1) as mem0.
      repeat (autodimp mem0 hyp); eauto 3 with slow; try omega. }
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



(* *************************************************************** *)
(* ****** LS3 ****** *)

Definition rule_ls3 {o}
           (lib : @library o)
           (A a b n x y z : NVar)
           (i : nat)
           (H : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ls3 A a b n i) (ls3_extract A a x y b z)))
    []
    [].

Lemma rule_ls3_true {o} :
  forall (lib : library)
         (A a b n x y z : NVar) (i : nat) (H : @bhyps o)
         (d1 : A <> a)
         (d2 : n <> A)
         (d3 : n <> a)
         (d4 : b <> n)
         (d5 : b <> A)
         (d6 : b <> a)
         (d7 : x <> b)
         (safe  : strong_safe_library lib)
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (satd  : lib_cond_sat_def lib)
         (nocs  : has_lib_cond_no_cs lib),
    rule_true lib (rule_ls3 lib A a b n x y z i H).
Proof.
  unfold rule_ls3, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (ls3_extract A a x y b z) (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp; introv h; autorewrite with slow in *; simpl in *; tcsp. }
  exists cv.

  vr_seq_true.
  autorewrite with slow.
  move2ext ext.

  dands.

  { apply tequality_ls3c; eauto 3 with slow. }

  apply equality_in_function3.
  dands; eauto 3 with slow;[].

  intros lib' ext A1 A2 eqA.
  move2ext ext.

  dands.

  { repeat (rewrite substc_mkcv_function; auto); autorewrite with slow.
    eapply tequality_ls3c_aux1; eauto 3 with slow. }

  rewrite substc_mkcv_function; auto;[].
  autorewrite with slow.

  rewrite substcv_as_substc2.

  apply equality_in_function3.
  dands; eauto 3 with slow;[].

  intros lib' ext a1 a2 eqa.

  eapply equality_monotone in eqA;[|eauto];[].
  move2ext ext.

  dands.

  { repeat rewrite substcv_as_substc2.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_fun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_fun|].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].
    apply tequality_ls3c_aux2; eauto 3 with slow.
    apply equality_refl in eqA; eauto 3 with slow. }

  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_fun].
  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym; apply mkcv_fun_substc].

  unfold mkcv_exists.
  autorewrite with slow.
  repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
  autorewrite with slow.

  apply equality_in_fun.
  dands.

  { eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_ffdefs|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_ffdefs|].
    autorewrite with slow.
    apply tequality_mkc_ffdefs; dands; eauto 3 with slow.
    apply equality_refl in eqA; eauto 3 with slow. }

  { introv extc equc.
    eapply inhabited_type_respects_alphaeqc in equc;
      [|apply substc_alphaeqcv; apply substc2_ffdefs].
    autorewrite with slow in equc.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_fun|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_fun|].
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].
    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.
    eapply tequality_ls3c_aux3; eauto 3 with slow;
      apply equality_refl in eqa; eauto 3 with slow;
      apply equality_refl in eqA; eauto 3 with slow. }

  intros lib' ext x1 x2 eqx.

  eapply alphaeqc_preserving_equality in eqx;
    [|apply substc_alphaeqcv; apply substc2_ffdefs].
  autorewrite with slow in *.

  dup eqx as eqf.
  apply equality_in_mkc_ffdefs in eqx; exrepnd.
  clear eqx0 eqx1.

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqa;[|eauto];[].
  move2ext ext.

  eapply alphaeqc_preserving_equality;
    [|apply substc_alphaeqcv;apply alphaeqcv_sym;apply substc2_fun];[].
  autorewrite with slow.
  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym; apply mkcv_fun_substc].
  repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
  autorewrite with slow.

  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact eqx2]; clear eqx2; introv ext eqx2.

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqa;[|eauto];[].
  eapply equality_monotone in eqx;[|eauto];[].
  eapply equality_monotone in eqf;[|eauto];[].

  unfold ex_nodefsc_eq in *; exrepnd.
  rename eqx1 into eqw.
  rename eqx0 into nodefs.

  move2ext ext.

  apply equality_in_fun.
  dands.

  { apply equality_refl in eqa; apply equality_refl in eqA.
    eapply equality_in_mkc_csprop_implies_tequality; eauto. }

  { introv xt inh.
    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;auto|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply substc_alphaeqcv; apply substc2_product;auto|].
    repeat (rewrite mkcv_product_substc; auto;[]).
    autorewrite with slow.

    apply equality_refl in eqa; apply equality_refl in eqA;
      eapply tequality_ls3c_aux4; eauto 3 with slow. }

  intros lib' ext z1 z2 eqz.

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqa;[|eauto];[].
  eapply equality_monotone in eqx;[|eauto];[].
  eapply equality_monotone in eqf;[|eauto];[].
  eapply equality_monotone in eqw;[|eauto];[].

  move2ext ext.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply apply3_ls3c_extract_ccequivc_ext|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply apply3_ls3c_extract_ccequivc_ext|].

  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym;apply substc_alphaeqcv;apply substc2_product;tcsp];[].

(*
  apply equality_in_mkc_squash_ax.
  apply equality_refl in eqA.
  apply equality_refl in eqa.
  apply equality_refl in eqx.
  apply equality_refl in eqf.
  apply equality_refl in eqz.
  GC.

  clear eqA.
  rename eqw into eqA.

  eapply inhabited_type_bar_respects_alphaeqc;
    [apply alphaeqc_sym;apply substc_alphaeqcv;apply substc2_product;tcsp|];[].
*)

  rewrite mkcv_product_substc; auto;[].
  autorewrite with slow.

  apply equality_in_product; dands; eauto 3 with slow.

  { introv xt eqq.
    repeat rewrite substc2_substc3_eq.
    repeat rewrite substc3_2_substc_eq.
    repeat (rewrite substc4_mkcv_function; tcsp; auto).
    autorewrite with slow.
    apply equality_refl in eqz; apply equality_refl in eqA; apply equality_refl in eqf;
      eapply tequality_ls3c_aux5; eauto 3 with slow.
    apply equality_refl in eqa; eauto 3 with slow. }


(*
XXXXXXXXXX
  apply equality_in_csname in eqa.
  unfold equality_of_csname_bar in eqa.
  apply all_in_ex_bar_inhabited_type_bar_implies_inhabited_type_bar.
  eapply all_in_ex_bar_modus_ponens1;[|exact eqa]; clear eqa; introv ext eqa.

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqf;[|eauto];[].
  eapply member_monotone in eqz;[|eauto];[].
  move2ext ext.

  unfold equality_of_csname in eqa; exrepnd; GC; spcast.

  eapply member_respects_cequivc_type in eqz;
    [|apply implies_ccequivc_ext_apply;
      [apply ccequivc_ext_refl
      |apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto]
    ];[].

  eapply inhabited_type_bar_cequivc;
    [apply ccequivc_ext_sym;
     apply implies_ccequivc_ext_product;
     [apply ccequivc_ext_refl
     |apply implies_bcequivc_ext_substc2_1;
      apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto]
    |].

  clear a1 eqa2.

  applydup (@equality_in_mkc_csprop_implies_tequality_cs o name) in eqA as teq; auto;[].
  eapply tequality_preserves_member in eqz;[|eauto].

  applydup @inhabited_implies_tequality in eqz as tya.
  apply types_converge in tya.
  eapply all_in_ex_bar_modus_ponens1;[|exact tya]; clear tya; introv ext tya.
  unfold chaltsc in tya; spcast.
  apply hasvaluec_implies_computes_to_valc in tya; exrepnd.

  eapply member_monotone in eqz;[|eauto];[].
  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqf;[|eauto];[].
  eapply member_monotone in eqz;[|eauto];[].
  eapply tequality_monotone in teq;[|eauto];[].
  move2ext ext.

  apply inhabited_product.
  dands; eauto 3 with slow;[|].

  { introv exte eque.
    repeat rewrite substc2_substc3_eq.
    repeat rewrite substc3_2_substc_eq.
    repeat (rewrite substc4_mkcv_function; tcsp; auto).
    autorewrite with slow.
    apply equality_refl in eqz; apply equality_refl in eqA; apply equality_refl in eqf;
      eapply tequality_ls3c_aux5; eauto 3 with slow. }


  (* ****************** *)
  (* Could we get rid of the squash here and use:

       [mkcv_swap_cs1 _ (mkcv_choice_seq _ name) (mkc_var b) z1]

     instead of [mkcv_ax] ?*)
  (* ****************** *)
  exists (@mkc_pair
            o
            (mkc_nat (S (lib_depth lib)))
            (mkc_lam b (mkcv_lam _ x (mkcv_ax _)))).

*)



  apply in_ext_implies_all_in_ex_bar.
  introv ext.
  eexists; eexists; eexists; eexists; dands;
    try (apply ccomputes_to_valc_ext_refl; eauto 3 with slow); eauto 3 with slow.

  rewrite substc2_substc3_eq.
  rewrite substc3_2_substc_eq.
  rewrite substc4_mkcv_function; tcsp.
  autorewrite with slow.

  eapply alphaeqc_preserving_equality;
    [|apply implies_alphaeqc_mk_function;
      apply alphaeqcv_sym;
      apply substc5_mkcv_fun];[].

(*
XXXXXXXXXX

  exists (@mkc_nat o (S (lib_depth lib))) (@mkc_lam o b (mkcv_lam _ x (mkcv_ax _))).
  dands; spcast; eauto 3 with slow;[].

  eapply equality_monotone in eqA;[|eauto];[].
(*  eapply member_monotone in eqz;[|eauto];[].*)

  assert (strong_safe_library lib') as safe' by eauto 3 with slow.
  assert (lib_nodup lib') as nodup' by eauto 3 with slow.
  assert (sat_lib_cond lib') as sat' by eauto 3 with slow.
  assert (has_lib_cond_no_cs lib') as nocs' by eauto 3 with slow.

  rename lib into lib1.
  rename safe into safe1.
  rename nodup into nodup1.
  rename sat into sat1.
  rename nocs into nocs1.

  rename lib' into lib.
  rename safe' into safe.
  rename nodup' into nodup.
  rename sat' into sat.
  rename nocs' into nocs.

  rewrite substc2_substc3_eq.
  rewrite substc3_2_substc_eq.
  rewrite substc4_mkcv_function; tcsp.
  autorewrite with slow.

  eapply member_respects_alphaeqc_r;
    [apply implies_alphaeqc_mk_function;
     apply alphaeqcv_sym;
     apply substc5_mkcv_fun|].
*)

  autorewrite with slow.
  rewrite substc5_var2; tcsp;[].
  rewrite substc5_var0; tcsp;[].

  eapply alphaeqc_preserving_equality;
    [|apply implies_alphaeqc_mk_function;
      apply implies_alphaeqcv_mkcv_fun;
      [|apply alphaeqcv_refl];
      apply implies_alphaeqcv_mkcv_equality;
      [apply alphaeqcv_refl|apply alphaeqcv_refl|];
      apply alphaeqcv_sym;apply substc5_mkcv_qnatk2nat
    ];[].

(*
  eapply member_respects_alphaeqc_r;
    [apply implies_alphaeqc_mk_function;
     apply implies_alphaeqcv_mkcv_fun;
     [|apply alphaeqcv_refl];
     apply implies_alphaeqcv_mkcv_equality;
     [apply alphaeqcv_refl|apply alphaeqcv_refl|];
     apply alphaeqcv_sym;apply substc5_mkcv_natk2nat
    |];[].
*)
  autorewrite with slow.
  rewrite substc5_var1; tcsp;[].

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqa;[|eauto];[].
  eapply equality_monotone in eqx;[|eauto];[].
  eapply equality_monotone in eqf;[|eauto];[].
  eapply equality_monotone in eqw;[|eauto];[].
  eapply equality_monotone in eqz;[|eauto];[].
  move2ext ext.

  apply equality_refl in eqA.
  apply equality_refl in eqa.
  apply equality_refl in eqx.
  apply equality_refl in eqf.
  apply equality_refl in eqz.
  GC.

  clear eqA.
  rename eqw into eqA.

  apply equality_in_csname in eqa.
  unfold equality_of_csname_bar in eqa.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact eqa]; clear eqa; introv ext eqa.
  unfold equality_of_csname in eqa; exrepnd; GC; spcast.

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqf;[|eauto];[].
  eapply equality_monotone in eqz;[|eauto];[].
  eapply lib_extends_preserves_ccomputes_to_valc in eqa2;[|eauto].
  move2ext ext.

  rev_assert (member
                lib
                (mkc_lam b (mkcv_lam [b] z (mkcv_ax _)))
                (mkc_function
                   (mkc_csname 0)
                   b
                   (mkcv_fun
                      [b]
                      (mkcv_equality
                         [b]
                         (mk_cv [b] (mkc_choice_seq name))
                         (mkc_var b)
                         (mkcv_qnatk2nat [b] (mk_cv [b] mkc_lib_depth1)))
                      (mkcv_squash _ (mkcv_apply [b] (mk_cv [b] u) (mkc_var b)))))) mem.
  {
    apply equality_in_function3 in mem; repnd.
    apply equality_in_function3; dands; auto; eauto 3 with slow.
    introv xt ea.
    pose proof (mem _ xt _ _ ea) as mem; repnd.
    dands.

    {
      eapply tequality_respects_alphaeqc_left; [apply alphaeqc_sym;apply substc_mkcv_fun|].
      eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_fun|].
      eapply tequality_respects_alphaeqc_left  in mem1;[|apply substc_mkcv_fun].
      eapply tequality_respects_alphaeqc_right in mem1;[|apply substc_mkcv_fun].
      autorewrite with slow in *.

      apply tequality_fun in mem1; repnd.
      apply tequality_fun; dands; auto.
      { eapply tequality_respects_cequivc_left;
          [apply ccequivc_ext_sym;apply implies_ccequivc_ext_equality;
           [apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto 3 with slow
           |apply ccequivc_ext_refl
           |apply ccequivc_ext_refl]
          |].
        eapply tequality_respects_cequivc_right;
          [apply ccequivc_ext_sym;apply implies_ccequivc_ext_equality;
           [apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto 3 with slow
           |apply ccequivc_ext_refl
           |apply ccequivc_ext_refl]
          |].
        auto. }
      introv xt1 inh.
      eapply lib_extends_preserves_ccomputes_to_valc in eqa2;[|eauto].
      eapply lib_extends_preserves_ccomputes_to_valc in eqa2;[|eauto].
      pose proof (mem1 _ xt1) as mem1; autodimp mem1 hyp.
      { eapply inhabited_type_respects_cequivc in inh;
          [|apply implies_ccequivc_ext_equality;
            [apply ccomputes_to_valc_ext_implies_ccequivc_ext;try exact eqa2
            |apply ccequivc_ext_refl
            |apply ccequivc_ext_refl]
          ]; tcsp. }
      allrw @tequality_mkc_squash.
      eapply equality_in_mkc_csprop_preserves_tequality;
        [apply equality_sym| |]; eauto 3 with slow.
    }

    {
      eapply tequality_preserving_equality;[exact mem|].
      eapply tequality_respects_alphaeqc_left; [apply alphaeqc_sym;apply substc_mkcv_fun|].
      eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_fun|].
      eapply tequality_respects_alphaeqc_left  in mem1;[|apply substc_mkcv_fun].
      eapply tequality_respects_alphaeqc_right in mem1;[|apply substc_mkcv_fun].
      autorewrite with slow in *.

      apply tequality_fun in mem1; repnd.
      apply tequality_fun; dands; auto.
      { eapply tequality_respects_cequivc_left;
          [apply ccequivc_ext_sym;apply implies_ccequivc_ext_equality;
           [apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto 3 with slow
           |apply ccequivc_ext_refl
           |apply ccequivc_ext_refl]
          |].
        eapply tequality_respects_cequivc_right;
          [apply ccequivc_ext_sym;apply implies_ccequivc_ext_equality;
           [apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto 3 with slow
           |apply ccequivc_ext_refl
           |apply ccequivc_ext_refl]
          |].
        apply tequality_refl in mem2; auto. }
      introv xt1 inh.
      eapply lib_extends_preserves_ccomputes_to_valc in eqa2;[|eauto].
      eapply lib_extends_preserves_ccomputes_to_valc in eqa2;[|eauto].
      pose proof (mem1 _ xt1) as mem1; autodimp mem1 hyp;[].
      allrw @tequality_mkc_squash.

      eapply equality_monotone in eqA;[|eauto];[].
      eapply equality_monotone in eqA;[|eauto];[].
      eapply equality_monotone in ea;[|eauto];[].
      apply equality_refl in ea.
      apply tequality_sym.
      eapply equality_in_mkc_csprop_implies_tequality; eauto.
    }
  }

  pose proof (equality_in_mkc_csprop_implies_tequality lib A1 u (mkc_choice_seq name) (mkc_choice_seq name) i) as teq.
  repeat (autodimp teq hyp); eauto 3 with slow.
  eapply cequivc_preserving_equality in eqz;
    [|apply implies_ccequivc_ext_apply;[apply ccequivc_ext_refl|apply ccomputes_to_valc_ext_implies_ccequivc_ext; eauto] ].
  eapply tequality_preserving_equality in eqz;[|eauto].

  apply equality_sym in eqA; apply equality_refl in eqA.
  clear dependent A1.

  apply equality_in_function3; dands; eauto 3 with slow;[].

  introv ext1 ecs.
  rename a0 into b1.
  rename a' into b2.
  dands.

  { eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply mkcv_fun_substc|].
    autorewrite with slow.
  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_mkc_fun;apply alphaeqc_sym;[|apply alphaeqc_refl];
     apply implies_alphaeqc_mkc_equality;[apply alphaeqc_refl|apply alphaeqc_refl|];
     apply substc_mkcv_qnatk2nat;auto|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_mkc_fun;apply alphaeqc_sym;[|apply alphaeqc_refl];
     apply implies_alphaeqc_mkc_equality;[apply alphaeqc_refl|apply alphaeqc_refl|];
     apply substc_mkcv_qnatk2nat;auto|].
  autorewrite with slow.
  eapply tequality_ls3c_aux6; eauto 3 with slow. }

  eapply alphaeqc_preserving_equality;[|apply alphaeqc_sym;apply substc_mkcv_fun].
  autorewrite with slow.
  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym;apply alphaeqc_mkc_fun;
      [|apply alphaeqc_refl];
      apply implies_alphaeqc_mkc_equality;
      [apply alphaeqc_refl|apply alphaeqc_refl|];
      apply substc_mkcv_qnatk2nat].
  autorewrite with slow.

  eapply member_monotone in eqA;[|exact ext1];[].
  eapply member_monotone in eqz;[|exact ext1];[].
  move2ext ext1.

  apply equality_in_fun.
  dands; eauto 3 with slow.

  { apply equality_refl in ecs; apply tequality_ls3c_aux7; eauto 3 with slow. }

  { apply equality_refl in ecs; introv extg equg.
    apply inhabited_mkc_equality in equg.
    apply implies_type_mkc_squash.
    apply (equality_in_mkc_csprop_implies_tequality _ _ _ _ _ i); eauto 3 with slow. }

  introv ext2 eb.

  eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym;apply ccequivc_app_app_ax|].
  eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym;apply ccequivc_app_app_ax|].

  apply equality_refl in ecs.
  clear b2.
  apply equality_in_mkc_equality in eb; repnd.
  clear eb eb1.
  rw @member_eq.

  eapply member_monotone in ecs;[|exact ext2];[].
  eapply member_monotone in eqA;[|exact ext2];[].
  eapply member_monotone in eqz;[|exact ext2];[].
  move2ext ext2.

  apply equality_in_csname_iff in ecs.
  unfold equality_of_csname_bar in ecs.
  apply all_in_ex_bar_member_implies_member.
  eapply in_open_bar_pres; try exact ecs; clear ecs; introv ext exc.
  eapply equality_monotone in eb0;[|exact ext];[].
  eapply member_monotone in eqA;[|exact ext];[].
  eapply member_monotone in eqz;[|exact ext];[].
  move2ext ext.

  unfold equality_of_csname in *; exrepnd; GC.
  rename name0 into name'.
  eapply member_respects_cequivc_type;
    [apply ccequivc_ext_mkc_squash_if;
     apply implies_ccequivc_ext_apply;
     [apply ccequivc_ext_refl|apply ccequivc_ext_sym;apply ccomputes_to_valc_ext_implies_ccequivc_ext;eauto]
    |].

  apply equality_qnatk2nat_implies in eb0.

  apply all_in_ex_bar_member_implies_member.
  eapply in_open_bar_pres; try exact eb0; clear eb0; introv ext eb0; exrepnd.
  eapply member_monotone in eqA;[|exact ext];[].
  eapply member_monotone in eqz;[|exact ext];[].
  eapply lib_extends_preserves_ccomputes_to_valc in exc2;[|exact ext];[].
  move2ext ext.

  apply all_in_ex_bar_member_implies_member.
  eapply in_open_bar_pres; try exact eb1; clear eb1; introv ext eb1; exrepnd.
  rename lib into lib1.
  rename lib' into lib.
  eapply lib_extends_preserves_ccomputes_to_valc in exc2;[|exact ext];[].

  spcast.
  pose proof (computes_to_valc_lib_depth1 lib1) as comp.
  computes_to_eqval.

  assert (forall m,
             m <= lib_depth lib1
             ->
             {k : nat
             , ccomputes_to_valc_ext lib (mkc_apply (mkc_choice_seq name) (mkc_nat m)) (mkc_nat k)
             # ccomputes_to_valc_ext lib (mkc_apply (mkc_choice_seq name') (mkc_nat m)) (mkc_nat k)}) as imp.
  {
    introv h; pose proof (eb1 m) as eb1; autodimp eb1 hyp; try omega; exrepnd.
    exists k; dands; spcast; auto.
    eapply implies_ccomputes_to_valc_ext_left; eauto.
  }
  clear dependent b1.

  assert (forall m,
             m <= lib_depth lib1
             ->
             {k : nat
              , find_cs_value_at lib name  m = Some (mkc_nat k)
              # find_cs_value_at lib name' m = Some (mkc_nat k)}) as imp'.
  {
    introv h; apply imp in h; exrepnd.
    exists k.
    apply ccomputes_to_valc_ext_nat_implies_ccomputes_to_valc in h1.
    apply ccomputes_to_valc_ext_nat_implies_ccomputes_to_valc in h0.
    spcast.
    apply computes_to_valc_nat_implies_find_cs_value_at_if_safe in h1; auto; eauto 3 with slow.
    apply computes_to_valc_nat_implies_find_cs_value_at_if_safe in h0; auto; eauto 3 with slow.
  }
  clear dependent imp.
  rename imp' into imp.

  assert (forall m,
             m <= lib_depth lib1
             ->
             {k : nat
              & find_cs_value_at lib name  m = Some (mkc_nat k)
              # find_cs_value_at lib name' m = Some (mkc_nat k)}) as imp'.
  {
    introv h; apply imp in h; exrepnd.
    apply ex_find_cs_value_at; auto.
  }
  clear dependent imp.
  rename imp' into imp.

  apply equality_in_mkc_squash_ax.
  apply inhabited_type_implies_inhabited_type_bar.
  exists (swap_cs_cterm (name,name') z1).


  (* === We might have to squash the application in the conclusion === *)

  (* === We have to show that because of [imp], [lib1] can be extended with [name']
         equivalent to [name] up to [lib_depth lib1] === *)

  destruct (choice_sequence_name_deq name' name) as [d|d];
    [subst; autorewrite with slow; eauto 3 with slow|];[].

  (* We will have to restrict [compatible_choice_sequence_name] to disallow sequences for those: *)

  assert (is_nat_cs name) as isna by eauto 3 with slow.
  assert (is_nat_cs name') as isnb by eauto 3 with slow.

  pose proof (to_library_with_equal_cs name name' lib lib1) as q.
  repeat (autodimp q hyp);[].
  exrepnd.

  assert (strong_safe_library lib0) as safe' by eauto 3 with slow.
  assert (lib_nodup lib0) as nodup' by eauto 3 with slow.
  assert (sat_lib_cond lib0) as sat' by eauto 3 with slow.
  assert (has_lib_cond_no_cs lib0) as nocs' by eauto 3 with slow.

  (* WARNING *)
  eapply member_monotone in eqz; try exact q1.
  clear dependent lib1.

  assert (sane_swapping (name, name')) as sane by eauto 3 with slow.
  apply (implies_member_swap_cs (name,name')) in eqz; auto.
  simpl in *; autorewrite with slow in *.
  rewrite (swap_cs_cterm_if_nodefsc _ u) in eqz; auto.

  pose proof (swapped_css_plib_trivial_no_cs (name,name') (lib_cond lib0) lib0) as q; simpl in q.
  repeat (autodimp q hyp); dands; eauto 3 with slow.

  assert (swapped_css_libs name name' (swap_cs_lib (name,name') lib0) lib0) as perm.
  { split; simpl; auto; eauto 3 with slow. }

  pose proof (member_swapped_css_libs
                name name' (swap_cs_lib (name,name') lib0) lib0
                (swap_cs_cterm (name, name') z1)
                (mkc_apply u (mkc_choice_seq name'))) as m.
  repeat (autodimp m hyp); simpl; eauto 3 with slow.
Qed.
