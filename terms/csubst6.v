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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export substc_more.
Require Export arith_props.
Require Export nat_defs.
Require Export alphaeq5.
Require Export subst_props2.


Definition mkcv_natk2nat {o} vs (t : @CVTerm o vs) :=
  mkcv_fun vs (mkcv_natk vs t) (mkcv_tnat vs).

Lemma alphaeqc_refl {o} :
  forall (t : @CTerm o), alphaeqc t t.
Proof.
  introv.
  destruct_cterms; unfold alphaeqc; simpl; eauto with slow.
Qed.
Hint Resolve alphaeqc_refl : slow.

Lemma mkcv_tnat_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_tnat [v])
    = mkc_tnat.
Proof.
  introv.
  unfold mkcv_tnat.
  allrw @csubst_mk_cv; auto.
Qed.

Lemma isprog_vars_squash {p} :
  forall (a : @NTerm p) vs,
    isprog_vars vs (mk_squash a) <=> isprog_vars vs a.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  allrw <- @wf_term_eq.
  allrw @wf_squash; split; sp.
Qed.

Lemma isprog_vars_squash_implies {p} :
  forall (a : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs (mk_squash a).
Proof.
  introv ispa.
  apply isprog_vars_squash; sp.
Qed.

Definition mkcv_squash {p} vs (t : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t in
    exist (isprog_vars vs) (mk_squash a) (isprog_vars_squash_implies a vs x).

Definition mkcv_product {o} vs (t1 : @CVTerm o vs) (v : NVar) (t2 : CVTerm (v :: vs)) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  exist (isprog_vars vs) (mk_product a v b) (isprog_vars_product vs a v b x y).

Definition mkcv_exists {o} vs (t1 : @CVTerm o vs) (v : NVar) (t2 : CVTerm (v :: vs)) : CVTerm vs :=
  mkcv_product vs t1 v t2.

Definition mkcv_forall {o} vs (t1 : @CVTerm o vs) (v : NVar) (t2 : CVTerm (v :: vs)) : CVTerm vs :=
  mkcv_function vs t1 v t2.

Definition mk_forall {o} (t1 : @NTerm o) (v : NVar) (t2 : NTerm) : NTerm :=
  mk_function t1 v t2.

Definition mkc_forall {o} (t1 : @CTerm o) (v : NVar) (t2 : CVTerm [v]) : CTerm :=
  mkc_function t1 v t2.

Definition mkc_exists {o} (t1 : @CTerm o) (v : NVar) (t2 : CVTerm [v]) : CTerm :=
  mkc_product t1 v t2.

Lemma implies_isprog_vars_apply2 {o} :
  forall vs (f a b : @NTerm o),
    isprog_vars vs f
    -> isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_apply2 f a b).
Proof.
  introv isp1 isp2 isp3.
  apply isprog_vars_apply2; sp.
Qed.

Definition mkcv_apply2 {o} vs (f t1 t2 : @CVTerm o vs) : CVTerm vs :=
  let (a,pa) := f in
  let (b,pb) := t1 in
  let (c,pc) := t2 in
    exist (isprog_vars vs) (mk_apply2 a b c) (implies_isprog_vars_apply2 vs a b c pa pb pc).

Lemma isprog_vars_image {p} :
  forall (f a : @NTerm p) vs,
    isprog_vars vs (mk_image f a) <=> (isprog_vars vs f # isprog_vars vs a).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  rw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw <- @wf_image_iff; split; sp.
Qed.

Lemma isprog_vars_image_implies {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_image a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_image; sp.
Qed.

Definition mkcv_image {p} vs (t1 t2 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  exist (isprog_vars vs) (mk_image a b) (isprog_vars_image_implies a b vs x y).

Lemma mkcv_image_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_image [v] a b)
    = mkc_image (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma substc_mkcv_squash {o} :
  forall v a (t : @CTerm o),
    substc t v (mkcv_squash [v] a) = mkc_squash (substc t v a).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma mkcv_product_substc {o} :
  forall v x (a : @CVTerm o [v]) (b : @CVTerm o [x,v]) (t : CTerm),
    x <> v
    -> substc t v (mkcv_product [v] a x b)
       = mkc_product (substc t v a) x (substc2 x t v b).
Proof.
  introv d.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
  simpl.
  allrw memvar_singleton; boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma mkcv_exists_substc {o} :
  forall v x (a : @CVTerm o [v]) (b : @CVTerm o [x,v]) (t : CTerm),
    x <> v
    -> substc t v (mkcv_exists [v] a x b)
       = mkc_exists (substc t v a) x (substc2 x t v b).
Proof.
  introv d.
  unfold mkcv_exists.
  rw @mkcv_product_substc; auto.
Qed.

Lemma substc_mkcv_axiom {o} :
  forall (t : @CTerm o) v,
    substc t v (mkcv_axiom v) = mkc_axiom.
Proof.
  introv.
  unfold mkcv_exists.
  destruct_cterms.
  apply cterm_eq; simpl.
  unfold subst, lsubst; simpl; auto.
Qed.

Lemma substc2_apply2 {o} :
  forall v x (w : @CTerm o) (a b c : CVTerm [v,x]),
    substc2 v w x (mkcv_apply2 [v,x] a b c)
    = mkcv_apply2 [v] (substc2 v w x a) (substc2 v w x b) (substc2 v w x c).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma substc2_apply {o} :
  forall v x (w : @CTerm o) (a b : CVTerm [v,x]),
    substc2 v w x (mkcv_apply [v,x] a b)
    = mkcv_apply [v] (substc2 v w x a) (substc2 v w x b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma substc2_squash {o} :
  forall v x (w : @CTerm o) (a : CVTerm [v,x]),
    substc2 v w x (mkcv_squash [v,x] a)
    = mkcv_squash [v] (substc2 v w x a).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma mkcv_apply2_substc {o} :
  forall v a b c (t : @CTerm o),
    substc t v (mkcv_apply2 [v] a b c)
    = mkc_apply2 (substc t v a) (substc t v b) (substc t v c).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma lsubstc_vars_mk_tnat_as_mkcv {o} :
  forall (w : @wf_term o mk_tnat) s vs c,
    lsubstc_vars mk_tnat w s vs c = mkcv_tnat vs.
Proof.
  introv.
  apply cvterm_eq; simpl.
  rw @csubst_mk_tnat; auto.
Qed.

Hint Rewrite @mkc_var_substc     : slow.
Hint Rewrite @mkcv_tnat_substc   : slow.
Hint Rewrite @mkcv_apply2_substc : slow.
Hint Rewrite @mkcv_add_substc    : slow.

Hint Rewrite @lsubstc_mkc_tnat             : slow.
Hint Rewrite @lsubstc_vars_mk_tnat_as_mkcv : slow.
Hint Rewrite @lsubstc_vars_var_not_in      : slow.
Hint Rewrite @lsubst_aux_nil               : slow.
Hint Rewrite @substc_mkcv_squash           : slow.
Hint Rewrite @csubst_mk_cv                 : slow.

Hint Rewrite @substc2_apply2      : slow.
Hint Rewrite @substc2_mk_cv       : slow.
Hint Rewrite @substc2_mk_cv_app_l : slow.
Hint Rewrite @substc2_squash      : slow.

Lemma alphaeqc_mkc_fun {o} :
  forall a b c d : @CTerm o,
    alphaeqc a b
    -> alphaeqc c d
    -> alphaeqc (mkc_fun a c) (mkc_fun b d).
Proof.
  introv aeq1 aeq2.
  destruct_cterms.
  allunfold @alphaeqc; allsimpl.
  constructor; simpl; auto.
  introv j.
  repeat (destruct n; tcsp); unfold selectbt; simpl.
  - apply alphaeqbt_nilv2; auto.
  - rw @newvar_prog; auto.
    rw @newvar_prog; auto.
    apply alpha_eq_bterm_congr; auto.
Qed.

Lemma mkcv_natk_eq {o} :
  forall vs (t : @CVTerm o vs),
    mkcv_natk vs t
    = let v := newvar (get_cvterm vs t) in
      mkcv_set vs (mkcv_int vs)
               v
               (mkcv_prod
                  (v :: vs)
                  (mkcv_le (v :: vs) (mkcv_zero (v :: vs)) (mk_cv_app_r vs [v] (mkc_var v)))
                  (mkcv_less_than (v :: vs) (mk_cv_app_r vs [v] (mkc_var v)) (mk_cv_app_l [v] vs t))).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; tcsp.
Qed.

Lemma cl_lsubst_aux_swap_filter0 {o} :
  forall (t : @NTerm o) (s : Substitution) vs,
    cl_sub s
    -> (forall v, LIn v (dom_sub s) -> LIn v vs -> !LIn v (free_vars t))
    -> lsubst_aux t (sub_filter s vs) = lsubst_aux t s.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv cl disj; allsimpl; auto.

  - Case "vterm".
    rw @sub_find_sub_filter_eq; boolvar; tcsp.
    remember (sub_find s v) as sf; symmetry in Heqsf; destruct sf; auto.
    provefalse.
    apply sub_find_some in Heqsf.
    apply in_sub_eta in Heqsf; repnd.
    eapply disj in Heqsf0; eauto.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    disj_flat_map.
    destruct x as [l t]; allsimpl.
    f_equal.
    rw @sub_filter_swap.
    apply (ind t l); eauto 3 with slow.

    introv j k q.
    allrw <- @dom_sub_sub_filter.
    allrw in_remove_nvars; repnd.
    eapply disj in j0; eauto.
    destruct j0; rw lin_flat_map.
    eexists; dands; eauto; simpl.
    rw in_remove_nvars; sp.
Qed.

Lemma cl_lsubst_aux_swap_filter {o} :
  forall (t : @NTerm o) (s : Substitution) vs,
    cl_sub s
    -> disjoint (free_vars t) vs
    -> lsubst_aux t (sub_filter s vs) = lsubst_aux t s.
Proof.
  introv cl disj.
  apply cl_lsubst_aux_swap_filter0; auto.
  introv i j k.
  apply disj in k; sp.
Qed.

Lemma disjoint_newvar_r {o} :
  forall (t : @NTerm o), disjoint (free_vars t) [newvar t].
Proof.
  introv; apply disjoint_singleton_r.
  apply newvar_prop.
Qed.
Hint Resolve disjoint_newvar_r : slow.

Lemma disjoint_newvar_l {o} :
  forall (t : @NTerm o), disjoint [newvar t] (free_vars t).
Proof.
  introv; apply disjoint_singleton_l.
  apply newvar_prop.
Qed.
Hint Resolve disjoint_newvar_l : slow.

Hint Rewrite app_nil_r : slow.

Lemma lsubstc_vars_mk_fun_as_mkcv {o} :
  forall (t1 t2 : @NTerm o) w s vs c,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars_upto t1 s vs
     & {c2 : cover_vars_upto t2 s vs
     & alphaeqcv
         vs
         (lsubstc_vars (mk_fun t1 t2) w s vs c)
         (mkcv_fun
            vs
            (lsubstc_vars t1 w1 s vs c1)
            (lsubstc_vars t2 w2 s vs c2))}}}}.
Proof.
  introv.

  dup w as w'.
  rw @wf_fun_iff in w'; repnd.
  exists w'0 w'.

  dup c as c'.
  rw @cover_vars_upto_fun in c'; repnd.
  exists c'0 c'.

  unfold alphaeqcv; simpl.
  unfold csubst.
  repeat (rewrite cl_lsubst_lsubst_aux; eauto 2 with slow;[]).
  simpl.
  autorewrite with slow.
  fold_terms.
  repeat (rewrite cl_lsubst_aux_swap_filter; eauto 3 with slow).

  { apply alphaeq_function_fun.
    apply disjoint_singleton_l; intro i.
    apply free_vars_lsubst_aux_subset in i.
    rewrite sub_free_vars_if_cl_sub in i; eauto 3 with slow.
    autorewrite with slow in *.
    apply in_remove_nvars in i; repnd.
    apply newvar_prop in i0; tcsp. }
Qed.

Lemma alphaeqcv_trans {o} :
  forall vs (t1 t2 t3 : @CVTerm o vs),
    alphaeqcv vs t1 t2
    -> alphaeqcv vs t2 t3
    -> alphaeqcv vs t1 t3.
Proof.
  introv aeq1 aeq2.
  destruct_cterms.
  allunfold @alphaeqcv; allsimpl.
  eapply alpha_eq_trans; eauto.
Qed.

Lemma alphaeqcv_sym {o} :
  forall vs (t1 t2 : @CVTerm o vs),
    alphaeqcv vs t1 t2
    -> alphaeqcv vs t2 t1.
Proof.
  introv aeq.
  destruct_cterms.
  allunfold @alphaeqcv; allsimpl.
  apply alpha_eq_sym; auto.
Qed.

Lemma alphaeqcv_refl {o} :
  forall vs (t : @CVTerm o vs), alphaeqcv vs t t.
Proof.
  introv.
  destruct_cterms.
  allunfold @alphaeqcv; allsimpl.
  apply alpha_eq_refl.
Qed.

Lemma alphaeq_mk_fun {o} :
  forall a b c d : @NTerm o,
    alphaeq a b
    -> alphaeq c d
    -> alphaeq (mk_fun a c) (mk_fun b d).
Proof.
  introv aeq1 aeq2.
  constructor; simpl; auto.
  introv j.
  apply alphaeqbt_eq.
  repeat (destruct n; tcsp; try lia); unfold selectbt; simpl.
  - apply alphaeqbt_nilv2.
    apply alphaeq_eq; auto.
  - pose proof (ex_fresh_var (all_vars c ++ all_vars d)) as h; exrepnd.
    apply (al_bterm_aux [v]); simpl; auto.
    + apply disjoint_singleton_l; auto.
    + repeat (rewrite lsubst_aux_trivial_cl_term); simpl; auto.
      * apply alphaeq_eq; auto.
      * apply disjoint_singleton_r.
        apply newvar_prop.
      * apply disjoint_singleton_r.
        apply newvar_prop.
Qed.

Lemma alpha_eq_mk_fun {o} :
  forall a b c d : @NTerm o,
    alpha_eq a b
    -> alpha_eq c d
    -> alpha_eq (mk_fun a c) (mk_fun b d).
Proof.
  introv aeq1 aeq2.
  allrw <- @alphaeq_eq.
  apply alphaeq_mk_fun; auto.
Qed.

Lemma beq_var_refl2 : forall X : NVar, beq_var X X = true.
Proof.
  introv; boolvar; auto.
Qed.
Hint Rewrite beq_var_refl2 : slow.

Lemma implies_alphaeqc_substc2 {o} :
  forall v (t : @CTerm o) x u1 u2,
    alphaeqcv [v,x] u1 u2
    -> alphaeqcv [v] (substc2 v t x u1) (substc2 v t x u2).
Proof.
  introv aeq.
  destruct_cterms.
  allunfold @alphaeqcv; allsimpl.
  apply lsubst_alpha_congr2; auto.
Qed.

Hint Rewrite memvar_singleton : slow.

Lemma substc2_fun {o} :
  forall v x (w : @CTerm o) (t u : CVTerm [v,x]),
    alphaeqcv
      [v]
      (substc2 v w x (mkcv_fun [v,x] t u))
      (mkcv_fun [v] (substc2 v w x t) (substc2 v w x u)).
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

Lemma isprog_vars_substc3 {o} :
  forall x y (a : @NTerm o) v b,
    isprog b
    -> isprog_vars [x,y,v] a
    -> isprog_vars [x,y] (subst a v b).
Proof.
  introv ispb ispa.
  apply subst_preserves_isprog_vars; auto.
Qed.

Definition substc3 {o} x y (u : @CTerm o) (v : NVar) (t : CVTerm [x,y,v]) : CVTerm [x,y] :=
  let (a,pa) := t in
  let (b,pb) := u in
  exist (isprog_vars [x,y]) (subst a v b) (isprog_vars_substc3 x y a v b pb pa).

Lemma substc2_product {o} :
  forall (v x : NVar) (w : @CTerm o) (t : CVTerm [v,x]) y (u : CVTerm [y,v,x]),
    y <> x
    -> alphaeqcv
         [v]
         (substc2 v w x (mkcv_product [v, x] t y u))
         (mkcv_product
            [v]
            (substc2 v w x t)
            y
            (substc3 y v w x u)).
Proof.
  introv d.
  destruct_cterms.
  unfold alphaeqcv; simpl.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).

  simpl.
  autorewrite with slow.
  boolvar; tcsp.
Qed.

Hint Resolve isprog_tnat : slow.

Lemma substc2_mkcv_tnat {o} :
  forall v (t : @CTerm o) x,
    substc2 v t x (mkcv_tnat [v,x]) = mkcv_tnat [v].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  apply subst_trivial; eauto 2 with slow.
Qed.
Hint Rewrite @substc2_mkcv_tnat : slow.

Lemma cover_vars_upto_arithop {p} :
  forall vs c a b sub,
    @cover_vars_upto p (mk_arithop c a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  intros; unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma lsubstc_vars_mk_add_as_mkcv {o} :
  forall (t1 t2 : @NTerm o) w s vs c,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars_upto t1 s vs
     & {c2 : cover_vars_upto t2 s vs
     & lsubstc_vars (mk_add t1 t2) w s vs c
       = mkcv_add
           vs
           (lsubstc_vars t1 w1 s vs c1)
           (lsubstc_vars t2 w2 s vs c2) }}}}.
Proof.
  introv.

  dup w as w'.
  apply wf_arithop_iff in w'; repnd.
  dup c as c'.
  rw @cover_vars_upto_arithop in c'; repnd.

  exists w'0 w' c'0 c'.
  apply cvterm_eq; simpl.
  unfold csubst.
  repeat unflsubst.
  simpl; fold_terms.
  allrw @sub_filter_nil_r; auto.
Qed.

Lemma substc3_apply2 {o} :
  forall v z x (w : @CTerm o) (a b c : CVTerm [v,z,x]),
    substc3 v z w x (mkcv_apply2 [v,z,x] a b c)
    = mkcv_apply2 [v,z] (substc3 v z w x a) (substc3 v z w x b) (substc3 v z w x c).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc3_apply2 : slow.

Lemma substc3_mk_cv {o} :
  forall y z (u : @CTerm o) x (t : CTerm),
    substc3 y z u x (mk_cv [y,z,x] t) = mk_cv [y,z] t.
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
  apply subst_trivial; auto.
Qed.
Hint Rewrite @substc3_mk_cv : slow.

Lemma substc3_add {o} :
  forall v z x (w : @CTerm o) (a b : CVTerm [v,z,x]),
    substc3 v z w x (mkcv_add [v,z,x] a b)
    = mkcv_add [v,z] (substc3 v z w x a) (substc3 v z w x b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc3_add : slow.

Lemma substc2_add {o} :
  forall v x (w : @CTerm o) (a b : CVTerm [v,x]),
    substc2 v w x (mkcv_add [v,x] a b)
    = mkcv_add [v] (substc2 v w x a) (substc2 v w x b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc2_add : slow.

Lemma lsubstc_vars_mk_var_as_mkcv3 {o} :
  forall (v v' v'' : NVar)
         (w : @wf_term o (mk_var v))
         (s : CSubstitution)
         (c : cover_vars_upto (mk_var v) s [v'', v', v]),
    !LIn v (dom_csub s)
    -> lsubstc_vars (mk_var v) w s [v'', v', v] c = mk_cv_app_l [v'', v'] [v] (mkc_var v).
Proof.
  introv ni.
  apply cvterm_eq; simpl.
  apply csubst_var_not_in; auto.
Qed.

Lemma substc3_mk_cv_app_l {o} :
  forall (u : @CTerm o) v w x (t : CVTerm [x]),
    substc3 v w u x (mk_cv_app_l [v,w] [x] t)
    = mk_cv [v,w] (substc u x t).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc3_mk_cv_app_l : slow.

Lemma lsubstc_vars_zero {o} :
  forall (w : @wf_term o mk_zero) s vs c,
    lsubstc_vars mk_zero w s vs c
    = mkcv_zero vs.
Proof.
  introv; apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @lsubstc_vars_zero : slow.

Lemma substc3_mkcv_zero {o} :
  forall (u : @CTerm o) v w x,
    substc3 v w u x (mkcv_zero [v,w,x])
    = mkcv_zero [v,w].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc3_mkcv_zero : slow.

Lemma substc2_mkcv_zero {o} :
  forall (u : @CTerm o) v x,
    substc2 v u x (mkcv_zero [v,x])
    = mkcv_zero [v].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc2_mkcv_zero : slow.

Lemma isprogram_mk_one {o} :
  @isprogram o mk_one.
Proof.
  repeat constructor; simpl; sp.
Qed.
Hint Immediate isprogram_mk_one.

Lemma isprog_mk_one {o} :
  @isprog o mk_one.
Proof.
  rw @isprog_eq.
  apply isprogram_mk_one.
Qed.
Hint Immediate isprog_mk_one.

Definition mkc_one {o} : @CTerm o := exist isprog mk_one isprog_mk_one.
Definition mkcv_one {o} (vs : list NVar) : @CVTerm o vs := mk_cv vs mkc_one.

Lemma lsubstc_vars_one {o} :
  forall (w : @wf_term o mk_one) s vs c,
    lsubstc_vars mk_one w s vs c
    = mkcv_one vs.
Proof.
  introv; apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @lsubstc_vars_one : slow.

Lemma substc3_mkcv_one {o} :
  forall (u : @CTerm o) v w x,
    substc3 v w u x (mkcv_one [v,w,x])
    = mkcv_one [v,w].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc3_mkcv_one : slow.

Lemma substc2_mkcv_one {o} :
  forall (u : @CTerm o) v x,
    substc2 v u x (mkcv_one [v,x])
    = mkcv_one [v].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc2_mkcv_one : slow.

Lemma mkcv_one_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_one [v]) = mkc_one.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.
Hint Rewrite @mkcv_one_substc : slow.

Lemma iscvalue_mkc_pair {o} :
  forall (a b : @CTerm o),
    iscvalue (mkc_pair a b).
Proof.
  introv; destruct_cterms; unfold iscvalue; simpl.
  allrw @isprog_eq.
  inversion i as [cl1 wf1].
  inversion i0 as [cl2 wf2].
  repeat constructor; simpl.
  - unfold closed; simpl; rw cl1; rw cl2; simpl; auto.
  - introv k; repndors; subst; tcsp; constructor; auto.
Qed.
Hint Resolve iscvalue_mkc_pair : slow.

Lemma subst_mk_set {o} :
  forall (a : @NTerm o) v b x u,
    closed u
    -> subst (mk_set a v b) x u
       = mk_set (subst a x u) v (if deq_nvar v x then b else subst b x u).
Proof.
  introv cl.
  repeat unfsubst; simpl; rw memvar_singleton; fold_terms;
  boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma subst_mk_product_disj {o} :
  forall (a : @NTerm o) v b x u,
    disjoint (free_vars u) (bound_vars (mk_product a v b))
    -> subst (mk_product a v b) x u
       = mk_product (subst a x u) v (if deq_nvar v x then b else subst b x u).
Proof.
  introv d.
  unfold subst.
  rw @lsubst_lsubst_aux; allsimpl; allrw app_nil_r; eauto 2 with slow.
  rw @lsubst_lsubst_aux; allsimpl; allrw app_nil_r; eauto 2 with slow;
  [|allrw disjoint_app_r; repnd; eauto 2 with slow].
  rw @lsubst_lsubst_aux; allsimpl; allrw app_nil_r; eauto 2 with slow;
  [|allrw disjoint_app_r; allrw disjoint_cons_r; repnd; eauto 2 with slow].
  allrw memvar_singleton; boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma subst_mk_product_cl {o} :
  forall (a : @NTerm o) v b x u,
    closed u
    -> subst (mk_product a v b) x u
       = mk_product (subst a x u) v (if deq_nvar v x then b else subst b x u).
Proof.
  introv d.
  unfold subst.
  repeat unflsubst.
  simpl; allrw memvar_singleton; boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma subst_mk_int {o} :
  forall x (u : @NTerm o),
    subst mk_int x u = mk_int.
Proof.
  introv; tcsp.
Qed.

Lemma alpha_eq_mk_set {o} :
  forall v (a1 a2 : @NTerm o) v1 v2 b1 b2,
    !LIn v (all_vars b1)
    -> !LIn v (all_vars b2)
    -> alpha_eq a1 a2
    -> alpha_eq (subst b1 v1 (mk_var v)) (subst b2 v2 (mk_var v))
    -> alpha_eq (mk_set a1 v1 b1) (mk_set a2 v2 b2).
Proof.
  introv ni1 ni2 aeqa aeqb.
  constructor; simpl; auto.
  introv i.
  repeat (destruct n; tcsp); unfold selectbt; simpl.
  - apply alphaeqbt_nilv2; auto.
  - apply (al_bterm _ _ [v]); simpl; auto.
    allrw disjoint_singleton_l; allrw in_app_iff; sp.
Qed.

Lemma ite_mk_product {o} :
  forall A B (b : {A} + {B}) (a1 a2 : @NTerm o) v1 v2 b1 b2,
    (if b then mk_product a1 v1 b1 else mk_product a2 v2 b2)
    = mk_product (if b then a1 else a2) (if b then v1 else v2) (if b then b1 else b2).
Proof.
  introv; destruct b; tcsp.
Qed.

Lemma ite_same :
  forall A B T (b : {A} + {B}) (x : T),
    (if b then x else x) = x.
Proof.
  introv; destruct b; tcsp.
Qed.

Lemma mkc_assert_eq {o} :
  forall (t : @CTerm o),
    mkc_assert t = mkc_ite t mkc_unit mkc_void.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
Qed.

Lemma wf_btrue {o} : @wf_term o mk_btrue.
Proof.
  unfold mk_btrue.
  apply wf_inl; eauto with slow.
Qed.
Hint Resolve wf_btrue : slow.

Lemma wf_bfalse {o} : @wf_term o mk_bfalse.
Proof.
  unfold mk_bfalse.
  apply wf_inr; eauto with slow.
Qed.
Hint Resolve wf_bfalse : slow.

Lemma isprog_btrue {o} : @isprog o mk_btrue.
Proof.
  unfold mk_btrue.
  apply isprog_inl; eauto with slow.
Qed.
Hint Resolve isprog_btrue : slow.

Lemma isprog_bfalse {o} : @isprog o mk_bfalse.
Proof.
  unfold mk_bfalse.
  apply isprog_inr; eauto with slow.
Qed.
Hint Resolve isprog_bfalse : slow.

Lemma isvalue_btrue {o} : @isvalue o mk_btrue.
Proof.
  unfold mk_btrue.
  apply isvalue_inl; eauto with slow.
Qed.
Hint Resolve isvalue_btrue : slow.

Lemma isvalue_bfalse {o} : @isvalue o mk_bfalse.
Proof.
  unfold mk_bfalse.
  apply isvalue_inr; eauto with slow.
Qed.
Hint Resolve isvalue_bfalse : slow.

Lemma closed_if_isprog {o} :
  forall (t : @NTerm o),
    isprog t -> closed t.
Proof.
  introv isp.
  apply isprog_eq in isp.
  destruct isp; auto.
Qed.

Lemma substc_mkcv_le {o} :
  forall v t (a b : @CVTerm o [v]),
    substc t v (mkcv_le [v] a b)
    = mkc_le (substc t v a) (substc t v b).
Proof.
  introv.
  apply cterm_eq; simpl.
  destruct_cterms; simpl.
  applydup @closed_if_isprog in i; unfold closed in i2.

  unfold subst, lsubst; simpl; allrw app_nil_r; rw i2; simpl; boolvar;
  allsimpl; try (complete (provefalse; tcsp)); tcsp; boolvar; allsimpl;
  tcsp; allrw not_over_or; repnd; tcsp; boolvar; allsimpl; tcsp.
Qed.

Lemma substc_mkcv_zero {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_zero [v])
    = mkc_zero.
Proof.
  introv.
  apply cterm_eq; simpl.
  destruct_cterms; simpl.
  unfold subst, lsubst; simpl; auto.
Qed.

Lemma substc_mkcv_int {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_int [v])
    = mkc_int.
Proof.
  introv.
  apply cterm_eq; simpl.
  destruct_cterms; simpl.
  unfold subst, lsubst; simpl; auto.
Qed.

Lemma lsubstc_int2int {o} :
  forall (w : @wf_term o int2int) s c,
    lsubstc int2int w s c = mkc_fun mkc_int mkc_int.
Proof.
  introv.
  apply cterm_eq; simpl.
  unfold int2int, csubst, lsubst; simpl.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @sub_free_vars_csub2sub; boolvar; tcsp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)
