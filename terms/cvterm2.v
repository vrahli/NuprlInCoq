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


Require Export cvterm.
Require Export csubst.
(*Require Export computation3.*)
Require Export substitution3.
Require Export subst_tacs2.
Require Export List.
Require Export list. (* WTF!!*)


Definition mkcv_tnat {o} (vs : list NVar) : @CVTerm o vs := mk_cv vs mkc_tnat.

Definition mk_isl {o} (t : @NTerm o) := mk_ite t mk_btrue mk_bfalse.

Lemma wf_term_decide_iff {p} :
  forall (a : @NTerm p) v1 b1 v2 b2,
    (wf_term a
     # wf_term b1
     # wf_term b2)
    <=> wf_term (mk_decide a v1 b1 v2 b2).
Proof.
  introv; split; intro wf; repnd.
  - allrw @wf_term_eq.
    constructor; simpl; unfold num_bvars; simpl; auto.
    sp; subst; constructor; auto.
  - allrw @wf_term_eq.
    inversion wf as [| o l bwf e ]; subst.
    generalize (bwf (nobnd a)) (bwf (bterm [v1] b1)) (bwf (bterm [v2] b2)); clear bwf; intros bwf1 bwf2 bwf3.
    autodimp bwf1 hyp; autodimp bwf2 hyp; autodimp bwf3 hyp; try (complete (simpl; sp)).
    inversion bwf1; subst.
    inversion bwf2; subst.
    inversion bwf3; subst; sp.
Qed.

Lemma isprog_vars_decide_iff {p} :
  forall vs (a : @NTerm p) v1 a1 v2 a2,
    isprog_vars vs (mk_decide a v1 a1 v2 a2)
    <=> (isprog_vars vs a
         # isprog_vars (v1 :: vs) a1
         # isprog_vars (v2 :: vs) a2).
Proof.
  introv; split; intro k; try (repnd; apply isprog_vars_decide); auto.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l.
  allrw subvars_eq.
  allrw app_nil_r.
  allrw subset_app; repnd.
  allrw <- @wf_term_eq.
  apply wf_term_decide_iff in k; repnd.
  allrw <- subvars_eq.
  allrw subvars_remove_nvars.
  allrw subvars_eq.
  dands; auto.
  - introv i; simpl.
    apply k2 in i; allrw in_app_iff; allsimpl; sp.
  - introv i; simpl.
    apply k0 in i; allrw in_app_iff; allsimpl; sp.
Qed.

Lemma isprog_vars_ite {p} :
  forall vs (a b c : @NTerm p),
    (isprog_vars vs a # isprog_vars vs b # isprog_vars vs c)
    <=> isprog_vars vs (mk_ite a b c).
Proof.
  introv.
  unfold mk_ite.
  rw @isprog_vars_decide_iff.
  allrw @isprog_vars_cons_newvar; sp.
Qed.

Lemma isprog_vars_ite_implies {p} :
  forall vs (a b c : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs c
    -> isprog_vars vs (mk_ite a b c).
Proof.
  intros; apply isprog_vars_ite; sp.
Qed.

Definition mkcv_ite {p} (vs : list NVar) (a b c : @CVTerm p vs) :=
  let (t1,x1) := a in
  let (t2,x2) := b in
  let (t3,x3) := c in
  exist (isprog_vars vs)
        (mk_ite t1 t2 t3)
        (isprog_vars_ite_implies vs t1 t2 t3 x1 x2 x3).

Lemma isprog_vars_isl {o} :
  forall vs (t : @NTerm o), isprog_vars vs (mk_isl t) <=> isprog_vars vs t.
Proof.
  introv.
  unfold mk_isl.
  rw <- @isprog_vars_ite.
  split; intro k; repnd; dands; eauto 3 with slow.
Qed.

Lemma isprog_isl {o} :
  forall (t : @NTerm o),
    isprog (mk_isl t) <=> isprog t.
Proof.
  introv; unfold mk_isl.
  rw @isprog_decide_iff.
  split; intro k; repnd; dands; tcsp; eauto 3 with slow.
Qed.

Lemma implies_isprog_isl {o} :
  forall (t : @NTerm o), isprog t -> isprog (mk_isl t).
Proof.
  introv isp; apply isprog_isl; auto.
Qed.

Definition mkc_isl {o} (t : @CTerm o) : CTerm :=
  let (a,x) := t in exist isprog (mk_isl a) (implies_isprog_isl a x).

Definition mk_assert {o} (t : @NTerm o) := mk_ite t mk_unit mk_void.

Lemma isprog_vars_unit {o} :
  forall vs, @isprog_vars o vs mk_unit.
Proof.
  introv; rw @isprog_vars_eq; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_unit : slow.

Lemma isprog_assert {o} :
  forall (t : @NTerm o),
    isprog (mk_assert t) <=> isprog t.
Proof.
  introv; unfold mk_assert.
  rw @isprog_decide_iff.
  split; intro k; repnd; dands; tcsp; eauto 3 with slow.
Qed.

Lemma implies_isprog_assert {o} :
  forall (t : @NTerm o), isprog t -> isprog (mk_assert t).
Proof.
  introv isp; apply isprog_assert; auto.
Qed.

Definition mkc_assert {o} (t : @CTerm o) : CTerm :=
  let (a,x) := t in exist isprog (mk_assert a) (implies_isprog_assert a x).

Definition mkcv_prod {p} vs (A B : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := A in
  let (b,y) := B in
  exist (isprog_vars vs) (mk_prod a b) (isprog_vars_prod_implies vs a b x y).

Definition mkcv_less_than {o} (vs : list NVar) (t1 t2 : @CVTerm o vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_less_than a b) (isprog_vars_less_than_implies a b vs x y).

Lemma mkc_natk_eq {o} :
  forall (t : @CTerm o),
    mkc_natk t
    = mkc_set
        mkc_int
        nvarx
        (mkcv_prod
           [nvarx]
           (mkcv_le [nvarx] (mkcv_zero [nvarx]) (mkc_var nvarx))
           (mkcv_less_than [nvarx] (mkc_var nvarx) (mk_cv [nvarx] t))).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
  unfold mk_natk.
  rw @newvar_prog; auto.
Qed.

Lemma closed_if_isprog {o} :
  forall (t : @NTerm o),
    isprog t -> closed t.
Proof.
  introv isp.
  apply closed_if_program.
  apply isprogram_eq; auto.
Qed.
Hint Resolve closed_if_isprog : slow.

Lemma mkcv_prod_substc {o} :
  forall v (a b : @CVTerm o [v]) t,
    alphaeqc
      (substc t v (mkcv_prod [v] a b))
      (mkc_prod (substc t v a) (substc t v b)).
Proof.
  introv.
  destruct_cterms.
  unfold alphaeqc; simpl.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
  simpl; fold_terms; rw memvar_singleton.
  constructor; simpl; auto.
  introv k.
  repeat (destruct n; tcsp).
  unfold selectbt; simpl.

  pose proof (newvar_prog (lsubst_aux x0 [(v, x)])) as h.
  autodimp h hyp.
  { apply isprog_vars_nil_implies_isprog.
    rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
    apply csubst.isprog_vars_lsubst; allsimpl; auto .
    introv j; repndors; subst; tcsp.
    apply isprogram_eq; auto. }
  rw h.

  boolvar.

  { rw @lsubst_aux_trivial_cl_term in h; allsimpl;
    [|apply disjoint_singleton_r; apply newvar_prop].
    rw (lsubst_aux_trivial_cl_term x0 [(newvar x0,x)]); allsimpl;
    [|apply disjoint_singleton_r; apply newvar_prop].
    rw h; rw @lsubst_aux_nil; auto. }

  { pose proof (ex_fresh_var (nvarx
                                :: (newvar x0)
                                :: (all_vars (lsubst_aux x0 [(v, x)]))
                                ++ (all_vars (lsubst_aux x0 [(v, x)])))) as fv;
    exrepnd; allsimpl; allrw in_app_iff.
    allrw not_over_or; repnd; GC.
    apply (al_bterm _ _ [v0]); allsimpl; auto.
    { rw disjoint_singleton_l; allrw in_app_iff; allrw not_over_or; sp. }
    unfold var_ren; simpl.

    assert (free_vars (lsubst_aux x0 [(v, x)]) = []) as f.
    { apply null_iff_nil.
      apply closed_null_free_vars.
      apply closed_if_isprog.
      apply isprog_vars_nil_implies_isprog.
      rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
      apply csubst.isprog_vars_lsubst; allsimpl; auto .
      introv j; repndors; subst; tcsp.
      apply isprogram_eq; auto. }

    repeat (rw @lsubst_trivial4; simpl; auto);
      allrw disjoint_singleton_l; try (rw f); simpl; tcsp;
      introv j; repndors; tcsp; ginv; simpl;
      apply disjoint_singleton_l; auto. }
Qed.

Lemma mkcv_fun_substc {o} :
  forall v (a b : @CVTerm o [v]) t,
    alphaeqc
      (substc t v (mkcv_fun [v] a b))
      (mkc_fun (substc t v a) (substc t v b)).
Proof.
  introv.
  destruct_cterms.
  unfold alphaeqc; simpl.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
  simpl; fold_terms; rw memvar_singleton.
  constructor; simpl; auto.
  introv k.
  repeat (destruct n; tcsp).
  unfold selectbt; simpl.

  pose proof (newvar_prog (lsubst_aux x0 [(v, x)])) as h.
  autodimp h hyp.
  { apply isprog_vars_nil_implies_isprog.
    rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
    apply csubst.isprog_vars_lsubst; allsimpl; auto .
    introv j; repndors; subst; tcsp.
    apply isprogram_eq; auto. }
  rw h.

  boolvar.

  { rw @lsubst_aux_trivial_cl_term in h; allsimpl;
    [|apply disjoint_singleton_r; apply newvar_prop].
    rw (lsubst_aux_trivial_cl_term x0 [(newvar x0,x)]); allsimpl;
    [|apply disjoint_singleton_r; apply newvar_prop].
    rw h; rw @lsubst_aux_nil; auto. }

  { pose proof (ex_fresh_var (nvarx
                                :: (newvar x0)
                                :: (all_vars (lsubst_aux x0 [(v, x)]))
                                ++ (all_vars (lsubst_aux x0 [(v, x)])))) as fv;
    exrepnd; allsimpl; allrw in_app_iff.
    allrw not_over_or; repnd; GC.
    apply (al_bterm _ _ [v0]); allsimpl; auto.
    { rw disjoint_singleton_l; allrw in_app_iff; allrw not_over_or; sp. }
    unfold var_ren; simpl.

    assert (free_vars (lsubst_aux x0 [(v, x)]) = []) as f.
    { apply null_iff_nil.
      apply closed_null_free_vars.
      apply closed_if_isprog.
      apply isprog_vars_nil_implies_isprog.
      rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
      apply csubst.isprog_vars_lsubst; allsimpl; auto .
      introv j; repndors; subst; tcsp.
      apply isprogram_eq; auto. }

    repeat (rw @lsubst_trivial4; simpl; auto);
      allrw disjoint_singleton_l; try (rw f); simpl; tcsp;
      introv j; repndors; tcsp; ginv; simpl;
      apply disjoint_singleton_l; auto. }
Qed.

Definition mkcv_not {p} vs (t : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t in
    exist (isprog_vars vs) (mk_not a) (implies_isprog_vars_not vs a x).

Lemma mkcv_le_eq {o} :
  forall vs (a b : @CVTerm o vs),
    mkcv_le vs a b = mkcv_not vs (mkcv_less_than vs b a).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.

Lemma mkc_not_eq {o} :
  forall (a : @CTerm o),
    mkc_not a = mkc_fun a mkc_void.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
Qed.

Definition mkcv_void {o} (vs : list NVar) : @CVTerm o vs := mk_cv vs mkc_void.

Lemma mkcv_not_eq {o} :
  forall vs (a : @CVTerm o vs),
    mkcv_not vs a = mkcv_fun vs a (mkcv_void vs).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.

Lemma mkcv_not_substc {o} :
  forall v a (t : @CTerm o),
    substc t v (mkcv_not [v] a)
    = mkc_not (substc t v a).
Proof.
  introv.
  rw @mkc_not_eq.
  rw @mkcv_not_eq.

  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst; simpl; fold_terms.
  allrw @sub_filter_nil_r.
  repeat (rw memvar_singleton; boolvar; allsimpl; tcsp).
  boolvar; tcsp.
Qed.

Definition mkcv_false {o} (vs : list NVar) : @CVTerm o vs := mk_cv vs mkc_false.
Definition mkcv_true {o} (vs : list NVar) : @CVTerm o vs := mk_cv vs mkc_true.

Lemma mkcv_less_than_eq {o} :
  forall vs (a b : @CVTerm o vs),
    mkcv_less_than vs a b = mkcv_less vs a b (mkcv_true vs) (mkcv_false vs).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.

Lemma mkc_less_than_eq {o} :
  forall a b : @CTerm o, mkc_less_than a b = mkc_less a b mkc_true mkc_false.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma mkcv_less_substc {o} :
  forall v a b c d (t : @CTerm o),
    substc t v (mkcv_less [v] a b c d)
    = mkc_less (substc t v a) (substc t v b) (substc t v c) (substc t v d).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma mkcv_true_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_true [v])
    = mkc_true.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; tcsp.
Qed.

Lemma mkcv_false_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_false [v])
    = mkc_false.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  unfsubst; simpl.
  allrw memvar_singleton; boolvar; simpl; tcsp.
  boolvar; simpl; tcsp.
Qed.

Lemma mkcv_less_than_substc {o} :
  forall v a b (c : @CTerm o),
    substc c v (mkcv_less_than [v] a b)
    = mkc_less_than (substc c v a) (substc c v b).
Proof.
  introv.
  rw @mkcv_less_than_eq.
  rw @mkc_less_than_eq.
  rw @mkcv_less_substc.
  rw @mkcv_true_substc.
  rw @mkcv_false_substc.
  auto.
Qed.

Lemma mkcv_le_substc2 {o} :
  forall v a b (c : @CTerm o),
    substc c v (mkcv_le [v] a b)
    = mkc_le (substc c v a) (substc c v b).
Proof.
  introv.
  rw @mkcv_le_eq.
  rw @mkc_le_eq.
  rw @mkcv_not_substc.
  rw @mkcv_less_than_substc.
  auto.
Qed.

Lemma mkc_zero_eq {o} :
  @mkc_zero o = mkc_nat 0.
Proof.
  apply cterm_eq; simpl; auto.
Qed.

Lemma mkc_nat_eq {o} :
  forall n, @mkc_nat o n = mkc_integer (Z.of_nat n).
Proof.
  introv.
  apply cterm_eq; simpl; auto.
Qed.

Hint Resolve isvalue_mk_nat.

Lemma isvalue_zero {o} : @isvalue o mk_zero.
Proof.
  unfold mk_zero; eauto with slow.
Qed.
Hint Resolve isvalue_zero : slow.

Lemma iscvalue_zero {o} : @iscvalue o mkc_zero.
Proof.
  unfold iscvalue; simpl; eauto 3 with slow.
Qed.
Hint Resolve iscvalue_zero : slow.

Lemma wf_fix_iff {p} :
  forall a : @NTerm p, wf_term (mk_fix a) <=> wf_term a.
Proof.
  introv; split; intro i.
  - allrw @wf_term_eq.
    inversion i as [| o lnt k e]; subst; allsimpl.
    generalize (k (nobnd a)); intros k1.
    repeat (dest_imp k1 hyp).
    inversion k1; subst; sp.
  - apply wf_fix; auto.
Qed.

Lemma isprog_vars_fix {p} :
  forall (a : @NTerm p) vs,
    isprog_vars vs (mk_fix a) <=> isprog_vars vs a.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  allrw <- @wf_term_eq.
  allrw @wf_fix_iff; split; sp.
Qed.

Lemma isprog_vars_fix_implies {p} :
  forall (a : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs (mk_fix a).
Proof.
  introv ispa.
  apply isprog_vars_fix; sp.
Qed.

Definition mkcv_fix {p} vs (t : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t in
    exist (isprog_vars vs) (mk_fix a) (isprog_vars_fix_implies a vs x).

Definition mkc_vbot {p} v : @CTerm p := mkc_fix (mkc_lam v (mkc_var v)).

Lemma isprog_get_cterm {o} :
  forall (t : @CTerm o), isprog (get_cterm t).
Proof.
  introv; destruct_cterms; auto.
Qed.
Hint Resolve isprog_get_cterm : slow.
