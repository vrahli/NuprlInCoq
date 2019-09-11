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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export substitution.
Require Export terms_props.


Definition mkcv_equality {p} vs (t1 t2 T : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := T in
    exist (isprog_vars vs) (mk_equality a b c) (isprog_vars_equality vs a b c x y z).

Definition mkcv_member {o} vs (t T : @CVTerm o vs) : CVTerm vs :=
  mkcv_equality vs t t T.

Definition mkcv_requality {p} vs (t1 t2 T : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := T in
    exist (isprog_vars vs) (mk_requality a b c) (isprog_vars_requality vs a b c x y z).

Definition mkcv_rmember {o} vs (t T : @CVTerm o vs) : CVTerm vs :=
  mkcv_requality vs t t T.

Definition mkcv_lam {o} vs (v : NVar) (t : @CVTerm o (v :: vs)) : CVTerm vs :=
  let (a,x) := t in
    exist (isprog_vars vs) (mk_lam v a) (isprog_vars_lam vs v a x).

Lemma isprog_vars_uand_if {o} :
  forall vs (t1 t2 : @NTerm o),
    isprog_vars vs t1
    -> isprog_vars vs t2
    -> isprog_vars vs (mk_uand t1 t2).
Proof.
  introv isp1 isp2.
  apply isprog_vars_uand; auto.
Qed.

Definition mkcv_uand {p} vs (t1 t2 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_uand a b) (isprog_vars_uand_if vs a b x y).

Definition mk_natk_aux {p} vi n : @NTerm p :=
  mk_set
    mk_int
    vi
    (mk_prod (mk_le mk_zero (mk_var vi))
             (mk_less_than (mk_var vi) n)).

Definition mk_natk {p} n : @NTerm p :=
  let v := newvar n in mk_natk_aux v n.

Lemma isprog_vars_int {p} : forall vs, @isprog_vars p vs mk_int.
Proof.
  introv.
  apply isprog_vars_eq; simpl; dands; sp.
  repeat constructor; simpl; sp.
Qed.

Lemma isprog_vars_add {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs (mk_add a b) <=> (isprog_vars vs a # isprog_vars vs b).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  rw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw <- @wf_apply_iff; split; sp.
Qed.

Lemma isprog_vars_add_implies {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_add a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_add; sp.
Qed.

Lemma isprog_vars_apply_implies {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_apply a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_apply; sp.
Qed.

Lemma isprog_vars_tuni_implies {o} :
  forall (f : @NTerm o) vs, isprog_vars vs f -> isprog_vars vs (mk_tuni f).
Proof.
  introv k.
  apply isprog_vars_tuni; sp.
Qed.

Definition mkcv_tuni {o} (vs : list NVar) (R : @CVTerm o vs) : CVTerm vs :=
  let (a,x) := R in
    exist (isprog_vars vs) (mk_tuni a) (isprog_vars_tuni_implies a vs x).

Definition mkcv_le {o} (vs : list NVar) (t1 t2 : @CVTerm o vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_le a b) (isprog_vars_le_implies a b vs x y).

Lemma isprog_le {o} :
  forall a b : @NTerm o,
    isprog (mk_le a b) <=> (isprog a # isprog b).
Proof.
  introv.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_le.
Qed.

Lemma isprog_le_implies {o} :
  forall a b : @NTerm o,
    isprog a
    -> isprog b
    -> isprog (mk_le a b).
Proof.
  introv x y.
  apply isprog_le; sp.
Qed.

Definition mkc_le {o} (t1 t2 : @CTerm o) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_le a b) (isprog_le_implies a b x y).

Definition mkc_less_than {o} (t1 t2 : @CTerm o) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_less_than a b) (isprog_less_than_implies a b x y).

Lemma isprog_less {o} :
  forall a b c d : @NTerm o,
    isprog (mk_less a b c d)
    <=> (isprog a
         # isprog b
         # isprog c
         # isprog d).
Proof.
  introv.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_less.
Qed.

Lemma isprog_less_implies {o} :
  forall a b c d : @NTerm o,
    isprog a
    -> isprog b
    -> isprog c
    -> isprog d
    -> isprog (mk_less a b c d).
Proof.
  introv u v w z.
  apply isprog_less; sp.
Qed.

Definition mkc_less {o} (t1 t2 t3 t4 : @CTerm o) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
  let (d,w) := t4 in
    exist isprog (mk_less a b c d) (isprog_less_implies a b c d x y z w).

Lemma mkc_less_than_eq {o} :
  forall a b : @CTerm o,
    mkc_less_than a b = mkc_less a b mkc_true mkc_false.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma mkc_le_eq {o} :
  forall a b : @CTerm o, mkc_le a b = mkc_not (mkc_less_than b a).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Definition mkcv_zero {o} (vs : list NVar) : @CVTerm o vs := mk_cv vs mkc_zero.

Lemma mkc_tnat_eq {o} :
  @mkc_tnat o = mkc_set mkc_int nvary (mkcv_le [nvary] (mkcv_zero [nvary]) (mkc_var nvary)).
Proof.
  apply cterm_eq; simpl; sp.
Qed.

Lemma mkcv_le_substc {o} :
  forall a b (c : @CTerm o),
    substc c nvary (mkcv_le [nvary] a b)
    = mkc_le (substc c nvary a) (substc c nvary b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  unfold subst.
  change_to_lsubst_aux4; simpl; sp; allrw app_nil_r;
  allrw @isprog_eq; destruct i as [c w]; rw c; sp.
Qed.

Lemma mkcv_tuni_substc {o} :
  forall v a (c : @CTerm o),
    substc c v (mkcv_tuni [v] a)
    = mkc_tuni (substc c v a).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  unfold subst.
  change_to_lsubst_aux4; simpl; sp; allrw app_nil_r;
  allrw @isprog_eq; destruct i as [c w]; rw c; sp.
Qed.

Lemma mkcv_zero_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_zero [v]) = mkc_zero.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma mkc_var_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkc_var v) = t.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
  unfold subst.
  change_to_lsubst_aux4; simpl; sp; boolvar; sp.
Qed.

Lemma isprog_vars_natk {p} :
  forall vs (n : @NTerm p),
    isprog_vars vs n
    -> isprog_vars vs (mk_natk n).
Proof.
  introv isp.
  apply isprog_vars_set.
  - apply isprog_vars_int.
  - apply isprog_vars_prod; dands; auto.
    + apply isprog_vars_le; dands; auto.
      * apply isprog_vars_zero.
      * apply isprog_vars_var_if; simpl; tcsp.
    + apply isprog_vars_less_than; dands; auto.
      * apply isprog_vars_var_if; simpl; tcsp.
      * apply isprog_vars_cons; auto.
Qed.

Lemma isprog_natk {p} :
  forall (n : @NTerm p),
    isprog n
    -> isprog (mk_natk n).
Proof.
  introv isp.
  apply isprog_vars_nil_iff_isprog.
  apply isprog_vars_natk.
  apply isprog_vars_nil_iff_isprog; auto.
Qed.

Definition mkc_natk {o} (n : @CTerm o) : CTerm :=
  let (t,x) := n in
  exist isprog (mk_natk t) (isprog_natk t x).

Definition mkcv_natk {o} vs (n : @CVTerm o vs) : CVTerm vs :=
  let (t,x) := n in
  exist (isprog_vars vs) (mk_natk t) (isprog_vars_natk vs t x).

Definition mkcv_int {o} vs : @CVTerm o vs :=
  exist (isprog_vars vs) mk_int (isprog_vars_int vs).

Lemma wf_minus {p} :
  forall (a : @NTerm p), wf_term a -> wf_term (mk_minus a).
Proof.
  intros a; repeat (rw <- @nt_wf_eq).
  intros nta; inversion nta; subst;
  constructor; allsimpl; sp; subst; auto; constructor; auto.
Qed.

Lemma wf_minus_iff {p} :
  forall a : @NTerm p, wf_term a <=> wf_term (mk_minus a).
Proof.
  introv; split; intro i.
  apply wf_minus; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)); intros k1.
  repeat (dest_imp k1 hyp).
  inversion k1; subst; sp.
Qed.

Lemma isprog_vars_minus {p} :
  forall (a : @NTerm p) vs,
    isprog_vars vs (mk_minus a) <=> isprog_vars vs a.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  allrw <- @wf_term_eq.
  allrw <- @wf_minus_iff; split; sp.
Qed.

Lemma isprog_vars_minus_implies {p} :
  forall (a : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs (mk_minus a).
Proof.
  introv ispa.
  apply isprog_vars_minus; sp.
Qed.

Lemma isprog_minus_implies {p} :
  forall (a : @NTerm p),
    isprog a
    -> isprog (mk_minus a).
Proof.
  introv ispa.
  apply isprog_vars_nil_iff_isprog; auto.
  apply isprog_vars_minus; sp.
Qed.

Definition mkc_minus {p} (t : @CTerm p) : CTerm :=
  let (a,x) := t in
  exist isprog (mk_minus a) (isprog_minus_implies a x).

Definition mkcv_function {p} vs (t1 : @CVTerm p vs) (v : NVar) (t2 : CVTerm (v :: vs)) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_function a v b) (isprog_vars_function vs a v b x y).

Definition mkcv_isect {p} vs (t1 : @CVTerm p vs) (v : NVar) (t2 : CVTerm (v :: vs)) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_isect a v b) (isprog_vars_isect vs a v b x y).

Definition mkcv_set {p} vs (t1 : @CVTerm p vs) (v : NVar) (t2 : CVTerm (v :: vs)) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_set a v b) (isprog_vars_set vs a v b x y).

Lemma isprog_vars_fun_implies {p} :
  forall vs (a b : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_fun a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_fun; sp.
Qed.

Definition mkcv_fun {p} vs (A B : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := A in
  let (b,y) := B in
  exist (isprog_vars vs) (mk_fun a b) (isprog_vars_fun_implies vs a b x y).

Lemma isprog_vars_ufun_implies {p} :
  forall vs (a b : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_ufun a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_ufun; sp.
Qed.

Definition mkcv_ufun {p} vs (A B : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := A in
  let (b,y) := B in
  exist (isprog_vars vs) (mk_ufun a b) (isprog_vars_ufun_implies vs a b x y).

Lemma cover_vars_upto_function {o} :
  forall vs (a : @NTerm o) v b sub,
    cover_vars_upto (mk_function a v b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b (csub_filter sub [v]) (v :: vs).
Proof.
  sp; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw subvars_prop; simpl; split; sp; apply_in_hyp pp;
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  generalize (deq_nvar v x); intro q; sp.
  right; right; sp.
Qed.

Lemma cover_vars_upto_fun {o} :
  forall vs (a b : @NTerm o) sub,
    cover_vars_upto (mk_fun a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  introv.
  rw @cover_vars_upto_function.
  split; intro k; repnd; dands; auto.
  - allunfold @cover_vars_upto.
    allrw subvars_prop; introv i.
    applydup k in i; allsimpl; allrw in_app_iff; repndors; subst; tcsp.
    + pose proof (newvar_prop b); sp.
    + rw @dom_csub_csub_filter in i0.
      rw in_remove_nvars in i0; sp.
  - allunfold @cover_vars_upto.
    allrw subvars_prop; introv i.
    applydup k in i; allsimpl; allrw in_app_iff; repndors; tcsp.
    rw @dom_csub_csub_filter.
    rw in_remove_nvars; simpl.
    destruct (deq_nvar (newvar b) x) as [j|j]; subst; tcsp.
    right; right; sp.
Qed.

Lemma cover_vars_upto_ufun {o} :
  forall vs (a b : @NTerm o) sub,
    cover_vars_upto (mk_ufun a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  introv.
  rw @cover_vars_upto_isect.
  split; intro k; repnd; dands; auto.
  - allunfold @cover_vars_upto.
    allrw subvars_prop; introv i.
    applydup k in i; allsimpl; allrw in_app_iff; repndors; subst; tcsp.
    + pose proof (newvar_prop b); sp.
    + rw @dom_csub_csub_filter in i0.
      rw in_remove_nvars in i0; sp.
  - allunfold @cover_vars_upto.
    allrw subvars_prop; introv i.
    applydup k in i; allsimpl; allrw in_app_iff; repndors; tcsp.
    rw @dom_csub_csub_filter.
    rw in_remove_nvars; simpl.
    destruct (deq_nvar (newvar b) x) as [j|j]; subst; tcsp.
    right; right; sp.
Qed.

Definition mkcv_add {p} vs (t1 t2 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_add a b) (isprog_vars_add_implies a b vs x y).

Definition mkcv_apply {p} vs (t1 t2 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_apply a b) (isprog_vars_apply_implies a b vs x y).

Lemma isprog_vars_cbv {p} :
  forall vs (a : @NTerm p) v b,
    isprog_vars vs a
    -> isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_cbv a v b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allrw subvars_prop; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  discover; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Definition mkcv_cbv {p} vs (t1 : @CVTerm p vs) (v : NVar) (t2 : CVTerm (v :: vs)) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist (isprog_vars vs) (mk_cbv a v b) (isprog_vars_cbv vs a v b x y).

Lemma isprog_vars_app_r {p} :
  forall (t : @NTerm p) vs1 vs2,
    isprog_vars vs1 t
    -> isprog_vars (vs1 ++ vs2) t.
Proof.
  sp; alltrewrite (@isprog_vars_eq p); sp.
  alltrewrite subvars_eq.
  apply subset_app_r; sp.
Qed.

Lemma mk_cv_app_r_pf {o} :
  forall vs2 vs1 (t : @CVTerm o vs1),
    isprog_vars (vs1 ++ vs2) (get_cvterm vs1 t).
Proof.
  introv; destruct_cterms; simpl.
  apply isprog_vars_app_r; auto.
Qed.

Lemma mk_cv_app_l_pf {o} :
  forall vs2 vs1 (t : @CVTerm o vs1),
    isprog_vars (vs2 ++ vs1) (get_cvterm vs1 t).
Proof.
  introv; destruct_cterms; simpl.
  apply isprog_vars_app_l; auto.
Qed.

Definition mk_cv_app_r {o} vs2 vs1 (t : @CVTerm o vs1) : @CVTerm o (vs1 ++ vs2) :=
  exist (isprog_vars (vs1 ++ vs2)) (get_cvterm vs1 t) (mk_cv_app_r_pf vs2 vs1 t).

Definition mk_cv_app_l {o} vs2 vs1 (t : @CVTerm o vs1) : @CVTerm o (vs2 ++ vs1) :=
  exist (isprog_vars (vs2 ++ vs1)) (get_cvterm vs1 t) (mk_cv_app_l_pf vs2 vs1 t).

Definition force_int_cv {o} vs (t : @CVTerm o vs) : CVTerm vs :=
  mkcv_add vs t (mkcv_zero vs).

Lemma isprog_vars_less_implies {p} :
  forall (a b c d : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs c
    -> isprog_vars vs d
    -> isprog_vars vs (mk_less a b c d).
Proof.
  introv ispa ispb ispc ispd.
  apply isprog_vars_less; sp.
Qed.

Definition mkcv_less {p} vs (t1 t2 t3 t4 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
  let (d,w) := t4 in
    exist (isprog_vars vs) (mk_less a b c d) (isprog_vars_less_implies a b c d vs x y z w).

Lemma isprog_vars_nat {p} :
  forall vs n,
    @isprog_vars p vs (mk_nat n).
Proof.
  introv.
  apply isprog_vars_eq; simpl; dands; tcsp.
  constructor; simpl; tcsp.
Qed.

Definition mkcv_minus {p} vs (t : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t in
    exist (isprog_vars vs) (mk_minus a) (isprog_vars_minus_implies a vs x).

Definition mkcv_nat {p} vs (n : nat) : @CVTerm p vs :=
  exist (isprog_vars vs) (mk_nat n) (isprog_vars_nat vs n).

Lemma isvalue_mk_integer {o} :
  forall i, @isvalue o (mk_integer i).
Proof.
  introv; constructor; simpl; eauto 3 with slow.
Qed.
Hint Resolve isvalue_mk_integer : slow.

Lemma iscvalue_mkc_integer {o} :
  forall i, @iscvalue o (mkc_integer i).
Proof.
  introv; unfold iscvalue; simpl; eauto with slow.
Qed.
Hint Resolve iscvalue_mkc_integer : slow.



Ltac get_newvar_prop :=
  match goal with
    | [ H : ?v = newvar ?t |- _ ] =>
      let nv := fresh "nv" in
      pose proof (newvar_prop t) as nv;
        rewrite <- H in nv;
        clear H
    | [ H : ?v = newvarlst ?l |- _ ] =>
      let nv := fresh "nv" in
      pose proof (newvarlst_prop l) as nv;
        rewrite <- H in nv;
        clear H
  end.

Lemma fresh_var_not_in2 :
  forall vs1 vs2, subvars vs2 vs1 -> !LIn (fresh_var vs1) vs2.
Proof.
  induction vs2; introv sv i; allsimpl; tcsp.
  repndors; subst.
  - allrw subvars_cons_l; repnd; sp.
    apply fresh_var_not_in in sv0; sp.
  - allrw subvars_cons_l; repnd; sp.
Qed.

Lemma newvars3_prop {p} :
  forall v1 v2 v3 (terms : list (@NTerm p)),
    (v1, v2, v3) = newvars3 terms
    -> !LIn v1 (free_vars_list terms)
       # !LIn v2 (free_vars_list terms)
       # !LIn v3 (free_vars_list terms)
       # !v1 = v2
       # !v1 = v3
       # !v2 = v3.
Proof.
  introv eq.
  unfold newvars3 in eq; cpx.
  unfold newvarlst; simpl; allrw @free_vars_list_app; simpl.
  dands;
    try (apply fresh_var_not_in);
    try (apply fresh_var_not_in2); eauto with slow;
    try (complete (apply subvars_app_weak_l; auto));
    match goal with
      | [ |- context[fresh_var ?t = fresh_var ?u] ] =>
        intro k;
          remember (fresh_var t) as f;
          pose proof (fresh_var_not_in u) as h;
          rewrite <- Heqf in h;
          rewrite <- k in h;
          repeat (trw_h in_app_iff h);
          allsimpl; tcsp
    end.
Qed.

(* This is: {v:UAtom|v ~ a} (both the open and closed versions) *)

Definition mk_singleton_uatom {o} (a : @get_patom_set o) :=
  mk_set mk_uatom nvarx (mk_cequiv (mk_var nvarx) (mk_utoken a)).

Definition mkcv_utoken {o} vs (a : @get_patom_set o) : CVTerm vs :=
  mk_cv vs (mkc_utoken a).

Lemma isprog_vars_cequiv {p} :
  forall vs (a b : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_cequiv a b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Definition mkcv_cequiv {o} vs (a b : @CVTerm o vs) : CVTerm vs :=
  let (ta,pa) := a in
  let (tb,pb) := b in
    exist (isprog_vars vs) (mk_cequiv ta tb) (isprog_vars_cequiv vs ta tb pa pb).

Lemma isprog_vars_approx {p} :
  forall vs (a b : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_approx a b).
Proof.
  introv ipa ipb.
  allrw @isprog_vars_eq; allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
  constructor; simpl; sp; subst; constructor; sp.
Qed.

Definition mkcv_approx {o} vs (a b : @CVTerm o vs) : CVTerm vs :=
  let (ta,pa) := a in
  let (tb,pb) := b in
    exist (isprog_vars vs) (mk_approx ta tb) (isprog_vars_approx vs ta tb pa pb).

Definition mkc_singleton_uatom {o} (a : @get_patom_set o) :=
  mkc_set
    mkc_uatom
    nvarx
    (mkcv_cequiv [nvarx] (mkc_var nvarx) (mkcv_utoken [nvarx] a)).

Definition mk_ntexc {o} a (E : @NTerm o) :=
  mk_texc (mk_singleton_uatom a) E.

Definition mkc_ntexc {o} a (E : @CTerm o) :=
  mkc_texc (mkc_singleton_uatom a) E.

Lemma csubst_mk_cv {p} :
  forall t v (u : @CTerm p), substc u v (mk_cv [v] t) = t.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  apply lsubst_trivial; simpl; sp; cpx; allrw @isprog_eq; sp.
  allunfold @isprogram; repnd.
  allrw i1; sp.
Qed.
