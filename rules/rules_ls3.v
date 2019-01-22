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


Require Export per_props_ffdefs.
Require Export per_props_nat.
Require Export per_props_nat2.
Require Export rules_choice_util3.



Definition mk_csprop {o} (i : nat) : @NTerm o :=
  mk_fun (mk_csname 0) (mk_uni i).

Definition mkc_csprop {o} (i : nat) : @CTerm o :=
  mkc_fun (mkc_csname 0) (mkc_uni i).

Definition mkcv_csprop {o} (vs : list NVar) (i : nat) : @CVTerm o vs :=
  mk_cv _ (mkc_fun (mkc_csname 0) (mkc_uni i)).

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
             (mk_squash
                (mk_exists
                   mk_tnat
                   n
                   (mk_function
                      (mk_csname 0)
                      b
                      (mk_fun
                         (mk_equality (mk_var a) (mk_var b) (mk_natk2nat (mk_var n)))
                         (mk_apply (mk_var A) (mk_var b))))))))).

Definition mkcv_free_from_defs {p} vs (A : @CVTerm p vs) (t : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := A in
  let (b,y) := t in
  exist (isprog_vars _) (mk_free_from_defs a b) (isprog_vars_free_from_defs _ _ _ x y).

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
             (mkcv_squash
                _
                (mkcv_exists
                   _
                   (mkcv_tnat _)
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
                            (mkcv_natk2nat _ (mk_cv_app_r [a,A] _ (mk_cv_app_l [b] _ (mkc_var n)))))
                         (mkcv_apply
                            _
                            (mk_cv_app_l [b,n,a] _ (mkc_var A))
                            (mk_cv_app_r [n,a,A] _ (mkc_var b)))))))))).

Definition ls3_extract {o} (A a x y : NVar) : @NTerm o :=
  mk_lam A (mk_lam a (mk_lam x (mk_lam y mk_axiom))).

Definition ls3c_extract {o} (A a x y : NVar) : @CTerm o :=
  mkc_lam A (mkcv_lam _ a (mkcv_lam _ x (mkcv_lam _ y (mkcv_ax _)))).

Lemma lsubstc_ls3_extract_eq {o} :
  forall A a x y (w : @wf_term o (ls3_extract A a x y)) s c,
    lsubstc (ls3_extract A a x y) w s c = ls3c_extract A a x y.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls3_extract_eq : slow.

Lemma apply3_ls3c_extract_compute {o} :
  forall lib A a x y (u v w z : @CTerm o),
    computes_to_valc
      lib
      (mkc_apply (mkc_apply (mkc_apply (mkc_apply (ls3c_extract A a x y) u) v) w) z)
      mkc_axiom.
Proof.
  introv; destruct_cterms; unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.

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
  forall lib A a x y (u v w z : @CTerm o),
    ccequivc_ext
      lib
      (mkc_apply (mkc_apply (mkc_apply (mkc_apply (ls3c_extract A a x y) u) v) w) z)
      mkc_axiom.
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve apply3_ls3c_extract_ccequivc_ext : slow.

Lemma remove_nvars_trivial1 {o} :
  forall A b,
    remove_nvars [@newvar o (mk_apply (mk_var A) (mk_var b))] [A, b]
    = [A,b].
Proof.
  introv.
  apply remove_nvars_unchanged.
  apply disjoint_singleton_r; intro xx.
  pose proof (@newvar_prop o (mk_apply (mk_var A) (mk_var b))) as q; simpl in q.
  repeat (apply not_over_or in q; repnd).
  simpl in *; repndors; subst; tcsp.
Qed.
Hint Rewrite @remove_nvars_trivial1 : slow.

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

Lemma implies_approx_product {o} :
  forall lib u1 u2 v1 v2 (t1 t2 : @NTerm o),
    isprog u1
    -> isprog u2
    -> isprog_vars [v1] t1
    -> isprog_vars [v2] t2
    -> cequiv lib u1 u2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v1 u) (subst t2 v2 u))
    -> approx lib (mk_product u1 v1 t1) (mk_product u2 v2 t2).
Proof.
  introv ispu1 uspu2 isp1 isp2 cequ imp.

  constructor.
  unfold close_comput; dands;
    try (apply isprog_eq; apply isprog_product);
    eauto 3 with slow;[|].

  - introv comp.
    apply computes_to_value_isvalue_eq in comp;
      try (apply isvalue_product);
      try (apply isprog_eq; apply isprog_product);
      eauto 3 with slow;[].

    unfold mk_product in comp; ginv; fold_terms.
    exists [nobnd u2, bterm [v2] t2]; fold_terms.
    dands.
    { apply computes_to_value_isvalue_refl;
        try (apply isvalue_product);
        try (apply isprog_eq; apply isprog_product);
        eauto 3 with slow. }

    unfold lblift; simpl; dands; auto.
    introv ltn.
    repeat (destruct n; try omega); clear ltn; unfold selectbt; simpl.

    {
      exists ([] : list NVar) u1 u2; dands; eauto 3 with slow.
      apply clearbots_olift; eauto 3 with slow.
      apply approx_implies_approx_open; eauto 3 with slow.
      destruct cequ; auto.
    }

    unfold blift.
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
      destruct p as [z u]; allsimpl.
      allrw @fold_subst.
      allrw @prog_sub_cons; repnd.
      pose proof (imp u) as h; clear imp; allsimpl.
      autodimp h hyp; eauto 3 with slow.
      destruct h; sp.
      eapply approx_trans; eauto.

      eapply approx_alpha_rw_r_aux;
        [apply alpha_eq_sym;apply combine_sub_nest|].
      simpl.
      allrw @fold_subst.
      rw @subst_mk_var1.

      destruct (deq_nvar v2 z); subst.

      * pose proof (cl_lsubst_app_sub_filter t2 [(z,u)] [(z,u)]) as h; allsimpl.
        autodimp h hyp; eauto 3 with slow.
        allrw memvar_singleton; boolvar; rw h; eauto 3 with slow.

      * pose proof (lsubst_sub_filter_alpha t2 [(v2, u), (z, u)] [z]) as h.
        allrw disjoint_singleton_r; allsimpl.
        allrw memvar_singleton; boolvar; tcsp.
        autodimp h hyp.
        { allrw @isprog_vars_eq; repnd.
          allrw subvars_eq.
          introv h; apply isp3 in h; allsimpl; tcsp. }

        eapply approx_alpha_rw_r_aux;[exact h|].
        allrw @fold_subst; eauto 3 with slow.

    + pose proof (alpha_eq_bterm_single_change t2 v2) as h.
      allrw subset_singleton_r.
      autodimp h hyp.
      { introv ix.
        clear imp.
        allrw @isprog_vars_eq; repnd.
        allrw subvars_eq.
        apply isp3 in ix; allsimpl; tcsp. }
      apply h.

  - introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.
Qed.

Lemma implies_approxc_product {o} :
  forall lib u1 u2 v1 v2 (t1 : @CVTerm o [v1]) t2,
    cequivc lib u1 u2
    -> (forall u : CTerm, cequivc lib (substc u v1 t1) (substc u v2 t2))
    -> approxc lib (mkc_product u1 v1 t1) (mkc_product u2 v2 t2).
Proof.
  introv cequ imp.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allunfold @approxc; allsimpl.

  apply implies_approx_product; auto.
  introv isp.
  apply isprogram_eq in isp.
  pose proof (imp (mk_cterm u isp)) as k; allsimpl; auto.
Qed.

Lemma implies_cequivc_product {o} :
  forall lib u1 u2 v1 v2 (t1 : @CVTerm o [v1]) t2,
    cequivc lib u1 u2
    -> (forall u : CTerm, cequivc lib (substc u v1 t1) (substc u v2 t2))
    -> cequivc lib (mkc_product u1 v1 t1) (mkc_product u2 v2 t2).
Proof.
  introv ceqa imp.
  apply cequivc_iff_approxc; dands.
  - apply implies_approxc_product; auto.
  - apply implies_approxc_product.
    { apply cequivc_sym; auto. }
    { introv; apply cequivc_sym; auto. }
Qed.

Lemma implies_ccequivc_ext_product {o} :
  forall lib (A1 A2 : @CTerm o) (v1 v2 : NVar) B1 B2,
    ccequivc_ext lib A1 A2
    -> bcequivc_ext lib [v1] B1 [v2] B2
    -> ccequivc_ext lib (mkc_product A1 v1 B1) (mkc_product A2 v2 B2).
Proof.
  introv ceqa ceqb ext.
  pose proof (ceqa _ ext) as ceqa.
  pose proof (ceqb _ ext) as ceqb.
  simpl in *; spcast.
  apply implies_cequivc_product; auto.
  apply bcequivc1; auto.
Qed.

Lemma implies_bcequivc_ext_substc2_1 {o} :
  forall (lib : @library o) v w t a1 a2,
    ccequivc_ext lib a1 a2
    -> bcequivc_ext lib [v] (substc2 v a1 w t) [v] (substc2 v a2 w t).
Proof.
  introv ceq ext.
  pose proof (ceq _ ext) as ceq; simpl in *; spcast.
  destruct_cterms.
  unfold bcequivc; simpl.
  unfold cequivc in *; simpl in *.
  unfold bcequiv.
  unfold blift.
  exists [v] (subst x1 w x0) (subst x1 w x); dands; eauto 3 with slow.
  apply cequiv_open_lsubst_same_term; eauto 3 with slow.
Qed.

Lemma isprog_vars_substc3_2 {o} :
  forall {v} {wt : @NTerm o} {w} {zt} {z} {u},
    isprog wt
    -> isprog zt
    -> isprog_vars [v,w,z] u
    -> isprog_vars [v] (lsubst u [(z,zt),(w,wt)]).
Proof.
  introv ispa ispb ispc.
  apply isprog_vars_eq in ispc; repnd.
  applydup @closed_if_isprog in ispa.
  applydup @closed_if_isprog in ispb.

  apply implies_isprog_vars.

  {
    apply lsubst_preserves_wf_term; eauto 3 with slow.
    repeat apply wf_sub_cons; eauto 3 with slow.
  }

  allrw @subvars_eq.
  introv i.
  apply eqset_free_vars_disjoint in i; simpl in *.
  left.
  apply in_app_iff in i.
  allrw in_remove_nvars; simpl in *.
  allrw not_over_or.
  repndors; repnd; tcsp.

  { apply ispc0 in i0; simpl in *; repndors; subst; tcsp. }

  boolvar; simpl in *; autorewrite with list in *; tcsp;[| |];
    try (rewrite ispa0 in * );
    try (rewrite ispb0 in * );
    simpl in *; tcsp.
Qed.

Definition substc3_2 {o} v (wt : @CTerm o) (w : NVar) (zt : CTerm) z (u : CVTerm [v,w,z]) : CVTerm [v] :=
  let (a,pa) := wt in
  let (b,pb) := zt in
  let (c,pc) := u in
  exist (isprog_vars [v]) (lsubst c [(z,b),(w,a)]) (isprog_vars_substc3_2 pa pb pc).

Lemma substc2_substc3_eq {o} :
  forall v (wt : @CTerm o) w (zt : @CTerm o) z (u : @CVTerm o [v,w,z]),
    substc2 v wt w (substc3 v w zt z u)
    = substc3_2 v wt w zt z u.
Proof.
  introv.
  destruct_cterms; simpl.
  apply cvterm_eq; simpl.
  unfold subst; rewrite <- cl_lsubst_app; eauto 3 with slow.
Qed.

Lemma isprog_vars_substc4 {o} :
  forall {vt : @NTerm o} {v} {wt : @NTerm o} {w} {zt} {z} {u},
    isprog vt
    -> isprog wt
    -> isprog zt
    -> isprog_vars [v,w,z] u
    -> isprog (lsubst u [(z,zt),(w,wt),(v,vt)]).
Proof.
  introv ispa ispb ispc ispd.
  apply isprog_vars_eq in ispd; repnd.
  applydup @closed_if_isprog in ispa.
  applydup @closed_if_isprog in ispb.
  applydup @closed_if_isprog in ispc.

  apply isprog_eq; apply isprogram_lsubst_prog_sub; eauto 3 with slow.

  { repeat try (apply prog_sub_cons; dands); eauto 3 with slow. }

  simpl.
  allrw subvars_eq.
  introv i; apply ispd0 in i; simpl in *; repndors; subst; tcsp.
Qed.

Definition substc4 {o} (vt : @CTerm o) v (wt : @CTerm o) (w : NVar) (zt : CTerm) z (u : CVTerm [v,w,z]) : CTerm :=
  let (a,pa) := vt in
  let (b,pb) := wt in
  let (c,pc) := zt in
  let (d,pd) := u in
  exist isprog (lsubst d [(z,c),(w,b),(v,a)]) (isprog_vars_substc4 pa pb pc pd).

Lemma substc3_2_substc_eq {o} :
  forall (vt : @CTerm o) v (wt : @CTerm o) w (zt : @CTerm o) z (u : @CVTerm o [v,w,z]),
    substc vt v (substc3_2 v wt w zt z u)
    = substc4 vt v wt w zt z u.
Proof.
  introv.
  destruct_cterms; simpl.
  apply cterm_eq; simpl.
  unfold subst; rewrite <- cl_lsubst_app; eauto 3 with slow.
  apply cl_sub_cons; dands; eauto 3 with slow.
Qed.


Definition cs_size {o} (lib : @library o) (name : choice_sequence_name) : nat :=
  match find_cs lib name with
  | Some e => length (cse_vals e)
  | None => 0
  end.

Definition cs_name_restr_size (name : choice_sequence_name) : nat :=
  match csn_kind name with
  | cs_kind_nat n => 0
  | cs_kind_seq l => length l
  end.

Definition entry_size {o} (entry : @library_entry o) : nat :=
  match entry with
  | lib_cs name e => Peano.max (length (cse_vals e)) (cs_name_restr_size name)
  | _ => 0
  end.

Fixpoint lib_size {o} (lib : @library o) : nat :=
  match lib with
  | [] => 0
  | entry :: entries => Peano.max (entry_size entry) (lib_size entries)
  end.

Lemma substc2_ffdefs {o} :
  forall v x (w : @CTerm o) (t u : CVTerm [v,x]),
    alphaeqcv
      [v]
      (substc2 v w x (mkcv_free_from_defs [v,x] t u))
      (mkcv_free_from_defs [v] (substc2 v w x t) (substc2 v w x u)).
Proof.
  introv.
  destruct_cterms.
  unfold alphaeqcv; simpl.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
Qed.

Lemma mkcv_ffdefs_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_free_from_defs [v] a b)
    = mkc_free_from_defs (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @mkcv_ffdefs_substc : slow.

Lemma substc2_mkcv_csprop {o} :
  forall x (t : @CTerm o) v i,
    substc2 x t v (mkcv_csprop _ i)
    = mkcv_csprop _ i.
Proof.
  introv; destruct_cterms; apply cvterm_eq; simpl; unfsubst.
Qed.
Hint Rewrite @substc2_mkcv_csprop : slow.

Lemma substc_mkcv_csprop {o} :
  forall (t : @CTerm o) v i,
    substc t v (mkcv_csprop _ i)
    = mkc_csprop i.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; unfsubst.
Qed.
Hint Rewrite @substc_mkcv_csprop : slow.

Lemma isprog_vars_substc5 {o} :
  forall {x} {vt : @NTerm o} {v} {wt : @NTerm o} {w} {zt} {z} {u},
    isprog vt
    -> isprog wt
    -> isprog zt
    -> isprog_vars [x,v,w,z] u
    -> isprog_vars [x] (lsubst u [(z,zt),(w,wt),(v,vt)]).
Proof.
  introv ispa ispb ispc ispd.
  apply isprog_vars_eq in ispd; repnd.
  applydup @closed_if_isprog in ispa.
  applydup @closed_if_isprog in ispb.
  applydup @closed_if_isprog in ispc.

  apply isprog_vars_eq; auto; dands.

  { allrw subvars_eq; introv i.
    apply eqset_free_vars_disjoint in i; simpl in *.
    apply in_app_iff in i; repndors.

    { apply in_remove_nvars in i; simpl in *; repnd.
      repeat (rw @not_over_or in i); repnd; GC.
      apply ispd0 in i0; simpl in *; repndors; subst; tcsp. }

    boolvar; simpl in *; autorewrite with slow in *;
      try (rw ispa0 in i);
      try (rw ispb0 in i);
      try (rw ispc0 in i);
      simpl in *; tcsp. }

  apply lsubst_wf_if_eauto; eauto 3 with slow.
  repeat (apply wf_sub_cons; eauto 3 with slow).
Qed.

Definition substc5 {o} x (vt : @CTerm o) v (wt : @CTerm o) (w : NVar) (zt : CTerm) z (u : CVTerm [x,v,w,z]) : CVTerm [x] :=
  let (a,pa) := vt in
  let (b,pb) := wt in
  let (c,pc) := zt in
  let (d,pd) := u in
  exist (isprog_vars [x]) (lsubst d [(z,c),(w,b),(v,a)]) (isprog_vars_substc5 pa pb pc pd).

Lemma substc4_mkcv_function {o} :
  forall (t1 t2 t3 : @CTerm o) v w z a x b,
    v <> w
    -> w <> z
    -> x <> v
    -> x <> z
    -> x <> w
    -> substc4 t1 v t2 w t3 z (mkcv_function [v,w,z] a x b)
       = mkc_function (substc4 t1 v t2 w t3 z a) x (substc5 x t1 v t2 w t3 z b).
Proof.
  introv d1 d2 d3 d4 d5; destruct_cterms; apply cterm_eq; simpl.
  repeat (unflsubst; eauto 3 with slow;
          [|repeat (apply cl_sub_cons; dands; eauto 3 with slow)];[]).
  simpl; autorewrite with slow; boolvar; simpl in *; tcsp.
Qed.

Lemma substc4_mkcv_csname {o} :
  forall (t1 t2 t3 : @CTerm o) v w z n,
    substc4 t1 v t2 w t3 z (mkcv_csname _ n) = mkc_csname n.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl.
  unflsubst; eauto 3 with slow.
  repeat (apply cl_sub_cons; dands; eauto 3 with slow).
Qed.
Hint Rewrite @substc4_mkcv_csname : slow.

Lemma eq_option_refl {o} :
  forall (x : option (@NTerm o)),
    eq_option x x.
Proof.
  introv; destruct x; simpl; auto.
Qed.
Hint Resolve eq_option_refl : slow.

Lemma eq_lsubst_aux_cons_not_in {o} :
  forall (t : @NTerm o) v u sub,
    cl_sub sub
    -> closed u
    -> !LIn v (free_vars t)
    -> lsubst_aux t ((v, u) :: sub) = lsubst_aux t sub.
Proof.
  introv cl1 cl2 ni.
  apply eq_lsubst_aux_if_ext_eq; simpl; eauto 3 with slow.

  { introv i; simpl; boolvar; tcsp; eauto 3 with slow. }

  { rw cl2; simpl.
    rw @sub_free_vars_if_cl_sub; auto. }

  { rw @sub_free_vars_if_cl_sub; auto. }
Qed.

Lemma eq_lsubst_aux_cons_cons_swap {o} :
  forall (t : @NTerm o) v u z w sub,
    v <> z
    -> cl_sub sub
    -> closed u
    -> closed w
    -> lsubst_aux t ((v,u) :: (z,w) :: sub)
       = lsubst_aux t ((z,w) :: (v,u) :: sub).
Proof.
  introv d cl1 cl2 cl3.
  apply eq_lsubst_aux_if_ext_eq; simpl; eauto 3 with slow.

  { introv i; simpl; boolvar; tcsp; eauto 3 with slow. }

  { rw cl2; simpl.
    rw cl3; simpl.
    rw @sub_free_vars_if_cl_sub; auto. }

  { rw cl2; simpl.
    rw cl3; simpl.
    rw @sub_free_vars_if_cl_sub; auto. }
Qed.

Lemma eq_lsubst_aux_cons_cons_cons_swap {o} :
  forall (t : @NTerm o) v u z w x y sub,
    v <> x
    -> z <> x
    -> cl_sub sub
    -> closed u
    -> closed w
    -> closed y
    -> lsubst_aux t ((v,u) :: (z,w) :: (x,y) :: sub)
       = lsubst_aux t ((x,y) :: (v,u) :: (z,w) :: sub).
Proof.
  introv d1 d2 cl1 cl2 cl3 cl4.
  apply eq_lsubst_aux_if_ext_eq; simpl; eauto 3 with slow.

  { introv i; simpl; boolvar; tcsp; eauto 3 with slow. }

  { rw cl2; simpl.
    rw cl3; simpl.
    rw cl4; simpl.
    rw @sub_free_vars_if_cl_sub; auto. }

  { rw cl2; simpl.
    rw cl3; simpl.
    rw cl4; simpl.
    rw @sub_free_vars_if_cl_sub; auto. }
Qed.

Lemma substc5_mkcv_fun {o} :
  forall (t1 t2 t3 : @CTerm o) x v w z a b,
    alphaeqcv
      _
      (substc5 x t1 v t2 w t3 z (mkcv_fun _ a b))
      (mkcv_fun _ (substc5 x t1 v t2 w t3 z a) (substc5 x t1 v t2 w t3 z b)).
Proof.
  introv.
  destruct_cterms.
  unfold alphaeqcv; simpl.
  repeat (unflsubst;repeat (apply cl_sub_cons; dands; eauto 3 with slow);[]).

  simpl.
  autorewrite with slow.

  unfold mk_fun; simpl.

  remember (newvar x3) as nv1.
  pose proof (newvar_prop x3) as p1.
  rewrite <- Heqnv1 in p1.

  remember (newvar (lsubst_aux x3 [(z, x0), (w, x1), (v, x2)])) as nv2.
  pose proof (newvar_prop (lsubst_aux x3 [(z, x0), (w, x1), (v, x2)])) as p2.
  rewrite <- Heqnv2 in p2.

  unfold mk_function, nobnd.
  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (all_vars (lsubst_aux x3
                                                 (if beq_var z nv1
                                                  then
                                                    if beq_var w nv1
                                                    then if beq_var v nv1 then [] else [(v, x2)]
                                                    else (w, x1) :: (if beq_var v nv1 then [] else [(v, x2)])
                                                  else
                                                    (z, x0)
                                                      :: (if beq_var w nv1
                                                          then if beq_var v nv1 then [] else [(v, x2)]
                                                          else (w, x1) :: (if beq_var v nv1 then [] else [(v, x2)]))))
                                     ++ all_vars (lsubst_aux x3 [(z, x0), (w, x1), (v, x2)]))) as fv.
  exrepnd.

  apply (al_bterm_aux [v0]); auto.
  {
    apply disjoint_singleton_l; auto.
  }

  assert (!LIn nv1 (free_vars (lsubst_aux x3 [(z, x0), (w, x1), (v, x2)]))) as ni1.
  {
    introv h.
    apply free_vars_lsubst_aux_subset in h.
    rewrite sub_free_vars_if_cl_sub in h;
      repeat (apply cl_sub_cons; dands; eauto 3 with slow);[].
    autorewrite with slow in h.
    apply in_remove_nvars in h; sp.
  }

  simpl.
  remember (beq_var z nv1) as b1.
  destruct b1; simpl; autorewrite with slow in *.

  {
    apply beq_var_true in Heqb1; subst z.
    unfold var_ren; simpl.

    remember (beq_var w nv1) as b2.
    destruct b2; simpl; autorewrite with slow in *.

    {
      apply beq_var_true in Heqb2; subst w.

      remember (beq_var v nv1) as b3.
      destruct b3; simpl; autorewrite with slow in *.

      {
        apply beq_var_true in Heqb3; subst v.

        rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].
        rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].
        rewrite (lsubst_aux_trivial_cl_term _ [(nv1,x0),(nv1,x1),(nv1,x2)]);
          [|simpl;repeat (apply disjoint_cons_r; dands; auto)];[].
        eauto 3 with slow.
      }

      {
        rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].
        rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto; intro xx;
            rewrite free_vars_lsubst_aux_cl in xx; eauto 3 with slow; simpl in *;
            apply in_remove_nvars in xx; simpl in *; repnd; tcsp];[].
        rewrite (eq_lsubst_aux_cons_not_in _ nv1); eauto 3 with slow;
          repeat (apply cl_sub_cons; dands; eauto 3 with slow);[].
        rewrite (eq_lsubst_aux_cons_not_in _ nv1); eauto 3 with slow;
          repeat (apply cl_sub_cons; dands; eauto 3 with slow).
      }
    }

    {
      remember (beq_var v nv1) as b3.
      destruct b3; simpl; autorewrite with slow in *.

      {
        apply beq_var_true in Heqb3; subst v.

        rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].
        rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto; intro xx;
            rewrite free_vars_lsubst_aux_cl in xx; eauto 3 with slow; simpl in *;
            apply in_remove_nvars in xx; simpl in *; repnd; tcsp];[].
        rewrite (eq_lsubst_aux_cons_not_in _ nv1); eauto 3 with slow;
          repeat (apply cl_sub_cons; dands; eauto 3 with slow);[].
        rewrite eq_lsubst_aux_cons_cons_swap; eauto 3 with slow;
          try (intro xx; subst w; autorewrite with slow in *; ginv);[].
        rewrite (eq_lsubst_aux_cons_not_in _ nv1); eauto 3 with slow;
          repeat (apply cl_sub_cons; dands; eauto 3 with slow).
      }

      {
        rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].
        rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto; intro xx;
            rewrite free_vars_lsubst_aux_cl in xx; eauto 3 with slow; simpl in *;
            repeat (apply cl_sub_cons; dands; eauto 3 with slow);
            apply in_remove_nvars in xx; simpl in *; repnd; tcsp];[].
        rewrite (eq_lsubst_aux_cons_not_in _ nv1); eauto 3 with slow;
          repeat (apply cl_sub_cons; dands; eauto 3 with slow).
      }
    }
  }

  {
    unfold var_ren; simpl.

    remember (beq_var w nv1) as b2.
    destruct b2; simpl; autorewrite with slow in *.

    {
      apply beq_var_true in Heqb2; subst w.

      remember (beq_var v nv1) as b3.
      destruct b3; simpl; autorewrite with slow in *.

      {
        apply beq_var_true in Heqb3; subst v.

        rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto; intro xx;
            rewrite free_vars_lsubst_aux_cl in xx; eauto 3 with slow; simpl in *;
            repeat (apply cl_sub_cons; dands; eauto 3 with slow);
            apply in_remove_nvars in xx; simpl in *; repnd; tcsp];[].
        rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].
        rewrite eq_lsubst_aux_cons_cons_swap; eauto 3 with slow;
          try (intro xx; subst z; autorewrite with slow in *; ginv);[].
        rewrite (eq_lsubst_aux_cons_not_in _ nv1); eauto 3 with slow;
          repeat (apply cl_sub_cons; dands; eauto 3 with slow).
        rewrite eq_lsubst_aux_cons_cons_swap; eauto 3 with slow;
          try (intro xx; subst z; autorewrite with slow in *; ginv);[].
        rewrite (eq_lsubst_aux_cons_not_in _ nv1); eauto 3 with slow;
          repeat (apply cl_sub_cons; dands; eauto 3 with slow).
      }

      {
        rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].
        rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto; intro xx;
            rewrite free_vars_lsubst_aux_cl in xx; eauto 3 with slow; simpl in *;
            repeat (apply cl_sub_cons; dands; eauto 3 with slow);
            apply in_remove_nvars in xx; simpl in *; repnd; tcsp];[].
        rewrite (eq_lsubst_aux_cons_cons_swap _ z _ nv1); eauto 3 with slow;
          try (intro xx; subst z; autorewrite with slow in *; ginv);[].
        rewrite (eq_lsubst_aux_cons_not_in _ nv1); eauto 3 with slow;
          repeat (apply cl_sub_cons; dands; eauto 3 with slow).
      }
    }

    {
      remember (beq_var v nv1) as b3.
      destruct b3; simpl; autorewrite with slow in *.

      {
        apply beq_var_true in Heqb3; subst v.

        rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].
        rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto; intro xx;
            rewrite free_vars_lsubst_aux_cl in xx; eauto 3 with slow; simpl in *;
            repeat (apply cl_sub_cons; dands; eauto 3 with slow);
            apply in_remove_nvars in xx; simpl in *; repnd; tcsp];[].
        rewrite eq_lsubst_aux_cons_cons_cons_swap; eauto 3 with slow;
          try (complete (intro xx; subst z; autorewrite with slow in *; ginv));
          try (complete (intro xx; subst w; autorewrite with slow in *; ginv)).
        rewrite (eq_lsubst_aux_cons_not_in _ nv1); eauto 3 with slow;
          repeat (apply cl_sub_cons; dands; eauto 3 with slow).
      }

      {
        rewrite (lsubst_aux_trivial_cl_term _ [(nv2,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto];[].
        rewrite (lsubst_aux_trivial_cl_term _ [(nv1,vterm v0)]);
          [|simpl;apply disjoint_singleton_r; auto; intro xx;
            rewrite free_vars_lsubst_aux_cl in xx; eauto 3 with slow; simpl in *;
            repeat (apply cl_sub_cons; dands; eauto 3 with slow);
            apply in_remove_nvars in xx; simpl in *; repnd; tcsp];[].
        eauto 3 with slow.
      }
    }
  }
Qed.

Lemma substc5_mkcv_equality {o} :
  forall (t1 t2 t3 : @CTerm o) x v w z a b c,
    substc5 x t1 v t2 w t3 z (mkcv_equality _ a b c)
    = mkcv_equality
        _
        (substc5 x t1 v t2 w t3 z a)
        (substc5 x t1 v t2 w t3 z b)
        (substc5 x t1 v t2 w t3 z c).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat (unflsubst;repeat (apply cl_sub_cons; dands; eauto 3 with slow)).
Qed.
Hint Rewrite @substc5_mkcv_equality : slow.

Lemma substc5_mkcv_apply {o} :
  forall (t1 t2 t3 : @CTerm o) x v w z a b,
    substc5 x t1 v t2 w t3 z (mkcv_apply _ a b)
    = mkcv_apply
        _
        (substc5 x t1 v t2 w t3 z a)
        (substc5 x t1 v t2 w t3 z b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat (unflsubst;repeat (apply cl_sub_cons; dands; eauto 3 with slow)).
Qed.
Hint Rewrite @substc5_mkcv_apply : slow.

Lemma substc5_var2 {o} :
  forall (t1 t2 t3 : @CTerm o) x u v w,
    v <> w
    -> substc5 x t1 u t2 v t3 w (mk_cv_app_r [w] [x, u, v] (mk_cv_app_l [x, u] [v] (mkc_var v)))
       = mk_cv _ t2.
Proof.
  introv d1; destruct_cterms; apply cvterm_eq; simpl.
  unflsubst; simpl;repeat (apply cl_sub_cons; dands; eauto 3 with slow).
  autorewrite with slow; boolvar; tcsp.
Qed.

Lemma substc5_var0 {o} :
  forall (t1 t2 t3 : @CTerm o) x u v w,
    w <> x
    -> v <> x
    -> u <> x
    -> substc5 x t1 u t2 v t3 w (mk_cv_app_r [u, v, w] [x] (mkc_var x))
       = mkc_var x.
Proof.
  introv d1 d2 d3; destruct_cterms; apply cvterm_eq; simpl.
  unflsubst; simpl;repeat (apply cl_sub_cons; dands; eauto 3 with slow).
  autorewrite with slow; boolvar; tcsp.
Qed.

Lemma substc5_var3 {o} :
  forall (t1 t2 t3 : @CTerm o) x u v w,
    substc5 x t1 u t2 v t3 w (mk_cv_app_l [x, u, v] [w] (mkc_var w))
    = mk_cv _ t3.
Proof.
  introv; destruct_cterms; apply cvterm_eq; simpl.
  unflsubst; simpl;repeat (apply cl_sub_cons; dands; eauto 3 with slow).
  autorewrite with slow; boolvar; tcsp.
Qed.
Hint Rewrite @substc5_var3 : slow.

Lemma substc5_mkcv_tnat {o} :
  forall (t1 t2 t3 : @CTerm o) x v w z,
    substc5 x t1 v t2 w t3 z (mkcv_tnat _)
    = mkcv_tnat _.
Proof.
  introv; destruct_cterms; apply cvterm_eq; simpl.
  rewrite cl_lsubst_trivial; simpl; eauto 3 with slow.
  repeat (apply cl_sub_cons; dands; eauto 3 with slow).
Qed.
Hint Rewrite @substc5_mkcv_tnat : slow.

Lemma alpha_eq_mk_set {o} :
  forall v (a1 a2 : @NTerm o) v1 v2 b1 b2,
    !LIn v (all_vars b1)
    -> !LIn v (all_vars b2)
    -> alpha_eq a1 a2
    -> alpha_eq (subst_aux b1 v1 (mk_var v)) (subst_aux b2 v2 (mk_var v))
    -> alpha_eq (mk_set a1 v1 b1) (mk_set a2 v2 b2).
Proof.
  introv ni1 ni2 aeqa aeqb.
  constructor; simpl; auto.
  introv i.
  repeat (destruct n; tcsp); unfold selectbt; simpl.
  - apply alphaeqbt_nilv2; auto.
  - apply (al_bterm _ _ [v]); simpl; auto.
    allrw disjoint_singleton_l; allrw in_app_iff; sp.
    rewrite lsubst_lsubst_aux; simpl;
      [|apply disjoint_singleton_r;
        intro j; apply bound_vars_subset_allvars in j;
        pose proof (allvars_eq_all_vars b1) as q; apply eqvars_is_eqset in q;
        apply q in j; tcsp];[].
    rewrite lsubst_lsubst_aux; simpl;
      [|apply disjoint_singleton_r;
        intro j; apply bound_vars_subset_allvars in j;
        pose proof (allvars_eq_all_vars b2) as q; apply eqvars_is_eqset in q;
        apply q in j; tcsp];[].
    auto.
Qed.

Lemma alpha_eq_mk_product {o} :
  forall v (a1 a2 : @NTerm o) v1 v2 b1 b2,
    !LIn v (all_vars b1)
    -> !LIn v (all_vars b2)
    -> alpha_eq a1 a2
    -> alpha_eq (subst_aux b1 v1 (mk_var v)) (subst_aux b2 v2 (mk_var v))
    -> alpha_eq (mk_product a1 v1 b1) (mk_product a2 v2 b2).
Proof.
  introv ni1 ni2 aeqa aeqb.
  constructor; simpl; auto.
  introv i.
  repeat (destruct n; tcsp); unfold selectbt; simpl.
  - apply alphaeqbt_nilv2; auto.
  - apply (al_bterm _ _ [v]); simpl; auto.
    allrw disjoint_singleton_l; allrw in_app_iff; sp.
    rewrite lsubst_lsubst_aux; simpl;
      [|apply disjoint_singleton_r;
        intro j; apply bound_vars_subset_allvars in j;
        pose proof (allvars_eq_all_vars b1) as q; apply eqvars_is_eqset in q;
        apply q in j; tcsp];[].
    rewrite lsubst_lsubst_aux; simpl;
      [|apply disjoint_singleton_r;
        intro j; apply bound_vars_subset_allvars in j;
        pose proof (allvars_eq_all_vars b2) as q; apply eqvars_is_eqset in q;
        apply q in j; tcsp];[].
    auto.
Qed.

Lemma alpha_eq_mk_function {o} :
  forall v (a1 a2 : @NTerm o) v1 v2 b1 b2,
    !LIn v (all_vars b1)
    -> !LIn v (all_vars b2)
    -> alpha_eq a1 a2
    -> alpha_eq (subst_aux b1 v1 (mk_var v)) (subst_aux b2 v2 (mk_var v))
    -> alpha_eq (mk_function a1 v1 b1) (mk_function a2 v2 b2).
Proof.
  introv ni1 ni2 aeqa aeqb.
  constructor; simpl; auto.
  introv i.
  repeat (destruct n; tcsp); unfold selectbt; simpl.
  - apply alphaeqbt_nilv2; auto.
  - apply (al_bterm _ _ [v]); simpl; auto.
    allrw disjoint_singleton_l; allrw in_app_iff; sp.
    rewrite lsubst_lsubst_aux; simpl;
      [|apply disjoint_singleton_r;
        intro j; apply bound_vars_subset_allvars in j;
        pose proof (allvars_eq_all_vars b1) as q; apply eqvars_is_eqset in q;
        apply q in j; tcsp];[].
    rewrite lsubst_lsubst_aux; simpl;
      [|apply disjoint_singleton_r;
        intro j; apply bound_vars_subset_allvars in j;
        pose proof (allvars_eq_all_vars b2) as q; apply eqvars_is_eqset in q;
        apply q in j; tcsp];[].
    auto.
Qed.

Lemma alpha_eq_mk_less {o} :
  forall (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    alpha_eq a1 a2
    -> alpha_eq b1 b2
    -> alpha_eq c1 c2
    -> alpha_eq d1 d2
    -> alpha_eq (mk_less a1 b1 c1 d1) (mk_less a2 b2 c2 d2).
Proof.
  introv aeqa aeqb aeqc aeqd.
  constructor; simpl; auto.
  introv i.
  repeat (destruct n; tcsp); unfold selectbt; simpl; apply alphaeqbt_nilv2; auto.
Qed.

Lemma alpha_eq_mk_less_than {o} :
  forall (a1 a2 b1 b2 : @NTerm o),
    alpha_eq a1 a2
    -> alpha_eq b1 b2
    -> alpha_eq (mk_less_than a1 b1) (mk_less_than a2 b2).
Proof.
  introv aeqa aeqb.
  constructor; simpl; auto.
  introv i.
  repeat (destruct n; tcsp); unfold selectbt; simpl; apply alphaeqbt_nilv2; auto.
Qed.

Hint Rewrite VarBeq_refl : slow.

Lemma trivial_sub_find_if_None {o} :
  forall (t : @NTerm o) v w,
    sub_find (if beq_var w v then [] else [(w, t)]) v = None.
Proof.
  introv; boolvar; simpl; tcsp; boolvar; tcsp.
Qed.
Hint Rewrite @trivial_sub_find_if_None : slow.

Lemma VarBeq_as_beq_var :
  forall v1 v2,
    VarBeq v1 v2 = beq_var (nvar v1) (nvar v2).
Proof.
  tcsp.
Qed.

Hint Resolve VarLt_implies_VarLe : slow.
Hint Resolve not_VarLt_implies_VarLe : slow.
Hint Resolve VarLe_trans : slow.
Hint Resolve sort_issorted : slow.

Lemma implies_issorted_insert :
  forall x l,
    issorted l
    -> issorted (insert x l).
Proof.
  induction l; introv h; simpl in *; eauto 3 with slow.
  { constructor; simpl in *; tcsp; eauto. }
  destruct a; simpl in *.
  inversion h as [|? ? imp iss]; subst; simpl in *; clear h.
  boolvar; eauto 3 with slow.
  { constructor; eauto 3 with slow.
    introv q.
    destruct x0; simpl in *.
    apply in_insert in q; repndors; subst; tcsp; eauto 3 with slow;[].
    apply imp in q; auto. }
  { constructor; eauto 3 with slow.
    introv q; simpl in *; repndors; subst; tcsp; eauto 3 with slow;[].
    destruct x0; simpl in *.
    apply imp in q; eauto 3 with slow. }
Qed.
Hint Resolve implies_issorted_insert : slow.

Lemma VarBeq_insert_false :
  forall v w l,
    VarBeq w (fresh_var_aux v (insert w (sort l))) = false.
Proof.
  introv; unfold VarBeq; boolvar; auto.
  pose proof (fresh_var_aux_sorted_not_in (insert w (sort l))) as q.
  autodimp q hyp; eauto 3 with slow.
  pose proof (q v) as q.
  rewrite <- e in q; destruct q.
  apply in_insert; tcsp.
Qed.
Hint Rewrite VarBeq_insert_false : slow.

Lemma sub_find_single_same {o} :
  forall v (t : @NTerm o),
    sub_find [(v, t)] v = Some t.
Proof.
  introv; simpl; boolvar; auto.
Qed.
Hint Rewrite @sub_find_single_same : slow.

Hint Resolve newvar_prop : slow.

Lemma not_in_newvar_mk_less_than_snd {o} :
  forall (u t : @NTerm o),
    ! LIn (newvar (mk_less_than u t)) (free_vars t).
Proof.
  introv i.
  pose proof (newvar_prop (mk_less_than u t)) as q; simpl in *.
  autorewrite with list slow in *.
  rw in_app_iff in q; apply not_over_or in q; repnd; tcsp.
Qed.
Hint Resolve not_in_newvar_mk_less_than_snd : slow.

Lemma beq_var_newvar_mk_less_then_var {o} :
  forall v (t : @NTerm o),
    beq_var v (newvar (mk_less_than (mk_var v) t)) = false.
Proof.
  introv; boolvar; auto.
  pose proof (newvar_prop (mk_less_than (mk_var v) t)) as q; simpl in q.
  apply not_over_or in q; repnd; tcsp.
Qed.
Hint Rewrite @beq_var_newvar_mk_less_then_var : slow.

Lemma VarBeq_fresh_var_insert_as {o} :
  forall v (t : @NTerm o),
    VarBeq
      (fresh_var_aux
         varx
         (insert (fresh_var_aux varx (sort (free_vars t))) (sort (free_vars t))))
      v
    = beq_var (fresh_var (newvar t :: (free_vars t))) (nvar v).
Proof.
  tcsp.
Qed.

Lemma newvar_not_in_cl_lsubst {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub
    -> !LIn (newvar t) (free_vars (lsubst_aux t sub)).
Proof.
  introv cl i.
  pose proof (newvar_prop t) as q; simpl in q.
  rewrite free_vars_lsubst_aux_cl in i; auto.
  apply in_remove_nvars in i; repnd; tcsp.
Qed.
Hint Resolve newvar_not_in_cl_lsubst : slow.

Lemma newvar_mk_less_than_not_in_cl_lsubst {o} :
  forall (u t : @NTerm o) sub,
    cl_sub sub
    -> !LIn (newvar (mk_less_than u t)) (free_vars (lsubst_aux t sub)).
Proof.
  introv cl i.
  pose proof (newvar_prop (mk_less_than u t)) as q; simpl in q.
  autorewrite with slow in *.
  rw in_app_iff in q; rw not_over_or in q; repnd.
  rewrite free_vars_lsubst_aux_cl in i; auto.
  apply in_remove_nvars in i; repnd; tcsp.
Qed.
Hint Resolve newvar_mk_less_than_not_in_cl_lsubst : slow.


Lemma alpha_eq_lsubst_mk_natk {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub
    -> alpha_eq (lsubst (mk_natk t) sub) (mk_natk (lsubst t sub)).
Proof.
  introv cl.
  repeat unflsubst; simpl; autorewrite with slow.
  unfold  mk_natk, mk_natk_aux.
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
          [|apply disjoint_singleton_r; eauto 3 with slow];[]).
  repeat (rewrite lsubst_aux_sub_filter in fvv1;
          [|apply disjoint_singleton_r; eauto 3 with slow];[]).

  match goal with
  | [ |- alpha_eq (mk_product _ _ ?a) (mk_product _ _ ?b) ] =>
    pose proof (ex_fresh_var (all_vars a ++ all_vars b)) as fvw
  end.
  exrepnd.
  rw @in_app_iff in fvw0; rw not_over_or in fvw0; repnd.

  apply (alpha_eq_mk_product v0); auto;[].
  unfold subst_aux; simpl in *; autorewrite with slow in *; fold_terms.

  destruct v; simpl.
  apply alpha_eq_mk_less_than; auto;[|].

  {
    repeat rewrite VarBeq_fresh_var_insert_as.
    boolvar; eauto 3 with slow.

    { pose proof (fresh_var_not_in (newvar t :: free_vars t)) as q.
      rewrite Heqb in q; simpl in q; apply not_over_or in q; repnd; tcsp. }

    { pose proof (fresh_var_not_in (newvar (lsubst_aux t sub) :: free_vars (lsubst_aux t sub))) as q.
      rewrite Heqb0 in q; simpl in q; apply not_over_or in q; repnd; tcsp. }
  }

  {
    rewrite (lsubst_aux_trivial3 (lsubst_aux t sub));
      [|simpl; introv h; repndors; tcsp; ginv; simpl; dands; eauto 3 with slow;
        apply disjoint_singleton_l; intro xx;
        destruct fvv0; right;
        rw in_app_iff; right; simpl;
        right; right; right; right;
        rw in_app_iff; left; auto];[].

    rewrite (lsubst_aux_trivial3 (lsubst_aux t sub)) in fvw1;
      [|simpl; introv h; repndors; tcsp; ginv; simpl; dands; eauto 3 with slow;
        apply disjoint_singleton_l; intro xx;
        destruct fvv0; right;
        rw in_app_iff; right; simpl;
        right; right; right; right;
        rw in_app_iff; left; auto];[].

    rewrite (lsubst_aux_trivial3 (lsubst_aux t sub)) in fvw0;
      [|simpl; introv h; repndors; tcsp; ginv; simpl; dands; eauto 3 with slow;
        apply disjoint_singleton_l; intro xx;
        destruct fvv0; right;
        rw in_app_iff; right; simpl;
        right; right; right; right;
        rw in_app_iff; left; auto];[].

    rewrite (lsubst_aux_trivial3 (lsubst_aux t sub));
      [|simpl; introv h; repndors; tcsp; ginv; simpl; dands; eauto 3 with slow;
        apply disjoint_singleton_l; intro xx;
        destruct fvw0; right;
        rw in_app_iff; right; simpl;
        rw in_app_iff; left; auto];[].

    rewrite (lsubst_aux_trivial3 (lsubst_aux t sub));
      [|simpl; introv h; repndors; tcsp; ginv; simpl; dands; eauto 3 with slow;
        apply disjoint_singleton_l; intro xx;
        destruct fvv0; right;
        rw in_app_iff; right; simpl;
        right; right; right; right;
        rw in_app_iff; left; auto];[].

    rewrite (lsubst_aux_trivial3 (lsubst_aux t sub));
      [|simpl; introv h; repndors; tcsp; ginv; simpl; dands; eauto 3 with slow;
        apply disjoint_singleton_l; intro xx;
        destruct fvw0; right;
        rw in_app_iff; right; auto;
        rw in_app_iff; left; auto];[].

    eauto 3 with slow.
  }
Qed.
Hint Resolve alpha_eq_lsubst_mk_natk : slow.

Lemma substc5_mkcv_natk {o} :
  forall (t1 t2 t3 : @CTerm o) x v w z a,
    alphaeqcv
      _
      (substc5 x t1 v t2 w t3 z (mkcv_natk _ a))
      (mkcv_natk _ (substc5 x t1 v t2 w t3 z a)).
Proof.
  introv; destruct_cterms; unfold alphaeqcv; simpl.
  remember [(z, x0), (w, x1), (v, x2)] as sub.
  assert (cl_sub sub) as cl by (subst; repeat (apply cl_sub_cons; dands; eauto 3 with slow)).
  eauto 3 with slow.
Qed.
Hint Resolve substc5_mkcv_natk : slow.

Lemma implies_alphaeqcv_mkcv_fun {o} :
  forall vs (a b c d : @CVTerm o vs),
    alphaeqcv _ a b
    -> alphaeqcv _ c d
    -> alphaeqcv _ (mkcv_fun _ a c) (mkcv_fun _ b d).
Proof.
  introv aeq1 aeq2; destruct_cterms; unfold alphaeqcv in *; simpl in *.
  apply alpha_eq_mk_fun; auto.
Qed.
Hint Resolve implies_alphaeqcv_mkcv_fun : slow.

Hint Resolve alphaeqcv_refl : slow.

Lemma substc5_mkcv_natk2nat {o} :
  forall (t1 t2 t3 : @CTerm o) x v w z a,
    alphaeqcv
      _
      (substc5 x t1 v t2 w t3 z (mkcv_natk2nat _ a))
      (mkcv_natk2nat _ (substc5 x t1 v t2 w t3 z a)).
Proof.
  introv; unfold mkcv_natk2nat.
  eapply alphaeqcv_trans;[apply substc5_mkcv_fun|].
  autorewrite with slow; eauto 3 with slow.
Qed.

Lemma alphaeq_mk_equality {o} :
  forall (a1 a2 b1 b2 c1 c2 : @NTerm o),
    alphaeq a1 a2
    -> alphaeq b1 b2
    -> alphaeq c1 c2
    -> alphaeq (mk_equality a1 b1 c1) (mk_equality a2 b2 c2).
Proof.
  introv aeq1 aeq2 aeq3.
  constructor; simpl; auto.
  introv j.
  apply alphaeqbt_eq.
  repeat (destruct n; tcsp; try omega); unfold selectbt; simpl;
    apply alphaeqbt_nilv2; apply alphaeq_eq; auto.
Qed.
Hint Resolve alphaeq_mk_equality : slow.

Lemma alpha_eq_mk_equality {o} :
  forall (a1 a2 b1 b2 c1 c2 : @NTerm o),
    alpha_eq a1 a2
    -> alpha_eq b1 b2
    -> alpha_eq c1 c2
    -> alpha_eq (mk_equality a1 b1 c1) (mk_equality a2 b2 c2).
Proof.
  introv aeq1 aeq2 aeq3.
  allrw <- @alphaeq_eq; eauto 3 with slow.
Qed.
Hint Resolve alpha_eq_mk_equality : slow.

Lemma implies_alphaeqcv_mkcv_equality {o} :
  forall vs (a1 a2 b1 b2 c1 c2 : @CVTerm o vs),
    alphaeqcv _ a1 a2
    -> alphaeqcv _ b1 b2
    -> alphaeqcv _ c1 c2
    -> alphaeqcv _ (mkcv_equality _ a1 b1 c1) (mkcv_equality _ a2 b2 c2).
Proof.
  introv aeq1 aeq2 eqa3; destruct_cterms; unfold alphaeqcv in *; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve implies_alphaeqcv_mkcv_equality : slow.

Lemma implies_alphaeqc_mkc_equality {o} :
  forall (a1 a2 b1 b2 c1 c2 : @CTerm o),
    alphaeqc a1 a2
    -> alphaeqc b1 b2
    -> alphaeqc c1 c2
    -> alphaeqc (mkc_equality a1 b1 c1) (mkc_equality a2 b2 c2).
Proof.
  introv aeq1 aeq2 eqa3; destruct_cterms; unfold alphaeqc in *; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve implies_alphaeqc_mkc_equality : slow.

Lemma substc5_var1 {o} :
  forall (t1 t2 t3 : @CTerm o) x u v w,
    w <> u
    -> v <> u
    -> substc5 x t1 u t2 v t3 w (mk_cv_app_r [v,w] [x,u] (mk_cv_app_l [x] [u] (mkc_var u)))
       = mk_cv _ t1.
Proof.
  introv d1 d2; destruct_cterms; apply cvterm_eq; simpl.
  unflsubst; simpl;repeat (apply cl_sub_cons; dands; eauto 3 with slow).
  autorewrite with slow; boolvar; tcsp.
Qed.

Lemma equality_in_mkc_csprop_implies_tequality {o} :
  forall lib (a b c d : @CTerm o) i,
    equality lib a b (mkc_csprop i)
    -> equality lib c d (mkc_csname 0)
    -> tequality lib (mkc_apply a c) (mkc_apply b d).
Proof.
  introv equp equc.
  unfold mkc_csprop in equp.
  apply equality_in_fun in equp; repnd.
  eapply equality_in_uni.
  apply equp; eauto 3 with slow.
Qed.

Lemma equality_in_mkc_csprop_implies_tequality_cs {o} :
  forall name lib (a b : @CTerm o) i,
    compatible_choice_sequence_name 0 name
    -> equality lib a b (mkc_csprop i)
    -> tequality
         lib
         (mkc_apply a (mkc_choice_seq name))
         (mkc_apply b (mkc_choice_seq name)).
Proof.
  introv comp equ.
  eapply equality_in_mkc_csprop_implies_tequality; eauto; eauto 3 with slow.
  apply equality_in_csname_iff.
  exists (trivial_bar lib); introv br ext; simpl in *.
  exists name; dands; spcast; eauto 3 with slow.
Qed.

Lemma tequality_preserves_member {o} :
  forall lib (a A B : @CTerm o),
    tequality lib A B
    -> member lib a A
    -> member lib a B.
Proof.
  introv teq mem; eapply tequality_preserving_equality in mem; eauto.
Qed.

Ltac rev_assert T h :=
    match goal with
    | [ |- ?C ] =>
      assert (T -> C) as h;[introv h|apply h;clear h]
    end.

Lemma equality_in_mkc_csprop_preserves_tequality {o} :
  forall lib (a b c d : @CTerm o) i,
    equality lib a b (mkc_csprop i)
    -> equality lib c d (mkc_csname 0)
    -> tequality lib (mkc_apply a c) (mkc_apply a d)
    -> tequality lib (mkc_apply b c) (mkc_apply b d).
Proof.
  introv equp equc teq.
  unfold mkc_csprop in equp.
  apply equality_in_fun in equp; repnd.

  dup equc as equc'.

  apply equp in equc; eauto 3 with slow.
  apply equality_in_uni in equc.
  eapply tequality_trans;[|eauto].

  apply equality_refl in equc'.
  apply equp in equc'; eauto 3 with slow.
  apply equality_in_uni in equc'.
  apply tequality_sym; auto.
Qed.
Hint Resolve equality_in_mkc_csprop_preserves_tequality : slow.

Lemma equality_in_mkc_csprop_preserves_type {o} :
  forall lib (a b c d : @CTerm o) i,
    equality lib a b (mkc_csprop i)
    -> equality lib c d (mkc_csname 0)
    -> type lib (mkc_apply a c)
    -> type lib (mkc_apply b c).
Proof.
  introv equp equc teq.
  eapply equality_in_mkc_csprop_preserves_tequality;eauto;eauto 3 with slow.
  apply equality_refl in equc; auto.
Qed.
Hint Resolve equality_in_mkc_csprop_preserves_type : slow.

Lemma computes_to_valc_apply {o} :
  forall lib (f : @CTerm o) v a w,
    computes_to_valc lib f v
    -> computes_to_valc lib (mkc_apply f a) w
    -> computes_to_valc lib (mkc_apply v a) w.
Proof.
  introv compf compa.
  destruct_cterms; unfold computes_to_valc in *; simpl in *.
  unfold computes_to_value in *; repnd; dands; auto.
  assert (reduces_to lib (mk_apply x2 x0) (mk_apply x1 x0)) as r.
  { apply reduces_to_prinarg; auto. }
  eapply reduces_to_value_eq in r;[|split;[exact compa0|];auto];[].
  destruct r; auto.
Qed.

(* renames fst to snd *)
Definition cs_ren : Type := choice_sequence_name * choice_sequence_name.

Definition ren_cs (r : cs_ren) (n : choice_sequence_name) : choice_sequence_name :=
  let (n1,n2) := r in
  if choice_sequence_name_deq n n1 then n2
  else n.

Definition ren_cs_can {o} (r : cs_ren) (can : @CanonicalOp o) : CanonicalOp :=
  match can with
  | Ncseq name => Ncseq (ren_cs r name)
  | _ => can
  end.

Definition ren_cs_op {o} (r : cs_ren) (op : @Opid o) : Opid :=
  match op with
  | Can can => Can (ren_cs_can r can)
  | _ => op
  end.

Fixpoint ren_cs_term {o} (r : cs_ren) (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => vterm v
  | oterm op bs => oterm (ren_cs_op r op) (map (ren_cs_bterm r) bs)
  end
with ren_cs_bterm {o} (r : cs_ren) (bt : @BTerm o) : BTerm :=
       match bt with
       | bterm vs t => bterm vs (ren_cs_term r t)
       end.

Lemma free_vars_ren_cs_term {o} :
  forall (r : cs_ren) (t : @NTerm o),
    free_vars (ren_cs_term r t) = free_vars t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  induction bs; simpl; auto.
  rewrite IHbs; clear IHbs; simpl in *; tcsp;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
Defined.
Hint Rewrite @free_vars_ren_cs_term : slow.

Lemma closed_rename_term {o} :
  forall (r : cs_ren) (t : @NTerm o),
    closed t
    -> closed (ren_cs_term r t).
Proof.
  introv cl.
  unfold closed in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve closed_rename_term : slow.

Lemma OpBindings_ren_cs_op {o} :
  forall r (op : @Opid o),
    OpBindings (ren_cs_op r op) = OpBindings op.
Proof.
  destruct op as [can| | |]; simpl; tcsp.
  destruct can; simpl; auto.
Qed.
Hint Rewrite @OpBindings_ren_cs_op : slow.

Lemma implies_wf_term_ren_cs_term {o} :
  forall (r : cs_ren) (t : @NTerm o),
    wf_term t
    -> wf_term (ren_cs_term r t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv wf; simpl; tcsp.

  - Case "oterm".
    allrw @wf_oterm_iff.
    allrw map_map; unfold compose.
    autorewrite with slow.
    repnd; dands; auto.

    + rewrite <- wf0.
      apply eq_maps; introv i.
      destruct x; unfold num_bvars; simpl; auto.

    + introv i.
      allrw in_map_iff; exrepnd; subst.
      destruct a; simpl in *.
      apply wf_bterm_iff.
      eapply ind; eauto.
      apply wf in i1.
      allrw @wf_bterm_iff; tcsp.
Qed.
Hint Resolve implies_wf_term_ren_cs_term : slow.

Lemma implies_isprog_ren_cs_term {o} :
  forall r {t : @NTerm o},
    isprog t
    -> isprog (ren_cs_term r t).
Proof.
  introv isp.
  allrw @isprog_eq.
  destruct isp.
  split; dands; allrw @nt_wf_eq; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_ren_cs_term : slow.

Definition ren_cs_cterm {o} r (ct : @CTerm o) : CTerm :=
  let (t,isp) := ct in
  mk_ct (ren_cs_term r t) (implies_isprog_ren_cs_term r isp).

Fixpoint ren_cs_sub {o} r (sub : @Sub o) :=
  match sub with
  | [] => []
  | (v,t) :: sub => (v, ren_cs_term r t) :: ren_cs_sub r sub
  end.

Lemma sub_find_ren_cs_sub {o} :
  forall r (sub : @Sub o) v,
    sub_find (ren_cs_sub r sub) v
    = match sub_find sub v with
      | Some t => Some (ren_cs_term r t)
      | None => None
      end.
Proof.
  induction sub; introv; simpl; auto; repnd; simpl; boolvar; auto.
Qed.

Lemma sub_filter_ren_cs_sub {o} :
  forall r (sub : @Sub o) l,
    sub_filter (ren_cs_sub r sub) l
    = ren_cs_sub r (sub_filter sub l).
Proof.
  induction sub; introv; simpl; auto; repnd; simpl; boolvar; auto.
  rewrite IHsub; simpl; auto.
Qed.

Lemma lsubst_aux_ren_cs_term {o} :
  forall r (t : @NTerm o) sub,
    lsubst_aux (ren_cs_term r t) (ren_cs_sub r sub)
    = ren_cs_term r (lsubst_aux t sub).
Proof.
  nterm_ind t as [v|t op ind] Case; introv; simpl; auto.

  { Case "vterm".
    rewrite sub_find_ren_cs_sub.
    destruct (sub_find sub v); auto. }

  Case "oterm".
  f_equal.
  allrw map_map; unfold compose; simpl.
  apply eq_maps; introv i.
  destruct x; simpl; f_equal.
  rewrite sub_filter_ren_cs_sub.
  erewrite ind; eauto.
Qed.

Lemma bound_vars_ren_cs_term {o} :
  forall (r : cs_ren) (t : @NTerm o),
    bound_vars (ren_cs_term r t) = bound_vars t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  induction bs; simpl; auto.
  rewrite IHbs; clear IHbs; simpl in *; tcsp;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
Defined.
Hint Rewrite @bound_vars_ren_cs_term : slow.

Lemma all_vars_ren_cs_term {o} :
  forall (r : cs_ren) (t : @NTerm o),
    all_vars (ren_cs_term r t) = all_vars t.
Proof.
  introv; unfold all_vars; autorewrite with slow; auto.
Defined.
Hint Rewrite @all_vars_ren_cs_term : slow.

Lemma flat_map_free_vars_range_ren_cs_sub {o} :
  forall r (sub : @Sub o),
    flat_map free_vars (range (ren_cs_sub r sub))
    = flat_map free_vars (range sub).
Proof.
  induction sub; introv; simpl; auto; repnd; simpl.
  rewrite IHsub; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @flat_map_free_vars_range_ren_cs_sub : slow.

Lemma ren_cs_sub_if_allvars_sub {o} :
  forall r (sub : @Sub o),
    allvars_sub sub
    -> ren_cs_sub r sub = sub.
Proof.
  induction sub; introv allvs; simpl in *; auto; repnd; simpl in *.
  apply allvars_sub_cons in allvs; repnd.
  rewrite IHsub; auto.
  apply isvariable_implies in allvs0; exrepnd; subst; simpl; auto.
Qed.

Lemma lsubst_aux_ren_cs_term_if_allvars_sub {o} :
  forall r (t : @NTerm o) sub,
    allvars_sub sub
    -> lsubst_aux (ren_cs_term r t) sub
       = ren_cs_term r (lsubst_aux t sub).
Proof.
  introv allvs.
  rewrite <- lsubst_aux_ren_cs_term.
  rewrite ren_cs_sub_if_allvars_sub; auto.
Qed.

Lemma change_bvars_alpha_ren_cs_term {o} :
  forall l r (t : @NTerm o),
    change_bvars_alpha l (ren_cs_term r t)
    = ren_cs_term r (change_bvars_alpha l t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; auto.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i; destruct x; simpl.
  erewrite ind;eauto; autorewrite with slow.
  f_equal.
  rewrite lsubst_aux_ren_cs_term_if_allvars_sub; eauto 3 with slow.
Qed.

Lemma lsubst_ren_cs_term {o} :
  forall r (t : @NTerm o) sub,
    lsubst (ren_cs_term r t) (ren_cs_sub r sub)
    = ren_cs_term r (lsubst t sub).
Proof.
  introv.
  unfold lsubst; autorewrite with slow.
  destruct (dec_disjointv (bound_vars t) (flat_map free_vars (range sub)));
    try rewrite lsubst_aux_ren_cs_term; auto.
  rewrite change_bvars_alpha_ren_cs_term.
  rewrite lsubst_aux_ren_cs_term; auto.
Qed.

Lemma subst_ren_cs_term {o} :
  forall r (t : @NTerm o) v u,
    subst (ren_cs_term r t) v (ren_cs_term r u)
    = ren_cs_term r (subst t v u).
Proof.
  introv.
  unfold subst; rewrite <- lsubst_ren_cs_term; simpl; auto.
Qed.

Lemma computes_to_valc_nat_implies_find_cs_value_at {o} :
  forall (lib : @library o) name m k,
    computes_to_valc lib (mkc_apply (mkc_choice_seq name) (mkc_nat m)) (mkc_nat k)
    -> {c : CTerm
        & find_cs_value_at lib name m = Some c
        # computes_to_valc lib c (mkc_nat k)}.
Proof.
  introv comp.
  unfold computes_to_valc, computes_to_value in comp; simpl in *; repnd.
  eapply reduces_to_split2 in comp0; repndors; ginv; exrepnd.
  csunf comp0; simpl in *; ginv.
  eapply reduces_to_split2 in comp1; repndors; ginv; exrepnd.
  csunf comp1; simpl in *.
  dcwf h; simpl in *; boolvar; try omega.
  autorewrite with slow in *.
  remember (find_cs_value_at lib name m) as xx; symmetry in Heqxx; destruct xx; ginv.
  exists c; dands; auto.
  split; simpl; auto.
Qed.

Lemma computes_to_valc_nat_implies_find_cs_value_at_if_safe {o} :
  forall (lib : @library o) name m k,
    safe_library lib
    -> compatible_choice_sequence_name 0 name
    -> computes_to_valc lib (mkc_apply (mkc_choice_seq name) (mkc_nat m)) (mkc_nat k)
    -> find_cs_value_at lib name m = Some (mkc_nat k).
Proof.
  introv safe compat comp.
  unfold computes_to_valc, computes_to_value in comp; simpl in *; repnd.
  eapply reduces_to_split2 in comp0; repndors; ginv; exrepnd.
  csunf comp0; simpl in *; ginv.
  eapply reduces_to_split2 in comp1; repndors; ginv; exrepnd.
  csunf comp1; simpl in *.
  dcwf h; simpl in *; boolvar; try omega.
  autorewrite with slow in *.
  remember (find_cs_value_at lib name m) as xx; symmetry in Heqxx; destruct xx; ginv.
  unfold find_cs_value_at in Heqxx.
  remember (find_cs lib name) as w; symmetry in Heqw.
  destruct w; ginv.

  pose proof (safe (lib_cs name c0)) as safe; simpl in *.
  autodimp safe hyp; eauto 3 with slow.
  unfold safe_choice_sequence_entry in safe.
  destruct c0 as [vals restr]; simpl in *; repnd.
  unfold correct_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  unfold compatible_choice_sequence_name in *.
  unfold compatible_cs_kind in *; simpl in *.
  remember (csn_kind name) as ckn; symmetry in Heqckn.
  rewrite find_value_of_cs_at_is_select in Heqxx.

  destruct ckn; subst; simpl in *; auto; GC; ginv.

  {
    unfold is_nat_restriction in *.
    destruct restr; simpl in *; tcsp; repnd.
    apply safe in Heqxx.
    apply safe0 in Heqxx.
    unfold is_nat in Heqxx; exrepnd; subst; simpl in *.
    apply reduces_to_if_value in comp0; eauto 3 with slow.
    apply mk_nat_eq_implies in comp0; subst; auto.
  }

  {
    unfold is_nat_seq_restriction in *.
    destruct restr; simpl in *; tcsp; repnd.
    apply safe in Heqxx.

    destruct (lt_dec m (length l0)) as [w|w].

    {
      apply safe3 in Heqxx; auto.
      unfold cterm_is_nth in Heqxx; exrepnd; subst; simpl in *.
      apply reduces_to_if_value in comp0; eauto 3 with slow.
      apply mk_nat_eq_implies in comp0; subst; auto.
    }

    {
      apply safe0 in Heqxx; auto; try omega.
      unfold is_nat in Heqxx; exrepnd; subst; simpl in *.
      apply reduces_to_if_value in comp0; eauto 3 with slow.
      apply mk_nat_eq_implies in comp0; subst; auto.
    }
  }
Qed.

Lemma find_cs_value_at_implies_lt_cs_size {o} :
  forall (lib : @library o) name n v,
    find_cs_value_at lib name n = Some v
    -> n < cs_size lib name.
Proof.
  introv h.
  unfold find_cs_value_at in h.
  unfold cs_size.
  remember (find_cs lib name) as fcs.
  symmetry in Heqfcs.
  destruct fcs; ginv.
  rewrite find_value_of_cs_at_is_select in h; eauto 3 with slow.
Qed.
Hint Resolve find_cs_value_at_implies_lt_cs_size : slow.

Hint Resolve Nat.le_max_l : num.
Hint Resolve Nat.le_max_r : num.
Hint Resolve Nat.le_refl : num.
Hint Resolve le_trans : num.

Lemma cs_size_le_lib_size {o} :
  forall name (lib : @library o),
    cs_size lib name <= lib_size lib.
Proof.
  introv.
  unfold cs_size.
  induction lib; simpl; auto.
  destruct a; simpl; boolvar; subst; eauto 3 with slow num.
Qed.
Hint Resolve cs_size_le_lib_size : slow.

Lemma find_cs_value_at_implies_lt_lib_size {o} :
  forall (lib : @library o) name n v,
    find_cs_value_at lib name n = Some v
    -> n < lib_size lib.
Proof.
  introv h.
  apply find_cs_value_at_implies_lt_cs_size in h.
  pose proof (cs_size_le_lib_size name lib) as q; omega.
Qed.
Hint Resolve find_cs_value_at_implies_lt_lib_size : slow.

Lemma eapply_wf_def_implies_eapply_wf_ren_cs_term_true {o} :
  forall r (t : @NTerm o),
    eapply_wf_def t
    -> eapply_wf (ren_cs_term r t) = true.
Proof.
  introv h.
  apply eapply_wf_def_implies_true in h.
  destruct t as [v|op bs]; simpl in *; ginv;[].
  destruct op; simpl in *; ginv;[].
  destruct c; simpl in *; ginv;[|].

  { destruct bs; simpl in *; ginv.
    destruct b.
    repeat (destruct l; simpl in *; ginv).
    destruct bs; simpl in *; ginv. }

  { destruct bs; simpl in *; ginv. }
Qed.

Lemma implies_eapply_wf_def_ren_cs_term {o} :
  forall r (t : @NTerm o),
    eapply_wf_def t
    -> eapply_wf_def (ren_cs_term r t).
Proof.
  introv h.
  apply (eapply_wf_def_implies_eapply_wf_ren_cs_term_true r) in h.
  apply eapply_wf_true; auto.
Qed.
Hint Resolve implies_eapply_wf_def_ren_cs_term : slow.

Definition up_to_name {o} (name : choice_sequence_name) (t : @NTerm o) :=
  subset (get_defs t) [defk_cs name].

Lemma up_to_name_fst {o} :
  forall name (op : @Opid o) l t bs,
    up_to_name name (oterm op (bterm l t :: bs))
    -> up_to_name name t.
Proof.
  introv h.
  unfold up_to_name in *; simpl in *; introv i; simpl in *.
  apply h; allrw in_app_iff; tcsp.
Qed.
Hint Resolve up_to_name_fst : slow.

Lemma up_to_name_snd {o} :
  forall name (op : @Opid o) l1 t1 l2 t2 bs,
    up_to_name name (oterm op (bterm l1 t1 :: bterm l2 t2 :: bs))
    -> up_to_name name t2.
Proof.
  introv h.
  unfold up_to_name in *; simpl in *; introv i; simpl in *.
  apply h; allrw in_app_iff; tcsp.
Qed.
Hint Resolve up_to_name_snd : slow.

Lemma implies_compute_step_eapply_success_if_isnoncan_like {o} :
  forall (lib : @library o) arg1 arg2 l t x ncr,
    isnoncan_like arg2
    -> eapply_wf_def arg1
    -> compute_step_eapply lib (nobnd arg2 :: l) t (csuccess x) arg1 ncr
       = csuccess (oterm (NCan ncr) (nobnd arg1 :: nobnd x :: l)).
Proof.
  introv isn wf.
  dcwf h; tcsp;[].

  unfold isnoncan_like in *; repndors.

  { unfold isnoncan in *; destruct arg2 as [v|op bs]; simpl in *; tcsp.
    destruct op; simpl in *; tcsp. }

  { unfold isabs in *; destruct arg2 as [v|op bs]; simpl in *; tcsp.
    destruct op; simpl in *; tcsp. }
Qed.

Lemma implies_isnoncan_like_ren_cs_term {o} :
  forall r (t : @NTerm o),
    isnoncan_like t
    -> isnoncan_like (ren_cs_term r t).
Proof.
  introv isn.
  unfold isnoncan_like in *.
  repndors;[left|right].

  { apply isnoncan_implies in isn; exrepnd; subst; simpl in *; auto. }

  { apply isabs_implies in isn; exrepnd; subst; simpl in *; auto. }
Qed.
Hint Resolve implies_isnoncan_like_ren_cs_term : slow.

Lemma co_wf_def_implies_co_wf_ren_cs_term_true {o} :
  forall r cop can (l : list (@BTerm o)),
    co_wf_def cop can l
    -> co_wf cop (ren_cs_can r can) (map (ren_cs_bterm r) l) = true.
Proof.
  introv h.
  apply co_wf_def_implies_true in h.
  unfold co_wf in *.
  destruct can; simpl in *; ginv;
    destruct l; simpl in *; ginv;
      destruct cop; simpl in *; ginv.
Qed.

Lemma implies_co_wf_def_ren_cs_term {o} :
  forall r cop can (l : list (@BTerm o)),
    co_wf_def cop can l
    -> co_wf_def cop (ren_cs_can r can) (map (ren_cs_bterm r) l).
Proof.
  introv h.
  apply (co_wf_def_implies_co_wf_ren_cs_term_true r) in h.
  apply co_wf_true; auto.
Qed.
Hint Resolve implies_co_wf_def_ren_cs_term : slow.

Definition ren_cs_pk {o} r (pk : @param_kind o) : param_kind :=
  match pk with
  | PKs s => PKs s
  | PKa a => PKa a
  | PKi i => PKi i
  | PKc c => PKc (ren_cs r c)
  end.

Lemma ren_cs_can_pk2can {o} :
  forall r (pk : @param_kind o),
    ren_cs_can r (pk2can pk) = pk2can (ren_cs_pk r pk).
Proof.
  destruct pk; simpl; auto.
Qed.

Hint Rewrite @get_param_from_cop_pk2can : slow.

Lemma compute_step_preserves_ren_cs {o} :
  forall lib lib' (t u : @NTerm o) name1 name2,
    name1 <> name2
    -> lib_extends lib' lib
    -> up_to_name name1 t
    -> (forall m : nat,
           m < cs_size lib name1
           ->
           {k : nat
            & find_cs_value_at lib' name1 m = Some (mkc_nat k)
            # find_cs_value_at lib' name2 m = Some (mkc_nat k)})
    -> compute_step lib t = csuccess u
    -> compute_step
         (lib' (* extend [lib] with [name2] *))
         (ren_cs_term (name1,name2) t)
       = csuccess (ren_cs_term (name1,name2) u).
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv dname ext upto imp comp; tcsp.

  { Case "vterm".
    csunf comp; simpl in *; ginv. }

  Case "oterm".
  dopid op as [can|ncan|exc|abs] SCase.

  { SCase "Can".
    csunf comp; simpl in *; ginv.
    csunf; simpl; auto. }

  { SCase "NCan".

    destruct bs; try (complete (allsimpl; ginv)).
    destruct b as [l t]; try (complete (allsimpl; ginv)).
    destruct l; try (complete (allsimpl; ginv));[|].

    { destruct t as [x|op bts]; try (complete (allsimpl; ginv));[].

      dopid op as [can2|ncan2|exc2|abs2] SSCase.

      { SSCase "Can".

        dopid_noncan ncan SSSCase.

        { SSSCase "NApply".
          csunf comp; simpl in *.
          apply compute_step_apply_success in comp; repndors; exrepnd; subst; simpl in *;
            csunf; simpl; auto.
          unfold apply_bterm; simpl.
          rewrite <- subst_ren_cs_term; simpl; auto. }

        { SSSCase "NEApply".
          csunf comp; simpl in *.
          apply compute_step_eapply_success in comp; repndors; exrepnd; subst; simpl in *;
            csunf; simpl; auto.
          repndors; exrepnd; subst; simpl;
            [| |].

          { apply compute_step_eapply2_success in comp1; repnd; subst; simpl in *.
            repndors; exrepnd; subst; unfold mk_lam, mk_choice_seq in *; ginv; simpl in *; GC;
              [|].

            { apply iscan_implies in comp0; exrepnd; subst; simpl in *; dcwf h.
              unfold compute_step_eapply2; unfold apply_bterm; simpl.
              rewrite <- lsubst_ren_cs_term; simpl; auto. }

            { unfold up_to_name in upto; simpl in upto.
              apply singleton_subset in upto; simpl in upto; repndors; tcsp; ginv.
              pose proof (imp n) as imp; autodimp imp hyp; eauto 3 with slow;[].
              exrepnd.
              eapply lib_extends_preserves_find_cs_value_at in comp5;[|eauto].
              rewrite imp1 in comp5; inversion comp5; subst; clear comp5.
              simpl in *; fold_terms.
              boolvar; tcsp; GC;[].

              dcwf h; simpl; boolvar; subst; autorewrite with slow in *; GC; try omega;[].
              rewrite imp0; auto. }
          }

          { apply isexc_implies2 in comp0; exrepnd; subst; simpl in *.
            dcwf h; auto.
            apply (eapply_wf_def_implies_eapply_wf_ren_cs_term_true (name1,name2)) in comp2.
            simpl in *; rewrite comp2 in Heqh; ginv. }

          { fold_terms.
            pose proof (ind arg2 arg2 []) as ind.
            repeat (autodimp ind hyp); eauto 3 with slow;[].
            pose proof (ind x name1 name2) as ind.
            repeat (autodimp ind hyp); eauto 3 with slow;[].
            rewrite ind.
            rewrite implies_compute_step_eapply_success_if_isnoncan_like; auto; eauto 3 with slow.
            apply (implies_eapply_wf_def_ren_cs_term (name1,name2)) in comp2; simpl in *; auto. }
        }

        { SSSCase "NFix".
          csunf comp; simpl in *.
          apply compute_step_fix_success in comp; repnd; subst; simpl in *.
          csunf; simpl; auto. }

        { SSSCase "NSpread".
          csunf comp; simpl in *.
          apply compute_step_spread_success in comp; exrepnd; subst; simpl in *.
          csunf; simpl; auto.
          unfold apply_bterm; simpl.
          rewrite <- lsubst_ren_cs_term; simpl; auto. }

        { SSSCase "NDsup".
          csunf comp; simpl in *.
          apply compute_step_dsup_success in comp; exrepnd; subst; simpl in *.
          csunf; simpl; auto.
          unfold apply_bterm; simpl.
          rewrite <- lsubst_ren_cs_term; simpl; auto. }

        { SSSCase "NDecide".
          csunf comp; simpl in *.
          apply compute_step_decide_success in comp; exrepnd; subst; simpl in *.
          repndors; exrepnd; subst; simpl in *; csunf; simpl; auto;
            unfold apply_bterm; simpl;
              rewrite <- subst_ren_cs_term; simpl; auto. }

        { SSSCase "NCbv".
          csunf comp; simpl in *.
          apply compute_step_cbv_success in comp; exrepnd; subst; simpl in *.
          repndors; exrepnd; subst; simpl in *; csunf; simpl; auto.
          unfold apply_bterm; simpl.
          rewrite <- subst_ren_cs_term; simpl; auto. }

        { SSSCase "NSleep".
          csunf comp; simpl in *.
          apply compute_step_sleep_success in comp; exrepnd; subst; simpl in *.
          repndors; exrepnd; subst; simpl in *; csunf; simpl; auto. }

        { SSSCase "NTUni".
          csunf comp; simpl in *.
          apply compute_step_tuni_success in comp; exrepnd; subst; simpl in *.
          repndors; exrepnd; subst; simpl in *; csunf; simpl; auto.
          unfold compute_step_tuni; simpl; boolvar; try omega; autorewrite with slow; auto. }

        { SSSCase "NMinus".
          csunf comp; simpl in *.
          apply compute_step_minus_success in comp; exrepnd; subst; simpl in *.
          repndors; exrepnd; subst; simpl in *; csunf; simpl; auto. }

        { SSSCase "NFresh".
          csunf comp; simpl in *; ginv. }

        { SSSCase "NTryCatch".
          csunf comp; simpl in *.
          apply compute_step_try_success in comp; exrepnd; subst; simpl in *.
          repndors; exrepnd; subst; simpl in *; csunf; simpl; auto. }

        { SSSCase "NParallel".
          csunf comp; simpl in *.
          apply compute_step_parallel_success in comp; exrepnd; subst; simpl in *.
          repndors; exrepnd; subst; simpl in *; csunf; simpl; auto. }

        { SSSCase "NCompSeq1".
          csunf comp; simpl in *.
          apply compute_step_comp_seq1_success in comp; exrepnd; subst; simpl in *.
          Opaque choice_sequence_name_deq.
          repndors; exrepnd; subst; csunf; simpl; auto;[|];
            [|autorewrite with slow; boolvar; try omega; auto];[].
          unfold mk_fresh_choice_nat_seq; simpl; fold_terms.
          boolvar; auto; subst; simpl in *;[].

          Print mk_comp_seq2.

          (* comp_seq1 and comp_seq2 terms need to contain the default choice sequence name
               as a parameter? *)

          admit. }

        { SSSCase "NCompSeq2".
          csunf comp; simpl in *.
          apply compute_step_comp_seq2_success in comp; exrepnd; subst; simpl in *.
          Opaque choice_sequence_name_deq.
          repndors; exrepnd; subst; csunf; simpl; auto;[|];
            [|autorewrite with slow; boolvar; try omega; auto];[].
          boolvar; auto; subst; simpl in *; auto; tcsp; ginv; try omega;
            autorewrite with slow; try reflexivity;[].

          (* comp_seq1 and comp_seq2 terms need to contain the default choice sequence name *)

          admit. }

        { SSSCase "NCompOp".
          apply compute_step_ncompop_can1_success in comp; repnd.
          repndors; exrepnd; subst;[| |].

          { apply compute_step_compop_success_can_can in comp1.
            exrepnd; subst; ginv.
            repndors; exrepnd; subst; csunf; simpl; dcwf h; simpl; tcsp; ginv.

            { apply get_param_from_cop_pki in comp3.
              apply get_param_from_cop_pki in comp4.
              subst; simpl in *.
              unfold compute_step_comp; simpl; boolvar; auto. }

            { apply (co_wf_def_implies_co_wf_ren_cs_term_true (name1,name2)) in comp0; simpl in *.
              rewrite comp0 in Heqh; ginv. }

            { apply get_param_from_cop_some in comp3.
              apply get_param_from_cop_some in comp4.
              subst; simpl in *.
              unfold compute_step_comp; simpl; autorewrite with slow.
              repeat rewrite ren_cs_can_pk2can.
              autorewrite with slow; boolvar; subst; tcsp;[].
              destruct pk1, pk2; simpl in *; ginv; tcsp;[].
              boolvar; subst; ginv; tcsp;[|].
              { apply up_to_name_snd in upto.
                unfold up_to_name in *; simpl in *.
                apply singleton_subset in upto; simpl in upto; repndors; tcsp; ginv; tcsp. }
              { apply up_to_name_fst in upto.
                unfold up_to_name in *; simpl in *.
                apply singleton_subset in upto; simpl in upto; repndors; tcsp; ginv; tcsp. }
            }

            { apply (co_wf_def_implies_co_wf_ren_cs_term_true (name1,name2)) in comp0; simpl in *.
              rewrite comp0 in Heqh; ginv. }
          }

          { admit. }

          { admit. }
        }

        { SSSCase "NArithOp".

          admit.
        }

        { SSSCase "NCanTest".

          admit.
        }
      }

      { SSCase "NCan".
        csunf comp; simpl in *.
        remember (compute_step lib (oterm (NCan ncan2) bts)) as c.
        symmetry in Heqc; destruct c; ginv;[].
        pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as ind.
        repeat (autodimp ind hyp); eauto 3 with slow;[].
        pose proof (ind n name1 name2) as ind.
        repeat (autodimp ind hyp); eauto 3 with slow;[].
        csunf; simpl in *.
        rewrite ind; simpl; auto.
      }

      { SSCase "Exc".
        csunf comp; simpl in *.
        apply compute_step_catch_success in comp.
        repndors; exrepnd; subst; simpl in *.

        { csunf; simpl; auto.
          rewrite <- subst_ren_cs_term; simpl; auto. }

        { csunf; simpl.
          rewrite compute_step_catch_non_trycatch; auto. }
      }

      { SSCase "Abs".
        csunf comp; simpl in *.
        remember (compute_step lib (oterm (Abs abs2) bts)) as c.
        symmetry in Heqc; destruct c; ginv;[].
        pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as ind.
        repeat (autodimp ind hyp); eauto 3 with slow;[].
        pose proof (ind n name1 name2) as ind.
        repeat (autodimp ind hyp); eauto 3 with slow;[].
        csunf; simpl in *.
        rewrite ind; simpl; auto.
      }
    }

    { (* fresh case *)

      csunf comp.

      admit.
    }
  }

  { SCase "Exc".
    csunf comp; simpl in *; ginv; simpl; auto.
  }

  { SCase "Abs".
    csunf comp; simpl in *.
    apply compute_step_lib_success in comp; exrepnd; subst.

    admit.
  }
Abort.

Definition up_to_namec {o} (name : choice_sequence_name) (t : @CTerm o) :=
  up_to_name name (get_cterm t).

Lemma compute_to_valc_preserves_ren_cs {o} :
  forall lib lib' (t v : @CTerm o) name1 name2,
    name1 <> name2
    -> lib_extends lib' lib
    -> up_to_namec name1 t
    -> (forall m : nat,
           m < cs_size lib name1
           ->
           {k : nat
            & find_cs_value_at lib' name1 m = Some (mkc_nat k)
            # find_cs_value_at lib' name2 m = Some (mkc_nat k)})
    -> computes_to_valc lib t v
    -> computes_to_valc
         (lib' (* extend [lib] with [name2] *))
         (ren_cs_cterm (name1,name2) t)
         (ren_cs_cterm (name1,name2) v).
Proof.
Abort.

Lemma hasvaluec_implies_computes_to_valc {o} :
  forall lib (t : @CTerm o),
    hasvaluec lib t
    -> {v : CTerm & computes_to_valc lib t v}.
Proof.
  introv h.
  destruct_cterms.
  unfold hasvaluec, hasvalue in h; simpl in *; exrepnd.
  destruct h0 as [comp isv].
  inversion isv as [? isp isc]; subst.
  exists (mk_cterm t' isp); unfold computes_to_valc; simpl.
  split; auto.
Qed.

(* swaps fst and snd *)
Definition cs_swap : Type := choice_sequence_name * choice_sequence_name.

Definition swap_cs (r : cs_swap) (n : choice_sequence_name) : choice_sequence_name :=
  let (n1,n2) := r in
  if choice_sequence_name_deq n n1 then n2
  else if choice_sequence_name_deq n n2 then n1
       else n.

Definition swap_cs_can {o} (r : cs_swap) (can : @CanonicalOp o) : CanonicalOp :=
  match can with
  | Ncseq name => Ncseq (swap_cs r name)
  | _ => can
  end.

Definition swap_cs_op {o} (r : cs_swap) (op : @Opid o) : Opid :=
  match op with
  | Can can => Can (swap_cs_can r can)
  | _ => op
  end.

Fixpoint swap_cs_term {o} (r : cs_swap) (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => vterm v
  | oterm op bs => oterm (swap_cs_op r op) (map (swap_cs_bterm r) bs)
  end
with swap_cs_bterm {o} (r : cs_swap) (bt : @BTerm o) : BTerm :=
       match bt with
       | bterm vs t => bterm vs (swap_cs_term r t)
       end.

Lemma free_vars_swap_cs_term {o} :
  forall (r : cs_swap) (t : @NTerm o),
    free_vars (swap_cs_term r t) = free_vars t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  induction bs; simpl; auto.
  rewrite IHbs; clear IHbs; simpl in *; tcsp;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
Defined.
Hint Rewrite @free_vars_swap_cs_term : slow.

Lemma closed_swap_cs_term {o} :
  forall (r : cs_ren) (t : @NTerm o),
    closed t
    -> closed (swap_cs_term r t).
Proof.
  introv cl.
  unfold closed in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve closed_swap_cs_term : slow.

Lemma OpBindings_swap_cs_op {o} :
  forall r (op : @Opid o),
    OpBindings (swap_cs_op r op) = OpBindings op.
Proof.
  destruct op as [can| | |]; simpl; tcsp.
  destruct can; simpl; auto.
Qed.
Hint Rewrite @OpBindings_swap_cs_op : slow.

Lemma implies_wf_term_swap_cs_term {o} :
  forall (r : cs_ren) (t : @NTerm o),
    wf_term t
    -> wf_term (swap_cs_term r t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv wf; simpl; tcsp.

  - Case "oterm".
    allrw @wf_oterm_iff.
    allrw map_map; unfold compose.
    autorewrite with slow.
    repnd; dands; auto.

    + rewrite <- wf0.
      apply eq_maps; introv i.
      destruct x; unfold num_bvars; simpl; auto.

    + introv i.
      allrw in_map_iff; exrepnd; subst.
      destruct a; simpl in *.
      apply wf_bterm_iff.
      eapply ind; eauto.
      apply wf in i1.
      allrw @wf_bterm_iff; tcsp.
Qed.
Hint Resolve implies_wf_term_swap_cs_term : slow.

Lemma implies_isprog_swap_cs_term {o} :
  forall r {t : @NTerm o},
    isprog t
    -> isprog (swap_cs_term r t).
Proof.
  introv isp.
  allrw @isprog_eq.
  destruct isp.
  split; dands; allrw @nt_wf_eq; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_swap_cs_term : slow.

Definition swap_cs_cterm {o} r (ct : @CTerm o) : CTerm :=
  let (t,isp) := ct in
  mk_ct (swap_cs_term r t) (implies_isprog_swap_cs_term r isp).

Fixpoint swap_cs_sub {o} r (sub : @Sub o) :=
  match sub with
  | [] => []
  | (v,t) :: sub => (v, swap_cs_term r t) :: swap_cs_sub r sub
  end.

Lemma sub_find_swap_cs_sub {o} :
  forall r (sub : @Sub o) v,
    sub_find (swap_cs_sub r sub) v
    = match sub_find sub v with
      | Some t => Some (swap_cs_term r t)
      | None => None
      end.
Proof.
  induction sub; introv; simpl; auto; repnd; simpl; boolvar; auto.
Qed.

Lemma sub_filter_swap_cs_sub {o} :
  forall r (sub : @Sub o) l,
    sub_filter (swap_cs_sub r sub) l
    = swap_cs_sub r (sub_filter sub l).
Proof.
  induction sub; introv; simpl; auto; repnd; simpl; boolvar; auto.
  rewrite IHsub; simpl; auto.
Qed.

Lemma lsubst_aux_swap_cs_term {o} :
  forall r (t : @NTerm o) sub,
    lsubst_aux (swap_cs_term r t) (swap_cs_sub r sub)
    = swap_cs_term r (lsubst_aux t sub).
Proof.
  nterm_ind t as [v|t op ind] Case; introv; simpl; auto.

  { Case "vterm".
    rewrite sub_find_swap_cs_sub.
    destruct (sub_find sub v); auto. }

  Case "oterm".
  f_equal.
  allrw map_map; unfold compose; simpl.
  apply eq_maps; introv i.
  destruct x; simpl; f_equal.
  rewrite sub_filter_swap_cs_sub.
  erewrite ind; eauto.
Qed.

Lemma bound_vars_swap_cs_term {o} :
  forall (r : cs_ren) (t : @NTerm o),
    bound_vars (swap_cs_term r t) = bound_vars t.
Proof.
  sp_nterm_ind1 t as [v|op bs ind] Case; introv; simpl; tcsp;[].
  induction bs; simpl; auto.
  rewrite IHbs; clear IHbs; simpl in *; tcsp;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
Defined.
Hint Rewrite @bound_vars_swap_cs_term : slow.

Lemma all_vars_swap_cs_term {o} :
  forall (r : cs_ren) (t : @NTerm o),
    all_vars (swap_cs_term r t) = all_vars t.
Proof.
  introv; unfold all_vars; autorewrite with slow; auto.
Defined.
Hint Rewrite @all_vars_swap_cs_term : slow.

Lemma flat_map_free_vars_range_swap_cs_sub {o} :
  forall r (sub : @Sub o),
    flat_map free_vars (range (swap_cs_sub r sub))
    = flat_map free_vars (range sub).
Proof.
  induction sub; introv; simpl; auto; repnd; simpl.
  rewrite IHsub; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @flat_map_free_vars_range_swap_cs_sub : slow.

Lemma swap_cs_sub_if_allvars_sub {o} :
  forall r (sub : @Sub o),
    allvars_sub sub
    -> swap_cs_sub r sub = sub.
Proof.
  induction sub; introv allvs; simpl in *; auto; repnd; simpl in *.
  apply allvars_sub_cons in allvs; repnd.
  rewrite IHsub; auto.
  apply isvariable_implies in allvs0; exrepnd; subst; simpl; auto.
Qed.

Lemma lsubst_aux_swap_cs_term_if_allvars_sub {o} :
  forall r (t : @NTerm o) sub,
    allvars_sub sub
    -> lsubst_aux (swap_cs_term r t) sub
       = swap_cs_term r (lsubst_aux t sub).
Proof.
  introv allvs.
  rewrite <- lsubst_aux_swap_cs_term.
  rewrite swap_cs_sub_if_allvars_sub; auto.
Qed.

Lemma change_bvars_alpha_swap_cs_term {o} :
  forall l r (t : @NTerm o),
    change_bvars_alpha l (swap_cs_term r t)
    = swap_cs_term r (change_bvars_alpha l t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; auto.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i; destruct x; simpl.
  erewrite ind;eauto; autorewrite with slow.
  f_equal.
  rewrite lsubst_aux_swap_cs_term_if_allvars_sub; eauto 3 with slow.
Qed.

Lemma swap_cs_idem :
  forall (r    : cs_swap)
         (name : choice_sequence_name),
    swap_cs r (swap_cs r name) = name.
Proof.
  destruct r; introv; simpl; boolvar; subst; tcsp.
Qed.
Hint Rewrite swap_cs_idem : slow.

Lemma swap_cs_op_idem {o} :
  forall (r  : cs_swap)
         (op : @Opid o),
    swap_cs_op r (swap_cs_op r op) = op.
Proof.
  destruct op; simpl; auto.
  destruct c; simpl; auto; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_op_idem : slow.

Lemma swap_cs_term_idem {o} :
  forall (r : cs_swap)
         (t : @NTerm o),
    swap_cs_term r (swap_cs_term r t) = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; auto.
  autorewrite with slow.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_map_l; introv i.
  destruct x; apply ind in i.
  simpl; f_equal; auto.
Qed.
Hint Rewrite @swap_cs_term_idem : slow.

Lemma swap_cs_cterm_idem {o} :
  forall (r : cs_swap)
         (t : @CTerm o),
    swap_cs_cterm r (swap_cs_cterm r t) = t.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_cterm_idem : slow.

Lemma lsubst_swap_cs_term {o} :
  forall r (t : @NTerm o) sub,
    lsubst (swap_cs_term r t) (swap_cs_sub r sub)
    = swap_cs_term r (lsubst t sub).
Proof.
  introv.
  unfold lsubst; autorewrite with slow.
  destruct (dec_disjointv (bound_vars t) (flat_map free_vars (range sub)));
    try rewrite lsubst_aux_swap_cs_term; auto.
  rewrite change_bvars_alpha_swap_cs_term.
  rewrite lsubst_aux_swap_cs_term; auto.
Qed.

Lemma subst_swap_cs_term {o} :
  forall r (t : @NTerm o) v u,
    subst (swap_cs_term r t) v (swap_cs_term r u)
    = swap_cs_term r (subst t v u).
Proof.
  introv.
  unfold subst; rewrite <- lsubst_swap_cs_term; simpl; auto.
Qed.

Lemma in_implies_select :
  forall {A} (a : A) l,
    LIn a l
    -> exists n, select n l = Some a.
Proof.
  induction l; introv i; simpl in *; tcsp.
  repndors; subst; simpl in *; tcsp.
  { exists 0; simpl; auto. }
  { apply IHl in i; exrepnd.
    exists (S n); simpl; auto. }
Qed.

Lemma swap_cs_term_nat {o} :
  forall n sw,
    @swap_cs_cterm o sw (mkc_nat n) = mkc_nat n.
Proof.
  introv; apply cterm_eq; auto.
Qed.
Hint Rewrite @swap_cs_term_nat : slow.

Lemma choice_sequence_0_implies_nat {o} :
  forall name vals (restr : @ChoiceSeqRestriction o) x,
    compatible_choice_sequence_name 0 name
    -> correct_restriction name restr
    -> choice_sequence_satisfies_restriction vals restr
    -> LIn x vals
    -> exists n, x = mkc_nat n.
Proof.
  introv comp cor sat i.
  unfold compatible_choice_sequence_name in *; simpl in *.
  unfold compatible_cs_kind in *; boolvar; tcsp; GC;[].
  destruct name as [name kind]; simpl in *.
  unfold correct_restriction in *; simpl in *.
  apply in_implies_select in i; exrepnd.
  destruct kind; simpl in *; tcsp; subst; simpl in *; GC;[|].

  { destruct restr; simpl in *; repnd; tcsp;[].
    apply sat in i0.
    apply cor in i0.
    unfold is_nat in i0; exrepnd; subst; simpl; eauto. }

  { destruct restr; simpl in *; repnd; tcsp;[].
    applydup sat in i0.
    destruct (lt_dec n (length l)) as [w|w].

    { apply cor2 in i1; auto.
      unfold cterm_is_nth in i1; exrepnd; subst; eauto. }

    { pose proof (cor n x) as z; autodimp z hyp; try omega;[].
      apply z in i1.
      unfold is_nat in *; exrepnd; subst; eauto. } }
Qed.

Lemma is_nat_restriction_implies_is_nat_seq_restriction {o} :
  forall (restr : @ChoiceSeqRestriction o),
    is_nat_restriction restr
    -> is_nat_seq_restriction [] restr.
Proof.
  introv isn.
  destruct restr; simpl in *; tcsp.
Qed.
Hint Resolve is_nat_restriction_implies_is_nat_seq_restriction : slow.

Lemma implies_same_restrictions_nat {o} :
  forall name (restr : @ChoiceSeqRestriction o),
    compatible_choice_sequence_name 0 name
    -> correct_restriction name restr
    -> exists l, is_nat_seq_restriction l restr.
Proof.
  introv comp cor.
  unfold compatible_choice_sequence_name in *; simpl in *.
  unfold compatible_cs_kind in *; simpl in *.
  destruct name as [name kind]; simpl in *.
  unfold correct_restriction in *; simpl in *.
  destruct kind; simpl in *; GC; subst; simpl in *; tcsp; eauto.
  exists ([] : list nat); eauto 3 with slow.
Qed.

Fixpoint keep_only {o} (name : choice_sequence_name) (lib : @library o) : @library o :=
  match lib with
  | [] => []
  | lib_cs name' e :: entries =>
    if choice_sequence_name_deq name name'
    then [lib_cs name' e]
    else keep_only name entries
  | entry :: entries => keep_only name entries
  end.

Lemma keep_only_equal {o} :
  forall name (lib : @library o),
    keep_only name lib
    = match find_cs lib name with
      | Some e => [lib_cs name e]
      | None => []
      end.
Proof.
  induction lib; introv; simpl; auto.
  destruct a; simpl; auto.
  boolvar; subst; auto.
Qed.

Definition contains_only {o} (name : choice_sequence_name) (t : @CTerm o) :=
  get_defs (get_cterm t) = [defk_cs name].

Definition swap_cs_choice_seq_vals {o} (r : cs_swap) (vals : @ChoiceSeqVals o) : ChoiceSeqVals :=
  map (swap_cs_cterm r) vals.

Definition swap_cs_default {o} (r : cs_swap) (d : nat -> @ChoiceSeqVal o) : nat -> ChoiceSeqVal :=
  fun n => swap_cs_cterm r (d n).

Definition swap_cs_restriction_pred {o} (r : cs_swap) (M : @RestrictionPred o) : RestrictionPred :=
  fun n t => M n (swap_cs_cterm r t).

Lemma swap_cs_restriction_pred_default {o}
      (r  : cs_swap)
      (d  : nat -> @ChoiceSeqVal o)
      (M  : @RestrictionPred o)
      (Md : forall n, M n (d n)) : forall n, swap_cs_restriction_pred r M n (swap_cs_default r d n).
Proof.
  introv.
  unfold swap_cs_default, swap_cs_restriction_pred; simpl.
  rewrite swap_cs_cterm_idem; auto.
Defined.

Definition cs_name2restr {o} (name : choice_sequence_name) : option (@ChoiceSeqRestriction o) :=
  match csn_kind name with
  | cs_kind_nat n =>
    if deq_nat n 0
    then Some csc_nat
    else if deq_nat n 1
         then Some csc_bool
         else None
  | cs_kind_seq l => Some (natSeq2restriction l)
  end.

Definition swap_cs_choice_seq_restr {o}
           (r     : cs_swap)
           (restr : @ChoiceSeqRestriction o) : ChoiceSeqRestriction :=
  match restr with
  | csc_type d M Md =>
    csc_type
      (swap_cs_default r d)
      (swap_cs_restriction_pred r M)
      (swap_cs_restriction_pred_default r d M Md)
  | csc_coq_law f => csc_coq_law (fun n => swap_cs_cterm r (f n))
  end.

(* We make sure that we generate compatible restrictions in case one name
   in the swapping has a [cs_kind_nat 0] space, while the other one has a
   [cs_kind_seq l] space, for example. *)
Definition swap_cs_choice_seq_restr_comp {o}
           (r     : cs_swap)
           (name  : choice_sequence_name)
           (restr : @ChoiceSeqRestriction o) : ChoiceSeqRestriction :=
  match cs_name2restr name with
  | Some restr => restr
  | None => swap_cs_choice_seq_restr r restr
  end.

Definition swap_cs_choice_seq_entry {o}
           (r : cs_swap)
           (e : @ChoiceSeqEntry o) : ChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    MkChoiceSeqEntry
      _
      (swap_cs_choice_seq_vals r vals)
      (swap_cs_choice_seq_restr r restr)
  end.

Fixpoint swap_cs_soterm {o} (r : cs_swap) (t : @SOTerm o) : SOTerm :=
  match t with
  | sovar v ts => sovar v (map (swap_cs_soterm r) ts)
  | soterm op bs => soterm (swap_cs_op r op) (map (swap_cs_sobterm r) bs)
  end
with swap_cs_sobterm {o} (r : cs_swap) (bt : @SOBTerm o) : SOBTerm :=
       match bt with
       | sobterm vs t => sobterm vs (swap_cs_soterm r t)
       end.

Lemma implies_wf_soterm_swap_cs_soterm {o} :
  forall (r : cs_ren) (t : @SOTerm o),
    wf_soterm t
    -> wf_soterm (swap_cs_soterm r t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv wf; simpl; tcsp.

  - Case "sovar".
    allrw @wf_sovar.
    introv i.
    apply in_map_iff in i; exrepnd; subst.
    applydup wf in i1.
    apply ind in i1; auto.

  - Case "soterm".
    allrw @wf_soterm_iff.
    allrw map_map; unfold compose.
    autorewrite with slow.
    repnd; dands; auto.

    + rewrite <- wf0.
      apply eq_maps; introv i.
      destruct x; unfold num_bvars; simpl; auto.

    + introv i.
      allrw in_map_iff; exrepnd; subst.
      destruct a; simpl in *; ginv.
      eapply ind; eauto.
Qed.
Hint Resolve implies_wf_soterm_swap_cs_soterm : slow.

Lemma so_free_vars_swap_cs_soterm {o} :
  forall (r : cs_swap) (t : @SOTerm o),
    so_free_vars (swap_cs_soterm r t) = so_free_vars t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    autorewrite with list; f_equal.
    rewrite flat_map_map.
    apply eq_flat_maps; introv i.
    apply ind in i.
    unfold compose; auto.

  - Case "soterm".
    rewrite flat_map_map.
    apply eq_flat_maps; introv i.
    unfold compose; auto.
    destruct x; simpl.
    apply ind in i; rewrite i; auto.
Defined.
Hint Rewrite @so_free_vars_swap_cs_soterm : slow.

Lemma implies_socovered_swap_cs_soterm {o} :
  forall r (t : @SOTerm o) vars,
    socovered t vars
    -> socovered (swap_cs_soterm r t) vars.
Proof.
  introv cov.
  unfold socovered in *; autorewrite with slow; auto.
Qed.
Hint Resolve implies_socovered_swap_cs_soterm : slow.

Lemma get_utokens_o_swap_cs_op {o} :
  forall r (op : @Opid o),
    get_utokens_o (swap_cs_op r op) = get_utokens_o op.
Proof.
  introv.
  destruct op; simpl; tcsp.
  destruct c; simpl; tcsp.
Qed.
Hint Rewrite @get_utokens_o_swap_cs_op : slow.

Lemma get_utokens_so_swap_cs_soterm {o} :
  forall (r : cs_swap) (t : @SOTerm o),
    get_utokens_so (swap_cs_soterm r t) = get_utokens_so t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; tcsp.

  - Case "sovar".
    rewrite flat_map_map; unfold compose; simpl.
    apply eq_flat_maps; introv i; tcsp.

  - Case "soterm".
    rewrite flat_map_map.
    autorewrite with slow.
    f_equal.
    apply eq_flat_maps; introv i.
    unfold compose; auto.
    destruct x; simpl.
    apply ind in i; rewrite i; auto.
Defined.
Hint Rewrite @get_utokens_so_swap_cs_soterm : slow.

Lemma implies_no_utokens_swap_cs_soterm {o} :
  forall r (t : @SOTerm o),
    no_utokens t
    -> no_utokens (swap_cs_soterm r t).
Proof.
  introv nou.
  unfold no_utokens in *; autorewrite with slow; auto.
Qed.
Hint Resolve implies_no_utokens_swap_cs_soterm : slow.

Lemma swap_cs_correct_abs {o}
      (r    : cs_swap)
      (abs  : opabs)
      (vars : list sovar_sig)
      (rhs  : @SOTerm o)
      (cor  : correct_abs abs vars rhs) : correct_abs abs vars (swap_cs_soterm r rhs).
Proof.
  unfold correct_abs in *; repnd.
  dands; eauto 3 with slow.
Qed.

Definition normalize_choice_seq_entry {o} (name : choice_sequence_name) (e : @ChoiceSeqEntry o) : ChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    match cs_name2restr name with
    | Some restr => MkChoiceSeqEntry _ vals restr
    | None => MkChoiceSeqEntry _ vals restr
    end
  end.

(* [name] is the old name, and [name'] is the new one.  If they're equal then
   we haven't renamed anything.  Otherwise, we have, and in that case, we normalize
   the sequence by making sure that its restriction is the correct one *)
Definition swap_cs_choice_seq_entry_normalize {o}
           (name name' : choice_sequence_name)
           (r : cs_swap)
           (e : @ChoiceSeqEntry o) : ChoiceSeqEntry :=
  let e' := swap_cs_choice_seq_entry r e in
  if choice_sequence_name_deq name name'
  then e'
  else normalize_choice_seq_entry name' e'.

Definition swap_cs_lib_entry {o} (r : cs_swap) (e : @library_entry o) :=
  match e with
  | lib_cs name e =>
    let name' := swap_cs r name in
    lib_cs name' (swap_cs_choice_seq_entry_normalize name name' r e)
  | lib_abs abs vars rhs correct =>
    lib_abs abs vars (swap_cs_soterm r rhs) (swap_cs_correct_abs r abs vars rhs correct)
  end.

Fixpoint swap_cs_lib {o} (r : cs_swap) (lib : @library o) :=
  match lib with
  | [] => []
  | entry :: entries => swap_cs_lib_entry r entry :: swap_cs_lib r entries
  end.

Definition upd_restr_choice_seq_entry {o} (cs : choice_sequence_name) (e : @ChoiceSeqEntry o) : ChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    match cs_name2restr cs with
    | Some restr => MkChoiceSeqEntry _ vals restr
    | None => MkChoiceSeqEntry _ vals restr
    end
  end.

Definition upd_restr_lib_entry {o} (cs : choice_sequence_name) (e : @library_entry o) :=
  match e with
  | lib_cs name e =>
    if String.string_dec (csn_name name) (csn_name cs)
    then Some (lib_cs cs (upd_restr_choice_seq_entry cs e))
    else None
  | lib_abs abs vars rhs correct => None
  end.

Lemma swap_cs_inj :
  forall (sw : cs_swap) (name1 name2 : choice_sequence_name),
    swap_cs sw name1 = swap_cs sw name2
    -> name1 = name2.
Proof.
  introv h.
  destruct sw; simpl in *; boolvar; subst; auto; tcsp.
Qed.

Lemma matching_entries_swap_iff {o} :
  forall (sw : cs_swap) (e1 e2 : @library_entry o),
    matching_entries (swap_cs_lib_entry sw e1) (swap_cs_lib_entry sw e2)
    <-> matching_entries e1 e2.
Proof.
  introv.
  unfold matching_entries; simpl.
  destruct e1, e2; simpl in *; tcsp.
  split; intro h; subst; ginv; tcsp.
  apply swap_cs_inj in h; auto.
Qed.
Hint Rewrite @matching_entries_swap_iff : slow.

Lemma swap_entry_in_library {o} :
  forall sw entry (lib : @library o),
    entry_in_library entry lib
    -> entry_in_library (swap_cs_lib_entry sw entry) (swap_cs_lib sw lib).
Proof.
  induction lib; introv h; simpl in *; tcsp;[].
  repndors; repnd; subst; simpl in *; auto;[].
  right.
  dands; auto.
  rewrite matching_entries_swap_iff; auto.
Qed.

Fixpoint cs_name_in_library {o} (name : choice_sequence_name) (lib : @library o) : bool :=
  match lib with
  | [] => false
  | lib_cs name' _ :: entries =>
    if choice_sequence_name_deq name name' then true
    else cs_name_in_library name entries
  | _ :: entries => cs_name_in_library name entries
  end.

Lemma swap_cs_cterm_nat_implies {o} :
  forall sw (v : @CTerm o) i,
    swap_cs_cterm sw v = mkc_nat i
    -> v = mkc_nat i.
Proof.
  introv h.
  destruct v; simpl in *; tcsp.
  destruct x as [z|op bs]; simpl in *; inversion h as [xx]; clear h.
  destruct bs; simpl in *; tcsp; GC.
  destruct op; ginv.
  destruct c; ginv.
  apply cterm_eq; simpl; auto.
Qed.

Lemma cterm_is_nth_swap_cs_cterm {o} :
  forall sw (v : @ChoiceSeqVal o) n l,
    cterm_is_nth (swap_cs_cterm sw v) n l <-> cterm_is_nth v n l.
Proof.
  introv.
  unfold cterm_is_nth.
  split; intro h; exrepnd.
  { apply swap_cs_cterm_nat_implies in h0; subst; simpl in *; eauto. }
  { subst; autorewrite with slow; eauto. }
Qed.
Hint Rewrite @cterm_is_nth_swap_cs_cterm : slow.

Lemma is_nat_swap_cs_cterm {o} :
  forall sw n (v : @ChoiceSeqVal o),
    is_nat n (swap_cs_cterm sw v) <-> is_nat n v.
Proof.
  introv.
  unfold is_nat.
  split; intro h; exrepnd.
  { apply swap_cs_cterm_nat_implies in h0; subst; simpl in *; eauto. }
  { subst; autorewrite with slow; eauto. }
Qed.
Hint Rewrite @is_nat_swap_cs_cterm : slow.

Lemma is_nat_seq_restriction_implies_same_swap_cs_choice_seq_restr {o} :
  forall l name name' (restr : @ChoiceSeqRestriction o),
    is_nat_seq_restriction l restr
    -> same_restrictions
         (swap_cs_choice_seq_restr (name, name') restr)
         restr.
Proof.
  introv isn.
  unfold is_nat_seq_restriction in *.
  destruct restr; simpl in *; repnd; tcsp;[].
  dands; tcsp.

  { introv.
    destruct (lt_dec n (length l)) as [w|w].

    { pose proof (isn0 n) as q; autodimp q hyp.
      unfold cterm_is_nth in q; exrepnd.
      unfold swap_cs_default; simpl.
      rewrite q0; autorewrite with slow; auto. }

    { pose proof (isn1 n) as q; autodimp q hyp; try omega.
      unfold cterm_is_nth in q; exrepnd.
      unfold swap_cs_default; simpl.
      rewrite q.
      rewrite mkc_zero_eq; autorewrite with slow; auto. } }

  { introv.
    unfold swap_cs_restriction_pred.
    destruct (lt_dec n (length l)) as [w|w].

    { pose proof (isn2 n v) as q; autodimp q hyp.
      pose proof (isn2 n (swap_cs_cterm (name,name') v)) as z; autodimp z hyp.
      rewrite q, z; autorewrite with slow; tcsp. }

    { pose proof (isn n v) as q; autodimp q hyp; try omega.
      pose proof (isn n (swap_cs_cterm (name,name') v)) as z; autodimp z hyp; try omega.
      rewrite q, z; autorewrite with slow; tcsp. } }
Qed.
Hint Resolve is_nat_seq_restriction_implies_same_swap_cs_choice_seq_restr : slow.

Lemma swap_cs_choice_seq_entry_0 {o} :
  forall name name' (lib : @library o) (e : ChoiceSeqEntry),
    safe_library lib
    -> compatible_choice_sequence_name 0 name
    -> find_cs lib name = Some e
    -> swap_cs_choice_seq_entry (name, name') e
       = MkChoiceSeqEntry _ (cse_vals e) (swap_cs_choice_seq_restr (name,name') (cse_restriction e)).
Proof.
  introv safe cop fcs.
  apply find_cs_some_implies_entry_in_library in fcs.
  apply safe in fcs; clear safe; simpl in *.
  destruct e as [vals restr]; simpl in *; repnd.
  applydup @implies_same_restrictions_nat in fcs0; auto; exrepnd.
  f_equal.
  apply eq_map_l; introv i.
  eapply choice_sequence_0_implies_nat in i; eauto.
  exrepnd; subst; autorewrite with slow; auto.
Qed.

Lemma swap_cs_cterm_apply {o} :
  forall sw (a b : @CTerm o),
    swap_cs_cterm sw (mkc_apply a b)
    = mkc_apply (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.

Lemma swap_cs_cterm_mkc_choice_seq_same {o} :
  forall name name',
    swap_cs_cterm (name, name') (@mkc_choice_seq o name)
    = mkc_choice_seq name'.
Proof.
  introv; apply cterm_eq; simpl; boolvar; tcsp.
Qed.

Lemma get_defs_o_nil_implies_eq_swap {o} :
  forall sw (op : @Opid o),
    get_defs_o op = []
    -> swap_cs_op sw op = op.
Proof.
  introv h.
  destruct op; simpl in *; tcsp.
  destruct c; simpl in *; tcsp.
Qed.

Lemma nodefs_oterm {o} :
  forall op (bs : list (@BTerm o)),
    nodefs (oterm op bs)
    <-> (get_defs_o op = [] /\ forall l t, LIn (bterm l t) bs -> nodefs t).
Proof.
  introv.
  unfold nodefs; simpl; split; intro h.
  { apply app_eq_nil_iff in h; repnd; dands; auto.
    introv i.
    eapply flat_map_empty in h; eauto; simpl  in *; auto. }
  repnd.
  apply app_eq_nil_iff; dands; auto.
  apply flat_map_empty; introv i.
  destruct a; simpl in *.
  eapply h; eauto.
Qed.

Lemma swap_cs_term_if_nodefsc {o} :
  forall sw (a : @NTerm o),
    nodefs a
    -> swap_cs_term sw a = a.
Proof.
  nterm_ind a as [v|op bs ind] Case; introv nod; simpl in *; auto;[].
  Case "oterm".
  apply nodefs_oterm in nod; repnd.
  rewrite get_defs_o_nil_implies_eq_swap; auto.
  f_equal.
  apply eq_map_l; introv i.
  destruct x; simpl; f_equal.
  apply ind in i; auto.
  apply nod in i; auto.
Qed.

Lemma swap_cs_cterm_if_nodefsc {o} :
  forall sw (a : @CTerm o),
    nodefsc a
    -> swap_cs_cterm sw a = a.
Proof.
  introv nod; destruct_cterms; apply cterm_eq; simpl in *.
  apply swap_cs_term_if_nodefsc; auto.
Qed.

Lemma swap_cs_choice_seq_vals_idem {o} :
  forall sw (vals : @ChoiceSeqVals o),
    swap_cs_choice_seq_vals sw (swap_cs_choice_seq_vals sw vals) = vals.
Proof.
  introv; unfold swap_cs_choice_seq_vals.
  rewrite map_map; unfold compose; simpl.
  apply eq_map_l; introv i; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_choice_seq_vals_idem : slow.
Hint Resolve swap_cs_choice_seq_vals_idem : slow.

Lemma swap_cs_choice_seq_restr_idem {o} :
  forall sw (restr : @ChoiceSeqRestriction o),
    same_restrictions
      (swap_cs_choice_seq_restr sw (swap_cs_choice_seq_restr sw restr))
      restr.
Proof.
  destruct restr; simpl; autorewrite with slow; dands.

  { introv; unfold swap_cs_default; simpl; autorewrite with slow; auto. }

  { introv; unfold swap_cs_restriction_pred; autorewrite with slow; tcsp. }

  { introv; autorewrite with slow; auto. }
Qed.
Hint Resolve swap_cs_choice_seq_restr_idem : slow.

Definition same_choice_seq_entries {o} (e1 e2 : @ChoiceSeqEntry o) :=
  cse_vals e1 = cse_vals e2
  /\ same_restrictions (cse_restriction e1) (cse_restriction e2).

Definition same_library_entries {o} (e1 e2 : @library_entry o) :=
  match e1, e2 with
  | lib_cs name1 e1, lib_cs name2 e2 => name1 = name2 /\ same_choice_seq_entries e1 e2
  | _, _ => e1 = e2
  end.

Fixpoint same_libraries {o} (lib1 lib2 : @library o) :=
  match lib1, lib2 with
  | [], [] => True
  | e1 :: l1, e2 :: l2 => same_library_entries e1 e2 /\ same_libraries l1 l2
  | _, _ => False
  end.

Lemma swap_cs_soterm_idem {o} :
  forall (r : cs_swap)
         (t : @SOTerm o),
    swap_cs_soterm r (swap_cs_soterm r t) = t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; auto;[|].

  { Case "sovar".
    f_equal.
    rewrite map_map; unfold compose; simpl.
    apply eq_map_l; introv i.
    apply ind in i; auto. }

  { Case "soterm".
    autorewrite with slow.
    f_equal.
    allrw map_map; unfold compose.
    apply eq_map_l; introv i.
    destruct x; apply ind in i.
    simpl; f_equal; auto. }
Qed.
Hint Rewrite @swap_cs_soterm_idem : slow.

Lemma swap_cs_choice_seq_entry_idem {o} :
  forall sw (entry : @ChoiceSeqEntry o),
    same_choice_seq_entries
      (swap_cs_choice_seq_entry
         sw
         (swap_cs_choice_seq_entry sw entry))
      entry.
Proof.
  introv.
  unfold swap_cs_choice_seq_entry.
  destruct entry as [vals restr]; simpl.
  autorewrite with slow.
  unfold same_choice_seq_entries; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve swap_cs_choice_seq_entry_idem : slow.

Lemma natSeq2default_eq {o} :
  forall l n,
    @natSeq2default o l n
    = if lt_dec n (length l)
      then mkc_nat (nth n l 0)
      else mkc_zero.
Proof.
  introv.
  boolvar.
  - applydup (@cterm_is_nth_natSeq2default o) in l0.
    unfold cterm_is_nth in *; exrepnd; allrw.
    rewrite (nth_select1 _ _ 0) in l1; auto; ginv.
  - rewrite natSeq2default_eq_zero; auto; try omega.
Qed.

Lemma is_nat_seq_restriction_implies_same {o} :
  forall l (restr : @ChoiceSeqRestriction o),
    is_nat_seq_restriction l restr
    -> same_restrictions (natSeq2restriction l) restr.
Proof.
  introv isn.
  unfold is_nat_seq_restriction in isn.
  destruct restr; simpl in *; repnd; tcsp.
  dands; introv.
  { rewrite natSeq2default_eq; boolvar.
    - applydup isn0 in l0.
      unfold cterm_is_nth in l1; exrepnd.
      rewrite (nth_select1 _ _ 0) in l1; auto; ginv.
    - symmetry; apply isn1; try omega. }
  { unfold natSeq2restrictionPred.
    remember (select n l) as sel; symmetry in Heqsel; destruct sel.
    - pose proof (isn2 n v) as isn2; autodimp isn2 hyp; eauto 3 with slow.
      rewrite isn2; unfold cterm_is_nth; allrw.
      split; intro h; exrepnd; ginv; subst; eauto.
    - applydup @nth_select2 in Heqsel.
      pose proof (isn n v) as isn; autodimp isn hyp; try omega.
      rewrite isn; tcsp. }
Qed.
Hint Resolve is_nat_seq_restriction_implies_same : slow.

Lemma same_restrictions_if_correct {o} :
  forall n (restr : @ChoiceSeqRestriction o) c,
    correct_restriction n restr
    -> cs_name2restr n = Some c
    -> same_restrictions c restr.
Proof.
  introv cor h.
  destruct n as [n k]; simpl in *.
  unfold cs_name2restr in *; simpl in *.
  unfold correct_restriction in *; simpl in *.
  destruct k; simpl in *; boolvar; subst; tcsp; ginv; eauto 3 with slow.
Qed.
Hint Resolve same_restrictions_if_correct : slow.

Definition compatible_cs_kinds (k1 k2 : cs_kind) :=
  match k1, k2 with
  | cs_kind_nat n, cs_kind_nat m => n = m
  | cs_kind_nat n, cs_kind_seq l => n = 0
  | cs_kind_seq l, cs_kind_nat n => n = 0
  | cs_kind_seq l, cs_kind_seq k => True
  end.

Definition compatible_choice_sequences (name1 name2 : choice_sequence_name) :=
  compatible_cs_kinds (csn_kind name1) (csn_kind name2).

Definition sane_swapping (sw : cs_swap) :=
  let (n1, n2) := sw in
  compatible_choice_sequences n1 n2.

Definition compatible_cs_kinds_same (k1 k2 : cs_kind) :=
  match k1, k2 with
  | cs_kind_nat n, cs_kind_nat m => n = m
  | cs_kind_seq l, cs_kind_seq k => l = k
  | _, _ => False
  end.

Definition compatible_choice_sequences_same (name1 name2 : choice_sequence_name) :=
  compatible_cs_kinds_same (csn_kind name1) (csn_kind name2).

Definition same_swapping (sw : cs_swap) :=
  let (n1, n2) := sw in
  compatible_choice_sequences_same n1 n2.

Lemma compatible_choice_sequences_implies_cs_name2restr_none {o} :
  forall n1 n2,
    compatible_choice_sequences n1 n2
    -> @cs_name2restr o n1 = None
    -> @cs_name2restr o n2 = None.
Proof.
  introv comp h.
  unfold compatible_choice_sequences in *.
  destruct n1 as [n1 k1], n2 as [n2 k2]; simpl in *.
  unfold cs_name2restr in *; simpl in *.
  destruct k1, k2; simpl in *; subst; boolvar; subst; simpl in *; tcsp.
Qed.
Hint Resolve compatible_choice_sequences_implies_cs_name2restr_none : slow.

Lemma compatible_cs_kinds_sym :
  forall k1 k2,
    compatible_cs_kinds k1 k2
    -> compatible_cs_kinds k2 k1.
Proof.
  introv comp.
  unfold compatible_cs_kinds in *.
  destruct k1, k2; simpl in *; tcsp.
Qed.
Hint Resolve compatible_cs_kinds_sym : slow.

Lemma compatible_choice_sequences_sym :
  forall n1 n2,
    compatible_choice_sequences n1 n2
    -> compatible_choice_sequences n2 n1.
Proof.
  introv comp.
  unfold compatible_choice_sequences in *.
  destruct n1 as [n1 k1], n2 as [n2 k2]; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve compatible_choice_sequences_sym : slow.

Lemma swap_cs_choice_seq_entry_normalize_idem {o} :
  forall sw name (entry : @ChoiceSeqEntry o),
    sane_swapping sw
    -> safe_choice_sequence_entry name entry
    -> same_choice_seq_entries
         (swap_cs_choice_seq_entry_normalize
            (swap_cs sw name)
            name sw
            (swap_cs_choice_seq_entry_normalize name (swap_cs sw name) sw entry))
         entry.
Proof.
  introv sane safe.
  unfold swap_cs_choice_seq_entry_normalize.
  destruct sw as [n1 n2]; simpl.
  boolvar; subst; simpl in *; GC; eauto 3 with slow; tcsp;[|].

  { destruct entry as [vals restr]; simpl in *; repnd.
    remember (cs_name2restr n2) as opr2; symmetry in Heqopr2.
    destruct opr2; simpl in *.

    { remember (cs_name2restr n1) as opr1; symmetry in Heqopr1.
      destruct opr1; simpl in *; autorewrite with slow; eauto 3 with slow;
        unfold same_choice_seq_entries; simpl; dands; eauto 3 with slow.
      apply (@compatible_choice_sequences_implies_cs_name2restr_none o) in sane; auto.
      rewrite sane in *; ginv. }

    { remember (cs_name2restr n1) as opr1; symmetry in Heqopr1.
      destruct opr1; simpl in *; autorewrite with slow; eauto 3 with slow;
        unfold same_choice_seq_entries; simpl; dands; eauto 3 with slow. } }

  { destruct entry as [vals restr]; simpl in *; repnd.
    remember (cs_name2restr n1) as opr1; symmetry in Heqopr1.
    destruct opr1; simpl in *;
      remember (cs_name2restr n2) as opr2; symmetry in Heqopr2;
        destruct opr2; simpl in *;
          unfold same_choice_seq_entries; simpl; dands; eauto 3 with slow;[].
    apply compatible_choice_sequences_sym in sane.
    apply (@compatible_choice_sequences_implies_cs_name2restr_none o) in sane; auto.
    rewrite sane in *; ginv. }
Qed.
Hint Resolve swap_cs_choice_seq_entry_normalize_idem : slow.

Lemma swap_cs_lib_entry_idem {o} :
  forall sw (e : @library_entry o),
    sane_swapping sw
    -> safe_library_entry e
    -> same_library_entries (swap_cs_lib_entry sw (swap_cs_lib_entry sw e)) e.
Proof.
  introv sane safe.
  destruct e; simpl in *; autorewrite with slow; dands; auto; eauto 3 with slow; GC;[].

  remember (swap_cs_correct_abs
              sw opabs vars (swap_cs_soterm sw rhs)
              (swap_cs_correct_abs sw opabs vars rhs correct)) as w.
  clear Heqw.
  revert w.
  autorewrite with slow; introv.
  f_equal; eauto with pi.
Qed.
Hint Resolve swap_cs_lib_entry_idem : slow.

Definition strong_safe_library {o} (lib : @library o) :=
  forall e, List.In e lib -> safe_library_entry e.

Lemma strong_safe_library_implies_safe {o} :
  forall (lib : @library o),
    strong_safe_library lib -> safe_library lib.
Proof.
  introv safe i.
  apply entry_in_library_implies_in in i; apply safe in i; auto.
Qed.
Hint Resolve strong_safe_library_implies_safe : slow.

Lemma strong_safe_library_cons {o} :
  forall e (lib : @library o),
    strong_safe_library (e :: lib) <-> (safe_library_entry e /\ strong_safe_library lib).
Proof.
  introv; split; intro safe; dands.
  { pose proof (safe e) as safe; simpl in *; tcsp. }
  { introv i; pose proof (safe e0) as safe; simpl in *; tcsp. }
  { repnd; introv i; simpl in *; repndors; subst; simpl in *; tcsp. }
Qed.

Lemma swap_cs_lib_idem {o} :
  forall sw (lib : @library o),
    sane_swapping sw
    -> strong_safe_library lib
    -> same_libraries
         (swap_cs_lib sw (swap_cs_lib sw lib))
         lib.
Proof.
  induction lib; introv sane safe; simpl; dands; auto;
    allrw @strong_safe_library_cons; repnd; eauto 3 with slow.
Qed.
Hint Resolve swap_cs_lib_idem : slow.

Lemma same_choice_seq_entries_sym {o} :
  forall (e1 e2 : @ChoiceSeqEntry o),
    same_choice_seq_entries e1 e2
    -> same_choice_seq_entries e2 e1.
Proof.
  introv same; unfold same_choice_seq_entries in *; repnd; dands; subst; tcsp; eauto 3 with slow.
Qed.
Hint Resolve same_choice_seq_entries_sym : slow.

Lemma same_library_entries_sym {o} :
  forall (e1 e2 : @library_entry o),
    same_library_entries e1 e2
    -> same_library_entries e2 e1.
Proof.
  introv same.
  unfold same_library_entries in *.
  destruct e1, e2; simpl in *; repnd; subst; dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_sym : slow.

Lemma same_libraries_sym {o} :
  forall (lib1 lib2 : @library o),
    same_libraries lib1 lib2 -> same_libraries lib2 lib1.
Proof.
  induction lib1; introv same; simpl in *; destruct lib2; simpl in *; tcsp.
  repnd; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve same_libraries_sym : slow.

Lemma same_library_entries_preserves_not_matching_entries {o} :
  forall (a b c d : @library_entry o),
    same_library_entries a b
    -> same_library_entries c d
    -> ~ matching_entries d b
    -> ~ matching_entries c a.
Proof.
  introv same1 same2 nm m.
  destruct nm.
  destruct a, b, c, d; simpl in *; repnd; subst; tcsp; ginv;[].
  inversion same1; subst.
  inversion same2; subst.
  unfold matching_entries in *; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_preserves_not_matching_entries : slow.

Lemma entry_in_same_library_implies {o} :
  forall (lib1 lib2 : @library o) e,
    same_libraries lib1 lib2
    -> entry_in_library e lib2
    -> exists e', entry_in_library e' lib1 /\ same_library_entries e' e.
Proof.
  induction lib1; destruct lib2; introv same i; simpl in *; tcsp.
  repnd; repndors; repnd; subst; tcsp.

  { exists a; dands; auto. }

  pose proof (IHlib1 lib2 e) as IHlib1.
  repeat (autodimp IHlib1 hyp); exrepnd.
  exists e'; dands; auto.
  right; dands; eauto 2 with slow.
Qed.

Lemma same_choice_seq_entries_preserves_choice_sequence_entry_extend {o} :
  forall (e e1 e2 : @ChoiceSeqEntry o),
    same_choice_seq_entries e1 e2
    -> choice_sequence_entry_extend e e2
    -> choice_sequence_entry_extend e e1.
Proof.
  introv same ext.
  unfold choice_sequence_entry_extend in *; repnd.
  unfold same_choice_seq_entries in *; repnd.
  destruct e1 as [vals1 restr1], e2 as [vals2 restr2]; simpl in *; subst; simpl in *.
  dands; eauto 3 with slow.
Qed.
Hint Resolve same_choice_seq_entries_preserves_choice_sequence_entry_extend : slow.

Lemma same_library_entries_preserves_entry_in_library_extends {o} :
  forall e1 e2 (lib : @library o),
    same_library_entries e1 e2
    -> entry_in_library_extends e2 lib
    -> entry_in_library_extends e1 lib.
Proof.
  destruct e1, e2; introv same i; simpl in *; repnd; subst; eauto 3 with slow; ginv;[].
  induction lib; simpl in *; tcsp;[].
  repndors; tcsp;[].
  left.
  unfold entry_extends in *.
  destruct a; simpl in *; tcsp; ginv.
  repnd; subst; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_preserves_entry_in_library_extends : slow.

Lemma same_libraries_implies_lib_extends_entries {o} :
  forall (lib1 lib2 : @library o),
    same_libraries lib1 lib2
    -> lib_extends_entries lib1 lib2.
Proof.
  introv same i.
  eapply entry_in_same_library_implies in i; try exact same.
  exrepnd; eauto 3 with slow.
  eapply same_library_entries_preserves_entry_in_library_extends;
    [apply same_library_entries_sym;eauto|].
  eauto 3 with slow.
Qed.
Hint Resolve same_libraries_implies_lib_extends_entries : slow.

Lemma same_restrictions_preserves_choice_sequence_satisfies_restriction {o} :
  forall vals (restr1 restr2 : @ChoiceSeqRestriction o),
    same_restrictions restr1 restr2
    -> choice_sequence_satisfies_restriction vals restr1
    -> choice_sequence_satisfies_restriction vals restr2.
Proof.
  introv same sat.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr1, restr2; simpl in *; repnd; tcsp.

  { introv sel.
    apply sat in sel; apply same; auto. }

  { introv w.
    apply sat in w; rewrite <- same; auto. }
Qed.
Hint Resolve same_restrictions_preserves_choice_sequence_satisfies_restriction : slow.

Lemma same_library_entries_preserves_safe {o} :
  forall (e1 e2 : @library_entry o),
  same_library_entries e1 e2
  -> safe_library_entry e1
  -> safe_library_entry e2.
Proof.
  introv same safe.
  destruct e1, e2; simpl in *; repnd; subst; tcsp; ginv;[].
  destruct entry as [vals1 restr1], entry0 as [vals2 restr2]; simpl in *; repnd.
  unfold same_choice_seq_entries in *; simpl in *; repnd; subst.
  dands; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_preserves_safe : slow.

Lemma same_libraries_preserves_safe_library {o} :
  forall (lib1 lib2 : @library o),
    same_libraries lib1 lib2
    -> safe_library lib2
    -> safe_library lib1.
Proof.
  introv same safe i.
  eapply entry_in_same_library_implies in i;[|apply same_libraries_sym;eauto].
  exrepnd.
  apply safe in i1; eauto 3 with slow.
Qed.
Hint Resolve same_libraries_preserves_safe_library : slow.

Lemma in_same_library_implies {o} :
  forall (lib1 lib2 : @library o) e,
    same_libraries lib1 lib2
    -> List.In e lib2
    -> exists e', List.In e' lib1 /\ same_library_entries e' e.
Proof.
  induction lib1; destruct lib2; introv same i; simpl in *; tcsp.
  repnd; repndors; repnd; subst; tcsp.

  { exists a; dands; auto. }

  pose proof (IHlib1 lib2 e) as IHlib1.
  repeat (autodimp IHlib1 hyp); exrepnd.
  exists e'; dands; auto.
Qed.

Lemma same_library_entries_implies_entry_extends {o} :
  forall (e1 e2 : @library_entry o),
    same_library_entries e1 e2
    -> entry_extends e1 e2.
Proof.
  introv same.
  destruct e1, e2; simpl in *; repnd; dands; subst; tcsp; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_implies_entry_extends : slow.

Lemma same_libraries_preserves_subset_library {o} :
  forall (lib1 lib2 : @library o),
    same_libraries lib1 lib2
    -> subset_library lib2 lib1.
Proof.
  introv same i.
  eapply in_same_library_implies in i; eauto.
  exrepnd.
  exists e'.
  dands; eauto 3 with slow.
Qed.
Hint Resolve same_libraries_preserves_subset_library : slow.

Lemma same_libraries_implies_lib_extends {o} :
  forall (lib1 lib2 : @library o),
    same_libraries lib1 lib2
    -> lib_extends lib1 lib2.
Proof.
  introv same.
  split; eauto 3 with slow.
Qed.
Hint Resolve same_libraries_implies_lib_extends : slow.

Definition swap_cs_inf_choice_seq_vals {o} (r : cs_swap) (vals : @InfChoiceSeqVals o) : InfChoiceSeqVals :=
  fun n => swap_cs_cterm r (vals n).

Definition swap_cs_inf_choice_seq_entry {o} (r : cs_swap) (e : @InfChoiceSeqEntry o) : InfChoiceSeqEntry :=
  match e with
  | MkInfChoiceSeqEntry _ vals restr =>
    MkInfChoiceSeqEntry _ (swap_cs_inf_choice_seq_vals r vals) (swap_cs_choice_seq_restr r restr)
  end.

Definition normalize_inf_choice_seq_entry {o} (name : choice_sequence_name) (e : @InfChoiceSeqEntry o) : InfChoiceSeqEntry :=
  match e with
  | MkInfChoiceSeqEntry _ vals restr =>
    match cs_name2restr name with
    | Some restr => MkInfChoiceSeqEntry _ vals restr
    | None => MkInfChoiceSeqEntry _ vals restr
    end
  end.

(* [name] is the old name, and [name'] is the new one.  If they're equal then
   we haven't renamed anything.  Otherwise, we have, and in that case, we normalize
   the sequence by making sure that its restriction is the correct one *)
Definition swap_cs_inf_choice_seq_entry_normalize {o}
           (name name' : choice_sequence_name)
           (r : cs_swap)
           (e : @InfChoiceSeqEntry o) : InfChoiceSeqEntry :=
  let e' := swap_cs_inf_choice_seq_entry r e in
  if choice_sequence_name_deq name name'
  then e'
  else normalize_inf_choice_seq_entry name' e'.

Definition swap_cs_inf_lib_entry {o} (r : cs_swap) (e : @inf_library_entry o) : inf_library_entry :=
  match e with
  | inf_lib_cs name e =>
    let name' := swap_cs r name in
    inf_lib_cs name' (swap_cs_inf_choice_seq_entry_normalize name name' r e)
  | inf_lib_abs abs vars rhs correct =>
    inf_lib_abs abs vars (swap_cs_soterm r rhs) (swap_cs_correct_abs r abs vars rhs correct)
  end.

Definition swap_cs_inf_lib {o}
           (sw : cs_swap)
           (ilib : @inf_library o) : inf_library :=
  fun n => swap_cs_inf_lib_entry sw (ilib n).


Definition normalize_inf_choice_seq_vals {o} (l : list nat) (vals : @InfChoiceSeqVals o) : InfChoiceSeqVals :=
  fun n =>
    match select n l with
    | Some v => mkc_nat v
    | None => vals n
    end.

(* as opposed to [normalize_inf_choice_seq_entry], this version also normalizes
   the values because we might swap to another name that has more default values
   (through [cs_kind_seq]) *)
Definition normalize_inf_choice_seq_entry_vals {o} (name : choice_sequence_name) (e : @InfChoiceSeqEntry o) : InfChoiceSeqEntry :=
  match e with
  | MkInfChoiceSeqEntry _ vals restr =>
    match csn_kind name with
    | cs_kind_nat n =>
      if deq_nat n 0
      then MkInfChoiceSeqEntry _ vals csc_nat
      else if deq_nat n 1
           then MkInfChoiceSeqEntry _ vals csc_bool
           else MkInfChoiceSeqEntry _ vals restr
    | cs_kind_seq l => MkInfChoiceSeqEntry _ (normalize_inf_choice_seq_vals l vals) (natSeq2restriction l)
    end
  end.

Definition swap_cs_inf_choice_seq_entry_normalize_vals {o}
           (name name' : choice_sequence_name)
           (r : cs_swap)
           (e : @InfChoiceSeqEntry o) : InfChoiceSeqEntry :=
  let e' := swap_cs_inf_choice_seq_entry r e in
  if choice_sequence_name_deq name name'
  then e'
  else normalize_inf_choice_seq_entry_vals name' e'.

Definition swap_cs_inf_lib_entry_normalize_vals {o} (r : cs_swap) (e : @inf_library_entry o) : inf_library_entry :=
  match e with
  | inf_lib_cs name e =>
    let name' := swap_cs r name in
    inf_lib_cs name' (swap_cs_inf_choice_seq_entry_normalize_vals name name' r e)
  | inf_lib_abs abs vars rhs correct =>
    inf_lib_abs abs vars (swap_cs_soterm r rhs) (swap_cs_correct_abs r abs vars rhs correct)
  end.

Definition swap_cs_inf_lib_norm {o}
           (sw : cs_swap)
           (ilib : @inf_library o) : inf_library :=
  fun n => swap_cs_inf_lib_entry_normalize_vals sw (ilib n).

Definition swap_cs_per {o} sw (p : per(o)) : per(o) :=
  fun a b => p (swap_cs_cterm sw a) (swap_cs_cterm sw b).

Lemma swap_same_restrictions {o} :
  forall sw (restr1 restr2 : @ChoiceSeqRestriction o),
    same_restrictions restr1 restr2
    -> same_restrictions
         (swap_cs_choice_seq_restr sw restr1)
         (swap_cs_choice_seq_restr sw restr2).
Proof.
  introv same; destruct restr1, restr2; simpl in *; repnd; dands; tcsp; introv; try congruence.

  { unfold swap_cs_default; try congruence. }

  { unfold swap_cs_restriction_pred; tcsp. }
Qed.
Hint Resolve swap_same_restrictions : slow.

Lemma option_map_Some :
  forall {A B} (f : A -> B) (o : option A) x,
    option_map f o = Some x <-> exists a, o = Some a /\ x = f a.
Proof.
  destruct o; introv; simpl; split; intro h; exrepnd; ginv; eauto.
Qed.

Lemma swap_inf_choice_sequence_vals_extend {o} :
  forall sw vals1 (vals2 : @ChoiceSeqVals o),
    inf_choice_sequence_vals_extend vals1 vals2
    -> inf_choice_sequence_vals_extend
         (swap_cs_inf_choice_seq_vals sw vals1)
         (swap_cs_choice_seq_vals sw vals2).
Proof.
  introv ext sel.
  unfold swap_cs_choice_seq_vals in sel.
  rewrite select_map in sel.
  apply option_map_Some in sel; exrepnd; subst; simpl in *.
  apply ext in sel1; subst; auto.
Qed.
Hint Resolve swap_inf_choice_sequence_vals_extend : slow.

Lemma swap_inf_choice_sequence_entry_extend {o} :
  forall sw e1 (e2 : @ChoiceSeqEntry o),
    inf_choice_sequence_entry_extend e1 e2
    -> inf_choice_sequence_entry_extend
         (swap_cs_inf_choice_seq_entry sw e1)
         (swap_cs_choice_seq_entry sw e2).
Proof.
  introv ext.
  unfold inf_choice_sequence_entry_extend in *.
  repnd.
  destruct e1 as [vals1 restr1], e2 as [vals2 restr2]; simpl in *.
  dands; eauto 3 with slow.
Qed.
Hint Resolve swap_inf_choice_sequence_entry_extend : slow.

Lemma normalize_swap_inf_choice_sequence_entry_extend {o} :
  forall name sw e1 (e2 : @ChoiceSeqEntry o),
    inf_choice_sequence_entry_extend e1 e2
    -> inf_choice_sequence_entry_extend
         (normalize_inf_choice_seq_entry name (swap_cs_inf_choice_seq_entry sw e1))
         (normalize_choice_seq_entry name (swap_cs_choice_seq_entry sw e2)).
Proof.
  introv ext.
  unfold normalize_inf_choice_seq_entry, normalize_choice_seq_entry.
  destruct e1, e2; simpl in *.
  unfold inf_choice_sequence_entry_extend in *; simpl in *.
  destruct name as [name kind]; simpl in *.
  unfold cs_name2restr in *; simpl in *; repnd.
  destruct kind; simpl in *; boolvar; subst; simpl in *; dands; eauto 3 with slow; tcsp.
Qed.
Hint Resolve normalize_swap_inf_choice_sequence_entry_extend : slow.

Lemma swap_inf_choice_sequence_entry_extend_normalize {o} :
  forall name name' sw e1 (e2 : @ChoiceSeqEntry o),
    inf_choice_sequence_entry_extend e1 e2
    -> inf_choice_sequence_entry_extend
         (swap_cs_inf_choice_seq_entry_normalize name name' sw e1)
         (swap_cs_choice_seq_entry_normalize name name' sw e2).
Proof.
  introv ext.
  unfold swap_cs_inf_choice_seq_entry_normalize, swap_cs_choice_seq_entry_normalize.
  boolvar; subst; eauto 3 with slow.
Qed.
Hint Resolve swap_inf_choice_sequence_entry_extend_normalize : slow.

Lemma swap_inf_entry_extends {o} :
  forall sw e1 (e2 : @library_entry o),
    inf_entry_extends e1 e2
    -> inf_entry_extends (swap_cs_inf_lib_entry sw e1) (swap_cs_lib_entry sw e2).
Proof.
  introv i.
  unfold inf_entry_extends; simpl in *.
  destruct e1, e2; simpl in *; repnd; subst; tcsp.
  dands; auto; eauto 2 with slow.
Qed.
Hint Resolve swap_inf_entry_extends : slow.

Lemma inf_matching_entries_swap_iff {o} :
  forall (sw : cs_swap) e1 (e2 : @library_entry o),
    inf_matching_entries (swap_cs_inf_lib_entry sw e1) (swap_cs_lib_entry sw e2)
    <-> inf_matching_entries e1 e2.
Proof.
  introv.
  unfold inf_matching_entries; simpl.
  destruct e1, e2; simpl in *; tcsp.
  split; intro h; subst; ginv; tcsp.
  apply swap_cs_inj in h; auto.
Qed.
Hint Rewrite @inf_matching_entries_swap_iff : slow.

Lemma swap_entry_in_inf_library_extends {o} :
  forall sw entry n (ilib : @inf_library o),
    entry_in_inf_library_extends entry n ilib
    -> entry_in_inf_library_extends (swap_cs_lib_entry sw entry) n (swap_cs_inf_lib sw ilib).
Proof.
  induction n; introv i; simpl in *; tcsp;[].
  repndors; repnd; subst; simpl in *; auto;[left|right].

  { unfold swap_cs_inf_lib; eauto 3 with slow. }

  dands; eauto 3 with slow.
  unfold swap_cs_inf_lib; simpl.
  autorewrite with slow; auto.
Qed.
Hint Resolve swap_entry_in_inf_library_extends : slow.

Lemma swap_same_choice_seq_entries {o} :
  forall sw e1 (e2 : @ChoiceSeqEntry o),
    same_choice_seq_entries e1 e2
    -> same_choice_seq_entries
         (swap_cs_choice_seq_entry sw e1)
         (swap_cs_choice_seq_entry sw e2).
Proof.
  introv same.
  destruct e1 as [vals1 restr1], e2 as [vals2 restr2]; simpl in *.
  unfold same_choice_seq_entries in *; simpl in *; repnd; subst; simpl in *.
  dands; eauto 3 with slow.
Qed.
Hint Resolve swap_same_choice_seq_entries : slow.

Lemma swap_normalize_same_choice_seq_entries {o} :
  forall name sw (e1 e2 : @ChoiceSeqEntry o),
    same_choice_seq_entries e1 e2
    -> same_choice_seq_entries
         (normalize_choice_seq_entry name (swap_cs_choice_seq_entry sw e1))
         (normalize_choice_seq_entry name (swap_cs_choice_seq_entry sw e2)).
Proof.
  introv same.
  unfold normalize_choice_seq_entry; simpl.
  destruct e1, e2; simpl in *.
  unfold same_choice_seq_entries in *; simpl in *.
  destruct name as [name restr]; simpl in *.
  unfold cs_name2restr in *; simpl in *.
  destruct restr; simpl in *; repnd; subst; boolvar; subst; simpl in *; tcsp.
  dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve swap_normalize_same_choice_seq_entries : slow.

Lemma swap_same_choice_seq_entries_normalize {o} :
  forall name name' sw e1 (e2 : @ChoiceSeqEntry o),
    same_choice_seq_entries e1 e2
    -> same_choice_seq_entries
         (swap_cs_choice_seq_entry_normalize name name' sw e1)
         (swap_cs_choice_seq_entry_normalize name name' sw e2).
Proof.
  introv same.
  unfold swap_cs_choice_seq_entry_normalize; boolvar; eauto 3 with slow.
Qed.
Hint Resolve swap_same_choice_seq_entries_normalize : slow.

Lemma swap_same_entry_libraries {o} :
  forall sw (e1 e2 : @library_entry o),
    same_library_entries e1 e2
    -> same_library_entries (swap_cs_lib_entry sw e1) (swap_cs_lib_entry sw e2).
Proof.
  introv same.
  destruct e1, e2; simpl in *; repnd; subst; dands; tcsp; ginv; eauto 3 with slow;[].
  inversion same; subst; auto.
  f_equal; eauto with pi.
Qed.
Hint Resolve swap_same_entry_libraries : slow.

Lemma same_choice_seq_entries_trans {o} :
  forall (e1 e2 e3 : @ChoiceSeqEntry o),
    same_choice_seq_entries e1 e2
    -> same_choice_seq_entries e2 e3
    -> same_choice_seq_entries e1 e3.
Proof.
  introv same1 same2; unfold same_choice_seq_entries in *; repnd; dands; subst; tcsp; eauto 3 with slow.
  destruct e1 as [vals1 restr1], e2 as [vals2 restr2], e3 as [vals3 restr3]; simpl in *; subst; auto.
Qed.
Hint Resolve same_choice_seq_entries_trans : slow.

Lemma same_library_entries_trans {o} :
  forall (e1 e2 e3 : @library_entry o),
    same_library_entries e1 e2
    -> same_library_entries e2 e3
    -> same_library_entries e1 e3.
Proof.
  introv same1 same2.
  unfold same_library_entries in *.
  destruct e1, e2, e3; simpl in *; repnd; subst; dands; tcsp; eauto 3 with slow; ginv.
Qed.
Hint Resolve same_library_entries_trans : slow.

Lemma same_library_entries_preserves_inf_entry_extends {o} :
  forall e (e1 e2 : @library_entry o),
    same_library_entries e1 e2
    -> inf_entry_extends e e2
    -> inf_entry_extends e e1.
Proof.
  introv same i.
  destruct e, e1, e2; simpl in *; repnd; subst; tcsp; ginv.

  { dands; auto; eauto 3 with slow. }

  { inversion same; subst; dands; auto. }
Qed.
Hint Resolve same_library_entries_preserves_inf_entry_extends : slow.

Lemma same_library_entries_preserves_not_inf_matching_entries {o} :
  forall e (e1 e2 : @library_entry o),
    same_library_entries e1 e2
    -> ~ inf_matching_entries e e2
    -> ~ inf_matching_entries e e1.
Proof.
  introv same nm m.
  destruct nm.
  destruct e, e1, e2; simpl in *; repnd; subst; tcsp; ginv.
Qed.
Hint Resolve same_library_entries_preserves_not_inf_matching_entries : slow.

Lemma same_library_entries_preserves_entry_in_inf_library_extends {o} :
  forall e1 e2 n (lib : @inf_library o),
    same_library_entries e1 e2
    -> entry_in_inf_library_extends e2 n lib
    -> entry_in_inf_library_extends e1 n lib.
Proof.
  induction n; introv same i; simpl in *; tcsp;[].
  repndors; repnd; [left|right]; eauto 3 with slow.
  dands; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_preserves_entry_in_inf_library_extends : slow.

Lemma implies_is_nat_restriction_swap {o} :
  forall sw (restr : @ChoiceSeqRestriction o),
    is_nat_restriction restr
    -> is_nat_restriction (swap_cs_choice_seq_restr sw restr).
Proof.
  introv isn.
  unfold is_nat_restriction in *.
  destruct restr in *; simpl in *; tcsp.
  repnd; dands; introv.
  { unfold swap_cs_default.
    rewrite isn0; simpl; apply cterm_eq; simpl; auto. }
  { unfold swap_cs_restriction_pred; simpl.
    rewrite isn; autorewrite with slow; tcsp. }
Qed.
Hint Resolve implies_is_nat_restriction_swap : slow.

Lemma swap_cs_cterm_bool_implies {o} :
  forall sw (v : @CTerm o) b,
    swap_cs_cterm sw v = mkc_boolean b
    -> v = mkc_boolean b.
Proof.
  introv h.
  destruct v; simpl in *; tcsp.
  unfold mkc_boolean in *.
  apply cterm_eq; simpl.
  destruct b; simpl;
    destruct x as [z|op bs]; simpl in *; inversion h as [xx]; clear h;
      destruct op; ginv; destruct c; ginv;
        unfold nobnd, mk_axiom in *;
        repeat (destruct bs; simpl in *; tcsp; GC);
        destruct b; simpl in *; destruct l; simpl in *; ginv;
          destruct n as [z|op bs]; simpl in *; ginv;
            repeat (destruct bs; simpl in *; ginv);
            destruct op; ginv; destruct c; ginv.
Qed.

Lemma swap_cs_term_bool {o} :
  forall b sw,
    @swap_cs_cterm o sw (mkc_boolean b) = mkc_boolean b.
Proof.
  introv; apply cterm_eq; auto.
  destruct b; simpl; auto.
Qed.
Hint Rewrite @swap_cs_term_bool : slow.

Lemma is_bool_swap_cs_cterm {o} :
  forall sw n (v : @ChoiceSeqVal o),
    is_bool n (swap_cs_cterm sw v) <-> is_bool n v.
Proof.
  introv.
  unfold is_bool.
  split; intro h; exrepnd.
  { apply swap_cs_cterm_bool_implies in h0; subst; simpl in *; eauto. }
  { subst; autorewrite with slow; eauto. }
Qed.
Hint Rewrite @is_bool_swap_cs_cterm : slow.

Lemma implies_is_bool_restriction_swap {o} :
  forall sw (restr : @ChoiceSeqRestriction o),
    is_bool_restriction restr
    -> is_bool_restriction (swap_cs_choice_seq_restr sw restr).
Proof.
  introv isn.
  unfold is_bool_restriction in *.
  destruct restr in *; simpl in *; tcsp.
  repnd; dands; introv.
  { unfold swap_cs_default.
    rewrite isn0; simpl; apply cterm_eq; simpl; auto. }
  { unfold swap_cs_restriction_pred; simpl.
    rewrite isn; autorewrite with slow; tcsp. }
Qed.
Hint Resolve implies_is_bool_restriction_swap : slow.

Lemma implies_is_nat_seq_restriction_swap {o} :
  forall l sw (restr : @ChoiceSeqRestriction o),
    is_nat_seq_restriction l restr
    -> is_nat_seq_restriction l (swap_cs_choice_seq_restr sw restr).
Proof.
  introv isn.
  unfold is_nat_seq_restriction in *.
  destruct restr in *; simpl in *; tcsp.
  repnd; dands; introv.
  { introv len.
    unfold swap_cs_default.
    pose proof (isn0 n) as isn0; autodimp isn0 hyp.
    unfold cterm_is_nth in *; exrepnd; allrw.
    eexists; dands; eauto.
    autorewrite with slow; auto. }
  { introv len.
    unfold swap_cs_default.
    rewrite isn1; auto; rewrite mkc_zero_eq; autorewrite with slow; auto. }
  { introv len.
    unfold swap_cs_restriction_pred.
    rewrite isn2; auto.
    autorewrite with slow; tcsp. }
  { introv len.
    unfold swap_cs_restriction_pred.
    rewrite isn; auto; autorewrite with slow; tcsp. }
Qed.
Hint Resolve implies_is_nat_seq_restriction_swap : slow.

Lemma swap_correct_restriction {o} :
  forall sw name (restr : @ChoiceSeqRestriction o),
    name = swap_cs sw name
    -> correct_restriction name restr
    -> correct_restriction (swap_cs sw name) (swap_cs_choice_seq_restr sw restr).
Proof.
  introv eqn cor.
  unfold correct_restriction in *.
  rewrite <- eqn.
  destruct name as [name kind]; simpl in *.
  destruct kind; simpl in *; boolvar; subst; simpl in *; tcsp; eauto 3 with slow.
Qed.
Hint Resolve swap_correct_restriction : slow.

Lemma swap_choice_sequence_satisfies_restriction {o} :
  forall sw (vals : @ChoiceSeqVals o) restr,
    choice_sequence_satisfies_restriction vals restr
    -> choice_sequence_satisfies_restriction
         (swap_cs_choice_seq_vals sw vals)
         (swap_cs_choice_seq_restr sw restr).
Proof.
  introv sat.
  unfold swap_cs_choice_seq_vals.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *.

  - introv sel.
    rewrite select_map in sel.
    apply option_map_Some in sel; exrepnd; subst; simpl in *.
    applydup sat in sel1.
    unfold swap_cs_restriction_pred; autorewrite with slow; auto.

  - introv h.
    autorewrite with list in *.
    applydup sat in h.
    rewrite select_map.
    unfold ChoiceSeqVal in *; rewrite h0; simpl; auto.
Qed.
Hint Resolve swap_choice_sequence_satisfies_restriction : slow.

Lemma swap_safe_choice_sequence_entry_same_name {o} :
  forall name sw (entry : @ChoiceSeqEntry o),
    name = swap_cs sw name
    -> safe_choice_sequence_entry name entry
    -> safe_choice_sequence_entry (swap_cs sw name) (swap_cs_choice_seq_entry sw entry).
Proof.
  introv eqn safe.
  unfold safe_choice_sequence_entry in *.
  destruct entry as [vals restr]; simpl in *; repnd.
  dands; eauto 3 with slow.
Qed.
Hint Resolve swap_safe_choice_sequence_entry_same_name : slow.

Lemma swap_safe_choice_sequence_entry_normalize {o} :
  forall name sw (entry : @ChoiceSeqEntry o),
    sane_swapping sw
    -> name <> swap_cs sw name
    -> safe_choice_sequence_entry name entry
    -> safe_choice_sequence_entry (swap_cs sw name) entry
    -> safe_choice_sequence_entry
         (swap_cs sw name)
         (normalize_choice_seq_entry
            (swap_cs sw name)
            (swap_cs_choice_seq_entry sw entry)).
Proof.
  introv sane eqn safe safesw.
  unfold normalize_choice_seq_entry.
  unfold safe_choice_sequence_entry in *.
  destruct entry as [vals restr]; simpl in *; repnd; GC.
  unfold swap_cs_choice_seq_vals.
  destruct sw as [n1 n2]; simpl in *.
  boolvar; subst; tcsp;[|].

  { destruct n2 as [n2 k2]; simpl in *.
    unfold cs_name2restr; simpl.
    destruct k2;[|].

    { unfold correct_restriction in safesw0; simpl in *.
      boolvar; subst; simpl in *; dands; eauto 3 with slow; GC;[| | |].

      { introv sel.
        rewrite select_map in sel.
        apply option_map_Some in sel; exrepnd; subst.
        autorewrite with slow.
        destruct restr; simpl in *; tcsp; repnd;[].
        apply safe in sel1.
        apply safesw0 in sel1; auto. }

      { introv sel.
        rewrite select_map in sel.
        apply option_map_Some in sel; exrepnd; subst; simpl in *.
        autorewrite with slow.
        destruct restr; simpl in *; tcsp; repnd;[].
        apply safe in sel1.
        apply safesw0 in sel1; auto. }

      { unfold correct_restriction; simpl; boolvar; tcsp. }

      { unfold choice_sequence_satisfies_restriction; simpl.
        unfold swap_cs_choice_seq_restr; simpl.
        destruct restr; autorewrite with list slow.

        { introv sel.
          rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst.
          simpl in *.
          unfold swap_cs_restriction_pred; simpl; autorewrite with slow.
          apply safe; auto. }

        { introv h.
          rewrite select_map.
          unfold choice_sequence_satisfies_restriction in *.
          applydup safe in h; unfold ChoiceSeqVal in *; rewrite h0; simpl; auto. } } }

    { unfold correct_restriction in *; simpl in *.
      destruct n1 as [n1 k1]; simpl in *.
      destruct k1; simpl in *; boolvar; subst; simpl in *; dands; eauto 3 with slow; tcsp;[|].

      { introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst.
        unfold natSeq2restrictionPred; simpl.
        unfold is_nat_seq_restriction in safesw0.
        unfold is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        applydup safe in sel1.
        remember (select n l) as sel; symmetry in Heqsel; destruct sel; simpl.

        { pose proof (safesw3 n a) as q; autodimp q hyp; eauto 3 with slow.
          apply q in sel0.
          unfold cterm_is_nth in sel0.
          rewrite Heqsel in sel0; exrepnd; ginv; autorewrite with slow; auto. }

        { autorewrite with slow.
          apply safe0 in sel0; auto. } }

      { introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst; simpl in *.
        unfold natSeq2restrictionPred; simpl.
        unfold is_nat_seq_restriction in safesw0.
        unfold is_bool_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        applydup safe in sel1.
        remember (select n l) as sel; symmetry in Heqsel; destruct sel; simpl.

        { pose proof (safesw3 n a) as q; autodimp q hyp; eauto 3 with slow.
          apply q in sel0.
          unfold cterm_is_nth in sel0.
          rewrite Heqsel in sel0; exrepnd; ginv; autorewrite with slow; auto. }

        { apply nth_select2 in Heqsel.
          pose proof (safesw0 n a) as q; autodimp q hyp.
          apply q in sel0.
          autorewrite with slow; auto. } } } }

  { GC.
    destruct n1 as [n1 k1]; simpl in *.
    unfold cs_name2restr; simpl.
    destruct k1;[|].

    { unfold correct_restriction in safesw0; simpl in *.
      boolvar; subst; simpl in *; dands; eauto 3 with slow; GC;[| | |].

      { introv sel.
        rewrite select_map in sel.
        apply option_map_Some in sel; exrepnd; subst.
        autorewrite with slow.
        destruct restr; simpl in *; tcsp; repnd;[].
        apply safe in sel1.
        apply safesw0 in sel1; auto. }

      { introv sel.
        rewrite select_map in sel.
        apply option_map_Some in sel; exrepnd; subst; simpl in *.
        autorewrite with slow.
        destruct restr; simpl in *; tcsp; repnd;[].
        apply safe in sel1.
        apply safesw0 in sel1; auto. }

      { unfold correct_restriction; simpl; boolvar; tcsp. }

      { unfold choice_sequence_satisfies_restriction; simpl.
        unfold swap_cs_choice_seq_restr; simpl.
        destruct restr; autorewrite with list slow.

        { introv sel.
          rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst.
          simpl in *.
          unfold swap_cs_restriction_pred; simpl; autorewrite with slow.
          apply safe; auto. }

        { introv h.
          rewrite select_map.
          unfold choice_sequence_satisfies_restriction in *.
          applydup safe in h; unfold ChoiceSeqVal in *; rewrite h0; simpl; auto. } } }

    { unfold correct_restriction in *; simpl in *.
      destruct n2 as [n2 k2]; simpl in *.
      destruct k2; simpl in *; boolvar; subst; simpl in *; dands; eauto 3 with slow; tcsp;[|].

      { introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst.
        unfold natSeq2restrictionPred; simpl.
        unfold is_nat_seq_restriction in safesw0.
        unfold is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        applydup safe in sel1.
        remember (select n0 l) as sel; symmetry in Heqsel; destruct sel; simpl.

        { pose proof (safesw3 n0 a) as q; autodimp q hyp; eauto 3 with slow.
          apply q in sel0.
          unfold cterm_is_nth in sel0.
          rewrite Heqsel in sel0; exrepnd; ginv; autorewrite with slow; auto. }

        { autorewrite with slow.
          apply safe0 in sel0; auto. } }

      { introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst; simpl in *.
        unfold natSeq2restrictionPred; simpl.
        unfold is_nat_seq_restriction in safesw0.
        unfold is_bool_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        applydup safe in sel1.
        remember (select n0 l) as sel; symmetry in Heqsel; destruct sel; simpl.

        { pose proof (safesw3 n0 a) as q; autodimp q hyp; eauto 3 with slow.
          apply q in sel0.
          unfold cterm_is_nth in sel0.
          rewrite Heqsel in sel0; exrepnd; ginv; autorewrite with slow; auto. }

        { apply nth_select2 in Heqsel.
          pose proof (safesw0 n0 a) as q; autodimp q hyp.
          apply q in sel0.
          autorewrite with slow; auto. } } } }
Qed.
Hint Resolve swap_safe_choice_sequence_entry_normalize : slow.

Lemma swap_normalize_safe_choice_sequence_entry {o} :
  forall name sw (entry : @ChoiceSeqEntry o),
    sane_swapping sw
    -> safe_choice_sequence_entry name entry
    -> safe_choice_sequence_entry (swap_cs sw name) entry
    -> safe_choice_sequence_entry
         (swap_cs sw name)
         (swap_cs_choice_seq_entry_normalize name (swap_cs sw name) sw entry).
Proof.
  introv sane safe safe'.
  unfold swap_cs_choice_seq_entry_normalize; boolvar; subst; eauto 3 with slow.
Qed.
Hint Resolve swap_normalize_safe_choice_sequence_entry : slow.

Definition safe_library_entry_sw {o} (sw : cs_swap) (e : @library_entry o) :=
  match e with
  | lib_cs name cse =>
    safe_choice_sequence_entry (swap_cs sw name) cse
  | _ => True
  end.

Definition safe_library_sw {o} (sw : cs_swap) (lib : @library o) :=
  forall entry, entry_in_library entry lib -> safe_library_entry_sw sw entry.

Lemma swap_safe_library_entry {o} :
  forall sw (entry : @library_entry o),
    sane_swapping sw
    -> safe_library_entry entry
    -> safe_library_entry_sw sw entry
    -> safe_library_entry (swap_cs_lib_entry sw entry).
Proof.
  introv sane safe.
  destruct entry; simpl in *; tcsp.
  apply swap_normalize_safe_choice_sequence_entry; auto.
Qed.
Hint Resolve swap_safe_library_entry : slow.

Lemma swap_is_primitive_kind :
  forall sw name,
    sane_swapping sw
    -> is_primitive_kind name
    -> is_primitive_kind (swap_cs sw name).
Proof.
  introv sane isk.
  unfold is_primitive_kind in *.
  destruct sw as [n1 n2]; simpl in *; boolvar; subst; tcsp.

  { destruct n2 as [n2 k2]; simpl; auto.
    unfold compatible_choice_sequences in *; simpl in *.
    destruct k2; simpl; auto.
    destruct n1 as [n1 k1]; simpl in *.
    destruct k1; simpl in *; subst; tcsp. }

  { destruct n2 as [n2 k2]; simpl; auto.
    unfold compatible_choice_sequences in *; simpl in *.
    destruct k2; simpl in *; auto.

    { unfold compatible_cs_kinds in *; simpl in *.
      destruct n1 as [n1 k1]; simpl in *.
      destruct k1; simpl in *; subst; tcsp. }

    { unfold compatible_cs_kinds in *; simpl in *.
      destruct n1 as [n1 k1]; simpl in *.
      destruct k1; simpl in *; subst; tcsp. } }
Qed.
Hint Resolve swap_is_primitive_kind : slow.

Lemma swap_is_default_choice_seq_entry {o} :
  forall sw (entry : @ChoiceSeqEntry o),
    is_default_choice_seq_entry entry
    -> is_default_choice_seq_entry (swap_cs_choice_seq_entry sw entry).
Proof.
  introv isdef.
  unfold is_default_choice_seq_entry in *.
  destruct entry as [vals restr];simpl in *.
  unfold is_default_choice_sequence in *.
  unfold swap_cs_choice_seq_vals.
  destruct restr; simpl in *; tcsp.

  { introv sel.
    rewrite select_map in sel; rewrite option_map_Some in sel; exrepnd; subst.
    applydup isdef in sel1; subst; auto. }

  { introv sel.
    rewrite select_map in sel; rewrite option_map_Some in sel; exrepnd; subst.
    applydup isdef in sel1; subst; auto. }
Qed.
Hint Resolve swap_is_default_choice_seq_entry : slow.

Lemma normalize_swap_is_default_choice_seq_entry {o} :
  forall sw name (entry : @ChoiceSeqEntry o),
    name <> swap_cs sw name
    -> safe_choice_sequence_entry (swap_cs sw name) entry
    -> is_default_choice_seq_entry entry
    -> is_default_choice_seq_entry
         (normalize_choice_seq_entry
            (swap_cs sw name)
            (swap_cs_choice_seq_entry sw entry)).
Proof.
  introv dsw safe isdef.
  unfold normalize_choice_seq_entry.
  unfold swap_cs_choice_seq_entry.
  destruct entry as [vals restr]; simpl.
  destruct sw as [n1 n2]; simpl; repeat (boolvar; simpl in *; subst; tcsp); repnd; GC; tcsp;[|].

  { destruct n2 as [n2 k2]; simpl in *; unfold cs_name2restr; simpl.
    destruct k2; simpl in *; boolvar; subst; tcsp;[| | |].

    { unfold is_default_choice_seq_entry; simpl.
      unfold swap_cs_choice_seq_vals.
      introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd.
      simpl in *; subst.
      unfold is_default_choice_sequence in isdef.
      unfold compatible_choice_sequences in *; simpl in *.
      unfold correct_restriction in *; simpl in *; repnd.
      destruct restr; simpl in *; tcsp;[].
      apply isdef in sel1; subst.
      repnd; allrw.
      rewrite mkc_zero_eq; autorewrite with slow; auto. }

    { repnd.
      unfold is_default_choice_seq_entry; simpl.
      unfold swap_cs_choice_seq_vals.
      introv sel; rewrite select_map in sel; rewrite option_map_Some in sel; exrepnd; subst.
      unfold correct_restriction in *; simpl in *.
      unfold is_default_choice_sequence in *.
      unfold choice_sequence_satisfies_restriction in *.
      unfold compatible_choice_sequences in *; simpl in *.
      destruct restr; simpl in *; repnd; tcsp;[].
      apply isdef in sel1; subst.
      rewrite safe1.
      rewrite swap_cs_cterm_if_nodefsc; simpl; auto.
      repeat constructor. }

    { repnd; GC.
      unfold is_default_choice_seq_entry; simpl.
      unfold swap_cs_choice_seq_vals.
      unfold is_default_choice_sequence; simpl.
      unfold correct_restriction in *; simpl in *.
      destruct restr; simpl in *; boolvar; subst; tcsp.

      { introv sel.
        rewrite select_map in sel; rewrite option_map_Some in sel; exrepnd; subst.
        apply isdef in sel1; subst; auto. }

      { introv sel.
        rewrite select_map in sel; rewrite option_map_Some in sel; exrepnd; subst.
        apply isdef in sel1; subst; auto. } }

    { repnd; GC.
      unfold is_default_choice_seq_entry; simpl.
      unfold swap_cs_choice_seq_vals.
      unfold is_default_choice_sequence; simpl.
      unfold correct_restriction in *; simpl in *.
      destruct restr; simpl in *; boolvar; subst; tcsp.
      introv sel.
      rewrite select_map in sel; rewrite option_map_Some in sel; exrepnd; subst.
      applydup isdef in sel1; subst; auto.
      unfold natSeq2default.
      remember (select n l) as sel; symmetry in Heqsel; destruct sel.

      { pose proof (safe1 n) as q; autodimp q hyp; eauto 3 with slow.
        unfold cterm_is_nth in q; rewrite Heqsel in q; exrepnd; ginv.
        rewrite q0; autorewrite with slow; auto. }

      { applydup @nth_select2 in Heqsel.
        pose proof (safe2 n) as q; autodimp q hyp; try omega; rewrite q.
        rewrite mkc_zero_eq; autorewrite with slow; auto. } } }

  { destruct n1 as [n1 k1]; simpl in *; unfold cs_name2restr; simpl.
    destruct k1; simpl in *; boolvar; subst; tcsp;[| | |].

    { unfold is_default_choice_seq_entry; simpl.
      unfold swap_cs_choice_seq_vals.
      introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd.
      simpl in *; subst.
      unfold is_default_choice_sequence in isdef.
      unfold compatible_choice_sequences in *; simpl in *.
      unfold correct_restriction in *; simpl in *; repnd.
      destruct restr; simpl in *; tcsp;[].
      apply isdef in sel1; subst.
      repnd; allrw.
      rewrite mkc_zero_eq; autorewrite with slow; auto. }

    { repnd.
      unfold is_default_choice_seq_entry; simpl.
      unfold swap_cs_choice_seq_vals.
      introv sel; rewrite select_map in sel; rewrite option_map_Some in sel; exrepnd; subst.
      unfold correct_restriction in *; simpl in *.
      unfold is_default_choice_sequence in *.
      unfold choice_sequence_satisfies_restriction in *.
      unfold compatible_choice_sequences in *; simpl in *.
      destruct restr; simpl in *; repnd; tcsp;[].
      apply isdef in sel1; subst.
      rewrite safe1.
      rewrite swap_cs_cterm_if_nodefsc; simpl; auto.
      repeat constructor. }

    { repnd; GC.
      unfold is_default_choice_seq_entry; simpl.
      unfold swap_cs_choice_seq_vals.
      unfold is_default_choice_sequence; simpl.
      unfold correct_restriction in *; simpl in *.
      destruct restr; simpl in *; boolvar; subst; tcsp.

      { introv sel.
        rewrite select_map in sel; rewrite option_map_Some in sel; exrepnd; subst.
        apply isdef in sel1; subst; auto. }

      { introv sel.
        rewrite select_map in sel; rewrite option_map_Some in sel; exrepnd; subst.
        apply isdef in sel1; subst; auto. } }

    { repnd; GC.
      unfold is_default_choice_seq_entry; simpl.
      unfold swap_cs_choice_seq_vals.
      unfold is_default_choice_sequence; simpl.
      unfold correct_restriction in *; simpl in *.
      destruct restr; simpl in *; boolvar; subst; tcsp.
      introv sel.
      rewrite select_map in sel; rewrite option_map_Some in sel; exrepnd; subst.
      applydup isdef in sel1; subst; auto.
      unfold natSeq2default.
      remember (select n l) as sel; symmetry in Heqsel; destruct sel.

      { pose proof (safe1 n) as q; autodimp q hyp; eauto 3 with slow.
        unfold cterm_is_nth in q; rewrite Heqsel in q; exrepnd; ginv.
        rewrite q0; autorewrite with slow; auto. }

      { applydup @nth_select2 in Heqsel.
        pose proof (safe2 n) as q; autodimp q hyp; try omega; rewrite q.
        rewrite mkc_zero_eq; autorewrite with slow; auto. } } }
Qed.

Lemma swap_normalize_is_default_choice_seq_entry {o} :
  forall name sw (entry : @ChoiceSeqEntry o),
    safe_choice_sequence_entry (swap_cs sw name) entry
    -> is_default_choice_seq_entry entry
    -> is_default_choice_seq_entry
         (swap_cs_choice_seq_entry_normalize name (swap_cs sw name) sw entry).
Proof.
  introv safe isdef.
  unfold swap_cs_choice_seq_entry_normalize.
  boolvar; eauto 3 with slow.
  apply normalize_swap_is_default_choice_seq_entry; auto.
Qed.
Hint Resolve swap_normalize_is_default_choice_seq_entry : slow.

Lemma swap_is_cs_default_entry {o} :
  forall sw (entry : @library_entry o),
    sane_swapping sw
    -> safe_library_entry_sw sw entry
    -> is_cs_default_entry entry
    -> is_cs_default_entry (swap_cs_lib_entry sw entry).
Proof.
  introv sane safe def.
  unfold is_cs_default_entry in *.
  destruct entry; simpl in *; tcsp; repnd.
  dands; eauto 3 with slow.
Qed.
Hint Resolve swap_is_cs_default_entry : slow.

Lemma swap_entry_in_inf_library_default {o} :
  forall sw entry (ilib : @inf_library o),
    sane_swapping sw
    -> safe_library_entry_sw sw entry
    -> entry_in_inf_library_default entry ilib
    -> entry_in_inf_library_default (swap_cs_lib_entry sw entry) (swap_cs_inf_lib sw ilib).
Proof.
  introv sane safe def; unfold entry_in_inf_library_default in *; repnd.
  dands; eauto 3 with slow;[].
  introv.
  unfold swap_cs_inf_lib; autorewrite with slow; auto.
Qed.
Hint Resolve swap_entry_in_inf_library_default : slow.

Lemma entry_in_swap_library_implies {o} :
  forall sw entry (lib : @library o),
    entry_in_library entry (swap_cs_lib sw lib)
    -> exists e,
      entry_in_library e lib
      /\ entry = swap_cs_lib_entry sw e.
Proof.
  induction lib; introv h; simpl in *; tcsp;[].
  repndors; repnd; subst; simpl in *; auto.

  { exists a; dands; tcsp. }

  autodimp IHlib hyp; exrepnd; subst; simpl in *.
  exists e; dands; tcsp.
  right; dands; tcsp.
  autorewrite with slow in *; auto.
Qed.

Lemma implies_swap_inf_lib_extends_ext_entries {o} :
  forall sw infLib (lib : @library o),
    sane_swapping sw
    -> safe_library_sw sw lib
    -> inf_lib_extends_ext_entries infLib lib
    -> inf_lib_extends_ext_entries (swap_cs_inf_lib sw infLib) (swap_cs_lib sw lib).
Proof.
  introv sane safe ext i.
  applydup @entry_in_swap_library_implies in i; exrepnd; subst; simpl in *.
  applydup ext in i0.
  repndors; exrepnd;[left; exists n|right].

  { apply (swap_entry_in_inf_library_extends sw) in i2; auto. }

  { apply (swap_entry_in_inf_library_default sw) in i1; auto; eauto 3 with slow. }
Qed.
Hint Resolve implies_swap_inf_lib_extends_ext_entries : slow.

Lemma matching_inf_entries_swap_iff {o} :
  forall (sw : cs_swap) e1 (e2 : @inf_library_entry o),
    matching_inf_entries (swap_cs_inf_lib_entry sw e1) (swap_cs_inf_lib_entry sw e2)
    <-> matching_inf_entries e1 e2.
Proof.
  introv.
  unfold matching_inf_entries; simpl.
  destruct e1, e2; simpl in *; tcsp.
  split; intro h; subst; ginv; tcsp.
  apply swap_cs_inj in h; auto.
Qed.
Hint Rewrite @matching_inf_entries_swap_iff : slow.

Lemma swap_entry_in_inf_library_n_right {o} :
  forall sw entry n (ilib : @inf_library o),
    entry_in_inf_library_n n entry (swap_cs_inf_lib sw ilib)
    -> exists e,
      entry = swap_cs_inf_lib_entry sw e
      /\ entry_in_inf_library_n n e ilib.
Proof.
  induction n; introv i; simpl in *; tcsp;[].
  repndors; repnd; subst; simpl in *; auto.

  { exists (ilib 0); dands; tcsp. }

  pose proof (IHn (shift_inf_lib ilib)) as IHn; autodimp IHn hyp;[].
  exrepnd; subst.
  exists e; dands; tcsp.
  right; dands; auto.
  intro xx; destruct i0.
  apply matching_inf_entries_swap_iff; auto.
Qed.

Lemma swap_correct_restriction0 {o} :
  forall sw name (restr : @ChoiceSeqRestriction o),
    correct_restriction name restr
    -> correct_restriction name (swap_cs_choice_seq_restr sw restr).
Proof.
  introv cor.
  unfold correct_restriction in *.
  destruct name as [name kind]; simpl in *.
  destruct sw as [n1 n2]; simpl.
  destruct kind; simpl in *; boolvar; subst; simpl in *; tcsp; eauto 3 with slow.
Qed.
Hint Resolve swap_correct_restriction0 : slow.

Lemma swap_safe_choice_sequence_entry {o} :
  forall name sw (entry : @ChoiceSeqEntry o),
    safe_choice_sequence_entry name entry
    -> safe_choice_sequence_entry name (swap_cs_choice_seq_entry sw entry).
Proof.
  introv safe.
  unfold safe_choice_sequence_entry in *.
  destruct entry as [vals restr]; simpl in *; repnd.
  dands; eauto 3 with slow.
Qed.
Hint Resolve swap_safe_choice_sequence_entry : slow.

Lemma swap_safe_choice_sequence_entry_normalize2 {o} :
  forall name sw (entry : @ChoiceSeqEntry o),
    sane_swapping sw
    -> name <> swap_cs sw name
    -> safe_choice_sequence_entry name entry
    -> safe_choice_sequence_entry (swap_cs sw name) entry
    -> safe_choice_sequence_entry
         name
         (normalize_choice_seq_entry
            (swap_cs sw name)
            (swap_cs_choice_seq_entry sw entry)).
Proof.
  introv sane eqn safe safesw.
  unfold normalize_choice_seq_entry.
  unfold safe_choice_sequence_entry in *.
  destruct entry as [vals restr]; simpl in *; repnd; GC.
  unfold swap_cs_choice_seq_vals.
  destruct sw as [n1 n2]; simpl in *.
  boolvar; subst; tcsp;[|].

  { destruct n2 as [n2 k2]; simpl in *.
    unfold cs_name2restr; simpl.
    destruct k2;[|].

    { unfold correct_restriction in safesw0; simpl in *.
      boolvar; subst; simpl in *; dands; eauto 3 with slow;GC;[| |].

      { introv sel.
        rewrite select_map in sel.
        apply option_map_Some in sel; exrepnd; subst.
        autorewrite with slow.
        destruct restr; simpl in *; tcsp; repnd;[].
        apply safe in sel1.
        apply safesw0 in sel1; auto. }

      { introv sel.
        rewrite select_map in sel.
        apply option_map_Some in sel; exrepnd; subst; simpl in *.
        autorewrite with slow.
        destruct restr; simpl in *; tcsp; repnd;[].
        apply safe in sel1.
        apply safesw0 in sel1; auto. }

      { unfold choice_sequence_satisfies_restriction; simpl.
        unfold swap_cs_choice_seq_restr; simpl.
        destruct restr; autorewrite with list slow.

        { introv sel.
          rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst.
          simpl in *.
          unfold swap_cs_restriction_pred; simpl; autorewrite with slow.
          apply safe; auto. }

        { introv h.
          rewrite select_map.
          unfold choice_sequence_satisfies_restriction in *.
          applydup safe in h; unfold ChoiceSeqVal in *; rewrite h0; simpl; auto. } } }

    { unfold correct_restriction in *; simpl in *.
      destruct n1 as [n1 k1]; simpl in *.
      unfold compatible_choice_sequences in *; simpl in *.
      unfold compatible_cs_kinds in *; simpl in *.
      destruct k1; simpl in *; boolvar; subst; simpl in *; dands; eauto 3 with slow; tcsp; GC.

      { introv; unfold natSeq2default.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd.
        remember (select n l) as sel; symmetry in Heqsel; destruct sel; simpl; auto.
        pose proof (safesw1 n) as q; autodimp q hyp; eauto 3 with slow.
        unfold cterm_is_nth in q; rewrite Heqsel in q; exrepnd; ginv. }

      { introv; unfold natSeq2restrictionPred.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd; tcsp.
        remember (select n l) as sel; symmetry in Heqsel; destruct sel; simpl; auto; tcsp.
        split; introv h; subst; eauto 3 with slow.
        pose proof (safesw3 n v) as q; autodimp q hyp; eauto 3 with slow.
        pose proof (safe0 n v) as z; apply z in h; apply q in h; clear q z.
        unfold cterm_is_nth in h; rewrite Heqsel in h.
        exrepnd; ginv. }

      { introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst.
        unfold natSeq2restrictionPred; simpl.
        unfold is_nat_seq_restriction in safesw0.
        unfold is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        applydup safe in sel1.
        remember (select n l) as sel; symmetry in Heqsel; destruct sel; simpl.

        { pose proof (safesw3 n a) as q; autodimp q hyp; eauto 3 with slow.
          apply q in sel0.
          unfold cterm_is_nth in sel0.
          rewrite Heqsel in sel0; exrepnd; ginv; autorewrite with slow; auto. }

        { autorewrite with slow.
          apply safe0 in sel0; auto. } }

      { introv h.
        unfold cterm_is_nth.
        unfold natSeq2default.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        pose proof (safe1 n) as q; autodimp q hyp.
        unfold cterm_is_nth in q; exrepnd.
        rewrite q1.
        eexists; dands; eauto.
        remember (select n l) as sel; symmetry in Heqsel; destruct sel.

        { pose proof (safesw1 n) as w; autodimp w hyp; eauto 3 with slow.
          unfold cterm_is_nth in w; rewrite Heqsel in w; exrepnd; ginv. }

        { applydup @nth_select2 in Heqsel.
          pose proof (safesw2 n) as w; autodimp w hyp; try congruence. } }

      { introv h.
        unfold cterm_is_nth.
        unfold natSeq2default.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        pose proof (safe2 n) as q; autodimp q hyp.
        remember (select n l) as sel; symmetry in Heqsel; destruct sel; auto;[].
        pose proof (safesw1 n) as w; autodimp w hyp; eauto 3 with slow.
        unfold cterm_is_nth in w; rewrite Heqsel in w; exrepnd; ginv. }

      { introv h.
        unfold natSeq2restrictionPred.
        unfold cterm_is_nth.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        pose proof (safe1 n) as q; autodimp q hyp.
        unfold cterm_is_nth in q; exrepnd; rewrite q1.
        remember (select n l) as sel; symmetry in Heqsel; destruct sel; auto.

        { pose proof (safesw1 n) as w; autodimp w hyp; eauto 3 with slow.
          unfold cterm_is_nth in w; rewrite Heqsel in w; exrepnd; ginv.
          split; intro w; subst; exrepnd; ginv.
          eexists; dands; eauto; try congruence. }

        { apply nth_select2 in Heqsel.
          split; intro w; subst; exrepnd; ginv; eauto 3 with slow;[].
          eexists; dands; eauto.
          pose proof (safesw2 n) as z; autodimp z hyp.
          pose proof (safesw0 n v) as u; apply u in w; clear u; auto.
          apply safe3 in w; auto.
          unfold cterm_is_nth in w.
          rewrite q1 in w; exrepnd; ginv. } }

      { introv h.
        unfold natSeq2restrictionPred.
        unfold cterm_is_nth.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        pose proof (safe2 n) as q; autodimp q hyp.
        remember (select n l) as sel; symmetry in Heqsel; destruct sel; tcsp;[].
        split; intro z; subst; eauto 3 with slow.
        pose proof (safe0 n v) as w; autodimp w hyp; apply w in z; clear w.
        pose proof (safesw3 n v) as w; autodimp w hyp; eauto 3 with slow.
        apply w in z; clear w.
        unfold cterm_is_nth in z; rewrite Heqsel in z; exrepnd; ginv. }

      { introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst; simpl in *.
        unfold natSeq2restrictionPred; simpl.
        unfold is_nat_seq_restriction in safesw0.
        unfold is_bool_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        applydup safe in sel1.
        remember (select n l) as sel; symmetry in Heqsel; destruct sel; simpl.

        { pose proof (safesw3 n a) as q; autodimp q hyp; eauto 3 with slow.
          apply q in sel0.
          unfold cterm_is_nth in sel0.
          rewrite Heqsel in sel0; exrepnd; ginv; autorewrite with slow; auto. }

        { apply nth_select2 in Heqsel.
          pose proof (safesw0 n a) as q; autodimp q hyp.
          apply q in sel0.
          autorewrite with slow; auto. } } } }

  { destruct n1 as [n1 k1]; simpl in *.
    unfold cs_name2restr; simpl.
    destruct k1;[|].

    { unfold correct_restriction in safesw0; simpl in *.
      boolvar; subst; simpl in *; dands; eauto 3 with slow;GC;[| |].

      { introv sel.
        rewrite select_map in sel.
        apply option_map_Some in sel; exrepnd; subst.
        autorewrite with slow.
        destruct restr; simpl in *; tcsp; repnd;[].
        apply safe in sel1.
        apply safesw0 in sel1; auto. }

      { introv sel.
        rewrite select_map in sel.
        apply option_map_Some in sel; exrepnd; subst; simpl in *.
        autorewrite with slow.
        destruct restr; simpl in *; tcsp; repnd;[].
        apply safe in sel1.
        apply safesw0 in sel1; auto. }

      { unfold choice_sequence_satisfies_restriction; simpl.
        unfold swap_cs_choice_seq_restr; simpl.
        destruct restr; autorewrite with list slow.

        { introv sel.
          rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst.
          simpl in *.
          unfold swap_cs_restriction_pred; simpl; autorewrite with slow.
          apply safe; auto. }

        { introv h.
          rewrite select_map.
          unfold choice_sequence_satisfies_restriction in *.
          applydup safe in h; unfold ChoiceSeqVal in *; rewrite h0; simpl; auto. } } }

    { unfold correct_restriction in *; simpl in *.
      destruct n2 as [n2 k2]; simpl in *.
      unfold compatible_choice_sequences in *; simpl in *.
      unfold compatible_cs_kinds in *; simpl in *.
      destruct k2; simpl in *; boolvar; subst; simpl in *; dands; eauto 3 with slow; tcsp; GC.

      { introv; unfold natSeq2default.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd.
        remember (select n0 l) as sel; symmetry in Heqsel; destruct sel; simpl; auto.
        pose proof (safesw1 n0) as q; autodimp q hyp; eauto 3 with slow.
        unfold cterm_is_nth in q; rewrite Heqsel in q; exrepnd; ginv. }

      { introv; unfold natSeq2restrictionPred.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd; tcsp.
        remember (select n0 l) as sel; symmetry in Heqsel; destruct sel; simpl; auto; tcsp.
        split; introv h; subst; eauto 3 with slow.
        pose proof (safesw3 n0 v) as q; autodimp q hyp; eauto 3 with slow.
        pose proof (safe0 n0 v) as z; apply z in h; apply q in h; clear q z.
        unfold cterm_is_nth in h; rewrite Heqsel in h.
        exrepnd; ginv. }

      { introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst.
        unfold natSeq2restrictionPred; simpl.
        unfold is_nat_seq_restriction in safesw0.
        unfold is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        applydup safe in sel1.
        remember (select n0 l) as sel; symmetry in Heqsel; destruct sel; simpl.

        { pose proof (safesw3 n0 a) as q; autodimp q hyp; eauto 3 with slow.
          apply q in sel0.
          unfold cterm_is_nth in sel0.
          rewrite Heqsel in sel0; exrepnd; ginv; autorewrite with slow; auto. }

        { autorewrite with slow.
          apply safe0 in sel0; auto. } }

      { introv h.
        unfold cterm_is_nth.
        unfold natSeq2default.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        pose proof (safe1 n0) as q; autodimp q hyp.
        unfold cterm_is_nth in q; exrepnd.
        rewrite q1.
        eexists; dands; eauto.
        remember (select n0 l) as sel; symmetry in Heqsel; destruct sel.

        { pose proof (safesw1 n0) as w; autodimp w hyp; eauto 3 with slow.
          unfold cterm_is_nth in w; rewrite Heqsel in w; exrepnd; ginv. }

        { applydup @nth_select2 in Heqsel.
          pose proof (safesw2 n0) as w; autodimp w hyp; try congruence. } }

      { introv h.
        unfold cterm_is_nth.
        unfold natSeq2default.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        pose proof (safe2 n0) as q; autodimp q hyp.
        remember (select n0 l) as sel; symmetry in Heqsel; destruct sel; auto;[].
        pose proof (safesw1 n0) as w; autodimp w hyp; eauto 3 with slow.
        unfold cterm_is_nth in w; rewrite Heqsel in w; exrepnd; ginv. }

      { introv h.
        unfold natSeq2restrictionPred.
        unfold cterm_is_nth.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        pose proof (safe1 n0) as q; autodimp q hyp.
        unfold cterm_is_nth in q; exrepnd; rewrite q1.
        remember (select n0 l) as sel; symmetry in Heqsel; destruct sel; auto.

        { pose proof (safesw1 n0) as w; autodimp w hyp; eauto 3 with slow.
          unfold cterm_is_nth in w; rewrite Heqsel in w; exrepnd; ginv.
          split; intro w; subst; exrepnd; ginv.
          eexists; dands; eauto; try congruence. }

        { apply nth_select2 in Heqsel.
          split; intro w; subst; exrepnd; ginv; eauto 3 with slow;[].
          eexists; dands; eauto.
          pose proof (safesw2 n0) as z; autodimp z hyp.
          pose proof (safesw0 n0 v) as u; apply u in w; clear u; auto.
          apply safe3 in w; auto.
          unfold cterm_is_nth in w.
          rewrite q1 in w; exrepnd; ginv. } }

      { introv h.
        unfold natSeq2restrictionPred.
        unfold cterm_is_nth.
        unfold is_nat_seq_restriction, is_nat_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        pose proof (safe2 n0) as q; autodimp q hyp.
        remember (select n0 l) as sel; symmetry in Heqsel; destruct sel; tcsp;[].
        split; intro z; subst; eauto 3 with slow.
        pose proof (safe0 n0 v) as w; autodimp w hyp; apply w in z; clear w.
        pose proof (safesw3 n0 v) as w; autodimp w hyp; eauto 3 with slow.
        apply w in z; clear w.
        unfold cterm_is_nth in z; rewrite Heqsel in z; exrepnd; ginv. }

      { introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst; simpl in *.
        unfold natSeq2restrictionPred; simpl.
        unfold is_nat_seq_restriction in safesw0.
        unfold is_bool_restriction in *.
        destruct restr; simpl in *; tcsp; repnd;[].
        applydup safe in sel1.
        remember (select n0 l) as sel; symmetry in Heqsel; destruct sel; simpl.

        { pose proof (safesw3 n0 a) as q; autodimp q hyp; eauto 3 with slow.
          apply q in sel0.
          unfold cterm_is_nth in sel0.
          rewrite Heqsel in sel0; exrepnd; ginv; autorewrite with slow; auto. }

        { apply nth_select2 in Heqsel.
          pose proof (safesw0 n0 a) as q; autodimp q hyp.
          apply q in sel0.
          autorewrite with slow; auto. } } } }
Qed.
Hint Resolve swap_safe_choice_sequence_entry_normalize2 : slow.

Lemma same_library_entries_preserves_is_cs_default_entry {o} :
  forall (e1 e2 : @library_entry o),
    same_library_entries e1 e2
    -> is_cs_default_entry e2
    -> is_cs_default_entry e1.
Proof.
  introv same ics.
  unfold is_cs_default_entry in *.
  destruct e1, e2; simpl in *; repnd; subst; tcsp; ginv; dands; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_preserves_is_cs_default_entry : slow.

Lemma same_library_entries_preserves_entry_in_inf_library_default {o} :
  forall e1 e2 (lib : @inf_library o),
    same_library_entries e1 e2
    -> entry_in_inf_library_default e2 lib
    -> entry_in_inf_library_default e1 lib.
Proof.
  introv same i.
  unfold entry_in_inf_library_default in *; repnd.
  dands; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_preserves_entry_in_inf_library_default : slow.

Lemma implies_swap_inf_lib_extends_ext_entries_right {o} :
  forall sw infLib (lib : @library o),
    sane_swapping sw
    -> safe_library lib
    -> safe_library_sw sw lib
    -> inf_lib_extends_ext_entries infLib (swap_cs_lib sw lib)
    -> inf_lib_extends_ext_entries (swap_cs_inf_lib sw infLib) lib.
Proof.
  introv sane safe safesw ext i.
  applydup (@swap_entry_in_library o sw) in i.
  applydup safe in i as safe0.
  applydup safesw in i as safe1.
  apply ext in i0.
  repndors; exrepnd;[left; exists n|right].

  { apply (swap_entry_in_inf_library_extends sw) in i1.
    pose proof (swap_cs_lib_entry_idem sw entry) as q.
    repeat (autodimp q hyp); auto;[].
    eapply same_library_entries_preserves_entry_in_inf_library_extends in i1;
      [|apply same_library_entries_sym; eauto]; auto. }

  { apply (swap_entry_in_inf_library_default sw) in i0; auto; eauto 3 with slow;
      [|destruct entry; simpl in *; tcsp;[]; autorewrite with slow;
        unfold swap_cs_choice_seq_entry_normalize; boolvar; eauto 3 with slow];[].
    pose proof (swap_cs_lib_entry_idem sw entry) as q.
    repeat (autodimp q hyp);[].
    eapply same_library_entries_preserves_entry_in_inf_library_default in i0;
      [|apply same_library_entries_sym; eauto]; auto. }
Qed.
Hint Resolve implies_swap_inf_lib_extends_ext_entries_right : slow.

Lemma implies_swap_safe_library {o} :
  forall sw (lib : @library o),
    sane_swapping sw
    -> safe_library lib
    -> safe_library_sw sw lib
    -> safe_library (swap_cs_lib sw lib).
Proof.
  introv sane safe safesw i.
  apply entry_in_swap_library_implies in i; exrepnd; subst; eauto 3 with slow.
  applydup safesw in i1; eauto 3 with slow.
Qed.
Hint Resolve implies_swap_safe_library : slow.

Definition same_inf_choice_seq_entries {o} (e1 e2 : @InfChoiceSeqEntry o) :=
  icse_vals e1 = icse_vals e2
  /\ same_restrictions (icse_restriction e1) (icse_restriction e2).

Definition same_inf_library_entries {o} (e1 e2 : @inf_library_entry o) :=
  match e1, e2 with
  | inf_lib_cs name1 e1, inf_lib_cs name2 e2 => name1 = name2 /\ same_inf_choice_seq_entries e1 e2
  | _, _ => e1 = e2
  end.

Lemma swap_cs_inf_choice_seq_vals_idem {o} :
  forall sw (vals : @InfChoiceSeqVals o),
    swap_cs_inf_choice_seq_vals sw (swap_cs_inf_choice_seq_vals sw vals) = vals.
Proof.
  introv; unfold swap_cs_inf_choice_seq_vals.
  apply functional_extensionality; introv; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_inf_choice_seq_vals_idem : slow.
Hint Resolve swap_cs_inf_choice_seq_vals_idem : slow.

Lemma swap_cs_inf_choice_seq_entry_idem {o} :
  forall sw (entry : @InfChoiceSeqEntry o),
    same_inf_choice_seq_entries
      (swap_cs_inf_choice_seq_entry
         sw
         (swap_cs_inf_choice_seq_entry sw entry))
      entry.
Proof.
  introv.
  unfold swap_cs_inf_choice_seq_entry.
  destruct entry as [vals restr]; simpl.
  autorewrite with slow.
  unfold same_inf_choice_seq_entries; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve swap_cs_inf_choice_seq_entry_idem : slow.

Lemma swap_cs_inf_choice_seq_entry_normalize_idem {o} :
  forall sw name (entry : @InfChoiceSeqEntry o),
    sane_swapping sw
    -> safe_inf_choice_sequence_entry name entry
    -> same_inf_choice_seq_entries
         (swap_cs_inf_choice_seq_entry_normalize
            (swap_cs sw name)
            name sw
            (swap_cs_inf_choice_seq_entry_normalize name (swap_cs sw name) sw entry))
         entry.
Proof.
  introv sane safe.
  unfold swap_cs_inf_choice_seq_entry_normalize.
  destruct sw as [n1 n2]; simpl.
  boolvar; subst; simpl in *; GC; eauto 3 with slow; tcsp;[|].

  { destruct entry as [vals restr]; simpl in *; repnd.
    remember (cs_name2restr n2) as opr2; symmetry in Heqopr2.
    destruct opr2; simpl in *.

    { remember (cs_name2restr n1) as opr1; symmetry in Heqopr1.
      destruct opr1; simpl in *; autorewrite with slow; eauto 3 with slow;
        unfold same_inf_choice_seq_entries; simpl; dands; eauto 3 with slow.
      apply (@compatible_choice_sequences_implies_cs_name2restr_none o) in sane; auto.
      rewrite sane in *; ginv. }

    { remember (cs_name2restr n1) as opr1; symmetry in Heqopr1.
      destruct opr1; simpl in *; autorewrite with slow; eauto 3 with slow;
        unfold same_inf_choice_seq_entries; simpl; dands; eauto 3 with slow. } }

  { destruct entry as [vals restr]; simpl in *; repnd.
    remember (cs_name2restr n1) as opr1; symmetry in Heqopr1.
    destruct opr1; simpl in *;
      remember (cs_name2restr n2) as opr2; symmetry in Heqopr2;
        destruct opr2; simpl in *;
          unfold same_inf_choice_seq_entries; simpl; dands; eauto 3 with slow;[].
    apply compatible_choice_sequences_sym in sane.
    apply (@compatible_choice_sequences_implies_cs_name2restr_none o) in sane; auto.
    rewrite sane in *; ginv. }
Qed.
Hint Resolve swap_cs_inf_choice_seq_entry_normalize_idem : slow.

Lemma swap_cs_inf_lib_entry_idem {o} :
  forall sw (e : @inf_library_entry o),
    sane_swapping sw
    -> safe_inf_library_entry e
    -> same_inf_library_entries (swap_cs_inf_lib_entry sw (swap_cs_inf_lib_entry sw e)) e.
Proof.
  introv sane safe.
  destruct e; simpl in *; autorewrite with slow; dands; auto; eauto 3 with slow; GC;[].

  remember (swap_cs_correct_abs
              sw opabs vars (swap_cs_soterm sw rhs)
              (swap_cs_correct_abs sw opabs vars rhs correct)) as w.
  clear Heqw.
  revert w.
  autorewrite with slow; introv.
  f_equal; eauto with pi.
Qed.
Hint Resolve swap_cs_inf_lib_entry_idem : slow.

Lemma entry_in_swap_inf_library_n_implies {o} :
  forall sw entry n (lib : @inf_library o),
    entry_in_inf_library_n n entry (swap_cs_inf_lib sw lib)
    -> exists e,
      entry_in_inf_library_n n e lib
      /\ entry = swap_cs_inf_lib_entry sw e.
Proof.
  induction n; introv h; simpl in *; tcsp;[].
  repndors; subst; repnd; tcsp.

  { exists (lib 0); dands; tcsp. }

  pose proof (IHn (shift_inf_lib lib)) as IHn; autodimp IHn hyp;[].
  exrepnd; subst.
  exists e; dands; tcsp.
  right; dands; auto.
  unfold swap_cs_inf_lib in *; simpl in *.
  autorewrite with slow in *; tcsp.
Qed.

Lemma swap_entry_in_inf_library_n {o} :
  forall sw entry n (lib : @inf_library o),
    entry_in_inf_library_n n entry lib
    -> entry_in_inf_library_n n (swap_cs_inf_lib_entry sw entry) (swap_cs_inf_lib sw lib).
Proof.
  induction n; introv h; simpl in *; tcsp;[].
  repndors; repnd; subst; simpl in *; auto;[].
  right.
  pose proof (IHn (shift_inf_lib lib)) as IHn; autodimp IHn hyp.
  unfold swap_cs_inf_lib; simpl.
  dands; auto; autorewrite with slow; tcsp.
Qed.
Hint Resolve swap_entry_in_inf_library_n : slow.

Lemma swap_inf_choice_sequence_satisfies_restriction {o} :
  forall sw (vals : @InfChoiceSeqVals o) restr,
    inf_choice_sequence_satisfies_restriction vals restr
    -> inf_choice_sequence_satisfies_restriction
         (swap_cs_inf_choice_seq_vals sw vals)
         (swap_cs_choice_seq_restr sw restr).
Proof.
  introv sat.
  unfold swap_cs_inf_choice_seq_vals.
  unfold inf_choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; introv; try congruence;[].
  unfold swap_cs_restriction_pred; autorewrite with slow; auto.
Qed.
Hint Resolve swap_inf_choice_sequence_satisfies_restriction : slow.

Lemma natSeq2restrictionPred_swap_cs_cterm {o} :
  forall sw l n (v : @ChoiceSeqVal o),
    natSeq2restrictionPred l n (swap_cs_cterm sw v) <-> natSeq2restrictionPred l n v.
Proof.
  introv.
  unfold natSeq2restrictionPred.
  remember (select n l) as sel; symmetry in Heqsel; destruct sel; autorewrite with slow; tcsp.
  split; intro h; subst; autorewrite with slow; auto.
  apply swap_cs_cterm_nat_implies in h; auto.
Qed.
Hint Rewrite @natSeq2restrictionPred_swap_cs_cterm : slow.

Definition safe_inf_library_entry_sw {o} sw (e : @inf_library_entry o) :=
  match e with
  | inf_lib_cs name cse => safe_inf_choice_sequence_entry (swap_cs sw name) cse
  | _ => True
  end.

Definition safe_inf_library_sw {o} sw (inflib : @inf_library o) :=
  forall entry, entry_in_inf_library entry inflib -> safe_inf_library_entry_sw sw entry.

Lemma swap_norm_inf_choice_sequence_vals_extend {o} :
  forall sw vals1 (vals2 : @ChoiceSeqVals o) l restr,
    is_nat_seq_restriction l restr
    -> choice_sequence_satisfies_restriction vals2 restr
    -> inf_choice_sequence_vals_extend vals1 vals2
    -> inf_choice_sequence_vals_extend
         (normalize_inf_choice_seq_vals l (swap_cs_inf_choice_seq_vals sw vals1))
         (swap_cs_choice_seq_vals sw vals2).
Proof.
  introv isn sat ext sel.
  unfold normalize_inf_choice_seq_vals.
  unfold swap_cs_choice_seq_vals in sel.
  rewrite select_map in sel.
  apply option_map_Some in sel; exrepnd; subst; simpl in *.
  applydup ext in sel1; subst; auto.
  unfold swap_cs_inf_choice_seq_vals.
  remember (select n l) as sel; symmetry in Heqsel; destruct sel; auto;[].
  unfold choice_sequence_satisfies_restriction, is_nat_seq_restriction in *.
  destruct restr; simpl in *; tcsp; repnd;[].
  applydup sat in sel1.
  apply isn2 in sel0; eauto 3 with slow;[].
  unfold cterm_is_nth in sel0.
  rewrite Heqsel in sel0; exrepnd; ginv.
  rewrite sel2; autorewrite with slow; auto.
Qed.
Hint Resolve swap_norm_inf_choice_sequence_vals_extend : slow.

Lemma normalize_vals_swap_inf_choice_sequence_entry_extend {o} :
  forall name sw e1 (e2 : @ChoiceSeqEntry o),
    safe_choice_sequence_entry name e2
    -> inf_choice_sequence_entry_extend e1 e2
    -> inf_choice_sequence_entry_extend
         (normalize_inf_choice_seq_entry_vals name (swap_cs_inf_choice_seq_entry sw e1))
         (normalize_choice_seq_entry name (swap_cs_choice_seq_entry sw e2)).
Proof.
  introv safe ext.
  unfold normalize_inf_choice_seq_entry_vals, normalize_choice_seq_entry.
  destruct e1, e2; simpl in *.
  unfold inf_choice_sequence_entry_extend in *; simpl in *.
  destruct name as [name kind]; simpl in *.
  unfold cs_name2restr in *; simpl in *; repnd.
  destruct kind; simpl in *; boolvar; subst; simpl in *; dands; eauto 3 with slow; tcsp.
  unfold correct_restriction in *; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve normalize_vals_swap_inf_choice_sequence_entry_extend : slow.

Lemma swap_inf_choice_sequence_entry_extend_normalize_vals {o} :
  forall name name' sw e1 (e2 : @ChoiceSeqEntry o),
    safe_choice_sequence_entry name' e2
    -> inf_choice_sequence_entry_extend e1 e2
    -> inf_choice_sequence_entry_extend
         (swap_cs_inf_choice_seq_entry_normalize_vals name name' sw e1)
         (swap_cs_choice_seq_entry_normalize name name' sw e2).
Proof.
  introv safe ext.
  unfold swap_cs_inf_choice_seq_entry_normalize_vals, swap_cs_choice_seq_entry_normalize.
  boolvar; subst; eauto 3 with slow.
Qed.
Hint Resolve swap_inf_choice_sequence_entry_extend_normalize_vals : slow.

Lemma swap_norm_inf_entry_extends {o} :
  forall sw e1 (e2 : @library_entry o),
    safe_library_entry_sw sw e2
    -> inf_entry_extends e1 e2
    -> inf_entry_extends
         (swap_cs_inf_lib_entry_normalize_vals sw e1)
         (swap_cs_lib_entry sw e2).
Proof.
  introv safe i.
  unfold inf_entry_extends; simpl in *.
  destruct e1, e2; simpl in *; repnd; subst; tcsp.
  dands; auto; eauto 2 with slow.
Qed.
Hint Resolve swap_norm_inf_entry_extends : slow.

Lemma inf_matching_entries_swap_norm_iff {o} :
  forall (sw : cs_swap) e1 (e2 : @library_entry o),
    inf_matching_entries (swap_cs_inf_lib_entry_normalize_vals sw e1) (swap_cs_lib_entry sw e2)
    <-> inf_matching_entries e1 e2.
Proof.
  introv.
  unfold inf_matching_entries; simpl.
  destruct e1, e2; simpl in *; tcsp.
  split; intro h; subst; ginv; tcsp.
  apply swap_cs_inj in h; auto.
Qed.
Hint Rewrite @inf_matching_entries_swap_norm_iff : slow.

Lemma swap_norm_entry_in_inf_library_extends {o} :
  forall sw entry n (ilib : @inf_library o),
    safe_library_entry_sw sw entry
    -> entry_in_inf_library_extends entry n ilib
    -> entry_in_inf_library_extends (swap_cs_lib_entry sw entry) n (swap_cs_inf_lib_norm sw ilib).
Proof.
  induction n; introv safe i; simpl in *; tcsp;[].
  repndors; repnd; subst; simpl in *; auto;[left|right].

  { unfold swap_cs_inf_lib_norm; eauto 3 with slow. }

  dands; eauto 3 with slow.
  unfold swap_cs_inf_lib_norm; simpl.
  autorewrite with slow; auto.
Qed.
Hint Resolve swap_norm_entry_in_inf_library_extends : slow.

Lemma satisfies_is_nat_restriction_implies {o} :
  forall restr (vals : @ChoiceSeqVals o) n v,
    is_nat_restriction restr
    -> choice_sequence_satisfies_restriction vals restr
    -> select n vals = Some v
    -> is_nat n v.
Proof.
  introv isn sat sel.
  unfold is_nat_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; tcsp; repnd.
  apply sat in sel; apply isn in sel; auto.
Qed.
Hint Resolve satisfies_is_nat_restriction_implies : slow.

Lemma satisfies_is_bool_restriction_implies {o} :
  forall restr (vals : @ChoiceSeqVals o) n v,
    is_bool_restriction restr
    -> choice_sequence_satisfies_restriction vals restr
    -> select n vals = Some v
    -> is_bool n v.
Proof.
  introv isn sat sel.
  unfold is_bool_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; tcsp; repnd.
  apply sat in sel; apply isn in sel; auto.
Qed.
Hint Resolve satisfies_is_bool_restriction_implies : slow.

Lemma natSeq2default_if_is_nat_restriction {o} :
  forall l n (restr : @ChoiceSeqRestriction o),
    is_nat_restriction restr
    -> is_nat_seq_restriction l restr
    -> @natSeq2default o l n = mkc_zero.
Proof.
  introv isn isnl.
  unfold is_nat_restriction in *.
  unfold is_nat_seq_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; tcsp; repnd.
  unfold natSeq2default.
  remember (select n l) as sel; symmetry in Heqsel; destruct sel; auto.
  pose proof (isnl0 n) as q; autodimp q hyp; eauto 3 with slow.
  unfold cterm_is_nth in *; exrepnd.
  rewrite Heqsel in q1; ginv.
Qed.
Hint Resolve natSeq2default_if_is_nat_restriction : slow.

Lemma natSeq2restrictionPred_if_is_nat_restriction {o} :
  forall l n (restr : @ChoiceSeqRestriction o) (v : @ChoiceSeqVal o),
    is_nat_restriction restr
    -> is_nat_seq_restriction l restr
    -> (natSeq2restrictionPred l n v <-> is_nat n v).
Proof.
  introv isn isnl.
  unfold is_nat_restriction in *.
  unfold is_nat_seq_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; tcsp; repnd.
  unfold natSeq2restrictionPred.
  remember (select n l) as sel; symmetry in Heqsel; destruct sel; tcsp.
  split; intro h; subst; eauto 3 with slow.
  pose proof (isnl2 n v) as q; autodimp q hyp; eauto 3 with slow.
  apply isn in h; apply q in h; clear q.
  unfold cterm_is_nth in *; exrepnd.
  rewrite Heqsel in h1; ginv.
Qed.
Hint Resolve natSeq2restrictionPred_if_is_nat_restriction : slow.

Lemma natSeq2restrictionPred_if_is_nat_restriction_select {o} :
  forall l n vals (restr : @ChoiceSeqRestriction o) (v : @ChoiceSeqVal o),
    is_nat_seq_restriction l restr
    -> choice_sequence_satisfies_restriction vals restr
    -> select n vals = Some v
    -> natSeq2restrictionPred l n v.
Proof.
  introv isnl sat sel.
  unfold is_nat_restriction in *.
  unfold is_nat_seq_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; tcsp; repnd.
  unfold natSeq2restrictionPred.
  applydup sat in sel.
  remember (select n l) as sell; symmetry in Heqsell; destruct sell; tcsp.

  { pose proof (isnl2 n v) as w; autodimp w hyp; eauto 3 with slow.
    apply w in sel0.
    unfold cterm_is_nth in sel0; rewrite Heqsell in sel0; exrepnd; ginv. }

  { applydup @nth_select2 in Heqsell.
    apply isnl; auto. }
Qed.
Hint Resolve natSeq2restrictionPred_if_is_nat_restriction_select : slow.

Lemma cterm_is_nth_if_is_nat_seq_restriction {o} :
  forall l1 l2 (restr : @ChoiceSeqRestriction o) n,
    is_nat_seq_restriction l1 restr
    -> is_nat_seq_restriction l2 restr
    -> n < length l1
    -> @cterm_is_nth o (natSeq2default l2 n) n l1.
Proof.
  introv isna isnb len.
  unfold cterm_is_nth, natSeq2default.
  unfold is_nat_seq_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; tcsp; repnd.
  pose proof (isna0 n) as q; autodimp q hyp.
  unfold cterm_is_nth in q; exrepnd.
  rewrite q1; eexists; dands; eauto.
  remember (select n l2) as sel; symmetry in Heqsel; destruct sel.

  { pose proof (isnb0 n) as z; autodimp z hyp; eauto 3 with slow.
    unfold cterm_is_nth in z; rewrite Heqsel in z; exrepnd; ginv. }

  { applydup @nth_select2 in Heqsel.
    pose proof (isnb1 n) as z; autodimp z hyp; try congruence. }
Qed.
Hint Resolve cterm_is_nth_if_is_nat_seq_restriction : slow.

Lemma natSeq2default_zero_if_is_nat_seq_restriction {o} :
  forall l1 l2 (restr : @ChoiceSeqRestriction o) n,
    is_nat_seq_restriction l1 restr
    -> is_nat_seq_restriction l2 restr
    -> length l1 <= n
    -> @natSeq2default o l2 n = mkc_zero.
Proof.
  introv isna isnb len.
  unfold cterm_is_nth, natSeq2default.
  unfold is_nat_seq_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; tcsp; repnd.
  pose proof (isna1 n) as q; autodimp q hyp.
  remember (select n l2) as sel; symmetry in Heqsel; destruct sel; auto.
  pose proof (isnb0 n) as z; autodimp z hyp; eauto 3 with slow.
  unfold cterm_is_nth in z; rewrite Heqsel in z; exrepnd; ginv.
Qed.
Hint Resolve natSeq2default_zero_if_is_nat_seq_restriction : slow.

Lemma natSeq2restrictionPred_iff_cterm_is_nth_if_is_nat_seq_restriction {o} :
  forall l1 l2 (restr : @ChoiceSeqRestriction o) n (v : @ChoiceSeqVal o),
    is_nat_seq_restriction l1 restr
    -> is_nat_seq_restriction l2 restr
    -> n < length l1
    -> natSeq2restrictionPred l2 n v <-> cterm_is_nth v n l1.
Proof.
  introv isna isnb len.
  unfold cterm_is_nth, natSeq2restrictionPred.
  unfold is_nat_seq_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; tcsp; repnd.
  pose proof (isna0 n) as q; autodimp q hyp.
  unfold cterm_is_nth in q; exrepnd; rewrite q1.
  remember (select n l2) as sel; symmetry in Heqsel; destruct sel;
    split; intro h; exrepnd; ginv; subst; eauto 3 with slow.

  { exists i; dands; auto.
    pose proof (isnb0 n) as z; autodimp z hyp; eauto 3 with slow.
    unfold cterm_is_nth in z; rewrite Heqsel in z; exrepnd; ginv. }

  { pose proof (isnb0 n) as z; autodimp z hyp; eauto 3 with slow.
    unfold cterm_is_nth in z; rewrite Heqsel in z; exrepnd; ginv. }

  { exists i; dands; auto.
    applydup @nth_select2 in Heqsel.
    pose proof (isnb n v) as z; autodimp z hyp; apply z in h; clear z.
    apply isna2 in h; auto.
    unfold cterm_is_nth in h; rewrite q1 in h; exrepnd; ginv. }
Qed.
Hint Resolve natSeq2restrictionPred_iff_cterm_is_nth_if_is_nat_seq_restriction : slow.

Lemma natSeq2restrictionPred_iff_is_nat_if_is_nat_seq_restriction {o} :
  forall l1 l2 (restr : @ChoiceSeqRestriction o) n (v : @ChoiceSeqVal o),
    is_nat_seq_restriction l1 restr
    -> is_nat_seq_restriction l2 restr
    -> length l1 <= n
    -> natSeq2restrictionPred l2 n v <-> is_nat n v.
Proof.
  introv isna isnb len.
  unfold natSeq2restrictionPred.
  unfold is_nat_seq_restriction in *.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; tcsp; repnd.
  remember (select n l2) as sel; symmetry in Heqsel; destruct sel; tcsp.
  split; intro h; subst; eauto 3 with slow.
  pose proof (isna n v) as q; apply q in h; auto; clear q.
  pose proof (isnb2 n v) as q; autodimp q hyp; eauto 3 with slow; apply q in h; clear q.
  unfold cterm_is_nth in h; rewrite Heqsel in h; exrepnd; ginv.
Qed.
Hint Resolve natSeq2restrictionPred_iff_is_nat_if_is_nat_seq_restriction : slow.

Lemma implies_safe_choice_sequence_entry_swap {o} :
  forall sw name (entry : @ChoiceSeqEntry o),
    sane_swapping sw
    -> safe_choice_sequence_entry name entry
    -> safe_choice_sequence_entry (swap_cs sw name) entry
    -> safe_choice_sequence_entry
         name
         (swap_cs_choice_seq_entry_normalize name (swap_cs sw name) sw entry).
Proof.
  introv sane safe safesw.
  destruct entry as [vals restr]; simpl in *; repnd.
  unfold swap_cs_choice_seq_entry_normalize; simpl; boolvar; simpl;
    autorewrite with slow; dands; eauto 3 with slow;[].

  destruct sw as [n1 n2]; simpl in *; boolvar; subst; simpl in *; tcsp.

  { destruct n1 as [n1 k1], n2 as [n2 k2]; unfold cs_name2restr in *; simpl in *.
    unfold compatible_choice_sequences in *; simpl in *.
    unfold correct_restriction in *; simpl in *.
    unfold swap_cs_choice_seq_vals in *; simpl in *.
    destruct k1, k2; simpl in *; tcsp; subst; boolvar; subst;
      simpl in *; tcsp; dands; eauto 3 with slow; GC;
        try (complete (introv sel; rewrite select_map in sel; apply option_map_Some in sel;
                       exrepnd; subst; autorewrite with slow; eauto 3 with slow));
        try (complete (unfold correct_restriction; simpl; dands; boolvar; subst; tcsp;
                       introv; eauto 3 with slow));[].

    unfold choice_sequence_satisfies_restriction; simpl.
    destruct restr; simpl in *; autorewrite with slow; introv; rewrite select_map; tcsp.

    { introv sel; apply option_map_Some in sel; exrepnd; subst.
      unfold swap_cs_restriction_pred; simpl; autorewrite with slow; tcsp. }

    { introv len; rewrite safe; auto. } }

  { destruct n1 as [n1 k1], n2 as [n2 k2]; unfold cs_name2restr in *; simpl in *.
    unfold compatible_choice_sequences in *; simpl in *.
    unfold correct_restriction in *; simpl in *.
    unfold swap_cs_choice_seq_vals in *; simpl in *.
    destruct k1, k2; simpl in *; tcsp; subst; boolvar; subst;
      simpl in *; tcsp; dands; eauto 3 with slow; GC;
        try (complete (introv sel; rewrite select_map in sel; apply option_map_Some in sel;
                       exrepnd; subst; autorewrite with slow; eauto 3 with slow));
        try (complete (unfold correct_restriction; simpl; dands; boolvar; subst; tcsp;
                       introv; eauto 3 with slow));[].

    unfold choice_sequence_satisfies_restriction; simpl.
    destruct restr; simpl in *; autorewrite with slow; introv; rewrite select_map; tcsp.

    { introv sel; apply option_map_Some in sel; exrepnd; subst.
      unfold swap_cs_restriction_pred; simpl; autorewrite with slow; tcsp. }

    { introv len; rewrite safe; auto. } }
Qed.
Hint Resolve implies_safe_choice_sequence_entry_swap : slow.

Lemma implies_safe_library_entry_sw_swap {o} :
  forall sw (entry : @library_entry o),
    sane_swapping sw
    -> safe_library_entry entry
    -> safe_library_entry_sw sw entry
    -> safe_library_entry_sw sw (swap_cs_lib_entry sw entry).
Proof.
  introv sane safe safesw.
  destruct entry; simpl in *; tcsp;[].
  autorewrite with slow; eauto 3 with slow.
Qed.
Hint Resolve implies_safe_library_entry_sw_swap : slow.

Lemma swap_norm_entry_in_inf_library_default {o} :
  forall sw entry (ilib : @inf_library o),
    sane_swapping sw
    -> safe_library_entry_sw sw entry
    -> entry_in_inf_library_default entry ilib
    -> entry_in_inf_library_default (swap_cs_lib_entry sw entry) (swap_cs_inf_lib_norm sw ilib).
Proof.
  introv sane safe def; unfold entry_in_inf_library_default in *; repnd.
  dands; eauto 3 with slow;[].
  introv.
  unfold swap_cs_inf_lib_norm; autorewrite with slow; auto.
Qed.
Hint Resolve swap_norm_entry_in_inf_library_default : slow.

Lemma implies_swap_norm_inf_lib_extends_ext_entries_right {o} :
  forall sw infLib (lib : @library o),
    sane_swapping sw
    -> safe_library lib
    -> safe_library_sw sw lib
    -> inf_lib_extends_ext_entries infLib (swap_cs_lib sw lib)
    -> inf_lib_extends_ext_entries (swap_cs_inf_lib_norm sw infLib) lib.
Proof.
  introv sane safe safesw ext i.
  applydup (@swap_entry_in_library o sw) in i.
  applydup safe in i as safe0.
  applydup safesw in i as safe1.
  apply ext in i0.
  repndors; exrepnd;[left; exists n|right].

  { apply (swap_norm_entry_in_inf_library_extends sw) in i1; eauto 3 with slow.
    pose proof (swap_cs_lib_entry_idem sw entry) as q.
    repeat (autodimp q hyp); auto;[].
    eapply same_library_entries_preserves_entry_in_inf_library_extends in i1;
      [|apply same_library_entries_sym; eauto]; auto. }

  { apply (swap_norm_entry_in_inf_library_default sw) in i0; auto; eauto 3 with slow;[].
    pose proof (swap_cs_lib_entry_idem sw entry) as q.
    repeat (autodimp q hyp);[].
    eapply same_library_entries_preserves_entry_in_inf_library_default in i0;
      [|apply same_library_entries_sym; eauto]; auto. }
Qed.
Hint Resolve implies_swap_norm_inf_lib_extends_ext_entries_right : slow.

Lemma matching_inf_entries_swap_norm_iff {o} :
  forall (sw : cs_swap) e1 (e2 : @inf_library_entry o),
    matching_inf_entries (swap_cs_inf_lib_entry_normalize_vals sw e1) (swap_cs_inf_lib_entry_normalize_vals sw e2)
    <-> matching_inf_entries e1 e2.
Proof.
  introv.
  unfold matching_inf_entries; simpl.
  destruct e1, e2; simpl in *; tcsp.
  split; intro h; subst; ginv; tcsp.
  apply swap_cs_inj in h; auto.
Qed.
Hint Rewrite @matching_inf_entries_swap_norm_iff : slow.

Lemma entry_in_swap_norm_inf_library_n_implies {o} :
  forall sw entry n (lib : @inf_library o),
    entry_in_inf_library_n n entry (swap_cs_inf_lib_norm sw lib)
    -> exists e,
      entry_in_inf_library_n n e lib
      /\ entry = swap_cs_inf_lib_entry_normalize_vals sw e.
Proof.
  induction n; introv h; simpl in *; tcsp;[].
  repndors; subst; repnd; tcsp.

  { exists (lib 0); dands; tcsp. }

  pose proof (IHn (shift_inf_lib lib)) as IHn; autodimp IHn hyp;[].
  exrepnd; subst.
  exists e; dands; tcsp.
  right; dands; auto.
  unfold swap_cs_inf_lib_norm in *; simpl in *.
  autorewrite with slow in *; tcsp.
Qed.

Lemma implies_safe_swap_norm_cs_inf_choice_sequence_entry {o} :
  forall name sw (entry : @InfChoiceSeqEntry o),
    sane_swapping sw
    -> safe_inf_choice_sequence_entry name entry
    -> safe_inf_choice_sequence_entry
         (swap_cs sw name)
         (swap_cs_inf_choice_seq_entry_normalize_vals name (swap_cs sw name) sw entry).
Proof.
  introv sane safe.
  destruct entry as [vals restr]; simpl in *; repnd.
  unfold safe_inf_choice_sequence_entry; simpl.
  unfold swap_cs_inf_choice_seq_entry_normalize_vals; simpl.
  boolvar; simpl; dands; eauto 3 with slow;[].

  destruct sw as [n1 n2]; simpl; repeat (boolvar; subst; simpl in *; tcsp; GC);[|];
    destruct n1 as [n1 k1]; destruct n2 as [n2 k2]; simpl in *;
      unfold cs_name2restr in *; simpl in *;[|].

  { unfold compatible_choice_sequences in *; simpl in *.
    destruct k2; boolvar; subst; simpl in *; tcsp; dands; eauto 3 with slow;[| | |].

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      destruct k1; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; try (complete (apply safe0; tcsp));[].
      pose proof (safe n0) as q.
      destruct (lt_dec n0 (length l)).
      { apply safe3 in q; auto.
        unfold cterm_is_nth in q; exrepnd; allrw; eauto 3 with slow. }
      { apply safe0 in q; try omega; auto. } }

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      destruct k1; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; try (complete (apply safe0; tcsp)). }

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      destruct k1; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; try (complete (apply safe0; tcsp)). }

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      unfold normalize_inf_choice_seq_vals.
      remember (select n0 l) as sel; symmetry in Heqsel.
      destruct sel, k1; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; GC; try (complete (apply safe0; tcsp));
          autorewrite with slow; eauto 3 with slow;
            try (complete (unfold natSeq2restrictionPred; allrw; auto));[|].

      { unfold natSeq2restrictionPred; allrw; auto; eauto 3 with slow.
        pose proof (safe n0) as q; apply safe0; auto. }

      { unfold natSeq2restrictionPred; allrw; auto; eauto 3 with slow.
        pose proof (safe n0) as q.
        destruct (lt_dec n0 (length l0)).

        { apply safe3 in q; auto.
          unfold cterm_is_nth in q; exrepnd.
          allrw; eauto 3 with slow. }

        { apply safe0 in q; auto; try omega. } } } }

  { unfold compatible_choice_sequences in *; simpl in *.
    destruct k1; boolvar; subst; simpl in *; tcsp; dands; eauto 3 with slow;[| | |].

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      destruct k2; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; try (complete (apply safe0; tcsp));[].
      pose proof (safe n) as q.
      destruct (lt_dec n (length l)).
      { apply safe3 in q; auto.
        unfold cterm_is_nth in q; exrepnd; allrw; eauto 3 with slow. }
      { apply safe0 in q; try omega; auto. } }

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      destruct k2; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; try (complete (apply safe0; tcsp)). }

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      destruct k2; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; try (complete (apply safe0; tcsp)). }

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      unfold normalize_inf_choice_seq_vals.
      remember (select n l) as sel; symmetry in Heqsel.
      destruct sel, k2; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; GC; try (complete (apply safe0; tcsp));
          autorewrite with slow; eauto 3 with slow;
            try (complete (unfold natSeq2restrictionPred; allrw; auto));[|].

      { unfold natSeq2restrictionPred; allrw; auto; eauto 3 with slow.
        pose proof (safe n) as q; apply safe0; auto. }

      { unfold natSeq2restrictionPred; allrw; auto; eauto 3 with slow.
        pose proof (safe n) as q.
        destruct (lt_dec n (length l0)).

        { apply safe3 in q; auto.
          unfold cterm_is_nth in q; exrepnd.
          allrw; eauto 3 with slow. }

        { apply safe0 in q; auto; try omega. } } } }
Qed.
Hint Resolve implies_safe_swap_norm_cs_inf_choice_sequence_entry : slow.

Lemma implies_swap_safe_inf_library {o} :
  forall sw (lib : @inf_library o),
    sane_swapping sw
    -> safe_inf_library lib
    -> safe_inf_library (swap_cs_inf_lib_norm sw lib).
Proof.
  introv sane safe i.

  destruct entry; simpl in *; tcsp;[].

  unfold entry_in_inf_library in *; repndors; exrepnd;[|].

  { apply entry_in_swap_norm_inf_library_n_implies in i0; exrepnd; subst.
    destruct e; simpl in *; ginv; eauto 3 with slow.
    pose proof (safe (inf_lib_cs name0 entry0)) as q.
    autodimp q hyp; [left; eauto|];[].
    simpl in *; eauto 3 with slow. }

  { unfold inf_entry_in_inf_library_default in i; simpl in *; repnd; eauto 3 with slow. }
Qed.
Hint Resolve implies_swap_safe_inf_library : slow.

Lemma implies_swap_inf_lib_extends_left {o} :
  forall sw infLib (lib : @library o),
    sane_swapping sw
    -> safe_library lib
    -> safe_library_sw sw lib
    -> inf_lib_extends infLib (swap_cs_lib sw lib)
    -> inf_lib_extends (swap_cs_inf_lib_norm sw infLib) lib.
Proof.
  introv sane safelib safesw ext.
  destruct ext as [ext safe].
  split; eauto 3 with slow.
  introv xx; GC.
  autodimp safe hyp; eauto 3 with slow.
Qed.
Hint Resolve implies_swap_inf_lib_extends_left : slow.

Lemma swap_choice_sequence_vals_extend {o} :
  forall sw (vals1 vals2 : @ChoiceSeqVals o),
    choice_sequence_vals_extend vals1 vals2
    -> choice_sequence_vals_extend
         (swap_cs_choice_seq_vals sw vals1)
         (swap_cs_choice_seq_vals sw vals2).
Proof.
  introv ext.
  unfold choice_sequence_vals_extend in *; exrepnd; subst.
  exists (swap_cs_choice_seq_vals sw vals).
  unfold swap_cs_choice_seq_vals; rewrite map_app; auto.
Qed.
Hint Resolve swap_choice_sequence_vals_extend : slow.

Lemma swap_choice_sequence_entry_extend {o} :
  forall name1 name2 sw (e1 e2 : @ChoiceSeqEntry o),
    choice_sequence_entry_extend e1 e2
    -> choice_sequence_entry_extend
         (swap_cs_choice_seq_entry_normalize name1 name2 sw e1)
         (swap_cs_choice_seq_entry_normalize name1 name2 sw e2).
Proof.
  introv ext.
  destruct e1 as [vals1 restr1], e2 as [vals2 restr2]; simpl in *.
  unfold choice_sequence_entry_extend in *; repnd; simpl in *.
  unfold swap_cs_choice_seq_entry_normalize; simpl; boolvar; subst; simpl in *;
    dands; eauto 3 with slow;
      remember (cs_name2restr name2) as restr2'; destruct restr2'; simpl; eauto 3 with slow.
Qed.
Hint Resolve swap_choice_sequence_entry_extend : slow.

Lemma swap_entry_extends {o} :
  forall sw (e1 e2 : @library_entry o),
    entry_extends e1 e2
    -> entry_extends (swap_cs_lib_entry sw e1) (swap_cs_lib_entry sw e2).
Proof.
  introv ext.
  unfold entry_extends in *.
  destruct e1, e2; simpl in *; tcsp; ginv;
    [|inversion ext; subst;f_equal; eauto 3 with pi];[].
  repnd; subst; dands; eauto 3 with slow.
Qed.
Hint Resolve swap_entry_extends : slow.

Lemma swap_entry_in_library_extends {o} :
  forall sw (e : @library_entry o) lib,
    entry_in_library_extends e lib
    -> entry_in_library_extends (swap_cs_lib_entry sw e) (swap_cs_lib sw lib).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; autorewrite with slow in *;[left|right];
    dands; autorewrite with slow; eauto 3 with slow.
Qed.
Hint Resolve swap_entry_in_library_extends : slow.

Lemma swap_lib_extends_entries {o} :
  forall sw (lib1 lib2 : @library o),
    lib_extends_entries lib1 lib2
    -> lib_extends_entries (swap_cs_lib sw lib1) (swap_cs_lib sw lib2).
Proof.
  introv ext i.
  apply entry_in_swap_library_implies in i; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve swap_lib_extends_entries : slow.

Definition swapping_in_library {o} (sw : cs_swap) (lib : @library o) :=
  name_in_library (fst sw) lib
  /\ name_in_library (snd sw) lib.

Lemma lib_extends_preserves_safe_library_sw {o} :
  forall sw (lib1 lib2 : @library o),
    swapping_in_library sw lib2
    -> lib_extends_entries lib1 lib2
    -> safe_library_sw sw lib2
    -> safe_library lib1
    -> safe_library_sw sw lib1.
Proof.
  introv inlib ext safea safeb i.
  destruct entry; simpl in *; tcsp.
  applydup safeb in i; simpl in *.
  destruct entry as [vals restr]; simpl in *; repnd.
  dands; eauto 3 with slow.

  destruct inlib as [inlib1 inlib2].

  applydup @name_in_library_implies_entry_in_library in inlib1; exrepnd.
  applydup @name_in_library_implies_entry_in_library in inlib2; exrepnd.
  applydup safea in inlib0.
  applydup safea in inlib4.
  destruct entry; simpl in *; tcsp; ginv;[].
  destruct entry0; simpl in *; tcsp; ginv;[].
  destruct entry as [vals1 restr1]; simpl in *; repnd.
  destruct entry0 as [vals2 restr2]; simpl in *; repnd.

  apply ext in inlib0.
  apply ext in inlib4.
  apply entry_in_library_extends_implies_entry_in_library in inlib0.
  apply entry_in_library_extends_implies_entry_in_library in inlib4.
  exrepnd.
  destruct entry', entry'0; simpl in *; tcsp; ginv.
  repnd; subst.
  unfold choice_sequence_entry_extend in *; repnd; simpl in *.
  destruct entry0 as [vals1' restr1']; simpl in *.
  destruct entry as [vals2' restr2']; simpl in *.

  destruct sw as [n1 n2]; simpl in *.
  boolvar; subst; tcsp; GC.

  { pose proof (two_entries_in_library_with_same_name
                  (lib_cs n1 (MkChoiceSeqEntry _ vals restr))
                  (lib_cs n1 (MkChoiceSeqEntry _ vals1' restr1'))
                  n1 lib1) as q.
    simpl in q.
    repeat (autodimp q hyp); ginv.
    eapply same_restrictions_preserves_correct_restriction;[|eauto]; eauto 3 with slow. }

  { pose proof (two_entries_in_library_with_same_name
                  (lib_cs n2 (MkChoiceSeqEntry _ vals restr))
                  (lib_cs n2 (MkChoiceSeqEntry _ vals2' restr2'))
                  n2 lib1) as q.
    simpl in q.
    repeat (autodimp q hyp); ginv.
    eapply same_restrictions_preserves_correct_restriction;[|eauto]; eauto 3 with slow. }
Qed.
Hint Resolve lib_extends_preserves_safe_library_sw : slow.

Lemma in_swap_library_implies {o} :
  forall sw entry (lib : @library o),
    List.In entry (swap_cs_lib sw lib)
    -> exists e,
      List.In e lib
      /\ entry = swap_cs_lib_entry sw e.
Proof.
  induction lib; introv h; simpl in *; tcsp;[].
  repndors; repnd; subst; simpl in *; auto.

  { exists a; dands; tcsp. }

  autodimp IHlib hyp; exrepnd; subst; simpl in *.
  exists e; dands; tcsp.
Qed.

Lemma swap_in_library {o} :
  forall sw entry (lib : @library o),
    List.In entry lib
    -> List.In (swap_cs_lib_entry sw entry) (swap_cs_lib sw lib).
Proof.
  induction lib; introv h; simpl in *; tcsp;[].
  repndors; repnd; subst; simpl in *; auto.
Qed.
Hint Resolve swap_in_library : slow.

Lemma swap_subset_library {o} :
  forall sw (lib1 lib2 : @library o),
    subset_library lib2 lib1
    -> subset_library (swap_cs_lib sw lib2) (swap_cs_lib sw lib1).
Proof.
  introv ss i.
  apply in_swap_library_implies in i; exrepnd; subst.
  apply ss in i1; exrepnd.
  apply (swap_in_library sw) in i1.
  eexists; dands; eauto.
  eauto 3 with slow.
Qed.
Hint Resolve swap_subset_library : slow.

Lemma swap_lib_extends {o} :
  forall sw (lib1 lib2 : @library o),
    swapping_in_library sw lib2
    -> sane_swapping sw
    -> safe_library lib2
    -> safe_library_sw sw lib2
    -> lib_extends lib1 lib2
    -> lib_extends (swap_cs_lib sw lib1) (swap_cs_lib sw lib2).
Proof.
  introv inlib sane safea safeb ext.
  destruct ext as [ext safe sub].
  split; eauto 3 with slow;[].

  introv safe'.
  autodimp safe hyp;[].
  apply implies_swap_safe_library; eauto 3 with slow.
Qed.
Hint Resolve swap_lib_extends : slow.

Definition ren_cs_per {o} r (e : per(o)) : per :=
  fun a b => e (ren_cs_cterm r a) (ren_cs_cterm r b).

Definition ren_cs_lib_per {o} {lib lib'}
           (r : cs_ren)
           (x : lib_extends lib' lib)
           (eqa : lib-per(lib,o)) : lib-per(lib',o).
Proof.
  exists (fun lib'' (xt : lib_extends lib'' lib') => ren_cs_per r (eqa lib'' (lib_extends_trans xt x)));[].
  repeat introv; simpl.
  unfold ren_cs_per.
  apply eqa.
Defined.

Definition cs_compatible_in_ext {o}
           (name1 name2 : choice_sequence_name)
           (lib' lib : @library o) :=
  forall m : nat,
    m < lib_size lib
    ->
    {k : nat
     & find_cs_value_at lib' name1 m = Some (mkc_nat k)
     # find_cs_value_at lib' name2 m = Some (mkc_nat k)}.

Record lib_extends_cs_ren {o}
       (name1 name2 : choice_sequence_name)
       (lib' lib : @library o) :=
  MkLibExtendsCsRen {
      lib_ext_cs_ren_ext  :> lib_extends lib' lib;
      lib_ext_cs_ren_comp : cs_compatible_in_ext name1 name2 lib' lib;
    }.

Lemma cs_compatible_in_ext_refl {o} :
  forall name1 name2 (lib : @library o),
    compatible_choice_sequence_name 0 name1
    -> cs_compatible_in_ext name1 name2 lib lib.
Proof.
  introv comp lts.
Abort.

Lemma lib_extends_cs_ren_refl {o} :
  forall name1 name2 (lib : @library o),
    lib_extends_cs_ren name1 name2 lib lib.
Proof.
  introv.
  split; eauto 3 with slow.
Abort.

Lemma lib_extends_cs_ren_implies_lib_extends {o} :
  forall (lib lib' : @library o) name1 name2,
    lib_extends_cs_ren name1 name2 lib' lib
    -> lib_extends lib' lib.
Proof.
  introv ext.
  destruct ext; auto.
Qed.
Hint Resolve lib_extends_cs_ren_implies_lib_extends : slow.

Lemma ren_cs_cterm_mkc_int {o} :
  forall ren, ren_cs_cterm ren (@mkc_int o) = mkc_int.
Proof.
  introv.
  apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @ren_cs_cterm_mkc_int : slow.

Lemma ren_cs_cterm_mkc_tnat {o} :
  forall ren, ren_cs_cterm ren (@mkc_tnat o) = mkc_tnat.
Proof.
  introv.
  apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @ren_cs_cterm_mkc_tnat : slow.

Lemma ren_cs_cterm_mkc_uatom {o} :
  forall ren, ren_cs_cterm ren (@mkc_uatom o) = mkc_uatom.
Proof.
  introv.
  apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @ren_cs_cterm_mkc_uatom : slow.

Lemma ren_cs_cterm_mkc_atom {o} :
  forall ren, ren_cs_cterm ren (@mkc_atom o) = mkc_atom.
Proof.
  introv.
  apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @ren_cs_cterm_mkc_atom : slow.

Lemma sub_per_equality_of_int_bar_eq {o} :
  forall (lib lib' : @library o) e,
    lib_extends lib' lib
    -> (e <=2=> (equality_of_int_bar lib))
    -> sub_per e (equality_of_int_bar lib').
Proof.
  introv ext equ.
  eapply sub_per_eq_eq_term_equals_left;[eauto|]; eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_int_bar_eq : slow.




(* *************************************************************** *)
(* ****** LS3 ****** *)

Definition rule_ls3 {o}
           (lib : @library o)
           (A a b n x y : NVar)
           (i : nat)
           (H : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ls3 A a b n i) (ls3_extract A a x y)))
    []
    [].

Lemma rule_ls3_true {o} :
  forall lib
         (A a b n x y : NVar) (i : nat) (H : @bhyps o)
         (d1 : A <> a)
         (d2 : n <> A)
         (d3 : n <> a)
         (d4 : b <> n)
         (d5 : b <> A)
         (d6 : b <> a)
         (d7 : x <> b)
         (safe : safe_library lib),
    rule_true lib (rule_ls3 lib A a b n x y i H).
Proof.
  unfold rule_ls3, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (ls3_extract A a x y) (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp; introv h; autorewrite with slow in *; simpl in *; tcsp. }
  exists cv.

  vr_seq_true.
  autorewrite with slow.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear lib safe ext.
  rename lib' into lib; rename safe' into safe.

  dands.

  { admit. }

  apply equality_in_function3.
  dands.

  { admit. }

  intros lib' ext A1 A2 eqA.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.

  dands.

  { admit. }

  rewrite substc_mkcv_function; auto;[].
  autorewrite with slow.

  rewrite substcv_as_substc2.

  apply equality_in_function3.
  dands.

  { admit. }

  intros lib' ext a1 a2 eqa.

  eapply equality_monotone in eqA;[|eauto];[].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.

  dands.

  { admit. }

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

  { admit. }

  { admit. }

  intros lib' ext x1 x2 eqx.

  eapply alphaeqc_preserving_equality in eqx;
    [|apply substc_alphaeqcv; apply substc2_ffdefs].
  autorewrite with slow in *.

  apply equality_in_mkc_ffdefs in eqx; exrepnd.
  clear eqx0 eqx1.

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqa;[|eauto];[].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.

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

  unfold ex_nodefsc_eq in *; exrepnd.
  rename eqx1 into eqw.
  rename eqx0 into nodefs.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.

  apply equality_in_fun.
  dands.

  { admit. }

  { admit. }

  intros lib' ext z1 z2 eqz.

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqa;[|eauto];[].
  eapply equality_monotone in eqx;[|eauto];[].
  eapply equality_monotone in eqw;[|eauto];[].

  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply apply3_ls3c_extract_ccequivc_ext|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply apply3_ls3c_extract_ccequivc_ext|].

  apply equality_in_mkc_squash_ax.
  apply equality_refl in eqA.
  apply equality_refl in eqa.
  apply equality_refl in eqx.
  apply equality_refl in eqz.
  GC.

  clear eqA.
  rename eqw into eqA.

  eapply inhabited_type_bar_respects_alphaeqc;
    [apply alphaeqc_sym;apply substc_alphaeqcv;apply substc2_product;tcsp|];[].

  rewrite mkcv_product_substc; auto;[].
  autorewrite with slow.

  apply equality_in_csname in eqa.
  unfold equality_of_csname_bar in eqa.
  apply all_in_ex_bar_inhabited_type_bar_implies_inhabited_type_bar.
  eapply all_in_ex_bar_modus_ponens1;[|exact eqa]; clear eqa; introv ext eqa.

  eapply equality_monotone in eqA;[|eauto];[].
  eapply member_monotone in eqz;[|eauto];[].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.

  unfold equality_of_csname in eqa; exrepnd; GC; spcast.

  eapply member_respects_cequivc_type in eqz;
    [|apply implies_ccequivc_ext_apply;
      [apply ccequivc_ext_refl
      |apply computes_to_valc_implies_ccequivc_ext;eauto]
    ];[].

  eapply inhabited_type_bar_cequivc;
    [apply ccequivc_ext_sym;
     apply implies_ccequivc_ext_product;
     [apply ccequivc_ext_refl
     |apply implies_bcequivc_ext_substc2_1;
      apply computes_to_valc_implies_ccequivc_ext;eauto]
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
  eapply tequality_monotone in teq;[|eauto];[].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.

  apply inhabited_product.
  dands; eauto 3 with slow;[|].

  { admit. }

  exists (@mkc_pair
            _
            (mkc_nat (lib_size lib))
            (mkc_lam b (mkcv_lam _ x (mk_cv _ z1)))).

  apply in_ext_implies_all_in_ex_bar.
  introv ext.
  exists (@mkc_nat o (lib_size lib)) (mkc_lam b (mkcv_lam _ x (mk_cv _ z1))).
  dands; spcast; eauto 3 with slow;[].

  eapply equality_monotone in eqA;[|eauto];[].
(*  eapply member_monotone in eqz;[|eauto];[].*)
  assert (safe_library lib') as safe' by eauto 3 with slow.

  rename lib into lib1.
  rename safe into safe1.
  rename lib' into lib.
  rename safe' into safe.

  rewrite substc2_substc3_eq.
  rewrite substc3_2_substc_eq.
  rewrite substc4_mkcv_function; tcsp.
  autorewrite with slow.

  eapply member_respects_alphaeqc_r;
    [apply implies_alphaeqc_mk_function;
     apply alphaeqcv_sym;
     apply substc5_mkcv_fun|].
  autorewrite with slow.
  rewrite substc5_var2; tcsp;[].
  rewrite substc5_var0; tcsp;[].

  eapply member_respects_alphaeqc_r;
    [apply implies_alphaeqc_mk_function;
     apply implies_alphaeqcv_mkcv_fun;
     [|apply alphaeqcv_refl];
     apply implies_alphaeqcv_mkcv_equality;
     [apply alphaeqcv_refl|apply alphaeqcv_refl|];
     apply alphaeqcv_sym;apply substc5_mkcv_natk2nat
    |];[].
  autorewrite with slow.
  rewrite substc5_var1; tcsp;[].

  rev_assert (member
                lib
                (mkc_lam b (mkcv_lam [b] x (mk_cv [x, b] z1)))
                (mkc_function
                   (mkc_csname 0)
                   b
                   (mkcv_fun
                      [b]
                      (mkcv_equality
                         [b]
                         (mk_cv [b] (mkc_choice_seq name))
                         (mkc_var b)
                         (mkcv_natk2nat [b] (mk_cv [b] (mkc_nat (lib_size lib1)))))
                      (mkcv_apply [b] (mk_cv [b] u) (mkc_var b))))) mem.
  {
    apply equality_in_function3 in mem; repnd.
    apply equality_in_function3; dands; auto.
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
      introv xt1 inh.
      apply mem1 in inh; auto; eauto 3 with slow;[].
      eapply equality_in_mkc_csprop_preserves_tequality;
        [apply equality_sym| |]; eauto 3 with slow.
    }

    {
      eapply alphaeqc_preserving_equality;[|apply alphaeqc_sym;apply substc_mkcv_fun].
      eapply alphaeqc_preserving_equality in mem;[|apply substc_mkcv_fun].
      autorewrite with slow in *.

      apply equality_in_fun in mem; repnd.
      apply equality_in_fun; dands; auto.

      {
        introv xt1 inh.
        eapply equality_in_mkc_csprop_preserves_type;
          [apply equality_sym| |]; eauto 3 with slow.
      }

      {
        introv xt1 eb.
        eapply tequality_preserving_equality;
          [|apply tequality_sym;eapply equality_in_mkc_csprop_implies_tequality];eauto;
            eauto 3 with slow.
        eapply equality_refl; eauto 3 with slow.
      }
    }
  }

  apply equality_sym in eqA; apply equality_refl in eqA.
  clear dependent A1.

  apply equality_in_function3; dands; eauto 3 with slow;[].

  introv ext1 ecs.
  rename a0 into b1.
  rename a' into b2.
  dands.

  { admit. }

  eapply alphaeqc_preserving_equality;[|apply alphaeqc_sym;apply substc_mkcv_fun].
  autorewrite with slow.
  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym;apply alphaeqc_mkc_fun;
      [|apply alphaeqc_refl];
      apply implies_alphaeqc_mkc_equality;
      [apply alphaeqc_refl|apply alphaeqc_refl|];
      apply substc_mkcv_natk2nat].
  autorewrite with slow.

  apply equality_in_fun.
  dands; eauto 3 with slow.

  { admit. }

  { admit. }

  introv ext2 eb.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;apply sp_implies_ccequivc_ext_apply;
     apply ccequivc_ext_beta|].
  rewrite mkcv_lam_substc; tcsp;[].
  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym; apply ccequivc_ext_beta|].
  autorewrite with slow.

  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;apply sp_implies_ccequivc_ext_apply;
     apply ccequivc_ext_beta|].
  rewrite mkcv_lam_substc; tcsp;[].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym; apply ccequivc_ext_beta|].
  autorewrite with slow.

  apply equality_refl in ecs.
  clear b2.
  apply equality_in_mkc_equality in eb; repnd.
  clear eb eb1.
  rw @member_eq.

  assert (lib_extends lib'0 lib) as xt by eauto 3 with slow.
  eapply member_monotone in ecs;[|exact ext2];[].
(*  eapply member_monotone in eqz;[|exact xt];[].*)
  eapply member_monotone in eqA;[|exact xt];[].
  assert (safe_library lib'0) as safe' by eauto 3 with slow.
  assert (lib_extends lib'0 lib1) as ext' by eauto 3 with slow.
  clear dependent lib'.
  clear dependent lib.
  rename lib'0 into lib.
  rename safe' into safe.
  rename ext'  into ext.

  apply equality_in_csname_iff in ecs.
  unfold equality_of_csname_bar in ecs.

  apply equality_natk2nat_implies2 in eb0.
  apply all_in_ex_bar_member_implies_member.

  eapply all_in_ex_bar_modus_ponens2;[|exact eb0|exact ecs]; clear eb0 ecs; introv xt eb0 ecs.

  eapply member_monotone in eqA;[|exact xt];[].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (lib_extends lib' lib1) as ext' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.
  rename ext' into ext.

  unfold equality_of_csname in ecs; exrepnd; spcast; GC.
  rename name0 into name'.

  rev_assert (member lib z1 (mkc_apply u (mkc_choice_seq name'))) mem.
  {
    pose proof (equality_in_mkc_csprop_implies_tequality lib u u b1 (mkc_choice_seq name') i) as teq.
    repeat (autodimp teq hyp); eauto 3 with slow.
    { apply equality_in_csname_iff; exists (trivial_bar lib); introv br xt; simpl in *.
      exists name'; dands; spcast; eauto 3 with slow. }
    eapply tequality_preserving_equality;[|apply tequality_sym;eauto]; auto.
  }

  assert (forall m,
             m < lib_size lib1
             ->
             {k : nat
             & computes_to_valc lib (mkc_apply (mkc_choice_seq name) (mkc_nat m)) (mkc_nat k)
             # computes_to_valc lib (mkc_apply (mkc_choice_seq name') (mkc_nat m)) (mkc_nat k)}) as imp.
  {
    introv h; apply eb0 in h.
    apply equality_of_nat_imp_tt in h; unfold equality_of_nat_tt in h; exrepnd.
    exists k; dands; spcast; auto.
    eapply computes_to_valc_apply; eauto.
  }
  clear dependent b1.

  assert (forall m,
             m < lib_size lib1
             ->
             {k : nat
              & find_cs_value_at lib name  m = Some (mkc_nat k)
              # find_cs_value_at lib name' m = Some (mkc_nat k)}) as imp'.
  {
    introv h; apply imp in h; exrepnd.
    exists k.
    apply computes_to_valc_nat_implies_find_cs_value_at_if_safe in h1; auto.
    apply computes_to_valc_nat_implies_find_cs_value_at_if_safe in h0; auto.
  }
  clear dependent imp.
  rename imp' into imp.

  (* === We might have to squash the application in the conclusion === *)

  (* === We have to show that because of [imp], [lib1] can be extended with [name']
         equivalent to [name] up to [lib_size lib1] === *)

  destruct (choice_sequence_name_deq name' name) as [d|d];[subst;eauto 3 with slow|];[].

  assert (lib_extends_cs_ren name name' lib lib1) as extren by (split; auto).



  (* xxxxxxxxxxxx *)


  Lemma sub_per_refl {o} : forall (eq : per(o)), sub_per eq eq.
  Proof.
    introv h; auto.
  Qed.
  Hint Resolve sub_per_refl : slow.

  Lemma lib_extends_preserves_cs_compatible_in_ext {o} :
    forall name1 name2 (lib lib' lib0 : @library o),
      lib_extends lib' lib
      -> cs_compatible_in_ext name1 name2 lib lib0
      -> cs_compatible_in_ext name1 name2 lib' lib0.
  Proof.
    introv ext comp h.
    pose proof (comp _ h) as comp; exrepnd.
    exists k.
    apply (lib_extends_preserves_find_cs_value_at _ _ _ _ _ ext) in comp1.
    apply (lib_extends_preserves_find_cs_value_at _ _ _ _ _ ext) in comp0.
    tcsp.
  Qed.
  Hint Resolve lib_extends_preserves_cs_compatible_in_ext : slow.

  Lemma lib_extends_cs_ren_trans {o} :
    forall name1 name2 (lib lib' lib0 : @library o),
      lib_extends lib' lib
      -> lib_extends_cs_ren name1 name2 lib lib0
      -> lib_extends_cs_ren name1 name2 lib' lib0.
  Proof.
    introv ext xt.
    destruct xt as [xt comp].
    split; dands; eauto 2 with slow.
  Qed.
  Hint Resolve lib_extends_cs_ren_trans : slow.

  Definition bar_per_type {o} {lib} (bar : @BarLib o lib) :=
    forall lib1 (b : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib), per(o).

  Definition bar_per_type_cond {o} {lib} {bar : @BarLib o lib}
             (p : bar_per_type bar) :=
    forall (lib' lib1 : library)
           (b : bar_lib_bar bar lib1)
           (ext : lib_extends lib' lib1)
           (x y : lib_extends lib' lib),
      (p lib1 b lib' ext x) <=2=> (p lib1 b lib' ext y).

  Record bar_per {o} {lib} (bar : @BarLib o lib) :=
    MkBarPer
      {
        bar_per_per :> bar_per_type bar;
        bar_per_cond : bar_per_type_cond bar_per_per
      }.

  Definition bar_per2per {o} {lib} {bar : @BarLib o lib} (p : bar_per bar) : per :=
    fun t1 t2 =>
      forall lib1 (b : bar_lib_bar bar lib1)
             lib2 (ext : lib_extends lib2 lib1)
             (x : lib_extends lib2 lib),
        bar_per_per _ p lib1 b lib2 ext x t1 t2.

  Definition bar_per2lib_per {o} {lib}
             {bar : @BarLib o lib}
             (p : bar_per bar)
    : lib-per(lib,o).
  Proof.
    exists (fun lib2 (x : lib_extends lib2 lib) t1 t2 =>
              forall lib1 (b : bar_lib_bar bar lib1) (ext : lib_extends lib2 lib1),
                bar_per_per _ p lib1 b lib2 ext x t1 t2).
    repeat introv.
    split; intro q; introv; eapply (bar_per_cond _ p); eauto.
  Defined.

  Lemma all_in_bar_ext_exists_per_implies_exists2 {o} :
    forall {lib}
           (bar : @BarLib o lib)
           (F : forall lib' (x : lib_extends lib' lib) (p : per(o)), Prop),
      (forall lib' (x y : lib_extends lib' lib) (p q : per(o)),
          F lib' x p
          -> F lib' y q
          -> (p <=2=> q))
      -> all_in_bar_ext bar (fun lib' x => exists (e : per(o)), F lib' x e)
      ->
      exists (f : bar_per(bar)),
      forall lib1 (br : bar_lib_bar bar lib1)
             lib2 (ext : lib_extends lib2 lib1)
             (x : lib_extends lib2 lib),
        F lib2 x (bar_per_per _ f lib1 br lib2 ext x).
  Proof.
    introv cond h.
    pose proof (DependentFunctionalChoice_on
                  (pack_lib_bar bar)
                  (fun x => per(o))
                  (fun x e => F (plb_lib2 _ x)
                                (plb_x _ x)
                                e)) as C.
    simpl in C.
    repeat (autodimp C hyp).
    { introv; destruct x; simpl in *; eapply h; eauto. }
    exrepnd.

    assert (bar_per_type_cond
              (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
                 (f (MkPackLibBar lib1 br lib2 ext x)))) as C.
    {
      repeat introv; simpl.
      pose proof (C0 (MkPackLibBar lib1 b lib' ext x)) as q1; simpl in q1.
      pose proof (C0 (MkPackLibBar lib1 b lib' ext y)) as q2; simpl in q2.
      eapply cond; eauto.
    }
    exists (MkBarPer
              _ _ _
              (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
                 (f (MkPackLibBar lib1 br lib2 ext x)))
              C).
    introv.
    pose proof (C0 (MkPackLibBar lib1 br lib2 ext x)) as w; auto.
  Defined.

  Lemma sub_per_per_bar_eq_raise_right {o} :
    forall {lib lib'}
           (bar  : @BarLib o lib)
           (eqa  : lib-per(lib,o))
           (extb : lib_extends lib' lib)
           (f    : bar_per (raise_bar bar extb)),
      (forall (lib1 : library)
              (br : bar_lib_bar (raise_bar bar extb) lib1)
              (lib2 : library)
              (ext : lib_extends lib2 lib1)
              (x : lib_extends lib2 lib'),
          sub_per (eqa lib2 (lib_extends_trans x extb)) (bar_per_per _ f lib1 br lib2 ext x))
      -> sub_per
           (per_bar_eq bar eqa)
           (per_bar_eq (raise_bar bar extb) (bar_per2lib_per f)).
  Proof.
    introv cond equ.

    introv br ext; introv; simpl in *; exrepnd.
    pose proof (equ _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x extb)) as equ; simpl in *.
    exrepnd.
    exists bar'.

    introv br' ext'; introv; simpl in *; exrepnd.
    pose proof (equ0 _ br' _ ext' x0) as equ0; simpl in *.
    apply cond.
    eapply (lib_per_cond _ eqa); eauto.
  Qed.

  Lemma sub_per_per_bar_eq_raise_right2 {o} :
    forall {lib lib'}
           (bar  : @BarLib o lib)
           (eqa  : lib-per(lib,o))
           (extb : lib_extends lib' lib)
           (f    : bar_per bar),
      (forall (lib1 : library)
              (br : bar_lib_bar bar lib1)
              (lib2 : library)
              (ext : lib_extends lib2 lib1)
              (x : lib_extends lib2 lib),
          sub_per (eqa lib2 x) (bar_per_per _ f lib1 br lib2 ext x))
      -> sub_per
           (per_bar_eq bar eqa)
           (per_bar_eq (raise_bar bar extb) (raise_lib_per (bar_per2lib_per f) extb)).
  Proof.
    introv cond equ.

    introv br ext; introv; simpl in *; exrepnd.
    pose proof (equ _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x extb)) as equ; simpl in *.
    exrepnd.
    exists bar'.

    introv br' ext'; introv; simpl in *; exrepnd.
    pose proof (equ0 _ br' _ ext' x0) as equ0; simpl in *.
    introv.
    apply cond; auto.
    eapply (lib_per_cond _ eqa); eauto.
  Qed.

  Lemma type_system_implies_type_extensionality {o} :
    forall (ts : cts(o)),
      type_system ts
      -> type_extensionality ts.
  Proof.
    introv h; destruct h; tcsp.
  Qed.
  Hint Resolve type_system_implies_type_extensionality : slow.

(* Inspired from name_invariance stuff *)
Lemma implies_close_ren_cs {o} :
  forall name1 name2 lib lib' (u : cts(o)) (t1 t2 : @CTerm o) e,
    local_ts u
    -> ts_implies_per_bar u
    -> type_system u
    -> defines_only_universes u
    -> type_monotone u
    -> name1 <> name2
    -> up_to_namec name1 t1
    -> up_to_namec name1 t2
    -> (forall lib lib' t1 t2 e,
           (lib_extends_cs_ren name1 name2 lib' lib
            [+] lib_extends lib lib')
           -> u lib t1 t2 e
           -> exists e',
               sub_per e e'
               /\ u lib'
                    (ren_cs_cterm (name1,name2) t1)
                    (ren_cs_cterm (name1,name2) t2)
                    e')
    -> (lib_extends_cs_ren name1 name2 lib' lib
        [+] lib_extends lib lib')
    -> close u lib t1 t2 e
    -> exists e',
        sub_per e e'
        /\ close
             u
             lib'
             (ren_cs_cterm (name1,name2) t1)
             (ren_cs_cterm (name1,name2) t2)
             e'.
Proof.
  introv locts iperbar tsts dou mon.
  introv dn upto1 upto2 imp exta cl.
  revert dependent lib'.
  close_cases (induction cl using @close_ind') Case; introv exta; subst.

  { Case "CL_init".
    pose proof (imp lib lib' T T' eq) as imp.
    repeat (autodimp imp hyp); exrepnd.
    exists e'; dands; auto.
  }

  { Case "CL_bar".
    clear per.

    assert (all_in_bar_ext
              bar
              (fun (lib' : library) (x : lib_extends lib' lib) =>
                 exists e',
                   sub_per (eqa lib' x) e'
                   /\
                   close ts lib'
                         (ren_cs_cterm (name1, name2) T)
                         (ren_cs_cterm (name1, name2) T') e')) as reca'.
    {
      introv br xt; introv.
      pose proof (reca _ br _ xt x) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      pose proof (reca lib'1) as reca.
      autodimp reca hyp; eauto 3 with slow.
    }
    clear reca; rename reca' into reca.

(*    assert (all_in_bar_ext
              (raise_bar bar extb)
              (fun (lib'' : library) (x : lib_extends lib'' lib') =>
                 exists e',
                   sub_per (eqa lib'' (lib_extends_trans x extb)) e'
                   /\
                   close ts lib''
                         (ren_cs_cterm (name1, name2) T)
                         (ren_cs_cterm (name1, name2) T') e')) as reca'.
    {
      introv br ext; introv; simpl in *; exrepnd.
      pose proof (reca _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x extb)) as reca; simpl in reca.
      repeat (autodimp reca hyp); eauto 3 with slow.
    }
    clear reca; rename reca' into reca.*)

    apply all_in_bar_ext_exists_per_implies_exists2 in reca; exrepnd;
      [|introv a b; repnd;
        eapply close_uniquely_valued; try exact a; try exact b; auto];[].

    repndors.

    {
      exists (per_bar_eq (raise_bar bar exta) (raise_lib_per (bar_per2lib_per f) exta)).
      dands; eauto 3 with slow.

      {
        eapply sub_per_eq_eq_term_equals_left;[eauto|].
        eapply sub_per_per_bar_eq_raise_right2.
        introv; apply reca0.
      }

      apply CL_bar; unfold per_bar.
      exists (raise_bar bar exta) (raise_lib_per (bar_per2lib_per f) exta).
      dands; tcsp;[].
      introv br ext; introv.
      simpl in *; exrepnd.
      pose proof (reca0 _ br1 _ (lib_extends_trans ext br2) (lib_extends_trans x exta)) as reca; repnd.

      eapply close_extensionality; try exact reca; eauto 2 with slow;[].
      introv; split; intro q; try apply q;[].
      introv.
      pose proof (reca0 _ b _ ext0 (lib_extends_trans x exta)) as reca0; repnd.
      eapply close_uniquely_valued; try exact reca; try exact reca0; auto.
    }

    {
      
    }
  }

  { Case "CL_int".
    unfold per_int in *; repnd.

  Lemma ren_cs_term_preserves_ccomputes_to_valc {o} :
    forall lib lib' name1 name2 (a b : @CTerm o),
      a ===>(lib) b
      -> lib_extend lib' lib
      -> lib_extend lib lib0
      -> lib_extends_cs_ren name1 name2 lib' lib0
      -> (ren_cs_cterm (name1,name2) a) ===>(lib') (ren_cs_cterm (name1,name2) b).
  Proof.
  Admitted.

    apply (ren_cs_term_preserves_ccomputes_to_valc _ lib' name1 name2) in per0; auto.



  Lemma lib_extends_preserves_cs_compatible_in_ext_right {o} :
    forall name1 name2 (lib lib0 lib1 : @library o),
      lib_extends lib1 lib0
      -> lib_extends lib lib1
      -> cs_compatible_in_ext name1 name2 lib lib0
      -> cs_compatible_in_ext name1 name2 lib lib1.
  Proof.
    introv exta extb comp h.
    apply comp.

  Qed.
  Hint Resolve lib_extends_preserves_cs_compatible_in_ext_right : slow.

  Lemma lib_extends_cs_ren_trans_right {o} :
    forall name1 name2 (lib lib0 lib1 : @library o),
      lib_extends lib1 lib0
      -> lib_extends lib lib1
      -> lib_extends_cs_ren name1 name2 lib lib0
      -> lib_extends_cs_ren name1 name2 lib lib1.
  Proof.
    introv exta extb xt.
    destruct xt as [xt comp].
    split; dands; eauto 2 with slow.

  Qed.
  Hint Resolve lib_extends_cs_ren_trans : slow.

    SearchAbout lib_extends_cs_ren.
    apply (ren_cs_term_preserves_ccomputes_to_valc _ lib' name1 name2) in per1; auto.
    autorewrite with slow in *.

    exists (equality_of_int_bar lib').
    dands; eauto 3 with slow.

    apply CL_int.
    unfold per_int.
    dands; eauto 2 with slow. }

  }

Qed.

Lemma implies_equality_ren_cs {o} :
  forall name1 name2 lib lib' (t1 t2 T : @CTerm o),
    name1 <> name2
    -> lib_extends lib' lib
    -> up_to_namec name1 T
    -> (forall m : nat,
           m < cs_size lib name1
           ->
           {k : nat
            & find_cs_value_at lib' name1 m = Some (mkc_nat k)
            # find_cs_value_at lib' name2 m = Some (mkc_nat k)})
    -> equality lib t1 t2 T
    -> equality
         lib'
         (ren_cs_cterm (name1,name2) t1)
         (ren_cs_cterm (name1,name2) t2)
         (ren_cs_cterm (name1,name2) T).
Proof.
  introv equ.
  unfold equality, nuprl in *; exrepnd.
(*  exists (rename_per r eq).
  unfold rename_per; autorewrite with slow in *.
  dands; auto;[].
  fold (rename_per r eq).
  apply implies_close_univ_rename; auto.*)
Abort.







   Definition contains_atmost {o} (name : choice_sequence_name) (t : @CTerm o) :=
     subset (get_defs (get_cterm t)) [defk_cs name].

   Lemma contains_only_implies_contains_atmost {o} :
     forall name (t : @CTerm o),
       contains_only name t -> contains_atmost name t.
   Proof.
     introv cont i; simpl in *.
     rewrite cont in i; simpl in *; tcsp.
   Qed.
   Hint Resolve contains_only_implies_contains_atmost : slow.

   Lemma contains_only_implies_computes_to_valc_keep_only {o} :
     forall name lib (t v : @CTerm o),
       contains_atmost name t
       -> computes_to_valc lib t v
       -> computes_to_valc (keep_only name lib) t v.
   Proof.
   Admitted.

   Lemma computes_to_valc_preserves_contains_only {o} :
     forall name lib (t v : @CTerm o),
       computes_to_valc lib t v
       -> contains_atmost name t
       -> contains_atmost name v.
   Proof.
   Admitted.

   Lemma contains_atmost_mkc_equality {o} :
     forall name (a b T : @CTerm o),
       contains_atmost name (mkc_equality a b T)
       <=> (contains_atmost name a # contains_atmost name b # contains_atmost name T).
   Proof.
     introv.
     unfold contains_atmost; simpl.
     destruct_cterms; simpl; autorewrite with list.
     split; intro h; repnd; dands; introv j; simpl in *;
       try (complete (pose proof (h x2) as h; allrw in_app_iff; simpl in *; tcsp));[].
     allrw in_app_iff; repndors.
     { pose proof (h0 x2) as q; tcsp. }
     { pose proof (h1 x2) as q; tcsp. }
     { pose proof (h x2) as q; tcsp. }
   Qed.

   Definition to_lib_per_ext {o}
              {lib} {F}
              (f : {l : @library o $ lib_extends l lib} -> per(o))
              (E : forall lib' a b, F lib' (f exI(lib',a)) -> F lib' (f exI(lib',b)) -> (f exI(lib',a)) <=2=> (f exI(lib',b)))
              (C : forall x : {l : library $ lib_extends l lib}, F (projT1 x) (f x)) : lib-per(lib,o).
   Proof.
     exists (fun lib x => f (existT _ lib x)).
     introv.
     pose proof (C (existT _ lib' e)) as a.
     pose proof (C (existT _ lib' y)) as b.
     simpl in *.
     apply E; auto.
   Defined.

   Lemma in_ext_ext_per_choice {o} :
     forall (lib : @library o) (F : forall lib' (p : per(o)), Prop),
       (forall lib' a b, F lib' a -> F lib' b -> a <=2=> b)
       -> in_ext_ext lib (fun lib' x => exists (e : per(o)), F lib' e)
       ->
       exists (f : lib-per(lib,o)),
       forall lib' (x : lib_extends lib' lib),
         F lib' (f lib' x).
   Proof.
     introv imp h.

     pose proof (DependentFunctionalChoice_on
                   {l : library & lib_extends l lib}
                   (fun x => per(o))
                   (fun l e => F (projT1 l) e)) as C.
     simpl in C.
     repeat (autodimp C hyp).
     { introv; destruct x; simpl in *; eapply h; eauto. }
     exrepnd.

     assert (forall lib' a b, F lib' (f exI(lib',a)) -> F lib' (f exI(lib',b)) -> (f exI(lib',a)) <=2=> (f exI(lib',b))) as E.
     { introv u v; apply (imp lib'); auto. }

     exists (to_lib_per_ext f E C0); simpl; auto.
     introv.
     pose proof (C0 (existT _ lib' x)) as z; simpl in z; auto.
   Qed.

   Lemma entry_in_library_keep_only {o} :
     forall name entry (lib : @library o),
       entry_in_library entry (keep_only name lib)
       -> entry_in_library entry lib
          /\ same_entry_name (entry2name entry) (entry_name_cs name).
   Proof.
     induction lib; introv i; simpl in *; tcsp.
     destruct a; simpl in *; boolvar; subst; simpl in *; repndors; subst; tcsp.

     { apply IHlib in i; repnd; tcsp.
       dands; tcsp.
       right; dands; auto.
       destruct entry; simpl in *; subst; tcsp. }

     { apply IHlib in i; repnd.
       dands; tcsp.
       right; dands; tcsp.
       destruct entry; simpl in *; subst; tcsp. }
   Qed.

   Lemma implies_entry_in_library_extends_keep_only {o} :
     forall name entry (lib : @library o),
       entry_in_library_extends entry lib
       -> same_entry_name (entry2name entry) (entry_name_cs name)
       -> entry_in_library_extends entry (keep_only name lib).
   Proof.
     induction lib; introv i same; simpl in *; tcsp.
     repndors; repnd; tcsp.

     { clear IHlib.
       destruct entry; simpl in *; subst; tcsp;[].
       destruct a; simpl in *; tcsp; ginv;[].
       repnd; subst; boolvar; subst; tcsp; GC.
       simpl; tcsp. }

     { applydup IHlib in i; auto; clear IHlib.
       destruct a; simpl in *; tcsp.
       boolvar; subst; tcsp. }
   Qed.
   Hint Resolve implies_entry_in_library_extends_keep_only : slow.

   Lemma implies_lib_extends_entries_keep_only {o} :
     forall name (lib1 lib2 : @library o),
       lib_extends_entries lib1 lib2
       -> lib_extends_entries (keep_only name lib1) (keep_only name lib2).
   Proof.
     introv ext i.
     applydup @entry_in_library_keep_only in i; repnd.
     apply ext in i1; eauto 3 with slow.
   Qed.
   Hint Resolve implies_lib_extends_entries_keep_only : slow.

   Lemma implies_safe_library_keep_only {o} :
     forall name (lib : @library o),
       safe_library lib
       -> safe_library (keep_only name lib).
   Proof.
     introv safe i.
     apply entry_in_library_keep_only in i; repnd.
     apply safe in i0; auto.
   Qed.
   Hint Resolve implies_safe_library_keep_only : slow.

   Lemma implies_safe_library_keep_only_imp {o} :
     forall name (lib1 lib2 : @library o),
       safe_library lib2
       -> (safe_library lib2 -> safe_library lib1)
       -> safe_library (keep_only name lib2)
       -> safe_library (keep_only name lib1).
   Proof.
     introv safe imp safeko.
     autodimp imp hyp; eauto 3 with slow.
   Qed.
   Hint Resolve implies_safe_library_keep_only_imp : slow.

   Lemma in_library_keep_only {o} :
     forall name entry (lib : @library o),
       List.In entry (keep_only name lib)
       -> List.In entry lib
          /\ same_entry_name (entry2name entry) (entry_name_cs name).
   Proof.
     induction lib; introv i; simpl in *; tcsp.
     destruct a; simpl in *; boolvar; subst; simpl in *; repndors; subst; tcsp.
   Qed.

   Lemma lin_library_keep_only {o} :
     forall name entry (lib : @library o),
       LIn entry (keep_only name lib)
       -> LIn entry lib
              # same_entry_name (entry2name entry) (entry_name_cs name).
   Proof.
     induction lib; introv i; simpl in *; tcsp.
     destruct a; simpl in *; boolvar; subst; simpl in *; repndors; subst; tcsp.
   Qed.

   Lemma in_library_keep_only_implies_entry_in_library {o} :
     forall name entry (lib : @library o),
       List.In entry (keep_only name lib)
       -> entry_in_library entry lib
          /\ same_entry_name (entry2name entry) (entry_name_cs name).
   Proof.
     induction lib; introv i; simpl in *; tcsp.
     destruct a; simpl in *; boolvar; subst; simpl in *; repndors; subst; tcsp.

     { apply IHlib in i; clear IHlib; repnd.
       dands; tcsp.
       right; dands; tcsp.
       destruct entry; simpl in *; subst; tcsp. }

     { apply IHlib in i; clear IHlib; repnd.
       dands; tcsp.
       right; dands; tcsp.
       destruct entry; simpl in *; subst; tcsp. }
   Qed.

   Lemma implies_subset_library_keep_only {o} :
     forall name (lib1 lib2 : @library o),
       lib_extends_entries lib1 lib2
       -> subset_library (keep_only name lib2) (keep_only name lib1).
   Proof.
     introv ext i.
     apply in_library_keep_only_implies_entry_in_library in i; repnd.
     apply ext in i0.
     apply (implies_entry_in_library_extends_keep_only name) in i0; auto.
     apply entry_in_library_extends_implies_entry_in_library in i0; exrepnd.
     exists entry'; dands; eauto 3 with slow.
   Qed.
   Hint Resolve implies_subset_library_keep_only : slow.

   Lemma implies_lib_extends_keep_only {o} :
     forall name (lib1 lib2 : @library o),
       safe_library lib2
       -> lib_extends lib1 lib2
       -> lib_extends (keep_only name lib1) (keep_only name lib2).
   Proof.
     introv safe0 ext.
     destruct ext as [ext safe sub].
     split; eauto 3 with slow.
   Qed.
   Hint Resolve implies_lib_extends_keep_only : slow.

   Lemma implies_entry_in_library_keep_only {o} :
     forall name entry (lib : @library o),
       entry_in_library entry lib
       -> same_entry_name (entry2name entry) (entry_name_cs name)
       -> entry_in_library entry (keep_only name lib).
   Proof.
     induction lib; introv i same; simpl in *; tcsp.
     repndors; repnd; tcsp.

     { clear IHlib.
       destruct entry; simpl in *; subst; tcsp;[].
       repnd; subst; boolvar; subst; tcsp. }

     { applydup IHlib in i; auto; clear IHlib.
       destruct a; simpl in *; tcsp.
       boolvar; subst; tcsp. }
   Qed.
   Hint Resolve implies_entry_in_library_keep_only : slow.

   Lemma entry_in_library_extends_app_left {o} :
     forall entry (lib1 lib2 : @library o),
       entry_in_library_extends entry lib1
       -> entry_in_library_extends entry (lib1 ++ lib2).
   Proof.
     induction lib1; introv h; simpl in *; tcsp.
   Qed.
   Hint Resolve entry_in_library_extends_app_left : slow.

   Lemma entry_in_library_extends_app_right {o} :
     forall entry (lib1 lib2 : @library o),
       entry_in_library_extends entry lib2
       -> (forall e, LIn e lib1 -> ~ matching_entries entry e)
       -> entry_in_library_extends entry (lib1 ++ lib2).
   Proof.
     induction lib1; introv i imp; simpl in *; tcsp.
   Qed.
   Hint Resolve entry_in_library_extends_app_right : slow.

   Lemma implies_lib_extends_entries_keep_only_app {o} :
     forall name x (lib : @library o),
       lib_extends_entries x (keep_only name lib)
       -> lib_extends_entries (keep_only name x ++ lib) lib.
   Proof.
     introv ext i.
     destruct (same_entry_name_dec (entry2name entry) (entry_name_cs name)).

     { apply (implies_entry_in_library_keep_only name) in i; auto.
       apply ext in i.
       apply (implies_entry_in_library_extends_keep_only name) in i; auto; eauto 3 with slow. }

     { apply entry_in_library_extends_app_right; eauto 3 with slow.
       introv j.
       apply lin_library_keep_only in j; repnd.
       destruct entry, e; simpl in *; tcsp; subst; tcsp. }
   Qed.
   Hint Resolve implies_lib_extends_entries_keep_only_app : slow.

   Lemma implies_safe_library_app {o} :
     forall (lib1 lib2 : @library o),
       safe_library lib1
       -> safe_library lib2
       -> safe_library (lib1 ++ lib2).
   Proof.
     introv safe1 safe2 i.
     apply entry_in_library_app_implies in i; repnd; tcsp.
   Qed.
   Hint Resolve implies_safe_library_app : slow.

   Lemma implies_safe_library_keep_only_app_imp {o} :
     forall name x (lib : @library o),
       (safe_library (keep_only name lib) -> safe_library x)
       -> safe_library lib
       -> safe_library (keep_only name x ++ lib).
   Proof.
     introv imp safe.
     autodimp imp hyp; eauto 3 with slow.
   Qed.
   Hint Resolve implies_safe_library_keep_only_app_imp : slow.

   Lemma implies_subset_library_keep_only_app {o} :
     forall name x (lib : @library o),
       subset_library (keep_only name lib) x
       -> subset_library lib (keep_only name x ++ lib).
   Proof.
     introv ss i.
     exists entry1; dands; eauto 3 with slow.
     apply in_or_app; tcsp.
   Qed.
   Hint Resolve implies_subset_library_keep_only_app : slow.

   Lemma implies_lib_extends_keep_only_app {o} :
     forall name x (lib : @library o),
       lib_extends x (keep_only name lib)
       -> lib_extends (keep_only name x ++ lib) lib.
   Proof.
     introv ext.
     destruct ext as [ext safe sub].
     split; eauto 3 with slow.
   Qed.
   Hint Resolve implies_lib_extends_keep_only_app : slow.

   Fixpoint remove_cs_lib {o} name (lib : @library o) : library :=
     match lib with
     | [] => []
     | lib_cs name' e :: entries =>
       if choice_sequence_name_deq name name'
       then (*lib_cs name (empty_choice_seq_entry e) ::*) remove_cs_lib name entries
       else lib_cs name' e :: remove_cs_lib name entries
     | entry :: entries => entry :: remove_cs_lib name entries
     end.

   Lemma find_cs_app_not_right {o} :
     forall name (lib1 lib2 : @library o),
       find_cs lib2 name = None
       -> find_cs (lib1 ++ lib2) name = find_cs lib1 name.
   Proof.
     induction lib1; introv fcs; simpl in *; tcsp.
     destruct a; simpl in *; tcsp.
     boolvar; subst; tcsp.
   Qed.

   Lemma keep_only_idem {o} :
     forall name (lib : @library o),
       keep_only name (keep_only name lib) = keep_only name lib.
   Proof.
     induction lib; simpl in *; tcsp.
     destruct a; tcsp; boolvar; subst; tcsp.
     simpl in *; boolvar; tcsp.
   Qed.
   Hint Rewrite @keep_only_idem : slow.

   Definition to_lib_per_ext2 {o}
              {lib} {F} {name}
              {f : {l : @library o $ lib_extends l (keep_only name lib)} -> per(o)}
              (E : forall lib' a b, F (keep_only name lib') (f exI(lib',a)) -> F (keep_only name lib') (f exI(lib',b)) -> (f exI(lib',a)) <=2=> (f exI(lib',b)))
              (C : forall x : {l : library $ lib_extends l (keep_only name lib)}, F (keep_only name (projT1 x)) (f x)) : lib-per(keep_only name lib,o).
   Proof.
     exists (fun lib x => f (existT _ lib x)).
     introv.
     pose proof (C (existT _ lib' e)) as a.
     pose proof (C (existT _ lib' y)) as b.
     simpl in *.
     apply E; auto.
   Defined.

   Lemma in_ext_ext_per_choice2 {o} :
     forall name (lib : @library o) (F : forall lib' (p : per(o)), Prop) (safe : safe_library lib),
       (forall lib' a b, F lib' a -> F lib' b -> a <=2=> b)
       -> in_ext_ext lib (fun lib' x => exists (e : per(o)), F (keep_only name lib') e)
       ->
       exists (f : lib-per(keep_only name lib,o)),
       forall lib' (x : lib_extends lib' lib),
         F (keep_only name lib')
           (f (keep_only name lib')
              (implies_lib_extends_keep_only name _ _ safe x)).
   Proof.
     introv imp h.

     pose proof (DependentFunctionalChoice_on
                   {l : library & lib_extends l (keep_only name lib)}
                   (fun x => per(o))
                   (fun l e => F (keep_only name (projT1 l)) e)) as C.
     simpl in C.
     repeat (autodimp C hyp).
     { introv; destruct x; simpl in *.
       remember (find_cs lib name) as fd; symmetry in Heqfd; destruct fd.

       { pose proof (h (keep_only name x ++ lib) (implies_lib_extends_keep_only_app _ _ _ l)) as h; simpl in h; exrepnd.
         rewrite keep_only_equal in l.
         rewrite Heqfd in l.
         eapply (lib_extends_preserves_find_cs _ _ name) in l;
           [|simpl; boolvar; try reflexivity; tcsp].
         exrepnd.
         rewrite (keep_only_equal name x) in h0.
         rewrite l1 in h0; simpl in h0; boolvar; tcsp; GC.
         rewrite keep_only_equal; allrw; eauto. }

       { rewrite keep_only_equal in l.
         rewrite Heqfd in l.
         pose proof (h (keep_only name x ++ lib)) as h; simpl in h; autodimp h hyp; eauto 3 with slow.
         { apply implies_lib_extends_keep_only_app.
           rewrite keep_only_equal; allrw; auto. }
         exrepnd.
         rewrite keep_only_equal in h0.
         rewrite find_cs_app_not_right in h0; auto.
         rewrite <- keep_only_equal in h0.
         autorewrite with slow in *.
         exists e; auto. } }
     exrepnd.

     assert (forall lib' a b, F (keep_only name lib') (f exI(lib',a)) -> F (keep_only name lib') (f exI(lib',b)) -> (f exI(lib',a)) <=2=> (f exI(lib',b))) as E.
     { introv u v; apply (imp (keep_only name lib')); auto. }
     simpl in *.

     exists (to_lib_per_ext2 E C0); simpl; auto.
     introv.
     pose proof (C0 (existT _ (keep_only name lib') (implies_lib_extends_keep_only name _ _ safe x))) as z; simpl in z; auto.
     autorewrite with slow in *; auto.
   Qed.

   Lemma in_ext_ext_per_choice3 {o} :
     forall name (lib : @library o) (F : forall lib' (p : per(o)), Prop),
       (forall lib' a b, F lib' a -> F lib' b -> a <=2=> b)
       -> in_ext_ext lib (fun lib' x => exists (e : per(o)), F (keep_only name lib') e)
       ->
       exists (f : lib-per(keep_only name lib,o)),
       forall lib' (x : lib_extends lib' (keep_only name lib)),
         F (keep_only name lib') (f lib' x).
   Proof.
     introv imp h.

     pose proof (DependentFunctionalChoice_on
                   {l : library & lib_extends l (keep_only name lib)}
                   (fun x => per(o))
                   (fun l e => F (keep_only name (projT1 l)) e)) as C.
     simpl in C.
     repeat (autodimp C hyp).
     { introv; destruct x; simpl in *.
       remember (find_cs lib name) as fd; symmetry in Heqfd; destruct fd.

       { pose proof (h (keep_only name x ++ lib) (implies_lib_extends_keep_only_app _ _ _ l)) as h; simpl in h; exrepnd.
         rewrite keep_only_equal in l.
         rewrite Heqfd in l.
         eapply (lib_extends_preserves_find_cs _ _ name) in l;
           [|simpl; boolvar; try reflexivity; tcsp].
         exrepnd.
         rewrite (keep_only_equal name x) in h0.
         rewrite l1 in h0; simpl in h0; boolvar; tcsp; GC.
         rewrite keep_only_equal; allrw; eauto. }

       { rewrite keep_only_equal in l.
         rewrite Heqfd in l.
         pose proof (h (keep_only name x ++ lib)) as h; simpl in h; autodimp h hyp; eauto 3 with slow.
         { apply implies_lib_extends_keep_only_app.
           rewrite keep_only_equal; allrw; auto. }
         exrepnd.
         rewrite keep_only_equal in h0.
         rewrite find_cs_app_not_right in h0; auto.
         rewrite <- keep_only_equal in h0.
         autorewrite with slow in *.
         exists e; auto. } }
     exrepnd.

     assert (forall lib' a b, F (keep_only name lib') (f exI(lib',a)) -> F (keep_only name lib') (f exI(lib',b)) -> (f exI(lib',a)) <=2=> (f exI(lib',b))) as E.
     { introv u v; apply (imp (keep_only name lib')); auto. }
     simpl in *.

     exists (to_lib_per_ext2 E C0); simpl; auto.
     introv.
     pose proof (C0 (existT _ lib' x)) as q; simpl in *; auto.
   Qed.

  (* TODO *)
  Lemma member_implies_keep_only {o} :
    forall name lib (t T : @CTerm o),
      contains_only name T
      -> computes_to_valc lib t mkc_axiom
      -> member lib t T
      -> member (keep_only name lib) t T.
  Proof.

    Lemma find_cs_implies_lib_extends_entries_singleton_right {o} :
      forall name e (lib : @library o),
        find_cs lib name = Some e
        -> lib_extends_entries lib [lib_cs name e].
    Proof.
      introv fcs i; simpl in *.
      repndors; repnd; tcsp; subst.
      apply entry_in_library_implies_entry_in_library_extends; eauto 3 with slow.
    Qed.
    Hint Resolve find_cs_implies_lib_extends_entries_singleton_right : slow.

    Lemma find_cs_implies_subset_library_singleton_right {o} :
      forall name e (lib : @library o),
        find_cs lib name = Some e
        -> subset_library [lib_cs name e] lib.
    Proof.
      introv fcs i; simpl in *; repndors; tcsp; subst.
      exists (lib_cs name e); dands; eauto 3 with slow.
    Qed.
    Hint Resolve find_cs_implies_subset_library_singleton_right : slow.

    Lemma find_cs_implies_lib_extends_singleton_right {o} :
      forall name e (lib : @library o),
        safe_library lib
        -> find_cs lib name = Some e
        -> lib_extends lib [lib_cs name e].
    Proof.
      introv safe fcs.
      split; eauto 3 with slow.
    Qed.
    Hint Resolve find_cs_implies_lib_extends_singleton_right : slow.

    Definition to_lib_per_ext4 {o}
               {lib} {F} {name}
               {f : {l : @library o $ lib_extends l (keep_only name lib)} -> per(o)}
               (E : forall lib' a b, F lib' (f exI(lib',a)) -> F lib' (f exI(lib',b)) -> (f exI(lib',a)) <=2=> (f exI(lib',b)))
               (C : forall x : {l : library $ lib_extends l (keep_only name lib)}, F (projT1 x) (f x)) : lib-per(keep_only name lib,o).
    Proof.
      exists (fun lib x => f (existT _ lib x)).
      introv.
      pose proof (C (existT _ lib' e)) as a.
      pose proof (C (existT _ lib' y)) as b.
      simpl in *.
      apply E; auto.
    Defined.

    Lemma in_ext_ext_per_choice4 {o} :
      forall name (lib : @library o) (F : forall lib' (p : per(o)), Prop),
        (forall lib' a b, F lib' a -> F lib' b -> a <=2=> b)
        -> in_ext_ext
             (keep_only name lib)
             (fun lib' x => exists (e : per(o)), F lib' e)
        ->
        exists (f : lib-per(keep_only name lib,o)),
        forall lib' (x : lib_extends lib' (keep_only name lib)),
          F lib' (f lib' x).
    Proof.
      introv imp h.

      pose proof (DependentFunctionalChoice_on
                    {l : library & lib_extends l (keep_only name lib)}
                    (fun x => per(o))
                    (fun l e => F (projT1 l) e)) as C.
      simpl in C.
      repeat (autodimp C hyp).
      { introv; destruct x; simpl in *; tcsp. }
      exrepnd.

      assert (forall lib' a b, F lib' (f exI(lib',a)) -> F lib' (f exI(lib',b)) -> (f exI(lib',a)) <=2=> (f exI(lib',b))) as E.
      { introv u v; eapply imp; eauto. }
      simpl in *.

      exists (to_lib_per_ext4 E C0); simpl; auto.
      introv.
      pose proof (C0 (existT _ lib' x)) as q; simpl in *; auto.
    Qed.

    Definition sub_per_contains_atmost {o} name (p1 p2 : per(o)) :=
      forall a b,
        contains_atmost name a
        -> contains_atmost name b
        -> p1 a b
        -> p2 a b.

    Definition inf_lib_cons_lib {o}
               (e : @inf_library_entry o)
               (lib : library) : inf_library :=
      fun n =>
        if deq_nat n 0 then e
        else library2inf lib e (pred n).


    (* Assuming that the infinite library [infLib] extends [keep_only name lib],
       we generate an infinite library that extends lib. *)
    Definition extend_inf_library_from_keep_only {o}
               name
               (lib : @library o)
               (infLib : @inf_library o) : inf_library :=
      fun n =>
        if same_entry_name_dec (entry_name_cs name) (inf_entry2name (infLib n))
        then infLib n
        else match find_entry_sign lib (inf_entry2name (infLib n)) with
             | Some e => library_entry2inf e
             | None => infLib n
             end.

    Lemma shift_inf_lib_inf_lib_cons_lib {o} :
      forall e (lib : @library o),
        shift_inf_lib (inf_lib_cons_lib e lib)
        = library2inf lib e.
    Proof.
      introv; apply functional_extensionality; introv; simpl.
      unfold shift_inf_lib; simpl.
      unfold inf_lib_cons_lib; simpl; auto.
    Qed.
    Hint Rewrite @shift_inf_lib_inf_lib_cons_lib : slow.

    Lemma implies_entry_in_inf_library_extends_inf_lib_cons_lib {o} :
      forall name c e entry (lib : @library o),
        entry_in_library entry lib
        -> inf_entry_extends e (lib_cs name c)
        -> !same_entry_name (entry_name_cs name) (entry2name entry)
        -> exists n, entry_in_inf_library_extends entry n (inf_lib_cons_lib e lib).
    Proof.
      induction lib; introv h q ns; simpl in *; tcsp.
      repndors; repnd; subst; tcsp.

      { exists 2; simpl.
        unfold inf_lib_cons_lib; simpl.
        right; dands; tcsp.

        { destruct e; simpl in *; repnd; subst; tcsp. }

        left.
        unfold shift_inf_lib; simpl.
        unfold inf_entry_extends; simpl.
        unfold library2inf; simpl.
        destruct a; simpl in *; tcsp.
        dands; tcsp; eauto 3 with slow. }

      { repeat (autodimp IHlib hyp); exrepnd.
        destruct n; simpl in *; tcsp.
        repndors; repnd.

        { unfold inf_lib_cons_lib in *; simpl in *.
          exists 1; simpl; tcsp. }

        rewrite shift_inf_lib_inf_lib_cons_lib in IHlib0.
        exists (S (S n)); simpl; right; dands; tcsp.
        right.
        rewrite shift_inf_lib_inf_lib_cons_lib; simpl.
        dands; tcsp;[].
        unfold library2inf; simpl.
        unfold inf_lib_cons_lib in IHlib1; simpl in *.
        intro xx; apply inf_matching_entries_library_entry2inf_implies in xx; tcsp.
        apply matching_entries_sym in xx; tcsp. }
    Qed.

    Lemma inf_lib_extends_ext_entries_inf_lib_cons_lib {o} :
      forall name (lib : @library o) c e,
        find_cs lib name = Some c
        -> inf_entry_extends e (lib_cs name c)
        -> inf_lib_extends_ext_entries (inf_lib_cons_lib e lib) lib.
    Proof.
      introv h i j.
      destruct (same_entry_name_dec (entry_name_cs name) (entry2name entry)).

      { left.
        applydup @find_cs_some_implies_entry_in_library in h.
        applydup same_entry_name_cs_implies_eq in s.
        pose proof (two_entries_in_library_with_same_name (lib_cs name c) entry name lib) as q.
        simpl in q; repeat (autodimp q hyp);[]; subst.
        simpl in *; GC.
        exists 1; simpl; left.
        unfold inf_lib_cons_lib; simpl; auto. }

      { left.
        eapply implies_entry_in_inf_library_extends_inf_lib_cons_lib; eauto. }
    Qed.
    Hint Resolve inf_lib_extends_ext_entries_inf_lib_cons_lib : slow.

    Lemma entry_in_inf_library_inf_lib_cons_lib_implies {o} :
      forall entry e (lib : @library o),
        entry_in_inf_library entry (inf_lib_cons_lib e lib)
        -> entry = e
           \/ entry_in_inf_library entry (library2inf lib e).
    Proof.
      introv h.
      unfold entry_in_inf_library in h; repndors; exrepnd.

      { destruct n; simpl in *; tcsp;[].
        repndors; repnd; subst; tcsp;[].
        autorewrite with slow in *.
        right.
        left; exists n; auto. }

      unfold inf_entry_in_inf_library_default in h; repnd.
      right.
      right.
      unfold inf_entry_in_inf_library_default.
      dands; tcsp.
      introv m.
      destruct (h0 (S n)).
      unfold inf_lib_cons_lib; simpl; auto.
    Qed.

    Lemma matching_inf_entries_implies_matching_entries {o} :
      forall (e1 e2 : @library_entry o),
        matching_inf_entries (library_entry2inf e1) (library_entry2inf e2)
        -> matching_entries e1 e2.
    Proof.
      introv m.
      destruct e1, e2; simpl in *; tcsp.
    Qed.
    Hint Resolve matching_inf_entries_implies_matching_entries : slow.

    Lemma implies_entry_in_lib_library_library_entry2inf {o} :
      forall e x (lib : @library o),
        entry_in_library e lib
        -> entry_in_inf_library (library_entry2inf e) (library2inf lib x).
    Proof.
      induction lib; introv h; simpl in *; tcsp.
      repndors; repnd; subst; tcsp.

      { unfold library2inf; simpl.
        left; exists 1; simpl; tcsp. }

      repeat (autodimp IHlib hyp).
      unfold entry_in_inf_library in *; repndors; exrepnd.

      { left.
        exists (S n); simpl; right; dands; tcsp.
        unfold library2inf; simpl.
        intro xx; destruct h0; eauto 3 with slow. }

      right.
      unfold inf_entry_in_inf_library_default in *; repnd; dands; auto.
      introv m.
      unfold library2inf in *; simpl in *.
      destruct n; simpl in *; tcsp.
      destruct h0; eauto 3 with slow.
    Qed.
    Hint Resolve implies_entry_in_lib_library_library_entry2inf : slow.

    Lemma implies_safe_inf_library_inf_lib_cons_lib {o} :
      forall name c e (lib : @library o),
        find_cs lib name = Some c
        -> inf_entry_extends e (lib_cs name c)
        -> safe_inf_library_entry e
        -> safe_library lib
        -> safe_inf_library (inf_lib_cons_lib e lib).
    Proof.
      introv fd ext safee safe i.
      apply entry_in_inf_library_inf_lib_cons_lib_implies in i.
      repndors; subst; tcsp;[].
      unfold entry_in_inf_library in i; repndors; exrepnd.

      { apply entry_in_inf_library_n_library2inf_implies in i0; repndors; subst; auto.
        exrepnd; subst; eauto 3 with slow.
        pose proof (implies_safe_inf_library_library2inf lib e) as q.
        repeat (autodimp q hyp).
        applydup safe in i0.
        eapply q; eauto 3 with slow. }

      { destruct i; tcsp. }
    Qed.
    Hint Resolve implies_safe_inf_library_inf_lib_cons_lib : slow.

    Lemma inf_lib_extends_inf_lib_cons_lib {o} :
      forall name (lib : @library o) c e,
        find_cs lib name = Some c
        -> inf_entry_extends e (lib_cs name c)
        -> safe_inf_library_entry e
        -> inf_lib_extends (inf_lib_cons_lib e lib) lib.
    Proof.
      introv fd h safe.
      split; eauto 3 with slow.
    Qed.
    Hint Resolve inf_lib_extends_inf_lib_cons_lib : slow.

    Lemma implies_inf_matching_entries_if_extends {o} :
      forall ie1 ie2 (e : @library_entry o),
        inf_entry_extends ie1 e
        -> matching_inf_entries ie2 ie1
        -> inf_matching_entries ie2 e.
    Proof.
      introv ext m.
      destruct ie1, ie2, e; simpl in *; repnd; subst; tcsp.
    Qed.
    Hint Resolve implies_inf_matching_entries_if_extends : slow.

    (* What's the relation between [e] and [e']?  If [t1] is [Free(0)], which is
       free of choice sequences, then if we keep only 1 choice sequence ([name]),
       don't we also reduce its equality? *)
    Lemma implies_close_keep_only {o} :
      forall name lib (u : cts(o)) (t1 t2 : @CTerm o) e,
        contains_atmost name t1
        -> contains_atmost name t2
        -> safe_library lib
        -> local_ts u
        -> ts_implies_per_bar u
        -> type_system u
        -> defines_only_universes u
        -> type_monotone u
        -> (forall lib t1 t2 e,
               contains_atmost name t1
               -> contains_atmost name t2
               -> u lib t1 t2 e
               -> exists e',
                   u (keep_only name lib) t1 t2 e'
                   /\ sub_per_contains_atmost name e e')
        -> close u lib t1 t2 e
        -> exists e',
            close u (keep_only name lib) t1 t2 e'
            /\ sub_per_contains_atmost name e e'.
    Proof.
      introv conta contb safe local tsimp tysys dou mon imp cl.
      close_cases (induction cl using @close_ind') Case; introv; subst.

      { Case "CL_init".
        pose proof (imp lib T T' eq) as imp; repeat (autodimp imp hyp); exrepnd.
        exists e'; dands; auto.
      }

      { Case "CL_bar".
        clear per.

        admit.
      }

      { Case "CL_int".
        unfold per_int in per; repnd.
        exists (equality_of_int_bar (keep_only name lib)).
        dands; eauto 3 with slow.

        { apply CL_int; unfold per_int.
          dands; spcast; auto; try (apply contains_only_implies_computes_to_valc_keep_only); auto. }

        Lemma sub_per_contains_atmost_int {o} :
          forall name lib (eq : per(o)),
            (eq <=2=> (equality_of_int_bar lib))
            -> sub_per_contains_atmost name eq (equality_of_int_bar (keep_only name lib)).
        Proof.
          introv h conta contb q.
          apply h in q.
          clear dependent eq.
          unfold equality_of_int_bar, all_in_ex_bar in *; exrepnd.

          (* The bar is not correct because if we have another name, say [name'],
             we need a bar that covers both name'(0) = 0 and name'(0) = 1,
             but our current bar [bar], might just cover one because lib sets name'(0)
             to say [0]... *)
          Definition bar_keep_only {o}
                     name {lib}
                     (safe : safe_library lib)
                     (bar : @BarLib o lib) : BarLib (keep_only name lib).
          Proof.
            exists (fun (lib0 : library) =>
                      exists lib1,
                        bar_lib_bar bar lib1
                        /\ lib_extends lib0 (keep_only name lib1)).

            - introv e.
              destruct bar as [bar1 bars1 ext1].
              simpl in *.

              remember (find_cs lib name) as fd; symmetry in Heqfd; destruct fd.

              { rewrite keep_only_equal in e; rewrite keep_only_equal.
                rewrite Heqfd in e; rewrite Heqfd.
                pose proof (inf_lib_extends_ext _ _ e (lib_cs name c)) as q.
                simpl in q; autodimp q hyp.
                repndors; exrepnd.

                { apply inf_library_extends_implies in q0; exrepnd.
                  pose proof (bars1 (inf_lib_cons_lib (infLib k) lib)) as q.
                  autodimp q hyp; eauto 3 with slow.

                  { eapply inf_lib_extends_inf_lib_cons_lib; eauto.
                    apply inf_lib_extends_safe in e; tcsp.
                    { apply e; eauto 3 with slow.
                      apply implies_entry_in_inf_library; introv xx mm.
                      pose proof (q1 m) as q1; autodimp q1 hyp; destruct q1.
                      eauto 3 with slow. }

                    introv i; simpl in *; repndors; subst; tcsp.
                    apply find_cs_some_implies_entry_in_library in Heqfd.
                    apply safe in Heqfd; auto. }

                  exrepnd.
                  exists (keep_only name lib').
                  dands; eauto 3 with slow.
                  { apply (implies_lib_extends_keep_only name) in q5; auto.
                    rewrite (keep_only_equal name lib) in q5.
                    rewrite Heqfd in q5; auto. }

                

XXXXXXXXXXXXXX

              SearchAbout inf_library library choice_sequence_name.
              Locate library2inf_def.

              Print BarLibBars.
              pose proof (bars1 (keep_only name lib)) as q.
              exists (keep_only name lib); dands; eauto 3 with slow.
              exists lib; dands; auto.

              pose proof (bars1 (swap_cs_inf_lib_norm sw infLib)) as q; autodimp q hyp; eauto 3 with slow;[].
              exrepnd.
              exists (swap_cs_lib sw lib').
              dands; eauto 3 with slow;[].

              destruct e as [xt1 safe1].
              destruct q0 as [xt2 safe2].
              autodimp safe1 hyp; eauto 3 with slow;[].
              autodimp safe2 hyp; eauto 3 with slow;[].
              split; eauto 3 with slow.

              introv i.
              apply entry_in_swap_library_implies in i; exrepnd; subst.
              applydup xt2 in i1.
              repndors; exrepnd;[left;exists n|right]; eauto 3 with slow.

              { unfold swap_cs_inf_lib_norm in i2; simpl in i2.
                apply inf_library_extends_implies in i2; exrepnd.
                apply (inf_entry_extends_implies_entry_in_inf_library_extends_same_names_lt k n _ (swap_cs_lib_entry sw e));
                  auto; eauto 3 with slow;
                    [|introv ltk; apply i0 in ltk; autorewrite with slow;
                      rewrite <- (inf_matching_entries_swap_norm_iff sw);
                      pose proof (swap_cs_lib_entry_idem sw e) as q;
                      repeat (autodimp q hyp); eauto 3 with slow];[].

                (* bars are different for choice sequences with different name spaces... *)

          (*XXXXXXXXX
        exrepnd.

        pose proof (intersect_inf_lib_extends2 infLib lib' lib'0) as h.
        repeat (autodimp h hyp).
        exrepnd.
        exists lib0; dands; eauto 3 with slow.
        exists lib'0; dands; eauto 3 with slow.

      - introv h; exrepnd; auto.*)

          Defined.

          SearchAbout BarLib lib_extends.

          SearchAbout BarLib keep_only.
        Qed.


        apply CL_int; unfold per_int.
        dands; spcast; auto; try (apply contains_only_implies_computes_to_valc_keep_only); auto. }

      { Case "CL_nat".
        unfold per_nat in per; repnd.
        exists (equality_of_nat_bar (keep_only name lib)).
        apply CL_nat; unfold per_nat.
        dands; spcast; auto; try (apply contains_only_implies_computes_to_valc_keep_only); auto. }

      { Case "CL_csname".
        unfold per_csname in per; exrepnd.
        exists (equality_of_csname_bar (keep_only name lib) n).
        apply CL_csname; unfold per_csname.
        exists n.
        dands; spcast; auto; try (apply contains_only_implies_computes_to_valc_keep_only); auto. }

      { Case "CL_atom".
        unfold per_atom in per; exrepnd.
        exists (equality_of_atom_bar (keep_only name lib)).
        apply CL_atom; unfold per_atom.
        dands; spcast; auto; try (apply contains_only_implies_computes_to_valc_keep_only); auto. }

      { Case "CL_uatom".
        unfold per_uatom in per; exrepnd.
        exists (equality_of_uatom_bar (keep_only name lib)).
        apply CL_uatom; unfold per_uatom.
        dands; spcast; auto; try (apply contains_only_implies_computes_to_valc_keep_only); auto. }

      { Case "CL_base".
        unfold per_base in per; exrepnd.
        exists (per_base_eq (keep_only name lib)).
        apply CL_base; unfold per_base.
        dands; spcast; auto; try (apply contains_only_implies_computes_to_valc_keep_only); auto. }

      { Case "CL_approx".
        unfold per_approx in per; exrepnd.
        exists (per_approx_eq_bar (keep_only name lib) a b).
        apply CL_approx; unfold per_approx.
        exists a b c d.
        dands; spcast; auto; try (apply contains_only_implies_computes_to_valc_keep_only); auto.

        admit. }

      { Case "CL_cequiv".
        unfold per_cequiv in per; exrepnd.
        exists (per_cequiv_eq_bar (keep_only name lib) a b).
        apply CL_cequiv; unfold per_cequiv.
        exists a b c d.
        dands; spcast; auto; try (apply contains_only_implies_computes_to_valc_keep_only); auto.

        admit. }

      { Case "CL_eq".
        clear per.

        assert (in_ext_ext
                  lib
                  (fun (lib' : library) (_ : lib_extends lib' lib) =>
                     exists e', close ts (keep_only name lib') A B e')) as q.
        { introv xt; pose proof (reca _ xt) as reca; simpl in *; spcast.
          apply (computes_to_valc_preserves_contains_only name) in c1; auto.
          apply (computes_to_valc_preserves_contains_only name) in c2; auto.
          allrw @contains_atmost_mkc_equality; repnd.
          repeat (autodimp reca hyp); eauto 3 with slow. }
        clear reca.

        assert (in_ext_ext
                  (keep_only name lib)
                  (fun lib' (e : lib_extends lib' (keep_only name lib)) =>
                     exists e', close ts lib' A B e')) as z.
        { introv ext.
          assert (safe_library lib') as safe' by eauto 3 with slow.
          remember (find_cs lib name) as fd; symmetry in Heqfd; destruct fd.

          { pose proof (q (keep_only name lib' ++ lib) (implies_lib_extends_keep_only_app _ _ _ ext)) as h; simpl in h; exrepnd.
            rewrite keep_only_equal in ext.
            rewrite Heqfd in ext.
            eapply (lib_extends_preserves_find_cs _ _ name) in ext;
              [|simpl; boolvar; try reflexivity; tcsp].
            exrepnd.
            rewrite (keep_only_equal name lib') in h0.
            rewrite ext1 in h0; simpl in h0; boolvar; tcsp; GC.
            pose proof (close_monotone ts) as z; autodimp z hyp.
            pose proof (z [lib_cs name entry2] lib' A B e') as z.
            repeat (autodimp z hyp); eauto 3 with slow. }

          { rewrite keep_only_equal in ext.
            rewrite Heqfd in ext.
            pose proof (q (keep_only name lib' ++ lib)) as h; simpl in h; autodimp h hyp; eauto 3 with slow.
            apply implies_lib_extends_keep_only_app.
            rewrite keep_only_equal; allrw; auto. } }
        clear q.

        pose proof (in_ext_ext_per_choice4 name lib (fun lib' e => close ts lib' A B e)) as w.
        simpl in w; repeat (autodimp w hyp).
        { introv cl1 cl2.
          eapply close_uniquely_valued; try exact cl1; try exact cl2; auto. }
        exrepnd.

        exists (eq_per_eq_bar (keep_only name lib) a1 a2 f).
        apply CL_eq; unfold per_eq.
        exists A B a1 a2 b1 b2 f.
        dands; auto; spcast;
          try (apply contains_only_implies_computes_to_valc_keep_only; auto).

        Lemma implies_eqorceq_ext_keep_only {o} :
          forall name lib ts
                 (eqa : lib-per(lib,o))
                 (eqb : lib-per(keep_only name lib,o))
                 (A B : @CTerm o)
                 (a b : @CTerm o),
            contains_atmost name a
            -> contains_atmost name b
            -> in_ext_ext lib (fun lib' x => close ts lib' A B (eqa lib' x))
            -> in_ext_ext (keep_only name lib) (fun lib' x => close ts lib' A B (eqb lib' x))
            -> eqorceq_ext lib eqa a b
            -> eqorceq_ext (keep_only name lib) eqb a b.
        Proof.
          introv conta contb exta extb eoc; introv.
          remember (find_cs lib name) as fd; symmetry in Heqfd; destruct fd.

          { pose proof (eoc (keep_only name lib' ++ lib) (implies_lib_extends_keep_only_app _ _ _ e)) as eoc; simpl in eoc; exrepnd.
            dup e as ext.
            rewrite keep_only_equal in ext.
            rewrite Heqfd in ext.
            eapply (lib_extends_preserves_find_cs _ _ name) in ext;
              [|simpl; boolvar; try reflexivity; tcsp].
            exrepnd.
            remember (implies_lib_extends_keep_only_app name lib' lib e) as z; clear Heqz.
            revert dependent z.
            rewrite (keep_only_equal name lib'); allrw; introv eoc; simpl in *.
            unfold eqorceq in *; repndors;[left|right].

            {


            rewrite ext1 in h0; simpl in h0; boolvar; tcsp; GC.
            pose proof (close_monotone ts) as z; autodimp z hyp.
            pose proof (z [lib_cs name entry2] lib' A B e') as z.
            repeat (autodimp z hyp); eauto 3 with slow. }

        Qed.

      }

    Abort.

  Admitted.

  Lemma implies_swap_inf_lib_extends {o} :
    forall sw infLib (lib : @library o),
      sane_swapping sw
      -> safe_library lib
      -> safe_library_sw sw lib
      -> inf_lib_extends infLib lib
      -> inf_lib_extends (swap_cs_inf_lib sw infLib) (swap_cs_lib sw lib).
  Proof.
    introv sane safe1 safe2 ext.
    destruct ext as [ext safe].
    split; eauto 3 with slow;[].
    introv safecs i.
    autodimp safe hyp;[].
    unfold entry_in_inf_library in i; repndors; exrepnd.

    { apply swap_entry_in_inf_library_n_right in i0; exrepnd; subst.
      pose proof (safe e) as q; autodimp q hyp.
      { left; eauto. }
  Abort.

  Definition swap_cs_bar {o} {lib}
             (sw     : cs_swap)
             (bar    : @BarLib o lib)
             (sane   : sane_swapping sw)
             (swin   : swapping_in_library sw lib)
             (safe   : safe_library lib)
             (safesw : safe_library_sw sw lib)
    : @BarLib o (swap_cs_lib sw lib).
  Proof.
    exists (fun (lib0 : library) =>
              exists lib1,
                bar_lib_bar bar lib1
                /\ lib_extends lib0 (swap_cs_lib sw lib1)).

    - introv e.
      destruct bar as [bar1 bars1 ext1].
      simpl in *.

      pose proof (bars1 (swap_cs_inf_lib_norm sw infLib)) as q; autodimp q hyp; eauto 3 with slow;[].
      exrepnd.
      exists (swap_cs_lib sw lib').
      dands; eauto 3 with slow;[].

      destruct e as [xt1 safe1].
      destruct q0 as [xt2 safe2].
      autodimp safe1 hyp; eauto 3 with slow;[].
      autodimp safe2 hyp; eauto 3 with slow;[].
      split; eauto 3 with slow.

      introv i.
      apply entry_in_swap_library_implies in i; exrepnd; subst.
      applydup xt2 in i1.
      repndors; exrepnd;[left;exists n|right]; eauto 3 with slow.

      { unfold swap_cs_inf_lib_norm in i2; simpl in i2.
        apply inf_library_extends_implies in i2; exrepnd.
        apply (inf_entry_extends_implies_entry_in_inf_library_extends_same_names_lt k n _ (swap_cs_lib_entry sw e));
          auto; eauto 3 with slow;
            [|introv ltk; apply i0 in ltk; autorewrite with slow;
              rewrite <- (inf_matching_entries_swap_norm_iff sw);
              pose proof (swap_cs_lib_entry_idem sw e) as q;
              repeat (autodimp q hyp); eauto 3 with slow];[].

        (* bars are different for choice sequences with different name spaces... *)

(*XXXXXXXXX
        exrepnd.

        pose proof (intersect_inf_lib_extends2 infLib lib' lib'0) as h.
        repeat (autodimp h hyp).
        exrepnd.
        exists lib0; dands; eauto 3 with slow.
        exists lib'0; dands; eauto 3 with slow.

      - introv h; exrepnd; auto.*)
    Abort.

Lemma implies_close_swap_cs {o} :
  forall sw lib (u : cts(o)) (t1 t2 : @CTerm o) e,
    (forall lib t1 t2 e,
        u lib t1 t2 e
        -> u (swap_cs_lib sw lib)
             (swap_cs_cterm sw t1)
             (swap_cs_cterm sw t2)
             (swap_cs_per sw e))
    -> close u lib t1 t2 e
    -> close
         u
         (swap_cs_lib sw lib)
         (swap_cs_cterm sw t1)
         (swap_cs_cterm sw t2)
         (swap_cs_per sw e).
Proof.
  introv imp cl.
  close_cases (induction cl using @close_ind') Case; introv; subst.

  { Case "CL_init".
    apply CL_init.
    apply imp; auto.
  }

  { Case "CL_bar".
    clear per.
    apply CL_bar.
    unfold per_bar.

(*xxxxxx
    Locate raise_bar.
    exists (raise_bar bar ext) (ren_cs_lib_per (name1,name2) ext eqa).
    dands.

    - introv br xt; introv; simpl in *; exrepnd.
      pose proof (reca _ br1 _ (lib_extends_trans xt br2) (lib_extends_trans x ext)) as reca; simpl in *.
      repeat (autodimp reca hyp); eauto 3 with slow.
      pose proof (reca lib'1) as reca; repeat (autodimp reca hyp); eauto 3 with slow.

      {
      }
    SearchAbout BarLib lib_extends.
  }
*)
Abort.

  (* TODO *)
  Lemma swap_preserves_member {o} :
    forall sw lib (t T : @CTerm o),
      member lib t T
      -> member (swap_cs_lib sw lib) (swap_cs_cterm sw t) (swap_cs_cterm sw T).
  Proof.
    introv mem.
    unfold member in *.
    unfold equality in *; exrepnd.
    exists (swap_cs_per sw eq); simpl; dands; tcsp;
      [|unfold swap_cs_per; autorewrite with slow; auto];[].

  Admitted.



  apply (member_implies_contains_only name) in eqz; auto;
    [|admit|admit].

  apply (swap_preserves_member (name,name')) in eqz.

  rewrite swap_cs_cterm_apply in eqz.
  rewrite swap_cs_cterm_mkc_choice_seq_same in eqz.
  rewrite (swap_cs_cterm_if_nodefsc _ u) in eqz; auto;[].

  assert (lib_extends lib []) as xtn by eauto 3 with slow.

  rewrite keep_only_equal in eqz.
  remember (find_cs lib1 name) as fcs; symmetry in Heqfcs.
  destruct fcs; simpl in *;
    [|eapply member_monotone in eqz;[|exact xtn] ].

  { boolvar; tcsp; GC;[].
    rewrite (swap_cs_choice_seq_entry_0 _ _ lib1) in eqz; auto;[].

    assert (lib_extends lib [lib_cs name' (MkChoiceSeqEntry _ (cse_vals c) (swap_cs_choice_seq_restr (name,name') (cse_restriction c)))]) as xt.
    {

    }

  }


XXXXXXXXXXXXXXXx

  pose proof (swap_cs_member lib1 (name,name') z1 (mkc_apply u (mkc_choice_seq name))) as equ'.
  autodimp equ' hyp.
  rewrite swap_cs_cterm_apply in equ'.
  rewrite swap_cs_cterm_mkc_choice_seq_same in equ'.
  rewrite (swap_cs_cterm_if_nodefsc _ u) in equ'; auto;[].

  Lemma implies_lib_extends_swap_cs_lib {o} :
    forall name name' (lib lib1 : @library o),
      lib_extends lib lib1
      -> (forall m : nat,
             m < lib_size lib1
             -> {k : nat
                 $ find_cs_value_at lib name m = Some (mkc_nat k)
                 # find_cs_value_at lib name' m = Some (mkc_nat k)})
      -> lib_extends lib (swap_cs_lib (name,name') lib1).
  Proof.
    introv ext imp.
    destruct ext as [ext safe sub].
    split.

    { introv i.
      apply (swap_entry_in_library (name,name')) in i.
      rewrite swap_cs_lib_idem in i.
      apply ext in i.

      (* This is not provable because other parts of the library will be renamed too *)


    }

  Abort.

  assert (lib_extends lib (swap_cs_lib (name,name') lib1)) as ext'.
  { }
*)





Fixpoint replace_first_vals_with {o}
         (lib   : @library o)
         (name  : choice_sequence_name)
         (vals  : @ChoiceSeqVals o)
         (restr : @ChoiceSeqRestriction o): library :=
  match lib with
  | [] => [lib_cs name (MkChoiceSeqEntry _ vals restr)]
  | entry :: entries =>
    match entry with
    | lib_cs name' (MkChoiceSeqEntry _ vals' restr) =>
      if choice_sequence_name_deq name name' then
        let n := length vals in
        lib_cs name' (MkChoiceSeqEntry _ (vals ++ skipn n vals') restr) :: entries
      else entry :: replace_first_vals_with entries name vals restr
    | _ => entry :: replace_first_vals_with entries name vals restr
    end
  end.

Definition ren_cs_lib_upto {o}
         (r   : cs_ren)
         (lib : @library o) :=
  let (name1,name2) := r in
  match find_cs lib name1 with
  | Some (MkChoiceSeqEntry _ vals1 restr1) => replace_first_vals_with lib name1 vals1 restr1
  | None => lib
  end.

(*
(* Inspired from name_invariance stuff *)
Lemma implies_close_ren_cs {o} :
  forall name1 name2 lib (u : cts(o)) (t1 t2 : @CTerm o) e,
    name1 <> name2
    -> up_to_namec name1 t1
    -> up_to_namec name1 t2
    -> (forall lib t1 t2 e,
           u lib t1 t2 e
           -> u (ren_cs_lib_upto (name1,name2) lib)
                (ren_cs_cterm (name1,name2) t1)
                (ren_cs_cterm (name1,name2) t2)
                (ren_cs_per (name1,name2) e))
    -> close u lib t1 t2 e
    -> close
         u
         (ren_cs_lib_upto (name1,name2) lib)
         (ren_cs_cterm (name1,name2) t1)
         (ren_cs_cterm (name1,name2) t2)
         (ren_cs_per (name1,name2) e).
Proof.
  introv dn upto1 upto2 imp cl.
  close_cases (induction cl using @close_ind') Case; introv; subst.

  { Case "CL_init".
    apply CL_init.
    apply imp; auto.
  }

  { Case "CL_bar".
    clear per.
    apply CL_bar.
    unfold per_bar.


    Definition raise_bar_ren_cs_upto {o} {lib}
               (r   : cs_ren)
               (bar : @BarLib o lib) : @BarLib o (ren_cs_lib_upto r lib).
    Proof.
      Print bar_lib.
      exists (fun (lib0 : library) =>
                exists lib1,
                  bar_lib_bar bar lib1
                  /\ lib_extends lib0 (ren_cs_lib_upto r lib1)).

      - introv e.
        destruct bar as [bar1 bars1 ext1].
        simpl in *.

        pose proof (bars1 infLib) as q; autodimp q hyp; eauto 3 with slow.
        exrepnd.

        pose proof (intersect_inf_lib_extends2 infLib lib' lib'0) as h.
        repeat (autodimp h hyp).
        exrepnd.
        exists lib0; dands; eauto 3 with slow.
        exists lib'0; dands; eauto 3 with slow.

      - introv h; exrepnd; auto.
    Defined.

    Locate raise_bar.
    exists (raise_bar bar ext) (ren_cs_lib_per (name1,name2) ext eqa).
    dands.

    - introv br xt; introv; simpl in *; exrepnd.
      pose proof (reca _ br1 _ (lib_extends_trans xt br2) (lib_extends_trans x ext)) as reca; simpl in *.
      repeat (autodimp reca hyp); eauto 3 with slow.
      pose proof (reca lib'1) as reca; repeat (autodimp reca hyp); eauto 3 with slow.

      {
      }
    SearchAbout BarLib lib_extends.
  }

Qed
 *)

Definition empty_choice_seq_entry {o} (e :  @ChoiceSeqEntry o) :=
  match e with
  | MkChoiceSeqEntry _ vals restr => MkChoiceSeqEntry _ [] restr
  end.

Definition bar_per {o} {lib} (bar : @BarLib o lib) :=
  forall lib1 (b : bar_lib_bar bar lib1)
         lib2 (ext : lib_extends lib2 lib1)
         (x : lib_extends lib2 lib), per(o).

Definition bar_per2per {o} {lib} {bar : @BarLib o lib} (p : bar_per bar) : per :=
  fun t1 t2 =>
    forall lib1 (b : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      p lib1 b lib2 ext x t1 t2.

Lemma all_in_bar_ext_exists_per_implies {o} :
  forall {lib} (bar : @BarLib o lib) F,
    all_in_bar_ext bar (fun lib' x => exists (e : per(o)), F lib' e)
    ->
    exists (f : bar_per(bar)),
    forall lib1 (br : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      F lib2 (f lib1 br lib2 ext x).
Proof.
  introv h.
  pose proof (DependentFunctionalChoice_on
                (pack_lib_bar bar)
                (fun x => per(o))
                (fun x b => F (plb_lib2 bar x) b)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv; destruct x; simpl in *; eapply h; eauto. }
  exrepnd.
  exists (fun lib1 (br : bar_lib_bar bar lib1) lib2 (ext : lib_extends lib2 lib1) (x : lib_extends lib2 lib) =>
            (f (MkPackLibBar lib1 br lib2 ext x))).
  introv.
  pose proof (C0 (MkPackLibBar lib1 br lib2 ext x)) as w; auto.
Qed.

(*Lemma empty_entry_in_library_rename_cs_lib {o} :
  forall name entry (lib : @library o),
    entry_in_library (lib_cs name entry) lib
    -> entry_in_library (lib_cs name (empty_choice_seq_entry entry))
                        (remove_cs_lib name lib).
Proof.
  induction lib; introv h; simpl in *; tcsp.
  repndors; subst; simpl in *; boolvar; tcsp.
  repnd; destruct a; simpl; boolvar; tcsp.
Qed.
Hint Resolve empty_entry_in_library_rename_cs_lib : slow.*)

Definition inf_library_fill_removed {o}
           (name   : choice_sequence_name)
           (lib    : @library o)
           (infLib : @inf_library o)
  : @inf_library o :=
  match find_cs lib name with
  | Some e =>
    fun n =>
      match infLib n with
      | inf_lib_cs name' e =>
        if choice_sequence_name_deq name name'
        then inf_lib_cs name' e
        else
      end
  | None => infLib
  end.

(*
match find_cs lib name with
  | Some e =>
    fun n =>
      if deq_nat n 0 then inf_lib_cs name (choice_seq_entry2inf e)
      else infLib (pred n)
  | None => infLib
  end.
*)

(*Proof.
  introv n.
  pose proof (infLib n) as e.
  destruct e;[|exact (inf_lib_abs opabs vars rhs correct)].
  destruct (choice_sequence_name_deq name name0) as [d|d];
    [|exact (inf_lib_cs name0 entry)].
  subst.
  remember (find_cs lib name0) as q; symmetry in Heqq; destruct q.
  { exact (inf_lib_cs name0 (choice_seq_entry2inf c)). }
  { exact (inf_lib_cs name0 entry). }
Defined.*)

Lemma entry_in_library_remove_cs_lib_if_diff {o} :
  forall name name' entry (lib : @library o),
    name <> name'
    -> entry_in_library (lib_cs name' entry) lib
    -> entry_in_library (lib_cs name' entry) (remove_cs_lib name lib).
Proof.
  induction lib; introv d i; simpl in *; tcsp.
  repndors; repnd; tcsp;
    destruct a; simpl in *; boolvar; subst; tcsp; simpl in *; ginv; tcsp.
Qed.
Hint Resolve entry_in_library_remove_cs_lib_if_diff : slow.

Lemma entry_abs_in_remove_cs_lib {o} :
  forall opabs vars rhs correct name (lib : @library o),
    entry_in_library (lib_abs opabs vars rhs correct) lib
    -> entry_in_library (lib_abs opabs vars rhs correct) (remove_cs_lib name lib).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; tcsp.
Qed.
Hint Resolve entry_abs_in_remove_cs_lib : slow.

Lemma entry_in_remove_cs_lib_implies {o} :
  forall entry name (lib : @library o),
    entry_in_library entry (remove_cs_lib name lib)
    ->
    (entry_in_library entry lib
     /\ entry2name entry <> entry_name_cs name)
    \/
    exists e,
      entry_in_library (lib_cs name e) lib
      /\ entry = lib_cs name (empty_choice_seq_entry e).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; simpl in *; subst; ginv;
    repndors; repnd; subst; tcsp;
      try (complete (simpl; left; dands; tcsp; introv xx; inversion xx; subst; tcsp));
      try (complete (autodimp IHlib hyp; repndors; exrepnd; subst; tcsp;
                     right; exists e; dands; auto));
      try (complete (right; exists entry0; dands; auto)).
Qed.

Lemma safe_empty_choice_seq_entry {o} :
  forall name (e : @ChoiceSeqEntry o),
    safe_choice_sequence_entry name e
    -> safe_choice_sequence_entry name (empty_choice_seq_entry e).
Proof.
  introv safe.
  destruct e; simpl in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve safe_empty_choice_seq_entry : slow.

Lemma safe_remove_cs_lib {o} :
  forall name (lib : @library o),
    safe_library lib
    -> safe_library (remove_cs_lib name lib).
Proof.
  introv safe i.
  apply entry_in_remove_cs_lib_implies in i; repndors; tcsp;[].
  exrepnd; subst.
  apply safe in i1; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve safe_remove_cs_lib : slow.

Lemma safe_inf_library_fill_removed {o} :
  forall name lib (infLib : @inf_library o),
    safe_library lib
    -> safe_inf_library infLib
    -> safe_inf_library (inf_library_fill_removed name lib infLib).
Proof.
  introv safelib safe i.
  unfold inf_library_fill_removed in *.
  remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; tcsp;[].
  applydup @find_cs_some_implies_entry_in_library in Heqfcs.
  apply safelib in Heqfcs0.
  unfold entry_in_inf_library in i; simpl in *.
  repndors; exrepnd.
  { destruct n; simpl in *; tcsp.
    repndors; subst; simpl in *; tcsp; eauto 3 with slow;[].
    repnd.
    unfold shift_inf_lib in i0; simpl in *.
    apply safe; left; exists n; auto. }
  { unfold inf_entry_in_inf_library_default in i; simpl in *; repnd.
    apply safe; right.
    unfold inf_entry_in_inf_library_default; dands; auto.
    introv.
    pose proof (i0 (S n)) as i0; simpl in *; auto. }
Qed.
Hint Resolve safe_inf_library_fill_removed : slow.

Lemma inf_lib_extends_inf_library_fill_removed {o} :
  forall name lib (infLib : @inf_library o),
    inf_lib_extends infLib (remove_cs_lib name lib)
    -> inf_lib_extends (inf_library_fill_removed name lib infLib) lib.
Proof.
  introv ext.
  destruct ext as [ext safe].
  split; simpl in *.

  { introv i.
    unfold inf_library_fill_removed.
    remember (find_cs lib name) as fcs; destruct fcs; symmetry in Heqfcs.

    { destruct entry.

      { applydup @entry_in_library_implies_find_cs_some in i.
        destruct (choice_sequence_name_deq name name0); subst.
        { rewrite i0 in Heqfcs; ginv.
          unfold inf_library_fill_removed; allrw.
          left; exists 1; simpl; left; dands; auto; eauto 3 with slow. }
        { pose proof (ext (lib_cs name0 entry)) as ext.
          autodimp ext hyp; eauto 3 with slow.
          repndors; exrepnd.
          { left; exists (S n0); simpl; right; dands; tcsp. }
          { right.
            unfold entry_in_inf_library_default in *; simpl in *; repnd.
            dands; tcsp.
            introv xx; boolvar; simpl in *; tcsp. } } }

      { pose proof (ext (lib_abs opabs vars rhs correct)) as ext.
        autodimp ext hyp; eauto 3 with slow;[].
        repndors; exrepnd.
        { left; exists (S n); simpl; right; dands; tcsp. }
        { right.
          unfold entry_in_inf_library_default in *; simpl in *; repnd.
          dands; tcsp. } } }

    { destruct entry.

      { applydup @entry_in_library_implies_find_cs_some in i.
        destruct (choice_sequence_name_deq name name0); subst.
        { rewrite i0 in Heqfcs; ginv. }
        { pose proof (ext (lib_cs name0 entry)) as ext.
          autodimp ext hyp; eauto 3 with slow. } }

      { pose proof (ext (lib_abs opabs vars rhs correct)) as ext.
        autodimp ext hyp; eauto 3 with slow. } } }

  { intro safelib; eauto 3 with slow.
    autodimp safe hyp; eauto 3 with slow. }
Qed.
Hint Resolve inf_lib_extends_inf_library_fill_removed : slow.

Lemma entry_in_library_extends_remove_cs_lib_if_diff {o} :
  forall entry name (lib : @library o),
    entry_in_library_extends entry lib
    -> entry2name entry <> entry_name_cs name
    -> entry_in_library_extends entry (remove_cs_lib name lib).
Proof.
  induction lib; introv i d; simpl in *; tcsp.
  repndors; repnd; destruct a, entry; simpl in *; boolvar; repnd;
    subst; simpl in *; tcsp; ginv.
Qed.
Hint Resolve entry_in_library_extends_remove_cs_lib_if_diff : slow.

Lemma entry_in_library_extends_remove_cs_lib_if_same {o} :
  forall e name (lib : @library o),
    entry_in_library_extends (lib_cs name e) lib
    -> entry_in_library_extends (lib_cs name (empty_choice_seq_entry e))
                                (remove_cs_lib name lib).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; destruct a, e; simpl in *; repnd; subst; boolvar; GC;
    simpl in *; tcsp; ginv;[].
  left; dands; tcsp; destruct entry.
  unfold choice_sequence_entry_extend in *; simpl in *.
  repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve entry_in_library_extends_remove_cs_lib_if_same : slow.

Lemma implies_lib_extends_entries_lr {o} :
  forall name (lib lib' : @library o),
    lib_extends_entries lib' lib
    -> lib_extends_entries (remove_cs_lib name lib') (remove_cs_lib name lib).
Proof.
  introv ext i.
  apply entry_in_remove_cs_lib_implies in i.
  repndors; exrepnd; eauto 3 with slow.
  subst; simpl in *.
  apply ext in i1; eauto 3 with slow.
Qed.
Hint Resolve implies_lib_extends_entries_lr : slow.

Lemma implies_safe_library_lr {o} :
  forall name (lib lib' : @library o),
    safe_library lib
    -> (safe_library lib -> safe_library lib')
    -> safe_library (remove_cs_lib name lib)
    -> safe_library (remove_cs_lib name lib').
Proof.
  introv safelib imp safe i.
  autodimp imp hyp.
  apply entry_in_remove_cs_lib_implies in i; repndors; exrepnd; tcsp.
  subst.
  apply imp in i1; auto; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve implies_safe_library_lr : slow.

Lemma in_remove_cs_lib_implies {o} :
  forall entry name (lib : @library o),
    List.In entry (remove_cs_lib name lib)
    ->
    (List.In entry lib
     /\ entry2name entry <> entry_name_cs name)
    \/
    exists e,
      List.In (lib_cs name e) lib
      /\ entry = lib_cs name (empty_choice_seq_entry e).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; simpl in *; subst; ginv;
    repndors; repnd; subst; tcsp;
      try (complete (simpl; left; dands; tcsp; introv xx; inversion xx; subst; tcsp));
      try (complete (autodimp IHlib hyp; repndors; exrepnd; subst; tcsp;
                     right; exists e; dands; auto));
      try (complete (right; exists entry0; dands; auto)).
Qed.

Lemma implies_in_remove_cs_lib_if_diff {o} :
  forall entry name (lib : @library o),
    List.In entry lib
    -> entry2name entry <> entry_name_cs name
    -> List.In entry (remove_cs_lib name lib).
Proof.
  induction lib; introv i d; simpl in *; tcsp.
  repndors; subst; simpl in *.
  { destruct entry; simpl in *; tcsp; boolvar; subst; tcsp. }
  { destruct a; simpl in *; tcsp; boolvar; subst; tcsp. }
Qed.
Hint Resolve implies_in_remove_cs_lib_if_diff : slow.

Lemma implies_in_remove_cs_lib_if_same {o} :
  forall entry name (lib : @library o),
    List.In (lib_cs name entry) lib
    -> List.In (lib_cs name (empty_choice_seq_entry entry)) (remove_cs_lib name lib).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; subst; simpl in *; tcsp; boolvar; simpl in *; tcsp.
  apply IHlib in i; clear IHlib.
  destruct a; simpl in *; boolvar; tcsp.
Qed.
Hint Resolve implies_in_remove_cs_lib_if_same : slow.

Lemma cse_restriction_empty_choice_seq_entry {o} :
  forall (e : @ChoiceSeqEntry o),
    cse_restriction (empty_choice_seq_entry e)
    = cse_restriction e.
Proof.
  introv; destruct e; simpl; tcsp.
Qed.
Hint Rewrite @cse_restriction_empty_choice_seq_entry : slow.

Lemma implies_empty_choice_sequence_entry_extend {o} :
  forall (e1 e2 : @ChoiceSeqEntry o),
    choice_sequence_entry_extend e1 e2
    -> choice_sequence_entry_extend (empty_choice_seq_entry e1) (empty_choice_seq_entry e2).
Proof.
  introv i.
  unfold choice_sequence_entry_extend in *; repnd; autorewrite with slow.
  dands; auto.
  destruct e1, e2; simpl; eauto 3 with slow.
Qed.
Hint Resolve implies_empty_choice_sequence_entry_extend : slow.

Lemma subset_remove_cs_lib_lr {o} :
  forall name (lib lib' : @library o),
    subset_library lib lib'
    -> subset_library (remove_cs_lib name lib) (remove_cs_lib name lib').
Proof.
  introv ss i.
  apply in_remove_cs_lib_implies in i.
  repndors; exrepnd; subst; simpl in *; tcsp.
  { apply ss in i0; exrepnd.
    exists entry2; dands; eauto 3 with slow.
    apply implies_in_remove_cs_lib_if_diff; eauto 3 with slow.
    apply entry_extends_implies_same_entry2name in i1; try congruence. }
  { apply ss in i1; exrepnd.
    destruct entry2; simpl in *; repnd; subst; tcsp; ginv;[].
    exists (lib_cs name (empty_choice_seq_entry entry)); simpl; dands; eauto 3 with slow. }
Qed.
Hint Resolve subset_remove_cs_lib_lr : slow.

Lemma implies_remove_cs_lib_lr {o} :
  forall name (lib lib' : @library o),
    safe_library lib
    -> lib_extends lib' lib
    -> lib_extends (remove_cs_lib name lib') (remove_cs_lib name lib).
Proof.
  introv safelib xt.
  destruct xt as [ext safe sub].
  split; eauto 3 with slow.
Qed.
Hint Resolve implies_remove_cs_lib_lr : slow.

(* Inspired from name_invariance stuff *)
Lemma implies_close_remove_cs {o} :
  forall name1 name2 lib (u : cts(o)) (t1 t2 : @CTerm o) e,
    name1 <> name2
    -> up_to_namec name1 t1
    -> up_to_namec name1 t2
    -> (forall lib t1 t2 e,
           u lib t1 t2 e
           -> {e : per(o) , u (remove_cs_lib name2 lib) t1 t2 e})
    -> close u lib t1 t2 e
    -> {e : per(o) , close u (remove_cs_lib name2 lib) t1 t2 e}.
Proof.
  introv dn upto1 upto2 imp cl.
  close_cases (induction cl using @close_ind') Case; introv; subst.

  { Case "CL_init".
    pose proof (imp lib T T' eq) as imp; autodimp imp hyp; exrepnd.
    exists e.
    apply CL_init; auto.
  }

  { Case "CL_bar".
    clear per.

    assert (all_in_bar_ext
              bar
              (fun (lib' : library) (_ : lib_extends lib' lib) =>
                 exists e, close ts (remove_cs_lib name2 lib') T T' e)) as w.
    { introv br ext x.
      pose proof (reca _ br _ ext x) as reca; simpl in *.
      repeat (autodimp reca hyp). }
    clear reca imp.

    apply all_in_bar_ext_exists_per_implies in w; exrepnd.

    exists (bar_per2per f).
    apply CL_bar.
    unfold per_bar.

(*          Lemma inf_entry2name_inf_library_fill_removed {o} :
            forall name (lib : @library o) infLib n,
              inf_entry2name (inf_library_fill_removed name lib infLib n)
              = inf_entry2name (infLib n).
          Proof.
            introv.
            unfold inf_library_fill_removed.
            destruct (infLib n); simpl; boolvar; auto.
            destruct (find_cs lib name0); simpl; auto.
          Qed.
          Hint Rewrite @inf_entry2name_inf_library_fill_removed : slow.

          Lemma shift_inf_lib_inf_library_fill_removed {o} :
            forall name (lib : @library o) infLib,
              shift_inf_lib (inf_library_fill_removed name lib infLib)
              = inf_library_fill_removed name lib (shift_inf_lib infLib).
          Proof.
            introv; unfold shift_inf_lib; simpl.
            apply functional_extensionality; introv; simpl; auto.
          Qed.

      Lemma entry_in_inf_library_extends_in_fill_removed {o} :
        forall name entry n lib (infLib : @inf_library o),
          entry_in_library (lib_cs name entry) lib
          -> entry_in_inf_library_extends (lib_cs name (empty_choice_seq_entry entry)) n infLib
          -> entry_in_inf_library_extends (lib_cs name entry) n (inf_library_fill_removed name lib infLib).
      Proof.
        induction n; introv i h; simpl in *; tcsp.
        repndors; subst; tcsp.

        { left.
          unfold inf_library_fill_removed; simpl.
          unfold inf_entry_extends in *.
          remember (infLib 0) as il; destruct il; tcsp.
          repnd; subst; boolvar; tcsp; GC.
          applydup @entry_in_library_implies_find_cs_some in i; allrw; dands; tcsp; eauto 3 with slow. }

        { repnd.
          right.
          dands.

          { intro xx; destruct h0.
            unfold inf_matching_entries in *; simpl in *.
            autorewrite with slow in *; auto. }

          { rewrite shift_inf_lib_inf_library_fill_removed.
            apply IHn; auto. } }
      Qed.
      Hint Resolve entry_in_inf_library_extends_in_fill_removed : slow.*)

Definition bar_of_remove_cs_lib {o} {lib} (safelib : safe_library lib) (bar : @BarLib o lib) name : BarLib (remove_cs_lib name lib).
Proof.
  exists (fun lib' => exists lib, bar_lib_bar bar lib /\ lib' = remove_cs_lib name lib).

  - introv ext.
    destruct bar as [bar1 bars1 ext1]; simpl in *.
    pose proof (bars1 (inf_library_fill_removed name lib infLib)) as q.
    autodimp q hyp; eauto 3 with slow;[].
    exrepnd.
    exists (remove_cs_lib name lib'); dands; auto; eauto 3 with slow.

Lemma inf_lib_extends_remove_cs_lib {o} :
  forall name lib (infLib : @inf_library o),
    inf_lib_extends (inf_library_fill_removed name lib infLib) lib
    -> inf_lib_extends infLib (remove_cs_lib name lib).
Proof.
  introv ext.
  destruct ext as [ext safe].
  split; simpl in *.

  { introv i.
    apply entry_in_remove_cs_lib_implies in i.
    repndors; exrepnd; subst; simpl in *.

    { apply ext in i0; clear ext.
      repndors; exrepnd; tcsp.

      { unfold inf_library_fill_removed in i1.
        remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs.

        { destruct n; simpl in *; tcsp.
          repndors; repnd; tcsp.

          { destruct entry; simpl in *; repnd; subst; tcsp. }

          { unfold shift_inf_lib in *; simpl in *.
            left; exists n; tcsp. } }

        { left; exists n; tcsp. } }

      { unfold inf_library_fill_removed in i0.
        remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; tcsp.

        unfold entry_in_inf_library_default in *; simpl in *; repnd.
        right; dands; auto.
        introv xx.
        pose proof (i1 (S n)) as i1; simpl in *; tcsp. } }

    { applydup ext in i1; clear ext.
      repndors; exrepnd; tcsp.

      { destruct (classic (exists n, same_entry_name (inf_entry2name (infLib n)) (entry_name_cs name))) as [d|d].

        { exrepnd.
          Print entry_in_inf_library_default.

  Print entry_in_inf_library.

        Print entry_in_inf_library_default.

Qed.
Hint Resolve inf_lib_extends_remove_cs_lib : slow.

    SearchAbout inf_lib_extends remove_cs_lib.

XXXXXXXXXXx
SearchAbout inf_library.

    Print inf_library.

          pose proof (bars
    exists (remove_cs_lib name lib); dands; auto; eauto 3 with slow.



    pose proof (bars1 infLib) as q; autodimp q hyp; exrepnd.
    remember (h lib' q1 lib' (lib_extends_refl lib') q2) as b; symmetry in Heqb.

    destruct b as [bar2 bars2 ext2]; simpl in *.
    pose proof (bars2 infLib) as w; autodimp w hyp; exrepnd.

    exists lib'0; dands; eauto 3 with slow.
    exists lib' q1 lib' (lib_extends_refl lib') q2.
    rewrite Heqb; simpl; auto.

  - introv w; exrepnd.
    remember (h lib1 br lib2 ext x) as b; symmetry in Heqb.
    destruct bar as [bar1 bars1 ext1]; simpl in *.
    destruct b as [bar2 bars2 ext2]; simpl in *.
    eauto 3 with slow.
Defined.

    exists bar.

Qed.


(* Inspired from name_invariance stuff *)
Lemma implies_close_ren_cs {o} :
  forall name1 name2 lib lib' (u : cts(o)) (t1 t2 : @CTerm o) e,
    name1 <> name2
    -> up_to_namec name1 t1
    -> up_to_namec name1 t2
    -> (forall lib' lib t1 t2 e,
           lib_extends_cs_ren name1 name2 lib' lib
           -> u lib t1 t2 e
           -> u lib'
                (ren_cs_cterm (name1,name2) t1)
                (ren_cs_cterm (name1,name2) t2)
                (ren_cs_per (name1,name2) e))
    -> lib_extends_cs_ren name1 name2 lib' lib
    -> close u lib t1 t2 e
    -> close
         u
         lib'
         (ren_cs_cterm (name1,name2) t1)
         (ren_cs_cterm (name1,name2) t2)
         (ren_cs_per (name1,name2) e).
Proof.
  introv dn upto1 upto2 imp ext cl.
  revert dependent lib'.
  close_cases (induction cl using @close_ind') Case; introv ext; subst.

  { Case "CL_init".
    apply CL_init.
    eapply imp; eauto.
  }

  { Case "CL_bar".
    clear per.
    apply CL_bar.
    unfold per_bar.
    exists (raise_bar bar ext) (ren_cs_lib_per (name1,name2) ext eqa).
    dands.

    - introv br xt; introv; simpl in *; exrepnd.
      pose proof (reca _ br1 _ (lib_extends_trans xt br2) (lib_extends_trans x ext)) as reca; simpl in *.
      repeat (autodimp reca hyp); eauto 3 with slow.
      pose proof (reca lib'1) as reca; repeat (autodimp reca hyp); eauto 3 with slow.

      {
      }
    SearchAbout BarLib lib_extends.
  }

Qed.

Lemma implies_equality_ren_cs {o} :
  forall name1 name2 lib lib' (t1 t2 T : @CTerm o),
    name1 <> name2
    -> lib_extends lib' lib
    -> up_to_namec name1 T
    -> (forall m : nat,
           m < cs_size lib name1
           ->
           {k : nat
            & find_cs_value_at lib' name1 m = Some (mkc_nat k)
            # find_cs_value_at lib' name2 m = Some (mkc_nat k)})
    -> equality lib t1 t2 T
    -> equality
         lib'
         (ren_cs_cterm (name1,name2) t1)
         (ren_cs_cterm (name1,name2) t2)
         (ren_cs_cterm (name1,name2) T).
Proof.
  introv equ.
  unfold equality, nuprl in *; exrepnd.
(*  exists (rename_per r eq).
  unfold rename_per; autorewrite with slow in *.
  dands; auto;[].
  fold (rename_per r eq).
  apply implies_close_univ_rename; auto.*)
Abort.


Qed.
