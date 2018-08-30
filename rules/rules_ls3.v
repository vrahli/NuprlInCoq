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

  eapply inhabited_type_cequivc;
    [apply ccequivc_ext_sym;
     apply implies_ccequivc_ext_product;
     [apply ccequivc_ext_refl
     |apply implies_bcequivc_ext_substc2_1;
      apply computes_to_valc_implies_ccequivc_ext;eauto]
    |].

  clear a1 eqa2.

  applydup (@equality_in_mkc_csprop_implies_tequality_cs o name) in eqA as teq; auto;[].
  eapply tequality_preserves_member in eqz;[|eauto].

  apply inhabited_product.
  dands; eauto 3 with slow;[|].

  { admit. }

  exists (@mkc_pair
            _
            (mkc_nat (cs_size lib name))
            (mkc_lam b (mkcv_lam _ x (mk_cv _ z1)))).

  apply in_ext_implies_all_in_ex_bar.
  introv ext.
  exists (@mkc_nat o (cs_size lib name)) (mkc_lam b (mkcv_lam _ x (mk_cv _ z1))).
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
                         (mkcv_natk2nat [b] (mk_cv [b] (mkc_nat (cs_size lib1 name)))))
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
             m < cs_size lib1 name
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

  (* === We might have to squash the application in the conclusion === *)

  (* === We have to show that because of [imp], [lib1] can be extended with [name']
         equivalent to [name] up to [cs_size lib1 name] === *)

  destruct (choice_sequence_name_deq name' name) as [d|d];[subst;eauto 3 with slow|];[].


  Definition up_to_name {o} (name : choice_sequence_name) (t : @NTerm o) :=
    subset (get_defs t) [defk_cs name].

  Lemma compute_step_preserves_ren_cs {o} :
    forall lib lib' (t u : @NTerm o) name1 name2,
      name1 <> name2
      -> lib_extends lib' lib
      -> up_to_name name1 t
      -> (forall m : nat,
             m < cs_size lib name1
             ->
             {k : nat
              & computes_to_valc lib' (mkc_apply (mkc_choice_seq name1) (mkc_nat m)) (mkc_nat k)
              # computes_to_valc lib' (mkc_apply (mkc_choice_seq name2) (mkc_nat m)) (mkc_nat k)})
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

            SearchAbout lsubst ren_cs_term.
            (* PROVE THAT! *)
          }

        }

        { SSCase "NCan".
        }

        { SSCase "Exc".
        }

        { SSCase "Abs".
        }

      }

      { (* fresh case *)
      }

    }

    { SCase "Exc".
    }

    { SCase "Abs".
    }


  Qed.

  Lemma xxx {o} :
    forall lib lib' (t v : @NTerm o) name1 name2,
      lib_extends lib' lib
      -> (forall m : nat,
             m < cs_size lib name1
             ->
             {k : nat
              & computes_to_valc lib' (mkc_apply (mkc_choice_seq name1) (mkc_nat m)) (mkc_nat k)
              # computes_to_valc lib' (mkc_apply (mkc_choice_seq name2) (mkc_nat m)) (mkc_nat k)})
      -> computes_to_value lib t v
      -> computes_to_value
           (lib' (* extend [lib] with [name2] *))
           (ren_cs_term (name1,name2) t)
           (ren_cs_term (name1,name2) v).
  Proof.

  Qed.

Qed.
