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


Require Export per_props_ffdefs.
Require Export per_props_nat.
Require Export per_props_nat2.
Require Export rules_choice_util3.

(* This is to allow make equivalent restrictions equal.
   This could be removed by allowing in extensions to replace
   an restriction by an equivalent one *)
Require Import Coq.Logic.PropExtensionality.

Require Export Permutation.



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
  introv ext; spcast; eauto 3 with slow.
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

Definition entry_depth {o} (entry : @library_entry o) : nat :=
  match entry with
  | lib_cs name e => length (cse_vals e) (*Peano.max (length (cse_vals e)) (cs_name_restr_size name)*)
  | _ => 0
  end.

Fixpoint lib_depth {o} (lib : @plibrary o) : nat :=
  match lib with
  | [] => 0
  | entry :: entries => Peano.max (entry_depth entry) (lib_depth entries)
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
  apply equality_in_csname_iff; eauto 3 with slow.
  unfold equality_of_csname_bar.
  apply in_ext_implies_in_open_bar; introv xta.
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

Lemma is_nat_implies_isvalue {o} :
  forall n (t : @CTerm o),
    is_nat n t
    -> isvalue (CSVal2term t).
Proof.
  introv isn; unfold is_nat in *.
  repeat constructor; exrepnd; subst; simpl; eauto 3 with slow.
Qed.
Hint Resolve is_nat_implies_isvalue : slow.

Lemma CSVal2term_eq_mk_nat_implies {o} :
  forall (t : @CTerm o) k,
    CSVal2term t = mk_nat k
    -> t = mkc_nat k.
Proof.
  introv h; apply cterm_eq; simpl; auto.
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
    { apply safe in Heqxx.
      apply safe0 in Heqxx.
      unfold is_nat in Heqxx; exrepnd; subst; simpl in *.
      apply reduces_to_if_value in comp0; eauto 3 with slow.
      apply mk_nat_eq_implies in comp0; subst; auto. }
(*    { rewrite safe in Heqxx; eauto 3 with slow; inversion Heqxx; subst.
      pose proof (safe0 m) as safe0.
      apply reduces_to_if_value in comp0; eauto 3 with slow.
      apply CSVal2term_eq_mk_nat_implies in comp0; try congruence. }
    { apply safe in Heqxx.
      apply safe0 in Heqxx.
      unfold is_nat in Heqxx; exrepnd; subst; simpl in *.
      apply reduces_to_if_value in comp0; eauto 3 with slow.
      apply mk_nat_eq_implies in comp0; subst; auto. }*)
  }

  {
    unfold is_nat_seq_restriction in *.
    destruct restr; simpl in *; tcsp; repnd.
    apply safe in Heqxx.

    destruct (lt_dec m (length l0)) as [w|w].

    {
      apply safe1 in Heqxx; auto.
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

Lemma cs_size_le_lib_depth {o} :
  forall name (lib : @library o),
    cs_size lib name <= lib_depth lib.
Proof.
  introv.
  unfold cs_size.
  destruct lib as [lib cond]; simpl.
  induction lib; simpl; auto.
  destruct a; simpl; boolvar; subst; eauto 3 with slow num.
Qed.
Hint Resolve cs_size_le_lib_depth : slow.

Lemma find_cs_value_at_implies_lt_lib_depth {o} :
  forall (lib : @library o) name n v,
    find_cs_value_at lib name n = Some v
    -> n < lib_depth lib.
Proof.
  introv h.
  apply find_cs_value_at_implies_lt_cs_size in h.
  pose proof (cs_size_le_lib_depth name lib) as q; omega.
Qed.
Hint Resolve find_cs_value_at_implies_lt_lib_depth : slow.

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

        { SSSCase "NLastCs".
          admit. }

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

  { destruct restr; simpl in *; repnd; tcsp.

    { apply sat in i0.
      apply cor in i0.
      unfold is_nat in i0; exrepnd; subst; simpl; eauto. }

(*    { rewrite sat in i0; eauto 3 with slow; inversion i0; subst; apply cor. }

    { apply sat in i0.
      apply cor in i0.
      unfold is_nat in i0; exrepnd; subst; simpl; eauto. }*)
  }

  { destruct restr; simpl in *; repnd; tcsp;[].
    applydup sat in i0.
    destruct (lt_dec n (length l)) as [w|w].

    { apply cor0 in i1; auto.
      unfold cterm_is_nth in i1; exrepnd; subst; eauto. }

    { pose proof (cor n x) as z; autodimp z hyp; try omega;[].
      apply z in i1.
      unfold is_nat in *; exrepnd; subst; eauto. } }
Qed.

(*Lemma is_nat_restriction_implies_is_nat_seq_restriction {o} :
  forall (restr : @ChoiceSeqRestriction o),
    is_nat_restriction restr
    -> is_nat_seq_restriction [] restr.
Proof.
  introv isn.
  destruct restr; simpl in *; tcsp.
Qed.
Hint Resolve is_nat_restriction_implies_is_nat_seq_restriction : slow.*)

(*Lemma implies_same_restrictions_nat {o} :
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
Qed.*)

Fixpoint keep_only_pre {o} (name : choice_sequence_name) (lib : @plibrary o) : @plibrary o :=
  match lib with
  | [] => []
  | lib_cs name' e :: entries =>
    if choice_sequence_name_deq name name'
    then [lib_cs name' e]
    else keep_only_pre name entries
  | entry :: entries => keep_only_pre name entries
  end.

Definition keep_only {o} (name : choice_sequence_name) (lib : @library o) : library :=
  MkLib (keep_only_pre name lib) (lib_cond lib).

Lemma keep_only_equal {o} :
  forall name (lib : @plibrary o),
    keep_only_pre name lib
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
  | csc_type M => csc_type (swap_cs_restriction_pred r M)
(*  | csc_coq_law f => csc_coq_law (fun n => swap_cs_cterm r (f n))
  | csc_res P => csc_res (swap_cs_restriction_pred r P)*)
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
    lib_cs (swap_cs r name) (swap_cs_choice_seq_entry r e)
  | lib_abs abs vars rhs correct =>
    lib_abs abs vars (swap_cs_soterm r rhs) (swap_cs_correct_abs r abs vars rhs correct)
  end.

Fixpoint swap_cs_plib {o} (r : cs_swap) (lib : @plibrary o) :=
  match lib with
  | [] => []
  | entry :: entries => swap_cs_lib_entry r entry :: swap_cs_plib r entries
  end.

Definition swap_cs_lib_cond {o} (sw : cs_swap) (c : @LibCond o) : LibCond :=
  fun x =>
    match x with
    | lck_term v => c (swap_cs_term sw v)
    | lck_restr r => c (swap_cs_choice_seq_restr sw r)
    end.

Definition swap_cs_lib {o} (r : cs_swap) (lib : @library o) :=
  MkLib (swap_cs_plib r lib) (swap_cs_lib_cond r (lib_cond lib)).

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
  forall sw entry (lib : @plibrary o),
    entry_in_library entry lib
    -> entry_in_library (swap_cs_lib_entry sw entry) (swap_cs_plib sw lib).
Proof.
  induction lib; introv h; simpl in *; tcsp;[].
  repndors; repnd; subst; simpl in *; auto;[].
  right.
  dands; auto.
  rewrite matching_entries_swap_iff; auto.
Qed.

Fixpoint cs_name_in_library {o} (name : choice_sequence_name) (lib : @plibrary o) : bool :=
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

    { unfold swap_cs_restriction_pred.
      repeat rewrite isn0; auto; autorewrite with slow; tcsp. }

    { unfold swap_cs_restriction_pred.
      repeat rewrite isn; try omega; auto; autorewrite with slow; tcsp. } }
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

Lemma swap_cs_choice_seq_restr_idem {o} :
  forall sw (restr : @ChoiceSeqRestriction o),
    swap_cs_choice_seq_restr sw (swap_cs_choice_seq_restr sw restr)
    = restr.
Proof.
  destruct restr; simpl; autorewrite with slow; dands; f_equal.

  { apply functional_extensionality; introv; unfold swap_cs_restriction_pred; simpl.
    apply functional_extensionality; introv; autorewrite with slow; auto. }

(*  { apply functional_extensionality; introv; autorewrite with slow; auto. }

  { apply functional_extensionality; introv; unfold swap_cs_restriction_pred; simpl.
    apply functional_extensionality; introv; autorewrite with slow; auto. }*)
Qed.
Hint Rewrite @swap_cs_choice_seq_restr_idem : slow.

Definition same_choice_seq_entries {o} (e1 e2 : @ChoiceSeqEntry o) :=
  cse_vals e1 = cse_vals e2
  /\ same_restrictions (cse_restriction e1) (cse_restriction e2).

Definition same_library_entries {o} (e1 e2 : @library_entry o) :=
  match e1, e2 with
  | lib_cs name1 e1, lib_cs name2 e2 => name1 = name2 /\ same_choice_seq_entries e1 e2
  | _, _ => e1 = e2
  end.

Fixpoint same_libraries {o} (lib1 lib2 : @plibrary o) :=
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
    swap_cs_choice_seq_entry
      sw
      (swap_cs_choice_seq_entry sw entry)
    = entry.
Proof.
  introv.
  unfold swap_cs_choice_seq_entry.
  destruct entry as [vals restr]; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_choice_seq_entry_idem : slow.

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
  { unfold natSeq2restrictionPred.
    remember (select n l) as sel; symmetry in Heqsel; destruct sel.
    - pose proof (isn0 n v) as isn2; autodimp isn2 hyp; eauto 3 with slow.
      rewrite isn2; unfold cterm_is_nth; allrw.
      split; intro h; exrepnd; ginv; subst; eauto.
    - applydup @nth_select2 in Heqsel.
      pose proof (isn n v) as isn; autodimp isn hyp; try omega.
      rewrite isn; tcsp. }
Qed.
Hint Resolve is_nat_seq_restriction_implies_same : slow.

Lemma is_nat_restriction_csc_nat {o} : @is_nat_restriction o csc_nat.
Proof.
  introv; tcsp.
Qed.
Hint Resolve is_nat_restriction_csc_nat : slow.

(*Lemma is_nat_restriction_implies_same {o} :
  forall (restr : @ChoiceSeqRestriction o),
    is_nat_restriction restr
    -> same_restrictions csc_nat restr.
Proof.
  introv h.
  unfold same_restrictions; simpl.
  destruct restr; simpl in *; tcsp.
Qed.
Hint Resolve is_nat_restriction_implies_same : slow.*)

(*Lemma same_restrictions_if_correct {o} :
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

SearchAbout is_nat_restriction csc_nat.
Qed.
Hint Resolve same_restrictions_if_correct : slow.*)

Definition compatible_cs_kinds (k1 k2 : cs_kind) :=
  match k1, k2 with
  | cs_kind_nat n, cs_kind_nat m => n = m
  | cs_kind_nat n, cs_kind_seq l => n = 0
  | cs_kind_seq l, cs_kind_nat n => n = 0
  | cs_kind_seq l, cs_kind_seq k => True
  end.

Definition compatible_choice_sequences (name1 name2 : choice_sequence_name) :=
  csn_kind name1 = csn_kind name2.
(*  compatible_cs_kinds (csn_kind name1) (csn_kind name2).*)

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
  destruct k1, k2; simpl in *; subst; boolvar; subst; simpl in *; ginv; tcsp.
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

(*Lemma swap_cs_choice_seq_entry_normalize_idem {o} :
  forall sw name (entry : @ChoiceSeqEntry o),
    sane_swapping sw
    -> safe_choice_sequence_entry name entry
    -> swap_cs_choice_seq_entry_normalize
         (swap_cs sw name)
         name sw
         (swap_cs_choice_seq_entry_normalize name (swap_cs sw name) sw entry)
       = entry.
Proof.
  introv sane safe.
  unfold swap_cs_choice_seq_entry_normalize.
  destruct sw as [n1 n2]; simpl.
  boolvar; subst; simpl in *; GC; eauto 3 with slow; tcsp; autorewrite with slow; tcsp.

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
Hint Resolve swap_cs_choice_seq_entry_normalize_idem : slow.*)

Lemma swap_cs_lib_entry_idem {o} :
  forall sw (e : @library_entry o),
    swap_cs_lib_entry sw (swap_cs_lib_entry sw e) = e.
Proof.
  introv; destruct e; simpl in *; autorewrite with slow; dands; auto; eauto 3 with slow.

  remember (swap_cs_correct_abs
              sw opabs vars (swap_cs_soterm sw rhs)
              (swap_cs_correct_abs sw opabs vars rhs correct)) as w.
  clear Heqw.
  revert w.
  autorewrite with slow; introv.
  f_equal; eauto with pi.
Qed.
Hint Rewrite @swap_cs_lib_entry_idem : slow.

Definition strong_safe_library {o} (lib : @plibrary o) :=
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
  forall e (lib : @plibrary o),
    strong_safe_library (e :: lib) <-> (safe_library_entry e /\ strong_safe_library lib).
Proof.
  introv; split; intro safe; dands.
  { pose proof (safe e) as safe; simpl in *; tcsp. }
  { introv i; pose proof (safe e0) as safe; simpl in *; tcsp. }
  { repnd; introv i; simpl in *; repndors; subst; simpl in *; tcsp. }
Qed.

Lemma swap_cs_plib_idem {o} :
  forall sw (lib : @plibrary o),
    swap_cs_plib sw (swap_cs_plib sw lib) = lib.
Proof.
  induction lib; introv; simpl; dands; auto.
  autorewrite with slow; tcsp; try congruence.
Qed.
Hint Rewrite @swap_cs_plib_idem : slow.

Lemma swap_cs_lib_cond_twice {o} sw (c : @LibCond o) :
  swap_cs_lib_cond sw (swap_cs_lib_cond sw c) = c.
Proof.
  introv; apply functional_extensionality; introv; simpl.
  unfold swap_cs_lib_cond; simpl; destruct x; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_lib_cond_twice : slow.

Lemma swap_cs_lib_idem {o} :
  forall sw (lib : @library o),
    swap_cs_lib sw (swap_cs_lib sw lib) = lib.
Proof.
  introv; destruct lib as [lib cond]; simpl.
  unfold swap_cs_lib; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_lib_idem : slow.

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
  forall (lib1 lib2 : @plibrary o),
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
  forall (lib1 lib2 : @plibrary o) e,
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

(*Lemma same_choice_seq_entries_preserves_choice_sequence_entry_extend {o} :
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
Hint Resolve same_choice_seq_entries_preserves_choice_sequence_entry_extend : slow.*)

(*Lemma same_library_entries_preserves_entry_in_library_extends {o} :
  forall e1 e2 (lib : @library o),
    same_library_entries e1 e2
    -> entry_in_library_extends e2 lib
    -> entry_in_library_extends e1 lib.
Proof.
  destruct e1, e2; introv same i; simpl in *; repnd; subst; eauto 3 with slow; ginv;[].
  induction lib; simpl in *; tcsp;[].
  repndors; tcsp;[].
  left.
  inversion i; subst; clear i; tcsp; eauto.
  unfold entry_extends in *.
  destruct a; simpl in *; tcsp; ginv.
  repnd; subst; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_preserves_entry_in_library_extends : slow.*)

(*Lemma same_libraries_implies_lib_extends_entries {o} :
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
Hint Resolve same_libraries_implies_lib_extends_entries : slow.*)

Lemma same_restrictions_preserves_choice_sequence_satisfies_restriction {o} :
  forall vals (restr1 restr2 : @ChoiceSeqRestriction o),
    same_restrictions restr1 restr2
    -> choice_sequence_satisfies_restriction vals restr1
    -> choice_sequence_satisfies_restriction vals restr2.
Proof.
  introv same sat.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr1, restr2; simpl in *; repnd; tcsp;
    try (complete (introv sel; apply sat in sel; apply same; auto)).
(*  { introv w.
    apply sat in w; rewrite <- same; auto. }*)
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
  forall (lib1 lib2 : @plibrary o) e,
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

(*Lemma same_library_entries_implies_entry_extends {o} :
  forall (e1 e2 : @library_entry o),
    same_library_entries e1 e2
    -> entry_extends e1 e2.
Proof.
  introv same.
  destruct e1, e2; simpl in *; repnd; dands; subst; tcsp; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_implies_entry_extends : slow.*)

(*Lemma same_libraries_preserves_subset_library {o} :
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
Hint Resolve same_libraries_preserves_subset_library : slow.*)

(*Lemma same_libraries_implies_lib_extends {o} :
  forall (lib1 lib2 : @library o),
    same_libraries lib1 lib2
    -> lib_extends lib1 lib2.
Proof.
  introv same.
  split; eauto 3 with slow.
Qed.
Hint Resolve same_libraries_implies_lib_extends : slow.*)

Definition swap_cs_inf_choice_seq_vals {o} (r : cs_swap) (vals : @InfChoiceSeqVals o) : InfChoiceSeqVals :=
  fun n => option_map (swap_cs_cterm r) (vals n).

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
    | Some v => Some (mkc_nat v)
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

(*Lemma swap_same_restrictions {o} :
  forall sw (restr1 restr2 : @ChoiceSeqRestriction o),
    same_restrictions restr1 restr2
    -> same_restrictions
         (swap_cs_choice_seq_restr sw restr1)
         (swap_cs_choice_seq_restr sw restr2).
Proof.
  introv same; destruct restr1, restr2; simpl in *; repnd; dands; tcsp; introv; try congruence.

  { unfold swap_cs_default; try congruence. }

  { unfold swap_cs_restriction_pred; tcsp. }

  { unfold swap_cs_restriction_pred; tcsp. }
Qed.
Hint Resolve swap_same_restrictions : slow.*)

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
  unfold swap_cs_inf_choice_seq_vals; allrw; simpl; auto.
Qed.
Hint Resolve swap_inf_choice_sequence_vals_extend : slow.

(*Lemma swap_inf_choice_sequence_entry_extend {o} :
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
Hint Resolve swap_inf_choice_sequence_entry_extend : slow.*)

(*Lemma normalize_swap_inf_choice_sequence_entry_extend {o} :
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
Hint Resolve normalize_swap_inf_choice_sequence_entry_extend : slow.*)

(*Lemma swap_inf_choice_sequence_entry_extend_normalize {o} :
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
Hint Resolve swap_inf_choice_sequence_entry_extend_normalize : slow.*)

(*Lemma swap_inf_entry_extends {o} :
  forall sw e1 (e2 : @library_entry o),
    inf_entry_extends e1 e2
    -> inf_entry_extends (swap_cs_inf_lib_entry sw e1) (swap_cs_lib_entry sw e2).
Proof.
  introv i.
  unfold inf_entry_extends; simpl in *.
  destruct e1, e2; simpl in *; repnd; subst; tcsp.
  dands; auto; eauto 2 with slow.
Qed.
Hint Resolve swap_inf_entry_extends : slow.*)

(*Lemma inf_matching_entries_swap_iff {o} :
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
Hint Rewrite @inf_matching_entries_swap_iff : slow.*)

(*Lemma swap_entry_in_inf_library_extends {o} :
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
Hint Resolve swap_entry_in_inf_library_extends : slow.*)

(*Lemma swap_same_choice_seq_entries {o} :
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
Hint Resolve swap_same_choice_seq_entries : slow.*)

(*Lemma swap_normalize_same_choice_seq_entries {o} :
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
Hint Resolve swap_normalize_same_choice_seq_entries : slow.*)

(*Lemma swap_same_choice_seq_entries_normalize {o} :
  forall name name' sw e1 (e2 : @ChoiceSeqEntry o),
    same_choice_seq_entries e1 e2
    -> same_choice_seq_entries
         (swap_cs_choice_seq_entry_normalize name name' sw e1)
         (swap_cs_choice_seq_entry_normalize name name' sw e2).
Proof.
  introv same.
  unfold swap_cs_choice_seq_entry_normalize; boolvar; eauto 3 with slow.
Qed.
Hint Resolve swap_same_choice_seq_entries_normalize : slow.*)

(*Lemma swap_same_entry_libraries {o} :
  forall sw (e1 e2 : @library_entry o),
    same_library_entries e1 e2
    -> same_library_entries (swap_cs_lib_entry sw e1) (swap_cs_lib_entry sw e2).
Proof.
  introv same.
  destruct e1, e2; simpl in *; repnd; subst; dands; tcsp; ginv; eauto 3 with slow;[].
  inversion same; subst; auto.
  f_equal; eauto with pi.
Qed.
Hint Resolve swap_same_entry_libraries : slow.*)

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

(*Lemma same_library_entries_preserves_inf_entry_extends {o} :
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
Hint Resolve same_library_entries_preserves_inf_entry_extends : slow.*)

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

(*Lemma same_library_entries_preserves_entry_in_inf_library_extends {o} :
  forall e1 e2 n (lib : @inf_library o),
    same_library_entries e1 e2
    -> entry_in_inf_library_extends e2 n lib
    -> entry_in_inf_library_extends e1 n lib.
Proof.
  induction n; introv same i; simpl in *; tcsp;[].
  repndors; repnd; [left|right]; eauto 3 with slow.
  dands; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_preserves_entry_in_inf_library_extends : slow.*)

Lemma implies_is_nat_restriction_swap {o} :
  forall sw (restr : @ChoiceSeqRestriction o),
    is_nat_restriction restr
    -> is_nat_restriction (swap_cs_choice_seq_restr sw restr).
Proof.
  introv isn.
  unfold is_nat_restriction in *.
  destruct restr in *; simpl in *; tcsp; introv;
    unfold swap_cs_restriction_pred; try rewrite isn; autorewrite with slow; tcsp.
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
  destruct restr in *; simpl in *; tcsp; introv;
    unfold swap_cs_restriction_pred; try rewrite isn; autorewrite with slow; tcsp.
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
    unfold swap_cs_restriction_pred.
    rewrite isn0; tcsp; autorewrite with slow; tcsp. }
  { introv len.
    unfold swap_cs_restriction_pred.
    rewrite isn; auto; autorewrite with slow; tcsp. }
Qed.
Hint Resolve implies_is_nat_seq_restriction_swap : slow.

Lemma sane_swapping_implies_csn_kind_swap_cs :
  forall sw name,
    sane_swapping sw
    -> csn_kind (swap_cs sw name) = csn_kind name.
Proof.
  introv sane; destruct name as [name kind]; simpl.
  destruct sw as [a b]; simpl in *; repeat (boolvar; subst; simpl in *; tcsp).
Qed.

Lemma swap_correct_restriction {o} :
  forall sw name (restr : @ChoiceSeqRestriction o),
    sane_swapping sw
    -> correct_restriction name restr
    -> correct_restriction (swap_cs sw name) (swap_cs_choice_seq_restr sw restr).
Proof.
  introv sane cor.
  unfold correct_restriction in *.
  rewrite sane_swapping_implies_csn_kind_swap_cs; auto.
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

(*
  - introv h.
    autorewrite with list in *.
    applydup sat in h.
    rewrite select_map.
    unfold ChoiceSeqVal in *; rewrite h0; simpl; auto.

  - introv h.
    rewrite select_map in h.
    apply option_map_Some in h; exrepnd; subst.
    unfold swap_cs_restriction_pred; autorewrite with slow; tcsp.*)
Qed.
Hint Resolve swap_choice_sequence_satisfies_restriction : slow.

Lemma swap_safe_choice_sequence_entry {o} :
  forall name sw (entry : @ChoiceSeqEntry o),
    sane_swapping sw
    -> safe_choice_sequence_entry name entry
    -> safe_choice_sequence_entry (swap_cs sw name) (swap_cs_choice_seq_entry sw entry).
Proof.
  introv sane safe.
  destruct entry as [vals restr]; simpl in *; repnd.
  dands; eauto 3 with slow.
Qed.
Hint Resolve swap_safe_choice_sequence_entry : slow.

(*Lemma swap_safe_choice_sequence_entry_same_name {o} :
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
Hint Resolve swap_safe_choice_sequence_entry_same_name : slow.*)

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
  { apply sat in sel; apply isn in sel; auto. }
(*  { rewrite sat in sel; eauto 3 with slow; inversion sel; tcsp. }
  { apply sat in sel; apply isn in sel; auto. }*)
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
  destruct restr; tcsp; repnd;
    try (complete (apply sat in sel; apply isn in sel; auto));
    try (complete (rewrite sat in sel; eauto 3 with slow; inversion sel; tcsp)).
Qed.
Hint Resolve satisfies_is_bool_restriction_implies : slow.

(*Lemma natSeq2default_if_is_nat_restriction {o} :
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
  pose proof (isnl0 n (mkc_nat n0)) as q; autodimp q hyp; eauto 3 with slow.
  unfold cterm_is_nth in *; exrepnd.
  rewrite Heqsel in q1; ginv.
Qed.
Hint Resolve natSeq2default_if_is_nat_restriction : slow.*)

(*Lemma natSeq2restrictionPred_if_is_nat_restriction {o} :
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
Hint Resolve natSeq2restrictionPred_if_is_nat_restriction : slow.*)

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

  { apply isnl0 in sel0; eauto 2 with slow.
    unfold cterm_is_nth in sel0; rewrite Heqsell in sel0; exrepnd; ginv. }

  { applydup @nth_select2 in Heqsell.
    apply isnl; auto. }
Qed.
Hint Resolve natSeq2restrictionPred_if_is_nat_restriction_select : slow.

(*Lemma cterm_is_nth_if_is_nat_seq_restriction {o} :
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
Hint Resolve cterm_is_nth_if_is_nat_seq_restriction : slow.*)

(*Lemma natSeq2default_zero_if_is_nat_seq_restriction {o} :
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
Hint Resolve natSeq2default_zero_if_is_nat_seq_restriction : slow.*)

(*Lemma natSeq2restrictionPred_iff_cterm_is_nth_if_is_nat_seq_restriction {o} :
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
Hint Resolve natSeq2restrictionPred_iff_cterm_is_nth_if_is_nat_seq_restriction : slow.*)

(*Lemma natSeq2restrictionPred_iff_is_nat_if_is_nat_seq_restriction {o} :
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
Hint Resolve natSeq2restrictionPred_iff_is_nat_if_is_nat_seq_restriction : slow.*)

(*Lemma swap_safe_choice_sequence_entry_normalize {o} :
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
  destruct sw as [n1 n2], n2 as [n2 k2], n1 as [n1 k1], k1, k2;
    unfold cs_name2restr, compatible_choice_sequences, correct_restriction in *;
    repeat (simpl in *; boolvar; subst; tcsp);
    unfold compatible_choice_sequences in *; simpl in *; subst;
    dands; tcsp; eauto 3 with slow; GC;
      try (complete (introv sel; unfold swap_cs_choice_seq_vals in sel;
                     rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst;
                     eapply satisfies_is_nat_restriction_implies in sel1; eauto;
                     unfold is_nat in sel1; exrepnd; subst; autorewrite with slow; eauto 3 with slow;
                     eapply natSeq2restrictionPred_if_is_nat_restriction; eauto; eauto 3 with slow));
      try (complete (introv sel; unfold swap_cs_choice_seq_vals in sel;
                     rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst;
                     eapply satisfies_is_bool_restriction_implies in sel1; eauto;
                     unfold is_bool in sel1; exrepnd; subst; autorewrite with slow; eauto 3 with slow));
      try (complete (unfold choice_sequence_satisfies_restriction in *; simpl in *; destruct restr; simpl;
                     try (complete (introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst; simpl in *;
                                    applydup safe in sel1;
                                    unfold swap_cs_restriction_pred; simpl; autorewrite with slow; tcsp));
                     introv len; autorewrite with slow in *; applydup safe in len;
                     rewrite select_map; simpl in *; unfold ChoiceSeqVal in *; allrw; simpl; auto));
      try (complete (introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst;
                     eapply natSeq2restrictionPred_if_is_nat_restriction_select in sel1; eauto;
                     unfold natSeq2restrictionPred in *;
                     try (destruct (select n l0); subst; autorewrite with slow; eauto 3 with slow);
                     try (destruct (select n0 l); subst; autorewrite with slow; eauto 3 with slow))).
Qed.
Hint Resolve swap_safe_choice_sequence_entry_normalize : slow.*)

(*Lemma swap_normalize_safe_choice_sequence_entry {o} :
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
Hint Resolve swap_normalize_safe_choice_sequence_entry : slow.*)

(*Definition safe_library_entry_sw {o} (sw : cs_swap) (e : @library_entry o) :=
  match e with
  | lib_cs name cse =>
    safe_choice_sequence_entry (swap_cs sw name) cse
  | _ => True
  end.*)

(*Definition safe_library_sw {o} (sw : cs_swap) (lib : @library o) :=
  forall entry, entry_in_library entry lib -> safe_library_entry_sw sw entry.*)

Lemma swap_safe_library_entry {o} :
  forall sw (entry : @library_entry o),
    sane_swapping sw
    -> safe_library_entry entry
    -> safe_library_entry (swap_cs_lib_entry sw entry).
Proof.
  introv sane safe.
  destruct entry; simpl in *; tcsp; eauto 3 with slow.
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
  rewrite sane_swapping_implies_csn_kind_swap_cs; auto.
Qed.
Hint Resolve swap_is_primitive_kind : slow.

(*Lemma swap_is_default_choice_seq_entry {o} :
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
Hint Resolve swap_is_default_choice_seq_entry : slow.*)

(*Lemma normalize_swap_is_default_choice_seq_entry {o} :
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
Qed.*)

(*Lemma swap_normalize_is_default_choice_seq_entry {o} :
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
Hint Resolve swap_normalize_is_default_choice_seq_entry : slow.*)

(*Lemma swap_is_cs_default_entry {o} :
  forall sw (entry : @library_entry o),
    sane_swapping sw
    -> is_cs_default_entry entry
    -> is_cs_default_entry (swap_cs_lib_entry sw entry).
Proof.
  introv sane def.
  unfold is_cs_default_entry in *.
  destruct entry; simpl in *; tcsp; repnd.
  dands; eauto 3 with slow.
Qed.
Hint Resolve swap_is_cs_default_entry : slow.*)

(*Lemma swap_entry_in_inf_library_default {o} :
  forall sw entry (ilib : @inf_library o),
    sane_swapping sw
    -> entry_in_inf_library_default entry ilib
    -> entry_in_inf_library_default (swap_cs_lib_entry sw entry) (swap_cs_inf_lib sw ilib).
Proof.
  introv sane def; unfold entry_in_inf_library_default in *; repnd.
  dands; eauto 3 with slow;[].
  introv.
  unfold swap_cs_inf_lib; autorewrite with slow; auto.
Qed.
Hint Resolve swap_entry_in_inf_library_default : slow.*)

Lemma entry_in_swap_library_implies {o} :
  forall sw entry (lib : @plibrary o),
    entry_in_library entry (swap_cs_plib sw lib)
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

(*Lemma implies_swap_inf_lib_extends_ext_entries {o} :
  forall sw infLib (lib : @library o),
    sane_swapping sw
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
Hint Resolve implies_swap_inf_lib_extends_ext_entries : slow.*)

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

(*Lemma swap_safe_choice_sequence_entry {o} :
  forall name sw (entry : @ChoiceSeqEntry o),
    safe_choice_sequence_entry name entry
    -> safe_choice_sequence_entry name (swap_cs_choice_seq_entry sw entry).
Proof.
  introv safe.
  unfold safe_choice_sequence_entry in *.
  destruct entry as [vals restr]; simpl in *; repnd.
  dands; eauto 3 with slow.
Qed.
Hint Resolve swap_safe_choice_sequence_entry : slow.*)

(*Lemma swap_safe_choice_sequence_entry_normalize2 {o} :
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
  destruct sw as [n1 n2], n2 as [n2 k2], n1 as [n1 k1], k1, k2;
    unfold cs_name2restr, compatible_choice_sequences, correct_restriction in *;
    repeat (simpl in *; boolvar; subst; tcsp);
    unfold compatible_choice_sequences in *; simpl in *; subst;
    dands; tcsp; eauto 3 with slow; GC;
      try (complete (introv sel; unfold swap_cs_choice_seq_vals in sel;
                     rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst;
                     eapply satisfies_is_nat_restriction_implies in sel1; eauto;
                     unfold is_nat in sel1; exrepnd; subst; autorewrite with slow; eauto 3 with slow;
                     eapply natSeq2restrictionPred_if_is_nat_restriction; eauto; eauto 3 with slow));
      try (complete (introv sel; unfold swap_cs_choice_seq_vals in sel;
                     rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst;
                     eapply satisfies_is_bool_restriction_implies in sel1; eauto;
                     unfold is_bool in sel1; exrepnd; subst; autorewrite with slow; eauto 3 with slow));
      try (complete (unfold choice_sequence_satisfies_restriction in *; simpl in *; destruct restr; simpl;
                     try (complete (introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst; simpl in *;
                                    applydup safe in sel1;
                                    unfold swap_cs_restriction_pred; simpl; autorewrite with slow; tcsp));
                     introv len; autorewrite with slow in *; applydup safe in len;
                     rewrite select_map; simpl in *; unfold ChoiceSeqVal in *; allrw; simpl; auto));
      try (complete (introv sel; rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst;
                     eapply natSeq2restrictionPred_if_is_nat_restriction_select in sel1; eauto;
                     unfold natSeq2restrictionPred in *;
                     try (destruct (select n l0); subst; autorewrite with slow; eauto 3 with slow);
                     try (destruct (select n0 l); subst; autorewrite with slow; eauto 3 with slow))).

    { introv len.
      eapply natSeq2restrictionPred_iff_cterm_is_nth_if_is_nat_seq_restriction; eauto.
      unfold natSeq2restrictionPred.
      pose proof (natSeq2default_if_is_nat_restriction l n restr) as q; repeat (autodimp q hyp).
      unfold natSeq2default in *.
      destruct (select n l); eauto 3 with slow. }

    { introv len; split; intro h; eauto 3 with slow.
      eapply natSeq2restrictionPred_if_is_nat_restriction in h; eauto.
      apply natSeq2restrictionPred_iff_cterm_is_nth; auto. }

    { introv len.
      apply natSeq2restrictionPred_iff_cterm_is_nth; auto.
      eapply natSeq2restrictionPred_if_is_nat_restriction; eauto; eauto 3 with slow. }

    { introv len; split; intro h; eauto 3 with slow.
      eapply natSeq2restrictionPred_if_is_nat_restriction in h; eauto.
      apply natSeq2restrictionPred_iff_cterm_is_nth; auto. }
Qed.
Hint Resolve swap_safe_choice_sequence_entry_normalize2 : slow.*)

(*Lemma same_library_entries_preserves_is_cs_default_entry {o} :
  forall (e1 e2 : @library_entry o),
    same_library_entries e1 e2
    -> is_cs_default_entry e2
    -> is_cs_default_entry e1.
Proof.
  introv same ics.
  unfold is_cs_default_entry in *.
  destruct e1, e2; simpl in *; repnd; subst; tcsp; ginv; dands; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_preserves_is_cs_default_entry : slow.*)

(*Lemma same_library_entries_preserves_entry_in_inf_library_default {o} :
  forall e1 e2 (lib : @inf_library o),
    same_library_entries e1 e2
    -> entry_in_inf_library_default e2 lib
    -> entry_in_inf_library_default e1 lib.
Proof.
  introv same i.
  unfold entry_in_inf_library_default in *; repnd.
  dands; eauto 3 with slow.
Qed.
Hint Resolve same_library_entries_preserves_entry_in_inf_library_default : slow.*)

(*Lemma implies_swap_inf_lib_extends_ext_entries_right {o} :
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
Hint Resolve implies_swap_inf_lib_extends_ext_entries_right : slow.*)

Lemma implies_swap_safe_library {o} :
  forall sw (lib : @library o),
    sane_swapping sw
    -> safe_library lib
    -> safe_library (swap_cs_lib sw lib).
Proof.
  introv sane safe i.
  apply entry_in_swap_library_implies in i; exrepnd; subst; eauto 3 with slow.
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
  remember (vals x) as w; destruct w; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_inf_choice_seq_vals_idem : slow.

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

(*Lemma swap_cs_inf_choice_seq_entry_normalize_idem {o} :
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
Hint Resolve swap_cs_inf_choice_seq_entry_normalize_idem : slow.*)

(*Lemma swap_cs_inf_lib_entry_idem {o} :
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
Hint Resolve swap_cs_inf_lib_entry_idem : slow.*)

(*Lemma entry_in_swap_inf_library_n_implies {o} :
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
Qed.*)

(*Lemma swap_entry_in_inf_library_n {o} :
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
Hint Resolve swap_entry_in_inf_library_n : slow.*)

(*Lemma swap_inf_choice_sequence_satisfies_restriction {o} :
  forall sw (vals : @InfChoiceSeqVals o) restr,
    inf_choice_sequence_satisfies_restriction vals restr
    -> inf_choice_sequence_satisfies_restriction
         (swap_cs_inf_choice_seq_vals sw vals)
         (swap_cs_choice_seq_restr sw restr).
Proof.
  introv sat.
  unfold swap_cs_inf_choice_seq_vals.
  unfold inf_choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; introv; try congruence;
    pose proof (sat n) as sat;
    remember (vals n) as w; destruct w; simpl; tcsp; try congruence;
      try (complete (unfold swap_cs_restriction_pred; autorewrite with slow; auto)).
Qed.
Hint Resolve swap_inf_choice_sequence_satisfies_restriction : slow.*)

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

(*Definition safe_inf_library_sw {o} sw (inflib : @inf_library o) :=
  forall entry, entry_in_inf_library entry inflib -> safe_inf_library_entry_sw sw entry.*)

(*Lemma swap_norm_inf_choice_sequence_vals_extend {o} :
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
  unfold swap_cs_inf_choice_seq_vals; allrw; simpl.
  remember (select n l) as sel; symmetry in Heqsel; destruct sel; auto;[].

  unfold choice_sequence_satisfies_restriction, is_nat_seq_restriction in *.
  destruct restr; simpl in *; tcsp; repnd;[].
  applydup sat in sel1.
  apply isn2 in sel2; eauto 3 with slow;[].
  unfold cterm_is_nth in sel2.
  rewrite Heqsel in sel2; exrepnd; ginv.
  autorewrite with slow; auto.
Qed.
Hint Resolve swap_norm_inf_choice_sequence_vals_extend : slow.*)

(*Lemma normalize_vals_swap_inf_choice_sequence_entry_extend {o} :
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
Hint Resolve normalize_vals_swap_inf_choice_sequence_entry_extend : slow.*)

(*Lemma swap_inf_choice_sequence_entry_extend_normalize_vals {o} :
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
Hint Resolve swap_inf_choice_sequence_entry_extend_normalize_vals : slow.*)

(*Lemma swap_norm_inf_entry_extends {o} :
  forall sw e1 (e2 : @library_entry o),
    inf_entry_extends e1 e2
    -> inf_entry_extends
         (swap_cs_inf_lib_entry_normalize_vals sw e1)
         (swap_cs_lib_entry sw e2).
Proof.
  introv safe i.
  unfold inf_entry_extends; simpl in *.
  destruct e1, e2; simpl in *; repnd; subst; tcsp.
  dands; auto; eauto 2 with slow.
Qed.
Hint Resolve swap_norm_inf_entry_extends : slow.*)

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

(*Lemma swap_norm_entry_in_inf_library_extends {o} :
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
Hint Resolve swap_norm_entry_in_inf_library_extends : slow.*)

(*Lemma implies_safe_choice_sequence_entry_swap {o} :
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

    { introv len; rewrite safe; auto. }

    { introv sel; apply option_map_Some in sel; exrepnd; subst.
      unfold swap_cs_restriction_pred; simpl; autorewrite with slow; tcsp. }
  }

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

    { introv len; rewrite safe; auto. }

    { introv sel; apply option_map_Some in sel; exrepnd; subst.
      unfold swap_cs_restriction_pred; simpl; autorewrite with slow; tcsp. }
  }
Qed.
Hint Resolve implies_safe_choice_sequence_entry_swap : slow.*)

(*Lemma implies_safe_library_entry_sw_swap {o} :
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
Hint Resolve implies_safe_library_entry_sw_swap : slow.*)

(*Lemma swap_norm_entry_in_inf_library_default {o} :
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
Hint Resolve swap_norm_entry_in_inf_library_default : slow.*)

(*Lemma implies_swap_norm_inf_lib_extends_ext_entries_right {o} :
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
Hint Resolve implies_swap_norm_inf_lib_extends_ext_entries_right : slow.*)

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

Lemma on_some_False_implies :
  forall {A} (x : option A) (f : A -> Prop),
    on_some x f False <-> exists a, x = Some a /\ f a.
Proof.
  introv; split; intro h.
  { destruct x; simpl in *; eauto; tcsp. }
  { exrepnd; subst; simpl; auto. }
Qed.

(*Lemma implies_safe_swap_norm_cs_inf_choice_sequence_entry {o} :
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
        repnd; tcsp; try (complete (apply safe0; tcsp));
          pose proof (safe n0) as safe; apply on_some_False_implies in safe; exrepnd; allrw; simpl.
      { apply safe0 in safe2; unfold is_nat in *; exrepnd; subst; autorewrite with slow; eauto. }

      destruct (lt_dec n0 (length l)).
      { pose proof (safe3 n0 a) as q; autodimp q hyp; apply q in safe4.
        unfold cterm_is_nth in safe4; exrepnd; allrw; autorewrite with slow; eauto 3 with slow. }
      { pose proof (safe0 n0 a) as q; autodimp q hyp; try omega; apply q in safe4.
        unfold cterm_is_nth in safe4; exrepnd; allrw; autorewrite with slow; eauto 3 with slow. }
    }

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      destruct k1; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; try (complete (apply safe0; tcsp)).
      pose proof (safe n0) as safe.
      remember (vals n0) as w; destruct w; simpl in *; tcsp.
      apply safe0 in safe; unfold is_bool in safe; exrepnd; subst; autorewrite with slow; eauto 3 with slow. }

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
        pose proof (safe n0) as q.
        apply on_some_False_implies in q; exrepnd; allrw; simpl.
        apply safe0 in q0; unfold is_nat in q0; exrepnd; subst; autorewrite with slow; eauto 3 with slow. }

      { unfold natSeq2restrictionPred; allrw; auto; eauto 3 with slow.
        pose proof (safe n0) as q.
        apply on_some_False_implies in q; exrepnd; allrw; simpl.
        destruct (lt_dec n0 (length l0)).

        { pose proof (safe3 n0 a) as q; autodimp q hyp; apply q in q0.
          unfold cterm_is_nth in q0; exrepnd.
          allrw; autorewrite with slow; eauto 3 with slow. }

        { pose proof (safe0 n0 a) as q; autodimp q hyp; try omega.
          apply q in q0; unfold is_nat in q0; exrepnd; subst; autorewrite with slow; eauto 3 with slow. } } } }

  { unfold compatible_choice_sequences in *; simpl in *.
    destruct k1; boolvar; subst; simpl in *; tcsp; dands; eauto 3 with slow;[| | |].

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      destruct k2; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; try (complete (apply safe0; tcsp));
         pose proof (safe n) as q; apply on_some_False_implies in q; exrepnd; allrw; simpl.
      { apply safe0 in q0; unfold is_nat in q0; exrepnd; subst; autorewrite with slow; eauto 3 with slow. }
      destruct (lt_dec n (length l)).
      { pose proof (safe3 n a) as q; apply q in q0; auto.
        unfold cterm_is_nth in q0; exrepnd; allrw; autorewrite with slow; eauto 3 with slow. }
      { pose proof (safe0 n a) as q; apply q in q0; try omega.
        unfold is_nat in q0; exrepnd; subst; autorewrite with slow; eauto 3 with slow. } }

    { introv; unfold swap_cs_inf_choice_seq_vals; autorewrite with slow.
      unfold correct_restriction in *; simpl in *.
      unfold inf_choice_sequence_satisfies_restriction in *.
      destruct k2; boolvar; subst; simpl in *; tcsp; destruct restr; simpl in *;
        repnd; tcsp; try (complete (apply safe0; tcsp)).
      pose proof (safe n) as safe; apply on_some_False_implies in safe; exrepnd; allrw; simpl.
      apply safe0 in safe2; unfold is_bool in safe2; exrepnd; subst; autorewrite with slow; eauto 3 with slow. }

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
        pose proof (safe n) as q; apply on_some_False_implies in q; exrepnd; allrw; simpl.
        apply safe0 in q0; unfold is_nat in q0; exrepnd; subst; autorewrite with slow; eauto 3 with slow. }

      { unfold natSeq2restrictionPred; allrw; auto; eauto 3 with slow.
        pose proof (safe n) as q; apply on_some_False_implies in q; exrepnd; allrw; simpl.
        destruct (lt_dec n (length l0)).

        { apply safe3 in q0; auto.
          unfold cterm_is_nth in q0; exrepnd.
          allrw; autorewrite with slow; eauto 3 with slow. }

        { apply safe0 in q0; auto; try omega; unfold is_nat in q0; exrepnd; subst; autorewrite with slow; eauto 3 with slow. } } } }
Qed.
Hint Resolve implies_safe_swap_norm_cs_inf_choice_sequence_entry : slow.*)

(*Lemma implies_swap_safe_inf_library {o} :
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
Hint Resolve implies_swap_safe_inf_library : slow.*)

(*Lemma implies_swap_inf_lib_extends_left {o} :
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
Hint Resolve implies_swap_inf_lib_extends_left : slow.*)

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

(*Lemma swap_choice_sequence_entry_extend {o} :
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
Hint Resolve swap_choice_sequence_entry_extend : slow.*)

Lemma swap_entry_extends {o} :
  forall sw (e1 e2 : @library_entry o),
    entry_extends e1 e2
    -> entry_extends (swap_cs_lib_entry sw e1) (swap_cs_lib_entry sw e2).
Proof.
  introv ext.
  inversion ext; subst; clear ext; eauto 3 with slow.
  unfold swap_cs_lib_entry; simpl; eauto.
  unfold swap_cs_choice_seq_vals; rewrite map_app; eauto.
Qed.
Hint Resolve swap_entry_extends : slow.

Lemma swap_entry_in_library_extends {o} :
  forall sw (e : @library_entry o) lib,
    entry_in_library_extends e lib
    -> entry_in_library_extends (swap_cs_lib_entry sw e) (swap_cs_plib sw lib).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; autorewrite with slow in *;[left|right];
    dands; autorewrite with slow; eauto 3 with slow.
Qed.
Hint Resolve swap_entry_in_library_extends : slow.

Lemma swap_lib_extends_entries {o} :
  forall sw (lib1 lib2 : @plibrary o),
    lib_extends_entries lib1 lib2
    -> lib_extends_entries (swap_cs_plib sw lib1) (swap_cs_plib sw lib2).
Proof.
  introv ext i.
  apply entry_in_swap_library_implies in i; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve swap_lib_extends_entries : slow.

Definition swapping_in_library {o} (sw : cs_swap) (lib : @library o) :=
  name_in_library (fst sw) lib
  /\ name_in_library (snd sw) lib.

(*Lemma lib_extends_preserves_safe_library_sw {o} :
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
Hint Resolve lib_extends_preserves_safe_library_sw : slow.*)

Lemma in_swap_library_implies {o} :
  forall sw entry (lib : @plibrary o),
    List.In entry (swap_cs_plib sw lib)
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
  forall sw entry (lib : @plibrary o),
    List.In entry lib
    -> List.In (swap_cs_lib_entry sw entry) (swap_cs_plib sw lib).
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

Lemma in_lib_entry_name_abs_swap_cs_lib {o} :
  forall sw op (lib : @library o),
    in_lib (entry_name_abs op) (swap_cs_lib sw lib)
    <-> in_lib (entry_name_abs op) lib.
Proof.
  introv; split; intro h; unfold in_lib in *; exrepnd.
  { apply in_swap_library_implies in h1; exrepnd; subst.
    eexists; dands; eauto.
    destruct e0; simpl in *; tcsp. }
  { apply (swap_in_library sw) in h1.
    eexists; dands; eauto.
    destruct e; simpl in *; tcsp. }
Qed.
Hint Rewrite @in_lib_entry_name_abs_swap_cs_lib : slow.

Lemma in_lib_entry_name_cs_swap_cs_lib {o} :
  forall sw name (lib : @library o),
    in_lib (entry_name_cs (swap_cs sw name)) (swap_cs_lib sw lib)
    <-> in_lib (entry_name_cs name) lib.
Proof.
  introv; split; intro h; unfold in_lib in *; exrepnd.
  { apply in_swap_library_implies in h1; exrepnd; subst.
    eexists; dands; eauto.
    destruct e0; simpl in *; tcsp.
    apply swap_cs_inj in h0; auto. }
  { apply (swap_in_library sw) in h1.
    eexists; dands; eauto.
    destruct e; simpl in *; subst; tcsp. }
Qed.
Hint Rewrite @in_lib_entry_name_cs_swap_cs_lib : slow.

Lemma length_swap_cs_choice_seq_vals {o} :
  forall sw (vals : @ChoiceSeqVals o),
    length (swap_cs_choice_seq_vals sw vals) = length vals.
Proof.
  introv; unfold swap_cs_choice_seq_vals; autorewrite with slow; auto.
Qed.
Hint Rewrite @length_swap_cs_choice_seq_vals : slow.

Lemma swap_cs_choice_seq_vals_snoc {o} :
  forall sw v (vals : @ChoiceSeqVals o),
    swap_cs_choice_seq_vals sw (snoc vals v)
    = snoc (swap_cs_choice_seq_vals sw vals) (swap_cs_cterm sw v).
Proof.
  introv; unfold swap_cs_choice_seq_vals; rewrite map_snoc; auto.
Qed.
Hint Rewrite @swap_cs_choice_seq_vals_snoc : slow.

Lemma implies_add_choice_swap {o} :
  forall sw name v (lib : @plibrary o) n restr lib',
    add_choice name v lib = Some (n, restr, lib')
    -> add_choice
         (swap_cs sw name)
         (swap_cs_cterm sw v)
         (swap_cs_plib sw lib)
       = Some (n, swap_cs_choice_seq_restr sw restr, swap_cs_plib sw lib').
Proof.
  induction lib; introv add; simpl in *; ginv;[].
  destruct a; simpl in *; tcsp;[|].

  { destruct entry as [vals restr']; simpl in *; boolvar; subst; simpl in *; ginv;
      autorewrite with slow; tcsp.

    { inversion add; subst; clear add; simpl in *; autorewrite with slow; tcsp. }

    { apply swap_cs_inj in e; subst; simpl in *; tcsp. }

    { remember (add_choice name v) as w; symmetry in Heqw; destruct w; ginv; repnd; simpl in *.
      inversion add; clear add; subst; simpl in *.
      pose proof (IHlib n restr p) as IHlib; repeat (autodimp IHlib hyp).
      allrw; tcsp. } }

  { remember (add_choice name v) as w; symmetry in Heqw; destruct w; ginv; repnd; simpl in *.
    inversion add; clear add; subst; simpl in *.
    pose proof (IHlib n restr p) as IHlib; repeat (autodimp IHlib hyp).
    allrw; tcsp. }
Qed.

Lemma implies_add_one_choice_swap {o} :
  forall sw name v (lib : @library o) n restr lib',
    add_one_choice name v lib = Some (n, restr, lib')
    -> add_one_choice
         (swap_cs sw name)
         (swap_cs_cterm sw v)
         (swap_cs_lib sw lib)
       = Some (n, swap_cs_choice_seq_restr sw restr, swap_cs_lib sw lib').
Proof.
  introv h; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv.
  erewrite implies_add_choice_swap; [|eauto]; tcsp.
Qed.

Lemma swap_add_new_abs {o} :
  forall sw op vars rhs correct (lib : @library o),
    swap_cs_lib sw (add_new_abs op vars rhs correct lib)
    = add_new_abs
        op vars (swap_cs_soterm sw rhs) (swap_cs_correct_abs sw op vars rhs correct)
        (swap_cs_lib sw lib).
Proof.
  introv; tcsp.
Qed.
Hint Rewrite @swap_add_new_abs : slow.

Lemma swap_apply_list {o} :
  forall sw l (t : @NTerm o),
    swap_cs_term sw (apply_list t l)
    = apply_list (swap_cs_term sw t) (map (swap_cs_term sw) l).
Proof.
  induction l; introv; simpl; auto.
  rewrite IHl; simpl; tcsp.
Qed.

Lemma swap_cs_term_soterm2nterm {o} :
  forall sw (t : @SOTerm o),
    swap_cs_term sw (soterm2nterm t)
    = soterm2nterm (swap_cs_soterm sw t).
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv; simpl; auto;[|].

  { rewrite swap_apply_list.
    repeat rewrite map_map.
    f_equal.
    apply eq_maps; introv i; unfold compose; simpl; tcsp. }

  { f_equal.
    repeat rewrite map_map.
    apply eq_maps; introv i; unfold compose; simpl; tcsp.
    destruct x; simpl; f_equal; eapply ind; eauto. }
Qed.

Lemma implies_sat_cond_soterm_swap {o} :
  forall sw t (lib : @library o),
    sat_cond_soterm lib t
    -> sat_cond_soterm (swap_cs_lib sw lib) (swap_cs_soterm sw t).
Proof.
  introv h; unfold sat_cond_soterm; simpl.
  unfold swap_cs_lib_cond; simpl.
  rewrite <- swap_cs_term_soterm2nterm; autorewrite with slow; tcsp.
Qed.
Hint Resolve implies_sat_cond_soterm_swap : slow.

Lemma implies_sat_cond_cterm_swap {o} :
  forall sw t (lib : @library o),
    sat_cond_cterm lib t
    -> sat_cond_cterm (swap_cs_lib sw lib) (swap_cs_cterm sw t).
Proof.
  introv h; unfold sat_cond_cterm; simpl.
  unfold swap_cs_lib_cond; simpl.
  destruct_cterms; simpl; autorewrite with slow; tcsp.
Qed.
Hint Resolve implies_sat_cond_cterm_swap : slow.

Lemma swap_add_new_cs {o} :
  forall sw name restr (lib : @library o),
    swap_cs_lib sw (add_new_cs name restr lib)
    = add_new_cs (swap_cs sw name) (swap_cs_choice_seq_restr sw restr) (swap_cs_lib sw lib).
Proof.
  introv; tcsp.
Qed.
Hint Rewrite @swap_add_new_cs : slow.

Lemma swap_lib_extends {o} :
  forall {sw} {lib1 lib2 : @library o},
    sane_swapping sw
    -> lib_extends lib1 lib2
    -> lib_extends (swap_cs_lib sw lib1) (swap_cs_lib sw lib2).
Proof.
  introv sane ext.
  lib_ext_ind ext Case.

  { Case "lib_ext_new_abs".
    autorewrite with slow.
    eapply lib_extends_new_abs; eauto 3 with slow.
    intro xx; autorewrite with slow in *; tcsp. }

  { Case "lib_ext_new_cs".
    autorewrite with slow.
    eapply lib_extends_new_cs; eauto with slow.
    { intro xx; autorewrite with slow in *; tcsp. }
    unfold sat_cond_restr; simpl; autorewrite with slow; tcsp. }

  { Case "lib_ext_cs".
    apply (lib_extends_cs
             _
             (swap_cs sw name)
             (swap_cs_cterm sw v)
             n
             (swap_cs_restriction_pred sw M)); eauto 3 with slow.
    { erewrite implies_add_one_choice_swap; eauto; simpl; tcsp. }
    unfold swap_cs_restriction_pred; autorewrite with slow; auto. }

(*  { Case "lib_ext_law".
    apply (lib_extends_law
             _
             (swap_cs sw name)
             (swap_cs_cterm sw v)
             n
             (fun n => swap_cs_cterm sw (f n))); eauto 3 with slow; try congruence.
    erewrite implies_add_choice_swap; eauto; simpl; tcsp. }

  { Case "lib_ext_res".
    apply (lib_extends_res
             _
             (swap_cs sw name)
             (swap_cs_cterm sw v)
             n
             (swap_cs_restriction_pred sw P)); eauto 3 with slow; try congruence.
    { erewrite implies_add_choice_swap; eauto; simpl; tcsp. }
    unfold swap_cs_restriction_pred; autorewrite with slow; auto. }*)
Qed.
Hint Resolve swap_lib_extends : slow.

Definition ren_cs_per {o} r (e : per(o)) : per :=
  fun a b => e (ren_cs_cterm r a) (ren_cs_cterm r b).

Definition ren_cs_lib_per_ext {o} {lib lib'}
           (r : cs_ren)
           (x : lib_extends lib' lib)
           (eqa : lib-per(lib,o)) : lib-per(lib',o).
Proof.
  exists (fun lib'' (xt : lib_extends lib'' lib') => ren_cs_per r (eqa lib'' (lib_extends_trans xt x)));[].
  repeat introv; simpl.
  unfold ren_cs_per.
  apply eqa.
Defined.

Definition ren_cs_lib_per {o} {lib}
           (r : cs_ren)
           (eqa : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (xt : lib_extends lib' lib) => ren_cs_per r (eqa lib' xt));[].
  repeat introv; simpl.
  unfold ren_cs_per.
  apply eqa.
Defined.

Definition cs_compatible_upto {o}
           (name1 name2 : choice_sequence_name)
           (lib : @library o)
           (b   : nat):=
  forall m : nat,
    m < b
    ->
    {k : nat
     & find_cs_value_at lib name1 m = Some (mkc_nat k)
     # find_cs_value_at lib name2 m = Some (mkc_nat k)}.

Definition cs_size_max {o} (lib : @library o) (name : choice_sequence_name) : nat :=
  match find_cs lib name with
  | Some e => Peano.max (length (cse_vals e)) (cs_name_restr_size name)
  | None => 0
  end.

Definition cs_compatible_in_lib {o}
           (name1 name2 : choice_sequence_name)
           (lib : @library o) :=
  forall m : nat,
    m < cs_size lib name1
    ->
    {k : nat
     & find_cs_value_at lib name1 m = Some (mkc_nat k)
     # find_cs_value_at lib name2 m = Some (mkc_nat k)}.

Definition cs_compatible_in_ext {o}
           (name1 name2 : choice_sequence_name)
           (lib' lib : @library o) :=
  forall m : nat,
    m < lib_depth lib
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

(*Definition bar_per_type {o} {lib} (bar : @BarLib o lib) :=
  forall lib1 (b : bar_lib_bar bar lib1)
         lib2 (ext : lib_extends lib2 lib1)
         (x : lib_extends lib2 lib), per(o).*)

(*Definition bar_per_type_cond {o} {lib} {bar : @BarLib o lib}
           (p : bar_per_type bar) :=
  forall (lib' lib1 : library)
         (b : bar_lib_bar bar lib1)
         (ext : lib_extends lib' lib1)
         (x y : lib_extends lib' lib),
    (p lib1 b lib' ext x) <=2=> (p lib1 b lib' ext y).*)

(*Record bar_per {o} {lib} (bar : @BarLib o lib) :=
  MkBarPer
    {
      bar_per_per :> bar_per_type bar;
      bar_per_cond : bar_per_type_cond bar_per_per
    }.*)

(*Definition bar_per2per {o} {lib} {bar : @BarLib o lib} (p : bar_per bar) : per :=
  fun t1 t2 =>
    forall lib1 (b : bar_lib_bar bar lib1)
           lib2 (ext : lib_extends lib2 lib1)
           (x : lib_extends lib2 lib),
      bar_per_per _ p lib1 b lib2 ext x t1 t2.*)

(*Definition bar_per2lib_per {o} {lib}
           {bar : @BarLib o lib}
           (p : bar_per bar)
  : lib-per(lib,o).
Proof.
  exists (fun lib2 (x : lib_extends lib2 lib) t1 t2 =>
            forall lib1 (b : bar_lib_bar bar lib1) (ext : lib_extends lib2 lib1),
              bar_per_per _ p lib1 b lib2 ext x t1 t2).
  repeat introv.
  split; intro q; introv; eapply (bar_per_cond _ p); eauto.
Defined.*)

(*Lemma all_in_bar_ext_exists_per_implies_exists2 {o} :
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
Defined.*)

(*Lemma sub_per_per_bar_eq_raise_right {o} :
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
         (per_bar_eq lib eqa)
         (per_bar_eq lib' (bar_per2lib_per f)).
Proof.
  introv cond equ.
  unfold per_bar_eq in *.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ extb) in equ; simpl in *.
  eapply in_open_bar_ext_pres; try exact equ; clear equ; introv equ; introv.
  pose proof (cond _ b0 _ ext e) as cond.
  apply cond; auto.
Qed.*)

(*Lemma sub_per_per_bar_eq_raise_right2 {o} :
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
         (per_bar_eq lib eqa)
         (per_bar_eq lib' (raise_lib_per (bar_per2lib_per f) extb)).
Proof.
  introv cond equ.
  unfold per_bar_eq in *.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ extb) in equ; simpl in *.
  eapply in_open_bar_ext_pres; try exact equ; clear equ; introv equ; introv.
  pose proof (cond _ b0 _ ext (lib_extends_trans e extb)) as cond.
  apply cond; auto.
Qed.*)

Lemma type_system_implies_type_extensionality {o} :
  forall (ts : cts(o)),
    type_system ts
    -> type_extensionality ts.
Proof.
  introv h; destruct h; tcsp.
Qed.
Hint Resolve type_system_implies_type_extensionality : slow.

(* [n2]'s name with [n1]'s space *)
Definition adopt_space (n1 n2 : choice_sequence_name) : choice_sequence_name :=
  MkChoiceSequenceName (csn_name n2) (csn_kind n1).

(* We traverse [lib], and remove [n2] as we go, until we reach [n1], in which case
     we rename it to n2 *)
Fixpoint rename_cs_plib {o}
         (lib : @plibrary o)
         (n1 n2 : choice_sequence_name) : plibrary :=
  match lib with
  | [] => []
  | lib_cs name e as entry :: lib =>
    if choice_sequence_name_deq name n1
    then lib_cs n2 e :: rename_cs_plib lib n1 n2
    else if choice_sequence_name_deq name n2
         then rename_cs_plib lib n1 n2
         else entry :: rename_cs_plib lib n1 n2
  | lib_abs _ _ _ _ as entry :: lib => entry :: rename_cs_plib lib n1 n2
  end.

Definition extend_lib_with {o}
           (lib : @plibrary o)
           (n1 n2 : choice_sequence_name) : plibrary :=
  match find_cs lib n1 with
  | Some e =>
    lib_cs (adopt_space n1 n2) e :: lib
  | None => lib
  end.

(*Definition inf_lib_extends_ext_entries_upto {o}
           (infl : inf_library)
           (lib  : @library o)
           (n    : nat) :=
  forall entry : library_entry,
    entry_in_library entry lib ->
    entry_in_inf_library_extends entry n infl
                                 {+} entry_in_inf_library_default entry infl.*)

(*Lemma inf_lib_extends_ext_entries_implies {o} :
  forall (infl : inf_library) (lib : @library o),
    inf_lib_extends_ext_entries infl lib
    -> exists n, inf_lib_extends_ext_entries_upto infl lib n.
Proof.
  induction lib using rev_list_ind; introv i; simpl in *.

  { exists 0; introv h; tcsp. }

  applydup @inf_lib_extends_ext_entries_snoc_implies_head in i.
  autodimp IHlib hyp; exrepnd.

  remember (forallb (diff_entry_names a) lib) as b; symmetry in Heqb.
  destruct b;
    [fold (non_shadowed_entry a lib) in Heqb
    |fold (shadowed_entry a lib) in Heqb].

  { apply inf_lib_extends_ext_entries_snoc_implies_entry_ext in i; auto.
    repndors; exrepnd.

    { exists (Peano.max k n).
      introv j.

      apply entry_in_library_snoc_implies in j.
      repndors; tcsp.

      { apply IHlib0 in j.
        repndors; tcsp;[].
        left.
        eapply le_preserves_entry_in_inf_library_extends;[|eauto].
        eauto 3 with slow. }

      repnd; subst; GC.
      left.
      eapply le_preserves_entry_in_inf_library_extends;[|eauto].
      eauto 3 with slow. }

    exists n.
    introv j.

    apply entry_in_library_snoc_implies in j.
    repndors; tcsp;[].
    repnd; subst; GC; tcsp. }

  exists n.
  introv j.

  apply entry_in_library_snoc_implies in j.
  repndors; tcsp.
  repnd; subst; GC.
  unfold non_shadowed_entry in j.
  rewrite Heqb in j; ginv.
Qed.*)

Fixpoint cs_name_in_inf_library {o}
         (name : choice_sequence_name)
         (lib  : @inf_library o)
         (n    : nat) : bool :=
  match n with
  | 0 => false
  | S n =>
    match lib 0 with
    | inf_lib_cs name' _ =>
      if choice_sequence_name_deq name name' then true
      else cs_name_in_inf_library name (shift_inf_lib lib) n
    | _ => cs_name_in_inf_library name (shift_inf_lib lib) n
    end
  end.

Lemma cs_name_in_library_implies {o} :
  forall name (lib : @plibrary o),
    cs_name_in_library name lib = true
    -> exists e,
      entry_in_library (lib_cs name e) lib.
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp; GC;[| |].

  { exists entry; tcsp. }

  { autodimp IHlib hyp; exrepnd.
    exists e; dands; tcsp. }

  { autodimp IHlib hyp; exrepnd.
    exists e; dands; tcsp. }
Qed.

Definition cons_inf_lib_entry {o}
           (e   : inf_library_entry)
           (lib : @inf_library o) : inf_library :=
  fun n =>
    if deq_nat n 0 then e
    else lib (pred n).

Lemma entry_in_inf_library_extends_implies_exists {o} :
  forall e n (infLib : @inf_library o),
    entry_in_inf_library_extends e n infLib
    -> exists k,
      inf_entry_extends (infLib k) e
      /\ forall j, j < k -> ~inf_matching_entries (infLib j) e.
Proof.
  induction n; introv i; simpl in *; tcsp.
  repndors; repnd.

  { exists 0; dands; tcsp. }

  applydup IHn in i.
  exrepnd.
  exists (S k); simpl.
  dands; eauto 3 with slow.
  introv ltk.
  destruct j; auto.
  apply i2; omega.
Qed.

(* The 2 names have different names but the same kind/space *)
Definition similar_cs_names (n1 n2 : choice_sequence_name) :=
  csn_name n1 <> csn_name n2
  /\ csn_kind n1 = csn_kind n2.

Lemma entry_in_rename_cs_lib_implies {o} :
  forall n1 n2 e (lib : @plibrary o),
    entry_in_library (lib_cs n2 e) (rename_cs_plib lib n1 n2)
    -> entry_in_library (lib_cs n1 e) lib.
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; boolvar; simpl in *; subst; tcsp;
    repndors; ginv; tcsp; repnd;[].
  destruct i0; tcsp.
Qed.
Hint Resolve entry_in_rename_cs_lib_implies : slow.

Lemma diff_implies_entry_in_rename_cs_lib {o} :
  forall n1 n2 name e (lib : @plibrary o),
    name <> n1
    -> name <> n2
    -> entry_in_library (lib_cs name e) lib
    -> entry_in_library (lib_cs name e) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; introv d1 d2 i; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp.
Qed.
Hint Resolve diff_implies_entry_in_rename_cs_lib : slow.

Lemma if_diff_entry_in_rename_cs_lib {o} :
  forall n1 n2 name e (lib : @plibrary o),
    name <> n1
    -> name <> n2
    -> entry_in_library (lib_cs name e) (rename_cs_plib lib n1 n2)
    -> entry_in_library (lib_cs name e) lib.
Proof.
  induction lib; introv d1 d2 i; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp;
    simpl in *; repndors; repnd; ginv; tcsp.
Qed.
Hint Resolve if_diff_entry_in_rename_cs_lib : slow.

Lemma abs_implies_entry_in_rename_cs_lib {o} :
  forall n1 n2 abs vars rhs cor (lib : @plibrary o),
    entry_in_library (lib_abs abs vars rhs cor) lib
    -> entry_in_library (lib_abs abs vars rhs cor) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp.
Qed.
Hint Resolve abs_implies_entry_in_rename_cs_lib : slow.

Lemma if_abs_entry_in_rename_cs_lib {o} :
  forall n1 n2 abs vars rhs cor (lib : @plibrary o),
    entry_in_library (lib_abs abs vars rhs cor) (rename_cs_plib lib n1 n2)
    -> entry_in_library (lib_abs abs vars rhs cor) lib.
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp;
    repndors; repnd; subst; simpl in *; tcsp; boolvar; subst; tcsp;
      repndors; repnd; ginv; tcsp.
Qed.
Hint Resolve if_abs_entry_in_rename_cs_lib : slow.

(*Lemma diff_implies_entry_in_inf_library_default_cons_two {o} :
  forall n e n1 e1 n2 e2 (infLib : @inf_library o),
    n <> n1
    -> n <> n2
    -> entry_in_inf_library_default (lib_cs n e) infLib
    -> entry_in_inf_library_default
         (lib_cs n e)
         (cons_inf_lib_entry
            (inf_lib_cs n1 e1)
            (cons_inf_lib_entry
               (inf_lib_cs n2 e2)
               infLib)).
Proof.
  introv d1 d2 i.
  unfold entry_in_inf_library_default in *; repnd.
  dands; eauto 3 with slow.
  introv x.
  unfold inf_matching_entries in x; simpl in x.
  unfold cons_inf_lib_entry in x; simpl in x.
  boolvar; subst; simpl in *; subst; tcsp.
Qed.
Hint Resolve diff_implies_entry_in_inf_library_default_cons_two : slow.*)

(*Lemma abs_entry_not_in_inf_library_default {o} :
  forall opabs vars rhs correct (infLib : @inf_library o),
    ~ entry_in_inf_library_default (lib_abs opabs vars rhs correct) infLib.
Proof.
  introv h.
  unfold entry_in_inf_library_default in h; repnd; simpl in *; tcsp.
Qed.*)

Lemma entry_not_in_rename_cs_lib {o} :
  forall n1 n2 e (lib : @plibrary o),
    n1 <> n2
    -> ~ entry_in_library (lib_cs n1 e) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; simpl; tcsp.
  introv d h.
  destruct a; simpl in *; boolvar; subst; tcsp;
    simpl in *; repndors; ginv; simpl in *; tcsp.
Qed.

Lemma rename_cs_lib_same {o} :
  forall n (lib : @plibrary o),
    rename_cs_plib lib n n = lib.
Proof.
  induction lib; simpl in *; tcsp.
  destruct a; simpl in *; rewrite IHlib; tcsp.
  boolvar; subst; tcsp.
Qed.
Hint Rewrite @rename_cs_lib_same : slow.

Lemma similar_cs_names_preserves_correct_restriction {o} :
  forall n1 n2 (restr : @ChoiceSeqRestriction o),
    similar_cs_names n1 n2
    -> correct_restriction n1 restr
    -> correct_restriction n2 restr.
Proof.
  introv sim cor.
  unfold similar_cs_names in sim; simpl in *; repnd; subst; auto.
  unfold correct_restriction in *; allrw <-; auto.
Qed.
Hint Resolve similar_cs_names_preserves_correct_restriction : slow.

Lemma similar_cs_names_preserves_safe_library_entry {o} :
  forall n1 n2 (e : @ChoiceSeqEntry o),
    similar_cs_names n1 n2
    -> safe_library_entry (lib_cs n1 e)
    -> safe_library_entry (lib_cs n2 e).
Proof.
  introv sim safe; simpl in *.
  unfold safe_choice_sequence_entry in *.
  destruct e; simpl in *; repnd.
  dands; eauto 3 with slow.
Qed.
Hint Resolve similar_cs_names_preserves_safe_library_entry : slow.

Lemma implies_safe_rename_cs_lib {o} :
  forall n1 n2 (lib : @plibrary o),
    similar_cs_names n1 n2
    -> safe_library lib
    -> safe_library (rename_cs_plib lib n1 n2).
Proof.
  introv sim safe i.

  destruct (choice_sequence_name_deq n1 n2); subst;
    autorewrite with slow in *; tcsp;[].

  destruct entry.

  { destruct (choice_sequence_name_deq name n1); subst; eauto 3 with slow.

    { apply entry_not_in_rename_cs_lib in i; tcsp. }

    destruct (choice_sequence_name_deq name n2); subst; eauto 3 with slow.

    apply entry_in_rename_cs_lib_implies in i.
    apply safe in i; auto; eauto 2 with slow. }

  { apply if_abs_entry_in_rename_cs_lib in i.
    apply safe in i; auto. }
Qed.
Hint Resolve implies_safe_rename_cs_lib : slow.

Lemma shift_inf_lib_cons_inf_lib_entry {o} :
  forall e (infLib : @inf_library o),
    shift_inf_lib (cons_inf_lib_entry e infLib) = infLib.
Proof.
  introv.
  apply functional_extensionality; introv; simpl.
  unfold shift_inf_lib.
  unfold cons_inf_lib_entry.
  boolvar; simpl; ginv; auto.
Qed.
Hint Rewrite @shift_inf_lib_cons_inf_lib_entry : slow.

(*Lemma entry_in_inf_library_zero {o} :
  forall (infLib : @inf_library o),
    entry_in_inf_library (infLib 0) infLib.
Proof.
  introv; left; exists 1; simpl; tcsp.
Qed.
Hint Resolve entry_in_inf_library_zero : slow.*)

(*Lemma entry_in_inf_library_n_implies_entry_in_inf_library {o} :
  forall n e (infLib : @inf_library o),
    entry_in_inf_library_n n e infLib
    -> entry_in_inf_library e infLib.
Proof.
  induction n; introv h; simpl in *; tcsp.
  repndors; subst; repnd; tcsp; eauto 3 with slow.
Qed.
Hint Resolve entry_in_inf_library_n_implies_entry_in_inf_library : slow.*)

Lemma cons_inf_lib_entry_S {o} :
  forall e (infLib : @inf_library o) n,
    cons_inf_lib_entry e infLib (S n) = infLib n.
Proof.
  introv.
  unfold cons_inf_lib_entry.
  boolvar; simpl; ginv; auto.
Qed.
Hint Rewrite @cons_inf_lib_entry_S : slow.

Lemma cons_inf_lib_entry_zero {o} :
  forall e (infLib : @inf_library o),
    cons_inf_lib_entry e infLib 0 = e.
Proof.
  introv.
  unfold cons_inf_lib_entry; simpl; auto.
Qed.
Hint Rewrite @cons_inf_lib_entry_zero : slow.

Lemma not_matching_inf_entries_implies_not_same_name {o} :
  forall (e1 e2 : @inf_library_entry o),
    ~ matching_inf_entries e2 e1
    -> ~ same_entry_name (inf_entry2name e1) (inf_entry2name e2).
Proof.
  introv h same; destruct h.
  destruct e1, e2; simpl in *; subst; tcsp.
  unfold matching_inf_entries; simpl; auto.
  apply same_opabs_sym; auto.
Qed.
Hint Resolve not_matching_inf_entries_implies_not_same_name : slow.

(*Lemma entry_in_inf_library_entry_implies {o} :
  forall e1 e2 (infLib : @inf_library o),
    entry_in_inf_library e1 (cons_inf_lib_entry e2 infLib)
    -> e1 = e2
       \/ (entry_in_inf_library e1 infLib
           /\ ~ same_entry_name (inf_entry2name e1) (inf_entry2name e2)).
Proof.
  introv i.
  unfold entry_in_inf_library in i; repndors; exrepnd.

  { destruct n; simpl in *; tcsp.
    repndors; exrepnd; subst; simpl in *.

    { unfold cons_inf_lib_entry; simpl; tcsp. }

    autorewrite with slow in *.
    unfold cons_inf_lib_entry in i1; simpl in *.
    right; dands; eauto 3 with slow. }

  { unfold inf_entry_in_inf_library_default in i; repnd.
    right; dands; eauto 3 with slow.

    { right.
      unfold inf_entry_in_inf_library_default.
      dands; eauto 3 with slow.
      introv m.
      destruct (i0 (S n)).
      autorewrite with slow; auto. }

    { pose proof (i0 0) as i0; autorewrite with slow in *; eauto 3 with slow. } }
Qed.*)

(*Lemma implies_safe_inf_library_cons_inf_lib_entry {o} :
  forall e (infLib : @inf_library o),
    safe_inf_library_entry e
    -> safe_inf_library infLib
    -> safe_inf_library (cons_inf_lib_entry e infLib).
Proof.
  introv safee safel i.
  apply entry_in_inf_library_entry_implies in i; repndors; repnd; subst; auto.
Qed.
Hint Resolve implies_safe_inf_library_cons_inf_lib_entry : slow.*)

Lemma similar_cs_name_sym :
  forall n1 n2,
    similar_cs_names n1 n2
    -> similar_cs_names n2 n1.
Proof.
  introv sim.
  unfold similar_cs_names in *; repnd; dands; tcsp.
Qed.
Hint Resolve similar_cs_name_sym : slow.

Lemma similar_cs_names_preserves_safe_in_library_entry {o} :
  forall n1 n2 (entry : @InfChoiceSeqEntry o),
    similar_cs_names n1 n2
    -> safe_inf_library_entry (inf_lib_cs n2 entry)
    -> safe_inf_library_entry (inf_lib_cs n1 entry).
Proof.
  introv sim safe; simpl in *.
  unfold safe_inf_choice_sequence_entry in *.
  destruct entry as [vals restr]; simpl in *; repnd.
  dands; auto; eauto 3 with slow.
Qed.
Hint Resolve similar_cs_names_preserves_safe_in_library_entry : slow.

Lemma similar_cs_names_imply_diff :
  forall n1 n2,
    similar_cs_names n1 n2
    -> n1 <> n2.
Proof.
  introv sim h; subst.
  unfold similar_cs_names in sim; repnd; tcsp.
Qed.
Hint Resolve similar_cs_names_imply_diff : slow.

Lemma implies_entry_in_rename_cs_lib {o} :
  forall n1 n2 e (lib : @plibrary o),
    entry_in_library (lib_cs n1 e) lib
    -> entry_in_library (lib_cs n2 e) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; boolvar; simpl in *; subst; tcsp;
    repndors; ginv; tcsp; repnd;[].
  destruct i0; tcsp.
Qed.
Hint Resolve implies_entry_in_rename_cs_lib : slow.

Lemma implies_entry_in_rename_cs_lib_extends {o} :
  forall n1 n2 e (lib : @plibrary o),
    entry_in_library_extends (lib_cs n1 e) lib
    -> entry_in_library_extends (lib_cs n2 e) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; boolvar; simpl in *; subst; tcsp;
    repndors; ginv; tcsp; repnd;
      try (complete (inversion i; subst; tcsp));
      try (complete (destruct i0; tcsp)).
Qed.
Hint Resolve implies_entry_in_rename_cs_lib_extends : slow.

Lemma diff_implies_entry_in_rename_cs_lib_extends {o} :
  forall n1 n2 name e (lib : @plibrary o),
    name <> n1
    -> name <> n2
    -> entry_in_library_extends (lib_cs name e) lib
    -> entry_in_library_extends (lib_cs name e) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; introv d1 d2 i; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp; boolvar; subst; tcsp;
    destruct a; simpl in *; tcsp; boolvar; subst; tcsp;
      try (complete (inversion i; subst; tcsp)).
Qed.
Hint Resolve diff_implies_entry_in_rename_cs_lib_extends : slow.

Lemma abs_implies_entry_in_rename_cs_lib_extends {o} :
  forall n1 n2 abs vars rhs cor (lib : @plibrary o),
    entry_in_library_extends (lib_abs abs vars rhs cor) lib
    -> entry_in_library_extends (lib_abs abs vars rhs cor) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp; boolvar; subst; tcsp;
    destruct a; simpl in *; tcsp; boolvar; subst; tcsp; ginv;
      try (complete (inversion i; subst; tcsp)).
Qed.
Hint Resolve abs_implies_entry_in_rename_cs_lib_extends : slow.

Lemma rename_cs_lib_preserves_lib_extends_entries {o} :
  forall n1 n2 (lib1 lib2 : @plibrary o),
    similar_cs_names n1 n2
    -> lib_extends_entries lib2 lib1
    -> lib_extends_entries (rename_cs_plib lib2 n1 n2) (rename_cs_plib lib1 n1 n2).
Proof.
  introv sim ext i.
  destruct entry.
  { destruct (choice_sequence_name_deq name n1); subst.
    { apply entry_not_in_rename_cs_lib in i; tcsp; eauto 3 with slow. }
    destruct (choice_sequence_name_deq name n2); subst.
    { apply entry_in_rename_cs_lib_implies in i.
      apply ext in i; eauto 3 with slow. }
    apply if_diff_entry_in_rename_cs_lib in i; auto.
    apply ext in i; eauto 3 with slow. }
  { apply if_abs_entry_in_rename_cs_lib in i; eauto 3 with slow. }
Qed.
Hint Resolve rename_cs_lib_preserves_lib_extends_entries : slow.

Lemma cs_not_in_rename_cs_lib {o} :
  forall n1 n2 e (lib : @plibrary o),
    n1 <> n2
    -> ~ List.In (lib_cs n1 e) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; simpl; tcsp.
  introv d h.
  destruct a; simpl in *; boolvar; subst; tcsp;
    simpl in *; repndors; ginv; simpl in *; tcsp.
Qed.

Lemma in_rename_cs_lib_implies {o} :
  forall n1 n2 e (lib : @plibrary o),
    List.In (lib_cs n2 e) (rename_cs_plib lib n1 n2)
    -> List.In (lib_cs n1 e) lib.
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; boolvar; simpl in *; subst; tcsp;
    repndors; ginv; tcsp; repnd.
Qed.
Hint Resolve in_rename_cs_lib_implies : slow.

Lemma implies_in_rename_cs_lib_extends {o} :
  forall n1 n2 e (lib : @plibrary o),
    List.In (lib_cs n1 e) lib
    -> List.In (lib_cs n2 e) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; boolvar; simpl in *; subst; tcsp;
    repndors; ginv; tcsp; repnd.
Qed.
Hint Resolve implies_in_rename_cs_lib_extends : slow.

Lemma if_diff_in_rename_cs_lib {o} :
  forall n1 n2 name e (lib : @plibrary o),
    name <> n1
    -> name <> n2
    -> List.In (lib_cs name e) (rename_cs_plib lib n1 n2)
    -> List.In (lib_cs name e) lib.
Proof.
  induction lib; introv d1 d2 i; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp;
    simpl in *; repndors; repnd; ginv; tcsp.
Qed.
Hint Resolve if_diff_in_rename_cs_lib : slow.

Lemma diff_implies_in_rename_cs_lib_extends {o} :
  forall n1 n2 name e (lib : @plibrary o),
    name <> n1
    -> name <> n2
    -> List.In (lib_cs name e) lib
    -> List.In (lib_cs name e) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; introv d1 d2 i; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp; boolvar; subst; tcsp;
    destruct a; simpl in *; tcsp; boolvar; subst; tcsp.
Qed.
Hint Resolve diff_implies_in_rename_cs_lib_extends : slow.

Lemma abs_implies_in_rename_cs_lib {o} :
  forall n1 n2 abs vars rhs cor (lib : @plibrary o),
    List.In (lib_abs abs vars rhs cor) lib
    -> List.In (lib_abs abs vars rhs cor) (rename_cs_plib lib n1 n2).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp.
Qed.
Hint Resolve abs_implies_in_rename_cs_lib : slow.

Lemma if_abs_in_rename_cs_lib {o} :
  forall n1 n2 abs vars rhs cor (lib : @plibrary o),
    List.In (lib_abs abs vars rhs cor) (rename_cs_plib lib n1 n2)
    -> List.In (lib_abs abs vars rhs cor) lib.
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp;
    repndors; repnd; subst; simpl in *; tcsp; boolvar; subst; tcsp;
      repndors; repnd; ginv; tcsp.
Qed.
Hint Resolve if_abs_in_rename_cs_lib : slow.

(*Lemma rename_cs_lib_preserves_subset_library {o} :
  forall n1 n2 (lib1 lib2 : @library o),
    similar_cs_names n1 n2
    -> subset_library lib2 lib1
    -> subset_library (rename_cs_lib lib2 n1 n2) (rename_cs_lib lib1 n1 n2).
Proof.
  introv sim ext i.
  destruct entry1.
  { destruct (choice_sequence_name_deq name n1); subst.
    { apply cs_not_in_rename_cs_lib in i; tcsp; eauto 3 with slow. }
    destruct (choice_sequence_name_deq name n2); subst.
    { apply in_rename_cs_lib_implies in i.
      apply ext in i; exrepnd.
      inversion i0; subst; simpl in *; tcsp; clear i0.
      destruct entry2; simpl in *; repnd; subst; tcsp; ginv.
      exists (lib_cs n2 entry0); simpl; dands; eauto 3 with slow. }
    apply if_diff_in_rename_cs_lib in i; auto.
    apply ext in i; exrepnd.
    destruct entry2; simpl in *; repnd; subst; tcsp; ginv.
    exists (lib_cs name entry0); simpl; dands; eauto 3 with slow. }
  { apply if_abs_in_rename_cs_lib in i.
    apply ext in i; exrepnd.
    destruct entry2; simpl in *; ginv.
    inversion i0; subst; proof_irr.
    pose proof (correct_abs_proof_irrelevance _ _ _ correct correct0); subst; GC.
    exists (lib_abs opabs vars rhs correct0); simpl; dands; eauto 3 with slow. }
Qed.
Hint Resolve rename_cs_lib_preserves_subset_library : slow.*)

Lemma rename_cs_lib_preserves_safe_library {o} :
  forall n1 n2 (lib1 lib2 : @plibrary o),
    similar_cs_names n1 n2
    -> safe_library lib1
    -> (safe_library lib1 -> safe_library lib2)
    -> safe_library (rename_cs_plib lib1 n1 n2)
    -> safe_library (rename_cs_plib lib2 n1 n2).
Proof.
  introv sim safe1 imp safe.
  autodimp imp hyp.
  apply implies_safe_rename_cs_lib; auto.
Qed.
Hint Resolve rename_cs_lib_preserves_safe_library : slow.

(*Lemma rename_cs_lib_preserves_lib_extends {o} :
  forall n1 n2 (lib1 lib2 : @library o),
    similar_cs_names n1 n2
    -> safe_library lib1
    -> lib_extends lib2 lib1
    -> lib_extends (rename_cs_lib lib2 n1 n2) (rename_cs_lib lib1 n1 n2).
Proof.
  introv sim safe1 ext.
  destruct ext as [ext safe sub].
  split; eauto 3 with slow.
Qed.
Hint Resolve rename_cs_lib_preserves_lib_extends : slow.*)

Lemma diff_entry_in_inf_library_extends_cons_inf_lib_entry_implies {o} :
  forall k n1 n2 e1 e2 (infLib : @inf_library o),
    n1 <> n2
    -> entry_in_inf_library_extends
         (lib_cs n1 e1)
         k
         (cons_inf_lib_entry (inf_lib_cs n2 e2) infLib)
    -> entry_in_inf_library_extends (lib_cs n1 e1) (pred k) infLib.
Proof.
  destruct k; introv d h; simpl in *; tcsp.
Qed.

(*Lemma entry_in_inf_library_default_cons_inf_lib_entry_implies {o} :
  forall n1 n2 e1 e2 (infLib : @inf_library o),
    entry_in_inf_library_default
      (lib_cs n1 e1)
      (cons_inf_lib_entry (inf_lib_cs n2 e2) infLib)
    -> entry_in_inf_library_default (lib_cs n1 e1) infLib.
Proof.
  introv h.
  unfold entry_in_inf_library_default in *.
  repnd; dands; auto.
  introv m.
  pose proof (h0 (S n)) as h0; simpl in *.
  autorewrite with slow in *; tcsp.
Qed.*)

Lemma abs_entry_in_inf_library_extends_cons_inf_lib_entry_implies {o} :
  forall k abs vars rhs cor n e (infLib : @inf_library o),
    entry_in_inf_library_extends
      (lib_abs abs vars rhs cor)
      k
      (cons_inf_lib_entry (inf_lib_cs n e) infLib)
    -> entry_in_inf_library_extends (lib_abs abs vars rhs cor) (pred k) infLib.
Proof.
  destruct k; introv h; simpl in *; tcsp.
Qed.

(*Lemma implies_inf_lib_extends_rename_cs_lib_prop1 {o} :
  forall n1 n2 (lib' lib : @library o) e1 e2 infLib k,
    safe_library lib
    -> similar_cs_names n1 n2
    -> lib_extends lib' lib
    -> inf_lib_cs n2 e1 = infLib k
    -> (forall j x, j < k -> ~ inf_matching_entries (infLib j) (lib_cs n2 x))
    -> inf_lib_extends infLib (rename_cs_lib lib n1 n2)
    -> inf_lib_extends
         (cons_inf_lib_entry
            (inf_lib_cs n1 e1)
            (cons_inf_lib_entry
               (library_entry2inf (lib_cs n2 e2))
               infLib))
         lib'
    -> inf_lib_extends infLib (rename_cs_lib lib' n1 n2).
Proof.
  introv safeL sim exta inInf nm extb extc.
  destruct extb as [extb safeb].
  destruct extc as [extc safec].
  autodimp safeb hyp; eauto 3 with slow;[].
  split; tcsp;[].

  introv i.
  destruct entry.
  { destruct (choice_sequence_name_deq name n1); subst.
    { apply entry_not_in_rename_cs_lib in i; tcsp; eauto 3 with slow. }
    destruct (choice_sequence_name_deq name n2); subst.
    { apply entry_in_rename_cs_lib_implies in i.
      apply extc in i; simpl in *.
      repndors; exrepnd.
      { destruct n0; simpl in *; tcsp.
        repndors; repnd; simpl in *; tcsp; GC;
          [|unfold cons_inf_lib_entry in *; simpl in *;
            destruct i1; unfold inf_matching_entries; simpl; auto];[].
        left.
        exists (S k).
        apply (inf_entry_extends_implies_entry_in_inf_library_extends_same_names
                 _ _ (lib_cs n2 entry)); simpl; tcsp.
        { rewrite <- inInf; simpl; tcsp. }
        introv ltk; apply nm; tcsp. }
      { unfold entry_in_inf_library_default in i; simpl in i; repnd.
        pose proof (i0 0) as i0; simpl in i0.
        unfold cons_inf_lib_entry in i0; simpl in i0; destruct i0; tcsp. } }
    apply if_diff_entry_in_rename_cs_lib in i; auto.
    apply extc in i; simpl in *.
    repndors; exrepnd.
    { apply diff_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0; tcsp.
      apply diff_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0; tcsp.
      left; eauto. }
    { apply entry_in_inf_library_default_cons_inf_lib_entry_implies in i.
      apply entry_in_inf_library_default_cons_inf_lib_entry_implies in i; tcsp. } }
  { apply if_abs_entry_in_rename_cs_lib in i.
    apply extc in i.
    repndors; exrepnd.
    { apply abs_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0.
      apply abs_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0.
      left; eauto. }
    { apply abs_entry_not_in_inf_library_default in i; tcsp. } }
Qed.*)

Lemma inf_choice_sequence_entry_extend_preserves_safe {o} :
  forall n e1 (e2 : @ChoiceSeqEntry o),
    inf_choice_sequence_entry_extend e1 e2
    -> safe_inf_choice_sequence_entry n e1
    -> safe_choice_sequence_entry n e2.
Proof.
  introv ext safe.
  unfold safe_choice_sequence_entry.
  unfold safe_inf_choice_sequence_entry in safe.
  unfold inf_choice_sequence_entry_extend in ext; simpl in *; repnd.
  destruct e1 as [vals1 restr1]; simpl in *; repnd.
  destruct e2 as [vals2 restr2]; simpl in *; repnd.
  dands; eauto 3 with slow.
  eapply same_restrictions_preserves_choice_sequence_satisfies_restriction;[eauto|].
  clear dependent restr2.

  unfold inf_choice_sequence_vals_extend in ext.
  destruct restr1; simpl in *; tcsp.

  { introv sel.
    pose proof (safe n0) as safe; apply on_some_False_implies in safe; exrepnd.
    apply ext in sel; subst; tcsp.
    rewrite safe2 in *; ginv. }

(*  { introv ltl.
    applydup @select_lt_length in ltl; exrepnd.
    rewrite ltl1.
    apply ext in ltl1; subst.
    pose proof (safe i) as safe; apply on_some_False_implies in safe; exrepnd; rewrite safe2 in *; ginv; auto. }

  { introv sel.
    applydup ext in sel.
    pose proof (safe n0) as safe; rewrite sel0 in *; simpl in *; auto. }*)
Qed.
Hint Resolve inf_choice_sequence_entry_extend_preserves_safe : slow.

(*Lemma implies_is_default_inf_choice_sequence_2inf {o} :
  forall vals (restr : @ChoiceSeqRestriction o),
    is_default_choice_sequence vals restr
    -> is_default_inf_choice_sequence
         (choice_seq_vals2inf vals (restriction2default restr)) restr.
Proof.
  introv def.
  unfold is_default_inf_choice_sequence in *.
  unfold is_default_choice_sequence in *.
  destruct restr; simpl in *; tcsp.

  { introv.
    unfold choice_seq_vals2inf.
    remember (select n vals) as sel; symmetry in Heqsel; destruct sel; simpl; tcsp. }

  { introv.
    unfold choice_seq_vals2inf.
    remember (select n vals) as sel; symmetry in Heqsel; destruct sel; simpl; tcsp. }

Qed.
Hint Resolve implies_is_default_inf_choice_sequence_2inf : slow.*)

(*Lemma inf_choice_sequence_entry_extend_2inf_preserves_is_default {o} :
  forall (e1 e2 : @ChoiceSeqEntry o),
    inf_choice_sequence_entry_extend (choice_seq_entry2inf e1) e2
    -> is_default_choice_seq_entry e1
    -> is_default_choice_seq_entry e2.
Proof.
  introv ext def.
  unfold inf_choice_sequence_entry_extend in *; simpl in *; repnd.
  unfold is_default_choice_seq_entry in *.
  destruct e1 as [vals1 restr1]; simpl in *; repnd.
  destruct e2 as [vals2 restr2]; simpl in *; repnd.
  eapply is_default_inf_choice_sequence_implies_is_default_choice_sequence; eauto; eauto 3 with slow.
Qed.
Hint Resolve inf_choice_sequence_entry_extend_2inf_preserves_is_default : slow.*)

(*Lemma inf_choice_sequence_entry_extend_preserves_entry_in_inf_library_default {o} :
  forall n e1 e2 (infLib : @inf_library o),
    inf_choice_sequence_entry_extend (choice_seq_entry2inf e1) e2
    -> entry_in_inf_library_default (lib_cs n e1) infLib
    -> entry_in_inf_library_default (lib_cs n e2) infLib.
Proof.
  introv ext i.
  unfold entry_in_inf_library_default in *.
  simpl in *; repnd; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve inf_choice_sequence_entry_extend_preserves_entry_in_inf_library_default : slow.*)

(*Lemma implies_inf_lib_extends_rename_cs_lib_prop2 {o} :
  forall n1 n2 (lib' lib : @library o) e1 e2 infLib,
    safe_library lib
    -> similar_cs_names n1 n2
    -> lib_extends lib' lib
    -> entry_in_inf_library_default (lib_cs n2 e1) infLib
    -> inf_lib_extends infLib (rename_cs_lib lib n1 n2)
    -> inf_lib_extends
         (cons_inf_lib_entry
            (library_entry2inf (lib_cs n1 e1))
            (cons_inf_lib_entry
               (library_entry2inf (lib_cs n2 e2))
               infLib))
         lib'
    -> inf_lib_extends infLib (rename_cs_lib lib' n1 n2).
Proof.
  introv safeL sim exta inInf extb extc.
  destruct extb as [extb safeb].
  destruct extc as [extc safec].
  autodimp safeb hyp; eauto 3 with slow;[].
  split; tcsp;[].

  introv i.
  destruct entry.
  { destruct (choice_sequence_name_deq name n1); subst.
    { apply entry_not_in_rename_cs_lib in i; tcsp; eauto 3 with slow. }
    destruct (choice_sequence_name_deq name n2); subst.
    { apply entry_in_rename_cs_lib_implies in i.
      apply extc in i; simpl in *.
      repndors; exrepnd.
      { destruct n0; simpl in *; tcsp.
        repndors; repnd; simpl in *; tcsp; GC;
          [|unfold cons_inf_lib_entry in *; simpl in *;
            destruct i1; unfold inf_matching_entries; simpl; auto];[].
        right.
        eauto 3 with slow. }
      { unfold entry_in_inf_library_default in i; simpl in i; repnd.
        pose proof (i0 0) as i0; simpl in i0.
        unfold cons_inf_lib_entry in i0; simpl in i0; destruct i0; tcsp. } }
    apply if_diff_entry_in_rename_cs_lib in i; auto.
    apply extc in i; simpl in *.
    repndors; exrepnd.
    { apply diff_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0; tcsp.
      apply diff_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0; tcsp.
      left; eauto. }
    { apply entry_in_inf_library_default_cons_inf_lib_entry_implies in i.
      apply entry_in_inf_library_default_cons_inf_lib_entry_implies in i; tcsp. } }
  { apply if_abs_entry_in_rename_cs_lib in i.
    apply extc in i.
    repndors; exrepnd.
    { apply abs_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0.
      apply abs_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0.
      left; eauto. }
    { apply abs_entry_not_in_inf_library_default in i; tcsp. } }
Qed.*)

(*Lemma rename_cs_bar_part1 {o} :
  forall {lib} bar1 (bars1 : @BarLibBars o bar1 lib)
         (ext1 : BarLibExt bar1 lib)
         (n1 n2 : choice_sequence_name)
         (sim : similar_cs_names n1 n2)
         (safeL : safe_library lib)
         (infLib : inf_library)
         (n : nat)
         (iext0 : inf_lib_extends_ext_entries_upto infLib (rename_cs_lib lib n1 n2) n)
         (infLibExt : inf_lib_extends infLib (rename_cs_lib lib n1 n2))
         (isafe : safe_inf_library infLib)
         (cond1 : cs_name_in_library n2 (rename_cs_lib lib n1 n2) = true)
         (cond2 : cs_name_in_library n2 lib = true),
  exists lib',
    (exists lib1, bar1 lib1 /\ lib_extends lib' (rename_cs_lib lib1 n1 n2)) /\
    lib_extends lib' (rename_cs_lib lib n1 n2) /\ inf_lib_extends infLib lib'.
Proof.
  introv bars1 ext1 sim safeL iext0 infLibExt isafe cond1 cond2.

  applydup @cs_name_in_library_implies in cond2 as j; exrepnd.
  applydup @cs_name_in_library_implies in cond1 as w; exrepnd.
  applydup @entry_in_rename_cs_lib_implies in w0.
  applydup iext0 in w0.

  repndors.

  { applydup @entry_in_inf_library_extends_implies_exists in w2; exrepnd.
    remember (infLib k) as ie; destruct ie; simpl in *; repnd; subst; tcsp;[].

    assert (entry_in_inf_library (infLib k) infLib) as j.
    { apply implies_entry_in_inf_library.
      introv ltk.
      apply w4 in ltk.
      rewrite <- Heqie.
      unfold inf_matching_entries in ltk; simpl in ltk.
      unfold matching_inf_entries; simpl; auto. }

    remember (cons_inf_lib_entry
                (inf_lib_cs n1 entry)
                (cons_inf_lib_entry
                   (library_entry2inf (lib_cs n2 e))
                   infLib)) as infLib'.

    pose proof (bars1 infLib') as q.
    autodimp q hyp.

    { subst infLib'; split.

      { introv i.
        destruct entry0.

        { dup i as i'.
          eapply two_entry_in_library_implies_or in i';[|exact w1].
          unfold matching_entries in i'; simpl in i'.
          repndors; ginv.

          { left.
            exists 1; simpl.
            left; dands; auto. }

          destruct (choice_sequence_name_deq name n2) as [d2|d2]; subst.

          { left.
            exists 2; simpl.
            right; dands; tcsp.
            left; dands; tcsp.
            pose proof (two_entry_in_library_implies_or
                          (lib_cs n2 entry0)
                          (lib_cs n2 e)
                          lib) as q.
            repeat (autodimp q hyp).
            repndors;[ginv|destruct q; tcsp]; eauto 3 with slow. }

          applydup (@diff_implies_entry_in_rename_cs_lib o n1 n2) in i; auto;[].
          applydup iext0 in i0.
          repndors.

          { left.
            exists (S (S n)).
            simpl.
            right; dands; tcsp. }

          { right.
            simpl; eauto 3 with slow. } }

        { left.
          apply (abs_implies_entry_in_rename_cs_lib n1 n2) in i.
          apply iext0 in i.
          repndors.

          { exists (S (S n)); simpl; tcsp. }

          { apply abs_entry_not_in_inf_library_default in i; tcsp. } } }

      { introv safeLib.
        applydup (@implies_safe_rename_cs_lib o n1 n2) in safeLib; auto.
        repeat apply implies_safe_inf_library_cons_inf_lib_entry; eauto 3 with slow.

        { applydup isafe in j.
          rewrite <- Heqie in j1; eauto 3 with slow. }

        { simpl.
          apply implies_safe_inf_choice_sequence_entry2inf.
          apply safeLib in j0; simpl in j0; auto. } } }

    exrepnd.
    exists (rename_cs_lib lib' n1 n2).
    dands; eauto 3 with slow;[].
    subst.
    eapply implies_inf_lib_extends_rename_cs_lib_prop1; eauto. }

  remember (cons_inf_lib_entry
              (library_entry2inf (lib_cs n1 e0))
              (cons_inf_lib_entry
                 (library_entry2inf (lib_cs n2 e))
                 infLib)) as infLib'.

  pose proof (bars1 infLib') as q.
  autodimp q hyp.

  { subst infLib'; split.

    { introv i.
      destruct entry.

      { destruct (choice_sequence_name_deq name n1) as [d1|d1]; subst.

        { eapply two_entry_in_library_implies_or in i; try exact w1.
          unfold matching_entries in i; simpl in i.
          repndors; tcsp; ginv;[].
          left.
          exists 1; simpl.
          left; dands; auto; eauto 3 with slow. }

        destruct (choice_sequence_name_deq name n2) as [d2|d2]; subst.

        { eapply two_entry_in_library_implies_or in i; try exact j0.
          unfold matching_entries in i; simpl in i.
          repndors; tcsp; ginv;[].
          left.
          exists 2; simpl.
          right; dands; tcsp.
          left; dands; tcsp; eauto 3 with slow. }

        applydup (@diff_implies_entry_in_rename_cs_lib o n1 n2) in i; auto;[].
        applydup iext0 in i0.
        repndors.

        { left.
          exists (S (S n)).
          simpl.
          right; dands; tcsp. }

        { right.
          simpl; eauto 3 with slow. } }

      { left.
        apply (abs_implies_entry_in_rename_cs_lib n1 n2) in i.
        apply iext0 in i.
        repndors.

        { exists (S (S n)); simpl; tcsp. }

        { apply abs_entry_not_in_inf_library_default in i; tcsp. } } }

    { introv safeLib.
      applydup (@implies_safe_rename_cs_lib o n1 n2) in safeLib; auto.
      repeat apply implies_safe_inf_library_cons_inf_lib_entry; simpl; eauto 3 with slow.

      { apply implies_safe_inf_choice_sequence_entry2inf.
        apply safeLib in w1; simpl in w1; auto. }

      { apply implies_safe_inf_choice_sequence_entry2inf.
        apply safeLib in j0; simpl in j0; auto. } } }

  exrepnd.
  exists (rename_cs_lib lib' n1 n2).
  dands; eauto 3 with slow;[].
  subst.
  eapply implies_inf_lib_extends_rename_cs_lib_prop2; eauto.
Qed.*)

Lemma entry_in_library_implies_cs_name_in_library {o} :
  forall name e (lib : @plibrary o),
    entry_in_library (lib_cs name e) lib
    -> cs_name_in_library name lib = true.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  repndors; repnd; subst; tcsp; boolvar; tcsp.
  destruct a; simpl in *; tcsp; boolvar; tcsp.
Qed.
Hint Resolve entry_in_library_implies_cs_name_in_library : slow.

(*Lemma diff_implies_entry_in_inf_library_default_cons_one {o} :
  forall n e n1 e1 (infLib : @inf_library o),
    n <> n1
    -> entry_in_inf_library_default (lib_cs n e) infLib
    -> entry_in_inf_library_default
         (lib_cs n e)
         (cons_inf_lib_entry (inf_lib_cs n1 e1) infLib).
Proof.
  introv d1 i.
  unfold entry_in_inf_library_default in *; repnd.
  dands; eauto 3 with slow.
  introv x.
  unfold inf_matching_entries in x; simpl in x.
  unfold cons_inf_lib_entry in x; simpl in x.
  boolvar; subst; simpl in *; subst; tcsp.
Qed.
Hint Resolve diff_implies_entry_in_inf_library_default_cons_one : slow.*)

(*Lemma implies_inf_lib_extends_rename_cs_lib_prop3 {o} :
  forall n1 n2 (lib' lib : @library o) e1 infLib k,
    safe_library lib
    -> similar_cs_names n1 n2
    -> lib_extends lib' lib
    -> inf_lib_cs n2 e1 = infLib k
    -> (forall j x, j < k -> ~ inf_matching_entries (infLib j) (lib_cs n2 x))
    -> inf_lib_extends infLib (rename_cs_lib lib n1 n2)
    -> inf_lib_extends (cons_inf_lib_entry (inf_lib_cs n1 e1) infLib) lib'
    -> inf_lib_extends infLib (rename_cs_lib lib' n1 n2).
Proof.
  introv safeL sim exta inInf nm extb extc.
  destruct extb as [extb safeb].
  destruct extc as [extc safec].
  autodimp safeb hyp; eauto 3 with slow;[].
  split; tcsp;[].

  introv i.
  destruct entry.
  { destruct (choice_sequence_name_deq name n1); subst.
    { apply entry_not_in_rename_cs_lib in i; tcsp; eauto 3 with slow. }
    destruct (choice_sequence_name_deq name n2); subst.
    { apply entry_in_rename_cs_lib_implies in i.
      apply extc in i; simpl in *.
      repndors; exrepnd.
      { destruct n0; simpl in *; tcsp.
        repndors; repnd; simpl in *; tcsp; GC;
          [|unfold cons_inf_lib_entry in *; simpl in *;
            destruct i1; unfold inf_matching_entries; simpl; auto];[].
        left.
        exists (S k).
        apply (inf_entry_extends_implies_entry_in_inf_library_extends_same_names
                 _ _ (lib_cs n2 entry)); simpl; tcsp.
        { rewrite <- inInf; simpl; tcsp. }
        introv ltk; apply nm; tcsp. }
      { unfold entry_in_inf_library_default in i; simpl in i; repnd.
        pose proof (i0 0) as i0; simpl in i0.
        unfold cons_inf_lib_entry in i0; simpl in i0; destruct i0; tcsp. } }
    apply if_diff_entry_in_rename_cs_lib in i; auto.
    apply extc in i; simpl in *.
    repndors; exrepnd.
    { apply diff_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0; tcsp.
      left; eauto. }
    { apply entry_in_inf_library_default_cons_inf_lib_entry_implies in i; tcsp. } }
  { apply if_abs_entry_in_rename_cs_lib in i.
    apply extc in i.
    repndors; exrepnd.
    { apply abs_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0.
      left; eauto. }
    { apply abs_entry_not_in_inf_library_default in i; tcsp. } }
Qed.*)

(*Lemma implies_inf_lib_extends_rename_cs_lib_prop4 {o} :
  forall n1 n2 (lib' lib : @library o) e1 infLib,
    safe_library lib
    -> similar_cs_names n1 n2
    -> lib_extends lib' lib
    -> entry_in_inf_library_default (lib_cs n2 e1) infLib
    -> inf_lib_extends infLib (rename_cs_lib lib n1 n2)
    -> inf_lib_extends (cons_inf_lib_entry (library_entry2inf (lib_cs n1 e1)) infLib) lib'
    -> inf_lib_extends infLib (rename_cs_lib lib' n1 n2).
Proof.
  introv safeL sim exta inInf extb extc.
  destruct extb as [extb safeb].
  destruct extc as [extc safec].
  autodimp safeb hyp; eauto 3 with slow;[].
  split; tcsp;[].

  introv i.
  destruct entry.
  { destruct (choice_sequence_name_deq name n1); subst.
    { apply entry_not_in_rename_cs_lib in i; tcsp; eauto 3 with slow. }
    destruct (choice_sequence_name_deq name n2); subst.
    { apply entry_in_rename_cs_lib_implies in i.
      apply extc in i; simpl in *.
      repndors; exrepnd.
      { destruct n0; simpl in *; tcsp.
        repndors; repnd; simpl in *; tcsp; GC;
          [|unfold cons_inf_lib_entry in *; simpl in *;
            destruct i1; unfold inf_matching_entries; simpl; auto];[].
        right.
        eauto 3 with slow. }
      { unfold entry_in_inf_library_default in i; simpl in i; repnd.
        pose proof (i0 0) as i0; simpl in i0.
        unfold cons_inf_lib_entry in i0; simpl in i0; destruct i0; tcsp. } }
    apply if_diff_entry_in_rename_cs_lib in i; auto.
    apply extc in i; simpl in *.
    repndors; exrepnd.
    { apply diff_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0; tcsp.
      left; eauto. }
    { apply entry_in_inf_library_default_cons_inf_lib_entry_implies in i; tcsp. } }
  { apply if_abs_entry_in_rename_cs_lib in i.
    apply extc in i.
    repndors; exrepnd.
    { apply abs_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0.
      left; eauto. }
    { apply abs_entry_not_in_inf_library_default in i; tcsp. } }
Qed.*)

(*Lemma rename_cs_bar_part2 {o} :
  forall {lib} bar1 (bars1 : @BarLibBars o bar1 lib)
         (ext1 : BarLibExt bar1 lib)
         (n1 n2 : choice_sequence_name)
         (sim : similar_cs_names n1 n2)
         (safeL : safe_library lib)
         (infLib : inf_library)
         (n : nat)
         (iext0 : inf_lib_extends_ext_entries_upto infLib (rename_cs_lib lib n1 n2) n)
         (infLibExt : inf_lib_extends infLib (rename_cs_lib lib n1 n2))
         (isafe : safe_inf_library infLib)
         (cond1 : cs_name_in_library n2 (rename_cs_lib lib n1 n2) = true)
         (cond2 : cs_name_in_library n2 lib = false),
  exists lib',
    (exists lib1, bar1 lib1 /\ lib_extends lib' (rename_cs_lib lib1 n1 n2)) /\
    lib_extends lib' (rename_cs_lib lib n1 n2) /\ inf_lib_extends infLib lib'.
Proof.
  introv bars1 ext1 sim safeL iext0 infLibExt isafe cond1 cond2.

  (*applydup @cs_name_in_library_implies in cond2 as j; exrepnd.*)
  applydup @cs_name_in_library_implies in cond1 as w; exrepnd.
  applydup @entry_in_rename_cs_lib_implies in w0.
  applydup iext0 in w0.

  repndors.

  { applydup @entry_in_inf_library_extends_implies_exists in w2; exrepnd.
    remember (infLib k) as ie; destruct ie; simpl in *; repnd; subst; tcsp;[].

    assert (entry_in_inf_library (infLib k) infLib) as j.
    { apply implies_entry_in_inf_library.
      introv ltk.
      apply w4 in ltk.
      rewrite <- Heqie.
      unfold inf_matching_entries in ltk; simpl in ltk.
      unfold matching_inf_entries; simpl; auto. }

    remember (cons_inf_lib_entry
                (inf_lib_cs n1 entry)
                infLib) as infLib'.

    pose proof (bars1 infLib') as q.
    autodimp q hyp.

    { subst infLib'; split.

      { introv i.
        destruct entry0.

        { dup i as i'.
          eapply two_entry_in_library_implies_or in i';[|exact w1].
          unfold matching_entries in i'; simpl in i'.
          repndors; ginv.

          { left.
            exists 1; simpl.
            left; dands; auto. }

          destruct (choice_sequence_name_deq name n2) as [d2|d2]; subst.

          { apply entry_in_library_implies_cs_name_in_library in i.
            rewrite cond2 in i; ginv. }

          applydup (@diff_implies_entry_in_rename_cs_lib o n1 n2) in i; auto;[].
          applydup iext0 in i0.
          repndors.

          { left.
            exists (S n).
            simpl.
            right; dands; tcsp. }

          { right.
            simpl; eauto 3 with slow. } }

        { left.
          apply (abs_implies_entry_in_rename_cs_lib n1 n2) in i.
          apply iext0 in i.
          repndors.

          { exists (S n); simpl; tcsp. }

          { apply abs_entry_not_in_inf_library_default in i; tcsp. } } }

      { introv safeLib.
        applydup (@implies_safe_rename_cs_lib o n1 n2) in safeLib; auto.
        repeat apply implies_safe_inf_library_cons_inf_lib_entry; eauto 3 with slow;[].
        applydup isafe in j.
        rewrite <- Heqie in j0; eauto 3 with slow. } }

    exrepnd.
    exists (rename_cs_lib lib' n1 n2).
    dands; eauto 3 with slow;[].
    subst.
    eapply implies_inf_lib_extends_rename_cs_lib_prop3; eauto. }

  remember (cons_inf_lib_entry
              (library_entry2inf (lib_cs n1 e))
              infLib) as infLib'.

  pose proof (bars1 infLib') as q.
  autodimp q hyp.

  { subst infLib'; split.

    { introv i.
      destruct entry.

      { destruct (choice_sequence_name_deq name n1) as [d1|d1]; subst.

        { eapply two_entry_in_library_implies_or in i; try exact w1.
          unfold matching_entries in i; simpl in i.
          repndors; tcsp; ginv;[].
          left.
          exists 1; simpl.
          left; dands; auto; eauto 3 with slow. }

        destruct (choice_sequence_name_deq name n2) as [d2|d2]; subst.

        { apply entry_in_library_implies_cs_name_in_library in i.
          rewrite cond2 in i; ginv. }

        applydup (@diff_implies_entry_in_rename_cs_lib o n1 n2) in i; auto;[].
        applydup iext0 in i0.
        repndors.

        { left.
          exists (S n).
          simpl.
          right; dands; tcsp. }

        { right.
          simpl; eauto 3 with slow. } }

      { left.
        apply (abs_implies_entry_in_rename_cs_lib n1 n2) in i.
        apply iext0 in i.
        repndors.

        { exists (S n); simpl; tcsp. }

        { apply abs_entry_not_in_inf_library_default in i; tcsp. } } }

    { introv safeLib.
      applydup (@implies_safe_rename_cs_lib o n1 n2) in safeLib; auto.
      repeat apply implies_safe_inf_library_cons_inf_lib_entry; simpl; eauto 3 with slow;[].
      apply implies_safe_inf_choice_sequence_entry2inf.
      apply safeLib in w1; simpl in w1; auto. } }

  exrepnd.
  exists (rename_cs_lib lib' n1 n2).
  dands; eauto 3 with slow;[].
  subst.
  eapply implies_inf_lib_extends_rename_cs_lib_prop4; eauto.
Qed.*)

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
  forall name entry (lib : @plibrary o),
    entry_in_library entry (keep_only_pre name lib)
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
  forall name entry (lib : @plibrary o),
    entry_in_library_extends entry lib
    -> same_entry_name (entry2name entry) (entry_name_cs name)
    -> entry_in_library_extends entry (keep_only_pre name lib).
Proof.
  induction lib; introv i same; simpl in *; tcsp.
  repndors; repnd; tcsp.

  { clear IHlib.
    destruct entry; simpl in *; subst; tcsp;[].
    inversion i; subst; simpl in *; tcsp; boolvar; subst; tcsp. }

  { applydup IHlib in i; auto; clear IHlib.
    destruct a; simpl in *; tcsp.
    boolvar; subst; tcsp. }
Qed.
Hint Resolve implies_entry_in_library_extends_keep_only : slow.

Lemma implies_lib_extends_entries_keep_only {o} :
  forall name (lib1 lib2 : @plibrary o),
    lib_extends_entries lib1 lib2
    -> lib_extends_entries (keep_only_pre name lib1) (keep_only_pre name lib2).
Proof.
  introv ext i.
  applydup @entry_in_library_keep_only in i; repnd.
  apply ext in i1; eauto 3 with slow.
Qed.
Hint Resolve implies_lib_extends_entries_keep_only : slow.

Lemma implies_safe_library_keep_only_pre {o} :
  forall name (lib : @plibrary o),
    safe_library lib
    -> safe_library (keep_only_pre name lib).
Proof.
  introv safe i.
  apply entry_in_library_keep_only in i; repnd.
  apply safe in i0; auto.
Qed.
Hint Resolve implies_safe_library_keep_only_pre : slow.

Lemma implies_safe_library_keep_only {o} :
  forall name (lib : @library o),
    safe_library lib
    -> safe_library (keep_only name lib).
Proof.
  introv safe i.
  eapply implies_safe_library_keep_only_pre; simpl in *; eauto.
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
  forall name entry (lib : @plibrary o),
    List.In entry (keep_only_pre name lib)
    -> List.In entry lib
       /\ same_entry_name (entry2name entry) (entry_name_cs name).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; subst; simpl in *; repndors; subst; tcsp.
Qed.

Lemma lin_library_keep_only {o} :
  forall name entry (lib : @plibrary o),
    LIn entry (keep_only_pre name lib)
    -> LIn entry lib
           # same_entry_name (entry2name entry) (entry_name_cs name).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; subst; simpl in *; repndors; subst; tcsp.
Qed.

Lemma in_library_keep_only_implies_entry_in_library {o} :
  forall name entry (lib : @plibrary o),
    List.In entry (keep_only_pre name lib)
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
  forall name (lib1 lib2 : @plibrary o),
    lib_extends_entries lib1 lib2
    -> subset_library (keep_only_pre name lib2) (keep_only_pre name lib1).
Proof.
  introv ext i.
  apply in_library_keep_only_implies_entry_in_library in i; repnd.
  apply ext in i0.
  apply (implies_entry_in_library_extends_keep_only name) in i0; auto.
  apply entry_in_library_extends_implies_entry_in_library in i0; exrepnd.
  exists entry'; dands; eauto 3 with slow.
Qed.
Hint Resolve implies_subset_library_keep_only : slow.

Lemma keep_only_pre_nil {o} :
  forall name (lib : @plibrary o),
    ~in_lib (entry_name_cs name) lib
    -> keep_only_pre name lib = [].
Proof.
  induction lib; introv i; simpl in *; tcsp.
  rewrite in_lib_cons in i.
  destruct a; simpl in *; boolvar; subst; repndors; subst; tcsp; GC.
  destruct i; tcsp.
Qed.

Definition lib2em {o} (lib : @library o) := MkLib [] (lib_cond lib).

Lemma keep_only_nil {o} :
  forall name (lib : @library o),
    ~in_lib (entry_name_cs name) lib
    -> keep_only name lib = lib2em lib.
Proof.
  introv h; destruct lib as [lib cond]; simpl in *.
  unfold keep_only; simpl.
  rewrite keep_only_pre_nil; auto.
Qed.

Lemma add_choice_keep_only_name_same {o} :
  forall name v (lib : @plibrary o) n restr lib',
    add_choice name v lib = Some (n, restr, lib')
    -> add_choice name v (keep_only_pre name lib) = Some (n, restr, keep_only_pre name lib').
Proof.
  induction lib; introv addc; simpl in *; ginv.
  destruct a; tcsp.

  { destruct entry as [vals restr']; boolvar; subst; tcsp.

    { inversion addc; subst; clear addc; simpl in *; boolvar; tcsp; GC. }

    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; ginv.
    inversion addc; subst; clear addc; simpl in *; tcsp; boolvar; tcsp. }

  { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; ginv.
    inversion addc; subst; clear addc; simpl in *; tcsp; boolvar; tcsp. }
Qed.

Lemma add_one_choice_keep_only_name_same {o} :
  forall name v (lib : @library o) n restr lib',
    add_one_choice name v lib = Some (n, restr, lib')
    -> add_one_choice name v (keep_only name lib) = Some (n, restr, keep_only name lib').
Proof.
  introv h.
  destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv.
  erewrite add_choice_keep_only_name_same; eauto; tcsp.
Qed.

Lemma add_choice_keep_only_name_diff {o} :
  forall name name' v (lib : @plibrary o) n restr lib',
    name' <> name
    -> add_choice name v lib = Some (n, restr, lib')
    -> keep_only_pre name' lib' = keep_only_pre name' lib.
Proof.
  induction lib; introv diff addc; simpl in *; ginv.
  destruct a; tcsp.

  { destruct entry as [vals restr']; boolvar; subst; tcsp.

    { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
      destruct addc'; repnd; ginv.
      inversion addc; subst; clear addc; simpl in *; tcsp; boolvar; tcsp. }

    { inversion addc; subst; clear addc; simpl in *; boolvar; tcsp; GC. }

    { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
      destruct addc'; repnd; ginv.
      inversion addc; subst; clear addc; simpl in *; tcsp; boolvar; tcsp.
      eapply IHlib; eauto. } }

  { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; ginv.
    inversion addc; subst; clear addc; simpl in *; tcsp; boolvar; tcsp.
    eapply IHlib; eauto. }
Qed.

Lemma add_one_choice_keep_only_name_diff {o} :
  forall name name' v (lib : @library o) n restr lib',
    name' <> name
    -> add_one_choice name v lib = Some (n, restr, lib')
    -> keep_only name' lib' = keep_only name' lib.
Proof.
  introv d h; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv.
  unfold keep_only; simpl; f_equal.
  eapply add_choice_keep_only_name_diff in Heqaddc; eauto.
Qed.

Lemma keep_only_add_new_cs {o} :
  forall name name' restr (lib : @library o),
    keep_only name (add_new_cs name' restr lib)
    = if choice_sequence_name_deq name name'
      then add_new_cs name' restr (lib2em lib)
      else keep_only name lib.
Proof.
  introv; tcsp.
  unfold keep_only, add_new_cs; simpl; boolvar; subst; tcsp.
Qed.

Lemma implies_lib_extends_keep_only {o} :
  forall name (lib1 lib2 : @library o),
    safe_library lib2
    -> lib_extends lib1 lib2
    -> lib_extends (keep_only name lib1) (keep_only name lib2).
Proof.
  introv safe ext.
  lib_ext_ind ext Case.

  { Case "lib_ext_trans".
    autodimp IHext1 hyp; eauto 3 with slow. }

  { Case "lib_ext_new_cs".
    rewrite keep_only_add_new_cs.
    boolvar; subst; tcsp.
    rewrite keep_only_nil; tcsp.
    apply lib_extends_new_cs; eauto 3 with slow. }

  { Case "lib_ext_cs".
    destruct (choice_sequence_name_deq name0 name); subst.
    { apply add_one_choice_keep_only_name_same in addc; eauto. }
    { apply (add_one_choice_keep_only_name_diff _ name) in addc; auto; allrw; eauto 3 with slow. } }
Qed.
Hint Resolve implies_lib_extends_keep_only : slow.

Lemma implies_entry_in_library_keep_only {o} :
  forall name entry (lib : @plibrary o),
    entry_in_library entry lib
    -> same_entry_name (entry2name entry) (entry_name_cs name)
    -> entry_in_library entry (keep_only_pre name lib).
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
  forall entry (lib1 lib2 : @plibrary o),
    entry_in_library_extends entry lib1
    -> entry_in_library_extends entry (lib1 ++ lib2).
Proof.
  induction lib1; introv h; simpl in *; tcsp.
Qed.
Hint Resolve entry_in_library_extends_app_left : slow.

Lemma entry_in_library_extends_app_right {o} :
  forall entry (lib1 lib2 : @plibrary o),
    entry_in_library_extends entry lib2
    -> (forall e, LIn e lib1 -> ~ matching_entries entry e)
    -> entry_in_library_extends entry (lib1 ++ lib2).
Proof.
  induction lib1; introv i imp; simpl in *; tcsp.
Qed.
Hint Resolve entry_in_library_extends_app_right : slow.

Lemma implies_lib_extends_entries_keep_only_app {o} :
  forall name x (lib : @plibrary o),
    lib_extends_entries x (keep_only_pre name lib)
    -> lib_extends_entries (keep_only_pre name x ++ lib) lib.
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
  forall (lib1 lib2 : @plibrary o),
    safe_library lib1
    -> safe_library lib2
    -> safe_library (lib1 ++ lib2).
Proof.
  introv safe1 safe2 i.
  apply entry_in_library_app_implies in i; repnd; tcsp.
Qed.
Hint Resolve implies_safe_library_app : slow.

Lemma implies_safe_library_keep_only_app_imp {o} :
  forall name x (lib : @plibrary o),
    (safe_library (keep_only_pre name lib) -> safe_library x)
    -> safe_library lib
    -> safe_library (keep_only_pre name x ++ lib).
Proof.
  introv imp safe.
  autodimp imp hyp; eauto 3 with slow.
Qed.
Hint Resolve implies_safe_library_keep_only_app_imp : slow.

Lemma implies_subset_library_keep_only_app {o} :
  forall name x (lib : @plibrary o),
    subset_library (keep_only_pre name lib) x
    -> subset_library lib (keep_only_pre name x ++ lib).
Proof.
  introv ss i.
  exists entry1; dands; eauto 3 with slow.
  apply in_or_app; tcsp.
Qed.
Hint Resolve implies_subset_library_keep_only_app : slow.

(*Lemma implies_lib_extends_keep_only_app {o} :
  forall name x (lib : @library o),
    lib_extends x (keep_only name lib)
    -> lib_extends (keep_only name x ++ lib) lib.
Proof.
  introv ext.

  destruct ext as [ext safe sub].
  split; eauto 3 with slow.
Qed.
Hint Resolve implies_lib_extends_keep_only_app : slow.*)

Fixpoint remove_cs_lib {o} name (lib : @plibrary o) : plibrary :=
  match lib with
  | [] => []
  | lib_cs name' e :: entries =>
    if choice_sequence_name_deq name name'
    then (*lib_cs name (empty_choice_seq_entry e) ::*) remove_cs_lib name entries
    else lib_cs name' e :: remove_cs_lib name entries
  | entry :: entries => entry :: remove_cs_lib name entries
  end.

Lemma find_cs_app_not_right {o} :
  forall name (lib1 lib2 : @plibrary o),
    find_cs lib2 name = None
    -> find_cs (lib1 ++ lib2) name = find_cs lib1 name.
Proof.
  induction lib1; introv fcs; simpl in *; tcsp.
  destruct a; simpl in *; tcsp.
  boolvar; subst; tcsp.
Qed.

Lemma keep_only_pre_idem {o} :
  forall name (lib : @plibrary o),
    keep_only_pre name (keep_only_pre name lib) = keep_only_pre name lib.
Proof.
  induction lib; simpl in *; tcsp.
  destruct a; tcsp; boolvar; subst; tcsp.
  simpl in *; boolvar; tcsp.
Qed.
Hint Rewrite @keep_only_pre_idem : slow.

Lemma keep_only_idem {o} :
  forall name (lib : @library o),
    keep_only name (keep_only name lib) = keep_only name lib.
Proof.
  introv; destruct lib as [lib cond]; unfold keep_only; simpl.
  autorewrite with slow; auto.
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

(*Lemma in_ext_ext_per_choice2 {o} :
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
Qed.*)

(*Lemma in_ext_ext_per_choice3 {o} :
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
Qed.*)

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

(*Lemma find_cs_implies_lib_extends_singleton_right {o} :
  forall name e (lib : @library o),
    safe_library lib
    -> find_cs lib name = Some e
    -> lib_extends lib [lib_cs name e].
Proof.
  introv safe fcs.
  split; eauto 3 with slow.
Qed.
Hint Resolve find_cs_implies_lib_extends_singleton_right : slow.*)

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

(*Definition inf_lib_cons_lib {o}
           (e : @inf_library_entry o)
           (lib : library) : inf_library :=
  fun n =>
    if deq_nat n 0 then e
    else library2inf lib e (pred n).*)


(*
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
*)

(*Lemma shift_inf_lib_inf_lib_cons_lib {o} :
  forall e (lib : @library o),
    shift_inf_lib (inf_lib_cons_lib e lib)
    = library2inf lib e.
Proof.
  introv; apply functional_extensionality; introv; simpl.
  unfold shift_inf_lib; simpl.
  unfold inf_lib_cons_lib; simpl; auto.
Qed.
Hint Rewrite @shift_inf_lib_inf_lib_cons_lib : slow.*)

(*Lemma implies_entry_in_inf_library_extends_inf_lib_cons_lib {o} :
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
Qed.*)

(*Lemma inf_lib_extends_ext_entries_inf_lib_cons_lib {o} :
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
Hint Resolve inf_lib_extends_ext_entries_inf_lib_cons_lib : slow.*)

(*Lemma entry_in_inf_library_inf_lib_cons_lib_implies {o} :
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
Qed.*)

(*Lemma matching_inf_entries_implies_matching_entries {o} :
  forall (e1 e2 : @library_entry o),
    matching_inf_entries (library_entry2inf e1) (library_entry2inf e2)
    -> matching_entries e1 e2.
Proof.
  introv m.
  destruct e1, e2; simpl in *; tcsp.
Qed.
Hint Resolve matching_inf_entries_implies_matching_entries : slow.*)

(*Lemma implies_entry_in_lib_library_library_entry2inf {o} :
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
Hint Resolve implies_entry_in_lib_library_library_entry2inf : slow.*)

(*Lemma implies_safe_inf_library_inf_lib_cons_lib {o} :
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
Hint Resolve implies_safe_inf_library_inf_lib_cons_lib : slow.*)

(*Lemma inf_lib_extends_inf_lib_cons_lib {o} :
  forall name (lib : @library o) c e,
    find_cs lib name = Some c
    -> inf_entry_extends e (lib_cs name c)
    -> safe_inf_library_entry e
    -> inf_lib_extends (inf_lib_cons_lib e lib) lib.
Proof.
  introv fd h safe.
  split; eauto 3 with slow.
Qed.
Hint Resolve inf_lib_extends_inf_lib_cons_lib : slow.*)

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

(*Lemma cs_name_in_library_rename_cs_lib_false_implies {o} :
  forall n1 n2 (lib : @plibrary o),
    cs_name_in_library n2 (rename_cs_lib lib n1 n2) = false
    -> cs_name_in_library n1 lib = false.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; GC; tcsp;
    simpl in *; boolvar; subst; tcsp.
Qed.*)

(*
(* We assume that [n1] and [n2] have the same space but different names *)
Definition rename_cs_bar
           {o} {lib}
           (bar   : @BarLib o lib)
           (n1 n2 : choice_sequence_name)
           (sim   : similar_cs_names n1 n2)
           (* it's easier and shouldn't be too constraining *)
           (csin  : cs_name_in_library n1 lib = true)
           (safeL : safe_library lib) : BarLib (rename_cs_lib lib n1 n2).
Proof.
  exists (fun (lib' : library) =>
            exists lib1,
              bar_lib_bar bar lib1
              /\ lib_extends lib' (rename_cs_lib lib1 n1 n2)).

  - introv e.
    destruct bar as [bar1 bars1 ext1]; simpl in *.
    dup e as infLibExt.
    destruct e as [iext isafe].
    autodimp isafe hyp; eauto 3 with slow;[].

    apply inf_lib_extends_ext_entries_implies in iext; exrepnd.

    (* If [n2] is in [rename_cs_lib lib n1 n2], then we might have to update
           [infLib] to obtain an infinite library that covers [lib] instead of
           [rename_cs_lib lib n1 n2], because [lib] might already contain an entry
           for [n2].  In the case where [n2] is in [rename_cs_lib lib n1 n2], then
           we get to know that [n1] is in [lib] (but not in [rename_cs_lib lib n1 n2]
           anymore).
     *)
    remember (cs_name_in_library n2 (rename_cs_lib lib n1 n2)) as b1; symmetry in Heqb1.
    destruct b1;[|].

    { (* if [n2] is in [lib] then we definitely have to rename the entry in [infLib]
             that covers [rename_cs_lib lib n1 n2], to cover [lib] instead
       *)
      remember (cs_name_in_library n2 lib) as b2; symmetry in Heqb2.
      destruct b2;[|].

      { eapply rename_cs_bar_part1; eauto. }

      { eapply rename_cs_bar_part2; eauto. } }

    { (* [n2] is not in [rename_cs_lib lib n1 n2], which means that [n1] is not
             is [lib], which meant that [rename_cs_lib lib n1 n2] is [lib], where
             all the entries for [n2] are removed *)

      applydup @cs_name_in_library_rename_cs_lib_false_implies in Heqb1.
      rewrite csin in Heqb0; ginv. }

  - introv h.
    exrepnd.
    eapply lib_extends_trans;[eauto|].
    eauto 3 with slow.
Defined.
*)

(*
Lemma entry_in_library_extends_implies_cs_name_in_library {o} :
  forall name e (lib : @library o),
    entry_in_library_extends (lib_cs name e) lib
    -> cs_name_in_library name lib = true.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  repndors; repnd; subst; tcsp; boolvar; tcsp;
    destruct a; simpl in *; tcsp; boolvar; tcsp; ginv.
Qed.
Hint Resolve entry_in_library_extends_implies_cs_name_in_library : slow.*)

(*Lemma lib_extends_preserves_cs_name_in_library {o} :
  forall name (lib1 lib2 : @library o),
    lib_extends lib2 lib1
    -> cs_name_in_library name lib1 = true
    -> cs_name_in_library name lib2 = true.
Proof.
  introv ext inlib.
  apply cs_name_in_library_implies in inlib; exrepnd.
  apply ext in inlib0; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_cs_name_in_library : slow.*)

(* [sw_cs_lib] swaps [n1] and [n2] *)
Fixpoint sw_cs_lib {o}
         (lib : @plibrary o)
         (n1 n2 : choice_sequence_name) : plibrary :=
  match lib with
  | [] => []
  | lib_cs name e as entry :: lib =>
    if choice_sequence_name_deq name n1
    then lib_cs n2 e :: sw_cs_lib lib n1 n2
    else if choice_sequence_name_deq name n2
         then lib_cs n1 e :: sw_cs_lib lib n1 n2
         else entry :: sw_cs_lib lib n1 n2
  | lib_abs _ _ _ _ as entry :: lib => entry :: sw_cs_lib lib n1 n2
  end.

Lemma entry_in_sw_cs_lib {o} :
  forall entry n1 n2 (lib : @plibrary o),
    entry_in_library entry (sw_cs_lib lib n1 n2)
    ->
    (exists e,
        entry = lib_cs n1 e /\ entry_in_library (lib_cs n2 e) lib)
    \/ (exists e,
           entry = lib_cs n2 e /\ entry_in_library (lib_cs n1 e) lib)
    \/ (exists n e,
           entry = lib_cs n e /\ n <> n1 /\ n <> n2 /\ entry_in_library entry lib)
    \/ (exists abs vars rhs cor,
           entry = lib_abs abs vars rhs cor /\ entry_in_library entry lib).
Proof.
  induction lib; introv h; simpl in *; tcsp;[].
  destruct a; simpl in ; tcsp; boolvar; subst; simpl in *; tcsp;
    repndors; repnd; subst; simpl in *; tcsp.
  { right; left.
    exists entry0; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp.
      right; dands; tcsp.
      unfold matching_entries in *; simpl in *; tcsp. }
    { right; left.
      exists e; dands; tcsp.
      unfold matching_entries in *; simpl in *; tcsp. }
    { right; right; left.
      exists n e; dands; tcsp. }
    { right; right; right.
      exists abs vars rhs cor; dands; tcsp. } }
  { left.
    exists entry0; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp.
      right; dands; tcsp.
      unfold matching_entries in *; simpl in *; tcsp. }
    { right; left.
      exists e; dands; tcsp. }
    { right; right; left.
      exists n0 e; dands; tcsp. }
    { right; right; right.
      exists abs vars rhs cor; dands; tcsp. } }
  { right; right; left.
    exists name entry0; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp. }
    { right; left.
      exists e; dands; tcsp. }
    { right; right; left.
      exists n3 e; dands; tcsp. }
    { right; right; right.
      exists abs vars rhs cor; dands; tcsp. } }
  { right; right; right.
    exists opabs vars rhs correct; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp. }
    { right; left.
      exists e; dands; tcsp. }
    { right; right; left.
      exists n e; dands; tcsp. }
    { right; right; right.
      exists abs vars0 rhs0 cor; dands; tcsp. } }
Qed.

Lemma if_in_sw_cs_lib {o} :
  forall entry n1 n2 (lib : @plibrary o),
    entry_in_library entry lib
    ->
    (exists e,
        entry = lib_cs n1 e /\ entry_in_library (lib_cs n2 e) (sw_cs_lib lib n1 n2))
    \/ (exists e,
           entry = lib_cs n2 e /\ entry_in_library (lib_cs n1 e) (sw_cs_lib lib n1 n2))
    \/ (exists n e,
           entry = lib_cs n e /\ n <> n1 /\ n <> n2 /\ entry_in_library entry (sw_cs_lib lib n1 n2))
    \/ (exists abs vars rhs cor,
           entry = lib_abs abs vars rhs cor /\ entry_in_library entry (sw_cs_lib lib n1 n2)).
Proof.
  induction lib; introv h; simpl in *; tcsp;[].
  destruct a; simpl in ; tcsp; boolvar; subst; simpl in *; tcsp;
    repndors; repnd; subst; simpl in *; tcsp.
  { left.
    exists entry0; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp.
      right; dands; tcsp.
      unfold matching_entries in *; simpl in *; tcsp. }
    { right; left.
      exists e; dands; tcsp.
      unfold matching_entries in *; simpl in *; tcsp. }
    { right; right; left.
      exists n e; dands; tcsp. }
    { right; right; right.
      exists abs vars rhs cor; dands; tcsp. } }
  { right; left.
    exists entry0; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp. }
    { right; left.
      exists e; dands; tcsp.
      right; dands; tcsp.
      unfold matching_entries in *; simpl in *; tcsp. }
    { right; right; left.
      exists n0 e; dands; tcsp. }
    { right; right; right.
      exists abs vars rhs cor; dands; tcsp. } }
  { right; right; left.
    exists name entry0; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp. }
    { right; left.
      exists e; dands; tcsp. }
    { right; right; left.
      exists n3 e; dands; tcsp. }
    { right; right; right.
      exists abs vars rhs cor; dands; tcsp. } }
  { right; right; right.
    exists opabs vars rhs correct; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp. }
    { right; left.
      exists e; dands; tcsp. }
    { right; right; left.
      exists n e; dands; tcsp. }
    { right; right; right.
      exists abs vars0 rhs0 cor; dands; tcsp. } }
Qed.

Lemma implies_safe_sw_cs_lib {o} :
  forall n1 n2 (lib : @library o),
    similar_cs_names n1 n2
    -> safe_library lib
    -> safe_library (sw_cs_lib lib n1 n2).
Proof.
  introv sim safe i.
  apply entry_in_sw_cs_lib in i.
  repndors; exrepnd; subst; auto;[|];
    apply safe in i0; eauto 3 with slow.
Qed.
Hint Resolve implies_safe_sw_cs_lib : slow.

Lemma if_safe_sw_cs_lib {o} :
  forall n1 n2 (lib : @library o),
    similar_cs_names n1 n2
    -> safe_library (sw_cs_lib lib n1 n2)
    -> safe_library lib.
Proof.
  introv sim safe i.
  apply (if_in_sw_cs_lib entry n1 n2) in i.
  repndors; exrepnd; subst; auto;[|];
    apply safe in i0; eauto 3 with slow.
Qed.
Hint Resolve if_safe_sw_cs_lib : slow.

Lemma entry_in_library_implies_in_sw_cs_lib1 {o} :
  forall n1 n2 e (lib : @plibrary o),
    entry_in_library (lib_cs n1 e) lib
    -> entry_in_library (lib_cs n2 e) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp.
  apply IHlib in h; tcsp.
  right; dands; auto.
  unfold matching_entries in *; simpl in *; tcsp.
Qed.
Hint Resolve entry_in_library_implies_in_sw_cs_lib1 : slow.

Lemma entry_in_library_implies_in_sw_cs_lib2 {o} :
  forall n1 n2 e (lib : @plibrary o),
    entry_in_library (lib_cs n2 e) lib
    -> entry_in_library (lib_cs n1 e) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp.
  { apply IHlib in h; tcsp.
    right; dands; auto.
    unfold matching_entries in *; simpl in *; tcsp. }
  { apply IHlib in h; tcsp.
    right; dands; auto.
    unfold matching_entries in *; simpl in *; tcsp. }
Qed.
Hint Resolve entry_in_library_implies_in_sw_cs_lib2 : slow.

Lemma entry_in_library_implies_in_sw_cs_lib3 {o} :
  forall n n1 n2 e (lib : @plibrary o),
    n <> n1
    -> n <> n2
    -> entry_in_library (lib_cs n e) lib
    -> entry_in_library (lib_cs n e) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv d1 d2 h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp.
Qed.
Hint Resolve entry_in_library_implies_in_sw_cs_lib3 : slow.

Lemma entry_in_library_implies_in_sw_cs_lib4 {o} :
  forall n1 n2 abs vars rhs cor (lib : @plibrary o),
    entry_in_library (lib_abs abs vars rhs cor) lib
    -> entry_in_library (lib_abs abs vars rhs cor) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp.
Qed.
Hint Resolve entry_in_library_implies_in_sw_cs_lib4 : slow.

(*Lemma entry_in_library_extends_implies_in_sw_cs_lib1 {o} :
  forall n1 n2 e (lib : @library o),
    entry_in_library_extends (lib_cs n1 e) lib
    -> entry_in_library_extends (lib_cs n2 e) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp;
      destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp; ginv.
  apply IHlib in h; tcsp.
  right; dands; auto.
  unfold matching_entries in *; simpl in *; tcsp.
Qed.
Hint Resolve entry_in_library_extends_implies_in_sw_cs_lib1 : slow.*)

(*Lemma entry_in_library_extends_implies_in_sw_cs_lib2 {o} :
  forall n1 n2 e (lib : @library o),
    entry_in_library_extends (lib_cs n2 e) lib
    -> entry_in_library_extends (lib_cs n1 e) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp;
      destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp; ginv.
  { apply IHlib in h; tcsp.
    right; dands; auto.
    unfold matching_entries in *; simpl in *; tcsp. }
  { apply IHlib in h; tcsp.
    right; dands; auto.
    unfold matching_entries in *; simpl in *; tcsp. }
Qed.
Hint Resolve entry_in_library_extends_implies_in_sw_cs_lib2 : slow.*)

(*Lemma entry_in_library_extends_implies_in_sw_cs_lib3 {o} :
  forall n n1 n2 e (lib : @library o),
    n <> n1
    -> n <> n2
    -> entry_in_library_extends (lib_cs n e) lib
    -> entry_in_library_extends (lib_cs n e) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv d1 d2 h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp;
      destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp.
Qed.
Hint Resolve entry_in_library_extends_implies_in_sw_cs_lib3 : slow.*)

(*Lemma entry_in_library_extends_implies_in_sw_cs_lib4 {o} :
  forall n1 n2 abs vars rhs cor (lib : @library o),
    entry_in_library_extends (lib_abs abs vars rhs cor) lib
    -> entry_in_library_extends (lib_abs abs vars rhs cor) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp;
      destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp; ginv.
Qed.
Hint Resolve entry_in_library_extends_implies_in_sw_cs_lib4 : slow.*)

(*Lemma sw_cs_lib_preserves_lib_extends_entries {o} :
  forall n1 n2 (lib1 lib2 : @library o),
    lib_extends_entries lib2 lib1
    -> lib_extends_entries (sw_cs_lib lib2 n1 n2) (sw_cs_lib lib1 n1 n2).
Proof.
  introv ext i.
  apply entry_in_sw_cs_lib in i; repndors; exrepnd; subst; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve sw_cs_lib_preserves_lib_extends_entries : slow.*)

Lemma in_sw_cs_lib {o} :
  forall entry n1 n2 (lib : @plibrary o),
    List.In entry (sw_cs_lib lib n1 n2)
    ->
    (exists e,
        entry = lib_cs n1 e /\ List.In (lib_cs n2 e) lib)
    \/ (exists e,
           entry = lib_cs n2 e /\ List.In (lib_cs n1 e) lib)
    \/ (exists n e,
           entry = lib_cs n e /\ n <> n1 /\ n <> n2 /\ List.In entry lib)
    \/ (exists abs vars rhs cor,
           entry = lib_abs abs vars rhs cor /\ List.In entry lib).
Proof.
  induction lib; introv h; simpl in *; tcsp;[].
  destruct a; simpl in ; tcsp; boolvar; subst; simpl in *; tcsp;
    repndors; repnd; subst; simpl in *; tcsp.
  { right; left.
    exists entry0; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp. }
    { right; left.
      exists e; dands; tcsp. }
    { right; right; left.
      exists n e; dands; tcsp. }
    { right; right; right.
      exists abs vars rhs cor; dands; tcsp. } }
  { left.
    exists entry0; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp. }
    { right; left.
      exists e; dands; tcsp. }
    { right; right; left.
      exists n0 e; dands; tcsp. }
    { right; right; right.
      exists abs vars rhs cor; dands; tcsp. } }
  { right; right; left.
    exists name entry0; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp. }
    { right; left.
      exists e; dands; tcsp. }
    { right; right; left.
      exists n3 e; dands; tcsp. }
    { right; right; right.
      exists abs vars rhs cor; dands; tcsp. } }
  { right; right; right.
    exists opabs vars rhs correct; dands; tcsp. }
  { autodimp IHlib hyp; repndors; exrepnd; subst; simpl in *; tcsp.
    { left.
      exists e; dands; tcsp. }
    { right; left.
      exists e; dands; tcsp. }
    { right; right; left.
      exists n e; dands; tcsp. }
    { right; right; right.
      exists abs vars0 rhs0 cor; dands; tcsp. } }
Qed.

Lemma in_library_implies_in_sw_cs_lib1 {o} :
  forall n1 n2 e (lib : @plibrary o),
    List.In (lib_cs n1 e) lib
    -> List.In (lib_cs n2 e) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp.
Qed.
Hint Resolve in_library_implies_in_sw_cs_lib1 : slow.

Lemma in_library_implies_in_sw_cs_lib2 {o} :
  forall n1 n2 e (lib : @plibrary o),
    List.In (lib_cs n2 e) lib
    -> List.In (lib_cs n1 e) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp.
Qed.
Hint Resolve in_library_implies_in_sw_cs_lib2 : slow.

Lemma in_library_implies_in_sw_cs_lib3 {o} :
  forall n n1 n2 e (lib : @plibrary o),
    n <> n1
    -> n <> n2
    -> List.In (lib_cs n e) lib
    -> List.In (lib_cs n e) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv d1 d2 h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp.
Qed.
Hint Resolve in_library_implies_in_sw_cs_lib3 : slow.

Lemma in_library_implies_in_sw_cs_lib4 {o} :
  forall n1 n2 abs vars rhs cor (lib : @plibrary o),
    List.In (lib_abs abs vars rhs cor) lib
    -> List.In (lib_abs abs vars rhs cor) (sw_cs_lib lib n1 n2).
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst;
    simpl in *; boolvar; subst; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp.
Qed.
Hint Resolve in_library_implies_in_sw_cs_lib4 : slow.

(*Lemma sw_cs_lib_preserves_subset_library {o} :
  forall n1 n2 (lib1 lib2 : @library o),
    similar_cs_names n1 n2
    -> subset_library lib2 lib1
    -> subset_library (sw_cs_lib lib2 n1 n2) (sw_cs_lib lib1 n1 n2).
Proof.
  introv sim ext i.
  apply in_sw_cs_lib in i; repndors; exrepnd; subst; tcsp.
  { apply ext in i0; exrepnd.
    destruct entry2; simpl in *; repnd; subst; tcsp; ginv.
    apply (in_library_implies_in_sw_cs_lib2 n1 n2) in i0.
    eexists; dands; eauto.
    simpl; tcsp. }
  { apply ext in i0; exrepnd.
    destruct entry2; simpl in *; repnd; subst; tcsp; ginv.
    apply (in_library_implies_in_sw_cs_lib1 n1 n2) in i0.
    eexists; dands; eauto.
    simpl; tcsp. }
  { apply ext in i1; exrepnd.
    destruct entry2; simpl in *; repnd; subst; tcsp; ginv.
    apply (in_library_implies_in_sw_cs_lib3 n n1 n2) in i1; auto.
    eexists; dands; eauto.
    simpl; tcsp. }
  { apply ext in i1; exrepnd.
    destruct entry2; simpl in *; repnd; subst; tcsp; ginv.
    apply (in_library_implies_in_sw_cs_lib4 n1 n2) in i1; auto.
    eexists; dands; eauto. }
Qed.
Hint Resolve sw_cs_lib_preserves_subset_library : slow.*)

(*Lemma sw_cs_lib_preserves_lib_extends {o} :
  forall n1 n2 (lib1 lib2 : @library o),
    similar_cs_names n1 n2
    -> lib_extends lib2 lib1
    -> lib_extends (sw_cs_lib lib2 n1 n2) (sw_cs_lib lib1 n1 n2).
Proof.
  introv sim ext.
  destruct ext as [ext safe sub].
  split; eauto 3 with slow;[].
  introv safe'.
  apply if_safe_sw_cs_lib in safe'; auto.
  apply safe in safe'.
  eapply implies_safe_sw_cs_lib in safe'; eauto.
Qed.
Hint Resolve sw_cs_lib_preserves_lib_extends : slow.*)

(*Lemma implies_inf_lib_extends_sw_cs_lib_prop1 {o} :
  forall n1 n2 (lib' lib : @library o) e1 e2 infLib k1 k2,
    safe_library lib
    -> similar_cs_names n1 n2
    -> lib_extends lib' lib
    -> inf_lib_cs n2 e1 = infLib k2
    -> (forall j x, j < k2 -> ~ inf_matching_entries (infLib j) (lib_cs n2 x))
    -> inf_lib_cs n1 e2 = infLib k1
    -> (forall j x, j < k1 -> ~ inf_matching_entries (infLib j) (lib_cs n1 x))
    -> inf_lib_extends infLib (sw_cs_lib lib n1 n2)
    -> inf_lib_extends
         (cons_inf_lib_entry
            (inf_lib_cs n1 e1)
            (cons_inf_lib_entry
               (inf_lib_cs n2 e2)
               infLib))
         lib'
    -> inf_lib_extends infLib (sw_cs_lib lib' n1 n2).
Proof.
  introv safeL sim exta inInf1 nm1 inInf2 nm2 extb extc.
  destruct extb as [extb safeb].
  destruct extc as [extc safec].
  autodimp safeb hyp; eauto 3 with slow;[].
  split; tcsp;[].

  introv i.
  apply entry_in_sw_cs_lib in i; repndors; exrepnd; subst; simpl in *; tcsp.

  { apply extc in i0.
    repndors; exrepnd.
    { destruct n; simpl in *; tcsp.
      repndors; repnd; tcsp; subst; tcsp.
      { unfold similar_cs_names in sim; tcsp. }
      destruct n; simpl in *; tcsp.
      repndors; repnd; tcsp; subst; tcsp; GC;
        [|unfold inf_matching_entries in *; simpl in *; tcsp];[].
      left.
      exists (S k1).
      apply (inf_entry_extends_implies_entry_in_inf_library_extends_same_names
               _ _ (lib_cs n1 e)); simpl; tcsp.
      { rewrite <- inInf2; simpl; tcsp. }
      introv ltk; apply nm2; auto. }
    { unfold entry_in_inf_library_default in i0; simpl in i0; repnd.
      pose proof (i1 1) as i1; simpl in i1.
      unfold cons_inf_lib_entry in i1; simpl in i1; destruct i1; tcsp. } }

  { apply extc in i0.
    repndors; exrepnd.
    { destruct n; simpl in *; tcsp.
      repndors; repnd; tcsp; subst; tcsp.
      { left.
        exists (S k2).
        apply (inf_entry_extends_implies_entry_in_inf_library_extends_same_names
                 _ _ (lib_cs n2 e)); simpl; tcsp.
        { rewrite <- inInf1; simpl; tcsp. }
        introv ltk; apply nm1; auto. }
      unfold inf_matching_entries in i0; simpl in i0; tcsp. }
    { unfold entry_in_inf_library_default in i0; simpl in i0; repnd.
      pose proof (i1 0) as i1; simpl in i1.
      unfold cons_inf_lib_entry in i1; simpl in i1; destruct i1; tcsp. } }

  { apply extc in i1.
    repndors; exrepnd.
    { destruct n0; simpl in *; tcsp.
      repndors; repnd; tcsp; subst; tcsp.
      destruct n0; simpl in *; tcsp.
      repndors; repnd; tcsp; subst; tcsp.
      autorewrite with slow in *.
      left.
      exists n0; auto. }
    { apply entry_in_inf_library_default_cons_inf_lib_entry_implies in i1.
      apply entry_in_inf_library_default_cons_inf_lib_entry_implies in i1; tcsp. } }

  { apply extc in i1.
    repndors; exrepnd.
    { apply abs_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0.
      apply abs_entry_in_inf_library_extends_cons_inf_lib_entry_implies in i0.
      left; eauto. }
    { apply abs_entry_not_in_inf_library_default in i1; tcsp. } }
Qed.*)

Definition non_inhabited {o} (p : per(o)) :=
  forall t, ~ p t t.

Definition inhabited_iff {o} (p1 p2 : per(o)) :=
  inhabited p1 <=> inhabited p2.

Definition non_inhabited_iff {o} (p1 p2 : per(o)) :=
  non_inhabited p1 <=> non_inhabited p2.

(*Lemma implies_inhabited_iff_equality_of_int_bar {o} :
  forall name1 name2 lib (eq : per(o)),
    (eq <=2=> (equality_of_int_bar lib))
    -> inhabited_iff eq (equality_of_int_bar (rename_cs_lib lib name1 name2)).
Proof.
  introv iff.
  unfold inhabited_iff, inhabited; split; intro h; exrepnd.
  { apply iff in h0.
    exists (@mkc_zero o); eauto 3 with slow.
    rw @mkc_zero_eq; eauto 3 with slow. }
  { exists (@mkc_zero o); apply iff.
    rw @mkc_zero_eq; eauto 3 with slow. }
Qed.
Hint Resolve implies_inhabited_iff_equality_of_int_bar : slow.*)

(*Lemma implies_non_inhabited_iff_equality_of_int_bar {o} :
  forall name1 name2 lib (eq : per(o)),
    (eq <=2=> (equality_of_int_bar lib))
    -> non_inhabited_iff eq (equality_of_int_bar (rename_cs_lib lib name1 name2)).
Proof.
  introv iff.
  unfold non_inhabited_iff, non_inhabited; split; intro h; introv q;
    destruct (h (@mkc_nat o 0)); eauto 3 with slow.
  apply iff; eauto 3 with slow.
Qed.
Hint Resolve implies_non_inhabited_iff_equality_of_int_bar : slow.*)

Lemma implies_inhabited_iff_equality_of_int_bar_keep_only {o} :
  forall name lib (eq : per(o)),
    (eq <=2=> (equality_of_int_bar lib))
    -> inhabited_iff eq (equality_of_int_bar (keep_only name lib)).
Proof.
  introv iff.
  unfold inhabited_iff, inhabited; split; intro h; exrepnd.
  { apply iff in h0.
    exists (@mkc_zero o); eauto 3 with slow.
    rw @mkc_zero_eq; eauto 3 with slow. }
  { exists (@mkc_zero o); apply iff.
    rw @mkc_zero_eq; eauto 3 with slow. }
Qed.
Hint Resolve implies_inhabited_iff_equality_of_int_bar_keep_only : slow.

Lemma implies_non_inhabited_iff_equality_of_int_bar_keep_only {o} :
  forall name lib (eq : per(o)),
    (eq <=2=> (equality_of_int_bar lib))
    -> non_inhabited_iff eq (equality_of_int_bar (keep_only name lib)).
Proof.
  introv iff.
  unfold non_inhabited_iff, non_inhabited; split; intro h; introv q;
    destruct (h (@mkc_nat o 0)); eauto 3 with slow.
  apply iff; eauto 3 with slow.
Qed.
Hint Resolve implies_non_inhabited_iff_equality_of_int_bar_keep_only : slow.

Lemma safe_library_sing_lib_cs {o} :
  forall name c (lib : @library o),
    safe_library lib
    -> find_cs lib name = Some c
    -> safe_library [lib_cs name c].
Proof.
  introv safe fcs i; simpl in *; repndors; repnd; subst; tcsp.
  eauto 3 with slow.
Qed.
Hint Resolve safe_library_sing_lib_cs : slow.

Lemma inf_entry_extends_lib_cs_implies_inf_matching_entries {o} :
  forall ie name (a b : @ChoiceSeqEntry o),
    inf_entry_extends ie (lib_cs name a)
    -> inf_matching_entries ie (lib_cs name b).
Proof.
  introv ext.
  unfold inf_matching_entries; simpl.
  unfold same_entry_name.
  destruct ie; simpl in *; repndors; subst; tcsp.
Qed.
Hint Resolve inf_entry_extends_lib_cs_implies_inf_matching_entries : slow.

(*Lemma implies_inf_lib_extend_sing {o} :
  forall k (infLib : @inf_library o) lib lib' name c x,
    safe_inf_library infLib
    -> inf_entry_extends (infLib k) (lib_cs name x)
    -> (forall j : nat, j < k -> ~ inf_matching_entries (infLib j) (lib_cs name x))
    -> inf_lib_extends (inf_lib_cons_lib (infLib k) lib) lib'
    -> find_cs lib' name = Some c
    -> inf_lib_extends infLib [lib_cs name c].
Proof.
  introv safei iext imp ext fcs.
  destruct ext as [ext safe].
  split;[|introv safen; auto];[].

  introv i; simpl in *; repndors; tcsp; subst.
  pose proof (ext (lib_cs name c)) as ext.
  autodimp ext hyp; eauto 3 with slow.
  repndors; exrepnd.

  { left.
    destruct n; simpl in *; tcsp.
    repndors.

    { unfold inf_lib_cons_lib in ext0; boolvar; tcsp; GC.
      exists (S k).
      eapply inf_entry_extends_implies_entry_in_inf_library_extends_same_names; eauto. }

    repnd.
    destruct ext1.
    unfold inf_lib_cons_lib; boolvar; tcsp; GC; eauto 3 with slow. }

  { right.
    unfold entry_in_inf_library_default in *; repnd.
    destruct (ext0 0).
    unfold inf_lib_cons_lib; boolvar; tcsp; GC; eauto 3 with slow. }
Qed.
Hint Resolve implies_inf_lib_extend_sing : slow.*)

(*Lemma inf_lib_extends_nil {o} :
  forall (infLib : @inf_library o),
    safe_inf_library infLib
    -> inf_lib_extends infLib [].
Proof.
  introv safe.
  split; eauto 3 with slow.
  introv xx; simpl in *; tcsp.
Qed.
Hint Resolve inf_lib_extends_nil : slow.*)

(*Lemma implies_inf_lib_extend_sing2 {o} :
  forall (infLib : @inf_library o) name c x lib lib',
    safe_inf_library infLib
    -> (forall n, ~ inf_matching_entries (infLib n) (lib_cs name x))
    -> safe_choice_sequence_entry name x
    -> is_primitive_kind name
    -> is_default_choice_seq_entry x
    -> inf_lib_extends (inf_lib_cons_lib (library_entry2inf (lib_cs name x)) lib) lib'
    -> find_cs lib' name = Some c
    -> inf_lib_extends infLib [lib_cs name c].
Proof.
  introv safei imp safee prim def ext fcs.
  split;[|introv safen; auto];[].

  destruct ext as [ext safe].
  clear safe.

  introv i; simpl in *; repndors; tcsp; subst.
  right.

  pose proof (ext (lib_cs name c)) as ext.
  autodimp ext hyp; eauto 3 with slow.
  repndors; exrepnd.

  { destruct n; simpl in *; tcsp.
    repndors; repnd; GC.
    { unfold entry_in_inf_library_default; simpl; dands; auto; eauto 3 with slow. }
    destruct ext1.
    unfold inf_lib_cons_lib; boolvar; tcsp; GC; eauto 3 with slow. }

  { unfold entry_in_inf_library_default in *; repnd.
    destruct (ext0 0).
    unfold inf_lib_cons_lib; boolvar; tcsp; GC; eauto 3 with slow. }
Qed.
Hint Resolve implies_inf_lib_extend_sing2 : slow.*)

(*Lemma implies_safe_inf_library_entry_library_entry2inf {o} :
  forall (e : @library_entry o),
    safe_library_entry e
    -> safe_inf_library_entry (library_entry2inf e).
Proof.
  introv safe.
  destruct e; simpl in *; tcsp.
  destruct entry as [vals restr]; simpl in *; repnd; dands; auto.
  destruct restr; simpl in *; tcsp.

  { introv.
    unfold choice_seq_vals2inf.
    remember (select n vals) as sel; symmetry in Heqsel; destruct sel; tcsp; simpl; tcsp. }

  { introv.
    unfold choice_seq_vals2inf.
    remember (select n vals) as sel; symmetry in Heqsel; destruct sel; tcsp; simpl; tcsp.
    pose proof (safe n) as q; autodimp q hyp; eauto 3 with slow.
    rewrite Heqsel in q; inversion q; auto. }

  { introv.
    unfold choice_seq_vals2inf.
    remember (select n vals) as sel; symmetry in Heqsel; destruct sel; tcsp; simpl; tcsp. }
Qed.
Hint Resolve implies_safe_inf_library_entry_library_entry2inf : slow.*)

Lemma safe_library_entry_0 {o} : @safe_library_entry o lib_entry_0.
Proof.
  unfold safe_library_entry; simpl; dands; eauto 3 with slow.
  introv xx; autorewrite with slow in *; ginv.
Qed.
Hint Resolve safe_library_entry_0 : slow.

Lemma nth_entry_in_inf_library2 {o} :
  forall n (inflib : @inf_library o),
    is_cs_entry (inflib n)
    -> exists k entry,
      k <= S n
      /\ same_entry_name (inf_entry2name entry) (inf_entry2name (inflib n))
      /\ entry_in_inf_library_n k entry inflib.
Proof.
  induction n; introv iscs.

  - exists 1 (inflib 0); dands; eauto 3 with slow; simpl; tcsp.

  - pose proof (IHn (shift_inf_lib inflib)) as IHn.
    repeat (autodimp IHn hyp); exrepnd.

    destruct (same_entry_name_dec (inf_entry2name (inflib 0)) (inf_entry2name entry)) as [d|d].

    + exists 1 (inflib 0); dands; eauto 3 with slow; try omega; simpl; tcsp.

    + exists (S k) entry; dands; try omega; eauto 3 with slow; simpl; tcsp.
Qed.

(*Lemma entry_in_inf_library_n_implies_safe {o} :
  forall k (entry : @inf_library_entry o) infLib,
    safe_inf_library infLib
    -> entry_in_inf_library_n k entry infLib
    -> safe_inf_library_entry entry.
Proof.
  introv safe h.
  apply safe; eauto 3 with slow.
Qed.
Hint Resolve entry_in_inf_library_n_implies_safe : slow.*)

(*Lemma inf_lib_extends_sing3 {o} :
  forall name (infLib : @inf_library o) entry lib lib' c k,
    safe_inf_library infLib
    -> entry_in_inf_library_n k entry infLib
    -> same_entry_name (inf_entry2name entry) (entry_name_cs name)
    -> inf_lib_extends (library2inf lib entry) lib'
    -> find_cs lib name = None
    -> find_cs lib' name = Some c
    -> inf_lib_extends infLib [lib_cs name c].
Proof.
  introv safei il same ext fcsn fcs.
  split;[|introv safen; auto];[].

  destruct ext as [ext safe].
  clear safe.

  introv i; simpl in *; repndors; tcsp; subst.

  pose proof (ext (lib_cs name c)) as ext.
  autodimp ext hyp; eauto 3 with slow.
  repndors; exrepnd.

  { apply entry_in_inf_library_extends_library2inf_implies in ext0; repndors.

    { left; exists k; eauto 3 with slow. }

    { exrepnd.
      unfold inf_entry_extends in ext1.
      destruct e; simpl in *; tcsp; repnd; subst.
      apply entry_in_library_implies_find_cs_some in ext0.
      rewrite fcsn in ext0; ginv. } }

  { unfold entry_in_inf_library_default in *; repnd.
    destruct (ext0 (length lib)).
    unfold inf_matching_entries; simpl.
    unfold library2inf.
    rewrite select_none; try omega; auto. }
Qed.
Hint Resolve inf_lib_extends_sing3 : slow.*)

(*Lemma inf_lib_extends_sing4 {o} :
  forall name (infLib : @inf_library o) lib lib' c,
    is_primitive_kind name
    -> safe_inf_library infLib
    -> ~ (exists n, same_entry_name (inf_entry2name (infLib n)) (entry_name_cs name))
    -> inf_lib_extends (library2inf lib (library_entry2inf (choice_sequence_name2entry name))) lib'
    -> find_cs lib name = None
    -> find_cs lib' name = Some c
    -> inf_lib_extends infLib [lib_cs name c].
Proof.
  introv prim safei ne ext fcsn fcs.
  split;[|introv safen; auto];[].

  destruct ext as [ext safe].
  clear safe.

  introv i; simpl in *; repndors; tcsp; subst.

  pose proof (ext (lib_cs name c)) as ext.
  autodimp ext hyp; eauto 3 with slow.
  repndors; exrepnd.

  { apply entry_in_inf_library_extends_library2inf_implies in ext0; repndors.

    { simpl in *; repnd; GC.
      right.
      unfold entry_in_inf_library_default; simpl; dands; auto.

      { introv m.
        destruct ne; exists n0; eauto 3 with slow. }

      { destruct c as [vals restr]; simpl in *.
        unfold inf_choice_sequence_entry_extend in ext0; simpl in *; repnd.
        dands; eauto 3 with slow.
        destruct restr; simpl in *; tcsp.

        { introv sel.
          unfold inf_choice_sequence_vals_extend in *.
          applydup ext0 in sel; subst; clear ext0.
          unfold choice_seq_vals2inf in *; autorewrite with slow in *.
          destruct name as [name kind]; simpl in *.
          unfold choice_sequence_name2restriction in*; simpl in *.
          destruct kind; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp; repnd;
            try (complete (rewrite (ext2 n0); auto));ginv; tcsp;
              try (complete (apply ext1; eauto 3 with slow)). }

        { introv len.
          unfold inf_choice_sequence_vals_extend in *.
          applydup @select_lt_length in len; exrepnd; rewrite len1.
          applydup ext0 in len1; subst; clear len1.
          unfold choice_seq_vals2inf in *; autorewrite with slow in *.
          destruct name as [name kind]; simpl in *.
          unfold choice_sequence_name2restriction in*; simpl in *.
          destruct kind; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp; repnd;
            try (complete (rewrite (ext2 n0); auto)). }

        { introv sel.
          unfold inf_choice_sequence_vals_extend in *.
          applydup ext0 in sel; subst; clear ext0.
          unfold choice_seq_vals2inf in *; autorewrite with slow in *.
          destruct name as [name kind]; simpl in *.
          unfold choice_sequence_name2restriction in*; simpl in *.
          destruct kind; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp; repnd;
            try (complete (rewrite (ext2 n0); auto));ginv; tcsp;
              try (complete (apply ext1; eauto 3 with slow)). }
      }

      { unfold is_default_choice_seq_entry.
        destruct c as [vals restr]; simpl in *.
        unfold inf_choice_sequence_entry_extend in *; simpl in *; repnd.
        unfold inf_choice_sequence_vals_extend in *.
        unfold is_default_choice_sequence.
        destruct restr; simpl in *.

        { introv sel.
          unfold inf_choice_sequence_vals_extend in *.
          applydup ext0 in sel; subst.
          unfold choice_seq_vals2inf in *; autorewrite with slow in *.
          destruct name as [name kind]; simpl in *.
          unfold choice_sequence_name2restriction in*; simpl in *.
          destruct kind; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp; repnd;
            try (complete (rewrite (ext2 n0); auto)); ginv; tcsp. }

        { introv len.
          applydup ext0 in len; subst.
          unfold choice_seq_vals2inf in *; autorewrite with slow in *.
          destruct name as [name kind]; simpl in *.
          unfold choice_sequence_name2restriction in*; simpl in *.
          destruct kind; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp; repnd;
            try (complete (rewrite (ext2 n0); auto)). }

        { destruct name as [name kind]; simpl in *.
          unfold choice_sequence_name2restriction in*; simpl in *.
          destruct kind; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp; repnd;
            try (complete (rewrite (ext2 n0); auto)); ginv; tcsp. }
    } }

    { exrepnd.
      unfold inf_entry_extends in ext1.
      destruct e; simpl in *; tcsp; repnd; subst.
      apply entry_in_library_implies_find_cs_some in ext0.
      rewrite fcsn in ext0; ginv. } }

  { unfold entry_in_inf_library_default in *; repnd.
    destruct (ext0 (length lib)).
    unfold inf_matching_entries; simpl.
    unfold library2inf.
    rewrite select_none; simpl; try omega; auto. }
Qed.
Hint Resolve inf_lib_extends_sing4 : slow.*)

(*Definition bar_keep_only {o}
           name {lib}
           (prim : is_primitive_kind name)
           (safe : safe_library lib)
           (bar  : @BarLib o lib) : BarLib (keep_only name lib).
Proof.
  exists (fun (lib0 : library) =>
            exists lib1,
              bar_lib_bar bar lib1
              /\ lib_extends lib0 (keep_only name lib1)).

  - introv e.
    destruct bar as [bar1 bars1 ext1].
    simpl in *.

    applydup @inf_lib_extends_safe in e; eauto 3 with slow;[].

    rewrite keep_only_equal in e; rewrite keep_only_equal.
    remember (find_cs lib name) as fd; symmetry in Heqfd; destruct fd.

    { pose proof (inf_lib_extends_ext _ _ e (lib_cs name c)) as q.
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

        rewrite keep_only_equal.
        remember (find_cs lib' name) as fd'; symmetry in Heqfd'; destruct fd'; eauto 3 with slow. }

      { unfold entry_in_inf_library_default in q; simpl in *; repnd.
        pose proof (bars1 (inf_lib_cons_lib (library_entry2inf (lib_cs name c)) lib)) as w.
        autodimp w hyp; eauto 3 with slow;[].

        exrepnd.
        exists (keep_only name lib').
        dands; eauto 3 with slow.
        { apply (implies_lib_extends_keep_only name) in w2; auto.
          rewrite (keep_only_equal name lib) in w2.
          rewrite Heqfd in w2; auto. }

        rewrite keep_only_equal.
        remember (find_cs lib' name) as fd'; symmetry in Heqfd'; destruct fd'; eauto 3 with slow. } }

    { (* We have to check whether [name] occurs in infLib
                 (1) if it does, we use the infinite entry above
                 (2) otherwise, we can use the default entry *)

      destruct (classic (exists n, same_entry_name (inf_entry2name (infLib n)) (entry_name_cs name))) as [d|d].

      { exrepnd.
        pose proof (nth_entry_in_inf_library2 n infLib) as q.
        autodimp q hyp; eauto 3 with slow;[]; exrepnd.
        eapply same_entry_name_trans in d0;[|exact q2].
        clear dependent n.
        pose proof (bars1 (library2inf lib entry)) as q.
        autodimp q hyp; eauto 3 with slow;[]; exrepnd.

        remember (find_cs lib' name) as fd'; symmetry in Heqfd'; destruct fd'.

        { exists [lib_cs name c]; dands; eauto 4 with slow;[].
          exists lib'.
          rewrite keep_only_equal; rewrite Heqfd'; dands; eauto 3 with slow. }

        { exists ([] : @library o); dands; eauto 3 with slow;[].
          exists lib'; dands; eauto 2 with slow.
          rewrite keep_only_equal; allrw; eauto 3 with slow. } }

      { pose proof (bars1 (library2inf lib (library_entry2inf (choice_sequence_name2entry name)))) as q.
        autodimp q hyp; eauto 3 with slow;[]; exrepnd.

        remember (find_cs lib' name) as fd'; symmetry in Heqfd'; destruct fd'.

        { exists [lib_cs name c]; dands; eauto 4 with slow;[].
          exists lib'; dands; auto.
          rewrite keep_only_equal; allrw; eauto 3 with slow. }

        { exists ([] : @library o); dands; eauto 3 with slow;[].
          exists lib'; dands; eauto 2 with slow.
          rewrite keep_only_equal; allrw; eauto 3 with slow. } } }

  - introv h; exrepnd; eauto 4 with slow.
Defined.*)

Lemma implies_ccomputes_to_valc_ext_left {o} :
  forall lib (a b : @CTerm o) v u,
    a ===>(lib) v
    -> (mkc_apply a b) ===>(lib) u
    -> (mkc_apply v b) ===>(lib) u.
Proof.
  introv compa compb ext; pose proof (compa _ ext) as compa; pose proof (compb _ ext) as compb.
  simpl in *; exrepnd; spcast.
  dup compb1 as compc.
  eapply computes_to_valc_apply in compb1; eauto.

  pose proof (implies_cequivc_apply lib' v c0 b b) as q; repeat (autodimp q hyp).
  apply cequivc_sym in q.
  dup compb1 as compd.
  eapply cequivc_val in compb1; eauto; exrepnd.
  exists w; dands; spcast; auto.
  eapply cequivc_trans;[eauto|].
  eapply cequivc_trans;[|apply computes_to_valc_implies_cequivc;eauto].
  eapply cequivc_trans;[apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto|].
  apply implies_cequivc_apply; auto; apply cequivc_sym; auto.
Qed.

Lemma dec_nat {o} :
  forall (t : @CTerm o),
    decidable {k : nat & t = mkc_nat k}.
Proof.
  introv.
  destruct t as [t isp].
  destruct t as [v|op bs]; try (complete (right; intro xx; exrepnd; inversion xx0));[].
  dopid op as [can|ncan|exc|abs] Case; try (complete (right; intro xx; exrepnd; inversion xx0));[].
  destruct can; try (complete (right; intro xx; exrepnd; inversion xx0));[].
  destruct bs; try (complete (right; intro xx; exrepnd; inversion xx0));[].
  destruct (Z_lt_le_dec z 0).
  { right; intro xx; exrepnd; inversion xx0; subst.
    pose proof (Zle_0_nat k) as q; try omega. }
  pose proof (Z_of_nat_complete_inf z) as h; autodimp h hyp; exrepnd; subst.
  left.
  exists n.
  apply cterm_eq; simpl; auto.
Qed.

Lemma ex_find_cs_value_at {o} :
  forall (lib : @library o) name name' m,
    {k : nat
     , find_cs_value_at lib name  m = Some (mkc_nat k)
     # find_cs_value_at lib name' m = Some (mkc_nat k)}
    -> {k : nat
        & find_cs_value_at lib name  m = Some (mkc_nat k)
        # find_cs_value_at lib name' m = Some (mkc_nat k)}.
Proof.
  introv imp.
  remember (find_cs_value_at lib name m) as wa; symmetry in Heqwa.
  destruct wa; try (complete (assert False; tcsp));[].
  remember (find_cs_value_at lib name' m) as wb; symmetry in Heqwb.
  destruct wb; try (complete (assert False; tcsp));[].
  destruct (dec_nat c); exrepnd; subst.
  { exists k; dands; auto; exrepnd; ginv. }
  { assert False; tcsp; exrepnd.
    inversion imp1; subst; destruct n; eauto. }
Qed.

Lemma implies_name_in_library_swap_cs_lib {o} :
  forall a b (lib : @plibrary o),
    name_in_library a lib
    -> name_in_library b (swap_cs_plib (a, b) lib).
Proof.
  induction lib; introv h; simpl in *; tcsp.
  repndors; tcsp; repnd;
    destruct a0; simpl in *; subst; tcsp; boolvar; subst; tcsp.
Qed.

Lemma implies_name_in_library_swap_cs_lib2 {o} :
  forall a b (lib : @plibrary o),
    name_in_library b lib
    -> name_in_library a (swap_cs_plib (a, b) lib).
Proof.
  induction lib; introv h; simpl in *; tcsp.
  repndors; tcsp; repnd;
    destruct a0; simpl in *; subst; tcsp; boolvar; subst; tcsp.
Qed.

Lemma implies_swapping_in_library_swap_cs_lib {o} :
  forall {sw} {lib : @library o},
    swapping_in_library sw lib
    -> swapping_in_library sw (swap_cs_lib sw lib).
Proof.
  introv h; unfold swapping_in_library in *; repnd.
  destruct sw as [a b]; simpl in *.
  dands;
    try apply implies_name_in_library_swap_cs_lib;
    try apply implies_name_in_library_swap_cs_lib2; auto.
Qed.
Hint Resolve implies_swapping_in_library_swap_cs_lib : slow.

(*Lemma implies_safe_library_entry_sw {o} :
  forall sw (e : @library_entry o),
    sane_swapping sw
    -> safe_library_entry e
    -> safe_library_entry_sw sw e
    -> safe_library_entry_sw sw (swap_cs_lib_entry sw e).
Proof.
  introv sane safe h; destruct e; simpl in *; tcsp.
  destruct entry as [vals restr]; simpl in *; repnd.
  unfold safe_choice_sequence_entry; simpl.
  unfold swap_cs_choice_seq_entry_normalize; boolvar; subst; simpl in *; tcsp.

  { dands; autorewrite with slow; eauto 3 with slow. }

  destruct name as [name kind]; destruct sw as [a b];
    repeat (simpl in *; boolvar; subst; tcsp; GC).

  { destruct b as [nameb kindb]; simpl in *; unfold cs_name2restr; simpl.
    unfold compatible_choice_sequences in *; simpl in *.
    unfold correct_restriction in *; simpl in *.
    destruct kind, kindb; boolvar; subst; simpl in *; subst; dands; tcsp; GC; eauto 3 with slow;
      try (complete (introv sel; unfold swap_cs_choice_seq_vals in sel;
                     rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst;
                     eapply satisfies_is_nat_restriction_implies in sel1; eauto;
                     unfold is_nat in sel1; exrepnd; subst; autorewrite with slow; eauto 3 with slow;
                     eapply natSeq2restrictionPred_if_is_nat_restriction; eauto; eauto 3 with slow));
      try (complete (introv sel; unfold swap_cs_choice_seq_vals in sel;
                     rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst;
                     eapply satisfies_is_bool_restriction_implies in sel1; eauto;
                     unfold is_bool in sel1; exrepnd; subst; autorewrite with slow; eauto 3 with slow)).

    { introv len.
      eapply natSeq2restrictionPred_iff_cterm_is_nth_if_is_nat_seq_restriction; eauto.
      unfold natSeq2restrictionPred.
      pose proof (natSeq2default_if_is_nat_restriction l n1 restr) as q; repeat (autodimp q hyp).
      unfold natSeq2default in *.
      destruct (select n1 l); eauto 3 with slow. }

    { introv len; split; intro h; eauto 3 with slow.
      eapply natSeq2restrictionPred_if_is_nat_restriction in h; eauto.
      apply natSeq2restrictionPred_iff_cterm_is_nth; auto. }

    { introv sel; unfold swap_cs_choice_seq_vals in sel.
      rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst.
      eapply natSeq2restrictionPred_if_is_nat_restriction_select in sel1; eauto.
      unfold natSeq2restrictionPred in *; destruct (select n1 l0); subst; autorewrite with slow; eauto 3 with slow. } }

  { destruct a as [namea kinda]; simpl in *; unfold cs_name2restr; simpl.
    unfold compatible_choice_sequences in *; simpl in *.
    unfold correct_restriction in *; simpl in *.
    destruct kind, kinda; boolvar; subst; simpl in *; subst; dands; tcsp; GC; eauto 3 with slow;
      try (complete (introv sel; unfold swap_cs_choice_seq_vals in sel;
                     rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst;
                     eapply satisfies_is_nat_restriction_implies in sel1; eauto;
                     unfold is_nat in sel1; exrepnd; subst; autorewrite with slow; eauto 3 with slow;
                     eapply natSeq2restrictionPred_if_is_nat_restriction; eauto; eauto 3 with slow));
      try (complete (introv sel; unfold swap_cs_choice_seq_vals in sel;
                     rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst;
                     eapply satisfies_is_bool_restriction_implies in sel1; eauto;
                     unfold is_bool in sel1; exrepnd; subst; autorewrite with slow; eauto 3 with slow)).

    { introv len.
      eapply natSeq2restrictionPred_iff_cterm_is_nth_if_is_nat_seq_restriction; eauto.
      unfold natSeq2restrictionPred.
      pose proof (natSeq2default_if_is_nat_restriction l n restr) as q; repeat (autodimp q hyp).
      unfold natSeq2default in *.
      destruct (select n l); eauto 3 with slow. }

    { introv len; split; intro h; eauto 3 with slow.
      eapply natSeq2restrictionPred_if_is_nat_restriction in h; eauto.
      apply natSeq2restrictionPred_iff_cterm_is_nth; auto. }

    { introv sel; unfold swap_cs_choice_seq_vals in sel.
      rewrite select_map in sel; apply option_map_Some in sel; exrepnd; subst.
      eapply natSeq2restrictionPred_if_is_nat_restriction_select in sel1; eauto.
      unfold natSeq2restrictionPred in *; destruct (select n l0); subst; autorewrite with slow; eauto 3 with slow. } }
Qed.
Hint Resolve implies_safe_library_entry_sw : slow.*)

(*Lemma implies_swap_safe_library_sw {o} :
  forall sw (lib : @library o),
    sane_swapping sw
    -> safe_library lib
    -> safe_library_sw sw lib
    -> safe_library_sw sw (swap_cs_lib sw lib).
Proof.
  introv sane safe safesw i.
  apply entry_in_swap_library_implies in i; exrepnd; subst; eauto 3 with slow.
  applydup safesw in i1; eauto 3 with slow.
Qed.
Hint Resolve implies_swap_safe_library_sw : slow.*)

Lemma lib_extends_preserves_swapping_in_library {o} :
  forall sw (lib1 lib2 : @library o),
    lib_extends lib2 lib1
    -> swapping_in_library sw lib1
    -> swapping_in_library sw lib2.
Proof.
  introv ext swin.
  unfold swapping_in_library in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_swapping_in_library : slow.

(*Lemma lib_extends_preserves_safe_library_sw2 {o} :
  forall sw (lib1 lib2 : @library o),
    swapping_in_library sw lib1
    -> safe_library lib2
    -> lib_extends lib2 lib1
    -> safe_library_sw sw lib1
    -> safe_library_sw sw lib2.
Proof.
  introv swin safe ext sfin.
  apply (lib_extends_preserves_safe_library_sw sw lib2 lib1); eauto 3 with slow.
  apply lib_extends_ext; auto.
Qed.
Hint Resolve lib_extends_preserves_safe_library_sw2 : slow.*)

Hint Rewrite @strong_safe_library_cons : slow.

Lemma implies_choice_sequence_satisfies_restriction_snoc {o} :
  forall (vals : @ChoiceSeqVals o) v restr,
    satisfies_restriction (length vals) v restr
    -> choice_sequence_satisfies_restriction vals restr
    -> choice_sequence_satisfies_restriction (snoc vals v) restr.
Proof.
  introv sata satb; destruct restr; simpl in *; introv sel; simpl in *.

  { rewrite select_snoc_eq in sel; boolvar; subst; tcsp; ginv; tcsp. }

(*  { rewrite length_snoc in sel.
    rewrite select_snoc_eq; boolvar; subst; tcsp; try omega. }

  { rewrite select_snoc_eq in sel; boolvar; subst; tcsp; ginv; tcsp. }*)
Qed.
Hint Resolve implies_choice_sequence_satisfies_restriction_snoc : slow.

Lemma add_choice_preserves_strong_safe_library {o} :
  forall name v (lib : @plibrary o) n restr lib',
    add_choice name v lib = Some (n, restr, lib')
    -> satisfies_restriction n v restr
    -> strong_safe_library lib
    -> strong_safe_library lib'.
Proof.
  induction lib; introv addc sat safe; simpl in *; ginv.
  destruct a; simpl in *; tcsp.

  { destruct entry as [vals restr']; simpl in *; boolvar; subst; simpl in *; tcsp.

    { inversion addc; subst; clear addc; simpl in *; autorewrite with slow in *; repnd; dands; tcsp.
      simpl in *; repnd; dands; tcsp; eauto 3 with slow. }

    { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
      destruct addc'; repnd; simpl in *; tcsp; ginv.
      inversion addc; clear addc; subst; simpl in *.
      autorewrite with slow in *; simpl in *; repnd; dands; tcsp.
      eapply IHlib; eauto. } }

  { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; simpl in *; tcsp; ginv.
    inversion addc; clear addc; subst; simpl in *.
    autorewrite with slow in *; simpl in *; repnd; dands; tcsp.
    eapply IHlib; eauto. }
Qed.
Hint Resolve add_choice_preserves_strong_safe_library : slow.

Lemma add_one_choice_preserves_strong_safe_library {o} :
  forall name v (lib : @library o) n restr lib',
    add_one_choice name v lib = Some (n, restr, lib')
    -> satisfies_restriction n v restr
    -> strong_safe_library lib
    -> strong_safe_library lib'.
Proof.
  introv h sat safe.
  destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv; eauto 3 with slow.
Qed.
Hint Resolve add_one_choice_preserves_strong_safe_library : slow.

Lemma lib_extends_preserves_strong_safe_library {o} :
  forall (lib' lib : @library o),
    lib_extends lib' lib
    -> strong_safe_library lib
    -> strong_safe_library lib'.
Proof.
  introv ext; lib_ext_ind ext Case; introv safe.

  { Case "lib_ext_new_abs".
    apply strong_safe_library_cons; dands; tcsp. }

  { Case "lib_ext_new_cs".
    apply strong_safe_library_cons; simpl; dands; tcsp; eauto 3 with slow. }
Qed.
Hint Resolve lib_extends_preserves_strong_safe_library : slow.

Lemma lib_extends_swap_cs_lib_twice_implies {o} :
  forall {sw} {lib1 lib2 : @library o},
    lib_extends lib1 (swap_cs_lib sw (swap_cs_lib sw lib2))
    -> lib_extends lib1 lib2.
Proof.
  introv h.
  rewrite swap_cs_lib_idem in h; auto.
Qed.

Definition swap_cs_lib_per {o} {lib}
           sw
           (s : sane_swapping sw)
           (p : lib-per(lib,o)) : lib-per(swap_cs_lib sw lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' (swap_cs_lib sw lib)) =>
            swap_cs_per
              sw
              (p (swap_cs_lib sw lib')
                 (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends s x)))).
  introv; unfold swap_cs_per; introv; apply lib_per_cond.
Defined.

Lemma lib_extends_swap_right_to_left {o} :
  forall {sw} {lib lib' : @library o},
    sane_swapping sw
    -> lib_extends lib' (swap_cs_lib sw lib)
    -> lib_extends (swap_cs_lib sw lib') lib.
Proof.
  introv sane ext.
  apply (@swap_lib_extends o sw) in ext; auto.
  rewrite swap_cs_lib_idem in ext; auto.
Qed.

Lemma lib_extends_swap_left_to_right {o} :
  forall {sw} {lib lib' : @library o},
    sane_swapping sw
    -> lib_extends (swap_cs_lib sw lib') lib
    -> lib_extends lib' (swap_cs_lib sw lib).
Proof.
  introv sane ext.
  apply (@swap_lib_extends o sw) in ext; auto.
  rewrite swap_cs_lib_idem in ext; auto.
Qed.

Lemma in_open_bar_ext_swap_cs_lib_pres {o} :
  forall sw (lib : @library o)
         (F : forall lib' (x : lib_extends lib' lib), Prop)
         (G : forall lib' (x : lib_extends lib' (swap_cs_lib sw lib)), Prop)
         (sane : sane_swapping sw),
    in_ext_ext lib (fun lib' (x : lib_extends lib' lib) =>
                      forall (y : lib_extends (swap_cs_lib sw lib') (swap_cs_lib sw lib)),
                        F lib' x -> G (swap_cs_lib sw lib') y)
    -> in_open_bar_ext lib F
    -> in_open_bar_ext (swap_cs_lib sw lib) G.
Proof.
  introv sane cond h.
  introv ext.
  pose proof (h _ (lib_extends_swap_right_to_left sane ext)) as h; simpl in h; exrepnd.
  exists (swap_cs_lib sw lib'') (lib_extends_swap_right_to_left sane y).

  introv xta; introv.
  pose proof (cond _ (lib_extends_swap_right_to_left sane z)) as cond; simpl in cond.
  rewrite swap_cs_lib_idem in cond.
  apply cond.
  apply h1.
  apply lib_extends_swap_right_to_left; auto.
Qed.

Lemma in_open_bar_ext_swap_cs_lib_pres2 {o} :
  forall sw (lib : @library o)
         (F : forall lib' (x : lib_extends lib' (swap_cs_lib sw lib)), Prop)
         (G : forall lib' (x : lib_extends lib' lib), Prop)
         (sane : sane_swapping sw),
    in_ext_ext lib (fun lib' (x : lib_extends lib' lib) =>
                      forall (y : lib_extends (swap_cs_lib sw lib') (swap_cs_lib sw lib)),
                        F (swap_cs_lib sw lib') y -> G lib' x)
    -> in_open_bar_ext (swap_cs_lib sw lib) F
    -> in_open_bar_ext lib G.
Proof.
  introv sane cond h.
  introv ext.
  pose proof (h _ (swap_lib_extends sane ext)) as h; simpl in h; exrepnd.
  exists (swap_cs_lib sw lib'') (lib_extends_swap_right_to_left sane y).

  introv xta; introv.
  pose proof (cond _ z (swap_lib_extends sane z)) as cond; simpl in cond.
  apply cond.
  apply h1.
  apply lib_extends_swap_right_to_left; auto.
Qed.

Lemma in_open_bar_swap_cs_lib_pres {o} :
  forall sw (lib : @library o)
         (F : library -> Prop)
         (G : library -> Prop)
         (sane : sane_swapping sw),
    in_ext lib (fun lib' => F lib' -> G (swap_cs_lib sw lib'))
    -> in_open_bar lib F
    -> in_open_bar (swap_cs_lib sw lib) G.
Proof.
  introv sane cond h.
  introv ext.
  pose proof (h _ (lib_extends_swap_right_to_left sane ext)) as h; simpl in h; exrepnd.
  exists (swap_cs_lib sw lib'') (lib_extends_swap_right_to_left sane xt).

  introv xta.
  pose proof (cond (swap_cs_lib sw lib'0)) as cond; simpl in cond.
  rewrite swap_cs_lib_idem in cond; apply cond.
  { eapply lib_extends_trans.
    { apply lib_extends_swap_right_to_left;eauto. }
    eapply lib_extends_trans;[eauto|].
    apply lib_extends_swap_right_to_left;eauto. }
  apply h1.
  apply lib_extends_swap_right_to_left;eauto.
Qed.

Lemma in_open_bar_swap_cs_lib_pres2 {o} :
  forall sw (lib : @library o)
         (F : library -> Prop)
         (G : library -> Prop)
         (sane : sane_swapping sw),
    in_ext lib (fun lib' => F (swap_cs_lib sw lib') -> G lib')
    -> in_open_bar (swap_cs_lib sw lib) F
    -> in_open_bar lib G.
Proof.
  introv sane cond h.
  apply (in_open_bar_swap_cs_lib_pres sw _ _ G) in h; auto.
  { autorewrite with slow in *; auto. }
  introv xt q.
  apply cond; autorewrite with slow; auto.
  apply lib_extends_swap_right_to_left; auto.
Qed.

Lemma swap_ccomputes_to_valc {o} :
  forall sw lib (a b : @CTerm o),
    ccomputes_to_valc lib a b
    -> ccomputes_to_valc (swap_cs_plib sw lib) (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv comp; introv.
Admitted.

Lemma swap_ccomputes_to_valc_ext {o} :
  forall sw lib (a b : @CTerm o),
    a ===>(lib) b
    -> (swap_cs_cterm sw a) ===>(swap_cs_lib sw lib) (swap_cs_cterm sw b).
Proof.
  introv comp; introv.
Admitted.

Lemma swap_ccequivc {o} :
  forall sw lib (a b : @CTerm o),
    a ~=~(lib) b
    -> (swap_cs_cterm sw a) ~=~(swap_cs_plib sw lib) (swap_cs_cterm sw b).
Proof.
  introv.
Admitted.

Lemma swap_capproxc {o} :
  forall sw lib (a b : @CTerm o),
    a ~<~(lib) b
    -> (swap_cs_cterm sw a) ~<~(swap_cs_plib sw lib) (swap_cs_cterm sw b).
Proof.
  introv.
Admitted.

Lemma swap_ccequivc_ext {o} :
  forall sw lib (a b : @CTerm o),
    sane_swapping sw
    -> ccequivc_ext lib a b
    -> ccequivc_ext (swap_cs_lib sw lib) (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv sane ceq ext.
  pose proof (ceq _ (lib_extends_swap_right_to_left sane ext)) as ceq; simpl in *.
  apply (swap_ccequivc sw) in ceq; autorewrite with slow in ceq; auto.
Qed.

Lemma swap_eqorceq_ext {o} :
  forall sw (sane : sane_swapping sw) lib eqa (a b : @CTerm o),
    eqorceq_ext lib eqa a b
    -> eqorceq_ext (swap_cs_lib sw lib) (swap_cs_lib_per sw sane eqa) (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv h; introv; simpl.
  pose proof (h _ (lib_extends_swap_right_to_left sane e)) as h; simpl in h.
  unfold eqorceq in *; repndors; tcsp.

  { left.
    unfold swap_cs_per; autorewrite with slow.
    eapply lib_per_cond; eauto. }

  { right.
    apply (swap_ccequivc_ext sw) in h; auto; autorewrite with slow in h; auto. }
Qed.

Lemma iff_swap_ccequivc {o} :
  forall sw lib (a b : @CTerm o),
    a ~=~(lib) b
    <-> (swap_cs_cterm sw a) ~=~(swap_cs_plib sw lib) (swap_cs_cterm sw b).
Proof.
  introv; split; intro h.
  { apply swap_ccequivc; auto. }
  { apply (swap_ccequivc sw) in h.
    autorewrite with slow in h; auto. }
Qed.

Lemma iff_swap_capproxc {o} :
  forall sw lib (a b : @CTerm o),
    a ~<~(lib) b
    <-> (swap_cs_cterm sw a) ~<~(swap_cs_plib sw lib) (swap_cs_cterm sw b).
Proof.
  introv; split; intro h.
  { apply swap_capproxc; auto. }
  { apply (swap_capproxc sw) in h.
    autorewrite with slow in h; auto. }
Qed.

Lemma implies_isprog_vars_swap_cs_term {o} :
  forall r {vs} {t : @NTerm o},
    isprog_vars vs t
    -> isprog_vars vs (swap_cs_term r t).
Proof.
  introv isp.
  allrw @isprog_vars_eq; repnd.
  autorewrite with slow.
  dands; allrw @nt_wf_eq; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_vars_swap_cs_term : slow.

Definition swap_cs_cvterm {o} sw {vs} (ct : @CVTerm o vs) : CVTerm vs :=
  let (t,isp) := ct in
  mk_cvterm _ (swap_cs_term sw t) (implies_isprog_vars_swap_cs_term sw isp).

Lemma ccomputes_to_valc_ext_equality_twice {o} :
  forall (lib : @library o) t a b c u v w,
    ccomputes_to_valc_ext lib t (mkc_equality a b c)
    -> ccomputes_to_valc_ext lib t (mkc_equality u v w)
    -> ccequivc_ext lib a u # ccequivc_ext lib b v # ccequivc_ext lib c w.
Proof.
  introv compa compb.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in compa.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in compb.
  eapply ccequivc_ext_trans in compb;[|apply ccequivc_ext_sym;exact compa].
  apply ccequivc_ext_mkc_equality_implies in compb; auto.
Qed.

Ltac ccomputes_to_valc_ext_decomp :=
  match goal with
  | [ H : ccomputes_to_valc_ext ?lib ?t (mkc_equality _ _ _),
      J : ccomputes_to_valc_ext ?lib ?t (mkc_equality _ _ _) |- _ ] =>
    eapply ccomputes_to_valc_ext_equality_twice in J; try exact H; repnd
  end.

Lemma type_system_ccequivc_ext_left {o} :
  forall (ts : cts(o)) lib a b c eq,
    type_system ts
    -> ccequivc_ext lib a c
    -> ts lib a b eq
    -> ts lib c b eq.
Proof.
  introv tysys ceq cl.
  dest_ts tysys.
  pose proof (ts_tyv lib a c eq) as ha.
  repeat (autodimp ha hyp).
  { eapply ts_tyt; eauto. }
  eapply ts_tys; eauto.
Qed.

Lemma type_system_ccequivc_ext_right {o} :
  forall (ts : cts(o)) lib a b c eq,
    type_system ts
    -> ccequivc_ext lib a c
    -> ts lib b a eq
    -> ts lib b c eq.
Proof.
  introv tysys ceq cl.
  dest_ts tysys.
  pose proof (ts_tyv lib a c eq) as ha.
  repeat (autodimp ha hyp).
  { eapply ts_tyt; eauto. }
  eapply ts_tys; eauto.
Qed.

Lemma close_type_value_respecting_left {o} :
  forall (ts : cts(o)) lib a b c eq,
    local_ts ts
    -> ts_implies_per_bar ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccequivc_ext lib a c
    -> close ts lib a b eq
    -> close ts lib c b eq.
Proof.
  introv loc imp tysys dou mon ceq cl.
  pose proof (close_type_system ts) as h; repeat (autodimp h hyp).
  unfold type_system in h; repnd.
  eapply type_system_ccequivc_ext_left; eauto.
  apply close_type_system; auto.
Qed.

Lemma close_type_value_respecting_right {o} :
  forall (ts : cts(o)) lib a b c eq,
    local_ts ts
    -> ts_implies_per_bar ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccequivc_ext lib a c
    -> close ts lib b a eq
    -> close ts lib b c eq.
Proof.
  introv loc imp tysys dou mon ceq cl.
  pose proof (close_type_system ts) as h; repeat (autodimp h hyp).
  unfold type_system in h; repnd.
  eapply type_system_ccequivc_ext_right; eauto.
  apply close_type_system; auto.
Qed.

Lemma swap_cs_cterm_mkc_int {o} : forall sw, @swap_cs_cterm o sw mkc_int = mkc_int.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_int : slow.

Lemma swap_cs_cterm_mkc_integer {o} : forall sw k, @swap_cs_cterm o sw (mkc_integer k) = mkc_integer k.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_integer : slow.

Lemma swap_cs_cterm_mkc_csname {o} : forall sw k, @swap_cs_cterm o sw (mkc_csname k) = mkc_csname k.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_csname : slow.

Lemma swap_cs_cterm_mkc_Nat {o} : forall sw, @swap_cs_cterm o sw mkc_Nat = mkc_Nat.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_Nat : slow.

Lemma swap_cs_cterm_mkc_qnat {o} : forall sw, @swap_cs_cterm o sw mkc_qnat = mkc_qnat.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_qnat : slow.

Lemma swap_cs_cterm_mkc_atom {o} : forall sw, @swap_cs_cterm o sw mkc_atom = mkc_atom.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_atom : slow.

Lemma swap_cs_cterm_mkc_uatom {o} : forall sw, @swap_cs_cterm o sw mkc_uatom = mkc_uatom.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_uatom : slow.

Lemma swap_cs_cterm_mkc_base {o} : forall sw, @swap_cs_cterm o sw mkc_base = mkc_base.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_base : slow.

Lemma swap_cs_cterm_mkc_nat {o} : forall sw k, @swap_cs_cterm o sw (mkc_nat k) = mkc_nat k.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_nat : slow.

Lemma swap_cs_cterm_mkc_token {o} : forall sw k, @swap_cs_cterm o sw (mkc_token k) = mkc_token k.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_token : slow.

Lemma swap_cs_cterm_mkc_utoken {o} : forall sw k, @swap_cs_cterm o sw (mkc_utoken k) = mkc_utoken k.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_utoken : slow.

Lemma swap_cs_cterm_mkc_choice_seq {o} : forall sw k, @swap_cs_cterm o sw (mkc_choice_seq k) = mkc_choice_seq (swap_cs sw k).
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_choice_seq : slow.

Lemma swap_cs_cterm_mkc_approx {o} :
  forall sw a b, @swap_cs_cterm o sw (mkc_approx a b) = mkc_approx (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_approx : slow.

Lemma swap_cs_cterm_mkc_cequiv {o} :
  forall sw a b, @swap_cs_cterm o sw (mkc_cequiv a b) = mkc_cequiv (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_cequiv : slow.

Lemma swap_cs_cterm_mkc_apply {o} :
  forall sw a b, @swap_cs_cterm o sw (mkc_apply a b) = mkc_apply (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_apply : slow.

Lemma swap_cs_cterm_mkc_pair {o} :
  forall sw a b, @swap_cs_cterm o sw (mkc_pair a b) = mkc_pair (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_pair : slow.

Lemma swap_cs_cterm_mkc_qtime {o} :
  forall sw a, @swap_cs_cterm o sw (mkc_qtime a) = mkc_qtime (swap_cs_cterm sw a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_qtime : slow.

Lemma swap_cs_cterm_mkc_inl {o} :
  forall sw a, @swap_cs_cterm o sw (mkc_inl a) = mkc_inl (swap_cs_cterm sw a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_inl : slow.

Lemma swap_cs_cterm_mkc_inr {o} :
  forall sw a, @swap_cs_cterm o sw (mkc_inr a) = mkc_inr (swap_cs_cterm sw a).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_inr : slow.

Lemma swap_cs_cterm_mkc_equality {o} :
  forall sw a b c, @swap_cs_cterm o sw (mkc_equality a b c) = mkc_equality (swap_cs_cterm sw a) (swap_cs_cterm sw b) (swap_cs_cterm sw c).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_equality : slow.

Lemma swap_cs_cterm_mkc_union {o} :
  forall sw a b, @swap_cs_cterm o sw (mkc_union a b) = mkc_union (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_union : slow.

Lemma swap_cs_cterm_mkc_image {o} :
  forall sw a b, @swap_cs_cterm o sw (mkc_image a b) = mkc_image (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_image : slow.

Lemma swap_cs_cterm_mkc_free_from_defs {o} :
  forall sw a b, @swap_cs_cterm o sw (mkc_free_from_defs a b) = mkc_free_from_defs (swap_cs_cterm sw a) (swap_cs_cterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_free_from_defs : slow.

Lemma swap_cs_cterm_mkc_function {o} :
  forall sw a x (b : @CVTerm o [x]), @swap_cs_cterm o sw (mkc_function a x b) = mkc_function (swap_cs_cterm sw a) x (swap_cs_cvterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_function : slow.

Lemma swap_cs_cterm_mkc_product {o} :
  forall sw a x (b : @CVTerm o [x]), @swap_cs_cterm o sw (mkc_product a x b) = mkc_product (swap_cs_cterm sw a) x (swap_cs_cvterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_product : slow.

Lemma swap_cs_cterm_mkc_set {o} :
  forall sw a x (b : @CVTerm o [x]), @swap_cs_cterm o sw (mkc_set a x b) = mkc_set (swap_cs_cterm sw a) x (swap_cs_cvterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_set : slow.

Lemma swap_cs_cterm_mkc_axiom {o} : forall sw, @swap_cs_cterm o sw mkc_axiom = mkc_axiom.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_axiom : slow.

Lemma swap_equality_of_atom_bar {o} :
  forall sw lib (eq : per(o)),
    sane_swapping sw
    -> (eq <=2=> (equality_of_atom_bar lib))
    -> (swap_cs_per sw eq) <=2=> (equality_of_atom_bar (swap_cs_lib sw lib)).
Proof.
  introv sane h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_swap_cs_lib_pres; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_atom in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    autorewrite with slow in *.
    eexists; dands; eauto. }
  { apply h; clear h.
    unfold equality_of_int_bar in *.
    eapply in_open_bar_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_atom in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    autorewrite with slow in *.
    eexists; dands; eauto. }
Qed.

Lemma swap_equality_of_uatom_bar {o} :
  forall sw lib (eq : per(o)),
    sane_swapping sw
    -> (eq <=2=> (equality_of_uatom_bar lib))
    -> (swap_cs_per sw eq) <=2=> (equality_of_uatom_bar (swap_cs_lib sw lib)).
Proof.
  introv sane h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_swap_cs_lib_pres; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_uatom in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    autorewrite with slow in *.
    eexists; dands; eauto. }
  { apply h; clear h.
    unfold equality_of_int_bar in *.
    eapply in_open_bar_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_uatom in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    autorewrite with slow in *.
    eexists; dands; eauto. }
Qed.

Lemma swap_equality_of_int_bar {o} :
  forall sw lib (eq : per(o)),
    sane_swapping sw
    -> (eq <=2=> (equality_of_int_bar lib))
    -> (swap_cs_per sw eq) <=2=> (equality_of_int_bar (swap_cs_lib sw lib)).
Proof.
  introv sane h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_swap_cs_lib_pres; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_int in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    autorewrite with slow in *.
    eexists; dands; eauto. }
  { apply h; clear h.
    unfold equality_of_int_bar in *.
    eapply in_open_bar_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_int in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    autorewrite with slow in *.
    eexists; dands; eauto. }
Qed.

Lemma swap_equality_of_nat_bar {o} :
  forall sw lib (eq : per(o)),
    sane_swapping sw
    -> (eq <=2=> (equality_of_nat_bar lib))
    -> (swap_cs_per sw eq) <=2=> (equality_of_nat_bar (swap_cs_lib sw lib)).
Proof.
  introv sane h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_swap_cs_lib_pres; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_nat in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    autorewrite with slow in *.
    eexists; dands; eauto. }
  { apply h; clear h.
    unfold equality_of_nat_bar in *.
    eapply in_open_bar_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_nat in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    autorewrite with slow in *.
    eexists; dands; eauto. }
Qed.

Lemma lib_pre_swap_cs_lib {o} :
  forall sw (lib : @library o),
    lib_pre (swap_cs_lib sw lib) = swap_cs_plib sw lib.
Proof.
  tcsp.
Qed.
Hint Rewrite @lib_pre_swap_cs_lib : slow.

Lemma swap_equality_of_qnat_bar {o} :
  forall sw lib (eq : per(o)),
    sane_swapping sw
    -> (eq <=2=> (equality_of_qnat_bar lib))
    -> (swap_cs_per sw eq) <=2=> (equality_of_qnat_bar (swap_cs_lib sw lib)).
Proof.
  introv sane h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_swap_cs_lib_pres; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_qnat in *; exrepnd.
    apply (swap_ccomputes_to_valc sw) in q1.
    apply (swap_ccomputes_to_valc sw) in q2.
    autorewrite with slow in *.
    eexists; dands; eauto. }
  { apply h; clear h.
    unfold equality_of_nat_bar in *.
    eapply in_open_bar_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_qnat in *; exrepnd.
    apply (swap_ccomputes_to_valc sw) in q1.
    apply (swap_ccomputes_to_valc sw) in q2.
    autorewrite with slow in *.
    eexists; dands; eauto. }
Qed.

Lemma sane_swapping_implies_compatible_choice_sequence_name :
  forall sw n name,
    sane_swapping sw
    -> compatible_choice_sequence_name n name
    -> compatible_choice_sequence_name n (swap_cs sw name).
Proof.
  introv sane comp.
  unfold compatible_choice_sequence_name, compatible_cs_kind in *.
  unfold sane_swapping, compatible_choice_sequences in *.
 destruct sw; simpl in *; boolvar; subst; try congruence;
   try (complete (rewrite sane in *; tcsp)).
Qed.

Lemma swap_equality_of_csname_bar {o} :
  forall sw lib (eq : per(o)) n,
    sane_swapping sw
    -> (eq <=2=> (equality_of_csname_bar lib n))
    -> (swap_cs_per sw eq) <=2=> (equality_of_csname_bar (swap_cs_lib sw lib) n).
Proof.
  introv sane h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_swap_cs_lib_pres; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_csname in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    apply (swap_ccomputes_to_valc_ext sw) in q2.
    autorewrite with slow in *.
    exists (swap_cs sw name); dands; auto.
    eapply sane_swapping_implies_compatible_choice_sequence_name; eauto. }
  { apply h; clear h.
    unfold equality_of_nat_bar in *.
    eapply in_open_bar_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv ext q.
    unfold equality_of_csname in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    apply (swap_ccomputes_to_valc_ext sw) in q2.
    autorewrite with slow in *.
    exists (swap_cs sw name); dands; auto.
    eapply sane_swapping_implies_compatible_choice_sequence_name; eauto. }
Qed.

Lemma swap_per_base_eq {o} :
  forall sw lib (eq : per(o)),
    sane_swapping sw
    -> (eq <=2=> (per_base_eq lib))
    -> (swap_cs_per sw eq) <=2=> (per_base_eq (swap_cs_lib sw lib)).
Proof.
  introv sane h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_swap_cs_lib_pres; try exact q; clear q; auto.
    introv ext q.
    apply (swap_ccequivc sw) in q.
    autorewrite with slow in *; auto. }
  { apply h; clear h.
    eapply in_open_bar_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv ext q.
    apply (swap_ccequivc sw) in q.
    autorewrite with slow in *; auto. }
Qed.

Lemma swap_per_approx_eq_bar {o} :
  forall sw lib (eq : per(o)) a b,
    sane_swapping sw
    -> (eq <=2=> (per_approx_eq_bar lib a b))
    -> (swap_cs_per sw eq) <=2=> (per_approx_eq_bar (swap_cs_lib sw lib) (swap_cs_cterm sw a) (swap_cs_cterm sw b)).
Proof.
  introv sane h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_swap_cs_lib_pres; try exact q; clear q; auto.
    introv ext q.
    unfold per_approx_eq in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    autorewrite with slow in *; dands; auto.
    apply iff_swap_capproxc; auto. }
  { apply h; clear h.
    eapply in_open_bar_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv ext q.
    unfold per_approx_eq in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    autorewrite with slow in *; dands; auto.
    apply iff_swap_capproxc in q; auto. }
Qed.

Lemma swap_per_cequiv_eq_bar {o} :
  forall sw lib (eq : per(o)) a b,
    sane_swapping sw
    -> (eq <=2=> (per_cequiv_eq_bar lib a b))
    -> (swap_cs_per sw eq) <=2=> (per_cequiv_eq_bar (swap_cs_lib sw lib) (swap_cs_cterm sw a) (swap_cs_cterm sw b)).
Proof.
  introv sane h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_swap_cs_lib_pres; try exact q; clear q; auto.
    introv ext q.
    unfold per_cequiv_eq in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    autorewrite with slow in *; dands; auto.
    apply iff_swap_ccequivc; auto. }
  { apply h; clear h.
    eapply in_open_bar_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv ext q.
    unfold per_cequiv_eq in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    autorewrite with slow in *; dands; auto.
    apply iff_swap_ccequivc in q; auto. }
Qed.

Lemma swap_eq_per_eq_bar {o} :
  forall sw (sane : sane_swapping sw) lib (eq : per(o)) a b (eqa : lib-per(lib,o)),
    (eq <=2=> (eq_per_eq_bar lib a b eqa))
    -> (swap_cs_per sw eq) <=2=> (eq_per_eq_bar (swap_cs_lib sw lib) (swap_cs_cterm sw a) (swap_cs_cterm sw b) (swap_cs_lib_per sw sane eqa)).
Proof.
  introv h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres; try exact q; clear q; auto.
    introv q.
    unfold eq_per_eq in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    autorewrite with slow in *; dands; auto.
    simpl; unfold swap_cs_per.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert xe; autorewrite with slow; introv.
    eapply lib_per_cond; eauto. }
  { apply h; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv q.
    unfold eq_per_eq in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    autorewrite with slow in *; dands; auto.
    simpl in *; unfold swap_cs_per in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert dependent xe; autorewrite with slow; introv h.
    eapply lib_per_cond; eauto. }
Qed.

Lemma swap_per_qtime_eq_bar {o} :
  forall sw (sane : sane_swapping sw) lib (eq : per(o)) (eqa : lib-per(lib,o)),
    (eq <=2=> (per_qtime_eq_bar lib eqa))
    -> (swap_cs_per sw eq) <=2=> (per_qtime_eq_bar (swap_cs_lib sw lib) (swap_cs_lib_per sw sane eqa)).
Proof.
  introv h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres; try exact q; clear q; auto.
    introv q.
    unfold per_qtime_eq in *; exrepnd.
    apply (swap_ccequivc sw) in q0.
    apply (swap_ccequivc sw) in q2.
    apply (swap_ccequivc_ext sw) in q3; auto.
    autorewrite with slow in *; dands; auto.
    eexists; eexists; dands; eauto.
    simpl; unfold swap_cs_per.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert xe; autorewrite with slow; introv.
    eapply lib_per_cond; eauto. }
  { apply h; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv q.
    unfold per_qtime_eq in *; exrepnd.
    apply (swap_ccequivc sw) in q0.
    apply (swap_ccequivc sw) in q2.
    apply (swap_ccequivc_ext sw) in q3; auto.
    autorewrite with slow in *; dands; auto.
    eexists; eexists; dands; eauto.
    simpl in *; unfold swap_cs_per in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert dependent xe; autorewrite with slow; introv h.
    eapply lib_per_cond; eauto. }
Qed.

Definition swap_cs_lib_per_fam {o} {lib}
           sw
           (sane : sane_swapping sw)
           {eqa  : lib-per(lib,o)}
           (eqb  : lib-per-fam(lib,eqa))
  : lib-per-fam(swap_cs_lib sw lib,swap_cs_lib_per sw sane eqa).
Proof.
  exists (fun lib' (x : lib_extends lib' (swap_cs_lib sw lib))
              a a' (p : swap_cs_lib_per sw sane eqa lib' x a a') =>
            swap_cs_per
              sw
              (eqb
                 (swap_cs_lib sw lib')
                 (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane x))
                 (swap_cs_cterm sw a) (swap_cs_cterm sw a')
                 p)).
  repeat introv; simpl; unfold swap_cs_per; eapply lib_per_fam_cond.
Defined.

Lemma swap_cterm_substc {o} :
  forall sw a x (b : @CVTerm o [x]),
    swap_cs_cterm sw (substc a x b)
    = substc (swap_cs_cterm sw a) x (swap_cs_cvterm sw b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl.
  rewrite subst_swap_cs_term; auto.
Qed.
Hint Rewrite @swap_cterm_substc : slow.

Lemma swap_per_func_ext_eq {o} :
  forall sw (sane : sane_swapping sw) lib (eq : per(o)) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa)),
    (eq <=2=> (per_func_ext_eq lib eqa eqb))
    -> (swap_cs_per sw eq) <=2=> (per_func_ext_eq (swap_cs_lib sw lib) (swap_cs_lib_per sw sane eqa) (swap_cs_lib_per_fam sw sane eqb)).
Proof.
  introv h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres; try exact q; clear q; auto.
    introv q.
    unfold per_func_eq in *; introv; simpl in *.
    unfold swap_cs_per in *; simpl in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert dependent xe; autorewrite with slow in *; introv.
    assert (eqa lib' e (swap_cs_cterm sw a) (swap_cs_cterm sw a')) as xa.
    { eapply lib_per_cond; eauto. }
    pose proof (q _ _ xa) as q.
    eapply lib_per_fam_cond; eauto. }
  { apply h; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv q.
    unfold per_func_eq in *; introv; simpl in *.
    unfold swap_cs_per in *; simpl in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert dependent xe; autorewrite with slow in *; introv imp.
    assert (eqa lib' xe (swap_cs_cterm sw (swap_cs_cterm sw a)) (swap_cs_cterm sw (swap_cs_cterm sw a'))) as xa.
    { autorewrite with slow; eapply lib_per_cond; eauto. }
    pose proof (imp _ _ xa) as q; revert dependent xa; autorewrite with slow; introv q.
    eapply lib_per_fam_cond; eauto. }
Qed.

Lemma swap_per_product_ext_eq {o} :
  forall sw (sane : sane_swapping sw) lib (eq : per(o)) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa)),
    (eq <=2=> (per_product_eq_bar lib eqa eqb))
    -> (swap_cs_per sw eq) <=2=> (per_product_eq_bar (swap_cs_lib sw lib) (swap_cs_lib_per sw sane eqa) (swap_cs_lib_per_fam sw sane eqb)).
Proof.
  introv h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres; try exact q; clear q; auto.
    introv q.
    unfold per_product_eq in *; exrepnd; simpl in *.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (swap_ccomputes_to_valc_ext sw) in q2.
    autorewrite with slow in *.
    unfold swap_cs_per in *; simpl in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as ex; clear Heqex.
    revert dependent ex; autorewrite with slow; introv.
    assert (eqa lib' ex (swap_cs_cterm sw (swap_cs_cterm sw a)) (swap_cs_cterm sw (swap_cs_cterm sw a'))) as ea.
    { autorewrite with slow; eapply lib_per_cond; eauto. }
    eexists; eexists; eexists; eexists; exists ea; dands; eauto.
    revert dependent ea; autorewrite with slow; introv.
    eapply lib_per_fam_cond; eauto. }
  { apply h; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv q.
    unfold per_product_eq in *; exrepnd; simpl in *.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (swap_ccomputes_to_valc_ext sw) in q2.
    autorewrite with slow in *.
    unfold swap_cs_per in *; simpl in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as ex; clear Heqex.
    revert dependent ex; autorewrite with slow; introv.
    assert (eqa lib' e (swap_cs_cterm sw a) (swap_cs_cterm sw a')) as ea.
    { eapply lib_per_cond; eauto. }
    eexists; eexists; eexists; eexists; exists ea; dands; eauto.
    eapply lib_per_fam_cond; eauto. }
Qed.

Lemma swap_inhabited {o} :
  forall sw (p : per(o)),
    inhabited p <-> inhabited (swap_cs_per sw p).
Proof.
  introv; split; introv h; unfold inhabited, swap_cs_per in *; exrepnd; eauto.
  exists (swap_cs_cterm sw t); autorewrite with slow; auto.
Qed.

Lemma swap_per_set_ext_eq {o} :
  forall sw (sane : sane_swapping sw) lib (eq : per(o)) (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa)),
    (eq <=2=> (per_set_eq_bar lib eqa eqb))
    -> (swap_cs_per sw eq) <=2=> (per_set_eq_bar (swap_cs_lib sw lib) (swap_cs_lib_per sw sane eqa) (swap_cs_lib_per_fam sw sane eqb)).
Proof.
  introv h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres; try exact q; clear q; auto.
    introv q.
    unfold per_set_eq in *; exrepnd; simpl in *.
    unfold swap_cs_per in *; simpl in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as ex; clear Heqex.
    revert dependent ex; autorewrite with slow; introv.
    assert (eqa lib' ex (swap_cs_cterm sw t1) (swap_cs_cterm sw t2)) as ea.
    { eapply lib_per_cond; eauto. }
    exists ea.
    apply (swap_inhabited sw) in q0; unfold swap_cs_per in *; simpl in *.
    eapply iff_inhabited_if_eq_term_equals; try exact q0; introv; apply lib_per_fam_cond. }
  { apply h; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv q.
    unfold per_set_eq in *; exrepnd; simpl in *.
    unfold swap_cs_per in *; simpl in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as ex; clear Heqex.
    revert dependent ex; autorewrite with slow; introv inh.
    assert (eqa lib' e (swap_cs_cterm sw t1) (swap_cs_cterm sw t2)) as ea.
    { eapply lib_per_cond; eauto. }
    exists ea.
    apply (swap_inhabited sw) ; unfold swap_cs_per in *; simpl in *.
    eapply iff_inhabited_if_eq_term_equals; try exact inh; introv; apply lib_per_fam_cond. }
Qed.

Lemma swap_per_union_eq_bar {o} :
  forall sw (sane : sane_swapping sw) lib (eq : per(o)) (eqa eqb : lib-per(lib,o)),
    (eq <=2=> (per_union_eq_bar lib eqa eqb))
    -> (swap_cs_per sw eq) <=2=> (per_union_eq_bar (swap_cs_lib sw lib) (swap_cs_lib_per sw sane eqa) (swap_cs_lib_per sw sane eqb)).
Proof.
  introv h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres; try exact q; clear q; auto.
    introv q.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *;
    repndors;[left|right]; exrepnd;
      apply (swap_ccomputes_to_valc_ext sw) in q0;
      apply (swap_ccomputes_to_valc_ext sw) in q2;
      autorewrite with slow in *; dands; auto;
        eexists; eexists; dands; eauto;
          simpl; unfold swap_cs_per;
            remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe;
              revert xe; autorewrite with slow; introv;
                eapply lib_per_cond; eauto. }
  { apply h; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv q.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *;
      repndors;[left|right]; exrepnd;
      apply (swap_ccomputes_to_valc_ext sw) in q0;
      apply (swap_ccomputes_to_valc_ext sw) in q2;
      autorewrite with slow in *; dands; auto;
        eexists; eexists; dands; eauto;
          simpl in *; unfold swap_cs_per in *;
            remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe;
              revert dependent xe; autorewrite with slow; introv h;
                eapply lib_per_cond; eauto. }
Qed.

Lemma implies_swap_per_image_eq {o} :
  forall sw lib (p : per(o)) f t1 t2,
    sane_swapping sw
    -> per_image_eq lib p f t1 t2
    -> per_image_eq (swap_cs_lib sw lib) (swap_cs_per sw p) (swap_cs_cterm sw f) (swap_cs_cterm sw t1) (swap_cs_cterm sw t2).
Proof.
  introv sane h.
  induction h as [|? ? ? ? e u v]; eauto.
  { eapply image_eq_cl; eauto. }
  apply (swap_ccequivc_ext sw) in u; auto.
  apply (swap_ccequivc_ext sw) in v; auto.
  autorewrite with slow in *.
  eapply image_eq_eq; eauto.
  unfold swap_cs_per; autorewrite with slow; auto.
Qed.

Lemma swap_per_image_eq_bar {o} :
  forall sw (sane : sane_swapping sw) lib (eq : per(o)) (eqa : lib-per(lib,o)) f,
    (eq <=2=> (per_image_eq_bar lib eqa f))
    -> (swap_cs_per sw eq) <=2=> (per_image_eq_bar (swap_cs_lib sw lib) (swap_cs_lib_per sw sane eqa) (swap_cs_cterm sw f)).
Proof.
  introv h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres; try exact q; clear q; auto.
    introv q; simpl in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert xe; autorewrite with slow; introv.
    apply (implies_swap_per_image_eq sw) in q; auto; autorewrite with slow in q.
    eapply implies_eq_term_equals_eq_image_eq; try exact q.
    introv; unfold swap_cs_per; simpl; apply lib_per_cond. }
  { apply h; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv q; simpl in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert dependent xe; autorewrite with slow; introv q.
    apply (implies_swap_per_image_eq sw) in q; auto; autorewrite with slow in q.
    eapply implies_eq_term_equals_eq_image_eq; try exact q.
    introv; unfold swap_cs_per; simpl; autorewrite with slow; apply lib_per_cond. }
Qed.

Definition swap_cs_def_kind sw (k : def_kind) : def_kind :=
  match k with
  | defk_abs op => defk_abs op
  | defk_cs name => defk_cs (swap_cs sw name)
  end.

Lemma get_defs_swap_cs_term {o} :
  forall sw (t : @NTerm o),
    get_defs (swap_cs_term sw t) = map (swap_cs_def_kind sw) (get_defs t).
Proof.
  introv.
  nterm_ind t as [|op bs ind] Case; simpl; auto.
  rewrite map_app.
  rewrite map_flat_map; unfold compose.
  rewrite flat_map_map; unfold compose.
  f_equal.
  { dopid op as [can|ncan|exc|abs] SCase; simpl; auto.
    destruct can; simpl; auto. }
  apply eq_flat_maps; introv i; destruct x; simpl; eauto.
Qed.

Lemma implies_swap_nodefsc {o} :
  forall sw (u : @CTerm o),
    nodefsc u
    -> nodefsc (swap_cs_cterm sw u).
Proof.
  introv h; destruct_cterms.
  unfold nodefsc in *; simpl in *.
  unfold nodefs in *; autorewrite with slow.
  rewrite get_defs_swap_cs_term; allrw; simpl; auto.
Qed.
Hint Resolve implies_swap_nodefsc : slow.

Lemma implies_swap_ex_nodefsc {o} :
  forall sw (p : per(o)) f,
    ex_nodefsc p f
    -> ex_nodefsc (swap_cs_per sw p) (swap_cs_cterm sw f).
Proof.
  introv h; unfold ex_nodefsc in *; exrepnd.
  exists (swap_cs_cterm sw u); unfold swap_cs_per; autorewrite with slow; dands; eauto 3 with slow.
Qed.
Hint Resolve implies_swap_ex_nodefsc : slow.

Lemma swap_per_ffdefs_eq_bar {o} :
  forall sw (sane : sane_swapping sw) lib (eq : per(o)) (eqa : lib-per(lib,o)) f,
    (eq <=2=> (per_ffdefs_eq_bar lib eqa f))
    -> (swap_cs_per sw eq) <=2=> (per_ffdefs_eq_bar (swap_cs_lib sw lib) (swap_cs_lib_per sw sane eqa) (swap_cs_cterm sw f)).
Proof.
  introv h; introv; unfold swap_cs_per; split; intro q.
  { apply h in q; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres; try exact q; clear q; auto.
    introv q; simpl in *.
    unfold per_ffdefs_eq in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (implies_swap_ex_nodefsc sw) in q; simpl in q.
    autorewrite with slow in *; dands; eauto 3 with slow.
    eapply ex_nodefsc_change_per; try exact q; introv; unfold swap_cs_per; simpl.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert xe; autorewrite with slow; introv; apply lib_per_cond. }
  { apply h; clear h.
    eapply in_open_bar_ext_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv q; simpl in *.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert dependent xe; autorewrite with slow; introv q.
    unfold per_ffdefs_eq in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in q0.
    apply (swap_ccomputes_to_valc_ext sw) in q1.
    apply (implies_swap_ex_nodefsc sw) in q; simpl in q.
    autorewrite with slow in *; dands; eauto 3 with slow.
    eapply ex_nodefsc_change_per; try exact q; introv; unfold swap_cs_per; simpl.
    autorewrite with slow; apply lib_per_cond. }
Qed.

Lemma swap_per_bar_eq {o} :
  forall sw (sane : sane_swapping sw) lib (eq : per(o)) (eqa : lib-per(lib,o)),
    (eq <=2=> (per_bar_eq lib eqa))
    -> (swap_cs_per sw eq) <=2=> (per_bar_eq (swap_cs_lib sw lib) (swap_cs_lib_per sw sane eqa)).
Proof.
  introv eqiff.
  introv; unfold swap_cs_per; simpl.
  split; intro q.

  { apply eqiff in q.
    eapply in_open_bar_ext_swap_cs_lib_pres; try exact q; clear q; auto.
    introv q; simpl.
    unfold swap_cs_per; simpl.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert dependent xe; autorewrite with slow; introv.
    eapply lib_per_cond; eauto. }

  { apply eqiff.
    eapply in_open_bar_ext_swap_cs_lib_pres2; try exact q; clear q; auto.
    introv q; simpl in q.
    unfold swap_cs_per in q; simpl in q.
    remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as xe; clear Heqxe.
    revert dependent xe; autorewrite with slow; introv q.
    eapply lib_per_cond; eauto. }
Qed.


Lemma implies_close_swap_cs {o} :
  forall sw lib (u : cts(o)) (t1 t2 : @CTerm o) e,
    sane_swapping sw
    -> type_extensionality u
    -> local_ts u
    -> ts_implies_per_bar u
    -> type_system u
    -> defines_only_universes u
    -> type_monotone u
    -> (forall lib t1 t2 e,
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
  introv sane tyext locts tsimp tysys dou mon imp cl.
  close_cases (induction cl using @close_ind') Case; introv; subst.

  { Case "CL_init".
    apply CL_init.
    apply imp; auto.
  }

  { Case "CL_bar".
    apply CL_bar; clear per.
    exists (swap_cs_lib_per sw sane eqa); simpl; dands.

    { eapply in_open_bar_ext_swap_cs_lib_pres; try exact reca; auto; clear reca; simpl.
      introv reca; repeat (autodimp reca hyp).
      eapply close_extensionality; try exact reca; auto.
      introv; unfold swap_cs_per; simpl.
      remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as z; clear Heqz.
      revert z.
      rewrite swap_cs_lib_idem; introv.
      apply lib_per_cond. }

    apply swap_per_bar_eq; auto. }

  { Case "CL_int".
    apply CL_int.
    unfold per_int in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in per0.
    apply (swap_ccomputes_to_valc_ext sw) in per1.
    autorewrite with slow in *.
    dands; eauto 3 with slow.
    apply swap_equality_of_int_bar; auto. }

  { Case "CL_nat".
    apply CL_nat.
    unfold per_nat in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in per0.
    apply (swap_ccomputes_to_valc_ext sw) in per1.
    autorewrite with slow in *.
    dands; eauto 3 with slow.
    apply swap_equality_of_nat_bar; auto. }

  { Case "CL_qnat".
    apply CL_qnat.
    unfold per_qnat in *; repnd.
    apply (swap_ccomputes_to_valc_ext sw) in per0.
    apply (swap_ccomputes_to_valc_ext sw) in per1.
    autorewrite with slow in *.
    dands; eauto 3 with slow.
    apply swap_equality_of_qnat_bar; auto. }

  { Case "CL_csname".
    apply CL_csname.
    unfold per_csname in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in per1.
    apply (swap_ccomputes_to_valc_ext sw) in per2.
    autorewrite with slow in *.
    exists n; dands; eauto 3 with slow.
    apply swap_equality_of_csname_bar; auto. }

  { Case "CL_atom".
    apply CL_atom.
    unfold per_atom in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in per1.
    apply (swap_ccomputes_to_valc_ext sw) in per0.
    autorewrite with slow in *.
    dands; eauto 3 with slow.
    apply swap_equality_of_atom_bar; auto. }

  { Case "CL_uatom".
    apply CL_uatom.
    unfold per_uatom in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in per1.
    apply (swap_ccomputes_to_valc_ext sw) in per0.
    autorewrite with slow in *.
    dands; eauto 3 with slow.
    apply swap_equality_of_uatom_bar; auto. }

  { Case "CL_base".
    apply CL_base.
    unfold per_base in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in per1.
    apply (swap_ccomputes_to_valc_ext sw) in per0.
    autorewrite with slow in *.
    dands; eauto 3 with slow.
    apply swap_per_base_eq; auto. }

  { Case "CL_approx".
    apply CL_approx.
    unfold per_approx in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in per0.
    apply (swap_ccomputes_to_valc_ext sw) in per2.
    autorewrite with slow in *.
    eexists; eexists; eexists; eexists; dands; eauto.
    { introv xt.
      pose proof (per3 _ (lib_extends_swap_right_to_left sane xt)) as per3; simpl in *; split; intro h.
      { apply (iff_swap_capproxc sw); autorewrite with slow; apply per3.
        apply (iff_swap_capproxc sw); autorewrite with slow; auto. }
      { apply (iff_swap_capproxc sw); autorewrite with slow; apply per3.
        apply (iff_swap_capproxc sw); autorewrite with slow; auto. } }
    apply swap_per_approx_eq_bar; auto. }

  { Case "CL_cequiv".
    apply CL_cequiv.
    unfold per_cequiv in *; exrepnd.
    apply (swap_ccomputes_to_valc_ext sw) in per0.
    apply (swap_ccomputes_to_valc_ext sw) in per2.
    autorewrite with slow in *.
    eexists; eexists; eexists; eexists; dands; eauto.
    { introv xt.
      pose proof (per3 _ (lib_extends_swap_right_to_left sane xt)) as per3; simpl in *; split; intro h.
      { apply (iff_swap_ccequivc sw); autorewrite with slow; apply per3.
        apply (iff_swap_ccequivc sw); autorewrite with slow; auto. }
      { apply (iff_swap_ccequivc sw); autorewrite with slow; apply per3.
        apply (iff_swap_ccequivc sw); autorewrite with slow; auto. } }
    apply swap_per_cequiv_eq_bar; auto. }

  { Case "CL_eq".
    apply CL_eq.
    clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1.
    apply (swap_ccomputes_to_valc_ext sw) in c2.
    autorewrite with slow in *.
    eexists; eexists; eexists; eexists; eexists; eexists.
    exists (swap_cs_lib_per sw sane eqa).
    dands; eauto;
      try (complete (apply (swap_eqorceq_ext sw sane); auto)).

    { introv; simpl.
      pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact reca; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

    apply swap_eq_per_eq_bar; auto. }

  { Case "CL_qtime".
    apply CL_qtime; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1.
    apply (swap_ccomputes_to_valc_ext sw) in c2.
    autorewrite with slow in *.
    unfold per_qtime.
    exists (swap_cs_lib_per sw sane eqa).
    eexists; eexists.
    dands; eauto.

    { introv; simpl.
      pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact reca; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

    apply swap_per_qtime_eq_bar; auto. }

  { Case "CL_func".
    apply CL_func; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1.
    apply (swap_ccomputes_to_valc_ext sw) in c2.
    autorewrite with slow in *.
    unfold per_func_ext.

    exists (swap_cs_lib_per sw sane eqa) (swap_cs_lib_per_fam sw sane eqb).
    dands; eauto.

    { unfold type_family_ext; simpl.
      eexists; eexists; eexists; eexists; eexists; eexists.
      dands; eauto.

      { introv; simpl.
        pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
        repeat (autodimp reca hyp).
        autorewrite with slow in *.
        eapply close_extensionality; try exact reca; auto.
        introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

      introv; simpl.
      assert (eqa (swap_cs_lib sw lib') (lib_extends_swap_right_to_left sane e) (swap_cs_cterm sw a) (swap_cs_cterm sw a')) as ex.
      { unfold swap_cs_per in *; simpl in *.
        eapply lib_per_cond; eauto. }
      pose proof (recb _ (lib_extends_swap_right_to_left sane e) (swap_cs_cterm sw a) (swap_cs_cterm sw a') ex) as recb; simpl in recb.
      repeat (autodimp recb hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact recb; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_fam_cond. }

    apply swap_per_func_ext_eq; auto. }

  { Case "CL_union".
    apply CL_union; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1.
    apply (swap_ccomputes_to_valc_ext sw) in c2.
    autorewrite with slow in *.
    unfold per_union.
    exists (swap_cs_lib_per sw sane eqa) (swap_cs_lib_per sw sane eqb).
    eexists; eexists; eexists; eexists.
    dands; eauto.

    { introv; simpl.
      pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact reca; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

    { introv; simpl.
      pose proof (recb _ (lib_extends_swap_right_to_left sane e)) as recb; simpl in recb.
      repeat (autodimp recb hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact recb; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

    apply swap_per_union_eq_bar; auto. }

  { Case "CL_image".
    apply CL_image; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1.
    apply (swap_ccomputes_to_valc_ext sw) in c2.
    apply (swap_ccequivc_ext sw) in ceq; auto.
    autorewrite with slow in *.
    unfold per_image.
    exists (swap_cs_lib_per sw sane eqa); eexists; eexists; eexists; eexists.
    dands; eauto.

    { introv; simpl.
      pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact reca; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

    apply swap_per_image_eq_bar; auto. }

  { Case "CL_ffdefs".
    apply CL_ffdefs; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1.
    apply (swap_ccomputes_to_valc_ext sw) in c2.
    autorewrite with slow in *.
    unfold per_ffdefs.
    eexists; eexists; eexists; eexists; exists (swap_cs_lib_per sw sane eqa).
    dands; eauto.

    { introv; simpl.
      pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
      repeat (autodimp reca hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact reca; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

    { introv; simpl.
      unfold swap_cs_per; simpl.
      autorewrite with slow; eauto. }

    apply swap_per_ffdefs_eq_bar; auto. }

  { Case "CL_set".
    apply CL_set; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1.
    apply (swap_ccomputes_to_valc_ext sw) in c2.
    autorewrite with slow in *.
    unfold per_set.

    exists (swap_cs_lib_per sw sane eqa) (swap_cs_lib_per_fam sw sane eqb).
    dands; eauto.

    { unfold type_family_ext; simpl.
      eexists; eexists; eexists; eexists; eexists; eexists.
      dands; eauto.

      { introv; simpl.
        pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
        repeat (autodimp reca hyp).
        autorewrite with slow in *.
        eapply close_extensionality; try exact reca; auto.
        introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

      introv; simpl.
      assert (eqa (swap_cs_lib sw lib') (lib_extends_swap_right_to_left sane e) (swap_cs_cterm sw a) (swap_cs_cterm sw a')) as ex.
      { unfold swap_cs_per in *; simpl in *.
        eapply lib_per_cond; eauto. }
      pose proof (recb _ (lib_extends_swap_right_to_left sane e) (swap_cs_cterm sw a) (swap_cs_cterm sw a') ex) as recb; simpl in recb.
      repeat (autodimp recb hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact recb; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_fam_cond. }

    apply swap_per_set_ext_eq; auto. }

  { Case "CL_product".
    apply CL_product; clear per.
    apply (swap_ccomputes_to_valc_ext sw) in c1.
    apply (swap_ccomputes_to_valc_ext sw) in c2.
    autorewrite with slow in *.
    unfold per_set.

    exists (swap_cs_lib_per sw sane eqa) (swap_cs_lib_per_fam sw sane eqb).
    dands; eauto.

    { unfold type_family_ext; simpl.
      eexists; eexists; eexists; eexists; eexists; eexists.
      dands; eauto.

      { introv; simpl.
        pose proof (reca _ (lib_extends_swap_right_to_left sane e)) as reca; simpl in reca.
        repeat (autodimp reca hyp).
        autorewrite with slow in *.
        eapply close_extensionality; try exact reca; auto.
        introv; unfold swap_cs_per; simpl; apply lib_per_cond. }

      introv; simpl.
      assert (eqa (swap_cs_lib sw lib') (lib_extends_swap_right_to_left sane e) (swap_cs_cterm sw a) (swap_cs_cterm sw a')) as ex.
      { unfold swap_cs_per in *; simpl in *.
        eapply lib_per_cond; eauto. }
      pose proof (recb _ (lib_extends_swap_right_to_left sane e) (swap_cs_cterm sw a) (swap_cs_cterm sw a') ex) as recb; simpl in recb.
      repeat (autodimp recb hyp).
      autorewrite with slow in *.
      eapply close_extensionality; try exact recb; auto.
      introv; unfold swap_cs_per; simpl; apply lib_per_fam_cond. }

    apply swap_per_product_ext_eq; auto. }
Qed.

Lemma swap_cs_cterm_mkc_uni {o} : forall sw k, @swap_cs_cterm o sw (mkc_uni k) = mkc_uni k.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @swap_cs_cterm_mkc_uni : slow.

Lemma swap_univi_eq {o} :
  forall sw i (e : per(o)) lib,
    sane_swapping sw
    -> (forall lib t1 t2 (e : per(o)),
           univi i lib t1 t2 e
           -> univi i (swap_cs_lib sw lib)
                    (swap_cs_cterm sw t1)
                    (swap_cs_cterm sw t2)
                    (swap_cs_per sw e))
    -> (e <=2=> (univi_eq (univi_bar i) lib))
    -> (swap_cs_per sw e) <=2=> (univi_eq (univi_bar i) (swap_cs_lib sw lib)).
Proof.
  introv sane imp eqiff; introv; split; intro h; simpl in *.

  { unfold swap_cs_per in h; apply eqiff in h; clear eqiff.
    unfold univi_eq in *; exrepnd.
    exists (swap_cs_per sw eqa).
    apply (implies_close_swap_cs sw) in h0; eauto 3 with slow; autorewrite with slow in *; auto.
    clear h0.
    introv h.
    unfold univi_bar, per_bar in *; exrepnd.
    exists (swap_cs_lib_per sw sane eqa0); dands; auto.

    { eapply in_open_bar_ext_swap_cs_lib_pres; try exact h1; auto; clear h1; simpl.
      introv h1; repeat (autodimp h1 hyp).
      remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as z; clear Heqz.
      revert z; autorewrite with slow; introv.
      apply imp; auto.
      eapply type_extensionality_univi; eauto; apply lib_per_cond. }

    apply swap_per_bar_eq; auto. }

  { unfold univi_eq, swap_cs_per in *; exrepnd.
    apply eqiff; clear eqiff.
    exists (swap_cs_per sw eqa).
    apply (implies_close_swap_cs sw) in h0; eauto 3 with slow; autorewrite with slow in *; auto.
    clear h0.
    introv h.
    unfold univi_bar, per_bar in *; exrepnd.
    exists (swap_cs_lib_per sw sane eqa0); dands; auto.

    { eapply in_open_bar_ext_swap_cs_lib_pres; try exact h1; auto; clear h1; simpl.
      introv h1; repeat (autodimp h1 hyp).
      remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as z; clear Heqz.
      revert z; autorewrite with slow; introv.
      apply imp; auto.
      eapply type_extensionality_univi; eauto; apply lib_per_cond. }

    apply swap_per_bar_eq; auto. }
Qed.

Lemma implies_univi_swap_cs {o} :
  forall sw i lib (t1 t2 : @CTerm o) e,
    sane_swapping sw
    -> univi i lib t1 t2 e
    -> univi
         i
         (swap_cs_lib sw lib)
         (swap_cs_cterm sw t1)
         (swap_cs_cterm sw t2)
         (swap_cs_per sw e).
Proof.
  induction i; introv sane u; simpl in *; tcsp.
  repndors; repnd;[left|right]; eauto;[].

  apply (swap_ccomputes_to_valc_ext sw) in u0.
  apply (swap_ccomputes_to_valc_ext sw) in u1.
  autorewrite with slow in *; dands; auto.
  apply swap_univi_eq; auto.
Qed.

Lemma implies_univ_swap_cs {o} :
  forall sw lib (t1 t2 : @CTerm o) e,
    sane_swapping sw
    -> univ lib t1 t2 e
    -> univ
         (swap_cs_lib sw lib)
         (swap_cs_cterm sw t1)
         (swap_cs_cterm sw t2)
         (swap_cs_per sw e).
Proof.
  introv sane u.
  unfold univ in *.
  unfold per_bar in *; exrepnd.
  exists (swap_cs_lib_per sw sane eqa); simpl; dands; auto;
    try (complete (apply swap_per_bar_eq; auto)).
  eapply in_open_bar_ext_swap_cs_lib_pres; try exact u1; auto; clear u1; simpl.
  introv u.
  unfold univ_ex in *; exrepnd; exists i.
  apply implies_univi_swap_cs; auto.
  remember (lib_extends_swap_cs_lib_twice_implies (swap_lib_extends sane y)) as ex; clear Heqex.
  revert ex; autorewrite with slow; introv.
  eapply type_extensionality_univi; eauto; apply lib_per_cond.
Qed.

Lemma implies_nuprl_swap_cs {o} :
  forall sw lib (t1 t2 : @CTerm o) e,
    sane_swapping sw
    -> nuprl lib t1 t2 e
    -> nuprl
         (swap_cs_lib sw lib)
         (swap_cs_cterm sw t1)
         (swap_cs_cterm sw t2)
         (swap_cs_per sw e).
Proof.
  introv sane n.
  unfold nuprl in *.
  apply implies_close_swap_cs; auto; eauto 3 with slow.
  introv u; apply implies_univ_swap_cs; auto.
Qed.

Fixpoint pre_replace_cs_entry {o} (lib : @plibrary o) name e : plibrary :=
  match lib with
  | [] => []
  | lib_cs name' e' :: entries =>
    if choice_sequence_name_deq name name' then
      lib_cs name e :: entries
    else lib_cs name' e' :: pre_replace_cs_entry entries name e
  | x :: entries => x :: pre_replace_cs_entry entries name e
  end.

Definition replace_cs_entry {o} (lib : @library o) name e : library :=
  MkLib (pre_replace_cs_entry lib name e) (lib_cond lib).

Lemma pre_replace_cs_entry_if_find_cs_in {o} :
  forall name (lib : @plibrary o) e,
    find_cs lib name = Some e
    -> pre_replace_cs_entry lib name e = lib.
Proof.
  induction lib; introv h; simpl in *; ginv.
  destruct a; simpl in *; boolvar; subst; ginv; tcsp;
    try (complete(rewrite IHlib; auto)).
Qed.

Lemma replace_cs_entry_if_find_cs_in {o} :
  forall name (lib : @library o) e,
    find_cs lib name = Some e
    -> replace_cs_entry lib name e = lib.
Proof.
  introv fcs; destruct lib as [lib cond]; simpl in *.
  unfold replace_cs_entry; simpl; f_equal.
  apply pre_replace_cs_entry_if_find_cs_in; auto.
Qed.

Lemma add_choice_preserves_find_none_rev {o} :
  forall name name' v (lib : @plibrary o) n restr lib',
    add_choice name v lib = Some (n, restr, lib')
    -> find_cs lib' name' = None
    -> find_cs lib name' = None.
Proof.
  induction lib; introv addc fcs; simpl in *; ginv.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp.

  { destruct entry; simpl in *; ginv.
    inversion addc; subst; clear addc; simpl in *; boolvar; tcsp. }

  { destruct entry; simpl in *; tcsp.
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; subst; tcsp.
    inversion addc; clear addc; subst; simpl in *; boolvar; tcsp. }

  { destruct entry; simpl in *; ginv.
    inversion addc; subst; clear addc; simpl in *; boolvar; tcsp. }

  { destruct entry; simpl in *; tcsp.
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; subst; tcsp.
    inversion addc; clear addc; subst; simpl in *; boolvar; tcsp.
    eapply IHlib; eauto. }

  { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; subst; tcsp.
    inversion addc; clear addc; subst; simpl in *; boolvar; tcsp.
    eapply IHlib; eauto. }
Qed.
Hint Resolve add_choice_preserves_find_none_rev : slow.

Lemma add_one_choice_preserves_find_none_rev {o} :
  forall name name' v (lib : @library o) n restr lib',
    add_one_choice name v lib = Some (n, restr, lib')
    -> find_cs lib' name' = None
    -> find_cs lib name' = None.
Proof.
  introv h fcs.
  destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve add_one_choice_preserves_find_none_rev : slow.

Lemma lib_extends_find_none_left_implies {o} :
  forall name (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> find_cs lib2 name = None
    -> find_cs lib1 name = None.
Proof.
  introv ext; lib_ext_ind ext Case; introv fcs; simpl in *; boolvar; subst; tcsp.
Qed.
Hint Resolve lib_extends_find_none_left_implies : slow.

Lemma not_in_lib_implies_find_cs_none {o} :
  forall name (lib : @plibrary o),
    !in_lib (entry_name_cs name) lib
    -> find_cs lib name = None.
Proof.
  introv h.
  remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; auto.
  destruct h; unfold in_lib.
  exists (lib_cs name c); dands; simpl; eauto 3 with slow.
Qed.
Hint Resolve not_in_lib_implies_find_cs_none : slow.

Definition add_choice_to_cs_entry {o} (e : @ChoiceSeqEntry o) c : ChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr => MkChoiceSeqEntry _ (snoc vals c) restr
  end.

Definition add_choices_to_cs_entry {o} (e : @ChoiceSeqEntry o) cs : ChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr => MkChoiceSeqEntry _ (vals ++ cs) restr
  end.

Lemma add_choice_preserves_find_some_rev {o} :
  forall name name' v (lib : @plibrary o) n restr lib' e,
    add_choice name v lib = Some (n, restr, lib')
    -> find_cs lib' name' = Some e
    -> exists e',
        find_cs lib name' = Some e'
        /\ ((name = name' /\ e = add_choice_to_cs_entry e' v)
            \/ name <> name' /\ e = e').
Proof.
  induction lib; introv addc fcs; simpl in *; ginv.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp.

  { destruct entry; simpl in *; ginv.
    inversion addc; subst; clear addc; simpl in *; boolvar; tcsp; GC.
    inversion fcs; subst; clear fcs; simpl in *.
    eexists; dands; eauto. }

  { destruct entry; simpl in *; tcsp.
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; subst; tcsp.
    inversion addc; clear addc; subst; simpl in *; boolvar; tcsp; GC.
    inversion fcs; subst; clear fcs; simpl in *; tcsp.
    eexists; dands; eauto. }

  { destruct entry; simpl in *; ginv.
    inversion addc; subst; clear addc; simpl in *; boolvar; tcsp; GC.
    eexists; dands; eauto. }

  { destruct entry; simpl in *; tcsp.
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; subst; tcsp.
    inversion addc; clear addc; subst; simpl in *; boolvar; tcsp.
    eapply IHlib; eauto. }

  { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; subst; tcsp.
    inversion addc; clear addc; subst; simpl in *; boolvar; tcsp.
    eapply IHlib; eauto. }
Qed.

Lemma add_one_choice_preserves_find_some_rev {o} :
  forall name name' v (lib : @library o) n restr lib' e,
    add_one_choice name v lib = Some (n, restr, lib')
    -> find_cs lib' name' = Some e
    -> exists e',
        find_cs lib name' = Some e'
        /\ ((name = name' /\ e = add_choice_to_cs_entry e' v)
            \/ name <> name' /\ e = e').
Proof.
  introv h fcs.
  destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv; simpl in *.
  eapply add_choice_preserves_find_some_rev in Heqaddc; eauto.
Qed.

Lemma entry_extends_add_choice_to_cs_entry {o} :
  forall name (e : @ChoiceSeqEntry o) v,
    entry_extends (lib_cs name (add_choice_to_cs_entry e v))
                  (lib_cs name e).
Proof.
  introv; unfold add_choice_to_cs_entry; destruct e as [vals restr]; simpl.
  rewrite snoc_as_append; eauto.
Qed.
Hint Resolve entry_extends_add_choice_to_cs_entry : slow.

Inductive satisfy_restriction {o} : @ChoiceSeqEntry o -> ChoiceSeqVals -> Prop :=
| sat_res_nil : forall (e : ChoiceSeqEntry), satisfy_restriction e []
| sat_res_cons :
    forall vals restr v l,
      satisfies_restriction (length (vals ++ l)) v restr
      -> satisfy_restriction (MkChoiceSeqEntry _ vals restr) l
      -> satisfy_restriction (MkChoiceSeqEntry _ vals restr) (snoc l v).
Hint Constructors satisfy_restriction.

Lemma add_choices_to_cs_entry_nil {o} :
  forall (e : @ChoiceSeqEntry o), add_choices_to_cs_entry e [] = e.
Proof.
  destruct e; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @add_choices_to_cs_entry_nil : slow.

Lemma add_choices_to_cs_entry_twice {o} :
  forall (e : @ChoiceSeqEntry o) vals1 vals2,
    add_choices_to_cs_entry (add_choices_to_cs_entry e vals1) vals2
    = add_choices_to_cs_entry e (vals1 ++ vals2).
Proof.
  introv; destruct e; simpl; rewrite app_assoc; auto.
Qed.
Hint Rewrite @add_choices_to_cs_entry_twice : slow.

Lemma satisfy_restriction_app {o} :
  forall (e : @ChoiceSeqEntry o) vals1 vals2,
    satisfy_restriction (add_choices_to_cs_entry e vals1) vals2
    -> satisfy_restriction e vals1
    -> satisfy_restriction e (vals1 ++ vals2).
Proof.
  introv sata satb.
  revert dependent e.
  revert dependent vals1.
  induction vals2 using rev_list_ind; introv sata satb; autorewrite with slow in *; auto.
  rewrite snoc_append_l.
  inversion sata as [|? ? ? ? sata' satb' satc' x]; clear sata;subst; tcsp;
    try (complete (destruct vals2; simpl in *; ginv)).
  apply snoc_inj in x; repnd; subst.
  destruct e as [vs rs]; simpl in *; ginv; simpl in *.
  econstructor; eauto.
  rewrite app_assoc; auto.
Qed.
Hint Resolve satisfy_restriction_app : slow.

Lemma add_choices_to_cs_entry_sing {o} :
  forall (e : @ChoiceSeqEntry o) v,
    add_choices_to_cs_entry e [v]
    = add_choice_to_cs_entry e v.
Proof.
  destruct e; introv; simpl; rewrite snoc_as_append; auto.
Qed.
Hint Rewrite @add_choices_to_cs_entry_sing : slow.

Lemma find_add_choice_implies {o} :
  forall name v (lib : @plibrary o) n restr lib' e,
    add_choice name v lib = Some (n, restr, lib')
    -> find_cs lib name = Some e
    -> cse_restriction e = restr /\ n = length (cse_vals e).
Proof.
  induction lib; introv addc fcs; simpl in *; ginv.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp.

  { destruct entry as [vals restr']; simpl in *; ginv; subst; simpl in *.
    inversion addc; subst; clear addc; tcsp. }

  { destruct entry as [vals restr']; simpl in *; ginv.
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; simpl in *; ginv; tcsp.
    inversion addc; subst; simpl in *; tcsp; clear addc.
    eapply IHlib; eauto. }

  { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; simpl in *; ginv; tcsp.
    inversion addc; subst; simpl in *; tcsp; clear addc.
    eapply IHlib; eauto. }
Qed.

Lemma find_add_one_choice_implies {o} :
  forall name v (lib : @library o) n restr lib' e,
    add_one_choice name v lib = Some (n, restr, lib')
    -> find_cs lib name = Some e
    -> cse_restriction e = restr /\ n = length (cse_vals e).
Proof.
  introv h fcs; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv.
  eapply find_add_choice_implies; eauto.
Qed.

Lemma satisfy_restriction_sing {o} :
  forall (e : @ChoiceSeqEntry o) v,
    satisfy_restriction e [v]
    <-> satisfies_restriction (length (cse_vals e)) v (cse_restriction e).
Proof.
  introv; split; intro h.
  { inversion h; subst; simpl in *.
    repeat (destruct l; simpl in *; ginv).
    autorewrite with slow in *; tcsp. }
  { destruct e as [vals restr]; simpl in *.
    rewrite singleton_as_snoc; constructor; simpl; eauto.
    autorewrite with slow; auto. }
Qed.
Hint Rewrite @satisfy_restriction_sing : slow.

Lemma lib_extends_find_some_left_implies {o} :
  forall name e (lib2 lib1 : @library o),
    find_cs lib2 name = Some e
    -> lib_extends lib2 lib1
    -> (find_cs lib1 name = None
        \/ exists vals e',
           find_cs lib1 name = Some e'
           /\ e = add_choices_to_cs_entry e' vals
           /\ satisfy_restriction e' vals
           /\ lib_cond_sat_choices lib1 vals).
Proof.
  introv fcs ext; revert dependent e.
  lib_ext_ind ext Case; introv fcs; tcsp.

  { Case "lib_ext_refl".
    right; exists ([] : @ChoiceSeqVals o) e; dands; auto; eauto 3 with slow.
    autorewrite with slow; auto. }

  { Case "lib_ext_trans".
    pose proof (IHext1 e) as IHext1; autodimp IHext1 hyp.
    repndors; exrepnd; subst; tcsp.

    { eapply lib_extends_find_none_left_implies in IHext1; eauto. }

    pose proof (IHext2 e') as IHext2; autodimp IHext2 hyp.
    repndors; exrepnd; subst; tcsp.
    right.
    exists (vals0 ++ vals) e'0; autorewrite with slow; dands; auto; eauto 3 with slow. }

  { Case "lib_ext_new_abs".
    right; exists ([] : @ChoiceSeqVals o) e; dands; auto; eauto 3 with slow.
    autorewrite with slow; auto. }

  { Case "lib_ext_new_cs".
    boolvar; subst; tcsp; ginv; simpl in *; tcsp.
    { left; eauto 3 with slow. }
    { right; exists ([] : @ChoiceSeqVals o) e; autorewrite with slow; dands; eauto 3 with slow. } }

  { Case "lib_ext_cs".
    eapply add_one_choice_preserves_find_some_rev in fcs; eauto.
    exrepnd; right.
    repndors; repnd; subst.
    { exists ([v] : @ChoiceSeqVals o) e'; autorewrite with slow; dands; auto; eauto 3 with slow.
      eapply find_add_one_choice_implies in addc; eauto; repnd; subst.
      destruct e' as [vs rs]; simpl in *; subst; auto. }
    { exists ([] : @ChoiceSeqVals o) e'; autorewrite with slow; dands; auto; eauto 3 with slow. } }

(*  { Case "lib_ext_law".
    eapply add_choice_preserves_find_some_rev in fcs; eauto.
    exrepnd; right.
    repndors; repnd; subst.
    { exists ([f n] : @ChoiceSeqVals o) e'; autorewrite with slow; dands; auto; eauto 3 with slow.
      eapply find_add_choice_implies in addc; eauto; repnd; subst.
      destruct e' as [vs rs]; simpl in *; subst; simpl; auto. }
    { exists ([] : @ChoiceSeqVals o) e'; autorewrite with slow; dands; auto; eauto 3 with slow. } }

  { Case "lib_ext_res".
    eapply add_choice_preserves_find_some_rev in fcs; eauto.
    exrepnd; right.
    repndors; repnd; subst.
    { exists ([v] : @ChoiceSeqVals o) e'; autorewrite with slow; dands; auto; eauto 3 with slow.
      eapply find_add_choice_implies in addc; eauto; repnd; subst.
      destruct e' as [vs rs]; simpl in *; subst; simpl; auto. }
    { exists ([] : @ChoiceSeqVals o) e'; autorewrite with slow; dands; auto; eauto 3 with slow. } }*)
Qed.

Lemma pre_replace_cs_entry_if_find_none {o} :
  forall (lib : @plibrary o) name e,
    find_cs lib name = None
    -> pre_replace_cs_entry lib name e = lib.
Proof.
  induction lib; introv fcs; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; subst; tcsp;
    try (complete (rewrite IHlib; auto)).
Qed.

Lemma replace_cs_entry_if_find_none {o} :
  forall (lib : @library o) name e,
    find_cs lib name = None
    -> replace_cs_entry lib name e = lib.
Proof.
  introv fcs; destruct lib as [lib cond]; unfold replace_cs_entry; simpl in *.
  f_equal; apply pre_replace_cs_entry_if_find_none; auto.
Qed.

Lemma pre_replace_cs_entry_app_right {o} :
  forall (lib1 lib2 : @plibrary o) name e,
    ~ in_lib (entry_name_cs name) lib1
    -> pre_replace_cs_entry (lib1 ++ lib2) name e
       = lib1 ++ pre_replace_cs_entry lib2 name e.
Proof.
  induction lib1; introv ni; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; simpl in *; subst; tcsp.

  { destruct ni; eexists; simpl; dands; eauto; simpl; auto. }

  { rewrite IHlib1; auto.
    rewrite in_lib_cons in ni; simpl in *.
    apply not_or in ni; tcsp. }

  { rewrite IHlib1; auto.
    rewrite in_lib_cons in ni; simpl in *.
    apply not_or in ni; tcsp. }
Qed.

Lemma replace_cs_entry_app_right {o} :
  forall cond (lib1 lib2 : @plibrary o) name e,
    ~ in_lib (entry_name_cs name) lib1
    -> replace_cs_entry (MkLib (lib1 ++ lib2) cond) name e
       = MkLib (lib1 ++ pre_replace_cs_entry lib2 name e) cond.
Proof.
  introv ni; simpl; unfold replace_cs_entry; simpl; f_equal.
  apply pre_replace_cs_entry_app_right; auto.
Qed.

Lemma lib_extends_middle_add0 {o} :
  forall (cond : LibCond) (lib1 lib2 : @plibrary o) name e vals,
    (forall v, LIn v vals -> cond (get_cterm v))
    -> satisfy_restriction e vals
    -> ~in_lib (entry_name_cs name) lib1
    -> lib_extends
         (MkLib (lib1 ++ lib_cs name (add_choices_to_cs_entry e vals) :: lib2) cond)
         (MkLib (lib1 ++ lib_cs name e :: lib2) cond).
Proof.
  introv.
  revert lib1 lib2 e.
  induction vals using rev_list_ind; introv scs sat ni; simpl in *; autorewrite with slow in *; auto.
  destruct e as [vs rs]; simpl in *.
  rewrite snoc_append_l.
  inversion sat as [|? ? ? ? sata satb xx xxx]; try (complete (destruct vals; simpl in *; ginv)); subst.
  apply snoc_inj in xxx; repnd; subst.
  pose proof (IHvals lib1 lib2 (MkChoiceSeqEntry _ vs rs)) as IHvals.
  repeat (autodimp IHvals hyp).
  { introv i; apply scs; apply in_snoc; tcsp. }
  eapply lib_extends_trans;[|exact IHvals]; clear IHvals.
  simpl.
  destruct rs; simpl in *.

  { eapply (lib_extends_cs _ name a (length (vs ++ vals)) typ); auto.
    { rewrite add_one_choice_if_not_in_left0; auto. }
    simpl; apply scs; apply in_snoc; tcsp. }
Qed.

Lemma lib_extends_middle_add {o} :
  forall (lib1 lib2 : @library o) name e vals,
    lib_cond_sat_choices lib2 vals
    -> satisfy_restriction e vals
    -> ~in_lib (entry_name_cs name) lib1
    -> lib_extends
         (add_mid_entry lib1 (lib_cs name (add_choices_to_cs_entry e vals)) lib2)
         (add_mid_entry lib1 (lib_cs name e) lib2).
Proof.
  introv sata satb ni.
  apply lib_extends_middle_add0; auto.
Qed.

Lemma in_lib_pre_replace_cs_entry_iff {o} :
  forall n (lib : @plibrary o) name e,
    in_lib n (pre_replace_cs_entry lib name e)
    <-> in_lib n lib.
Proof.
  induction lib; introv; simpl; tcsp.
  destruct a; boolvar; simpl in *; subst; tcsp;
    repeat rewrite in_lib_cons; simpl; tcsp;
      try (complete (rewrite IHlib; tcsp)).
Qed.
Hint Rewrite @in_lib_pre_replace_cs_entry_iff : slow.

Lemma pre_replace_cs_entry_not_in {o} :
  forall (lib : @plibrary o) name e,
    ~ in_lib (entry_name_cs name) lib
    -> pre_replace_cs_entry lib name e = lib.
Proof.
  introv ni.
  rewrite pre_replace_cs_entry_if_find_none; eauto 3 with slow.
Qed.

Lemma replace_cs_entry_not_in {o} :
  forall (lib : @library o) name e,
    ~ in_lib (entry_name_cs name) lib
    -> replace_cs_entry lib name e = lib.
Proof.
  introv ni; destruct lib as [lib cond]; unfold replace_cs_entry; simpl in *; f_equal.
  apply pre_replace_cs_entry_if_find_none; auto; eauto 3 with slow.
Qed.

Definition has_compatible_restriction {o} (lib : @library o) name e :=
  exists x,
    find_cs lib name = Some x
    /\ cse_restriction x = cse_restriction e.

Lemma lib_extends_preserves_has_compatible_restriction {o} :
  forall (lib1 lib2 : @library o) name e,
    lib_extends lib2 lib1
    -> has_compatible_restriction lib1 name e
    -> has_compatible_restriction lib2 name e.
Proof.
  introv ext comp.
  unfold has_compatible_restriction in *; exrepnd.
  eapply lib_extends_preserves_find_cs in comp1; eauto; exrepnd.
  eexists; dands; eauto.
Qed.
Hint Resolve lib_extends_preserves_has_compatible_restriction : slow.

Lemma has_compatible_restriction_implies_in_lib {o} :
  forall (lib : @library o) name e,
    has_compatible_restriction lib name e
    -> in_lib (entry_name_cs name) lib.
Proof.
  introv comp; unfold has_compatible_restriction in *; exrepnd.
  apply find_cs_some_implies_list_in in comp1.
  eexists; dands; eauto; simpl; auto.
Qed.
Hint Resolve has_compatible_restriction_implies_in_lib : slow.

Lemma pre_replace_cs_entry_add_choice_same {o} :
  forall name v (lib : @plibrary o) n restr lib' e,
    add_choice name v lib = Some (n, restr, lib')
    -> pre_replace_cs_entry lib' name e = pre_replace_cs_entry lib name e.
Proof.
  induction lib; introv addc; simpl in *; ginv.
  destruct a; simpl in *; boolvar; subst; tcsp.

  { destruct entry; simpl in *; ginv.
    inversion addc; subst; clear addc; simpl in *; boolvar; subst; tcsp. }

  { destruct entry; simpl in *.
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; tcsp.
    inversion addc; subst; clear addc; simpl in *; boolvar; tcsp.
    pose proof (IHlib n restr p e) as IHlib; autodimp IHlib hyp; try congruence. }

  { remember (add_choice name v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; tcsp.
    inversion addc; subst; clear addc; simpl in *; boolvar; tcsp.
    pose proof (IHlib n restr p e) as IHlib; autodimp IHlib hyp; try congruence. }
Qed.

Lemma replace_cs_entry_add_choice_same {o} :
  forall name v (lib : @library o) n restr lib' e,
    add_one_choice name v lib = Some (n, restr, lib')
    -> replace_cs_entry lib' name e = replace_cs_entry lib name e.
Proof.
  introv h; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv.
  unfold replace_cs_entry; simpl; f_equal.
  eapply pre_replace_cs_entry_add_choice_same in Heqaddc; eauto.
Qed.

Lemma pre_replace_cs_entry_add_choice_diff {o} :
  forall name' name v (lib : @plibrary o) n restr lib' e,
    name <> name'
    -> add_choice name' v lib = Some (n, restr, lib')
    -> add_choice name' v (pre_replace_cs_entry lib name e)
       = Some (n, restr, pre_replace_cs_entry lib' name e).
Proof.
  induction lib; introv diff addc; simpl in *; ginv.
  destruct a; simpl in *; boolvar; subst; tcsp; simpl in *; ginv; simpl in *.

  { destruct e; simpl in *; boolvar; subst; tcsp.
    destruct entry as [vals1 restr1]; simpl in *; tcsp.
    remember (add_choice name' v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; ginv; GC.
    inversion addc; subst; clear addc; simpl in *; boolvar; subst; tcsp. }

  { destruct entry as [vals1 restr1]; simpl in *; ginv.
    boolvar; tcsp; subst; GC.
    inversion addc; subst; clear addc; simpl in *; boolvar; subst; tcsp. }

  { destruct entry as [vals1 restr1]; simpl in *; tcsp.
    boolvar; subst; tcsp; GC.
    remember (add_choice name' v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; ginv; GC.
    inversion addc; subst; clear addc; simpl in *; boolvar; subst; tcsp; GC.
    pose proof (IHlib n restr p e) as IHlib; repeat (autodimp IHlib hyp).
    allrw; tcsp. }

  { remember (add_choice name' v lib) as addc'; symmetry in Heqaddc'.
    destruct addc'; repnd; ginv; GC.
    inversion addc; subst; clear addc; simpl in *; boolvar; subst; tcsp; GC.
    pose proof (IHlib n restr p e) as IHlib; repeat (autodimp IHlib hyp).
    allrw; tcsp. }
Qed.

Lemma replace_cs_entry_add_choice_diff {o} :
  forall name' name v (lib : @library o) n restr lib' e,
    name <> name'
    -> add_one_choice name' v lib = Some (n, restr, lib')
    -> add_one_choice name' v (replace_cs_entry lib name e)
       = Some (n, restr, replace_cs_entry lib' name e).
Proof.
  introv d h; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name' v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv.
  erewrite pre_replace_cs_entry_add_choice_diff; eauto; tcsp.
Qed.

Lemma in_lib_replace_cs_entry_iff {o} :
  forall n (lib : @library o) name e,
    in_lib n (replace_cs_entry lib name e)
    <-> in_lib n lib.
Proof.
  introv; destruct lib as [lib cond]; simpl; autorewrite with slow; tcsp.
Qed.
Hint Rewrite @in_lib_replace_cs_entry_iff : slow.

Lemma replace_cs_entry_add_new_abs {o} :
  forall op vars rhs correct (lib : @library o) name e,
    replace_cs_entry (add_new_abs op vars rhs correct lib) name e
    = add_new_abs op vars rhs correct (replace_cs_entry lib name e).
Proof.
  tcsp.
Qed.
Hint Rewrite @replace_cs_entry_add_new_abs : slow.

Lemma replace_cs_entry_add_new_cs {o} :
  forall name' restr (lib : @library o) name e,
    replace_cs_entry (add_new_cs name' restr lib) name e
    = if choice_sequence_name_deq name name'
      then add_one_entry (lib_cs name e) lib
      else add_new_cs name' restr (replace_cs_entry lib name e).
Proof.
  introv; destruct lib as [lib cond]; simpl.
  unfold replace_cs_entry; simpl; boolvar; subst; tcsp.
Qed.
Hint Rewrite @replace_cs_entry_add_new_cs : slow.

Lemma implies_lib_extends_replace_cs_entry {o} :
  forall (lib1 lib2 : @library o) name e,
    has_compatible_restriction lib1 name e
    -> lib_extends lib2 lib1
    -> lib_extends (replace_cs_entry lib2 name e) (replace_cs_entry lib1 name e).
Proof.
  introv comp ext.
  lib_ext_ind ext Case; introv; tcsp.

  { Case "lib_ext_trans".
    repeat (autodimp IHext1 hyp); eauto 3 with slow. }

  { Case "lib_ext_new_abs".
    autorewrite with slow.
    eapply lib_extends_new_abs; tcsp.
    intro xx; autorewrite with slow in *; tcsp. }

  { Case "lib_ext_new_cs".
    autorewrite with slow.
    boolvar; subst; tcsp.
    { apply has_compatible_restriction_implies_in_lib in comp; tcsp. }
    apply lib_extends_new_cs; auto.
    introv xx; autorewrite with slow in xx; tcsp. }

  { Case "lib_ext_cs".
    destruct (choice_sequence_name_deq name0 name); subst.
    { erewrite replace_cs_entry_add_choice_same; eauto. }
    eapply (lib_extends_cs _ name0); eauto.
    apply replace_cs_entry_add_choice_diff; auto. }

(*  { Case "lib_ext_law".
    destruct (choice_sequence_name_deq name0 name); subst.
    { erewrite pre_replace_cs_entry_add_choice_same; eauto. }
    eapply (lib_extends_law _ name0 _ n f); eauto.
    apply pre_replace_cs_entry_add_choice_diff; auto. }

  { Case "lib_ext_res".
    destruct (choice_sequence_name_deq name0 name); subst.
    { erewrite pre_replace_cs_entry_add_choice_same; eauto. }
    eapply (lib_extends_res _ name0); eauto.
    apply pre_replace_cs_entry_add_choice_diff; auto. }*)
Qed.

Lemma find_cs_implies_has_compatible_restriction {o} :
  forall (lib : @library o) name e,
    find_cs lib name = Some e
    -> has_compatible_restriction lib name e.
Proof.
  introv fcs.
  unfold has_compatible_restriction; eexists; dands; eauto.
Qed.
Hint Resolve find_cs_implies_has_compatible_restriction : slow.

Lemma res_add_choices_to_cs_entry {o} :
  forall (e : @ChoiceSeqEntry o) vals,
    cse_restriction (add_choices_to_cs_entry e vals) = cse_restriction e.
Proof.
  introv; destruct e; simpl; auto.
Qed.
Hint Rewrite @res_add_choices_to_cs_entry : slow.

Lemma implies_has_compatible_restriction_add_choices {o} :
  forall (lib : @library o) name e vals,
    has_compatible_restriction lib name e
    -> has_compatible_restriction lib name (add_choices_to_cs_entry e vals).
Proof.
  introv comp.
  unfold has_compatible_restriction in *; exrepnd.
  eexists; dands; eauto; simpl; autorewrite with slow; auto.
Qed.
Hint Resolve implies_has_compatible_restriction_add_choices : slow.

Lemma pre_replace_cs_entry_if_add_choice {o} :
  forall name name' v (lib : @plibrary o) n restr lib' e,
    add_choice name' v lib = Some (n, restr, lib')
    -> find_cs lib' name = Some e
    -> if choice_sequence_name_deq name' name
       then pre_replace_cs_entry lib name e = lib'
       else pre_replace_cs_entry lib name e = lib.
Proof.
  induction lib; introv addc fcs; simpl in *; ginv.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp; GC;
    try (complete (try (destruct entry as [vals1 restr1]; simpl in *);
                   try (first [remember (add_choice name' v lib) as addc'
                              |remember (add_choice name v lib) as addc'];
                        symmetry in Heqaddc';
                        destruct addc'; repnd; simpl in *; tcsp; ginv);
                   inversion addc; subst; clear addc; simpl in *; boolvar; subst; tcsp; GC;
                   try (complete (erewrite IHlib; eauto));
                   try (complete (inversion fcs; subst; auto)))).

  { destruct entry as [vals1 restr1]; simpl in *.
    inversion addc; subst; clear addc; simpl in *; boolvar; subst; tcsp; GC.
    rewrite pre_replace_cs_entry_if_find_cs_in; auto. }
Qed.

Lemma replace_cs_entry_if_add_one_choice {o} :
  forall name name' v (lib : @library o) n restr lib' e,
    add_one_choice name' v lib = Some (n, restr, lib')
    -> find_cs lib' name = Some e
    -> if choice_sequence_name_deq name' name
       then replace_cs_entry lib name e = lib'
       else replace_cs_entry lib name e = lib.
Proof.
  introv h fcs; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name' v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv.
  eapply pre_replace_cs_entry_if_add_choice in Heqaddc; eauto.
  unfold replace_cs_entry; simpl; boolvar; subst; tcsp; try congruence.
Qed.

Lemma lib_extends_pre_replace_cs_entry {o} :
  forall name e (lib2 lib1 : @library o),
    find_cs lib2 name = Some e
    -> lib_extends lib2 lib1
    -> lib_extends (replace_cs_entry lib1 name e) lib1
       /\ lib_extends lib2 (replace_cs_entry lib1 name e).
Proof.
  introv fcs ext; revert dependent e.
  lib_ext_ind ext Case; introv fcs; tcsp.

  { Case "lib_ext_refl".
    rewrite replace_cs_entry_if_find_cs_in; auto. }

  { Case "lib_ext_trans".
    pose proof (IHext1 e) as IHext1; repeat (autodimp IHext1 hyp); repnd.
    pose proof (lib_extends_find_some_left_implies name e lib1 lib2) as q.
    repeat (autodimp q hyp).
    repndors; exrepnd; subst.

    { rewrite replace_cs_entry_if_find_none in IHext0; auto.
      rewrite replace_cs_entry_if_find_none in IHext1; auto.
      pose proof (lib_extends_find_none_left_implies name lib2 lib3) as h.
      repeat (autodimp h hyp).
      rewrite replace_cs_entry_if_find_none; auto.
      dands; eauto 3 with slow. }

    pose proof (IHext2 e') as IHext2.
    repeat (autodimp IHext2 hyp); repnd.
    dands.

    { eapply lib_extends_trans;[|eauto].

      pose proof (lib_extends_find_some_left_implies name e' lib2 lib3) as w.
      repeat (autodimp w hyp).
      repndors; exrepnd; subst.

      { repeat (rewrite replace_cs_entry_if_find_none; auto). }

      apply find_cs_some_implies_entry_in_library in w0.
      apply entry_in_library_split in w0; exrepnd; subst; simpl in *.
      destruct lib3 as [lib3 cond3]; simpl in *; subst; simpl in *.
      repeat (rewrite replace_cs_entry_app_right; auto; simpl; boolvar; tcsp; GC).
      apply lib_extends_middle_add0; auto.
      introv i; apply q1 in i.
      apply lib_extends_implies_same_conds in ext2; unfold same_conds in *; simpl in *; subst; auto. }

    eapply lib_extends_trans;[eauto|].

    pose proof (lib_extends_find_some_left_implies name e' lib2 lib3) as w.
    repeat (autodimp w hyp).
    repndors; exrepnd; subst.

    { repeat (rewrite (replace_cs_entry_if_find_none lib3); auto).
      rewrite (replace_cs_entry_if_find_none lib3) in IHext2; auto.
      eapply lib_extends_trans;[|eauto]; auto. }

    apply implies_lib_extends_replace_cs_entry; auto.
    autorewrite with slow; eauto 3 with slow. }

  { Case "lib_ext_new_abs".
    rewrite replace_cs_entry_if_find_cs_in; auto. }

  { Case "lib_ext_new_cs".
    boolvar; subst; tcsp; ginv; simpl in *; tcsp.
    { rewrite replace_cs_entry_not_in; auto. }
    rewrite replace_cs_entry_if_find_cs_in; auto. }

  { Case "lib_ext_cs".
    dup addc as w.
    eapply replace_cs_entry_if_add_one_choice in w; eauto.
    boolvar; allrw; dands; eauto 3 with slow. }

(*  { Case "lib_ext_law".
    dup addc as w.
    eapply pre_replace_cs_entry_if_add_choice in w; eauto.
    boolvar; allrw; dands; eauto 3 with slow. }

  { Case "lib_ext_res".
    dup addc as w.
    eapply pre_replace_cs_entry_if_add_choice in w; eauto.
    boolvar; allrw; dands; eauto 3 with slow. }*)
Qed.

Definition firstn_cs_entry {o} n (e : @ChoiceSeqEntry o) :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    MkChoiceSeqEntry _ (firstn n vals) restr
  end.

Definition is_nat_cs (name : choice_sequence_name) :=
  match csn_kind name with
  | cs_kind_nat 0 => True
  | _ => False
  end.

Lemma lib_depth_0 {o} :
  forall name (lib : @plibrary o),
    is_nat_cs name
    -> lib_depth lib = 0
    -> forall e,
        find_cs lib name = Some e
        -> length (cse_vals e) = 0.
Proof.
  induction lib; introv isn len h; simpl in *; auto; ginv.
  destruct a; simpl in *; boolvar; subst; tcsp; ginv.

  { remember (length (cse_vals e)) as xa; destruct xa; simpl in *; auto.
    destruct name0 as [n k], k; unfold is_nat_cs in *; simpl in *; tcsp.
    destruct n0; simpl in *; tcsp.
    remember (lib_depth lib) as ls; symmetry in Heqls; destruct ls; ginv. }

  { remember (lib_depth lib) as ls; symmetry in Heqls; destruct ls; simpl in *; tcsp.
    clear IHlib.
    pose proof (Max.le_max_r (length (cse_vals entry)) (S ls)) as q.
    rewrite len in q; omega. }
Qed.

Inductive cs_entry_extends {o} : @ChoiceSeqEntry o -> @ChoiceSeqEntry o -> Prop :=
| cs_entry_ext :
    forall vals vals' restr,
      cs_entry_extends
        (MkChoiceSeqEntry _ (vals ++ vals') restr)
        (MkChoiceSeqEntry _ vals restr).
Hint Constructors cs_entry_extends.

Definition cs_entry_between {o} name (e2 e : @ChoiceSeqEntry o) (lib : @library o) :=
  forall e1,
    find_cs lib name = Some e1
    -> (cs_entry_extends e2 e /\ cs_entry_extends e e1).

Lemma app_right_is_nil : forall {A} (l : list A) k, l = l ++ k -> k = [].
Proof.
  induction l; simpl; introv h; auto.
  inversion h; eapply IHl; auto.
Qed.

Lemma cs_entry_extends_implies_eq {o} :
  forall (e e' : @ChoiceSeqEntry o),
    cs_entry_extends e e'
    -> cs_entry_extends e' e
    -> e = e'.
Proof.
  introv exta extb.
  inversion exta; subst; clear exta.
  inversion extb as [? ? ? xx xxx]; subst; clear extb.
  rewrite <- app_assoc in xxx; apply app_right_is_nil in xxx.
  apply app_eq_nil in xxx; repnd; subst; simpl; autorewrite with slow; auto.
Qed.

Lemma find_cs_cs_entry_between_implies {o} :
  forall (lib : @library o) name e e',
    find_cs lib name = Some e
    -> cs_entry_between name e e' lib
    -> e = e'.
Proof.
  introv fcs betw.
  applydup betw in fcs; repnd.
  apply cs_entry_extends_implies_eq; auto.
Qed.

Lemma choice_sequence_satisfies_restriction_app_implies {o} :
  forall (vals vals' : @ChoiceSeqVals o) restr,
    choice_sequence_satisfies_restriction (vals ++ vals') restr
    -> choice_sequence_satisfies_restriction vals restr.
Proof.
  introv sat.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr; simpl in *; simpl in *; introv sel.
  { apply sat; rewrite select_app_l; auto; eauto 3 with slow. }
(*  { rewrite <- sat; try rewrite length_app; try omega.
    rewrite select_app_l; auto; eauto 3 with slow. }
  { apply sat; rewrite select_app_l; auto; eauto 3 with slow. }*)
Qed.
Hint Resolve choice_sequence_satisfies_restriction_app_implies : slow.

Lemma app_eq_app_implies :
  forall {A} (l1 l2 l3 l4 : list A),
    l1 ++ l2 = l3 ++ l4
    -> if le_dec (length l1) (length l3) then
         exists l,
           l2 = l ++ l4
           /\ l3 = l1 ++ l
       else
         exists l,
           l1 = l3 ++ l
           /\ l4 = l ++ l2.
Proof.
  induction l1; introv h; simpl in *; subst; tcsp.

  - exists l3; dands; auto.

  - boolvar.

    + destruct l3; simpl in *; ginv; try omega.
      apply le_S_n in l.
      inversion h; subst; clear h.
      match goal with
      | [ H : _ = _ |- _ ] => rename H into h
      end.
      apply IHl1 in h; boolvar; try omega.
      exrepnd; subst.
      exists l5; dands; auto.

    + assert (length l3 < S (length l1)) as q by omega; clear n.
      destruct l3; simpl in *; ginv.

      * exists (a :: l1); dands; auto.

      * inversion h; subst; clear h.
        match goal with
        | [ H : _ = _ |- _ ] => rename H into h
        end.
        apply IHl1 in h; boolvar; try omega.
        exrepnd; subst.
        exists l; dands; auto.
Qed.

Lemma lib_extends_pre_replace_cs_entry_app {o} :
  forall (lib1 lib2 : @library o) name vals1 vals2 vals3 restr,
    lib_extends lib2 lib1
    -> find_cs lib2 name = Some (MkChoiceSeqEntry _ (vals1 ++ vals2 ++ vals3) restr)
    -> find_cs lib1 name = Some (MkChoiceSeqEntry _ vals1 restr)
    -> lib_extends lib2 (replace_cs_entry lib1 name (MkChoiceSeqEntry _ (vals1 ++ vals2) restr)).
Proof.
  introv ext.
  revert vals1 vals2 vals3 restr.
  lib_ext_ind ext Case; introv fcs btw; tcsp.

  { Case "lib_ext_refl".
    rewrite fcs in btw; inversion btw as [xx]; subst; clear btw.
    symmetry in xx; apply app_right_is_nil in xx.
    apply app_eq_nil in xx; repnd; subst; autorewrite with slow in *.
    rewrite replace_cs_entry_if_find_cs_in; auto. }

  { Case "lib_ext_trans".
    dup btw as h.
    eapply lib_extends_preserves_find_cs in h; eauto; exrepnd.
    unfold choice_sequence_vals_extend in *; exrepnd; simpl in *; subst; simpl in *.
    dup h1 as q.
    eapply lib_extends_preserves_find_cs in q; eauto; exrepnd.
    unfold choice_sequence_vals_extend in *; exrepnd; simpl in *; subst; simpl in *.
    rewrite fcs in q1; inversion q1 as [xx]; clear q1.
    rewrite <- app_assoc in xx.
    apply app_inv_head in xx.
    apply app_eq_app_implies in xx; boolvar; exrepnd; subst; simpl in *.

    { pose proof (IHext1 (vals1 ++ vals2 ++ l0) vals4 [] restr) as IHext1.
      autorewrite with slow in IHext1.
      repeat rewrite <- app_assoc in IHext1.
      repeat (autodimp IHext1 hyp).
      pose proof (IHext2 vals1 vals2 l0 restr) as IHext2.
      autorewrite with slow in IHext2.
      repeat rewrite <- app_assoc in IHext2.
      repeat (autodimp IHext2 hyp).
      eapply lib_extends_trans;[|eauto]; auto. }

    { repeat rewrite <- app_assoc in fcs.
      pose proof (IHext1 (vals1 ++ vals) l vals3 restr) as IHext1.
      autorewrite with slow in *.
      repeat rewrite <- app_assoc in IHext1.
      repeat (autodimp IHext1 hyp).
      pose proof (IHext2 vals1 vals [] restr) as IHext2.
      autorewrite with slow in *.
      repeat rewrite <- app_assoc in IHext2.
      repeat (autodimp IHext2 hyp).
      eapply lib_extends_trans;[eauto|].
      apply implies_lib_extends_replace_cs_entry; eauto 3 with slow.
      eexists; dands; eauto. } }

  { Case "lib_ext_new_abs".
    rewrite fcs in btw; inversion btw as [xx]; clear btw.
    symmetry in xx; apply app_right_is_nil in xx.
    apply app_eq_nil in xx; repnd; subst; autorewrite with slow in *.
    rewrite replace_cs_entry_if_find_cs_in; auto. }

  { Case "lib_ext_new_cs".
    boolvar; subst; simpl in *; tcsp.
    { inversion fcs as [xx]; subst; clear fcs.
      symmetry in xx.
      repeat (apply app_eq_nil in xx; repnd; subst; autorewrite with slow in * ).
      rewrite replace_cs_entry_if_find_cs_in; auto. }
    rewrite fcs in btw; inversion btw as [xx]; clear btw.
    symmetry in xx; apply app_right_is_nil in xx.
    apply app_eq_nil in xx; repnd; subst; autorewrite with slow in *.
    rewrite replace_cs_entry_if_find_cs_in; auto. }

  { Case "lib_ext_cs".
    dup fcs as xx.
    eapply add_one_choice_preserves_find_some_rev in xx; eauto.
    exrepnd.
    rewrite xx1 in btw; ginv; simpl in *.
    repndors; repnd; subst; simpl in *.
    { inversion xx0 as [xx]; clear xx0.
      rewrite snoc_as_append in xx.
      apply app_inv_head in xx.
      destruct vals2; simpl in *; subst; ginv; autorewrite with slow in *.
      { rewrite replace_cs_entry_if_find_cs_in; eauto. }
      destruct vals2; simpl in *; ginv.
      eapply replace_cs_entry_if_add_one_choice in addc; eauto; boolvar; tcsp; GC.
      subst; simpl in *; eauto. }
    inversion xx0 as [xx]; clear xx0; symmetry in xx.
    apply app_right_is_nil in xx; apply app_eq_nil in xx; repnd; subst; autorewrite with slow in *.
    rewrite replace_cs_entry_if_find_cs_in; eauto. }

(*  { Case "lib_ext_law".
    dup fcs as xx.
    eapply add_choice_preserves_find_some_rev in xx; eauto.
    exrepnd.
    rewrite xx1 in btw; ginv; simpl in *.
    repndors; repnd; subst; simpl in *.
    { inversion xx0 as [xx]; clear xx0.
      rewrite snoc_as_append in xx.
      apply app_inv_head in xx.
      destruct vals2; simpl in *; subst; ginv; autorewrite with slow in *.
      { rewrite pre_replace_cs_entry_if_find_cs_in; eauto. }
      destruct vals2; simpl in *; ginv.
      eapply pre_replace_cs_entry_if_add_choice in addc; eauto; boolvar; tcsp; GC.
      subst; simpl in *; eauto. }
    inversion xx0 as [xx]; clear xx0; symmetry in xx.
    apply app_right_is_nil in xx; apply app_eq_nil in xx; repnd; subst; autorewrite with slow in *.
    rewrite pre_replace_cs_entry_if_find_cs_in; eauto. }

  { Case "lib_ext_res".
    dup fcs as xx.
    eapply add_choice_preserves_find_some_rev in xx; eauto.
    exrepnd.
    rewrite xx1 in btw; ginv; simpl in *.
    repndors; repnd; subst; simpl in *.
    { inversion xx0 as [xx]; clear xx0.
      rewrite snoc_as_append in xx.
      apply app_inv_head in xx.
      destruct vals2; simpl in *; subst; ginv; autorewrite with slow in *.
      { rewrite pre_replace_cs_entry_if_find_cs_in; eauto. }
      destruct vals2; simpl in *; ginv.
      eapply pre_replace_cs_entry_if_add_choice in addc; eauto; boolvar; tcsp; GC.
      subst; simpl in *; eauto. }
    inversion xx0 as [xx]; clear xx0; symmetry in xx.
    apply app_right_is_nil in xx; apply app_eq_nil in xx; repnd; subst; autorewrite with slow in *.
    rewrite pre_replace_cs_entry_if_find_cs_in; eauto. }*)
Qed.

Lemma find_cs_implies_lib_extends_pre_replace_cs_entry_app_left {o} :
  forall name (vals vals' : @ChoiceSeqVals o) restr (lib : library),
    lib_cond_sat_choices lib (vals ++ vals')
    -> correct_restriction name restr
    -> choice_sequence_satisfies_restriction (vals ++ vals') restr
    -> find_cs lib name = Some (MkChoiceSeqEntry _ vals restr)
    -> lib_extends (replace_cs_entry lib name (MkChoiceSeqEntry _ (vals ++ vals') restr)) lib.
Proof.
  introv sata cor sat fcs.
  apply find_cs_some_implies_entry_in_library in fcs.
  apply entry_in_library_split in fcs; exrepnd; subst; simpl in *.
  destruct lib as [lib cond]; simpl in *; subst; simpl in *.
  repeat (rewrite replace_cs_entry_app_right; auto; simpl; boolvar; tcsp; GC).
  apply lib_extends_middle0; simpl; auto.
Qed.

Lemma lib_cond_sat_choices_app_sym {o} :
  forall (lib : @library o) vals1 vals2,
    lib_cond_sat_choices lib (vals1 ++ vals2)
    -> lib_cond_sat_choices lib (vals2 ++ vals1).
Proof.
  introv sat i; apply sat; allrw in_app_iff; tcsp.
Qed.

Lemma lib_extends_pre_replace_cs_entry_between {o} :
  forall name e e' (lib2 lib1 : @library o),
    sat_lib_cond lib1
    -> safe_library lib1
    -> find_cs lib2 name = Some e
    -> cs_entry_between name e e' lib1
    -> lib_extends lib2 lib1
    -> lib_extends (replace_cs_entry lib1 name e') lib1
       /\ lib_extends lib2 (replace_cs_entry lib1 name e').
Proof.
  introv sat safe fcs btw ext.
  pose proof (lib_extends_find_some_left_implies name e lib2 lib1) as q.
  repeat (autodimp q hyp).
  repndors; exrepnd; subst.

  { rewrite replace_cs_entry_if_find_none; auto; dands; eauto 3 with slow. }

  applydup btw in q0; repnd.
  inversion q2 as [? ? ? xa xb]; subst; clear q2.
  inversion q4 as [? ? ? ya yb]; subst; clear q4.
  rewrite <- app_assoc in ya.
  apply app_inv_head in ya; subst; simpl in *.

  dands; try (complete (eapply lib_extends_pre_replace_cs_entry_app; eauto));[].
  dup ext as safe'; dup ext as sat'.
  eapply lib_extends_preserves_safe in safe'; eauto.
  eapply lib_extends_preserves_sat_lib_cond in sat'; eauto.
  apply find_cs_some_implies_entry_in_library in fcs.
  rewrite app_assoc in fcs; eauto 3 with slow.
  applydup safe' in fcs; simpl in *; repnd.
  applydup sat' in fcs; simpl in *; repnd.
  apply find_cs_implies_lib_extends_pre_replace_cs_entry_app_left; eauto 3 with slow.
Qed.

Lemma cs_entry_extends_firstn_cs_entry {o} :
  forall (c : @ChoiceSeqEntry o) n,
    cs_entry_extends c (firstn_cs_entry n c).
Proof.
  introv; destruct c as [vals restr]; simpl.
  pose proof (firstn_skipn n vals) as q; rewrite <- q at 1; eauto.
Qed.
Hint Resolve cs_entry_extends_firstn_cs_entry : slow.

Lemma find_cs_implies_greater_lib_depth {o} :
  forall (lib : @plibrary o) name e,
    find_cs lib  name = Some e
    -> length (cse_vals e) <= lib_depth lib.
Proof.
  induction lib; introv fcs; simpl in *; ginv.
  destruct a; simpl in *; boolvar; ginv; tcsp; eauto 3 with slow; eauto.
  eapply IHlib in fcs; eapply le_trans;[eauto|]; eauto 3 with slow.
Qed.

Lemma find_cs_implies_cs_entry_extends_firstn_cs_entry {o} :
  forall (lib2 lib1 : @library o) name c e,
    lib_extends lib2 lib1
    -> find_cs lib2 name = Some c
    -> find_cs lib1 name = Some e
    -> cs_entry_extends (firstn_cs_entry (lib_depth lib1 + 1) c) e.
Proof.
  introv ext fcsa fcsb.
  eapply lib_extends_preserves_find_cs in ext; eauto; exrepnd.
  rewrite fcsa in ext1; ginv; simpl in *.
  unfold choice_sequence_vals_extend in *; exrepnd; subst; simpl in *.
  destruct e as [vals' restr]; simpl in *.
  applydup @find_cs_implies_greater_lib_depth in fcsb; simpl in *.
  rewrite firstn_app.
  rewrite (firstn_all2 vals'); try omega; eauto.
Qed.
Hint Resolve find_cs_implies_cs_entry_extends_firstn_cs_entry : slow.

Lemma cs_entry_between_firstn_cs_entry {o} :
  forall name c (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> find_cs lib2 name = Some c
    -> cs_entry_between name c (firstn_cs_entry (lib_depth lib1 + 1) c) lib1.
Proof.
  introv ext fcsa fcsb; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve cs_entry_between_firstn_cs_entry : slow.

Lemma find_cs_pre_replace_cs_entry_implies {o} :
  forall (lib : @plibrary o) name e name' e',
    find_cs (pre_replace_cs_entry lib name e) name' = Some e'
    -> if choice_sequence_name_deq name name'
       then e' = e
       else find_cs lib name' = Some e'.
Proof.
  induction lib; introv fcs; simpl in *; ginv.
  destruct a; simpl in *; repeat (boolvar; subst; simpl in *; tcsp; GC; ginv);
    try (complete (apply IHlib in fcs; boolvar; subst; tcsp)).
Qed.

Lemma cs_entry_extends_refl {o} :
  forall (e : @ChoiceSeqEntry o), cs_entry_extends e e.
Proof.
  introv; destruct e as [vals restr].
  pose proof (app_nil_end vals) as h.
  rewrite h at 1; eauto.
Qed.
Hint Resolve cs_entry_extends_refl : slow.

Lemma cs_entry_between_firstn_cs_entry_pre_replace_cs_entry {o} :
  forall name name' c c' (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> find_cs lib2 name = Some c
    -> find_cs lib2 name' = Some c'
    -> cs_entry_between
         name'
         c'
         (firstn_cs_entry (lib_depth lib1 + 1) c')
         (replace_cs_entry lib1 name (firstn_cs_entry (lib_depth lib1 + 1) c)).
Proof.
  introv ext fcsa fcsb fcs; dands; eauto 3 with slow.
  apply find_cs_pre_replace_cs_entry_implies in fcs; boolvar; subst; eauto 3 with slow.
  rewrite fcsa in fcsb; ginv; eauto 3 with slow.
Qed.
Hint Resolve cs_entry_between_firstn_cs_entry_pre_replace_cs_entry : slow.

Lemma in_lib_add_cs {o} :
  forall name restr (lib : @library o),
    in_lib (entry_name_cs name) (add_cs name restr lib).
Proof.
  unfold add_cs; introv; simpl.
  rewrite in_lib_cons; simpl; tcsp.
Qed.
Hint Resolve in_lib_add_cs : slow.

Lemma lib_extends_preserves_not_in_lib {o} :
  forall (lib1 lib2 : @library o) name,
    lib_extends lib1 lib2
    -> !in_lib name lib1
    -> !in_lib name lib2.
Proof.
  introv ext nilib ilib; destruct nilib; unfold in_lib in *; exrepnd.
  apply implies_lib_extends_sub in ext.
  apply ext in ilib1; exrepnd.
  exists entry2; dands; eauto 3 with slow.
  inversion ilib2; subst; auto.
Qed.
Hint Resolve lib_extends_preserves_not_in_lib : slow.

(*Lemma lib_extends_add_cs {o} :
  forall name restr (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> correct_restriction name restr
    -> ! in_lib (entry_name_cs name) lib2
    -> lib_extends (add_cs name restr lib2) (add_cs name restr lib1).
Proof.
  introv ext; lib_ext_ind ext Case; introv cres nilib.

  { Case "lib_ext_trans".
    repeat (autodimp IHext1 hyp).
    repeat (autodimp IHext2 hyp); eauto 3 with slow. }

  { Case "lib_ext_new_abs".

Qed.*)

Definition erase_choices_entry {o} (e : @ChoiceSeqEntry o) : ChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr => MkChoiceSeqEntry _ [] restr
  end.

Definition erase_entry {o} (e : @library_entry o) : library_entry :=
  match e with
  | lib_cs a b => lib_cs a (erase_choices_entry b)
  | _ => e
  end.

Fixpoint erase_entries {o} (lib : @plibrary o) : plibrary :=
  match lib with
  | [] => []
  | e :: rest => erase_entry e :: erase_entries rest
  end.

Fixpoint erase_entries_upto {o} (name : EntryName) (lib : @plibrary o) : plibrary :=
  match lib with
  | [] => []
  | e :: rest =>
    if same_entry_name_dec name (entry2name e)
    then []
    else erase_entry e :: erase_entries_upto name rest
  end.


Definition pre_inc_cs_lib {o} name (lib2 lib1 : @plibrary o) : plibrary :=
  erase_entries_upto name lib2 ++ lib1.

Definition inc_cs_lib {o} name (lib2 lib1 : @library o) : library :=
  MkLib (pre_inc_cs_lib name lib2 lib1) (lib_cond lib2).

Definition has_first_name {o} name (lib : @plibrary o) :=
  match lib with
  | [] => False
  | e :: _ => same_entry_name name (entry2name e)
  end.

Lemma same_opabs_refl :
  forall op, same_opabs op op.
Proof.
  destruct op as [op params sign]; simpl.
  unfold same_opabs, matching_entry_sign; simpl; dands; auto.
  induction params; simpl; tcsp.
  unfold matching_parameters in *; simpl in *.
  rewrite assert_andb; dands; auto.
  destruct a; simpl in *.
  inversion p; subst; apply assert_true.
Qed.
Hint Resolve same_opabs_refl : slow.

Lemma same_entry_name_refl :
  forall name, same_entry_name name name.
Proof.
  destruct name; simpl; auto; eauto 3 with slow.
Qed.
Hint Resolve same_entry_name_refl : slow.

Definition dec_has_first_name {o} :
  forall (lib : @plibrary o), lib = [] \/ exists name, has_first_name name lib.
Proof.
  introv; destruct lib; simpl in *; tcsp; right; eauto.
  eexists; apply same_entry_name_refl.
Qed.

Lemma pre_inc_cs_lib_same {o} :
  forall name (lib : @plibrary o),
    has_first_name name lib
    -> pre_inc_cs_lib name lib lib = lib.
Proof.
  introv hf; unfold has_first_name, inc_cs_lib, pre_inc_cs_lib in *; destruct lib; simpl; auto; boolvar; tcsp.
Qed.

Lemma pre_inc_cs_lib_nil {o} :
  forall name (lib : @plibrary o), pre_inc_cs_lib name [] lib = lib.
Proof.
  tcsp.
Qed.
Hint Rewrite @pre_inc_cs_lib_nil : slow.

(*Lemma lib_extends_nil_l_implies {o} :
  forall (lib : @library o), lib_extends [] lib -> lib = [].
Proof.
  introv ext.
  apply implies_lib_extends_sub in ext.
  destruct lib; auto.
  pose proof (ext l) as ext; simpl in ext; autodimp ext hyp; exrepnd; tcsp.
Qed.*)


Fixpoint extension {o} (lib2 lib1 : @plibrary o) : Prop :=
  match lib2, lib1 with
  | [], [] => True
  | e2 :: rest2, e1 :: rest1 => entry_extends e2 e1 /\ extension rest2 rest1
  | _, _ => False
  end.


(*Lemma lib_extends_implies {o} :
  forall (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> exists liba libb,
      lib2 = liba ++ libb
      /\ extension libb lib1
      /\ no_repeats (lib_names liba)
      /\ disjoint (lib_names liba) (lib_names libb).*)

Lemma erase_entries_upto_app_not_in_left {o} :
  forall name (lib1 lib2 : @plibrary o),
    ~in_lib name lib1
    -> erase_entries_upto name (lib1 ++ lib2)
       = erase_entries_upto name lib1 ++ erase_entries_upto name lib2.
Proof.
  induction lib1; introv nilib; simpl in *; tcsp.
  rewrite in_lib_cons in nilib; apply not_or in nilib; repnd.
  rewrite IHlib1; auto.
  boolvar; subst; tcsp.
Qed.

Inductive norepeats {T} : list T -> Prop :=
| norep_nil : norepeats []
| norep_cons : forall x xs, ~List.In x xs -> norepeats xs -> norepeats (x :: xs).
Hint Constructors norepeats.

Lemma safe_library_nil {o} : @safe_library o [].
Proof.
  introv i; simpl in *; tcsp.
Qed.
Hint Resolve safe_library_nil : slow.

Lemma extension_refl {o} :
  forall (lib : @plibrary o), extension lib lib.
Proof.
  induction lib; introv; simpl; auto.
Qed.
Hint Resolve extension_refl : slow.

Lemma entry_in_library_extends_right {o} :
  forall e (lib1 lib2 : @library o),
    lib_extends lib1 lib2
    -> entry_in_library e lib2
    -> exists e',
        entry_in_library e' lib1
        /\ entry_extends e' e.
Proof.
  introv ext i.
  apply implies_lib_extends_ext in ext.
  apply ext in i.
  apply entry_in_library_extends_implies_entry_in_library; auto.
Qed.

Lemma eq_app_cons_implies {o} :
  forall (liba libb libc libd : @plibrary o) e1 e2,
    same_entry_name (entry2name e1) (entry2name e2)
    -> ~in_lib (entry2name e1) liba
    -> ~in_lib (entry2name e2) libc
    -> liba ++ e1 :: libb = libc ++ e2 :: libd
    -> liba = libc
       /\ e1 = e2
       /\ libb = libd.
Proof.
  induction liba; introv same nia nib eql; simpl in *.

  { destruct libc; simpl in *; tcsp; ginv; try (complete (dands; tcsp)).
    allrw @in_lib_cons; destruct nib; left; apply same_entry_name_sym; auto. }

  destruct libc; simpl in *; tcsp; ginv.

  { allrw @in_lib_cons; destruct nia; tcsp. }

  allrw @in_lib_cons.
  apply not_or in nia; repnd.
  apply not_or in nib; repnd.
  apply cons_inj in eql; repnd; subst.
  apply IHliba in eql; auto; repnd; subst; tcsp.
Qed.

Lemma entry_extends_implies_same_entry_name {o} :
  forall (e1 e2 : @library_entry o),
    entry_extends e1 e2
    -> same_entry_name (entry2name e1) (entry2name e2).
Proof.
  introv ext; inversion ext; subst; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve entry_extends_implies_same_entry_name : slow.

Lemma extension_trans {o} :
  forall (liba libb libc : @plibrary o),
    extension liba libb
    -> extension libb libc
    -> extension liba libc.
Proof.
  induction liba; introv exta extb; simpl in *; tcsp;
    destruct libb; simpl in *; tcsp.
  destruct libc; simpl in *; tcsp; repnd.
  dands; eauto 3 with slow.
Qed.

Lemma in_lib_app {o} :
  forall n (lib1 lib2 : @plibrary o),
    in_lib n (lib1 ++ lib2)
    <-> (in_lib n lib1 \/ in_lib n lib2).
Proof.
  introv; split; intro h; unfold in_lib in *; repndors; exrepnd.
  { allrw @list_in_app; repndors; eauto. }
  { exists e; allrw @list_in_app; eauto. }
  { exists e; allrw @list_in_app; eauto. }
Qed.

Lemma add_choice_extension {o} :
  forall name v (lib : @plibrary o) n restr lib',
    add_choice name v lib = Some (n, restr, lib')
    -> extension lib' lib.
Proof.
  induction lib; introv addc; simpl in *; ginv.
  destruct a; simpl in *; tcsp.

  { destruct entry as [vals restr']; simpl in *; boolvar; subst; tcsp; ginv.
    { inversion addc; subst; clear addc; simpl in *; dands; eauto 3 with slow.
      rewrite snoc_as_append; eauto. }
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp; ginv.
    inversion addc; clear addc; subst; simpl in *.
    pose proof (IHlib n restr p) as IHlib; autodimp IHlib hyp. }

  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp; ginv.
  inversion addc; clear addc; subst; simpl in *.
  pose proof (IHlib n restr p) as IHlib; autodimp IHlib hyp.
Qed.

Lemma add_one_choice_extension {o} :
  forall name v (lib : @library o) n restr lib',
    add_one_choice name v lib = Some (n, restr, lib')
    -> extension lib' lib.
Proof.
  introv h; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp; ginv; simpl in *.
  eapply add_choice_extension; eauto.
Qed.

Lemma extension_app_right_implies {o} :
  forall (lib lib1 lib2 : @plibrary o),
    extension lib (lib1 ++ lib2)
    -> exists lib3 lib4,
      lib = lib3 ++ lib4
      /\ extension lib3 lib1
      /\ extension lib4 lib2.
Proof.
  induction lib; introv ext; simpl in *.

  { destruct lib1; simpl in *; tcsp.
    destruct lib2; simpl in *; tcsp.
    exists ([] : @plibrary o) ([] : @plibrary o); simpl; auto. }

  destruct lib1; simpl in *.

  { destruct lib2; simpl in *; tcsp; repnd.
    exists ([] : @plibrary o) (a :: lib); simpl; dands; eauto 3 with slow. }

  repnd.
  apply IHlib in ext; exrepnd; subst.
  exists (a :: lib3) lib4; simpl; dands; tcsp.
Qed.

Lemma extension_cons_right_implies {o} :
  forall (lib1 : @plibrary o) e lib2,
    extension lib1 (e :: lib2)
    -> exists e' lib',
      lib1 = e' :: lib'
      /\ entry_extends e' e
      /\ extension lib' lib2.
Proof.
  destruct lib1; introv ext; simpl in *; tcsp; repnd; eauto.
Qed.

Lemma extension_preserves_in_lib {o} :
  forall n (lib1 lib2 : @plibrary o),
    extension lib1 lib2
    -> (in_lib n lib1 <-> in_lib n lib2).
Proof.
  induction lib1; introv ext; simpl in *; destruct lib2; simpl in *; tcsp; repnd.
  apply IHlib1 in ext.
  allrw @in_lib_cons.
  rewrite ext.
  apply entry_extends_implies_same_entry_name in ext0.
  split; intro h; repndors; tcsp; left; eauto 3 with slow.
Qed.

Lemma extension_implies_same_names {o} :
  forall (lib2 lib1 : @plibrary o),
    extension lib2 lib1
    -> lib_names lib2 = lib_names lib1.
Proof.
  induction lib2; introv ext; simpl in *; destruct lib1; simpl in *; tcsp; repnd.
  apply IHlib2 in ext.
  apply entry_extends_implies_same_entry2name in ext0.
  allrw; auto.
Qed.

Lemma add_choice_preserves_lib_names {o} :
  forall name v (lib : @plibrary o) n restr lib',
    add_choice name v lib = Some (n, restr, lib')
    -> lib_names lib = lib_names lib'.
Proof.
  induction lib; introv addc; simpl in *; ginv.
  destruct a; simpl in *; tcsp.
  { destruct entry as [vals restr']; simpl in *; boolvar; subst; simpl in *; tcsp.
    { inversion addc; clear addc; subst; simpl in *; tcsp. }
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
    pose proof (IHlib p1 p0 p) as IHlib; autodimp IHlib hyp.
    inversion addc; clear addc; subst; simpl; auto; try congruence. }
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
  pose proof (IHlib p1 p0 p) as IHlib; autodimp IHlib hyp.
  inversion addc; clear addc; subst; simpl; auto; try congruence.
Qed.

Lemma add_one_choice_preserves_lib_names {o} :
  forall name v (lib : @library o) n restr lib',
    add_one_choice name v lib = Some (n, restr, lib')
    -> lib_names lib = lib_names lib'.
Proof.
  introv h; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc; destruct addc; repnd; ginv.
  apply add_choice_preserves_lib_names in Heqaddc; tcsp.
Qed.

Lemma lib_extends_implies_lib_names {o} :
  forall (lib1 lib2 : @library o),
    lib_extends lib1 lib2
    -> exists names, lib_names lib1 = names ++ lib_names lib2.
Proof.
  introv ext; lib_ext_ind ext Case; introv; tcsp;
    try (complete (try apply add_one_choice_preserves_lib_names in addc; exists ([] : list EntryName); simpl; auto)).

  { Case "lib_ext_trans"; exrepnd.
    rewrite IHext2; rewrite IHext0.
    exists (names0 ++ names); rewrite app_assoc; auto. }

  { Case "lib_ext_new_abs".
    exists [entry_name_abs op]; simpl; tcsp. }

  { Case "lib_ext_new_cs".
    exists [entry_name_cs name]; simpl; tcsp. }
Qed.

Lemma app_left_implies_nil :
  forall {T} (l k : list T),
    l ++ k = k
    -> l = [].
Proof.
  introv h.
  assert (length (l ++ k) = length k) as q by (rewrite h; auto).
  rewrite length_app in q.
  remember (length l) as ll; destruct ll; simpl in *; try omega.
  destruct l; simpl in *; auto; ginv.
Qed.

Fixpoint lib_nodup {o} (lib : @plibrary o) :=
  match lib with
  | [] => True
  | e :: rest => ~in_lib (entry2name e) rest /\ lib_nodup rest
  end.

Lemma add_choice_preserves_in_lib {o} :
  forall name v (lib : @plibrary o) n restr lib',
    add_choice name v lib = Some (n, restr, lib')
    -> (forall x, in_lib x lib <-> in_lib x lib').
Proof.
  induction lib; introv addc; introv; simpl in *; ginv.
  destruct a; simpl in *; tcsp.
  { destruct entry as [vals restr']; simpl in *; boolvar; subst; simpl in *; tcsp.
    { inversion addc; clear addc; subst; simpl in *; tcsp.
      allrw @in_lib_cons; simpl; tcsp. }
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
    pose proof (IHlib p1 p0 p) as IHlib; autodimp IHlib hyp.
    inversion addc; clear addc; subst; simpl; auto.
    allrw @in_lib_cons; simpl.
    rewrite IHlib; tcsp. }
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
  pose proof (IHlib p1 p0 p) as IHlib; autodimp IHlib hyp.
  inversion addc; clear addc; subst; simpl; auto.
  allrw @in_lib_cons; simpl.
  rewrite IHlib; tcsp.
Qed.

Lemma add_one_choice_preserves_in_lib {o} :
  forall name v (lib : @library o) n restr lib',
    add_one_choice name v lib = Some (n, restr, lib')
    -> (forall x, in_lib x lib <-> in_lib x lib').
Proof.
  introv h; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
  inversion h; subst; clear h; simpl in *.
  eapply add_choice_preserves_in_lib; eauto.
Qed.

Lemma add_choice_preserves_nodup {o} :
  forall name v (lib : @plibrary o) n restr lib',
    add_choice name v lib = Some (n, restr, lib')
    -> lib_nodup lib
    -> lib_nodup lib'.
Proof.
  induction lib; introv addc nodup; simpl in *; repnd; tcsp.
  destruct a; simpl in *; tcsp.
  { destruct entry as [vals restr']; boolvar; simpl in *; subst; tcsp.
    { inversion addc; clear addc; subst; simpl in *; tcsp. }
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
    pose proof (IHlib p1 p0 p) as IHlib; repeat (autodimp IHlib hyp).
    inversion addc; clear addc; subst; simpl in *; dands; tcsp; eauto 3 with slow.
    introv xx; eapply add_choice_preserves_in_lib in xx; eauto. }
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
  pose proof (IHlib p1 p0 p) as IHlib; repeat (autodimp IHlib hyp).
  inversion addc; clear addc; subst; simpl in *; dands; tcsp; eauto 3 with slow.
  introv xx; eapply add_choice_preserves_in_lib in xx; eauto.
Qed.
Hint Resolve add_choice_preserves_nodup : slow.

Lemma add_one_choice_preserves_nodup {o} :
  forall name v (lib : @library o) n restr lib',
    add_one_choice name v lib = Some (n, restr, lib')
    -> lib_nodup lib
    -> lib_nodup lib'.
Proof.
  introv h nodup; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc; symmetry in Heqaddc;
    destruct addc; repnd; ginv; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve add_one_choice_preserves_nodup : slow.

Lemma lib_extends_preserves_nodup {o} :
  forall (lib1 lib2 : @library o),
    lib_extends lib1 lib2
    -> lib_nodup lib2
    -> lib_nodup lib1.
Proof.
  introv ext; lib_ext_ind ext Case; introv nodup; tcsp.
Qed.
Hint Resolve lib_extends_preserves_nodup : slow.

Lemma add_choice_implies_in_lib {o} :
  forall name v (lib : @plibrary o) n restr lib',
    add_choice name v lib = Some (n, restr, lib')
    -> in_lib (entry_name_cs name) lib.
Proof.
  induction lib; introv addc; simpl in *; ginv.
  destruct a; simpl in *; tcsp.
  { destruct entry as [vals restr']; boolvar; simpl in *; subst; tcsp.
    { inversion addc; clear addc; subst; simpl in *; tcsp.
      allrw @in_lib_cons; simpl; tcsp. }
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
    pose proof (IHlib p1 p0 p) as IHlib; repeat (autodimp IHlib hyp).
    inversion addc; clear addc; subst; simpl in *; dands; tcsp; eauto 3 with slow. }
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
  pose proof (IHlib p1 p0 p) as IHlib; repeat (autodimp IHlib hyp).
  inversion addc; clear addc; subst; simpl in *; dands; tcsp; eauto 3 with slow.
Qed.

Lemma add_one_choice_implies_in_lib {o} :
  forall name v (lib : @library o) n restr lib',
    add_one_choice name v lib = Some (n, restr, lib')
    -> in_lib (entry_name_cs name) lib.
Proof.
  introv h; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
  inversion h; subst; clear h; simpl in *.
  eapply add_choice_implies_in_lib; eauto.
Qed.

Lemma implies_lib_cons_lr {o} :
  forall e (lib1 lib2 : @library o),
    lib_extends lib2 lib1
    -> ~ in_lib (entry2name e) lib2
    -> lib_names lib2 = lib_names lib1
    -> lib_extends (add_one_entry e lib2) (add_one_entry e lib1).
Proof.
  introv ext; lib_ext_ind ext Case; introv nilib eqn; tcsp.

  { Case "lib_ext_trans".
    applydup @lib_extends_implies_lib_names in ext1.
    applydup @lib_extends_implies_lib_names in ext2.
    exrepnd.
    dup eqn as h.
    rewrite ext3 in h; rewrite ext4 in h; rewrite app_assoc in h.
    apply app_left_implies_nil in h; apply app_eq_nil in h; repnd; subst; simpl in *.
    repeat (autodimp IHext1 hyp); repeat (autodimp IHext2 hyp); eauto.
    eapply lib_extends_preserves_not_in_lib; eauto. }

  { Case "lib_ext_new_abs".
    rewrite cons_as_app in eqn; apply app_left_implies_nil in eqn; ginv. }

  { Case "lib_ext_new_cs".
    rewrite cons_as_app in eqn; apply app_left_implies_nil in eqn; ginv. }

  { Case "lib_ext_cs".
    eapply (lib_extends_cs _ name); try exact cond; simpl; tcsp.
    assert (~in_lib (entry2name e) lib) as nilib'.
    { intro xx; erewrite add_one_choice_preserves_in_lib in xx; eauto. }
    applydup @add_one_choice_implies_in_lib in addc.
    destruct e; simpl in *; tcsp; allrw; tcsp.
    { destruct entry as [vals restr]; boolvar; subst; tcsp.
      destruct lib as [lib c]; simpl in *; tcsp.
      remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
      inversion addc; subst; tcsp. }
    destruct lib as [lib c]; simpl in *; tcsp.
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
    inversion addc; subst; tcsp. }

(*  { Case "lib_ext_law".
    eapply (lib_extends_law _ name); try exact cond.
    assert (~in_lib (entry2name e) lib) as nilib'.
    { intro xx; erewrite add_choice_preserves_in_lib in xx; eauto. }
    applydup @add_choice_implies_in_lib in addc.
    simpl; destruct e; simpl in *; tcsp; allrw; tcsp.
    destruct entry as [vals restr]; boolvar; subst; tcsp. }

  { Case "lib_ext_res".
    eapply (lib_extends_res _ name); try exact cond.
    assert (~in_lib (entry2name e) lib) as nilib'.
    { intro xx; erewrite add_choice_preserves_in_lib in xx; eauto. }
    applydup @add_choice_implies_in_lib in addc.
    simpl; destruct e; simpl in *; tcsp; allrw; tcsp.
    destruct entry as [vals restr]; boolvar; subst; tcsp. }*)
Qed.


Lemma entry_in_library_implies_in_lib {o} :
  forall e a (lib : @plibrary o),
    entry_in_library e lib
    -> matching_entries e a
    -> in_lib (entry2name a) lib.
Proof.
  introv i m.
  unfold in_lib; exists e; dands; eauto 3 with slow.
Qed.
Hint Resolve entry_in_library_implies_in_lib : slow.

Lemma not_in_sat_cond_lib_cons_implies {o} :
  forall (lib : @plibrary o) cond a,
    ~ in_lib (entry2name a) lib
    -> sat_cond_lib cond (a :: lib)
    -> (sat_cond_entry cond a /\ sat_cond_lib cond lib).
Proof.
  introv ni sat; dands.
  { apply sat; simpl; tcsp. }
  introv i; apply sat; simpl; right; dands; tcsp.
  introv m; destruct ni; eauto 3 with slow.
Qed.

Lemma sat_cond_lib_cons_implies {o} :
  forall (lib : @plibrary o) cond a,
    ~ in_lib (entry2name a) lib
    -> sat_cond_lib cond (a :: lib)
    -> sat_cond_lib cond lib.
Proof.
  introv ni sat; eapply not_in_sat_cond_lib_cons_implies; eauto.
Qed.
Hint Resolve sat_cond_lib_cons_implies : slow.

Lemma sat_cond_entry_implies_lib_cond_sat_vals_entry {o} :
  forall cond (lib : @plibrary o) e,
    sat_cond_entry cond e
    -> lib_cond_sat_vals_entry (MkLib lib cond) e.
Proof.
  introv sat; destruct e; simpl in *; tcsp.
  destruct entry as [vals restr]; simpl in *; repnd; tcsp.
Qed.
Hint Resolve sat_cond_entry_implies_lib_cond_sat_vals_entry : slow.

Lemma extension_implies_lib_extends0 {o} :
  forall cond (lib2 lib1 : @plibrary o),
    sat_cond_lib cond lib2
    -> strong_safe_library lib2
    -> lib_nodup lib2
    -> extension lib2 lib1
    -> lib_extends (MkLib lib2 cond) (MkLib lib1 cond).
Proof.
  induction lib2; introv sat safe nodup ext; simpl in *; destruct lib1; simpl in *; tcsp; repnd.
  allrw @strong_safe_library_cons; repnd.
  applydup IHlib2 in ext; auto; eauto 3 with slow;[].
  applydup @extension_implies_same_names in ext.
  eapply lib_extends_trans;
    [|apply (implies_lib_extends_cons l a (MkLib lib1 cond)); auto]; eauto 3 with slow.
  { apply (implies_lib_cons_lr a (MkLib lib1 cond) (MkLib lib2 cond)); tcsp. }
  pose proof (sat a) as sat; simpl in *; autodimp sat hyp; eauto 3 with slow.
Qed.

Lemma extension_implies_lib_extends {o} :
  forall (lib2 lib1 : @library o),
    sat_lib_cond lib2
    -> strong_safe_library lib2
    -> lib_nodup lib2
    -> extension lib2 lib1
    -> same_conds lib2 lib1
    -> lib_extends lib2 lib1.
Proof.
  introv sat safe nodup ext same.
  destruct lib2 as [lib2 cond2], lib1 as [lib1 cond1]; simpl in *.
  unfold same_conds in *; simpl in *; subst.
  eapply extension_implies_lib_extends0; eauto.
Qed.

Lemma strong_safe_library_app {o} :
  forall (lib1 lib2 : @plibrary o),
    strong_safe_library (lib1 ++ lib2)
    <-> (strong_safe_library lib1 /\ strong_safe_library lib2).
Proof.
  introv; split; intro h; repnd; dands; introv i.
  { apply h; apply list_in_app; tcsp. }
  { apply h; apply list_in_app; tcsp. }
  { apply list_in_app in i; repndors; eauto. }
Qed.
Hint Rewrite @strong_safe_library_app : slow.

Lemma lib_nodup_app_implies {o} :
  forall (lib1 lib2 : @plibrary o),
    lib_nodup (lib1 ++ lib2)
    -> lib_nodup lib1 /\ lib_nodup lib2.
Proof.
  induction lib1; introv h; simpl in *; tcsp; repnd.
  apply IHlib1 in h; repnd.
  dands; tcsp; intro xx; destruct h0.
  apply in_lib_app; tcsp.
Qed.

Lemma extension_preserves_lib_nodup {o} :
  forall (lib2 lib1 : @plibrary o),
    extension lib2 lib1
    -> lib_nodup lib1
    -> lib_nodup lib2.
Proof.
  induction lib2; introv ext nodup; simpl in *; tcsp.
  destruct lib1; simpl in *; repnd; dands; tcsp; eauto 3 with slow.
  introv xx; erewrite extension_preserves_in_lib in xx; eauto.
  destruct nodup0; eapply same_entry_name_preserves_in_lib; eauto; eauto 3 with slow.
Qed.
Hint Resolve extension_preserves_lib_nodup : slow.

Lemma same_conds_preserves_sat_cond_restr {o} :
  forall (lib1 lib2 : @library o) restr,
    same_conds lib1 lib2
    -> sat_cond_restr lib1 restr
    -> sat_cond_restr lib2 restr.
Proof.
  introv same sat.
  unfold sat_cond_restr; rewrite <- same; tcsp.
Qed.
Hint Resolve same_conds_preserves_sat_cond_restr : slow.

(* MOVE *)
Lemma same_conds_preserves_lib_cond_sat_entry {o} :
  forall (lib1 lib2 : @library o) e,
    same_conds lib1 lib2
    -> lib_cond_sat_entry lib1 e
    -> lib_cond_sat_entry lib2 e.
Proof.
  introv same sat.
  unfold lib_cond_sat_entry in *; destruct e; tcsp.
  { destruct entry as [vals restr]; simpl in *; repnd; dands; eauto 3 with slow. }
  { unfold sat_cond_soterm.
    rewrite <- same; apply sat; auto. }
Qed.
Hint Resolve same_conds_preserves_lib_cond_sat_entry : slow.

(* MOVE *)
Lemma entry_extends_preserves_lib_cond_sat_entry_rev {o} :
  forall (lib : @library o) e e',
    entry_extends e' e
    -> lib_cond_sat_entry lib e'
    -> lib_cond_sat_entry lib e.
Proof.
  introv ext sat.
  inversion ext; subst; tcsp; simpl in *; clear ext; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve entry_extends_preserves_lib_cond_sat_entry_rev : slow.

(* MOVE *)
Lemma lib_extends_preserves_sat_lib_cond_rev {o} :
  forall (lib1 lib2 : @library o),
    lib_extends lib1 lib2
    -> sat_lib_cond lib1
    -> sat_lib_cond lib2.
Proof.
  introv ext sat i.
  eapply entry_in_library_extends_right in i; eauto; exrepnd.
  apply sat in i1.
  apply lib_extends_implies_same_conds in ext.
  eapply same_conds_preserves_lib_cond_sat_entry; eauto; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_sat_lib_cond_rev : slow.

(* MOVE *)
Lemma lib_cond_sat_entry_mk_as {o} :
  forall (lib : @plibrary o) cond e,
    lib_cond_sat_entry (MkLib lib cond) e
    <-> sat_cond_entry cond e.
Proof.
  introv; tcsp.
Qed.
Hint Rewrite @lib_cond_sat_entry_mk_as : slow.

Lemma in_lib_extends_implies_split {o} :
  forall (lib1 lib2 : @library o) e,
    lib_extends lib1 lib2
    -> sat_lib_cond lib1
    -> strong_safe_library lib2
    -> lib_nodup lib2
    -> entry_in_library e lib2
    -> exists liba libb libc libd e' cond,
        lib1 = MkLib (liba ++ e' :: libb) cond
        /\ lib2 = MkLib (libc ++ e :: libd) cond
        /\ ~in_lib (entry2name e') liba
        /\ ~in_lib (entry2name e) libc
        /\ entry_extends e' e
        /\ extension (MkLib libb cond) (MkLib libd cond)
        /\ lib_extends (MkLib liba cond) (MkLib libc cond).
Proof.
  introv ext; revert e; lib_ext_ind ext Case; introv satl safe nodup i; tcsp.

  { Case "lib_ext_refl".
    apply entry_in_library_split in i; exrepnd.
    destruct lib as [lib cond]; simpl in *; subst; simpl in *.
    exists lib1 lib2 lib1 lib2 e cond; dands; tcsp; eauto 3 with slow. }

  { Case "lib_ext_trans".
    assert (strong_safe_library lib2) as safe' by eauto 3 with slow.
    assert (sat_lib_cond lib2) as satl' by eauto 3 with slow.
    assert (lib_nodup lib2) as nodup' by eauto 3 with slow.
    pose proof (IHext2 _ satl' safe nodup i) as IHext2; exrepnd; subst.
    dup i as j.
    eapply entry_in_library_extends_right in j; eauto; exrepnd.
    pose proof (IHext1 _  satl safe' nodup' j1) as IHext1; exrepnd; subst.
    inversion IHext3 as [IHext3']; subst; clear IHext3; simpl in *.

    assert (same_entry_name (entry2name e') (entry2name e'0)) as same.
    { allapply @entry_extends_implies_same_entry_name; eauto 3 with slow. }
    apply eq_app_cons_implies in IHext3'; eauto 3 with slow; repnd; subst.

    exists liba0 libb0 libc libd e'1 cond0; dands; eauto 3 with slow;
      try (complete (eapply extension_trans; eauto)). }

  { Case "lib_ext_new_abs".
    applydup @entry_in_library_split in i; exrepnd; subst.
    destruct lib as [lib cond]; simpl in *; subst; simpl in *.
    exists (lib_abs op vars rhs correct :: lib1) lib2 lib1 lib2 e cond; dands; eauto 3 with slow.

    { intro xx; allrw @in_lib_cons; simpl in *; repndors; tcsp.
      destruct ni; allrw @in_lib_app; allrw @in_lib_cons.
      right; left; apply same_entry_name_sym; auto. }

    eapply (lib_extends_new_abs (MkLib lib1 cond)); simpl; tcsp; intro xx; destruct ni.
    apply in_lib_app; tcsp. }

  { Case "lib_ext_new_cs".
    applydup @entry_in_library_split in i; exrepnd; subst.
    destruct lib as [lib cond]; simpl in *; subst.
    unfold add_cs; simpl.
    exists (lib_cs name (MkChoiceSeqEntry _ [] restr) :: lib1) lib2 lib1 lib2 e cond; dands; eauto 3 with slow.

    { intro xx; allrw @in_lib_cons; simpl in *; repndors; tcsp.
      destruct ni; allrw @in_lib_app; allrw @in_lib_cons.
      right; left; apply same_entry_name_sym; auto. }

    eapply (lib_extends_new_cs (MkLib lib1 cond)); auto; intro xx; destruct ni.
    apply in_lib_app; tcsp. }

  { Case "lib_ext_cs".
    applydup @add_one_choice_extension in addc.
    dup i as j; apply entry_in_library_split in j; exrepnd; subst.
    destruct lib as [lib cond0]; simpl in *; subst; simpl in *.
    remember (add_choice name v (lib1 ++ e :: lib2)) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
    inversion addc; subst; clear addc.
    apply extension_app_right_implies in addc0; exrepnd; subst; simpl in *.
    apply extension_cons_right_implies in addc0; exrepnd; subst; simpl in *.
    exists lib3 lib' lib1 lib2 e' cond0; dands; tcsp.
    { apply (extension_preserves_in_lib (entry2name e)) in addc2.
      intro xx; destruct j1; apply addc2.
      eapply same_entry_name_preserves_in_lib; try exact xx; eauto 3 with slow. }
    applydup @add_choice_preserves_strong_safe_library in Heqaddc'; simpl; auto.
    allrw @strong_safe_library_app; repnd.
    apply lib_nodup_app_implies in nodup; simpl in *; repnd.
    apply extension_implies_lib_extends; simpl; eauto 3 with slow; tcsp.
    introv j; simpl in *; autorewrite with slow.
    apply satl; simpl; eauto 3 with slow. }

(*  { Case "lib_ext_law".
    applydup @add_choice_extension in addc.
    dup i as j; apply entry_in_library_split in j; exrepnd; subst.
    apply extension_app_right_implies in addc0; exrepnd; subst; simpl in *.
    apply extension_cons_right_implies in addc0; exrepnd; subst; simpl in *.
    exists lib3 lib' lib1 lib2 e'; dands; tcsp.
    { apply (extension_preserves_in_lib (entry2name e)) in addc2.
      intro xx; destruct j1; apply addc2.
      eapply same_entry_name_preserves_in_lib; try exact xx; eauto 3 with slow. }
    applydup @add_choice_preserves_strong_safe_library in addc; simpl; auto.
    allrw @strong_safe_library_app; repnd.
    apply lib_nodup_app_implies in nodup; simpl in *; repnd.
    apply extension_implies_lib_extends; auto; eauto 3 with slow. }

  { Case "lib_ext_res".
    applydup @add_choice_extension in addc.
    dup i as j; apply entry_in_library_split in j; exrepnd; subst.
    apply extension_app_right_implies in addc0; exrepnd; subst; simpl in *.
    apply extension_cons_right_implies in addc0; exrepnd; subst; simpl in *.
    exists lib3 lib' lib1 lib2 e'; dands; tcsp.
    { apply (extension_preserves_in_lib (entry2name e)) in addc2.
      intro xx; destruct j1; apply addc2.
      eapply same_entry_name_preserves_in_lib; try exact xx; eauto 3 with slow. }
    applydup @add_choice_preserves_strong_safe_library in addc; simpl; auto.
    allrw @strong_safe_library_app; repnd.
    apply lib_nodup_app_implies in nodup; simpl in *; repnd.
    apply extension_implies_lib_extends; auto; eauto 3 with slow. }*)
Qed.

Lemma not_in_lib_nil {o} :
  forall n, ~ (@in_lib o n []).
Proof.
  introv xx; autorewrite with slow in *; tcsp.
Qed.
Hint Resolve not_in_lib_nil : slow.

Definition lib_disjoint {o} (lib1 lib2 : @plibrary o) :=
  forall n, in_lib n lib1 -> ~in_lib n lib2.

Lemma lib_disjoint_cons_right {o} :
  forall lib e (lib' : @plibrary o),
    lib_disjoint lib (e :: lib')
    <-> (lib_disjoint lib lib' /\ ~in_lib (entry2name e) lib).
Proof.
  introv; split; introv h; repnd; dands; tcsp.
  { introv i j; apply h in i; simpl in *; destruct i; apply in_lib_cons; tcsp. }
  { introv i; apply h in i; destruct i; apply in_lib_cons; simpl; left; eauto 3 with slow. }
  { introv i j; apply in_lib_cons in j; repndors; tcsp.
    { destruct h; eapply same_entry_name_preserves_in_lib; eauto. }
    { eapply h0; eauto. } }
Qed.
Hint Rewrite @lib_disjoint_cons_right : slow.

Lemma lib_disjoint_cons_left {o} :
  forall lib e (lib' : @plibrary o),
    lib_disjoint (e :: lib) lib'
    <-> (lib_disjoint lib lib' /\ ~in_lib (entry2name e) lib').
Proof.
  introv; split; introv h; repnd; dands; tcsp.
  { introv i j; apply h in j; simpl in *; tcsp; apply in_lib_cons; tcsp. }
  { introv i; apply h in i; destruct i; apply in_lib_cons; simpl; left; eauto 3 with slow. }
  { introv i j; apply in_lib_cons in i; repndors; tcsp.
    { destruct h; eapply same_entry_name_preserves_in_lib; eauto. }
    { eapply h0; eauto. } }
Qed.
Hint Rewrite @lib_disjoint_cons_left : slow.

Lemma in_lib_snoc {o} :
  forall n e (lib : @plibrary o),
    in_lib n (snoc lib e) <-> (same_entry_name n (entry2name e) \/ in_lib n lib).
Proof.
  introv; unfold in_lib; split; intro h; repndors; exrepnd; allrw @list_in_snoc;
    repndors; subst; simpl in *; tcsp; eauto;
      try (complete (eexists; dands; try apply list_in_snoc; try exact h0; eauto)).
Qed.

Lemma lib_disjoint_snoc_left {o} :
  forall lib e (lib' : @plibrary o),
    lib_disjoint (snoc lib e) lib'
    <-> (lib_disjoint lib lib' /\ ~in_lib (entry2name e) lib').
Proof.
  introv; split; introv h; repnd; dands; tcsp.
  { introv i j; apply h in j; simpl in *; tcsp; apply in_lib_snoc; tcsp. }
  { intro i; apply h in i; tcsp; apply in_lib_snoc; left; eauto 3 with slow. }
  { introv i j; apply in_lib_snoc in i; repndors; tcsp.
    { destruct h; eapply same_entry_name_preserves_in_lib; eauto. }
    { eapply h0; eauto. } }
Qed.

Lemma extension_implies_lib_extends_app {o} :
  forall cond (lib2 lib1 : @plibrary o) lib,
    lib_disjoint lib lib2
    -> strong_safe_library lib2
    -> sat_cond_lib cond lib2
    -> lib_nodup lib2
    -> extension lib2 lib1
    -> lib_extends (MkLib (lib ++ lib2) cond) (MkLib (lib ++ lib1) cond).
Proof.
  induction lib2; introv disj safe sat nodup ext; simpl in *; destruct lib1; simpl in *; tcsp; repnd.
  allrw @strong_safe_library_cons; repnd.
  apply lib_disjoint_cons_right in disj; repnd.
  applydup (IHlib2 lib1 (snoc lib a)) in ext; auto; eauto 3 with slow;
    try (complete (apply lib_disjoint_snoc_left; tcsp));[].
  rewrite snoc_as_append in ext1; repeat (rewrite <- app_assoc in ext1); simpl in *.
  eapply lib_extends_trans;[exact ext1|]; clear ext1.
  apply (lib_extends_middle (MkLib lib cond) (MkLib lib1 cond)); eauto 3 with slow.
  { pose proof (sat a) as sat; simpl in sat; autodimp sat hyp; eauto 3 with slow. }
  intro xx; eapply same_entry_name_preserves_in_lib in xx; eauto; eauto 3 with slow.
Qed.

Lemma lib_extends_preserves_lib_disjoint {o} :
  forall (lib1 lib2 : @library o) lib,
    lib_extends lib1 lib2
    -> lib_disjoint lib1 lib
    -> lib_disjoint lib2 lib.
Proof.
  introv ext disj i j.
  applydup @implies_lib_extends_sub in ext.
  unfold in_lib in i; exrepnd.
  apply ext0 in i1; exrepnd.
  pose proof (disj n) as disj; autodimp disj hyp.
  apply entry_extends_implies_same_entry_name in i2.
  exists entry2; dands; eauto 3 with slow.
Qed.

Lemma add_choice_preserves_lib_disjoint {o} :
  forall name v (lib : @plibrary o) n restr lib' k,
    add_choice name v lib = Some (n, restr, lib')
    -> lib_disjoint lib' k
    -> lib_disjoint lib k.
Proof.
  introv ext disj; apply add_choice_extension in ext; eauto 3 with slow.
  revert dependent lib.
  induction lib'; introv ext; simpl in *; destruct lib; simpl in *; tcsp; repnd.
  allrw @lib_disjoint_cons_left; repnd.
  autodimp IHlib' hyp.
  pose proof (IHlib' lib) as IHlib'; autodimp IHlib' hyp; eauto 3 with slow.
  dands; eauto 3 with slow.
  apply entry_extends_implies_same_entry_name in ext0; intro xx; destruct disj.
  eapply same_entry_name_preserves_in_lib; eauto; eauto 3 with slow.
Qed.
Hint Resolve add_choice_preserves_lib_disjoint : slow.

Lemma add_one_choice_preserves_lib_disjoint {o} :
  forall name v (lib : @library o) n restr lib' k,
    add_one_choice name v lib = Some (n, restr, lib')
    -> lib_disjoint lib' k
    -> lib_disjoint lib k.
Proof.
  introv h disj; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
  inversion h; subst; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve add_one_choice_preserves_lib_disjoint : slow.

Lemma implies_add_choice_app {o} :
  forall name v (lib : @plibrary o) n restr lib' k,
    add_choice name v lib = Some (n, restr, lib')
    -> add_choice name v (lib ++ k) = Some (n, restr, lib' ++ k).
Proof.
  induction lib; introv addc; simpl in *; ginv.
  destruct a; simpl in *; tcsp.
  { destruct entry as [vals restr']; boolvar; simpl in *; subst; tcsp.
    { inversion addc; clear addc; subst; simpl in *; tcsp. }
    remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
    pose proof (IHlib p1 p0 p k) as IHlib; repeat (autodimp IHlib hyp); allrw.
    inversion addc; clear addc; subst; simpl in *; dands; tcsp; eauto 3 with slow. }
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
  pose proof (IHlib p1 p0 p k) as IHlib; repeat (autodimp IHlib hyp); allrw.
  inversion addc; clear addc; subst; simpl in *; dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve implies_add_choice_app : slow.

Definition lib_app {o} (lib1 lib2 : @library o) :=
  MkLib (lib_pre lib1 ++ lib_pre lib2) (lib_cond lib1).

Lemma implies_add_one_choice_app {o} :
  forall name v (lib : @library o) n restr lib' k,
    add_one_choice name v lib = Some (n, restr, lib')
    -> add_one_choice name v (lib_app lib k) = Some (n, restr, lib_app lib' k).
Proof.
  introv h; destruct lib as [lib cond]; simpl in *.
  remember (add_choice name v lib) as addc'; symmetry in Heqaddc'; destruct addc'; repnd; simpl in *; tcsp.
  inversion h; subst; simpl in *; clear h.
  erewrite implies_add_choice_app; eauto; simpl; tcsp.
Qed.
Hint Resolve implies_add_one_choice_app : slow.

Lemma lib_extends_preserves_same_conds {o} :
  forall (lib1 lib2 lib : @library o),
    lib_extends lib1 lib2
    -> same_conds lib1 lib
    -> same_conds lib2 lib.
Proof.
  introv ext same.
  apply lib_extends_implies_same_conds in ext; try congruence.
Qed.
Hint Resolve lib_extends_preserves_same_conds : slow.

Lemma as_lib_app {o} :
  forall (lib1 lib2 lib : @library o),
    same_conds lib1 lib
    -> MkLib (lib_pre lib1 ++ lib_pre lib2) (lib_cond lib) = lib_app lib1 lib2.
Proof.
  introv same; unfold lib_app; try congruence.
Qed.

Lemma implies_lib_extends_app {o} :
  forall (liba libb libc libd : @library o),
    lib_extends liba libc
    -> extension libb libd
    -> strong_safe_library libb
    -> sat_lib_cond liba
    -> sat_lib_cond libb
    -> same_conds liba libb
    -> lib_nodup libb
    -> lib_disjoint liba libb
    -> lib_extends (lib_app liba libb) (lib_app libc libd).
Proof.
  introv ext; revert libb libd; lib_ext_ind ext Case; introv ext' safe sata satb same nodup disj; tcsp.

  { Case "lib_ext_refl".
    apply extension_implies_lib_extends_app; auto.
    rewrite same; tcsp. }

  { Case "lib_ext_trans".
    dup disj as disj'; eapply lib_extends_preserves_lib_disjoint in disj'; eauto.
    assert (sat_lib_cond lib2) as sat' by eauto 3 with slow.
    assert (same_conds lib2 libb) as same' by eauto 3 with slow.
    pose proof (IHext2 _ _ ext' safe sat' satb same' nodup disj') as IHext2.
    eapply lib_extends_trans;[|eauto].
    apply IHext1; eauto 3 with slow. }

  { Case "lib_ext_new_abs".
    apply lib_disjoint_cons_left in disj; repnd; simpl in *.
    apply (extension_implies_lib_extends_app (lib_cond libb) _ _ lib) in ext'; eauto 3 with slow.
    repeat (rewrite as_lib_app in ext'; eauto 3 with slow;[]).
    eapply lib_extends_trans;[|eauto].
    eapply (lib_extends_new_abs (lib_app lib libb)); simpl; tcsp.
    intro xx; apply in_lib_app in xx; repndors; tcsp. }

  { Case "lib_ext_new_cs".
    apply lib_disjoint_cons_left in disj; repnd; simpl in *.
    apply (extension_implies_lib_extends_app (lib_cond libb) _ _ lib) in ext'; eauto 3 with slow.
    repeat (rewrite as_lib_app in ext'; eauto 3 with slow;[]).
    eapply lib_extends_trans;[|eauto].
    eapply (lib_extends_new_cs (lib_app lib libb)); auto.
    intro xx; apply in_lib_app in xx; repndors; tcsp. }

  { Case "lib_ext_cs".
    apply (extension_implies_lib_extends_app (lib_cond libb) _ _ lib) in ext'; eauto 3 with slow;[].
    repeat (rewrite as_lib_app in ext'; eauto 3 with slow;[]).
    eapply lib_extends_trans;[|eauto].
    eapply lib_extends_cs;[apply implies_add_one_choice_app; eauto| |]; tcsp. }

(*  { Case "lib_ext_law".
    apply (extension_implies_lib_extends_app _ _ lib) in ext'; eauto 3 with slow;[].
    eapply lib_extends_trans;[|eauto].
    eapply lib_extends_law;[apply implies_add_choice_app;eauto|]; auto. }

  { Case "lib_ext_res".
    apply (extension_implies_lib_extends_app _ _ lib) in ext'; eauto 3 with slow;[].
    eapply lib_extends_trans;[|eauto].
    eapply lib_extends_res;[apply implies_add_choice_app;eauto|]; auto. }*)
Qed.

Lemma lib_disjoint_nil {o} :
  forall (lib : @plibrary o), lib_disjoint [] lib.
Proof.
  introv i; autorewrite with slow in *; tcsp.
Qed.
Hint Resolve lib_disjoint_nil : slow.

Lemma lib_nodup_app {o} :
  forall (lib1 lib2 : @plibrary o),
    lib_nodup (lib1 ++ lib2)
    <-> (lib_nodup lib1 /\ lib_nodup lib2 /\ lib_disjoint lib1 lib2).
Proof.
  induction lib1; split; introv h; simpl in *; tcsp; repnd.
  { dands; eauto 3 with slow. }
  { apply IHlib1 in h; repnd.
    dands; tcsp; try (complete (intro xx; destruct h0; apply in_lib_app; tcsp)).
    apply lib_disjoint_cons_left; dands; tcsp.
    allrw @in_lib_app; intro xx; destruct h0; tcsp. }
  { apply lib_disjoint_cons_left in h; repnd.
    rewrite IHlib1; dands; tcsp.
    rewrite in_lib_app; tcsp. }
Qed.
Hint Rewrite @lib_nodup_app : slow.

Lemma erase_entries_upto_as_erase_entries {o} :
  forall name (lib : @plibrary o),
    ~in_lib name lib
    -> erase_entries_upto name lib
       = erase_entries lib.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  allrw @in_lib_cons; apply not_or in h; repnd.
  autodimp IHlib hyp.
  rewrite IHlib; clear IHlib.
  boolvar; tcsp.
Qed.

Lemma entry_extends_erase {o} :
  forall (e : @library_entry o),
    entry_extends e (erase_entry e).
Proof.
  destruct e; simpl; eauto.
  destruct entry as [vals restr]; simpl.
  eapply (entry_extends_ext _ [] vals).
Qed.
Hint Resolve entry_extends_erase : slow.

Lemma extension_erase_entries {o} :
  forall (lib : @plibrary o),
    extension lib (erase_entries lib).
Proof.
  induction lib; simpl; tcsp; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve extension_erase_entries : slow.

Lemma in_erase_entries {o} :
  forall e (lib : @plibrary o),
    List.In e (erase_entries lib) <-> exists e', List.In e' lib /\ e = erase_entry e'.
Proof.
  induction lib; introv; split; intro h; exrepnd; simpl in *; repndors; subst; tcsp.
  { eexists; dands; eauto. }
  { apply IHlib in h; exrepnd; eexists; dands; eauto. }
  { right; apply IHlib; eexists; dands; eauto. }
Qed.

Lemma entry2name_erase_entry {o} :
  forall (e : @library_entry o),
    entry2name (erase_entry e) = entry2name e.
Proof.
  destruct e; simpl; tcsp.
Qed.
Hint Rewrite @entry2name_erase_entry : slow.

Lemma in_lib_erase_entries {o} :
  forall n (lib : @plibrary o), in_lib n (erase_entries lib) <-> in_lib n lib.
Proof.
  introv; unfold in_lib; split; intro h; exrepnd.
  { allrw @in_erase_entries; exrepnd; subst; eexists; dands; eauto.
    autorewrite with slow in *; tcsp. }
  { exists (erase_entry e); autorewrite with slow; dands; auto.
    apply in_erase_entries; eauto. }
Qed.
Hint Rewrite @in_lib_erase_entries : slow.

Lemma implies_lib_disjoint_erase_entries_left {o} :
  forall (lib1 lib2 : @plibrary o),
    lib_disjoint lib1 lib2
    -> lib_disjoint (erase_entries lib1) lib2.
Proof.
  introv disj i j; autorewrite with slow in *.
  eapply disj; eauto.
Qed.
Hint Resolve implies_lib_disjoint_erase_entries_left : slow.

Lemma extension_preserves_lib_disjoint_right {o} :
  forall (lib lib1 lib2 : @plibrary o),
    extension lib1 lib2
    -> lib_disjoint lib lib1
    -> lib_disjoint lib lib2.
Proof.
  introv ext disj i j; apply disj in i.
  eapply extension_preserves_in_lib in j; eauto.
Qed.
Hint Resolve extension_preserves_lib_disjoint_right : slow.

Lemma implies_lib_extends_app_left0 {o} :
  forall cond (lib k : @plibrary o),
    sat_cond_lib cond lib
    -> lib_disjoint lib k
    -> lib_nodup lib
    -> strong_safe_library lib
    -> lib_extends (MkLib (lib ++ k) cond) (MkLib k cond).
Proof.
  induction lib; introv sat disj nodup safe; simpl in *; repnd; eauto.
  allrw @lib_disjoint_cons_left; repnd.
  allrw @strong_safe_library_cons; repnd.
  eapply lib_extends_trans;[|apply IHlib;auto]; eauto 3 with slow.
  apply (implies_lib_extends_cons_left a (MkLib (lib ++ k) cond)); simpl; auto;
    try (complete (autorewrite with slow; apply sat; simpl; tcsp)).
  unfold non_shadowed_entry; rewrite forallb_forall; introv i.
  unfold diff_entry_names; boolvar; tcsp.
  apply list_in_app in i; repndors; tcsp.
  { destruct nodup0; eexists; dands; eauto. }
  { destruct disj; eexists; dands; eauto. }
Qed.

Lemma lib_eta {o} :
  forall (lib : @library o),
    MkLib (lib_pre lib) (lib_cond lib) = lib.
Proof.
  destruct lib; tcsp.
Qed.
Hint Rewrite @lib_eta : slow.

Lemma implies_lib_extends_app_left {o} :
  forall (lib k : @library o),
    lib_disjoint lib k
    -> lib_nodup lib
    -> strong_safe_library lib
    -> same_conds lib k
    -> sat_lib_cond lib
    -> lib_extends (lib_app lib k) k.
Proof.
  introv disj nodup safe same sat.
  pose proof (implies_lib_extends_app_left0 (lib_cond lib) lib k) as q.
  repeat (autodimp q hyp); simpl in *.
  rewrite as_lib_app in q; tcsp.
  rewrite same in q; autorewrite with slow in *; auto.
Qed.

Lemma lib_disjoint_nil_right {o} :
  forall (lib : @plibrary o), lib_disjoint lib [].
Proof.
  introv i j; autorewrite with slow in *; tcsp.
Qed.
Hint Resolve lib_disjoint_nil_right : slow.

Lemma lib_nodup_erase_entries {o} :
  forall (lib : @plibrary o),
    lib_nodup (erase_entries lib) <-> lib_nodup lib.
Proof.
  induction lib; introv; simpl; tcsp; autorewrite with slow.
  rewrite IHlib; tcsp.
Qed.
Hint Rewrite @lib_nodup_erase_entries : slow.

Lemma extension_preserves_strong_safe_library {o} :
  forall (lib1 lib2 : @plibrary o),
    extension lib1 lib2
    -> strong_safe_library lib1
    -> strong_safe_library lib2.
Proof.
  induction lib1; introv ext safe; destruct lib2; simpl in *; repnd; tcsp.
  allrw @strong_safe_library_cons; repnd; dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve extension_preserves_strong_safe_library : slow.

Lemma lib_names_app {o} :
  forall (lib1 lib2 : @plibrary o),
    lib_names (lib1 ++ lib2) = lib_names lib1 ++ lib_names lib2.
Proof.
  introv; unfold lib_names; rewrite map_app; auto.
Qed.
Hint Rewrite @lib_names_app : slow.

Lemma lib_names_erase_entries {o} :
  forall (lib : @plibrary o),
    lib_names (erase_entries lib) = lib_names lib.
Proof.
  induction lib; simpl; tcsp; allrw; autorewrite with slow; auto.
Qed.
Hint Rewrite @lib_names_erase_entries : slow.

Lemma sat_lib_cond_nil {o} :
  forall (cond : @LibCond o), sat_lib_cond (MkLib [] cond).
Proof.
  introv i; simpl in *; tcsp.
Qed.
Hint Resolve sat_lib_cond_nil : slow.

Lemma disjoint_implies_entry_in_library_app_right {o} :
  forall e (lib1 lib2 : @plibrary o),
    lib_disjoint lib1 lib2
    -> entry_in_library e lib2
    -> entry_in_library e (lib1 ++ lib2).
Proof.
  introv disj i.
  apply implies_entry_in_library_app_right; tcsp.
  introv j m.
  pose proof (disj (entry2name e')) as disj; autodimp disj hyp.
  { exists e'; dands; eauto 3 with slow.
    apply LIn_implies_In;auto. }
  destruct disj; exists e; dands; tcsp.
  { apply entry_in_library_implies_in; auto. }
  eauto 3 with slow.
Qed.
Hint Resolve disjoint_implies_entry_in_library_app_right : slow.

Lemma sat_lib_cond_app_implies_right {o} :
  forall (lib1 lib2 : @plibrary o) cond,
    lib_disjoint lib1 lib2
    -> sat_lib_cond (MkLib (lib1 ++ lib2) cond)
    -> sat_lib_cond (MkLib lib2 cond).
Proof.
  introv disj sat i; simpl in *.
  autorewrite with slow in *.
  apply sat; simpl; eauto 3 with slow.
Qed.
Hint Resolve sat_lib_cond_app_implies_right : slow.

Lemma entry_in_erase_entries_upto_implies {o} :
  forall entry name (lib : @plibrary o),
    entry_in_library entry (erase_entries_upto name lib)
    -> exists entry', entry_in_library entry' lib /\ entry = erase_entry entry'.
Proof.
  induction lib; introv i; simpl in *; tcsp; boolvar; subst; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp.
  { exists a; dands; tcsp. }
  { apply IHlib in i; exrepnd; subst; simpl in *.
    exists entry'; dands; tcsp.
    right; dands; tcsp.
    destruct entry', a; simpl in *; tcsp. }
Qed.

Lemma entry_in_erase_entries {o} :
  forall e (lib : @plibrary o),
    entry_in_library e (erase_entries lib) <-> exists e', entry_in_library e' lib /\ e = erase_entry e'.
Proof.
  induction lib; introv; split; intro h; exrepnd; simpl in *; repndors; repnd; subst; tcsp.
  { eexists; dands; eauto. }
  { applydup IHlib in h; clear IHlib; exrepnd; subst.
    exists e'; dands; tcsp; right; dands; tcsp.
    introv xx; destruct h0; eauto 3 with slow. }
  { right; dands; tcsp; eauto 3 with slow.
    { intro xx; destruct h2; eauto 3 with slow. }
    apply IHlib; exists e'; dands; tcsp. }
Qed.

Lemma sat_cond_choices_nil {o} :
  forall (cond : @LibCond o), sat_cond_choices cond [].
Proof.
  introv i; simpl in *; tcsp.
Qed.
Hint Resolve sat_cond_choices_nil : slow.

Lemma implies_sat_cond_entry_erase_entry {o} :
  forall cond (e : @library_entry o),
    sat_cond_entry cond e
    -> sat_cond_entry cond (erase_entry e).
Proof.
  introv sat; destruct e; simpl in *; tcsp.
  destruct entry as [vals restr]; simpl in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve implies_sat_cond_entry_erase_entry : slow.

Lemma sat_lib_cond_erase_entries {o} :
  forall (lib : @plibrary o) cond,
    sat_lib_cond (MkLib lib cond)
    -> sat_lib_cond (MkLib (erase_entries lib) cond).
Proof.
  introv sat i; simpl in *.
  apply entry_in_erase_entries in i; exrepnd; subst; simpl in *.
  apply sat in i1; simpl in *.
  autorewrite with slow in *; eauto 3 with slow.
Qed.
Hint Resolve sat_lib_cond_erase_entries : slow.

Lemma lib_extends_erase_choices_upto {o} :
  forall (lib2 lib1 : @library o) name,
    has_first_name name lib1
    -> strong_safe_library lib1
    -> sat_lib_cond lib1
    -> lib_nodup lib1
    -> lib_extends lib2 lib1
    -> lib_extends lib2 (inc_cs_lib name lib2 lib1)
       /\ lib_extends (inc_cs_lib name lib2 lib1) lib1
       /\ lib_names lib2 = lib_names (inc_cs_lib name lib2 lib1).
Proof.
  introv hf safe sat nodup ext.
  unfold has_first_name, inc_cs_lib, pre_inc_cs_lib in *.
  destruct lib1 as [lib1 cond1]; simpl in *.
  destruct lib1 as [|e lib1]; tcsp; subst; simpl in *.

  assert (entry_in_library e (e :: lib1)) as i by (simpl; tcsp).
  applydup @implies_lib_extends_ext in ext.
  apply ext0 in i; clear ext0.
  apply entry_in_library_extends_implies_entry_in_library in i; exrepnd.
  apply entry_in_library_split in i1; exrepnd; subst.
  destruct lib2 as [lib2 cond2]; simpl in *; subst; simpl in *.
  applydup @lib_extends_implies_same_conds in ext as same.
  unfold same_conds in same; simpl in *; subst.

  rewrite (erase_entries_upto_app_not_in_left _ lib0);
    try (complete (inversion i0; subst; eauto 3 with slow; intro xx;
                   eapply same_entry_name_preserves_in_lib in xx; eauto)).
  simpl.
  boolvar; try (complete (inversion i0; subst; tcsp)); autorewrite with slow.
  dup ext as ext'.
  apply (in_lib_extends_implies_split _ _ e) in ext'; simpl; auto; eauto 3 with slow.
  exrepnd.
  inversion ext'0 as [w1]; subst; simpl in *; clear ext'0.
  inversion ext'2 as [w2]; subst; simpl in *; clear ext'2.
  assert (e :: lib1 = [] ++ e :: lib1) as xx by (simpl; auto).
  rewrite xx in w2; clear xx.
  apply eq_app_cons_implies in w2; simpl; eauto 3 with slow; repnd; subst; simpl in *; GC.
  apply eq_app_cons_implies in w1; simpl; eauto 3 with slow; repnd; subst; simpl in *; GC;
    try (complete (allapply @entry_extends_implies_same_entry_name; eauto 3 with slow)).

  applydup @lib_extends_preserves_strong_safe_library in ext as safe'; simpl in *; auto;[].
  allrw @strong_safe_library_app; repnd.
  allrw @strong_safe_library_cons; repnd.
  applydup @lib_extends_preserves_nodup in ext as ext'; simpl in *; tcsp;[].
  allrw @lib_nodup_app; simpl in *; repnd.
  allrw @lib_disjoint_cons_right; repnd.

  rewrite erase_entries_upto_as_erase_entries;
    try (complete (intro xx; eapply same_entry_name_preserves_in_lib in s; eauto)).
  dands.

  { apply (implies_lib_extends_app
             (MkLib liba cond)
             (MkLib (e' :: libb) cond)
             (MkLib (erase_entries liba) cond)
             (MkLib (e :: libd) cond)); simpl;
      allrw @strong_safe_library_cons;
      allrw @lib_disjoint_cons_right;
      simpl; dands; eauto 3 with slow; tcsp;
        try (complete (eapply sat_lib_cond_app_implies_right;[|eauto 3 with slow];
                       allrw @lib_disjoint_cons_right; tcsp)).
    apply extension_implies_lib_extends; simpl; eauto 3 with slow; tcsp. }

  { assert (e :: libd = [] ++ e :: libd) as xx by (simpl; auto); rewrite xx at 2; clear xx.
    apply (implies_lib_extends_app
             (MkLib (erase_entries liba) cond)
             (MkLib (e :: libd) cond)
             (MkLib [] cond)
             (MkLib (e :: libd) cond)); simpl;
      allrw @strong_safe_library_cons;
      allrw @lib_disjoint_cons_right;
      autorewrite with slow; simpl; dands; eauto 3 with slow; tcsp;
        try (complete (allapply @entry_extends_implies_same_entry_name;
                       intro xx; eapply same_entry_name_preserves_in_lib in xx;
                       try apply same_entry_name_sym; eauto));[].
    assert (erase_entries liba = erase_entries liba ++ []) as xx by (autorewrite with slow; auto); rewrite xx; clear xx.
    apply (implies_lib_extends_app_left
             (MkLib (erase_entries liba) cond)
             (MkLib [] cond)); simpl; autorewrite with slow; eauto 3 with slow; tcsp. }

  { autorewrite with slow; simpl.
    allapply @extension_implies_same_names; allrw.
    allapply @entry_extends_implies_same_entry2name; allrw; auto. }
Qed.

Lemma find_cs_value_at_nil {o} :
  forall name m, @find_cs_value_at o [] name m = None.
Proof.
  tcsp.
Qed.
Hint Rewrite @find_cs_value_at_nil : slow.

Lemma entry_in_pre_replace_cs_entry_implies {o} :
  forall entry (lib : @plibrary o) name e,
    entry_in_library entry (pre_replace_cs_entry lib name e)
    -> (entry_in_library entry lib \/ entry = lib_cs name e).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp; simpl in *; repndors; repnd; subst; tcsp;
    apply IHlib in i; repndors; subst; tcsp.
Qed.

Lemma entry_in_inc_cs_lib_implies {o} :
  forall entry name (lib2 lib1 : @plibrary o),
    entry_in_library entry (pre_inc_cs_lib name lib2 lib1)
    -> (entry_in_library entry lib1
        \/ exists entry', entry_in_library entry' lib2 /\ entry = erase_entry entry').
Proof.
  introv i.
  unfold inc_cs_lib in i.
  apply entry_in_library_app_implies in i; repndors; repnd; tcsp.
  apply entry_in_erase_entries_upto_implies in i; exrepnd; eauto.
Qed.

Lemma implies_safe_library_pre_replace_cs_entry {o} :
  forall (lib : @plibrary o) name e,
    safe_library lib
    -> safe_choice_sequence_entry name e
    -> safe_library (pre_replace_cs_entry lib name e).
Proof.
  introv safea safeb i.
  apply entry_in_pre_replace_cs_entry_implies in i; repndors; subst; simpl in *; tcsp.
Qed.
Hint Resolve implies_safe_library_pre_replace_cs_entry : slow.

Lemma implies_safe_library_replace_cs_entry {o} :
  forall (lib : @library o) name e,
    safe_library lib
    -> safe_choice_sequence_entry name e
    -> safe_library (replace_cs_entry lib name e).
Proof.
  introv safea safeb.
  destruct lib as [lib cond]; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve implies_safe_library_replace_cs_entry : slow.

Lemma implies_safe_erase_entry {o} :
  forall (entry : @library_entry o),
    safe_library_entry entry
    -> safe_library_entry (erase_entry entry).
Proof.
  introv safe; destruct entry; simpl in *; tcsp.
  destruct entry as [vals restr]; simpl in *; repnd; dands; tcsp; eauto 3 with slow.
Qed.

Lemma implies_safe_pre_inc_cs_lib {o} :
  forall name (lib2 lib1 : @plibrary o),
    safe_library lib2
    -> safe_library lib1
    -> safe_library (pre_inc_cs_lib name lib2 lib1).
Proof.
  introv safea safeb i.
  apply entry_in_inc_cs_lib_implies in i; repndors; exrepnd; subst; auto.
  apply implies_safe_erase_entry; eauto.
Qed.
Hint Resolve implies_safe_pre_inc_cs_lib : slow.

Lemma implies_safe_inc_cs_lib {o} :
  forall name (lib2 lib1 : @library o),
    safe_library lib2
    -> safe_library lib1
    -> safe_library (inc_cs_lib name lib2 lib1).
Proof.
  introv safea safeb.
  destruct lib2 as [lib2 cond2]; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve implies_safe_inc_cs_lib : slow.

Lemma implies_choice_sequence_satisfies_restriction_firstn {o} :
  forall n (vals : @ChoiceSeqVals o) restr,
    choice_sequence_satisfies_restriction vals restr
    -> choice_sequence_satisfies_restriction (firstn n vals) restr.
Proof.
  introv sat.
  pose proof (firstn_skipn n vals) as h.
  rewrite <- h in sat; clear h.
  eapply choice_sequence_satisfies_restriction_app_implies; eauto.
Qed.
Hint Resolve implies_choice_sequence_satisfies_restriction_firstn : slow.

Lemma implies_safe_firstn_cs_entry {o} :
  forall name n (c : @ChoiceSeqEntry o),
    safe_choice_sequence_entry name c
    -> safe_choice_sequence_entry name (firstn_cs_entry n c).
Proof.
  introv safe.
  destruct c as [vals restr]; simpl in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve implies_safe_firstn_cs_entry : slow.

Lemma lib_depth_app {o} :
  forall (lib1 lib2 : @plibrary o),
    lib_depth (lib1 ++ lib2) = Init.Nat.max (lib_depth lib1) (lib_depth lib2).
Proof.
  induction lib1; introv; simpl; tcsp.
  rewrite IHlib1; clear IHlib1.
  rewrite Nat.max_assoc; auto.
Qed.

Lemma entry_depth_erase_entry {o} :
  forall (e : @library_entry o),
    entry_depth (erase_entry e) = 0.
Proof.
  destruct e; simpl; auto.
  destruct entry as [vals restr]; simpl; auto.
Qed.
Hint Rewrite @entry_depth_erase_entry : slow.

Lemma lib_depth_erase_entries_upto {o} :
  forall name (lib : @plibrary o),
    lib_depth (erase_entries_upto name lib) = 0.
Proof.
  induction lib; simpl; tcsp.
  boolvar; simpl; allrw; tcsp; autorewrite with slow; auto.
Qed.
Hint Rewrite @lib_depth_erase_entries_upto : slow.

Lemma lib_depth_inc_cs_lib {o} :
  forall name (lib2 lib1 : @plibrary o),
    lib_depth (pre_inc_cs_lib name lib2 lib1) = lib_depth lib1.
Proof.
  introv; unfold inc_cs_lib, pre_inc_cs_lib.
  rewrite lib_depth_app; autorewrite with slow; simpl; auto.
Qed.
Hint Rewrite @lib_depth_inc_cs_lib : slow.

Lemma strong_safe_library_implies_safe_choice_sequence_entry {o} :
  forall (lib : @library o) name c,
    find_cs lib name = Some c
    -> strong_safe_library lib
    -> safe_choice_sequence_entry name c.
Proof.
  introv fcs safe.
  apply find_cs_some_implies_list_in in fcs.
  apply safe in fcs; tcsp.
Qed.
Hint Resolve strong_safe_library_implies_safe_choice_sequence_entry : slow.

Lemma find_cs_pre_replace_cs_entry {o} :
  forall (lib : @plibrary o) name e name',
    find_cs (pre_replace_cs_entry lib name e) name'
    = if choice_sequence_name_deq name name'
      then match find_cs lib name with
           | Some _ => Some e
           | None => None
           end
      else find_cs lib name'.
Proof.
  induction lib; introv; simpl in *; ginv; boolvar; subst; tcsp;
    destruct a; simpl in *; repeat (boolvar; subst; tcsp; simpl in *; tcsp; GC; ginv);
      rewrite IHlib; boolvar; tcsp.
Qed.

Lemma find_cs_replace_cs_entry {o} :
  forall (lib : @library o) name e name',
    find_cs (replace_cs_entry lib name e) name'
    = if choice_sequence_name_deq name name'
      then match find_cs lib name with
           | Some _ => Some e
           | None => None
           end
      else find_cs lib name'.
Proof.
  introv; destruct lib as [lib cond]; simpl.
  apply find_cs_pre_replace_cs_entry.
Qed.

Lemma eq_lib_names_preserves_find_cs {o} :
  forall (lib2 lib1 : @plibrary o) name c,
    lib_names lib2 = lib_names lib1
    -> find_cs lib2 name = Some c
    -> exists x, find_cs lib1 name = Some x.
Proof.
  induction lib2; introv eqn fcs; simpl in *; destruct lib1; simpl in *; tcsp.
  destruct a, l; simpl in *; boolvar; subst; ginv; tcsp;
    try apply cons_inj in eqn; repnd; ginv; eauto; tcsp.
Qed.

Lemma implies_eq_firstn :
  forall {T} n (l k : list T),
    (forall i, i < n -> select i l = select i k)
    -> firstn n l = firstn n k.
Proof.
  induction n; introv imp; simpl; tcsp.
  destruct l, k; simpl in *; tcsp;
    pose proof (imp 0) as q; autodimp q hyp; try omega; simpl in *; ginv.
  f_equal; apply IHn; introv h.
  pose proof (imp (S i)) as imp; simpl in *; apply imp; try omega.
Qed.

Lemma select_firstn :
  forall {T} n k (l : list T),
    select n (firstn k l)
    = if le_dec k n then None
      else select n l.
Proof.
  induction n; introv; simpl; destruct k, l; simpl; tcsp; boolvar; subst; tcsp;
    rewrite IHn; boolvar; try omega; auto.
Qed.

Lemma is_nat_cs_implies_sane_swapping :
  forall name name',
    is_nat_cs name
    -> is_nat_cs name'
    -> sane_swapping (name,name').
Proof.
  introv isna isnb.
  unfold sane_swapping, is_nat_cs, compatible_choice_sequences in *.
  destruct name as [n1 k1], name' as [n2 k2], k1, k2; simpl in *; tcsp.
  destruct n, n0; simpl in *; tcsp.
Qed.
Hint Resolve is_nat_cs_implies_sane_swapping : slow.

Lemma swap_cs_name :
  forall name name',
    swap_cs (name,name') name = name'.
Proof.
  introv; unfold swap_cs; boolvar; tcsp.
Qed.
Hint Rewrite swap_cs_name : slow.

Lemma is_nat_cs_correct_restriction_implies {o} :
  forall name (restr : @ChoiceSeqRestriction o),
    is_nat_cs name
    -> correct_restriction name restr
    -> is_nat_restriction restr.
Proof.
  introv isn cor.
  unfold correct_restriction, is_nat_cs in *.
  destruct name as [n k], k in *; simpl in *; tcsp.
  destruct n0; simpl in *; tcsp; GC.
Qed.
Hint Resolve is_nat_cs_correct_restriction_implies : slow.

Lemma is_nat_restriction_implies_swap_cs_choice_seq_restr_eq {o} :
  forall sw (restr : @ChoiceSeqRestriction o),
    is_nat_restriction restr
    -> swap_cs_choice_seq_restr sw restr = restr.
Proof.
  introv isn.
  unfold is_nat_restriction in isn.
  destruct restr; simpl in *.
  { f_equal; simpl.
    apply functional_extensionality; introv; simpl.
    apply functional_extensionality; introv; simpl.
    unfold swap_cs_restriction_pred; simpl.
    apply propositional_extensionality; allrw; autorewrite with slow; tcsp. }
Qed.

Lemma swap_cs_plib_keep_only_pre_nat {o} :
  forall name name' (lib : @plibrary o),
    is_nat_cs name
    -> safe_library lib
    -> find_cs lib name = find_cs lib name'
    -> (forall (m : nat) (v : ChoiceSeqVal), find_cs_value_at lib name m = Some v -> is_nat m v)
    -> swap_cs_plib (name,name') (keep_only_pre name lib)
       = keep_only_pre name' lib.
Proof.
  introv isn safe eqfcs cond.
  repeat rewrite keep_only_equal.
  remember (find_cs lib name) as fcs; symmetry in Heqfcs.
  rewrite <- eqfcs; symmetry in eqfcs.
  destruct fcs; simpl; auto.
  boolvar; subst; tcsp; GC.
  f_equal; f_equal.

  applydup @find_cs_some_implies_entry_in_library in Heqfcs as i.
  apply safe in i; simpl in *.

  destruct c as [vals restr]; simpl in *; repnd.
  apply is_nat_cs_correct_restriction_implies in i0; auto.

  f_equal.

  { unfold swap_cs_choice_seq_vals.
    apply eq_map_l; introv j.
    unfold find_cs_value_at in cond.
    rewrite Heqfcs in cond; simpl in *.
    apply in_implies_select in j; exrepnd.
    pose proof (cond n x) as cond.
    rewrite find_value_of_cs_at_is_select in cond; autodimp cond hyp.
    unfold is_nat in cond; exrepnd; subst; autorewrite with slow; auto. }

  { rewrite is_nat_restriction_implies_swap_cs_choice_seq_restr_eq; auto. }
Qed.

Definition get_cs_c {p} (c : @CanonicalOp p) : list choice_sequence_name :=
  match c with
  | Ncseq c => [c]
  | _ => []
  end.

Definition get_cs_o {p} (o : @Opid p) : list choice_sequence_name :=
  match o with
  | Can c => get_cs_c c
  | _ => []
  end.

Fixpoint get_cs {p} (t : @NTerm p) : list choice_sequence_name :=
  match t with
  | vterm _ => []
  | oterm o bterms => (get_cs_o o) ++ (flat_map get_cs_b bterms)
  end
with get_cs_b {p} (bt : @BTerm p) : list choice_sequence_name :=
       match bt with
       | bterm _ t => get_cs t
       end.

Definition im_swap_cs_restr {o} (r : @ChoiceSeqRestriction o) :=
  forall sw, swap_cs_choice_seq_restr sw r = r.

Definition lib_cond_no_cs {o} (cond : @LibCond o) :=
  (forall v, cond (lck_term v) <-> get_cs v = [])
  /\ (forall r, cond (lck_restr r) <-> im_swap_cs_restr r).

Definition has_lib_cond_no_cs {o} (lib : @library o) :=
  lib_cond_no_cs (lib_cond lib).

Definition im_swap_cs_entry {o} (e : @ChoiceSeqEntry o) :=
  im_swap_cs_restr (cse_restriction e).

Definition im_swap_lib {o} (lib : @plibrary o) :=
  forall name e,
    find_cs lib name = Some e
    -> im_swap_cs_entry e.

Lemma im_swap_cs_restr_csc_nat {o} :
  im_swap_cs_restr (@csc_nat o).
Proof.
  introv.
  simpl; unfold csc_nat; f_equal.
  apply functional_extensionality; introv.
  apply functional_extensionality; introv.
  unfold swap_cs_restriction_pred.
  apply propositional_extensionality.
  apply is_nat_swap_cs_cterm.
Qed.

Lemma get_cs_swap_cs_term_nil_iff {o} :
  forall sw (t : @NTerm o),
    get_cs (swap_cs_term sw t) = [] <-> get_cs t = [].
Proof.
  nterm_ind t as [v|op vs ind] Case; simpl; tcsp.
  split; intro h; allrw app_eq_nil_iff; repnd; dands;
    try (complete (destruct op; simpl in *; tcsp;
                   destruct c; simpl in *; tcsp)).

  { allrw flat_map_map; unfold compose in *.
    allrw flat_map_empty; introv i.
    destruct a; simpl in *.
    applydup h in i; simpl in *.
    eapply ind; eauto. }

  { allrw flat_map_map; unfold compose in *.
    allrw flat_map_empty; introv i.
    destruct a; simpl in *.
    applydup h in i; simpl in *.
    eapply ind; eauto. }
Qed.

Lemma swap_cs_lib_keep_only_nat {o} :
  forall name name' (lib : @library o),
    is_nat_cs name
    -> has_lib_cond_no_cs lib
    -> safe_library lib
    -> find_cs lib name = find_cs lib name'
    -> (forall (m : nat) (v : ChoiceSeqVal), find_cs_value_at lib name m = Some v -> is_nat m v)
    -> swap_cs_lib (name,name') (keep_only name lib)
       = keep_only name' lib.
Proof.
  introv isn nocs safe eqfcs cond.
  destruct lib as [lib c]; simpl in *.
  unfold swap_cs_lib, keep_only; simpl.
  rewrite swap_cs_plib_keep_only_pre_nat; auto.
  f_equal.

  apply functional_extensionality; introv; simpl.
  unfold swap_cs_lib_cond; simpl in *.
  unfold has_lib_cond_no_cs in *; simpl in *.
  unfold lib_cond_no_cs in *; repnd.

  apply propositional_extensionality.
  destruct x; simpl; tcsp.
  { repeat rewrite nocs0.
    apply get_cs_swap_cs_term_nil_iff. }
  { split; intro x; dup x as xx; rewrite nocs in x; pose proof (x (name,name')) as x; try congruence.
    rewrite swap_cs_choice_seq_restr_idem in x; rewrite <- x in xx; auto. }
Qed.

Lemma lib_extends_replace_cs_entry_between1 {o} :
  forall name e e' (lib2 lib1 : @library o),
    sat_lib_cond lib1
    -> safe_library lib1
    -> find_cs lib2 name = Some e
    -> cs_entry_between name e e' lib1
    -> lib_extends lib2 lib1
    -> lib_extends (replace_cs_entry lib1 name e') lib1.
Proof.
  introv sat safe find btw ext; eapply lib_extends_pre_replace_cs_entry_between; eauto.
Qed.

Lemma lib_extends_replace_cs_entry_between2 {o} :
  forall name e e' (lib2 lib1 : @library o),
    sat_lib_cond lib1
    -> safe_library lib1
    -> find_cs lib2 name = Some e
    -> cs_entry_between name e e' lib1
    -> lib_extends lib2 lib1
    -> lib_extends lib2 (replace_cs_entry lib1 name e').
Proof.
  introv sat safe find btw ext; eapply lib_extends_pre_replace_cs_entry_between; eauto.
Qed.

Lemma implies_equality_swap_cs {o} :
  forall sw (lib : @library o) T t1 t2,
    sane_swapping sw
    -> equality lib t1 t2 T
    -> equality (swap_cs_lib sw lib) (swap_cs_cterm sw t1) (swap_cs_cterm sw t2) (swap_cs_cterm sw T).
Proof.
  introv sane equ.
  unfold equality in *; exrepnd.
  apply (implies_nuprl_swap_cs sw) in equ1; auto.
  exists (swap_cs_per sw eq).
  dands; tcsp.
  unfold swap_cs_per; autorewrite with slow; auto.
Qed.

Lemma implies_member_swap_cs {o} :
  forall sw (lib : @library o) T t,
    sane_swapping sw
    -> member lib t T
    -> member (swap_cs_lib sw lib) (swap_cs_cterm sw t) (swap_cs_cterm sw T).
Proof.
  introv sane equ.
  unfold member in *; apply implies_equality_swap_cs; auto.
Qed.

Lemma lib_cond_sat_entry_replace_cs_entry {o} :
  forall (lib : @library o) name e x,
    lib_cond_sat_entry (replace_cs_entry lib name e) x
    <-> lib_cond_sat_entry lib x.
Proof.
  introv; tcsp.
Qed.
Hint Rewrite @lib_cond_sat_entry_replace_cs_entry : slow.

Lemma sat_lib_cond_replace_cs_entry {o} :
  forall (lib : @library o) name e,
    lib_cond_sat_cs_entry lib e
    -> sat_lib_cond lib
    -> sat_lib_cond (replace_cs_entry lib name e).
Proof.
  introv sata satb i; simpl in *.
  apply entry_in_pre_replace_cs_entry_implies in i; repndors; subst; tcsp.
  autorewrite with slow; apply satb in i; tcsp.
Qed.
Hint Resolve sat_lib_cond_replace_cs_entry : slow.

Lemma lib_cond_sat_cs_entry_inc_cs_lib {o} :
  forall name (lib2 lib1 : @library o) e,
    lib_cond_sat_cs_entry (inc_cs_lib name lib2 lib1) e
    <-> lib_cond_sat_cs_entry lib2 e.
Proof.
  tcsp.
Qed.
Hint Rewrite @lib_cond_sat_cs_entry_inc_cs_lib : slow.

Lemma implies_lib_cond_sat_cs_entry_firstn_cs_entry {o} :
  forall (lib : @library o) n e,
    lib_cond_sat_cs_entry lib e
    -> lib_cond_sat_cs_entry lib (firstn_cs_entry n e).
Proof.
  introv sat.
  destruct e as [vals restr]; simpl in *; repnd; dands; tcsp.
  introv i; apply in_firstn in i; tcsp.
Qed.
Hint Resolve implies_lib_cond_sat_cs_entry_firstn_cs_entry : slow.

Lemma find_cs_implies_lib_cond_sat_cs_entry {o} :
  forall (lib : @library o) name c,
    sat_lib_cond lib
    -> find_cs lib name = Some c
    -> lib_cond_sat_cs_entry lib c.
Proof.
  introv sat fcs.
  apply find_cs_some_implies_entry_in_library in fcs.
  apply sat in fcs; simpl in *; tcsp.
Qed.
Hint Resolve find_cs_implies_lib_cond_sat_cs_entry : slow.

Lemma lib_cond_sat_entry_inc_cs_lib {o} :
  forall name (lib2 lib1 : @library o) e,
    lib_cond_sat_entry (inc_cs_lib name lib2 lib1) e
    <-> lib_cond_sat_entry lib2 e.
Proof.
  tcsp.
Qed.
Hint Rewrite @lib_cond_sat_entry_inc_cs_lib : slow.

Lemma sat_lib_cond_inc_cs_lib {o} :
  forall name (lib2 lib1 : @library o),
    same_conds lib1 lib2
    -> sat_lib_cond lib2
    -> sat_lib_cond lib1
    -> sat_lib_cond (inc_cs_lib name lib2 lib1).
Proof.
  introv same sata satb i; simpl in *.
  unfold pre_inc_cs_lib in *.
  apply entry_in_library_app_implies in i; repndors; repnd; autorewrite with slow in *; eauto 3 with slow.
  apply entry_in_erase_entries_upto_implies in i; exrepnd; subst; eauto 3 with slow.
Qed.
Hint Resolve sat_lib_cond_inc_cs_lib : slow.

Definition name_in_lib {o} name (lib : @plibrary o) :=
  match find_cs lib name with
  | Some _ => True
  | None => False
  end.

Definition swap_in_lib {o} (sw : cs_swap) (lib : @plibrary o) :=
  let (n1,n2) := sw in
  n1 <> n2
  /\ name_in_lib n1 lib
  /\ name_in_lib n2 lib.

Lemma find_cs_erase_entries {o} :
  forall (lib : @plibrary o) name,
    find_cs (erase_entries lib) name
    = match find_cs lib name with
      | Some e => Some (erase_choices_entry e)
      | None => None
      end.
Proof.
  induction lib; introv; simpl; tcsp.
  destruct a; simpl; tcsp; boolvar; subst; tcsp.
Qed.
Hint Rewrite @find_cs_erase_entries : slow.

Lemma name_in_lib_erase_entries {o} :
  forall name (lib : @plibrary o),
    name_in_lib name (erase_entries lib) <-> name_in_lib name lib.
Proof.
  introv; unfold name_in_lib.
  rewrite find_cs_erase_entries.
  remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; tcsp.
Qed.
Hint Rewrite @name_in_lib_erase_entries : slow.

Lemma find_cs_some_implies_name_in_lib {o} :
  forall name (lib : @plibrary o) e,
    find_cs lib name = Some e
    -> name_in_lib name lib.
Proof.
  introv fcs; unfold name_in_lib; allrw; auto.
Qed.
Hint Resolve find_cs_some_implies_name_in_lib : slow.

Lemma lib_extends_erase_entries {o} :
  forall (lib : @library o) cond,
    cond = lib_cond lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> lib_nodup lib
    -> lib_extends lib (MkLib (erase_entries lib) cond).
Proof.
  introv same sat safe nodup.
  apply extension_implies_lib_extends; simpl; eauto 3 with slow.
  unfold same_conds; simpl; auto.
Qed.

Lemma find_cs_value_at_erase_entries {o} :
  forall (lib : @plibrary o) name n,
    find_cs_value_at (erase_entries lib) name n = None.
Proof.
  introv; unfold find_cs_value_at; autorewrite with slow.
  remember (find_cs lib name) as fcs; destruct fcs; auto.
  rewrite find_value_of_cs_at_is_select.
  destruct c as [vals restr]; simpl in *; autorewrite with slow; auto.
Qed.
Hint Rewrite @find_cs_value_at_erase_entries : slow.

Lemma not_in_lib_implies_non_shadowed_entry {o} :
  forall a (lib : @plibrary o),
    ~ in_lib (entry2name a) lib
    -> non_shadowed_entry a lib.
Proof.
  introv ni.
  unfold non_shadowed_entry; rewrite forallb_forall; introv i.
  apply non_matching_entries_iff_diff_entry_names_true; intro xx; destruct ni.
  exists x; dands; tcsp.
Qed.
Hint Resolve not_in_lib_implies_non_shadowed_entry : slow.

Lemma lib_extends_nil {o} :
  forall cond (lib : @plibrary o),
    sat_cond_lib cond lib
    -> strong_safe_library lib
    -> lib_nodup lib
    -> lib_extends (MkLib lib cond) (MkLib [] cond).
Proof.
  induction lib; introv sat safe nodup; simpl in *; auto.
  autorewrite with slow in *; repnd.
  apply not_in_sat_cond_lib_cons_implies in sat; auto; repnd.
  eapply lib_extends_trans;[|apply IHlib]; auto; clear IHlib.
  apply (implies_lib_extends_cons_left a (MkLib lib cond)); simpl; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_nil : slow.

Lemma implies_sat_cond_lib_erase_entries {o} :
  forall cond (lib : @plibrary o),
    sat_cond_lib cond lib
    -> sat_cond_lib cond (erase_entries lib).
Proof.
  introv sat i.
  apply entry_in_erase_entries in i; exrepnd; subst; simpl in *.
  apply sat in i1; clear sat.
  destruct e'; simpl in *; tcsp.
  destruct entry as [vals restr]; simpl in *; repnd; dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve implies_sat_cond_lib_erase_entries : slow.

Lemma find_cs_none_implies_not_list_in {o} :
  forall (lib : @plibrary o) name e,
    find_cs lib name = None -> ~List.In (lib_cs name e) lib.
Proof.
  induction lib; introv fcs i; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; subst; repndors; ginv; tcsp; apply IHlib in i; auto.
Qed.

Lemma name_in_lib_as_in_lib {o} :
  forall name (lib : @plibrary o),
    name_in_lib name lib <-> in_lib (entry_name_cs name) lib.
Proof.
  introv; unfold name_in_lib, in_lib; split; intro h.

  { remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; GC; tcsp.
    exists (lib_cs name c); simpl; dands; tcsp; eauto 3 with slow. }

  { exrepnd; destruct e; simpl in *; subst; tcsp.
    remember (find_cs lib name0) as fcs; symmetry in Heqfcs; destruct fcs; auto.
    apply find_cs_none_implies_not_list_in in h1; auto. }
Qed.

Lemma eq_lib_names_preserves_list_in {o} :
  forall (lib1 lib2 : @plibrary o) e,
    lib_names lib1 = lib_names lib2
    -> List.In e lib1
    -> exists e',
        List.In e' lib2
        /\ same_entry_name (entry2name e) (entry2name e').
Proof.
  induction lib1; introv eqnames i; simpl in *; tcsp.
  destruct lib2; simpl in *; tcsp; ginv.
  apply cons_inj in eqnames; repnd.
  repndors; subst; tcsp.
  { exists l; dands; tcsp; allrw; eauto 3 with slow. }
  eapply IHlib1 in i; eauto; exrepnd.
  exists e'; dands; tcsp.
Qed.

Lemma eq_lib_names_preserves_in_lib {o} :
  forall (lib2 lib1 : @plibrary o) name,
    lib_names lib1 = lib_names lib2
    -> in_lib name lib1
    -> in_lib name lib2.
Proof.
  introv eqnames i; unfold in_lib in *; exrepnd.
  eapply eq_lib_names_preserves_list_in in i1; eauto; exrepnd.
  exists e'; dands; tcsp.
  eapply same_entry_name_trans;eauto.
Qed.

Lemma to_library_with_equal_cs {o} :
  forall name name' (lib2 lib1 : @library o),
    is_nat_cs name
    -> is_nat_cs name'
    -> strong_safe_library lib1
    -> sat_lib_cond lib1
    -> lib_nodup lib1
    -> lib_extends lib2 lib1
    -> (forall m,
           m <= lib_depth lib1
           -> {k : nat
               $ find_cs_value_at lib2 name m = Some (mkc_nat k)
               # find_cs_value_at lib2 name' m = Some (mkc_nat k)})
    -> exists lib,
        lib_extends lib lib1
        /\ lib_extends lib2 lib
        /\ find_cs lib name = find_cs lib name'
        /\ name_in_lib name lib
        /\ name_in_lib name' lib
        /\ (forall m v, find_cs_value_at lib name m = Some v -> is_nat m v).
Proof.
  introv isna isnb safe sat nodup ext imp.

  remember (find_cs lib2 name) as fcsa; symmetry in Heqfcsa.
  destruct fcsa;
    try (complete (pose proof (imp 0) as imp; autodimp imp hyp; try omega; exrepnd;
                   unfold find_cs_value_at in *; rewrite Heqfcsa in *; ginv)).

  remember (find_cs lib2 name') as fcsb; symmetry in Heqfcsb.
  destruct fcsb;
    try (complete (pose proof (imp 0) as imp; autodimp imp hyp; try omega; exrepnd;
                   unfold find_cs_value_at in *; rewrite Heqfcsb in *; ginv)).

  destruct (dec_has_first_name lib1) as [d|d]; exrepnd; subst; simpl in *.

  { destruct lib1 as [lib1 cond1]; simpl in *; subst; simpl in *.
    applydup @lib_extends_implies_same_conds in ext as same; unfold same_conds in same; simpl in *; subst.
    applydup @lib_extends_preserves_sat_lib_cond in ext as sat'; eauto 3 with slow.
    applydup @lib_extends_preserves_safe in ext as safe'; eauto 3 with slow.
    exists (MkLib (erase_entries lib2) (lib_cond lib2)); simpl; dands;
      autorewrite with slow; eauto 3 with slow;
        try (complete (apply lib_extends_erase_entries; eauto 3 with slow));
        try (complete (introv fcs; autorewrite with slow in fcs; ginv));
        try (complete (apply lib_extends_nil; simpl; autorewrite with slow; eauto 3 with slow));[].

    allrw.
    apply find_cs_some_implies_entry_in_library in Heqfcsa; apply safe' in Heqfcsa.
    apply find_cs_some_implies_entry_in_library in Heqfcsb; apply safe' in Heqfcsb.
    simpl in *.
    destruct c as [vals1 r1], c0 as [vals2 r2]; simpl in *; repnd.
    apply is_nat_cs_correct_restriction_implies in Heqfcsa0; auto.
    apply is_nat_cs_correct_restriction_implies in Heqfcsb0; auto.
    f_equal; f_equal.
    destruct r1, r2; simpl in *; f_equal.
    apply functional_extensionality; introv.
    apply functional_extensionality; introv.
    apply propositional_extensionality.
    allrw; tcsp. }

(*
    exists (MkLib [] cond1 : @library o); simpl; dands; eauto 3 with slow.
    introv find; autorewrite with slow in *; ginv. }*)

  assert (strong_safe_library lib2) as safe' by eauto 3 with slow.

  exists (replace_cs_entry
            (replace_cs_entry
               (inc_cs_lib name0 lib2 lib1)
               name (firstn_cs_entry (lib_depth lib1 + 1) c))
            name' (firstn_cs_entry (lib_depth lib1 + 1) c0)).
  dands.

  { eapply lib_extends_trans.
    { eapply lib_extends_replace_cs_entry_between1; eauto; eauto 3 with slow.
      { apply sat_lib_cond_replace_cs_entry; autorewrite with slow; eauto 4 with slow. }
      { apply implies_safe_library_replace_cs_entry; eauto 4 with slow. }
      { pose proof (lib_depth_inc_cs_lib name0 lib2 lib1) as xx; rewrite <- xx.
        eapply cs_entry_between_firstn_cs_entry_pre_replace_cs_entry; try exact Heqfcsa; auto.
        apply lib_extends_erase_choices_upto; eauto 3 with slow. }
      { eapply lib_extends_replace_cs_entry_between2; eauto; eauto 4 with slow;[|].
        { pose proof (lib_depth_inc_cs_lib name0 lib2 lib1) as xx; rewrite <- xx.
          eapply cs_entry_between_firstn_cs_entry; try exact Heqfcsa; auto.
          apply lib_extends_erase_choices_upto; eauto 3 with slow. }
        { eapply lib_extends_erase_choices_upto; eauto 3 with slow. } } }
    eapply lib_extends_trans.
    { eapply lib_extends_replace_cs_entry_between1; eauto; eauto 4 with slow.
      { pose proof (lib_depth_inc_cs_lib name0 lib2 lib1) as xx; rewrite <- xx.
        eapply cs_entry_between_firstn_cs_entry; try exact Heqfcsa; auto.
        apply lib_extends_erase_choices_upto; eauto 3 with slow. }
      { eapply lib_extends_erase_choices_upto; eauto 3 with slow. } }
    eapply lib_extends_erase_choices_upto; auto. }

  { eapply lib_extends_replace_cs_entry_between2; eauto 3 with slow.
    { apply sat_lib_cond_replace_cs_entry; autorewrite with slow; eauto 4 with slow. }
    { apply implies_safe_library_replace_cs_entry; eauto 4 with slow. }
    { pose proof (lib_depth_inc_cs_lib name0 lib2 lib1) as xx; rewrite <- xx.
      eapply cs_entry_between_firstn_cs_entry_pre_replace_cs_entry; try exact Heqfcsa; auto.
      apply lib_extends_erase_choices_upto; eauto 3 with slow. }
    eapply lib_extends_replace_cs_entry_between2; eauto 4 with slow.
    { pose proof (lib_depth_inc_cs_lib name0 lib2 lib1) as xx; rewrite <- xx.
      eapply cs_entry_between_firstn_cs_entry; try exact Heqfcsa; auto.
      apply lib_extends_erase_choices_upto; eauto 3 with slow. }
    eapply lib_extends_erase_choices_upto; auto. }

  { repeat rewrite find_cs_replace_cs_entry.
    boolvar; subst; tcsp; GC.
    pose proof (lib_extends_erase_choices_upto lib2 lib1 name0) as q.
    repeat (autodimp q hyp); repnd.
    dup q as q'.
    eapply (eq_lib_names_preserves_find_cs _ _ name) in q; eauto.
    eapply (eq_lib_names_preserves_find_cs _ _ name') in q'; eauto.
    exrepnd; allrw; f_equal.
    destruct c as [vals1 restr1], c0 as [vals2 restr2]; simpl in *.
    f_equal.

    { apply implies_eq_firstn; introv ltd.
      pose proof (imp i) as imp; autodimp imp hyp; try omega; exrepnd.
      unfold find_cs_value_at in imp1, imp0.
      rewrite Heqfcsa, Heqfcsb in *; simpl in *.
      rewrite @find_value_of_cs_at_is_select in *; try congruence. }

    apply strong_safe_library_implies_safe_choice_sequence_entry in Heqfcsa; auto.
    apply strong_safe_library_implies_safe_choice_sequence_entry in Heqfcsb; auto.
    simpl in *; repnd.
    destruct name as [name1 kind1], name' as [name2 kind2], kind1, kind2;
      unfold is_nat_cs in *; simpl in *; tcsp; destruct n1, n2; simpl in *; tcsp; GC.
    unfold correct_restriction, is_nat_restriction in *; simpl in *.
    destruct restr1, restr2; f_equal.
    apply functional_extensionality; introv.
    apply functional_extensionality; introv.
    apply propositional_extensionality; allrw; tcsp.
  }

  {
    allrw @name_in_lib_as_in_lib.
    autorewrite with slow.
    pose proof (lib_extends_erase_choices_upto lib2 lib1 name0) as q.
    repeat (autodimp q hyp); repnd.
    eapply eq_lib_names_preserves_in_lib;[eauto|]; eauto 3 with slow.
  }

  {
    allrw @name_in_lib_as_in_lib.
    autorewrite with slow.
    pose proof (lib_extends_erase_choices_upto lib2 lib1 name0) as q.
    repeat (autodimp q hyp); repnd.
    eapply eq_lib_names_preserves_in_lib;[eauto|]; eauto 3 with slow.
  }

  { introv fcs.

    pose proof (lib_extends_erase_choices_upto lib2 lib1 name0) as q.
    repeat (autodimp q hyp); repnd.
    dup q as q'.
    eapply (eq_lib_names_preserves_find_cs _ _ name) in q; eauto.
    eapply (eq_lib_names_preserves_find_cs _ _ name') in q'; eauto.
    exrepnd; allrw.

    unfold find_cs_value_at in fcs.
    repeat (rewrite find_cs_replace_cs_entry in fcs).
    boolvar; subst; tcsp; GC.

    { rewrite q2 in *; ginv.
      rewrite @find_value_of_cs_at_is_select in *.
      rewrite Heqfcsa in *; ginv.
      destruct c0 as [vals restr]; simpl in *.
      rewrite select_firstn in fcs; boolvar; ginv.
      pose proof (imp m) as imp; autodimp imp hyp; try omega; exrepnd; GC.
      unfold find_cs_value_at in *.
      rewrite Heqfcsa in *; simpl in *.
      rewrite find_value_of_cs_at_is_select in imp1.
      rewrite fcs in *; inversion imp1; subst; eauto 3 with slow. }

    { rewrite q2 in *; ginv.
      rewrite @find_value_of_cs_at_is_select in *.
      destruct c as [vals restr]; simpl in *.
      rewrite select_firstn in fcs; boolvar; ginv.
      pose proof (imp m) as imp; autodimp imp hyp; try omega; exrepnd; GC.
      unfold find_cs_value_at in *.
      rewrite Heqfcsa, Heqfcsb in *; simpl in *.
      rewrite find_value_of_cs_at_is_select in imp1.
      rewrite fcs in *; inversion imp1; subst; eauto 3 with slow. } }
Qed.

Definition strong_sat_cond_lib {o} (c : @LibCond o) (lib : @plibrary o) :=
  forall e, List.In e lib -> sat_cond_entry c e.

Definition strong_sat_lib_cond {o} (lib : @library o) :=
  forall e, List.In e (lib_pre lib) -> lib_cond_sat_entry lib e.

Lemma sat_lib_cond_as_sat_cond_lib {o} :
  forall (lib : @plibrary o) cond,
    sat_lib_cond (MkLib lib cond) <-> sat_cond_lib cond lib.
Proof.
  introv; tcsp.
Qed.
Hint Rewrite @sat_lib_cond_as_sat_cond_lib : slow.

Lemma strong_sat_lib_cond_as_strong_sat_cond_lib {o} :
  forall (lib : @plibrary o) cond,
    strong_sat_lib_cond (MkLib lib cond) <-> strong_sat_cond_lib cond lib.
Proof.
  introv; tcsp.
Qed.
Hint Rewrite @strong_sat_lib_cond_as_strong_sat_cond_lib : slow.

Lemma strong_sat_lib_cond_implies_sat_lib_cond {o} :
  forall (lib : @library o),
    strong_sat_lib_cond lib
    -> sat_lib_cond lib.
Proof.
  introv sat i.
  apply sat; eauto 3 with slow.
Qed.
Hint Resolve strong_sat_lib_cond_implies_sat_lib_cond : slow.

Lemma strong_sat_cond_lib_cons {o} :
  forall cond e (lib : @plibrary o),
    strong_sat_cond_lib cond (e :: lib)
    <-> (sat_cond_entry cond e /\ strong_sat_cond_lib cond lib).
Proof.
  introv; split; intro h; repnd; dands; tcsp.
  { apply h; simpl; tcsp. }
  { introv i; apply h; simpl; tcsp. }
  { introv i; simpl in *; repndors; subst; tcsp. }
Qed.
Hint Rewrite @strong_sat_cond_lib_cons : slow.

Lemma get_cs_apply_list {o} :
  forall l (t : @NTerm o),
    get_cs (apply_list t l) = get_cs t ++ flat_map get_cs l.
Proof.
  induction l; introv; simpl; autorewrite with slow; auto.
  rewrite IHl; simpl; autorewrite with slow.
  rewrite app_assoc; auto.
Qed.
Hint Rewrite @get_cs_apply_list : slow.

Lemma get_cs_o_nil_implies_eq_swap {o} :
  forall sw (op : @Opid o),
    get_cs_o op = []
    -> swap_cs_op sw op = op.
Proof.
  introv h.
  destruct op; simpl in *; tcsp.
  destruct c; simpl in *; tcsp.
Qed.

Lemma swap_cs_soterm_trivial_if_no_cs {o} :
  forall sw (t : @SOTerm o),
    get_cs (soterm2nterm t) = []
    -> swap_cs_soterm sw t = t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; introv nocs; simpl in *; autorewrite with slow in *.

  { Case "sovar".
    f_equal.
    apply eq_map_l; introv i.
    rw flat_map_empty in nocs.
    pose proof (nocs (soterm2nterm x)) as nocs; autodimp nocs hyp.
    apply in_map_iff; eexists; dands; eauto. }

  { Case "soterm".
    apply app_eq_nil in nocs; repnd.
    rw flat_map_empty in nocs.
    rewrite get_cs_o_nil_implies_eq_swap; auto.
    f_equal.
    apply eq_map_l; introv i.
    destruct x; simpl in *; f_equal.
    applydup ind in i; tcsp.
    pose proof (nocs (sobterm2bterm (sobterm l s))) as nocs; simpl in *; autodimp nocs hyp; tcsp.
    apply in_map_iff; eexists; dands; eauto. }
Qed.

Lemma swap_cs_term_trivial_if_no_cs {o} :
  forall sw (t : @NTerm o),
    get_cs t = []
    -> swap_cs_term sw t = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv nocs; simpl in *; autorewrite with slow in *; tcsp.
  Case "oterm".
  apply app_eq_nil in nocs; repnd.
  rw flat_map_empty in nocs.
  rewrite get_cs_o_nil_implies_eq_swap; auto.
  f_equal.
  apply eq_map_l; introv i.
  destruct x; simpl in *; f_equal.
  applydup ind in i; tcsp.
  apply nocs in i; simpl in *; auto.
Qed.

Lemma swap_cs_cterm_trivial_if_no_cs {o} :
  forall sw (t : @CTerm o),
    get_cs (get_cterm t) = []
    -> swap_cs_cterm sw t = t.
Proof.
  introv nocs; destruct_cterms; simpl in *; apply cterm_eq; simpl.
  apply swap_cs_term_trivial_if_no_cs; auto.
Qed.

Lemma in_lib_abs_swap_cs_plib {o} :
  forall op sw (lib : @plibrary o),
    in_lib (entry_name_abs op) (swap_cs_plib sw lib)
    <-> in_lib (entry_name_abs op) lib.
Proof.
  introv; split; intro h; unfold in_lib in *; exrepnd.

  { apply in_swap_library_implies in h1; exrepnd; subst; simpl in *.
    eexists; dands; eauto.
    destruct e0; simpl in *; simpl in *; tcsp. }

  { exists (swap_cs_lib_entry sw e); dands; eauto 3 with slow.
    destruct e; simpl in *; tcsp. }
Qed.
Hint Rewrite @in_lib_abs_swap_cs_plib : slow.

Lemma in_lib_cs_swap_cs_plib {o} :
  forall sw name (lib : @plibrary o),
    in_lib (entry_name_cs (swap_cs sw name)) (swap_cs_plib sw lib)
    <-> in_lib (entry_name_cs name) lib.
Proof.
  introv; split; intro h; unfold in_lib in *; exrepnd.

  { apply in_swap_library_implies in h1; exrepnd; subst.
    eexists; dands; eauto.
    destruct e0; simpl in *; tcsp.
    apply swap_cs_inj in h0; auto. }

  { apply (swap_in_library sw) in h1.
    eexists; dands; eauto.
    destruct e; simpl in *; subst; tcsp. }
Qed.
Hint Rewrite @in_lib_cs_swap_cs_plib : slow.

Lemma implies_lib_nodup_swap_cs_plib {o} :
  forall sw (lib : @plibrary o),
    lib_nodup lib
    -> lib_nodup (swap_cs_plib sw lib).
Proof.
  induction lib; introv h; simpl in *; tcsp; repnd.
  dands; tcsp.
  intro xx; destruct h0.
  destruct a; simpl in *; tcsp; autorewrite with slow in *; tcsp.
Qed.
Hint Resolve implies_lib_nodup_swap_cs_plib : slow.

Lemma lib_nodup_implies_NoDup {o} :
  forall (lib : @plibrary o),
    lib_nodup lib
    -> NoDup lib.
Proof.
  induction lib; introv nodup; simpl in *; repnd; eauto; try constructor; tcsp.
  intro xx; destruct nodup0.
  exists a; dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve lib_nodup_implies_NoDup : slow.

Definition eq_sw_in_lib {o} (sw : cs_swap) (lib : @ plibrary o) :=
  let (a,b) := sw in
  find_cs lib a = find_cs lib b.

Lemma swap_cs_op_trivial_same {o} :
  forall name (op : @Opid o),
    swap_cs_op (name, name) op = op.
Proof.
  introv; destruct op; simpl; tcsp.
  destruct c; simpl; tcsp; boolvar; subst; tcsp.
Qed.
Hint Rewrite @swap_cs_op_trivial_same : slow.

Lemma swap_cs_term_trivial_same {o} :
  forall name (t : @NTerm o),
    swap_cs_term (name, name) t = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; tcsp.
  autorewrite with slow; f_equal.
  apply eq_map_l; introv i; destruct x; simpl.
  erewrite ind; eauto.
Qed.
Hint Rewrite @swap_cs_term_trivial_same : slow.

Lemma swap_cs_cterm_trivial_same {o} :
  forall name (t : @CTerm o),
    swap_cs_cterm (name, name) t = t.
Proof.
  introv; destruct_cterms; simpl; apply cterm_eq; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_cterm_trivial_same : slow.

Lemma swap_cs_choice_seq_vals_trivial_same {o} :
  forall name (vals : @ChoiceSeqVals o),
    swap_cs_choice_seq_vals (name, name) vals = vals.
Proof.
  introv; unfold swap_cs_choice_seq_vals.
  apply eq_map_l; introv i; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_choice_seq_vals_trivial_same : slow.

Lemma swap_cs_choice_seq_trivial_same {o} :
  forall name (restr : @ChoiceSeqRestriction o),
    swap_cs_choice_seq_restr (name, name) restr = restr.
Proof.
  introv; destruct restr; simpl; f_equal.
  apply functional_extensionality; introv.
  apply functional_extensionality; introv.
  unfold swap_cs_restriction_pred; simpl; f_equal; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_choice_seq_trivial_same : slow.

Lemma swap_cs_choice_seq_entry_trivial_same {o} :
  forall name (entry : @ChoiceSeqEntry o),
    swap_cs_choice_seq_entry (name, name) entry = entry.
Proof.
  introv; destruct entry as [vals restr]; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_choice_seq_entry_trivial_same : slow.

Lemma swap_cs_soterm_trivial_same {o} :
  forall name (t : @SOTerm o),
    swap_cs_soterm (name, name) t = t.
Proof.
  soterm_ind t as [v ts ind|op bs ind] Case; simpl; tcsp.

  { Case "sovar".
    f_equal; apply eq_map_l; tcsp. }

  { Case "soterm".
    autorewrite with slow; f_equal.
    apply eq_map_l; introv i; destruct x; simpl.
    erewrite ind; eauto. }
Qed.
Hint Rewrite @swap_cs_soterm_trivial_same : slow.

Lemma swap_cs_lib_entry_trivial_same {o} :
  forall name (e : @library_entry o),
    swap_cs_lib_entry (name, name) e = e.
Proof.
  introv; destruct e; simpl; tcsp; boolvar; subst; GC; simpl; autorewrite with slow; tcsp.
  remember (swap_cs_correct_abs (name, name) opabs vars rhs correct) as cor'; clear Heqcor'.
  revert dependent cor'; autorewrite with slow; introv; f_equal; apply correct_abs_proof_irrelevance.
Qed.
Hint Rewrite @swap_cs_lib_entry_trivial_same : slow.

Lemma swap_cs_plib_trivial_same {o} :
  forall name (lib : @plibrary o),
    swap_cs_plib (name, name) lib = lib.
Proof.
  induction lib; simpl; tcsp; autorewrite with slow; try congruence.
Qed.
Hint Rewrite @swap_cs_plib_trivial_same : slow.

Lemma in_implies_entry_in_library_if_nodup {o} :
  forall e (lib : @plibrary o),
    lib_nodup lib
    -> List.In e lib
    -> entry_in_library e lib.
Proof.
  induction lib; introv nodup i; simpl in *; tcsp; repnd; repndors; subst; tcsp.
  right; dands; tcsp.
  intro m; destruct nodup0; eauto 3 with slow.
Qed.
Hint Resolve in_implies_entry_in_library_if_nodup : slow.

Lemma swap_cs_choice_seq_vals_trivial_if_no_cs {o} :
  forall sw cond (vals : @ChoiceSeqVals o),
    lib_cond_no_cs cond
    -> sat_cond_choices cond vals
    -> swap_cs_choice_seq_vals sw vals = vals.
Proof.
  introv nocs sat.
  apply eq_map_l; introv i.
  apply sat in i.
  unfold lib_cond_no_cs in *; repnd.
  rewrite nocs0 in i.
  apply swap_cs_cterm_trivial_if_no_cs; auto.
Qed.

Lemma swap_cs_lib_entry_trivial_if_none {o} :
  forall cond n1 n2 e (lib : @plibrary o),
    is_nat_cs n1
    -> is_nat_cs n2
    -> lib_cond_no_cs cond
    -> im_swap_lib lib
    -> sat_cond_entry cond e
    -> safe_library lib
    -> find_cs lib n2 = None
    -> find_cs lib n1 = None
    -> entry_in_library e lib
    -> swap_cs_lib_entry (n1, n2) e = e.
Proof.
  introv isna isnb nocs im sat safe fcsa fcsb i.
  applydup safe in i.
  destruct e; simpl in *; boolvar; subst; GC; tcsp.

  { apply entry_in_library_implies_find_cs_some in i; rewrite i in *; ginv. }

  { apply entry_in_library_implies_find_cs_some in i; rewrite i in *; ginv. }

  { f_equal.
    destruct entry as [vals restr]; simpl in *; repnd.
    apply entry_in_library_implies_find_cs_some in i.
    apply im in i; simpl in *; rewrite i.
    erewrite swap_cs_choice_seq_vals_trivial_if_no_cs; eauto. }

  { remember (swap_cs_correct_abs (n1, n2) opabs vars rhs correct) as cor'; clear Heqcor'.
    revert dependent cor'; rewrite swap_cs_soterm_trivial_if_no_cs;
      [introv; f_equal; apply correct_abs_proof_irrelevance|].
    unfold lib_cond_no_cs in *; repnd; rewrite nocs0 in sat; tcsp. }
Qed.

Definition is_nat_swap (sw : cs_swap) :=
  let (n1,n2) := sw in
  is_nat_cs n1 /\ is_nat_cs n2.

Lemma swap_cs_choice_seq_entry_trivial_if_no_cs {o} :
  forall sw cond (e : @ChoiceSeqEntry o),
    im_swap_cs_entry e
    -> lib_cond_no_cs cond
    -> sat_cond_cs_entry cond e
    -> swap_cs_choice_seq_entry sw e = e.
Proof.
  introv im nocs sat.
  destruct e as [vals restr]; simpl in *; repnd.
  erewrite swap_cs_choice_seq_vals_trivial_if_no_cs; eauto.
  rewrite im; simpl; tcsp.
Qed.

Lemma in_swap_library_iff {o} :
  forall sw entry (lib : @plibrary o),
    List.In entry (swap_cs_plib sw lib)
    <-> exists e,
      List.In e lib
      /\ entry = swap_cs_lib_entry sw e.
Proof.
  introv; split; intro h; try apply in_swap_library_implies; auto.
  exrepnd; subst; eauto 3 with slow.
Qed.

Lemma swap_cs_plib_trivial_no_cs {o} :
  forall sw cond (lib : @plibrary o),
    im_swap_lib lib
    -> eq_sw_in_lib sw lib
    -> is_nat_swap sw
    -> lib_nodup lib
    -> strong_sat_cond_lib cond lib
    -> safe_library lib
    -> lib_cond_no_cs cond
    -> Permutation (swap_cs_plib sw lib) lib.
Proof.
  introv im eqsw isn nodup sat safe nocs.
  apply NoDup_Permutation; eauto 3 with slow.
  introv; split; intro h.

  { apply in_swap_library_implies in h; exrepnd; subst.
    applydup sat in h1.
    apply in_implies_entry_in_library_if_nodup in h1; auto.
    destruct sw as [n1 n2]; simpl in *; repnd.
    remember (find_cs lib n2) as fcs; symmetry in Heqfcs.
    destruct fcs;
      [|erewrite swap_cs_lib_entry_trivial_if_none; eauto; eauto 3 with slow].

    destruct e; simpl in *;
      [|remember (swap_cs_correct_abs (n1, n2) opabs vars rhs correct) as cor'; clear Heqcor';
        revert cor'; rewrite swap_cs_soterm_trivial_if_no_cs; introv;
        [|unfold lib_cond_no_cs in *; repnd; rewrite nocs0 in h0; tcsp];
        assert (cor' = correct) by eauto with pi; subst; eauto 3 with slow].

    boolvar; subst; GC; tcsp.

    { apply entry_in_library_implies_find_cs_some in h1; rewrite h1 in *; ginv.
      apply im in h1.
      erewrite swap_cs_choice_seq_entry_trivial_if_no_cs; eauto; eauto 3 with slow. }

    { apply entry_in_library_implies_find_cs_some in h1; rewrite h1 in *; ginv.
      apply im in h1.
      erewrite swap_cs_choice_seq_entry_trivial_if_no_cs; eauto; eauto 3 with slow. }

    apply entry_in_library_implies_find_cs_some in h1.
    applydup im in h1.
    erewrite swap_cs_choice_seq_entry_trivial_if_no_cs; eauto; eauto 3 with slow. }

  { applydup sat in h.
    apply in_implies_entry_in_library_if_nodup in h; auto.
    destruct sw as [n1 n2]; simpl in *; repnd.
    apply in_swap_library_iff.
    remember (find_cs lib n2) as fcs; symmetry in Heqfcs.
    destruct fcs;
      [|dup h as q; eapply (swap_cs_lib_entry_trivial_if_none _ n1 n2) in h;
        eauto; simpl in *; exists x; dands; eauto 3 with slow].

    destruct x; simpl in *;
      [|exists (lib_abs opabs vars rhs correct); simpl; dands; eauto 3 with slow;
        remember (swap_cs_correct_abs (n1, n2) opabs vars rhs correct) as cor'; clear Heqcor';
        revert cor'; rewrite swap_cs_soterm_trivial_if_no_cs; introv;
        [|unfold lib_cond_no_cs in *; repnd; rewrite nocs0 in h0; tcsp];
        assert (cor' = correct) by eauto with pi; subst; eauto 3 with slow].

    destruct (choice_sequence_name_deq name n1) as [d1|d1]; subst; tcsp.

    { applydup @entry_in_library_implies_find_cs_some in h; rewrite h1 in *; ginv.
      apply im in h1.
      exists (lib_cs n2 c); dands; eauto 3 with slow.
      simpl; boolvar; subst; tcsp; GC;
        erewrite swap_cs_choice_seq_entry_trivial_if_no_cs; eauto; eauto 3 with slow. }

    destruct (choice_sequence_name_deq name n2) as [d2|d2]; subst; tcsp.

    { applydup @entry_in_library_implies_find_cs_some in h; rewrite h1 in *; ginv.
      apply im in h1.
      exists (lib_cs n1 c); dands; eauto 3 with slow.
      simpl; boolvar; subst; tcsp; GC;
        erewrite swap_cs_choice_seq_entry_trivial_if_no_cs; eauto; eauto 3 with slow. }

    apply entry_in_library_implies_find_cs_some in h.
    applydup im in h.
    exists (lib_cs name entry); simpl; dands; eauto 3 with slow.
    boolvar; tcsp; GC.
    erewrite swap_cs_choice_seq_entry_trivial_if_no_cs; eauto; eauto 3 with slow. }
Qed.

Inductive swapped_css {o} sw : @plibrary o -> @plibrary o -> Prop :=
| sw_css :
    forall lib1 name1 e1 lib2 name2 e2 lib3,
      (sw = (name1,name2) \/ sw = (name2,name1))
      -> swapped_css
           sw
           (lib1 ++ lib_cs name1 e1 :: lib2 ++ lib_cs name2 e2 :: lib3)
           (lib1 ++ lib_cs name2 e2 :: lib2 ++ lib_cs name1 e1 :: lib3).
Hint Constructors swapped_css.

Fixpoint entry_in_lib {o} (entry : @library_entry o) (lib : plibrary) : Type :=
  match lib with
  | [] => False
  | entry' :: entries =>
    entry = entry'
    [+]
    (~ matching_entries entry entry'
       # entry_in_lib entry entries)
  end.

Lemma matching_entries_refl {o} :
  forall (a : @library_entry o), matching_entries a a.
Proof.
  destruct a; simpl; simpl; tcsp.
  unfold matching_entries; simpl; eauto 3 with slow.
Qed.
Hint Resolve matching_entries_refl : slow.

Lemma entry_in_library_implies_entry_in_lib {o} :
  forall e (lib : @plibrary o),
    entry_in_library e lib
    -> entry_in_lib e lib.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  destruct (dec_matching_entries e a) as [d|d].
  { left; repndors; tcsp. }
  right; dands; tcsp.
  apply IHlib; repndors; subst; tcsp.
  destruct d; eauto 3 with slow.
Qed.

Lemma entry_in_lib_split {o} :
  forall e (lib : @plibrary o),
    entry_in_lib e lib
    -> {lib1 : plibrary
        & {lib2 : plibrary
        & lib = lib1 ++ e :: lib2
        /\ ~in_lib (entry2name e) lib1 } }.
Proof.
  induction lib; introv h; simpl in *; tcsp; repndors; repnd; subst; tcsp.
  { exists ([] : @plibrary o) lib; simpl; autorewrite with slow; dands; tcsp. }
  autodimp IHlib hyp; exrepnd; subst.
  exists (a :: lib1) lib2; simpl; dands; tcsp.
  rewrite in_lib_cons; intro xx; repndors; tcsp.
Qed.

Lemma entry_in_lib_app_implies {o} :
  forall entry (lib1 lib2 : @plibrary o),
    entry_in_lib entry (lib1 ++ lib2)
    ->
    (
      entry_in_lib entry lib1
      [+]
      (
        entry_in_lib entry lib2
        # forall e, List.In e lib1 -> ~matching_entries entry e
      )
    ).
Proof.
  induction lib1; introv i; simpl in *; tcsp.
  repndors; repnd; tcsp.
  apply IHlib1 in i; repndors; repnd; tcsp.
  right; dands; auto.
  introv j; repndors; subst; tcsp.
  applydup i in j; tcsp.
Qed.

Lemma swap_cs_plib_app {o} :
  forall sw (lib1 lib2 : @plibrary o),
    swap_cs_plib sw (lib1 ++ lib2) = swap_cs_plib sw lib1 ++ swap_cs_plib sw lib2.
Proof.
  induction lib1; introv; simpl; tcsp.
  allrw; auto.
Qed.
Hint Rewrite @swap_cs_plib_app : slow.

Definition im_swap_lib_entry {o} (e : @library_entry o) :=
  match e with
  | lib_cs name e => im_swap_cs_entry e
  | lib_abs _ _ _ _ => True
  end.

Lemma im_swap_lib_cons {o} :
  forall e (lib : @plibrary o),
    ~ in_lib (entry2name e) lib
    -> (im_swap_lib (e :: lib) <-> (im_swap_lib_entry e /\ im_swap_lib lib)).
Proof.
  introv ni; split; intro h; repnd; dands; tcsp.
  { destruct e; simpl in *; tcsp.
    apply (h name); simpl; boolvar; tcsp. }
  { introv i; apply (h name); simpl; tcsp.
    destruct e; simpl in *; tcsp; boolvar; subst; tcsp.
    apply not_in_lib_implies_find_cs_none in ni; rewrite ni in *; ginv. }
  { introv i; simpl in *; destruct e; simpl in *; boolvar; subst; tcsp; ginv; tcsp;
      apply (h name); tcsp. }
Qed.

Lemma find_cs_app_eq {o} :
  forall name (lib1 lib2 : @plibrary o),
    find_cs (lib1 ++ lib2) name
    = match find_cs lib1 name with
      | Some e => Some e
      | None => find_cs lib2 name
      end.
Proof.
  induction lib1; introv; simpl; tcsp.
  destruct a; simpl; tcsp; boolvar; subst; tcsp.
Qed.

Lemma find_cs_some_implies_in_lib {o} :
  forall (lib : @plibrary o) name c,
    find_cs lib name = Some c
    -> in_lib (entry_name_cs name) lib.
Proof.
  introv fcs.
  exists (lib_cs name c); simpl; dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve find_cs_some_implies_in_lib : slow.

Lemma lib_disjoint_find_cs_some_implies {o} :
  forall (lib1 lib2 : @plibrary o) name c,
    lib_disjoint lib1 lib2
    -> find_cs lib1 name = Some c
    -> find_cs lib2 name = None.
Proof.
  introv disj fcs.
  pose proof (disj (entry_name_cs name)) as disj.
  autodimp disj hyp; eauto 3 with slow.
Qed.

Lemma im_swap_lib_app {o} :
  forall (lib1 lib2 : @plibrary o),
    lib_disjoint lib1 lib2
    -> (im_swap_lib (lib1 ++ lib2) <-> (im_swap_lib lib1 /\ im_swap_lib lib2)).
Proof.
  introv ni; split; intro h; repnd; dands; tcsp; introv i.
  { apply (h name); rewrite find_cs_app_eq; allrw; auto. }
  { apply (h name); rewrite find_cs_app_eq; allrw; auto.
    remember (find_cs lib1 name) as fcs; symmetry in Heqfcs; destruct fcs; auto.
    eapply lib_disjoint_find_cs_some_implies in Heqfcs; eauto; rewrite Heqfcs in *; ginv. }
  { rewrite find_cs_app_eq in i.
    remember (find_cs lib1 name) as fcs; symmetry in Heqfcs; destruct fcs; auto; ginv; tcsp.
    { apply (h0 name); tcsp. }
    { apply (h name); tcsp. } }
Qed.

Definition sw_not_in_lib {o} (sw : cs_swap) (lib : @plibrary o) :=
  let (n1,n2) := sw in
  ~in_lib (entry_name_cs n1) lib
  /\ ~in_lib (entry_name_cs n2) lib.

Definition sw_not_in_entry {o} (sw : cs_swap) (e : @library_entry o) :=
  let (n1,n2) := sw in
  ~same_entry_name (entry_name_cs n1) (entry2name e)
  /\ ~same_entry_name (entry_name_cs n2) (entry2name e).

Lemma sw_not_in_lib_cons {o} :
  forall sw a (lib : @plibrary o),
    sw_not_in_lib sw (a :: lib) <-> (sw_not_in_entry sw a /\ sw_not_in_lib sw lib).
Proof.
  introv; split; intro h; destruct sw as [n1 n2]; simpl in *; repnd; dands; tcsp;
    allrw @in_lib_cons;
    try (complete (apply not_or in h0; tcsp));
    try (complete (destruct a; simpl in *; simpl in *; tcsp)).
Qed.
Hint Rewrite @sw_not_in_lib_cons : slow.

Lemma swap_cs_trivial_if_not_in {o} :
  forall sw name (e : @ChoiceSeqEntry o),
    sw_not_in_entry sw (lib_cs name e)
    -> swap_cs sw name = name.
Proof.
  introv notin.
  destruct sw as [n1 n2]; simpl in *; repnd; boolvar; tcsp.
Qed.

Lemma swap_cs_plib_trivial_if_no_cs {o} :
  forall sw cond (lib : @plibrary o),
    sw_not_in_lib sw lib
    -> lib_nodup lib
    -> im_swap_lib lib
    -> lib_cond_no_cs cond
    -> strong_sat_cond_lib cond lib
    -> swap_cs_plib sw lib = lib.
Proof.
  induction lib; introv notin nodup im nocs sat; simpl in *; repnd; tcsp.
  autorewrite with slow in *; repnd.
  rewrite im_swap_lib_cons in im; auto; repnd.
  rewrite IHlib; auto; f_equal; clear IHlib.
  destruct a; simpl in *.

  { erewrite swap_cs_choice_seq_entry_trivial_if_no_cs; eauto.
    erewrite swap_cs_trivial_if_not_in; eauto. }

  { remember (swap_cs_correct_abs sw opabs vars rhs correct) as cor'; clear Heqcor'.
    revert cor'; rewrite swap_cs_soterm_trivial_if_no_cs; introv.
    { assert (cor' = correct) by eauto with pi; subst; eauto 3 with slow. }
    unfold lib_cond_no_cs in *; repnd; rewrite nocs0 in sat0; tcsp. }
Qed.

Lemma strong_sat_cond_lib_app {o} :
  forall cond (lib1 lib2 : @plibrary o),
    strong_sat_cond_lib cond (lib1 ++ lib2) <-> (strong_sat_cond_lib cond lib1 /\ strong_sat_cond_lib cond lib2).
Proof.
  introv; split; intro h; repnd; dands; introv i.
  { apply h; apply list_in_app; tcsp. }
  { apply h; apply list_in_app; tcsp. }
  { apply list_in_app in i; repndors; tcsp. }
Qed.
Hint Rewrite @strong_sat_cond_lib_app : slow.

Lemma implies_sw_not_in_lib {o} :
  forall n1 n2 (lib : @plibrary o),
    ~ in_lib (entry_name_cs n1) lib
    -> ~ in_lib (entry_name_cs n2) lib
    -> sw_not_in_lib (n1, n2) lib.
Proof.
  introv na nb; simpl; tcsp.
Qed.
Hint Resolve implies_sw_not_in_lib : slow.

Lemma lib_disjoint_app_left {o} :
  forall (lib1 lib2 lib : @plibrary o),
    lib_disjoint (lib1 ++ lib2) lib
    <-> (lib_disjoint lib1 lib /\ lib_disjoint lib2 lib).
Proof.
  introv; split; intro h; repnd; dands; introv i; tcsp;
    try (complete (apply h; apply in_lib_app; tcsp)).
  apply in_lib_app in i; repndors; tcsp; try (complete (apply h0; auto)); try (complete (apply h; auto)).
Qed.
Hint Rewrite @lib_disjoint_app_left : slow.

Lemma lib_disjoint_app_right {o} :
  forall (lib1 lib2 lib : @plibrary o),
    lib_disjoint lib (lib1 ++ lib2)
    <-> (lib_disjoint lib lib1 /\ lib_disjoint lib lib2).
Proof.
  introv; split; intro h; repnd; dands; introv i; tcsp;
    try (complete (apply h in i; intro q; destruct i; apply in_lib_app; tcsp)).
  intro j; apply in_lib_app in j; repndors; tcsp; try (complete (apply h0 in i; auto)); try (complete (apply h in i; auto)).
Qed.
Hint Rewrite @lib_disjoint_app_right : slow.

Lemma swapped_css_plib_trivial_no_cs {o} :
  forall sw cond (lib : @plibrary o),
    swap_in_lib sw lib
    -> im_swap_lib lib
    -> eq_sw_in_lib sw lib
    -> is_nat_swap sw
    -> lib_nodup lib
    -> strong_sat_cond_lib cond lib
    -> strong_safe_library lib
    -> lib_cond_no_cs cond
    -> swapped_css sw (swap_cs_plib sw lib) lib.
Proof.
  introv swi im eqsw isn nodup sat safe nocs.
  destruct sw as [n1 n2]; simpl in *; repnd.
  remember (find_cs lib n2) as fcs; symmetry in Heqfcs.
  destruct fcs; try (complete (unfold name_in_lib in *; rewrite eqsw in *; tcsp)).

  apply find_cs_some_implies_entry_in_library in Heqfcs.
  applydup @entry_in_library_implies_entry_in_lib in Heqfcs as ia.
  apply entry_in_lib_split in ia; exrepnd; subst.

  apply find_cs_some_implies_entry_in_library in eqsw.
  applydup @entry_in_library_implies_entry_in_lib in eqsw as ib.
  apply entry_in_lib_app_implies in ib; repndors.

  { apply entry_in_lib_split in ib; exrepnd; subst; simpl in *.
    repeat (autorewrite with slow; simpl).
    boolvar; tcsp; GC.
    repeat (autorewrite with slow in *; repnd; simpl in *; repnd).
    allrw @in_lib_app; allrw @in_lib_cons.
    apply not_or in ia1; repnd.
    apply not_or in ia1; repnd.
    apply not_or in nodup; repnd.
    apply not_or in nodup; repnd.
    rewrite im_swap_lib_app in im; eauto 3 with slow; repnd;
      try (complete (repeat (autorewrite with slow; repnd; simpl in *; dands; eauto 3 with slow);
                     intro xx; apply in_lib_cons in xx; repndors; tcsp)).
    rewrite im_swap_lib_app in im0; eauto 3 with slow; repnd;
      try (complete (repeat (autorewrite with slow; repnd; simpl in *; dands; eauto 3 with slow);
                     intro xx; apply in_lib_cons in xx; repndors; tcsp)).
    rewrite im_swap_lib_cons in im0; eauto 3 with slow; repnd.
    rewrite im_swap_lib_cons in im; eauto 3 with slow; repnd.

    rewrite (swap_cs_plib_trivial_if_no_cs (n1,n2) cond lib0); eauto 3 with slow;[].
    rewrite (swap_cs_plib_trivial_if_no_cs (n1,n2) cond lib3); eauto 3 with slow;[].
    rewrite (swap_cs_plib_trivial_if_no_cs (n1,n2) cond lib2); eauto 3 with slow;[].
    erewrite swap_cs_choice_seq_entry_trivial_if_no_cs; eauto; eauto.
    repeat rewrite <- app_assoc.
    apply sw_css; tcsp. }

  repnd; simpl in *; repndors; repnd; ginv; tcsp.
  apply entry_in_lib_split in ib0; exrepnd; subst; simpl in *.
  repeat (autorewrite with slow; simpl).
  boolvar; tcsp; GC.
  repeat (autorewrite with slow in *; repnd; simpl in *; repnd).
  allrw @in_lib_app; allrw @in_lib_cons.
  apply not_or in nodup5; repnd.
  apply not_or in nodup5; repnd.
  rewrite im_swap_lib_app in im; eauto 3 with slow; repnd;
    try (complete (repeat (autorewrite with slow; repnd; simpl in *; dands; eauto 3 with slow);
                   intro xx; apply in_lib_cons in xx; repndors; tcsp)).
  rewrite im_swap_lib_cons in im; eauto 3 with slow; repnd;
    try (complete (rewrite in_lib_app; simpl; rewrite in_lib_cons; simpl; tcsp)).
  rewrite im_swap_lib_app in im; eauto 3 with slow; repnd;
    try (complete (repeat (autorewrite with slow; repnd; simpl in *; dands; eauto 3 with slow);
                   intro xx; apply in_lib_cons in xx; repndors; tcsp)).
  rewrite im_swap_lib_cons in im; eauto 3 with slow; repnd.

  rewrite (swap_cs_plib_trivial_if_no_cs (n1,n2) cond lib1); eauto 3 with slow;[].
  rewrite (swap_cs_plib_trivial_if_no_cs (n1,n2) cond lib0); eauto 3 with slow;[].
  rewrite (swap_cs_plib_trivial_if_no_cs (n1,n2) cond lib3); eauto 3 with slow;[].
  erewrite swap_cs_choice_seq_entry_trivial_if_no_cs; eauto; eauto.
Qed.

Lemma eta_strong_sat_cond_lib {o} :
  forall (lib : @library o),
    strong_sat_lib_cond lib
    -> strong_sat_cond_lib (lib_cond lib) (lib_pre lib).
Proof.
  introv sat; tcsp.
Qed.
Hint Resolve eta_strong_sat_cond_lib : slow.

Lemma sat_lib_cond_implies_strong {o} :
  forall (lib : @library o),
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_sat_lib_cond lib.
Proof.
  introv nodup sat i.
  apply sat; eauto 3 with slow.
Qed.
Hint Resolve sat_lib_cond_implies_strong : slow.

Lemma lib_extends_preserves_has_lib_cond_no_cs {o} :
  forall (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> has_lib_cond_no_cs lib1
    -> has_lib_cond_no_cs lib2.
Proof.
  introv ext nocs.
  apply lib_extends_implies_same_conds in ext.
  destruct lib1 as [lib1 cond1], lib2 as [lib2 cond2]; simpl in *.
  unfold same_conds, has_lib_cond_no_cs in *; simpl in *; subst; auto.
Qed.
Hint Resolve lib_extends_preserves_has_lib_cond_no_cs : slow.

Lemma has_lib_cond_no_cs_implies_im_swap_lib {o} :
  forall (lib : @library o),
    has_lib_cond_no_cs lib
    -> sat_lib_cond lib
    -> im_swap_lib lib.
Proof.
  introv nocs safe i.
  apply find_cs_some_implies_entry_in_library in i.
  apply safe in i; simpl in *; clear safe.
  destruct e as [vals restr]; simpl in *; simpl in *; repnd.
  unfold im_swap_cs_entry; simpl.
  unfold has_lib_cond_no_cs in *.
  destruct lib as [lib cond]; simpl in *.
  clear i0.
  unfold lib_cond_no_cs in *; repnd.
  introv; apply nocs in i; tcsp.
Qed.
Hint Resolve has_lib_cond_no_cs_implies_im_swap_lib : slow.

Definition perm_libs {o} (lib1 lib2 : @library o) :=
  Permutation (lib_pre lib1) (lib_pre lib2) /\ same_conds lib1 lib2.

Definition swapped_css_libs {o} name name' (lib1 lib2 : @library o) :=
  swapped_css (name, name') (lib_pre lib1) (lib_pre lib2)
  /\ same_conds lib1 lib2.

Lemma same_conds_swap_cs_lib {o} sw (lib : @library o) :
  has_lib_cond_no_cs lib
  -> same_conds (swap_cs_lib sw lib) lib.
Proof.
  introv nocs; destruct lib as [lib cond]; unfold same_conds; simpl in *.
  unfold has_lib_cond_no_cs in *; simpl in *.
  unfold lib_cond_no_cs in *; repnd.
  apply functional_extensionality; introv.
  unfold swap_cs_lib_cond; destruct x; simpl; tcsp; apply propositional_extensionality.
  { repeat rewrite nocs0; tcsp.
    apply get_cs_swap_cs_term_nil_iff. }
  { split; intro x; dup x as xx; rewrite nocs in x; pose proof (x sw) as x; try congruence.
    rewrite swap_cs_choice_seq_restr_idem in x; rewrite <- x in xx; auto. }
Qed.
Hint Resolve same_conds_swap_cs_lib : slow.

Definition swap_two_names_entry {o} name e name' e' (entry : @library_entry o) : library_entry :=
  match entry with
  | lib_cs n x =>
    if choice_sequence_name_deq n name
    then lib_cs name' e'
    else if choice_sequence_name_deq n name'
         then lib_cs name e
         else lib_cs n x
  | _ => entry
  end.

Fixpoint swap_two_names {o} name e name' e' (lib : @plibrary o) : plibrary :=
  match lib with
  | [] => []
  | entry :: entries => swap_two_names_entry name e name' e' entry :: swap_two_names name e name' e' entries
  end.

Definition pre_swap_names {o} name name' (lib : @plibrary o) : plibrary :=
  match find_cs lib name with
  | Some e =>
    match find_cs lib name' with
    | Some e' => swap_two_names name e name' e' lib
    | None => lib
    end
  | None => lib
  end.

Lemma extension_preserves_lib_disjoint_right_rev {o} :
  forall (lib lib1 lib2 : @plibrary o),
    extension lib2 lib1
    -> lib_disjoint lib lib1
    -> lib_disjoint lib lib2.
Proof.
  introv ext disj i j; apply disj in i.
  rewrite extension_preserves_in_lib in j; eauto.
Qed.
Hint Resolve extension_preserves_lib_disjoint_right_rev : slow.

Lemma extension_preserves_lib_disjoint_left_rev {o} :
  forall (lib lib1 lib2 : @plibrary o),
    extension lib2 lib1
    -> lib_disjoint lib1 lib
    -> lib_disjoint lib2 lib.
Proof.
  introv ext disj i j.
  rewrite (extension_preserves_in_lib n lib2 lib1) in i; auto.
  apply disj in i; tcsp.
Qed.
Hint Resolve extension_preserves_lib_disjoint_left_rev : slow.

Lemma sat_cond_lib_nil {o} :
  forall (cond : @LibCond o),
    sat_cond_lib cond [].
Proof.
  introv i; simpl in *; tcsp.
Qed.
Hint Resolve sat_cond_lib_nil : slow.

Lemma strong_safe_library_nil {o} :
  @strong_safe_library o [].
Proof.
  introv i; simpl in *; tcsp.
Qed.
Hint Resolve strong_safe_library_nil : slow.

Lemma lib_extends_implies_app_extension {o} :
  forall (lib2 lib1 : @library o),
    lib_extends lib2 lib1
    -> exists (lib : plibrary) (lib' : plibrary),
      lib_pre lib2 = lib ++ lib'
      /\ extension lib' lib1
      /\ lib_disjoint lib lib'.
Proof.
  introv ext.
  lib_ext_ind ext Case.

  { Case "lib_ext_refl".
    exists ([] : @plibrary o) lib; simpl; dands; eauto 3 with slow. }

  { Case "lib_ext_trans".
    exrepnd; subst.
    destruct lib1 as [lib1 cond1]; simpl in *; subst.
    destruct lib2 as [lib2 cond2]; simpl in *; subst.
    apply extension_app_right_implies in IHext5; exrepnd; subst.
    autorewrite with slow in *; repnd.
    exists (lib0 ++ lib1) lib4; rewrite app_assoc; dands; eauto 3 with slow.
    { eapply extension_trans; eauto. }
    { autorewrite with slow; dands; eauto 3 with slow. } }

  { Case "lib_ext_new_abs".
    exists [lib_abs op vars rhs correct] lib; simpl; dands; eauto 3 with slow.
    autorewrite with slow; simpl; dands; tcsp; eauto 3 with slow. }

  { Case "lib_ext_new_cs".
    exists [lib_cs name (MkChoiceSeqEntry _ [] restr)] lib; simpl; dands; eauto 3 with slow.
    autorewrite with slow; simpl; dands; tcsp; eauto 3 with slow. }

  { Case "lib_ext_cs".
    apply add_one_choice_extension in addc.
    exists ([] : @plibrary o) lib'; simpl; dands; eauto 3 with slow. }
Qed.

Lemma entry_extends_lib_cs_right_implies {o} :
  forall (e : @library_entry o) name c,
    entry_extends e (lib_cs name c)
    -> exists c',
      e = lib_cs name c'
      /\ cs_entry_extends c' c.
Proof.
  introv q; inversion q; subst; eauto.
  exists c; dands; tcsp; eauto 3 with slow.
Qed.

Lemma extension_preserves_not_in_lib {o} :
  forall name (lib1 lib0 : @plibrary o),
    extension lib1 lib0
    -> ~ in_lib name lib0
    -> ! in_lib name lib1.
Proof.
  introv ext ni i; eapply extension_preserves_in_lib in ext; apply ext in i; tcsp.
Qed.
Hint Resolve extension_preserves_not_in_lib : slow.

Lemma extension_preserves_not_in_lib2 {o} :
  forall name (lib1 lib0 : @plibrary o),
    extension lib1 lib0
    -> ~ in_lib name lib0
    -> ~ in_lib name lib1.
Proof.
  introv ext ni i; eapply extension_preserves_in_lib in ext; apply ext in i; tcsp.
Qed.
Hint Resolve extension_preserves_not_in_lib2 : slow.

Lemma extension_preserves_not_in_lib3 {o} :
  forall name (lib1 lib0 : @plibrary o),
    extension lib1 lib0
    -> ~ in_lib name lib0
    -> in_lib name lib1 -> False.
Proof.
  introv ext ni i; eapply extension_preserves_in_lib in ext; apply ext in i; tcsp.
Qed.
Hint Resolve extension_preserves_not_in_lib3 : slow.

Lemma swap_two_names_split_fst_eq {o} :
  forall name1 c1 name2 c2 a (lib1 lib2 : @plibrary o),
    name1 <> name2
    -> ~in_lib (entry_name_cs name1) lib1
    -> ~in_lib (entry_name_cs name2) lib1
    -> swap_two_names name1 c1 name2 c2 (lib1 ++ lib_cs name1 a :: lib2)
       = lib1 ++ lib_cs name2 c2 :: swap_two_names name1 c1 name2 c2 lib2.
Proof.
  induction lib1; introv d na nb; simpl in *; boolvar; tcsp.
  allrw @in_lib_cons.
  apply not_or in na; repnd.
  apply not_or in nb; repnd.
  destruct a0; simpl in *; boolvar; subst; tcsp; GC; rewrite IHlib1; auto.
Qed.

Lemma swap_two_names_split_snd_eq {o} :
  forall name1 c1 name2 c2 a (lib1 lib2 : @plibrary o),
    name1 <> name2
    -> ~in_lib (entry_name_cs name1) lib1
    -> ~in_lib (entry_name_cs name2) lib1
    -> swap_two_names name1 c1 name2 c2 (lib1 ++ lib_cs name2 a :: lib2)
       = lib1 ++ lib_cs name1 c1 :: swap_two_names name1 c1 name2 c2 lib2.
Proof.
  induction lib1; introv d na nb; simpl in *; boolvar; tcsp.
  allrw @in_lib_cons.
  apply not_or in na; repnd.
  apply not_or in nb; repnd.
  destruct a0; simpl in *; boolvar; subst; tcsp; GC; rewrite IHlib1; auto.
Qed.

Lemma swap_two_names_split_eq_not_in {o} :
  forall name1 c1 name2 c2 (lib : @plibrary o),
    ~in_lib (entry_name_cs name1) lib
    -> ~in_lib (entry_name_cs name2) lib
    -> swap_two_names name1 c1 name2 c2 lib = lib.
Proof.
  induction lib; introv na nb; simpl in *; boolvar; tcsp.
  allrw @in_lib_cons.
  apply not_or in na; repnd.
  apply not_or in nb; repnd.
  destruct a; simpl in *; boolvar; subst; tcsp; GC; rewrite IHlib; auto.
Qed.

Lemma extension_implies_in_lib {o} :
  forall n (lib1 lib2 : @plibrary o),
    extension lib1 lib2
    -> in_lib n lib1
    -> in_lib n lib2.
Proof.
  introv ext i.
  rewrite <- extension_preserves_in_lib; eauto.
Qed.
Hint Resolve extension_implies_in_lib : slow.

Lemma sat_cond_lib_app_disj_implies {o} :
  forall cond (lib1 lib2 : @plibrary o),
    lib_disjoint lib1 lib2
    -> sat_cond_lib cond (lib1 ++ lib2)
    -> (sat_cond_lib cond lib1 /\ sat_cond_lib cond lib2).
Proof.
  introv disj sat; dands; introv i; eauto 3 with slow.
Qed.

Lemma sat_cond_lib_cons_disj_implies {o} :
  forall cond e (lib : @plibrary o),
    ~in_lib (entry2name e) lib
    -> sat_cond_lib cond (e :: lib)
    -> (sat_cond_entry cond e /\ sat_cond_lib cond lib).
Proof.
  introv disj sat; dands.
  { apply sat; simpl; tcsp. }
  { introv i; apply sat; simpl; right; dands; eauto 3 with slow. }
Qed.

Lemma implies_extension_app {o} :
  forall (lib1 lib2 lib3 lib4 : @plibrary o),
    extension lib1 lib2
    -> extension lib3 lib4
    -> extension (lib1 ++ lib3) (lib2 ++ lib4).
Proof.
  induction lib1; introv exta extb; simpl in *; destruct lib2; simpl in *; tcsp.
Qed.
Hint Resolve implies_extension_app : slow.

Lemma cs_entry_extends_implies_entry_extends {o} :
  forall name (c1 c2 : @ChoiceSeqEntry o),
    cs_entry_extends c1 c2
    -> entry_extends (lib_cs name c1) (lib_cs name c2).
Proof.
  introv xx; inversion xx; subst; simpl in *; eauto.
Qed.
Hint Resolve cs_entry_extends_implies_entry_extends : slow.

Lemma implies_sat_cond_lib_app {o} :
  forall cond (lib1 lib2 : @plibrary o),
    sat_cond_lib cond lib1
    -> sat_cond_lib cond lib2
    -> sat_cond_lib cond (lib1 ++ lib2).
Proof.
  introv sata satb i.
  apply entry_in_library_app_implies in i; repndors; repnd; tcsp.
Qed.
Hint Resolve implies_sat_cond_lib_app : slow.

Lemma implies_sat_cond_lib_cons {o} :
  forall cond e (lib : @plibrary o),
    sat_cond_entry cond e
    -> sat_cond_lib cond lib
    -> sat_cond_lib cond (e :: lib).
Proof.
  introv sata satb i; simpl in *; repndors; repnd; subst; tcsp.
Qed.
Hint Resolve implies_sat_cond_lib_cons : slow.

Definition swap_names {o} name name' (lib : @library o) : library :=
  MkLib (pre_swap_names name name' lib) (lib_cond lib).

Lemma lib_extends_preserves_perm_libs {o} :
  forall {name name'} {lib2 lib1 lib1' : @library o},
    lib_nodup lib1
    -> sat_lib_cond lib1
    -> strong_safe_library lib1
    -> lib_extends lib2 lib1
    -> swapped_css_libs name name' lib1 lib1'
    -> lib_extends (swap_names name name' lib2) lib1'
       /\ swapped_css_libs name name' lib2 (swap_names name name' lib2).
Proof.
  introv nodup sat safe ext sw.
  eapply lib_extends_preserves_sat_lib_cond in ext as sat'; auto.
  eapply lib_extends_preserves_strong_safe_library in ext as safe'; auto.
  eapply lib_extends_preserves_nodup in ext as nodup'; auto.

  unfold swapped_css_libs in *; repnd.
  inversion sw0 as [? ? ? ? ? ? ? eqsw eqa eqb]; clear sw0; subst.
  destruct lib1 as [lib1 cond1]; simpl in *; subst; simpl in *.
  destruct lib1' as [lib1' cond1']; simpl in *; subst; simpl in *.
  unfold same_conds in *; simpl in *; subst.
  unfold swap_names, pre_swap_names.
  remember (find_cs lib2 name) as fcsa; symmetry in Heqfcsa.
  remember (find_cs lib2 name') as fcsb; symmetry in Heqfcsb.
  destruct fcsa;
    [|eapply lib_extends_find_none_left_implies in ext;eauto; simpl in *;
      rewrite find_cs_app_eq in ext; remember (find_cs lib0 name) as xx; destruct xx; ginv; simpl in *; boolvar; tcsp;
      rewrite find_cs_app_eq in ext; remember (find_cs lib3 name) as xx; destruct xx; ginv; simpl in *; boolvar; tcsp;
      assert False; repndors; ginv; tcsp];[].
  destruct fcsb;
    [|eapply lib_extends_find_none_left_implies in ext;eauto; simpl in *;
      rewrite find_cs_app_eq in ext; remember (find_cs lib0 name') as xx; destruct xx; ginv; simpl in *; boolvar; tcsp;
      rewrite find_cs_app_eq in ext; remember (find_cs lib3 name') as xx; destruct xx; ginv; simpl in *; boolvar; tcsp;
      assert False; repndors; ginv; tcsp];[].

  applydup @lib_extends_implies_app_extension in ext; exrepnd.
  destruct lib2 as [lib2 cond2]; simpl in *; subst.
  apply extension_app_right_implies in ext2; exrepnd; subst; simpl in *.
  apply extension_cons_right_implies in ext2; exrepnd; subst; simpl in *.
  apply extension_app_right_implies in ext2; exrepnd; subst; simpl in *.
  apply extension_cons_right_implies in ext2; exrepnd; subst; simpl in *.
  apply entry_extends_lib_cs_right_implies in ext4; exrepnd; subst.
  apply entry_extends_lib_cs_right_implies in ext6; exrepnd; subst.

  assert (~in_lib (entry_name_cs name) lib) as na.
  { introv i; apply ext0 in i; destruct i.
    repeat first [rewrite in_lib_app | rewrite in_lib_cons]; simpl.
    repndors; ginv. }

  assert (~in_lib (entry_name_cs name') lib) as nb.
  { introv i; apply ext0 in i; destruct i.
    repeat first [rewrite in_lib_app | rewrite in_lib_cons]; simpl.
    repndors; ginv. }

  rewrite find_cs_app_right in Heqfcsa; auto.
  rewrite find_cs_app_right in Heqfcsb; auto.

  repeat (autorewrite with slow in *; simpl in *; repnd).
  rewrite @in_lib_app in *; rewrite @in_lib_cons in *.
  repeat (apply not_or in nodup5; repnd); simpl in *.
  repeat (apply not_or in nodup'11; repnd); simpl in *.

  apply sat_cond_lib_app_disj_implies in sat; repnd; autorewrite with slow; auto;[].
  apply sat_cond_lib_cons_disj_implies in sat; repnd; repeat first [rewrite in_lib_app | rewrite in_lib_cons]; simpl; tcsp;[].
  apply sat_cond_lib_app_disj_implies in sat; repnd; autorewrite with slow; auto;[].
  apply sat_cond_lib_cons_disj_implies in sat; repnd; repeat first [rewrite in_lib_app | rewrite in_lib_cons]; simpl; tcsp;[].
  apply sat_cond_lib_app_disj_implies in sat'; repnd; autorewrite with slow; auto;[].
  apply sat_cond_lib_app_disj_implies in sat'; repnd; autorewrite with slow; auto; simpl; try complete (dands; eauto 3 with slow);[].
  apply sat_cond_lib_cons_disj_implies in sat'; repnd; repeat first [rewrite in_lib_app | rewrite in_lib_cons]; simpl; tcsp;
    try (complete (intro xx; repndors; subst; tcsp; revert xx; eauto 3 with slow));[].
  apply sat_cond_lib_app_disj_implies in sat'; repnd; autorewrite with slow; auto; simpl; try complete (dands; eauto 3 with slow);[].
  apply sat_cond_lib_cons_disj_implies in sat'; repnd; repeat first [rewrite in_lib_app | rewrite in_lib_cons]; simpl; tcsp;
    try (complete (intro xx; repndors; subst; tcsp; revert xx; eauto 3 with slow));[].

  dands; repndors; ginv.

  { rewrite find_cs_app_right in Heqfcsa; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite find_cs_app_right in Heqfcsb; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite find_cs_app_right in Heqfcsb; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite app_assoc.
    rewrite swap_two_names_split_fst_eq; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup2; eauto 3 with slow)).
    rewrite swap_two_names_split_snd_eq; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup1; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup10; eauto 3 with slow)).
    rewrite swap_two_names_split_eq_not_in; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup5; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup9; eauto 3 with slow)).

    applydup @lib_extends_implies_same_conds in ext as same; unfold same_conds in same; simpl in *; subst.
    rewrite <- app_assoc.
    pose proof (implies_lib_extends_app
                  (MkLib lib cond1')
                  (MkLib (lib1 ++ lib_cs name2 c0 :: lib2 ++ lib_cs name1 c :: lib') cond1')
                  (MkLib [] cond1')
                  (MkLib (lib0 ++ lib_cs name2 e2 :: lib3 ++ lib_cs name1 e1 :: lib4) cond1')) as q.
    unfold same_conds in q; simpl in q.
    repeat (autorewrite with slow in q; simpl in q).
    repeat (autodimp q hyp); repnd; dands; eauto 3 with slow.

    { repeat (apply implies_extension_app; simpl; dands; eauto 3 with slow). }
    { repeat (first [apply implies_sat_cond_lib_app|apply implies_sat_cond_lib_cons]; eauto 3 with slow). }
    { repeat (first [rewrite in_lib_app|rewrite in_lib_cons]); simpl; tcsp. } }

  { rewrite find_cs_app_right in Heqfcsa; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite find_cs_app_right in Heqfcsa; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite find_cs_app_right in Heqfcsb; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite app_assoc.
    rewrite swap_two_names_split_snd_eq; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup2; eauto 3 with slow)).
    rewrite swap_two_names_split_fst_eq; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup1; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup10; eauto 3 with slow)).
    rewrite swap_two_names_split_eq_not_in; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup5; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup9; eauto 3 with slow)).

    applydup @lib_extends_implies_same_conds in ext as same; unfold same_conds in same; simpl in *; subst.
    rewrite <- app_assoc.
    pose proof (implies_lib_extends_app
                  (MkLib lib cond1')
                  (MkLib (lib1 ++ lib_cs name2 c :: lib2 ++ lib_cs name1 c0 :: lib') cond1')
                  (MkLib [] cond1')
                  (MkLib (lib0 ++ lib_cs name2 e2 :: lib3 ++ lib_cs name1 e1 :: lib4) cond1')) as q.
    unfold same_conds in q; simpl in q.
    repeat (autorewrite with slow in q; simpl in q).
    repeat (autodimp q hyp); repnd; dands; eauto 3 with slow.

    { repeat (apply implies_extension_app; simpl; dands; eauto 3 with slow). }
    { repeat (first [apply implies_sat_cond_lib_app|apply implies_sat_cond_lib_cons]; eauto 3 with slow). }
    { repeat (first [rewrite in_lib_app|rewrite in_lib_cons]); simpl; tcsp. } }

  { spcast; dands; auto.
    rewrite find_cs_app_right in Heqfcsa; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite find_cs_app_right in Heqfcsb; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite find_cs_app_right in Heqfcsb; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite app_assoc.
    rewrite swap_two_names_split_fst_eq; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup2; eauto 3 with slow)).
    rewrite swap_two_names_split_snd_eq; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup1; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup10; eauto 3 with slow)).
    rewrite swap_two_names_split_eq_not_in; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup5; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup9; eauto 3 with slow)). }

  { spcast; dands; auto.
    rewrite find_cs_app_right in Heqfcsa; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite find_cs_app_right in Heqfcsa; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite find_cs_app_right in Heqfcsb; eauto 3 with slow.
    simpl in *; boolvar; tcsp; GC; ginv.
    rewrite app_assoc.
    rewrite swap_two_names_split_snd_eq; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup2; eauto 3 with slow)).
    rewrite swap_two_names_split_fst_eq; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup1; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup10; eauto 3 with slow)).
    rewrite swap_two_names_split_eq_not_in; eauto 3 with slow;
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup5; eauto 3 with slow));
      try (complete (allrw @in_lib_app; intro xx; repndors; tcsp; destruct nodup9; eauto 3 with slow)). }
Qed.

Lemma eqset_nil_l :
  forall {A} (l : list A),
    eqset [] l <=> l = [].
Proof.
  introv; split; intro h; subst; tcsp.
  destruct l; tcsp.
  pose proof (h a) as h; simpl in h.
  destruct h as [h1 h2]; clear h1; autodimp h2 hyp; tcsp.
Qed.
Hint Rewrite @eqset_nil_l : slow.

Lemma swapped_css_preserves_lib_nodup {o} :
  forall {sw} {lib lib' : @plibrary o},
    swapped_css sw lib lib'
    -> lib_nodup lib
    -> lib_nodup lib'.
Proof.
  introv swap nodup.
  inversion swap as [? ? ? ? ? ? ? eqsw eqa eqb]; clear swap; subst.
  repeat (autorewrite with slow in *; repnd; simpl in *; repnd).
  rewrite in_lib_app, in_lib_cons in *.
  repeat (apply not_or in nodup5; repnd).
  dands; tcsp.
  introv xx; repndors; tcsp; simpl in *; subst; tcsp.
Qed.
Hint Resolve swapped_css_preserves_lib_nodup : slow.

Lemma swapped_css_libs_preserves_lib_nodup {o} :
  forall {name} {name'} {lib lib' : @library o},
    swapped_css_libs name name' lib lib'
    -> lib_nodup lib
    -> lib_nodup lib'.
Proof.
  introv swap nodup.
  unfold swapped_css_libs in *; repnd; eauto 3 with slow.
Qed.
Hint Resolve swapped_css_libs_preserves_lib_nodup : slow.

Lemma same_conds_sym {o} :
  forall (lib1 lib2 : @library o),
    same_conds lib1 lib2 -> same_conds lib2 lib1.
Proof.
  introv same; unfold same_conds in *; tcsp.
Qed.

Lemma swapped_css_sym {o} :
  forall {sw} {lib lib' : @plibrary o},
    swapped_css sw lib lib'
    -> swapped_css sw lib' lib.
Proof.
  introv swap.
  inversion swap as [? ? ? ? ? ? ? eqsw eqa eqb]; clear swap; subst.
  apply sw_css; tcsp.
Qed.

Lemma swapped_css_libs_sym {o} :
  forall {name} {name'} {lib lib' : @library o},
    swapped_css_libs name name' lib lib'
    -> swapped_css_libs name name' lib' lib.
Proof.
  introv swap.
  unfold swapped_css_libs in *; repnd; dands;[|apply same_conds_sym;auto].
  apply swapped_css_sym; auto.
Qed.

Lemma swapped_css_libs_preserves_sat_lib_cond {o} :
  forall {name} {name'} {lib lib' : @library o},
    swapped_css_libs name name' lib lib'
    -> lib_nodup lib
    -> sat_lib_cond lib
    -> sat_lib_cond lib'.
Proof.
  introv swap nodup sat.
  apply sat_lib_cond_implies_strong in sat; auto.
  apply strong_sat_lib_cond_implies_sat_lib_cond.
  clear nodup.
  unfold swapped_css_libs in *; repnd.
  inversion swap0 as [? ? ? ? ? ? ? eqsw eqa eqb]; clear swap0; subst.
  destruct lib as [lib cond]; simpl in *; subst.
  destruct lib' as [lib' cond']; simpl in *; subst.
  repeat (autorewrite with slow in *; repnd; simpl in *; repnd).
  unfold same_conds in *; simpl in *; subst.
  dands; tcsp.
Qed.
Hint Resolve swapped_css_libs_preserves_sat_lib_cond : slow.

Lemma swapped_css_libs_preserves_strong_safe_library {o} :
  forall {name} {name'} {lib lib' : @library o},
    swapped_css_libs name name' lib lib'
    -> strong_safe_library lib
    -> strong_safe_library lib'.
Proof.
  introv swap safe.
  unfold swapped_css_libs in *; repnd.
  inversion swap0 as [? ? ? ? ? ? ? eqsw eqa eqb]; clear swap0; subst.
  destruct lib as [lib cond]; simpl in *; subst.
  destruct lib' as [lib' cond']; simpl in *; subst.
  repeat (autorewrite with slow in *; repnd; simpl in *; repnd).
  unfold same_conds in *; simpl in *; subst.
  dands; tcsp.
Qed.
Hint Resolve swapped_css_libs_preserves_strong_safe_library : slow.

Definition perm_lib_per {o} {name} {name'} {lib : library} {lib'}
           (sat   : sat_lib_cond lib)
           (safe  : strong_safe_library lib)
           (nodup : lib_nodup lib)
           (swap  : swapped_css_libs name name' lib lib')
           (p     : lib-per(lib,o)) : lib-per(lib',o).
Proof.
  exists (fun lib'' (x : lib_extends lib'' lib') =>
            p _ (proj1 (lib_extends_preserves_perm_libs
                          (swapped_css_libs_preserves_lib_nodup swap nodup)
                          (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                          (swapped_css_libs_preserves_strong_safe_library swap safe)
                          x
                          (swapped_css_libs_sym swap)))).
  introv; apply lib_per_cond.
Defined.


Ltac one_move2ext ext :=
  match type of ext with
  | lib_extends ?lib1 ?lib2 =>
    match goal with
    | [ H : strong_safe_library ?lib3 |- _ ] =>
      let x := fresh "x" in
      assert (lib3 = lib2) as x by reflexivity; clear x;
      let h := fresh H in
      assert (strong_safe_library lib1) as h by eauto 3 with slow;
      clear H; rename h into H

    | [ H : lib_nodup ?lib3 |- _ ] =>
      let x := fresh "x" in
      assert (lib3 = lib2) as x by reflexivity; clear x;
      let h := fresh H in
      assert (lib_nodup lib1) as h by eauto 3 with slow;
      clear H; rename h into H

    | [ H : sat_lib_cond ?lib3 |- _ ] =>
      let x := fresh "x" in
      assert (lib3 = lib2) as x by reflexivity; clear x;
      let h := fresh H in
      assert (sat_lib_cond lib1) as h by eauto 3 with slow;
      clear H; rename h into H

    | [ H : has_lib_cond_no_cs ?lib3 |- _ ] =>
      let x := fresh "x" in
      assert (lib3 = lib2) as x by reflexivity; clear x;
      let h := fresh H in
      assert (has_lib_cond_no_cs lib1) as h by eauto 3 with slow;
      clear H; rename h into H
    end
  end.

Ltac move2ext ext :=
  repeat (one_move2ext ext);
  match type of ext with
  | lib_extends ?lib1 ?lib2 =>
    try (clear dependent lib2); rename lib1 into lib2
  end.

Lemma find_cs_swap_two_names_diff_left {o} :
  forall name c name' c' (lib : @plibrary o),
    name <> name'
    -> find_cs (swap_two_names name c name' c' lib) name
       = match find_cs lib name' with
         | Some e => Some c
         | None => None
         end.
Proof.
  induction lib; introv d; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; GC; subst; tcsp; GC.
Qed.

Lemma find_cs_swap_two_names_diff_right {o} :
  forall name c name' c' (lib : @plibrary o),
    name <> name'
    -> find_cs (swap_two_names name c name' c' lib) name'
       = match find_cs lib name with
         | Some e => Some c'
         | None => None
         end.
Proof.
  induction lib; introv d; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; GC; subst; tcsp; GC.
Qed.

Lemma find_cs_swap_two_names_same {o} :
  forall name c (lib : @plibrary o),
    find_cs (swap_two_names name c name c lib) name
    = match find_cs lib name with
      | Some e => Some c
      | None => None
      end.
Proof.
  induction lib; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; GC; subst; tcsp; GC.
Qed.

Lemma swap_two_names_same {o} :
  forall name c (lib : @plibrary o),
    lib_nodup lib
    -> find_cs lib name = Some c
    -> swap_two_names name c name c lib = lib.
Proof.
  induction lib; introv nodup fcs; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; subst; tcsp; GC; ginv; repnd; tcsp;
    try (complete (rewrite IHlib; auto)).
  rewrite swap_two_names_split_eq_not_in; auto.
Qed.

Lemma find_cs_non_implies_not_in_lib2 {o} :
  forall (lib : @plibrary o) name,
    find_cs lib name = None
    -> ~ in_lib (entry_name_cs name) lib.
Proof.
  induction lib; introv fcs i; simpl in *; tcsp; ginv.
  { unfold in_lib in *; simpl in *; exrepnd; tcsp. }
  destruct a; simpl in *; boolvar; tcsp; ginv.
  { apply IHlib in fcs; clear IHlib; destruct fcs.
    unfold in_lib in *; simpl in *; exrepnd; repndors; subst; simpl in *; subst; tcsp; eauto. }
  { apply IHlib in fcs; clear IHlib; destruct fcs.
    unfold in_lib in *; simpl in *; exrepnd; repndors; subst; simpl in *; subst; tcsp; eauto. }
Qed.
Hint Resolve find_cs_non_implies_not_in_lib2 : slow.

Lemma swap_two_names_twice_same_right {o} :
  forall name1 c1 name2 c2 (lib : @plibrary o),
    name1 <> name2
    -> lib_nodup lib
    -> find_cs lib name1 = None
    -> find_cs lib name2 = Some c2
    -> swap_two_names name1 c1 name2 c2 (swap_two_names name1 c1 name2 c2 lib) = lib.
Proof.
  induction lib; introv d nodup fcsa fcsb; simpl in *; tcsp; repnd.
  destruct a; simpl in *; repeat (boolvar; subst; tcsp; GC; ginv; repnd; simpl in *; tcsp);
    try (complete (rewrite IHlib; auto)).
  rewrite (swap_two_names_split_eq_not_in _ _ _ _ lib); auto; eauto 3 with slow.
  rewrite (swap_two_names_split_eq_not_in _ _ _ _ lib); auto; eauto 3 with slow.
Qed.

Lemma swap_two_names_twice_same_left {o} :
  forall name1 c1 name2 c2 (lib : @plibrary o),
    name1 <> name2
    -> lib_nodup lib
    -> find_cs lib name1 = Some c1
    -> find_cs lib name2 = None
    -> swap_two_names name1 c1 name2 c2 (swap_two_names name1 c1 name2 c2 lib) = lib.
Proof.
  induction lib; introv d nodup fcsa fcsb; simpl in *; tcsp; repnd.
  destruct a; simpl in *; repeat (boolvar; subst; tcsp; GC; ginv; repnd; simpl in *; tcsp);
    try (complete (rewrite IHlib; auto)).
  rewrite (swap_two_names_split_eq_not_in _ _ _ _ lib); auto; eauto 3 with slow.
  rewrite (swap_two_names_split_eq_not_in _ _ _ _ lib); auto; eauto 3 with slow.
Qed.

Lemma swap_two_names_twice {o} :
  forall name1 c1 name2 c2 (lib : @plibrary o),
    name1 <> name2
    -> lib_nodup lib
    -> find_cs lib name1 = Some c1
    -> find_cs lib name2 = Some c2
    -> swap_two_names name1 c1 name2 c2 (swap_two_names name1 c1 name2 c2 lib) = lib.
Proof.
  induction lib; introv d nodup fcsa fcsb; simpl in *; tcsp; repnd.
  destruct a; simpl in *; repeat (boolvar; subst; simpl in *; tcsp; GC; ginv);
    try (complete (rewrite IHlib; auto)).
  { rewrite swap_two_names_twice_same_right; auto; eauto 3 with slow. }
  { rewrite swap_two_names_twice_same_left; auto; eauto 3 with slow. }
Qed.

Lemma swap_names_twice {o} :
  forall name name' (lib : @library o),
    lib_nodup lib
    -> swap_names name name' (swap_names name name' lib) = lib.
Proof.
  introv nodup; destruct lib as [lib cond]; unfold swap_names; simpl; f_equal.
  unfold pre_swap_names; simpl.
  remember (find_cs lib name) as fcsa; symmetry in Heqfcsa.
  remember (find_cs lib name') as fcsb; symmetry in Heqfcsb.
  destruct fcsa, fcsb; simpl in *; allrw; tcsp.

  destruct (choice_sequence_name_deq name' name); subst; tcsp.

  { rewrite Heqfcsb in *; ginv.
    rewrite find_cs_swap_two_names_same; allrw.
    repeat rewrite (swap_two_names_same _ _ lib); auto. }

  { rewrite find_cs_swap_two_names_diff_left; tcsp.
    rewrite find_cs_swap_two_names_diff_right; tcsp.
    allrw.
    rewrite swap_two_names_twice; auto. }
Qed.

Lemma in_open_bar_ext_swapped_css_libs_pres {o} :
  forall name name' (lib lib' : @library o)
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib')
         (F : forall lib'' (x : lib_extends lib'' lib), Prop)
         (G : forall lib'' (x : lib_extends lib'' lib'), Prop),
    in_ext_ext lib (fun lib'' (x : lib_extends lib'' lib) =>
                      forall (y : lib_extends (swap_names name name' lib'') lib'),
                        F lib'' x -> G (swap_names name name' lib'') y)
    -> in_open_bar_ext lib F
    -> in_open_bar_ext lib' G.
Proof.
  introv nodup sat safe swap imp h.
  introv ext.

  applydup @swapped_css_libs_sym in swap as swap'.
  assert (lib_nodup lib') as nodup' by eauto 3 with slow.
  assert (sat_lib_cond lib') as sat' by eauto 3 with slow.
  assert (strong_safe_library lib') as safe' by eauto 3 with slow.
  pose proof (lib_extends_preserves_perm_libs nodup' sat' safe' ext swap') as q; repnd; spcast.

  pose proof (h _ q0) as h; exrepnd.

  applydup @swapped_css_libs_sym in q as swap''.
  assert (lib_nodup (swap_names name name' lib'0)) as nodup'' by eauto 3 with slow.
  assert (sat_lib_cond (swap_names name name' lib'0)) as sat'' by eauto 3 with slow.
  assert (strong_safe_library (swap_names name name' lib'0)) as safe'' by eauto 3 with slow.
  pose proof (lib_extends_preserves_perm_libs nodup'' sat'' safe'' y swap'') as z; repnd; spcast.

  exists (swap_names name name' lib'') z0.
  introv xta; introv.

  applydup @swapped_css_libs_sym in z as swap'''.
  assert (lib_nodup (swap_names name name' lib'')) as nodup''' by eauto 3 with slow.
  assert (sat_lib_cond (swap_names name name' lib'')) as sat''' by eauto 3 with slow.
  assert (strong_safe_library (swap_names name name' lib'')) as safe''' by eauto 3 with slow.
  pose proof (lib_extends_preserves_perm_libs nodup''' sat''' safe''' xta swap''') as w; repnd; spcast.

  assert (lib_extends (swap_names name name' lib'1) lib) as xtb by eauto 3 with slow.
  pose proof (imp (swap_names name name' lib'1) xtb) as imp; simpl in imp.
  rewrite swap_names_twice in imp; eauto 3 with slow.
Qed.

Lemma eq_term_equals_per_bar_eq_per_lib_per {o} :
  forall name name'
         (lib   : @library o)
         (lib'  : @library o)
         (nodup : lib_nodup lib)
         (safe  : strong_safe_library lib)
         (sat   : sat_lib_cond lib)
         (swap  : swapped_css_libs name name' lib lib')
         (eqa   : lib-per(lib,o)),
    (per_bar_eq lib eqa) <=2=> (per_bar_eq lib' (perm_lib_per sat safe nodup swap eqa)).
Proof.
  repeat introv; unfold per_bar_eq; split; intro h.

  { eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; clear h.
    introv h; simpl.
    remember (proj1
                (lib_extends_preserves_perm_libs
                   (swapped_css_libs_preserves_lib_nodup swap nodup)
                   (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                   (swapped_css_libs_preserves_strong_safe_library swap safe) y
                   (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
    eapply lib_per_cond; eauto. }

  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; clear h; eauto 3 with slow.
    introv h; simpl in *.
    remember (proj1
                (lib_extends_preserves_perm_libs
                   (swapped_css_libs_preserves_lib_nodup swap nodup)
                   (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                   (swapped_css_libs_preserves_strong_safe_library swap safe) e
                   (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    eapply lib_per_cond; eauto. }
Qed.

Lemma swapped_css_preserves_find_cs {o} :
  forall sw (lib lib' : @plibrary o) name,
    lib_nodup lib
    -> swapped_css sw lib lib'
    -> find_cs lib name = find_cs lib' name.
Proof.
  introv nodup h.
  inversion h as [? ? ? ? ? ? ? q]; subst; simpl in *; clear h.
  repeat (autorewrite with slow in *; simpl in *; repnd).
  rewrite in_lib_app in nodup5; apply not_or in nodup5; repnd.
  rewrite in_lib_cons in nodup5; apply not_or in nodup5; repnd.
  simpl in *; GC.
  repeat (rewrite find_cs_app_eq; simpl).
  remember (find_cs lib1 name) as fcsa; symmetry in Heqfcsa; destruct fcsa; auto.
  boolvar; subst; tcsp; GC.

  { remember (find_cs lib2 name1) as fcsb; symmetry in Heqfcsb; destruct fcsb; tcsp.
    apply find_cs_some_implies_in_lib in Heqfcsb; tcsp. }

  { remember (find_cs lib2 name2) as fcsb; symmetry in Heqfcsb; destruct fcsb; tcsp.
    apply find_cs_some_implies_in_lib in Heqfcsb; tcsp. }
Qed.

Lemma swapped_css_preserves_find_cs_value_at {o} :
  forall sw (lib lib' : @plibrary o) name n,
    lib_nodup lib
    -> swapped_css sw lib lib'
    -> find_cs_value_at lib name n = find_cs_value_at lib' name n.
Proof.
  introv nodup swap.
  unfold find_cs_value_at.
  rewrite (swapped_css_preserves_find_cs sw lib lib' name); auto.
Qed.

Lemma swapped_css_preserves_find_last_entry_default {o} :
  forall sw (lib lib' : @plibrary o) name d,
    lib_nodup lib
    -> swapped_css sw lib lib'
    -> find_last_entry_default lib name d = find_last_entry_default lib' name d.
Proof.
  introv nodup swap.
  unfold find_last_entry_default.
  rewrite (swapped_css_preserves_find_cs sw lib lib' name); auto.
Qed.

Lemma find_entry_app {o} :
  forall (lib1 lib2 : @plibrary o) op bs,
    find_entry (lib1 ++ lib2) op bs =
    match find_entry lib1 op bs with
    | Some e => Some e
    | None => find_entry lib2 op bs
    end.
Proof.
  induction lib1; introv; simpl; tcsp.
  destruct a; simpl in *; tcsp; boolvar; tcsp.
Qed.

Lemma swapped_css_preserves_find_entry {o} :
  forall sw (lib lib' : @plibrary o) op bs,
    lib_nodup lib
    -> swapped_css sw lib lib'
    -> find_entry lib op bs = find_entry lib' op bs.
Proof.
  introv nodup h.
  inversion h as [? ? ? ? ? ? ? q]; subst; simpl in *; clear h.
  repeat (autorewrite with slow in *; simpl in *; repnd).
  rewrite in_lib_app in nodup5; apply not_or in nodup5; repnd.
  rewrite in_lib_cons in nodup5; apply not_or in nodup5; repnd.
  simpl in *; GC.
  repeat (rewrite find_entry_app; simpl); tcsp.
Qed.

Lemma swapped_css_preserves_found_entry {o} :
  forall sw (lib lib' : @plibrary o) op bs oa vars rhs cor,
    lib_nodup lib
    -> swapped_css sw lib lib'
    -> found_entry lib op bs oa vars rhs cor
    -> found_entry lib' op bs oa vars rhs cor.
Proof.
  introv nodup h found.
  unfold found_entry in *.
  erewrite swapped_css_preserves_find_entry; eauto;
    [|apply swapped_css_sym;eauto]; eauto 3 with slow.
Qed.
Hint Resolve swapped_css_preserves_found_entry : slow.

Definition alpha_eq_comp_res {o} (r1 r2 : @Comput_Result o) :=
  match r1, r2 with
  | csuccess a, csuccess b => alpha_eq a b
  | cfailure s1 t1, cfailure s2 t2 => True
  | _, _ => False
  end.

Lemma alpha_eq_comp_res_refl {o} :
  forall (a : @Comput_Result o), alpha_eq_comp_res a a.
Proof.
  introv.
  destruct a; simpl; eauto 3 with slow.
Qed.
Hint Resolve alpha_eq_comp_res_refl : slow.

Lemma implies_alpha_eq_comp_res_on_success {o} :
  forall (a b : @Comput_Result o) f,
    alpha_eq_comp_res a b
    -> (forall x y, alpha_eq x y -> alpha_eq (f x) (f y))
    -> alpha_eq_comp_res (on_success a f) (on_success b f).
Proof.
  introv aeqa aeqb.
  destruct a, b; simpl in *; tcsp.
Qed.

Lemma on_success_csuccess {o} :
  forall (c : @Comput_Result o) f b,
    on_success c f = csuccess b
    -> {x : NTerm & c = csuccess x /\ b = f x}.
Proof.
  introv h; destruct c; simpl in *; ginv; eauto.
Qed.

Lemma swapped_css_preserves_get_utokens_library {o} :
  forall sw (lib lib' : @plibrary o) x,
    swapped_css sw lib lib'
    -> LIn x (get_utokens_library lib)
    -> LIn x (get_utokens_library lib').
Proof.
  introv swap i.
  apply LIn_iff_In; try apply get_patom_deq.
  apply LIn_iff_In in i; try apply get_patom_deq.
  inversion swap; subst; simpl in *; clear swap.
  unfold get_utokens_library in *.
  repeat (rewrite flat_map_app in *; simpl in *); tcsp.
  repeat (rewrite list_in_app in *; simpl in *); tcsp.
Qed.
Hint Resolve swapped_css_preserves_get_utokens_library : slow.

Lemma swapped_css_preserves_get_utokens_lib {o} :
  forall sw (lib lib' : @plibrary o) t x,
    swapped_css sw lib lib'
    -> LIn x (get_utokens_lib lib t)
    -> LIn x (get_utokens_lib lib' t).
Proof.
  introv swap i; unfold get_utokens_lib in *; allrw in_app_iff; repndors; tcsp; right; eauto 3 with slow.
Qed.
Hint Resolve swapped_css_preserves_get_utokens_lib : slow.

Ltac dterm name :=
  match goal with
  (* ** on conclusion ** *)
  | [ |- context[ match ?c with | [] => _ | _ :: _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [|name1 name2]
  | [ |- context[ match ?c with | vterm _ => _ | oterm _ _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [|name1 name2]
  | [ |- context[ match ?c with | Can _ => _ | NCan _ => _ | Exc => _ | Abs _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    remember c as name0; destruct name0 as [name1|name1|name1|name1]
  | [ |- context[ match ?c with | bterm _ _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1 name2]
  | [ |- context[ match (match ?c with | csuccess _ => _ | cfailure _ _ => _ end) with _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1|name1 name2]
  | [ |- context[ match ?c with | csuccess _ => _ | cfailure _ _ => _ end ] ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1|name1 name2]
  | [ |- context[ match ?c with _ => _ end ] ] =>
    match type of c with
    | CanonicalOp =>
      let name0 := fresh name in
      remember c as name0; destruct name0
    | NonCanonicalOp =>
      let name0 := fresh name in
      remember c as name0; destruct name0
    end

  (* ** on hypotheses ** *)
  | [ H : context[ match ?c with | [] => _ | _ :: _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [|name1 name2]
  | [ H : context[ match ?c with | vterm _ => _ | oterm _ _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [|name1 name2]
  | [ H : context[ match ?c with | Can _ => _ | NCan _ => _ | Exc => _ | Abs _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    remember c as name0; destruct name0 as [name1|name1|name1|name1]
  | [ H : context[ match ?c with | bterm _ _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1 name2]
  | [ H : context[ match (match ?c with | csuccess _ => _ | cfailure _ _ => _ end) with _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1|name1 name2]
  | [ H : context[ match ?c with | csuccess _ => _ | cfailure _ _ => _ end ] |- _ ] =>
    let name0 := fresh name in
    let name1 := fresh name in
    let name2 := fresh name in
    remember c as name0; destruct name0 as [name1|name1 name2]
  | [ H : context[ match ?c with _ => _ end ] |- _ ] =>
    match type of c with
    | CanonicalOp =>
      let name0 := fresh name in
      remember c as name0; destruct name0
    | NonCanonicalOp =>
      let name0 := fresh name in
      remember c as name0; destruct name0
    end
  end.

Ltac dterms name :=
  repeat (dterm name; subst; simpl in *; ginv; eauto 2 with slow).

Lemma swapped_css_compute_step {o} :
  forall {sw} {lib lib' : @plibrary o} {a b : @NTerm o},
    nt_wf a
    -> lib_nodup lib
    -> swapped_css sw lib lib'
    -> compute_step lib a = csuccess b
    -> {c : NTerm & compute_step lib' a = csuccess c # alpha_eq b c}.
Proof.
  nterm_ind1s a as [v|op bs ind] Case; introv wf nodup swap comp; tcsp.

  { Case "vterm".
    csunf comp; simpl in *; ginv. }

  Case "oterm".
  dopid op as [can|ncan|exc|abs] SCase.

  { SCase "Can".
    csunf; simpl in *; ginv; eauto 3 with slow. }

  { SCase "NCan".
    csunf comp; simpl in *.
    dterms w; try (complete (csunf; simpl; eauto));
      try (complete (apply on_success_csuccess in comp; exrepnd; subst; simpl in *;
                     eapply ind in comp1; try (left; eauto); eauto 3 with slow; exrepnd;
                     csunf; simpl; allrw; simpl; eexists; dands; eauto;
                     repeat (prove_alpha_eq4; auto; intros k w; repeat (destruct k; simpl in *; tcsp)))).

    { csunf; simpl.
      applydup @compute_step_fresh_bs_nil in comp; repnd; subst; GC.
      apply compute_step_fresh_success in comp; repnd; GC; repndors; exrepnd; subst; ginv;
        try (complete (simpl in *; boolvar; eauto)).

      { simpl; dterms w; simpl in *; eauto; tcsp;
          try (complete (unfold isvalue_like in *; simpl in *; tcsp)). }

      rewrite compute_step_fresh_if_isnoncan_like0; auto; simpl.

      remember (get_fresh_atom lib w2) as a'.
      remember (get_fresh_atom lib' w2) as a''.

      pose proof (get_fresh_atom_prop_and_lib lib w2) as fa'; rw <- Heqa' in fa'.
      pose proof (get_fresh_atom_prop_and_lib lib' w2) as fa''; rw <- Heqa'' in fa''.

      pose proof (compute_step_subst_utoken lib w2 x [(w0, mk_utoken a')]) as ch.
      allrw @nt_wf_fresh.
      repeat (autodimp ch hyp); eauto 4 with slow.
      { unfold get_utokens_sub; simpl; apply disjoint_singleton_l; tcsp. }
      exrepnd.

      pose proof (ch0 [(w0,mk_utoken a'')]) as comp'; clear ch0; allsimpl.
      repeat (autodimp comp' hyp).
      { apply nr_ut_sub_cons; auto; introv i j.
        destruct fa''; eauto 3 with slow. }
      { unfold get_utokens_sub; simpl; rw disjoint_singleton_l; intro i.
        destruct fa''; eauto 3 with slow. }
      exrepnd.
      allrw @fold_subst.

      pose proof (ind w2 (subst w2 w0 (mk_utoken a'')) [w0]) as h; clear ind.
      repeat (autodimp h hyp).
      { rw @simple_osize_subst; eauto 3 with slow. }
      pose proof (h s) as k; clear h.
      repeat (autodimp k hyp); eauto 3 with slow.

      exrepnd; allrw; simpl.
      eexists; dands; eauto.
      pose proof (implies_alpha_eq_mk_fresh_subst_utokens w0 (get_fresh_atom lib' w2) s (subst w w0 (mk_utoken a'')) comp'0) as h.

      eapply alpha_eq_trans;
        [|apply implies_alpha_eq_mk_fresh; apply alpha_eq_subst_utokens_same; eauto].
      apply alpha_eq_sym; eapply alpha_eq_trans;[exact h|clear h].
      eapply alpha_eq_trans;
        [apply implies_alpha_eq_mk_fresh;
         rewrite <- Heqa'';
         apply simple_alphaeq_subst_utokens_subst|].

      { intro h.
        apply (get_utokens_subset_get_utokens_lib lib) in h.
        apply ch4 in h.
        allrw @get_utokens_lsubst; allrw @get_utokens_lib_lsubst;
          allrw in_app_iff; allrw not_over_or; repnd.
        repndors; tcsp.
        destruct fa''; eauto 3 with slow. }

      apply implies_alpha_eq_mk_fresh.
      apply (alpha_eq_subst_utokens _ _ [(a',mk_var w0)] [(a',mk_var w0)]) in ch1; eauto 3 with slow.
      pose proof (simple_alphaeq_subst_utokens_subst w w0 a') as aeq1.
      autodimp aeq1 hyp.
      { intro xx.
        apply (get_utokens_subset_get_utokens_lib lib) in xx.
        apply ch4 in xx; tcsp. }

      assert (alpha_eq (subst_utokens x [(a', mk_var w0)]) w) as aeq2; eauto 3 with slow; clear aeq1.
      apply alpha_eq_sym; subst; auto. }

    dopid_noncan ncan SSSCase; simpl in *;
      try (complete (csunf; simpl in *; eexists; dands; eauto)).

    { SSSCase "NEApply".
      apply compute_step_eapply_success in comp; exrepnd; subst; tcsp.
      inversion comp0; subst.
      repndors; exrepnd; subst; tcsp;
        try (complete (csunf; simpl; unfold compute_step_eapply; dcwf h; simpl; dterms w; tcsp; GC; eauto)).

      { apply compute_step_eapply2_success in comp1; repeat (repndors; exrepnd; subst; simpl in *; tcsp).
        { inversion comp4; subst; simpl in *; csunf; simpl; unfold compute_step_eapply; simpl; dterms w; tcsp; GC; eauto. }
        { inversion comp1; subst; simpl in *; csunf; simpl; unfold compute_step_eapply; simpl; boolvar; try omega.
          autorewrite with slow.
          rewrite (swapped_css_preserves_find_cs_value_at (sw0,sw) lib' lib name n); eauto 3 with slow;
            try apply swapped_css_sym; auto; allrw; eauto. } }

      { eapply ind in comp1; try (right; eauto); eauto 3 with slow; exrepnd.
        csunf; simpl; unfold compute_step_eapply; dcwf h; simpl; dterms w; simpl in *; allrw; simpl; eauto;
          try (complete (unfold isnoncan_like in *; simpl in *; tcsp));
          eexists; dands; eauto; prove_alpha_eq4; intros k w;
            repeat (destruct k; simpl in *; tcsp); prove_alpha_eq4; auto. } }

    { SSSCase "NLastCs".
      apply compute_step_last_cs_success in comp; exrepnd; subst; simpl in *.
      inversion comp3; subst; simpl in *.
      csunf; simpl; eexists; dands; eauto.
      erewrite swapped_css_preserves_find_last_entry_default; eauto. }

    { SSSCase "NCompOp".
      csunf; simpl; dcwf h; dterms w; simpl in *; tcsp; dcwf h; eauto;
        apply on_success_csuccess in comp; exrepnd; subst; simpl in *;
          eapply ind in comp1; try (right; left; eauto); eauto 3 with slow; exrepnd;
       allrw; simpl; eexists; dands; eauto; prove_alpha_eq4; intros k w; repeat (destruct k; tcsp); prove_alpha_eq4; auto. }

    { SSSCase "NArithOp".
      csunf; simpl; dcwf h; dterms w; simpl in *; tcsp; dcwf h; eauto;
        apply on_success_csuccess in comp; exrepnd; subst; simpl in *;
          eapply ind in comp1; try (right; left; eauto); eauto 3 with slow; exrepnd;
       allrw; simpl; eexists; dands; eauto; prove_alpha_eq4; intros k w; repeat (destruct k; tcsp); prove_alpha_eq4; auto. } }

  { SSCase "Exc".
    csunf comp; simpl in *; ginv; csunf; simpl; eauto. }

  { SSCase "Abs".
    csunf comp; simpl in *.
    apply compute_step_lib_success in comp; exrepnd; subst; simpl in *.
    csunf; simpl.
    eapply swapped_css_preserves_found_entry in comp0; eauto.
    erewrite found_entry_implies_compute_step_lib_success; eauto. }
Qed.

Lemma swapped_css_compute_at_most_k_steps {o} :
  forall {sw} {lib lib' : @plibrary o} n {a b : @NTerm o},
    nt_wf a
    -> lib_nodup lib
    -> swapped_css sw lib lib'
    -> compute_at_most_k_steps lib n a = csuccess b
    -> {c : NTerm & compute_at_most_k_steps lib' n a = csuccess c # alpha_eq b c}.
Proof.
  induction n; introv wf nodup swap comp; simpl in *; ginv; eauto.
  remember (compute_at_most_k_steps lib n a) as comp'; symmetry in Heqcomp'.
  destruct comp'; ginv.
  eapply IHn in Heqcomp'; auto; exrepnd; allrw.
  applydup @compute_at_most_k_steps_preserves_wf in Heqcomp'1; auto.
  eapply compute_step_alpha in comp; eauto; eauto 3 with slow; exrepnd.
  eapply swapped_css_compute_step in comp1; eauto; eauto 3 with slow.
  exrepnd; eexists; dands; eauto; eauto 3 with slow.
Qed.

Lemma swapped_css_reduces_in_atmost_k_steps {o} :
  forall {sw} {lib lib' : @plibrary o} n {a b : @NTerm o},
    nt_wf a
    -> lib_nodup lib
    -> swapped_css sw lib lib'
    -> reduces_in_atmost_k_steps lib a b n
    -> {c : NTerm & reduces_in_atmost_k_steps lib' a c n # alpha_eq b c}.
Proof.
  introv wf nodup swap r.
  unfold reduces_in_atmost_k_steps in *.
  eapply swapped_css_compute_at_most_k_steps in r; eauto.
Qed.

Lemma swapped_css_reduces_to {o} :
  forall {sw} {lib lib' : @plibrary o} {a b : @NTerm o},
    nt_wf a
    -> lib_nodup lib
    -> swapped_css sw lib lib'
    -> reduces_to lib a b
    -> {c : NTerm & reduces_to lib' a c # alpha_eq b c}.
Proof.
  introv wf nodup swap r; unfold reduces_to in *; exrepnd.
  eapply swapped_css_reduces_in_atmost_k_steps in r0; eauto; exrepnd.
  exists c; dands; auto; eauto.
Qed.

Lemma swapped_css_computes_to_value {o} :
  forall {sw} {lib lib' : @plibrary o} {a b : @NTerm o},
    nt_wf a
    -> lib_nodup lib
    -> swapped_css sw lib lib'
    -> computes_to_value lib a b
    -> {c : NTerm & computes_to_value lib' a c # alpha_eq b c}.
Proof.
  introv wf nodup swap r; unfold computes_to_value in *; repnd; dands; auto.
  eapply swapped_css_reduces_to in r0; eauto; exrepnd.
  exists c; dands; eauto 3 with slow.
Qed.

Lemma swapped_css_ccomputes_to_valc {o} :
  forall {sw} {lib lib' : @plibrary o} {a b : @CTerm o},
    lib_nodup lib
    -> swapped_css sw lib lib'
    -> ccomputes_to_valc lib a b
    -> exists (c : CTerm), ccomputes_to_valc lib' a c /\ Cast (alphaeqc b c).
Proof.
  introv nodup swap comp; spcast.
  destruct_cterms; simpl in *.
  unfold computes_to_valc in *; simpl in *.
  eapply swapped_css_computes_to_value in comp; eauto; eauto 3 with slow; exrepnd.
  assert (isprog c) as wc by eauto 3 with slow.
  exists (mk_ct c wc); simpl; dands; spcast; tcsp.
Qed.

Lemma swapped_css_libs_ccomputes_to_valc {o} :
  forall {name name'} {lib lib' : @library o} {a b : @CTerm o},
    lib_nodup lib
    -> swapped_css_libs name name' lib lib'
    -> ccomputes_to_valc lib a b
    -> exists (c : CTerm), ccomputes_to_valc lib' a c /\ Cast (alphaeqc b c).
Proof.
  introv nodup swap comp; spcast.
  unfold swapped_css_libs in *; repnd; simpl in *.
  eapply swapped_css_ccomputes_to_valc; try exact comp; eauto; spcast; auto.
Qed.

Lemma alpha_eq_bterms_implies_len {o} :
  forall (l k : list (@BTerm o)),
    alpha_eq_bterms l k
    -> length l = length k.
Proof.
  introv h; inversion h; tcsp.
Qed.

Lemma alpha_eq_bterms_implies_alpha_eq_bterm_selectbt {o} :
  forall (bs1 bs2 : list (@BTerm o)) n,
    alpha_eq_bterms bs1 bs2
    -> n < Datatypes.length bs2
    -> alpha_eq_bterm (selectbt bs1 n) (selectbt bs2 n).
Proof.
  introv aeq len; unfold alpha_eq_bterms in *; repnd.
  apply aeq.
  eapply select2bts in aeq0;[|rewrite aeq0; eauto]; exrepnd; subst; auto.
Qed.

Lemma swapped_css_approx {o} :
  forall {sw} {lib lib' : @plibrary o} {a b : @NTerm o},
    lib_nodup lib
    -> swapped_css sw lib lib'
    -> approx lib a b
    -> approx lib' a b.
Proof.
  cofix ind; introv nodup swap apx.
  destruct apx as [cc].
  destruct cc as [isp1 [isp2 [cv [ce cc] ] ] ]; GC.
  constructor.
  unfold close_comput; dands; auto.

  { introv compa.
    eapply swapped_css_computes_to_value in compa;
      [| | |apply swapped_css_sym;eauto]; eauto 3 with slow.
    exrepnd.
    apply alpha_eq_oterm_implies_combine2 in compa0; exrepnd; subst.

    apply cv in compa1; exrepnd.
    eapply swapped_css_computes_to_value in compa1; eauto; eauto 3 with slow; exrepnd.
    apply alpha_eq_oterm_implies_combine2 in compa3; exrepnd; subst.

    exists bs'0; dands; auto.
    applydup @alpha_eq_bterms_implies_len in compa2 as len1.
    applydup @alpha_eq_bterms_implies_len in compa4 as len2.
    unfold lblift in *; repnd; dands; auto; try congruence.
    introv len.
    rewrite len1 in len; applydup compa0 in len; clear compa0.
    unfold blift in *; exrepnd.
    exists lv nt1 nt2; dands; auto.
    { unfold olift in *; repnd; dands; auto.
      introv wf ispa ispb.
      pose proof (len0 _ wf ispa ispb) as len0. repndors; tcsp; left.
      eapply ind; eauto. }
    { eapply alpha_eq_bterm_trans;[|eauto].
      apply alpha_eq_bterms_implies_alpha_eq_bterm_selectbt; auto. }
    { eapply alpha_eq_bterm_trans;[|eauto].
      apply alpha_eq_bterm_sym.
      apply alpha_eq_bterms_implies_alpha_eq_bterm_selectbt; auto; omega. } }

  { introv compa.
    eapply swapped_css_reduces_to in compa;
      [| | |apply swapped_css_sym;eauto]; eauto 3 with slow.
    exrepnd.
    apply alpha_eq_exception in compa0; exrepnd; subst.
    apply ce in compa1; exrepnd.
    eapply swapped_css_reduces_to in compa2; eauto; eauto 3 with slow; exrepnd.
    apply alpha_eq_exception in compa5; exrepnd; subst.
    exists a'1 e'1; dands; auto.
    { repndors; tcsp; left; eapply ind; eauto.
      eapply approx_alpha_rw_r_aux;[eauto|].
      eapply approx_alpha_rw_l_aux;[apply alpha_eq_sym;eauto|]; tcsp. }
    { repndors; tcsp; left; eapply ind; eauto.
      eapply approx_alpha_rw_r_aux;[eauto|].
      eapply approx_alpha_rw_l_aux;[apply alpha_eq_sym;eauto|]; tcsp. } }
Qed.

Lemma swapped_css_approxc {o} :
  forall {sw} {lib lib' : @plibrary o} {a b : @CTerm o},
    lib_nodup lib
    -> swapped_css sw lib lib'
    -> approxc lib a b
    -> approxc lib' a b.
Proof.
  introv swap apx; spcast.
  destruct_cterms; unfold approxc in *; simpl in *.
  eapply swapped_css_approx; eauto.
Qed.

Lemma swapped_css_libs_capproxc {o} :
  forall {name} {name'} {lib lib' : @library o} {a b : @CTerm o},
    lib_nodup lib
    -> swapped_css_libs name name' lib lib'
    -> a ~<~(lib) b
    -> a ~<~(lib') b.
Proof.
  introv nodup swap apx; spcast.
  unfold swapped_css_libs in *; repnd.
  eapply swapped_css_approxc; eauto.
Qed.

Lemma swapped_css_ccequivc {o} :
  forall {sw} {lib lib' : @plibrary o} {a b : @CTerm o},
    lib_nodup lib
    -> swapped_css sw lib lib'
    -> a ~=~(lib) b
    -> a ~=~(lib') b.
Proof.
  introv nodup swap ceq; spcast.
  allrw @cequivc_iff_approxc; repnd.
  unfold swapped_css_libs in *; repnd.
  dands; eapply swapped_css_approxc; eauto.
Qed.

Lemma swapped_css_libs_ccequivc {o} :
  forall {name} {name'} {lib lib' : @library o} {a b : @CTerm o},
    lib_nodup lib
    -> swapped_css_libs name name' lib lib'
    -> a ~=~(lib) b
    -> a ~=~(lib') b.
Proof.
  introv nodup swap ceq; spcast.
  allrw @cequivc_iff_approxc; repnd.
  unfold swapped_css_libs in *; repnd.
  dands; eapply swapped_css_approxc; eauto.
Qed.

Lemma swapped_css_libs_ccomputes_to_valc_ext {o} :
  forall {name} {name'} {lib lib' : @library o} {a b : @CTerm o},
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> a ===>(lib) b
    -> a ===>(lib') b.
Proof.
  introv nodup sat safe swap comp ext.

  applydup @swapped_css_libs_sym in swap as swap'.
  assert (lib_nodup lib') as nodup' by eauto 3 with slow.
  assert (sat_lib_cond lib') as sat' by eauto 3 with slow.
  assert (strong_safe_library lib') as safe' by eauto 3 with slow.
  pose proof (lib_extends_preserves_perm_libs nodup' sat' safe' ext swap') as q; repnd; spcast.

  pose proof (comp _ q0) as comp; simpl in *; exrepnd.
  unfold swapped_css_libs in *; repnd.
  apply swapped_css_sym in q1.
  eapply swapped_css_ccomputes_to_valc in comp1; eauto; eauto 3 with slow;
    [|assert (lib_nodup (swap_names name name' lib'0)) as nodup'' by eauto 3 with slow; tcsp].
  eapply swapped_css_ccequivc in comp0; eauto; eauto with slow;
    [|assert (lib_nodup (swap_names name name' lib'0)) as nodup'' by eauto 3 with slow; tcsp].
  exrepnd; spcast.
  exists c0; dands; spcast; tcsp; eauto 3 with slow.
  eapply respects_alphaeqc_cequivc; eauto.
Qed.

Lemma swapped_css_libs_ccomputes_to_valc_ext_swap_names {o} :
  forall {name} {name'} {lib lib' lib0 : @library o} {a b : @CTerm o},
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> lib_extends lib0 lib
    -> a ===>(lib0) b
    -> a ===>(swap_names name name' lib0) b.
Proof.
  introv nodup sat safe swap ext comp.
  eapply swapped_css_libs_ccomputes_to_valc_ext; try exact comp; eauto 3 with slow.
  eapply lib_extends_preserves_perm_libs; eauto.
Qed.
Hint Resolve swapped_css_libs_ccomputes_to_valc_ext_swap_names : slow.

Lemma swapped_css_libs_ccomputes_to_valc_ext_swap_names_rev {o} :
  forall {name} {name'} {lib lib' lib0 : @library o} {a b : @CTerm o},
    lib_nodup lib'
    -> sat_lib_cond lib'
    -> strong_safe_library lib'
    -> swapped_css_libs name name' lib lib'
    -> lib_extends lib0 lib
    -> a ===>(lib0) b
    -> a ===>(swap_names name name' lib0) b.
Proof.
  introv nodup sat safe swap ext comp.
  applydup @swapped_css_libs_sym in swap.
  eapply swapped_css_libs_ccomputes_to_valc_ext; try exact comp; eauto 3 with slow.
  eapply lib_extends_preserves_perm_libs; try exact swap; eauto 3 with slow.
Qed.
Hint Resolve swapped_css_libs_ccomputes_to_valc_ext_swap_names_rev : slow.

Lemma in_open_bar_swapped_css_libs_pres {o} :
  forall name name' (lib lib' : @library o)
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib')
         (F : library -> Prop)
         (G : library -> Prop),
    in_ext lib (fun lib'' => F lib'' -> G (swap_names name name' lib''))
    -> in_open_bar lib F
    -> in_open_bar lib' G.
Proof.
  introv nodup sat safe swap imp h.
  eapply (in_open_bar_comb2 _ (fun lib x => G lib)).
  { apply in_ext_ext_implies_in_open_bar_ext; introv xt; tcsp. }
  apply in_open_bar_implies_in_open_bar_ext in h.
  eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; simpl.
  introv xta xtb.
  apply imp; auto.
Qed.

Lemma swapped_css_libs_equality_of_int_bar {o} :
  forall name name' (lib lib' : @library o),
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> (equality_of_int_bar lib) <=2=> (equality_of_int_bar lib').
Proof.
  introv nodup sat safe swap; introv; split; intro h.
  { eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; simpl.
    clear h; introv ext h.
    unfold equality_of_int in *; exrepnd.
    exists k; dands; eauto 3 with slow. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; simpl; eauto 3 with slow.
    clear h; introv ext h.
    unfold equality_of_int in *; exrepnd.
    exists k; dands; eauto 3 with slow. }
Qed.

Lemma swapped_css_libs_equality_of_nat_bar {o} :
  forall name name' (lib lib' : @library o),
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> (equality_of_nat_bar lib) <=2=> (equality_of_nat_bar lib').
Proof.
  introv nodup sat safe swap; introv; split; intro h.
  { eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; simpl.
    clear h; introv ext h.
    unfold equality_of_nat in *; exrepnd.
    exists n; dands; eauto 3 with slow. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; simpl; eauto 3 with slow.
    clear h; introv ext h.
    unfold equality_of_nat in *; exrepnd.
    exists n; dands; eauto 3 with slow. }
Qed.

Lemma swapped_css_libs_equality_of_qnat_bar {o} :
  forall name name' (lib lib' : @library o),
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> (equality_of_qnat_bar lib) <=2=> (equality_of_qnat_bar lib').
Proof.
  introv nodup sat safe swap; introv; split; intro h.
  { eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv ext h.
    unfold equality_of_qnat in *; exrepnd.
    eapply swapped_css_libs_ccomputes_to_valc in h2; eauto;
      try eapply lib_extends_preserves_perm_libs; eauto; eauto 3 with slow; exrepnd.
    eapply swapped_css_libs_ccomputes_to_valc in h1; eauto;
      try eapply lib_extends_preserves_perm_libs; eauto; eauto 3 with slow; exrepnd.
    spcast.
    apply alphaeqc_mkc_nat_implies in h0; subst.
    apply alphaeqc_mkc_nat_implies in h3; subst.
    dands.
    { exists n0; spcast; auto. }
    { exists n; spcast; auto. } }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv ext h.
    unfold equality_of_qnat in *; exrepnd.
    eapply swapped_css_libs_ccomputes_to_valc in h2; eauto;
      try eapply lib_extends_preserves_perm_libs; try exact ext; eauto; eauto 3 with slow.
    eapply swapped_css_libs_ccomputes_to_valc in h1; eauto;
      try eapply lib_extends_preserves_perm_libs; try exact ext; eauto; eauto 3 with slow.
    exrepnd; spcast.
    apply alphaeqc_mkc_nat_implies in h0; subst.
    apply alphaeqc_mkc_nat_implies in h3; subst.
    dands.
    { exists n0; spcast; auto. }
    { exists n; spcast; auto. } }
Qed.

Lemma swapped_css_libs_equality_of_csname_bar {o} :
  forall name name' (lib lib' : @library o) n,
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> (equality_of_csname_bar lib n) <=2=> (equality_of_csname_bar lib' n).
Proof.
  introv nodup sat safe swap; introv; split; intro h.
  { eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv ext h.
    unfold equality_of_csname in *; exrepnd.
    exists name0; dands; tcsp; eauto 3 with slow. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv ext h.
    unfold equality_of_csname in *; exrepnd.
    exists name0; dands; tcsp; eauto 3 with slow. }
Qed.

Lemma swapped_css_libs_equality_of_atom_bar {o} :
  forall name name' (lib lib' : @library o),
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> (equality_of_atom_bar lib) <=2=> (equality_of_atom_bar lib').
Proof.
  introv nodup sat safe swap; introv; split; intro h.
  { eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv ext h.
    unfold equality_of_atom in *; exrepnd.
    exists s; dands; tcsp; eauto 3 with slow. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv ext h.
    unfold equality_of_atom in *; exrepnd.
    exists s; dands; tcsp; eauto 3 with slow. }
Qed.

Lemma swapped_css_libs_equality_of_uatom_bar {o} :
  forall name name' (lib lib' : @library o),
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> (equality_of_uatom_bar lib) <=2=> (equality_of_uatom_bar lib').
Proof.
  introv nodup sat safe swap; introv; split; intro h.
  { eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv ext h.
    unfold equality_of_uatom in *; exrepnd.
    exists u; dands; tcsp; eauto 3 with slow. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv ext h.
    unfold equality_of_uatom in *; exrepnd.
    exists u; dands; tcsp; eauto 3 with slow. }
Qed.

Lemma swapped_css_libs_equality_of_base_bar {o} :
  forall name name' (lib lib' : @library o),
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> (per_base_eq lib) <=2=> (per_base_eq lib').
Proof.
  introv nodup sat safe swap; introv; split; intro h.
  { eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv ext h.
    eapply swapped_css_libs_ccequivc; try exact h; eauto 3 with slow.
    eapply lib_extends_preserves_perm_libs; eauto. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv ext h.
    eapply swapped_css_libs_ccequivc; try exact h; eauto 3 with slow.
    eapply lib_extends_preserves_perm_libs; try exact swap'; eauto 3 with slow. }
Qed.

Lemma swapped_css_libs_preserves_in_ext {o} :
  forall name name' (lib lib' : @library o) (F G : library -> Prop),
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> in_ext lib (fun lib'' => F lib'' -> G (swap_names name name' lib''))
    -> in_ext lib F
    -> in_ext lib' G.
Proof.
  introv nodup sat safe swap imp h ext.

  applydup @swapped_css_libs_sym in swap as swap'.
  assert (lib_nodup lib') as nodup' by eauto 3 with slow.
  assert (sat_lib_cond lib') as sat' by eauto 3 with slow.
  assert (strong_safe_library lib') as safe' by eauto 3 with slow.
  pose proof (lib_extends_preserves_perm_libs nodup' sat' safe' ext swap') as q; repnd; spcast.

  pose proof (imp (swap_names name name' lib'0) q0) as imp; simpl in imp.
  rewrite swap_names_twice in imp; eauto 3 with slow.
Qed.

Lemma swapped_css_libs_preserves_in_ext_ext {o} :
  forall name name' (lib lib' : @library o)
         (F : forall lib'' (x : lib_extends lib'' lib), Prop)
         (G : forall lib'' (x : lib_extends lib'' lib'), Prop),
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> in_ext_ext lib (fun lib'' (x : lib_extends lib'' lib) =>
                         forall (y : lib_extends (swap_names name name' lib'') lib'),
                           F lib'' x -> G (swap_names name name' lib'') y)
    -> in_ext_ext lib F
    -> in_ext_ext lib' G.
Proof.
  introv nodup sat safe swap imp h; introv.

  applydup @swapped_css_libs_sym in swap as swap'.
  assert (lib_nodup lib') as nodup' by eauto 3 with slow.
  assert (sat_lib_cond lib') as sat' by eauto 3 with slow.
  assert (strong_safe_library lib') as safe' by eauto 3 with slow.
  pose proof (lib_extends_preserves_perm_libs nodup' sat' safe' e swap') as q; repnd; spcast.

  pose proof (imp (swap_names name name' lib'0) q0) as imp; simpl in imp.
  rewrite swap_names_twice in imp; eauto 3 with slow.
Qed.

Lemma implies_lib_nodup_swap_names {o} :
  forall name name' (lib lib1 lib2 : @library o),
    lib_nodup lib1
    -> sat_lib_cond lib1
    -> strong_safe_library lib1
    -> swapped_css_libs name name' lib1 lib2
    -> lib_extends lib lib1
    -> lib_nodup (swap_names name name' lib).
Proof.
  introv nodup sat safe swap ext.
  eapply lib_extends_preserves_perm_libs in ext; eauto; repnd.
  eauto 3 with slow.
Qed.
Hint Resolve implies_lib_nodup_swap_names : slow.

Lemma ccapproxc_swap_names_iff {o} :
  forall (lib1 lib2 : @library o) name name' (lib : @library o) a b,
    lib_nodup lib1
    -> sat_lib_cond lib1
    -> strong_safe_library lib1
    -> swapped_css_libs name name' lib1 lib2
    -> lib_extends lib lib1
    -> ((a ~<~(swap_names name name' lib) b)
          <=> (a ~<~(lib) b)).
Proof.
  introv nodup sat safe swap ext; split; intro h.

  { eapply swapped_css_libs_capproxc; try exact h; eauto 3 with slow.
    apply swapped_css_libs_sym.
    eapply lib_extends_preserves_perm_libs; try exact ext; eauto. }

  { eapply swapped_css_libs_capproxc; try exact h; eauto 3 with slow.
    eapply lib_extends_preserves_perm_libs; try exact ext; eauto. }
Qed.

Lemma ccequivc_swap_names_iff {o} :
  forall (lib1 lib2 : @library o) name name' (lib : @library o) a b,
    lib_nodup lib1
    -> sat_lib_cond lib1
    -> strong_safe_library lib1
    -> swapped_css_libs name name' lib1 lib2
    -> lib_extends lib lib1
    -> ((a ~=~(swap_names name name' lib) b)
          <=> (a ~=~(lib) b)).
Proof.
  introv nodup sat safe swap ext; split; intro h.

  { eapply swapped_css_libs_ccequivc; try exact h; eauto 3 with slow.
    apply swapped_css_libs_sym.
    eapply lib_extends_preserves_perm_libs; try exact ext; eauto. }

  { eapply swapped_css_libs_ccequivc; try exact h; eauto 3 with slow.
    eapply lib_extends_preserves_perm_libs; try exact ext; eauto. }
Qed.

Lemma swapped_css_libs_equality_of_approx_bar {o} :
  forall name name' (lib lib' : @library o) a b,
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> (per_approx_eq_bar lib a b) <=2=> (per_approx_eq_bar lib' a b).
Proof.
  introv nodup sat safe swap; introv; split; intro h.
  { eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv ext h.
    unfold per_approx_eq in *; exrepnd.
    dands; tcsp; eauto 3 with slow.
    eapply swapped_css_libs_capproxc; try exact h; eauto 3 with slow.
    eapply lib_extends_preserves_perm_libs; eauto. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv ext h.
    unfold per_approx_eq in *; exrepnd.
    dands; tcsp; eauto 3 with slow.
    eapply swapped_css_libs_capproxc; try exact h; eauto 3 with slow.
    eapply lib_extends_preserves_perm_libs; try exact swap'; eauto 3 with slow. }
Qed.

Lemma swapped_css_libs_equality_of_cequiv_bar {o} :
  forall name name' (lib lib' : @library o) a b,
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> (per_cequiv_eq_bar lib a b) <=2=> (per_cequiv_eq_bar lib' a b).
Proof.
  introv nodup sat safe swap; introv; split; intro h.
  { eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv ext h.
    unfold per_cequiv_eq in *; exrepnd.
    dands; tcsp; eauto 3 with slow.
    eapply swapped_css_libs_ccequivc; try exact h; eauto 3 with slow.
    eapply lib_extends_preserves_perm_libs; eauto. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv ext h.
    unfold per_cequiv_eq in *; exrepnd.
    dands; tcsp; eauto 3 with slow.
    eapply swapped_css_libs_ccequivc; try exact h; eauto 3 with slow.
    eapply lib_extends_preserves_perm_libs; try exact swap'; eauto 3 with slow. }
Qed.

Lemma implies_ccequivc_ext_swap_names {o} :
  forall name name' (lib lib1 lib2 : @library o) (a b : @CTerm o),
    lib_nodup lib1
    -> strong_safe_library lib1
    -> sat_lib_cond lib1
    -> lib_extends lib lib1
    -> swapped_css_libs name name' lib1 lib2
    -> ccequivc_ext lib a b
    -> ccequivc_ext (swap_names name name' lib) a b.
Proof.
  introv nodup safe sat ext swap ceq.
  eapply swapped_css_libs_preserves_in_ext; try exact ceq; eauto; eauto 3 with slow.
  { eapply lib_extends_preserves_perm_libs; try exact swap; eauto 3 with slow. }
  clear ceq; introv xt ceq.
  eapply swapped_css_libs_ccequivc; try exact ceq; eauto 3 with slow.
  eapply lib_extends_preserves_perm_libs; try exact swap; eauto 3 with slow.
Qed.
Hint Resolve implies_ccequivc_ext_swap_names : slow.

Lemma implies_eqorceq_ext_per_lib_per {o} :
  forall name name' (lib lib' : @library o) eqa a b
         (nodup : lib_nodup lib)
         (safe  : strong_safe_library lib)
         (sat   : sat_lib_cond lib)
         (swap  : swapped_css_libs name name' lib lib'),
    eqorceq_ext lib eqa a b
    -> eqorceq_ext lib' (perm_lib_per sat safe nodup swap eqa) a b.
Proof.
  introv h; unfold eqorceq_ext in *.
  eapply swapped_css_libs_preserves_in_ext_ext; try exact h; eauto.
  clear h; introv h; simpl in *.
  unfold eqorceq in *; repndors;[left|right]; eauto 3 with slow.
  remember (proj1 (lib_extends_preserves_perm_libs
              (swapped_css_libs_preserves_lib_nodup swap nodup)
              (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
              (swapped_css_libs_preserves_strong_safe_library swap safe) y
              (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
  revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
  eapply lib_per_cond; eauto.
Qed.
Hint Resolve implies_eqorceq_ext_per_lib_per : slow.

Lemma swapped_css_libs_equality_of_eq_bar {o} :
  forall name name' (lib lib' : @library o) a b eqa
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib'),
    (eq_per_eq_bar lib a b eqa) <=2=> (eq_per_eq_bar lib' a b (perm_lib_per sat safe nodup swap eqa)).
Proof.
  introv; introv; split; intro h.
  { eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv h.
    unfold eq_per_eq in *; exrepnd.
    dands; tcsp; eauto 3 with slow.
    simpl.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) y
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
    eapply lib_per_cond; eauto. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv h.
    unfold eq_per_eq in *; exrepnd.
    dands; tcsp; eauto 3 with slow.
    simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) e
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    eapply lib_per_cond; eauto. }
Qed.

Lemma swapped_css_libs_equality_of_qtime_bar {o} :
  forall name name' (lib lib' : @library o) eqa
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib'),
    (per_qtime_eq_bar lib eqa) <=2=> (per_qtime_eq_bar lib' (perm_lib_per sat safe nodup swap eqa)).
Proof.
  introv; introv; split; intro h.
  { eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv h.
    unfold per_qtime_eq in *; exrepnd.
    dands; tcsp; eauto 3 with slow.
    exists x y0; dands; eauto 3 with slow.
    { eapply swapped_css_libs_ccequivc; try exact h0; eauto 3 with slow.
      eapply lib_extends_preserves_perm_libs; try exact swap; eauto 3 with slow. }
    { eapply swapped_css_libs_ccequivc; try exact h2; eauto 3 with slow.
      eapply lib_extends_preserves_perm_libs; try exact swap; eauto 3 with slow. }
    simpl.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) y
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
    eapply lib_per_cond; eauto. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv h.
    unfold per_qtime_eq in *; exrepnd.
    exists x y0; dands; eauto 3 with slow.
    { eapply swapped_css_libs_ccequivc; try exact h0; eauto 3 with slow.
      eapply lib_extends_preserves_perm_libs; try exact swap'; eauto 3 with slow. }
    { eapply swapped_css_libs_ccequivc; try exact h2; eauto 3 with slow.
      eapply lib_extends_preserves_perm_libs; try exact swap'; eauto 3 with slow. }
    { eapply implies_ccequivc_ext_swap_names; try exact e; eauto; eauto 3 with slow. }
    simpl in *.
    remember (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) e
                (swapped_css_libs_sym swap)) as w; clear Heqw; repnd.
    eapply lib_per_cond; eauto. }
Qed.

Definition perm_lib_per_fam {o} {name} {name'} {lib : library} {lib'}
           (sat   : sat_lib_cond lib)
           (safe  : strong_safe_library lib)
           (nodup : lib_nodup lib)
           (swap  : swapped_css_libs name name' lib lib')
           {eqa   : lib-per(lib,o)}
           (eqb   : lib-per-fam(lib,eqa)) : lib-per-fam(lib',perm_lib_per sat safe nodup swap eqa).
Proof.
  exists (fun lib'' (x : lib_extends lib'' lib')
              a a' (p : perm_lib_per sat safe nodup swap eqa lib'' x a a') =>
            eqb _ (proj1 (lib_extends_preserves_perm_libs
                            (swapped_css_libs_preserves_lib_nodup swap nodup)
                            (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                            (swapped_css_libs_preserves_strong_safe_library swap safe)
                            x
                            (swapped_css_libs_sym swap)))
                a a' p).
  introv.
  eapply lib_per_fam_cond.
Defined.

Lemma swapped_css_libs_equality_of_func_bar {o} :
  forall name name' (lib lib' : @library o) eqa eqb
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib'),
    (per_func_ext_eq lib eqa eqb) <=2=> (per_func_ext_eq lib' (perm_lib_per sat safe nodup swap eqa)(perm_lib_per_fam sat safe nodup swap eqb)).
Proof.
  introv; introv; split; intro h.
  { eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv h.
    unfold per_func_eq in *; introv; simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) y
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    revert dependent w; rewrite swap_names_twice; eauto 3 with slow; introv.
    assert (eqa lib'0 e a a') as e1 by (eapply lib_per_cond; eauto).
    pose proof (h _ _ e1) as h; eapply lib_per_fam_cond; eauto. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv h.
    unfold per_func_eq in *; introv; simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) e
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    assert (eqa (swap_names name name' lib'0) w a a') as e1 by (eapply lib_per_cond; eauto).
    pose proof (h _ _ e1) as h; eapply lib_per_fam_cond; eauto. }
Qed.

Lemma swapped_css_libs_equality_of_union_bar {o} :
  forall name name' (lib lib' : @library o) eqa eqb
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib'),
    (per_union_eq_bar lib eqa eqb) <=2=> (per_union_eq_bar lib' (perm_lib_per sat safe nodup swap eqa) (perm_lib_per sat safe nodup swap eqb)).
Proof.
  introv; introv; split; intro h.
  { eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv h.
    unfold per_union_eq in *; introv; simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) y
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    revert dependent w; rewrite swap_names_twice; eauto 3 with slow; introv.
    repndors;[left|right]; unfold per_union_eq_L, per_union_eq_R in *; exrepnd;
      exists x y0; dands; eauto 3 with slow; eapply lib_per_cond; eauto. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv h.
    unfold per_union_eq in *; introv; simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) e
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    repndors;[left|right]; unfold per_union_eq_L, per_union_eq_R in *; exrepnd;
      exists x y0; dands; eauto 3 with slow; eapply lib_per_cond; eauto. }
Qed.

Lemma swapped_css_libs_equality_of_set_bar {o} :
  forall name name' (lib lib' : @library o) eqa eqb
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib'),
    (per_set_eq_bar lib eqa eqb) <=2=> (per_set_eq_bar lib' (perm_lib_per sat safe nodup swap eqa)(perm_lib_per_fam sat safe nodup swap eqb)).
Proof.
  introv; introv; split; intro h.
  { eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv h.
    unfold per_set_eq in *; exrepnd; simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) y
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    revert dependent w; rewrite swap_names_twice; eauto 3 with slow; introv.
    assert (eqa lib'0 w t1 t2) as e1 by (eapply lib_per_cond; eauto).
    exists e1.
    eapply eq_term_equals_preserves_inhabited; try exact h0; apply lib_per_fam_cond. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv h.
    unfold per_set_eq in *; exrepnd; simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) e
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    assert (eqa (swap_names name name' lib'0) y t1 t2) as e1 by (eapply lib_per_cond; eauto).
    exists e1.
    eapply eq_term_equals_preserves_inhabited; try exact h0; apply lib_per_fam_cond. }
Qed.

Lemma swapped_css_libs_equality_of_product_bar {o} :
  forall name name' (lib lib' : @library o) eqa eqb
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib'),
    (per_product_eq_bar lib eqa eqb) <=2=> (per_product_eq_bar lib' (perm_lib_per sat safe nodup swap eqa)(perm_lib_per_fam sat safe nodup swap eqb)).
Proof.
  introv; introv; split; intro h.
  { eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv h.
    unfold per_product_eq in *; exrepnd; simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) y
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    revert dependent w; rewrite swap_names_twice; eauto 3 with slow; introv.
    assert (eqa lib'0 w a a') as e1 by (eapply lib_per_cond; eauto).
    exists a a' b b' e1; dands; eauto 3 with slow.
    eapply lib_per_fam_cond; eauto. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv h.
    unfold per_product_eq in *; exrepnd; simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) e
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    assert (eqa (swap_names name name' lib'0) y a a') as e1 by (eapply lib_per_cond; eauto).
    exists a a' b b' e1; dands; eauto 3 with slow.
    eapply lib_per_fam_cond; eauto. }
Qed.

Lemma swapped_css_libs_ccequivc_ext {o} :
  forall {name name'} {lib lib' : @library o} {a b : @CTerm o},
    lib_nodup lib
    -> sat_lib_cond lib
    -> strong_safe_library lib
    -> swapped_css_libs name name' lib lib'
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib' a b.
Proof.
  introv nodup sat safe swap ceq ext.
  applydup @swapped_css_libs_sym in swap as swap'.
  eapply lib_extends_preserves_perm_libs in ext; eauto; eauto 3 with slow; repnd.
  pose proof (ceq _ ext0) as ceq.
  eapply swapped_css_libs_ccequivc; try exact ceq; eauto 3 with slow.
  apply swapped_css_libs_sym; eauto.
Qed.

Lemma swapped_css_libs_equality_of_ffdefs_bar {o} :
  forall name name' (lib lib' : @library o) eqa f
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib'),
    (per_ffdefs_eq_bar lib eqa f) <=2=> (per_ffdefs_eq_bar lib' (perm_lib_per sat safe nodup swap eqa) f).
Proof.
  introv; introv; split; intro h.
  { eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv h.
    unfold per_ffdefs_eq in *; exrepnd.
    dands; tcsp; eauto 3 with slow; simpl in *.
    eapply ex_nodefsc_change_per; try exact h.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) y
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
    eapply lib_per_cond; eauto. }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv h.
    unfold per_ffdefs_eq in *; exrepnd.
    dands; eauto 3 with slow; simpl in *.
    eapply ex_nodefsc_change_per; try exact h.
    eapply lib_per_cond; eauto. }
Qed.

Lemma swapped_css_libs_equality_of_image_bar {o} :
  forall name name' (lib lib' : @library o) eqa f
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib'),
    (per_image_eq_bar lib eqa f) <=2=> (per_image_eq_bar lib' (perm_lib_per sat safe nodup swap eqa) f).
Proof.
  introv; introv; split; intro h.
  { eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto.
    clear h; introv h.
    simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) y
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
    induction h as [|? ? ? ? ea eb ec]; eauto.
    { eapply image_eq_cl; eauto. }
    eapply image_eq_eq.
    { eapply lib_per_cond; eauto. }
    { eapply swapped_css_libs_ccequivc_ext; try exact eb; eauto 3 with slow.
      eapply lib_extends_preserves_perm_libs; try exact ext; eauto. }
    { eapply swapped_css_libs_ccequivc_ext; try exact ec; eauto 3 with slow.
      eapply lib_extends_preserves_perm_libs; try exact ext; eauto. } }
  { dup swap as swap'; apply swapped_css_libs_sym in swap'.
    eapply in_open_bar_ext_swapped_css_libs_pres; try exact h; eauto; eauto 3 with slow.
    clear h; introv h; simpl in *.
    remember (proj1 (lib_extends_preserves_perm_libs
                (swapped_css_libs_preserves_lib_nodup swap nodup)
                (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                (swapped_css_libs_preserves_strong_safe_library swap safe) e
                (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    induction h as [|? ? ? ? ea eb ec]; eauto.
    { eapply image_eq_cl; eauto. }
    eapply image_eq_eq.
    { eapply lib_per_cond; eauto. }
    { eapply swapped_css_libs_ccequivc_ext; try exact eb; eauto 3 with slow.
      eapply lib_extends_preserves_perm_libs; try exact e; eauto; eauto 3 with slow. }
    { eapply swapped_css_libs_ccequivc_ext; try exact ec; eauto 3 with slow.
      eapply lib_extends_preserves_perm_libs; try exact e; eauto; eauto 3 with slow. } }
Qed.

Lemma close_swapped_css_libs {o} :
  forall name name' (lib lib' : library) (u : cts(o)) (t1 t2 : @CTerm o) e,
    local_ts u
    -> ts_implies_per_bar u
    -> type_system u
    -> defines_only_universes u
    -> type_monotone u
    -> lib_nodup lib
    -> strong_safe_library lib
    -> sat_lib_cond lib
    -> swapped_css_libs name name' lib lib'
    -> (forall (lib lib' : library) t1 t2 e,
           lib_nodup lib
           -> strong_safe_library lib
           -> sat_lib_cond lib
           -> swapped_css_libs name name' lib lib'
           -> u lib t1 t2 e
           -> u lib' t1 t2 e)
    -> close u lib t1 t2 e
    -> close u lib' t1 t2 e.
Proof.
  introv locts tsimp tysys dou mon; introv nodup safe sat swap imp cl.
  revert dependent lib'.
  close_cases (induction cl using @close_ind') Case; introv swap; subst.

  { Case "CL_init".
    apply CL_init.
    eapply imp; eauto.
  }

  { Case "CL_bar".
    apply CL_bar; clear per.
    exists (perm_lib_per sat safe nodup swap eqa); simpl; dands.

    { eapply in_open_bar_ext_swapped_css_libs_pres; try exact reca; try exact swap; auto; simpl.
      clear reca; introv reca; repeat (autodimp reca hyp); eauto 3 with slow.
      pose proof (reca (swap_names name name' lib'0)) as reca.
      autodimp reca hyp.
      { eapply lib_extends_preserves_perm_libs; eauto. }
      eapply close_type_extensionality; try exact reca; auto.
      remember (proj1 (lib_extends_preserves_perm_libs
                  (swapped_css_libs_preserves_lib_nodup swap nodup)
                  (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                  (swapped_css_libs_preserves_strong_safe_library swap safe) y
                  (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
      revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
      apply lib_per_cond. }

    { eapply eq_term_equals_trans;[exact eqiff|]; clear eqiff.
      apply eq_term_equals_per_bar_eq_per_lib_per. } }

  { Case "CL_int".
    apply CL_int.
    unfold per_int in *; repnd.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per0.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per1.
    dands; eauto 3 with slow.
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_int_bar; eauto. }

  { Case "CL_nat".
    apply CL_nat.
    unfold per_nat in *; repnd.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per0.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per1.
    dands; eauto 3 with slow.
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_nat_bar; eauto. }

  { Case "CL_qnat".
    apply CL_qnat.
    unfold per_qnat in *; repnd.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per0.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per1.
    dands; eauto 3 with slow.
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_qnat_bar; eauto. }

  { Case "CL_csname".
    apply CL_csname.
    unfold per_csname in *; exrepnd.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per1.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per2.
    exists n; dands; eauto 3 with slow.
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_csname_bar; eauto. }

  { Case "CL_atom".
    apply CL_atom.
    unfold per_atom in *; exrepnd.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per0.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per1.
    dands; eauto 3 with slow.
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_atom_bar; eauto. }

  { Case "CL_uatom".
    apply CL_uatom.
    unfold per_uatom in *; exrepnd.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per0.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per1.
    dands; eauto 3 with slow.
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_uatom_bar; eauto. }

  { Case "CL_base".
    apply CL_base.
    unfold per_base in *; exrepnd.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per0.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per1.
    dands; eauto 3 with slow.
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_base_bar; eauto. }

  { Case "CL_approx".
    apply CL_approx.
    unfold per_approx in *; exrepnd.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per0.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per2.
    exists a b c d; dands; auto.
    { eapply swapped_css_libs_preserves_in_ext; try exact per3; eauto.
      clear per3; introv xt h.
      pose proof (ccapproxc_swap_names_iff lib lib' name name' lib'0 a b) as q.
      repeat (autodimp q hyp); simpl in *; rw q; clear q.
      pose proof (ccapproxc_swap_names_iff lib lib' name name' lib'0 c d) as q.
      repeat (autodimp q hyp); simpl in *; rw q; clear q; auto. }
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_approx_bar; eauto. }

  { Case "CL_cequiv".
    apply CL_cequiv.
    unfold per_cequiv in *; exrepnd.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per0.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in per2.
    exists a b c d; dands; auto.
    { eapply swapped_css_libs_preserves_in_ext; try exact per3; eauto.
      clear per3; introv xt h.
      pose proof (ccequivc_swap_names_iff lib lib' name name' lib'0 a b) as q.
      repeat (autodimp q hyp); simpl in *; rw q; clear q.
      pose proof (ccequivc_swap_names_iff lib lib' name name' lib'0 c d) as q.
      repeat (autodimp q hyp); simpl in *; rw q; clear q; auto. }
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_cequiv_bar; eauto. }

  { Case "CL_eq".
    apply CL_eq.
    clear per.
    unfold per_eq in *; exrepnd.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c1.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c2.
    exists A B a1 a2 b1 b2 (perm_lib_per sat safe nodup swap eqa); dands; auto; eauto 3 with slow.
    { eapply swapped_css_libs_preserves_in_ext_ext; try exact reca; eauto.
      clear reca; introv reca; simpl in *.
      repeat (autodimp reca hyp); eauto 3 with slow.
      pose proof (reca (swap_names name name' lib'0)) as reca.
      autodimp reca hyp.
      { eapply lib_extends_preserves_perm_libs; eauto. }
      eapply close_type_extensionality; try exact reca; auto.
      remember (proj1 (lib_extends_preserves_perm_libs
                  (swapped_css_libs_preserves_lib_nodup swap nodup)
                  (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                  (swapped_css_libs_preserves_strong_safe_library swap safe) y
                  (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
      revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
      apply lib_per_cond. }
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_eq_bar; eauto. }

  { Case "CL_qtime".
    apply CL_qtime.
    clear per.
    unfold per_qtime in *.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c1.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c2.
    exists (perm_lib_per sat safe nodup swap eqa) A B; dands; auto; eauto 3 with slow.
    { eapply swapped_css_libs_preserves_in_ext_ext; try exact reca; eauto.
      clear reca; introv reca; simpl in *.
      repeat (autodimp reca hyp); eauto 3 with slow.
      pose proof (reca (swap_names name name' lib'0)) as reca.
      autodimp reca hyp.
      { eapply lib_extends_preserves_perm_libs; eauto. }
      eapply close_type_extensionality; try exact reca; auto.
      remember (proj1 (lib_extends_preserves_perm_libs
                  (swapped_css_libs_preserves_lib_nodup swap nodup)
                  (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                  (swapped_css_libs_preserves_strong_safe_library swap safe) y
                  (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
      revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
      apply lib_per_cond. }
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_qtime_bar; eauto. }

  { Case "CL_func".
    apply CL_func.
    clear per.
    unfold per_func_ext in *.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c1.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c2.

    exists (perm_lib_per sat safe nodup swap eqa) (perm_lib_per_fam sat safe nodup swap eqb); dands; auto; eauto 3 with slow.
    { unfold type_family_ext.
      exists A A' v v' B B'; dands; eauto 3 with slow.
      { eapply swapped_css_libs_preserves_in_ext_ext; try exact reca; eauto.
        clear reca; introv reca; simpl in *.
        repeat (autodimp reca hyp); eauto 3 with slow.
        pose proof (reca (swap_names name name' lib'0)) as reca.
        autodimp reca hyp.
        { eapply lib_extends_preserves_perm_libs; eauto. }
        eapply close_type_extensionality; try exact reca; auto.
        remember (proj1 (lib_extends_preserves_perm_libs
                    (swapped_css_libs_preserves_lib_nodup swap nodup)
                    (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                    (swapped_css_libs_preserves_strong_safe_library swap safe) y
                    (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
        revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
        apply lib_per_cond. }
      { eapply swapped_css_libs_preserves_in_ext_ext; try exact recb; eauto.
        clear recb; introv recb; simpl in *; introv.
        remember (proj1 (lib_extends_preserves_perm_libs
                    (swapped_css_libs_preserves_lib_nodup swap nodup)
                    (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                    (swapped_css_libs_preserves_strong_safe_library swap safe) y
                    (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
        revert dependent w; rewrite swap_names_twice; introv; eauto 3 with slow.
        assert (eqa lib'0 e a a') as e1 by (eapply lib_per_cond; eauto).
        pose proof (recb a a' e1) as recb.
        repeat (autodimp recb hyp); eauto 3 with slow.
        pose proof (recb (swap_names name name' lib'0)) as recb.
        autodimp recb hyp.
        { eapply lib_extends_preserves_perm_libs; eauto. }
        eapply close_type_extensionality; try exact recb; auto; eapply lib_per_fam_cond. } }
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_func_bar; eauto. }

  { Case "CL_union".
    apply CL_union.
    clear per.
    unfold per_union in *.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c1.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c2.

    exists (perm_lib_per sat safe nodup swap eqa) (perm_lib_per sat safe nodup swap eqb) A A' B B'; dands; auto; eauto 3 with slow.
    { eapply swapped_css_libs_preserves_in_ext_ext; try exact reca; eauto.
      clear reca; introv reca; simpl in *.
      repeat (autodimp reca hyp); eauto 3 with slow.
      pose proof (reca (swap_names name name' lib'0)) as reca.
      autodimp reca hyp.
      { eapply lib_extends_preserves_perm_libs; eauto. }
      eapply close_type_extensionality; try exact reca; auto.
      remember (proj1 (lib_extends_preserves_perm_libs
                         (swapped_css_libs_preserves_lib_nodup swap nodup)
                         (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                         (swapped_css_libs_preserves_strong_safe_library swap safe) y
                         (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
      revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
      apply lib_per_cond. }
    { eapply swapped_css_libs_preserves_in_ext_ext; try exact recb; eauto.
      clear recb; introv recb; simpl in *.
      repeat (autodimp recb hyp); eauto 3 with slow.
      pose proof (recb (swap_names name name' lib'0)) as recb.
      autodimp recb hyp.
      { eapply lib_extends_preserves_perm_libs; eauto. }
      eapply close_type_extensionality; try exact recb; auto.
      remember (proj1 (lib_extends_preserves_perm_libs
                         (swapped_css_libs_preserves_lib_nodup swap nodup)
                         (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                         (swapped_css_libs_preserves_strong_safe_library swap safe) y
                         (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
      revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
      apply lib_per_cond. }
  eapply eq_term_equals_trans;[eauto|].
  eapply swapped_css_libs_equality_of_union_bar; eauto. }

  { Case "CL_image".
    apply CL_image.
    clear per.
    unfold per_image in *.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c1.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c2.
    exists (perm_lib_per sat safe nodup swap eqa) A A' f f'; dands; auto; eauto 3 with slow.
    { eapply swapped_css_libs_preserves_in_ext_ext; try exact reca; eauto.
      clear reca; introv reca; simpl in *.
      repeat (autodimp reca hyp); eauto 3 with slow.
      pose proof (reca (swap_names name name' lib'0)) as reca.
      autodimp reca hyp.
      { eapply lib_extends_preserves_perm_libs; eauto. }
      eapply close_type_extensionality; try exact reca; auto.
      remember (proj1 (lib_extends_preserves_perm_libs
                  (swapped_css_libs_preserves_lib_nodup swap nodup)
                  (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                  (swapped_css_libs_preserves_strong_safe_library swap safe) y
                  (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
      revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
      apply lib_per_cond. }
    { eapply swapped_css_libs_ccequivc_ext; eauto. }
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_image_bar; eauto. }

  { Case "CL_ffdefs".
    apply CL_ffdefs.
    clear per.
    unfold per_ffdefs in *.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c1.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c2.
    exists A1 A2 x1 x2 (perm_lib_per sat safe nodup swap eqa); dands; auto; eauto 3 with slow.
    { eapply swapped_css_libs_preserves_in_ext_ext; try exact reca; eauto.
      clear reca; introv reca; simpl in *.
      repeat (autodimp reca hyp); eauto 3 with slow.
      pose proof (reca (swap_names name name' lib'0)) as reca.
      autodimp reca hyp.
      { eapply lib_extends_preserves_perm_libs; eauto. }
      eapply close_type_extensionality; try exact reca; auto.
      remember (proj1 (lib_extends_preserves_perm_libs
                  (swapped_css_libs_preserves_lib_nodup swap nodup)
                  (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                  (swapped_css_libs_preserves_strong_safe_library swap safe) y
                  (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
      revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
      apply lib_per_cond. }
    { eapply swapped_css_libs_preserves_in_ext_ext; try exact ex; eauto.
      clear ex; introv ex; simpl in *.
      remember (proj1 (lib_extends_preserves_perm_libs
                  (swapped_css_libs_preserves_lib_nodup swap nodup)
                  (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                  (swapped_css_libs_preserves_strong_safe_library swap safe) y
                  (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
      revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
      eapply lib_per_cond; eauto. }
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_ffdefs_bar; eauto. }

  { Case "CL_set".
    apply CL_set.
    clear per.
    unfold per_set in *.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c1.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c2.

    exists (perm_lib_per sat safe nodup swap eqa) (perm_lib_per_fam sat safe nodup swap eqb); dands; auto; eauto 3 with slow.
    { unfold type_family_ext.
      exists A A' v v' B B'; dands; eauto 3 with slow.
      { eapply swapped_css_libs_preserves_in_ext_ext; try exact reca; eauto.
        clear reca; introv reca; simpl in *.
        repeat (autodimp reca hyp); eauto 3 with slow.
        pose proof (reca (swap_names name name' lib'0)) as reca.
        autodimp reca hyp.
        { eapply lib_extends_preserves_perm_libs; eauto. }
        eapply close_type_extensionality; try exact reca; auto.
        remember (proj1 (lib_extends_preserves_perm_libs
                    (swapped_css_libs_preserves_lib_nodup swap nodup)
                    (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                    (swapped_css_libs_preserves_strong_safe_library swap safe) y
                    (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
        revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
        apply lib_per_cond. }
      { eapply swapped_css_libs_preserves_in_ext_ext; try exact recb; eauto.
        clear recb; introv recb; simpl in *; introv.
        remember (proj1 (lib_extends_preserves_perm_libs
                    (swapped_css_libs_preserves_lib_nodup swap nodup)
                    (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                    (swapped_css_libs_preserves_strong_safe_library swap safe) y
                    (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
        revert dependent w; rewrite swap_names_twice; introv; eauto 3 with slow.
        assert (eqa lib'0 e a a') as e1 by (eapply lib_per_cond; eauto).
        pose proof (recb a a' e1) as recb.
        repeat (autodimp recb hyp); eauto 3 with slow.
        pose proof (recb (swap_names name name' lib'0)) as recb.
        autodimp recb hyp.
        { eapply lib_extends_preserves_perm_libs; eauto. }
        eapply close_type_extensionality; try exact recb; auto; eapply lib_per_fam_cond. } }
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_set_bar; eauto. }

  { Case "CL_product".
    apply CL_product.
    clear per.
    unfold per_product in *.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c1.
    apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in c2.

    exists (perm_lib_per sat safe nodup swap eqa) (perm_lib_per_fam sat safe nodup swap eqb); dands; auto; eauto 3 with slow.
    { unfold type_family_ext.
      exists A A' v v' B B'; dands; eauto 3 with slow.
      { eapply swapped_css_libs_preserves_in_ext_ext; try exact reca; eauto.
        clear reca; introv reca; simpl in *.
        repeat (autodimp reca hyp); eauto 3 with slow.
        pose proof (reca (swap_names name name' lib'0)) as reca.
        autodimp reca hyp.
        { eapply lib_extends_preserves_perm_libs; eauto. }
        eapply close_type_extensionality; try exact reca; auto.
        remember (proj1 (lib_extends_preserves_perm_libs
                    (swapped_css_libs_preserves_lib_nodup swap nodup)
                    (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                    (swapped_css_libs_preserves_strong_safe_library swap safe) y
                    (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
        revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
        apply lib_per_cond. }
      { eapply swapped_css_libs_preserves_in_ext_ext; try exact recb; eauto.
        clear recb; introv recb; simpl in *; introv.
        remember (proj1 (lib_extends_preserves_perm_libs
                    (swapped_css_libs_preserves_lib_nodup swap nodup)
                    (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                    (swapped_css_libs_preserves_strong_safe_library swap safe) y
                    (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
        revert dependent w; rewrite swap_names_twice; introv; eauto 3 with slow.
        assert (eqa lib'0 e a a') as e1 by (eapply lib_per_cond; eauto).
        pose proof (recb a a' e1) as recb.
        repeat (autodimp recb hyp); eauto 3 with slow.
        pose proof (recb (swap_names name name' lib'0)) as recb.
        autodimp recb hyp.
        { eapply lib_extends_preserves_perm_libs; eauto. }
        eapply close_type_extensionality; try exact recb; auto; eapply lib_per_fam_cond. } }
    eapply eq_term_equals_trans;[eauto|].
    eapply swapped_css_libs_equality_of_product_bar; eauto. }
Qed.

Lemma swapped_css_libs_univi_eq {o} :
  forall i name name' (lib lib' : @library o)
         (nodup : lib_nodup lib)
         (sat   : sat_lib_cond lib)
         (safe  : strong_safe_library lib)
         (swap  : swapped_css_libs name name' lib lib'),
    (forall (lib lib' : library) t1 t2 (e : per(o)),
        lib_nodup lib
        -> sat_lib_cond lib
        -> strong_safe_library lib
        -> swapped_css_libs name name' lib lib'
        -> univi i lib t1 t2 e
        -> univi i lib' t1 t2 e)
    -> ((univi_eq (univi_bar i) lib) <=2=> (univi_eq (univi_bar i) lib')).
Proof.
  introv nodup sat safe swap imp; split; intro h.

  { unfold univi_eq in *; exrepnd.
    exists eqa.
    eapply close_swapped_css_libs; try exact h0; eauto; eauto 3 with slow.
    clear dependent lib.
    clear dependent lib'.
    introv nodup safe sat swap u.
    unfold univi_bar, per_bar in *; exrepnd.
    exists (perm_lib_per sat safe nodup swap eqa0); simpl; dands.

    { eapply in_open_bar_ext_swapped_css_libs_pres; try exact u1; try exact swap; auto; simpl.
      clear u1; introv u1; repeat (autodimp u1 hyp); eauto 3 with slow.
      remember (proj1 (lib_extends_preserves_perm_libs
                  (swapped_css_libs_preserves_lib_nodup swap nodup)
                  (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                  (swapped_css_libs_preserves_strong_safe_library swap safe) y
                  (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
      revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
      eapply imp; try eapply lib_extends_preserves_perm_libs; eauto; eauto 3 with slow.
      eapply type_extensionality_univi; try exact u1; auto.
      apply lib_per_cond. }

    { eapply eq_term_equals_trans;[exact u0|]; clear u0.
      apply eq_term_equals_per_bar_eq_per_lib_per. } }

  { unfold univi_eq in *; exrepnd.
    exists eqa.
    eapply close_swapped_css_libs; try exact h0;
      try apply swapped_css_libs_sym; eauto; eauto with slow.
    clear dependent lib.
    clear dependent lib'.
    introv nodup safe sat swap u.
    unfold univi_bar, per_bar in *; exrepnd.
    exists (perm_lib_per sat safe nodup swap eqa0); simpl; dands.

    { eapply in_open_bar_ext_swapped_css_libs_pres; try exact u1; try exact swap; auto; simpl.
      clear u1; introv u1; repeat (autodimp u1 hyp); eauto 3 with slow.
      remember (proj1 (lib_extends_preserves_perm_libs
                  (swapped_css_libs_preserves_lib_nodup swap nodup)
                  (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                  (swapped_css_libs_preserves_strong_safe_library swap safe) y
                  (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
      revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
      eapply imp; try eapply lib_extends_preserves_perm_libs; eauto; eauto 3 with slow.
      eapply type_extensionality_univi; try exact u1; auto.
      apply lib_per_cond. }

    { eapply eq_term_equals_trans;[exact u0|]; clear u0.
      apply eq_term_equals_per_bar_eq_per_lib_per. } }
Qed.

Lemma univi_swapped_css_libs {o} :
  forall i name name' (lib lib' : @library o) (t1 t2 : @CTerm o) e,
    lib_nodup lib
    -> strong_safe_library lib
    -> sat_lib_cond lib
    -> swapped_css_libs name name' lib lib'
    -> univi i lib t1 t2 e
    -> univi i lib' t1 t2 e.
Proof.
  induction i; introv nodup safe sat swap u; simpl in *; tcsp; repndors; repnd; tcsp;
    try (complete (right; eauto)).
  apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in u0.
  apply (swapped_css_libs_ccomputes_to_valc_ext nodup sat safe swap) in u1.
  left; dands; eauto 3 with slow.
  eapply eq_term_equals_trans; eauto; simpl.
  eapply swapped_css_libs_univi_eq; eauto.
Qed.

Lemma univ_swapped_css_libs {o} :
  forall name name' (lib lib' : @library o) (t1 t2 : @CTerm o) e,
    lib_nodup lib
    -> strong_safe_library lib
    -> sat_lib_cond lib
    -> swapped_css_libs name name' lib lib'
    -> univ lib t1 t2 e
    -> univ lib' t1 t2 e.
Proof.
  introv nodup safe sat swap u.
  unfold univ in *.
  unfold per_bar in *; exrepnd.
  exists (perm_lib_per sat safe nodup swap eqa).
  dands.

  { eapply in_open_bar_ext_swapped_css_libs_pres; try exact u1; try exact swap; auto; simpl.
    clear u1; introv u1; repeat (autodimp u1 hyp); eauto 3 with slow.
    unfold univ_ex in *; exrepnd; exists i.
    remember (proj1 (lib_extends_preserves_perm_libs
                       (swapped_css_libs_preserves_lib_nodup swap nodup)
                       (swapped_css_libs_preserves_sat_lib_cond swap nodup sat)
                       (swapped_css_libs_preserves_strong_safe_library swap safe) y
                       (swapped_css_libs_sym swap))) as w; clear Heqw; repnd.
    revert w; rewrite swap_names_twice; eauto 3 with slow; introv.
    apply (type_extensionality_univi _ _ _ _ (eqa lib'0 e0)); try apply lib_per_cond.
    eapply univi_swapped_css_libs; try exact u2; eauto 3 with slow.
    eapply lib_extends_preserves_perm_libs; eauto; eauto 3 with slow. }

  { eapply eq_term_equals_trans;[exact u0|]; clear u0.
    apply eq_term_equals_per_bar_eq_per_lib_per. }
Qed.

Lemma nuprl_swapped_css_libs {o} :
  forall name name' (lib lib' : @library o) (t1 t2 : @CTerm o) e,
    lib_nodup lib
    -> strong_safe_library lib
    -> sat_lib_cond lib
    -> swapped_css_libs name name' lib lib'
    -> nuprl lib t1 t2 e
    -> nuprl lib' t1 t2 e.
Proof.
  introv nodup safe sat swap n.
  unfold nuprl in *.
  eapply close_swapped_css_libs; try exact n; eauto; eauto 3 with slow.
  clear dependent lib.
  clear dependent lib'.
  introv nodup safe sat swap u.
  eapply univ_swapped_css_libs; eauto.
Qed.

Lemma equality_swapped_css_libs {o} :
  forall name name' (lib lib' : @library o) (t1 t2 : @CTerm o) T,
    lib_nodup lib
    -> strong_safe_library lib
    -> sat_lib_cond lib
    -> swapped_css_libs name name' lib lib'
    -> equality lib t1 t2 T
    -> equality lib' t1 t2 T.
Proof.
  introv nodup safe sat swap e.
  unfold equality in *; exrepnd.
  exists eq; dands; auto.
  eapply nuprl_swapped_css_libs; eauto.
Qed.

Lemma member_swapped_css_libs {o} :
  forall name name' (lib lib' : @library o) (t T : @CTerm o),
    lib_nodup lib
    -> strong_safe_library lib
    -> sat_lib_cond lib
    -> swapped_css_libs name name' lib lib'
    -> member lib t T
    -> member lib' t T.
Proof.
  introv nodup safe sat swap m.
  unfold member in *; eapply equality_swapped_css_libs; eauto.
Qed.

Lemma strong_safe_library_swap_cs_plib {o} :
  forall sw (lib : @plibrary o),
    sane_swapping sw
    -> strong_safe_library lib
    -> strong_safe_library (swap_cs_plib sw lib).
Proof.
  introv sane safe i.
  apply in_swap_library_iff in i; exrepnd; subst.
  apply safe in i1; eauto 3 with slow.
Qed.
Hint Resolve strong_safe_library_swap_cs_plib : slow.

Lemma sat_lib_cond_swap_cs_lib {o} :
  forall sw (lib : @library o),
    sat_lib_cond lib
    -> sat_lib_cond (swap_cs_lib sw lib).
Proof.
  introv sat i.
  destruct lib as [lib cond]; simpl in *.
  apply entry_in_swap_library_implies in i; exrepnd; subst; simpl in *.
  autorewrite with slow in *.
  apply sat in i1; clear sat.
  unfold swap_cs_lib; simpl.
  destruct e0; simpl in *.

  { destruct entry as [vals restr]; simpl in *; repnd.
    autorewrite with slow; dands; auto.
    introv j; simpl in *.
    unfold swap_cs_choice_seq_vals in *.
    apply in_map_iff in j; exrepnd; subst; simpl.
    apply i0 in j1.
    destruct_cterms; simpl in *; autorewrite with slow; auto. }

  { rewrite <- swap_cs_term_soterm2nterm; autorewrite with slow; auto. }
Qed.
Hint Resolve sat_lib_cond_swap_cs_lib : slow.




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
  forall (lib : library)
         (A a b n x y : NVar) (i : nat) (H : @bhyps o)
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
         (nocs  : has_lib_cond_no_cs lib),
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
  move2ext ext.

  dands.

  { admit. }

  apply equality_in_function3.
  dands.

  { admit. }

  intros lib' ext A1 A2 eqA.
  move2ext ext.

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
  move2ext ext.

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

  unfold ex_nodefsc_eq in *; exrepnd.
  rename eqx1 into eqw.
  rename eqx0 into nodefs.

  move2ext ext.

  apply equality_in_fun.
  dands.

  { admit. }

  { admit. }

  intros lib' ext z1 z2 eqz.

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqa;[|eauto];[].
  eapply equality_monotone in eqx;[|eauto];[].
  eapply equality_monotone in eqw;[|eauto];[].

  move2ext ext.

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
  eapply tequality_monotone in teq;[|eauto];[].
  move2ext ext.

  apply inhabited_product.
  dands; eauto 3 with slow;[|].

  { admit. }

  exists (@mkc_pair
            _
            (mkc_nat (S (lib_depth lib)))
            (mkc_lam b (mkcv_lam _ x (mk_cv _ z1)))).

  apply in_ext_implies_all_in_ex_bar.
  introv ext.
  exists (@mkc_nat o (S (lib_depth lib))) (mkc_lam b (mkcv_lam _ x (mk_cv _ z1))).
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
                         (mkcv_natk2nat [b] (mk_cv [b] (mkc_nat (S (lib_depth lib1))))))
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
        introv xt1 eb.

      {
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
  assert (lib_extends lib'0 lib1) as ext' by eauto 3 with slow.
  move2ext xt.

  apply equality_in_csname_iff in ecs.
  unfold equality_of_csname_bar in ecs.

  apply equality_natk2nat_implies2 in eb0.
  apply all_in_ex_bar_member_implies_member.

  eapply all_in_ex_bar_modus_ponens2;[|exact eb0|exact ecs]; clear eb0 ecs; introv xt eb0 ecs.

  eapply member_monotone in eqA;[|exact xt];[].
  assert (lib_extends lib'0 lib1) as ext'' by eauto 3 with slow.
  move2ext xt.

  unfold equality_of_csname in ecs; exrepnd; spcast; GC.
  rename name0 into name'.

  rev_assert (member lib z1 (mkc_apply u (mkc_choice_seq name'))) mem.
  {
    pose proof (equality_in_mkc_csprop_implies_tequality lib u u b1 (mkc_choice_seq name') i) as teq.
    repeat (autodimp teq hyp); eauto 3 with slow.
    { apply equality_in_csname_iff.
      unfold equality_of_csname_bar.
      apply in_ext_implies_in_open_bar; introv xta.
      exists name'; dands; spcast; eauto 3 with slow. }
    eapply tequality_preserving_equality;[|apply tequality_sym;eauto]; auto.
  }

  assert (forall m,
             m <= lib_depth lib1
             ->
             {k : nat
             , ccomputes_to_valc_ext lib (mkc_apply (mkc_choice_seq name) (mkc_nat m)) (mkc_nat k)
             # ccomputes_to_valc_ext lib (mkc_apply (mkc_choice_seq name') (mkc_nat m)) (mkc_nat k)}) as imp.
  {
    introv h; pose proof (eb0 m) as eb0; autodimp eb0 hyp; try omega; exrepnd.
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


  (* === We might have to squash the application in the conclusion === *)

  (* === We have to show that because of [imp], [lib1] can be extended with [name']
         equivalent to [name] up to [lib_depth lib1] === *)

  destruct (choice_sequence_name_deq name' name) as [d|d];[subst;eauto 3 with slow|];[].

  (* We will have to restrict [compatible_choice_sequence_name] to disallow sequences for those: *)
  assert (is_nat_cs name) as isna by admit.
  assert (is_nat_cs name') as isnb by admit.

  pose proof (to_library_with_equal_cs name name' lib lib1) as q.
  repeat (autodimp q hyp);[].
  exrepnd.

  assert (strong_safe_library lib0) as safe' by eauto 3 with slow.
  assert (lib_nodup lib0) as nodup' by eauto 3 with slow.
  assert (sat_lib_cond lib0) as sat' by eauto 3 with slow.
  assert (has_lib_cond_no_cs lib0) as nocs' by eauto 3 with slow.

  (* WARNING *)
  clear tya0.
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

  (* For this we can add a swapping operator to the computation system *)

Qed.
