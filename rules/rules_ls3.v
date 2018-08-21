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

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqa;[|eauto];[].
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

  clear A2 a2 x2.

  eapply inhabited_type_bar_respects_alphaeqc;
    [apply alphaeqc_sym;apply substc_alphaeqcv;apply substc2_product;tcsp|];[].

  rewrite mkcv_product_substc; auto;[].
  autorewrite with slow.

  apply equality_in_csname in eqa.
  eapply all_in_ex_bar_modus_ponens1;[|exact eqa]; clear eqa; introv ext eqa.

  eapply equality_monotone in eqA;[|eauto];[].
  eapply equality_monotone in eqx;[|eauto];[].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  clear dependent lib.
  rename lib' into lib.
  rename safe' into safe.

  unfold equality_of_csname in eqa; exrepnd; GC; spcast.

  eapply member_respects_cequivc_type in eqx;
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

  apply inhabited_product.
  dands; eauto 3 with slow;[|].

  { admit. }

  exists (@mkc_pair _ (mkc_nat (cs_size lib name)) (mkc_lam b (mkcv_lam _ x (mk_cv _ x1)))).

  apply in_ext_implies_all_in_ex_bar.
  introv ext.
  exists (@mkc_nat o (cs_size lib name)) (mkc_lam b (mkcv_lam _ x (mk_cv _ x1))).
  dands; spcast; eauto 3 with slow;[].

  rewrite substc2_substc3_eq.
  rewrite substc3_2_substc_eq.

  (* TODO: assume that [A1] is free from definitions/choice sequences *)


Qed.
