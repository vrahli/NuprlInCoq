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


Require Export rules_choice2.



Definition ls_exists {o} (a n x : NVar) : @NTerm o :=
  mk_function
    (mk_csname 0)
    a
    (mk_function
       mk_tnat
       n
       (mk_exists
          mk_tnat
          x
          (mk_equality
             (mk_apply (mk_var a) (mk_var n))
             (mk_var x)
             mk_tnat))).

Definition ls_existsc {o} (a n x : NVar) : @CTerm o :=
  mkc_function
    (mkc_csname 0)
    a
    (mkcv_function
       _
       (mkcv_tnat _)
       n
       (mkcv_exists
          _
          (mkcv_tnat _)
          x
          (mkcv_equality
             _
             (mkcv_apply _ (mk_cv_app_l [x,n] _ (mkc_var a)) (mk_cv_app_l [x] _ (mk_cv_app_r [a] _ (mkc_var n))))
             (mk_cv_app_r [n,a] _ (mkc_var x))
             (mkcv_tnat _)))).

Definition ls_exists_extract {o} (a n : NVar) : @NTerm o :=
  mk_lam a (mk_lam n (mk_pair (mk_apply (mk_var a) (mk_var n)) mk_axiom)).

Definition ls_existsc_extract {o} (a n : NVar) : @CTerm o :=
  mkc_lam a (mkcv_lam [a] n (mkcv_pair _ (mkcv_apply _ (mk_cv_app_l [n] _ (mkc_var a)) (mk_cv_app_r [a] _ (mkc_var n))) (mkcv_ax _))).

Lemma lsubstc_ls_exists_eq {o} :
  forall a n x (w : @wf_term o (ls_exists a n x)) s c,
    lsubstc (ls_exists a n x) w s c = ls_existsc a n x.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls_exists_eq : slow.

Lemma lsubstc_ls_exists_extract_eq {o} :
  forall a n (w : @wf_term o (ls_exists_extract a n)) s c,
    lsubstc (ls_exists_extract a n) w s c = ls_existsc_extract a n.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls_exists_extract_eq : slow.

Lemma sub_find_nil {o} :
  forall a, @sub_find o [] a = None.
Proof.
  introv; simpl; auto.
Qed.
Hint Rewrite @sub_find_nil : slow.

Lemma sub_find_single_in {o} :
  forall a b, @sub_find o [(a,b)] a = Some b.
Proof.
  introv; simpl; boolvar; tcsp.
Qed.
Hint Rewrite @sub_find_single_in : slow.

Lemma sub_find_single_not_in {o} :
  forall a b c,
    a <> c
    -> @sub_find o [(a,b)] c = None.
Proof.
  introv d; simpl; boolvar; tcsp.
Qed.

Lemma subst_ls_exists_cond1 {o} :
  forall a n x (t : @CTerm o) (d1 : a <> n) (d2 : a <> x),
    alphaeqcv
      _
      (substcv
         [n] t a
         (mkcv_exists
            _
            (mkcv_tnat _)
            x
            (mkcv_equality
               _
               (mkcv_apply _ (mk_cv_app_l [x,n] [a] (mkc_var a)) (mk_cv_app_l [x] [n,a] (mk_cv_app_r [a] [n] (mkc_var n))))
               (mk_cv_app_r [n,a] [x] (mkc_var x))
               (mkcv_tnat _))))
      (mkcv_exists
         _
         (mkcv_tnat _)
         x
         (mkcv_equality
            _
            (mkcv_apply _ (mk_cv _ t) (mk_cv_app_l [x] [n] (mkc_var n)))
            (mk_cv_app_r [n] [x] (mkc_var x))
            (mkcv_tnat _))).
Proof.
  introv d1 d2.
  destruct_cterms.
  unfold alphaeqcv; simpl.
  unfsubst; simpl.

  autorewrite with slow.
  boolvar; tcsp.

  - fold_terms.
    autorewrite with slow.
    repeat (rewrite @sub_find_single_not_in; tcsp).

  - fold_terms.
    autorewrite with slow.
    repeat (rewrite @sub_find_single_not_in; tcsp).
Qed.

Hint Rewrite @substc2_apply : slow.
Hint Rewrite @mkcv_apply_substc : slow.

Lemma substc2_pair {o} :
  forall v x (w : @CTerm o) (a b : CVTerm [v,x]),
    substc2 v w x (mkcv_pair [v,x] a b)
    = mkcv_pair [v] (substc2 v w x a) (substc2 v w x b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc2_pair : slow.

Lemma substc2_ax {o} :
  forall v x (w : @CTerm o),
    substc2 v w x (mkcv_ax [v,x])
    = mkcv_ax [v].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc2_ax : slow.

Lemma ccequivc_ext_mkc_apply_ls_existsc_extract {o} :
  forall lib (s : @CTerm o) a n (d : n <> a),
    ccequivc_ext
      lib
      (mkc_apply (ls_existsc_extract a n) s)
      (mkc_lam n (mkcv_pair _ (mkcv_apply _ (mk_cv _ s) (mkc_var n)) (mkcv_ax _))).
Proof.
  introv d ext; spcast.
  unfold ls_existsc_extract.
  eapply cequivc_trans;[apply cequivc_beta|].
  rewrite mkcv_lam_substc; tcsp.
  autorewrite with slow.
  rewrite substc2_mk_cv_app_r; tcsp.
Qed.

Hint Rewrite @mkcv_pair_substc : slow.

Lemma substc_mkcv_ax {o} :
  forall (t : @CTerm o) v,
    substc t v (mkcv_ax _) = mkc_axiom.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl.
  unfsubst.
Qed.
Hint Rewrite @substc_mkcv_ax : slow.

Lemma ccequivc_ext_mkc_apply_ls_existsc_extract2 {o} :
  forall lib (s k : @CTerm o) n,
    ccequivc_ext
      lib
      (mkc_apply (mkc_lam n (mkcv_pair _ (mkcv_apply _ (mk_cv _ s) (mkc_var n)) (mkcv_ax _))) k)
      (mkc_pair (mkc_apply s k) mkc_axiom).
Proof.
  introv ext; spcast.
  eapply cequivc_trans;[apply cequivc_beta|].
  autorewrite with slow; auto.
Qed.

Hint Resolve equality_nat2nat_apply : slow.



(**

<<
   H |- ∀ (a ∈ Free) (n ∈ ℕ). ∃ (x:ℕ). a(n) = x ∈ ℕ

     By LS_EXISTS
>>

 *)

(* Write a proper extract instead of axiom *)
Definition rule_ls_exists {o}
           (lib   : @library o)
           (a n x : NVar)
           (H     : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ls_exists a n x) (ls_exists_extract a n)))
    []
    [].

Lemma rule_ls_exists_true {o} :
  forall (lib : library) (a n x : NVar) (H : @bhyps o)
         (d1 : a <> n) (d2 : a <> x) (d3 : n <> x)
         (safe  : safe_library lib)
         (norep : no_repeats_library lib)
         (sat   : lib_cond_sat_def lib),
    rule_true uk0 lib (rule_ls_exists lib a n x H).
Proof.
  unfold rule_ls_exists, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (ls_exists_extract a n) (nh_vars_hyps H)) as cv.
  {
    dwfseq; tcsp.
    introv h; autorewrite with slow in *; simpl in *; tcsp.
  }
  exists cv.

  vr_seq_true.
  autorewrite with slow.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  clear lib safe norep sat ext.
  rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

  assert (tequality uk0 lib (ls_existsc a n x) (ls_existsc a n x)) as teq.
  {
    apply tequality_function; dands; eauto 3 with slow.
    introv xt ec.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt norep safe sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    repeat (rewrite substc_mkcv_function;[|auto];[]).

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
       apply subst_ls_exists_cond1; auto|];[].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
       apply subst_ls_exists_cond1; auto|];[].

    autorewrite with slow.

    apply tequality_function; dands; eauto 3 with slow;[].

    introv xt en.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ec;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt safe norep sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    repeat (rewrite mkcv_exists_substc; tcsp;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow.

    introv xt ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ec;[|eauto].
    eapply equality_monotone in en;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt safe norep sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    apply tequality_mkc_equality_if_equal; eauto 3 with slow.
  }

  dands; eauto;[].

  apply equality_in_function2.
  dands; eauto 3 with slow;[].

  clear teq.

  introv xt ec.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  clear lib xt safe norep sat.
  rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

  repeat (rewrite substc_mkcv_function;[|auto];[]).

  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
      apply subst_ls_exists_cond1; auto];[].
  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_ls_existsc_extract;eauto|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_ls_existsc_extract;eauto|].

  autorewrite with slow.
  apply equality_in_function2.
  dands; eauto 3 with slow;[|].

  {
    apply tequality_function; dands; eauto 3 with slow.

    introv xt en.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ec;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt safe norep sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    repeat (rewrite mkcv_exists_substc; tcsp;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow.

    introv xt ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ec;[|eauto].
    eapply equality_monotone in en;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt safe norep sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    apply tequality_mkc_equality_if_equal; eauto 3 with slow.
    apply equality_in_csname_implies_equality_in_nat2nat in ec; auto.
    eapply equality_nat2nat_apply; eauto.
    apply equality_refl in ec; auto.
  }

  introv xt en.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply equality_monotone in ec;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  clear lib xt safe norep sat.
  rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_ls_existsc_extract2;eauto|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_ls_existsc_extract2;eauto|].

  rewrite mkcv_exists_substc; auto.
  autorewrite with slow.
  rewrite substc2_mk_cv_app_r; auto.

  apply equality_in_product.
  dands; eauto 3 with slow;[|].

  {
    introv xt ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ec;[|eauto].
    eapply equality_monotone in en;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt safe norep sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    autorewrite with slow.
    apply tequality_mkc_equality_sp; dands; eauto 3 with slow.

    apply in_ext_implies_all_in_ex_bar; introv xt; right; eauto 3 with slow.
  }

  apply in_ext_implies_all_in_ex_bar.
  introv xt.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply equality_monotone in ec;[|eauto].
  eapply equality_monotone in en;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  clear lib xt safe norep sat.
  rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

  exists (mkc_apply a0 a1) (mkc_apply a' a'0) (@mkc_axiom o) (@mkc_axiom o).
  dands; spcast; eauto 3 with slow;[].

  autorewrite with slow.
  apply member_equality.
  eapply equality_refl; eauto 3 with slow.
Qed.
Hint Resolve rule_ls_exists_true : slow.



Definition ls_exists2 {o} (a n x : NVar) : @NTerm o :=
  mk_function
    (mk_csname 0)
    a
    (mk_function
       mk_tnat
       n
       (mk_squash
          (mk_exists
             mk_tnat
             x
             (mk_equality
                (mk_apply (mk_var a) (mk_var x))
                (mk_var n)
                mk_tnat)))).

Definition ls_exists2c {o} (a n x : NVar) : @CTerm o :=
  mkc_function
    (mkc_csname 0)
    a
    (mkcv_function
       _
       (mkcv_tnat _)
       n
       (mkcv_squash
          _
          (mkcv_exists
             _
             (mkcv_tnat _)
             x
             (mkcv_equality
                _
                (mkcv_apply _ (mk_cv_app_l [x,n] _ (mkc_var a)) (mk_cv_app_r [a] _ (mk_cv_app_r [n] _ (mkc_var x))))
                (mk_cv_app_r [a] _ (mk_cv_app_l [x] _ (mkc_var n)))
                (mkcv_tnat _))))).

Definition ls_exists2_extract {o} (a n : NVar) : @NTerm o :=
  mk_lam a (mk_lam n mk_axiom).

Definition ls_exists2c_extract {o} (a n : NVar) : @CTerm o :=
  mkc_lam a (mkcv_lam [a] n (mkcv_ax _)).

Lemma lsubstc_ls_exists2_eq {o} :
  forall a n x (w : @wf_term o (ls_exists2 a n x)) s c,
    lsubstc (ls_exists2 a n x) w s c = ls_exists2c a n x.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls_exists2_eq : slow.

Lemma lsubstc_ls_exists2_extract_eq {o} :
  forall a n (w : @wf_term o (ls_exists2_extract a n)) s c,
    lsubstc (ls_exists2_extract a n) w s c = ls_exists2c_extract a n.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls_exists2_extract_eq : slow.

Lemma subst_ls_exists2_cond1 {o} :
  forall a n x (t : @CTerm o) (d1 : a <> n) (d2 : a <> x),
    alphaeqcv
      _
      (substcv
         [n] t a
         (mkcv_squash
            _
            (mkcv_exists
               _
               (mkcv_tnat _)
               x
               (mkcv_equality
                  _
                  (mkcv_apply _ (mk_cv_app_l [x,n] [a] (mkc_var a)) (mk_cv_app_r [a] [x,n] (mk_cv_app_r [n] [x] (mkc_var x))))
                  (mk_cv_app_r [a] [x,n] (mk_cv_app_l [x] [n] (mkc_var n)))
                  (mkcv_tnat _)))))
      (mkcv_squash
         _
         (mkcv_exists
            _
            (mkcv_tnat _)
            x
            (mkcv_equality
               _
               (mkcv_apply _ (mk_cv _ t) (mk_cv_app_r [n] [x] (mkc_var x)))
               (mk_cv_app_l [x] [n] (mkc_var n))
               (mkcv_tnat _)))).
Proof.
  introv d1 d2.
  destruct_cterms.
  unfold alphaeqcv; simpl.
  unfsubst; simpl.

  autorewrite with slow.
  boolvar; tcsp.

  - fold_terms.
    autorewrite with slow.
    repeat (rewrite @sub_find_single_not_in; tcsp).

  - fold_terms.
    autorewrite with slow.
    repeat (rewrite @sub_find_single_not_in; tcsp).
Qed.

Lemma ccequivc_ext_mkc_apply_ls_exists2c_extract {o} :
  forall lib (s : @CTerm o) a n (d : n <> a),
    ccequivc_ext
      lib
      (mkc_apply (ls_exists2c_extract a n) s)
      (mkc_lam n (mkcv_ax _)).
Proof.
  introv d ext; spcast.
  unfold ls_exists2c_extract.
  eapply cequivc_trans;[apply cequivc_beta|].
  rewrite mkcv_lam_substc; tcsp.
  autorewrite with slow; eauto 3 with slow.
Qed.

Lemma ccequivc_ext_mkc_apply_ls_exists2c_extract2 {o} :
  forall lib (k : @CTerm o) n,
    ccequivc_ext
      lib
      (mkc_apply (mkc_lam n (mkcv_ax _)) k)
      mkc_axiom.
Proof.
  introv ext; spcast.
  eapply cequivc_trans;[apply cequivc_beta|].
  autorewrite with slow; auto.
Qed.



(**

<<
   H |- ∀ (a ∈ Free) (n ∈ ℕ). ∃ (x:ℕ). a(x) = n ∈ ℕ

     By LS_EXISTS2
>>

 *)

(* Write a proper extract instead of axiom *)
Definition rule_ls_exists2 {o}
           (lib   : @library o)
           (a n x : NVar)
           (H     : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ls_exists2 a n x) (ls_exists2_extract a n)))
    []
    [].

Lemma rule_ls_exists2_true {o} :
  forall (lib : library) (a n x : NVar) (H : @bhyps o)
         (d1 : a <> n) (d2 : a <> x) (d3 : n <> x)
         (safe  : safe_library lib)
         (norep : no_repeats_library lib)
         (sat   : lib_cond_sat_def lib),
    rule_true uk0 lib (rule_ls_exists2 lib a n x H).
Proof.
  unfold rule_ls_exists2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (ls_exists2_extract a n) (nh_vars_hyps H)) as cv.
  {
    dwfseq; tcsp.
  }
  exists cv.

  vr_seq_true.
  autorewrite with slow.

  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  clear lib safe norep sat ext.
  rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

  assert (tequality uk0 lib (ls_exists2c a n x) (ls_exists2c a n x)) as teq.
  {
    apply tequality_function; dands; eauto 3 with slow.
    introv xt ec.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt norep safe sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    repeat (rewrite substc_mkcv_function;[|auto];[]).

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
       apply subst_ls_exists2_cond1; auto|];[].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
       apply subst_ls_exists2_cond1; auto|];[].

    autorewrite with slow.

    apply tequality_function; dands; eauto 3 with slow;[].

    introv xt en.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ec;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt safe norep sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    autorewrite with slow.
    apply tequality_mkc_squash.
    repeat (rewrite mkcv_exists_substc; tcsp;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow.

    introv xt ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ec;[|eauto].
    eapply equality_monotone in en;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt safe norep sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    apply tequality_mkc_equality_if_equal; eauto 3 with slow.
  }

  dands; eauto;[].

  apply equality_in_function2.
  dands; eauto 3 with slow;[].

  clear teq.

  introv xt ec.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  clear lib xt safe norep sat.
  rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

  repeat (rewrite substc_mkcv_function;[|auto];[]).

  eapply alphaeqc_preserving_equality;
    [|apply alphaeqc_sym; apply implies_alphaeqc_mk_function;
      apply subst_ls_exists2_cond1; auto];[].
  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_ls_exists2c_extract;eauto|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_ls_exists2c_extract;eauto|].

  autorewrite with slow.
  apply equality_in_function2.
  dands; eauto 3 with slow;[|].

  {
    apply tequality_function; dands; eauto 3 with slow.

    introv xt en.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ec;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt safe norep sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    autorewrite with slow.
    apply tequality_mkc_squash.
    repeat (rewrite mkcv_exists_substc; tcsp;[]).
    autorewrite with slow.
    apply tequality_product; dands; eauto 3 with slow.

    introv xt ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ec;[|eauto].
    eapply equality_monotone in en;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt safe norep sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    apply tequality_mkc_equality_if_equal; eauto 3 with slow.
    apply equality_in_csname_implies_equality_in_nat2nat in ec; auto.
    eapply equality_nat2nat_apply; eauto.
    apply equality_refl in ec; auto.
  }

  introv xt en.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply equality_monotone in ec;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  clear lib xt safe norep sat.
  rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

  eapply equality_respects_cequivc_left;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_ls_exists2c_extract2;eauto|].
  eapply equality_respects_cequivc_right;
    [apply ccequivc_ext_sym;eapply ccequivc_ext_mkc_apply_ls_exists2c_extract2;eauto|].

  autorewrite with slow.
  apply equality_in_mkc_squash_ax.

  rewrite mkcv_exists_substc; auto.
  autorewrite with slow.
  rewrite substc2_mk_cv_app_r; auto.

  apply equality_in_product.
  dands; eauto 3 with slow;[|].

  {
    introv xt ea.

    eapply lib_extends_preserves_similarity in sim;[|eauto].
    eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
    eapply equality_monotone in ec;[|eauto].
    eapply equality_monotone in en;[|eauto].
    assert (safe_library lib') as safe' by eauto 3 with slow.
    assert (no_repeats_library lib') as norep' by eauto 3 with slow.
    assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
    clear lib xt safe norep sat.
    rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

    autorewrite with slow.
    apply tequality_mkc_equality_sp; dands; eauto 3 with slow.

    apply in_ext_implies_all_in_ex_bar; introv xt; right; eauto 3 with slow.
  }

  apply in_ext_implies_all_in_ex_bar.
  introv xt.

  eapply lib_extends_preserves_similarity in sim;[|eauto].
  eapply lib_extends_preserves_hyps_functionality_ext in eqh;[|eauto].
  eapply equality_monotone in ec;[|eauto].
  eapply equality_monotone in en;[|eauto].
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (no_repeats_library lib') as norep' by eauto 3 with slow.
  assert (lib_cond_sat_def lib') as sat' by eauto 3 with slow.
  clear lib xt safe norep sat.
  rename lib' into lib; rename safe' into safe; rename norep' into norep; rename sat' into sat.

  exists (mkc_apply a0 a1) (mkc_apply a' a'0) (@mkc_axiom o) (@mkc_axiom o).
  dands; spcast; eauto 3 with slow;[].

  autorewrite with slow.
  apply member_equality.
  eapply equality_refl; eauto 3 with slow.
Qed.
Hint Resolve rule_ls_exists_true : slow.
