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



Definition ls3 {o} (A a b n : NVar) (i : nat) : @NTerm o :=
  mk_function
    (mk_fun (mk_csname 0) (mk_uni i))
    A
    (mk_function
       (mk_csname 0)
       a
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
                      (mk_apply (mk_var A) (mk_var b)))))))).

Definition ls3c {o} (A a b n : NVar) (i : nat) : @CTerm o :=
  mkc_function
    (mkc_fun (mkc_csname 0) (mkc_uni i))
    A
    (mkcv_function
       _
       (mkcv_csname _ 0)
       a
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
                         (mk_cv_app_r [n,a,A] _ (mkc_var b))))))))).

Definition ls3_extract {o} (A a x : NVar) : @NTerm o :=
  mk_lam A (mk_lam a (mk_lam x mk_axiom)).

Definition ls3c_extract {o} (A a x : NVar) : @CTerm o :=
  mkc_lam A (mkcv_lam _ a (mkcv_lam _ x (mkcv_ax _))).

Lemma lsubstc_ls3_extract_eq {o} :
  forall A a x (w : @wf_term o (ls3_extract A a x)) s c,
    lsubstc (ls3_extract A a x) w s c = ls3c_extract A a x.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls3_extract_eq : slow.

Lemma apply3_ls3c_extract_compute {o} :
  forall lib A a x (u v w : @CTerm o),
    computes_to_valc
      lib
      (mkc_apply (mkc_apply (mkc_apply (ls3c_extract A a x) u) v) w)
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

  unfold apply_bterm; simpl; unflsubst.
Qed.
Hint Resolve apply3_ls3c_extract_compute : slow.

Lemma apply3_ls3c_extract_ccequivc_ext {o} :
  forall lib A a x (u v w : @CTerm o),
    ccequivc_ext
      lib
      (mkc_apply (mkc_apply (mkc_apply (ls3c_extract A a x) u) v) w)
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
Qed.
Hint Rewrite @lsubstc_ls3_eq : slow.

Definition rule_ls3 {o}
           (lib : @library o)
           (A a b n x : NVar)
           (i : nat)
           (H : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ls3 A a b n i) (ls3_extract A a x)))
    []
    [].

Lemma rule_ls3_true {o} :
  forall lib
         (A a b n x : NVar) (i : nat) (H : @bhyps o)
         (d1 : A <> a)
         (d2 : n <> A)
         (d3 : n <> a)
         (safe : safe_library lib),
    rule_true lib (rule_ls3 lib A a b n x i H).
Proof.
  unfold rule_ls3, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.

  assert (@covered o (ls3_extract A a x) (nh_vars_hyps H)) as cv.
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

Qed.
