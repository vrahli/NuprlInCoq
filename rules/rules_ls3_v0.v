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


Require Export rules_choice_util4.


Definition ls3 {o} (A a b n : NVar) (u i : nat) : @NTerm o :=
  mk_function
    (mk_csprop u i)
    A
    (mk_function
       (mk_csname 0)
       a
       (mk_fun
          (mk_free_from_defs (mk_fun (mk_csname 0) (mk_uni u i)) (mk_var A))
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
                         (mk_squash (mk_apply (mk_var A) (mk_var b)))))))))).

Definition ls3c {o} (A a b n : NVar) (u i : nat) : @CTerm o :=
  mkc_function
    (mkc_csprop u i)
    A
    (mkcv_function
       _
       (mkcv_csname _ 0)
       a
       (mkcv_fun
          _
          (mkcv_free_from_defs
             _
             (mkcv_csprop _ u i)
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
                         (mkcv_squash
                            _
                            (mkcv_apply
                               _
                               (mk_cv_app_l [b,n,a] _ (mkc_var A))
                               (mk_cv_app_r [n,a,A] _ (mkc_var b))))))))))).

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

Lemma lsubstc_ls3_eq {o} :
  forall A a b n u i (w : @wf_term o (ls3 A a b n u i)) s c,
    lsubstc (ls3 A a b n u i) w s c = ls3c A a b n u i.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
  repeat rewrite remove_nvars_app_l; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls3_eq : slow.

Lemma tequality_ls3c_aux7 {o} :
  forall uk (lib : @library o) a1 a'0 a'1 a2 a'2 a3,
    no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality uk lib a1 a'0 (mkc_csname 0)
    -> equality uk lib a2 a'1 mkc_tnat
    -> equality uk lib a3 a'2 (mkc_csname 0)
    -> tequality uk lib (mkc_equality a1 a3 (natk2nat a2)) (mkc_equality a'0 a'2 (natk2nat a'1)).
Proof.
  introv norep safe sat; introv equb eque equf.

  apply tequality_mkc_equality_if_equal.
  { apply equality_in_tnat in eque.
    apply all_in_ex_bar_tequality_implies_tequality.
    unfold equality_of_nat_bar in eque.
    eapply lib_extends_preserves_in_open_bar in eque; eauto.
    eapply in_open_bar_comb; eauto.
    apply in_ext_implies_in_open_bar; introv xt e.
    unfold equality_of_nat in e; exrepnd.
    eapply tequality_natk2nat_aux;eauto.
    introv xx; apply Z_of_nat_complete in xx; exrepnd; subst.
    destruct (lt_dec n0 n);[left|right]; dands;
      allrw <- Nat2Z.inj_lt; allrw <- Nat2Z.inj_le; auto; try omega. }

  { apply equality_nat2nat_to_natk2nat.
    { apply equality_refl in eque; eauto 3 with slow. }
    apply equality_in_csname_implies_equality_in_nat2nat in equb; eauto 3 with slow. }

  { apply equality_nat2nat_to_natk2nat.
    { apply equality_refl in eque; eauto 3 with slow. }
    apply equality_in_csname_implies_equality_in_nat2nat in equf; eauto 3 with slow. }
Qed.

Lemma tequality_ls3c_aux6 {o} :
  forall uk (lib : @library o) i a0 a' a1 a'0 a'1 a2 a'2 a3,
    no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality uk lib a0 a' (mkc_csprop uk i)
    -> equality uk lib a1 a'0 (mkc_csname 0)
    -> equality uk lib a2 a'1 mkc_tnat
    -> equality uk lib a3 a'2 (mkc_csname 0)
    -> tequality
         uk lib
         (mkc_fun (mkc_equality a1 a3 (natk2nat a2)) (mkc_squash (mkc_apply a0 a3)))
         (mkc_fun (mkc_equality a'0 a'2 (natk2nat a'1)) (mkc_squash (mkc_apply a' a'2))).
Proof.
  introv norep safe sat; introv equa equb eque equf.

  apply tequality_fun; dands.

  { apply tequality_ls3c_aux7; auto. }

  introv extg equg.
  apply tequality_mkc_squash.
  apply inhabited_mkc_equality in equg.
  apply (equality_in_mkc_csprop_implies_tequality _ _ _ _ _ _ i); eauto 3 with slow.
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
    -> equality uk0 lib a0 a' (mkc_csprop uk0 i)
    -> equality uk0 lib a1 a'0 (mkc_csname 0)
    -> equality uk0 lib a2 a'1 mkc_tnat
    -> tequality uk0 lib
    (mkc_function (mkc_csname 0) b
       (substc5 b a2 n a1 a a0 A
          (mkcv_fun (([b, n] ++ [a]) ++ [A])
             (mkcv_equality (([b, n] ++ [a]) ++ [A])
                (mk_cv_app_r [A] ([b, n] ++ [a])
                   (mk_cv_app_l [b, n] [a] (mkc_var a)))
                (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                (mkcv_natk2nat (([b] ++ [n]) ++ [a, A])
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
                (mkcv_natk2nat (([b] ++ [n]) ++ [a, A])
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
     apply substc_alphaeqcv; apply substc5_mkcv_natk2nat;auto|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_mkc_fun;apply alphaeqc_sym;[|apply alphaeqc_refl];
     apply implies_alphaeqc_mkc_equality;[apply alphaeqc_refl|apply alphaeqc_refl|];
     apply substc_alphaeqcv; apply substc5_mkcv_natk2nat;auto|].
  eapply tequality_respects_alphaeqc_left;
    [apply alphaeqc_mkc_fun;apply alphaeqc_sym;[|apply alphaeqc_refl];
     apply implies_alphaeqc_mkc_equality;[apply alphaeqc_refl|apply alphaeqc_refl|];
     apply substc_mkcv_natk2nat;auto|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_mkc_fun;apply alphaeqc_sym;[|apply alphaeqc_refl];
     apply implies_alphaeqc_mkc_equality;[apply alphaeqc_refl|apply alphaeqc_refl|];
     apply substc_mkcv_natk2nat;auto|].
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
    -> equality uk0 lib a0 a' (mkc_csprop uk0 i)
    -> equality uk0 lib a1 a'0 (mkc_csname 0)
    -> tequality uk0 lib
    (mkc_product mkc_tnat n
       (substc2 n a1 a
          (substc3 n a a0 A
             (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                (mkcv_fun (([b, n] ++ [a]) ++ [A])
                   (mkcv_equality (([b, n] ++ [a]) ++ [A])
                      (mk_cv_app_r [A] ([b, n] ++ [a])
                         (mk_cv_app_l [b, n] [a] (mkc_var a)))
                      (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                      (mkcv_natk2nat (([b] ++ [n]) ++ [a, A])
                         (mk_cv_app_r [a, A] ([b] ++ [n])
                            (mk_cv_app_l [b] [n] (mkc_var n)))))
                   (mkcv_squash ([b, n, a] ++ [A])
                   (mkcv_apply ([b, n, a] ++ [A])
                      (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                      (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))))
    (mkc_product mkc_tnat n
       (substc2 n a'0 a
          (substc3 n a a' A
             (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                (mkcv_fun [b, n, a, A]
                   (mkcv_equality (([b, n] ++ [a]) ++ [A])
                      (mk_cv_app_r [A] ([b, n] ++ [a])
                         (mk_cv_app_l [b, n] [a] (mkc_var a)))
                      (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                      (mkcv_natk2nat (([b] ++ [n]) ++ [a, A])
                         (mk_cv_app_r [a, A] ([b] ++ [n])
                            (mk_cv_app_l [b] [n] (mkc_var n)))))
                   (mkcv_squash ([b, n, a] ++ [A])
                   (mkcv_apply [b, n, a, A] (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                      (mk_cv_app_r [n, a, A] [b] (mkc_var b))))))))).
Proof.
  introv da db dc dd de df norep safe sat; introv equa equb.

  apply tequality_product; dands; eauto 3 with slow.

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
    -> equality uk0 lib a0 a' (mkc_csprop uk0 i)
    -> equality uk0 lib a1 a'0 (mkc_csname 0)
    -> tequality uk0 lib
    (mkc_fun (mkc_apply a0 a1)
       (mkc_squash
          (substc2 a a0 A
             (mkcv_exists [a, A] (mkcv_tnat [a, A]) n
                (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                   (mkcv_fun (([b, n] ++ [a]) ++ [A])
                      (mkcv_equality (([b, n] ++ [a]) ++ [A])
                         (mk_cv_app_r [A] ([b, n] ++ [a])
                            (mk_cv_app_l [b, n] [a] (mkc_var a)))
                         (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                         (mkcv_natk2nat (([b] ++ [n]) ++ [a, A])
                            (mk_cv_app_r [a, A] ([b] ++ [n])
                               (mk_cv_app_l [b] [n] (mkc_var n)))))
                      (mkcv_squash ([b, n, a] ++ [A])
                      (mkcv_apply ([b, n, a] ++ [A])
                         (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                         (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))) [[a \\ a1]]))
    (mkc_fun (mkc_apply a' a'0)
       (mkc_squash
          (substc2 a a' A
             (mkcv_exists [a, A] (mkcv_tnat [a, A]) n
                (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                   (mkcv_fun [b, n, a, A]
                      (mkcv_equality (([b, n] ++ [a]) ++ [A])
                         (mk_cv_app_r [A] ([b, n] ++ [a])
                            (mk_cv_app_l [b, n] [a] (mkc_var a)))
                         (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                         (mkcv_natk2nat (([b] ++ [n]) ++ [a, A])
                            (mk_cv_app_r [a, A] ([b] ++ [n])
                               (mk_cv_app_l [b] [n] (mkc_var n)))))
                      (mkcv_squash ([b, n, a] ++ [A])
                      (mkcv_apply [b, n, a, A]
                         (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                         (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))) [[a \\ a'0]])).
Proof.
  introv da db dc dd de df norep safe sat; introv equa equb.

  apply tequality_fun; dands.

  { apply (equality_in_mkc_csprop_implies_tequality _ _ _ _ _ _ i); eauto; eauto 3 with slow. }

  introv extd equd.
  apply tequality_mkc_squash.
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
    -> equality uk0 lib a0 a' (mkc_csprop uk0 i)
    -> equality uk0 lib a1 a'0 (mkc_csname 0)
    -> tequality uk0 lib
    (mkc_fun
       (substc2 a a0 A
          (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) uk0 i)
             (mk_cv_app_l [a] [A] (mkc_var A)))) [[a \\ a1]]
       (substc2 a a0 A
          (mkcv_fun ([a] ++ [A])
             (mkcv_apply ([a] ++ [A]) (mk_cv_app_l [a] [A] (mkc_var A))
                (mk_cv_app_r [A] [a] (mkc_var a)))
             (mkcv_squash [a, A]
                (mkcv_exists [a, A] (mkcv_tnat [a, A]) n
                   (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                      (mkcv_fun (([b, n] ++ [a]) ++ [A])
                         (mkcv_equality (([b, n] ++ [a]) ++ [A])
                            (mk_cv_app_r [A] ([b, n] ++ [a])
                               (mk_cv_app_l [b, n] [a] (mkc_var a)))
                            (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                            (mkcv_natk2nat (([b] ++ [n]) ++ [a, A])
                               (mk_cv_app_r [a, A] ([b] ++ [n])
                                  (mk_cv_app_l [b] [n] (mkc_var n)))))
                         (mkcv_squash ([b, n, a] ++ [A])
                         (mkcv_apply ([b, n, a] ++ [A])
                            (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                            (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))))) [[a \\
       a1]])
    (mkc_fun
       (substc2 a a' A
          (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) uk0 i)
             (mk_cv_app_l [a] [A] (mkc_var A)))) [[a \\ a'0]]
       (substc2 a a' A
          (mkcv_fun ([a] ++ [A])
             (mkcv_apply ([a] ++ [A]) (mk_cv_app_l [a] [A] (mkc_var A))
                (mk_cv_app_r [A] [a] (mkc_var a)))
             (mkcv_squash [a, A]
                (mkcv_exists [a, A] (mkcv_tnat [a, A]) n
                   (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                      (mkcv_fun [b, n, a, A]
                         (mkcv_equality (([b, n] ++ [a]) ++ [A])
                            (mk_cv_app_r [A] ([b, n] ++ [a])
                               (mk_cv_app_l [b, n] [a] (mkc_var a)))
                            (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                            (mkcv_natk2nat (([b] ++ [n]) ++ [a, A])
                               (mk_cv_app_r [a, A] ([b] ++ [n])
                                  (mk_cv_app_l [b] [n] (mkc_var n)))))
                         (mkcv_squash ([b, n, a] ++ [A])
                         (mkcv_apply [b, n, a, A]
                            (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                            (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))))) [[a \\
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
    -> equality uk0 lib a0 a' (mkc_csprop uk0 i)
    -> tequality uk0 lib
                 (mkc_function (mkc_csname 0) a
       (substcv [a] a0 A
          (mkcv_fun ([a] ++ [A])
             (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) uk0 i)
                (mk_cv_app_l [a] [A] (mkc_var A)))
             (mkcv_fun ([a] ++ [A])
                (mkcv_apply ([a] ++ [A]) (mk_cv_app_l [a] [A] (mkc_var A))
                   (mk_cv_app_r [A] [a] (mkc_var a)))
                (mkcv_squash [a, A]
                   (mkcv_exists [a, A] (mkcv_tnat [a, A]) n
                      (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                         (mkcv_fun (([b, n] ++ [a]) ++ [A])
                            (mkcv_equality (([b, n] ++ [a]) ++ [A])
                               (mk_cv_app_r [A] ([b, n] ++ [a])
                                  (mk_cv_app_l [b, n] [a] (mkc_var a)))
                               (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                               (mkcv_natk2nat (([b] ++ [n]) ++ [a, A])
                                  (mk_cv_app_r [a, A] ([b] ++ [n])
                                     (mk_cv_app_l [b] [n] (mkc_var n)))))
                            (mkcv_squash ([b, n, a] ++ [A])
                            (mkcv_apply ([b, n, a] ++ [A])
                               (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                               (mk_cv_app_r [n, a, A] [b] (mkc_var b))))))))))))
    (mkc_function (mkc_csname 0) a
       (substcv [a] a' A
          (mkcv_fun ([a] ++ [A])
             (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) uk0 i)
                (mk_cv_app_l [a] [A] (mkc_var A)))
             (mkcv_fun ([a] ++ [A])
                (mkcv_apply ([a] ++ [A]) (mk_cv_app_l [a] [A] (mkc_var A))
                   (mk_cv_app_r [A] [a] (mkc_var a)))
                (mkcv_squash [a, A]
                   (mkcv_exists [a, A] (mkcv_tnat [a, A]) n
                      (mkcv_function [n, a, A] (mkcv_csname [n, a, A] 0) b
                         (mkcv_fun [b, n, a, A]
                            (mkcv_equality (([b, n] ++ [a]) ++ [A])
                               (mk_cv_app_r [A] ([b, n] ++ [a])
                                  (mk_cv_app_l [b, n] [a] (mkc_var a)))
                               (mk_cv_app_r [n, a, A] [b] (mkc_var b))
                               (mkcv_natk2nat (([b] ++ [n]) ++ [a, A])
                                  (mk_cv_app_r [a, A] ([b] ++ [n])
                                     (mk_cv_app_l [b] [n] (mkc_var n)))))
                            (mkcv_squash ([b, n, a] ++ [A])
                            (mkcv_apply [b, n, a, A]
                               (mk_cv_app_l [b, n, a] [A] (mkc_var A))
                               (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))))))).
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
    -> tequality uk0 lib (ls3c A a b n uk0 i) (ls3c A a b n uk0 i).
Proof.
  introv da db dc dd de df norep safe sat.
  unfold ls3c.

  apply tequality_function; dands; eauto 3 with slow.
  introv exta equa.
  repeat (rewrite substc_mkcv_function; auto); autorewrite with slow.

  apply tequality_ls3c_aux1; eauto 3 with slow.
Qed.



(* *************************************************************** *)
(* ****** LS3 ****** *)

Definition rule_ls3 {o}
           (lib : @library o)
           (A a b n x y : NVar)
           (i : nat)
           (H : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ls3 A a b n uk0 i) (ls3_extract A a x y)))
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
         (satd  : lib_cond_sat_def lib)
         (nocs  : has_lib_cond_no_cs lib),
    rule_true uk0 lib (rule_ls3 lib A a b n x y i H).
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

  { apply tequality_ls3c; eauto 3 with slow. }

  apply equality_in_function3.
  dands; eauto 3 with slow; try apply type_mkc_csprop;[].

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
    apply tequality_mkc_ffdefs; dands; eauto 3 with slow;try apply tequality_mkc_csprop.
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
    apply tequality_mkc_squash.
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

  rewrite mkcv_product_substc; auto;[].
  autorewrite with slow.

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

  apply in_ext_implies_all_in_ex_bar.
  introv ext.
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
                uk0 lib
                (mkc_lam b (mkcv_lam [b] x (mkcv_ax _)))
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
                      (mkcv_squash _ (mkcv_apply [b] (mk_cv [b] u) (mkc_var b)))))) mem.
  {
    apply equality_in_function3 in mem; repnd.
    apply equality_in_function3; dands; auto.
    introv xt ea.
    pose proof (mem _ xt _ _ ea) as mem; repnd.
    dands.

    {
      eapply tequality_respects_alphaeqc_left; [apply alphaeqc_sym;apply substc_mkcv_fun|].
      eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_fun|].
      eapply tequality_respects_alphaeqc_left  in mem2;[|apply substc_mkcv_fun].
      eapply tequality_respects_alphaeqc_right in mem2;[|apply substc_mkcv_fun].
      autorewrite with slow in *.

      apply tequality_fun in mem2; repnd.
      apply tequality_fun; dands; auto.
      introv xt1 inh.
      apply mem2 in inh; auto; eauto 3 with slow;[].
      allrw @tequality_mkc_squash.
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
        apply implies_type_mkc_squash.
        apply equality_refl in eqA; apply equality_refl in ea.
        eapply equality_in_mkc_csprop_implies_tequality; eauto 3 with slow.
      }

      introv xt1 eb.
      eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym;apply ccequivc_app_app_ax|].
      eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym;apply ccequivc_app_app_ax|].
      apply equality_in_mkc_squash_ax.
      apply mem in eb; eauto 3 with slow;[].
      eapply equality_in_mkc_squash in eb; repnd; auto.
      eapply in_open_bar_pres; try exact eb;[]; introv xtt inh.
      eapply inhabited_type_tequality;
        [apply tequality_sym;eapply equality_in_mkc_csprop_implies_tequality|];
        try exact inh; eapply equality_monotone; try exact xtt; eauto 3 with slow.
      eapply equality_refl; eauto 3 with slow.
    }
  }

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
     apply substc_mkcv_natk2nat;auto|].
  eapply tequality_respects_alphaeqc_right;
    [apply alphaeqc_mkc_fun;apply alphaeqc_sym;[|apply alphaeqc_refl];
     apply implies_alphaeqc_mkc_equality;[apply alphaeqc_refl|apply alphaeqc_refl|];
     apply substc_mkcv_natk2nat;auto|].
  autorewrite with slow.
  eapply tequality_ls3c_aux6; eauto 3 with slow. }

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

  { apply equality_refl in ecs; apply tequality_ls3c_aux7; eauto 3 with slow. }

  { apply equality_refl in ecs; introv extg equg.
    apply inhabited_mkc_equality in equg.
    apply implies_type_mkc_squash.
    apply (equality_in_mkc_csprop_implies_tequality _ _ _ _ _ _ i); eauto 3 with slow. }

  introv ext2 eb.

  eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym;apply ccequivc_app_app_ax|].
  eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym;apply ccequivc_app_app_ax|].

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

  rev_assert (member uk0 lib mkc_axiom (mkc_squash (mkc_apply u (mkc_choice_seq name')))) mem.
  {
    pose proof (equality_in_mkc_csprop_implies_tequality uk0 lib u u b1 (mkc_choice_seq name') i) as teq.
    repeat (autodimp teq hyp); eauto 3 with slow.
    { apply equality_in_csname_iff.
      unfold equality_of_csname_bar.
      apply in_ext_implies_in_open_bar; introv xta.
      exists name'; dands; spcast; eauto 3 with slow. }
    eapply tequality_preserving_equality;[|apply tequality_mkc_squash;apply tequality_sym;eauto]; auto.
  }

  apply equality_in_mkc_squash_ax.
  apply inhabited_type_implies_inhabited_type_bar.
  exists (swap_cs_cterm (name,name') z1).

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
                name name' uk0 (swap_cs_lib (name,name') lib0) lib0
                (swap_cs_cterm (name, name') z1)
                (mkc_apply u (mkc_choice_seq name'))) as m.
  repeat (autodimp m hyp); simpl; eauto 3 with slow.
Qed.
