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


Require Export per_props_qtime_nat.
Require Export per_props_qnat.
Require Export rules_choice_util4.


Lemma isprog_vars_qtime {p} :
  forall (a : @NTerm p) vs,
    isprog_vars vs (mk_qtime a) <=> isprog_vars vs a.
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  allrw <- @wf_term_eq.
  allrw @wf_qtime; split; sp.
Qed.

Lemma isprog_vars_qtime_implies {p} :
  forall (a : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs (mk_qtime a).
Proof.
  introv ispa.
  apply isprog_vars_qtime; sp.
Qed.

Definition mkcv_qtime {o} vs (t : @CVTerm o vs) : CVTerm vs :=
  let (a,x) := t in
  exist (isprog_vars vs) (mk_qtime a) (isprog_vars_qtime_implies a vs x).

Definition mkcv_qtnat {o} vs : @CVTerm o vs :=
  mkcv_qtime _ (mkcv_tnat _).

Lemma isprog_vars_qnat_implies {o} :
  forall vs, @isprog_vars o vs mk_qnat.
Proof.
  introv; repeat constructor; simpl.
  apply assert_sub_vars; simpl; tcsp.
Qed.

Definition mkcv_qnat {o} vs : @CVTerm o vs :=
  exist (isprog_vars vs) mk_qnat (isprog_vars_qnat_implies vs).

Lemma nt_wf_mk_lib_depth {o} : @nt_wf o mk_lib_depth.
Proof.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve nt_wf_mk_lib_depth : slow.

Lemma isprog_vars_lib_depth {p} :
  forall vs, @isprog_vars p vs mk_lib_depth.
Proof.
  introv; apply isprog_vars_eq; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_lib_depth : slow.

Lemma isprog_lib_depth {o} : @isprog o mk_lib_depth.
Proof.
  repeat constructor.
Qed.

Definition mkcv_lib_depth {o} (vs : list NVar) : @CVTerm o vs :=
  exist (isprog_vars vs) mk_lib_depth (@isprog_vars_lib_depth o vs).

Definition mkc_lib_depth {o} : @CTerm o :=
  exist isprog mk_lib_depth isprog_lib_depth.


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
             (mk_exists
                mk_qnat
                n
                (mk_function
                   (mk_csname 0)
                   b
                   (mk_fun
                      (mk_equality (mk_var a) (mk_var b) (mk_natk2nat (mk_var n)))
                      (mk_squash (mk_apply (mk_var A) (mk_var b))))))))).

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
             (mkcv_exists
                _
                (mkcv_qnat _)
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
                            (mk_cv_app_r [n,a,A] _ (mkc_var b)))))))))).

Definition ls3_extract {o} (A a x y b z : NVar) : @NTerm o :=
  mk_lam A (mk_lam a (mk_lam x (mk_lam y (mk_pair mk_lib_depth (mk_lam b (mk_lam z mk_axiom)))))).

Definition ls3c_extract {o} (A a x y b z : NVar) : @CTerm o :=
  mkc_lam A (mkcv_lam _ a (mkcv_lam _ x (mkcv_lam _ y (mkcv_pair _ (mkcv_lib_depth _) (mkcv_lam _ b (mkcv_lam _ z (mkcv_ax _))))))).

Lemma lsubstc_ls3_extract_eq {o} :
  forall A a x y b z (w : @wf_term o (ls3_extract A a x y b z)) s c,
    lsubstc (ls3_extract A a x y b z) w s c = ls3c_extract A a x y b z.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_ls3_extract_eq : slow.

Lemma isvalue_pair_aux1 {o} :
  forall b c,
    @isvalue o (mk_pair mk_lib_depth (mk_lam b (mk_lam c mk_axiom))).
Proof.
  introv.
  repeat (repeat constructor; simpl; introv xx; repndors; subst; tcsp).
Qed.
Hint Resolve isvalue_pair_aux1 : slow.

Lemma apply3_ls3c_extract_compute {o} :
  forall lib A a x y b c (u v w z : @CTerm o),
    computes_to_valc
      lib
      (mkc_apply (mkc_apply (mkc_apply (mkc_apply (ls3c_extract A a x y b c) u) v) w) z)
      (mkc_pair mkc_lib_depth (mkc_lam b (mkcv_lam _ c (mkcv_ax _)))).
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
  forall lib A a x y b c (u v w z : @CTerm o),
    ccequivc_ext
      lib
      (mkc_apply (mkc_apply (mkc_apply (mkc_apply (ls3c_extract A a x y b c) u) v) w) z)
      (mkc_pair mkc_lib_depth (mkc_lam b (mkcv_lam _ c (mkcv_ax _)))).
Proof.
  introv ext; spcast; eauto 3 with slow.
Qed.
Hint Resolve apply3_ls3c_extract_ccequivc_ext : slow.

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

Hint Rewrite @mkcv_le_substc2 : slow.
Hint Rewrite @mkcv_less_than_substc : slow.

Lemma implies_equality_in_int_implies_tequality_mkc_le {o} :
  forall lib (a b c d : @CTerm o),
    equality lib a b mkc_int
    -> equality lib c d mkc_int
    -> tequality lib (mkc_le a c) (mkc_le b d).
Proof.
  introv equa equb.
  allrw @equality_in_int.
  apply all_in_ex_bar_tequality_implies_tequality.
  eapply in_open_bar_comb;[|exact equa]; clear equa.
  eapply in_open_bar_pres;[|exact equb]; clear equb.
  introv ext equb eqa.
  unfold equality_of_int in *; exrepnd.
  eapply tequality_mkc_le_aux; eauto.
  destruct (Z_le_gt_dec k k0); [left|right]; dands; auto; try omega.
Qed.

Lemma zero_equal_in_int {o} :
  forall (lib : @library o),
    equality lib mkc_zero mkc_zero mkc_int.
Proof.
  introv.
  apply equality_in_int.
  apply in_ext_implies_in_open_bar; introv ext.
  exists 0%Z; rewrite mkc_integer_as_mk_zero; dands; eauto 3 with slow.
Qed.
Hint Resolve zero_equal_in_int : slow.

Lemma implies_cequivc_mkc_less_than {o} :
  forall lib (f g a b : @CTerm o),
    cequivc lib f g
    -> cequivc lib a b
    -> cequivc lib (mkc_less_than f a) (mkc_less_than g b).
Proof.
  introv ceqa ceqb.
  repeat rewrite cvterm2.mkc_less_than_eq.
  apply implies_cequivc_less; eauto 3 with slow.
Qed.
Hint Resolve implies_cequivc_mkc_less_than : slow.

Lemma implies_ccequivc_ext_mkc_less_than {o} :
  forall lib (f g a b : @CTerm o),
    ccequivc_ext lib f g
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib (mkc_less_than f a) (mkc_less_than g b).
Proof.
  introv ceqa ceqb ext.
  applydup ceqa in ext.
  applydup ceqb in ext.
  spcast; eauto 3 with slow.
Qed.
Hint Resolve implies_ccequivc_ext_mkc_less_than : slow.

Lemma equality_mkc_qnat_implies_tequality_mkc_natk {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_qnat
    -> tequality lib (mkc_natk a) (mkc_natk b).
Proof.
  introv equ.
  repeat rewrite mkc_natk_eq.

  apply tequality_set; dands; eauto 3 with slow.
  introv exta equa.
  eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_prod_substc|].
  eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_prod_substc|].
  autorewrite with slow.

  apply tequality_mkc_prod; dands; eauto 3 with slow.

  { apply implies_equality_in_int_implies_tequality_mkc_le; eauto 3 with slow. }

  introv ext inh.
  eapply equality_monotone in equ; eauto.
  clear dependent lib; rename lib' into lib.
  eapply equality_monotone in equ; eauto.
  eapply equality_monotone in equa; eauto.
  clear dependent lib; rename lib'0 into lib.

  apply equality_in_qnat in equ.

  apply all_in_ex_bar_tequality_implies_tequality.
  eapply in_open_bar_pres;[|exact equ]; clear equ.
  introv ext equ; exrepnd.

  assert (ccequivc_ext lib' a b) as ceq.
  { introv x; apply equ in x; exrepnd; spcast.
    apply computes_to_valc_implies_cequivc in x1.
    apply computes_to_valc_implies_cequivc in x0.
    eapply cequivc_trans;[eauto|].
    apply cequivc_sym; auto. }

  eapply tequality_respects_cequivc_left;
    [apply implies_ccequivc_ext_mkc_less_than;
     [apply ccequivc_ext_refl|apply ccequivc_ext_sym;eauto] |].

  applydup @equality_in_int_implies_cequiv in equa.
  apply ccequivc_ext_bar_iff_ccequivc_bar in equa0.
  apply all_in_ex_bar_tequality_implies_tequality.
  eapply lib_extends_preserves_in_open_bar in equa0; eauto.
  eapply in_open_bar_pres;[|exact equa0]; clear equa0.
  introv xt ceq'.

  eapply tequality_respects_cequivc_left;
    [apply implies_ccequivc_ext_mkc_less_than;
     [apply ccequivc_ext_sym;eauto|apply ccequivc_ext_refl] |].

SearchAbout mkc_less_than mkc_le.
SearchAbout type mkc_less_than.
Locate type_mkc_less_than_aux.
Qed.

Lemma tequality_ls3c_aux7 {o} :
  forall (lib : @library o) a1 a'0 a'1 a2 a'2 a3,
    no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality lib a1 a'0 (mkc_csname 0)
    -> equality lib a2 a'1 mkc_qnat
    -> equality lib a3 a'2 (mkc_csname 0)
    -> tequality lib (mkc_equality a1 a3 (natk2nat a2)) (mkc_equality a'0 a'2 (natk2nat a'1)).
Proof.
  introv norep safe sat; introv equb eque equf.

  apply tequality_mkc_equality_if_equal.
  { apply tequality_fun; dands; eauto 3 with slow.

SearchAbout tequality mkc_natk.
SearchAbout tequality mkc_fun.


XXXXXXXXXXX

apply equality_in_tnat in eque.
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
  forall (lib : @library o) i a0 a' a1 a'0 a'1 a2 a'2 a3,
    no_repeats_library lib
    -> safe_library lib
    -> lib_cond_sat_def lib
    -> equality lib a0 a' (mkc_csprop i)
    -> equality lib a1 a'0 (mkc_csname 0)
    -> equality lib a2 a'1 mkc_tnat
    -> equality lib a3 a'2 (mkc_csname 0)
    -> tequality
         lib
         (mkc_fun (mkc_equality a1 a3 (natk2nat a2)) (mkc_squash (mkc_apply a0 a3)))
         (mkc_fun (mkc_equality a'0 a'2 (natk2nat a'1)) (mkc_squash (mkc_apply a' a'2))).
Proof.
  introv norep safe sat; introv equa equb eque equf.

  apply tequality_fun; dands.

  { apply tequality_ls3c_aux7; auto. }

  introv extg equg.
  apply tequality_mkc_squash.
  apply inhabited_mkc_equality in equg.
  apply (equality_in_mkc_csprop_implies_tequality _ _ _ _ _ i); eauto 3 with slow.
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
    -> equality lib a0 a' (mkc_csprop i)
    -> equality lib a1 a'0 (mkc_csname 0)
    -> equality lib a2 a'1 mkc_qtnat
    -> tequality lib
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
    -> equality lib a0 a' (mkc_csprop i)
    -> equality lib a1 a'0 (mkc_csname 0)
    -> tequality lib
    (mkc_product mkc_qtnat n
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
    (mkc_product mkc_qtnat n
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
    -> equality lib a0 a' (mkc_csprop i)
    -> equality lib a1 a'0 (mkc_csname 0)
    -> tequality lib
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

  { apply (equality_in_mkc_csprop_implies_tequality _ _ _ _ _ i); eauto; eauto 3 with slow. }

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
    -> equality lib a0 a' (mkc_csprop i)
    -> equality lib a1 a'0 (mkc_csname 0)
    -> tequality lib
    (mkc_fun
       (substc2 a a0 A
          (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) i)
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
          (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) i)
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
    -> equality lib a0 a' (mkc_csprop i)
    -> tequality lib
                 (mkc_function (mkc_csname 0) a
       (substcv [a] a0 A
          (mkcv_fun ([a] ++ [A])
             (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) i)
                (mk_cv_app_l [a] [A] (mkc_var A)))
             (mkcv_fun ([a] ++ [A])
                (mkcv_apply ([a] ++ [A]) (mk_cv_app_l [a] [A] (mkc_var A))
                   (mk_cv_app_r [A] [a] (mkc_var a)))
                   (mkcv_exists [a, A] (mkcv_qtnat [a, A]) n
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
                               (mk_cv_app_r [n, a, A] [b] (mkc_var b)))))))))))
    (mkc_function (mkc_csname 0) a
       (substcv [a] a' A
          (mkcv_fun ([a] ++ [A])
             (mkcv_free_from_defs ([a] ++ [A]) (mkcv_csprop ([a] ++ [A]) i)
                (mk_cv_app_l [a] [A] (mkc_var A)))
             (mkcv_fun ([a] ++ [A])
                (mkcv_apply ([a] ++ [A]) (mk_cv_app_l [a] [A] (mkc_var A))
                   (mk_cv_app_r [A] [a] (mkc_var a)))
                   (mkcv_exists [a, A] (mkcv_qtnat [a, A]) n
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
                               (mk_cv_app_r [n, a, A] [b] (mkc_var b))))))))))).
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
*)

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
    -> tequality lib (ls3c A a b n i) (ls3c A a b n i).
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
         (satd  : lib_cond_sat_def lib)
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

  { apply tequality_ls3c; eauto 3 with slow. }

  apply equality_in_function3.
  dands; eauto 3 with slow;[].

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
    apply tequality_mkc_ffdefs; dands; eauto 3 with slow.
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
                lib
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
      eapply tequality_respects_alphaeqc_left  in mem1;[|apply substc_mkcv_fun].
      eapply tequality_respects_alphaeqc_right in mem1;[|apply substc_mkcv_fun].
      autorewrite with slow in *.

      apply tequality_fun in mem1; repnd.
      apply tequality_fun; dands; auto.
      introv xt1 inh.
      apply mem1 in inh; auto; eauto 3 with slow;[].
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
    apply (equality_in_mkc_csprop_implies_tequality _ _ _ _ _ i); eauto 3 with slow. }

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

  rev_assert (member lib mkc_axiom (mkc_squash (mkc_apply u (mkc_choice_seq name')))) mem.
  {
    pose proof (equality_in_mkc_csprop_implies_tequality lib u u b1 (mkc_choice_seq name') i) as teq.
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
                name name' (swap_cs_lib (name,name') lib0) lib0
                (swap_cs_cterm (name, name') z1)
                (mkc_apply u (mkc_choice_seq name'))) as m.
  repeat (autodimp m hyp); simpl; eauto 3 with slow.
Qed.



(*Lemma approx_swap {o} :
  forall lib n1 n2 (t : @NTerm o),
    isprogram t
    -> approx
         lib
         (swap_cs_term (n1,n2) t)
         (mk_swap_cs2 n1 n2 t).
Proof.
  cofix ind; introv isp.
  constructor.
  unfold close_comput; dands; eauto 2 with slow;[|].

  { introv comp.

Definition swap_cs_bterms {o} sw (bs : list (@BTerm o)) :=
  map (swap_cs_bterm sw) bs.

Lemma swap_cs_bterms_twice {o} :
  forall sw (bs : list (@BTerm o)),
    map (swap_cs_bterm sw) (map (swap_cs_bterm sw) bs)
    = bs.
Proof.
  induction bs; simpl;auto; allrw;autorewrite with slow; auto.
Qed.
Hint Rewrite @swap_cs_bterms_twice : slow.

Lemma xxx {o} :
  forall (lib : @plibrary o) n1 n2 t (u : NTerm),
    n1 <> n2
    -> compute_step lib (swap_cs_term (n1,n2) t) = csuccess u
    -> reduces_to lib (mk_swap_cs2 n1 n2 t) (mk_swap_cs2 n1 n2 (swap_cs_term (n1,n2) u)).
Proof.
  nterm_ind1s t as [v|op bs ind] Case; introv dn comp; tcsp.

  { csunf comp; simpl in comp; ginv. }

  dopid op as [can|ncan|exc|abs] SCase.

  { csunf comp; simpl in *; ginv; simpl; autorewrite with slow; eauto 3 with slow. }

  { csunf comp; simpl in *.
    destruct bs; simpl in *; ginv.
    destruct b; simpl in *; ginv.
    destruct l; simpl in *; ginv.

    { destruct n; simpl in *; ginv.
      destruct o0; simpl in *; ginv.

      { dopid_noncan ncan SSCase; simpl in *;
          try apply_comp_success;
          try (complete (dcwf h));
          try (complete (ginv; csunf; simpl in *; eauto)).

        { destruct c; simpl in *; ginv.
          repeat (destruct l; simpl in *; ginv).
          destruct b0; simpl in *; inversion comp2; subst; clear comp2.
          repeat (destruct bs; simpl in *; ginv).
          destruct b; simpl in *; inversion comp3; subst; clear comp3; simpl in *.
          apply reduces_to_if_step; csunf; simpl; auto.
          rewrite swap_cs_term_subst; autorewrite with slow; auto. }

        { destruct c; simpl in *; ginv.
          repeat (destruct l; simpl in *; ginv).
          repeat (destruct bs; simpl in *; ginv).
          destruct b; simpl in *; inversion comp3; subst; clear comp3; simpl in *.
          apply reduces_to_if_step; csunf; simpl; auto.
          boolvar; subst; tcsp; autorewrite with slow; auto. }

        { repndors; exrepnd.

          { destruct bs; simpl in *; ginv.
            destruct b; simpl in *.
            inversion comp0; subst; clear comp0.
            apply compute_step_eapply2_success in comp1; exrepnd.
            destruct bs; simpl in *; ginv.
            repndors; exrepnd; subst; simpl in *; ginv.

            { destruct c; simpl in *; ginv.
              repeat (destruct l; simpl in *; ginv).
              destruct b0; simpl in *.
              inversion comp0; subst; clear comp0; simpl in *.
              apply reduces_to_if_step; csunf; simpl.
              apply iscan_implies in comp3; exrepnd.
              destruct n; simpl in *; ginv.
              destruct o0; simpl in *; ginv; simpl in *.
              unfold apply_bterm; simpl.
              rewrite swap_cs_term_lsubst; repeat (autorewrite with slow; simpl;auto). }

            { destruct c; simpl in *; ginv.
              repeat (destruct l; simpl in *; ginv).
              destruct n; simpl in *; ginv.
              destruct o0; simpl in *; ginv; GC.
              destruct c0; simpl in *; ginv.
              inversion comp4; subst; simpl in *.
              destruct l; simpl in *; ginv.
              apply reduces_to_if_step; csunf; simpl.
              boolvar; subst; simpl in *; tcsp; inversion comp1; subst; simpl in *.
              { csunf; simpl; auto.
                unfold compute_step_eapply; simpl; boolvar; try omega; autorewrite with slow.

Qed.

Lemma xxx {o} :
  forall (lib : @plibrary o) n1 n2 t can (bs : list BTerm),
    (swap_cs_term (n1,n2) t) =v>(lib) (oterm (Can can) bs)
    -> (mk_swap_cs2 n1 n2 t) =v>(lib) (oterm (Can (swap_cs_can (n1,n2) can)) (push_swap_cs_bterms n1 n2 (swap_cs_bterms (n1,n2) bs))).

    apply (@swap_computes_to_value o (n1,n2)) in comp; autorewrite with slow in comp; simpl in comp.
    apply (approx_star_swap.implies_reduces_to_mk_swap_cs2 _ n1 n2) in comp.

SearchAbout mk_swap_cs2.
SearchAbout swap_cs_term computes_to_value.

Qed.
*)
