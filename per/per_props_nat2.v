(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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


Require Export natk.
Require Export natk2.
Require Export cequiv_seq_util.
Require Export per_respects.
Require Export per_props_nat.
Require Export per_props_function.
Require Export per_props_union.


Lemma isprog_vars_integer {o} :
  forall vs i,  @isprog_vars o vs (mk_integer i).
Proof.
  introv.
  apply isprog_vars_eq; simpl; dands; eauto 2 with slow.
Qed.

Definition mkcv_integer {o} vs (i : Z) : @CVTerm o vs :=
  exist (isprog_vars vs) (mk_integer i) (isprog_vars_integer vs i).

Lemma mkcv_integer_substc {o} :
  forall v i (t : @CTerm o), substc t v (mkcv_integer [v] i) = mkc_integer i.
Proof.
  introv.
  destruct_cterms; apply cterm_eq; simpl.
  unfsubst.
Qed.

Definition lam_uptok {o} v k : @CTerm o :=
  mkc_lam v (mkcv_less
               [v]
               (mkc_var v)
               (mkcv_integer [v] k)
               (mkcv_zero [v])
               (mkcv_bot [v])).

Hint Rewrite @mkcv_less_substc    : slow.
Hint Rewrite @mkcv_bot_substc     : slow.
Hint Rewrite @mkcv_integer_substc : slow.

Lemma mkc_bot_doesnt_converge {o} :
  forall lib (t : @CTerm o), !computes_to_valc lib mkc_bot t.
Proof.
  introv comp.
  apply bottom_diverges in comp; auto.
Qed.

Lemma bot_not_in_nat {o} :
  forall lib, !@member o lib mkc_bot mkc_tnat.
Proof.
  introv m.
  apply equality_in_tnat in m.
  unfold equality_of_nat in m; exrepnd; spcast; GC.
  apply mkc_bot_doesnt_converge in m1; auto.
Qed.

Lemma lam_uptok_member_iff_lt {o} :
  forall lib v (a : @CTerm o) (k1 k2 : Z),
    computes_to_valc lib a (mkc_integer k2)
    -> (0 <= k1)%Z
    -> (0 <= k2)%Z
    ->
    (member
        lib
        (lam_uptok v k1)
        (mkc_fun (mkc_natk a) mkc_tnat)
        <=> (k2 <= k1)%Z).
Proof.
  introv comp lek1 lek2.

  pose proof (Z_of_nat_complete k1) as h1; autodimp h1 hyp.
  pose proof (Z_of_nat_complete k2) as h2; autodimp h2 hyp.
  exrepnd; subst.

  split; intro h.

  - apply equality_in_fun in h; repnd.
    clear h0 h1.
    destruct (le_lt_dec n n0) as [d|d]; auto; try omega.

    assert False; tcsp.

    pose proof (h (mkc_nat (pred n)) (mkc_nat (pred n))) as q; clear h.
    autodimp q hyp.

    { apply equality_in_natk.
      exists (pred n) (Z.of_nat n).
      dands; spcast; eauto 3 with slow.
      apply Nat2Z.inj_lt.
      apply lt_pred_n_n; try omega. }

    eapply equality_respects_cequivc_left in q;[|apply cequivc_beta].
    eapply equality_respects_cequivc_right in q;[|apply cequivc_beta].
    autorewrite with slow in q.
    allrw <- @mkc_nat_eq.

    eapply equality_respects_cequivc_left in q;[|apply cequivc_mkc_less_nat].
    apply equality_refl in q.
    boolvar; try omega.

    apply bot_not_in_nat in q; auto.

  - apply equality_in_fun; dands; eauto 3 with slow.

    { apply type_mkc_natk.
      exists (Z.of_nat n); spcast; auto. }

    introv ea.
    eapply equality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_beta|].
    eapply equality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_beta|].
    autorewrite with slow.

    apply equality_in_natk in ea; exrepnd; spcast.
    computes_to_eqval.

    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;
       apply cequivc_mkc_less;
       [apply computes_to_valc_implies_cequivc;eauto
       |apply cequivc_refl
       |apply cequivc_refl
       |apply cequivc_refl]
      |].

    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
       apply cequivc_mkc_less;
       [apply computes_to_valc_implies_cequivc;eauto
       |apply cequivc_refl
       |apply cequivc_refl
       |apply cequivc_refl]
      |].

    allrw <- @mkc_nat_eq.

    eapply equality_respects_cequivc_left;
      [apply cequivc_sym; apply cequivc_mkc_less_nat
      |].

    eapply equality_respects_cequivc_right;
      [apply cequivc_sym; apply cequivc_mkc_less_nat
      |].

    boolvar; try omega.

    apply equality_in_tnat.
    exists 0.
    allrw <- @mkc_zero_eq.
    dands; spcast; eauto 2 with slow.
Qed.

Lemma member_fun_natk2nat_if_le0 {o} :
  forall lib (a : @CTerm o) (k : Z) t,
    computes_to_valc lib a (mkc_integer k)
    -> (k <= 0)%Z
    -> member lib t (mkc_fun (mkc_natk a) mkc_tnat).
Proof.
  introv comp lek.
  apply equality_in_fun; dands; eauto 3 with slow.

  { apply type_mkc_natk.
    exists k; spcast; auto. }

  introv ea.
  apply equality_in_natk in ea; exrepnd; spcast; computes_to_eqval; omega.
Qed.

Lemma equality_fun_natk2nat_if_le0 {o} :
  forall lib (a : @CTerm o) (k : Z) t u,
    computes_to_valc lib a (mkc_integer k)
    -> (k <= 0)%Z
    -> equality lib t u (mkc_fun (mkc_natk a) mkc_tnat).
Proof.
  introv comp lek.
  apply equality_in_fun; dands; eauto 3 with slow.

  { apply type_mkc_natk.
    exists k; spcast; auto. }

  introv ea.
  apply equality_in_natk in ea; exrepnd; spcast; computes_to_eqval; omega.
Qed.

Lemma mkc_apply_bot_cequivc_bot {o} :
  forall lib (t : @CTerm o),
    cequivc lib (mkc_apply mkc_bot t) mkc_bot.
Proof.
  introv.
  apply cequivc_iff_approxc; dands;
    [|apply bottom_approx_any; eauto 2 with slow].
  apply approxc_assume_hasvalue; introv hv.
  assert False; tcsp.

  destruct_cterms.
  unfold hasvalue_likec in hv; simpl in hv.
  unfold hasvalue_like in hv; exrepnd.

  unfold reduces_to in hv1; exrepnd.
  revert dependent v.
  induction k as [? ind] using comp_ind; introv comp isv.

  destruct k.

  { allrw @reduces_in_atmost_k_steps_0; subst.
    apply isvalue_like_apply in isv; auto. }

  allrw @reduces_in_atmost_k_steps_S; exrepnd.
  csunf comp1; simpl in comp1; ginv; fold_terms.

  destruct k.

  { allrw @reduces_in_atmost_k_steps_0; subst.
    apply isvalue_like_apply in isv; auto. }

  allrw @reduces_in_atmost_k_steps_S; exrepnd.
  csunf comp0; simpl in comp0; ginv; fold_terms.

  unfold apply_bterm in comp1; simpl in comp1.
  unflsubst in comp1; simpl in comp1.
  apply ind in comp1; auto.
Qed.

Lemma not_member_fun_natk2nat_if_lt0 {o} :
  forall lib (a : @CTerm o) (k : Z),
    computes_to_valc lib a (mkc_integer k)
    -> (0 < k)%Z
    -> !member lib mkc_bot (mkc_fun (mkc_natk a) mkc_tnat).
Proof.
  introv comp lek m.
  apply equality_in_fun in m; repnd.

  pose proof (m mkc_zero mkc_zero) as q; clear m.
  autodimp q hyp.

  { apply equality_in_natk.
    exists 0 k; allrw <- @mkc_zero_eq; dands; spcast; eauto 2 with slow. }

  eapply equality_respects_cequivc_left in q;[|apply mkc_apply_bot_cequivc_bot].
  eapply equality_respects_cequivc_right in q;[|apply mkc_apply_bot_cequivc_bot].

  apply equality_in_tnat in q.
  unfold equality_of_nat in q; exrepnd; spcast; GC.
  apply mkc_bot_doesnt_converge in q1; auto.
Qed.

Lemma ext_eq_mkc_fun_natk2nat_iff {o} :
  forall lib (a b : @CTerm o) k1 k2,
    computes_to_valc lib a (mkc_integer k1)
    -> computes_to_valc lib b (mkc_integer k2)
    ->
    (
      ext_eq lib (mkc_fun (mkc_natk a) mkc_tnat) (mkc_fun (mkc_natk b) mkc_tnat)
      <=>
      (((k1 <= 0)%Z # (k2 <= 0)%Z)
       {+}
       ((0 < k1)%Z # (0 < k2)%Z # k1 = k2))
    ).
Proof.
  introv comp1 comp2.
  split; intro h.

  - destruct (Z_lt_le_dec 0 k1) as [d1|d1];
      destruct (Z_lt_le_dec 0 k2) as [d2|d2]; tcsp.

    + right; dands; auto.

      pose proof (h (lam_uptok nvarx k1) (lam_uptok nvarx k1)) as q.
      destruct q as [q1 q']; clear q'.

      pose proof (h (lam_uptok nvarx k2) (lam_uptok nvarx k2)) as q.
      destruct q as [q' q2]; clear q'.

      autodimp q1 hyp.

      { pose proof (lam_uptok_member_iff_lt lib nvarx a k1 k1) as w.
        repeat (autodimp w hyp); try omega.
        apply w; omega. }

      pose proof (lam_uptok_member_iff_lt lib nvarx b k1 k2) as w.
      repeat (autodimp w hyp); try omega.
      apply w in q1; clear w.

      autodimp q2 hyp.

      { pose proof (lam_uptok_member_iff_lt lib nvarx b k2 k2) as w.
        repeat (autodimp w hyp); try omega.
        apply w; omega. }

      pose proof (lam_uptok_member_iff_lt lib nvarx a k2 k1) as w.
      repeat (autodimp w hyp); try omega.
      apply w in q2; clear w.

      omega.

    + pose proof (h mkc_bot mkc_bot) as q.
      destruct q as [q' q]; clear q'.
      autodimp q hyp.

      { rewrite member_eq.
        eapply member_fun_natk2nat_if_le0; eauto; try omega. }

      rewrite member_eq in q.
      eapply not_member_fun_natk2nat_if_lt0 in q; eauto; tcsp.

    + pose proof (h mkc_bot mkc_bot) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp.

      { rewrite member_eq.
        eapply member_fun_natk2nat_if_le0; eauto; try omega. }

      rewrite member_eq in q.
      eapply not_member_fun_natk2nat_if_lt0 in q; eauto; tcsp.

  - introv; split; intro q; repndors; repnd; subst.

    + eapply equality_fun_natk2nat_if_le0; eauto.

    + eapply cequivc_preserving_equality;[exact q|].
      apply cequivc_mkc_fun; eauto 2 with slow.
      apply cequivc_mkc_natk.
      eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;exact comp1|].
      apply cequivc_sym; apply computes_to_valc_implies_cequivc; auto.

    + eapply equality_fun_natk2nat_if_le0; eauto.

    + eapply cequivc_preserving_equality;[exact q|].
      apply cequivc_mkc_fun; eauto 2 with slow.
      apply cequivc_mkc_natk.
      eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;exact comp2|].
      apply cequivc_sym; apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma tequality_natk2nat {o} :
  forall lib (a b : @CTerm o),
    tequality lib (natk2nat a) (natk2nat b)
     <=> {k1 : Z
         , {k2 : Z
         , (a) ===>(lib) (mkc_integer k1)
         # (b) ===>(lib) (mkc_integer k2)
         # (((k1 <= 0)%Z # (k2 <= 0)%Z)
           {+}
           ((0 < k1)%Z # (0 < k2)%Z # k1 = k2))
         }}.
Proof.
  introv.
  unfold natk2nat.
  rw @tequality_fun.
  allrw @type_mkc_natk.
  split; intro k; exrepnd; dands; eauto 3 with slow.

  - spcast; exists k1 k4; dands; spcast; auto.
    eapply ext_eq_mkc_fun_natk2nat_iff in k; eauto.

  - spcast; eapply ext_eq_mkc_fun_natk2nat_iff; eauto.
Qed.

Lemma lsubstc_mk_unit {o} :
  forall w (s : @CSub o) c,
    lsubstc mk_unit w s c = mkc_unit.
Proof.
  introv.
  unfold mk_unit, mkc_unit.
  rw @lsubstc_mk_true; apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_natU {o} :
  forall w (s : @CSub o) c,
    alphaeqc (lsubstc mk_natU w s c) natU.
Proof.
  introv.
  unfold mk_natU, natU.
  pose proof (lsubstc_mk_bunion_ex mk_tnat mk_unit s w c) as h.
  exrepnd.
  eapply alphaeqc_trans;[exact h1|]; clear h1.
  rw @lsubstc_mkc_tnat.
  rw @lsubstc_mk_unit.
  apply alphaeqc_refl.
Qed.

Lemma type_natU {o} :
  forall (lib : @library o),
    type lib natU.
Proof.
  introv.
  apply type_bunion; dands; eauto 2 with slow.
Qed.
Hint Resolve type_natU : slow.

Lemma lsubstc_mk_nat2nat {o} :
  forall w (s : @CSub o) c,
    alphaeqc (lsubstc mk_nat2nat w s c) nat2nat.
Proof.
  introv.
  unfold alphaeqc; simpl.
  unfold csubst.
  rw @cl_lsubst_lsubst_aux; eauto 2 with slow.

  simpl.

  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_trivial.
  fold_terms.
  auto.
Qed.

Lemma type_nat2nat {o} :
  forall (lib : @library o), type lib nat2nat.
Proof.
  introv.
  unfold nat2nat.
  apply type_mkc_fun; dands; eauto 3 with slow.
Qed.
Hint Resolve type_nat2nat : slow.

Lemma equality_natk_to_tnat {o} :
  forall lib (n1 n2 k : @CTerm o),
    equality lib n1 n2 (mkc_natk k)
    -> equality lib n1 n2 mkc_tnat.
Proof.
  introv e.

  apply equality_in_natk in e; exrepnd; spcast.
  apply equality_in_tnat.
  exists m; dands; spcast; auto.
Qed.

Lemma equality_nat2nat_to_natk2nat {o} :
  forall lib (n f g : @CTerm o),
    member lib n mkc_tnat
    -> equality lib f g nat2nat
    -> equality lib f g (natk2nat n).
Proof.
  introv m e.

  allrw @equality_in_tnat.
  allunfold @equality_of_nat; exrepnd; spcast; GC.

  allrw @equality_in_fun; repnd; dands; eauto 3 with slow.
  { apply type_mkc_natk.
    exists (Z.of_nat k); spcast; auto. }

  introv en.
  apply equality_natk_to_tnat in en; apply e in en; auto.
Qed.
