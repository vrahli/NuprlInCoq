(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export prog.
Require Export cvterm.
Require Export per_props2.


Lemma nuprl_mkc_not {o} :
  forall lib (a b : @CTerm o) eq,
    nuprl lib a b eq
    -> nuprl lib (mkc_not a) (mkc_not b) (fun t t' => forall a a', eq a a' -> False).
Proof.
  introv n.
  apply CL_func.
  unfold per_func.
  exists eq (fun (a a' : CTerm) (e : eq a a') (t t' : @CTerm o) => False); dands.

  - unfold type_family.
    eexists; eexists; eexists; eexists; eexists; eexists;
    dands; auto; spcast; try (fold nuprl).

    unfold mkc_not.
    rw <- @fold_mkc_fun.
    apply computes_to_valc_refl.
    apply iscvalue_mkc_function.

    unfold mkc_not.
    rw <- @fold_mkc_fun.
    apply computes_to_valc_refl.
    apply iscvalue_mkc_function.

    auto.

    introv e.
    allrw @csubst_mk_cv.
    apply CL_approx.
    unfold per_approx.
    eexists; eexists; eexists; eexists; dands; auto; spcast;
    try (rw @mkc_void_eq_mkc_false; rw @mkc_false_eq);
    try (apply @computes_to_valc_refl; apply @iscvalue_mkc_approx).
    introv; split; intro k; repnd; sp; spcast.
    apply not_axiom_approxc_bot in k; sp.

  - sp.
Qed.

Lemma fold_less {o} :
  forall a b c d : @NTerm o,
    oterm (NCan (NCompOp CompOpLess)) [nobnd a, nobnd b, nobnd c, nobnd d]
    = mk_less a b c d.
Proof. sp. Qed.

Lemma mkc_less_than_comp1 {o} :
  forall lib (a b : @CTerm o) n m,
    computes_to_valc lib a (mkc_integer n)
    -> computes_to_valc lib b (mkc_integer m)
    -> (n < m)%Z
    -> computes_to_valc lib (mkc_less_than a b) mkc_true.
Proof.
  introv comp1 comp2 h.
  rw @mkc_less_than_eq.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto.
  pose proof (reduce_to_prinargs_comp
                lib CompOpLess
                x0 x
                [nobnd mk_true, nobnd mk_false]
                (mk_integer n)
                (mk_integer m)) as r.
  repeat (autodimp r hyp).
  { unfold computes_to_value; dands; auto. }
  { unfold iswfpk; eauto 3 with slow. }
  allrw @fold_nobnd.
  allrw @fold_less.
  eapply reduces_to_trans; eauto.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf q; allsimpl.
  unfold compute_step_comp; simpl.
  boolvar; auto; try omega.
Qed.

Lemma mkc_less_than_comp2 {o} :
  forall lib (a b : @CTerm o) n m,
    computes_to_valc lib a (mkc_integer n)
    -> computes_to_valc lib b (mkc_integer m)
    -> (m <= n)%Z
    -> computes_to_valc lib (mkc_less_than a b) mkc_false.
Proof.
  introv comp1 comp2 h.
  rw @mkc_less_than_eq.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto.
  pose proof (reduce_to_prinargs_comp
                lib CompOpLess
                x0 x
                [nobnd mk_true, nobnd mk_false]
                (mk_integer n)
                (mk_integer m)) as r.
  repeat (autodimp r hyp).
  { unfold computes_to_value; dands; auto. }
  { unfold iswfpk; eauto 3 with slow. }
  allrw @fold_nobnd.
  allrw @fold_less.
  eapply reduces_to_trans; eauto.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf q; allsimpl.
  unfold compute_step_comp; simpl.
  boolvar; auto; try omega.
Qed.

Lemma nuprl_mkc_true {o} :
  forall lib, @nuprl o lib
                     mkc_true
                     mkc_true
                     (fun t t' => t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom).
Proof.
  introv.
  apply CL_approx.
  rw @mkc_true_eq.
  unfold per_approx.
  eexists; eexists; eexists; eexists; dands; spcast.
  apply computes_to_valc_refl; apply iscvalue_mkc_approx.
  apply computes_to_valc_refl; apply iscvalue_mkc_approx.
  sp.
  introv; split; sp; spcast.
  apply approxc_refl.
Qed.

Lemma nuprl_computes_left {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    nuprl lib t1 t2 eq
    -> computes_to_valc lib t3 t1
    -> nuprl lib t3 t2 eq.
Proof.
  introv n c.
  apply @nuprl_value_respecting_left with (t1 := t1); auto.
  apply cequivc_sym.
  apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma nuprl_computes_right {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    nuprl lib t1 t2 eq
    -> computes_to_valc lib t3 t2
    -> nuprl lib t1 t3 eq.
Proof.
  introv n c.
  apply @nuprl_value_respecting_right with (t2 := t2); auto.
  apply cequivc_sym.
  apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma nuprl_tnat {o} :
  forall lib,
  @nuprl o
    lib
    mkc_tnat
    mkc_tnat
    (fun (t t' : @CTerm o) =>
       { _ : equality_of_int lib t t'
                             &
                             inhabited
                             (fun _ _ : @CTerm o =>
                                forall u v : @CTerm o,
                                  (forall k : Z,
                                     computes_to_valc lib t (mkc_integer k) ->
                                     if (k <? 0)%Z
                                     then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
                                     else False) -> False)}).
Proof.
  introv.
  rw @mkc_tnat_eq.
  apply CL_set; fold (@nuprl o).
  unfold per_set.
  exists (@equality_of_int o lib).
  exists
    (fun (a a' : @CTerm o)
         (e : equality_of_int lib a a')
         (t t' : @CTerm o) =>
       forall (u v : @CTerm o),
         (forall k,
            computes_to_valc lib a (mkc_integer k)
            -> if (k <? 0)%Z
               then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
               else False)
         -> False);
    dands; auto.

  - unfold type_family.
    eexists; eexists; eexists; eexists; eexists; eexists;
    dands; auto; spcast; try (fold nuprl).

    + apply computes_to_valc_refl; apply iscvalue_mkc_set.

    + apply computes_to_valc_refl; apply iscvalue_mkc_set.

    + apply nuprl_int.

    + introv e.
      allrw @mkcv_le_substc.
      allrw @mkcv_zero_substc.
      allrw @mkc_var_substc.
      allrw @mkc_le_eq.
      unfold equality_of_int in e; exrepnd; spcast.

      apply CL_func.
      unfold per_func.
      exists (fun t t' : @CTerm o =>
                if (k <? 0)%Z
                then t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom
                else False).
      exists (fun (a a' : @CTerm o) (e : if (k <? 0)%Z
                            then a ===>(lib) mkc_axiom # a' ===>(lib) mkc_axiom
                            else False) (t t' : @CTerm o) => False).
      dands; auto.

      * unfold type_family.
        eexists; eexists; eexists; eexists; eexists; eexists;
        dands; auto; spcast; try (fold nuprl).

        unfold mkc_not.
        rw <- @fold_mkc_fun.
        apply computes_to_valc_refl.
        apply iscvalue_mkc_function.

        unfold mkc_not.
        rw <- @fold_mkc_fun.
        apply computes_to_valc_refl.
        apply iscvalue_mkc_function.

        remember ((k <? 0)%Z); symmetry in Heqb; destruct b.

        apply Z.ltb_lt in Heqb.

        pose proof (mkc_less_than_comp1 lib a mkc_zero k 0) as h1; repeat (autodimp h1 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_zero, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        pose proof (mkc_less_than_comp1 lib a' mkc_zero k 0) as h2; repeat (autodimp h2 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_zero, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        apply nuprl_value_respecting_left with (t1 := mkc_true).
        apply nuprl_value_respecting_right with (t2 := mkc_true).
        apply nuprl_mkc_true.
        apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp.
        apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp.

        apply Z.ltb_ge in Heqb.

        pose proof (mkc_less_than_comp2 lib a mkc_zero k 0) as h1; repeat (autodimp h1 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_zero, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        pose proof (mkc_less_than_comp2 lib a' mkc_zero k 0) as h2; repeat (autodimp h2 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_zero, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        apply nuprl_computes_left with (t1 := mkc_false); auto.
        apply nuprl_computes_right with (t2 := mkc_false); auto.
        rw @mkc_false_eq.
        apply CL_approx.
        unfold per_approx.
        eexists; eexists; eexists; eexists; dands; auto; spcast.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        introv; split; intro j; repnd; sp; spcast.
        apply not_axiom_approxc_bot in j; auto.

        introv e; simphyps.
        allrw @csubst_mk_cv.
        rw @mkc_void_eq_mkc_false; rw @mkc_false_eq.
        apply CL_approx.
        unfold per_approx.
        eexists; eexists; eexists; eexists; dands; auto; spcast.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        sp; split; intro j; repnd; sp; spcast.
        apply not_axiom_approxc_bot in j; auto.

      * intros; split; intro j; introv m.

        apply j with (u := a0) (v := a'0); auto.
        introv c.
        pose proof (computes_to_valc_eq lib a (mkc_integer k) (mkc_integer k0)) as e;
          repeat (autodimp e hyp).
        inversion e; subst; GC; sp.

        pose proof (m k) as l; autodimp l hyp.
        apply j in l; sp.

  - introv.
    split; intro k; exrepnd.
    exists v; sp.
    exists e; sp.
Qed.

Lemma tnat_type {o} : forall lib, @type o lib mkc_tnat.
Proof.
  introv.
  unfold type, tequality.
  pose proof @nuprl_tnat as h.
  exists
    (fun (t t' : @CTerm o) =>
       { _ : equality_of_int lib t t'
                             &
                             inhabited
                             (fun _ _ : @CTerm o =>
                                forall u v : @CTerm o,
                                  (forall k : Z,
                                     computes_to_valc lib t (mkc_integer k) ->
                                     if (k <? 0)%Z
                                     then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
                                     else False) -> False)}); sp.
Qed.

Lemma computes_to_valc_tuni {o} :
  forall lib (t : @CTerm o) k,
    (0 <= k)%Z
    -> computes_to_valc lib t (mkc_integer k)
    -> computes_to_valc lib (mkc_tuni t) (mkc_uni (Z.to_nat k)).
Proof.
  introv le c.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto; try (apply isvalue_mk_uni).
  apply reduces_to_trans with (b := mk_tuni (mk_integer k)).
  apply reduces_to_prinarg; auto.
  apply reduces_to_if_step.
  csunf; simpl.
  unfold compute_step_tuni; simpl.
  destruct (Z_le_gt_dec 0 k); auto; omega.
Qed.

Lemma ccomputes_to_valc_tuni {o} :
  forall lib (t : @CTerm o) k,
    (0 <= k)%Z
    -> t ===>(lib) (mkc_integer k)
    -> (mkc_tuni t) ===>(lib) (mkc_uni (Z.to_nat k)).
Proof.
  introv le c.
  spcast.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto; try (apply isvalue_mk_uni).
  apply reduces_to_trans with (b := mk_tuni (mk_integer k)).
  apply reduces_to_prinarg; auto.
  apply reduces_to_if_step.
  csunf; simpl.
  unfold compute_step_tuni; simpl.
  destruct (Z_le_gt_dec 0 k); auto; omega.
Qed.

(*

  We could also have defined this type using 0 < y.
  I used 1 <= y because the proofs will be similar to the ones for tnat.

 *)
Definition mk_tnatp {o} := @mk_set o mk_int nvary (mk_le mk_one (mk_var nvary)).

Lemma isprogram_mk_one {o} :
  @isprogram o mk_one.
Proof.
  repeat constructor; simpl; sp.
Qed.
Hint Immediate isprogram_mk_one.

Lemma isprog_mk_one {o} :
  @isprog o mk_one.
Proof.
  rw @isprog_eq.
  apply isprogram_mk_one.
Qed.
Hint Immediate isprog_mk_one.

Lemma isprog_tnatp {o} : @isprog o mk_tnatp.
Proof.
  rw <- @isprog_set_iff.
  dands; eauto 3 with slow.
  rw @isprog_vars_le; dands; eauto 3 with slow.
Qed.

Definition mkc_tnatp {o} : @CTerm o := exist isprog mk_tnatp isprog_tnatp.

Definition mkc_one {o} : @CTerm o := exist isprog mk_one isprog_mk_one.

Definition mkcv_one {o} (vs : list NVar) : @CVTerm o vs := mk_cv vs mkc_one.

Lemma mkc_tnatp_eq {o} :
  @mkc_tnatp o = mkc_set mkc_int nvary (mkcv_le [nvary] (mkcv_one [nvary]) (mkc_var nvary)).
Proof.
  apply cterm_eq; simpl; sp.
Qed.

Lemma mkcv_one_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_one [v]) = mkc_one.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma nuprl_tnatp {o} :
  forall lib,
  nuprl
    lib
    mkc_tnatp
    mkc_tnatp
    (fun (t t' : @CTerm o) =>
       { _ : equality_of_int lib t t'
                             &
                             inhabited
                             (fun _ _ : @CTerm o =>
                                forall u v : @CTerm o,
                                  (forall k : Z,
                                     computes_to_valc lib t (mkc_integer k) ->
                                     if (k <? 1)%Z
                                     then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
                                     else False) -> False)}).
Proof.
  introv.
  rw @mkc_tnatp_eq.
  apply CL_set; fold (@nuprl o).
  unfold per_set.
  exists (@equality_of_int o lib).
  exists
    (fun (a a' : @CTerm o)
         (e : equality_of_int lib a a')
         (t t' : @CTerm o) =>
       forall (u v : @CTerm o),
         (forall k,
            computes_to_valc lib a (mkc_integer k)
            -> if (k <? 1)%Z
               then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
               else False)
         -> False);
    dands; auto.

  - unfold type_family.
    eexists; eexists; eexists; eexists; eexists; eexists;
    dands; auto; spcast; try (fold nuprl).

    + apply computes_to_valc_refl; apply iscvalue_mkc_set.

    + apply computes_to_valc_refl; apply iscvalue_mkc_set.

    + apply nuprl_int.

    + introv e.
      allrw @mkcv_le_substc.
      allrw @mkcv_one_substc.
      allrw @mkc_var_substc.
      allrw @mkc_le_eq.
      unfold equality_of_int in e; exrepnd; spcast.

      apply CL_func.
      unfold per_func.
      exists (fun t t' : @CTerm o =>
                if (k <? 1)%Z
                then t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom
                else False).
      exists (fun (a a' : @CTerm o) (e : if (k <? 1)%Z
                            then a ===>(lib) mkc_axiom # a' ===>(lib) mkc_axiom
                            else False) (t t' : @CTerm o) => False).
      dands; auto.

      * unfold type_family.
        eexists; eexists; eexists; eexists; eexists; eexists;
        dands; auto; spcast; try (fold nuprl).

        unfold mkc_not.
        rw <- @fold_mkc_fun.
        apply computes_to_valc_refl.
        apply iscvalue_mkc_function.

        unfold mkc_not.
        rw <- @fold_mkc_fun.
        apply computes_to_valc_refl.
        apply iscvalue_mkc_function.

        remember ((k <? 1)%Z); symmetry in Heqb; destruct b.

        apply Z.ltb_lt in Heqb.

        pose proof (mkc_less_than_comp1 lib a mkc_one k 1) as h1; repeat (autodimp h1 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_one, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        pose proof (mkc_less_than_comp1 lib a' mkc_one k 1) as h2; repeat (autodimp h2 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_one, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        apply nuprl_value_respecting_left with (t1 := mkc_true).
        apply nuprl_value_respecting_right with (t2 := mkc_true).
        apply nuprl_mkc_true.
        apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp.
        apply cequivc_sym; apply computes_to_valc_implies_cequivc; sp.

        apply Z.ltb_ge in Heqb.

        pose proof (mkc_less_than_comp2 lib a mkc_one k 1) as h1; repeat (autodimp h1 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_one, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        pose proof (mkc_less_than_comp2 lib a' mkc_one k 1) as h2; repeat (autodimp h2 hyp); try omega.
        unfold computes_to_valc; simpl; unfold mk_zero, mk_nat; simpl.
        apply computes_to_value_isvalue_refl; apply isvalue_mk_integer.

        apply nuprl_computes_left with (t1 := mkc_false); auto.
        apply nuprl_computes_right with (t2 := mkc_false); auto.
        rw @mkc_false_eq.
        apply CL_approx.
        unfold per_approx.
        eexists; eexists; eexists; eexists; dands; auto; spcast.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        introv; split; intro j; repnd; sp; spcast.
        apply not_axiom_approxc_bot in j; auto.

        introv e; simphyps.
        allrw @csubst_mk_cv.
        rw @mkc_void_eq_mkc_false; rw @mkc_false_eq.
        apply CL_approx.
        unfold per_approx.
        eexists; eexists; eexists; eexists; dands; auto; spcast.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        apply computes_to_valc_refl; apply iscvalue_mkc_approx.
        sp; split; intro j; repnd; sp; spcast.
        apply not_axiom_approxc_bot in j; auto.

      * intros; split; intro j; introv m.

        apply j with (u := a0) (v := a'0); auto.
        introv c.
        pose proof (computes_to_valc_eq lib a (mkc_integer k) (mkc_integer k0)) as e;
          repeat (autodimp e hyp).
        inversion e; subst; GC; sp.

        pose proof (m k) as l; autodimp l hyp.
        apply j in l; sp.

  - introv.
    split; intro k; exrepnd.
    exists v; sp.
    exists e; sp.
Qed.

Lemma tnatp_type {o} : forall lib, @type o lib mkc_tnatp.
Proof.
  introv.
  unfold type, tequality.
  pose proof @nuprl_tnatp as h.
  exists
    (fun (t t' : @CTerm o) =>
       { _ : equality_of_int lib t t'
                             &
                             inhabited
                             (fun _ _ : @CTerm o =>
                                forall u v : @CTerm o,
                                  (forall k : Z,
                                     computes_to_valc lib t (mkc_integer k) ->
                                     if (k <? 1)%Z
                                     then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
                                     else False) -> False)}); sp.
Qed.

Definition reducek_pair {o} lib (t1 t2 : @NTerm o) (k : Z) (n : nat) :=
    reduces_in_atmost_k_steps lib t1 (mk_integer k) n
  # reduces_in_atmost_k_steps lib t2 (mk_integer k) n.

Definition equality_of_int_p_2 {o} lib (n m : @NTerm o) :=
  {x : Z # nat , reducek_pair lib n m (fst x) (snd x)}.

Definition equality_of_int_p_2_c {o} lib (n m : @CTerm o) :=
  equality_of_int_p_2 lib (get_cterm n) (get_cterm m).

Lemma equality_of_int_imp1 {o} :
  forall lib (n m : @CTerm o),
    equality_of_int lib n m
    <-> equality_of_int_p_2_c lib n m.
Proof.
  introv; split.
  - introv e.
    unfold equality_of_int in e; exrepnd; spcast.
    allunfold @computes_to_valc; allsimpl.
    allunfold @computes_to_value; repnd.
    allunfold @reduces_to; exrepnd.
    allunfold @reduces_in_atmost_k_steps.
    pose proof (no_change_after_value2 lib
                  (get_cterm n) k1 (mk_integer k) e2 e1 (Peano.max k1 k0)) as h1.
    autodimp h1 hyp; try (apply max_prop1).
    pose proof (no_change_after_value2 lib
                (get_cterm m) k0 (mk_integer k) e4 e0 (Peano.max k1 k0)) as h2.
    autodimp h2 hyp; try (apply max_prop2).
    exists ((k,Peano.max k1 k0)); simpl; sp.
    unfold reducek_pair; sp.
  - introv e.
    unfold equality_of_int.
    unfold equality_of_int_p_2_c, equality_of_int_p_2, reducek_pair in e.
    exrepnd; allsimpl.
    exists x0; dands; spcast;
    unfold computes_to_valc, computes_to_value; simpl;
    dands; try (apply isvalue_mk_integer);
    exists x; auto.
Qed.

Lemma compute_step_dec {o} :
  forall lib (t : @NTerm o),
    {u : NTerm $ compute_step lib t = csuccess u}
    [+]
    !{u : NTerm $ compute_step lib t = csuccess u}.
Proof.
  introv.
  remember (compute_step lib t); destruct c.
  - left.
    exists n; sp.
  - right; intro k; exrepnd; inversion k0.
Qed.

(*
Lemma reduces_in_atmost_k_steps_dec {o} :
  forall lib (pc : dec_consts o) k (t1 t2 : @NTerm o),
    reduces_in_atmost_k_steps lib t1 t2 k [+] !(reduces_in_atmost_k_steps lib t1 t2 k).
Proof.
  induction k; introv.

  - rw @reduces_in_atmost_k_steps_0.
    pose proof (deq_nterm pc t1 t2) as h; sp.

  - rw @reduces_in_atmost_k_steps_S.
    pose proof (compute_step_dec lib t1) as h.
    dorn h.

    + exrepnd.
      pose proof (IHk u t2) as j.
      dorn j.

      * left.
        exists u; sp.

      * right.
        intro c; exrepnd.
        rw h0 in c1; inversion c1; subst; sp.

    + right; intro j; exrepnd.
      apply h.
      exists u; sp.
Qed.
*)

Lemma deq_nterm_int {p} :
  forall (t : @NTerm p) z, {t = mk_integer z} + {t <> mk_integer z}.
Proof.
  introv.
  nterm_ind1 t as [v1|f1 ind|o1 lbt1 Hind] Case; intros.

  - Case "vterm".
    right; intro k; inversion k.

  - Case "sterm".
    right; intro k; inversion k.

  - Case "oterm".
    destruct o1; try (complete (right; intro k; inversion k)).
    destruct c; try (complete (right; intro k; inversion k)).
    destruct lbt1; try (complete (right; intro k; inversion k)).
    assert ({z < z0} + {z > z0} + {z = z0})%Z as h by (apply Z_dec).
    destruct h as [ h | h ]; subst.
    destruct h as [ h | h ]; sp; right; sp; inversion H; omega.
    left; sp.
Qed.

Lemma reduces_in_atmost_k_steps_int_dec {o} :
  forall lib k (t : @NTerm o) z,
    reduces_in_atmost_k_steps lib t (mk_integer z) k
    [+]
    !(reduces_in_atmost_k_steps lib t (mk_integer z) k).
Proof.
  induction k; introv.

  - rw @reduces_in_atmost_k_steps_0.
    pose proof (deq_nterm_int t z) as h; sp.

  - rw @reduces_in_atmost_k_steps_S.
    pose proof (compute_step_dec lib t) as h.
    dorn h.

    + exrepnd.
      pose proof (IHk u z) as j.
      dorn j.

      * left.
        exists u; sp.

      * right.
        intro c; exrepnd.
        rw h0 in c1; inversion c1; subst; sp.

    + right; intro j; exrepnd.
      apply h.
      exists u; sp.
Qed.

Lemma reducek_pair_dec {o} :
  forall lib (t1 t2 : @NTerm o) z n,
    reducek_pair lib t1 t2 z n [+] !(reducek_pair lib t1 t2 z n).
Proof.
  introv.
  unfold reducek_pair.
  pose proof (reduces_in_atmost_k_steps_int_dec lib n t1 z) as h1.
  pose proof (reduces_in_atmost_k_steps_int_dec lib n t2 z) as h2.
  dorn h1; dorn h2.
  - left; sp.
  - right; sp.
  - right; sp.
  - right; sp.
Qed.


(*

  The following is an adaptation of:
     http://coq.inria.fr/stdlib/Coq.Logic.ConstructiveEpsilon.html
  This is required to prove equality_of_int_imp_t without using
  the indefinite_description axiom.

*)

Inductive before_witness (P : Z -> nat -> Prop) (k : nat) : Prop :=
  | stop_pos : forall (z n : nat), k = z + n -> P (Z.of_nat z) n -> before_witness P k
  | stop_neg : forall z n, k = z + n -> P (Z.opp (Z.of_nat z)) n -> before_witness P k
  | next : before_witness P (S k) -> before_witness P k.

Fixpoint O_witness
         (P : Z -> nat -> Prop)
         (k : nat) : before_witness P k -> before_witness P 0 :=
  match k return (before_witness P k -> before_witness P 0) with
    | 0 => fun b => b
    | S n => fun b => O_witness P n (next P n b)
  end.

Definition inv_before_witness :
  forall (P : Z -> nat -> Prop) (k : nat),
    before_witness P k
    -> (forall z n : nat, k = z + n -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n)
    -> before_witness P (S k) :=
  fun P k b =>
    match b
          in before_witness _ _
          return (forall z n, k = z + n -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n)
                 -> before_witness P (S k) with
      | stop_pos z n e p => fun f => match fst (f z n e) p with end
      | stop_neg z n e p => fun f => match snd (f z n e) p with end
      | next b => fun _ => b
    end.

Lemma leS:
  forall n m : nat, n <= S m -> n <= m [+] n = S m.
Proof.
  introv; revert n.
  induction m; simpl; introv e.
  - destruct n; sp.
    destruct n; sp.
    provefalse.
    inversion e as [|x h].
    inversion h.
  - apply leb_correct in e.
    destruct n; allsimpl.
    + left; omega.
    + apply leb_complete in e.
      apply IHm in e; dorn e.
      left; omega.
      right; omega.
Qed.

(* This is the crux of linear_search *)
Lemma P_search :
  forall (P : Z -> nat -> Prop)
         (dec : forall z n, P z n [+] !P z n)
         (k : nat),
    {x : Z # nat & P (fst x) (snd x)}
    [+]
    (forall z n : nat, k = (z + n)%nat -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n).
Proof.
  intros P dec k.

  assert (forall k z,
            {x : Z # nat & P (fst x) (snd x)}
              [+]
              (forall n : nat, n <= k -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n)) as hyp1.
  clear k.
  introv.
  induction k.
  pose proof (dec (Z.of_nat z) 0) as h.
  dorn h.
  left; exists (Z.of_nat z,0); simpl; sp.
  pose proof (dec (Z.opp (Z.of_nat z)) 0) as j.
  dorn j.
  left; exists (Z.opp (Z.of_nat z),0); simpl; sp.
  right; introv e.
  assert (n = 0) by omega; subst; simpl; sp.
  dorn IHk.
  left; auto.
  pose proof (dec (Z.of_nat z) (S k)) as h.
  dorn h.
  left; exists (Z.of_nat z,S k); simpl; sp.
  pose proof (dec (Z.opp (Z.of_nat z)) (S k)) as j.
  dorn j.
  left; exists (Z.opp (Z.of_nat z),S k); simpl; sp.
  right; introv e; simpl.
  apply leS in e.
  dorn e.
  apply IHk in e; sp.
  subst; sp.

  assert (forall k n,
            {x : Z # nat & P (fst x) (snd x)}
              [+]
              (forall z : nat, z <= k -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n)) as hyp2.
  clear k.
  introv.
  induction k.
  pose proof (dec 0%Z n) as h.
  dorn h.
  left; exists (0%Z,n); simpl; sp.
  right; introv e.
  assert (z = 0) by omega; subst; simpl; sp.
  dorn IHk.
  left; auto.
  pose proof (dec (Z.of_nat (S k)) n) as h.
  dorn h.
  left; exists (Z.of_nat (S k),n); simpl; sp.
  pose proof (dec (Z.opp (Z.of_nat (S k))) n) as j.
  dorn j.
  left; exists (Z.opp (Z.of_nat (S k)),n); simpl; sp.
  right; introv e; simpl.
  apply leS in e.
  dorn e.
  apply IHk in e; sp.
  subst; sp.

  assert ({x : Z # nat & P (fst x) (snd x)}
            [+]
            (forall z n : nat, z <= k -> n <= k -> ~ P (Z.of_nat z) n # ~ P (Z.opp (Z.of_nat z)) n)) as hyp.
  induction k.
  pose proof (dec 0%Z 0) as h.
  dorn h.
  left; exists (0%Z,0); simpl; sp.
  right; introv e1 e2.
  assert (z = 0) by omega; assert (n = 0) by omega; subst; simpl; sp.
  dorn IHk.
  left; auto.
  pose proof (hyp1 (S k) (S k)) as h1.
  dorn h1.
  left; auto.
  pose proof (hyp2 (S k) (S k)) as h2.
  dorn h2.
  left; auto.
  right; introv e1 e2.
  apply leS in e1.
  apply leS in e2.
  dorn e1; dorn e2; subst.
  apply IHk; auto.
  apply h2; auto.
  apply h1; auto.
  apply h1; sp.

  dorn hyp.
  left; auto.
  right.
  introv e; subst.
  apply hyp; omega.
Qed.

Fixpoint linear_search
      (P : Z -> nat -> Prop)
      (dec : forall z n, P z n [+] !P z n)
      (k : nat)
      (b : before_witness P k) : {x : Z # nat | P (fst x) (snd x)} :=
  match P_search P dec k with
    | inl p => p
    | inr a => linear_search P dec (S k) (inv_before_witness P k b a)
  end.

Definition constructive_indefinite_ground_description_nat {o}
           lib (t1 t2 : @CTerm o) :
  equality_of_int_p_2_c lib t1 t2
  -> {x : Z # nat | reducek_pair lib (get_cterm t1) (get_cterm t2) (fst x) (snd x)}.
Proof.
  introv pex.
  apply linear_search with (k := 0).
  apply reducek_pair_dec; auto.
  unfold equality_of_int_p_2_c, equality_of_int_p_2 in pex; auto.
  exrepnd; allsimpl.
  apply O_witness with (k := Z.abs_nat x0 + x).
  pose proof (Zabs.Zabs_dec x0) as h.
  dorn h.
  - apply stop_pos with (z := Z.abs_nat x0) (n := x); auto.
    rw h in pex0.
    rw Znat.Zabs2Nat.id_abs; auto.
  - apply stop_neg with (z := Z.abs_nat x0) (n := x); auto.
    rw h in pex0.
    rw Znat.Zabs2Nat.id_abs; auto.
Qed.

(*

   Thanks to constructive_indefinite_ground_description_nat,
   the following proof does not need the indefinite_description axiom

 *)

Definition equality_of_int_t {o} lib (n m : @CTerm o) :=
  {k : Z | n ===>(lib) (mkc_integer k)
         # m ===>(lib) (mkc_integer k)}.

Lemma equality_of_int_imp_t {o} :
  forall lib (n m : @CTerm o),
    equality_of_int lib n m
    -> equality_of_int_t lib n m.
Proof.
  introv e.
  apply equality_of_int_imp1 in e.
  apply constructive_indefinite_ground_description_nat in e; auto.
  exrepnd; allsimpl.
  unfold equality_of_int_t.
  unfold reducek_pair in e0; repnd.
  exists x0; dands; spcast;
  unfold computes_to_valc, computes_to_value; simpl;
  dands; try (apply isvalue_mk_integer);
  exists x; auto.
Qed.

(*
Here is the alternative that uses the indefinite_description axiom.

Axiom indefinite_description :
  forall (A : Type) (P : A -> Prop),
    ex P -> sig P.

Lemma equality_of_int_imp_t :
  forall n m,
    equality_of_int n m
    -> equality_of_int_t n m.
Proof.
  introv e.
  unfold equality_of_int in e.
  unfold equality_of_int_t.
  apply indefinite_description; auto.
Qed.
*)

Definition equality_of_int_tt {o} lib (n m : @CTerm o) :=
  {k : Z & computes_to_valc lib n (mkc_integer k)
         # computes_to_valc lib m (mkc_integer k)}.

Lemma equality_of_int_imp_tt {o} :
  forall lib (n m : @CTerm o),
    equality_of_int lib n m
    -> equality_of_int_tt lib n m.
Proof.
  introv e.
  apply equality_of_int_imp1 in e.
  apply constructive_indefinite_ground_description_nat in e; auto.
  exrepnd; allsimpl.
  unfold equality_of_int_tt.
  unfold reducek_pair in e0; repnd.
  exists x0; dands; spcast;
  unfold computes_to_valc, computes_to_value; simpl;
  dands; try (apply isvalue_mk_integer);
  exists x; auto.
Qed.

Lemma tuni_fun {o} :
  forall lib (v : NVar),
    @type o lib (mkc_function mkc_tnat v (mkcv_tuni [v] (mkc_var v))).
Proof.
  introv.
  unfold type, tequality.
  eexists.
  apply CL_func.
  unfold per_func.

  exists
    (fun t t' : @CTerm o =>
       { _ : equality_of_int lib t t'
                             &
                             inhabited
                             (fun _ _ : @CTerm o =>
                                forall u v : @CTerm o,
                                  (forall k : Z,
                                     computes_to_valc lib t (mkc_integer k) ->
                                     if (k <? 0)%Z
                                     then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
                                     else False) -> False)}).

  exists (fun (a a' : @CTerm o)
              (e : { _ : equality_of_int lib a a'
                                         &
                                         inhabited
                                         (fun _ _ : @CTerm o =>
                                            forall u v : @CTerm o,
                                              (forall k : Z,
                                                 computes_to_valc lib a (mkc_integer k) ->
                                                 if (k <? 0)%Z
                                                 then u ===>(lib) mkc_axiom # v ===>(lib) mkc_axiom
                                                 else False) -> False)})
              (t t' : @CTerm o) =>
            (exists eqa, close lib (univi lib (Z.to_nat (projT1 (equality_of_int_imp_t lib a a' (projT1 e)))))
                               t t' eqa)).

  dands; auto.

  - unfold type_family.
    eexists; eexists; eexists; eexists; eexists; eexists;
    dands; auto; spcast; try (fold nuprl).
    apply computes_to_valc_refl; apply iscvalue_mkc_function.
    apply computes_to_valc_refl; apply iscvalue_mkc_function.
    apply nuprl_tnat.
    introv; simpl in e; exrepnd.
    allrw @mkcv_tuni_substc.
    allrw @mkc_var_substc.
    unfold equality_of_int in v0; exrepnd.
    unfold inhabited in e0; exrepnd.

    pose proof (Z_lt_le_dec k 0) as oo; dorn oo.

    + pose proof (e1 mkc_axiom mkc_axiom) as h.

      autodimp h hyp; tcsp.
      introv c.
      spcast.
      pose proof (computes_to_valc_eq lib a (mkc_integer k) (mkc_integer k0)) as e;
        repeat (autodimp e hyp).
      symmetry in e; inversion e; subst; GC.

      remember ((k <? 0)%Z); symmetry in Heqb; destruct b.
      sp; spcast; apply @computes_to_value_isvalue_refl; simpl; sp.
      apply Z.ltb_ge in Heqb; omega.

    + pose proof (ccomputes_to_valc_tuni lib a k) as c1; repeat (autodimp c1 hyp); try omega.
      pose proof (ccomputes_to_valc_tuni lib a' k) as c2; repeat (autodimp c2 hyp); try omega.
      destruct c1 as [c1].
      destruct c2 as [c2].
      apply nuprl_computes_left with (t1 := mkc_uni (Z.to_nat k)); auto.
      apply nuprl_computes_right with (t2 := mkc_uni (Z.to_nat k)); auto.

      remember (Z.to_nat k) as m.
      apply CL_init.

      exists (S m).
      simpl; left; dands.
      spcast; apply computes_to_value_isvalue_refl; simpl; apply isvalue_mk_uni.
      spcast; apply computes_to_value_isvalue_refl; simpl; apply isvalue_mk_uni.

      introv.

      remember (equality_of_int_imp_t lib a a'
                 (ex_intro
                    (fun k0 : Z =>
                     a ===>(lib) (mkc_integer k0) # a' ===>(lib) (mkc_integer k0))
                    k (v0, v1))); clear Heqe.
      unfold equality_of_int_t in e; exrepnd; simpl.
      spcast.

      pose proof (computes_to_valc_eq lib a (mkc_integer k) (mkc_integer k0)) as e.
      repeat (autodimp e hyp); inversion e; subst; GC.
      sp.

  - introv.
    apply t_iff_refl.
Qed.

Lemma computes_to_valc_implies_hasvaluec {o} :
  forall lib (a b : @CTerm o), computes_to_valc lib a b -> hasvaluec lib a.
Proof.
  introv c.
  unfold computes_to_valc in c.
  unfold hasvaluec, hasvalue.
  exists (get_cterm b); auto.
Qed.

Lemma types_converge {o} :
  forall lib (t : @CTerm o), type lib t -> chaltsc lib t.
Proof.
  introv n.
  unfold type, tequality, nuprl in n; exrepnd.
  induction n0
    as [ h | h | h | h | h
         | h | h | h | h | h
         | h | h | h | h | h
         | h | h | h | h | h
         | h | h | h | h | h
         | h | h | h | h | h ];
    allunfold_per; uncast; allapply @computes_to_valc_implies_hasvaluec;
    try (complete (spcast; auto)).
  inversion h as [i u].
  rw @univi_exists_iff in u; exrepnd.
  spcast.
  apply computes_to_valc_implies_hasvaluec in u2; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
