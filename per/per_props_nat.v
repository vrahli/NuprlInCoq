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


  Websites : http://nuprl.org/html/verification/
             http://nuprl.org/html/Nuprl2Coq
             https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli
           Abhishek Anand

*)

Require Export alphaeq5.
Require Export cvterm.
Require Export nat_defs.
Require Export cequiv_props4.
Require Export per_props_set.
Require Export per_props_false.
Require Export per_props_product.
Require Export per_props_not.
Require Export types_converge.

(*Require Export per_props_union.*)

(*Require Export list.  (* ??? *)*)


Lemma dest_nuprl_int {o} :
  forall (lib : @library o) eq,
    nuprl lib mkc_int mkc_int eq
    -> per_bar (per_int nuprl) lib mkc_int mkc_int eq.
Proof.
  introv cl.
  eapply dest_close_per_int_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
  unfold per_int_bar in *; exrepnd.
  exists bar (equality_of_int_bar_lib_per lib).
  dands; auto.

  {
    introv br ext; introv.
    unfold per_int; dands; spcast; eauto 3 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym;apply per_bar_eq_equality_of_int_bar_lib_per.
  }
Qed.

Lemma dest_nuprl_int2 {o} :
  forall lib (eq : per(o)),
    nuprl lib mkc_int mkc_int eq
    -> eq <=2=> (equality_of_int_bar lib).
Proof.
  introv u.
  apply dest_nuprl_int in u.
  unfold per_bar in u; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply (per_bar_eq_equality_of_int_bar_lib_per _ bar)].
  apply implies_eq_term_equals_per_bar_eq.
  apply all_in_bar_ext_intersect_bars_same; simpl; auto.
  introv br ext; introv.
  pose proof (u0 _ br _ ext x) as u0; simpl in *.
  unfold per_int in *; exrepnd; spcast; auto.
Qed.


Lemma nuprl_int {p} :
  forall lib, @nuprl p lib mkc_int mkc_int (equality_of_int_bar lib).
Proof.
  sp.
  apply CL_int.
  unfold per_int; sp; spcast; try computes_to_value_refl.
Qed.
Hint Resolve nuprl_int : slow.

Lemma equality_of_int_xxx {o} :
  forall lib, @close o univ lib mkc_int mkc_int (equality_of_int_bar lib).
Proof.
  apply nuprl_int.
Qed.
Hint Resolve equality_of_int_xxx : slow.

Lemma equality_of_int_bar_same_nat {o} :
  forall (lib : @library o) n,
    equality_of_int_bar lib (mkc_nat n) (mkc_nat n).
Proof.
  introv; exists (trivial_bar lib).
  apply in_ext_implies_all_in_bar_trivial_bar.
  introv x.
  exists (Z_of_nat n); sp;
  unfold mkc_nat, mkc_integer, isprog_mk_nat, isprog_mk_integer, mk_nat;
    spcast; computes_to_value_refl.
Qed.
Hint Resolve equality_of_int_bar_same_nat : slow.

Lemma nat_in_int {p} : forall lib (n : nat), @member p lib (mkc_nat n) mkc_int.
Proof.
  unfold member, equality; sp.
  exists (@equality_of_int_bar p lib).
  dands; eauto 3 with slow.
Qed.

Lemma equality_in_int {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_int <=> equality_of_int_bar lib t1 t2.
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_int2 in e1.
    apply e1 in e0; auto.

  - exists (equality_of_int_bar lib); dands; auto; eauto 3 with slow.
Qed.

Lemma hasvaluec_mkc_less {o} :
  forall lib (a b c d : @CTerm o),
    hasvaluec lib (mkc_less a b c d)
    -> {k1 : Z
        & {k2 : Z
        & reduces_toc lib a (mkc_integer k1)
        # reduces_toc lib b (mkc_integer k2)
        # (((k1 < k2)%Z # hasvaluec lib c)
           [+]
           ((k2 <= k1)%Z # hasvaluec lib d)
          )}}.
Proof.
  introv hv.
  destruct_cterms; allsimpl.
  allunfold @hasvaluec; allsimpl.
  allunfold @reduces_toc; allsimpl.
  apply hasvalue_mk_less in hv; eauto 3 with slow.
Qed.

Lemma equality_in_less {o} :
  forall lib (u v a b c d : @CTerm o),
    equality lib u v (mkc_less a b c d)
    <=>
    all_in_ex_bar
      lib
      (fun lib =>
         {ka , kb : Z
         , a ===>(lib) (mkc_integer ka)
         # b ===>(lib) (mkc_integer kb)
         # (
             ((ka < kb)%Z # equality lib u v c)
             {+}
             ((kb <= ka)%Z # equality lib u v d)
           )}).
Proof.
  introv.

  split; intro k; exrepnd.

  - applydup @inhabited_implies_tequality in k.
    apply types_converge in k0.

XXXXXX
    spcast.
    apply hasvaluec_mkc_less in k0.
    exrepnd.

    exists k1 k0; dands; spcast; eauto with slow;
    try (complete (apply computes_to_valc_iff_reduces_toc; dands; eauto with slow)).

    assert (cequivc lib
                    (mkc_less a b c d)
                    (mkc_less (mkc_integer k1) (mkc_integer k0) c d)) as c1.
    { apply reduces_toc_implies_cequivc.
      destruct_cterms; allunfold @reduces_toc; allunfold @computes_to_valc; allsimpl.
      apply reduce_to_prinargs_comp; eauto with slow.
      allunfold @computes_to_value; sp; eauto with slow. }

    repndors; repnd.

    + left; dands; auto.

      assert (cequivc lib
                      (mkc_less (mkc_integer k1) (mkc_integer k0) c d)
                      c) as c2.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      rwg c2.
      rwg c1; auto.

    + right; dands; auto.

      assert (cequivc lib
                      (mkc_less (mkc_integer k1) (mkc_integer k0) c d)
                      d) as c2.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      rwg c2.
      rwg c1; auto.

  - spcast.
    assert (cequivc lib
                    (mkc_less a b c d)
                    (mkc_less (mkc_integer ka) (mkc_integer kb) c d)) as c1.
    { apply reduces_toc_implies_cequivc.
      destruct_cterms; allunfold @reduces_toc; allunfold @computes_to_valc; allsimpl.
      apply reduce_to_prinargs_comp; eauto with slow. }

    rwg c1.

    repndors; repnd.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      c) as c2.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c2; auto.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      d) as c2.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c2; auto.
Qed.

Lemma equality_in_true {o} :
  forall lib (u v : @CTerm o),
    equality lib u v mkc_true
    <=>
    (u ===>(lib) mkc_axiom
     # v ===>(lib) mkc_axiom).
Proof.
  introv.
  rw @mkc_true_eq.
  rw <- @equality_in_approx; split; intro k; dands; repnd; spcast; auto.
  unfold approxc; simpl.
  apply approx_decomp_axiom.
Qed.

Lemma equality_in_less_than {o} :
  forall lib (u v a b : @CTerm o),
    equality lib u v (mkc_less_than a b)
    <=>
    {ka : Z
     , {kb : Z
        , u ===>(lib) mkc_axiom
        # v ===>(lib) mkc_axiom
        # a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # (ka < kb)%Z}}.
Proof.
  introv.
  rw @mkc_less_than_eq.
  rw @equality_in_less.
  split; intro k; exrepnd; spcast.
  - repndors; repnd.
    + apply equality_in_true in k1; repnd; spcast.
      exists ka kb; dands; spcast; auto.
    + apply equality_in_false in k1; sp.
  - exists ka kb; dands; spcast; auto.
    left; dands; auto.
    apply equality_in_true; dands; spcast; auto.
Qed.

Lemma inhabited_less_than {o} :
  forall lib (a b : @CTerm o),
    inhabited_type lib (mkc_less_than a b)
    <=>
    {ka : Z
     , {kb : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # (ka < kb)%Z}}.
Proof.
  introv.
  unfold inhabited_type; split; intro k; exrepnd; spcast.
  - rw @equality_in_less_than in k0; exrepnd; spcast.
    exists ka kb; dands; spcast; auto.
  - exists (@mkc_axiom o).
    apply equality_in_less_than.
    exists ka kb; dands; spcast; auto;
    apply computes_to_valc_refl; eauto with slow.
Qed.

Lemma tequality_mkc_less_aux {o} :
  forall lib (a b c d e f g h : @CTerm o) ka kb ke kf,
    computes_to_valc lib a (mkc_integer ka)
    -> computes_to_valc lib b (mkc_integer kb)
    -> computes_to_valc lib e (mkc_integer ke)
    -> computes_to_valc lib f (mkc_integer kf)
    -> (tequality lib (mkc_less a b c d) (mkc_less e f g h)
        <=>
        (
          ((ka < kb)%Z # (ke < kf)%Z # tequality lib c g)
          [+]
          ((kb <= ka)%Z # (kf <= ke)%Z # tequality lib d h)
          [+]
          ((ka < kb)%Z # (kf <= ke)%Z # tequality lib c h)
          [+]
          ((kb <= ka)%Z # (ke < kf)%Z # tequality lib d g)
        )
       ).
Proof.
  introv ca cb ce cf.

  assert (cequivc lib
                  (mkc_less a b c d)
                  (mkc_less (mkc_integer ka) (mkc_integer kb) c d)) as c1.
  { apply reduces_toc_implies_cequivc.
    destruct_cterms; allunfold @reduces_toc; allunfold @computes_to_valc; allsimpl.
    apply reduce_to_prinargs_comp; eauto with slow. }

  assert (cequivc lib
                  (mkc_less e f g h)
                  (mkc_less (mkc_integer ke) (mkc_integer kf) g h)) as c2.
  { apply reduces_toc_implies_cequivc.
    destruct_cterms; allunfold @reduces_toc; allunfold @computes_to_valc; allsimpl.
    apply reduce_to_prinargs_comp; eauto with slow. }

  split; intro k; repnd.

  - destruct (Z_lt_ge_dec ka kb); destruct (Z_lt_ge_dec ke kf).

    + left; dands; auto.

      assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      c) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      g) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      apply cequivc_sym in c3.
      apply cequivc_sym in c4.
      rwg c3.
      rwg c4.
      rwg c1.
      rwg c2; auto.

    + right; right; left; dands; auto; try omega.

      assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      c) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      h) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      apply cequivc_sym in c3.
      apply cequivc_sym in c4.
      rwg c3.
      rwg c4.
      rwg c1.
      rwg c2; auto.

    + right; right; right; dands; auto; try omega.

      assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      d) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      g) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      apply cequivc_sym in c3.
      apply cequivc_sym in c4.
      rwg c3.
      rwg c4.
      rwg c1.
      rwg c2; auto.

    + right; left; dands; auto; try omega.

      assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      d) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      h) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      apply cequivc_sym in c1.
      apply cequivc_sym in c2.
      apply cequivc_sym in c3.
      apply cequivc_sym in c4.
      rwg c3.
      rwg c4.
      rwg c1.
      rwg c2; auto.

  - rwg c1.
    rwg c2.
    clear c1 c2 ca cb ce cf.
    repndors; exrepnd.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      c) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      g) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c3.
      rwg c4; auto.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      d) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      h) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c3.
      rwg c4; auto.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      c) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      h) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c3.
      rwg c4; auto.

    + assert (cequivc lib
                      (mkc_less (mkc_integer ka) (mkc_integer kb) c d)
                      d) as c3.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      assert (cequivc lib
                      (mkc_less (mkc_integer ke) (mkc_integer kf) g h)
                      g) as c4.
      { apply reduces_toc_implies_cequivc.
        destruct_cterms; unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl.
        dcwf h; simpl.
        unfold compute_step_comp; simpl; boolvar; tcsp; try omega. }

      rwg c3.
      rwg c4; auto.
Qed.

Lemma tequality_mkc_less {o} :
  forall lib (a b c d e f g h : @CTerm o),
    tequality lib (mkc_less a b c d) (mkc_less e f g h)
    <=>
    {ka : Z
     , {kb : Z
     , {ke : Z
     , {kf : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # e ===>(lib) (mkc_integer ke)
        # f ===>(lib) (mkc_integer kf)
        # (
            ((ka < kb)%Z # (ke < kf)%Z # tequality lib c g)
            {+}
            ((kb <= ka)%Z # (kf <= ke)%Z # tequality lib d h)
            {+}
            ((ka < kb)%Z # (kf <= ke)%Z # tequality lib c h)
            {+}
            ((kb <= ka)%Z # (ke < kf)%Z # tequality lib d g)
          )}}}}.
Proof.
  introv.

  split; intro k; exrepnd.

  - applydup @tequality_refl in k.
    applydup @tequality_sym in k.
    apply tequality_refl in k1.
    allrw @fold_type.
    apply types_converge in k0.
    apply types_converge in k1.
    spcast.

    apply hasvaluec_mkc_less in k0.
    apply hasvaluec_mkc_less in k1.
    exrepnd.

    exists k6 k0 k2 k1; dands; spcast; eauto with slow;
    try (complete (apply computes_to_valc_iff_reduces_toc; dands; eauto with slow)).

    pose proof (tequality_mkc_less_aux
                  lib a b c d e f g h k6 k0 k2 k1) as p.
    repeat (autodimp p hyp);
    try (complete (apply computes_to_valc_iff_reduces_toc; dands; eauto with slow)).
    apply p in k; sp.

  - pose proof (tequality_mkc_less_aux
                  lib a b c d e f g h ka kb ke kf) as p.
    spcast.
    repeat (autodimp p hyp).
    apply p.

    destruct (Z_lt_ge_dec ka kb); destruct (Z_lt_ge_dec ke kf).

    + left; dands; auto.
      repndors; repnd; try omega; auto.

    + right; right; left; dands; auto; try omega.
      repndors; repnd; try omega; auto.

    + right; right; right; dands; auto; try omega.
      repndors; repnd; try omega; auto.

    + right; left; dands; auto; try omega.
      repndors; repnd; try omega; auto.
Qed.

Lemma true_not_equal_to_false {o} :
  forall (lib : @library o),
    !tequality lib mkc_true mkc_false.
Proof.
  introv teq.
  unfold tequality, nuprl in teq; exrepnd.
  inversion teq0; subst; try not_univ.
  - duniv j h.
    allrw @univi_exists_iff; exrepd; spcast; repeat computes_to_value_isvalue.
  - allunfold @per_approx; exrepnd; spcast; repeat computes_to_value_isvalue.
    match goal with
      | [ H : computes_to_valc ?a ?b ?c |- _ ] => rename H into k
    end.

    apply @computes_to_valc_isvalue_eq in k; try (apply iscvalue_mkc_true).
    allrw @mkc_true_eq.
    allrw @mkc_false_eq.
    allapply @mkc_approx_eq; repnd; subst.

    match goal with
      | [ H : _ <=> _ |- _ ] => rename H into h
    end.
    destruct h.
    destruct c as [k]; spcast.

    { unfold approxc; simpl.
      apply approx_decomp_axiom. }

    apply not_axiom_approxc_bot in k; sp.
Qed.

Lemma type_mkc_true {o} :
  forall (lib : @library o), type lib mkc_true.
Proof.
  introv; rw @mkc_true_eq.
  apply tequality_mkc_approx; sp.
Qed.

Lemma tequality_mkc_less_than {o} :
  forall lib (a b c d : @CTerm o),
    tequality lib (mkc_less_than a b) (mkc_less_than c d)
    <=>
    {ka : Z
     , {kb : Z
     , {kc : Z
     , {kd : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # c ===>(lib) (mkc_integer kc)
        # d ===>(lib) (mkc_integer kd)
        # (
            ((ka < kb)%Z # (kc < kd)%Z)
            {+}
            ((kb <= ka)%Z # (kd <= kc)%Z)
          )}}}}.
Proof.
  introv.
  allrw @mkc_less_than_eq.
  rw (tequality_mkc_less
        lib a b mkc_true mkc_false c d mkc_true mkc_false).

  split; intro k; exrepnd.

  - exists ka kb ke kf; dands; auto.
    repndors; repnd; tcsp.

    + apply true_not_equal_to_false in k1; sp.

    + apply tequality_sym in k1.
      apply true_not_equal_to_false in k1; sp.

  - exists ka kb kc kd; dands; auto.
    repndors; repnd; tcsp.

    left; sp.
    apply type_mkc_true.
Qed.

Lemma equality_in_le {o} :
  forall lib (u v a b : @CTerm o),
    equality lib u v (mkc_le a b)
    <=>
    {ka : Z
     , {kb : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # (ka <= kb)%Z}}.
Proof.
  introv.
  rw @mkc_le_eq.
  rw @equality_in_not.
  rw @tequality_mkc_less_than.
  rw @inhabited_less_than.
  split; intro k; exrepnd; spcast; dands.
  - repeat computes_to_eqval.
    exists kb ka; dands; spcast; auto.
    repndors; repnd; tcsp.
    destruct k.
    exists ka kb; dands; spcast; auto.
  - exists kb ka kb ka; dands; spcast; auto.
  - intro h; exrepnd; spcast.
    repeat computes_to_eqval.
    omega.
Qed.

Lemma inhabited_le {o} :
  forall lib (a b : @CTerm o),
    inhabited_type lib (mkc_le a b)
    <=>
    {ka : Z
     , {kb : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # (ka <= kb)%Z}}.
Proof.
  introv.
  unfold inhabited_type; split; intro k; exrepnd; spcast.
  - apply equality_in_le in k0; exrepnd; spcast.
    exists ka kb; dands; spcast; auto.
  - exists (@mkc_axiom o).
    apply equality_in_le.
    exists ka kb; dands; spcast; auto.
Qed.

Lemma tequality_mkc_le {o} :
  forall lib (a b c d : @CTerm o),
    tequality lib (mkc_le a b) (mkc_le c d)
    <=>
    {ka : Z
     , {kb : Z
     , {kc : Z
     , {kd : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # c ===>(lib) (mkc_integer kc)
        # d ===>(lib) (mkc_integer kd)
        # (
            ((ka <= kb)%Z # (kc <= kd)%Z)
            {+}
            ((kb < ka)%Z # (kd < kc)%Z)
          )}}}}.
Proof.
  introv.
  allrw @mkc_le_eq.
  rw @tequality_not.
  rw @tequality_mkc_less_than.

  split; intro k; exrepnd.

  - exists kb ka kd kc; dands; auto.
    repndors; repnd; tcsp.

  - exists kb ka kd kc; dands; auto.
    repndors; repnd; tcsp.
Qed.


Hint Resolve computes_to_valc_refl : slow.

Lemma tequality_int {p} : forall lib, @tequality p lib mkc_int mkc_int.
Proof.
  introv.
  exists (@equality_of_int p lib).
  apply CL_int; split; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve tequality_int : slow.

Hint Rewrite @mkcv_le_substc   : slow.
Hint Rewrite @substc_mkcv_zero : slow.

Lemma tnat_type {o} : forall lib, @type o lib mkc_tnat.
Proof.
  introv.
  rw @mkc_tnat_eq.
  apply tequality_set; dands; eauto 3 with slow.
  introv ea.
  autorewrite with slow.
  apply tequality_mkc_le.
  apply equality_in_int in ea.
  unfold equality_of_int in ea; exrepnd; spcast.
  exists 0%Z k 0%Z k.
  rw @mkc_zero_eq; rw @mkc_nat_eq; simpl.
  dands; spcast; auto; eauto 3 with slow.
  destruct (Z_lt_le_dec k 0); tcsp.
Qed.

(*

  We could also have defined this type using 0 < y.
  I used 1 <= y because the proofs will be similar to the ones for tnat.

 *)
Definition mk_tnatp {o} := @mk_set o mk_int nvary (mk_le mk_one (mk_var nvary)).

Lemma isprog_tnatp {o} : @isprog o mk_tnatp.
Proof.
  rw <- @isprog_set_iff.
  dands; eauto 3 with slow.
Qed.

Definition mkc_tnatp {o} : @CTerm o := exist isprog mk_tnatp isprog_tnatp.

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

(*
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
*)

Lemma mkc_one_eq {o} :
  @mkc_one o = mkc_nat 1.
Proof.
  apply cterm_eq; simpl; auto.
Qed.

Lemma tnatp_type {o} : forall lib, @type o lib mkc_tnatp.
Proof.
  introv.
  rw @mkc_tnatp_eq.
  apply tequality_set; dands; eauto 3 with slow.
  introv ea.
  autorewrite with slow.
  apply tequality_mkc_le.
  apply equality_in_int in ea.
  unfold equality_of_int in ea; exrepnd; spcast.
  exists 1%Z k 1%Z k.
  rw @mkc_one_eq; rw @mkc_nat_eq; simpl.
  dands; spcast; auto; eauto 3 with slow.
  destruct (Z_lt_le_dec k 1); tcsp.
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
      | stop_pos _ _ z n e p => fun f => match fst (f z n e) p with end
      | stop_neg _ _ z n e p => fun f => match snd (f z n e) p with end
      | next _ _ b => fun _ => b
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
      (b : before_witness P k) : {x : Z # nat & P (fst x) (snd x)} :=
  match P_search P dec k with
    | inl p => p
    | inr a => linear_search P dec (S k) (inv_before_witness P k b a)
  end.

Definition constructive_indefinite_ground_description_nat {o}
           lib (t1 t2 : @CTerm o) :
  equality_of_int_p_2_c lib t1 t2
  -> {x : Z # nat & reducek_pair lib (get_cterm t1) (get_cterm t2) (fst x) (snd x)}.
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

Lemma tequality_mkc_natk {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib (mkc_natk t1) (mkc_natk t2)
    <=> {k1 : Z , {k2 : Z
         , t1 ===>(lib) (mkc_integer k1)
         # t2 ===>(lib) (mkc_integer k2)
         # (forall (k : Z), (0 <= k)%Z -> ((k < k1)%Z # (k < k2)%Z){+}(k1 <= k)%Z # (k2 <= k)%Z) }}.
Proof.
  introv.
  allrw @mkc_natk_eq.
  allrw @tequality_set.

  split; intro k; repnd.

  - clear k0.

    assert (forall a a' : CTerm,
              equality lib a a' mkc_int
              -> tequality
                   lib
                   (mkc_prod (mkc_le mkc_zero a) (mkc_less_than a t1))
                   (mkc_prod (mkc_le mkc_zero a') (mkc_less_than a' t2))) as h1.
    { introv ei.
      applydup k in ei.
      eapply tequality_respects_alphaeqc_left in ei0;[|apply mkcv_prod_substc].
      eapply tequality_respects_alphaeqc_right in ei0;[|apply mkcv_prod_substc].
      allrw @mkcv_le_substc2.
      allrw @mkcv_zero_substc.
      allrw @mkcv_less_than_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      auto. }
    clear k.

    assert (forall (k : Z),
              (0 <= k)%Z
              -> {k1 : Z , {k2 : Z
                  , t1 ===>(lib) (mkc_integer k1)
                  # t2 ===>(lib) (mkc_integer k2)
                  # ((k < k1)%Z # (k < k2)%Z){+}(k1 <= k)%Z # (k2 <= k)%Z }}) as h2.
    { introv le0k.
      pose proof (h1 (mkc_integer k) (mkc_integer k)) as h.
      autodimp h hyp.
      { apply equality_in_int; unfold equality_of_int; exists k; dands; spcast; auto;
        apply computes_to_valc_refl; eauto with slow. }
      allrw @tequality_mkc_prod; repnd.
      allrw @inhabited_le.
      allrw @tequality_mkc_less_than.
      clear h0 (* trivial *).
      autodimp h hyp.
      { exists 0%Z k; dands; auto; spcast; tcsp; allrw @mkc_zero_eq; allrw @mkc_nat_eq;
        allsimpl; apply computes_to_valc_refl; eauto with slow. }
      exrepnd; spcast.
      apply computes_to_valc_isvalue_eq in h0; eauto with slow; ginv.
      apply computes_to_valc_isvalue_eq in h4; eauto with slow; ginv.
      exists kb kd; dands; spcast; auto. }
    clear h1.

    pose proof (h2 0%Z) as h; autodimp h hyp; tcsp; exrepnd; spcast.
    exists k1 k2; dands; spcast; tcsp.
    introv i.
    apply h2 in i; exrepnd; spcast.
    repeat computes_to_eqval; auto.

  - dands.
    { apply tequality_int. }
    introv ei.
    exrepnd; spcast.

    apply equality_in_int in ei.
    apply equality_of_int_imp_tt in ei.
    unfold equality_of_int_tt in ei; exrepnd.

    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    allrw @mkcv_le_substc2.
    allrw @mkcv_less_than_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_zero_substc.
    allrw @csubst_mk_cv.

    apply tequality_mkc_prod; dands.
    { apply tequality_mkc_le.
      exists 0%Z k 0%Z k.
      dands; tcsp; spcast; auto;
      try (rw @mkc_zero_eq; rw @mkc_nat_eq; simpl;
           apply computes_to_valc_refl; eauto with slow).
      destruct (Z_lt_le_dec k 0); tcsp. }

    introv inh.
    allrw @inhabited_le; exrepnd; spcast.
    apply computes_to_valc_isvalue_eq in inh0; eauto with slow.
    rw @mkc_zero_eq in inh0; rw @mkc_nat_eq in inh0; ginv.
    computes_to_eqval.
    apply tequality_mkc_less_than.
    exists k k1 k k2; dands; spcast; tcsp.
Qed.

Lemma type_mkc_natk {o} :
  forall lib (t : @CTerm o),
    type lib (mkc_natk t)
    <=> {k : Z , t ===>(lib) (mkc_integer k)}.
Proof.
  introv.
  rw @tequality_mkc_natk; split; introv h; exrepnd; spcast; repeat computes_to_eqval.
  - exists k1; spcast; auto.
  - exists k k; dands; spcast; auto.
    introv i.
    destruct (Z_lt_le_dec k0 k); tcsp.
Qed.

Lemma type_mkc_le {o} :
  forall lib (a b : @CTerm o),
  type lib (mkc_le a b) <=>
       (exists ka kb
        , (a) ===>( lib)(mkc_integer ka)
        # (b) ===>( lib)(mkc_integer kb)).
Proof.
  introv.
  rw @tequality_mkc_le; split; intro h; exrepnd; spcast; repeat computes_to_eqval.
  - exists ka kb; dands; spcast; auto.
  - exists ka kb ka kb; dands; spcast; auto.
    destruct (Z_lt_le_dec kb ka); tcsp.
Qed.

Lemma type_mkc_less_than {o} :
  forall lib (a b : @CTerm o),
    type lib (mkc_less_than a b) <=>
         (exists ka kb
          , (a) ===>( lib)(mkc_integer ka)
          # (b) ===>( lib)(mkc_integer kb)).
Proof.
  introv.
  rw @tequality_mkc_less_than; split; intro h; exrepnd; spcast; repeat computes_to_eqval.
  - exists ka kb; dands; spcast; auto.
  - exists ka kb ka kb; dands; spcast; auto.
    destruct (Z_lt_le_dec ka kb); tcsp.
Qed.

Lemma equality_in_natk {o} :
  forall lib (a b t : @CTerm o),
    equality lib a b (mkc_natk t)
    <=> {m : nat , {k : Z
         , a ===>(lib) (mkc_nat m)
         # b ===>(lib) (mkc_nat m)
         # t ===>(lib) (mkc_integer k)
         # (Z.of_nat m < k)%Z }} .
Proof.
  introv.
  rw @mkc_natk_eq.
  rw @equality_in_set.

  split; intro h; exrepnd; dands.

  - allrw @equality_in_int.
    unfold equality_of_int in h1; exrepnd; spcast.
    eapply inhabited_type_respects_alphaeqc in h;[|apply mkcv_prod_substc].
    allrw @mkcv_le_substc2.
    allrw @mkcv_less_than_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_zero_substc.
    allrw @csubst_mk_cv.
    allrw @inhabited_prod; repnd.
    allrw @inhabited_le; exrepnd; spcast.
    apply computes_to_valc_isvalue_eq in h6; eauto with slow.
    rw @mkc_zero_eq in h6; rw @mkc_nat_eq in h6; ginv.
    computes_to_eqval.
    allrw @inhabited_less_than; exrepnd; spcast.
    computes_to_eqval.
    exists (Z.to_nat k) kb; dands; spcast; tcsp;
    try (complete (rw @mkc_nat_eq; rw Znat.Z2Nat.id; auto)).
    rw Znat.Z2Nat.id; auto.

  - introv ei.
    allrw @equality_in_int.
    unfold equality_of_int in ei; exrepnd; spcast.
    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    allrw @mkcv_le_substc2.
    allrw @mkcv_less_than_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_zero_substc.
    allrw @csubst_mk_cv.
    allrw @tequality_mkc_prod; dands.

    + allrw @tequality_mkc_le.
      exists 0%Z k0 0%Z k0.
      dands; tcsp; spcast; auto;
      try (rw @mkc_zero_eq; rw @mkc_nat_eq; simpl;
           apply computes_to_valc_refl; eauto with slow).
      destruct (Z_lt_le_dec k0 0); tcsp.

    + introv inh.
      allrw @inhabited_le; exrepnd; spcast.
      computes_to_eqval.
      apply computes_to_valc_isvalue_eq in inh0; eauto with slow.
      rw @mkc_zero_eq in inh0; rw @mkc_nat_eq in inh0; ginv.
      apply tequality_mkc_less_than.
      exists k0 k k0 k; dands; spcast; auto.
      destruct (Z_lt_le_dec k0 k); tcsp.

  - spcast.
    apply equality_in_int; unfold equality_of_int.
    exists (Z.of_nat m); dands; spcast; auto.

  - spcast.
    eapply inhabited_type_respects_alphaeqc;[apply alphaeqc_sym; apply mkcv_prod_substc|].
    allrw @mkcv_le_substc2.
    allrw @mkcv_less_than_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_zero_substc.
    allrw @csubst_mk_cv.
    apply inhabited_prod.
    allrw @type_mkc_le.
    allrw @type_mkc_less_than.
    allrw @inhabited_le.
    allrw @inhabited_less_than.
    dands.

    + exists 0%Z (Z.of_nat m); dands; spcast.
      * rw @mkc_zero_eq; rw @mkc_nat_eq; simpl; apply computes_to_valc_refl; eauto with slow.
      * allrw @mkc_nat_eq; auto.

    + exists (Z.of_nat m) k; dands; spcast; auto.

    + exists 0%Z (Z.of_nat m); dands; spcast; tcsp; try omega.
      rw @mkc_zero_eq; rw @mkc_nat_eq; simpl; apply computes_to_valc_refl; eauto with slow.

    + exists (Z.of_nat m) k; dands; spcast; auto.
Qed.

Lemma computes_to_valc_implies_reduces_toc {o} :
  forall lib (t1 t2 : @CTerm o),
    computes_to_valc lib t1 t2
    -> reduces_toc lib t1 t2.
Proof.
  introv comp.
  allrw @computes_to_valc_iff_reduces_toc; sp.
Qed.
Hint Resolve computes_to_valc_implies_reduces_toc : slow.

Lemma cequivc_mkc_isl {o} :
  forall lib (t u : @CTerm o),
    cequivc lib t u
    -> cequivc lib (mkc_isl t) (mkc_isl u).
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  unfold mk_isl, mk_ite.
  apply cequiv_congruence; fold_terms.
  - unfold cequiv_bts, lblift; simpl; dands; auto.
    introv k.
    repeat (destruct n; tcsp; try omega); clear k; unfold selectbt; simpl;
    try (fold (bcequiv lib)); eauto with slow.
    + apply bcequiv_nobnd; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
Qed.

Lemma cequivc_mkc_assert {o} :
  forall lib (t u : @CTerm o),
    cequivc lib t u
    -> cequivc lib (mkc_assert t) (mkc_assert u).
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  unfold mk_assert, mk_ite.
  apply cequiv_congruence; fold_terms.
  - unfold cequiv_bts, lblift; simpl; dands; auto.
    introv k.
    repeat (destruct n; tcsp; try omega); clear k; unfold selectbt; simpl;
    try (fold (bcequiv lib)); eauto with slow.
    + apply bcequiv_nobnd; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
    + apply bcequiv_refl.
      apply wf_bterm_iff; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
  - apply isprogram_decide_iff2; dands; eauto 3 with slow.
Qed.

Lemma computes_to_valc_inl_implies_cequivc_isl_tt {o} :
  forall lib (t u : @CTerm o),
    computes_to_valc lib t (mkc_inl u)
    -> cequivc lib (mkc_isl t) tt.
Proof.
  introv comp.
  eapply cequivc_trans;
    [apply cequivc_mkc_isl;
      apply computes_to_valc_implies_cequivc;
      exact comp|].
  apply computes_to_valc_implies_cequivc; clear comp t.
  destruct_cterms.
  unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
Qed.

Lemma computes_to_valc_inr_implies_cequivc_isl_ff {o} :
  forall lib (t u : @CTerm o),
    computes_to_valc lib t (mkc_inr u)
    -> cequivc lib (mkc_isl t) ff.
Proof.
  introv comp.
  eapply cequivc_trans;
    [apply cequivc_mkc_isl;
      apply computes_to_valc_implies_cequivc;
      exact comp|].
  apply computes_to_valc_implies_cequivc; clear comp t.
  destruct_cterms.
  unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; eauto 3 with slow.
Qed.

Lemma implies_isl_in_bool {o} :
  forall lib (A B a b : @CTerm o),
    equality lib a b (mkc_union A B)
    -> equality lib (mkc_isl a) (mkc_isl b) mkc_bool.
Proof.
  introv e.
  apply equality_mkc_union in e; exrepnd.
  apply equality_in_bool.
  repndors; exrepnd; spcast;[left|right]; dands; spcast.
  - eapply computes_to_valc_inl_implies_cequivc_isl_tt; eauto.
  - eapply computes_to_valc_inl_implies_cequivc_isl_tt; eauto.
  - eapply computes_to_valc_inr_implies_cequivc_isl_ff; eauto.
  - eapply computes_to_valc_inr_implies_cequivc_isl_ff; eauto.
Qed.

Lemma tt_not_approx_ff {o} :
  forall (lib : @library o), !approx lib mk_btrue mk_bfalse.
Proof.
  introv apr.
  inversion apr as [cl]; clear apr.
  unfold close_comput in cl; repnd.
  unfold close_compute_val in cl2.
  pose proof (cl2 (NInj NInl) [nobnd mk_axiom]) as h; fold_terms.
  autodimp h hyp; eauto 3 with slow.
  exrepnd.
  apply computes_to_value_isvalue_eq in h1; ginv; eauto 3 with slow.
Qed.

Lemma tt_not_cequiv_ff {o} :
  forall (lib : @library o), !cequiv lib mk_btrue mk_bfalse.
Proof.
  introv ceq.
  apply cequiv_le_approx in ceq.
  apply tt_not_approx_ff in ceq; sp.
Qed.

Lemma tt_not_cequivc_ff {o} :
  forall (lib : @library o), !cequivc lib tt ff.
Proof.
  introv.
  unfold cequivc; simpl.
  apply tt_not_cequiv_ff.
Qed.

Lemma equality_tt_in_bool_implies_cequiv {o} :
  forall lib (t : @CTerm o),
    equality lib t tt mkc_bool
    -> ccequivc lib t tt.
Proof.
  introv e.
  apply equality_in_bool in e; repndors; repnd; spcast; eauto with slow.
  apply tt_not_cequivc_ff in e; sp.
Qed.

Lemma isprogram_mk_assert {o} :
  forall (t : @NTerm o),
    isprogram (mk_assert t) <=> isprogram t.
Proof.
  introv.
  unfold mk_assert.
  rw @isprogram_decide_iff2; split; intro k; repnd; tcsp; dands; auto;
  apply isprog_vars_isprogrambt;
  apply isprog_vars_if_isprog; eauto 3 with slow.
Qed.

Lemma mkc_assert_tt {o} :
  forall (lib : @library o), cequivc lib (mkc_assert tt) mkc_unit.
Proof.
  introv.
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_mk_assert.
  apply isprogram_inl; eauto with slow.
Qed.

Lemma inhabited_type_mkc_unit {o} :
  forall (lib : @library o), inhabited_type lib mkc_unit.
Proof.
  introv.
  unfold inhabited_type.
  exists (@mkc_axiom o).
  apply equality_in_unit; dands; spcast;
  apply computes_to_valc_refl; eauto with slow.
Qed.
Hint Resolve inhabited_type_mkc_unit : slow.

Lemma equality_mkc_inl_implies {o} :
  forall lib (t1 t2 A B : @CTerm o),
    equality lib (mkc_inl t1) (mkc_inl t2) (mkc_union A B)
    -> equality lib t1 t2 A.
Proof.
  introv e.
  apply equality_mkc_union in e; repnd.
  repndors; exrepnd; spcast;
  apply computes_to_valc_isvalue_eq in e2; eauto 3 with slow;
  apply computes_to_valc_isvalue_eq in e4; eauto 3 with slow;
  eqconstr e2; eqconstr e4; auto.
Qed.

Lemma type_tnat {o} :
  forall (lib : @library o), type lib mkc_tnat.
Proof.
  introv.
  rw @mkc_tnat_eq.
  apply tequality_set; dands; auto.
  { apply tequality_int. }

  introv e.
  allrw @substc_mkcv_le.
  allrw @substc_mkcv_zero.
  allrw @mkc_var_substc.
  apply equality_in_int in e.
  unfold equality_of_int in e; exrepnd; spcast.

  apply tequality_mkc_le.
  exists (0%Z) k (0%Z) k; dands; spcast; tcsp.

  - unfold computes_to_valc; simpl.
    unfold computes_to_value; dands; eauto with slow.

  - unfold computes_to_valc; simpl.
    unfold computes_to_value; dands; eauto with slow.

  - destruct (Z_le_gt_dec 0 k); tcsp.
    right; dands; omega.
Qed.
Hint Resolve type_tnat : slow.

Definition equality_of_nat {p} lib (n m : @CTerm p) :=
  {k : nat , n ===>(lib) (mkc_nat k)
           # m ===>(lib) (mkc_nat k)}.

Lemma equality_in_tnat {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_tnat
    <=> equality_of_nat lib a b.
Proof.
  introv.
  rw @mkc_tnat_eq.
  rw @equality_in_set.
  rw @equality_in_int.
  unfold equality_of_int, equality_of_nat.
  rw @substc_mkcv_le.
  rw @substc_mkcv_zero.
  rw @mkc_var_substc.
  rw @inhabited_le.
  split; introv k; exrepnd; spcast; dands;
  repeat computes_to_eqval;
  computes_to_value_isvalue; ginv.
  - inversion k2; subst.
    apply Wf_Z.Z_of_nat_complete in k3; exrepnd; subst.
    exists n; dands; spcast; auto.
  - introv e.
    allrw @substc_mkcv_le.
    allrw @substc_mkcv_zero.
    allrw @mkc_var_substc.
    apply equality_in_int in e.
    unfold equality_of_int in e; exrepnd; spcast.
    apply tequality_mkc_le.
    exists (0%Z) k (0%Z) k; dands; spcast; auto;
    try (complete (unfold computes_to_valc; simpl;
                   unfold computes_to_value; dands;
                   eauto with slow)).
    destruct (Z_le_gt_dec 0 k); sp.
    right; sp; omega.
  - exists (Z.of_nat k0); dands; spcast; auto.
  - exists (0%Z) (Z.of_nat k0); dands; spcast; auto;
    try omega;
    try (complete (unfold computes_to_valc; simpl;
                   unfold computes_to_value; dands;
                   eauto with slow)).
Qed.

Lemma equality_in_int_and_inhabited_le_implies_equality_in_nat {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_int
    -> inhabited_type lib (mkc_le mkc_zero a)
    -> equality lib a b mkc_tnat.
Proof.
  introv e inh.
  apply equality_in_tnat.
  apply equality_in_int in e.
  apply inhabited_le in inh.
  unfold equality_of_nat.
  unfold equality_of_int in e.
  exrepnd; spcast.
  repeat computes_to_eqval.
  computes_to_value_isvalue; ginv.
  inversion inh0; subst.
  apply Wf_Z.Z_of_nat_complete in inh1; exrepnd; subst.
  exists n; dands; spcast; auto.
Qed.

Lemma equality_of_nat_implies_equality_of_int {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat lib t1 t2
    -> equality_of_int lib t1 t2.
Proof.
  introv e.
  unfold equality_of_nat in e; exrepnd; spcast.
  unfold equality_of_int.
  allrw @mkc_nat_eq.
  exists (Z.of_nat k); dands; spcast; auto.
Qed.

Lemma equality_in_int_implies_cequiv {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_int
    -> cequivc lib a b.
Proof.
  introv e.
  apply equality_in_int in e.
  apply equality_of_int_imp_tt in e.
  unfold equality_of_int_tt in e; exrepnd.
  destruct_cterms; allunfold @computes_to_valc; allunfold @cequivc; allsimpl.
  allunfold @computes_to_value; repnd.
  apply (cequiv_trans _ _ (mk_integer k)).
  - apply reduces_to_implies_cequiv; auto.
    apply isprogram_eq; auto.
  - apply cequiv_sym.
    apply reduces_to_implies_cequiv; auto.
    apply isprogram_eq; auto.
Qed.
