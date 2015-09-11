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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export alphaeq3.
Require Export cvterm.
Require Export nat_defs.
Require Export per_props_set.
Require Export per_props_union.
Require Export per_props3.

Require Export list.  (* ??? *)

Lemma equality_in_int {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_int <=> equality_of_int lib t1 t2.
Proof.
  intros; split; intro e.

  - unfold equality, nuprl in e; exrepnd.
    inversion e1; subst; try not_univ.
    allunfold @per_int; sp.
    discover; sp.

  - unfold equality, nuprl.
    exists (fun a b : @CTerm p => equality_of_int lib a b); dands; tcsp.
    apply CL_int; unfold per_int; sp;
    spcast; apply computes_to_value_isvalue_refl; repeat constructor; simpl; sp.
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
    {ka : Z
     , {kb : Z
        , a ===>(lib) (mkc_integer ka)
        # b ===>(lib) (mkc_integer kb)
        # (
            ((ka < kb)%Z # equality lib u v c)
            {+}
            ((kb <= ka)%Z # equality lib u v d)
          )}}.
Proof.
  introv.

  split; intro k; exrepnd.

  - applydup @inhabited_implies_tequality in k.
    apply types_converge in k0.
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

Lemma iscvalue_mkc_pair {o} :
  forall (a b : @CTerm o),
    iscvalue (mkc_pair a b).
Proof.
  introv; destruct_cterms; unfold iscvalue; simpl.
  allrw @isprog_eq.
  inversion i as [cl1 wf1].
  inversion i0 as [cl2 wf2].
  repeat constructor; simpl.
  - unfold closed; simpl; rw cl1; rw cl2; simpl; auto.
  - introv k; repndors; subst; tcsp; constructor; auto.
Qed.
Hint Resolve iscvalue_mkc_pair : slow.

Lemma inhabited_prod {p} :
  forall lib (A B : @CTerm p),
    inhabited_type lib (mkc_prod A B)
    <=>
    (type lib A
     # type lib B
     # inhabited_type lib A
     # inhabited_type lib B).
Proof.
  introv.
  unfold inhabited_type; split; intro k; exrepnd.

  - apply equality_in_prod in k0; exrepnd; spcast.
    autodimp k2 hyp.
    { allapply @inhabited_type_if_equality; auto. }
    allapply @equality_refl.
    dands; auto; eexists; eauto.

  - exists (mkc_pair t0 t).
    apply equality_in_prod; dands; auto.
    exists t0 t0 t t; dands; spcast; tcsp;
    apply computes_to_valc_refl; eauto with slow.
Qed.

Lemma inhabited_prod2 {p} :
  forall lib (A B : @CTerm p),
    inhabited_type lib (mkc_prod A B)
    <=>
    (type lib A
     # inhabited_type lib A
     # type lib B
     # inhabited_type lib B).
Proof.
  introv.
  rw @inhabited_prod; split; sp.
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

Lemma alphaeqc_mkc_fun {o} :
  forall a b c d : @CTerm o,
    alphaeqc a b
    -> alphaeqc c d
    -> alphaeqc (mkc_fun a c) (mkc_fun b d).
Proof.
  introv aeq1 aeq2.
  destruct_cterms.
  allunfold @alphaeqc; allsimpl.
  constructor; simpl; auto.
  introv j.
  repeat (destruct n; tcsp); unfold selectbt; simpl.
  - apply alphaeqbt_nilv2; auto.
  - rw @newvar_prog; auto.
    rw @newvar_prog; auto.
    apply alpha_eq_bterm_congr; auto.
Qed.

Lemma alphaeqc_refl {o} :
  forall (t : @CTerm o), alphaeqc t t.
Proof.
  introv.
  destruct_cterms; unfold alphaeqc; simpl; eauto with slow.
Qed.
Hint Resolve alphaeqc_refl : slow.

Lemma mkcv_tnat_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_tnat [v])
    = mkc_tnat.
Proof.
  introv.
  unfold mkcv_tnat.
  allrw @csubst_mk_cv; auto.
Qed.

Lemma mkcv_natk_eq {o} :
  forall vs (t : @CVTerm o vs),
    mkcv_natk vs t
    = let v := newvar (get_cvterm vs t) in
      mkcv_set vs (mkcv_int vs)
               v
               (mkcv_prod
                  (v :: vs)
                  (mkcv_le (v :: vs) (mkcv_zero (v :: vs)) (mk_cv_app_r vs [v] (mkc_var v)))
                  (mkcv_less_than (v :: vs) (mk_cv_app_r vs [v] (mkc_var v)) (mk_cv_app_l [v] vs t))).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; tcsp.
Qed.

Lemma subst_mk_set {o} :
  forall (a : @NTerm o) v b x u,
    closed u
    -> subst (mk_set a v b) x u
       = mk_set (subst a x u) v (if deq_nvar v x then b else subst b x u).
Proof.
  introv cl.
  repeat unfsubst; simpl; rw memvar_singleton; fold_terms;
  boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma subst_mk_product_disj {o} :
  forall (a : @NTerm o) v b x u,
    disjoint (free_vars u) (bound_vars (mk_product a v b))
    -> subst (mk_product a v b) x u
       = mk_product (subst a x u) v (if deq_nvar v x then b else subst b x u).
Proof.
  introv d.
  unfold subst.
  rw @lsubst_lsubst_aux; allsimpl; allrw app_nil_r; eauto 2 with slow.
  rw @lsubst_lsubst_aux; allsimpl; allrw app_nil_r; eauto 2 with slow;
  [|allrw disjoint_app_r; repnd; eauto 2 with slow].
  rw @lsubst_lsubst_aux; allsimpl; allrw app_nil_r; eauto 2 with slow;
  [|allrw disjoint_app_r; allrw disjoint_cons_r; repnd; eauto 2 with slow].
  allrw memvar_singleton; boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma subst_mk_product_cl {o} :
  forall (a : @NTerm o) v b x u,
    closed u
    -> subst (mk_product a v b) x u
       = mk_product (subst a x u) v (if deq_nvar v x then b else subst b x u).
Proof.
  introv d.
  unfold subst.
  repeat unflsubst.
  simpl; allrw memvar_singleton; boolvar; allrw @lsubst_aux_nil; tcsp.
Qed.

Lemma subst_mk_int {o} :
  forall x (u : @NTerm o),
    subst mk_int x u = mk_int.
Proof.
  introv; tcsp.
Qed.

Lemma alpha_eq_mk_set {o} :
  forall v (a1 a2 : @NTerm o) v1 v2 b1 b2,
    !LIn v (all_vars b1)
    -> !LIn v (all_vars b2)
    -> alpha_eq a1 a2
    -> alpha_eq (subst b1 v1 (mk_var v)) (subst b2 v2 (mk_var v))
    -> alpha_eq (mk_set a1 v1 b1) (mk_set a2 v2 b2).
Proof.
  introv ni1 ni2 aeqa aeqb.
  constructor; simpl; auto.
  introv i.
  repeat (destruct n; tcsp); unfold selectbt; simpl.
  - apply alphaeqbt_nilv2; auto.
  - apply (al_bterm _ _ [v]); simpl; auto.
    allrw disjoint_singleton_l; allrw in_app_iff; sp.
Qed.

Lemma ite_mk_product {o} :
  forall A B (b : {A} + {B}) (a1 a2 : @NTerm o) v1 v2 b1 b2,
    (if b then mk_product a1 v1 b1 else mk_product a2 v2 b2)
    = mk_product (if b then a1 else a2) (if b then v1 else v2) (if b then b1 else b2).
Proof.
  introv; destruct b; tcsp.
Qed.

Lemma ite_same :
  forall A B T (b : {A} + {B}) (x : T),
    (if b then x else x) = x.
Proof.
  introv; destruct b; tcsp.
Qed.

Lemma alpha_eq_bterm_bterm_disjoint {o} :
  forall vs1 vs2 (t : @NTerm o),
    disjoint vs1 (free_vars t)
    -> disjoint vs2 (free_vars t)
    -> length vs1 = length vs2
    -> alpha_eq_bterm (bterm vs1 t) (bterm vs2 t).
Proof.
  introv d1 d2 len.
  pose proof (fresh_vars (length vs1)
                         (vs1 ++ vs2
                              ++ free_vars t
                              ++ bound_vars t)) as fvs; exrepnd.
  allrw disjoint_app_r; repnd.
  apply (al_bterm_aux lvn); auto.
  { allrw disjoint_app_r; tcsp. }
  rw @lsubst_aux_trivial_cl_term;[|rw @dom_sub_var_ren;eauto with slow].
  rw @lsubst_aux_trivial_cl_term;[|rw @dom_sub_var_ren;eauto with slow; try omega].
  eauto with slow.
Qed.

Lemma mkcv_natk_substc {o} :
  forall v a (t : @CTerm o),
    alphaeqc
      (substc t v (mkcv_natk [v] a))
      (mkc_natk (substc t v a)).
Proof.
  introv.
  rw @mkc_natk_eq.
  rw @mkcv_natk_eq.

  destruct_cterms.
  unfold alphaeqc; simpl.

  (* brute force *)

  remember (newvar x0) as nv1.
  pose proof (newvar_prop x0) as nvp1; rw <- Heqnv1 in nvp1.
  clear Heqnv1.
  rw @cl_subst_subst_aux; eauto 2 with slow.
  unfold subst_aux; simpl; allrw @sub_filter_nil_r; allrw memvar_singleton.
  pose proof (newvar_prog (@mk_void o)) as nvv; autodimp nvv hyp; tcsp;eauto 2 with slow;[].
  rw nvv.

  remember (newvar (mk_less_than (mk_var nv1) x0)) as nv2.
  pose proof (newvar_prop (mk_less_than (mk_var nv1) x0)) as nvp2; rw <- Heqnv2 in nvp2.
  clear Heqnv2.
  allsimpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.

  boolvar; allsimpl; tcsp.

  { constructor; simpl; auto; [].
    unfold selectbt; simpl.
    introv k.
    repeat (destruct n; tcsp);[]; clear k.
    fold_terms.
    allrw @lsubst_aux_nil.
    eapply isprog_vars_disjoint_implies_isprog in i0; allrw disjoint_singleton_l; auto.
    rw @subst_trivial; auto.

    pose proof (ex_fresh_var (nv1 :: nv2
                                  :: nvarx
                                  :: newvar (mk_less_than (mk_var nvarx) x0)
                                  :: bound_vars x0
                                  ++ free_vars x0)) as fv1.
    destruct fv1 as [v1 fv1].
    exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.
    apply (al_bterm_aux [v1]); simpl; auto;[|].

    { unfold all_vars; simpl; allrw remove_nvars_nil_l; allrw app_nil_r;[].
      apply disjoint_singleton_l.
      rw nvv.
      remember (newvar (mk_less_than (mk_var nvarx) x0)) as nv3.
      pose proof (newvar_prop (mk_less_than (mk_var nvarx) x0)) as nvp3.
      rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      allrw remove_nvars_nil_l; allrw app_nil_r; allrw not_over_or; repnd.
      repeat (boolvar; tcsp; allsimpl;
              allrw @lsubst_aux_nil;
              allrw remove_nvars_cons;
              allrw remove_nvars_nil_l;
              allrw app_nil_r).
      repeat (allrw in_app_iff; allsimpl; allrw in_remove).
      allrw not_over_or; dands; tcsp. }

    rw nvv.
    remember (newvar (mk_less_than (mk_var nvarx) x0)) as nv3.
    pose proof (newvar_prop (mk_less_than (mk_var nvarx) x0)) as nvp3.
    rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      allrw remove_nvars_nil_l; allrw app_nil_r; allrw not_over_or; repnd.

    allrw memvar_singleton.
    allrw @sub_filter_nil_r.
    boolvar; allsimpl; tcsp; fold_terms;[|].

    { rw @lsubst_aux_trivial_cl_term2; eauto 2 with slow.
      constructor; simpl; auto; [].
      unfold selectbt; simpl.
      introv k.
      repeat (destruct n; tcsp);[]; clear k.

      apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
      allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp.
    }

    { allrw memvar_singleton; simpl; boolvar; tcsp.
      simpl; boolvar; tcsp; fold_terms.
      repeat (rw @lsubst_aux_trivial_cl_term2; eauto 2 with slow).
      constructor; simpl; auto; [].
      unfold selectbt; simpl.
      introv k.
      repeat (destruct n; tcsp);[]; clear k.

      apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
      allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp.
    }
  }

  { allrw memvar_singleton; simpl.
    repeat (boolvar; tcsp; simpl; allrw memvar_singleton; allrw @lsubst_aux_nil; fold_terms;GC).

    { apply isprog_vars_disjoint_implies_isprog in i0; allrw disjoint_singleton_l; auto;[].
      rw @subst_trivial; auto.

      constructor; simpl; auto.
      introv k.
      repeat (destruct n; tcsp); clear k;[].
      unfold selectbt; simpl.

      pose proof (ex_fresh_var (nv1 :: nvarx
                                    :: newvar (mk_less_than (mk_var nvarx) x0)
                                    :: bound_vars x0
                                    ++ free_vars x0)) as fvv.
      exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

      apply (al_bterm_aux [v]); auto.

      { unfold all_vars; simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
        apply disjoint_singleton_l; simpl.
        allrw in_app_iff; simpl; allrw in_app_iff; simpl.
        allrw in_remove_nvars; allsimpl.
        allrw in_app_iff; simpl.
        allrw not_over_or; dands; tcsp. }

      simpl.
      allrw @sub_filter_nil_r.
      remember (newvar (mk_less_than (mk_var nvarx) x0)) as nv3.
      pose proof (newvar_prop (mk_less_than (mk_var nvarx) x0)) as nvp3.
      rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      rw nvv.
      allrw remove_nvars_nil_l; allrw app_nil_r; allrw not_over_or; repnd.
      allrw memvar_singleton.
      repeat (boolvar; tcsp; simpl); fold_terms.
      allrw not_over_or; repnd; GC.
      repeat (rw @lsubst_aux_trivial_cl_term2; eauto 2 with slow).

      constructor; simpl; auto; [].
      unfold selectbt; simpl.
      introv k.
      repeat (destruct n; tcsp);[]; clear k.

      apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
      allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp.
    }

    { constructor; simpl; auto.
      introv k.
      repeat (destruct n; tcsp); clear k.
      unfold selectbt; simpl.
      unfsubst.

      pose proof (ex_fresh_var (nv1 :: nvarx
                                    :: nv2
                                    :: newvar (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(nvarx,x)]))
                                    :: (bound_vars (lsubst_aux x0 [(nvarx, x)]))
                                    ++ (free_vars (lsubst_aux x0 [(nvarx, x)])))) as fvv.
      exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

      apply (al_bterm_aux [v]); auto.

      { unfold all_vars; simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
        apply disjoint_singleton_l; simpl.
        allrw in_app_iff; simpl; allrw in_app_iff; simpl.
        allrw in_remove_nvars; allsimpl.
        allrw in_app_iff; simpl.
        allrw not_over_or; dands; tcsp. }

      simpl.
      allrw @sub_filter_nil_r.
      remember (newvar (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(nvarx, x)]))) as nv3.
      pose proof (newvar_prop (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(nvarx, x)]))) as nvp3.
      rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      rw nvv.
      allrw memvar_singleton.
      repeat (boolvar; allsimpl; tcsp;
              allrw remove_nvars_nil_l; allrw app_nil_r;
              allrw not_over_or; repnd; tcsp;GC).
      fold_terms.
      assert (closed (lsubst_aux x0 [(nvarx,x)])) as c
          by (apply closed_lsubst_aux; simpl; eauto 3 with slow).
      repeat (rw (lsubst_aux_trivial_cl_term2 (lsubst_aux x0 [(nvarx,x)])); auto).

      constructor; simpl; auto.
      introv k.
      repeat (destruct n; tcsp); clear k.
      unfold selectbt; simpl.

      apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
      allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp;
      rw c; simpl; tcsp.
    }

    { constructor; simpl; auto.
      introv k.
      repeat (destruct n; tcsp); clear k.
      unfold selectbt; simpl.
      apply isprog_vars_disjoint_implies_isprog in i0; allrw disjoint_singleton_l; auto;[].
      rw @subst_trivial; auto.

      pose proof (ex_fresh_var (nv1 :: nvarx
                                    :: nv2
                                    :: newvar (mk_less_than (mk_var nvarx) x0)
                                    :: bound_vars x0
                                    ++ free_vars x0)) as fvv.
      exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

      apply (al_bterm_aux [v]); auto.

      { unfold all_vars; simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
        apply disjoint_singleton_l; simpl.
        allrw in_app_iff; simpl; allrw in_app_iff; simpl.
        allrw in_remove_nvars; allsimpl.
        allrw in_app_iff; simpl.
        allrw not_over_or; dands; tcsp. }

      simpl.
      allrw @sub_filter_nil_r.
      remember (newvar (mk_less_than (mk_var nvarx) x0)) as nv3.
      pose proof (newvar_prop (mk_less_than (mk_var nvarx) x0)) as nvp3.
      rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      rw nvv.
      allrw memvar_singleton.
      repeat (boolvar; allsimpl; tcsp;
              allrw remove_nvars_nil_l; allrw app_nil_r;
              allrw not_over_or; repnd; tcsp;GC);
        fold_terms;
        repeat (rw (lsubst_aux_trivial_cl_term2 x0); eauto 3 with slow).

      { constructor; simpl; auto.
        introv k.
        repeat (destruct n; tcsp); clear k.
        unfold selectbt; simpl.

        apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
        allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp;
        rw c; simpl; tcsp. }

      { constructor; simpl; auto.
        introv k.
        repeat (destruct n; tcsp); clear k.
        unfold selectbt; simpl.

        apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
        allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp;
        rw c; simpl; tcsp. }
    }

    { rw @cl_subst_subst_aux; eauto 3 with slow; unfold subst_aux.
      constructor; simpl; auto.
      introv k.
      repeat (destruct n; tcsp); clear k.
      unfold selectbt; simpl.

      pose proof (ex_fresh_var (nv1 :: nvarx
                                    :: nv2
                                    :: v
                                    :: newvar (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(v,x)]))
                                    :: bound_vars (lsubst_aux x0 [(v,x)])
                                    ++ free_vars (lsubst_aux x0 [(v,x)]))) as fvv.
      exrepnd; allsimpl; allrw in_app_iff; allrw not_over_or; repnd; GC.

      apply (al_bterm_aux [v0]); auto.

      { unfold all_vars; simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
        apply disjoint_singleton_l; simpl.
        allrw in_app_iff; simpl; allrw in_app_iff; simpl.
        allrw in_remove_nvars; allsimpl.
        allrw in_app_iff; simpl.
        allrw not_over_or; dands; tcsp. }

      simpl.
      allrw @sub_filter_nil_r.
      remember (newvar (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(v,x)]))) as nv3.
      pose proof (newvar_prop (mk_less_than (mk_var nvarx) (lsubst_aux x0 [(v,x)]))) as nvp3.
      rw <- Heqnv3 in nvp3; clear Heqnv3; allsimpl.
      rw nvv.
      allrw memvar_singleton.
      repeat (boolvar; allsimpl; tcsp;
              allrw remove_nvars_nil_l; allrw app_nil_r;
              allrw not_over_or; repnd; tcsp;GC);
        fold_terms;
        assert (closed (lsubst_aux x0 [(v,x)])) as c
            by (apply closed_lsubst_aux; simpl; eauto 3 with slow);
        repeat (rw (lsubst_aux_trivial_cl_term2 (lsubst_aux x0 [(v,x)])); auto).

      { constructor; simpl; auto.
        introv k.
        repeat (destruct n; tcsp); clear k.
        unfold selectbt; simpl.

        apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
        allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp;
        rw c; simpl; tcsp. }

      { constructor; simpl; auto.
        introv k.
        repeat (destruct n; tcsp); clear k.
        unfold selectbt; simpl.

        apply alpha_eq_bterm_bterm_disjoint; simpl; auto; apply disjoint_singleton_l;
        allrw remove_nvars_nil_l; allrw app_nil_r; simpl; rw not_over_or; dands; tcsp;
        rw c; simpl; tcsp. }
    }
  }
Qed.

Lemma mkc_assert_eq {o} :
  forall (t : @CTerm o),
    mkc_assert t = mkc_ite t mkc_unit mkc_void.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
Qed.

Lemma bcequiv_refl {o} :
  forall lib (b : @BTerm o),
    wf_bterm b
    -> bcequiv lib b b.
Proof.
  introv wf.
  destruct b as [l t].
  allrw @wf_bterm_iff.
  apply blift_approx_cequiv.
  - unfold approx_open_bterm, blift.
    exists l t t; dands; eauto 3 with slow.
  - unfold approx_open_bterm, blift.
    exists l t t; dands; eauto 3 with slow.
Qed.

Lemma bcequiv_nobnd {o} :
  forall lib (t u : @NTerm o),
    wf_term t
    -> wf_term u
    -> cequiv lib t u
    -> bcequiv lib (nobnd t) (nobnd u).
Proof.
  introv wft wfu ceq.
  applydup @cequiv_sym in ceq.
  apply cequiv_le_approx in ceq.
  apply cequiv_le_approx in ceq0.
  apply blift_approx_cequiv.
  - unfold approx_open_bterm, blift.
    exists ([] : list NVar) t u; dands; eauto 3 with slow.
    apply approx_implies_approx_open; auto.
  - unfold approx_open_bterm, blift.
    exists ([] : list NVar) u t; dands; eauto 3 with slow.
    apply approx_implies_approx_open; auto.
Qed.

Lemma wf_btrue {o} : @wf_term o mk_btrue.
Proof.
  unfold mk_btrue.
  apply wf_inl; eauto with slow.
Qed.
Hint Resolve wf_btrue : slow.

Lemma wf_bfalse {o} : @wf_term o mk_bfalse.
Proof.
  unfold mk_bfalse.
  apply wf_inr; eauto with slow.
Qed.
Hint Resolve wf_bfalse : slow.

Lemma isprog_btrue {o} : @isprog o mk_btrue.
Proof.
  unfold mk_btrue.
  apply isprog_inl; eauto with slow.
Qed.
Hint Resolve isprog_btrue : slow.

Lemma isprog_bfalse {o} : @isprog o mk_bfalse.
Proof.
  unfold mk_bfalse.
  apply isprog_inr; eauto with slow.
Qed.
Hint Resolve isprog_bfalse : slow.

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

Lemma isvalue_btrue {o} : @isvalue o mk_btrue.
Proof.
  unfold mk_btrue.
  apply isvalue_inl; eauto with slow.
Qed.
Hint Resolve isvalue_btrue : slow.

Lemma isvalue_bfalse {o} : @isvalue o mk_bfalse.
Proof.
  unfold mk_bfalse.
  apply isvalue_inr; eauto with slow.
Qed.
Hint Resolve isvalue_bfalse : slow.

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

Lemma closed_if_isprog {o} :
  forall (t : @NTerm o),
    isprog t -> closed t.
Proof.
  introv isp.
  apply isprog_eq in isp.
  destruct isp; auto.
Qed.

Lemma substc_mkcv_le {o} :
  forall v t (a b : @CVTerm o [v]),
    substc t v (mkcv_le [v] a b)
    = mkc_le (substc t v a) (substc t v b).
Proof.
  introv.
  apply cterm_eq; simpl.
  destruct_cterms; simpl.
  applydup @closed_if_isprog in i; unfold closed in i2.

  unfold subst, lsubst; simpl; allrw app_nil_r; rw i2; simpl; boolvar;
  allsimpl; try (complete (provefalse; tcsp)); tcsp; boolvar; allsimpl;
  tcsp; allrw not_over_or; repnd; tcsp; boolvar; allsimpl; tcsp.
Qed.

Lemma substc_mkcv_zero {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_zero [v])
    = mkc_zero.
Proof.
  introv.
  apply cterm_eq; simpl.
  destruct_cterms; simpl.
  unfold subst, lsubst; simpl; auto.
Qed.

Lemma substc_mkcv_int {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_int [v])
    = mkc_int.
Proof.
  introv.
  apply cterm_eq; simpl.
  destruct_cterms; simpl.
  unfold subst, lsubst; simpl; auto.
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

Lemma lsubstc_int2int {o} :
  forall (w : @wf_term o int2int) s c,
    lsubstc int2int w s c = mkc_fun mkc_int mkc_int.
Proof.
  introv.
  apply cterm_eq; simpl.
  unfold int2int, csubst, lsubst; simpl.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @sub_free_vars_csub2sub; boolvar; tcsp.
Qed.

Lemma member_product2 {o} :
  forall lib (p : @CTerm o) A v B,
    member lib p (mkc_product A v B)
    <=>
    (type lib (mkc_product A v B)
     # {a, b : CTerm
        , p ===>(lib) (mkc_pair a b)
        # member lib a A
        # member lib b (substc a v B)}).
Proof.
  introv.
  rw @equality_in_product; split; intro k; exrepnd.
  - dands; auto.
    + apply tequality_product; auto.
    + allapply @equality_refl.
      exists a1 b1; dands; auto.
  - apply @tequality_product in k0; repnd.
    dands; auto.
    exists a a b b; dands; auto.
Qed.

Lemma equality_in_ufun {p} :
  forall lib (f g A B : @CTerm p),
    equality lib f g (mkc_ufun A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # (inhabited_type lib A -> equality lib f g B)).
Proof.
  introv.
  rw <- @fold_mkc_ufun.
  rw @equality_in_isect.
  split; intro k; repnd; dands; auto.

  - introv i.
    unfold inhabited_type in i; exrepnd.
    generalize (k1 t t); intro j; autodimp j hyp.
    repeat (rw @csubst_mk_cv in j); sp.

  - introv e.
    unfold inhabited_type in e; exrepnd.
    unfold member in e0.
    apply k in e0.
    repeat (rw @csubst_mk_cv in e0); sp.

  - introv e.
    repeat (rw @csubst_mk_cv); sp.
    autodimp k1 hyp.
    exists a; apply equality_refl in e; auto.

  - introv e.
    repeat (rw @csubst_mk_cv); sp.
    apply k.
    exists a; apply equality_refl in e; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/")
*** End:
*)
