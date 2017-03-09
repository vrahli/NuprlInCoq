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


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.


Lemma either_computes_to_equality_mkc_image_false {o} :
  forall lib (T1 T2 f1 f2 : @CTerm o),
    !either_computes_to_equality lib (mkc_image T1 f1) (mkc_image T2 f2).
Proof.
  introv e.
  unfold either_computes_to_equality, computes_to_equality in e.
  repndors; exrepnd; spcast; computes_to_value_isvalue.
Qed.
Hint Resolve either_computes_to_equality_mkc_image_false : slow.

Lemma equal_equality_types_mkc_image {o} :
  forall lib ts (T1 T2 f1 f2 : @CTerm o),
    equal_equality_types lib ts (mkc_image T1 f1) (mkc_image T2 f2).
Proof.
  introv e.
  apply either_computes_to_equality_mkc_image_false in e; tcsp.
Qed.
Hint Resolve equal_equality_types_mkc_image : slow.


Inductive equal_in_image {p} lib (A f t1 t2 : @CTerm p) : [U] :=
| eq_in_image_cl :
    forall t,
      equal_in_image lib A f t1 t
      -> equal_in_image lib A f t t2
      -> equal_in_image lib A f t1 t2
| eq_in_image_eq :
    forall a1 a2,
      equality lib a1 a2 A
      -> t1 ~=~(lib) (mkc_apply f a1)
      -> t2 ~=~(lib) (mkc_apply f a2)
      -> equal_in_image lib A f t1 t2.

Lemma equality_in_mkc_image {p} :
  forall lib (t1 t2 T f : @CTerm p),
    equality lib t1 t2 (mkc_image T f)
    <=> (type lib T # equal_in_image lib T f t1 t2).
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    inversion e1; subst; try not_univ.

    match goal with
    | [ H : per_image _ _ _ _ |- _ ] => rename H into h
    end.

    allunfold @per_image; exrepnd; spcast; computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    dands.
    { exists eqa; sp. }

    induction h.

    { apply @eq_in_image_cl with (t := t).
      - apply IHh1; apply h0; auto.
      - apply IHh2; apply h0; auto. }

    { apply @eq_in_image_eq with (a1 := a1) (a2 := a2); sp.
      exists eqa; sp. }

  - exrepnd.
    unfold type, tequality in e0; exrepnd.
    exists (per_image_eq lib eq f); dands.

    { apply CL_image; unfold per_image.
      exists eq T f; sp; spcast; sp;
        try (apply computes_to_valc_refl; apply iscvalue_mkc_image). }

    induction e.

    { apply @image_eq_cl with (t := t); sp. }

    { apply @image_eq_eq with (a1 := a1) (a2 := a2); sp.
      allunfold @equality; exrepnd.
      generalize (nuprl_uniquely_valued lib T eq eq0); intro h; repeat (dest_imp h hyp).
      rw h; sp. }
Qed.

Lemma equal_in_image_prop {p} :
  forall lib (A f t1 t2 : @CTerm p),
    equal_in_image lib A f t1 t2
    -> {a1, a2 : CTerm
        , t1 ~=~(lib) (mkc_apply f a1)
        # t2 ~=~(lib) (mkc_apply f a2)
        # member lib a1 A
        # member lib a2 A}.
Proof.
  introv e.
  induction e; exrepnd.

  exists a0 a2; sp.

  exists a1 a2; sp.
  allapply @equality_refl; sp.
  apply @equality_refl with (t2 := a1); apply equality_sym; sp.
Qed.

Lemma per_image_eq_as_equal_in_image {o} :
  forall lib (A : @CTerm o) f eqa,
    nuprl lib A eqa
    -> (per_image_eq lib eqa f) <=2=> (equal_in_image lib A f).
Proof.
  introv n; split; intro h; induction h.
  { eapply eq_in_image_cl; eauto. }
  { spcast.
    eapply eq_in_image_eq; spcast; eauto.
    apply (equality_eq lib A a1 a2 eqa); auto. }
  { eapply image_eq_cl; eauto. }
  { spcast.
    eapply image_eq_eq; spcast; eauto.
    apply (equality_eq lib A a1 a2 eqa); auto. }
Qed.

Lemma implies_eq_equal_in_image {o} :
  forall lib (A1 A2 : @CTerm o) f1 f2 eqa1 eqa2,
    nuprl lib A1 eqa1
    -> nuprl lib A2 eqa2
    -> ((per_image_eq lib eqa1 f1) <=2=> (per_image_eq lib eqa2 f2))
    -> (equal_in_image lib A1 f1) <=2=> (equal_in_image lib A2 f2).
Proof.
  introv na1 na2 eqiff; split; intro h.
  { eapply per_image_eq_as_equal_in_image;[eauto|].
    apply eqiff; eapply per_image_eq_as_equal_in_image;eauto. }
  { eapply per_image_eq_as_equal_in_image;[eauto|].
    apply eqiff; eapply per_image_eq_as_equal_in_image;eauto. }
Qed.

Lemma implies_eq_per_image_eq {o} :
  forall lib (A1 A2 : @CTerm o) f1 f2 eqa1 eqa2,
    nuprl lib A1 eqa1
    -> nuprl lib A2 eqa2
    -> ((equal_in_image lib A1 f1) <=2=> (equal_in_image lib A2 f2))
    -> ((per_image_eq lib eqa1 f1) <=2=> (per_image_eq lib eqa2 f2)).
Proof.
  introv na1 na2 eqiff; split; intro h.
  { eapply per_image_eq_as_equal_in_image;[eauto|].
    apply eqiff; eapply per_image_eq_as_equal_in_image;eauto. }
  { eapply per_image_eq_as_equal_in_image;[eauto|].
    apply eqiff; eapply per_image_eq_as_equal_in_image;eauto. }
Qed.

Hint Resolve iscvalue_mkc_image : slow.

Lemma tequality_mkc_image {p} :
  forall lib (T1 T2 f1 f2 : @CTerm p),
    tequality lib (mkc_image T1 f1) (mkc_image T2 f2)
    <=>
    (
      type lib T1
      # type lib T2
      # ((equal_in_image lib T1 f1) <=2=> (equal_in_image lib T2 f2))
    ).
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    destruct teq0 as [teq1 teq2].
    inversion teq1; try not_univ; clear teq1.
    inversion teq2; try not_univ; clear teq2.

    match goal with
    | [ H1 : per_image _ _ _ _ , H2 : per_image _ _ _ _ |- _ ] =>
      rename H1 into h; rename H2 into q
    end.

    allunfold @per_image; exrepnd.
    computes_to_value_isvalue; sp; try (complete (spcast; sp)).

    { exists eqa0; sp. }

    { exists eqa; sp. }

    {
      eapply eq_term_equals_trans in q0;[|apply eq_term_equals_sym;exact h0].
      clear h0.
      eapply implies_eq_equal_in_image; eauto.
    }

  - unfold type in teq0; exrepnd.
    unfold type in teq1; exrepnd.
    exists (per_image_eq lib eq f1); split; eauto 2 with slow; apply CL_image; unfold per_image.
    { exists eq T1 f1; sp; spcast; apply computes_to_valc_refl; eauto 2 with slow. }
    { exists eq0 T2 f2; sp; spcast; try (apply computes_to_valc_refl; eauto 2 with slow).
      eapply implies_eq_per_image_eq; eauto. }
Qed.
