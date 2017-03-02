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
    allunfold @per_image; exrepnd; spcast; computes_to_value_isvalue.
    allunfold @eq_term_equals; discover.
    dands.
    exists eqa; sp.
    induction h.
    apply @eq_in_image_cl with (t := t).
    apply IHh1; allrw; sp.
    apply IHh2; allrw; sp.
    apply @eq_in_image_eq with (a1 := a1) (a2 := a2); sp.
    exists eqa; sp.

  - exrepnd.
    unfold type, tequality in e0; exrepnd.
    exists (per_image_eq lib eq f); dands.
    apply CL_image; unfold per_image.
    exists eq T T f f; sp; spcast; sp;
    try (apply computes_to_valc_refl; apply iscvalue_mkc_image).
    induction e.
    apply @image_eq_cl with (t := t); sp.
    apply @image_eq_eq with (a1 := a1) (a2 := a2); sp.
    allunfold @equality; exrepnd.
    generalize (nuprl_uniquely_valued lib T eq eq0); intro h; repeat (dest_imp h hyp).
    rw h; sp.
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

Lemma tequality_mkc_image {p} :
  forall lib (T1 T2 f1 f2 : @CTerm p),
    tequality lib (mkc_image T1 f1) (mkc_image T2 f2)
    <=> (tequality lib T1 T2 # ccequivc lib f1 f2).
Proof.
  introv; split; intro teq; repnd.

  - unfold tequality in teq; exrepnd.
    inversion teq0; try not_univ; allunfold @per_image; exrepnd.
    computes_to_value_isvalue; sp; try (complete (spcast; sp)).
    exists eqa; sp.

  - unfold tequality in teq0; exrepnd.
    exists (per_image_eq lib eq f1); apply CL_image; unfold per_image.
    exists eq T1 T2 f1 f2; sp; spcast;
    apply computes_to_valc_refl; apply iscvalue_mkc_image.
Qed.
