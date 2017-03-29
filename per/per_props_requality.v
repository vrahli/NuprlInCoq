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

  Authors: Vincent Rahli

*)


Require Export per_props_cequiv.
Require Export per_props_function.
Require Export per_props_uni.


Lemma equality_in_mkc_requality {p} :
  forall lib (t1 t2 T a b : @CTerm p),
    equality lib a b (mkc_requality t1 t2 T)
    <=>
    { x1 , x2  : CTerm
    , a ===>(lib) (mkc_refl x1)
    # b ===>(lib) (mkc_refl x2)
    # equality lib t1 t2 T
    # equality lib t1 x1 T
    # equality lib t2 x2 T }.
Proof.
  introv; split; intro i.

  - unfold equality in i; exrepnd.
    inversion i1; subst; try not_univ.

    match goal with
    | [ H : per_req _ _ _ _ _ |- _ ] => rename H into h
    end.

    unfold per_req in h; exrepnd; spcast; computes_to_value_isvalue.
    fold (nuprl lib) in *.
    apply h0 in i0.
    unfold per_req_eq in i0; exrepnd.
    exists x1 x2; dands; auto;
      try (complete (eapply eq_equality1;eauto)).

  - exrepnd.
    unfold equality in i3; exrepnd.
    exists (per_req_eq lib t1 t2 eq).
    dands; auto.

    + apply CL_req.
      exists T T t1 t2 t1 t2 eq; dands; spcast; eauto 3 with slow;
        right; spcast; auto.

    + exists x1 x2; dands; auto; try (complete (eapply equality_eq1; eauto)).
Qed.

(* !!MOVE *)
Hint Resolve tequality_if_nuprl : slow.

(* !!MOVE *)
Lemma tequality_implies_type_left {p} :
  forall lib (A B : @CTerm p),
    tequality lib A B -> type lib A.
Proof.
  introv teq.
  unfold type.
  eapply tequality_refl; eauto.
Qed.
Hint Resolve tequality_implies_type_left : slow.

(* !!MOVE *)
Lemma tequality_implies_type_right {p} :
  forall lib (A B : @CTerm p),
    tequality lib A B -> type lib B.
Proof.
  introv teq.
  unfold type.
  apply tequality_sym in teq.
  eapply tequality_refl; eauto.
Qed.
Hint Resolve tequality_implies_type_right : slow.

(* !!MOVE *)
Hint Resolve eq_equality1 : slow.

Lemma tequality_mkc_requality {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_requality a1 a2 A) (mkc_requality b1 b2 B)
    <=>
    (
      tequality lib A B
      # equorsq lib a1 b1 A
      # equorsq lib a2 b2 A
    ).
Proof.
  introv; split; intro h.

  - unfold tequality in h; exrepnd.
    inversion h0; subst; try not_univ.

    match goal with
    | [ H : per_req _ _ _ _ _ |- _ ] => rename H into h
    end.

    unfold per_req in h; exrepnd; spcast; computes_to_value_isvalue.
    fold (nuprl lib) in *.
    dands; eauto 3 with slow; eapply eqorceq_iff_equorsq; eauto.

  - repnd.
    unfold tequality in h0; exrepnd.
    rename eq into eqa.
    exists (per_req_eq lib a1 a2 eqa).
    apply CL_req.
    exists A B a1 a2 b1 b2 eqa; dands; spcast; eauto 3 with slow;
      eapply eqorceq_iff_equorsq; eauto.
Qed.
