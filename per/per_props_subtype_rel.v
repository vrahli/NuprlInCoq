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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export per_props_equality.
Require Export per_props_function.
Require Export cequiv_tacs.


Hint Rewrite @mkc_var_substc : slow.
Hint Rewrite @substc_cvterm_var : slow.

Lemma if_member_vsubtype {p} :
  forall lib (A : @CTerm p) v B r,
    member lib r (mkc_vsubtype A v B)
    -> forall x y, equality lib x y A -> equality lib x y B.
Proof.
  introv; rewrite <- fold_mkc_vsubtype; introv m e.
  apply member_mkc_member_implies in m; exrepnd; spcast.
  clear m0 m2.
  apply equality_refl in m1.

  apply equality_in_function in m1; repnd.

  appdup m1 in e.

  eapply equality_respects_cequivc_left in e0;[|apply cequivc_beta].
  eapply equality_respects_cequivc_right in e0;[|apply cequivc_beta].
  autorewrite with slow in *; auto.
Qed.


Lemma mkc_subtype_rel_eq {o} :
  forall (a b : @CTerm o),
    mkc_subtype_rel a b = mkc_member mkc_id (mkc_fun a b).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.

Definition subtype_rel {o} lib (A B : @CTerm o) :=
  forall a a', equality lib a a' A -> equality lib a a' B.

Lemma equality_in_subtype_rel {p} :
  forall lib (t u A B : @CTerm p),
    equality lib t u (mkc_subtype_rel A B)
    <=>
    { x1 , x2 , y1 , y2 : CTerm
    , (t ===>(lib) (mkc_prefl x1 y1))
    # (u ===>(lib) (mkc_prefl x2 y2))
    # equality lib x1 mkc_id (mkc_fun A B)
    # equality lib x2 mkc_id (mkc_fun A B)
    # equality lib y1 y2 (mkc_fun A B)
    # type lib A
    # (inhabited_type lib A -> type lib B)
    # subtype_rel lib A B }.
Proof.
  introv.
  rw @mkc_subtype_rel_eq.
  rw @equality_in_member.

  split; intro k; exrepnd.

  - exists x y z w; dands; auto; eauto 2 with nequality slow;
      try (complete (rw @equality_in_fun in k1; tcsp)).

    clear k1 k4.
    apply equality_refl in k3.
    rw @equality_in_fun in k3; repnd.
    introv xx.
    applydup k3 in xx.
    eapply equality_respects_cequivc_left in xx0;[|apply cequivc_apply_id].
    eapply equality_respects_cequivc_right in xx0;[|apply cequivc_apply_id].
    auto.

  - exists x1 x2 y1 y2.
    dands; eauto 2 with nequality.
Qed.

Lemma subtype_rel_implies_mkc_id_in_mkc_fun {o} :
  forall lib (A B : @CTerm o),
    type lib A
    -> (inhabited_type lib A -> type lib B)
    -> subtype_rel lib A B
    -> member lib mkc_id (mkc_fun A B).
Proof.
  introv tA tB sr.
  apply equality_in_fun; dands; auto.
  introv e.
  applydup sr in e.
  eapply equality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_apply_id|].
  eapply equality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_apply_id|].
  auto.
Qed.

Lemma inhabited_subtype_rel {o} :
  forall lib (A B : @CTerm o),
    inhabited_type lib (mkc_subtype_rel A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # subtype_rel lib A B).
Proof.
  introv; split; intro k.

  - unfold inhabited_type in k; exrepnd.
    rw @equality_in_subtype_rel in k0; exrepnd.
    dands; auto.

  - repnd.
    unfold inhabited_type.
    exists (@mkc_prefl o mkc_id mkc_id).
    apply equality_in_subtype_rel.
    exists (@mkc_id o) (@mkc_id o) (@mkc_id o) (@mkc_id o).
    dands; spcast; auto; eauto 3 with slow;
      apply subtype_rel_implies_mkc_id_in_mkc_fun; auto.
Qed.
