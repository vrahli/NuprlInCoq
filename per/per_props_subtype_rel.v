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
  clear m1 m0.

  apply equality_in_function in m2; repnd.

  appdup m2 in e.

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
    { x , y : CTerm
    , (t ===>(lib) (mkc_refl x))
    # (u ===>(lib) (mkc_refl y))
    # equality lib x mkc_id (mkc_fun A B)
    # equality lib y mkc_id (mkc_fun A B)
    # type lib A
    # (inhabited_type lib A -> type lib B)
    # subtype_rel lib A B }.
Proof.
  introv.
  rw @mkc_subtype_rel_eq.
  rw @equality_in_member.

  split; intro k; exrepnd.

  - exists x y; dands; auto.

    { apply equality_sym; auto. }

    { apply equality_sym; auto. }

    { rw @equality_in_fun in k1; tcsp. }

    { rw @equality_in_fun in k1; tcsp. }

    { apply equality_refl in k1.
      rw @equality_in_fun in k1; repnd.
      introv xx.
      applydup k1 in xx.
      eapply equality_respects_cequivc_left in xx0;[|apply cequivc_apply_id].
      eapply equality_respects_cequivc_right in xx0;[|apply cequivc_apply_id].
      auto. }

  - exists x y.
    dands; auto.
    { apply equality_sym; auto. }
    { apply equality_sym; auto. }
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
    exists (@mkc_refl o mkc_id).
    apply equality_in_subtype_rel.
    exists (@mkc_id o) (@mkc_id o).
    dands; spcast; auto; try (apply computes_to_valc_refl; auto; eauto 2 with slow).

    + apply equality_in_fun; dands; auto.
      introv e.
      applydup k in e.
      eapply equality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_apply_id|].
      eapply equality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_apply_id|].
      auto.

    + apply equality_in_fun; dands; auto.
      introv e.
      applydup k in e.
      eapply equality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_apply_id|].
      eapply equality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_apply_id|].
      auto.
Qed.
