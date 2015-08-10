(*

  Copyright 2014 Cornell University

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


Require Export per_props_equality.
Require Export cequiv_tacs.

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
    ((t ===>(lib) mkc_axiom)
     # (u ===>(lib) mkc_axiom)
     # type lib A
     # (inhabited_type lib A -> type lib B)
     # subtype_rel lib A B).
Proof.
  introv.
  rw @mkc_subtype_rel_eq.
  rw @equality_in_member.
  rw @equality_in_fun.
  split; intro k; repnd; dands; auto.

  - introv e.
    apply k in e.
    pose proof (cequivc_apply_id lib a) as e1.
    pose proof (cequivc_apply_id lib a') as e2.
    apply (equality_trans _ _ (mkc_apply mkc_id a)).
    + apply equality_sym; apply equality_respects_cequivc; auto.
      apply equality_refl in e; auto.
    + apply (equality_trans _ _ (mkc_apply mkc_id a')); auto.
      apply equality_respects_cequivc; auto.
      apply equality_sym in e; apply equality_refl in e; auto.

  - introv e.
    apply k in e.
    pose proof (cequivc_apply_id lib a) as e1.
    pose proof (cequivc_apply_id lib a') as e2.
    rwg e1.
    rwg e2; auto.
Qed.

Lemma inhabited_subtype_rel {p} :
  forall lib (A B : @CTerm p),
    inhabited_type lib (mkc_subtype_rel A B)
    <=>
    (type lib A
     # (inhabited_type lib A -> type lib B)
     # subtype_rel lib A B).
Proof.
  introv; split; intro k.
  - unfold inhabited_type in k; exrepnd.
    rw @equality_in_subtype_rel in k0; repnd; dands; auto.
  - repnd.
    unfold inhabited_type.
    exists (@mkc_axiom p).
    apply equality_in_subtype_rel.
    dands; spcast; auto; apply computes_to_valc_refl; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
