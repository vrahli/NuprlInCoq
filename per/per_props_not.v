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


Require Export per_props_false.
Require Export per_props_function.


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
    try (apply @computes_to_valc_refl; apply @iscvalue_mkc_approx);
      introv; split; intro k; repnd; sp; spcast.
    eapply not_axiom_approxc_bot in k; sp.

  - sp.
Qed.

Lemma tequality_void {p} :
  forall lib, @tequality p lib mkc_void mkc_void.
Proof.
  introv; rw @mkc_void_eq_mkc_false; sp.
Qed.
Hint Immediate tequality_void.

Lemma tequality_not {p} :
  forall lib (A1 A2 : @CTerm p),
    tequality lib (mkc_not A1) (mkc_not A2)
    <=>
    tequality lib A1 A2.
Proof.
  intros.
  rw @tequality_fun; split; sp.
Qed.

Lemma equality_in_not {p} :
  forall lib (t1 t2 A : @CTerm p),
    equality lib t1 t2 (mkc_not A)
    <=>
    (type lib A # !inhabited_type lib A).
Proof.
  introv.
  rw @equality_in_fun; split; intro e; repnd; dands; auto; try (complete sp).

  intro inh.
  destruct inh.
  discover.
  allapply @equality_in_void; sp.

  introv ea.
  apply equality_in_void.
  apply e.
  exists a.
  allapply @equality_refl; auto.
Qed.
