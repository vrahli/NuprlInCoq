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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

 *)


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.


Hint Resolve iscvalue_mkc_approx : slow.
Hint Resolve approxc_refl : slow.
Hint Resolve computes_to_valc_refl : slow.


Lemma nuprl_mkc_true {o} :
  forall lib,
    @nuprl o lib
           mkc_true
           mkc_true
           (fun t t' => t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom).
Proof.
  introv.
  apply CL_approx.
  rw @mkc_true_eq.
  unfold per_approx.
  eexists; eexists; eexists; eexists; dands; spcast;
    try (apply computes_to_valc_refl; eauto 3 with slow); tcsp;[].
  introv; split; sp; spcast; eauto 3 with slow.
Qed.

Lemma tequality_true {p} :
  forall lib, @tequality p lib mkc_true mkc_true.
Proof.
  introv.
  eapply tequality_if_nuprl; apply nuprl_mkc_true.
Qed.
Hint Immediate tequality_true.
Hint Resolve tequality_true : slow.

Lemma equality_axiom_true {p} :
  forall lib, @equality p lib mkc_axiom mkc_axiom mkc_true.
Proof.
  introv.
  eapply eq_equality1;[|apply nuprl_mkc_true]; simpl.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Immediate equality_axiom_true.
Hint Resolve equality_axiom_true : slow.
