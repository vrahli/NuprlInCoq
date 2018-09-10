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


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.



Lemma nuprl_mkc_true {o} :
  forall lib, @nuprl o lib
                     mkc_true
                     mkc_true
                     (fun t t' => t ===>(lib) mkc_axiom # t' ===>(lib) mkc_axiom).
Proof.
  introv.
  apply CL_approx.
  rw @mkc_true_eq.
  unfold per_approx.
  eexists; eexists; eexists; eexists; dands; spcast.
  apply computes_to_valc_refl; apply iscvalue_mkc_approx.
  apply computes_to_valc_refl; apply iscvalue_mkc_approx.
  sp.
  introv; split; sp; spcast.
  apply approxc_refl.
Qed.

Lemma tequality_true {p} :
  forall lib, @tequality p lib mkc_true mkc_true.
Proof. intro. pose proof (@nuprl_mkc_true p lib) as xx. eapply tequality_if_nuprl. eauto. 
Qed.
Hint Immediate tequality_true.

Lemma equality_axiom_true {p} :
  forall lib, @equality p lib mkc_axiom mkc_axiom mkc_true.
Proof. intro. pose proof (@nuprl_mkc_true p lib) as xx.  eapply eq_equality1.
 2: { eauto. } 
 simpl. split; unfold ccomputes_to_valc; spcast; apply computes_to_valc_refl; auto.
Qed.
Hint Immediate equality_axiom_true.


