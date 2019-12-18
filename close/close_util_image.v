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


  Website: http://nuprl.org/html/verification/
  Authors: Vincent Rahli

*)


Require Export type_sys.
Require Export nuprl_mon_func.
Require Export per_ceq_bar.
Require Export close_util_bar.


Lemma implies_eq_term_equals_per_image_eq {o} :
  forall inh lib (eqa eqb : per(o)) f,
    (eqa <=2=> eqb)
    -> (per_image_eq inh lib eqa f) <=2=> (per_image_eq inh lib eqb f).
Proof.
  introv eqas; introv.
  split; introv h; induction h; eauto 2 with slow.
  { eapply image_eq_cl; eauto. }
  { eapply image_eq_eq; eauto; apply eqas; auto. }
  { eapply image_eq_cl; eauto. }
  { eapply image_eq_eq; eauto; apply eqas; auto. }
Qed.

Lemma per_bar_eq_per_image_eq_bar_lib_per {o} :
  forall inh (lib : @library o) (eqa : lib-per(inh,lib,o)) f,
    (per_bar_eq inh lib (per_image_eq_bar_lib_per inh lib eqa f))
    <=2=> (per_image_eq_bar inh lib eqa f).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.

  - unfold per_image_eq_bar.
    eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_image_eq_bar in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_image_eq; try exact h;
      try apply (lib_per_cond _ _ eqa).

  - unfold per_image_eq_bar in h.
    eapply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold per_image_eq_bar.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_per_image_eq; try exact h;
      try apply (lib_per_cond _ _ eqa).
Qed.
