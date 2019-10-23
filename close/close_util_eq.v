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


Lemma implies_eq_term_equals_eq_per_eq {o} :
  forall lib a b (eqa eqb : per(o)),
    (eqa <=2=> eqb)
    -> (eq_per_eq lib a b eqa) <=2=> (eq_per_eq lib a b eqb).
Proof.
  introv eqiff; introv; unfold eq_per_eq; introv; split; intro h; repnd; dands;
    auto; apply eqiff; auto.
Qed.

Lemma per_bar_eq_eq_per_eq_bar_lib_per {o} :
  forall (lib : @library o) a b (eqa : lib-per(lib,o)),
    (per_bar_eq lib (eq_per_eq_bar_lib_per lib a b eqa))
    <=2=> (eq_per_eq_bar lib a b eqa).
Proof.
  introv; simpl; split; intro h; eauto 3 with slow.

  - unfold eq_per_eq_bar.
    eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold eq_per_eq_bar in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_eq_per_eq; try exact h;
      try apply (lib_per_cond _ eqa).

  - unfold eq_per_eq_bar in *.
    apply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold eq_per_eq_bar.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_eq_per_eq; try exact h;
      try apply (lib_per_cond _ eqa).
Qed.
