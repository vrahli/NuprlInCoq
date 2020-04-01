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
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys.
Require Import dest_close.
Require Export per_ceq_bar.

Require Export close_util_eq.
Require Export close_util_eq2.


Lemma close_type_system_eq {o} :
  forall uk lib (ts : cts(o))
         T T' (eq : per) A B a1 a2 b1 b2 (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T (mkc_equality a1 a2 A)
    -> ccomputes_to_valc_ext lib T' (mkc_equality b1 b2 B)
    -> in_ext_ext lib (fun lib' x => close ts uk lib' A B (eqa lib' x))
    -> eqorceq_ext lib eqa a1 b1
    -> eqorceq_ext lib eqa a2 b2
    -> (eq <=2=> (eq_per_eq_bar lib a1 a2 eqa))
    -> per_eq (close ts) uk lib T T' eq
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' A B (eqa lib' x))
    -> type_sys_props4 (close ts) uk lib T T' eq.
Proof.
  introv tsts dou mon c1 c2 inextcl eos1 eos2 eqiff per; introv inexttsp.

  prove_type_sys_props4 SCase; introv.

  + SCase "uniquely_valued".
    introv cl.
    dclose_lr; clear cl.
    apply per_eq_implies_per_bar in per.
    eapply uniquely_valued_per_bar_per_eq; eauto.

  + SCase "type_symmetric".
    introv cl eqs.
    dclose_lr; clear cl.
    apply per_bar_per_eq_implies_close.
    eapply type_extensionality_per_bar; eauto.

  + SCase "type_value_respecting".
    introv h ceq.
    apply CL_eq.
    eapply ccequivc_ext_implies_per_eq1; try exact h; eauto.

  + SCase "type_value_respecting_trans1".
    eapply implies_type_equality_respecting_trans1_per_eq; eauto.

  + SCase "type_value_respecting_trans2".
    eapply implies_type_equality_respecting_trans2_per_eq; eauto.

  + SCase "term_symmetric".
    clear per.
    introv ee.
    apply eqiff in ee; apply eqiff.
    apply eq_per_eq_bar_sym; auto.

  + SCase "term_transitive".
    clear per.
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff.
    eapply eq_per_eq_bar_trans; eauto.

  + SCase "term_value_respecting".
    clear per.
    introv ee ceq.
    apply eqiff in ee; apply eqiff; clear eqiff.
    apply eq_per_eq_bar_resp; auto.

  + SCase "type_gsymmetric".
    clear per.
    dup inexttsp as inexttsp'.
    apply in_ext_ext_type_sys_props4_sym in inexttsp'.

    split; introv cl; dclose_lr; clear cl; apply per_bar_per_eq_implies_close.

    * eapply type_symmetric_per_bar_per_eq1; try exact c1; eauto.

    * eapply type_symmetric_per_bar_per_eq2; try exact c1; eauto.

  + SCase "type_gtransitive".
    sp.

  + SCase "type_mtransitive".
    clear per.
    introv h cl1 cl2.
    dup inexttsp as inexttsp'.
    apply in_ext_ext_type_sys_props4_sym in inexttsp'.

    repndors; subst; dclose_lr; clear cl1 cl2;
      dands; apply per_bar_per_eq_implies_close.

    * eapply type_transitive_per_bar_per_eq1; try exact inexttsp; eauto.

    * eapply type_transitive_per_bar_per_eq2; try exact inexttsp; eauto.

    * eapply type_transitive_per_bar_per_eq1; try exact inexttsp'; eauto.

    * eapply type_transitive_per_bar_per_eq2; try exact inexttsp'; eauto.
Qed.
