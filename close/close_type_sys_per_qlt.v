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


Require Export close_util_qlt2.


Lemma close_type_system_qlt {o} :
  forall (ts : cts(o))
         lib
         T T'
         (eq : per)
         a b a' b',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T (mkc_qlt a b)
    -> ccomputes_to_valc_ext lib T' (mkc_qlt a' b')
    -> ccequivc_ext lib a a'
    -> ccequivc_ext lib b b'
    -> (eq <=2=> (equality_of_qlt_bar lib a b))
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tysys dou mon c1 c2 ceqa ceqb eqiff.

  prove_type_sys_props4 SCase; introv.

  - SCase "uniquely_valued".
    introv cl.
    dclose_lr; clear cl.
    eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    eapply equality_of_qlt_bar_implies_eq_term_equals_equality_of_qlt_bar; eauto.

  - SCase "type_symmetric".
    introv cl eqs.
    dclose_lr; clear cl.
    apply per_bar_per_qlt_implies_close.
    eapply type_extensionality_per_bar;[eauto|]; auto.

  - SCase "type_value_respecting".
    introv h ceq.
    repndors; subst; apply CL_qlt.

    {
      eapply ccequivc_ext_qlt in ceq;[|eauto]; exrepnd; spcast.
      eexists; eexists; eexists; eexists; dands; eauto 3 with slow.
    }

    {
      eapply ccequivc_ext_qlt in ceq;[|eauto]; exrepnd; spcast.
      eexists; eexists; eexists; eexists; dands; try exact c2; try exact eqiff; eauto 3 with slow.
      eapply eq_term_equals_trans;[eauto|].
      apply implies_eq_term_equals_per_qlt_bar2; auto.
    }

  - SCase "type_value_respecting_trans1".
    eapply implies_type_value_respecting_trans1_per_qlt; eauto.

  - SCase "type_value_respecting_trans2".
    eapply implies_type_value_respecting_trans2_per_qlt; eauto.

  - SCase "term_symmetric".
    introv ee.
    apply eqiff in ee; apply eqiff; clear eqiff; tcsp.

  - SCase "term_transitive".
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff; clear eqiff; tcsp.

  - SCase "term_value_respecting".
    introv ee ceq.
    apply eqiff in ee; apply eqiff; tcsp.

  - SCase "type_gsymmetric".
    split; intro cl; dclose_lr; clear cl; apply per_bar_per_qlt_implies_close.
    { eapply per_bar_per_qlt_sym_rev; try exact c1;eauto. }
    { eapply per_bar_per_qlt_sym_rev; try exact c1;eauto. }

  - SCase "type_gtransitive".
    apply CL_qlt.
    eexists; eexists; eexists; eexists; dands; spcast; eauto.

  - SCase "type_mtransitive".
    introv ee cl1 cl2.
    repndors; subst; dclose_lr; clear cl1 cl2; dands; apply per_bar_per_qlt_implies_close.

    { eapply per_bar_per_qlt_trans1; try exact c1; try exact h; try exact h0; eauto. }
    { eapply per_bar_per_qlt_trans2; try exact c1; try exact h; try exact h0; eauto. }
    { eapply per_bar_per_qlt_trans1; try exact c2; try exact h; try exact h0; eauto. }
    { eapply per_bar_per_qlt_trans2; try exact c2; try exact h; try exact h0; eauto. }
Qed.
