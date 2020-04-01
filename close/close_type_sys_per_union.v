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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export close_util_union2.


Lemma close_type_system_union {o} :
  forall (ts : cts(o))
         uk
         lib
         T T'
         (eq : per)
         A1 A2 B1 B2 (eqa eqb : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ccomputes_to_valc_ext lib T (mkc_union A1 B1)
    -> ccomputes_to_valc_ext lib T' (mkc_union A2 B2)
    -> in_ext_ext lib (fun lib' x => close ts uk lib' A1 A2 (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' A1 A2 (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => close ts uk lib' B1 B2 (eqb lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' B1 B2 (eqb lib' x))
    -> (eq <=2=> (per_union_eq_bar lib eqa eqb))
    -> type_sys_props4 (close ts) uk lib T T' eq.
Proof.
  introv tysys dou mon c1 c2 cla tsa clb tsb eqiff.

  prove_type_sys_props4 SCase; introv.

  - SCase "uniquely_valued".
    introv cl.
    dclose_lr; clear cl.
    eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    eapply per_bar_per_union_implies_eq_term_equals_per_union_eq_bar;
      try exact c1; eauto.

  - SCase "type_symmetric".
    introv cl eqs.
    dclose_lr; clear cl.
    apply per_bar_per_union_implies_close.
    eapply type_extensionality_per_bar;[eauto|]; auto.

  - SCase "type_value_respecting".
    introv h ceq.
    repndors; subst; apply CL_union.

    {
      eapply ccequivc_ext_union in ceq;[|eauto]; exrepnd; spcast.
      exists eqa eqb A1 A1 B1 B1; dands; spcast; auto.
      { eapply in_ext_ext_type_sys_props4_ccequivc_ext_implies; try exact tsa; eauto 3 with slow. }
      { eapply in_ext_ext_type_sys_props4_ccequivc_ext_implies; try exact tsb; eauto 3 with slow. }
    }

    {
      eapply ccequivc_ext_union in ceq;[|eauto]; exrepnd; spcast.
      exists eqa eqb A2 A2 B2 B2; dands; spcast; auto.
      { eapply in_ext_ext_type_sys_props4_ccequivc_ext_implies; try exact tsa; eauto 3 with slow. }
      { eapply in_ext_ext_type_sys_props4_ccequivc_ext_implies; try exact tsb; eauto 3 with slow. }
    }

  - SCase "type_value_respecting_trans1".
    eapply implies_type_value_respecting_trans1_per_union; eauto.

  - SCase "type_value_respecting_trans2".
    eapply implies_type_value_respecting_trans2_per_union; eauto.

  - SCase "term_symmetric".
    introv ee.
    apply eqiff in ee; apply eqiff; clear eqiff.
    apply per_union_eq_bar_symmetric; eauto 3 with slow.

  - SCase "term_transitive".
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff; clear eqiff.
    eapply per_union_eq_bar_transitive; eauto 3 with slow.

  - SCase "term_value_respecting".
    introv ee ceq.
    apply eqiff in ee; apply eqiff.
    eapply per_union_eq_bar_cequiv; eauto 3 with slow.

  - SCase "type_gsymmetric".
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsb'; auto.
    split; intro cl; dclose_lr; clear cl; apply per_bar_per_union_implies_close.
    { eapply per_bar_per_union_sym; try exact c1;eauto. }
    { eapply per_bar_per_union_sym_rev; try exact c1;eauto. }

  - SCase "type_gtransitive".
    apply CL_union.
    eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.

  - SCase "type_mtransitive".
    introv ee cl1 cl2.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsb'.

    repndors; subst; dclose_lr; clear cl1 cl2; dands; apply per_bar_per_union_implies_close.

    { eapply per_bar_per_union_trans1; try exact c1; try exact h; try exact h0; eauto. }
    { eapply per_bar_per_union_trans2; try exact c1; try exact h; try exact h0; eauto. }
    { eapply per_bar_per_union_trans3; try exact c2; try exact h; try exact h0; eauto. }
    { eapply per_bar_per_union_trans4; try exact c2; try exact h; try exact h0; eauto. }
Qed.
