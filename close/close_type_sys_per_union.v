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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys_useful.
Require Export dest_close.
Require Export per_ceq_bar.


Lemma close_type_system_union {o} :
  forall (ts : cts(o))
         lib (bar : BarLib lib)
         T T'
         (eq : per)
         A1 A2 B1 B2 eqa eqb,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> (T ==b==>(bar) (mkc_union A1 B1))
    -> (T' ==b==>(bar) (mkc_union A2 B2))
    -> all_in_bar bar (fun lib => close ts lib A1 A2 eqa)
    -> all_in_bar bar (fun lib => type_sys_props4 (close ts) lib A1 A2 eqa)
    -> all_in_bar bar (fun lib => close ts lib B1 B2 eqb)
    -> all_in_bar bar (fun lib => type_sys_props4 (close ts) lib B1 B2 eqb)
    -> (eq <=2=> (per_union_eq_bar lib eqa eqb))
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tysys dou mon c1 c2 cla reca clb recb eqiff.

  prove_type_sys_props4 SCase; introv.

  - SCase "uniquely_valued".
    introv cl.
    dclose_lr.
    clear cl.

    allunfold @per_union_bar; exrepnd.

    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T A1 B1 A0 B0) as ceq1.
    repeat (autodimp ceq1 hyp).
    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq1.
    pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T A1 B1 A0 B0) as ceq2.
    repeat (autodimp ceq2 hyp).
    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq2.

    apply implies_eq_term_equals_per_union_bar.

    { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans; eauto. }

    { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans; eauto. }

  - SCase "type_symmetric".
    introv cl ee.
    dclose_lr; clear cl.
    apply CL_union.
    allunfold @per_union_bar; exrepnd.
    exists eqa0 eqb0 A0 A3 B0 B3; dands; auto; eauto.
    eapply eq_term_equals_trans;[apply eq_term_equals_sym;eauto|]; auto.

  - SCase "type_value_respecting".
    introv h ceq.
    repndors; subst; apply CL_union.

    { eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto].
      exists eqa eqb A1 A1 B1 B1; dands; auto.
      exists bar; dands; auto; eauto 3 with slow. }

    { eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto].
      exists eqa eqb A2 A2 B2 B2; dands; auto.
      exists bar; dands; auto; eauto 3 with slow. }

  - SCase "type_value_respecting_trans".
    introv h ceq cl.
    repndors; subst;
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;eauto;
        dclose_lr; clear cl; apply CL_union.

    {
      unfold per_union_bar in *; exrepnd.

      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T3 A1 B1 A0 B0) as ceq1.
      repeat (autodimp ceq1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T3 A1 B1 A0 B0) as ceq2.
      repeat (autodimp ceq2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq2.

      exists eqa eqb; eexists; eexists; eexists; eexists; dands; eauto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow;
          eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans2; eauto.

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym.
        apply implies_eq_term_equals_per_union_bar;
          eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans; eauto.
    }

    {
      unfold per_union_bar in *; exrepnd.

      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T3 A2 B2 A0 B0) as ceq1.
      repeat (autodimp ceq1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T3 A2 B2 A0 B0) as ceq2.
      repeat (autodimp ceq2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq2.

      exists eqa eqb; eexists; eexists; eexists; eexists; dands; eauto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow;
          eapply all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans2; eauto.

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym.
        apply implies_eq_term_equals_per_union_bar;
          eapply all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans; eauto.
    }

    {
      unfold per_union_bar in *; exrepnd.

      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T3 A1 B1 A3 B3) as ceq1.
      repeat (autodimp ceq1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T3 A1 B1 A3 B3) as ceq2.
      repeat (autodimp ceq2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq2.

      exists eqa eqb; eexists; eexists; eexists; eexists; dands; eauto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow;
          eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans4; eauto.

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym.
        apply implies_eq_term_equals_per_union_bar;
          eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans3; eauto.
    }

    {
      unfold per_union_bar in *; exrepnd.

      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T3 A2 B2 A3 B3) as ceq1.
      repeat (autodimp ceq1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T3 A2 B2 A3 B3) as ceq2.
      repeat (autodimp ceq2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq2.

      exists eqa eqb; eexists; eexists; eexists; eexists; dands; eauto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow;
          eapply all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans4; eauto.

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym.
        apply implies_eq_term_equals_per_union_bar;
          eapply all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans3; eauto.
    }

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
    eapply per_union_eq_bar_cequiv; eauto 2 with slow.

  - SCase "type_gsymmetric".
    split; introv cl; dclose_lr; clear cl; apply CL_union;
      unfold per_union_bar in *; exrepnd.

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T A1 B1 A0 B0) as q1.
      repeat (autodimp q1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T A1 B1 A0 B0) as q2.
      repeat (autodimp q2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q2.

      exists eqa0 eqb0 A3 A1 B3 B1; dands; auto.
      exists (intersect_bars bar bar0); dands; eauto 3 with slow.

      { eapply all_in_bar_type_sys_props4_implies_ts_sym2; eauto 3 with slow;[].
        eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5; eauto 3 with slow. }

      { eapply all_in_bar_type_sys_props4_implies_ts_sym2; eauto 3 with slow;[].
        eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5; eauto 3 with slow. }
    }

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T A1 B1 A3 B3) as q1.
      repeat (autodimp q1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T A1 B1 A3 B3) as q2.
      repeat (autodimp q2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q2.

      exists eqa0 eqb0 A1 A0 B1 B0; dands; auto.
      exists (intersect_bars bar bar0); dands; eauto 3 with slow.

      { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6; eauto 3 with slow. }

      { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6; eauto 3 with slow. }
    }

  - SCase "type_gtransitive".
    apply CL_union.
    eexists; eexists; eexists; eexists; eexists; eexists; dands; eauto.

  - SCase "type_mtransitive".
    introv ee cl1 cl2.
    repndors; subst; dclose_lr; clear cl1 cl2; dands; apply CL_union;
      unfold per_union_bar in *; exrepnd.

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar1 T A1 B1 A4 B4) as q1.
      repeat (autodimp q1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar1 T A1 B1 A4 B4) as q2.
      repeat (autodimp q2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q2.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T A1 B1 A3 B3) as q3.
      repeat (autodimp q3 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q3.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T A1 B1 A3 B3) as q4.
      repeat (autodimp q4 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q4.

      exists eqa0 eqb0 A0 A5 B0 B5; dands; auto;[].
      exists (intersect3bars bar bar1 bar0); dands; eauto 3 with slow.

      { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6 in h4;
          try exact reca; eauto 3 with slow;[].
        eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5 in h9;
          try exact reca; auto;[].
        eapply all_in_bar_type_sys_props4_trans4;[|eauto 3 with slow|eauto 3 with slow]; eauto 3 with slow. }

      { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6 in h2;
          try exact recb; eauto 3 with slow;[].
        eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5 in h7;
          try exact recb; auto;[].
        eapply all_in_bar_type_sys_props4_trans4;[|eauto 3 with slow|eauto 3 with slow]; eauto 3 with slow. }
    }

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar1 T A1 B1 A4 B4) as q1.
      repeat (autodimp q1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar1 T A1 B1 A4 B4) as q2.
      repeat (autodimp q2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q2.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T A1 B1 A3 B3) as q3.
      repeat (autodimp q3 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q3.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T A1 B1 A3 B3) as q4.
      repeat (autodimp q4 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q4.

      exists eqa1 eqb1 A0 A5 B0 B5; dands; auto;[].
      exists (intersect3bars bar bar1 bar0); dands; eauto 3 with slow.

      { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6 in h4;
          try exact reca; eauto 3 with slow;[].
        eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5 in h9;
          try exact reca; auto;[].
        eapply all_in_bar_type_sys_props4_trans5;[|eauto 3 with slow|eauto 3 with slow]; eauto 3 with slow. }

      { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6 in h2;
          try exact recb; eauto 3 with slow;[].
        eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5 in h7;
          try exact recb; auto;[].
        eapply all_in_bar_type_sys_props4_trans5;[|eauto 3 with slow|eauto 3 with slow]; eauto 3 with slow. }
    }

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar1 T' A2 B2 A4 B4) as q1.
      repeat (autodimp q1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar1 T' A2 B2 A4 B4) as q2.
      repeat (autodimp q2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q2.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T' A2 B2 A3 B3) as q3.
      repeat (autodimp q3 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q3.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T' A2 B2 A3 B3) as q4.
      repeat (autodimp q4 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q4.

      exists eqa0 eqb0 A0 A5 B0 B5; dands; auto;[].
      exists (intersect3bars bar bar1 bar0); dands; eauto 3 with slow.

      { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6 in h4;
          try apply all_in_bar_type_sys_props4_sym; try exact reca; eauto 3 with slow;[].
        eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5 in h9;
          try apply all_in_bar_type_sys_props4_sym; try exact reca; auto;[].
        eapply all_in_bar_type_sys_props4_trans4;[|eauto 3 with slow|eauto 3 with slow]; eauto 3 with slow. }

      { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6 in h2;
          try apply all_in_bar_type_sys_props4_sym; try exact recb; eauto 3 with slow;[].
        eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5 in h7;
          try apply all_in_bar_type_sys_props4_sym; try exact recb; auto;[].
        eapply all_in_bar_type_sys_props4_trans4;[|eauto 3 with slow|eauto 3 with slow]; eauto 3 with slow. }
    }

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar1 T' A2 B2 A4 B4) as q1.
      repeat (autodimp q1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar1 T' A2 B2 A4 B4) as q2.
      repeat (autodimp q2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q2.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T' A2 B2 A3 B3) as q3.
      repeat (autodimp q3 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q3.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T' A2 B2 A3 B3) as q4.
      repeat (autodimp q4 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in q4.

      exists eqa1 eqb1 A0 A5 B0 B5; dands; auto;[].
      exists (intersect3bars bar bar1 bar0); dands; eauto 3 with slow.

      { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6 in h4;
          try apply all_in_bar_type_sys_props4_sym; try exact reca; eauto 3 with slow;[].
        eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5 in h9;
          try apply all_in_bar_type_sys_props4_sym; try exact reca; auto;[].
        eapply all_in_bar_type_sys_props4_trans5;[|eauto 3 with slow|eauto 3 with slow]; eauto 3 with slow. }

      { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans6 in h2;
          try apply all_in_bar_type_sys_props4_sym; try exact recb; eauto 3 with slow;[].
        eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans5 in h7;
          try apply all_in_bar_type_sys_props4_sym; try exact recb; auto;[].
        eapply all_in_bar_type_sys_props4_trans5;[|eauto 3 with slow|eauto 3 with slow]; eauto 3 with slow. }
    }
Qed.
