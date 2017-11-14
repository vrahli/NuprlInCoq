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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys.
Require Import dest_close.
Require Export per_ceq_bar.


Lemma close_type_system_eq {p} :
  forall lib (bar : BarLib lib) (ts : cts(p))
         T T' (eq : per) A B a1 a2 b1 b2 eqa,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T ==b==>(bar) (mkc_equality a1 a2 A)
    -> T' ==b==>(bar) (mkc_equality b1 b2 B)
    -> all_in_bar_ext bar (fun lib' x => close ts lib' A B (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a1 b1)
    -> all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a2 b2)
    -> (eq <=2=> (per_eq_eq lib a1 a2 eqa))
    -> per_eq_bar (close ts) lib T T' eq
    -> all_in_bar_ext bar (fun lib' x => type_sys_props4 (close ts) lib' A B (eqa lib' x))
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tsts dou mon c1 c2 X1 eos1 eos2 eqiff per; introv IHX1.

  prove_type_sys_props4 SCase; intros.

  + SCase "uniquely_valued".
    clear per.
    dclose_lr;[].

    allunfold @per_eq_bar; exrepnd.
    introv; allrw.

    pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 a0 a3 A A0) as q1.
    repeat (autodimp q1 hyp);[].
    pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 a0 a3 A A0) as q2.
    repeat (autodimp q2 hyp);[].
    pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 a0 a3 A A0) as q3.
    repeat (autodimp q3 hyp);[].

    eapply implies_iff_per_eq_eq; eauto 5 with slow refl.

  + SCase "type_symmetric".
    clear per.
    repdors; subst; dclose_lr.
    allunfold @per_eq_bar; exrepd.
    apply CL_eq; unfold per_eq_bar.

    pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 a0 a3 A A0) as h1.
    repeat (autodimp h1 hyp);[].
    pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 a0 a3 A A0) as h2.
    repeat (autodimp h2 hyp);[].
    pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 a0 a3 A A0) as h3.
    repeat (autodimp h3 hyp);[].

    pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans (close ts) lib (intersect_bars bar bar0) A B A0 B0 eqa eqa0) as q.
    repeat (autodimp q hyp); eauto 3 with slow;[].

    (* 1 *)
    exists A B0 a1 a2 b0 b3 eqa; sp; spcast; sp.

    {
      exists (intersect_bars bar bar0).
      dands; auto; eauto 3 with slow.

      - eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2; eauto 3 with slow.

      - eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.

      - eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.
    }

    {
      eapply eq_term_equals_trans;[apply eq_term_equals_sym;eauto|].
      eapply eq_term_equals_trans;[eauto|].
      apply eq_term_equals_sym.
      eapply implies_iff_per_eq_eq; eauto 3 with slow.
    }

  + SCase "type_value_respecting".
    clear per.
    repdors; subst; apply CL_eq; allunfold @per_eq_bar; sp.

    {
      rename_hyp_with @ccequivc_ext ceq.
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto].
      exists A A a1 a2 a1 a2 eqa; dands; auto.
      exists bar; dands; auto; eauto 3 with slow.
    }

    {
      rename_hyp_with @ccequivc_ext ceq.
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto].
      exists B B b1 b2 b1 b2 eqa; dands; auto.

      - exists bar; dands; auto; eauto 3 with slow.

      - eapply eq_term_equals_trans;[eauto|].
        eapply eqorceq_implies_iff_per_eq_eq; eauto 2 with slow.
    }

  + SCase "type_value_respecting_trans".
    clear per.
    eapply type_equality_respecting_trans_per_eq_bar_implies; eauto.
    introv e ceq cl.
    repndors; subst; allunfold @per_eq_bar; exrepnd.

    {
      dup cl1 as cl'.
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in cl';[|apply ccequivc_ext_sym;eauto].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 a0 a3 A A0) as h1.
      repeat (autodimp h1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 a0 a3 A A0) as h2.
      repeat (autodimp h2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 a0 a3 A A0) as h3.
      repeat (autodimp h3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in h3.
      pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans (close ts) lib (intersect_bars bar bar0) A B A0 B0 eqa eqa0) as h4.
      repeat (autodimp h4 hyp); eauto 3 with slow;[].

      exists A B0 a1 a2 b0 b3 eqa; dands; auto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow.
        { eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2; eauto 3 with slow. }
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow. }
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow. }

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym;eauto 3 with slow.
        eapply implies_iff_per_eq_eq; eauto; eauto 3 with slow.
    }

    {
      dup cl1 as cl'.
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in cl';[|apply ccequivc_ext_sym;eauto].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T' b1 b2 a0 a3 B A0) as h1.
      repeat (autodimp h1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T' b1 b2 a0 a3 B A0) as h2.
      repeat (autodimp h2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T' b1 b2 a0 a3 B A0) as h3.
      repeat (autodimp h3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in h3.
      pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans (close ts) lib (intersect_bars bar bar0) B A A0 B0 eqa eqa0) as h4.
      repeat (autodimp h4 hyp); eauto 3 with slow;[].

      exists B B0 b1 b2 b0 b3 eqa; dands; auto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow.
        { eapply all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans2; eauto 3 with slow. }
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow. }
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow. }

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym;eauto 3 with slow.
        eapply implies_iff_per_eq_eq; eauto; eauto 3 with slow.
    }

    {
      dup cl3 as cl'.
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in cl';[|apply ccequivc_ext_sym;eauto].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 b0 b3 A B0) as h1.
      repeat (autodimp h1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 b0 b3 A B0) as h2.
      repeat (autodimp h2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 b0 b3 A B0) as h3.
      repeat (autodimp h3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in h3.
      pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans3 (close ts) lib (intersect_bars bar bar0) A B B0 A0 eqa eqa0) as h4.
      repeat (autodimp h4 hyp); eauto 3 with slow;[].
      exists A A0 a1 a2 a0 a3 eqa; dands; auto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow.
        { eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans4; eauto 3 with slow. }
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym; eauto 3 with slow. }
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym; eauto 3 with slow. }

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym;eauto 3 with slow.
        eapply (eqorceq_implies_iff_per_eq_eq _  (intersect_bars bar bar0)); eauto 3 with slow.

        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym; eauto 3 with slow. }

        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym; eauto 3 with slow. }
    }

    {
      dup cl3 as cl'.
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in cl';[|apply ccequivc_ext_sym;eauto].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T' b1 b2 b0 b3 B B0) as h1.
      repeat (autodimp h1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T' b1 b2 b0 b3 B B0) as h2.
      repeat (autodimp h2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T' b1 b2 b0 b3 B B0) as h3.
      repeat (autodimp h3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in h3.
      pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans3 (close ts) lib (intersect_bars bar bar0) B A B0 A0 eqa eqa0) as h4.
      repeat (autodimp h4 hyp);eauto 3 with slow;[].
      exists B A0 b1 b2 a0 a3 eqa; dands; auto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow.
        { eapply all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans4; eauto 3 with slow. }
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym; eauto 3 with slow. }
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym; eauto 3 with slow. }

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym;eauto 3 with slow.
        eapply (eqorceq_implies_iff_per_eq_eq _  (intersect_bars bar bar0)); eauto 3 with slow.

        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym; eauto 3 with slow. }

        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym; eauto 3 with slow. }
    }

  + SCase "term_symmetric".
    clear per.
    introv ee.
    apply eqiff in ee; apply eqiff.
    unfold per_eq_eq, per_eq_eq1 in *; exrepnd.
    exists bar0.
    introv br ext; introv.
    pose proof (ee0 lib' br lib'0 ext x) as ee0; simpl in ee0.
    repnd; dands; auto.

  + SCase "term_transitive".
    clear per.
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff.
    unfold per_eq_eq, per_eq_eq1 in *; exrepnd.
    exists (intersect_bars bar1 bar0).
    introv br ext; introv; simpl in *; exrepnd.
    pose proof (ee2 lib1 br0 lib'0 (lib_extends_trans ext br3) x) as ee2; simpl in ee2.
    pose proof (ee0 lib2 br2 lib'0 (lib_extends_trans ext br1) x) as ee0; simpl in ee0.
    repnd; dands; auto.

  + SCase "term_value_respecting".
    clear per.
    introv ee ceq.
    apply eqiff in ee; apply eqiff; clear eqiff.
    unfold per_eq_eq, per_eq_eq1 in *; exrepnd.
    exists bar0.
    introv br ext; introv.
    pose proof (ee0 lib' br lib'0 ext x) as ee0; simpl in ee0.
    repnd; dands; auto.
    pose proof (ceq lib'0) as ceq; simpl in ceq; autodimp ceq hyp; eauto 3 with slow.
    spcast; eapply cequivc_axiom; eauto.

  + SCase "type_gsymmetric".
    clear per.
    split; introv cl; dclose_lr; apply CL_eq;
      unfold per_eq_bar in *; exrepnd.

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 a0 a3 A A0) as w1.
      repeat (autodimp w1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 a0 a3 A A0) as w2.
      repeat (autodimp w2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 a0 a3 A A0) as w3.
      repeat (autodimp w3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in w3.
      pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans (close ts) lib (intersect_bars bar bar0) A B A0 B0 eqa eqa0) as w4.
      repeat (autodimp w4 hyp); eauto 3 with slow;[].

      exists B0 A b0 b3 a1 a2 eqa.
      dands; auto.

      {
        exists (intersect_bars bar bar0); dands; eauto 3 with slow.

        { eapply all_in_bar_ext_type_sys_props4_implies_ts_sym;
            [apply implies_all_in_bar_ext_intersect_bars_left;eauto|].
          eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2;eauto 3 with slow. }

        { eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow;[].
          eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow. }

        { eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow;[].
          eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow. }
      }

      {
        eapply eq_term_equals_trans;[eauto|].
        eapply (eqorceq_implies_iff_per_eq_eq _ (intersect_bars bar bar0)); eauto 3 with slow sym.
        { eapply eq_term_equals_preserves_all_in_bar_ext_term_equality_symmetric; eauto 3 with slow. }
        { eapply eq_term_equals_preserves_all_in_bar_ext_term_equality_transitive; eauto 3 with slow. }
        { eapply eq_term_equals_preserves_all_in_bar_ext_term_equality_respecting; eauto 3 with slow. }
      }
    }

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 b0 b3 A B0) as w1.
      repeat (autodimp w1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 b0 b3 A B0) as w2.
      repeat (autodimp w2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 b0 b3 A B0) as w3.
      repeat (autodimp w3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in w3.

      pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans3 (close ts) lib (intersect_bars bar bar0) A B B0 A0 eqa eqa0) as w4.
      repeat (autodimp w4 hyp); eauto 3 with slow;[].

      exists A A0 a1 a2 a0 a3 eqa.
      dands; auto.

      {
        exists (intersect_bars bar bar0); dands; eauto 3 with slow.

        { eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans4;eauto 3 with slow. }

        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow. }

        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow. }
      }

      {
        eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym.
        eapply (eqorceq_implies_iff_per_eq_eq _ (intersect_bars bar bar0)); eauto 3 with slow.
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow. }
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow. }
      }
    }

  + SCase "type_gtransitive".
    sp.

  + SCase "type_mtransitive".
    clear per.
    rename_hyp_with eq1 cl1.
    rename_hyp_with eq2 cl2.

    repndors; subst; dclose_lr; clear cl1 cl2;
      allunfold @per_eq_bar; exrepnd.

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 b0 b3 A B0) as w1.
      repeat (autodimp w1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 b0 b3 A B0) as w2.
      repeat (autodimp w2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 b0 b3 A B0) as w3.
      repeat (autodimp w3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in w3.
      pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans3 (close ts) lib (intersect_bars bar bar0) A B B0 A0 eqa eqa0) as w4.
      repeat (autodimp w4 hyp); eauto 3 with slow;[].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar1 T a1 a2 a4 a5 A A1) as z1.
      repeat (autodimp z1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar1 T a1 a2 a4 a5 A A1) as z2.
      repeat (autodimp z2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar1 T a1 a2 a4 a5 A A1) as z3.
      repeat (autodimp z3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in z3.
      pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans (close ts) lib (intersect_bars bar bar1) A B A1 B1 eqa eqa1) as z4.
      repeat (autodimp z4 hyp); eauto 3 with slow;[].

      dands; apply CL_eq; unfold per_eq_bar.

      - exists A0 B1 a0 a3 b4 b5 eqa0; dands; auto.

        exists (intersect3bars bar bar0 bar1); dands; eauto 3 with slow.

        + pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2 (close ts) lib (intersect_bars bar bar1) A B A1 B1 eqa eqa1) as u1.
          repeat (autodimp u1 hyp); eauto 3 with slow;[].
          pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans4 (close ts) lib (intersect_bars bar bar0) A B B0 A0 eqa eqa0) as u2.
          repeat (autodimp u2 hyp); eauto 3 with slow;[].
          eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1 in u1; try (exact w4); eauto 3 with slow;[].
          eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1 in u2; try (exact w4); eauto 3 with slow;[].

          pose proof (all_in_bar_ext_type_sys_props4_trans2 (close ts) lib (intersect3bars bar bar0 bar1) A B A0 B1 eqa eqa0) as q.
          repeat (autodimp q hyp); eauto 3 with slow.

          eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1; eauto 3 with slow.
          eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2; eauto 3 with slow.

        + eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
          apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b0 _ A B); eauto 4 with slow;[].
          apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a4); eauto 4 with slow;[].
          apply all_in_bar_ccequivc_sym.
          eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

        + eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
          apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b3 _ A B); eauto 4 with slow;[].
          apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a5); eauto 4 with slow;[].
          apply all_in_bar_ccequivc_sym.
          eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

      - exists A0 B1 a0 a3 b4 b5 eqa0; dands; auto.

        + exists (intersect3bars bar bar0 bar1); dands; eauto 3 with slow.

          * pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2 (close ts) lib (intersect_bars bar bar1) A B A1 B1 eqa eqa1) as u1.
            repeat (autodimp u1 hyp); eauto 3 with slow;[].
            pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans4 (close ts) lib (intersect_bars bar bar0) A B B0 A0 eqa eqa0) as u2.
            repeat (autodimp u2 hyp); eauto 3 with slow;[].
            eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1 in u1; try (exact w4); eauto 3 with slow;[].
            eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1 in u2; try (exact w4); eauto 3 with slow;[].

            pose proof (all_in_bar_ext_type_sys_props4_trans2 (close ts) lib (intersect3bars bar bar0 bar1) A B A0 B1 eqa eqa0) as q.
            repeat (autodimp q hyp); eauto 3 with slow.

            eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1; eauto 3 with slow.
            eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2; eauto 3 with slow.

          * eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b0 _ A B); eauto 4 with slow;[].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a4); eauto 4 with slow;[].
            apply all_in_bar_ccequivc_sym.
            eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

          * eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b3 _ A B); eauto 4 with slow;[].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a5); eauto 4 with slow;[].
            apply all_in_bar_ccequivc_sym.
            eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

        + eapply eq_term_equals_trans;[eauto|].
          apply (eqorceq_implies_iff_per_eq_eq _ (intersect3bars bar bar0 bar1)); eauto 5 with slow.

          * eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow].
            apply all_in_bar_ext_eq_term_equals_sym; eauto 3 with slow.

          * eapply (all_in_bar_ext_eqorceq_eq_term_equals _ _ eqa);
              [|eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow];apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ b0); eauto 3 with slow.
            { eapply all_in_bar_ccequivc_trans; eauto 3 with slow. }
            { eapply implies_all_in_bar_ext_eqorceq_sym; eauto 4 with slow. }

          * eapply (all_in_bar_ext_eqorceq_eq_term_equals _ _ eqa);
              [|eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow];apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ b3); eauto 3 with slow.
            { eapply all_in_bar_ccequivc_trans; eauto 3 with slow. }
            { eapply implies_all_in_bar_ext_eqorceq_sym; eauto 4 with slow. }
    }

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T' b1 b2 b0 b3 B B0) as w1.
      repeat (autodimp w1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T' b1 b2 b0 b3 B B0) as w2.
      repeat (autodimp w2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T' b1 b2 b0 b3 B B0) as w3.
      repeat (autodimp w3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in w3.
      pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans3 (close ts) lib (intersect_bars bar bar0) B A B0 A0 eqa eqa0) as w4.
      repeat (autodimp w4 hyp); eauto 3 with slow;[].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar1 T' b1 b2 a4 a5 B A1) as z1.
      repeat (autodimp z1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar1 T' b1 b2 a4 a5 B A1) as z2.
      repeat (autodimp z2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar1 T' b1 b2 a4 a5 B A1) as z3.
      repeat (autodimp z3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in z3.
      pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans (close ts) lib (intersect_bars bar bar1) B A A1 B1 eqa eqa1) as z4.
      repeat (autodimp z4 hyp); eauto 3 with slow;[].

      dands; apply CL_eq; unfold per_eq_bar.

      - exists A0 B1 a0 a3 b4 b5 eqa0; dands; auto.

        exists (intersect3bars bar bar0 bar1); dands; eauto 3 with slow.

        + pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans2 (close ts) lib (intersect_bars bar bar1) B A A1 B1 eqa eqa1) as u1.
          repeat (autodimp u1 hyp); eauto 3 with slow;[].
          pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans4 (close ts) lib (intersect_bars bar bar0) B A B0 A0 eqa eqa0) as u2.
          repeat (autodimp u2 hyp); eauto 3 with slow;[].

          eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1 in u1; try (exact w4); eauto 3 with slow;[].
          eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1 in u2; try (exact w4); eauto 3 with slow;[].

          pose proof (all_in_bar_ext_type_sys_props4_sym_trans2 (close ts) lib (intersect3bars bar bar0 bar1) B A A0 B1 eqa eqa0) as q.
          repeat (autodimp q hyp); eauto 3 with slow.

          eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1; eauto 3 with slow.
          eapply all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans2; eauto 3 with slow.

        + eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
          apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b0 _ A B); eauto 4 with slow;[].
          apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a4); eauto 4 with slow;[].
          apply all_in_bar_ccequivc_sym.
          eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

        + eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
          apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b3 _ A B); eauto 4 with slow;[].
          apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a5); eauto 4 with slow;[].
          apply all_in_bar_ccequivc_sym.
          eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

      - exists A0 B1 a0 a3 b4 b5 eqa0; dands; auto.

        + exists (intersect3bars bar bar0 bar1); dands; eauto 3 with slow.

          * pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans2 (close ts) lib (intersect_bars bar bar1) B A A1 B1 eqa eqa1) as u1.
            repeat (autodimp u1 hyp); eauto 3 with slow.
            pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans4 (close ts) lib (intersect_bars bar bar0) B A B0 A0 eqa eqa0) as u2.
            repeat (autodimp u2 hyp); eauto 3 with slow.

            eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1 in u1; try (exact w4); eauto 3 with slow;[].
            eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1 in u2; try (exact w4); eauto 3 with slow;[].
            pose proof (all_in_bar_ext_type_sys_props4_sym_trans2 (close ts) lib (intersect3bars bar bar0 bar1) B A A0 B1 eqa eqa0) as q.
            repeat (autodimp q hyp); eauto 3 with slow.

            eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1; eauto 3 with slow.
            eapply all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans2; eauto 3 with slow.

          * eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b0 _ A B); eauto 4 with slow;[].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a4); eauto 4 with slow;[].
            apply all_in_bar_ccequivc_sym.
            eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

          * eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b3 _ A B); eauto 4 with slow;[].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a5); eauto 4 with slow;[].
            apply all_in_bar_ccequivc_sym.
            eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

        + eapply eq_term_equals_trans;[eauto|].
          apply (eqorceq_implies_iff_per_eq_eq _ (intersect3bars bar bar0 bar1)); eauto 5 with slow.

          * eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow].
            apply all_in_bar_ext_eq_term_equals_sym; eauto 3 with slow.

          * eapply (all_in_bar_ext_eqorceq_eq_term_equals _ _ eqa);
              [|eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow];apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ b0); eauto 3 with slow.
            { eapply all_in_bar_ccequivc_trans; eauto 3 with slow. }
            { eapply implies_all_in_bar_ext_eqorceq_sym; eauto 4 with slow. }

          * eapply (all_in_bar_ext_eqorceq_eq_term_equals _ _ eqa);
              [|eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow];apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ b3); eauto 3 with slow.
            { eapply all_in_bar_ccequivc_trans; eauto 3 with slow. }
            { eapply implies_all_in_bar_ext_eqorceq_sym; eauto 4 with slow. }
    }
Qed.
