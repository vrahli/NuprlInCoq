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


  Website: http://nuprl.org/html/verification/

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys_useful.
Require Import dest_close.
Require Export per_ceq_bar.

Require Export close_util_func.


Lemma close_type_system_func {o} :
  forall lib (ts : cts(o))
         T T'
         (eq : per)
         A A' v v' B B'
         (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> computes_to_valc lib T (mkc_function A v B)
    -> computes_to_valc lib T' (mkc_function A' v' B')
    -> in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall (a a' : CTerm) (e : eqa lib' x a a'),
              close ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall (a a' : CTerm) (e : eqa lib' x a a'),
              type_sys_props4 (close ts) lib' (substc a v B) (substc a' v' B')
                              (eqb lib' x a a' e))
    -> (eq <=2=> (per_func_ext_eq lib eqa eqb))
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp1 comp2 cla tysysa clb tysysb eqiff.

  prove_type_sys_props4 SCase; introv.

  + SCase "uniquely_valued".
    introv cl.
    dclose_lr.

    (* Why is dclose_lr not working? *)

XXX
    clear cl.

    allunfold @per_func_ext; exrepnd.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
    apply eq_term_equals_per_func_ext_eq; eauto 3 with slow.

  + SCase "type_symmetric".
    introv cl eqs.
    dclose_lr.
    apply CL_func.

    allunfold @per_func_ext; exrepnd.
    exists eqa0 eqb0.
    dands; auto.
    eapply eq_term_equals_trans;[apply eq_term_equals_sym;eauto|];auto.

  + SCase "type_value_respecting".
    introv ee ceq; repndors; subst; apply CL_func;
      exists eqa eqb; dands; auto.

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      eapply type_family_ext_cequivc; eauto.
    }

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      eapply type_family_ext_cequivc2; eauto.
    }

  + SCase "type_value_respecting_trans".
    introv ee ceq cl.
    repndors; subst.

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_func.
      unfold per_func_ext in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans1; eauto 3 with slow.
    }

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_func.
      unfold per_func_ext in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans2; eauto 3 with slow.
    }

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_func.
      unfold per_func_ext in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans3; eauto 3 with slow.
    }

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_func.
      unfold per_func_ext in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans4; eauto 3 with slow.
    }

  + SCase "term_symmetric".
    introv ee.
    apply eqiff in ee; apply eqiff; clear eqiff.
    introv.
    pose proof (ee lib' e) as ee; simpl in *; introv.

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa lib' e a a) as e1 by (eauto).
    assert (eqa lib' e a' a) as e2 by (eauto).

    pose proof (eq_term_equals_sym_tsp
                  (close ts) lib' (eqa lib' e) (eqb lib' e) a a' e1 e0 e2 v B v' B') as q.
    repeat (autodimp q hyp).
    { introv; apply type_sys_props4_implies_type_sys_props; tcsp. }
    repnd.

    pose proof (ee a' a e2) as ee'; apply q in ee'.

    pose proof (tysysb lib' e a a' e0) as x; simpl in x.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.

  + SCase "term_transitive".
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff; clear eqiff.

    repeat introv.
    pose proof (ee1 lib' e) as ee1.
    pose proof (ee2 lib' e) as ee2.
    simpl in *.

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa lib' e a a) as e1 by (eauto).
    assert (eqa lib' e a' a) as e2 by (eauto).

    pose proof (ee1 a a e1) as ee1.
    pose proof (ee2 a a' e0) as ee2.

    pose proof (eq_term_equals_sym_tsp
                  (close ts) lib' (eqa lib' e) (eqb lib' e) a a' e1 e0 e2 v B v' B') as q.
    repeat (autodimp q hyp).
    { introv; apply type_sys_props4_implies_type_sys_props; tcsp. }
    repnd.
    apply q0 in ee1.

    pose proof (tysysb lib' e a a' e0) as x; simpl in x.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
    eapply tet; eauto.

  + SCase "term_value_respecting".
    introv ee ceq.
    apply eqiff in ee; apply eqiff; clear eqiff.

    repeat introv.
    pose proof (ee lib' e) as ee; simpl in *.

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa lib' e a a) as e1 by (eauto).
    assert (eqa lib' e a' a) as e2 by (eauto).
    assert (eqa lib' e a' a') as e3 by (eauto).

    pose proof (eq_term_equals_sym_tsp
                  (close ts) lib' (eqa lib' e) (eqb lib' e) a' a e3 e2 e0 v B v' B') as q.
    repeat (autodimp q hyp).
    { introv; apply type_sys_props4_implies_type_sys_props; tcsp. }
    repnd.

    pose proof (ee a' a' e3) as eex.
    apply q1 in eex.

    pose proof (tysysb lib' e a a' e0) as x; simpl in x.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
    eapply tet;
      [|eapply tevr;[exact eex|];
        apply sp_implies_ccequivc_ext_apply; eauto 3 with slow];tcsp.

  + SCase "type_gsymmetric".
    split; intro cl; dclose_lr; clear cl; apply CL_func.
    { eapply per_func_ext_sym; eauto. }
    { eapply per_func_ext_sym_rev; eauto. }

  + SCase "type_gtransitive".
    apply CL_func.
    exists eqa eqb; dands; auto.
    eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.

  + SCase "type_mtransitive".
    introv ee cl1 cl2; repndors; subst; dclose_lr; clear cl1 cl2;
      dands; apply CL_func.
    { eapply per_func_ext_function_trans1; try exact h; try exact h0; eauto. }
    { eapply per_func_ext_function_trans2; try exact h; try exact h0; eauto. }
    { eapply per_func_ext_function_trans3; try exact h; try exact h0; eauto. }
    { eapply per_func_ext_function_trans4; try exact h; try exact h0; eauto. }
Qed.
