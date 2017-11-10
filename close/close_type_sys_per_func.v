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


Lemma close_type_system_func {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A A' v v' B B' eqa eqb,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> computes_to_valc lib T (mkc_function A v B)
    -> computes_to_valc lib T' (mkc_function A' v' B')
    -> in_ext lib (fun lib => close ts lib A A' (eqa lib))
    -> in_ext lib (fun lib => type_sys_props4 (close ts) lib A A' (eqa lib))
    -> in_ext
         lib
         (fun lib =>
            forall (a a' : CTerm) (e : eqa lib a a'),
              close ts lib (substc a v B) (substc a' v' B') (eqb lib a a' e))
    -> in_ext
         lib
         (fun lib =>
            forall (a a' : CTerm) (e : eqa lib a a'),
              type_sys_props4 (close ts) lib (substc a v B) (substc a' v' B')
                              (eqb lib a a' e))
    -> (eq <=2=> (per_func_ext_eq eqa eqb lib))
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp1 comp2 cla tysysa clb tysysb eqiff.

  prove_type_sys_props4 SCase; introv.

  + SCase "uniquely_valued".
    introv cl.
    dclose_lr.
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
    introv ext.
    pose proof (ee lib' ext) as ee; simpl in *; introv.

    assert (term_equality_symmetric (eqa lib')) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib')) as teet by (eauto 3 with slow).

    assert (eqa lib' a a) as e1 by (eauto).
    assert (eqa lib' a' a) as e2 by (eauto).

    pose proof (eq_term_equals_sym_tsp
                  (close ts) lib' (eqa lib') (eqb lib') a a' e1 e e2 v B v' B') as q.
    repeat (autodimp q hyp).
    { introv; apply type_sys_props4_implies_type_sys_props; tcsp. }
    repnd.

    pose proof (ee a' a e2) as ee'; apply q in ee'.

    pose proof (tysysb lib' ext a a' e) as x; simpl in x.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.

  + SCase "term_transitive".
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff; clear eqiff.

    introv ext; introv.
    pose proof (ee1 lib' ext) as ee1.
    pose proof (ee2 lib' ext) as ee2.
    simpl in *.

    assert (term_equality_symmetric (eqa lib')) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib')) as teet by (eauto 3 with slow).

    assert (eqa lib' a a) as e1 by (eauto).
    assert (eqa lib' a' a) as e2 by (eauto).

    pose proof (ee1 a a e1) as ee1.
    pose proof (ee2 a a' e) as ee2.

    pose proof (eq_term_equals_sym_tsp
                  (close ts) lib' (eqa lib') (eqb lib') a a' e1 e e2 v B v' B') as q.
    repeat (autodimp q hyp).
    { introv; apply type_sys_props4_implies_type_sys_props; tcsp. }
    repnd.
    apply q0 in ee1.

    pose proof (tysysb lib' ext a a' e) as x; simpl in x.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
    eapply tet; eauto.

  + SCase "term_value_respecting".
    introv ee ceq.
    apply eqiff in ee; apply eqiff; clear eqiff.

    introv ext; introv.
    pose proof (ee lib' ext) as ee; simpl in *.

    assert (term_equality_symmetric (eqa lib')) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib')) as teet by (eauto 3 with slow).

    assert (eqa lib' a a) as e1 by (eauto).
    assert (eqa lib' a' a) as e2 by (eauto).
    assert (eqa lib' a' a') as e3 by (eauto).

    pose proof (eq_term_equals_sym_tsp
                  (close ts) lib' (eqa lib') (eqb lib') a' a e3 e2 e v B v' B') as q.
    repeat (autodimp q hyp).
    { introv; apply type_sys_props4_implies_type_sys_props; tcsp. }
    repnd.

    pose proof (ee a' a' e3) as eex.
    apply q1 in eex.

    pose proof (tysysb lib' ext a a' e) as x; simpl in x.
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
