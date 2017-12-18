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


Require Export close_util_approx.


Lemma close_type_system_approx {p} :
  forall lib (ts : cts(p)),
  forall T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> per_approx (close ts) lib T T' eq
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tsts dou mon per.

  dup per as ps; unfold per_approx in ps; exrepnd; spcast.

  prove_type_sys_props4 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    assert (uniquely_valued (per_approx_bar (close ts)))
      as uv
        by (apply per_approx_bar_uniquely_valued).

    apply per_approx_bar_implies_per_bar in per.

Lemma per_bar_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_bar ts).
Proof.
  unfold uniquely_valued, per_bar; introv h q; introv; exrepnd.
  rw q1.
  rw h1.
  split; introv w br ext; introv.

Qed.


    XXXX
    apply (uv lib T T'); auto.

    apply uniquely_valued_trans5 with (T2 := T3) (eq2 := eq); auto.
    { apply per_approx_bar_type_extensionality. }
    { apply per_approx_bar_type_symmetric. }
    { apply per_approx_bar_type_transitive. }

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_approx; auto;
    assert (type_symmetric (per_approx_bar (close ts)))
      as tys
        by (apply per_approx_bar_type_symmetric);
    assert (type_extensionality (per_approx_bar (close ts)))
      as tye
        by (apply per_approx_bar_type_extensionality);
    apply tye with (eq := eq); auto.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_approx;
    assert (type_value_respecting (per_approx_bar (close ts)))
           as tvr
           by (apply per_approx_bar_type_value_respecting).

    { apply tvr; auto.
      apply @type_system_type_mem with (T' := T'); auto.
      apply per_approx_bar_type_symmetric.
      apply per_approx_bar_type_transitive. }

    { apply tvr; auto.
      apply @type_system_type_mem1 with (T := T); auto.
      apply per_approx_bar_type_symmetric.
      apply per_approx_bar_type_transitive. }

  + SCase "type_value_respecting_trans".
    eapply type_equality_respecting_trans_per_approx_bar_implies; eauto.
    apply type_system_implies_type_equality_respecting_trans.
    apply per_approx_bar_type_system.

  + SCase "term_symmetric".
    assert (term_symmetric (per_approx_bar (close ts)))
      as tes
        by (apply per_approx_bar_term_symmetric).
    apply (tes lib T T'); auto.

  + SCase "term_transitive".
    assert (term_transitive (per_approx_bar (close ts)))
      as tet
        by (apply per_approx_bar_term_transitive).
    apply (tet lib T T'); auto.

  + SCase "term_value_respecting".
    assert (term_value_respecting (per_approx_bar (close ts)))
      as tvr
        by (apply per_approx_bar_term_value_respecting).
    apply tvr with (T := T); auto.
    apply @type_system_type_mem with (T' := T'); auto.
    { apply per_approx_bar_type_symmetric. }
    { apply per_approx_bar_type_transitive. }

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr.

    { apply CL_approx; apply per_approx_bar_type_symmetric; auto. }

    { apply CL_approx; apply per_approx_bar_type_symmetric; auto. }

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr.

    dands; apply CL_approx; try (complete sp).

    { apply per_approx_bar_type_transitive with (T2 := T); auto.
      allunfold @per_approx_bar; sp.
      exists a1 b1 c1 d1; dands; auto;[exists bar1; dands; auto|];[].
      eapply eq_term_equals_trans;[eauto|].
      pose proof (two_computes_to_valc_ceq_bar_mkc_approx bar1 bar0 T a1 b1 c0 d0) as q; repeat (autodimp q hyp).
      apply eq_per_approx_eq_bar in q.
      apply eq_term_equals_sym in q.
      eapply eq_term_equals_trans;[|exact q]; clear q.
      eapply approx_iff_implies_eq_per_approx_eq_bar; eauto. }

    { apply per_approx_bar_type_transitive with (T2 := T); auto.
      allunfold @per_approx_bar; sp.
      exists a0 b0 c0 d0; dands; auto;[exists bar0; dands; auto|];[].
      eapply eq_term_equals_trans;[eauto|].
      pose proof (two_computes_to_valc_ceq_bar_mkc_approx bar1 bar0 T a1 b1 c0 d0) as q; repeat (autodimp q hyp).
      apply eq_per_approx_eq_bar in q.
      eapply eq_term_equals_trans;[exact q|]; clear q.
      apply eq_term_equals_sym.
      eapply approx_iff_implies_eq_per_approx_eq_bar; eauto. }

    dands; apply CL_approx.

    { apply per_approx_bar_type_transitive with (T2 := T'); auto.
      allunfold @per_approx_bar; sp.
      exists a1 b1 c1 d1; dands; auto;[exists bar1; dands; auto|];[].
      eapply eq_term_equals_trans;[eauto|].
      pose proof (two_computes_to_valc_ceq_bar_mkc_approx bar1 bar0 T' a1 b1 c0 d0) as q; repeat (autodimp q hyp).
      apply eq_per_approx_eq_bar in q.
      apply eq_term_equals_sym in q.
      eapply eq_term_equals_trans;[|exact q]; clear q.
      eapply approx_iff_implies_eq_per_approx_eq_bar; eauto. }

    { apply per_approx_bar_type_transitive with (T2 := T'); auto.
      allunfold @per_approx_bar; sp.
      exists a0 b0 c0 d0; dands; auto;[exists bar0; dands; auto|];[].
      eapply eq_term_equals_trans;[eauto|].
      pose proof (two_computes_to_valc_ceq_bar_mkc_approx bar1 bar0 T' a1 b1 c0 d0) as q; repeat (autodimp q hyp).
      apply eq_per_approx_eq_bar in q.
      eapply eq_term_equals_trans;[exact q|]; clear q.
      apply eq_term_equals_sym.
      eapply approx_iff_implies_eq_per_approx_eq_bar; eauto. }
Qed.
