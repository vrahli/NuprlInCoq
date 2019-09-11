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


Require Export type_sys_useful.
Require Import dest_close.


Lemma close_type_system_teq {p} :
  forall lib (ts : cts(p)),
  forall T T' (eq : per) a1 a2 b1 b2 eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_tequality a1 a2)
    -> computes_to_valc lib T' (mkc_tequality b1 b2)
    -> close lib ts a1 b1 eqa
    -> type_sys_props lib (close lib ts) a1 b1 eqa
    -> close lib ts a2 b2 eqa
    -> type_sys_props lib (close lib ts) a2 b2 eqa
    -> close lib ts a1 a2 eqa
    -> type_sys_props lib (close lib ts) a1 a2 eqa
    -> eq <=2=> true_per
    -> per_teq lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou c1 c2 cl1 tsp1 cl2 tsp2 cl3 tsp3.
  introv eqiff perteq.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    * SSCase "CL_teq".
      clear perteq.
      allunfold @per_teq; sp.
      apply eq_term_equals_trans with (eq2 := true_per); auto.
      apply eq_term_equals_sym; auto.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    allunfold @per_teq; exrepd;
    ccomputes_to_eqval;
    apply CL_teq; unfold per_teq.

    (* 1 *)
    exists a1 a2 b0 b3 eqa0; sp; spcast; sp.
    apply eq_term_equals_trans with (eq2 := eq); auto.
    apply eq_term_equals_sym; auto.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_teq; allunfold @per_teq; sp;
    ccomputes_to_eqval.

    duplicate c1 as c0.
    apply cequivc_mkc_tequality with (t' := T3) in c0; sp.
    exists a1 a2 a' b' eqa; sp; spcast; sp; try (complete (right; spcast; sp));
    allunfold @type_sys_props; sp.

    duplicate c2 as c0.
    apply cequivc_mkc_tequality with (t' := T3) in c0; sp.
    exists b1 b2 a' b' eqa; sp; spcast; sp; try (complete (right; spcast; sp)).
    allunfold @type_sys_props; sp.
    allunfold @type_sys_props; sp.
    generalize (type_sys_props_ts_trans2 lib (close lib ts) a1 b1 a2 a2 eqa eqa eqa);
      intro k; repeat (autodimp k hyp).
    generalize (type_sys_props_ts_trans3 lib (close lib ts) b1 a2 b2 b2 eqa eqa eqa);
      intro j; repeat (autodimp j hyp).

  + SCase "term_symmetric".
    unfold term_equality_symmetric; sp.
    allrw; discover; sp.

  + SCase "term_transitive".
    unfold term_equality_transitive; sp.
    allrw; discover; sp.

  + SCase "term_value_respecting".
    unfold term_equality_respecting; sp.
    allrw; discover; sp; spcast.

  + SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_teq;
    clear perteq;
    allunfold @per_teq; exrepd;
    ccomputes_to_eqval;
    unfold per_teq.

    (* 1 *)
    exists b0 b3 a1 a2 eqa; sp; spcast; sp.
    eapply type_sys_props_ts_sym4 with (C := b1) (eq2 := eqa0); eauto.
    eapply type_sys_props_ts_sym4 with (C := b2) (eq2 := eqa0); eauto.
    eapply type_sys_props_ts_trans2 with (A := a1) (D := b1) (eq1 := eqa0) (eq2 := eqa); eauto.
    eapply type_sys_props_ts_trans with (B := a2) (eq1 := eqa) (eq2 := eqa0); eauto.

    (* 2 *)
    exists a1 a2 a0 a3 eqa; sp; spcast; sp.
    eapply type_sys_props_ts_sym with (C := b1) (eq2 := eqa0); eauto.
    eapply type_sys_props_ts_sym with (C := b2) (eq2 := eqa0); eauto.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    clear perteq;
    allunfold @per_teq; exrepd;
    ccomputes_to_eqval;
    dands; apply CL_teq; unfold per_teq.

    (* 1 *)
    exists a0 a3 b4 b5 eqa0; sp; spcast; sp.
    generalize (type_sys_props_ts_trans5 lib (close lib ts) a1 a0 b4 b1 eqa0 eqa1 eqa); intro k.
    repeat (autodimp k hyp); repnd; auto.
    eapply @type_sys_props_ts_sym2 with (C := a2) (eq1 := eqa); eauto.
    generalize (type_sys_props_ts_trans5 lib (close lib ts) a2 a3 b5 b2 eqa0 eqa1 eqa); intro k.
    repeat (autodimp k hyp); repnd; auto.
    apply (type_sys_props_ts_sym2 lib) with (C := a1) (eq1 := eqa); auto.
    apply type_sys_props_sym; auto.

    (* 2 *)
    exists a0 a3 b4 b5 eqa0; sp; spcast; sp.
    generalize (type_sys_props_ts_trans5 lib (close lib ts) a1 a0 b4 b1 eqa0 eqa1 eqa); intro k.
    repeat (autodimp k hyp); repnd; auto.
    eapply @type_sys_props_ts_sym2 with (C := a2) (eq1 := eqa); eauto.
    generalize (type_sys_props_ts_trans5 lib (close lib ts) a2 a3 b5 b2 eqa0 eqa1 eqa); intro k.
    repeat (autodimp k hyp); repnd; auto.
    apply (type_sys_props_ts_sym2 lib) with (C := a1) (eq1 := eqa); auto.
    apply type_sys_props_sym; auto.

    (* 4 *)
    exists a0 a3 b4 b5 eqa0; sp; spcast; sp.
    apply (type_sys_props_ts_trans3 lib) with (B := b1) (D := a1) (eq := eqa) (eq2 := eqa1); auto.
    apply type_sys_props_sym; auto.
    apply (type_sys_props_ts_trans3 lib) with (B := b2) (D := a2) (eq := eqa) (eq2 := eqa1); auto.
    apply type_sys_props_sym; auto.

    (* 5 *)
    exists a0 a3 b4 b5 eqa0; sp; spcast; sp.
    apply (type_sys_props_ts_trans3 lib) with (B := b1) (D := a1) (eq := eqa) (eq2 := eqa1); auto.
    apply type_sys_props_sym; auto.
    apply (type_sys_props_ts_trans3 lib) with (B := b2) (D := a2) (eq := eqa) (eq2 := eqa1); auto.
    apply type_sys_props_sym; auto.
Qed.

