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


Require Import type_sys_useful.
Require Import dest_close.




Lemma close_type_system_w {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A A' v v' B B' eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_w A v B)
    -> computes_to_valc lib T' (mkc_w A' v' B')
    -> close lib ts A A' eqa
    -> (forall (a a' : CTerm) (e : eqa a a'),
          close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
    -> (forall (a a' : CTerm) (e : eqa a a'),
          type_system lib ts ->
          defines_only_universes lib ts ->
          type_sys_props lib (close lib ts) (substc a v B) (substc a' v' B')
                         (eqb a a' e))
    -> (forall t t' : CTerm, eq t t' <=> weq lib eqa eqb t t')
    -> per_w lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) A A' eqa
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 c1 c2 X1 clb recb eqiff per IHX1.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    SSCase "CL_w".
    allunfold @per_w; exrepd.
    generalize (eq_term_equals_type_family lib T T3 eqa0 eqa eqb0 eqb (close lib ts) A v B A' v' B' mkc_w); intro i.
    repeat (autodimp i hyp; try (complete (introv eqw; eqconstr eqw; sp))); repnd.

    unfold eq_term_equals; sp.
    rw e; rw eqiff; split; sp.

    apply @weq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    generalize (i1 a1 a2 e2 e1); sp; apply eq_term_equals_sym; sp.

    apply @weq_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_w;
    clear per;
    allunfold @per_w; exrepd;
    unfold per_w;
    exists eqa0 eqb0; sp;
    allrw <-; sp;
    apply eq_term_equals_trans with (eq2 := eq); sp;
    try (complete (apply eq_term_equals_sym; auto)).

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_w; unfold per_w; exists eqa eqb; sp.

    duplicate c1 as ct.
    apply @cequivc_mkc_w with (T' := T3) in ct; sp.

    apply @type_family_cequivc
          with
          (A1 := A)
          (v1 := v)
          (B1 := B)
          (A2 := A'0)
          (v2 := v'0)
          (B2 := B'0)
          (A := A')
          (v := v')
          (B := B'); sp.

    duplicate c2 as ct.
    apply @cequivc_mkc_w with (T' := T3) in ct; sp.

    apply @type_family_cequivc2
          with
          (A1 := A')
          (v1 := v')
          (B1 := B')
          (A2 := A'0)
          (v2 := v'0)
          (B2 := B'0)
          (A := A)
          (v := v)
          (B := B); sp.

  + SCase "term_symmetric".
    unfold term_equality_symmetric; sp.
    onedtsp e pp p0 p1 c t t0 t3 tygs tygt dum.
    apply eqiff; sp.
    assert (eq t1 t2) as eq12 by auto.
    apply eqiff in eq12.

    apply @weq_sym with (v1 := v) (v2 := v') (B1 := B) (B2 := B') (ts := close lib ts); sp.

  + SCase "term_transitive".
    unfold term_equality_transitive; sp.
    apply eqiff; sp.
    assert (eq t1 t2) as eq12 by auto.
    assert (eq t2 t3) as eq23 by auto.
    apply eqiff in eq12.
    apply eqiff in eq23.
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1; sp.
    apply @weq_trans with (t2 := t2) (ts := close lib ts) (v1 := v) (B1 := B) (v2 := v') (B2 := B'); sp.

  + SCase "term_value_respecting".
    unfold term_equality_respecting; sp.
    apply eqiff; sp.
    assert (eq t t) as eqtt by auto.
    apply eqiff in eqtt.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.

    spcast; apply @weq_cequivc with (t1 := t) (ts := close lib ts) (v1 := v) (B1 := B) (v2 := v') (B2 := B'); sp.

  + SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_w;
    clear per;
    allunfold @per_w; exrepd.

    (* 1 *)
    generalize (eq_term_equals_type_family
                  lib T T3 eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_w); intro i.
    repeat (autodimp i hyp; try (complete (introv eqw; eqconstr eqw; sp))).
    repnd.

    unfold per_w.
    exists eqa eqb; sp.

    apply eq_term_equals_trans with (eq2 := weq lib eqa0 eqb0);
      try (complete sp); split; sp.

    apply weq_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.

    apply weq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.

    (* 2 *)
    generalize (eq_term_equals_type_family2
                  lib T3 T eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_w); intro i;
    repeat (autodimp i hyp; try (complete (introv eqw; eqconstr eqw; sp)));
    repnd.

    unfold per_w.
    exists eqa eqb; sp.

    apply eq_term_equals_trans with (eq2 := weq lib eqa0 eqb0);
      try (complete sp); split; sp.

    apply weq_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.

    apply weq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_w lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_w lib (close lib ts) T' T4 eq2)).

    (* 1 *)
    clear per.
    allunfold @per_w; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T eqa1 eqa eqb1 eqb (close lib ts)
                  A v B A' v' B' mkc_w); intro i.
    repeat (autodimp i hyp; try (complete (introv eqw; eqconstr eqw; sp))).
    repnd.

    generalize (type_family_trans2
                  lib mkc_w (close lib ts) T3 T T4 eqa eqb eqa0 eqb0 A v B A' v' B');
      intro j.
    repeat (autodimp j hyp; try (complete (introv eqw; eqconstr eqw; sp))).
    repnd.

    dands; apply CL_w; unfold per_w; exists eqa eqb; unfold eq_term_equals; sp; allrw.

    split; sp.

    apply @weq_eq_term_equals with (eqa1 := eqa1) (eqb1 := eqb1); sp.
    apply eq_term_equals_sym; sp.

    apply @weq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp; try (complete (allrw <-; sp)).

    split; sp.

    apply @weq_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_sym; sp.

    apply @weq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.

    (* 2 *)
    clear per.
    allunfold @per_w; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T' eqa1 eqa eqb1 eqb (close lib ts)
                  A' v' B' A v B mkc_w); intro i.
    repeat (autodimp i hyp;
            try (complete (introv eqw; eqconstr eqw; sp));
            try (complete (apply type_sys_props_sym; sp))).
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    intros.
    apply type_sys_props_sym.
    apply type_sys_props_eqb_comm; sp.
    apply tet with (t2 := a'); sp.
    apply tet with (t2 := a); sp.
    repnd.

    generalize (type_family_trans2
                  lib mkc_w (close lib ts) T3 T' T4 eqa eqb eqa0 eqb0 A' v' B' A v B); intro j.
    repeat (autodimp j hyp;
            try (complete (introv eqw; eqconstr eqw; sp));
            try (complete (apply type_sys_props_sym; sp))).
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    intros.
    apply type_sys_props_sym.
    apply type_sys_props_eqb_comm; sp.
    apply tet with (t2 := a'); sp.
    apply tet with (t2 := a); sp.
    repnd.

    dands; apply CL_w; unfold per_w; exists eqa eqb; unfold eq_term_equals; sp; allrw.

    split; sp.

    apply @weq_eq_term_equals with (eqa1 := eqa1) (eqb1 := eqb1); sp.
    apply eq_term_equals_sym; sp.

    apply @weq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.

    split; sp.

    apply @weq_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_sym; sp.

    apply @weq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
Qed.

