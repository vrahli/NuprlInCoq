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


Add LoadPath "../".

Require Import type_sys_useful.
Require Import dest_close.



Lemma per_product_eq_preserves_eq_term_equals {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2 t1 t2,
    eq_term_equals eqa1 eqa2
    -> (forall (a1 a2 : CTerm) (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
          eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2))
    -> per_product_eq lib eqa1 eqb1 t1 t2
    -> per_product_eq lib eqa2 eqb2 t1 t2.
Proof.
  introv eqta eqtb peq.
  allunfold @per_product_eq; exrepnd.
  assert (eqa2 a a') as e' by (rw <- eqta; sp).
  exists a a' b b' e'; sp.
  generalize (eqtb a a' e e'); intro eqt.
 rw <- eqt; sp.
Qed.

Lemma per_product_eq_sym {p} :
  forall lib (eqa : per(p)) eqb t1 t2,
    term_equality_symmetric eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
          term_equality_symmetric (eqb a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e1 : eqa a1 a2) (e2 : eqa a2 a1),
          eq_term_equals (eqb a1 a2 e1) (eqb a2 a1 e2))
    -> per_product_eq lib eqa eqb t1 t2
    -> per_product_eq lib eqa eqb t2 t1.
Proof.
  introv syma symb symb2 peq.
  allunfold @per_product_eq; exrepnd.
  assert (eqa a' a) as e' by (apply syma; sp).
  exists a' a b' b e'; sp.
  apply symb; sp.
  generalize (symb2 a a' e e'); intro eqt.
  apply eqt; sp.
Qed.

Lemma per_product_eq_trans {p} :
  forall lib (eqa : per(p)) eqb t1 t2 t3,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall a1 a2 (e : eqa a1 a2),
          term_equality_transitive (eqb a1 a2 e))
    -> (forall a1 a2 (e1 : eqa a1 a2) (e : eqa a1 a1),
          eq_term_equals (eqb a1 a2 e1) (eqb a1 a1 e))
    -> (forall a1 a2 (e2 : eqa a2 a1) (e : eqa a1 a1),
          eq_term_equals (eqb a2 a1 e2) (eqb a1 a1 e))
    -> per_product_eq lib eqa eqb t1 t2
    -> per_product_eq lib eqa eqb t2 t3
    -> per_product_eq lib eqa eqb t1 t3.
Proof.
  introv syma tra trb refb1 refb2 peq1 peq2.
  allunfold @per_product_eq; exrepnd.
  spcast; computes_to_eqval.
  assert (eqa a0 a') as e' by (apply tra with (t2 := a'0); sp).
  exists a0 a' b0 b' e'; sp; try (complete (spcast; sp)).
  assert (eqa a0 a0) as e1 by (apply tra with (t2 := a'0); sp).
  assert (eqa a'0 a'0) as e2 by (apply tra with (t2 := a0); sp).
  generalize (refb1 a'0 a' e e2); intro eqt1.
  rw eqt1 in peq0.
  generalize (refb2 a'0 a0 e0 e2); intro eqt2.
  rw <- eqt2 in peq0.
  generalize (trb a0 a'0 e0 b0 b'0 b'); intro trb1.
  repeat (autodimp trb1 hyp).
  generalize (refb1 a0 a'0 e0 e1); intro eqt3.
  generalize (refb1 a0 a' e' e1); intro eqt4.
  rw eqt3 in trb1.
  rw eqt4; sp.
Qed.

Lemma per_product_eq_cequivc {p} :
  forall lib (eqa : per(p)) eqb t1 t2,
    term_equality_respecting lib eqa
    -> (forall a1 a2 (e : eqa a1 a2),
          term_equality_respecting lib (eqb a1 a2 e))
    -> (forall a1 a2 (e1 : eqa a1 a2) (e : eqa a1 a1),
          eq_term_equals (eqb a1 a2 e1) (eqb a1 a1 e))
    -> cequivc lib t1 t2
    -> per_product_eq lib eqa eqb t1 t1
    -> per_product_eq lib eqa eqb t1 t2.
Proof.
  introv tera terb eqt1 ceq peq.
  allunfold @per_product_eq; exrepnd.
  spcast; computes_to_eqval.
  generalize (cequivc_mkc_pair lib t1 t2 a b); intro k.
  repeat (autodimp k hyp); exrepnd.
  assert (eqa a a') as e' by (apply tera; sp; try (spcast; sp)).
  exists a a' b b' e'; sp; try (complete (spcast; sp)).
  generalize (eqt1 a a' e' e); intro eqt.
  apply eqt in peq0.
  generalize (terb a a' e'); intro k.
  apply k; sp; try (spcast; sp).
Qed.

Lemma close_type_system_product {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A A' v v' B B' eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_product A v B)
    -> computes_to_valc lib T' (mkc_product A' v' B')
    -> close lib ts A A' eqa
    -> (forall (a a' : CTerm) (e : eqa a a'),
          close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
    -> (forall (a a' : CTerm) (e : eqa a a'),
          type_system lib ts ->
          defines_only_universes lib ts ->
          type_sys_props lib (close lib ts) (substc a v B) (substc a' v' B')
                         (eqb a a' e))
    -> (forall t t' : CTerm, eq t t' <=> per_product_eq lib eqa eqb t t')
    -> per_product lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) A A' eqa
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 c1 c2 X1 clb recb eqiff per IHX1.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    SSCase "CL_product".
    allunfold @per_product; exrepd.
    generalize (eq_term_equals_type_family lib T T3 eqa0 eqa eqb0 eqb (close lib ts) A v B A' v' B' mkc_product); intro i.
    repeat (autodimp i hyp; try (complete (introv eqp; eqconstr eqp; sp))); repnd.

    unfold eq_term_equals; sp.
    rw e; rw eqiff; split; sp.
    apply @per_product_eq_preserves_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.
    apply @per_product_eq_preserves_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_product;
    clear per;
    allunfold @per_product; exrepd;
    unfold per_product;
    exists eqa0 eqb0; sp;
    allunfold @eq_term_equals; sp;
    allrw <-; sp.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_product; unfold per_product; exists eqa eqb; sp.

    duplicate c1 as ct.
    apply @cequivc_mkc_product with (T' := T3) in ct; sp.

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
    apply @cequivc_mkc_product with (T' := T3) in ct; sp.

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
    discover.

    generalize (eq_term_equals_sym_tsp2
                  lib (close lib ts) eqa eqb
                  v B v' B'); intro i.
    repeat (autodimp i hyp); repnd.

    apply per_product_eq_sym; sp.

    generalize (recb a1 a2 e0); sp.
    onedtsp X5 X6 X7 X8 X9 X10 X11 X4 tygs1 tygt1 dum1; sp.

  + SCase "term_transitive".
    unfold term_equality_transitive; sp.
    apply eqiff; sp.
    assert (eq t1 t2) as eq12 by auto.
    assert (eq t2 t3) as eq23 by auto.
    apply eqiff in eq12; apply eqiff in eq23.

    onedtsp IHX0 IHX2 IHX3 IHX4 IHX5 IHX6 IHX7 IHX8 tygs tygt dum.

    generalize (eq_term_equals_sym_tsp2
                  lib (close lib ts) eqa eqb
                  v B v' B'); intro i.
    repeat (autodimp i hyp); repnd.

    apply @per_product_eq_trans with (t2 := t2); sp;
    try (complete (generalize (recb a1 a2 e); intro tsp;
                   unfold type_sys_props in tsp; sp)).

  + SCase "term_value_respecting".
    unfold term_equality_respecting; sp.
    apply eqiff; sp.
    assert (eq t t) as eqtt by auto.
    apply eqiff in eqtt.

    onedtsp IHX0 IHX2 IHX3 IHX4 IHX5 IHX6 IHX7 IHX8 tygs tygt dum.

    generalize (eq_term_equals_sym_tsp2
                  lib (close lib ts) eqa eqb
                  v B v' B'); intro i.
    repeat (autodimp i hyp); repnd.

    spcast; apply per_product_eq_cequivc; sp.

    generalize (recb a1 a2 e); sp.
    onedtsp X5 X6 X7 X8 X9 X10 X11 X4 tygs1 tygt1 dum1; sp.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr;
    apply CL_product;
    clear per;
    allunfold @per_product; exrepd.

    (* 1 *)
    generalize (eq_term_equals_type_family
                  lib T T3 eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_product); intro i.
    repeat (autodimp i hyp; try (complete (introv eqp; eqconstr eqp; sp))).
    repnd.

    exists eqa eqb; sp.

    unfold eq_term_equals; sp.

    rw e; split; intro k; sp.

    apply per_product_eq_preserves_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.

    apply per_product_eq_preserves_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.

    (* 2 *)
    generalize (eq_term_equals_type_family2
                  lib T3 T eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_product); intro i;
    repeat (autodimp i hyp; try (complete (introv eqp; eqconstr eqp; sp)));
    repnd.

    exists eqa eqb; sp.

    unfold eq_term_equals; sp.

    rw e; split; intro k; sp.

    apply per_product_eq_preserves_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.

    apply per_product_eq_preserves_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_product lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_product lib (close lib ts) T' T4 eq2)).

    (* 1 *)
    clear per.
    allunfold @per_product; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T eqa1 eqa eqb1 eqb (close lib ts)
                  A v B A' v' B' mkc_product); intro i.
    repeat (autodimp i hyp; try (complete (introv eqp; eqconstr eqp; sp))).
    repnd.

    generalize (type_family_trans2
                  lib mkc_product (close lib ts) T3 T T4 eqa eqb eqa0 eqb0 A v B A' v' B'); intro j.
    repeat (autodimp j hyp; try (complete (introv eqp; eqconstr eqp; sp))).
    repnd.

    dands; apply CL_product; unfold per_product; exists eqa eqb;
    unfold eq_term_equals; sp; allrw.

    split; intro pp; sp.

    apply @per_product_eq_preserves_eq_term_equals with (eqa1 := eqa1) (eqb1 := eqb1); sp.
    apply eq_term_equals_sym; sp.

    apply @per_product_eq_preserves_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.

    split; intro pp; sp.

    apply @per_product_eq_preserves_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_sym; sp.

    apply @per_product_eq_preserves_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.

    (* 2 *)
    clear per.
    allunfold @per_product; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T' eqa1 eqa eqb1 eqb (close lib ts)
                  A' v' B' A v B mkc_product); intro i.
    repeat (autodimp i hyp;
            try (complete (introv eqp; eqconstr eqp; sp));
            try (complete (apply type_sys_props_sym; sp))).
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    intros.
    apply type_sys_props_sym.
    apply type_sys_props_eqb_comm; sp.
    apply tet with (t2 := a'); sp.
    apply tet with (t2 := a); sp.
    repnd.

    generalize (type_family_trans2
                  lib mkc_product (close lib ts) T3 T' T4 eqa eqb eqa0 eqb0 A' v' B' A v B); intro j.
    repeat (autodimp j hyp;
            try (complete (introv eqp; eqconstr eqp; sp));
            try (complete (apply type_sys_props_sym; sp))).
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    intros.
    apply type_sys_props_sym.
    apply type_sys_props_eqb_comm; sp.
    apply tet with (t2 := a'); sp.
    apply tet with (t2 := a); sp.
    repnd.

    dands; apply CL_product; unfold per_product; exists eqa eqb;
    unfold eq_term_equals; sp; allrw.

    split; intro pp; sp.

    apply @per_product_eq_preserves_eq_term_equals with (eqa1 := eqa1) (eqb1 := eqb1); sp.
    apply eq_term_equals_sym; sp.

    apply @per_product_eq_preserves_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.

    split; intro pp; sp.

    apply @per_product_eq_preserves_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_sym; sp.

    apply @per_product_eq_preserves_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
