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



Lemma eq_term_equals_per_union_eq_if {p} :
  forall lib (eqa1 eqa2 eqb1 eqb2 : per(p)),
    eq_term_equals eqa1 eqa2
    -> eq_term_equals eqb1 eqb2
    -> eq_term_equals (per_union_eq lib eqa1 eqb1) (per_union_eq lib eqa2 eqb2).
Proof.
  introv eqta eqtb.
  unfold eq_term_equals, per_union_eq, per_union_eq_L, per_union_eq_R;
    introv; split; intro k; repdors; exrepnd.

  left.
  exists x y; sp.
  apply eqta; sp.

  right.
  exists x y; sp.
  apply eqtb; sp.

  left.
  exists x y; sp.
  apply eqta; sp.

  right.
  exists x y; sp.
  apply eqtb; sp.
Qed.

Lemma per_union_eq_symmetric {p} :
  forall lib (eqa eqb : per(p)) t1 t2,
    term_equality_symmetric eqa
    -> term_equality_symmetric eqb
    -> per_union_eq lib eqa eqb t1 t2
    -> per_union_eq lib eqa eqb t2 t1.
Proof.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R.
  introv tesa tesb per; repdors; exrepnd.

  left.
  exists y x; sp.

  right.
  exists y x; sp.
Qed.

Lemma per_union_eq_transitive {p} :
  forall lib (eqa eqb : per(p)) t1 t2 t3,
    term_equality_transitive eqa
    -> term_equality_transitive eqb
    -> per_union_eq lib eqa eqb t1 t2
    -> per_union_eq lib eqa eqb t2 t3
    -> per_union_eq lib eqa eqb t1 t3.
Proof.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R.
  introv teta tetb per1 per2; repdors; exrepnd; ccomputes_to_eqval.

  left.
  exists x0 y; sp; spcast; sp.
  apply teta with (t2 := y0); sp.

  right.
  exists x0 y; sp; spcast; sp.
  apply tetb with (t2 := y0); sp.
Qed.

Lemma per_union_eq_cequiv {p} :
  forall lib (eqa eqb : per(p)) t1 t2,
    term_equality_respecting lib eqa
    -> term_equality_respecting lib eqb
    -> term_equality_symmetric eqa
    -> term_equality_symmetric eqb
    -> term_equality_transitive eqa
    -> term_equality_transitive eqb
    -> cequivc lib t1 t2
    -> per_union_eq lib eqa eqb t1 t1
    -> per_union_eq lib eqa eqb t1 t2.
Proof.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R.
  introv resa resb syma symb tra trb ceq per; repdors; exrepnd.

  left; spcast.
  generalize (cequivc_mkc_inl lib t1 t2 x); introv k;
  repeat (autodimp k hyp); exrepnd.
  exists x b; sp; spcast; sp.
  apply resa; spcast; sp.
  apply tra with (t2 := y); sp.

  right; spcast.
  generalize (cequivc_mkc_inr lib t1 t2 x); introv k;
  repeat (autodimp k hyp); exrepnd.
  exists x b; sp; spcast; sp.
  apply resb; spcast; sp.
  apply trb with (t2 := y); sp.
Qed.


Lemma close_type_system_union {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A1 A2 B1 B2 eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_union A1 B1)
    -> computes_to_valc lib T' (mkc_union A2 B2)
    -> close lib ts A1 A2 eqa
    -> type_sys_props lib (close lib ts) A1 A2 eqa
    -> close lib ts B1 B2 eqb
    -> type_sys_props lib (close lib ts) B1 B2 eqb
    -> (forall t t' : CTerm, eq t t' <=> per_union_eq lib eqa eqb t t')
    -> per_union lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou c1 c2 cla reca clb recb eqiff per.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  - SCase "uniquely_valued".
    dclose_lr.

    + SSCase "CL_union".
      clear per.
      allunfold @per_union; exrepd.
      unfold eq_term_equals; intros.
      allrw.
      ccomputes_to_eqval.
      revert t1 t2; rw @fold_eq_term_equals.
      apply eq_term_equals_per_union_eq_if.
      apply type_sys_props_eq_term_equals4 with (B := A3) (eq1 := eqa0) in reca; sp.
      apply type_sys_props_eq_term_equals4 with (B := B3) (eq1 := eqb0) in recb; sp.

  - SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_union;
    clear per;
    allunfold @per_union; exrepd;
    unfold per_union;
    ccomputes_to_eqval.

    + exists eqa0 eqb0 A1 A3 B1 B3; sp; spcast; sp.
      apply eq_term_equals_trans with (eq2 := eq); sp.
      apply eq_term_equals_sym; sp.

  - SCase "type_value_respecting"; repdors; subst;
    apply CL_union; unfold per_union.

    (* 1 *)
    generalize (cequivc_mkc_union lib T T3 A1 B1); introv k; repeat (autodimp k hyp); exrepnd.
    exists eqa eqb A1 a' B1 b'; sp; spcast; sp.
    generalize (type_sys_props_cequivc lib (close lib ts) A1 A2 a' eqa); sp.
    generalize (type_sys_props_cequivc lib (close lib ts) B1 B2 b' eqb); sp.

    (* 2 *)
    generalize (cequivc_mkc_union lib T' T3 A2 B2); introv k; repeat (autodimp k hyp); exrepnd.
    exists eqa eqb A2 a' B2 b'; sp; spcast; sp.
    apply type_sys_props_sym in reca.
    generalize (type_sys_props_cequivc lib (close lib ts) A2 A1 a' eqa); sp.
    apply type_sys_props_sym in recb.
    generalize (type_sys_props_cequivc lib (close lib ts) B2 B1 b' eqb); sp.

  - SCase "term_symmetric".
    unfold term_equality_symmetric; introv eqt.
    rw eqiff in eqt; rw eqiff.
    apply per_union_eq_symmetric; sp;
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 tymt1; sp;
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2; sp.

  - SCase "term_transitive".
    unfold term_equality_transitive; introv eqt1 eqt2.
    rw eqiff in eqt1; rw eqiff in eqt2; rw eqiff.
    apply @per_union_eq_transitive with (t2 := t2); sp;
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 tymt1; sp;
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2; sp.

  - SCase "term_value_respecting".
    unfold term_equality_respecting; introv eqt ceq.
    rw eqiff in eqt; rw eqiff.
    spcast.
    apply per_union_eq_cequiv; sp;
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 tymt1; sp;
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2; sp.

  - SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_union;
    clear per;
    allunfold @per_union; exrepd;
    ccomputes_to_eqval;
    unfold per_union.

    (* 1 *)
    exists eqa0 eqb0 A3 A1 B3 B1; sp; spcast; sp.
    generalize (type_sys_props_ts_sym3 lib (close lib ts) A1 A3 A2 eqa eqa0); sp.
    generalize (type_sys_props_ts_sym3 lib (close lib ts) B1 B3 B2 eqb eqb0); sp.

    (* 2 *)
    exists eqa0 eqb0 A1 A0 B1 B0; sp; spcast; sp.
    generalize (type_sys_props_ts_sym2 lib (close lib ts) A1 A0 A2 eqa eqa0); sp.
    generalize (type_sys_props_ts_sym2 lib (close lib ts) B1 B0 B2 eqb eqb0); sp.

  - SCase "type_gtransitive"; sp.

  - SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_union lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_union lib (close lib ts) T' T4 eq2));
    allunfold @per_union; exrepd;
    ccomputes_to_eqval.

    + dands; apply CL_union; unfold per_union.

      * exists eqa1 eqb1 A4 A3 B4 B3; sp; spcast; sp.
        generalize (type_sys_props_ts_trans3 lib (close lib ts) A4 A1 A3 A2 eqa1 eqa0 eqa); sp.
        generalize (type_sys_props_ts_trans3 lib (close lib ts) B4 B1 B3 B2 eqb1 eqb0 eqb); sp.

      * exists eqa0 eqb0 A4 A3 B4 B3; sp; spcast; sp.
        generalize (type_sys_props_ts_trans4 lib (close lib ts) A4 A1 A3 A2 eqa1 eqa0 eqa); sp.
        generalize (type_sys_props_ts_trans4 lib (close lib ts) B4 B1 B3 B2 eqb1 eqb0 eqb); sp.

    + dands; apply CL_union; unfold per_union.

      * exists eqa1 eqb1 A4 A3 B4 B3; sp; spcast; sp.
        apply type_sys_props_sym in reca.
        generalize (type_sys_props_ts_trans3 lib (close lib ts) A4 A2 A3 A1 eqa1 eqa0 eqa); sp.
        apply type_sys_props_sym in recb.
        generalize (type_sys_props_ts_trans3 lib (close lib ts) B4 B2 B3 B1 eqb1 eqb0 eqb); sp.

      * exists eqa0 eqb0 A4 A3 B4 B3; sp; spcast; sp.
        apply type_sys_props_sym in reca.
        generalize (type_sys_props_ts_trans4 lib (close lib ts) A4 A2 A3 A1 eqa1 eqa0 eqa); sp.
        apply type_sys_props_sym in recb.
        generalize (type_sys_props_ts_trans4 lib (close lib ts) B4 B2 B3 B1 eqb1 eqb0 eqb); sp.
Qed.

