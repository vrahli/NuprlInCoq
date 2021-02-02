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



Lemma eq_term_equals_per_texc_eq_if {p} :
  forall lib (eqn1 eqn2 eqe1 eqe2 : per(p)),
    eq_term_equals eqn1 eqn2
    -> eq_term_equals eqe1 eqe2
    -> eq_term_equals (per_texc_eq lib eqn1 eqe1)
                      (per_texc_eq lib eqn2 eqe2).
Proof.
  introv eqtn eqte.
  unfold eq_term_equals, per_texc_eq;
    introv; split; intro k; repndors; exrepnd; tcsp.

  - exists n1 n2 e1 e2; dands; auto; try (apply eqtn); try (apply eqte); auto.

  - exists n1 n2 e1 e2; dands; auto; try (apply eqtn); try (apply eqte); auto.
Qed.

Lemma per_texc_eq_symmetric {p} :
  forall lib (eqn eqe : per(p)) t1 t2,
    term_equality_symmetric eqn
    -> term_equality_symmetric eqe
    -> per_texc_eq lib eqn eqe t1 t2
    -> per_texc_eq lib eqn eqe t2 t1.
Proof.
  unfold per_texc_eq.
  introv tesn tese h; repdors; exrepnd; tcsp.
  exists n2 n1 e2 e1; dands; auto.
Qed.

Lemma per_texc_eq_transitive {p} :
  forall lib (eqn eqe : per(p)) t1 t2 t3,
    term_equality_transitive eqn
    -> term_equality_transitive eqe
    -> per_texc_eq lib eqn eqe t1 t2
    -> per_texc_eq lib eqn eqe t2 t3
    -> per_texc_eq lib eqn eqe t1 t3.
Proof.
  unfold per_texc_eq.
  introv tetn tete per1 per2; repdors; exrepnd; ccomputes_to_eqval; tcsp.
  exists n0 n2 e0 e2; dands; spcast; auto.
  - eapply tetn; eauto.
  - eapply tete; eauto.
Qed.

Lemma per_texc_eq_cequiv {p} :
  forall lib (eqn eqe : per(p)) t1 t2,
    term_equality_respecting lib eqn
    -> term_equality_respecting lib eqe
    -> cequivcn lib t1 t2
    -> per_texc_eq lib eqn eqe t1 t1
    -> per_texc_eq lib eqn eqe t1 t2.
Proof.
  unfold per_texc_eq.
  introv resn rese ceq per; repdors; exrepnd.
  ccomputes_to_eqval.
  dup per0 as comp.
  eapply cequivcn_mkcn_exception in comp;[|exact ceq]; exrepnd.
  exists n1 a' e1 b'; dands; spcast; auto.
  - eapply resn; spcast; auto.
  - eapply rese; spcast; auto.
Qed.

Lemma close_type_system_texc {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A1 A2 B1 B2 eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valcn lib T (mkcn_texc A1 B1)
    -> computes_to_valcn lib T' (mkcn_texc A2 B2)
    -> close lib ts A1 A2 eqa
    -> type_sys_props lib (close lib ts) A1 A2 eqa
    -> close lib ts B1 B2 eqb
    -> type_sys_props lib (close lib ts) B1 B2 eqb
    -> (forall t t' : cterm, eq t t' <=> per_texc_eq lib eqa eqb t t')
    -> per_texc lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou c1 c2 cla reca clb recb eqiff per.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  - SCase "uniquely_valued".
    dclose_lr.

    + SSCase "CL_texc".
      clear per.
      allunfold @per_texc; exrepd.
      unfold eq_term_equals; intros.
      allrw.
      ccomputes_to_eqval.
      revert t1 t2; rw @fold_eq_term_equals.
      apply eq_term_equals_per_texc_eq_if.
      { apply type_sys_props_eq_term_equals4 with (B := N2) (eq1 := eqn) in reca; sp. }
      { apply type_sys_props_eq_term_equals4 with (B := E2) (eq1 := eqe) in recb; sp. }

  - SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_texc;
    clear per;
    allunfold @per_texc; exrepd;
    unfold per_texc;
    ccomputes_to_eqval.

    + exists eqn eqe A1 N2 B1 E2; sp; spcast; sp.
      apply eq_term_equals_trans with (eq2 := eq); sp.
      apply eq_term_equals_sym; sp.

  - SCase "type_value_respecting"; repdors; subst;
    apply CL_texc; unfold per_texc.

    (* 1 *)
    generalize (cequivcn_mkcn_texc lib T T3 A1 B1); introv k; repeat (autodimp k hyp); exrepnd.
    exists eqa eqb A1 a' B1 b'; sp; spcast; sp.
    generalize (type_sys_props_cequivc lib (close lib ts) A1 A2 a' eqa); sp.
    generalize (type_sys_props_cequivc lib (close lib ts) B1 B2 b' eqb); sp.

    (* 2 *)
    generalize (cequivcn_mkcn_texc lib T' T3 A2 B2); introv k; repeat (autodimp k hyp); exrepnd.
    exists eqa eqb A2 a' B2 b'; sp; spcast; sp.
    apply type_sys_props_sym in reca.
    generalize (type_sys_props_cequivc lib (close lib ts) A2 A1 a' eqa); sp.
    apply type_sys_props_sym in recb.
    generalize (type_sys_props_cequivc lib (close lib ts) B2 B1 b' eqb); sp.

  - SCase "term_symmetric".
    unfold term_equality_symmetric; introv eqt.
    rw eqiff in eqt; rw eqiff.
    apply per_texc_eq_symmetric; sp;
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 tymt1; sp;
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2; sp.

  - SCase "term_transitive".
    unfold term_equality_transitive; introv eqt1 eqt2.
    rw eqiff in eqt1; rw eqiff in eqt2; rw eqiff.
    apply @per_texc_eq_transitive with (t2 := t2); sp;
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 tymt1; sp;
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2; sp.

  - SCase "term_value_respecting".
    unfold term_equality_respecting; introv eqt ceq.
    rw eqiff in eqt; rw eqiff.
    spcast.
    apply per_texc_eq_cequiv; sp;
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 tymt1; sp;
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2; sp.

  - SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_texc;
    clear per;
    allunfold @per_texc; exrepd;
    ccomputes_to_eqval;
    unfold per_texc.

    (* 1 *)
    { exists eqn eqe N2 A1 E2 B1; sp; spcast; sp.
      - generalize (type_sys_props_ts_sym3 lib (close lib ts) A1 N2 A2 eqa eqn); sp.
      - generalize (type_sys_props_ts_sym3 lib (close lib ts) B1 E2 B2 eqb eqe); sp. }

    (* 2 *)
    { exists eqn eqe A1 N1 B1 E1; sp; spcast; sp.
      - generalize (type_sys_props_ts_sym2 lib (close lib ts) A1 N1 A2 eqa eqn); sp.
      - generalize (type_sys_props_ts_sym2 lib (close lib ts) B1 E1 B2 eqb eqe); sp. }

  - SCase "type_gtransitive"; sp.

  - SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_texc lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_texc lib (close lib ts) T' T4 eq2));
    allunfold @per_texc; exrepd;
    ccomputes_to_eqval.

    + dands; apply CL_texc; unfold per_texc.

      * exists eqn0 eqe0 N0 N2 E0 E2; sp; spcast; sp.
        { generalize (type_sys_props_ts_trans3 lib (close lib ts) N0 A1 N2 A2 eqn0 eqn eqa); sp. }
        { generalize (type_sys_props_ts_trans3 lib (close lib ts) E0 B1 E2 B2 eqe0 eqe eqb); sp. }

      * exists eqn eqe N0 N2 E0 E2; sp; spcast; sp.
        { generalize (type_sys_props_ts_trans4 lib (close lib ts) N0 A1 N2 A2 eqn0 eqn eqa); sp. }
        { generalize (type_sys_props_ts_trans4 lib (close lib ts) E0 B1 E2 B2 eqe0 eqe eqb); sp. }

    + dands; apply CL_texc; unfold per_texc.

      * exists eqn0 eqe0 N0 N2 E0 E2; sp; spcast; sp.
        { apply type_sys_props_sym in reca.
          generalize (type_sys_props_ts_trans3 lib (close lib ts) N0 A2 N2 A1 eqn0 eqn eqa); sp. }
        { apply type_sys_props_sym in recb.
          generalize (type_sys_props_ts_trans3 lib (close lib ts) E0 B2 E2 B1 eqe0 eqe eqb); sp. }

      * exists eqn eqe N0 N2 E0 E2; sp; spcast; sp.
        { apply type_sys_props_sym in reca.
          generalize (type_sys_props_ts_trans4 lib (close lib ts) N0 A2 N2 A1 eqn0 eqn eqa); sp. }
        { apply type_sys_props_sym in recb.
          generalize (type_sys_props_ts_trans4 lib (close lib ts) E0 B2 E2 B1 eqe0 eqe eqb); sp. }
Qed.
