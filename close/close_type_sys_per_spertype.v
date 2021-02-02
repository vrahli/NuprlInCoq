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


Lemma close_type_system_spertype {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         R1 R2 eq1,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valcn lib T (mkcn_spertype R1)
    -> computes_to_valcn lib T' (mkcn_spertype R2)
    -> (forall x y : cterm,
          close lib ts (mkcn_apply2 R1 x y) (mkcn_apply2 R2 x y) (eq1 x y))
    -> (forall x y : cterm,
          type_sys_props lib (close lib ts)
                         (mkcn_apply2 R1 x y)
                         (mkcn_apply2 R2 x y)
                         (eq1 x y))
    -> (forall x y z : cterm,
          inhabited (eq1 x z)
          -> close lib ts (mkcn_apply2 R1 x y) (mkcn_apply2 R1 z y) (eq1 x y))
    -> (forall x y z : cterm,
          inhabited (eq1 x z)
          -> type_sys_props lib (close lib ts) (mkcn_apply2 R1 x y) (mkcn_apply2 R1 z y) (eq1 x y))
    -> (forall x y z : cterm,
          inhabited (eq1 y z)
          -> close lib ts (mkcn_apply2 R1 x y) (mkcn_apply2 R1 x z) (eq1 x y))
    -> (forall x y z : cterm,
          inhabited (eq1 y z)
          -> type_sys_props lib (close lib ts) (mkcn_apply2 R1 x y) (mkcn_apply2 R1 x z) (eq1 x y))
    -> is_per eq1
    -> (eq <=2=> (pertype_eq eq1))
    -> per_spertype lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou c1 c2 cl1 rec1 cl2 rec2 cl3 rec3.
  introv isper eqiff per.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  - SCase "uniquely_valued".
    dclose_lr.

    + SSCase "CL_spertype".
      clear per.
      allunfold @per_spertype; exrepd.
      ccomputes_to_eqval.
      apply @eq_term_equals_trans with (eq2 := pertype_eq eq1); auto.
      apply @eq_term_equals_trans with (eq2 := pertype_eq eq0); auto;
      try (complete (apply eq_term_equals_sym; auto)).
      unfold pertype_eq, eq_term_equals; introv.
      generalize (type_sys_props_pertype_eq_term_equals1
                    lib (close lib ts) R1 R2 R3 eq1 eq0); intro k.
      repeat (autodimp k hyp).
      generalize (k t1 t2); clear k; intro k.
      allapply @iff_inhabited_if_eq_term_equals; auto.

  - SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_spertype;
    clear per;
    allunfold @per_spertype; exrepd;
    unfold per_spertype;
    ccomputes_to_eqval.

    + exists R1 R3 eq0; sp; spcast; sp.
      apply @eq_term_equals_trans with (eq2 := eq); auto.
      apply @eq_term_equals_sym; auto.

  - SCase "type_value_respecting"; repdors; subst;
    apply CL_spertype; unfold per_spertype.

    (* 1 *)
    apply cequivcn_mkcn_spertype with (a := R1) in X; sp.
    exists R1 a' eq1; sp; spcast; sp.
    generalize (cl1 x y); intro clt1.
    generalize (rec1 x y); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr (mkcn_apply2 R1 x y) (mkcn_apply2 a' x y)); intro imp1.
    repeat (autodimp imp1 hyp).
    repeat (rw @mkcn_apply2_eq).
    repeat (apply sp_implies_cequivcn_apply); auto.

    (* 2 *)
    apply cequivcn_mkcn_spertype with (a := R2) in X; sp.
    exists R2 a' eq1; dands; spcast; try (complete sp); introv.

    generalize (cl1 x y); intro clt1.
    generalize (rec1 x y); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr (mkcn_apply2 R2 x y) (mkcn_apply2 a' x y)); intro imp1.
    repeat (autodimp imp1 hyp).
    repeat (rw @mkcn_apply2_eq).
    repeat (apply sp_implies_cequivcn_apply); auto.

    intro inh.
    generalize (cl2 x y z inh); intro clt2.
    generalize (rec2 x y z inh); intro tsp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tymt (mkcn_apply2 R1 x y) (mkcn_apply2 R2 x y) (mkcn_apply2 R2 z y) (eq1 x y) (eq1 x y));
      intro k; repeat (autodimp k hyp); repnd; auto.
    generalize (tygs (mkcn_apply2 R1 x y) (mkcn_apply2 R2 x y) (eq1 x y));
      intro k; repeat (autodimp k hyp); apply k; auto.
    generalize (tymt (mkcn_apply2 R1 z y) (mkcn_apply2 R1 x y) (mkcn_apply2 R2 z y) (eq1 x y) (eq1 z y));
      intro k; repeat (autodimp k hyp); repnd; auto.

    intro inh.
    generalize (cl3 x y z inh); intro clt3.
    generalize (rec3 x y z inh); intro tsp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tymt (mkcn_apply2 R1 x y) (mkcn_apply2 R2 x y) (mkcn_apply2 R2 x z) (eq1 x y) (eq1 x y));
      intro k; repeat (autodimp k hyp); repnd; auto.
    generalize (tygs (mkcn_apply2 R1 x y) (mkcn_apply2 R2 x y) (eq1 x y));
      intro k; repeat (autodimp k hyp); apply k; auto.
    generalize (tymt (mkcn_apply2 R1 x z) (mkcn_apply2 R1 x y) (mkcn_apply2 R2 x z) (eq1 x y) (eq1 x z));
      intro k; repeat (autodimp k hyp); repnd; auto.

  - SCase "term_symmetric".
    unfold term_equality_symmetric; introv eqt.
    rw eqiff in eqt; rw eqiff.
    apply is_per_sym; sp.

  - SCase "term_transitive".
    unfold term_equality_transitive; introv eqt1 eqt2.
    rw eqiff in eqt1; rw eqiff in eqt2; rw eqiff.
    apply is_per_trans with (b := t2); sp.

  - SCase "term_value_respecting".
    unfold term_equality_respecting; introv eqt ceq.
    rw eqiff in eqt; rw eqiff.

    spcast.
    assert (eq_term_equals (eq1 t t') (eq1 t t)) as eqteq.
    generalize (rec1 t t); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr (mkcn_apply2 R1 t t) (mkcn_apply2 R1 t t')); intro i; repeat (autodimp i h).
    repeat (rw @mkcn_apply2_eq).
    apply implies_cequivcn_apply; eauto 3 with slow.
    generalize (rec1 t t'); sp.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2.
    generalize (tygs (mkcn_apply2 R1 t t) (mkcn_apply2 R1 t t') (eq1 t t)); intro k; repeat (autodimp k h).
    rw k in i.
    generalize (uv2 (mkcn_apply2 R1 t t) (eq1 t t)); intro j; repeat (autodimp j h).

    apply eq_term_equals_implies_inhabited in eqteq.
    rw eqteq; sp.

  - SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_spertype;
    clear per;
    allunfold @per_spertype; exrepd;
    ccomputes_to_eqval;
    unfold per_spertype.

    (* 1 *)
    exists R3 R1 eq0; sp; spcast; sp.

    eapply @type_sys_props_ts_sym3 with (C := mkcn_apply2 R2 x y) (eq1 := eq1 x y); sp.

    eapply @type_sys_props_ts_trans3 with (B := mkcn_apply2 R1 x y) (D := mkcn_apply2 R2 x y) (eq2 := eq0 x y) (eq := eq1 x y); auto.
    eapply @type_sys_props_ts_sym3 with (C := mkcn_apply2 R2 x y) (eq1 := eq1 x y); sp.
    eapply @type_sys_props_ts_trans3 with (B := mkcn_apply2 R1 z y) (D := mkcn_apply2 R2 z y) (eq2 := eq0 z y) (eq := eq1 z y); auto.

    eapply @type_sys_props_ts_trans3 with (B := mkcn_apply2 R1 x y) (D := mkcn_apply2 R2 x y) (eq2 := eq0 x y) (eq := eq1 x y); auto.
    eapply @type_sys_props_ts_sym3 with (C := mkcn_apply2 R2 x y) (eq1 := eq1 x y); sp.
    eapply @type_sys_props_ts_trans3 with (B := mkcn_apply2 R1 x z) (D := mkcn_apply2 R2 x z) (eq2 := eq0 x z) (eq := eq1 x z); auto.

    (* 2 *)
    exists R1 R0 eq0; dands; spcast; try (complete sp); introv.

    eapply @type_sys_props_ts_sym2 with (C := mkcn_apply2 R2 x y) (eq1 := eq1 x y); sp.

    introv inh.
    assert (forall a b, (eq1 a b) <=2=> (eq0 a b)) as eqs.
    (* begin proof of assert *)
    introv.
    generalize (c3 a b); intro cl.
    generalize (rec1 a b); intro tsp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    apply tygs in cl.
    generalize (uv (mkcn_apply2 R0 a b) (eq0 a b)); intro k; repeat (autodimp k hyp).
    sp.
    (* end proof of assert *)
    generalize (iff_inhabited_if_eq_term_equals (eq1 x z) (eq0 x z) (eqs x z)); intro j.
    dup inh as inh'; apply j in inh'.
    generalize (rec2 x y z inh'); intro tsp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    apply tys; sp.

    introv inh.
    assert (forall a b, (eq1 a b) <=2=> (eq0 a b)) as eqs.
    (* begin proof of assert *)
    introv.
    generalize (c3 a b); intro cl.
    generalize (rec1 a b); intro tsp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    apply tygs in cl.
    generalize (uv (mkcn_apply2 R0 a b) (eq0 a b)); intro k; repeat (autodimp k hyp).
    sp.
    (* end proof of assert *)
    generalize (iff_inhabited_if_eq_term_equals (eq1 y z) (eq0 y z) (eqs y z)); intro j.
    dup inh as inh'; apply j in inh'.
    generalize (rec3 x y z inh'); intro tsp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    apply tys; sp.

  - SCase "type_gtransitive"; sp.

  - SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    allunfold @per_spertype; exrepnd;
    ccomputes_to_eqval.

    + dands; apply CL_spertype; unfold per_spertype.

      * exists R0 R5 eq3; sp; spcast; sp.
        eapply @type_sys_props_ts_trans3 with (B := mkcn_apply2 R1 x y) (D := mkcn_apply2 R2 x y) (eq2 := eq4 x y) (eq := eq1 x y); auto.

      * exists R0 R5 eq4; dands; spcast; introv; try (complete sp).

        eapply @type_sys_props_ts_trans4 with (B := mkcn_apply2 R1 x y) (D := mkcn_apply2 R2 x y) (eq1 := eq3 x y) (eq := eq1 x y); auto.

        intro inh.
        eapply @type_sys_props_ts_trans4 with (B := mkcn_apply2 R1 x y) (D := mkcn_apply2 R2 x y) (eq1 := eq3 x y) (eq := eq1 x y); auto.
        eapply @type_sys_props_ts_trans3 with (B := mkcn_apply2 R1 z y) (D := mkcn_apply2 R2 z y) (eq2 := eq3 z y) (eq := eq1 z y); auto.
        generalize (h3 z y); intro cl.
        generalize (rec1 z y); intro tsp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        apply tygs in cl; auto.

        intro inh.
        eapply @type_sys_props_ts_trans4 with (B := mkcn_apply2 R1 x y) (D := mkcn_apply2 R2 x y) (eq1 := eq3 x y) (eq := eq1 x y); auto.
        eapply @type_sys_props_ts_trans3 with (B := mkcn_apply2 R1 x z) (D := mkcn_apply2 R2 x z) (eq2 := eq3 x z) (eq := eq1 x z); auto.
        generalize (h3 x z); intro cl.
        generalize (rec1 x z); intro tsp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        apply tygs in cl; auto.

    + dands; apply CL_spertype; unfold per_spertype.

      * exists R0 R5 eq3; sp; spcast; sp.
        eapply @type_sys_props_ts_trans3 with (B := mkcn_apply2 R2 x y) (D := mkcn_apply2 R1 x y) (eq2 := eq4 x y) (eq := eq1 x y); auto.
        apply type_sys_props_sym; auto.

      * exists R0 R5 eq4; dands; spcast; introv; try (complete sp).

        eapply @type_sys_props_ts_trans4 with (B := mkcn_apply2 R2 x y) (D := mkcn_apply2 R1 x y) (eq1 := eq3 x y) (eq := eq1 x y); auto.
        apply type_sys_props_sym; auto.

        intro inh.
        eapply @type_sys_props_ts_trans4 with (B := mkcn_apply2 R2 x y) (D := mkcn_apply2 R1 x y) (eq1 := eq3 x y) (eq := eq1 x y); auto;
        try (complete (apply type_sys_props_sym; auto)).
        eapply @type_sys_props_ts_trans3 with (B := mkcn_apply2 R2 z y) (D := mkcn_apply2 R1 z y) (eq2 := eq3 z y) (eq := eq1 z y); auto;
        try (complete (apply type_sys_props_sym; auto)).
        generalize (h3 z y); intro cl.
        generalize (rec1 z y); intro tsp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        apply tygs in cl; auto.

        intro inh.
        eapply @type_sys_props_ts_trans4 with (B := mkcn_apply2 R2 x y) (D := mkcn_apply2 R1 x y) (eq1 := eq3 x y) (eq := eq1 x y); auto;
        try (complete (apply type_sys_props_sym; auto)).
        eapply @type_sys_props_ts_trans3 with (B := mkcn_apply2 R2 x z) (D := mkcn_apply2 R1 x z) (eq2 := eq3 x z) (eq := eq1 x z); auto;
        try (complete (apply type_sys_props_sym; auto)).
        generalize (h3 x z); intro cl.
        generalize (rec1 x z); intro tsp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        apply tygs in cl; auto.
Qed.
