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



Lemma close_type_system_pertype {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         R1 R2 eq1 eq2,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_pertype R1)
    -> computes_to_valc lib T' (mkc_pertype R2)
    -> (forall x y : CTerm,
          close lib ts (mkc_apply2 R1 x y) (mkc_apply2 R1 x y) (eq1 x y))
    -> (forall x y : CTerm,
          type_system lib ts
          -> defines_only_universes lib ts
          -> type_sys_props lib (close lib ts)
                            (mkc_apply2 R1 x y)
                            (mkc_apply2 R1 x y)
                            (eq1 x y))
    -> (forall x y : CTerm,
          close lib ts (mkc_apply2 R2 x y) (mkc_apply2 R2 x y) (eq2 x y))
    -> (forall x y : CTerm,
          type_system lib ts
          -> defines_only_universes lib ts
          -> type_sys_props lib (close lib ts)
                            (mkc_apply2 R2 x y)
                            (mkc_apply2 R2 x y)
                            (eq2 x y))
    -> (forall x y : CTerm, inhabited (eq1 x y) <=> inhabited (eq2 x y))
    -> is_per eq1
    -> (forall t t' : CTerm, eq t t' <=> inhabited (eq1 t t'))
    -> per_pertype lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 c1 c2 cl1 rec1 cl2 rec2 inh isper.
  intros eqiff per.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  - SCase "uniquely_valued".
    dclose_lr.

    SSCase "CL_pertype".
    clear per.
    allunfold @per_pertype; exrepd.
    unfold eq_term_equals; intros.
    allrw.
    ccomputes_to_eqval.
    rw <- t; rw <- inh.
    generalize (c3 t1 t2); intro clt1.
    generalize (rec1 t1 t2); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    implies_ts_or (mkc_apply2 R1 t1 t2) clt1.
    apply uv in clt1.
    unfold eq_term_equals in clt1.
    unfold inhabited; split; sp.
    exists t3; rw <- clt1; sp.
    exists t3; rw clt1; sp.

  - SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_pertype;
    clear per;
    allunfold @per_pertype; exrepd;
    unfold per_pertype;
    ccomputes_to_eqval.

    + exists R1 R3 eq1 eq3; sp; spcast; sp.
      rw <- t; rw <- eqiff; rw <- t0; sp.
      allrw <-; sp.

  - SCase "type_value_respecting"; repdors; subst;
    apply CL_pertype; unfold per_pertype.

    (* 1 *)
    apply cequivc_mkc_pertype with (a := R1) in X1; sp.
    exists R1 b eq1 eq1; sp; spcast; sp.
    generalize (cl1 x y); intro clt1.
    generalize (rec1 x y); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr (mkc_apply2 R1 x y) (mkc_apply2 b x y)); intro imp1.
    repeat (autodimp imp1 hyp).
    repeat (rw @mkc_apply2_eq).
    repeat (apply sp_implies_cequivc_apply); auto.

    generalize (tyt (mkc_apply2 b x y) (eq1 x y)); sp.

    (* 2 *)
    apply @cequivc_mkc_pertype with (a := R2) in X1; sp.
    exists R2 b eq2 eq2; sp; spcast; sp.
    generalize (cl2 x y); intro clt1.
    generalize (rec2 x y); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr (mkc_apply2 R2 x y) (mkc_apply2 b x y)); intro imp1.
    repeat (autodimp imp1 hyp).
    repeat (rw @mkc_apply2_eq).
    repeat (apply sp_implies_cequivc_apply); auto.

    generalize (tyt (mkc_apply2 b x y) (eq2 x y)); sp.

    apply @is_per_iff with (eq1 := eq1); auto.

    rw eqiff; sp.

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
    generalize (tyvr (mkc_apply2 R1 t t) (mkc_apply2 R1 t t')); intro i; repeat (autodimp i h).
    repeat (rw @mkc_apply2_eq).
    apply implies_cequivc_apply; sp.
    generalize (rec1 t t'); sp.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2.
    generalize (tygs (mkc_apply2 R1 t t) (mkc_apply2 R1 t t') (eq1 t t)); intro k; repeat (autodimp k h).
    rw k in i.
    generalize (uv2 (mkc_apply2 R1 t t) (eq1 t t)); intro j; repeat (autodimp j h).

    apply eq_term_equals_implies_inhabited in eqteq.
    rw eqteq; sp.

  - SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_pertype;
    clear per;
    allunfold @per_pertype; exrepd;
    ccomputes_to_eqval;
    unfold per_pertype.

    (* 1 *)
    assert (forall x y, eq_term_equals (eq1 x y) (eq0 x y))
           as eqteq1
           by (apply (type_sys_props_pertype_eq_term_equals lib) with (ts := close lib ts) (R := R1); sp).

    exists R3 R1 eq3 eq1; sp; spcast; sp.
    rw <- t.
    apply eq_term_equals_implies_inhabited; sp.
    apply eq_term_equals_sym; sp.

    apply @is_per_iff with (eq1 := eq0); auto.

    rw t0; auto.

    (* 2 *)
    assert (forall x y, eq_term_equals (eq1 x y) (eq3 x y))
           as eqteq1
           by (apply (type_sys_props_pertype_eq_term_equals lib) with (ts := close lib ts) (R := R1); sp).

    exists R1 R0 eq1 eq0; sp; spcast; sp.
    rw t.
    apply eq_term_equals_implies_inhabited; sp.

    rw t0.
    rw t.
    apply eq_term_equals_implies_inhabited; sp.
    apply eq_term_equals_sym; sp.

  - SCase "type_gtransitive"; sp.

  - SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_pertype lib (close lib ts) T T4 eq3));
    try (move_term_to_top (per_pertype lib (close lib ts) T' T4 eq3));
    allunfold @per_pertype; exrepd;
    ccomputes_to_eqval;
    try (assert (forall x y, eq_term_equals (eq1 x y) (eq8 x y))
                as eqteq1
                by (apply (type_sys_props_pertype_eq_term_equals lib) with (ts := close lib ts) (R := R1); sp));
    try (assert (forall x y, eq_term_equals (eq1 x y) (eq7 x y))
                as eqteq2
                by (apply (type_sys_props_pertype_eq_term_equals lib) with (ts := close lib ts) (R := R1); sp));
    try (assert (forall x y, eq_term_equals (eq1 x y) (eq4 x y))
                as eqteq3
                by (apply (type_sys_props_pertype_eq_term_equals lib) with (ts := close lib ts) (R := R1); sp));
    try (assert (forall x y, eq_term_equals (eq2 x y) (eq9 x y))
                as eqteq4
                by (apply (type_sys_props_pertype_eq_term_equals lib) with (ts := close lib ts) (R := R2); sp));
    try (assert (forall x y, eq_term_equals (eq2 x y) (eq7 x y))
                as eqteq5
                by (apply (type_sys_props_pertype_eq_term_equals lib) with (ts := close lib ts) (R := R2); sp));
    try (assert (forall x y, eq_term_equals (eq2 x y) (eq4 x y))
                as eqteq6
                by (apply (type_sys_props_pertype_eq_term_equals lib) with (ts := close lib ts) (R := R2); sp)).

    + dands; apply CL_pertype; unfold per_pertype.

      * exists R4 R3 eq6 eq5; sp; spcast; sp.
        rw <- t; rw t1.
        apply eq_term_equals_implies_inhabited; sp.
        apply @eq_term_equals_trans with (eq2 := eq1 x y); sp.
        apply eq_term_equals_sym; sp.

      * exists R4 R3 eq6 eq5; sp; spcast; sp.
        rw <- t; rw t1.
        apply eq_term_equals_implies_inhabited; sp.
        apply @eq_term_equals_trans with (eq2 := eq1 x y); sp.
        apply eq_term_equals_sym; sp.

        rw t0; rw t1.
        apply eq_term_equals_implies_inhabited; sp.
        apply @eq_term_equals_trans with (eq2 := eq1 t5 t'); sp.
        apply eq_term_equals_sym; sp.

    + dands; apply CL_pertype; unfold per_pertype.

      * exists R4 R3 eq6 eq5; sp; spcast; sp.
        rw <- t; rw t1.
        apply eq_term_equals_implies_inhabited; sp.
        apply @eq_term_equals_trans with (eq2 := eq2 x y); sp.
        apply eq_term_equals_sym; sp.

      * exists R4 R3 eq6 eq5; sp; spcast; sp.
        rw <- t; rw t1.
        apply eq_term_equals_implies_inhabited; sp.
        apply @eq_term_equals_trans with (eq2 := eq2 x y); sp.
        apply eq_term_equals_sym; sp.

        rw t0; rw t1.
        apply eq_term_equals_implies_inhabited; sp.
        apply @eq_term_equals_trans with (eq2 := eq2 t5 t'); sp.
        apply eq_term_equals_sym; sp.
Qed.

