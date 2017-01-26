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



Lemma eq_term_equals_per_image_eq_if {p} :
  forall lib (eqa1 eqa2 : per(p)) f1 f2,
    cequivc lib f1 f2
    -> eq_term_equals eqa1 eqa2
    -> eq_term_equals (per_image_eq lib eqa1 f1) (per_image_eq lib eqa2 f2).
Proof.
  introv ceq eqt.
  unfold eq_term_equals; introv; split; intro k; induction k.

  apply @image_eq_cl with (t := t); sp.

  apply @image_eq_eq with (a1 := a1) (a2 := a2); sp; spcast.
  apply eqt; sp.
  apply cequivc_trans with (b := mkc_apply f1 a1); auto.
  apply sp_implies_cequivc_apply; sp.
  apply cequivc_trans with (b := mkc_apply f1 a2); auto.
  apply sp_implies_cequivc_apply; sp.

  apply @image_eq_cl with (t := t); sp.

  apply @image_eq_eq with (a1 := a1) (a2 := a2); sp; spcast.
  apply eqt; sp.
  apply cequivc_trans with (b := mkc_apply f2 a1); auto.
  apply sp_implies_cequivc_apply; sp; apply cequivc_sym; sp.
  apply cequivc_trans with (b := mkc_apply f2 a2); auto.
  apply sp_implies_cequivc_apply; sp; apply cequivc_sym; sp.
Qed.

Lemma per_image_eq_sym {p} :
  forall lib (eqa : per(p)) f t1 t2,
    term_equality_symmetric eqa
    -> per_image_eq lib eqa f t1 t2
    -> per_image_eq lib eqa f t2 t1.
Proof.
  introv tes per.
  induction per.
  apply @image_eq_cl with (t := t); sp.
  apply @image_eq_eq with (a1 := a2) (a2 := a1); sp.
Qed.

Lemma per_image_eq_trans {p} :
  forall lib (eqa : per(p)) f t1 t2 t3,
    term_equality_transitive eqa
    -> per_image_eq lib eqa f t1 t2
    -> per_image_eq lib eqa f t2 t3
    -> per_image_eq lib eqa f t1 t3.
Proof.
  introv tet per1 per2.
  apply image_eq_cl with (t := t2); sp.
Qed.

Lemma per_image_eq_cequiv {p} :
  forall lib (eqa : per(p)) f t t',
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> t ~=~(lib) t'
    -> per_image_eq lib eqa f t t
    -> per_image_eq lib eqa f t t'.
Proof.
  introv tes tet ceq per.
  revert_dependents t'.
  induction per; introv ceq.
  apply IHper2; auto.
  apply @image_eq_eq with (a1 := a2) (a2 := a2); sp.
  apply tet with (t2 := a1); sp.
  spcast.
  apply cequivc_trans with (b := t2); sp.
  apply cequivc_sym; sp.
Qed.

Lemma close_type_system_image {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A A' f f' eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_image A f)
    -> computes_to_valc lib T' (mkc_image A' f')
    -> close lib ts A A' eqa
    -> type_sys_props lib (close lib ts) A A' eqa
    -> ccequivc lib f f'
    -> (forall t t' : CTerm, eq t t' <=> per_image_eq lib eqa f t t')
    -> per_image lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou c1 c2 cla reca ceq eqiff per.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  - SCase "uniquely_valued".
    dclose_lr.

    + SSCase "CL_image".
      clear per.
      allunfold @per_image; exrepd.
      unfold eq_term_equals; intros.
      allrw.
      ccomputes_to_eqval.
      revert t1 t2.
      rw @fold_eq_term_equals.
      apply eq_term_equals_per_image_eq_if; sp.
      onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
      generalize (uv A2 eqa0); sp.

  - SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_image;
    clear per;
    allunfold @per_image; exrepd;
    unfold per_image;
    ccomputes_to_eqval.

    + exists eqa0 A A2 f f2; sp; spcast; sp.
      apply eq_term_equals_trans with (eq2 := eq); sp.
      apply eq_term_equals_sym; sp.

  - SCase "type_value_respecting"; repdors; subst;
    apply CL_image; unfold per_image.

    (* 1 *)
    generalize (cequivc_mkc_image lib T T3 A f); intro k; repeat (autodimp k hyp); exrepnd.
    exists eqa A a' f b'; sp; spcast; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr A a'); introv j; repeat (autodimp j hyp).

    (* 2 *)
    generalize (cequivc_mkc_image lib T' T3 A' f'); intro k; repeat (autodimp k hyp); exrepnd.
    exists eqa A' a' f' b'; sp; spcast; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr A' a'); introv j; repeat (autodimp j hyp).
    allrw (@fold_eq_term_equals).
    apply eq_term_equals_trans with (eq2 := per_image_eq lib eqa f); sp.
    apply eq_term_equals_per_image_eq_if; sp.

  - SCase "term_symmetric".
    unfold term_equality_symmetric; introv eqt.
    rw eqiff in eqt; rw eqiff.
    apply per_image_eq_sym; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; sp.

  - SCase "term_transitive".
    unfold term_equality_transitive; introv eqt1 eqt2.
    rw eqiff in eqt1; rw eqiff in eqt2; rw eqiff.
    apply @per_image_eq_trans with (t2 := t2); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; sp.

  - SCase "term_value_respecting".
    unfold term_equality_respecting; introv e c.
    rw eqiff in e; rw eqiff.
    apply per_image_eq_cequiv; sp;
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; sp.

  - SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_image;
    clear per;
    allunfold @per_image; exrepd;
    ccomputes_to_eqval;
    unfold per_image.

    (* 1 *)
    exists eqa0 A2 A f2 f; sp; spcast; sp.
    apply (type_sys_props_ts_sym3 lib) with (C := A') (eq1 := eqa); sp.
    apply cequivc_sym; sp.
    apply eq_term_equals_trans with (eq2 := per_image_eq lib eqa0 f); sp.
    apply eq_term_equals_per_image_eq_if; sp.

    (* 2 *)
    exists eqa0 A A1 f f1; sp; spcast; sp.
    apply (type_sys_props_ts_sym2 lib) with (C := A') (eq1 := eqa); sp.
    apply cequivc_sym; sp.
    apply eq_term_equals_trans with (eq2 := per_image_eq lib eqa0 f1); sp.
    apply eq_term_equals_per_image_eq_if; sp.

  - SCase "type_gtransitive"; sp.

  - SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_image lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_image lib (close lib ts) T' T4 eq2));
    allunfold @per_image; exrepd;
    ccomputes_to_eqval.

    + dands; apply CL_image; unfold per_image.

      * exists eqa1 A0 A2 f0 f2; sp; spcast; sp.
        apply (type_sys_props_ts_trans3 lib) with (B := A) (D := A') (eq2 := eqa0) (eq := eqa); sp.
        apply cequivc_trans with (b := f); sp.

      * exists eqa0 A0 A2 f0 f2; sp; spcast; sp.
        apply (type_sys_props_ts_trans4 lib) with (B := A) (D := A') (eq1 := eqa1) (eq := eqa); sp.
        apply cequivc_trans with (b := f); sp.
        apply @eq_term_equals_trans with (eq2 := per_image_eq lib eqa0 f); sp.
        apply eq_term_equals_per_image_eq_if; sp.
        apply cequivc_sym; sp.

    + dands; apply CL_image; unfold per_image.

      * exists eqa1 A0 A2 f0 f2; sp; spcast; sp.
        apply type_sys_props_sym in reca.
        apply (type_sys_props_ts_trans3 lib) with (B := A') (D := A) (eq2 := eqa0) (eq := eqa); sp.
        apply cequivc_trans with (b := f'); sp.

      * exists eqa0 A0 A2 f0 f2; sp; spcast; sp.
        apply type_sys_props_sym in reca.
        apply (type_sys_props_ts_trans4 lib) with (B := A') (D := A) (eq1 := eqa1) (eq := eqa); sp.
        apply cequivc_trans with (b := f'); sp.
        apply @eq_term_equals_trans with (eq2 := per_image_eq lib eqa0 f'); sp.
        apply eq_term_equals_per_image_eq_if; sp.
        apply cequivc_sym; sp.
Qed.

