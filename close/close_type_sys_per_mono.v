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


Lemma per_mono_eq_congr {p} :
  forall lib (eqa eqb : per(p)),
  eq_term_equals eqa eqb
  -> (mono_equality lib eqa  <=> mono_equality lib eqb).
Proof.
  introv; unfold eq_term_equals, mono_equality, cofinite_subst_fapprox_eqc,
    subst_fix_eqc; split; spc;
  dtiffs2;
  match goal with
  [ H : forall _ _ , _  |- _] => (apply H)
  end; eauto.
Qed.

(* !! Move to eq_rel.v *)
Hint Immediate t_iff_refl.

Lemma eq_term_equals_per_mono_eq_if {p} :
  forall lib (eqa1 eqa2 : per(p)),
    eq_term_equals eqa1 eqa2
    -> eq_term_equals (per_mono_eq lib eqa1) (per_mono_eq lib eqa2).
Proof.
  introv eqt.
  unfold eq_term_equals.
  allunfold @per_mono_eq. introv.
  apply (per_mono_eq_congr lib) in eqt.
  rw eqt. auto.
Qed.

Lemma per_mono_eq_symmetric {p} :
  forall lib (eq : per(p)) t1 t2,
    term_equality_symmetric eq
    -> per_mono_eq lib eq t1 t2
    -> per_mono_eq lib eq t2 t1.
Proof.
  introv tes per.
  allunfold @per_mono_eq; exrepnd; dands; allrw; try (complete sp).
Qed.

Lemma per_mono_eq_transitive {p} :
  forall lib (eq : per(p)) t1 t2 t3,
    term_equality_transitive eq
    -> per_mono_eq lib eq t1 t2
    -> per_mono_eq lib eq t2 t3
    -> per_mono_eq lib eq t1 t3.
Proof.
  introv tet per1 per2.
  allunfold @per_mono_eq; exrepnd.
  dands; try (allrw; complete sp).
Qed.

Lemma per_mono_eq_cequiv {p} :
  forall lib (eq : per(p)) t1 t2,
    term_equality_respecting lib eq
    -> cequivcn lib t1 t2
    -> per_mono_eq lib eq t1 t1
    -> per_mono_eq lib eq t1 t2.
Proof.
  introv res ceq per.
  allunfold @per_mono_eq; repnd; dands; auto.
  GC; try (spcast; eapply cequivcn_axiom; eauto 3 with slow).
Qed.



Lemma close_type_system_mono {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A1 A2 eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valcn lib T (mkcn_mono A1)
    -> computes_to_valcn lib T' (mkcn_mono A2)
    -> close lib ts A1 A2 eqa
    -> type_sys_props lib (close lib ts) A1 A2 eqa
    -> (forall t t' : cterm, eq t t' <=> per_mono_eq lib eqa t t')
    -> per_mono lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou c1 c2 cla reca eqiff per.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  - SCase "uniquely_valued".
    dclose_lr.

    + SSCase "CL_mono".
      clear per.
      allunfold @per_mono; exrepd.
      unfold eq_term_equals; intros.
      allrw.
      ccomputes_to_eqval.
      revert t1 t2; rw @fold_eq_term_equals.
      apply eq_term_equals_per_mono_eq_if.
      onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
      generalize (uv A3 eqa0); sp.

  - SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_mono;
    clear per;
    allunfold @per_mono; exrepd;
    unfold per_mono;
    ccomputes_to_eqval.

    + exists A1 A3 eqa0; sp; spcast; sp.
      apply eq_term_equals_trans with (eq2 := eq); sp.
      apply eq_term_equals_sym; sp.

  - SCase "type_value_respecting"; repdors; subst;
    apply CL_mono; unfold per_mono.

    (* 1 *)
    generalize (cequivcn_mkcn_mono lib T T3 A1); introv k; repeat (autodimp k hyp); exrepnd.
    exists A1 a' eqa; sp; spcast; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr A1 a'); sp.

    (* 2 *)
    generalize (cequivcn_mkcn_mono lib T' T3 A2); introv k; repeat (autodimp k hyp); exrepnd.
    exists A2 a' eqa; sp; spcast; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr A2 a'); sp.

  - SCase "term_symmetric".
    unfold term_equality_symmetric; introv eqt.
    rw eqiff in eqt; rw eqiff.
    apply per_mono_eq_symmetric; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; sp.

  - SCase "term_transitive".
    unfold term_equality_transitive; introv eqt1 eqt2.
    rw eqiff in eqt1; rw eqiff in eqt2; rw eqiff.
    apply @per_mono_eq_transitive with (t2 := t2); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; sp.

  - SCase "term_value_respecting".
    unfold term_equality_respecting; introv eqt ceq.
    rw eqiff in eqt; rw eqiff.
    spcast.
    apply per_mono_eq_cequiv; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; sp.

  - SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_mono;
    clear per;
    allunfold @per_mono; exrepd;
    ccomputes_to_eqval;
    unfold per_mono.

    (* 1 *)
    exists A3 A1 eqa0; sp; spcast; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tygs A1 A3 eqa0); intro k; repeat (autodimp k hyp).
    rw <- k; sp.

    (* 2 *)
    exists A1 A0 eqa0; sp; spcast; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tygs A1 A0 eqa0); intro k; repeat (autodimp k hyp).
    rw k; sp.

  - SCase "type_gtransitive"; sp.

  - SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_mono lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_mono lib (close lib ts) T' T4 eq2));
    allunfold @per_mono; exrepd;
    ccomputes_to_eqval.

    + dands; apply CL_mono; unfold per_mono.

      * exists A4 A3 eqa1; sp; spcast; sp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        generalize (tymt A1 A4 A3 eqa1 eqa0); sp.

      * exists A4 A3 eqa0; sp; spcast; sp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        generalize (tymt A1 A4 A3 eqa1 eqa0); sp.

    + dands; apply CL_mono; unfold per_mono.

      * exists A4 A3 eqa1; sp; spcast; sp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        generalize (tymt A2 A4 A3 eqa1 eqa0); sp.

      * exists A4 A3 eqa0; sp; spcast; sp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        generalize (tymt A2 A4 A3 eqa1 eqa0); sp.
Qed.
