(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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



Lemma eq_term_equals_per_ffatom_eq_if {p} :
  forall lib (eqa1 eqa2 : per(p)) u x,
    eq_term_equals eqa1 eqa2
    -> eq_term_equals
         (per_ffatom_eq lib eqa1 u x)
         (per_ffatom_eq lib eqa2 u x).
Proof.
  introv eqt.
  unfold eq_term_equals, per_ffatom_eq; introv; split; intro k; exrepnd;
  dands; auto; exists y; dands; auto; apply eqt; auto.
Qed.

Lemma per_ffatom_eq_symmetric {p} :
  forall lib (eq : per(p)) x u t1 t2,
    term_equality_symmetric eq
    -> per_ffatom_eq lib eq x u t1 t2
    -> per_ffatom_eq lib eq x u t2 t1.
Proof.
  introv tes per.
  allunfold @per_ffatom_eq; exrepnd; dands; allrw; try (complete sp).
  exists y; dands; auto.
Qed.

Lemma per_ffatom_eq_transitive {p} :
  forall lib (eq : per(p)) x u t1 t2 t3,
    term_equality_transitive eq
    -> per_ffatom_eq lib eq x u t1 t2
    -> per_ffatom_eq lib eq x u t2 t3
    -> per_ffatom_eq lib eq x u t1 t3.
Proof.
  introv tet per1 per2.
  allunfold @per_ffatom_eq; exrepnd.
  dands; try (allrw; complete sp).
  exists y; dands; auto.
Qed.

Lemma per_ffatom_eq_cequiv {p} :
  forall lib (eq : per(p)) x u t1 t2,
    term_equality_respecting lib eq
    -> cequivc lib t1 t2
    -> per_ffatom_eq lib eq x u t1 t1
    -> per_ffatom_eq lib eq x u t1 t2.
Proof.
  introv res ceq per.
  allunfold @per_ffatom_eq; repnd; dands; auto; spcast.
  apply cequivc_axiom in ceq; auto.
Qed.

Lemma cequiv_mk_ffatom {p} :
  forall lib t t' T x a,
    computes_to_value lib t (mk_free_from_atom T x a)
    -> cequiv lib t t'
    -> {T', x', a' : @NTerm p $
         computes_to_value lib t' (mk_free_from_atom T' x' a')
         # cequiv lib T T'
         # cequiv lib x x'
         # cequiv lib a a'}.
Proof. prove_cequiv_mk.
Qed.

Lemma cequivc_mkc_ffatom {p} :
  forall lib t t' T x a,
    computes_to_valc lib t (mkc_free_from_atom T x a)
    -> cequivc lib t t'
    -> {T', x', a' : @CTerm p $
         computes_to_valc lib t' (mkc_free_from_atom T' x' a')
         # cequivc lib T T'
         # cequivc lib x x'
         # cequivc lib a a'}.
Proof.
  unfold computes_to_valc, cequivc; intros; destruct_cterms; allsimpl.
  generalize (cequiv_mk_ffatom lib x3 x2 x1 x x0); intro k.
  repeat (dest_imp k hyp); exrepnd.
  applydup @computes_to_value_isvalue in k1 as j.
  inversion j as [u isp v]; subst.
  allrw <- @isprogram_free_from_atom_iff; repnd.
  exists (mk_cterm T' isp0) (mk_cterm x' isp1) (mk_cterm a' isp); simpl; sp.
Qed.

Lemma cequivc_utoken {o} :
  forall lib t t' u,
    computes_to_valc lib t (mkc_utoken u)
    -> @cequivc o lib t t'
    -> computes_to_valc lib t' (mkc_utoken u).
Proof.
  introv comp ceq.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply @cequivc_canonical_form with (t' := t') in comp; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

Lemma per_ffatom_eq_elt {o} :
  forall lib (eqa : per(o)) u x1 x2,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> eqa x1 x2
    -> (per_ffatom_eq lib eqa u x1) <=2=> (per_ffatom_eq lib eqa u x2).
Proof.
  introv sym trans eqxs.
  unfold per_ffatom_eq; introv; split; introv k; exrepnd; dands; auto;
  exists y; dands; auto.
  apply (trans x2 x1 y); sp.
  apply (trans x1 x2 y); sp.
Qed.

Lemma close_type_system_ffatom {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A1 A2 x1 x2 a1 a2
         eqa (u : get_patom_set p),
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_free_from_atom A1 x1 a1)
    -> computes_to_valc lib T' (mkc_free_from_atom A2 x2 a2)
    -> close lib ts A1 A2 eqa
    -> type_sys_props lib (close lib ts) A1 A2 eqa
    -> eqa x1 x2
    -> computes_to_valc lib a1 (mkc_utoken u)
    -> computes_to_valc lib a2 (mkc_utoken u)
    -> (eq <=2=> (per_ffatom_eq lib eqa u x1))
    -> per_ffatom lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou c1 c2 cla reca eqxs ca1 ca2 eqiff; introv per.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  - SCase "uniquely_valued".
    dclose_lr.

    + SSCase "CL_ffatom".
      clear per.
      allunfold @per_ffatom; exrepd.
      unfold eq_term_equals; intros.
      allrw.
      ccomputes_to_eqval.
      revert t1 t2; rw @fold_eq_term_equals.
      apply eq_term_equals_per_ffatom_eq_if; auto.
      onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
      generalize (uv A3 eqa0); sp.

  - SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_ffatom;
    clear per;
    allunfold @per_ffatom; exrepd;
    unfold per_ffatom;
    ccomputes_to_eqval.

    + exists A1 A3 x1 x3 a1 a3 eqa0 u; sp; spcast; sp.
      apply eq_term_equals_trans with (eq2 := eq); sp.
      apply eq_term_equals_sym; sp.

  - SCase "type_value_respecting"; repdors; subst;
    apply CL_ffatom; unfold per_ffatom.

    (* 1 *)
    generalize (cequivc_mkc_ffatom lib T T3 A1 x1 a1); introv k; repeat (autodimp k hyp); exrepnd.
    exists A1 T'0 x1 x' a1 a' eqa u; sp; spcast; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr A1 T'0); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    pose proof (tevr x1 x') as h; repeat (autodimp h hyp).
    eapply tet; eauto.
    spcast; auto.
    eapply cequivc_utoken in k0; eauto.

    (* 2 *)
    generalize (cequivc_mkc_ffatom lib T' T3 A2 x2 a2); introv k; repeat (autodimp k hyp); exrepnd.
    exists A2 T'0 x2 x' a2 a' eqa u; sp; spcast; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tyvr A2 T'0); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    pose proof (tevr x2 x') as h; repeat (autodimp h hyp).
    eapply tet; eauto.
    spcast; auto.
    eapply cequivc_utoken in k0; eauto.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    pose proof (per_ffatom_eq_elt lib eqa u x1 x2) as h; repeat (autodimp h hyp).
    eapply eq_term_equals_trans; eauto.

  - SCase "term_symmetric".
    unfold term_equality_symmetric; introv eqt.
    rw eqiff in eqt; rw eqiff.
    apply per_ffatom_eq_symmetric; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; sp.

  - SCase "term_transitive".
    unfold term_equality_transitive; introv eqt1 eqt2.
    rw eqiff in eqt1; rw eqiff in eqt2; rw eqiff.
    apply @per_ffatom_eq_transitive with (t2 := t2); sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; sp.

  - SCase "term_value_respecting".
    unfold term_equality_respecting; introv eqt ceq.
    rw eqiff in eqt; rw eqiff.
    spcast.
    apply per_ffatom_eq_cequiv; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; sp.

  - SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_ffatom;
    clear per;
    allunfold @per_ffatom; exrepd;
    ccomputes_to_eqval;
    unfold per_partial.

    (* 1 *)
    exists A3 A1 x3 x1 a3 a1 eqa0 u; sp; spcast; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tygs A1 A3 eqa0); intro k; repeat (autodimp k hyp).
    rw <- k; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; auto.
    pose proof (uv A3 eqa0) as h; autodimp h hyp.
    apply h; apply h in e; auto.
    eapply eq_term_equals_trans; eauto.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; auto.
    pose proof (uv A3 eqa0) as h; autodimp h hyp.
    pose proof (eq_term_equals_per_ffatom_eq_if lib eqa0 eqa u x1) as h1.
    autodimp h1 hyp; [apply eq_term_equals_sym; auto|].
    eapply eq_term_equals_trans; eauto.
    pose proof (per_ffatom_eq_elt lib eqa u x1 x3) as h2; repeat (autodimp h2 hyp).
    apply h; auto.
    eapply eq_term_equals_trans; eauto.
    apply eq_term_equals_per_ffatom_eq_if; auto.

    (* 2 *)
    exists A1 A0 x1 x0 a1 a0 eqa0 u; sp; spcast; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
    generalize (tygs A1 A0 eqa0); intro k; repeat (autodimp k hyp).
    rw k; sp.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; auto.
    pose proof (tygs A1 A0 eqa0) as k; repeat (autodimp k hyp); apply k in c3; clear k.
    pose proof (uv A0 eqa0) as h; autodimp h hyp.
    apply h; apply h in e; auto.
    eapply eq_term_equals_trans; eauto.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt; auto.
    pose proof (tygs A1 A0 eqa0) as k; repeat (autodimp k hyp); apply k in c3; clear k.
    pose proof (uv A0 eqa0) as h; autodimp h hyp.
    pose proof (eq_term_equals_per_ffatom_eq_if lib eqa0 eqa u x0) as h1.
    autodimp h1 hyp; [apply eq_term_equals_sym; auto|].
    eapply eq_term_equals_trans; eauto.
    pose proof (per_ffatom_eq_elt lib eqa u x0 x1) as h2; repeat (autodimp h2 hyp).
    apply h; auto.
    eapply eq_term_equals_trans; eauto.
    apply eq_term_equals_per_ffatom_eq_if; auto.

  - SCase "type_gtransitive"; sp.

  - SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_ffatom lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_ffatom lib (close lib ts) T' T4 eq2));
    allunfold @per_ffatom; exrepd;
    ccomputes_to_eqval.

    + dands; apply CL_ffatom; unfold per_ffatom.

      * exists A4 A3 x4 x3 a4 a3 eqa1 u; sp; spcast; sp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        generalize (tymt A1 A4 A3 eqa1 eqa0); sp.

        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        pose proof (tygs A1 A4 eqa1) as k; repeat (autodimp k hyp).
        apply k in c8.
        pose proof (uv A4 eqa1) as h1; autodimp h1 hyp.
        pose proof (uv A3 eqa0) as h2; autodimp h2 hyp.
        apply h1; apply h1 in e1; apply h2 in e.
        eapply tet; eauto.

      * exists A4 A3 x4 x3 a4 a3 eqa0 u; sp; spcast; sp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        generalize (tymt A1 A4 A3 eqa1 eqa0); sp.

        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        pose proof (tygs A1 A4 eqa1) as k; repeat (autodimp k hyp).
        apply k in c8.
        pose proof (uv A4 eqa1) as h1; autodimp h1 hyp.
        pose proof (uv A3 eqa0) as h2; autodimp h2 hyp.
        apply h2; apply h1 in e1; apply h2 in e.
        eapply tet; eauto.

        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        pose proof (tygs A1 A4 eqa1) as k; repeat (autodimp k hyp).
        apply k in c8.
        pose proof (uv A4 eqa1) as h1; autodimp h1 hyp.
        pose proof (uv A3 eqa0) as h2; autodimp h2 hyp.
        apply h1 in e1; apply h2 in e.
        eapply eq_term_equals_trans; eauto.
        apply per_ffatom_eq_elt; auto.
        introv z; apply h2 in z; apply h2; auto.
        introv z1 z2; apply h2 in z1; apply h2 in z2; apply h2; auto.
        eapply tet; eauto.
        apply h2; eapply tet; eauto.

    + dands; apply CL_ffatom; unfold per_ffatom.

      * exists A4 A3 x4 x3 a4 a3 eqa1 u; sp; spcast; sp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        generalize (tymt A2 A4 A3 eqa1 eqa0); sp.

        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        pose proof (tygs A2 A4 eqa1) as k; repeat (autodimp k hyp).
        apply k in c8.
        pose proof (uv A4 eqa1) as h1; autodimp h1 hyp.
        pose proof (uv A3 eqa0) as h2; autodimp h2 hyp.
        apply h1; apply h1 in e1; apply h2 in e.
        eapply tet; eauto.

      * exists A4 A3 x4 x3 a4 a3 eqa0 u; sp; spcast; sp.
        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        generalize (tymt A2 A4 A3 eqa1 eqa0); sp.

        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        pose proof (tygs A2 A4 eqa1) as k; repeat (autodimp k hyp).
        apply k in c8.
        pose proof (uv A4 eqa1) as h1; autodimp h1 hyp.
        pose proof (uv A3 eqa0) as h2; autodimp h2 hyp.
        apply h2; apply h1 in e1; apply h2 in e.
        eapply tet; eauto.

        onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
        pose proof (tygs A2 A4 eqa1) as k; repeat (autodimp k hyp).
        apply k in c8.
        pose proof (uv A4 eqa1) as h1; autodimp h1 hyp.
        pose proof (uv A3 eqa0) as h2; autodimp h2 hyp.
        apply h1 in e1; apply h2 in e.
        eapply eq_term_equals_trans; eauto.
        apply per_ffatom_eq_elt; auto.
        introv z; apply h2 in z; apply h2; auto.
        introv z1 z2; apply h2 in z1; apply h2 in z2; apply h2; auto.
        eapply tet; eauto.
        apply h2; eapply tet; eauto.
Qed.

