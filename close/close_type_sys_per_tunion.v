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


Lemma eq_term_equals_per_tunion_eq_if {p} :
  forall (eqa1 eqa2 : per(p)) (eqb1 : per-fam(eqa1)) (eqb2 : per-fam(eqa2)),
    eqa1 <=2=> eqa2
    -> (forall (a1 a2 : cterm) (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
          (eqb1 a1 a2 e1) <=2=> (eqb2 a1 a2 e2))
    -> (per_tunion_eq eqa1 eqb1) <=2=> (per_tunion_eq eqa2 eqb2).
Proof.
  introv eqt1 eqt2.
  introv; split; intro k; induction k.

  - apply @tunion_eq_cl with (t := t); sp.

  - dup e as e'; apply eqt1 in e'.
    apply @tunion_eq_eq with (a1 := a1) (a2 := a2) (e := e'); sp; spcast.
    apply (eqt2 a1 a2 e e'); auto.

  - apply @tunion_eq_cl with (t := t); sp.

  - dup e as e'; apply eqt1 in e'.
    apply @tunion_eq_eq with (a1 := a1) (a2 := a2) (e := e'); sp; spcast.
    apply (eqt2 a1 a2 e' e); auto.
Qed.

Lemma per_tunion_eq_sym {p} :
  forall (eqa : per(p)) eqb t1 t2,
    (forall (a1 a2 : cterm) (e : eqa a1 a2),
       term_equality_symmetric (eqb a1 a2 e))
    -> per_tunion_eq eqa eqb t1 t2
    -> per_tunion_eq eqa eqb t2 t1.
Proof.
  introv tesb per.
  induction per.
  apply @tunion_eq_cl with (t := t); sp.
  apply @tunion_eq_eq with (a1 := a1) (a2 := a2) (e := e); sp.
  apply tesb; auto.
Qed.

Lemma per_tunion_eq_trans {p} :
  forall (eqa : per(p)) eqb t1 t2 t3,
    per_tunion_eq eqa eqb t1 t2
    -> per_tunion_eq eqa eqb t2 t3
    -> per_tunion_eq eqa eqb t1 t3.
Proof.
  introv per1 per2.
  apply tunion_eq_cl with (t := t2); sp.
Qed.

Lemma per_tunion_eq_cequiv {p} :
  forall lib (eqa : per(p)) eqb t t',
    (forall (a1 a2 : cterm) (e : eqa a1 a2),
       term_equality_symmetric (eqb a1 a2 e))
    -> (forall (a1 a2 : cterm) (e : eqa a1 a2),
       term_equality_transitive (eqb a1 a2 e))
    -> (forall (a1 a2 : cterm) (e : eqa a1 a2),
          term_equality_respecting lib (eqb a1 a2 e))
    -> t ~=~(lib) t'
    -> per_tunion_eq eqa eqb t t
    -> per_tunion_eq eqa eqb t t'.
Proof.
  introv tes tet ter ceq per.
  revert_dependents t'.
  induction per; introv ceq.
  apply IHper2; auto.
  apply @tunion_eq_eq with (a1 := a1) (a2 := a2) (e := e); sp.
  apply (ter a1 a2 e t2 t'); auto.
  apply tet with (t2 := t1); auto.
  apply tes; auto.
Qed.

Lemma close_type_system_tunion {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A A' v v' B B' eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valcn lib T (mkcn_tunion A v B)
    -> computes_to_valcn lib T' (mkcn_tunion A' v' B')
    -> close lib ts A A' eqa
    -> (forall (a a' : cterm) (e : eqa a a'),
          close lib ts (substcn a v B) (substcn a' v' B') (eqb a a' e))
    -> (forall (a a' : cterm) (e : eqa a a'),
          type_system lib ts ->
          defines_only_universes lib ts ->
          type_sys_props lib (close lib ts) (substcn a v B) (substcn a' v' B')
                         (eqb a a' e))
    -> (forall t t' : cterm,
          eq t t' <=> per_tunion_eq eqa eqb t t')
    -> per_tunion lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) A A' eqa
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 c1 c2 X1 clb recb eqiff per IHX1.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr;
    try (complete (apply defines_only_universes_tunion_L with (T2 := T3) (eq2 := eq') in per; sp));
    try (complete (apply defines_only_universes_tunion_R with (T2 := T3) (eq2 := eq') in per; sp)).

    SSCase "CL_tunion".
    allunfold @per_tunion; exrepd.
    generalize (eq_term_equals_type_family lib T T3 eqa0 eqa eqb0 eqb (close lib ts) A v B A' v' B' mkcn_tunion); intro i.
    repeat (autodimp i hyp; try (complete (introv ee; eqconstr ee; sp))); repnd.

    generalize (eq_term_equals_type_family lib T T' eqa1 eqa eqb1 eqb (close lib ts) A v B A' v' B' mkcn_tunion); intro j.
    repeat (autodimp j hyp; try (complete (introv ee; eqconstr ee; sp))); repnd.

    apply eq_term_equals_trans with (eq2 := per_tunion_eq eqa1 eqb1); auto.
    apply eq_term_equals_trans with (eq2 := per_tunion_eq eqa0 eqb0); auto;
    try (complete (apply eq_term_equals_sym; auto)).

    apply eq_term_equals_per_tunion_eq_if; auto.

    apply eq_term_equals_trans with (eq2 := eqa); auto.
    apply eq_term_equals_sym; auto.

    introv.
    dup e2 as e3.
    rw <- i0 in e3.
    apply eq_term_equals_trans with (eq2 := eqb a1 a2 e3); auto.
    apply eq_term_equals_sym; auto.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_tunion;
    clear per;
    allunfold @per_tunion; exrepd;
    unfold per_tunion;
    exists eqa0 eqb0; sp;
    allrw <-; sp.
    apply eq_term_equals_trans with (eq2 := eq); auto.
    apply eq_term_equals_sym; auto.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_tunion; unfold per_tunion; exists eqa eqb; sp.

    duplicate c1 as ct.
    apply @cequivcn_mkcn_tunion with (T' := T3) in ct; sp.

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
    apply @cequivcn_mkcn_tunion with (T' := T3) in ct; sp.

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
    unfold term_equality_symmetric; introv eqts.
    onedtsp e pp p0 p1 c t t0 t3 tygs tygt dum.
    apply eqiff; apply eqiff in eqts; exrepnd.
    apply per_tunion_eq_sym; auto.
    introv.
    pose proof (recb a1 a2 e0) as h; repeat (autodimp h hyp).
    onedtsp x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11; auto.

  + SCase "term_transitive".
    unfold term_equality_transitive; sp.
    apply eqiff; sp.
    assert (eq t1 t2) as eq12 by auto.
    assert (eq t2 t3) as eq23 by auto.
    rw eqiff in eq12; rw eqiff in eq23; exrepnd.
    apply (per_tunion_eq_trans eqa eqb t1 t2 t3); auto.

  + SCase "term_value_respecting".
    unfold term_equality_respecting; sp.
    apply eqiff; sp.
    assert (eq t t) as eqtt by auto.
    apply eqiff in eqtt; exrepnd.
    apply (per_tunion_eq_cequiv lib eqa eqb t t'); auto;
    introv;
    pose proof (recb a1 a2 e) as h; repeat (autodimp h hyp);
    onedtsp x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11; auto.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr;
    apply CL_tunion;
    clear per;
    allunfold @per_tunion; exrepd.

    (* 1 *)
    generalize (eq_term_equals_type_family
                  lib T T3 eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkcn_tunion); intro i.
    repeat (autodimp i hyp; try (complete (introv ee; eqconstr ee; sp))).
    repnd.

    exists eqa eqb; sp.

    apply eq_term_equals_trans with (eq2 := per_tunion_eq eqa0 eqb0); auto.
    apply eq_term_equals_per_tunion_eq_if; auto.
    apply eq_term_equals_sym; auto.

    (* 2 *)
    generalize (eq_term_equals_type_family2
                  lib T3 T eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkcn_tunion); intro i;
    repeat (autodimp i hyp; try (complete (introv ee; eqconstr ee; sp)));
    repnd.

    exists eqa eqb; sp.

    apply eq_term_equals_trans with (eq2 := per_tunion_eq eqa0 eqb0); auto.
    apply eq_term_equals_per_tunion_eq_if; auto.
    apply eq_term_equals_sym; auto.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_tunion lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_tunion lib (close lib ts) T' T4 eq2)).

    (* 1 *)
    clear per.
    allunfold @per_tunion; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T eqa1 eqa eqb1 eqb (close lib ts)
                  A v B A' v' B' mkcn_tunion); intro i.
    repeat (autodimp i hyp; try (complete (introv ee; eqconstr ee; sp))).
    repnd.

    generalize (type_family_trans2
                  lib mkcn_tunion (close lib ts) T3 T T4 eqa eqb eqa0 eqb0 A v B A' v' B'); intro j.
    repeat (autodimp j hyp; try (complete (introv ee; eqconstr ee; sp))).
    repnd.

    dands; apply CL_tunion; unfold per_tunion; exists eqa eqb; sp; allrw.

    eapply eq_term_equals_trans; eauto.
    apply eq_term_equals_per_tunion_eq_if; auto.
    apply eq_term_equals_sym; auto.

    eapply eq_term_equals_trans; eauto.
    apply eq_term_equals_per_tunion_eq_if; auto.
    apply eq_term_equals_sym; auto.
    introv.
    apply eq_term_equals_sym; auto.

    (* 2 *)
    clear per.
    allunfold @per_tunion; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T' eqa1 eqa eqb1 eqb (close lib ts)
                  A' v' B' A v B mkcn_tunion); intro i.
    repeat (autodimp i hyp;
            try (complete (introv ee; eqconstr ee; sp));
            try (complete (apply type_sys_props_sym; sp))).
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    intros.
    apply type_sys_props_sym.
    apply type_sys_props_eqb_comm; sp.
    apply tet with (t2 := a'); sp.
    apply tet with (t2 := a); sp.
    repnd.

    generalize (type_family_trans2
                  lib mkcn_tunion (close lib ts) T3 T' T4 eqa eqb eqa0 eqb0 A' v' B' A v B); intro j.
    repeat (autodimp j hyp;
            try (complete (introv ee; eqconstr ee; sp));
            try (complete (apply type_sys_props_sym; sp))).
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    intros.
    apply type_sys_props_sym.
    apply type_sys_props_eqb_comm; sp.
    apply tet with (t2 := a'); sp.
    apply tet with (t2 := a); sp.
    repnd.

    dands; apply CL_tunion; unfold per_tunion; exists eqa eqb; sp; allrw.

    eapply eq_term_equals_trans; eauto.
    apply eq_term_equals_per_tunion_eq_if; auto.
    apply eq_term_equals_sym; auto.

    eapply eq_term_equals_trans; eauto.
    apply eq_term_equals_per_tunion_eq_if; auto.
    apply eq_term_equals_sym; auto.
    introv.
    apply eq_term_equals_sym; auto.
Qed.
