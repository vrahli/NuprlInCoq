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


Lemma inhabited_point {p} :
  forall lib (eqa : per(p)) (eqb : per-fam(eqa)) t1 t2 t3 e e'
         ts v1 v2 B1 B2,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
          type_sys_props lib ts
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> inhabited (eqb t1 t2 e)
    -> inhabited (eqb t1 t3 e').
Proof.
  introv syma tra tsp inh.
  generalize (eq_term_equals_sym_tsp2 lib ts eqa eqb v1 B1 v2 B2); intro k;
  repeat (autodimp k hyp); repnd.
  unfold inhabited in inh; exrepnd.
  exists t.
  assert (eqa t1 t1) as e1 by (apply tra with (t2 := t2); sp).
  generalize (k0 t1 t2 e e1); introv eqt1.
  generalize (k0 t1 t3 e' e1); introv eqt2.
  rw eqt2; rw eqt1 in inh0; sp.
Qed.


Lemma close_type_system_set {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A A' v v' B B' eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_set A v B)
    -> computes_to_valc lib T' (mkc_set A' v' B')
    -> close lib ts A A' eqa
    -> (forall (a a' : CTerm) (e : eqa a a'),
          close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
    -> (forall (a a' : CTerm) (e : eqa a a'),
          type_system lib ts ->
          defines_only_universes lib ts ->
          type_sys_props lib (close lib ts) (substc a v B) (substc a' v' B')
                         (eqb a a' e))
    -> (forall t t' : CTerm,
          eq t t' <=> {e : eqa t t' , inhabited (eqb t t' e)})
    -> per_set lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) A A' eqa
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 c1 c2 X1 clb recb eqiff per IHX1.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr;
    try (complete (apply defines_only_universes_set_L with (T2 := T3) (eq2 := eq') in per; sp));
    try (complete (apply defines_only_universes_set_R with (T2 := T3) (eq2 := eq') in per; sp)).

    SSCase "CL_set".
    allunfold @per_set; exrepd.
    generalize (eq_term_equals_type_family lib T T3 eqa0 eqa eqb0 eqb (close lib ts) A v B A' v' B' mkc_set); intro i.
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))); repnd.

    unfold eq_term_equals; sp.
    rw t0; rw eqiff; split; intro k; exrepnd.

    duplicate e as e'; rw i0 in e.
    exists e; sp.
    unfold inhabited in k0; exrepnd.
    exists t5.
    generalize (i1 t3 t4 e e'); intro j; rw j; sp.

    duplicate e as e'; rw <- i0 in e.
    exists e; sp.
    unfold inhabited in k0; exrepnd.
    exists t5.
    generalize (i1 t3 t4 e' e); intro j; rw <- j; sp.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_set;
    clear per;
    allunfold @per_set; exrepd;
    unfold per_set;
    exists eqa0 eqb0; sp;
    allrw <-; sp.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_set; unfold per_set; exists eqa eqb; sp.

    duplicate c1 as ct.
    apply @cequivc_mkc_set with (T' := T3) in ct; sp.

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
    apply @cequivc_mkc_set with (T' := T3) in ct; sp.

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
    assert (eqa t1 t1) as eqaa by (apply t0 with (t2 := t2); auto).
    assert (eqa t2 t1) as e' by auto.
    exists e'.
    unfold inhabited in eqts0; exrepnd.
    unfold inhabited; exists t4.

    generalize (eq_term_equals_sym_tsp lib (close lib ts) eqa eqb t1 t2 eqaa e0 e'
                                       v B v' B'); intro i.
    autodimp i h; repnd.
    rw i1; rw <- i0; sp.

  + SCase "term_transitive".
    unfold term_equality_transitive; sp.
    apply eqiff; sp.
    assert (eq t1 t2) as eq12 by auto.
    assert (eq t2 t3) as eq23 by auto.
    rw eqiff in eq12; rw eqiff in eq23; exrepnd.

    onedtsp IHX0 IHX2 IHX3 IHX4 IHX5 IHX6 IHX7 IHX8 tygs tygt dum.

    assert (eqa t1 t3) as e' by (apply IHX7 with (t2 := t2); auto).
    exists e'.

    generalize (inhabited_point lib eqa eqb t1 t2 t3 e0 e' (close lib ts) v v' B B');
      introv k; repeat (autodimp k hyp).

  + SCase "term_value_respecting".
    unfold term_equality_respecting; sp.
    apply eqiff; sp.
    assert (eq t t) as eqtt by auto.
    apply eqiff in eqtt; exrepnd.

    onedtsp X5 X6 X7 X8 X9 X10 X11 X4 tygs1 tygt1 dum1; sp.
    generalize (X4 t t'); introv e'; repeat (autodimp e' hyp).
    exists e'.

    generalize (inhabited_point lib eqa eqb t t t' e e' (close lib ts) v v' B B');
      introv k; repeat (autodimp k hyp).

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr;
    apply CL_set;
    clear per;
    allunfold @per_set; exrepd.

    (* 1 *)
    generalize (eq_term_equals_type_family
                  lib T T3 eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_set); intro i.
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    unfold per_set.
    exists eqa eqb; sp.

    rw t0; split; intro k; sp.

    duplicate e as e'.
    rw <- i0 in e.
    exists e.
    generalize (i1 t1 t' e' e); intro j.
    apply eq_term_equals_implies_inhabited in j.
    rw <- j; auto.

    duplicate e as e'.
    rw i0 in e.
    exists e.
    generalize (i1 t1 t' e e'); intro j.
    apply eq_term_equals_implies_inhabited in j.
    rw j; auto.

    (* 2 *)
    generalize (eq_term_equals_type_family2
                  lib T3 T eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_set); intro i;
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp)));
    repnd.

    unfold per_set.
    exists eqa eqb; sp.

    rw t0; split; intro k; sp.

    duplicate e as e'.
    rw <- i0 in e.
    exists e.
    generalize (i1 t1 t' e' e); intro j.
    apply eq_term_equals_implies_inhabited in j.
    rw <- j; auto.

    duplicate e as e'.
    rw i0 in e.
    exists e.
    generalize (i1 t1 t' e e'); intro j.
    apply eq_term_equals_implies_inhabited in j.
    rw j; auto.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_set lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_set lib (close lib ts) T' T4 eq2)).

    (* 1 *)
    clear per.
    allunfold @per_set; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T eqa1 eqa eqb1 eqb (close lib ts)
                  A v B A' v' B' mkc_set); intro i.
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    generalize (type_family_trans2
                  lib mkc_set (close lib ts) T3 T T4 eqa eqb eqa0 eqb0 A v B A' v' B'); intro j.
    repeat (autodimp j hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    dands; apply CL_set; unfold per_set; exists eqa eqb; sp; allrw.

    split; intro pp; sp.

    duplicate e as e'.
    rw <- i0 in e.
    exists e.
    generalize (i1 t3 t' e' e); intro k.
    apply eq_term_equals_implies_inhabited in k.
    rw <- k; auto.

    duplicate e as e'.
    rw i0 in e.
    exists e.
    generalize (i1 t3 t' e e'); intro k.
    apply eq_term_equals_implies_inhabited in k.
    rw k; auto.

    split; intro pp; sp.

    duplicate e as e'.
    rw <- j0 in e.
    exists e.
    generalize (j1 t3 t' e e'); intro k.
    apply eq_term_equals_implies_inhabited in k.
    rw k; auto.

    duplicate e as e'.
    rw j0 in e.
    exists e.
    generalize (j1 t3 t' e' e); intro k.
    apply eq_term_equals_implies_inhabited in k.
    rw <- k; auto.

    (* 2 *)
    clear per.
    allunfold @per_set; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T' eqa1 eqa eqb1 eqb (close lib ts)
                  A' v' B' A v B mkc_set); intro i.
    repeat (autodimp i hyp;
            try (complete (introv e; eqconstr e; sp));
            try (complete (apply type_sys_props_sym; sp))).
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    intros.
    apply type_sys_props_sym.
    apply type_sys_props_eqb_comm; sp.
    apply tet with (t2 := a'); sp.
    apply tet with (t2 := a); sp.
    repnd.

    generalize (type_family_trans2
                  lib mkc_set (close lib ts) T3 T' T4 eqa eqb eqa0 eqb0 A' v' B' A v B); intro j.
    repeat (autodimp j hyp;
            try (complete (introv e; eqconstr e; sp));
            try (complete (apply type_sys_props_sym; sp))).
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    intros.
    apply type_sys_props_sym.
    apply type_sys_props_eqb_comm; sp.
    apply tet with (t2 := a'); sp.
    apply tet with (t2 := a); sp.
    repnd.

    dands; apply CL_set; unfold per_set; exists eqa eqb; sp; allrw.

    split; intro pp; sp.

    duplicate e as e'.
    rw <- i0 in e.
    exists e.
    generalize (i1 t3 t' e' e); intro k.
    apply eq_term_equals_implies_inhabited in k.
    rw <- k; auto.

    duplicate e as e'.
    rw i0 in e.
    exists e.
    generalize (i1 t3 t' e e'); intro k.
    apply eq_term_equals_implies_inhabited in k.
    rw k; auto.

    split; intro pp; sp.

    duplicate e as e'.
    rw <- j0 in e.
    exists e.
    generalize (j1 t3 t' e e'); intro k.
    apply eq_term_equals_implies_inhabited in k.
    rw k; auto.

    duplicate e as e'.
    rw j0 in e.
    exists e.
    generalize (j1 t3 t' e' e); intro k.
    apply eq_term_equals_implies_inhabited in k.
    rw <- k; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
