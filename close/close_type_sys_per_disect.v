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

Require Export type_sys_useful.
Require Import dest_close.



Lemma close_type_system_disect {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A A' v v' B B' eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_disect A v B)
    -> computes_to_valc lib T' (mkc_disect A' v' B')
    -> close lib ts A A' eqa
    -> (forall (a a' : CTerm) (e : eqa a a'),
          close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
    -> (forall (a a' : CTerm) (e : eqa a a'),
          type_system lib ts ->
          defines_only_universes lib ts ->
          type_sys_props lib (close lib ts) (substc a v B) (substc a' v' B')
                         (eqb a a' e))
    -> (forall t t' : CTerm,
          eq t t' <=> {e : eqa t t' , eqb t t' e t t'})
    -> per_disect lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) A A' eqa
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 c1 c2 X1 clb recb eqiff per IHX1.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    * SSCase "CL_disect".
      allunfold @per_disect; exrepd.
      generalize (eq_term_equals_type_family lib T T3 eqa0 eqa eqb0 eqb (close lib ts) A v B A' v' B' mkc_disect); intro i.
      repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))); repnd.

      unfold eq_term_equals; sp.
      rw t0; rw eqiff; split; sp.

      assert (eqa0 t3 t4) as e' by (rw <- i0; auto).
      exists e'.
      generalize (i1 t3 t4 e' e); intro k.
      rw k; sp.

      assert (eqa t3 t4) as e' by (rw i0; auto).
      exists e'.
      generalize (i1 t3 t4 e e'); intro k.
      rw <- k; sp.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_disect;
    clear per;
    allunfold @per_disect; exrepd;
    unfold per_disect;
    exists eqa0 eqb0; sp;
    allrw <-; sp.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_disect; unfold per_disect; exists eqa eqb; sp.

    duplicate c1 as ct.
    apply @cequivc_mkc_disect with (T' := T3) in ct; sp.

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
    apply @cequivc_mkc_disect with (T' := T3) in ct; sp.

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
    assert (eq t1 t2) as eq12 by auto.
    apply eqiff in eq12; exrepnd.

    assert (eqa t1 t1) as e' by (apply t0 with (t2 := t2); auto).
    assert (eqa t2 t1) as e2 by auto.
    exists e2.

    generalize (eq_term_equals_sym_tsp lib (close lib ts) eqa eqb t1 t2 e' e0 e2
                                       v B v' B'); intro i.
    autodimp i h; repnd.

    (* Now we prove the equality between the applies *)
    unfold eq_term_equals in i.
    apply i in eq0.
    generalize (recb t2 t1 e2); sp.
    onedtsp X5 X6 X7 X8 X9 X10 X11 X4 tygs1 tygt1 dum1; sp.

  + SCase "term_transitive".
    unfold term_equality_transitive; introv e1 e2.
    assert (eq t1 t2) as eq12 by auto.
    assert (eq t2 t3) as eq23 by auto.
    apply eqiff in eq12; apply eqiff in eq23; apply eqiff; exrepnd.

    onedtsp IHX0 IHX2 IHX3 IHX4 IHX5 IHX6 IHX7 IHX8 tygs tygt dum.

    assert (eqa t1 t3) as e13 by (apply IHX7 with (t2 := t2); auto).
    assert (eqa t2 t2) as e22 by (apply IHX7 with (t2 := t1); auto).
    assert (eqa t2 t1) as e21 by sp.
    assert (eqa t1 t1) as e11 by (apply IHX7 with (t2 := t2); auto).
    assert (eqa t3 t2) as e32 by sp.
    assert (eqa t3 t1) as e31 by sp.

    exists e13.

    generalize (eq_term_equals_sym_tsp lib (close lib ts) eqa eqb t1 t2 e11 e0 e21
                                       v B v' B'); intro i; autodimp i h; repnd.

    generalize (eq_term_equals_sym_tsp lib (close lib ts) eqa eqb t2 t1 e22 e21 e0
                                       v B v' B'); intro j; autodimp j h; repnd.

    generalize (eq_term_equals_sym_tsp lib (close lib ts) eqa eqb t2 t3 e22 e e32
                                       v B v' B'); intro k; autodimp k h; repnd.

    generalize (eq_term_equals_sym_tsp lib (close lib ts) eqa eqb t1 t3 e11 e13 e31
                                       v B v' B'); intro l; autodimp l h; repnd.

    rw k0 in eq0.
    rw <- j1 in eq0.
    rw i0 in eq0.
    rw i0 in eq1.
    rw l0.

    generalize (recb t1 t1 e11); sp.
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1.
    unfold term_equality_transitive in tet1.
    apply tet1 with (t3 := t2); sp.

  + SCase "term_value_respecting".
    unfold term_equality_respecting; introv eqtt X3.
    apply eqiff in eqtt; apply eqiff; sp.

    onedtsp IHX0 IHX2 IHX3 IHX4 IHX5 IHX6 IHX7 IHX1 tygs tygt dum.

    assert (eqa t t') as e' by (apply IHX1; auto).

    exists e'.

    generalize (recb t t' e'); sp.
    onedtsp X4 X5 X6 X7 X8 X9 X10 X2 tygs1 tygt1 dum1.
    apply X2; auto.

    generalize (recb t t e); sp.
    onedtsp X12 X13 X14 X15 X16 X17 X18 X11 tygs2 tygt2 dum2.
    implies_ts_or (substc t' v' B') tygt2.
    apply X4 in tygt2.
    unfold eq_term_equals in tygt2; apply tygt2; auto.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr;
    apply CL_disect;
    clear per;
    allunfold @per_disect; exrepd.

    (* 1 *)
    generalize (eq_term_equals_type_family
                  lib T T3 eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_disect); intro i.
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    unfold per_disect.
    exists eqa eqb; sp.

    rw t0; split; sp.

    duplicate e as e'.
    rw <- i0 in e.
    exists e.
    generalize (i1 t1 t' e' e); intro eqt.
    rw <- eqt; sp.

    duplicate e as e'.
    rw i0 in e.
    exists e.
    generalize (i1 t1 t' e e'); intro eqt.
    rw eqt; sp.

    (* 2 *)
    generalize (eq_term_equals_type_family2
                  lib T3 T eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_disect); intro i;
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp)));
    repnd.

    unfold per_disect.
    exists eqa eqb; sp.

    rw t0; split; sp.

    duplicate e as e'.
    rw <- i0 in e.
    exists e.
    generalize (i1 t1 t' e' e); intro eqt.
    rw <- eqt; sp.

    duplicate e as e'.
    rw i0 in e.
    exists e.
    generalize (i1 t1 t' e e'); intro eqt.
    rw eqt; sp.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_disect lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_disect lib (close lib ts) T' T4 eq2)).

    (* 1 *)
    clear per.
    allunfold @per_disect; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T eqa1 eqa eqb1 eqb (close lib ts)
                  A v B A' v' B' mkc_disect); intro i.
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    generalize (type_family_trans2
                  lib mkc_disect (close lib ts) T3 T T4 eqa eqb eqa0 eqb0 A v B A' v' B'); intro j.
    repeat (autodimp j hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    dands; apply CL_disect; unfold per_disect; exists eqa eqb; sp; allrw.

    split; sp.

    assert (eqa t3 t') as e' by (rw i0; auto).
    exists e'.
    generalize (i1 t3 t' e e'); intro l.
    rw <- l; sp.

    assert (eqa1 t3 t') as e' by (rw <- i0; auto).
    exists e'.
    generalize (i1 t3 t' e' e); intro l.
    rw l; sp.

    split; sp.

    assert (eqa t3 t') as e' by (rw j0; auto).
    exists e'.
    generalize (j1 t3 t' e' e); intro l.
    rw l; sp.

    assert (eqa0 t3 t') as e' by (rw <- j0; auto).
    exists e'.
    generalize (j1 t3 t' e e'); intro l.
    rw <- l; sp.

    (* 2 *)
    clear per.
    allunfold @per_disect; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T' eqa1 eqa eqb1 eqb (close lib ts)
                  A' v' B' A v B mkc_disect); intro i.
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
                  lib mkc_disect (close lib ts) T3 T' T4 eqa eqb eqa0 eqb0 A' v' B' A v B); intro j.
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

    dands; apply CL_disect; unfold per_disect; exists eqa eqb; sp; allrw.

    split; sp.

    assert (eqa t3 t') as e' by (rw i0; auto).
    exists e'.
    generalize (i1 t3 t' e e'); intro l.
    rw <- l; sp.

    assert (eqa1 t3 t') as e' by (rw <- i0; auto).
    exists e'.
    generalize (i1 t3 t' e' e); intro l.
    rw l; sp.

    split; sp.

    assert (eqa t3 t') as e' by (rw j0; auto).
    exists e'.
    generalize (j1 t3 t' e' e); intro l.
    rw l; sp.

    assert (eqa0 t3 t') as e' by (rw <- j0; auto).
    exists e'.
    generalize (j1 t3 t' e e'); intro l.
    rw <- l; sp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
