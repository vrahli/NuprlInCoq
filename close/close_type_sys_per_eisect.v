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


Require Export type_sys_useful.
Require Export etype_family.
Require Import dest_close.




Lemma close_type_system_isect :
  forall (ts : candidate-type-system)
         T T'
         (eq : per)
         A A' v v' B B' eqa eqa' eqb
         f f' g g',
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc T (mkc_eisect A v B)
    -> computes_to_valc T' (mkc_eisect A' v' B')
    -> close ts A A eqa
    -> close ts A' A' eqa'
    -> (forall (a : CTerm) (e : eqa a a),
          close ts (substc a v B) (substc (f a e) v' B') (eqb a (f a e) e (g a e)))
    -> (forall (a : CTerm) (e : eqa a a),
          type_system ts
          -> defines_only_universes ts
          -> type_sys_props (close ts) (substc a v B) (substc (f a e) v' B')
                            (eqb a (f a e) e (g a e)))
    -> (forall (a' : CTerm) (e' : eqa' a' a'),
          close ts (substc (f' a' e') v B) (substc a' v' B') (eqb (f' a' e') a' (g' a' e') e'))
    -> (forall (a' : CTerm) (e' : eqa' a' a'),
          type_system ts
          -> defines_only_universes ts
          -> type_sys_props (close ts) (substc (f' a' e') v B) (substc a' v' B')
                            (eqb (f' a' e') a' (g' a' e') e'))
    -> (eq <=2=> (eisect_eq eqa eqa' eqb))
    -> per_eisect (close ts) T T' eq
    -> type_sys_props (close ts) A A eqa
    -> type_sys_props (close ts) A' A' eqa'
    -> type_sys_props (close ts) T T' eq.
Proof.
  introv tysys dou c1 c2 cla cla' clb tspb clb' tspb'.
  introv eqiff perTT' IHa IHa'.

  rw type_sys_props_iff_type_sys_props2.
  prove_type_sys_props2 SCase; intros.

  + SCase "uniquely_valued".
    dclose cl cl; dclose_lr.

    * SSCase "CL_isect".
      allunfold per_eisect; exrepd.
      apply eq_term_equals_trans with (eq2 := eisect_eq eqa0 eqa'0 eqb0);
        try (complete (apply eq_term_equals_sym; auto)).
      apply eq_term_equals_trans with (eq2 := eisect_eq eqa eqa' eqb); auto.

XXXXXXXXXX

      generalize (eq_term_equals_type_family T T3 eqa0 eqa eqb0 eqb (close ts) A v B A' v' B' mkc_isect); intro i.
      repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))); repnd.

      unfold eq_term_equals; sp.
      rw t0; rw eqiff; split; sp.

      duplicate e as e'; rw <- i0 in e.
      generalize (i1 a a' e' e); intro k.
      rw k; sp.

      duplicate e as e'; rw i0 in e.
      generalize (i1 a a' e e'); intro k.
      rw <- k; sp.

    * SSCase "CL_isect".
      allunfold per_isect; exrepd.
      generalize (eq_term_equals_type_family T' T3 eqa0 eqa eqb0 eqb (close ts) A' v' B' A v B mkc_isect); intro i.
      repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))); repnd.
      apply type_sys_props_sym; sp.
      onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
      intros.
      apply type_sys_props_sym.
      apply type_sys_props_eqb_comm; sp.
      apply tet with (t2 := a'); sp.
      apply tet with (t2 := a); sp.

      unfold eq_term_equals; sp.
      rw t0; rw eqiff; split; sp.

      duplicate e as e'; rw <- i0 in e.
      generalize (i1 a a' e' e); intro k.
      rw k; sp.

      duplicate e as e'; rw i0 in e.
      generalize (i1 a a' e e'); intro k.
      rw <- k; sp.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_isect;
    clear per;
    allunfold per_isect; exrepd;
    unfold per_isect;
    exists eqa0 eqb0; sp;
    allrw <-; sp.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_isect; unfold per_isect; exists eqa eqb; sp.

    duplicate c1 as ct.
    apply cequivc_mkc_isect with (T' := T3) in ct; sp.

    apply type_family_cequivc
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
    apply cequivc_mkc_isect with (T' := T3) in ct; sp.

    apply type_family_cequivc2
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
    onedtsp e p p0 p1 c t t0 t3 tygs tygt dum.
    apply eqiff; sp.
    assert (eqa a a) as eqaa by (apply t0 with (t2 := a'); auto).
    assert (eqa a' a) as e' by auto.
    assert (eq t1 t2) as eq12 by auto.
    apply eqiff with (a := a') (a' := a) (e := e') in eq12; auto.

    generalize (eq_term_equals_sym_tsp (close ts) eqa eqb a a' eqaa e0 e'
                                       v B v' B'); intro i.
    autodimp i h; repnd.

    (* Now we prove the equality between the applies *)
    unfold eq_term_equals in i.
    apply i in eq12.
    generalize (recb a a' e0); sp.
    onedtsp X5 X6 X7 X8 X9 X10 X11 X4 tygs1 tygt1 dum1; sp.

  + SCase "term_transitive".
    unfold term_equality_transitive; sp.
    apply eqiff; sp.
    assert (eq t1 t2) as eq12 by auto.
    assert (eq t2 t3) as eq23 by auto.
    apply eqiff with (a := a) (a' := a') (e := e) in eq12; auto.
    apply eqiff with (a := a) (a' := a') (e := e) in eq23; auto.

    onedtsp IHX0 IHX2 IHX3 IHX4 IHX5 IHX6 IHX7 IHX8 tygs tygt dum.

    generalize (recb a a' e); intro tsp.
    unfold type_sys_props in tsp; sp.
    apply tsp6 with (t2 := t2); auto.

  + SCase "term_value_respecting".
    unfold term_equality_respecting; sp.
    apply eqiff; sp.
    assert (eq t t) as eqtt by auto.
    apply eqiff with (a := a) (a' := a') (e := e) in eqtt; auto.

    generalize (recb a a' e); sp.
    onedtsp X5 X6 X7 X8 X9 X10 X11 X4 tygs1 tygt1 dum1; sp.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr;
    apply CL_isect;
    clear per;
    allunfold per_isect; exrepd.

    (* 1 *)
    generalize (eq_term_equals_type_family
                  T T3 eqa0 eqa eqb0 eqb (close ts)
                  A v B A' v' B' mkc_isect); intro i.
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    unfold per_isect.
    exists eqa eqb; sp.

    rw t0; split; intro k; sp.

    duplicate e as e'.
    rw i0 in e.
    generalize (k a a' e); intro j.
    generalize (i1 a a' e e'); intro eqt.
    rw eqt in j; sp.

    duplicate e as e'.
    rw <- i0 in e.
    generalize (k a a' e); intro j.
    generalize (i1 a a' e' e); intro eqt.
    rw <- eqt in j; sp.

    (* 2 *)
    generalize (eq_term_equals_type_family2
                  T3 T eqa0 eqa eqb0 eqb (close ts)
                  A v B A' v' B' mkc_isect); intro i;
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp)));
    repnd.

    unfold per_isect.
    exists eqa eqb; sp.

    rw t0; split; intro k; sp.

    duplicate e as e'.
    rw i0 in e.
    generalize (k a a' e); intro j.
    generalize (i1 a a' e e'); intro eqt.
    rw eqt in j; sp.

    duplicate e as e'.
    rw <- i0 in e.
    generalize (k a a' e); intro j.
    generalize (i1 a a' e' e); intro eqt.
    rw <- eqt in j; sp.

    (* 3 *)
    generalize (eq_term_equals_type_family
                  T' T3 eqa0 eqa eqb0 eqb (close ts)
                  A' v' B' A v B mkc_isect); intro i.
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

    unfold per_isect.
    exists eqa eqb; sp.

    rw t0; split; intro k; sp.

    duplicate e as e'.
    rw i0 in e.
    generalize (k a a' e); intro j.
    generalize (i1 a a' e e'); intro eqt.
    rw eqt in j; sp.

    duplicate e as e'.
    rw <- i0 in e.
    generalize (k a a' e); intro j.
    generalize (i1 a a' e' e); intro eqt.
    rw <- eqt in j; sp.

    (* 4 *)
    generalize (eq_term_equals_type_family2
                  T3 T' eqa0 eqa eqb0 eqb (close ts)
                  A' v' B' A v B mkc_isect); intro i;
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

    unfold per_isect.
    exists eqa eqb; sp.

    rw t0; split; intro k; sp.

    duplicate e as e'.
    rw i0 in e.
    generalize (k a a' e); intro j.
    generalize (i1 a a' e e'); intro eqt.
    rw eqt in j; sp.

    duplicate e as e'.
    rw <- i0 in e.
    generalize (k a a' e); intro j.
    generalize (i1 a a' e' e); intro eqt.
    rw <- eqt in j; sp.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_isect (close ts) T T4 eq2));
    try (move_term_to_top (per_isect (close ts) T' T4 eq2)).

    (* 1 *)
    clear per.
    allunfold per_isect; exrepd.

    generalize (eq_term_equals_type_family2
                  T3 T eqa1 eqa eqb1 eqb (close ts)
                  A v B A' v' B' mkc_isect); intro i.
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    generalize (type_family_trans2
                  mkc_isect (close ts) T3 T T4 eqa eqb eqa0 eqb0 A v B A' v' B'); intro j.
    repeat (autodimp j hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    dands; apply CL_isect; unfold per_isect; exists eqa eqb; sp; allrw.

    split; intro p; sp.

    assert (eqa1 a a') as e' by (rw <- i0; auto).
    generalize (p a a' e'); intro k.
    generalize (i1 a a' e' e); intro l.
    rw <- l; sp.

    assert (eqa a a') as e' by (rw i0; auto).
    generalize (p a a' e'); intro k.
    generalize (i1 a a' e e'); intro l.
    rw l; sp.

    split; intro p; sp.

    assert (eqa0 a a') as e' by (rw <- j0; auto).
    generalize (p a a' e'); intro k.
    generalize (j1 a a' e e'); intro l.
    rw l; sp.

    assert (eqa a a') as e' by (rw j0; auto).
    generalize (p a a' e'); intro k.
    generalize (j1 a a' e' e); intro l.
    rw <- l; sp.

    split; intro p; sp.

    assert (eqa1 a a') as e' by (rw <- i0; auto).
    generalize (p a a' e'); intro k.
    generalize (i1 a a' e' e); intro l.
    rw <- l; sp.

    assert (eqa a a') as e' by (rw i0; auto).
    generalize (p a a' e'); intro k.
    generalize (i1 a a' e e'); intro l.
    rw l; sp.

    (* 2 *)
    clear per.
    allunfold per_isect; exrepd.

    generalize (eq_term_equals_type_family2
                  T3 T' eqa1 eqa eqb1 eqb (close ts)
                  A' v' B' A v B mkc_isect); intro i.
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
                  mkc_isect (close ts) T3 T' T4 eqa eqb eqa0 eqb0 A' v' B' A v B); intro j.
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

    dands; apply CL_isect; unfold per_isect; exists eqa eqb; sp; allrw.

    split; intro p; sp.

    assert (eqa1 a a') as e' by (rw <- i0; auto).
    generalize (p a a' e'); intro k.
    generalize (i1 a a' e' e); intro l.
    rw <- l; sp.

    assert (eqa a a') as e' by (rw i0; auto).
    generalize (p a a' e'); intro k.
    generalize (i1 a a' e e'); intro l.
    rw l; sp.

    split; intro p; sp.

    assert (eqa0 a a') as e' by (rw <- j0; auto).
    generalize (p a a' e'); intro k.
    generalize (j1 a a' e e'); intro l.
    rw l; sp.

    assert (eqa a a') as e' by (rw j0; auto).
    generalize (p a a' e'); intro k.
    generalize (j1 a a' e' e); intro l.
    rw <- l; sp.

    split; intro p; sp.

    assert (eqa1 a a') as e' by (rw <- i0; auto).
    generalize (p a a' e'); intro k.
    generalize (i1 a a' e' e); intro l.
    rw <- l; sp.

    assert (eqa a a') as e' by (rw i0; auto).
    generalize (p a a' e'); intro k.
    generalize (i1 a a' e e'); intro l.
    rw l; sp.
Qed.
