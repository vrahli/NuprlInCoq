(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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
Require Import dest_close.


Lemma close_type_system_func {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A A' v v' B B' eqa eqb,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> in_ext lib (fun lib => T ===>(lib) (mkc_function A v B))
    -> in_ext lib (fun lib => T' ===>(lib) (mkc_function A' v' B'))
    -> in_ext lib (fun lib => close ts lib A A' (eqa lib))
    -> in_ext lib (fun lib => type_sys_props (close ts) lib A A' (eqa lib))
    -> in_ext
         lib
         (fun lib =>
            forall (a a' : CTerm) (e : eqa lib a a'),
              close ts lib (substc a v B) (substc a' v' B') (eqb lib a a' e))
    -> in_ext
         lib
         (fun lib =>
            forall (a a' : CTerm) (e : eqa lib a a'),
              type_sys_props (close ts) lib (substc a v B) (substc a' v' B')
                             (eqb lib a a' e))
    -> (eq <=2=> (per_func_eq eqa eqb lib))
    -> per_func_ext (close ts) lib T T' eq
    -> type_sys_props (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp1 comp2 cla tysysa clb tysysb eqiff; introv perfunc.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    SSCase "CL_func".
    allunfold @per_func_ext; exrepd.
    generalize (eq_term_equals_type_family lib T T3 eqa0 eqa eqb0 eqb (close lib ts) A v B A' v' B' mkc_function); intro i.
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))); repnd.

    unfold eq_term_equals; sp.
    rw t0; rw eqiff; split; sp.

    duplicate e as e'; rw <- i0 in e.
    generalize (i1 a a' e' e); intro k.
    rw k; sp.

    duplicate e as e'; rw i0 in e.
    generalize (i1 a a' e e'); intro k.
    rw <- k; sp.

  + SCase "type_symmetric"; repdors; subst;
    dclose_lr;
    apply CL_func;
    clear per;
    allunfold @per_func; exrepd;
    unfold per_func;
    exists eqa0 eqb0; sp;
    allrw <-; sp.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_func; unfold per_func; exists eqa eqb; sp.

    duplicate c1 as ct.
    apply @cequivc_mkc_function with (T' := T3) in ct; sp.

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
    apply @cequivc_mkc_function with (T' := T3) in ct; sp.

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
    assert (eqa a a) as eqaa by (apply t0 with (t2 := a'); auto).
    assert (eqa a' a) as e' by auto.
    assert (eq t1 t2) as eq12 by auto.
    apply eqiff with (a := a') (a' := a) (e := e') in eq12; auto.

    generalize (eq_term_equals_sym_tsp lib (close lib ts) eqa eqb a a' eqaa e0 e'
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
    assert (eq t1 t2) as eqt12 by auto.
    assert (eq t2 t3) as eqt23 by auto.
    assert (eq t1 t2) as eq12 by auto.
    assert (eq t2 t3) as eq23 by auto.
    apply eqiff with (a := a) (a' := a') (e := e) in eqt12; auto.
    apply eqiff with (a := a) (a' := a') (e := e) in eqt23; auto.

    assert (eqb a a' e (mkc_apply t2 a') (mkc_apply t2 a));
      try (complete (generalize (recb a a' e); sp;
                     onedtsp X6 X7 X8 X9 X10 X11 X12 X5 tygs1 tygt1 dum1; sp;
                     apply X12 with (mkc_apply t2 a'); auto;
                     apply X12 with (mkc_apply t2 a); auto)).

    assert (eq t2 t2) as eqt2;
      try (complete (apply eqiff with (a := a) (a' := a') (e := e) in eqt2; auto;
                     generalize (recb a a' e); sp;
                     allunfold @type_sys_props; sp)).

    apply eqiff; sp.
    duplicate eq23 as eq2.
    apply eqiff with (a := a0) (a' := a'0) (e := e0) in eq23; auto.
    assert (eqa a'0 a'0) as eqa'
           by (unfold type_sys_props in IHX1; sp; apply IHX7 with (t2 := a0); sp).
    apply eqiff with (a := a'0) (a' := a'0) (e := eqa') in eq2; auto.

    assert (eq_term_equals (eqb a0 a'0 e0) (eqb a'0 a'0 eqa')) as eqteq;
      try (complete (unfold eq_term_equals in eqteq;
                     apply eqteq in eq2;
                     generalize (recb a0 a'0 e0); sp;
                     onedtsp X6 X7 X8 X9 X10 X11 X12 X5 tygs1 tygt1 dum1; sp;
                     apply X12 with (t2 := mkc_apply t3 a'0); sp)).

    allunfold @per_func; exrepd.
    generalize (eq_term_equals_type_family
                  lib T T' eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_function); intro i.
    repeat (autodimp i hyp; try (complete (introv f; eqconstr f; sp))).
    repnd.
    apply eq_term_equals_sym; sp.

  + SCase "term_value_respecting".
    unfold term_equality_respecting; sp.
    apply eqiff; sp.
    assert (eq t t) as eqtt by auto.
    apply eqiff with (a := a) (a' := a') (e := e) in eqtt; auto.

    generalize (recb a a' e); sp.
    onedtsp X5 X6 X7 X8 X9 X10 X11 X4 tygs1 tygt1 dum1; sp.
    apply X11 with (t2 := mkc_apply t a'); auto.
    apply X4.
    apply term_equality_refl with (t2 := mkc_apply t a); auto.

    spcast; apply sp_implies_cequivc_apply; sp.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr;
    apply CL_func;
    clear per;
    allunfold @per_func; exrepd.

    (* 1 *)
    generalize (eq_term_equals_type_family
                  lib T T3 eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_function); intro i.
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    unfold per_func.
    exists eqa eqb; sp.

    rw t0; split; intro pp; sp.

    duplicate e as e'.
    rw i0 in e.
    generalize (pp a a' e); intro j.
    generalize (i1 a a' e e'); intro eqt.
    rw eqt in j; sp.

    duplicate e as e'.
    rw <- i0 in e.
    generalize (pp a a' e); intro j.
    generalize (i1 a a' e' e); intro eqt.
    rw <- eqt in j; sp.

    (* 2 *)
    generalize (eq_term_equals_type_family2
                  lib T3 T eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_function); intro i;
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp)));
    repnd.

    unfold per_func.
    exists eqa eqb; sp.

    rw t0; split; intro pp; sp.

    duplicate e as e'.
    rw i0 in e.
    generalize (pp a a' e); intro j.
    generalize (i1 a a' e e'); intro eqt.
    rw eqt in j; sp.

    duplicate e as e'.
    rw <- i0 in e.
    generalize (pp a a' e); intro j.
    generalize (i1 a a' e' e); intro eqt.
    rw <- eqt in j; sp.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_func lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_func lib (close lib ts) T' T4 eq2)).

    (* 1 *)
    clear per.
    allunfold @per_func; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T eqa1 eqa eqb1 eqb (close lib ts)
                  A v B A' v' B' mkc_function); intro i.
    repeat (autodimp i hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    generalize (type_family_trans2
                  lib mkc_function (close lib ts) T3 T T4 eqa eqb eqa0 eqb0 A v B A' v' B');
      intro j.
    repeat (autodimp j hyp; try (complete (introv e; eqconstr e; sp))).
    repnd.

    dands; apply CL_func; unfold per_func; exists eqa eqb; sp; allrw.

    split; intro pp; sp.

    assert (eqa1 a a') as e' by (rw <- i0; auto).
    generalize (pp a a' e'); intro k.
    generalize (i1 a a' e' e); intro l.
    rw <- l; sp.

    assert (eqa a a') as e' by (rw i0; auto).
    generalize (pp a a' e'); intro k.
    generalize (i1 a a' e e'); intro l.
    rw l; sp.

    split; intro pp; sp.

    assert (eqa0 a a') as e' by (rw <- j0; auto).
    generalize (pp a a' e'); intro k.
    generalize (j1 a a' e e'); intro l.
    rw l; sp.

    assert (eqa a a') as e' by (rw j0; auto).
    generalize (pp a a' e'); intro k.
    generalize (j1 a a' e' e); intro l.
    rw <- l; sp.

    (* 2 *)
    clear per.
    allunfold @per_func; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T' eqa1 eqa eqb1 eqb (close lib ts)
                  A' v' B' A v B mkc_function); intro i.
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
                  lib mkc_function (close lib ts) T3 T' T4 eqa eqb eqa0 eqb0 A' v' B' A v B); intro j.
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

    dands; apply CL_func; unfold per_func; exists eqa eqb; sp; allrw.

    split; intro pp; sp.

    assert (eqa1 a a') as e' by (rw <- i0; auto).
    generalize (pp a a' e'); intro k.
    generalize (i1 a a' e' e); intro l.
    rw <- l; sp.

    assert (eqa a a') as e' by (rw i0; auto).
    generalize (pp a a' e'); intro k.
    generalize (i1 a a' e e'); intro l.
    rw l; sp.

    split; intro pp; sp.

    assert (eqa0 a a') as e' by (rw <- j0; auto).
    generalize (pp a a' e'); intro k.
    generalize (j1 a a' e e'); intro l.
    rw l; sp.

    assert (eqa a a') as e' by (rw j0; auto).
    generalize (pp a a' e'); intro k.
    generalize (j1 a a' e' e); intro l.
    rw <- l; sp.
Qed.

