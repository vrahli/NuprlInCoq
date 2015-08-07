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



Lemma meq_eq_term_equals {p} :
  forall lib (eqa1 eqa2 : per(p))
         eqb1 eqb2 t1 t2,
    (forall (a1 a2 : CTerm) (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
       eq_term_equals (eqb1 a1 a2 e1) (eqb2 a1 a2 e2))
    -> eq_term_equals eqa1 eqa2
    -> meq lib eqa1 eqb1 t1 t2
    -> meq lib eqa2 eqb2 t1 t2.
Proof.
  introv eqbeq eqaeq meqt.
  revert_dependents t2.
  revert t1.
  cofix MEQIH.
  introv meqt.
  destruct meqt.
  duplicate e as e'.
  rw eqaeq in e.
  apply @meq_cons with (a := a) (a' := a') (f := f) (f' := f') (e := e);
    try (complete sp).
  introv eb2.
  generalize (eqbeq a a' e' e); intro eqb.
  applydup eqb in eb2 as eb1.
  discover.
  auto.
Qed.

Lemma meq_sym {p} :
  forall lib eqa eqb t1 t2 v1 v2 B1 B2 ts,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall (a1 a2 : @CTerm p) (e : eqa a1 a2),
          type_sys_props lib ts
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> meq lib eqa eqb t1 t2
    -> meq lib eqa eqb t2 t1.
Proof.
  introv teqsa teqta ftsp meq1.
  revert_dependents t2.
  revert t1.
  cofix MEQIH.
  introv meq1.
  destruct meq1.
  duplicate e as e'.
  apply teqsa in e.
  apply @meq_cons with (a := a') (a' := a) (f := f') (f' := f) (e := e);
    try (complete sp).
  introv eb.
  generalize (eq_term_equals_sym_tsp2 lib ts eqa eqb v1 B1 v2 B2); introv i.
  autodimp i hyp; sp.
  generalize (i a a' e' e); intro eqeb.
  rw <- eqeb in eb.
  discover.
  auto.
Qed.

Lemma meq_trans {p} :
  forall lib eqa eqb t1 t2 t3 ts v1 B1 v2 B2,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall (a1 a2 : @CTerm p) (e : eqa a1 a2),
          type_sys_props lib ts
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> meq lib eqa eqb t1 t2
    -> meq lib eqa eqb t2 t3
    -> meq lib eqa eqb t1 t3.
Proof.
  introv teqsa teqta ftsp.
  revert t1 t2 t3.
  cofix MEQIH.
  introv meq1 meq2.
  destruct meq1.
  destruct meq2.
  ccomputes_to_eqval.
  assert (eqa a a'0) as e' by (apply teqta with (t2 := a'); sp).
  apply @meq_cons with (a := a) (f := f) (a' := a'0) (f' := f'0) (e := e');
    try (complete (spcast; sp)); introv eb.

  assert (eqa a a) as eqaaa by (apply teqta with (t2 := a'); sp).

  assert (eqb a a' e b b)
    as eb1
      by (generalize (eq_term_equals_sym_tsp2 lib ts eqa eqb v1 B1 v2 B2); intro i; sp;
          generalize (i0 a a'0 e' eqaaa); introv e1;
          generalize (i0 a a' e eqaaa); introv e2;
          rw e2; rw <- e1;
          generalize (ftsp a a'0 e'); intro tsp;
          onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1; sp;
          apply tet1 with (t2 := b'); sp).

  assert (eqa a'0 a'0) as eqaa'0a'0 by (apply teqta with (t2 := a'); sp).

  assert (eqb a' a'0 e0 b b')
    as eb2
      by (generalize (eq_term_equals_sym_tsp2 lib ts eqa eqb v1 B1 v2 B2); intro i; sp;
          generalize (i1 a'0 a' e0 eqaa'0a'0); introv e1; rw e1;
          generalize (i1 a'0 a e' eqaa'0a'0); introv e2; rw <- e2; auto).

  discover; auto.
  apply MEQIH with (t2 := mkc_apply f' b); auto.
Qed.

Lemma meq_cequivc {p} :
  forall lib eqa eqb t t1 t2 ts v1 B1 v2 B2,
    term_equality_respecting lib eqa
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall (a1 a2 : @CTerm p) (e : eqa a1 a2),
          type_sys_props lib ts
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> meq lib eqa eqb t t1
    -> cequivc lib t1 t2
    -> meq lib eqa eqb t t2.
Proof.
  introv tera tesa teta ftspb meq1.
  revert t2.
  revert meq1.
  revert t t1.
  cofix MEQIH.
  introv meq1 ceq.
  destruct meq1 as [ a f a1 f1 ea c1 c2 I ]; spcast.
  generalize (cequivc_mkc_sup lib t1 t2 a1 f1); intros i.
  repeat (autodimp i hyp); exrepnd.
  rename a' into a2.
  rename b' into f2.

  assert (eqa a a2)
    as ea2
      by (apply teta with (t2 := a1); sp;
          apply tera; sp; spcast; sp;
          apply teta with (t2 := a); sp).

  apply @meq_cons with (a := a) (f := f) (a' := a2) (f' := f2) (e := ea2);
    try (complete (spcast; sp)).
  introv eb.

  assert (eqa a a) as eqaaa by (apply teta with (t2 := a2); sp).

  assert (eqb a a1 ea b b')
    as eb'
      by (generalize (eq_term_equals_sym_tsp2 lib ts eqa eqb v1 B1 v2 B2); intro i; sp;
          generalize (i3 a a2 ea2 eqaaa); introv e1; rw e1 in eb;
          generalize (i3 a a1 ea eqaaa); introv e2; rw e2; auto).

  apply I in eb'.
  generalize (MEQIH (mkc_apply f b) (mkc_apply f1 b') eb' (mkc_apply f2 b'));
    intro h; autodimp h hyp.
  apply sp_implies_cequivc_apply; sp.
Qed.


Lemma close_type_system_m {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A A' v v' B B' eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_m A v B)
    -> computes_to_valc lib T' (mkc_m A' v' B')
    -> close lib ts A A' eqa
    -> (forall (a a' : CTerm) (e : eqa a a'),
          close lib ts (substc a v B) (substc a' v' B') (eqb a a' e))
    -> (forall (a a' : CTerm) (e : eqa a a'),
          type_system lib ts ->
          defines_only_universes lib ts ->
          type_sys_props lib (close lib ts) (substc a v B) (substc a' v' B')
                         (eqb a a' e))
    -> (forall t t' : CTerm, eq t t' <=> meq lib eqa eqb t t')
    -> per_m lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) A A' eqa
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 c1 c2 X1 clb recb eqiff per IHX1.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    SSCase "CL_m".
    allunfold @per_m; exrepd.
    generalize (eq_term_equals_type_family lib T T3 eqa0 eqa eqb0 eqb (close lib ts) A v B A' v' B' mkc_m); intro i.
    repeat (autodimp i hyp; try (complete (introv eqw; eqconstr eqw; sp))); repnd.

    unfold eq_term_equals; sp.
    rw e; rw eqiff; split; sp.

    apply @meq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    generalize (i1 a1 a2 e2 e1); sp; apply eq_term_equals_sym; sp.

    apply @meq_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_m;
    clear per;
    allunfold @per_m; exrepd;
    unfold per_m;
    exists eqa0 eqb0; sp;
    allrw <-; sp;
    apply eq_term_equals_trans with (eq2 := eq); sp;
    try (complete (apply eq_term_equals_sym; auto)).

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_m; unfold per_m; exists eqa eqb; sp.

    duplicate c1 as ct.
    apply @cequivc_mkc_m with (T' := T3) in ct; sp.

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
    apply @cequivc_mkc_m with (T' := T3) in ct; sp.

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
    apply eqiff in eq12.

    apply @meq_sym with (v1 := v) (v2 := v') (B1 := B) (B2 := B') (ts := close lib ts); sp.

  + SCase "term_transitive".
    unfold term_equality_transitive; sp.
    apply eqiff; sp.
    assert (eq t1 t2) as eq12 by auto.
    assert (eq t2 t3) as eq23 by auto.
    apply eqiff in eq12.
    apply eqiff in eq23.
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1; sp.
    apply @meq_trans with (t2 := t2) (ts := close lib ts) (v1 := v) (B1 := B) (v2 := v') (B2 := B'); sp.

  + SCase "term_value_respecting".
    unfold term_equality_respecting; sp.
    apply eqiff; sp.
    assert (eq t t) as eqtt by auto.
    apply eqiff in eqtt.
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.

    spcast; apply @meq_cequivc with (t1 := t) (ts := close lib ts) (v1 := v) (B1 := B) (v2 := v') (B2 := B'); sp.

  + SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_m;
    clear per;
    allunfold @per_m; exrepd.

    (* 1 *)
    generalize (eq_term_equals_type_family
                  lib T T3 eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_m); intro i.
    repeat (autodimp i hyp; try (complete (introv eqw; eqconstr eqw; sp))).
    repnd.

    unfold per_m.
    exists eqa eqb; sp.

    apply eq_term_equals_trans with (eq2 := meq lib eqa0 eqb0);
      try (complete sp); split; sp.

    apply meq_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.

    apply meq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.

    (* 2 *)
    generalize (eq_term_equals_type_family2
                  lib T3 T eqa0 eqa eqb0 eqb (close lib ts)
                  A v B A' v' B' mkc_m); intro i;
    repeat (autodimp i hyp; try (complete (introv eqw; eqconstr eqw; sp)));
    repnd.

    unfold per_m.
    exists eqa eqb; sp.

    apply eq_term_equals_trans with (eq2 := meq lib eqa0 eqb0);
      try (complete sp); split; sp.

    apply meq_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.

    apply meq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_m lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_m lib (close lib ts) T' T4 eq2)).

    (* 1 *)
    clear per.
    allunfold @per_m; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T eqa1 eqa eqb1 eqb (close lib ts)
                  A v B A' v' B' mkc_m); intro i.
    repeat (autodimp i hyp; try (complete (introv eqw; eqconstr eqw; sp))).
    repnd.

    generalize (type_family_trans2
                  lib mkc_m (close lib ts) T3 T T4 eqa eqb eqa0 eqb0 A v B A' v' B');
      intro j.
    repeat (autodimp j hyp; try (complete (introv eqw; eqconstr eqw; sp))).
    repnd.

    dands; apply CL_m; unfold per_m; exists eqa eqb; unfold eq_term_equals; sp; allrw.

    split; sp.

    apply @meq_eq_term_equals with (eqa1 := eqa1) (eqb1 := eqb1); sp.
    apply eq_term_equals_sym; sp.

    apply @meq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp; try (complete (allrw <-; sp)).

    split; sp.

    apply @meq_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_sym; sp.

    apply @meq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.

    (* 2 *)
    clear per.
    allunfold @per_m; exrepd.

    generalize (eq_term_equals_type_family2
                  lib T3 T' eqa1 eqa eqb1 eqb (close lib ts)
                  A' v' B' A v B mkc_m); intro i.
    repeat (autodimp i hyp;
            try (complete (introv eqw; eqconstr eqw; sp));
            try (complete (apply type_sys_props_sym; sp))).
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    intros.
    apply type_sys_props_sym.
    apply type_sys_props_eqb_comm; sp.
    apply tet with (t2 := a'); sp.
    apply tet with (t2 := a); sp.
    repnd.

    generalize (type_family_trans2
                  lib mkc_m (close lib ts) T3 T' T4 eqa eqb eqa0 eqb0 A' v' B' A v B); intro j.
    repeat (autodimp j hyp;
            try (complete (introv eqw; eqconstr eqw; sp));
            try (complete (apply type_sys_props_sym; sp))).
    onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
    intros.
    apply type_sys_props_sym.
    apply type_sys_props_eqb_comm; sp.
    apply tet with (t2 := a'); sp.
    apply tet with (t2 := a); sp.
    repnd.

    dands; apply CL_m; unfold per_m; exists eqa eqb; unfold eq_term_equals; sp; allrw.

    split; sp.

    apply @meq_eq_term_equals with (eqa1 := eqa1) (eqb1 := eqb1); sp.
    apply eq_term_equals_sym; sp.

    apply @meq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
    apply eq_term_equals_sym; sp.

    split; sp.

    apply @meq_eq_term_equals with (eqa1 := eqa0) (eqb1 := eqb0); sp.
    apply eq_term_equals_sym; sp.
    apply eq_term_equals_sym; sp.

    apply @meq_eq_term_equals with (eqa1 := eqa) (eqb1 := eqb); sp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
