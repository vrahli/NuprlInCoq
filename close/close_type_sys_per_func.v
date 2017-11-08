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
Require Export per_ceq_bar.


Lemma eq_term_equals_per_func_ext_eq {o} :
  forall lib (eqa1 eqa2 : lib-per(o)) eqb1 eqb2,
    in_ext lib (fun lib => (eqa1 lib) <=2=> (eqa2 lib))
    -> in_ext lib (fun lib => forall a1 a2 (e1 : eqa1 lib a1 a2) (e2 : eqa2 lib a1 a2), (eqb1 lib a1 a2 e1) <=2=> (eqb2 lib a1 a2 e2))
    -> (per_func_ext_eq eqa1 eqb1 lib) <=2=> (per_func_ext_eq eqa2 eqb2 lib).
Proof.
  introv eqas eqbs; introv.
  unfold per_func_ext_eq.
  split; introv h ext; introv.

  - pose proof (h lib' ext) as h; simpl in h.
    pose proof (eqas lib' ext) as eqas.
    pose proof (eqbs lib' ext) as eqbs.
    simpl in *.
    dup e as e'.
    apply eqas in e'.
    apply (eqbs _ _ e'); tcsp.

  - pose proof (h lib' ext) as h; simpl in h.
    pose proof (eqas lib' ext) as eqas.
    pose proof (eqbs lib' ext) as eqbs.
    simpl in *.
    dup e as e'.
    apply eqas in e'.
    apply (eqbs _ _ _ e'); tcsp.
Qed.

Lemma type_family_ext_function_implies_in_ext_eqas {o} :
  forall ts lib (T T' : @CTerm o) A A' v B eqa1 eqa2 eqb2,
    in_ext lib (fun lib => type_sys_props4 ts lib A A' (eqa1 lib))
    -> type_family_ext mkc_function ts lib T T' eqa2 eqb2
    -> computes_to_valc lib T (mkc_function A v B)
    -> in_ext lib (fun lib => (eqa1 lib) <=2=> (eqa2 lib)).
Proof.
  introv tsp tf comp ext.
  pose proof (tsp lib' ext) as tsp; simpl in tsp.
  unfold type_family_ext in tf; exrepnd; spcast.
  computes_to_eqval.
  pose proof (tf3 lib' ext) as tf3; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply uv in tf3; auto.
Qed.
Hint Resolve type_family_ext_function_implies_in_ext_eqas : slow.

Lemma type_family_ext_function_implies_in_ext_eqbs {o} :
  forall ts lib (T T' : @CTerm o) A1 A2 v1 v2 B1 B2 eqa1 eqa2 eqb1 eqb2,
    in_ext lib (fun lib => type_sys_props4 ts lib A1 A2 (eqa1 lib))
    -> type_family_ext mkc_function ts lib T T' eqa2 eqb2
    -> computes_to_valc lib T (mkc_function A1 v1 B1)
    -> in_ext lib
              (fun lib =>
                 forall a a' (e : eqa1 lib a a'),
                   type_sys_props4 ts lib (B1)[[v1\\a]] (B2)[[v2\\a']] (eqb1 lib a a' e))
    -> in_ext lib
              (fun lib =>
                 forall a1 a2 (e1 : eqa1 lib a1 a2) (e2 : eqa2 lib a1 a2),
                   (eqb1 lib a1 a2 e1) <=2=> (eqb2 lib a1 a2 e2)).
Proof.
  introv tspa tf comp tspb ext; repeat introv.
  pose proof (type_family_ext_function_implies_in_ext_eqas ts lib T T' A1 A2 v1 B1 eqa1 eqa2 eqb2) as eqas.
  repeat (autodimp eqas hyp);[].
  pose proof (tspa lib' ext) as tspa; simpl in *.
  pose proof (tspb lib' ext) as tspb; simpl in *.
  pose proof (eqas lib' ext) as eqas; simpl in *.
  unfold type_family_ext in tf; exrepnd; spcast.
  computes_to_eqval.
  pose proof (tf3 lib' ext) as tf3; simpl in *.
  pose proof (tf1 lib' ext) as tf1; simpl in *.

  clear tspa.
  pose proof (tspb a1 a2 e1) as tsp; clear tspb.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  pose proof (tf1 a1 a2 e2) as q.
  apply uv in q; auto.
Qed.
Hint Resolve type_family_ext_function_implies_in_ext_eqbs : slow.

Lemma ccequivc_ext_function {o} :
  forall lib (T T' : @CTerm o) A v B,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_function A v B)
    -> {A' : CTerm , {v' : NVar , { B' : CVTerm [v'] ,
        ccomputes_to_valc lib T' (mkc_function A' v' B')
        # ccequivc_ext lib A A'
        # bcequivc_ext lib [v] B [v'] B' }}}.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_mkc_function in ceq';[|eauto]; exrepnd.
  exists A' v' B'; dands; spcast; auto.

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_function A v B) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_function A' v' B') ceq'1) as z.
    eapply cequivc_mkc_function in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_function A v B) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_function A' v' B') ceq'1) as z.
    eapply cequivc_mkc_function in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }
Qed.

Lemma lib_extends_preserves_ccequivc_ext {o} :
  forall lib lib' (A B : @CTerm o),
    lib_extends lib' lib
    -> ccequivc_ext lib A B
    -> ccequivc_ext lib' A B.
Proof.
  introv ext ceq e.
  apply ceq; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_ccequivc_ext : slow.

Lemma bcequivc_ext_implies_ccequivc_ext {o} :
  forall lib v v' (B : @CVTerm o [v]) (B' : @CVTerm o [v']) a,
    bcequivc_ext lib [v] B [v'] B'
    -> ccequivc_ext lib (B)[[v\\a]] (B')[[v'\\a]].
Proof.
  introv beq ext.
  pose proof (beq lib' ext) as beq; simpl in *.
  spcast.
  apply bcequivc1; auto.
Qed.

Lemma type_sys_props4_implies_type_sys_props {p} :
  forall (ts : cts(p)) lib T1 T2 e,
    type_sys_props4 ts lib T1 T2 e
    -> type_sys_props ts lib T1 T2 e.
Proof.
  introv tsp.
  apply type_sys_prop4_implies_type_sys_props3 in tsp.
  apply type_sys_props_iff_type_sys_props3; auto.
Qed.
Hint Resolve type_sys_props4_implies_type_sys_props : slow.

Lemma type_family_ext_cequivc {o} :
  forall C ts lib (T1 T2 : @CTerm o) eqa eqb A1 v1 B1 A2 v2 B2 A v B,
    computes_to_valc lib T1 (C A1 v1 B1)
    -> computes_to_valc lib T2 (C A2 v2 B2)
    -> ccequivc_ext lib A1 A2
    -> bcequivc_ext lib [v1] B1 [v2] B2
    -> in_ext lib (fun lib => type_sys_props4 ts lib A1 A (eqa lib))
    -> in_ext lib (fun lib =>
                     forall a1 a2 (e : eqa lib a1 a2),
                       type_sys_props4 ts lib
                                       (substc a1 v1 B1)
                                       (substc a2 v B)
                                       (eqb lib a1 a2 e))
    -> type_family_ext C ts lib T1 T2 eqa eqb.
Proof.
  introv co1 co2 ca cb tspa tspb.

  exists A1 A2 v1 v2 B1 B2; dands; spcast; auto.

  - introv ext.
    pose proof (tspa lib' ext) as tspa; simpl in *.

    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvr; eauto 3 with slow.

  - introv ext; introv.
    pose proof (tspa lib' ext) as tspa; simpl in *.
    pose proof (tspb lib' ext) as tspb; simpl in *.

    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

    assert (eqa lib' a' a') as e' by (apply tet with (t2 := a); sp).

    pose proof (tspb a' a' e') as i.

    onedtsp4 uv2 tys2 tyvr2 tyvrt2 tes2 tet2 tevr2 tygs2 tygt2 dum2.

    pose proof (tyvr2 (substc a' v1 B1) (substc a' v2 B2)) as k.
    repeat (autodimp k hyp).

    {
      apply (lib_extends_preserves_ccequivc_ext lib lib'); eauto 3 with slow.
      apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a'); auto.
    }

    pose proof (tspb a a' e) as i.
    pose proof (tspb a' a' e') as j.

    pose proof (type_sys_props_eq ts lib' (substc a v1 B1) (substc a' v1 B1) (substc a' v B) (eqb lib' a a' e) (eqb lib' a' a' e')) as l; repeat (autodimp l hyp); eauto 3 with slow;[].
    pose proof (type_sys_props_ts_trans3 ts lib' (substc a v1 B1) (substc a' v1 B1) (substc a' v2 B2) (substc a' v B) (eqb lib' a a' e) (eqb lib' a' a' e') (eqb lib' a' a' e')) as w; repeat (autodimp w hyp); eauto 3 with slow.
Qed.

Lemma type_sys_props4_sym {p} :
  forall (ts : cts(p)) lib A B eq,
    type_sys_props4 ts lib A B eq
    -> type_sys_props4 ts lib B A eq.
Proof.
  introv tsp.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  prove_type_sys_props4 Case; tcsp.

  - Case "uniquely_valued".
    introv tsts.
    pose proof (dum B A T3 eq eq') as q; repeat (autodimp q hyp); repnd.
    eapply uv; eauto.

  - Case "type_symmetric".
    introv tsts eqiff.
    pose proof (dum B A T3 eq eq) as q; repeat (autodimp q hyp); repnd.
    eapply tys in q;[|eauto].
    pose proof (dum A B T3 eq eq') as w; repeat (autodimp w hyp); repnd; auto.
    apply tygs; auto.

  - Case "type_value_respecting_trans".
    introv ee ceq tsts.
    repndors; subst; try (complete (eapply tyvrt; eauto)).

  - Case "type_gsymmetric".
    introv; split; intro tsts.

    { pose proof (dum B A T3 eq eq') as q; repeat (autodimp q hyp); repnd.
      pose proof (dum A T3 B eq' eq) as w; repeat (autodimp w hyp); repnd; auto;
        try (complete (apply tygs; auto)). }

    { pose proof (dum B T3 A eq' eq) as q; repeat (autodimp q hyp); repnd;
        try (complete (apply tygs; auto)).
      pose proof (dum A B T3 eq eq') as w; repeat (autodimp w hyp); repnd; auto;
        try (complete (apply tygs; auto)). }

  - Case "type_gtransitive".
    apply tygs; auto.

  - Case "type_mtransitive".
    introv ee ts1 ts2.
    repndors; subst; try (complete (eapply dum; eauto));
      try (complete (pose proof (dum A T3 T4 eq1 eq2) as q; tcsp)).
Qed.

Lemma in_ext_type_sys_props4_sym {p} :
  forall (ts : cts(p)) lib A B eq,
    in_ext lib (fun lib => type_sys_props4 ts lib A B (eq lib))
    -> in_ext lib (fun lib => type_sys_props4 ts lib B A (eq lib)).
Proof.
  introv tsp ext.
  pose proof (tsp lib' ext) as tcsp; apply type_sys_props4_sym; auto.
Qed.

Lemma type_sys_props4_eqb_comm {p} :
  forall (ts : cts(p)) lib eqa (eqb : per-fam(eqa))
         a1 a2
         (e : eqa a1 a2) (e1 : eqa a2 a1) (e2 : eqa a1 a1) (e3 : eqa a2 a2)
         v1 B1 v2 B2,
    (forall (a1 a2 : CTerm) (e : eqa a1 a2),
        type_sys_props4 ts lib (substc a1 v1 B1) (substc a2 v2 B2) (eqb a1 a2 e))
    -> type_sys_props4 ts lib (substc a2 v1 B1) (substc a1 v2 B2) (eqb a1 a2 e).
Proof.
  introv e1 e2 e3 ftspb.

  pose proof (eq_term_equals_sym_tsp
                ts lib eqa eqb a2 a1 e3 e1 e
                v1 B1 v2 B2) as i.
  repeat (autodimp i hyp); eauto 3 with slow.
  destruct i as [eqtb2 i].
  destruct i as [eqtb1 eqtb3].

  prove_type_sys_props4 Case; introv; tcsp.

  - Case "uniquely_valued".
    introv tsts.

    pose proof (ftspb a2 a1 e1) as i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    implies_ts_or_eq (substc a2 v1 B1) T3 (substc a1 v2 B2) h.
    apply uv2 in h.
    apply eq_term_equals_trans with (eq2 := eqb a2 a1 e1); sp.
    apply eq_term_equals_sym; sp.

  - Case "type_symmetric".
    introv tsa eqiff.

    generalize (ftspb a2 a1 e1); intro i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tyst2 T3 (eqb a1 a2 e)); intro i.
    dest_imp i h; repnd.
    generalize (tyt2 T3 (eqb a1 a2 e)); intro j.
    dest_imp j h; repnd.
    generalize (tys2 (substc a2 v1 B1) T3 eq'); intro k.
    repeat (dest_imp k h).
    apply eq_term_equals_trans with (eq2 := eqb a1 a2 e); sp.

  - Case "type_value_respecting".
    introv ee ceq.
    repdors; subst.

    {
      generalize (ftspb a2 a2 e3); intro i.
      apply type_sys_props4_implies_type_sys_props in i.
      onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
      generalize (tyvr2 (substc a2 v1 B1) T3); intro i.
      dest_imp i h.
      dest_imp i h.

      generalize (ftspb a1 a2 e); intro j.
      apply type_sys_props4_implies_type_sys_props in j.
      onedtsp uv3 tys3 tyt3 tyst3 tyvr3 tes3 tet3 tevr3 tygs3 tygt3 dum3.
      generalize (tygs3 (substc a1 v1 B1) (substc a2 v2 B2) (eqb a1 a2 e)); intro k.
      repeat (dest_imp k h); repnd.
      rw k in tygt3.
      rev_implies_ts_or (substc a2 v1 B1) tygt3.
      apply uv2 in tygt3.
      generalize (tys2 (substc a2 v1 B1) (substc a2 v2 B2) (eqb a1 a2 e)); intro l.
      dest_imp l h.
    }

    {
      generalize (ftspb a1 a1 e2); intro i.
      apply type_sys_props4_implies_type_sys_props in i.
      onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
      generalize (tyvr2 (substc a1 v2 B2) T3); intro i.
      dest_imp i h.
      dest_imp i h.

      generalize (ftspb a1 a2 e); intro j.
      apply type_sys_props4_implies_type_sys_props in j.
      onedtsp uv3 tys3 tyt3 tyst3 tyvr3 tes3 tet3 tevr3 tygs3 tygt3 dum3.
      implies_ts_or (substc a1 v2 B2) tygt3.
      apply uv2 in tygt3.
      generalize (tys2 (substc a1 v1 B1) T3 (eqb a1 a2 e)); intro l.
      dest_imp l h.
    }

  - Case "type_value_respecting_trans".
    introv ee ceq tsa.
    repdors; subst.

    {
      pose proof (ftspb a2 a2 e3) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tyvrt; eauto.
    }

    {
      pose proof (ftspb a1 a1 e2) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tyvrt; eauto.
    }

    {
      pose proof (ftspb a2 a2 e3) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tyvrt; eauto.
    }

    {
      pose proof (ftspb a1 a1 e2) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tyvrt; eauto.
    }

  - Case "term_symmetric".
    introv h.
    generalize (ftspb a1 a2 e); intro i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.

  - Case "term_transitive".
    introv h1 h2.
    generalize (ftspb a1 a2 e); intro i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.
    eapply tet2; eauto.

  - Case "term_value_respecting".
    introv h ceq.
    generalize (ftspb a1 a2 e); intro i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2; sp.

  - Case "type_gsymmetric".
    introv; split; intro h.

    {
      pose proof (ftspb a2 a1 e1) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tygs; auto.
    }

    {
      pose proof (ftspb a2 a1 e1) as i.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tygs; auto.
    }

  - Case "type_gtransitive".
    generalize (ftspb a2 a1 e1); intro i.
    apply type_sys_props4_implies_type_sys_props in i.
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
    generalize (tys2 (substc a2 v1 B1) (substc a1 v2 B2) (eqb a2 a1 e1)); sp.

  - Case "type_mtransitive".
    introv ee ts1 ts2.
    repdors; subst.

    {
      generalize (ftspb a2 a1 e1); intro i.
      apply type_sys_props4_implies_type_sys_props in i.
      onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2.
      generalize (tymt2 (substc a2 v1 B1) T3 T4 eq1 eq2); sp.
    }

    {
      generalize (ftspb a2 a1 e1); intro i.
      apply type_sys_props4_implies_type_sys_props in i.
      onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2.
      generalize (tymt2 (substc a1 v2 B2) T3 T4 eq1 eq2); sp.
    }
Qed.

Lemma type_family_ext_cequivc2 {p} :
  forall C (ts : cts(p)) lib T1 T2 eqa eqb A1 v1 B1 A2 v2 B2 A v B,
    computes_to_valc lib T1 (C A1 v1 B1)
    -> computes_to_valc lib T2 (C A2 v2 B2)
    -> ccequivc_ext lib A1 A2
    -> bcequivc_ext lib [v1] B1 [v2] B2
    -> in_ext lib (fun lib => type_sys_props4 ts lib A A1 (eqa lib))
    -> in_ext lib (fun lib =>
                     forall a1 a2 (e : eqa lib a1 a2),
                       type_sys_props4
                         ts lib
                         (substc a1 v B)
                         (substc a2 v1 B1)
                         (eqb lib a1 a2 e))
    -> type_family_ext C ts lib T1 T2 eqa eqb.
Proof.
  introv co1 co2 ca cb tspa tspb.

  apply @type_family_ext_cequivc
    with
      (A1 := A1)
      (v1 := v1)
      (B1 := B1)
      (A2 := A2)
      (v2 := v2)
      (B2 := B2)
      (A := A)
      (v := v)
      (B := B); sp;
    try (complete (apply (in_ext_type_sys_props4_sym ts lib); sp)).

  introv ext; introv.
  pose proof (tspa lib' ext) as tspa.
  pose proof (tspb lib' ext) as tspb.
  simpl in *.

  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

  assert (eqa lib' a2 a1) as e1 by sp.
  assert (eqa lib' a1 a1) as e2 by (apply tet with (t2 := a2); sp).
  assert (eqa lib' a2 a2) as e3 by (apply tet with (t2 := a1); sp).

  apply type_sys_props4_sym; sp.
  apply type_sys_props4_eqb_comm; sp.
Qed.

Lemma type_family_ext_value_respecting_trans1 {o} :
  forall ts lib (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    computes_to_valc lib T (mkc_function A v B)
    -> computes_to_valc lib T3 (mkc_function A1 v1 B1)
    -> ccequivc_ext lib A A1
    -> bcequivc_ext lib [v] B [v1] B1
    -> in_ext lib (fun lib => type_sys_props4 ts lib A A' (eqa lib))
    -> in_ext lib (fun lib =>
                     forall a a' (e : eqa lib a a'),
                       type_sys_props4 ts lib (B)[[v\\a]] (B')[[v'\\a']] (eqb lib a a' e))
    -> type_family_ext mkc_function ts lib T3 T4 eqa1 eqb1
    -> type_family_ext mkc_function ts lib T T4 eqa1 eqb1.
Proof.
  introv comp1 comp2 ceqa ceqb tspa tspb tf.

  unfold type_family_ext in *; exrepnd; spcast.
  computes_to_eqval.
  exists A A'0 v v'0 B B'0; dands; spcast; auto.

  - introv ext.
    pose proof (tf3 lib' ext) as tf3.
    pose proof (tf1 lib' ext) as tf1.
    pose proof (tspa lib' ext) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto; eauto 3 with slow.

  - introv ext; introv.
    pose proof (tf3 lib' ext) as tf3.
    pose proof (tf1 lib' ext) as tf1.
    pose proof (tspa lib' ext) as tspa.
    pose proof (tspb lib' ext) as tspb.
    simpl in *.

    pose proof (tf1 a a' e) as tf1.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in ceqb; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in ceqb; auto.

    assert ((eqa lib') <=2=> (eqa1 lib')) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      pose proof (tyvrt A A1 A'0 (eqa1 lib')) as q; repeat (autodimp q hyp); eauto 3 with slow.
    }

    dup e as e1.
    apply eqas in e1.
    pose proof (tspb a a' e1) as tspb.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto.
Qed.

Lemma type_family_ext_value_respecting_trans2 {o} :
  forall ts lib (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    computes_to_valc lib T (mkc_function A' v' B')
    -> computes_to_valc lib T3 (mkc_function A1 v1 B1)
    -> ccequivc_ext lib A' A1
    -> bcequivc_ext lib [v'] B' [v1] B1
    -> in_ext lib (fun lib => type_sys_props4 ts lib A A' (eqa lib))
    -> in_ext lib (fun lib =>
                     forall a a' (e : eqa lib a a'),
                       type_sys_props4 ts lib (B)[[v\\a]] (B')[[v'\\a']] (eqb lib a a' e))
    -> type_family_ext mkc_function ts lib T3 T4 eqa1 eqb1
    -> type_family_ext mkc_function ts lib T T4 eqa1 eqb1.
Proof.
  introv comp1 comp2 ceqa ceqb tspa tspb tf.

  unfold type_family_ext in *; exrepnd; spcast.
  computes_to_eqval.
  exists A' A'0 v' v'0 B' B'0; dands; spcast; auto.

  - introv ext.
    pose proof (tf3 lib' ext) as tf3.
    pose proof (tf1 lib' ext) as tf1.
    pose proof (tspa lib' ext) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto; eauto 3 with slow.

  - introv ext; introv.
    pose proof (tf3 lib' ext) as tf3.
    pose proof (tf1 lib' ext) as tf1.
    pose proof (tspa lib' ext) as tspa.
    pose proof (tspb lib' ext) as tspb.
    simpl in *.

    assert ((eqa lib') <=2=> (eqa1 lib')) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      pose proof (tyvrt A' A1 A'0 (eqa1 lib')) as q; repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (dum A' A A'0 (eqa lib') (eqa1 lib')) as w; repeat (autodimp w hyp); repnd.
      apply uv in w; auto.
    }

    assert (eqa1 lib' a a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tet;[|apply tes; apply eqas;exact e].
      apply eqas; auto.
    }

    pose proof (tf1 a a' e) as etf1.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in ceqb; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in ceqb; auto.

    dup e1 as e2.
    apply eqas in e2.
    pose proof (tspb a a e2) as etspb.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

    pose proof (tyvrt (B')[[v'\\a]] (B1)[[v1\\a]] (B'0)[[v'0\\a']] (eqb1 lib' a a' e)) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
Qed.

Lemma type_sys_props4_implies_eq_term_equals_sym {p} :
  forall (ts  : cts(p))
         (lib : library)
         (eqa : per)
         (eqb : per-fam(eqa))
         v1 B1 v2 B2,
    term_equality_transitive eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           type_sys_props4 ts lib
                           (substc a1 v1 B1)
                           (substc a2 v2 B2)
                           (eqb a1 a2 e))
    -> (forall a1 a2 (e1 : eqa a1 a2) (e : eqa a1 a1),
          eq_term_equals (eqb a1 a2 e1) (eqb a1 a1 e))
     # (forall a1 a2 (e2 : eqa a2 a1) (e : eqa a1 a1),
          eq_term_equals (eqb a2 a1 e2) (eqb a1 a1 e))
     # (forall a1 a2 (e1 : eqa a1 a2) (e2 : eqa a2 a1),
          eq_term_equals (eqb a1 a2 e1) (eqb a2 a1 e2)).
Proof.
  introv tet h.
  eapply eq_term_equals_sym_tsp2; auto.
  introv;apply type_sys_props4_implies_type_sys_props;eauto.
Qed.

Lemma type_sys_props4_implies_term_equality_transitive {o} :
  forall lib ts (A B : @CTerm o) eqa,
    type_sys_props4 ts lib A B eqa
    -> term_equality_transitive eqa.
Proof.
  introv h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve type_sys_props4_implies_term_equality_transitive : slow.

Lemma type_family_ext_value_respecting_trans3 {o} :
  forall ts lib (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    computes_to_valc lib T (mkc_function A v B)
    -> computes_to_valc lib T3 (mkc_function A1 v1 B1)
    -> ccequivc_ext lib A A1
    -> bcequivc_ext lib [v] B [v1] B1
    -> in_ext lib (fun lib => type_sys_props4 ts lib A A' (eqa lib))
    -> in_ext lib (fun lib =>
                     forall a a' (e : eqa lib a a'),
                       type_sys_props4 ts lib (B)[[v\\a]] (B')[[v'\\a']] (eqb lib a a' e))
    -> type_family_ext mkc_function ts lib T4 T3 eqa1 eqb1
    -> type_family_ext mkc_function ts lib T T4 eqa1 eqb1.
Proof.
  introv comp1 comp2 ceqa ceqb tspa tspb tf.

  unfold type_family_ext in *; exrepnd; spcast.
  computes_to_eqval.
  exists A A0 v v0 B B0; dands; spcast; auto.

  - introv ext.
    pose proof (tf3 lib' ext) as tf3.
    pose proof (tf1 lib' ext) as tf1.
    pose proof (tspa lib' ext) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto; eauto 3 with slow.

  - introv ext; introv.
    pose proof (tf3 lib' ext) as tf3.
    pose proof (tf1 lib' ext) as tf1.
    pose proof (tspa lib' ext) as tspa.
    pose proof (tspb lib' ext) as tspb.
    simpl in *.

    assert ((eqa lib') <=2=> (eqa1 lib')) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      pose proof (tyvrt A A1 A0 (eqa1 lib')) as q; repeat (autodimp q hyp); eauto 3 with slow.
    }

    assert (eqa1 lib' a' a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tes; apply eqas; auto.
    }

    assert (eqa1 lib' a' a') as x1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tet;[|apply eqas;eauto]; apply tes; apply eqas; auto.
    }

    pose proof (tf1 a' a e1) as atf1.
    dup ceqb as aceqb.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in aceqb; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in aceqb; auto.

    dup e as e2.
    apply eqas in e2.
    pose proof (tspb a a' e2) as atspb.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

    pose proof (tyvrt (B)[[v\\a]] (B1)[[v1\\a]] (B0)[[v0\\a']] (eqb1 lib' a' a e1)) as q.
    repeat (autodimp q hyp).

    applydup uv in q.
    apply tys.

    {
      pose proof (dum (B)[[v\\a]] (B')[[v'\\a']] (B0)[[v0\\a']] (eqb lib' a a' e2) (eqb1 lib' a' a e1)) as w.
      repeat (autodimp w hyp); try (complete (apply tygs; auto)); repnd; auto.
      pose proof (dum (B')[[v'\\a']] (B)[[v\\a]] (B0)[[v0\\a']] (eqb1 lib' a' a e1) (eqb lib' a a' e2)) as z.
      repeat (autodimp z hyp); try (complete (apply tygs; auto)); repnd; auto.
    }

    {
      dup x1 as x2.
      apply eqas in x2.
      pose proof (tspb a' a' x2) as btspb.

      assert ((eqb lib' a' a' x2) <=2=> (eqb1 lib' a a' e)) as eqbs1.
      {
        pose proof (tf1 a a' e) as btf1.
        dup ceqb as bceqb.
        apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a') in bceqb; auto.
        apply (lib_extends_preserves_ccequivc_ext lib lib') in bceqb; auto.

        onedtsp4 uv2 tys2 tyvr2 tyvrt2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
        pose proof (tyvrt2 (B)[[v\\a']] (B1)[[v1\\a']] (B0)[[v0\\a]] (eqb1 lib' a a' e)) as z.
        repeat (autodimp z hyp);[].
        apply uv2 in z; auto.
      }
      eapply eq_term_equals_trans;[|eauto];[].

      apply type_sys_props4_implies_eq_term_equals_sym in tspb; eauto 3 with slow;[].
      repnd; tcsp.
    }
Qed.

Lemma type_family_ext_value_respecting_trans4 {o} :
  forall ts lib (T T3 T4 : @CTerm o) A v B A' v' B' A1 v1 B1 eqa eqb eqa1 eqb1,
    computes_to_valc lib T (mkc_function A' v' B')
    -> computes_to_valc lib T3 (mkc_function A1 v1 B1)
    -> ccequivc_ext lib A' A1
    -> bcequivc_ext lib [v'] B' [v1] B1
    -> in_ext lib (fun lib => type_sys_props4 ts lib A A' (eqa lib))
    -> in_ext lib (fun lib =>
                     forall a a' (e : eqa lib a a'),
                       type_sys_props4 ts lib (B)[[v\\a]] (B')[[v'\\a']] (eqb lib a a' e))
    -> type_family_ext mkc_function ts lib T4 T3 eqa1 eqb1
    -> type_family_ext mkc_function ts lib T T4 eqa1 eqb1.
Proof.
  introv comp1 comp2 ceqa ceqb tspa tspb tf.

  unfold type_family_ext in *; exrepnd; spcast.
  computes_to_eqval.
  exists A' A0 v' v0 B' B0; dands; spcast; auto.

  - introv ext.
    pose proof (tf3 lib' ext) as tf3.
    pose proof (tf1 lib' ext) as tf1.
    pose proof (tspa lib' ext) as tspa.
    simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto; eauto 3 with slow.

  - introv ext; introv.
    pose proof (tf3 lib' ext) as tf3.
    pose proof (tf1 lib' ext) as tf1.
    pose proof (tspa lib' ext) as tspa.
    pose proof (tspb lib' ext) as tspb.
    simpl in *.

    assert ((eqa lib') <=2=> (eqa1 lib')) as eqas.
    {
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      pose proof (tyvrt A' A1 A0 (eqa1 lib')) as q; repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (dum A' A A0 (eqa lib') (eqa1 lib')) as w; repeat (autodimp w hyp); repnd.
      apply uv in w; auto.
    }

    assert (eqa1 lib' a a) as e1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tet;[apply eqas;exact e|].
      apply tes; apply eqas; auto.
    }

    assert (eqa1 lib' a' a) as e2.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      apply tes; apply eqas; auto.
    }

    assert (eqa1 lib' a' a') as x1.
    {
      apply eqas.
      onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
      eapply tet;[|apply eqas;exact e].
      apply tes; apply eqas; auto.
    }

    dup ceqb as aceqb.
    apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a) in aceqb; auto.
    apply (lib_extends_preserves_ccequivc_ext lib lib') in aceqb; auto.

    pose proof (tf1 a' a e2) as etf1.

    dup e1 as e3.
    apply eqas in e3.
    pose proof (tspb a a e3) as etspb.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.

    pose proof (tyvrt (B')[[v'\\a]] (B1)[[v1\\a]] (B0)[[v0\\a']] (eqb1 lib' a' a e2)) as q.
    repeat (autodimp q hyp); eauto 3 with slow.

    pose proof (dum (B)[[v\\a]] (B')[[v'\\a]] (B0)[[v0\\a']] (eqb lib' a a e3) (eqb1 lib' a a' e)) as w.
    repeat (autodimp w hyp); repnd; tcsp; try (complete (apply tygs; auto)).

    pose proof (dum (B')[[v'\\a]] (B)[[v\\a]] (B0)[[v0\\a']] (eqb lib' a a e3) (eqb1 lib' a' a e2)) as z.
    repeat (autodimp z hyp); repnd; tcsp; try (complete (apply tygs; auto)).

    applydup uv in z.
    apply tys.

    {
      pose proof (dum (B')[[v'\\a]] (B)[[v\\a]] (B0)[[v0\\a']] (eqb lib' a a e3) (eqb1 lib' a' a e2)) as w.
      repeat (autodimp w hyp); try (complete (apply tygs; auto)); repnd; auto.
    }

    {
      dup x1 as x2.
      apply eqas in x2.
      pose proof (tspb a' a' x2) as btspb.

      assert ((eqb lib' a' a' x2) <=2=> (eqb1 lib' a a' e)) as eqbs1.
      {
        pose proof (tf1 a a' e) as btf1.
        dup ceqb as bceqb.
        apply (bcequivc_ext_implies_ccequivc_ext _ _ _ _ _ a') in bceqb; auto.
        apply (lib_extends_preserves_ccequivc_ext lib lib') in bceqb; auto.

        onedtsp4 uv2 tys2 tyvr2 tyvrt2 tes2 tet2 tevr2 tygs2 tygt2 dum2.
        pose proof (tyvrt2 (B')[[v'\\a']] (B1)[[v1\\a']] (B0)[[v0\\a]] (eqb1 lib' a a' e)) as u.
        repeat (autodimp u hyp);[].
        pose proof (dum2 (B')[[v'\\a']] (B)[[v\\a']] (B0)[[v0\\a]] (eqb lib' a' a' x2) (eqb1 lib' a a' e)) as w.
        repeat (autodimp w hyp); try (complete (apply tygs; auto)); repnd; auto.

        apply uv2 in w; auto.
      }
      eapply eq_term_equals_trans;[|eauto];[].

      apply type_sys_props4_implies_eq_term_equals_sym in tspb; eauto 3 with slow;[].
      repnd; tcsp.
      dup e as x3.
      apply eqas in x3.
      pose proof (tspb0 a a' x3 e3) as p1.
      pose proof (tspb1 a' a x3 x2) as p2.
      eapply eq_term_equals_trans;[|exact p2].
      apply eq_term_equals_sym; auto.
    }
Qed.

Lemma type_sys_props4_implies_term_equality_symmetric {o} :
  forall lib (ts : cts(o)) A B eqa,
    type_sys_props4 ts lib A B eqa
    -> term_equality_symmetric eqa.
Proof.
  introv h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve type_sys_props4_implies_term_equality_symmetric : slow.

Lemma close_type_system_func {p} :
  forall lib (ts : cts(p))
         T T'
         (eq : per)
         A A' v v' B B' eqa eqb,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> computes_to_valc lib T (mkc_function A v B)
    -> computes_to_valc lib T' (mkc_function A' v' B')
    -> in_ext lib (fun lib => close ts lib A A' (eqa lib))
    -> in_ext lib (fun lib => type_sys_props4 (close ts) lib A A' (eqa lib))
    -> in_ext
         lib
         (fun lib =>
            forall (a a' : CTerm) (e : eqa lib a a'),
              close ts lib (substc a v B) (substc a' v' B') (eqb lib a a' e))
    -> in_ext
         lib
         (fun lib =>
            forall (a a' : CTerm) (e : eqa lib a a'),
              type_sys_props4 (close ts) lib (substc a v B) (substc a' v' B')
                              (eqb lib a a' e))
    -> (eq <=2=> (per_func_ext_eq eqa eqb lib))
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp1 comp2 cla tysysa clb tysysb eqiff.

  prove_type_sys_props4 SCase; introv.

  + SCase "uniquely_valued".
    introv cl.
    dclose_lr.
    clear cl.

    allunfold @per_func_ext; exrepnd.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
    apply eq_term_equals_per_func_ext_eq; eauto 3 with slow.

  + SCase "type_symmetric".
    introv cl eqs.
    dclose_lr.
    apply CL_func.

    allunfold @per_func_ext; exrepnd.
    exists eqa0 eqb0.
    dands; auto.
    eapply eq_term_equals_trans;[apply eq_term_equals_sym;eauto|];auto.

  + SCase "type_value_respecting".
    introv ee ceq; repndors; subst; apply CL_func;
      exists eqa eqb; dands; auto.

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      eapply type_family_ext_cequivc; eauto.
    }

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      eapply type_family_ext_cequivc2; eauto.
    }

  + SCase "type_value_respecting_trans".
    introv ee ceq cl.
    repndors; subst.

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_func.
      unfold per_func_ext in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans1; eauto.
    }

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_func.
      unfold per_func_ext in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans2; eauto.
    }

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_func.
      unfold per_func_ext in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans3; eauto.
    }

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_func.
      unfold per_func_ext in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans4; eauto.
    }

  + SCase "term_symmetric".
    introv ee.
    apply eqiff in ee; apply eqiff; clear eqiff.
    introv ext.
    pose proof (ee lib' ext) as ee; simpl in *; introv.

    assert (term_equality_symmetric (eqa lib')) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib')) as teet by (eauto 3 with slow).

    assert (eqa lib' a a) as e1 by (eauto).
    assert (eqa lib' a' a) as e2 by (eauto).

    pose proof (eq_term_equals_sym_tsp
                  (close ts) lib' (eqa lib') (eqb lib') a a' e1 e e2 v B v' B') as q.
    repeat (autodimp q hyp).
    { introv; apply type_sys_props4_implies_type_sys_props; tcsp. }
    repnd.

    pose proof (ee a' a e2) as ee'; apply q in ee'.

    pose proof (tysysb lib' ext a a' e) as x; simpl in x.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.

  + SCase "term_transitive".
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff; clear eqiff.

    introv ext; introv.
    pose proof (ee1 lib' ext) as ee1.
    pose proof (ee2 lib' ext) as ee2.
    simpl in *.

    assert (term_equality_symmetric (eqa lib')) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib')) as teet by (eauto 3 with slow).


XXXXXX
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
