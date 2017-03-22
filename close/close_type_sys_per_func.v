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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys_useful.
Require Import dest_close.


Lemma eq_term_equals_per_func_eq {o} :
  forall (eqa1 eqa2 : per(o)) eqb1 eqb2,
    term_equality_symmetric eqa1
    -> term_equality_transitive eqa1
    -> (eqa1 <=2=> eqa2)
    -> (forall a a' (e1 : eqa1 a a') (e2 : eqa2 a a'), (eqb1 a a' e1) <=2=> (eqb2 a a' e2))
    -> (per_func_eq eqa1 eqb1) <=2=> (per_func_eq eqa2 eqb2).
Proof.
  introv syma trana eaiff ebiff.
  unfold per_func_eq.
  split; introv h; introv.

  - appdup eaiff in e.
    apply (ebiff _ _ e0); auto.

  - appdup eaiff in e.
    apply (ebiff _ _ _ e0); auto.
Qed.

Lemma per_func_eq_sym {o} :
  forall lib ts v B (eqa : per(o)) eqb t1 t2,
    term_equality_symmetric eqa
    -> (forall a a' (e : eqa a a'), type_system_props lib ts (B)[[v \\ a]] (B)[[v \\ a']] (eqb a a' e))
    -> per_fam_equiv eqb
    -> per_func_eq eqa eqb t1 t2
    -> per_func_eq eqa eqb t2 t1.
Proof.
  introv syma tsb eqbiff per.
  unfold per_func_eq in *.
  introv.
  appdup syma in e.
  pose proof (per a' a e0) as e1.
  destruct eqbiff as [symb tranb].
  apply (symb _ _ e) in e1.

  pose proof (tsb a a' e) as q.
  dts_props q uv te tys tylt tyt tv tes tet tev.
  apply tes; auto.
Qed.

Lemma per_func_eq_trans {o} :
  forall lib ts v B (eqa : per(o)) eqb t1 t2 t3,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> per_fam_equiv eqb
    -> (forall a a' (e : eqa a a'), type_system_props lib ts (B)[[v \\ a]] (B)[[v \\ a']] (eqb a a' e))
    -> per_func_eq eqa eqb t1 t2
    -> per_func_eq eqa eqb t2 t3
    -> per_func_eq eqa eqb t1 t3.
Proof.
  introv syma trana pfb tsb per1 per2.
  unfold per_func_eq in *.
  introv.

  assert (eqa a a) as q.
  { eapply trana;[eauto|].
    apply syma; auto. }

  pose proof (per1 a a q) as h1.
  pose proof (per2 a a' e) as h2.

  apply (per_fam_equiv_refl_l eqb a a' e q) in h2; auto.
  apply (per_fam_equiv_refl_l eqb a a' e q); auto.

  pose proof (tsb a a q) as w.
  dts_props w uv te tys tylt tyt tv tes tet tev.
  eapply tet; eauto.
Qed.

Lemma per_func_eq_cequivc {o} :
  forall lib ts v B (eqa : per(o)) eqb t1 t2,
    (forall a a' (e : eqa a a'), type_system_props lib ts (B)[[v \\ a]] (B)[[v \\ a']] (eqb a a' e))
    -> cequivc lib t1 t2
    -> per_func_eq eqa eqb t1 t1
    -> per_func_eq eqa eqb t1 t2.
Proof.
  introv tsb ceq per.
  unfold per_func_eq in *.
  introv.

  pose proof (per a a' e) as q.
  pose proof (tsb a a' e) as w.
  dts_props w uv te tys tylt tyt tv tes tet tev.
  eapply tet;[eauto|].
  apply tev;[eapply tet;eauto|].
  spcast.
  apply implies_cequivc_apply; auto.
Qed.

Lemma close_type_system_func {o} :
  forall lib (ts : cts(o)) T T' (eq : per) A v B eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_function A v B)
    -> per_extensional lib (close lib ts) T T' eq
    -> per_extensional lib
                       (fun (T1 T2 : CTerm) (eq : per( o)) =>
                          type_system lib ts ->
                          defines_only_universes lib ts ->
                          type_system_props lib (close lib ts) T1 T2 eq)
                       T T' eq
    -> per_intensional lib mkc_function (close lib ts) T' A v B eqa eqb
    -> per_intensional lib mkc_function
                       (fun (T1 T2 : CTerm) (eq : per(o)) =>
                          type_system lib ts ->
                          defines_only_universes lib ts ->
                          type_system_props lib (close lib ts) T1 T2 eq)
                       T' A v B eqa eqb
    -> close lib ts A A eqa
    -> type_system_props lib (close lib ts) A A eqa
    -> (forall a a' (e : eqa a a'), close lib ts (substc a v B) (substc a' v B) (eqb a a' e))
    -> (forall a a' (e : eqa a a'),
           type_system_props lib (close lib ts) (substc a v B) (substc a' v B) (eqb a a' e))
    -> per_fam_equiv eqb
    -> eq <=2=> (per_func_eq eqa eqb)
    -> per_func lib (close lib ts) T T' eq
    -> type_system_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp ext extP int intP;
    introv cla tsa clb tsb eqbiff eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".

    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_func in h; exrepnd; spcast.
    unfold type_family in h0; exrepnd.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    dts_props tsa uv te tys tylt tyt tv tes tet tev.
    apply uv in h5.

    pose proof (eqbs_trans lib (close lib ts) v B eqa eqa0 eqb eqb0) as q.
    repeat (autodimp q hyp).

    apply eq_term_equals_per_func_eq; auto.

  - SCase "type_extensionality".

    introv eqt.
    apply CL_func.
    exists eqa eqb; dands; auto.

    {
      exists A v B; dands; spcast; auto;[|split;auto];[].

      unfold per_extensional; unfold per_extensional in extP; repndors; tcsp; right;[].
      repnd; dands; auto.
      repeat (autodimp extP0 hyp).
      dts_props extP0 uv te tys tyrr tyt tv tes tet tev.
      apply te; auto.
    }

    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_symmetric".

    unfold type_symmetric_body.

    clear ext.
    unfold per_extensional in extP.
    repndors; spcast.

    {
      apply CL_func.
      dup extP as ceq.
      eapply cequivc_mkc_function in extP;[|eauto]; exrepnd.
      exists eqa eqb; dands; spcast; auto.
      exists A' v' B'; dands; spcast; auto.

      - left; spcast; apply cequivc_sym; auto.

      - introv comp0; spcast; computes_to_eqval.
        dands; auto.
        { dts_props tsa uv te tys tyrr tyt tv tes tet tev.
          eapply tv; auto. }
        introv.
        pose proof (tsb a a' e) as h.
        dts_props h uv te tys tyrr tyt tv tes tet tev.
        eapply tv; auto; apply bcequivc1; auto.

      - dts_props tsa uv te tys tyrr tyt tv tes tet tev.
        eapply tv; auto.

      - unfold type_family_members_eq; dands; auto.
        introv.
        pose proof (tsb a a' e) as q.
        dts_props q uv te tys tyrr tyt tv tes tet tev.
        eapply tv; apply bcequivc1; auto.
    }

    {
      repnd.
      repeat (autodimp extP0 hyp).

Lemma equal_to_function {o} :
  forall lib ts (T1 T2 T : @CTerm o) A v B eq eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> not_uni lib T1
    -> computes_to_valc lib T (mkc_function A v B)
    -> close lib ts T1 T2 eq
    -> close lib ts A A eqa
    -> type_system_props lib (close lib ts) A A eqa
    -> type_family_members_eq (close lib ts) v B eqb
    -> per_intensional lib mkc_function (close lib ts) T1 A v B eqa eqb
    -> (eq <=2=> (per_func_eq eqa eqb))
    -> close lib ts T1 T eq.
Proof.
  introv tysys dou nuni comp cl cla tsa tfb intT eqiff.
  revert A v B eqa eqb T comp cla tsa tfb intT eqiff.
  close_cases (induction cl using @close_ind') Case; introv compT cla tsa tfb intT eiff.

  - Case "CL_init".
    apply CL_init.

    match goal with
    | [ H : ts _ _ _ |- _ ] => rename H into h
    end.
    apply dou in h; exrepnd.
    spcast.
    pose proof (nuni i) as q; destruct q; spcast; auto.

  - Case "CL_int".
    clear per.
    spcast.
    apply CL_int.
    unfold per_int; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_func; unfold per_func; exists eqa eqb; dands; auto.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_eqval; dands; auto; apply tfb. }

  - Case "CL_atom".
    clear per.
    spcast.
    apply CL_atom.
    unfold per_atom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_func; unfold per_func; exists eqa eqb; dands; auto.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_eqval; dands; auto; apply tfb. }

  - Case "CL_uatom".
    clear per.
    spcast.
    apply CL_uatom.
    unfold per_uatom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_func; unfold per_func; exists eqa eqb; dands; auto.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_eqval; dands; auto; apply tfb. }

  - Case "CL_base".
    clear per.
    spcast.
    apply CL_base.
    unfold per_base; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_func; unfold per_func; exists eqa eqb; dands; auto.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_eqval; dands; auto; apply tfb. }

  - Case "CL_approx".
    clear per.
    spcast.
    apply CL_approx.
    unfold per_approx.
    exists a b; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_func; unfold per_func; exists eqa eqb; dands; auto.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_eqval; dands; auto; apply tfb. }

  - Case "CL_cequiv".
    clear per.
    spcast.
    apply CL_cequiv.
    unfold per_cequiv.
    exists a b; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_func; unfold per_func; exists eqa eqb; dands; auto.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_eqval; dands; auto; apply tfb. }

  - Case "CL_eq".
    clear per.
    spcast.
    apply CL_eq.
    unfold per_eq.
    exists A a b eqa; dands; spcast; auto.
    right; dands; eauto 3 with slow.
    apply CL_func; unfold per_func; exists eqa0 eqb; dands; auto.
    exists A0 v B; dands; spcast; auto.
    { unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_eqval; dands; auto; apply tfb. }

  - Case "CL_teq".
    clear per.
    spcast.
    apply CL_teq.
    unfold per_teq.
    exists A B eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_func; unfold per_func; exists eqa0 eqb; dands; auto.
    exists A0 v B0; dands; spcast; auto.
    { unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_eqval; dands; auto; apply tfb. }

  - Case "CL_isect".
    clear per.
    spcast.
    apply CL_isect.
    unfold per_isect.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_func; unfold per_func; exists eqa0 eqb0; dands; auto.
      exists A0 v0 B0; dands; spcast; auto.
      { unfold per_extensional; left; spcast; auto. }
      { unfold per_intensional; introv c; spcast; computes_to_eqval; dands; auto; apply tfb. }
    }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_func".
    clear per.
    spcast.
    apply CL_func.
    unfold per_func.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto;
      [| |unfold type_family_members_eq; dands; tcsp];[|].

    {
      unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_func; unfold per_func; exists eqa0 eqb0; dands; auto.
      exists A0 v0 B0; dands; spcast; auto.
      { unfold per_extensional; left; spcast; auto. }
      { unfold per_intensional; introv c; spcast; computes_to_eqval; dands; auto; apply tfb. }
    }

    {
      unfold per_intensional; introv cc; spcast; computes_to_eqval.
      unfold per_intensional in intT.
      pose proof (intT A v B) as q; autodimp q hyp; spcast; auto; repnd.

      dands.

      - dts_props tsa uv te tys tyrr tyt tv tes tet tev.
        unfold type_transitive_body in tyt.
        unfold type_left_transitive in tyrr.

    }

  - Case "CL_disect".
    clear per.
    spcast.
    apply CL_disect.
    unfold per_disect.
    exists eqa0 eqb; dands; spcast; auto.
    unfold type_family.
    exists A0 v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_pertype".
    clear per.
    spcast.
    apply CL_pertype.
    unfold per_pertype.
    exists R eqr; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_w".
    clear per.
    spcast.
    apply CL_w.
    unfold per_w.
    exists eqa0 eqb; dands; spcast; auto.
    unfold type_family.
    exists A0 v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_m".
    clear per.
    spcast.
    apply CL_m.
    unfold per_m.
    exists eqa0 eqb; dands; spcast; auto.
    unfold type_family.
    exists A0 v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_texc".
    clear per.
    spcast.
    apply CL_texc.
    unfold per_texc.
    exists eqn eqe N E; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_union".
    clear per.
    spcast.
    apply CL_union.
    unfold per_union.
    exists eqa0 eqb A0 B; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_image".
    clear per.
    spcast.
    apply CL_image.
    unfold per_image.
    exists eqa0 A0 f; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_partial".
    clear per.
    spcast.
    apply CL_partial.
    unfold per_partial.
    exists A0 eqa0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_admiss".
    clear per.
    spcast.
    apply CL_admiss.
    unfold per_admiss.
    exists A0 eqa0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_mono".
    clear per.
    spcast.
    apply CL_mono.
    unfold per_mono.
    exists A0 eqa0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatom".
    clear per.
    spcast.
    apply CL_ffatom.
    unfold per_ffatom.
    exists A0 x a0 eqa0 u; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatoms".
    clear per.
    spcast.
    apply CL_ffatoms.
    unfold per_ffatoms.
    exists A0 x eqa0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_set".
    clear per.
    spcast.
    apply CL_set.
    unfold per_set.
    exists eqa0 eqb; dands; spcast; auto.
    unfold type_family.
    exists A0 v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_tunion".
    clear per.
    spcast.
    apply CL_tunion.
    unfold per_tunion.
    exists eqa0 eqb; dands; spcast; auto.
    unfold type_family.
    exists A0 v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_product".
    clear per.
    spcast.
    apply CL_product.
    unfold per_product.
    exists eqa0 eqb; dands; spcast; auto.
    unfold type_family.
    exists A0 v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.
Qed.

      (* copy equal_to_eq from close_type_sys_per_eq *)
      eapply equal_to_function; eauto.
      eapply type_system_props_implies_equal; eauto.
    }

  - SCase "type_left_transitive".

  - SCase "type_transitive".

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_func.
    eapply cequivc_mkc_function in comp;[|eauto]; exrepnd.
    exists eqa eqb; dands; auto.

    exists A' v' B'; dands; spcast; auto.

    { dts_props tsa uv tv te tes tet tev.
      apply te; auto. }

    split; dands; auto.
    introv.
    pose proof (tsb a a' e) as q.
    dts_props q uv tv te tes tet tev.
    apply te.
    apply bcequivc1; auto.

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply per_func_eq_sym; eauto.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply per_func_eq_trans; eauto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff.
    eapply per_func_eq_cequivc; eauto.
Qed.
