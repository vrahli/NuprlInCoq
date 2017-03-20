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


Lemma eq_term_equals_per_eq_eq {o} :
  forall lib (a b : @CTerm o) (eq1 eq2 : per(o)),
    (eq1 <=2=> eq2)
    -> (per_eq_eq lib a b eq1) <=2=> (per_eq_eq lib a b eq2).
Proof.
  introv eqs; introv.
  unfold per_eq_eq; split; intro h; exrepnd; exists x1 x2 y1 y2; dands; auto;
    try (complete (apply eqs; auto)).
Qed.

Lemma cequiv_per_eq_eq {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o) (eq1 eq2 : per(o)),
    term_equality_symmetric eq1
    -> term_equality_transitive eq1
    -> term_equality_respecting lib eq1
    -> (eq1 <=2=> eq2)
    -> cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> (per_eq_eq lib a1 b1 eq1) <=2=> (per_eq_eq lib a2 b2 eq2).
Proof.
  introv tys tyt tvr eqs ceqa ceqb.
  eapply eq_term_equals_trans;[|apply eq_term_equals_per_eq_eq;exact eqs].
  clear dependent eq2.

  unfold per_eq_eq; split; intro q; exrepnd; exists x1 x2 y1 y2; dands; auto;
    try (complete (apply eqs; auto)).

  { eapply tyt; try (exact h);
      [eapply tys; try (exact h);
       eapply tvr; try (exact h);
       try (spcast; exact ceqa);
       eapply tyt; try (exact h);
       [exact q3|];
       eapply tys; try (exact h);auto
      |].

    eapply tyt; try (exact h);
      [|eapply tvr; try (exact h);try (spcast; exact ceqb)];auto.
    eapply tyt; try (exact h); try (exact q3).
    eapply tys; eauto. }

  { eapply tyt; try (exact h);
      [eapply tys; try (exact h); eapply tvr; try (exact h);
       try (spcast; exact ceqa)
      |]; auto.
    eapply tyt; try (exact h); try (exact q3).
    eapply tys; eauto. }

  { eapply tyt; try (exact h);
      [eapply tys; try (exact h);eapply tvr; try (exact h);
       try (spcast; try (exact ceqb));
       eapply tyt; try (exact h); try (exact q3);
       eapply tys; try (exact h);auto
      |]; auto. }

  { eapply tyt; try (exact h);
      [eapply tys; try (exact h);
       eapply tvr; try (exact h);
       try (spcast; apply cequivc_sym; exact ceqa);
       eapply tyt; try (exact h); try (exact q3);
       eapply tys; try (exact h);auto
      |].

    eapply tyt; try (exact h);
      [|eapply tvr; try (exact h);try (spcast;apply cequivc_sym;exact ceqb)];auto.
    eapply tyt; try (exact h); try (exact q3).
    eapply tys; eauto. }

  { eapply tyt; try (exact h);
      [eapply tys; try (exact h);eapply tvr; try (exact h);
       try (spcast;apply cequivc_sym;exact ceqa)
      |]; auto.
    eapply tyt; try (exact h); try (exact q3).
    eapply tys; eauto. }

  { eapply tyt; try (exact h);
      [eapply tys; try (exact h);eapply tvr; try (exact h);
       try (spcast; apply cequivc_sym;try (exact ceqb));
       eapply tyt; try (exact h); try (exact q3);
       eapply tys; try (exact h);auto
      |]; auto. }
Qed.

Lemma equal_to_eq {o} :
  forall lib ts (T1 T2 T : @CTerm o) a b A eq eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> not_uni lib T1
    -> computes_to_valc lib T (mkc_equality a b A)
    -> close lib ts T1 T2 eq
    -> close lib ts A A eqa
    -> (eq <=2=> (per_eq_eq lib a b eqa))
    -> close lib ts T1 T eq.
Proof.
  introv tysys dou nuni comp cl cla eqiff.
  close_cases (induction cl using @close_ind') Case; tcsp.

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
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_atom".
    clear per.
    spcast.
    apply CL_atom.
    unfold per_atom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_uatom".
    clear per.
    spcast.
    apply CL_uatom.
    unfold per_uatom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_base".
    clear per.
    spcast.
    apply CL_base.
    unfold per_base; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_approx".
    clear per.
    spcast.
    apply CL_approx.
    unfold per_approx.
    exists a0 b0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_cequiv".
    clear per.
    spcast.
    apply CL_cequiv.
    unfold per_cequiv.
    exists a0 b0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_eq".
    clear per.
    spcast.
    apply CL_eq.
    unfold per_eq.
    exists A0 a0 b0 eqa0; dands; spcast; auto.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_teq".
    clear per.
    spcast.
    apply CL_teq.
    unfold per_teq.
    exists A0 B eqa0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_isect".
    clear per.
    spcast.
    apply CL_isect.
    unfold per_isect.
    exists eqa0 eqb; dands; spcast; auto.
    unfold type_family.
    exists A0 v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_func".
    clear per.
    spcast.
    apply CL_func.
    unfold per_func.
    exists eqa0 eqb; dands; spcast; auto.
    unfold type_family.
    exists A0 v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_eq; unfold per_eq; exists A a b eqa; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

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

Lemma close_type_system_eq {o} :
  forall lib (ts : cts(o)) T T' eq A a b eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_equality a b A)
    -> per_extensional lib (close lib ts) T T' eq
    -> per_extensional lib
                       (fun (T1 T2 : CTerm) (eq : per( o)) =>
                          type_system lib ts
                          -> defines_only_universes lib ts
                          -> type_system_props lib (close lib ts) T1 T2 eq)
                       T T' eq
    -> close lib ts A A eqa
    -> (eq <=2=> (per_eq_eq lib a b eqa))
    -> per_eq lib (close lib ts) T T' eq
    -> type_system_props lib (close lib ts) A A eqa
    -> type_system_props lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp ext extP cla (*eoc*) eqiff per props.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".

    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_eq in h; exrepnd; spcast.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
    dts_props props uv te tys tyrr tyt tv tes tet tev.
    eapply uv in h3.
    apply eq_term_equals_per_eq_eq; auto.

  - SCase "type_extensionality".

    introv eqt.
    apply CL_eq.
    exists A a b eqa; dands; spcast; auto.

    { unfold per_extensional; unfold per_extensional in extP; repndors; tcsp; right.
      repnd; dands; auto.
      repeat (autodimp extP0 hyp).
      dts_props extP0 uv te tys tyrr tyt tv tes tet tev.
      apply te; auto. }

    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_symmetric".

    unfold type_symmetric_body.

    clear ext.
    unfold per_extensional in extP.
    repndors; spcast.

    {
      apply CL_eq.
      dup extP as ceq.
      eapply cequivc_mkc_equality in extP;[|eauto]; exrepnd.
      exists T'0 a' b' eqa; dands; spcast; auto.

      - left; spcast; apply cequivc_sym; auto.

      - dts_props props uv te tys tyrr tyt tv tes tet tev.
        eapply tv; auto.

      - eapply eq_term_equals_trans;[exact eqiff|].
        dts_props props uv te tys tyrr tyt tv tes tet tev.
        eapply cequiv_per_eq_eq; try (exact cla); auto.
    }

    {
      repnd.
      repeat (autodimp extP0 hyp).
      eapply equal_to_eq; eauto.
      eapply type_system_props_implies_equal; eauto.
    }

    (*
  - SCase "type_left_reflexive".

    unfold type_left_reflexive.
    apply CL_eq; exists A a b eqa; dands; spcast; auto.
    left; spcast; auto.

  - SCase "type_right_reflexive".

    unfold type_right_reflexive.
    clear ext.
    unfold per_extensional in extP.
    repndors; spcast.

    {
      dup extP as ceq.
      eapply cequivc_mkc_equality in extP; eauto; exrepnd.
      apply CL_eq.
      exists T'0 a' b' eqa; dands; spcast; auto.

      - left; spcast; apply cequivc_sym; auto.

      - dts_props props uv te tys tylr tyrr tyt tv tes tet tev.
        eapply tv; auto.

      - eapply eq_term_equals_trans;[exact eqiff|].
        dts_props props uv te tys tylr tyrr tyt tv tes tet tev.
        eapply cequiv_per_eq_eq; try (exact cla); auto.
    }

    {
      repnd.
      repeat (autodimp extP0 hyp).
      eapply type_system_props_implies_equal; eauto.
    }*)

  - SCase "type_left_transitive".

    introv cl.
    pose proof (dest_close_per_equality_l lib ts T a b A T3 eq tysys dou comp cl) as q.
    unfold per_eq in q; exrepnd; spcast; computes_to_eqval.
    unfold per_extensional in q2; repndors; spcast; tcsp.
    apply CL_eq.
    eapply cequivc_mkc_equality in q2; eauto; exrepnd.
    exists T'0 a' b' eqa; dands; spcast; auto.

    { left; spcast; apply cequivc_sym; auto. }

    { dts_props props uv te tys tyrr tyt tv tes tet tev.
      eapply tv; auto. }

    { eapply eq_term_equals_trans;[exact eqiff|].
      dts_props props uv te tys tyrr tyt tv tes tet tev.
      eapply cequiv_per_eq_eq; try (exact cla); auto. }

  - SCase "type_transitive".

    intros cl2.
    apply CL_eq.
    exists A a b eqa; dands; spcast; auto.

    clear ext.
    unfold per_extensional in extP.
    repndors; spcast.

    {
      dup extP as ceq.
      eapply cequivc_mkc_equality in extP; eauto; exrepnd.
      pose proof (dest_close_per_equality_l lib ts T' a' b' T'0 T3 eq tysys dou extP1 cl2) as q.
      unfold per_eq in q; exrepnd; spcast.
      computes_to_eqval.

      unfold per_extensional in *; repndors; repnd; spcast.

      { left; spcast; eapply cequivc_trans; eauto. }

      right; tcsp.
    }

    {
      repnd.
      repeat (autodimp extP0 hyp).
      right.
      dands;[|eapply close_preserves_not_uni; eauto].
      dts_props extP0 uv te tys tylt tyt tv tes tet tev.

      eapply tylt; auto.
    }

  - SCase "type_value_respecting".

    introv ceq1 ceq2.
    apply CL_eq.
    eapply cequivc_mkc_equality in comp;[|eauto]; exrepnd.

    dts_props props uv te tys tylt tyt tv tes tet tev.

    exists T'0 a' b' eqa; dands; spcast; auto.

    {
      clear ext.
      unfold per_extensional in extP.
      repndors; spcast; tcsp.

      - left; spcast.
        eapply cequivc_trans;[apply cequivc_sym;exact ceq1|].
        eapply cequivc_trans;[exact extP|]; auto.

      - repnd.
        repeat (autodimp extP0 hyp).
        right; dands; auto.

        + dts_props extP0 uv2 te2 tys2 tylt2 tyt2 tv2 tes2 tet2 tev2.
          eapply tv2; auto.

        + eapply cequivc_preserves_not_uni; eauto.
    }

    {
      eapply eq_term_equals_trans;[eauto|].
      apply cequiv_per_eq_eq; auto.
    }

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    unfold per_eq_eq in e; unfold per_eq_eq; exrepnd.
    dts_props props uv te tys tylt tyt tv tes tet tev.
    exists x2 x1 y2 y1; dands; auto.
    { eapply tet; eauto. }
    { eapply tet; eauto. }

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    unfold per_eq_eq in e1, e2; unfold per_eq_eq; exrepnd.
    dts_props props uv te tys tylt tyt tv tes tet tev.
    ccomputes_to_eqval.
    exists x0 x2 y0 y2; dands; spcast; auto.
    eapply tet;[eauto|]; eauto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff.
    unfold per_eq_eq in e; unfold per_eq_eq; exrepnd.
    ccomputes_to_eqval.
    eapply cequivc_mkc_prefl in c;[|eauto]; exrepnd.
    dts_props props uv te tys tylt tyt tv tes tet tev.
    exists x1 c0 y1 d; dands; spcast; auto.
    { apply (eq_ts_cequivc lib b x1 b c0 eqa); auto. }
    { eapply eq_ts_cequivc; try (exact c2); try (apply cequivc_refl); auto. }
Qed.
