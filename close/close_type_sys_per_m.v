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


Require Import type_sys_useful.
Require Import dest_close.



Lemma meq_eq_term_equals {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2,
    term_equality_symmetric eqa1
    -> term_equality_transitive eqa1
    -> (eqa1 <=2=> eqa2)
    -> (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2), (eqb1 a1 a2 e1) <=2=> (eqb2 a1 a2 e2))
    -> (meq lib eqa1 eqb1) <=2=> (meq lib eqa2 eqb2).
Proof.
  introv syma trana eqas eqbs.

  split.

  - revert t1 t2.
    cofix MEQIH.
    introv meqt.
    destruct meqt as [? ? ? ? ea c1 c2 imp].
    appdup eqas in ea.
    econstructor; try (exact c1); try (exact c2); auto.
    introv eb.
    apply MEQIH.
    apply imp.
    apply (eqbs a a' ea ea0); exact eb.

  - revert t1 t2.
    cofix MEQIH.
    introv meqt.
    destruct meqt as [? ? ? ? ea c1 c2 imp].
    appdup eqas in ea.
    econstructor; try (exact c1); try (exact c2); auto.
    introv eb.
    apply MEQIH.
    apply imp.
    apply (eqbs a a' ea0 ea); exact eb.
Qed.

Lemma meq_sym {o} :
  forall lib eqa eqb (t1 t2 : @CTerm o) v B ts,
    term_equality_symmetric eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
          type_system_props lib ts (substc a1 v B) (eqb a1 a2 e))
    -> per_fam_equiv eqb
    -> meq lib eqa eqb t1 t2
    -> meq lib eqa eqb t2 t1.
Proof.
  introv syma tsb eqbs.
  revert t1 t2.
  cofix MEQIH.
  introv meqt.
  destruct meqt as [? ? ? ? ea c1 c2 imp].

  appdup syma in ea.

  econstructor; try (exact c1); try (exact c2); auto.
  introv eb.

  apply MEQIH.
  apply imp.
  pose proof (tsb a a' ea) as q.
  dts_props q uv tv te tes tet tev; tcsp.
  apply tes.
  apply (per_fam_equiv_sym _ _ _ ea ea0); auto; exact eb.
Qed.

Lemma meq_trans {o} :
  forall lib eqa eqb (t1 t2 t3 : @CTerm o) ts v B,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall a1 a2 (e : eqa a1 a2), type_system_props lib ts (substc a1 v B) (eqb a1 a2 e))
    -> per_fam_equiv eqb
    -> meq lib eqa eqb t1 t2
    -> meq lib eqa eqb t2 t3
    -> meq lib eqa eqb t1 t3.
Proof.
  introv syma trana tsb eqbs.
  revert t1 t2 t3.
  cofix MEQIH.
  introv meq1 meq2.

  destruct meq1 as [? ? ? ? ea1 c1 c2 imp1].
  destruct meq2 as [? ? ? ? ea2 c3 c4 imp2].
  ccomputes_to_eqval.

  assert (eqa a a'0) as e' by (eapply trana; eauto).

  econstructor; spcast; try (exact c1); try (exact c4); auto.
  introv eb.
  eapply MEQIH;
    [|apply imp2;
      apply (per_fam_equiv_trans_l _ a'0 a' a ea2 e');
      auto; exact eb].

  apply imp1.

  pose proof (tsb a a' ea1) as q.
  dts_props q uv tv te tes tet tev; tcsp.
  eapply tet; eauto;
    [apply (per_fam_equiv_trans_r _ a a'0 a' e' ea1); auto; exact eb|].
  apply tes.
  apply (per_fam_equiv_trans_r _ a a'0 a' e' ea1); auto; exact eb.
Qed.

Lemma meq_cequivc {o} :
  forall lib eqa eqb (t t1 t2 : @CTerm o) ts v B,
    term_equality_respecting lib eqa
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> per_fam_equiv eqb
    -> (forall a1 a2 (e : eqa a1 a2), type_system_props lib ts (substc a1 v B) (eqb a1 a2 e))
    -> meq lib eqa eqb t t1
    -> cequivc lib t1 t2
    -> meq lib eqa eqb t t2.
Proof.
  introv respa syma trana pfb tsb.
  revert t t1 t2.
  cofix MEQIH.
  introv meq1 ceq.

  destruct meq1 as [? ? ? ? ea1 c1 c2 imp1].
  spcast.
  eapply cequivc_mkc_sup in c2;[|eauto].
  exrepnd.
  rename a'0 into a2.
  rename b' into f2.

  assert (eqa a a2)
    as ea2
      by (eapply trana;[eauto|]; apply respa; spcast; auto; eapply trana; eauto).

  econstructor; spcast; try (exact c1); try (exact c0); auto.
  introv eb.

  eapply MEQIH;
    [apply imp1; apply (per_fam_equiv_trans_r _ a a2 a' ea2 ea1); auto; exact eb|].
  apply sp_implies_cequivc_apply; sp.
Qed.


Lemma close_type_system_m {p} :
    forall lib (ts : cts(p)) T (eq : per) A v B eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_m A v B)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> (forall (a a' : CTerm) (e : eqa a a'), close lib ts (substc a v B) (eqb a a' e))
    -> (forall (a a' : CTerm) (e : eqa a a'),
           type_system_props lib (close lib ts) (substc a v B) (eqb a a' e))
    -> per_fam_equiv eqb
    -> eq <=2=> (meq lib eqa eqb)
    -> per_m lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa clb tsb eqbiff eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_m in h; exrepnd; spcast.
    unfold type_family in h0; exrepnd.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    dts_props tsa uv tv te tes tet tev.
    apply uv in h3.

    pose proof (eqbs_trans lib (close lib ts) v B eqa eqa0 eqb eqb0) as q.
    repeat (autodimp q hyp).

    apply meq_eq_term_equals; auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_m.
    exists eqa eqb; dands; auto.
    { exists A v B; dands; spcast; auto.
      split; auto. }
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_m.
    eapply cequivc_mkc_m in comp;[|eauto]; exrepnd.
    exists eqa eqb; dands; auto.

    exists A' v' B'; dands; spcast; auto.

    { dts_props tsa uv tv te tes tet tev.
      apply te; auto. }

    split; dands; auto; introv.
    pose proof (tsb a a' e) as h.
    dts_props h uv tv te tes tet tev.
    apply te.
    apply bcequivc1; auto.

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply meq_sym; eauto.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply meq_trans; eauto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply meq_cequivc; eauto.
Qed.
