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
    -> (forall a1 a2, eqa1 a1 a2 -> (eqb1 a1) <=2=> (eqb2 a2))
    -> (meq lib eqa1 eqb1) <=2=> (meq lib eqa2 eqb2).
Proof.
  introv syma trana eqas eqbs.

  split.

  - revert t1 t2.
    cofix MEQIH.
    introv meqt.
    destruct meqt as [? ? ? ? ea c1 c2 imp].
    applydup eqas in ea.
    econstructor; try (exact c1); try (exact c2); auto.
    introv eb.
    apply MEQIH.
    apply imp.
    eapply eqbs;[|exact eb].
    eapply trana; eauto.

  - revert t1 t2.
    cofix MEQIH.
    introv meqt.
    destruct meqt as [? ? ? ? ea c1 c2 imp].
    applydup eqas in ea.
    econstructor; try (exact c1); try (exact c2); auto.
    introv eb.
    apply MEQIH.
    apply imp.
    eapply eqbs;[|exact eb].
    eapply trana; eauto.
Qed.

Lemma meq_sym {o} :
  forall lib eqa eqb (t1 t2 : @CTerm o) v B ts,
    term_equality_symmetric eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
          type_system_props lib ts (substc a1 v B) (eqb a1))
    -> (forall (a a' : CTerm) (e : eqa a a'), (eqb a) <=2=> (eqb a'))
    -> meq lib eqa eqb t1 t2
    -> meq lib eqa eqb t2 t1.
Proof.
  introv syma tsb eqbs.
  revert t1 t2.
  cofix MEQIH.
  introv meqt.
  destruct meqt as [? ? ? ? ea c1 c2 imp].

  econstructor; try (exact c1); try (exact c2); auto.
  introv eb.

  apply MEQIH.
  apply imp.
  eapply eqbs in eb;[|eauto].

  applydup tsb in ea.
  dts_props ea0 uv tv te tes tet tev; tcsp.
Qed.

Lemma meq_trans {o} :
  forall lib eqa eqb (t1 t2 t3 : @CTerm o) ts v B,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall a1 a2, eqa a1 a2 -> type_system_props lib ts (substc a1 v B) (eqb a1))
    -> (forall (a a' : CTerm) (e : eqa a a'), (eqb a) <=2=> (eqb a'))
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
  eapply MEQIH;[|apply imp2;eapply eqbs;[|eauto];auto ].

  apply imp1.

  apply tsb in ea1.
  dts_props ea1 uv tv te tes tet tev; tcsp.
  eapply tet; eauto.
Qed.

Lemma meq_cequivc {o} :
  forall lib eqa eqb (t t1 t2 : @CTerm o) ts v B,
    term_equality_respecting lib eqa
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall a1 a2, eqa a1 a2 -> type_system_props lib ts (substc a1 v B) (eqb a1))
    -> meq lib eqa eqb t t1
    -> cequivc lib t1 t2
    -> meq lib eqa eqb t t2.
Proof.
  introv respa syma trana tsb.
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

  eapply MEQIH;[apply imp1;eauto|].
  apply sp_implies_cequivc_apply; sp.
Qed.


Lemma close_type_system_m {p} :
    forall lib (ts : cts(p)) T (eq : per) A v B eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_m A v B)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> (forall (a a' : CTerm) (e : eqa a a'), close lib ts (substc a v B) (eqb a))
    -> (forall (a a' : CTerm) (e : eqa a a'),
           type_system_props lib (close lib ts) (substc a v B) (eqb a))
    -> (forall (a a' : CTerm) (e : eqa a a'), (eqb a) <=2=> (eqb a'))
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
      introv e; dands; tcsp.
      eapply clb; eauto. }
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

    introv e; dands; auto.
    applydup tsb in e.
    dts_props e0 uv tv te tes tet tev.
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
