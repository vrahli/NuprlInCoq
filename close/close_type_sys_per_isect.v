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


Lemma eq_term_equals_per_isect_eq {o} :
  forall (eqa1 eqa2 : per(o)) eqb1 eqb2,
    term_equality_symmetric eqa1
    -> (eqa1 <=2=> eqa2)
    -> (forall a a' : CTerm, eqa1 a a' -> (eqb1 a) <=2=> (eqb2 a'))
    -> (per_isect_eq eqa1 eqb1) <=2=> (per_isect_eq eqa2 eqb2).
Proof.
  introv syma eaiff ebiff.
  unfold per_isect_eq.
  split; introv h e.

  - applydup eaiff in e.
    apply syma in e0.
    applydup h in e0.
    apply ebiff in e0.
    apply e0 in e1; auto.

  - applydup ebiff in e.
    apply e0.
    apply syma in e.
    apply eaiff in e.
    eapply h; eauto.
Qed.

Lemma per_isect_eq_sym {o} :
  forall lib ts v B (eqa : per(o)) eqb t1 t2,
    (forall a a' : CTerm,
        eqa a a' -> type_system_props lib ts (B) [[v \\ a]] (eqb a))
    -> per_isect_eq eqa eqb t1 t2
    -> per_isect_eq eqa eqb t2 t1.
Proof.
  introv tsb per.
  unfold per_isect_eq in *.
  introv e.
  applydup per in e.
  applydup tsb in e.
  dts_props e1 uv tv te tes tet tev.
  apply tes; auto.
Qed.

Lemma per_isect_eq_trans {o} :
  forall lib ts v B (eqa : per(o)) eqb t1 t2 t3,
    (forall a a' : CTerm,
        eqa a a' -> type_system_props lib ts (B) [[v \\ a]] (eqb a))
    -> per_isect_eq eqa eqb t1 t2
    -> per_isect_eq eqa eqb t2 t3
    -> per_isect_eq eqa eqb t1 t3.
Proof.
  introv tsb per1 per2.
  unfold per_isect_eq in *.
  introv e.
  applydup per1 in e.
  applydup per2 in e.
  applydup tsb in e.
  dts_props e2 uv tv te tes tet tev.
  eapply tet; eauto.
Qed.

Lemma per_isect_eq_cequivc {o} :
  forall lib ts v B (eqa : per(o)) eqb t1 t2,
    (forall a a' : CTerm,
        eqa a a' -> type_system_props lib ts (B) [[v \\ a]] (eqb a))
    -> cequivc lib t1 t2
    -> per_isect_eq eqa eqb t1 t1
    -> per_isect_eq eqa eqb t1 t2.
Proof.
  introv tsb ceq per.
  unfold per_isect_eq in *.
  introv e.
  applydup per in e.
  applydup tsb in e.
  dts_props e1 uv tv te tes tet tev.
  eapply tev; spcast; eauto.
Qed.

Lemma close_type_system_isect {p} :
  forall lib (ts : cts(p)) T (eq : per) A v B eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_isect A v B)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> (forall (a a' : CTerm) (e : eqa a a'), close lib ts (substc a v B) (eqb a))
    -> (forall (a a' : CTerm) (e : eqa a a'),
           type_system_props lib (close lib ts) (substc a v B) (eqb a))
    -> (forall (a a' : CTerm) (e : eqa a a'), (eqb a) <=2=> (eqb a'))
    -> eq <=2=> (per_isect_eq eqa eqb)
    -> per_isect lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa clb tsb eqbiff eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_isect in h; exrepnd; spcast.
    unfold type_family in h0; exrepnd.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    dts_props tsa uv tv te tes tet tev.
    apply uv in h3.

    pose proof (eqbs_trans lib (close lib ts) v B eqa eqa0 eqb eqb0) as q.
    repeat (autodimp q hyp).

    apply eq_term_equals_per_isect_eq; auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_isect.
    exists eqa eqb; dands; auto.
    { exists A v B; dands; spcast; auto.
      introv e; dands; tcsp.
      eapply clb; eauto. }
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_isect.
    eapply cequivc_mkc_isect in comp;[|eauto]; exrepnd.
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
    eapply per_isect_eq_sym; eauto.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    eapply per_isect_eq_trans; eauto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff.
    eapply per_isect_eq_cequivc; eauto.
Qed.
