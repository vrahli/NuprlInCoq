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



Lemma eq_term_equals_per_tunion_eq_if {p} :
  forall (eqa1 eqa2 : per(p)) (eqb1 : per-fam(eqa1)) (eqb2 : per-fam(eqa2)),
    term_equality_symmetric eqa1
    -> term_equality_transitive eqa1
    -> eqa1 <=2=> eqa2
    -> (forall a1 a2 (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2), (eqb1 a1 a2 e1) <=2=> (eqb2 a1 a2 e2))
    -> (per_tunion_eq eqa1 eqb1) <=2=> (per_tunion_eq eqa2 eqb2).
Proof.
  introv syma trana eqt1 eqt2.
  introv; split; intro k; induction k.

  - apply @tunion_eq_cl with (t := t); sp.

  - dup e as e'; apply eqt1 in e'.
    eapply tunion_eq_eq; eauto.
    assert (eqa1 a1 a1) as q by (eapply trana; eauto).
    eapply (eqt2 a1 a2 e e'); eauto.

  - apply @tunion_eq_cl with (t := t); sp.

  - dup e as e'; apply eqt1 in e'.
    eapply tunion_eq_eq; eauto.
    assert (eqa1 a1 a1) as q by (eapply trana; eauto).
    eapply (eqt2 a1 a2 e' e); eauto.
Qed.

Lemma per_tunion_eq_sym {p} :
  forall (eqa : per(p)) eqb t1 t2,
    (forall a1 a2 (e : eqa a1 a2), term_equality_symmetric (eqb a1 a2 e))
    -> per_tunion_eq eqa eqb t1 t2
    -> per_tunion_eq eqa eqb t2 t1.
Proof.
  introv tesb per.
  induction per.
  apply @tunion_eq_cl with (t := t); sp.
  eapply tunion_eq_eq; eauto.
  eapply tesb; eauto.
Qed.

Lemma per_tunion_eq_trans {p} :
  forall (eqa : per(p)) eqb t1 t2 t3,
    per_tunion_eq eqa eqb t1 t2
    -> per_tunion_eq eqa eqb t2 t3
    -> per_tunion_eq eqa eqb t1 t3.
Proof.
  introv per1 per2.
  apply tunion_eq_cl with (t := t2); sp.
Qed.

Lemma per_tunion_eq_cequiv {p} :
  forall lib (eqa : per(p)) eqb t t',
    (forall a1 a2 (e : eqa a1 a2), term_equality_symmetric (eqb a1 a2 e))
    -> (forall a1 a2 (e : eqa a1 a2), term_equality_transitive (eqb a1 a2 e))
    -> (forall a1 a2 (e : eqa a1 a2), term_equality_respecting lib (eqb a1 a2 e))
    -> t ~=~(lib) t'
    -> per_tunion_eq eqa eqb t t
    -> per_tunion_eq eqa eqb t t'.
Proof.
  introv tes tet ter ceq per.
  revert_dependents t'.
  induction per; introv ceq.
  apply IHper2; auto.
  eapply tunion_eq_eq; eauto.
  eapply ter; eauto.
  eapply tet; eauto.
  eapply tes; eauto.
Qed.


Lemma close_type_system_tunion {p} :
  forall lib (ts : cts(p)) T (eq : per) A v B eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_tunion A v B)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> (forall a a' (e : eqa a a'), close lib ts (substc a v B) (eqb a a' e))
    -> (forall a a' (e : eqa a a'),
           type_system_props lib (close lib ts) (substc a v B) (eqb a a' e))
    -> per_fam_equiv eqb
    -> eq <=2=> (per_tunion_eq eqa eqb)
    -> per_tunion lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa clb tsb eqbiff eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_tunion in h; exrepnd; spcast.
    unfold type_family in h0; exrepnd.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    dts_props tsa uv tv te tes tet tev.
    apply uv in h3.

    pose proof (eqbs_trans lib (close lib ts) v B eqa eqa0 eqb eqb0) as q.
    repeat (autodimp q hyp).

    apply eq_term_equals_per_tunion_eq_if; auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_tunion.
    exists eqa eqb; dands; auto.
    { exists A v B; dands; spcast; auto.
      split; auto. }
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_tunion.
    eapply cequivc_mkc_tunion in comp;[|eauto]; exrepnd.
    exists eqa eqb; dands; auto.

    exists A' v' B'; dands; spcast; auto.

    { dts_props tsa uv tv te tes tet tev.
      apply te; auto. }

    split; dands; auto; introv.
    pose proof (tsb a a' e ) as h.
    dts_props h uv tv te tes tet tev.
    apply te.
    apply bcequivc1; auto.

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply per_tunion_eq_sym; eauto.
    introv; pose proof (tsb _ _ e0) as h; dts_props h uv2 tv2 te2 tes2 tet2 tev2; tcsp.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply per_tunion_eq_trans; eauto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply per_tunion_eq_cequiv; spcast; eauto;
      introv; pose proof (tsb _ _ e0) as h; dts_props h uv2 tv2 te2 tes2 tet2 tev2; tcsp.
Qed.
