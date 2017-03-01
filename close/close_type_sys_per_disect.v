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


Lemma eq_term_equals_per_disect_eq {o} :
  forall (eqa1 eqa2 : per(o)) eqb1 eqb2,
    term_equality_symmetric eqa1
    -> term_equality_transitive eqa1
    -> (eqa1 <=2=> eqa2)
    -> (forall a a' (e1 : eqa1 a a') (e2 : eqa2 a a'), (eqb1 a a' e1) <=2=> (eqb2 a a' e2))
    -> (per_disect_eq eqa1 eqb1) <=2=> (per_disect_eq eqa2 eqb2).
Proof.
  introv syma trana eaiff ebiff.
  unfold per_disect_eq.
  split; introv h; exrepnd; dands; auto.

  - appdup eaiff in e; exists e0.
    eapply ebiff; eauto.

  - appdup eaiff in e; exists e0.
    eapply ebiff; eauto.
Qed.

Lemma per_disect_eq_sym {o} :
  forall lib ts v B (eqa : per(o)) eqb t1 t2,
    term_equality_symmetric eqa
    -> (forall a a' (e : eqa a a'), type_system_props lib ts (B) [[v \\ a]] (eqb a a' e))
    -> per_fam_equiv eqb
    -> per_disect_eq eqa eqb t1 t2
    -> per_disect_eq eqa eqb t2 t1.
Proof.
  introv syma tsb eqbiff per.
  unfold per_disect_eq in *.
  exrepnd; dands; tcsp.
  appdup syma in e; exists e0.
  apply (per_fam_equiv_sym _ _ _ e e0); auto.

  pose proof (tsb t1 t2 e) as h.
  dts_props h uv tv te tes tet tev.
  apply tes; auto.
Qed.

Lemma per_disect_eq_trans {o} :
  forall lib ts v B (eqa : per(o)) eqb t1 t2 t3,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall a a' (e : eqa a a'), type_system_props lib ts (B) [[v \\ a]] (eqb a a' e))
    -> per_fam_equiv eqb
    -> per_disect_eq eqa eqb t1 t2
    -> per_disect_eq eqa eqb t2 t3
    -> per_disect_eq eqa eqb t1 t3.
Proof.
  introv syma trana tsb eqbiff per1 per2.
  unfold per_disect_eq in *.
  exrepnd; dands; auto.

  assert (eqa t1 t1) as ea.
  { eapply trana; eauto. }

  pose proof (trana t1 t2 t3 e0 e) as q; exists q.
  apply (per_fam_equiv_refl_l _ _ _ q ea); auto.
  apply (per_fam_equiv_refl_l _ _ _ e0 ea) in per2; auto.
  apply (per_fam_equiv_trans_l _ _ _ _ e q) in per0; auto.
  apply (per_fam_equiv_refl_l _ _ _ q ea) in per0; auto.

  pose proof (tsb t1 t1 ea) as h.
  dts_props h uv tv te tes tet tev.
  eapply tet; eauto.
Qed.

Lemma per_disect_eq_cequivc {o} :
  forall lib ts A v B (eqa : per(o)) eqb t1 t2,
    type_system_props lib ts A eqa
    -> per_fam_equiv eqb
    -> (forall a a' (e : eqa a a'), type_system_props lib ts (B) [[v \\ a]] (eqb a a' e))
    -> cequivc lib t1 t2
    -> per_disect_eq eqa eqb t1 t1
    -> per_disect_eq eqa eqb t1 t2.
Proof.
  introv tsa pf tsb ceq per.
  unfold per_disect_eq in *.
  exrepnd; dands; auto.

  assert (eqa t1 t2) as ea.
  { dts_props tsa uv tv te tes tet tev.
    apply tev; spcast; auto. }
  exists ea.

  apply (per_fam_equiv_refl_l _ _ _ ea e); auto; auto.

  pose proof (tsb t1 t1 e) as q.
  dts_props q uv tv te tes tet tev.
  apply tev; spcast; auto.
Qed.

Lemma close_type_system_disect {p} :
  forall lib (ts : cts(p)) T (eq : per) A v B eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_disect A v B)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> (forall (a a' : CTerm) (e : eqa a a'), close lib ts (substc a v B) (eqb a a' e))
    -> (forall (a a' : CTerm) (e : eqa a a'),
           type_system_props lib (close lib ts) (substc a v B) (eqb a a' e))
    -> per_fam_equiv eqb
    -> eq <=2=> (per_disect_eq eqa eqb)
    -> per_disect lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa clb tsb eqbiff eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_disect in h; exrepnd; spcast.
    unfold type_family in h0; exrepnd.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    dts_props tsa uv tv te tes tet tev.
    apply uv in h3.

    pose proof (eqbs_trans lib (close lib ts) v B eqa eqa0 eqb eqb0) as q.
    repeat (autodimp q hyp).

    apply eq_term_equals_per_disect_eq; auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_disect.
    exists eqa eqb; dands; auto.
    { exists A v B; dands; spcast; auto.
      split; tcsp. }
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_disect.
    eapply cequivc_mkc_disect in comp;[|eauto]; exrepnd.
    exists eqa eqb; dands; auto.

    exists A' v' B'; dands; spcast; auto.

    { dts_props tsa uv tv te tes tet tev.
      apply te; auto. }

    split; dands; auto; introv.
    pose proof (tsb a a' e) as q.
    dts_props q uv tv te tes tet tev.
    apply te.
    apply bcequivc1; auto.

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply per_disect_eq_sym; eauto.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply per_disect_eq_trans; eauto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff.
    eapply per_disect_eq_cequivc; eauto.
Qed.
