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


Require Export type_sys.
Require Import dest_close.


Lemma eq_term_equals_implies_per_aeq_eq {o} :
  forall lib (a b : @CTerm o) (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> (per_aeq_eq lib a b eqa1) <=2=> (per_aeq_eq lib a b eqa2).
Proof.
  introv h; introv; unfold per_aeq_eq; split; intro q; exrepnd;
    exists x1 x2; dands; auto; apply h; auto.
Qed.

Lemma cequivc_implies_per_aeq_eq {o} :
  forall lib (a a' b b' : @CTerm o) eqa,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> term_equality_respecting lib eqa
    -> cequivc lib a a'
    -> cequivc lib b b'
    -> (per_aeq_eq lib a b eqa) <=2=> (per_aeq_eq lib a' b' eqa).
Proof.
  introv sym trans resp ceq1 ceq2; introv;
    unfold per_aeq_eq; split; intro h; exrepnd;
      exists x1 x2; dands; auto.
  - apply (eq_ts_cequivc lib a b a' b' eqa); auto.
  - apply (eq_ts_cequivc lib a' b' a b eqa); auto; apply cequivc_sym; auto.
Qed.

Lemma per_aeq_eq_sym {o} :
  forall lib (a b t1 t2 : @CTerm o) eqa,
    term_equality_symmetric eqa
    -> per_aeq_eq lib a b eqa t1 t2
    -> per_aeq_eq lib a b eqa t2 t1.
Proof.
  introv sym per.
  unfold per_aeq_eq in *; exrepnd.
  exists x2 x1; dands; auto.
Qed.

Lemma per_aeq_eq_trans {o} :
  forall lib (a b t1 t2 t3 : @CTerm o) eqa,
    term_equality_transitive eqa
    -> per_aeq_eq lib a b eqa t1 t2
    -> per_aeq_eq lib a b eqa t2 t3
    -> per_aeq_eq lib a b eqa t1 t3.
Proof.
  introv tran per1 per2.
  unfold per_aeq_eq in *; exrepnd.
  ccomputes_to_eqval.
  exists x0 x2; dands; spcast; auto.
  eapply tran; eauto.
Qed.

Lemma per_aeq_eq_resp {o} :
  forall lib (a b t t' : @CTerm o) eqa,
    term_equality_respecting lib eqa
    -> cequivc lib t t'
    -> per_aeq_eq lib a b eqa t t
    -> per_aeq_eq lib a b eqa t t'.
Proof.
  introv resp ceq per.
  unfold per_aeq_eq in *; exrepnd.
  spcast; computes_to_eqval.
  eapply cequivc_mkc_refl in ceq;[|eauto]; exrepnd.
  exists x1 b0; dands; spcast; auto.
  eapply resp; spcast; eauto.
Qed.

Lemma close_type_system_aeq {o} :
  forall lib (ts : cts(o)) T eq A a b eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_aequality a b A)
    -> close lib ts A eqa
    -> (eq <=2=> (per_aeq_eq lib a b eqa))
    -> per_aeq lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) A eqa
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla (*eoc*) eqiff per props.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_aeq in h; exrepnd; spcast.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
    dts_props props uv tv te tes tet tev.
    eapply uv in h2.
    apply eq_term_equals_implies_per_aeq_eq; auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_aeq.
    exists A a b eqa; dands; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_aeq.
    eapply cequivc_mkc_aequality in comp;[|eauto]; exrepnd.
    exists T'0 a' b' eqa.

    dts_props props uv tv te tes tet tev.
    dands; spcast; auto.
    eapply eq_term_equals_trans;[eauto|].
    apply cequivc_implies_per_aeq_eq; auto.

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    dts_props props uv tv te tes tet tev.
    eapply per_aeq_eq_sym; eauto.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    dts_props props uv tv te tes tet tev.
    eapply per_aeq_eq_trans; eauto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff.
    dts_props props uv tv te tes tet tev.
    eapply per_aeq_eq_resp; eauto.
Qed.
