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


Lemma close_type_system_aeq {o} :
  forall lib (ts : cts(o)) T eq A a b eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_aequality a b A)
    -> close lib ts A eqa
    -> eqorceq lib eqa a b
    -> (eq <=2=> (per_aeq_eq lib a b eqa))
    -> per_aeq lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) A eqa
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla eoc eqiff per props.
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
    unfold per_aeq_eq; split; introv q; exrepnd; dands; auto;
      try (apply h2); auto.

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
    { eapply eqorceq_cequivc; eauto. }
    { eapply eq_term_equals_trans;[eauto|].
      unfold per_aeq_eq; split; intro q; exrepnd; dands; auto.
      - apply (eq_ts_cequivc lib a b a' b' eqa); auto.
      - apply (eq_ts_cequivc lib a' b' a b eqa); auto; apply cequivc_sym; auto. }

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    unfold per_aeq_eq in e; unfold per_aeq_eq; exrepnd.
    dts_props props uv tv te tes tet tev.
    dands; auto.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    unfold per_aeq_eq in e1, e2; unfold per_aeq_eq; exrepnd.
    dts_props props uv tv te tes tet tev.
    ccomputes_to_eqval.
    dands; spcast; auto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff.
    unfold per_aeq_eq in e; unfold per_aeq_eq; exrepnd.
    ccomputes_to_eqval.
    eapply cequivc_axiom in c;[|eauto]; exrepnd.
    dts_props props uv tv te tes tet tev.
    dands; spcast; auto.
Qed.
