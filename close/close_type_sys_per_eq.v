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


Lemma close_type_system_eq {o} :
  forall lib (ts : cts(o)) T eq A a b eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_equality a b A)
    -> close lib ts A eqa
    -> (eq <=2=> (per_eq_eq lib a b eqa))
    -> per_eq lib (close lib ts) T eq
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
    unfold per_eq in h; exrepnd; spcast.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
    dts_props props uv tv te tes tet tev.
    eapply uv in h2.
    unfold per_eq_eq; split; introv q; exrepnd; exists x1 x2 y1 y2; dands; auto;
      try (apply h2); auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_eq.
    exists A a b eqa; dands; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_eq.
    eapply cequivc_mkc_equality in comp;[|eauto]; exrepnd.
    exists T'0 a' b' eqa.

    dts_props props uv tv te tes tet tev.
    dands; spcast; auto.
(*    { eapply eqorceq_cequivc; eauto. }*)
    { eapply eq_term_equals_trans;[eauto|].
      unfold per_eq_eq; split; intro q; exrepnd; exists x1 x2 y1 y2; dands; auto.
      - apply (eq_ts_cequivc lib a b a' b' eqa); auto.
      - apply (eq_ts_cequivc lib a x1 a' x1 eqa); auto.
      - apply (eq_ts_cequivc lib b x2 b' x2 eqa); auto.
      - apply (eq_ts_cequivc lib a' b' a b eqa); auto; apply cequivc_sym; auto.
      - apply (eq_ts_cequivc lib a' x1 a x1 eqa); auto; apply cequivc_sym; auto.
      - apply (eq_ts_cequivc lib b' x2 b x2 eqa); auto; apply cequivc_sym; auto. }

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    unfold per_eq_eq in e; unfold per_eq_eq; exrepnd.
    dts_props props uv tv te tes tet tev.
    exists x2 x1 y2 y1; dands; auto.
    { eapply tet; eauto. }
    { eapply tet; eauto. }

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    unfold per_eq_eq in e1, e2; unfold per_eq_eq; exrepnd.
    dts_props props uv tv te tes tet tev.
    ccomputes_to_eqval.
    exists x0 x2 y0 y2; dands; spcast; auto.
    eapply tet;[eauto|]; eauto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff.
    unfold per_eq_eq in e; unfold per_eq_eq; exrepnd.
    ccomputes_to_eqval.
    eapply cequivc_mkc_prefl in c;[|eauto]; exrepnd.
    dts_props props uv tv te tes tet tev.
    exists x1 c0 y1 d; dands; spcast; auto.
    { apply (eq_ts_cequivc lib b x1 b c0 eqa); auto. }
    { eapply eq_ts_cequivc; try (exact c2); try (apply cequivc_refl); auto. }
Qed.
