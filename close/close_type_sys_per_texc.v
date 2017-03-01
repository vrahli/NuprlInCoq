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



Lemma eq_term_equals_per_texc_eq_if {p} :
  forall lib (eqn1 eqn2 eqe1 eqe2 : per(p)),
    eqn1 <=2=> eqn2
    -> eqe1 <=2=> eqe2
    -> (per_texc_eq lib eqn1 eqe1) <=2=> (per_texc_eq lib eqn2 eqe2).
Proof.
  introv eqtn eqte.
  unfold per_texc_eq; split; intro h; exrepnd;
    eexists; eexists; eexists; eexists; dands;
      try (exact h0); try (exact h2); auto;
        try (complete (apply eqtn; auto));
        try (complete (apply eqte; auto)).
Qed.

Lemma per_texc_eq_symmetric {p} :
  forall lib (eqn eqe : per(p)) t1 t2,
    term_equality_symmetric eqn
    -> term_equality_symmetric eqe
    -> per_texc_eq lib eqn eqe t1 t2
    -> per_texc_eq lib eqn eqe t2 t1.
Proof.
  unfold per_texc_eq.
  introv tesn tese h; repdors; exrepnd; tcsp.
  exists n2 n1 e2 e1; dands; auto.
Qed.

Lemma per_texc_eq_transitive {p} :
  forall lib (eqn eqe : per(p)) t1 t2 t3,
    term_equality_transitive eqn
    -> term_equality_transitive eqe
    -> per_texc_eq lib eqn eqe t1 t2
    -> per_texc_eq lib eqn eqe t2 t3
    -> per_texc_eq lib eqn eqe t1 t3.
Proof.
  unfold per_texc_eq.
  introv tetn tete per1 per2; repdors; exrepnd; ccomputes_to_eqval; tcsp.
  exists n0 n2 e0 e2; dands; spcast; auto.
  - eapply tetn; eauto.
  - eapply tete; eauto.
Qed.

Lemma per_texc_eq_cequiv {p} :
  forall lib (eqn eqe : per(p)) t1 t2,
    term_equality_respecting lib eqn
    -> term_equality_respecting lib eqe
    -> cequivc lib t1 t2
    -> per_texc_eq lib eqn eqe t1 t1
    -> per_texc_eq lib eqn eqe t1 t2.
Proof.
  unfold per_texc_eq.
  introv resn rese ceq per; repdors; exrepnd.
  ccomputes_to_eqval.
  dup per0 as comp.
  eapply cequivc_mkc_exception in comp;[|exact ceq]; exrepnd.
  exists n1 a' e1 b'; dands; spcast; auto.
  - eapply resn; spcast; auto.
  - eapply rese; spcast; auto.
Qed.

Lemma close_type_system_texc {p} :
  forall lib (ts : cts(p)) T (eq : per) A B eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_texc A B)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> close lib ts B eqb
    -> type_system_props lib (close lib ts) B eqb
    -> eq <=2=> (per_texc_eq lib eqa eqb)
    -> per_texc lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa clb tsb eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_texc in h; exrepnd; spcast.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    apply eq_term_equals_per_texc_eq_if; auto.

    { dts_props tsa uv tv te tes tet tev.
      eapply uv; auto. }

    { dts_props tsb uv tv te tes tet tev.
      eapply uv; auto. }

  - SCase "type_extensionality".
    introv eqt.
    apply CL_texc.
    exists eqa eqb A B; dands; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_texc.
    eapply cequivc_mkc_texc in comp;[|eauto]; exrepnd.
    exists eqa eqb a' b'; dands; spcast; auto.
    { dts_props tsa uv tv te tes tet tev; tcsp. }
    { dts_props tsb uv tv te tes tet tev; tcsp. }

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    eapply per_texc_eq_symmetric; eauto.
    { dts_props tsa uv tv te tes tet tev; tcsp. }
    { dts_props tsb uv tv te tes tet tev; tcsp. }

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    eapply per_texc_eq_transitive; eauto.
    { dts_props tsa uv tv te tes tet tev; tcsp. }
    { dts_props tsb uv tv te tes tet tev; tcsp. }

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff; clear eqiff.
    eapply per_texc_eq_cequiv; eauto.
    { dts_props tsa uv tv te tes tet tev; tcsp. }
    { dts_props tsb uv tv te tes tet tev; tcsp. }
Qed.
