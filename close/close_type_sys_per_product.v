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



Lemma per_product_eq_preserves_eq_term_equals {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2 t1 t2,
    term_equality_symmetric eqa1
    -> term_equality_transitive eqa1
    -> (eqa1 <=2=> eqa2)
    -> (forall a1 a2, eqa1 a1 a2 -> (eqb1 a1) <=2=> (eqb2 a2))
    -> per_product_eq lib eqa1 eqb1 t1 t2
    -> per_product_eq lib eqa2 eqb2 t1 t2.
Proof.
  introv syma trana eqta eqtb peq.
  allunfold @per_product_eq; exrepnd.
  assert (eqa2 a a') as e' by (rw <- eqta; sp).
  exists a a' b b'; sp.
  eapply eqtb;[|eauto].
  eapply trana; eauto.
Qed.

Lemma per_product_eq_term_equals {p} :
  forall lib (eqa1 eqa2 : per(p)) eqb1 eqb2,
    term_equality_symmetric eqa1
    -> term_equality_transitive eqa1
    -> (eqa1 <=2=> eqa2)
    -> (forall a1 a2, eqa1 a1 a2 -> (eqb1 a1) <=2=> (eqb2 a2))
    -> (per_product_eq lib eqa1 eqb1) <=2=> (per_product_eq lib eqa2 eqb2).
Proof.
  introv syma trana eqta eqtb.
  split; intro xx;
    eapply per_product_eq_preserves_eq_term_equals;
    try (exact xx); auto.
  { introv h; apply eqta in h; apply eqta; auto. }
  { introv h1 h2; apply eqta in h1; apply eqta in h2; apply eqta; eapply trana; eauto. }
  { apply eq_term_equals_sym; auto. }
  { introv e; apply eq_term_equals_sym; apply eqtb; apply eqta in e; auto. }
Qed.

Lemma per_product_eq_sym {p} :
  forall lib (eqa : per(p)) eqb t1 t2,
    term_equality_symmetric eqa
    -> (forall a1 a2, eqa a1 a2 -> term_equality_symmetric (eqb a1))
    -> (forall a1 a2, eqa a1 a2 -> (eqb a1) <=2=> (eqb a2))
    -> per_product_eq lib eqa eqb t1 t2
    -> per_product_eq lib eqa eqb t2 t1.
Proof.
  introv syma symb symb2 peq.
  allunfold @per_product_eq; exrepnd.
  assert (eqa a' a) as e' by (apply syma; sp).
  exists a' a b' b; sp.
  eapply symb; eauto.
  eapply symb2; eauto.
Qed.

Lemma per_product_eq_trans {p} :
  forall lib (eqa : per(p)) eqb t1 t2 t3,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall a1 a2, eqa a1 a2 -> term_equality_transitive (eqb a1))
    -> (forall a1 a2, eqa a1 a2 -> (eqb a1) <=2=> (eqb a2))
    -> per_product_eq lib eqa eqb t1 t2
    -> per_product_eq lib eqa eqb t2 t3
    -> per_product_eq lib eqa eqb t1 t3.
Proof.
  introv syma trana trb eqbs peq1 peq2.
  allunfold @per_product_eq; exrepnd.
  spcast; computes_to_eqval.
  eexists; eexists; eexists; eexists; dands; spcast; eauto.
  eapply trb; eauto.
  eapply eqbs; eauto.
Qed.

Lemma per_product_eq_cequivc {p} :
  forall lib (eqa : per(p)) eqb t1 t2,
    term_equality_respecting lib eqa
    -> (forall a1 a2, eqa a1 a2 -> term_equality_respecting lib (eqb a1))
    -> (forall a1 a2, eqa a1 a2 -> (eqb a1) <=2=> (eqb a2))
    -> cequivc lib t1 t2
    -> per_product_eq lib eqa eqb t1 t1
    -> per_product_eq lib eqa eqb t1 t2.
Proof.
  introv respa trb eqbs ceq peq.
  allunfold @per_product_eq; exrepnd.
  spcast; computes_to_eqval.
  eapply cequivc_mkc_pair in ceq;[|eauto];exrepnd.

  eexists; eexists; eexists; eexists; dands; spcast; eauto.
  { apply respa; spcast; auto. }
  { eapply trb; spcast; eauto. }
Qed.

Lemma close_type_system_product {p} :
  forall lib (ts : cts(p)) T (eq : per) A v B eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_product A v B)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> (forall (a a' : CTerm) (e : eqa a a'), close lib ts (substc a v B) (eqb a))
    -> (forall (a a' : CTerm) (e : eqa a a'),
           type_system_props lib (close lib ts) (substc a v B) (eqb a))
    -> (forall (a a' : CTerm) (e : eqa a a'), (eqb a) <=2=> (eqb a'))
    -> eq <=2=> (per_product_eq lib eqa eqb)
    -> per_product lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa clb tsb eqbiff eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_product in h; exrepnd; spcast.
    unfold type_family in h0; exrepnd.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    dts_props tsa uv tv te tes tet tev.
    apply uv in h3.

    pose proof (eqbs_trans lib (close lib ts) v B eqa eqa0 eqb eqb0) as q.
    repeat (autodimp q hyp).

    apply per_product_eq_term_equals; auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_product.
    exists eqa eqb; dands; auto.
    { exists A v B; dands; spcast; auto.
      introv e; dands; tcsp.
      eapply clb; eauto. }
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_product.
    eapply cequivc_mkc_product in comp;[|eauto]; exrepnd.
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
    eapply per_product_eq_sym; eauto.

    introv xx; apply tsb in xx.
    dts_props xx uv2 tv2 te2 tes2 tet2 tev2; auto.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply per_product_eq_trans; eauto.

    introv xx; apply tsb in xx.
    dts_props xx uv2 tv2 te2 tes2 tet2 tev2; auto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff.
    dts_props tsa uv tv te tes tet tev.
    eapply per_product_eq_cequivc; eauto.

    introv xx; apply tsb in xx.
    dts_props xx uv2 tv2 te2 tes2 tet2 tev2; auto.
Qed.
