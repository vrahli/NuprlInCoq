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



Lemma eq_term_equals_per_image_eq_if {p} :
  forall lib (eqa1 eqa2 : per(p)) f1 f2,
    cequivc lib f1 f2
    -> eqa1 <=2=> eqa2
    -> (per_image_eq lib eqa1 f1) <=2=> (per_image_eq lib eqa2 f2).
Proof.
  introv ceq eqt.
  introv; split; intro k; induction k.

  - apply @image_eq_cl with (t := t); sp.

  - apply @image_eq_eq with (a1 := a1) (a2 := a2); sp; spcast.
    apply eqt; sp.
    apply cequivc_trans with (b := mkc_apply f1 a1); auto.
    apply sp_implies_cequivc_apply; sp.
    apply cequivc_trans with (b := mkc_apply f1 a2); auto.
    apply sp_implies_cequivc_apply; sp.

  - apply @image_eq_cl with (t := t); sp.

  - apply @image_eq_eq with (a1 := a1) (a2 := a2); sp; spcast.
    apply eqt; sp.
    apply cequivc_trans with (b := mkc_apply f2 a1); auto.
    apply sp_implies_cequivc_apply; sp; apply cequivc_sym; sp.
    apply cequivc_trans with (b := mkc_apply f2 a2); auto.
    apply sp_implies_cequivc_apply; sp; apply cequivc_sym; sp.
Qed.

Lemma per_image_eq_sym {p} :
  forall lib (eqa : per(p)) f t1 t2,
    term_equality_symmetric eqa
    -> per_image_eq lib eqa f t1 t2
    -> per_image_eq lib eqa f t2 t1.
Proof.
  introv tes per.
  induction per.
  apply @image_eq_cl with (t := t); sp.
  apply @image_eq_eq with (a1 := a2) (a2 := a1); sp.
Qed.

Lemma per_image_eq_trans {p} :
  forall lib (eqa : per(p)) f t1 t2 t3,
    term_equality_transitive eqa
    -> per_image_eq lib eqa f t1 t2
    -> per_image_eq lib eqa f t2 t3
    -> per_image_eq lib eqa f t1 t3.
Proof.
  introv tet per1 per2.
  apply image_eq_cl with (t := t2); sp.
Qed.

Lemma per_image_eq_cequiv {p} :
  forall lib (eqa : per(p)) f t t',
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> t ~=~(lib) t'
    -> per_image_eq lib eqa f t t
    -> per_image_eq lib eqa f t t'.
Proof.
  introv tes tet ceq per.
  revert_dependents t'.
  induction per; introv ceq.
  apply IHper2; auto.
  apply @image_eq_eq with (a1 := a2) (a2 := a2); sp.
  apply tet with (t2 := a1); sp.
  spcast.
  apply cequivc_trans with (b := t2); sp.
  apply cequivc_sym; sp.
Qed.

Lemma close_type_system_image {p} :
  forall lib (ts : cts(p)) T (eq : per) A f eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_image A f)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> eq <=2=> (per_image_eq lib eqa f)
    -> per_image lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_image in h; exrepnd; spcast.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    apply eq_term_equals_per_image_eq_if; auto.

    dts_props tsa uv tv te tes tet tev.
    eapply uv; auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_image.
    exists eqa A f; dands; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_image.
    eapply cequivc_mkc_image in comp;[|eauto]; exrepnd.
    exists eqa a' b'; dands; spcast; auto.
    { dts_props tsa uv tv te tes tet tev; tcsp. }
    { eapply eq_term_equals_trans;[eauto|].
      apply eq_term_equals_per_image_eq_if; auto. }

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    eapply per_image_eq_sym; eauto.
    dts_props tsa uv tv te tes tet tev; tcsp.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    eapply per_image_eq_trans; eauto.
    dts_props tsa uv tv te tes tet tev; tcsp.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff; clear eqiff.
    dts_props tsa uva tva tea tesa teta teva; repnd.
    eapply per_image_eq_cequiv; spcast; eauto.
Qed.
