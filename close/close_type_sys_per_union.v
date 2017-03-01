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



Lemma eq_term_equals_per_union_eq_if {p} :
  forall lib (eqa1 eqa2 eqb1 eqb2 : per(p)),
    eqa1 <=2=> eqa2
    -> eqb1 <=2=> eqb2
    -> (per_union_eq lib eqa1 eqb1) <=2=> (per_union_eq lib eqa2 eqb2).
Proof.
  introv eqta eqtb.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R;
    introv; split; intro k; repdors; exrepnd.

  - left.
    exists x y; sp.
    apply eqta; sp.

  - right.
    exists x y; sp.
    apply eqtb; sp.

  - left.
    exists x y; sp.
    apply eqta; sp.

  - right.
    exists x y; sp.
    apply eqtb; sp.
Qed.

Lemma per_union_eq_symmetric {p} :
  forall lib (eqa eqb : per(p)) t1 t2,
    term_equality_symmetric eqa
    -> term_equality_symmetric eqb
    -> per_union_eq lib eqa eqb t1 t2
    -> per_union_eq lib eqa eqb t2 t1.
Proof.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R.
  introv tesa tesb per; repdors; exrepnd.

  - left.
    exists y x; sp.

  - right.
    exists y x; sp.
Qed.

Lemma per_union_eq_transitive {p} :
  forall lib (eqa eqb : per(p)) t1 t2 t3,
    term_equality_transitive eqa
    -> term_equality_transitive eqb
    -> per_union_eq lib eqa eqb t1 t2
    -> per_union_eq lib eqa eqb t2 t3
    -> per_union_eq lib eqa eqb t1 t3.
Proof.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R.
  introv teta tetb per1 per2; repdors; exrepnd; ccomputes_to_eqval.

  - left.
    exists x0 y; sp; spcast; sp.
    apply teta with (t2 := y0); sp.

  - right.
    exists x0 y; sp; spcast; sp.
    apply tetb with (t2 := y0); sp.
Qed.

Lemma per_union_eq_cequiv {p} :
  forall lib (eqa eqb : per(p)) t1 t2,
    term_equality_respecting lib eqa
    -> term_equality_respecting lib eqb
    -> term_equality_symmetric eqa
    -> term_equality_symmetric eqb
    -> term_equality_transitive eqa
    -> term_equality_transitive eqb
    -> cequivc lib t1 t2
    -> per_union_eq lib eqa eqb t1 t1
    -> per_union_eq lib eqa eqb t1 t2.
Proof.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R.
  introv resa resb syma symb tra trb ceq per; repdors; exrepnd.

  - left; spcast.
    generalize (cequivc_mkc_inl lib t1 t2 x); introv k;
      repeat (autodimp k hyp); exrepnd.
    exists x b; sp; spcast; sp.
    apply resa; spcast; sp.
    apply tra with (t2 := y); sp.

  - right; spcast.
    generalize (cequivc_mkc_inr lib t1 t2 x); introv k;
      repeat (autodimp k hyp); exrepnd.
    exists x b; sp; spcast; sp.
    apply resb; spcast; sp.
    apply trb with (t2 := y); sp.
Qed.


Lemma close_type_system_union {p} :
  forall lib (ts : cts(p)) T (eq : per) A B eqa eqb,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_union A B)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> close lib ts B eqb
    -> type_system_props lib (close lib ts) B eqb
    -> eq <=2=> (per_union_eq lib eqa eqb)
    -> per_union lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa clb tsb eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_union in h; exrepnd; spcast.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    apply eq_term_equals_per_union_eq_if; auto.

    { dts_props tsa uv tv te tes tet tev.
      eapply uv; auto. }

    { dts_props tsb uv tv te tes tet tev.
      eapply uv; auto. }

  - SCase "type_extensionality".
    introv eqt.
    apply CL_union.
    exists eqa eqb A B; dands; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_union.
    eapply cequivc_mkc_union in comp;[|eauto]; exrepnd.
    exists eqa eqb a' b'; dands; spcast; auto.
    { dts_props tsa uv tv te tes tet tev; tcsp. }
    { dts_props tsb uv tv te tes tet tev; tcsp. }

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    eapply per_union_eq_symmetric; eauto.
    { dts_props tsa uv tv te tes tet tev; tcsp. }
    { dts_props tsb uv tv te tes tet tev; tcsp. }

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    eapply per_union_eq_transitive; eauto.
    { dts_props tsa uv tv te tes tet tev; tcsp. }
    { dts_props tsb uv tv te tes tet tev; tcsp. }

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff; clear eqiff.
    dts_props tsa uva tva tea tesa teta teva; repnd.
    dts_props tsb uvb tvb teb tesb tetb tevb; repnd.
    eapply per_union_eq_cequiv; eauto.
Qed.
