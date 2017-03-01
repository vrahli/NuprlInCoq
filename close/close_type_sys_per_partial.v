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


Lemma eq_term_equals_per_partial_eq_if {p} :
  forall lib (eqa1 eqa2 : per(p)),
    eqa1 <=2=> eqa2
    -> (per_partial_eq lib eqa1) <=2=> (per_partial_eq lib eqa2).
Proof.
  introv eqt.
  unfold per_partial_eq; introv; split; intro k; repnd;
  dands; auto; intro hv; autodimp k hyp.
  allrw <-; sp.
  allrw; sp.
Qed.

Lemma per_partial_eq_symmetric {p} :
  forall lib (eq : per(p)) t1 t2,
    term_equality_symmetric eq
    -> per_partial_eq lib eq t1 t2
    -> per_partial_eq lib eq t2 t1.
Proof.
  introv tes per.
  allunfold @per_partial_eq; exrepnd; dands; allrw; try (complete sp).
  introv hv.
  rw <- per0 in hv; sp.
Qed.

Lemma per_partial_eq_transitive {p} :
  forall lib (eq : per(p)) t1 t2 t3,
    term_equality_transitive eq
    -> per_partial_eq lib eq t1 t2
    -> per_partial_eq lib eq t2 t3
    -> per_partial_eq lib eq t1 t3.
Proof.
  introv tet per1 per2.
  allunfold @per_partial_eq; exrepnd.
  dands; try (allrw; complete sp).
  introv hv.
  dup hv as hv2.
  rw per3 in hv2.
  dup hv2 as hv3.
  rw per0 in hv3.
  autodimp per2 hyp.
  autodimp per1 hyp.
  apply tet with (t2 := t2); sp.
Qed.

Lemma per_partial_eq_cequiv {p} :
  forall lib (eq : per(p)) t1 t2,
    term_equality_respecting lib eq
    -> cequivc lib t1 t2
    -> per_partial_eq lib eq t1 t1
    -> per_partial_eq lib eq t1 t2.
Proof.
  introv res ceq per.
  allunfold @per_partial_eq; repnd; dands.

  split; intro k; spcast.
  apply @hasvaluec_cequivc with (t1 := t1); sp.
  apply @hasvaluec_cequivc with (t1 := t2); sp.
  apply cequivc_sym; sp.

  introv h.
  autodimp per hyp;
  try(apply res; sp; spcast; sp).
Qed.


Lemma close_type_system_partial {p} :
  forall lib (ts : cts(p)) T (eq : per) A eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_partial A)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> (forall a, eqa a a -> chaltsc lib a)
    -> eq <=2=> (per_partial_eq lib eqa)
    -> per_partial lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa hv eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_partial in h; exrepnd; spcast.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    apply eq_term_equals_per_partial_eq_if; auto.

    dts_props tsa uv tv te tes tet tev.
    eapply uv; auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_partial.
    exists A eqa; dands; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_partial.
    eapply cequivc_mkc_partial in comp;[|eauto]; exrepnd.
    exists b eqa; dands; spcast; auto.
    dts_props tsa uv tv te tes tet tev; tcsp.

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    eapply per_partial_eq_symmetric; eauto.
    dts_props tsa uv tv te tes tet tev; tcsp.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    eapply per_partial_eq_transitive; eauto.
    dts_props tsa uv tv te tes tet tev; tcsp.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff; clear eqiff.
    dts_props tsa uva tva tea tesa teta teva; repnd.
    eapply per_partial_eq_cequiv; spcast; eauto.
Qed.
