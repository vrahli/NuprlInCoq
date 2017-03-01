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


Lemma close_type_system_teq {p} :
  forall lib (ts : cts(p)) T (eq : per) A B eqa,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_tequality A B)
    -> close lib ts A eqa
    -> type_system_props lib (close lib ts) A eqa
    -> close lib ts B eqa
    -> type_system_props lib (close lib ts) B eqa
    -> eq <=2=> true_per
    -> per_teq lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp cla tsa clb tsb eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_teq in h; exrepnd; spcast.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
    tcsp.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_teq.
    exists A B eqa; dands; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_teq.
    eapply cequivc_mkc_tequality in comp;[|eauto]; exrepnd.
    exists a' b' eqa.
    dands; spcast; auto.

    { dts_props tsa uv tv te tes tet tev.
      apply te; auto. }
    { dts_props tsb uv tv te tes tet tev.
      apply te; auto. }

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff; tcsp.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff; tcsp.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff; tcsp.
Qed.
