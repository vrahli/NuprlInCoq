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


Lemma term_equality_symmetric_eq_term_equals {p} :
  forall eq eq' : per(p),
    term_equality_symmetric eq
    -> eq_term_equals eq eq'
    -> term_equality_symmetric eq'.
Proof.
  introv tes eqt.
  unfold term_equality_symmetric; introv.
  allrw <- eqt; sp.
Qed.

Lemma term_equality_transitive_eq_term_equals {p} :
  forall eq eq' : per(p),
    term_equality_transitive eq
    -> eq_term_equals eq eq'
    -> term_equality_transitive eq'.
Proof.
  introv tet eqt.
  unfold term_equality_transitive; introv.
  allrw <- eqt; sp.
  apply tet with (t2 := t2); sp.
Qed.

Lemma term_equality_respecting_eq_term_equals {p} :
  forall lib (eq eq' : per(p)),
    term_equality_respecting lib eq
    -> eq_term_equals eq eq'
    -> term_equality_respecting lib eq'.
Proof.
  introv ter eqt.
  unfold term_equality_respecting; introv.
  allrw <- eqt; sp.
Qed.

(*
Lemma type_system_props_uv {p} :
  forall lib (ts : cts(p)) A B eq eq',
    type_system_props lib ts A B eq
    -> (eq <=2=> eq')
    -> type_system_props lib ts A B eq'.
Proof.
  introv tsp eqt.
  dts_props tsp uv tv te tes tet tev.

  prove_ts_props Case.

  - Case "uniquely_valued".
    introv tsa.
    eapply uv in tsa.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "type_extensionality".
    introv e.
    apply tv.
    eapply eq_term_equals_trans; eauto.

  - Case "type_value_respecting".
    introv c.
    apply te in c.

    (* ARG! *)
Abort.
*)

Lemma type_system_props_implies_term_eq_sym {p} :
  forall lib (ts : cts(p)) A B eqp,
    type_system_props lib ts A B eqp
    -> term_equality_symmetric eqp.
Proof.
  introv tsp.
  dts_props tsp uv te tys tyt tv tes tet tev; auto.
Qed.

Lemma type_system_props_implies_term_eq_trans {p} :
  forall lib (ts : cts(p)) A B eqp,
    type_system_props lib ts A B eqp
    -> term_equality_transitive eqp.
Proof.
  introv tsp.
  dts_props tsp uv te tys tyt tv tes tet tev; auto.
Qed.
