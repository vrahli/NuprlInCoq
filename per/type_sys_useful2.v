(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


  Website: http://nuprl.org/html/verification/
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

Lemma type_sys_props_uv {p} :
  forall lib (ts : cts(p)) A B eq eq',
    type_sys_props lib ts A B eq
    -> eq_term_equals eq eq'
    -> type_sys_props lib ts A B eq'.
Proof.
  introv tsp eqt.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt tymt.
  prove_type_sys_props Case.

  - Case "uniquely_valued".
    introv e.
    apply uv in e.
    apply eq_term_equals_trans with (eq2 := eq); sp.
    apply eq_term_equals_sym; sp.

  - Case "type_symmetric".
    introv e1 e2 e3.
    generalize (tys T T3 eq'0); introv k.
    repeat (dest_imp k hyp).
    generalize (tyt A eq); introv j; repeat (dest_imp j hyp); repnd.
    apply tygs; sp.
    generalize (tyst B eq); introv u; repeat (dest_imp u hyp); repnd.
    repdors; subst.
    generalize (tymt A A T3 eq eq'); sp.
    generalize (tymt B B T3 eq eq'); sp.
    apply eq_term_equals_trans with (eq2 := eq'); sp.

  - Case "type_transitive".
    introv e1.
    generalize (tyt T3 eq'0); introv k; dest_imp k hyp.

  - Case "type_stransitive".
    introv e.
    generalize (tyst T3 eq'0); introv k; dest_imp k hyp.

  - Case "type_value_respecting".
    introv e c.
    generalize (tyvr T T3); introv k; dest_imp k hyp.

  - Case "term_symmetric".
    apply @term_equality_symmetric_eq_term_equals with (eq := eq); sp.

  - Case "term_transitive".
    apply @term_equality_transitive_eq_term_equals with (eq := eq); sp.

  - Case "term_value_respecting".
    apply @term_equality_respecting_eq_term_equals with (eq := eq); sp.

  - Case "type_gsymmetric".
    introv e.
    generalize (tygs T T3 eq'0); sp.

  - Case "type_gtransitive".
    sp.

  - Case "type_mtransitive".
    introv e1 e2 e3.
    generalize (tymt T T3 T4 eq1 eq2); sp.
Qed.

Lemma type_sys_props_implies_term_eq_sym {p} :
  forall lib (ts : cts(p)) P P' eqp,
    type_sys_props lib ts P P' eqp
    -> term_equality_symmetric eqp.
Proof.
  intros; onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1; sp.
Qed.

Lemma type_sys_props_implies_term_eq_trans {p} :
  forall lib (ts : cts(p)) P P' eqp,
    type_sys_props lib ts P P' eqp
    -> term_equality_transitive eqp.
Proof.
  intros; onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1; sp.
Qed.
