(*

  Copyright 2014 Cornell University

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


Require Export type_sys.
Require Import dest_close.

(*
Lemma per_uatom_uniquely_valued {p} :
  forall lib (ts : cts(p)), uniquely_valued (per_uatom lib ts).
Proof.
 unfold uniquely_valued, per_uatom, eq_term_equals; sp.
 allrw; sp.
Qed.

Lemma per_uatom_type_extensionality {p} :
  forall lib (ts : cts(p)), type_extensionality (per_uatom lib ts).
Proof.
  unfold type_extensionality, per_uatom, eq_term_equals; sp.
  allrw <-; sp.
Qed.

Lemma per_uatom_type_symmetric {p} :
  forall lib (ts : cts(p)), type_symmetric (per_uatom lib ts).
Proof.
  unfold type_symmetric, per_uatom; sp.
Qed.

Lemma per_uatom_type_transitive {p} :
  forall lib (ts : cts(p)), type_transitive (per_uatom lib ts).
Proof.
  unfold type_transitive, per_uatom; sp.
Qed.

Lemma per_uatom_type_value_respecting {p} :
  forall lib (ts : cts(p)), type_value_respecting lib (per_uatom lib ts).
Proof.
 sp; unfold type_value_respecting, per_uatom; sp; auto.
 spcast; apply @cequivc_uatom with (T := T); auto.
Qed.

Lemma per_uatom_term_symmetric {p} :
  forall lib (ts : cts(p)), term_symmetric (per_uatom lib ts).
Proof.
  introv; unfold term_symmetric, term_equality_symmetric, per_uatom.
  introv k e; repnd.
  allrw.
  apply k in e.
  allunfold @equality_of_uatom; exrepnd.
  exists u; sp.
Qed.

Lemma per_uatom_term_transitive {p} :
  forall lib (ts : cts(p)), term_transitive (per_uatom lib ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_uatom.
  introv cts i e1 e2.
  destruct i as [ ct i ].
  destruct i as [ ct' i ].
  rw i in e1; rw i in e2; rw i; sp.
  allunfold @equality_of_uatom; exrepnd.
  exists u; sp.
  ccomputes_to_eqval; spcast; sp.
Qed.

Lemma per_uatom_term_value_respecting {p} :
  forall lib (ts : cts(p)), term_value_respecting lib (per_uatom lib ts).
Proof.
  sp; unfold term_value_respecting, term_equality_respecting, per_uatom.
  introv i e c.
  destruct i as [ ct i ].
  destruct i as [ ct' i ].
  rw i in e; rw i; sp.
  allunfold @equality_of_uatom; exrepnd.
  exists u; sp.
  spcast; apply @cequivc_utoken with (T := t); auto.
Qed.

Lemma per_uatom_type_system {p} :
  forall lib (ts : cts(p)), type_system lib (per_uatom lib ts).
Proof.
  intros; unfold type_system; sp.
  try apply per_uatom_uniquely_valued; auto.
  try apply per_uatom_type_extensionality; auto.
  try apply per_uatom_type_symmetric; auto.
  try apply per_uatom_type_transitive; auto.
  try apply per_uatom_type_value_respecting; auto.
  try apply per_uatom_term_symmetric; auto.
  try apply per_uatom_term_transitive; auto.
  try apply per_uatom_term_value_respecting; auto.
Qed.
*)

Lemma close_type_system_uatom {p} :
  forall lib (ts : cts(p)) T eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> per_uatom lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou per.
  unfold per_uatom in per; repnd; spcast.

  prove_ts_props Case.

  + SCase "uniquely_valued".
    introv cl.
    eapply eq_term_equals_trans;[eauto|].
    dest_close_lr h.
    onedts uv tye tyvr tes tet tevr.
    unfold per_uatom in h; repnd.
    apply eq_term_equals_sym; auto.

  + SCase "type_extensionality".
    introv eqt.
    apply CL_uatom.
    split; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  + SCase "type_value_respecting".
    introv ceq.
    apply CL_uatom.
    apply cequivc_uatom in ceq; auto.
    split; spcast; auto.

  + SCase "term_symmetric".
    introv e.
    apply per in e; apply per; clear per.
    unfold equality_of_uatom in *; exrepnd; exists u; auto.

  + SCase "term_transitive".
    introv e1 e2.
    apply per in e1; apply per in e2; apply per; clear per.
    unfold equality_of_uatom in *; exrepnd; exists u; auto.
    ccomputes_to_eqval; dands; spcast; auto.

  + SCase "term_value_respecting".
    introv e c; spcast.
    apply per in e; apply per; clear per.
    unfold equality_of_uatom in *; exrepnd; spcast.
    exists u; dands; spcast; auto.
    eapply cequivc_utoken; eauto.
Qed.
