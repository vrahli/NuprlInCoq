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


(*
Lemma per_base_uniquely_valued {p} :
  forall lib (ts : cts(p)), uniquely_valued (per_base lib ts).
Proof.
  unfold uniquely_valued, per_base, eq_term_equals; sp.
  allrw; sp.
Qed.

Lemma per_base_type_extensionality {p} :
  forall lib (ts : cts(p)), type_extensionality (per_base lib ts).
Proof.
  unfold type_extensionality, per_base, eq_term_equals; sp.
  allrw <-; sp.
Qed.

Lemma per_base_type_symmetric {p} :
  forall lib (ts : cts(p)), type_symmetric (per_base lib ts).
Proof.
  unfold type_symmetric, per_base; sp.
Qed.

Lemma per_base_type_transitive {p} :
  forall lib (ts : cts(p)), type_transitive (per_base lib ts).
Proof.
  unfold type_transitive, per_base; sp.
Qed.

Lemma per_base_type_value_respecting {p} :
  forall lib (ts : cts(p)), type_value_respecting lib (per_base lib ts).
Proof.
  sp; unfold type_value_respecting, per_base; sp.
  spcast; apply cequivc_base with (t := T); auto.
Qed.

Lemma per_base_term_symmetric {p} :
  forall lib (ts : cts(p)), term_symmetric (per_base lib ts).
Proof.
  unfold term_symmetric, term_equality_symmetric, per_base.
  introv cts i e.
  destruct i as [ ct i ].
  destruct i as [ ct' i ].
  rw i in e; rw i.
  spcast; apply cequivc_sym; auto.
Qed.

Lemma per_base_term_transitive {p} :
  forall lib (ts : cts(p)), term_transitive (per_base lib ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_base.
  introv cts i e1 e2.
  destruct i as [ ct i ].
  destruct i as [ ct' i ].
  rw i in e1; rw i in e2; rw i.
  spcast; apply cequivc_trans with (b := t2); auto.
Qed.

Lemma per_base_term_value_respecting {p} :
  forall lib (ts : cts(p)), term_value_respecting lib (per_base lib ts).
Proof.
  sp; unfold term_value_respecting, term_equality_respecting, per_base; sp.
  allrw; sp.
Qed.

Lemma per_base_type_system {p} :
  forall lib (ts : cts(p)), type_system lib (per_base lib ts).
Proof.
  intros; unfold type_system; sp.
  try apply per_base_uniquely_valued; auto.
  try apply per_base_type_extensionality; auto.
  try apply per_base_type_symmetric; auto.
  try apply per_base_type_transitive; auto.
  try apply per_base_type_value_respecting; auto.
  try apply per_base_term_symmetric; auto.
  try apply per_base_term_transitive; auto.
  try apply per_base_term_value_respecting; auto.
Qed.
*)


Lemma close_type_system_base {p} :
  forall lib (ts : cts(p)) T eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> per_base lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou per.
  unfold per_base in per; repnd; spcast.

  prove_ts_props Case.

  + SCase "uniquely_valued".
    introv cl.
    eapply eq_term_equals_trans;[eauto|].
    dest_close_lr h.
    onedts uv tye tyvr tes tet tevr.
    unfold per_base in h; repnd.
    apply eq_term_equals_sym; auto.

  + SCase "type_extensionality".
    introv eqt.
    apply CL_base.
    split; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  + SCase "type_value_respecting".
    introv ceq.
    apply CL_base.
    apply cequivc_base in ceq; auto.
    split; spcast; auto.

  + SCase "term_symmetric".
    introv e.
    apply per in e; apply per; clear per.
    spcast; apply cequivc_sym; auto.

  + SCase "term_transitive".
    introv e1 e2.
    apply per in e1; apply per in e2; apply per; clear per.
    spcast; eapply cequivc_trans; eauto.

  + SCase "term_value_respecting".
    introv e c; spcast.
    apply per in e; apply per; clear per.
    spcast; auto.
Qed.
