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
Lemma per_approx_uniquely_valued {p} :
  forall lib (ts : cts(p)), uniquely_valued (per_approx lib ts).
Proof.
  unfold uniquely_valued, per_approx, eq_term_equals; sp.
  ccomputes_to_eqval.
  allrw; sp.
Qed.

Lemma per_approx_type_extensionality {p} :
  forall lib (ts : cts(p)), type_extensionality (per_approx lib ts).
Proof.
  unfold type_extensionality, per_approx, eq_term_equals; sp.
  exists a b c d; sp.
  allrw <-; sp.
Qed.

Lemma per_approx_type_symmetric {p} :
  forall lib (ts : cts(p)), type_symmetric (per_approx lib ts).
Proof.
  unfold type_symmetric, per_approx; sp.
  exists c d a b; sp.
  symm; auto.
  allrw; sp.
Qed.

Lemma per_approx_type_transitive {p} :
  forall lib (ts : cts(p)), type_transitive (per_approx lib ts).
Proof.
  unfold type_transitive, per_approx; sp.
  ccomputes_to_eqval.
  exists a0 b0 c d; sp; spcast; sp.
  allrw; sp.
Qed.

Lemma per_approx_type_value_respecting {p} :
  forall lib (ts : cts(p)), type_value_respecting lib (per_approx lib ts).
Proof.
  sp; unfold type_value_respecting, per_approx; sp.
  ccomputes_to_eqval.
  dupcomp T Hcompt.
  apply cequivc_mkc_approx with (t' := T') in Hcompt; sp.
  exists a b a' b'; sp; spcast; sp.
  split; sp; spcast.
  apply @approxc_cequivc_trans with (b := b); auto.
  apply @cequivc_approxc_trans with (b := a); auto.
  apply cequivc_sym; auto.
  apply @approxc_cequivc_trans with (b := b'); auto.
  apply @cequivc_approxc_trans with (b := a'); auto.
  apply cequivc_sym; auto.
Qed.

Lemma per_approx_term_symmetric {p} :
  forall lib (ts : cts(p)), term_symmetric (per_approx lib ts).
Proof.
  unfold term_symmetric, term_equality_symmetric, per_approx.
  introv cts i e.
  exrepnd.
  allrw; discover; sp.
Qed.

Lemma per_approx_term_transitive {p} :
  forall lib (ts : cts(p)), term_transitive (per_approx lib ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_approx.
  introv cts i e1 e2.
  exrepnd.
  allrw; discover; sp.
Qed.

Lemma per_approx_term_value_respecting {p} :
  forall lib (ts : cts(p)), term_value_respecting lib (per_approx lib ts).
Proof.
  sp; unfold term_value_respecting, term_equality_respecting, per_approx.
  introv i e c; exrepnd.
  ccomputes_to_eqval.
  allrw; discover; sp.
  spcast; apply @cequivc_axiom with (t' := t') in c; sp.
Qed.

Lemma per_approx_type_system {p} :
  forall lib (ts : cts(p)), type_system lib (per_approx lib ts).
Proof.
  intros; unfold type_system; sp.
  try apply per_approx_uniquely_valued; auto.
  try apply per_approx_type_extensionality; auto.
  try apply per_approx_type_symmetric; auto.
  try apply per_approx_type_transitive; auto.
  try apply per_approx_type_value_respecting; auto.
  try apply per_approx_term_symmetric; auto.
  try apply per_approx_term_transitive; auto.
  try apply per_approx_term_value_respecting; auto.
Qed.
 *)

(* !!MOVE *)
Lemma cequivc_implies_approxc {o} :
  forall lib (a b : @CTerm o),
    cequivc lib a b -> (approxc lib a b # approxc lib b a).
Proof.
  introv ceq.
  unfold cequivc in ceq.
  destruct ceq.
  dands; auto.
Qed.

Lemma close_type_system_approx {p} :
  forall lib (ts : cts(p)) T eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> per_approx lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou per.
  unfold per_approx in per; exrepnd; spcast.

  prove_ts_props Case.

  + SCase "uniquely_valued".
    introv cl.
    eapply eq_term_equals_trans;[eauto|].
    dest_close_lr h.
    onedts uv tye tyvr tes tet tevr.
    unfold per_approx in h; exrepnd.
    ccomputes_to_eqval.
    apply eq_term_equals_sym; auto.

  + SCase "type_extensionality".
    introv eqt.
    apply CL_approx.
    exists a b; dands; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  + SCase "type_value_respecting".
    introv ceq.
    apply CL_approx.
    eapply cequivc_mkc_approx in ceq;[|eauto]; exrepnd.
    exists a' b'; dands; spcast; auto.
    eapply eq_term_equals_trans;[eauto|].
    apply cequivc_implies_approxc in ceq1.
    apply cequivc_implies_approxc in ceq2.
    repnd.
    split; introv h; spcast;
      eapply approxc_trans; eauto;
        eapply approxc_trans; eauto.

  + SCase "term_symmetric".
    introv e.
    apply per1 in e; apply per1; clear per1; auto.

  + SCase "term_transitive".
    introv e1 e2.
    apply per1 in e1; apply per1 in e2; apply per1; clear per1; auto.

  + SCase "term_value_respecting".
    introv e c; spcast.
    apply per1 in e; apply per1; clear per1; auto.
Qed.
