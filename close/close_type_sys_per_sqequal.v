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



Lemma per_cequiv_uniquely_valued {p} :
  forall lib (ts : cts(p)), uniquely_valued (per_cequiv lib ts).
Proof.
  unfold uniquely_valued, per_cequiv, eq_term_equals; sp.
  ccomputes_to_eqval; allrw; sp.
Qed.

Lemma per_cequiv_type_extensionality {p} :
  forall lib (ts : cts(p)), type_extensionality (per_cequiv lib ts).
Proof.
  unfold type_extensionality, per_cequiv, eq_term_equals; sp.
  exists a b c d; sp.
  allrw <-; sp.
Qed.

Lemma per_cequiv_type_symmetric {p} :
  forall lib (ts : cts(p)), type_symmetric (per_cequiv lib ts).
Proof.
  unfold type_symmetric, per_cequiv; sp.
  exists c d a b; sp.
  symm; auto.
  allrw; sp.
Qed.

Lemma per_cequiv_type_transitive {p} :
  forall lib (ts : cts(p)), type_transitive (per_cequiv lib ts).
Proof.
  unfold type_transitive, per_cequiv; sp.
  ccomputes_to_eqval.
  exists a0 b0 c d; sp; spcast; sp.
  allrw; sp.
Qed.

Lemma per_cequiv_type_value_respecting {p} :
  forall lib (ts : cts(p)), type_value_respecting lib (per_cequiv lib ts).
Proof.
  sp; unfold type_value_respecting, per_cequiv; sp.
  ccomputes_to_eqval.
  dupcomp T Hcompt.
  apply cequivcn_mkcn_cequiv with (t' := T') in Hcompt; sp.
  exists a b a' b'; sp; spcast; sp.
  split; sp; spcast.
  apply @cequivcn_trans with (b := b); auto.
  apply @cequivcn_trans with (b := a); auto.
  apply cequivcn_sym; auto.
  apply @cequivcn_trans with (b := b'); auto.
  apply @cequivcn_trans with (b := a'); auto.
  apply cequivcn_sym; auto.
Qed.

Lemma per_cequiv_term_symmetric {p} :
  forall lib (ts : cts(p)), term_symmetric (per_cequiv lib ts).
Proof.
  unfold term_symmetric, term_equality_symmetric, per_cequiv.
  introv cts i e.
  exrepnd.
  allrw; discover; sp.
Qed.

Lemma per_cequiv_term_transitive {p} :
  forall lib (ts : cts(p)), term_transitive (per_cequiv lib ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_cequiv.
  introv cts i e1 e2.
  exrepnd.
  allrw; discover; sp.
Qed.

Lemma per_cequiv_term_value_respecting {p} :
  forall lib (ts : cts(p)), term_value_respecting lib (per_cequiv lib ts).
Proof.
  sp; unfold term_value_respecting, term_equality_respecting, per_cequiv.
  introv i e c; exrepnd.
  ccomputes_to_eqval.
  allrw; discover; sp.
  spcast; eapply cequivcn_axiom in c; sp.
Qed.

Lemma per_cequiv_type_system {p} :
  forall lib (ts : cts(p)), type_system lib (per_cequiv lib ts).
Proof.
  intros; unfold type_system; sp.
  try apply per_cequiv_uniquely_valued; auto.
  try apply per_cequiv_type_extensionality; auto.
  try apply per_cequiv_type_symmetric; auto.
  try apply per_cequiv_type_transitive; auto.
  try apply per_cequiv_type_value_respecting; auto.
  try apply per_cequiv_term_symmetric; auto.
  try apply per_cequiv_term_transitive; auto.
  try apply per_cequiv_term_value_respecting; auto.
Qed.


Lemma close_type_system_cequiv {p} :
  forall lib (ts : cts(p)),
  forall T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> per_cequiv lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 per.

  dup per as ps; unfold per_cequiv in ps; exrepnd; spcast.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    * SSCase "CL_cequiv".
      assert (uniquely_valued (per_cequiv lib (close lib ts)))
        as uv
          by (apply per_cequiv_uniquely_valued).
      apply uv with (T := T) (T' := T'); auto.
      apply uniquely_valued_trans5 with (T2 := T3) (eq2 := eq); auto.
      apply per_cequiv_type_extensionality.
      apply per_cequiv_type_symmetric.
      apply per_cequiv_type_transitive.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_cequiv; auto;
    assert (type_symmetric (per_cequiv lib (close lib ts)))
      as tys
        by (apply per_cequiv_type_symmetric);
    assert (type_extensionality (per_cequiv lib (close lib ts)))
      as tye
        by (apply per_cequiv_type_extensionality);
    apply tye with (eq := eq); auto.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_cequiv;
    assert (type_value_respecting lib (per_cequiv lib (close lib ts)))
           as tvr
           by (apply per_cequiv_type_value_respecting).

    apply tvr; auto.
    apply @type_system_type_mem with (T' := T'); auto.
    apply per_cequiv_type_symmetric.
    apply per_cequiv_type_transitive.

    apply tvr; auto.
    apply @type_system_type_mem1 with (T := T); auto.
    apply per_cequiv_type_symmetric.
    apply per_cequiv_type_transitive.

  + SCase "term_symmetric".
    assert (term_symmetric (per_cequiv lib (close lib ts)))
      as tes
        by (apply per_cequiv_term_symmetric).
    apply tes with (T := T) (T' := T'); auto.

  + SCase "term_transitive".
    assert (term_transitive (per_cequiv lib (close lib ts)))
      as tet
        by (apply per_cequiv_term_transitive).
    apply tet with (T := T) (T' := T'); auto.

  + SCase "term_value_respecting".
    assert (term_value_respecting lib (per_cequiv lib (close lib ts)))
      as tvr
        by (apply per_cequiv_term_value_respecting).
    apply tvr with (T := T); auto.
    apply @type_system_type_mem with (T' := T'); auto.
    apply per_cequiv_type_symmetric.
    apply per_cequiv_type_transitive.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr.

    apply CL_cequiv; apply per_cequiv_type_symmetric; auto.
    apply CL_cequiv; apply per_cequiv_type_symmetric; auto.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr.

    dands; apply CL_cequiv.

    apply per_cequiv_type_transitive with (T2 := T); auto.
    allunfold @per_cequiv; sp.
    ccomputes_to_eqval.
    exists a2 b2 c1 d1; sp; spcast; sp.
    allrw; sp.

    apply per_cequiv_type_transitive with (T2 := T); auto.
    allunfold @per_cequiv; sp.
    ccomputes_to_eqval.
    exists a0 b0 a2 b2; sp; spcast; sp.
    allrw; sp.

    dands; apply CL_cequiv.

    apply per_cequiv_type_transitive with (T2 := T'); auto.
    allunfold @per_cequiv; sp.
    ccomputes_to_eqval.
    exists c2 d2 c1 d1; sp; spcast; sp.
    allrw; sp.

    apply per_cequiv_type_transitive with (T2 := T'); auto.
    allunfold @per_cequiv; sp.
    ccomputes_to_eqval.
    exists a0 b0 c2 d2; sp; spcast; sp.
    allrw; sp.
Qed.
