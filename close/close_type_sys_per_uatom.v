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


Add LoadPath "../".

Require Export type_sys.
Require Import dest_close.


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


Lemma close_type_system_uatom {p} :
  forall lib (ts : cts(p)),
  forall T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> per_uatom lib (close lib ts) T T' eq
    -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv X X0 per.

  duplicate per as pi.
  unfold per_uatom in pi; repnd; spcast.

  rw @type_sys_props_iff_type_sys_props3.
  prove_type_sys_props3 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    * SSCase "CL_uatom".
      assert (uniquely_valued (per_uatom lib (close lib ts))) as uv
        by (apply per_uatom_uniquely_valued).
      apply uv with (T := T) (T' := T'); auto.
      apply uniquely_valued_trans5 with (T2 := T3) (eq2 := eq); auto.
      apply per_uatom_type_extensionality.
      apply per_uatom_type_symmetric.
      apply per_uatom_type_transitive.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_uatom; auto;
    assert (type_symmetric (per_uatom lib (close lib ts))) as tys
      by (apply per_uatom_type_symmetric);
    assert (type_extensionality (per_uatom lib (close lib ts))) as tye
      by (apply per_uatom_type_extensionality);
    apply tye with (eq := eq); auto.

  + SCase "type_value_respecting"; sp; subst; apply CL_uatom;
    assert (type_value_respecting lib (per_uatom lib (close lib ts)))
           as tvr
           by (apply per_uatom_type_value_respecting).

    apply tvr; auto;
    apply @type_system_type_mem with (T' := T'); auto;
    try (apply per_uatom_type_symmetric);
    try (apply per_uatom_type_transitive).

    apply tvr; auto.
    apply @type_system_type_mem1 with (T := T); auto;
    try (apply per_uatom_type_transitive);
    try (apply per_uatom_type_symmetric).

  + SCase "term_symmetric".
    assert (term_symmetric (per_uatom lib (close lib ts))) as tes
      by (apply per_uatom_term_symmetric).
    apply tes with (T := T) (T' := T'); auto.

  + SCase "term_transitive".
    assert (term_transitive (per_uatom lib (close lib ts))) as tet
      by (apply per_uatom_term_transitive).
    apply tet with (T := T) (T' := T'); auto.

  + SCase "term_value_respecting".
    assert (term_value_respecting lib (per_uatom lib (close lib ts))) as tvr
      by (apply per_uatom_term_value_respecting).
    apply tvr with (T := T); auto.
    apply @type_system_type_mem with (T' := T'); auto.
    apply per_uatom_type_symmetric.
    apply per_uatom_type_transitive.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr.

    apply CL_uatom; allunfold @per_uatom; sp.
    apply CL_uatom; allunfold @per_uatom; sp.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive"; repdors; subst; dclose_lr;
    dands; apply CL_uatom; allunfold @per_uatom; sp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("../")
*** End:
*)
