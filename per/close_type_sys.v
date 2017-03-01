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


Require Export type_sys_useful2.
Require Import dest_close.

Require Import close_type_sys_per_init.
Require Import close_type_sys_per_int.
Require Import close_type_sys_per_atom.
Require Import close_type_sys_per_uatom.
Require Import close_type_sys_per_base.
Require Import close_type_sys_per_sqle.
Require Import close_type_sys_per_sqequal.
Require Import close_type_sys_per_eq.
Require Import close_type_sys_per_aeq.
Require Import close_type_sys_per_teq.
Require Import close_type_sys_per_isect.
(*Require Import close_type_sys_per_eisect.*)
Require Import close_type_sys_per_func.
Require Import close_type_sys_per_disect.
Require Import close_type_sys_per_pertype.
(*
Require Import close_type_sys_per_ipertype.
Require Import close_type_sys_per_spertype.
*)
Require Import close_type_sys_per_w.
Require Import close_type_sys_per_m.
(*
Require Import close_type_sys_per_texc.
Require Import close_type_sys_per_union.
Require Import close_type_sys_per_image.
Require Import close_type_sys_per_partial.
Require Import close_type_sys_per_admiss.
Require Import close_type_sys_per_mono.
Require Import close_type_sys_per_ffatom.
Require Import close_type_sys_per_effatom.
Require Import close_type_sys_per_ffatoms.
Require Import close_type_sys_per_set.
Require Import close_type_sys_per_tunion.
Require Import close_type_sys_per_product.
Require Import close_type_sys_per_pw.
Require Import close_type_sys_per_pm.
*)

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ *)
(** printing ~=~  $\sim$ *)
(* printing ===>  $\longmapsto$ *)
(** printing ===>  $\Downarrow$ *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)
(* begin hide *)


(* This is Crary's lemma 4.12 *)
Lemma close_ts {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_system lib (close lib ts).
Proof.
  introv tysys dou.
  rw @type_system_iff_is_type_system.
  introv cl.

  close_cases (induction cl using @close_ind') Case; spcast.

  - Case "CL_init".
    apply close_type_system_init; auto.

  - Case "CL_int".
    apply close_type_system_int; auto.

  - Case "CL_atom".
    apply close_type_system_atom; auto.

  - Case "CL_uatom".
    apply close_type_system_uatom; auto.

  - Case "CL_base".
    apply close_type_system_base; auto.

  - Case "CL_approx".
    apply close_type_system_approx; auto.

  - Case "CL_cequiv".
    apply close_type_system_cequiv; auto.

  - Case "CL_aeq".
    eapply close_type_system_aeq; eauto.

  - Case "CL_eq".
    eapply close_type_system_eq; eauto.

  - Case "CL_teq".
    eapply close_type_system_teq; eauto.

  - Case "CL_isect".
    eapply close_type_system_isect; eauto.

  - Case "CL_func".
    eapply close_type_system_func; eauto.

  - Case "CL_disect".
    eapply close_type_system_disect; eauto.

  - Case "CL_pertype".
    eapply close_type_system_pertype; eauto.

  - Case "CL_w".
    eapply close_type_system_w; eauto.

  - Case "CL_m".
    eapply close_type_system_m; eauto.

Qed.



(* ------ proofs that the type definitions define type systems ------ *)

(* end hide *)

(**

  It is then tedious but fairly straightforward to prove that [close]
  preserves the [type_system] property.  We currently have prove that
  the integer, base, approximation, computational equivalence,
  equality, intersection, function, dependent intersection, PER, W,
  parameterized W, M, refinement, partial, admissibility, disjoint
  union, image, and product types preserve the type system properties.
  It remains to prove that the parameterized M and extensional
  intersection types preserves the type system properties.  This means
  that we cannot use these types yet.  This is why we have not yet
  added these types to the type system.

*)

Lemma close_type_system {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_system lib (close lib ts).
Proof.
  intros.
  apply type_system_prop.
  unfold type_sys; introv cl.

  close_cases (induction cl using @close_ind') Case; sp; spcast.


  - Case "CL_init".
    apply close_type_system_init; auto.


  - Case "CL_int".
    apply close_type_system_int; auto.


  - Case "CL_atom".
    apply close_type_system_atom; auto.


  - Case "CL_uatom".
    apply close_type_system_uatom; auto.


  - Case "CL_base".
    apply close_type_system_base; auto.


  - Case "CL_approx".
    apply close_type_system_approx; auto.


  - Case "CL_cequiv".
    apply close_type_system_cequiv; auto.


  - Case "CL_aeq".
    apply @close_type_system_aeq
    with (A := A)
           (B := B)
           (a1 := a1)
           (a2 := a2)
           (b1 := b1)
           (b2 := b2)
           (eqa := eqa); auto.


  - Case "CL_eq".
    apply @close_type_system_eq
    with (A := A)
           (B := B)
           (a1 := a1)
           (a2 := a2)
           (b1 := b1)
           (b2 := b2)
           (eqa := eqa); auto.


  - Case "CL_teq".
    apply @close_type_system_teq
    with (a1 := a1)
           (a2 := a2)
           (b1 := b1)
           (b2 := b2)
           (eqa := eqa); auto.


  - Case "CL_isect".
    apply @close_type_system_isect
    with (A := A)
           (A' := A')
           (v := v)
           (v' := v')
           (B := B)
           (B' := B')
           (eqa := eqa)
           (eqb := eqb); auto.


  - Case "CL_func".
    apply @close_type_system_func
    with (A := A)
           (A' := A')
           (v := v)
           (v' := v')
           (B := B)
           (B' := B')
           (eqa := eqa)
           (eqb := eqb); auto.


  - Case "CL_disect".
    apply @close_type_system_disect
    with (A := A)
           (A' := A')
           (v := v)
           (v' := v')
           (B := B)
           (B' := B')
           (eqa := eqa)
           (eqb := eqb); auto.


  - Case "CL_pertype".
    apply @close_type_system_pertype
    with (R1 := R1)
           (R2 := R2)
           (eq1 := eq1)
           (eq2 := eq2); auto.


  - Case "CL_ipertype".
    apply @close_type_system_ipertype
    with (R1 := R1)
           (R2 := R2)
           (eq1 := eq1); auto.


  - Case "CL_spertype".
    apply @close_type_system_spertype
    with (R1 := R1)
           (R2 := R2)
           (eq1 := eq1); auto.


  - Case "CL_w".
    apply @close_type_system_w
    with (A := A)
           (A' := A')
           (v := v)
           (v' := v')
           (B := B)
           (B' := B')
           (eqa := eqa)
           (eqb := eqb); auto.


  - Case "CL_m".
    apply @close_type_system_m
    with (A := A)
           (A' := A')
           (v := v)
           (v' := v')
           (B := B)
           (B' := B')
           (eqa := eqa)
           (eqb := eqb); auto.


  - Case "CL_pw".
    apply @close_type_system_pw
          with (P := Pr)
          (P' := Pr')
          (ap := ap)
          (ap' := ap')
          (A := A)
          (A' := A')
          (bp := bp)
          (bp' := bp')
          (ba := ba)
          (ba' := ba')
          (B := B)
          (B' := B')
          (cp := cp)
          (cp' := cp')
          (ca := ca)
          (ca' := ca')
          (cb := cb)
          (cb' := cb')
          (C := C)
          (C' := C')
          (p := p)
          (p' := p')
          (eqp := eqp)
          (eqa := eqa)
          (eqb := eqb);
      auto; spcast; sp;
      try (complete (unfold type_sys_props_fam; sp));
      try (complete (unfold type_sys_props_fam_fam; sp)).


  - Case "CL_pm".
    apply @close_type_system_pm
          with (P := Pr)
          (P' := Pr')
          (ap := ap)
          (ap' := ap')
          (A := A)
          (A' := A')
          (bp := bp)
          (bp' := bp')
          (ba := ba)
          (ba' := ba')
          (B := B)
          (B' := B')
          (cp := cp)
          (cp' := cp')
          (ca := ca)
          (ca' := ca')
          (cb := cb)
          (cb' := cb')
          (C := C)
          (C' := C')
          (p := p)
          (p' := p')
          (eqp := eqp)
          (eqa := eqa)
          (eqb := eqb);
      auto; spcast; sp;
      try (complete (unfold type_sys_props_fam; sp));
      try (complete (unfold type_sys_props_fam_fam; sp)).


  - Case "CL_texc".
    apply @close_type_system_texc
    with (A1 := N)
           (A2 := N')
           (B1 := E)
           (B2 := E')
           (eqa := eqn)
           (eqb := eqe); auto; spcast; sp.


  - Case "CL_union".
    apply @close_type_system_union
    with (A1 := A)
           (A2 := A')
           (B1 := B)
           (B2 := B')
           (eqa := eqa)
           (eqb := eqb); auto; spcast; sp.


  - Case "CL_image".
    apply @close_type_system_image
    with (A := A)
           (A' := A')
           (f := f)
           (f' := f')
           (eqa := eqa); auto; spcast; sp.


(*
  - Case "CL_eisect".
    admit.
*)


  - Case "CL_partial".
    apply @close_type_system_partial
    with (A1 := A1)
           (A2 := A2)
           (eqa := eqa); auto.


  - Case "CL_admiss".
    apply @close_type_system_admiss
    with (A1 := A1)
           (A2 := A2)
           (eqa := eqa); auto.


  - Case "CL_mono".
    apply @close_type_system_mono
    with (A1 := A1)
           (A2 := A2)
           (eqa := eqa); auto.


  - Case "CL_ffatom".
    apply @close_type_system_ffatom
    with (A1 := A1)
           (A2 := A2)
           (x1 := x1)
           (x2 := x2)
           (a1 := a1)
           (a2 := a2)
           (eqa := eqa)
           (u := u); auto.


  - Case "CL_effatom".
    apply @close_type_system_effatom
    with (A1 := A1)
           (A2 := A2)
           (x1 := x1)
           (x2 := x2)
           (a1 := a1)
           (a2 := a2)
           (eqa := eqa); auto.


  - Case "CL_ffatoms".
    apply @close_type_system_ffatoms
    with (A1 := A1)
           (A2 := A2)
           (x1 := x1)
           (x2 := x2)
           (eqa := eqa); auto.


  - Case "CL_set".
    apply @close_type_system_set
    with (A := A)
           (A' := A')
           (v := v)
           (v' := v')
           (B := B)
           (B' := B')
           (eqa := eqa)
           (eqb := eqb); auto.


  - Case "CL_tunion".
    apply @close_type_system_tunion
    with (A := A)
           (A' := A')
           (v := v)
           (v' := v')
           (B := B)
           (B' := B')
           (eqa := eqa)
           (eqb := eqb); auto.


  - Case "CL_product".
    apply @close_type_system_product
    with (A := A)
           (A' := A')
           (v := v)
           (v' := v')
           (B := B)
           (B' := B')
           (eqa := eqa)
           (eqb := eqb); auto.

Qed.

(* begin hide *)

Lemma close_uniquely_valued {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> uniquely_valued (close lib ts).
Proof.
  intros.
  apply close_type_system in X; auto.
  unfold type_system in X; sp.
Qed.

Lemma close_type_symmetric {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_symmetric (close lib ts).
Proof.
  intros.
  apply close_type_system in X; auto.
  unfold type_system in X; sp.
Qed.

Lemma close_type_extensionality {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_extensionality (close lib ts).
Proof.
  intros.
  apply close_type_system in X; auto.
  unfold type_system in X; sp.
Qed.

Lemma close_type_transitive {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_transitive (close lib ts).
Proof.
  intros.
  apply close_type_system in X; auto.
  unfold type_system in X; sp.
Qed.

Lemma close_type_value_respecting {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_value_respecting lib (close lib ts).
Proof.
  intros.
  apply close_type_system in X; auto.
  unfold type_system in X; sp.
Qed.

(* end hide *)
