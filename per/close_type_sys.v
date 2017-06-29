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
Require Import close_type_sys_per_init.
Require Import close_type_sys_per_int.
Require Import close_type_sys_per_nat.
Require Import close_type_sys_per_atom.
Require Import close_type_sys_per_uatom.
Require Import close_type_sys_per_csname.
Require Import close_type_sys_per_base.

(*Require Import close_type_sys_per_sqle.
Require Import close_type_sys_per_sqequal.
Require Import close_type_sys_per_eq.
Require Import close_type_sys_per_req.
Require Import close_type_sys_per_teq.
Require Import close_type_sys_per_isect.
(*Require Import close_type_sys_per_eisect.*)
Require Import close_type_sys_per_func.
Require Import close_type_sys_per_disect.
Require Import close_type_sys_per_pertype.
Require Import close_type_sys_per_ipertype.
Require Import close_type_sys_per_spertype.
Require Import close_type_sys_per_w.
Require Import close_type_sys_per_m.
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
Require Import close_type_sys_per_pm.*)

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
(*Lemma close_ts {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> defines_only_universes lib ts
    -> type_system lib (close lib ts).
Proof.
  introv tysys dou.
  rw @type_system_iff_is_type_system.
  unfold is_type_system; introv cl.

  close_cases (induction cl using @close_ind') Case.

  - Case "CL_init".
    admit.

  - Case "CL_int".
    admit.

  - Case "CL_atom".
    admit.

  - Case "CL_uatom".
    admit.

  - Case "CL_base".
    admit.

  - Case "CL_approx".
    admit.

  - Case "CL_cequiv".
    admit.

  - Case "CL_eq".

    assert (forall ts : cts(o),
              type_system lib ts
              -> type_system lib (per_eq lib ts)) as eqts by admit.

    repeat (dest_imp IHcl hyp).

    generalize (eqts ts); intro k; autodimp k hyp.
    rw @type_system_iff_is_type_system in k.
    generalize (k T T' eq); intro j.
    autodimp j hyp.
    exists A B a1 a2 b1 b2 eqa; sp.
Abort.

Lemma close_type_system_eq_implies {o} :
  forall lib (ts : cts(o)),
    type_system lib ts
    -> is_type_system lib (per_eq lib ts)
    -> forall T T' (eq : per) A B a1 a2 b1 b2 eqa,
         defines_only_universes lib ts
         -> computes_to_valc lib T (mkc_equality a1 a2 A)
         -> computes_to_valc lib T' (mkc_equality b1 b2 B)
         -> close lib ts A B eqa
         -> eqorceq lib eqa a1 b1
         -> eqorceq lib eqa a2 b2
         -> (forall t t' : CTerm,
               eq t t' <=>
                  ccomputes_to_valc lib t mkc_axiom
                  # ccomputes_to_valc lib t' mkc_axiom
                  # eqa a1 a2)
         -> per_eq lib (close lib ts) T T' eq
         -> type_sys_props lib (close lib ts) A B eqa
         -> type_sys_props lib (close lib ts) T T' eq.
Proof.
  introv tysys istysys dou c1 c2 cl eos1 eos2.
  introv eqiff peq tsp.
  unfold is_type_system in istysys.
Abort.
*)


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
  forall (ts : cts(o)),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> type_system (close ts).
Proof.
  intros.
  apply type_system_prop.
  unfold type_sys; introv cl.

  close_cases (induction cl using @close_ind') Case; sp; spcast.

  Focus 14.

  - Case "CL_init".
    apply close_type_system_init; auto.

  - Case "CL_int".
    apply close_type_system_int; auto.

  - Case "CL_nat".
    apply close_type_system_nat; auto.

  - Case "CL_csname".
    apply close_type_system_csname; auto.

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

  - Case "CL_eq".
    eapply close_type_system_eq; eauto.

  - Case "CL_req".
    eapply close_type_system_req; eauto.

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

  - Case "CL_ipertype".
    eapply close_type_system_ipertype; eauto.

  - Case "CL_spertype".
    eapply close_type_system_spertype; eauto.

  - Case "CL_w".
    eapply close_type_system_w; eauto.

  - Case "CL_m".
    eapply close_type_system_m; eauto.

  - Case "CL_pw".
    eapply close_type_system_pw; eauto;
      try (complete (unfold type_sys_props_fam; sp));
      try (complete (unfold type_sys_props_fam_fam; sp)).

  - Case "CL_pm".
    eapply close_type_system_pm; eauto;
      try (complete (unfold type_sys_props_fam; sp));
      try (complete (unfold type_sys_props_fam_fam; sp)).

  - Case "CL_texc".
    eapply close_type_system_texc; eauto.

  - Case "CL_union".
    eapply close_type_system_union; eauto.

  - Case "CL_image".
    eapply close_type_system_image; eauto; spcast; auto.

  - Case "CL_partial".
    eapply close_type_system_partial; eauto.

  - Case "CL_admiss".
    eapply close_type_system_admiss; eauto.

  - Case "CL_mono".
    eapply close_type_system_mono; eauto.

  - Case "CL_ffatom".
    eapply close_type_system_ffatom; eauto.

  - Case "CL_effatom".
    eapply close_type_system_effatom; eauto.

  - Case "CL_ffatoms".
    eapply close_type_system_ffatoms; eauto.

  - Case "CL_set".
    eapply close_type_system_set; eauto.

  - Case "CL_tunion".
    eapply close_type_system_tunion; eauto.

  - Case "CL_product".
    eapply close_type_system_product; eauto.
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
