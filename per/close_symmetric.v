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


Definition defines_only_universes_per {p} lib (ts : cts(p)) :=
  forall T T' eq,
    ts T T' eq
    -> {i : nat , eq <=2=> (univi_eq lib (univi lib i)) }.

Lemma defines_only_universes_per_univi {o} :
  forall lib i, @defines_only_universes_per o lib (univi lib i).
Proof.
  unfold defines_only_universes_per; introv u.
  allrw @univi_exists_iff; exrepnd; spcast.
  exists j; auto.
Qed.
Hint Resolve defines_only_universes_per_univi : slow.

Lemma defines_only_universes_per_univ {o} :
  forall lib, @defines_only_universes_per o lib (univ lib).
Proof.
  unfold defines_only_universes, univ; introv u; exrepnd.
  induction i; allsimpl; tcsp; repndors; exrepnd; spcast; tcsp.
  exists i; auto.
Qed.
Hint Resolve defines_only_universes_per_univ : slow.

Lemma int_is_not_uni {o} :
  forall lib (T : @CTerm o),
    computes_to_valc lib T mkc_int
    -> not_uni lib T.
Proof.
  introv comp1 comp2; spcast.
  computes_to_valc_diff.
Qed.
Hint Resolve int_is_not_uni : slow.

Lemma approx_is_not_uni {o} :
  forall lib a b (T : @CTerm o),
    computes_to_valc lib T (mkc_approx a b)
    -> not_uni lib T.
Proof.
  introv comp1 comp2; spcast.
  computes_to_valc_diff.
Qed.
Hint Resolve approx_is_not_uni : slow.

Lemma equal_to_int {o} :
  forall lib ts (T1 T2 T : @CTerm o) eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> not_uni lib T1
    -> computes_to_valc lib T mkc_int
    -> close lib ts T1 T2 eq
    -> (eq <=2=> (equality_of_int lib))
    -> close lib ts T1 T eq.
Proof.
  introv tysys dou nuni comp cl eqiff.
  close_cases (induction cl using @close_ind') Case; tcsp.

  - Case "CL_init".
    apply CL_init.

    match goal with
    | [ H : ts _ _ _ |- _ ] => rename H into h
    end.
    apply dou in h; exrepnd.
    spcast.
    pose proof (nuni i) as q; destruct q; spcast; auto.

  - Case "CL_int".
    clear per.
    spcast.
    apply CL_int.
    unfold per_int; dands; spcast; auto.
    unfold per_extensional.
    left; spcast.
    eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;eauto|].
    apply cequivc_sym; apply computes_to_valc_implies_cequivc; auto.

  - Case "CL_atom".
    clear per.
    spcast.
    apply CL_atom.
    unfold per_atom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_uatom".
    clear per.
    spcast.
    apply CL_uatom.
    unfold per_uatom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_base".
    clear per.
    spcast.
    apply CL_base.
    unfold per_base; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_approx".
    clear per.
    spcast.
    apply CL_approx.
    unfold per_approx.
    exists a b; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_cequiv".
    clear per.
    spcast.
    apply CL_cequiv.
    unfold per_cequiv.
    exists a b; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_eq".
    clear per.
    spcast.
    apply CL_eq.
    unfold per_eq.
    exists A a b eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_teq".
    clear per.
    spcast.
    apply CL_teq.
    unfold per_teq.
    exists A B eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_isect".
    clear per.
    spcast.
    apply CL_isect.
    unfold per_isect.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_int; unfold per_int; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_func".
    clear per.
    spcast.
    apply CL_func.
    unfold per_func.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_int; unfold per_int; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_disect".
    clear per.
    spcast.
    apply CL_disect.
    unfold per_disect.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_int; unfold per_int; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_pertype".
    clear per.
    spcast.
    apply CL_pertype.
    unfold per_pertype.
    exists R eqr; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_w".
    clear per.
    spcast.
    apply CL_w.
    unfold per_w.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_int; unfold per_int; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_m".
    clear per.
    spcast.
    apply CL_m.
    unfold per_m.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_int; unfold per_int; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_texc".
    clear per.
    spcast.
    apply CL_texc.
    unfold per_texc.
    exists eqn eqe N E; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_union".
    clear per.
    spcast.
    apply CL_union.
    unfold per_union.
    exists eqa eqb A B; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_image".
    clear per.
    spcast.
    apply CL_image.
    unfold per_image.
    exists eqa A f; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_partial".
    clear per.
    spcast.
    apply CL_partial.
    unfold per_partial.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_admiss".
    clear per.
    spcast.
    apply CL_admiss.
    unfold per_admiss.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_mono".
    clear per.
    spcast.
    apply CL_mono.
    unfold per_mono.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatom".
    clear per.
    spcast.
    apply CL_ffatom.
    unfold per_ffatom.
    exists A x a eqa u; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatoms".
    clear per.
    spcast.
    apply CL_ffatoms.
    unfold per_ffatoms.
    exists A x eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_int; unfold per_int; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_set".
    clear per.
    spcast.
    apply CL_set.
    unfold per_set.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_int; unfold per_int; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_tunion".
    clear per.
    spcast.
    apply CL_tunion.
    unfold per_tunion.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_int; unfold per_int; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_product".
    clear per.
    spcast.
    apply CL_product.
    unfold per_product.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_int; unfold per_int; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.
Qed.

Lemma equal_to_approx {o} :
  forall lib ts (T1 T2 T : @CTerm o) a b eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> not_uni lib T1
    -> computes_to_valc lib T (mkc_approx a b)
    -> close lib ts T1 T2 eq
    -> (eq <=2=> (fun _ _ => capproxc lib a b))
    -> close lib ts T1 T eq.
Proof.
  introv tysys dou nuni comp cl eqiff.
  close_cases (induction cl using @close_ind') Case; tcsp.

  - Case "CL_init".
    apply CL_init.

    match goal with
    | [ H : ts _ _ _ |- _ ] => rename H into h
    end.
    apply dou in h; exrepnd.
    spcast.
    pose proof (nuni i) as q; destruct q; spcast; auto.

  - Case "CL_int".
    clear per.
    spcast.
    apply CL_int.
    unfold per_int; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_atom".
    clear per.
    spcast.
    apply CL_atom.
    unfold per_atom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_uatom".
    clear per.
    spcast.
    apply CL_uatom.
    unfold per_uatom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_base".
    clear per.
    spcast.
    apply CL_base.
    unfold per_base; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_approx".
    clear per.
    spcast.
    apply CL_approx.
    unfold per_approx.
    exists a0 b0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_cequiv".
    clear per.
    spcast.
    apply CL_cequiv.
    unfold per_cequiv.
    exists a0 b0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_eq".
    clear per.
    spcast.
    apply CL_eq.
    unfold per_eq.
    exists A a0 b0 eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_teq".
    clear per.
    spcast.
    apply CL_teq.
    unfold per_teq.
    exists A B eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_isect".
    clear per.
    spcast.
    apply CL_isect.
    unfold per_isect.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_func".
    clear per.
    spcast.
    apply CL_func.
    unfold per_func.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_disect".
    clear per.
    spcast.
    apply CL_disect.
    unfold per_disect.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_pertype".
    clear per.
    spcast.
    apply CL_pertype.
    unfold per_pertype.
    exists R eqr; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_w".
    clear per.
    spcast.
    apply CL_w.
    unfold per_w.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_m".
    clear per.
    spcast.
    apply CL_m.
    unfold per_m.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_texc".
    clear per.
    spcast.
    apply CL_texc.
    unfold per_texc.
    exists eqn eqe N E; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_union".
    clear per.
    spcast.
    apply CL_union.
    unfold per_union.
    exists eqa eqb A B; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_image".
    clear per.
    spcast.
    apply CL_image.
    unfold per_image.
    exists eqa A f; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_partial".
    clear per.
    spcast.
    apply CL_partial.
    unfold per_partial.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_admiss".
    clear per.
    spcast.
    apply CL_admiss.
    unfold per_admiss.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_mono".
    clear per.
    spcast.
    apply CL_mono.
    unfold per_mono.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatom".
    clear per.
    spcast.
    apply CL_ffatom.
    unfold per_ffatom.
    exists A x a0 eqa u; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatoms".
    clear per.
    spcast.
    apply CL_ffatoms.
    unfold per_ffatoms.
    exists A x eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_set".
    clear per.
    spcast.
    apply CL_set.
    unfold per_set.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_tunion".
    clear per.
    spcast.
    apply CL_tunion.
    unfold per_tunion.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.

  - Case "CL_product".
    clear per.
    spcast.
    apply CL_product.
    unfold per_product.
    exists eqa eqb; dands; spcast; auto.
    unfold type_family.
    exists A v B; dands; spcast; auto.
    { unfold per_extensional.
      right; dands; eauto 3 with slow.
      apply CL_approx; unfold per_approx; exists a b; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.
Qed.

Lemma close_symmetric {o} :
  forall lib ts (T T' : @CTerm o) eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> defines_only_universes_per lib ts
    -> close lib ts T T' eq
    -> close lib ts T' T eq.
Proof.
  introv tysys dou dou_per cl.
  close_cases (induction cl using @close_ind') Case; tcsp.

  - Case "CL_init".
    apply CL_init.
    assert (type_symmetric ts) as tvr by (unfold type_system in *; tcsp).
    tcsp.

  - Case "CL_int".
    clear per.
    unfold per_extensional in *.
    clear extP.
    repndors; repnd; spcast.

    + applydup @cequivc_int in ext; auto.
      apply CL_int; unfold per_int; dands; spcast; auto.
      unfold per_extensional; tcsp.
      left; spcast; apply cequivc_sym; auto.

    + eapply equal_to_int; eauto.

  - Case "CL_atom".
    clear per.
    unfold per_extensional in *.
    clear extP.
    repndors; repnd; spcast.

    + applydup @cequivc_atom in ext; auto.
      apply CL_int; unfold per_int; dands; spcast; auto.
      unfold per_extensional; tcsp.
      left; spcast; apply cequivc_sym; auto.

    + eapply equal_to_int; eauto.

  - Case "CL_approx".
    clear per.
    unfold per_extensional in *.
    clear extP.
    repndors; repnd; spcast.

    + dup ext as ceq.
      eapply cequivc_mkc_approx in ceq;[|eauto].
      exrepnd.
      apply CL_approx; unfold per_approx.
      exists a' b'; dands; spcast; auto.
      { unfold per_extensional; tcsp.
        left; spcast; apply cequivc_sym; auto. }
      { eapply eq_term_equals_trans;[eauto|].
        intros u v.
        split; intro h; spcast.
        { eapply approxc_cequivc_trans;[|eauto].
          eapply cequivc_approxc_trans;[apply cequivc_sym;eauto|].
          auto. }
        { eapply approxc_cequivc_trans;[|apply cequivc_sym;eauto].
          eapply cequivc_approxc_trans;[eauto|].
          auto. }
      }

    + eapply equal_to_approx; eauto.

Qed.
