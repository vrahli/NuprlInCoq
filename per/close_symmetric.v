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

Lemma equal_to_atom {o} :
  forall lib ts (T1 T2 T : @CTerm o) eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> not_uni lib T1
    -> computes_to_valc lib T mkc_atom
    -> close lib ts T1 T2 eq
    -> (eq <=2=> (equality_of_atom lib))
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
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_atom".
    clear per.
    spcast.
    apply CL_atom.
    unfold per_atom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_uatom".
    clear per.
    spcast.
    apply CL_uatom.
    unfold per_uatom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_base".
    clear per.
    spcast.
    apply CL_base.
    unfold per_base; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_approx".
    clear per.
    spcast.
    apply CL_approx.
    unfold per_approx.
    exists a b; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_cequiv".
    clear per.
    spcast.
    apply CL_cequiv.
    unfold per_cequiv.
    exists a b; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_eq".
    clear per.
    spcast.
    apply CL_eq.
    unfold per_eq.
    exists A a b eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_teq".
    clear per.
    spcast.
    apply CL_teq.
    unfold per_teq.
    exists A B eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
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
      apply CL_atom; unfold per_atom; dands; spcast; auto.
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
      apply CL_atom; unfold per_atom; dands; spcast; auto.
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
      apply CL_atom; unfold per_atom; dands; spcast; auto.
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
    apply CL_atom; unfold per_atom; dands; spcast; auto.
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
      apply CL_atom; unfold per_atom; dands; spcast; auto.
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
      apply CL_atom; unfold per_atom; dands; spcast; auto.
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
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_union".
    clear per.
    spcast.
    apply CL_union.
    unfold per_union.
    exists eqa eqb A B; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_image".
    clear per.
    spcast.
    apply CL_image.
    unfold per_image.
    exists eqa A f; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_partial".
    clear per.
    spcast.
    apply CL_partial.
    unfold per_partial.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_admiss".
    clear per.
    spcast.
    apply CL_admiss.
    unfold per_admiss.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_mono".
    clear per.
    spcast.
    apply CL_mono.
    unfold per_mono.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatom".
    clear per.
    spcast.
    apply CL_ffatom.
    unfold per_ffatom.
    exists A x a eqa u; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatoms".
    clear per.
    spcast.
    apply CL_ffatoms.
    unfold per_ffatoms.
    exists A x eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_atom; unfold per_atom; dands; spcast; auto.
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
      apply CL_atom; unfold per_atom; dands; spcast; auto.
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
      apply CL_atom; unfold per_atom; dands; spcast; auto.
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
      apply CL_atom; unfold per_atom; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.
Qed.

Lemma equal_to_uatom {o} :
  forall lib ts (T1 T2 T : @CTerm o) eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> not_uni lib T1
    -> computes_to_valc lib T mkc_uatom
    -> close lib ts T1 T2 eq
    -> (eq <=2=> (equality_of_uatom lib))
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
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_atom".
    clear per.
    spcast.
    apply CL_atom.
    unfold per_atom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_uatom".
    clear per.
    spcast.
    apply CL_uatom.
    unfold per_uatom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_base".
    clear per.
    spcast.
    apply CL_base.
    unfold per_base; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_approx".
    clear per.
    spcast.
    apply CL_approx.
    unfold per_approx.
    exists a b; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_cequiv".
    clear per.
    spcast.
    apply CL_cequiv.
    unfold per_cequiv.
    exists a b; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_eq".
    clear per.
    spcast.
    apply CL_eq.
    unfold per_eq.
    exists A a b eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_teq".
    clear per.
    spcast.
    apply CL_teq.
    unfold per_teq.
    exists A B eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
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
      apply CL_uatom; unfold per_uatom; dands; spcast; auto.
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
      apply CL_uatom; unfold per_uatom; dands; spcast; auto.
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
      apply CL_uatom; unfold per_uatom; dands; spcast; auto.
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
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
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
      apply CL_uatom; unfold per_uatom; dands; spcast; auto.
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
      apply CL_uatom; unfold per_uatom; dands; spcast; auto.
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
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_union".
    clear per.
    spcast.
    apply CL_union.
    unfold per_union.
    exists eqa eqb A B; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_image".
    clear per.
    spcast.
    apply CL_image.
    unfold per_image.
    exists eqa A f; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_partial".
    clear per.
    spcast.
    apply CL_partial.
    unfold per_partial.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_admiss".
    clear per.
    spcast.
    apply CL_admiss.
    unfold per_admiss.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_mono".
    clear per.
    spcast.
    apply CL_mono.
    unfold per_mono.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatom".
    clear per.
    spcast.
    apply CL_ffatom.
    unfold per_ffatom.
    exists A x a eqa u; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatoms".
    clear per.
    spcast.
    apply CL_ffatoms.
    unfold per_ffatoms.
    exists A x eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_uatom; unfold per_uatom; dands; spcast; auto.
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
      apply CL_uatom; unfold per_uatom; dands; spcast; auto.
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
      apply CL_uatom; unfold per_uatom; dands; spcast; auto.
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
      apply CL_uatom; unfold per_uatom; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.
Qed.

Lemma equal_to_base {o} :
  forall lib ts (T1 T2 T : @CTerm o) eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> not_uni lib T1
    -> computes_to_valc lib T mkc_base
    -> close lib ts T1 T2 eq
    -> (eq <=2=> (ccequivc lib))
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
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_atom".
    clear per.
    spcast.
    apply CL_atom.
    unfold per_atom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_uatom".
    clear per.
    spcast.
    apply CL_uatom.
    unfold per_uatom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_base".
    clear per.
    spcast.
    apply CL_base.
    unfold per_base; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_approx".
    clear per.
    spcast.
    apply CL_approx.
    unfold per_approx.
    exists a b; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_cequiv".
    clear per.
    spcast.
    apply CL_cequiv.
    unfold per_cequiv.
    exists a b; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_eq".
    clear per.
    spcast.
    apply CL_eq.
    unfold per_eq.
    exists A a b eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_teq".
    clear per.
    spcast.
    apply CL_teq.
    unfold per_teq.
    exists A B eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
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
      apply CL_base; unfold per_base; dands; spcast; auto.
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
      apply CL_base; unfold per_base; dands; spcast; auto.
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
      apply CL_base; unfold per_base; dands; spcast; auto.
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
    apply CL_base; unfold per_base; dands; spcast; auto.
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
      apply CL_base; unfold per_base; dands; spcast; auto.
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
      apply CL_base; unfold per_base; dands; spcast; auto.
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
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_union".
    clear per.
    spcast.
    apply CL_union.
    unfold per_union.
    exists eqa eqb A B; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_image".
    clear per.
    spcast.
    apply CL_image.
    unfold per_image.
    exists eqa A f; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_partial".
    clear per.
    spcast.
    apply CL_partial.
    unfold per_partial.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_admiss".
    clear per.
    spcast.
    apply CL_admiss.
    unfold per_admiss.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_mono".
    clear per.
    spcast.
    apply CL_mono.
    unfold per_mono.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatom".
    clear per.
    spcast.
    apply CL_ffatom.
    unfold per_ffatom.
    exists A x a eqa u; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatoms".
    clear per.
    spcast.
    apply CL_ffatoms.
    unfold per_ffatoms.
    exists A x eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_base; unfold per_base; dands; spcast; auto.
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
      apply CL_base; unfold per_base; dands; spcast; auto.
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
      apply CL_base; unfold per_base; dands; spcast; auto.
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
      apply CL_base; unfold per_base; dands; spcast; auto.
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

Lemma equal_to_cequiv {o} :
  forall lib ts (T1 T2 T : @CTerm o) a b eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> not_uni lib T1
    -> computes_to_valc lib T (mkc_cequiv a b)
    -> close lib ts T1 T2 eq
    -> (eq <=2=> (fun _ _ => ccequivc lib a b))
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
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_atom".
    clear per.
    spcast.
    apply CL_atom.
    unfold per_atom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_uatom".
    clear per.
    spcast.
    apply CL_uatom.
    unfold per_uatom; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_base".
    clear per.
    spcast.
    apply CL_base.
    unfold per_base; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_approx".
    clear per.
    spcast.
    apply CL_approx.
    unfold per_approx.
    exists a0 b0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_cequiv".
    clear per.
    spcast.
    apply CL_cequiv.
    unfold per_cequiv.
    exists a0 b0; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_eq".
    clear per.
    spcast.
    apply CL_eq.
    unfold per_eq.
    exists A a0 b0 eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_teq".
    clear per.
    spcast.
    apply CL_teq.
    unfold per_teq.
    exists A B eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
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
      apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
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
      apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
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
      apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
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
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
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
      apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
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
      apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
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
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_union".
    clear per.
    spcast.
    apply CL_union.
    unfold per_union.
    exists eqa eqb A B; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_image".
    clear per.
    spcast.
    apply CL_image.
    unfold per_image.
    exists eqa A f; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_partial".
    clear per.
    spcast.
    apply CL_partial.
    unfold per_partial.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_admiss".
    clear per.
    spcast.
    apply CL_admiss.
    unfold per_admiss.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_mono".
    clear per.
    spcast.
    apply CL_mono.
    unfold per_mono.
    exists A eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatom".
    clear per.
    spcast.
    apply CL_ffatom.
    unfold per_ffatom.
    exists A x a0 eqa u; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
    unfold per_extensional; left; spcast; auto.

  - Case "CL_ffatoms".
    clear per.
    spcast.
    apply CL_ffatoms.
    unfold per_ffatoms.
    exists A x eqa; dands; spcast; auto.
    unfold per_extensional.
    right; dands; eauto 3 with slow.
    apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
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
      apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
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
      apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
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
      apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; auto.
      unfold per_extensional; left; spcast; auto. }
    { unfold per_intensional; introv c; spcast; computes_to_valc_diff. }
    unfold type_family_members_eq; dands; tcsp.
Qed.

Definition type_respects_cequivc {p}
           lib
           (ts : cts(p))
           (T1 T2 : @CTerm p)
           (eq : per) :=
  forall T3 T4, cequivc lib T1 T3 -> cequivc lib T2 T4 -> ts T3 T4 eq.

Lemma close_preserves_cequivc {o} :
  forall lib ts (A B : @CTerm o) eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> close lib ts A B eq
    ->
    (
      uniquely_valued_body (close lib ts) A B eq
      # type_extensionality_body (close lib ts) A B eq
      # type_respects_cequivc lib (close lib ts) A B eq
      # close lib ts A A eq
      # close lib ts B B eq
      # term_equality_symmetric eq
      # term_equality_transitive eq
      # term_equality_respecting lib eq
    ).
Proof.
  introv tysys dou cl.
  close_cases (induction cl using @close_ind') Case; introv.

  - Case "CL_init".
    dest_ts tysys.

    dands; tcsp.

    { introv h.
      eapply ts_uv; eauto. }

    { introv eqiff.
      eapply ts_ext; eauto. }

    { introv ceqa ceqb.

      apply (ts_tyt _ T);[apply ts_tys|].
      { apply ts_tyv; auto.
        eapply ts_tyt;[eauto|]; tcsp. }
      { apply (ts_tyt _ T'); auto.
        apply ts_tyv; auto.
        eapply ts_tyt;[eauto|]; tcsp. } }

    { apply 

    { apply (tyt _ T'); tcsp. }

    { apply (tyt _ T); tcsp. }

  - Case "CL_int".
    clear per.

    dands.

    {
      apply CL_int; unfold per_int; dands; spcast; tcsp.

      { apply cequivc_int in ceqa; auto. }

      {
        unfold per_extensional in *.
        clear ext.
        repndors; spcast.

        { left; spcast.
          eapply cequivc_trans;[apply cequivc_sym;exact ceqa|].
          eapply cequivc_trans;[exact extP|]; auto. }

        { right; repnd.
          repeat (autodimp extP0 hyp).
          pose proof (extP0 B2 B2) as q.
          repeat (autodimp q hyp); repnd; dands; auto; eauto 3 with slow. }
      }
    }

    {
      apply CL_int; unfold per_int; dands; spcast; tcsp.
      left; spcast; auto.
    }

    {
      unfold per_extensional in *.
      clear ext.
      repndors; spcast.

      { apply cequivc_int in extP; auto.
        apply CL_int; unfold per_int; dands; spcast; auto.
        left; spcast; auto. }

      { repnd.
        repeat (autodimp extP0 hyp).
        pose proof (extP0 B2 B2) as q; repeat (autodimp q hyp); tcsp. }
    }

  - Case "CL_atom".
    clear per.

    dands.

    {
      apply CL_atom; unfold per_atom; dands; spcast; tcsp.

      { apply cequivc_atom in ceqa; auto. }

      {
        unfold per_extensional in *.
        clear ext.
        repndors; spcast.

        { left; spcast.
          eapply cequivc_trans;[apply cequivc_sym;exact ceqa|].
          eapply cequivc_trans;[exact extP|]; auto. }

        { right; repnd.
          repeat (autodimp extP0 hyp).
          pose proof (extP0 B2 B2) as q.
          repeat (autodimp q hyp); repnd; dands; auto; eauto 3 with slow. }
      }
    }

    {
      apply CL_atom; unfold per_atom; dands; spcast; tcsp.
      left; spcast; auto.
    }

    {
      unfold per_extensional in *.
      clear ext.
      repndors; spcast.

      { apply cequivc_atom in extP; auto.
        apply CL_atom; unfold per_atom; dands; spcast; auto.
        left; spcast; auto. }

      { repnd.
        repeat (autodimp extP0 hyp).
        pose proof (extP0 B2 B2) as q; repeat (autodimp q hyp); tcsp. }
    }

  - Case "CL_uatom".
    clear per.

    dands.

    {
      apply CL_uatom; unfold per_uatom; dands; spcast; tcsp.

      { apply cequivc_uatom in ceqa; auto. }

      {
        unfold per_extensional in *.
        clear ext.
        repndors; spcast.

        { left; spcast.
          eapply cequivc_trans;[apply cequivc_sym;exact ceqa|].
          eapply cequivc_trans;[exact extP|]; auto. }

        { right; repnd.
          repeat (autodimp extP0 hyp).
          pose proof (extP0 B2 B2) as q.
          repeat (autodimp q hyp); repnd; dands; auto; eauto 3 with slow. }
      }
    }

    {
      apply CL_uatom; unfold per_uatom; dands; spcast; tcsp.
      left; spcast; auto.
    }

    {
      unfold per_extensional in *.
      clear ext.
      repndors; spcast.

      { apply cequivc_uatom in extP; auto.
        apply CL_uatom; unfold per_uatom; dands; spcast; auto.
        left; spcast; auto. }

      { repnd.
        repeat (autodimp extP0 hyp).
        pose proof (extP0 B2 B2) as q; repeat (autodimp q hyp); tcsp. }
    }

  - Case "CL_base".
    clear per.

    dands.

    {
      apply CL_base; unfold per_base; dands; spcast; tcsp.

      { apply cequivc_base in ceqa; auto. }

      {
        unfold per_extensional in *.
        clear ext.
        repndors; spcast.

        { left; spcast.
          eapply cequivc_trans;[apply cequivc_sym;exact ceqa|].
          eapply cequivc_trans;[exact extP|]; auto. }

        { right; repnd.
          repeat (autodimp extP0 hyp).
          pose proof (extP0 B2 B2) as q.
          repeat (autodimp q hyp); repnd; dands; auto; eauto 3 with slow. }
      }
    }

    {
      apply CL_base; unfold per_base; dands; spcast; tcsp.
      left; spcast; auto.
    }

    {
      unfold per_extensional in *.
      clear ext.
      repndors; spcast.

      { apply cequivc_base in extP; auto.
        apply CL_base; unfold per_base; dands; spcast; auto.
        left; spcast; auto. }

      { repnd.
        repeat (autodimp extP0 hyp).
        pose proof (extP0 B2 B2) as q; repeat (autodimp q hyp); tcsp. }
    }

  - Case "CL_approx".
    clear per.

    dands.

    {
      spcast.
      dup ceqa as ceq1.
      eapply cequivc_mkc_approx in ceqa;[|eauto]; exrepnd.
      apply CL_approx; unfold per_approx; exists a' b'; dands; spcast; tcsp.

      {
        unfold per_extensional in *.
        clear ext.
        repndors; spcast.

        { left; spcast.
          eapply cequivc_trans;[apply cequivc_sym;exact ceq1|].
          eapply cequivc_trans;[|exact ceqb].
          eapply cequivc_trans;[|exact extP]; auto. }

        { right; repnd.
          repeat (autodimp extP0 hyp).
          pose proof (extP0 B2 B2) as q.
          repeat (autodimp q hyp); repnd; dands; auto; eauto 3 with slow. }
      }

      { eapply eq_term_equals_approx_if_cequivc; try (exact eqiff); auto. }
    }

    {
      apply CL_approx; unfold per_approx; exists a b; dands; spcast; tcsp.
      left; spcast; auto.
    }

    {
      unfold per_extensional in *.
      clear ext.
      repndors; spcast.

      { eapply cequivc_mkc_approx in extP; eauto; exrepnd.
        apply CL_approx; unfold per_approx; exists a' b'; dands; spcast; auto.
        { left; spcast; auto. }
        { eapply eq_term_equals_approx_if_cequivc; try (exact eqiff); auto. }
      }

      { repnd.
        repeat (autodimp extP0 hyp).
        pose proof (extP0 B2 B2) as q; repeat (autodimp q hyp); tcsp. }
    }

  - Case "CL_cequiv".
    clear per.

    dands.

    {
      spcast.
      dup ceqa as ceq1.
      eapply cequivc_mkc_cequiv in ceqa;[|eauto]; exrepnd.
      apply CL_cequiv; unfold per_cequiv; exists a' b'; dands; spcast; tcsp.

      {
        unfold per_extensional in *.
        clear ext.
        repndors; spcast.

        { left; spcast.
          eapply cequivc_trans;[apply cequivc_sym;exact ceq1|].
          eapply cequivc_trans;[|exact ceqb].
          eapply cequivc_trans;[|exact extP]; auto. }

        { right; repnd.
          repeat (autodimp extP0 hyp).
          pose proof (extP0 B2 B2) as q.
          repeat (autodimp q hyp); repnd; dands; auto; eauto 3 with slow. }
      }

      { eapply eq_term_equals_cequiv_if_cequivc; try (exact eqiff); auto. }
    }

    {
      apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; tcsp.
      left; spcast; auto.
    }

    {
      unfold per_extensional in *.
      clear ext.
      repndors; spcast.

      { eapply cequivc_mkc_cequiv in extP; eauto; exrepnd.
        apply CL_cequiv; unfold per_cequiv; exists a' b'; dands; spcast; auto.
        { left; spcast; auto. }
        { eapply eq_term_equals_cequiv_if_cequivc; try (exact eqiff); auto. }
      }

      { repnd.
        repeat (autodimp extP0 hyp).
        pose proof (extP0 B2 B2) as q; repeat (autodimp q hyp); tcsp. }
    }

  - Case "CL_eq".
    clear per.

    dands.

    {
      spcast.
      dup ceqa as ceq1.
      eapply cequivc_mkc_equality in ceqa;[|eauto]; exrepnd.
      apply CL_eq; unfold per_eq; exists T'0 a' b' eqa ; dands; spcast; tcsp.

      {
        unfold per_extensional in *.
        clear ext.
        repndors; spcast.

        { left; spcast.
          eapply cequivc_trans;[apply cequivc_sym; exact ceq1|].
          eapply cequivc_trans;[|exact ceqb]; auto. }

        { right; repnd.
          repeat (autodimp extP0 hyp).
          pose proof (extP0 B2 B2) as q.
          repeat (autodimp q hyp); repnd; dands; auto; eauto 3 with slow. }
      }

      {
        repeat (autodimp IHcl hyp).
        pose proof (IHcl T'0 T'0) as q.
        repeat (autodimp q hyp); tcsp.
      }

Lemma per_eq_eq_preserves_cequivc {o} :
  forall lib (t1 t2 t3 t4 : @CTerm o) eq,
    cequivc lib t1 t3
    -> cequivc lib t2 t4
    -> (per_eq_eq lib t1 t2 eq) <=2=> (per_eq_eq lib t3 t4 eq).
Proof.
  introv ceq1 ceq2; introv; unfold per_eq_eq; split; intro h; exrepnd; spcast.

  - eexists; eexists; eexists; eexists; dands; spcast; try (exact h0); try (exact h2); auto.

Qed.

      { eapply eq_term_equals_cequiv_if_cequivc; try (exact eqiff); auto. }
    }

    {
      apply CL_cequiv; unfold per_cequiv; exists a b; dands; spcast; tcsp.
      left; spcast; auto.
    }

    {
      unfold per_extensional in *.
      clear ext.
      repndors; spcast.

      { eapply cequivc_mkc_cequiv in extP; eauto; exrepnd.
        apply CL_cequiv; unfold per_cequiv; exists a' b'; dands; spcast; auto.
        { left; spcast; auto. }
        { eapply eq_term_equals_cequiv_if_cequivc; try (exact eqiff); auto. }
      }

      { repnd.
        repeat (autodimp extP0 hyp).
        pose proof (extP0 B2 B2) as q; repeat (autodimp q hyp); tcsp. }
    }

Qed.

Lemma close_symmetric {o} :
  forall lib ts (T T' : @CTerm o) eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> close lib ts T T' eq
    -> close lib ts T' T eq.
Proof.
  introv tysys dou cl.
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
      apply CL_atom; unfold per_atom; dands; spcast; auto.
      unfold per_extensional; tcsp.
      left; spcast; apply cequivc_sym; auto.

    + eapply equal_to_atom; eauto.

  - Case "CL_uatom".
    clear per.
    unfold per_extensional in *.
    clear extP.
    repndors; repnd; spcast.

    + applydup @cequivc_uatom in ext; auto.
      apply CL_uatom; unfold per_uatom; dands; spcast; auto.
      unfold per_extensional; tcsp.
      left; spcast; apply cequivc_sym; auto.

    + eapply equal_to_uatom; eauto.

  - Case "CL_base".
    clear per.
    unfold per_extensional in *.
    clear extP.
    repndors; repnd; spcast.

    + applydup @cequivc_base in ext; auto.
      apply CL_base; unfold per_base; dands; spcast; auto.
      unfold per_extensional; tcsp.
      left; spcast; apply cequivc_sym; auto.

    + eapply equal_to_base; eauto.

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

  - Case "CL_cequiv".
    clear per.
    unfold per_extensional in *.
    clear extP.
    repndors; repnd; spcast.

    + dup ext as ceq.
      eapply cequivc_mkc_cequiv in ceq;[|eauto].
      exrepnd.
      apply CL_cequiv; unfold per_cequiv.
      exists a' b'; dands; spcast; auto.
      { unfold per_extensional; tcsp.
        left; spcast; apply cequivc_sym; auto. }
      { eapply eq_term_equals_trans;[eauto|].
        intros u v.
        split; intro h; spcast.
        { eapply cequivc_trans;[|eauto].
          eapply cequivc_trans;[apply cequivc_sym;eauto|].
          auto. }
        { eapply cequivc_trans;[|apply cequivc_sym;eauto].
          eapply cequivc_trans;[eauto|].
          auto. }
      }

    + eapply equal_to_cequiv; eauto.

  - Case "CL_eq".
    clear per.
    unfold per_extensional in *.
    clear extP.
    repndors; repnd; spcast.

    + dup ext as ceq.
      eapply cequivc_mkc_equality in ceq;[|eauto].
      exrepnd.
      apply CL_eq; unfold per_eq.
      exists T'0 a' b' eqa; dands; spcast; auto.
      { unfold per_extensional; tcsp.
        left; spcast; apply cequivc_sym; auto. }
      { (* Should we prove that close preserves cequivc first? *)
      }
      { eapply eq_term_equals_trans;[eauto|].
        intros u v.
        split; intro h; spcast.
        { eapply cequivc_trans;[|eauto].
          eapply cequivc_trans;[apply cequivc_sym;eauto|].
          auto. }
        { eapply cequivc_trans;[|apply cequivc_sym;eauto].
          eapply cequivc_trans;[eauto|].
          auto. }
      }

    + eapply equal_to_cequiv; eauto.

Qed.
