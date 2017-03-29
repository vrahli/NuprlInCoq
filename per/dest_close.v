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


Require Import type_sys.

Lemma dest_close_per_func_l {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_function A v B)
    -> close lib ts T T' eq
    -> per_func lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_func_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_function A v B)
    -> close lib ts T T' eq
    -> per_func lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_isect_l {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_isect A v B)
    -> close lib ts T T' eq
    -> per_isect lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_isect_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_isect A v B)
    -> close lib ts T T' eq
    -> per_isect lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_eisect_l {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_eisect A v B)
    -> close lib ts T T' eq
    -> per_eisect lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_eisect_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_eisect A v B)
    -> close lib ts T T' eq
    -> per_eisect lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_product_l {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_product A v B)
    -> close lib ts T T' eq
    -> per_product lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_product_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_product A v B)
    -> close lib ts T T' eq
    -> per_product lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_w_l {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_w A v B)
    -> close lib ts T T' eq
    -> per_w lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_w_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_w A v B)
    -> close lib ts T T' eq
    -> per_w lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_m_l {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_m A v B)
    -> close lib ts T T' eq
    -> per_m lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_m_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_m A v B)
    -> close lib ts T T' eq
    -> per_m lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_pw_l {p} :
  forall lib (ts : cts(p)) T P ap A bp ba B cp ca cb C p T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_pw P ap A bp ba B cp ca cb C p)
    -> close lib ts T T' eq
    -> per_pw lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_pw_r {p} :
  forall lib (ts : cts(p)) T P ap A bp ba B cp ca cb C p T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_pw P ap A bp ba B cp ca cb C p)
    -> close lib ts T T' eq
    -> per_pw lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_pm_l {p} :
  forall lib (ts : cts(p)) T P ap A bp ba B cp ca cb C p T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_pm P ap A bp ba B cp ca cb C p)
    -> close lib ts T T' eq
    -> per_pm lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_pm_r {p} :
  forall lib (ts : cts(p)) T P ap A bp ba B cp ca cb C p T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_pm P ap A bp ba B cp ca cb C p)
    -> close lib ts T T' eq
    -> per_pm lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_disect_l {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_disect A v B)
    -> close lib ts T T' eq
    -> per_disect lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_disect_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_disect A v B)
    -> close lib ts T T' eq
    -> per_disect lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_set_l {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_set A v B)
    -> close lib ts T T' eq
    -> per_set lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_set_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_set A v B)
    -> close lib ts T T' eq
    -> per_set lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_tunion_l {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_tunion A v B)
    -> close lib ts T T' eq
    -> per_tunion lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_tunion_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_tunion A v B)
    -> close lib ts T T' eq
    -> per_tunion lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_approx_l {p} :
  forall lib (ts : cts(p)) T A B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_approx A B)
    -> close lib ts T T' eq
    -> per_approx lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_approx_r {p} :
  forall lib (ts : cts(p)) T A B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_approx A B)
    -> close lib ts T T' eq
    -> per_approx lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_cequiv_l {p} :
  forall lib (ts : cts(p)) T A B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_cequiv A B)
    -> close lib ts T T' eq
    -> per_cequiv lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_cequiv_r {p} :
  forall lib (ts : cts(p)) T A B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_cequiv A B)
    -> close lib ts T T' eq
    -> per_cequiv lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_texc_l {p} :
  forall lib (ts : cts(p)) T A B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_texc A B)
    -> close lib ts T T' eq
    -> per_texc lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_texc_r {p} :
  forall lib (ts : cts(p)) T A B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_texc A B)
    -> close lib ts T T' eq
    -> per_texc lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_union_l {p} :
  forall lib (ts : cts(p)) T A B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_union A B)
    -> close lib ts T T' eq
    -> per_union lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_union_r {p} :
  forall lib (ts : cts(p)) T A B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_union A B)
    -> close lib ts T T' eq
    -> per_union lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_eunion_l {p} :
  forall lib (ts : cts(p)) T A B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_eunion A B)
    -> close lib ts T T' eq
    -> per_eunion lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_eunion_r {p} :
  forall lib (ts : cts(p)) T A B T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_eunion A B)
    -> close lib ts T T' eq
    -> per_eunion lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_image_l {p} :
  forall lib (ts : cts(p)) T A f T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_image A f)
    -> close lib ts T T' eq
    -> per_image lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_image_r {p} :
  forall lib (ts : cts(p)) T A f T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_image A f)
    -> close lib ts T T' eq
    -> per_image lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_partial_l {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_partial A)
    -> close lib ts T T' eq
    -> per_partial lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_partial_r {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_partial A)
    -> close lib ts T T' eq
    -> per_partial lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_admiss_l {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_admiss A)
    -> close lib ts T T' eq
    -> per_admiss lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_admiss_r {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_admiss A)
    -> close lib ts T T' eq
    -> per_admiss lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_mono_l {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_mono A)
    -> close lib ts T T' eq
    -> per_mono lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_mono_r {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_mono A)
    -> close lib ts T T' eq
    -> per_mono lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_ffatom_l {p} :
  forall lib (ts : cts(p)) T A x a T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_free_from_atom A x a)
    -> close lib ts T T' eq
    -> per_ffatom lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_ffatom_r {p} :
  forall lib (ts : cts(p)) T A x a T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_free_from_atom A x a)
    -> close lib ts T T' eq
    -> per_ffatom lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_effatom_l {p} :
  forall lib (ts : cts(p)) T A x a T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_efree_from_atom A x a)
    -> close lib ts T T' eq
    -> per_effatom lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_effatom_r {p} :
  forall lib (ts : cts(p)) T A x a T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_efree_from_atom A x a)
    -> close lib ts T T' eq
    -> per_effatom lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_ffatoms_l {p} :
  forall lib (ts : cts(p)) T A x T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_free_from_atoms A x)
    -> close lib ts T T' eq
    -> per_ffatoms lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_ffatoms_r {p} :
  forall lib (ts : cts(p)) T A x T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_free_from_atoms A x)
    -> close lib ts T T' eq
    -> per_ffatoms lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_pertype_l {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_pertype A)
    -> close lib ts T T' eq
    -> per_pertype lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_pertype_r {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_pertype A)
    -> close lib ts T T' eq
    -> per_pertype lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_ipertype_l {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_ipertype A)
    -> close lib ts T T' eq
    -> per_ipertype lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_ipertype_r {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_ipertype A)
    -> close lib ts T T' eq
    -> per_ipertype lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_spertype_l {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_spertype A)
    -> close lib ts T T' eq
    -> per_spertype lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_spertype_r {p} :
  forall lib (ts : cts(p)) T A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_spertype A)
    -> close lib ts T T' eq
    -> per_spertype lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_equality_l {p} :
  forall lib (ts : cts(p)) T a b A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_equality a b A)
    -> close lib ts T T' eq
    -> per_eq lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_equality_r {p} :
  forall lib (ts : cts(p)) T a b A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_equality a b A)
    -> close lib ts T T' eq
    -> per_eq lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_requality_l {p} :
  forall lib (ts : cts(p)) T a b A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_requality a b A)
    -> close lib ts T T' eq
    -> per_req lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_requality_r {p} :
  forall lib (ts : cts(p)) T a b A T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_requality a b A)
    -> close lib ts T T' eq
    -> per_req lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_tequality_l {p} :
  forall lib (ts : cts(p)) T a b T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_tequality a b)
    -> close lib ts T T' eq
    -> per_teq lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_tequality_r {p} :
  forall lib (ts : cts(p)) T a b T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_tequality a b)
    -> close lib ts T T' eq
    -> per_teq lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_base_l {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T mkc_base
    -> close lib ts T T' eq
    -> per_base lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_base_r {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' mkc_base
    -> close lib ts T T' eq
    -> per_base lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_int_l {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T mkc_int
    -> close lib ts T T' eq
    -> per_int lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_int_r {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' mkc_int
    -> close lib ts T T' eq
    -> per_int lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_atom_l {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T mkc_atom
    -> close lib ts T T' eq
    -> per_atom lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_atom_r {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' mkc_atom
    -> close lib ts T T' eq
    -> per_atom lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_uatom_l {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T mkc_uatom
    -> close lib ts T T' eq
    -> per_uatom lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_uatom_r {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' mkc_uatom
    -> close lib ts T T' eq
    -> per_uatom lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_uni_l {p} :
  forall lib (ts : cts(p)) T i T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_uni i)
    -> close lib ts T T' eq
    -> ts T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_uni_r {p} :
  forall lib (ts : cts(p)) T i T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_uni i)
    -> close lib ts T T' eq
    -> ts T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_tuni_l {p} :
  forall lib (ts : cts(p)) T i T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_tuni i)
    -> close lib ts T T' eq
    -> ts T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_tuni_r {p} :
  forall lib (ts : cts(p)) T i T' eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T' (mkc_tuni i)
    -> close lib ts T T' eq
    -> ts T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.


Ltac dest_close_lr h :=
  match goal with

    (* function *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_function ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_l lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_function ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_r lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* isect *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_isect ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_isect_l lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_isect ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_isect_r lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* eisect *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_eisect ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eisect_l lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_eisect ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eisect_r lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* disect*)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_disect ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_disect_l lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_disect ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_disect_r lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* product *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_product ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_product_l lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_product ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_product_r lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* w *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_w ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_w_l lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_w ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_w_r lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* m *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_m ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_m_l lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_m ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_m_r lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pw *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pw ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pw_l lib ts T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pw ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pw_r lib ts T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pm *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pm ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pm_l lib ts T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pm ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pm_r lib ts T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (*  set *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_set ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_set_l lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_set ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_set_r lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (*  tunion *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tunion ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tunion_l lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tunion ?A ?v ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tunion_r lib ts T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* approx *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_approx ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_approx_l lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_approx ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_approx_r lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* cequiv *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_cequiv ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_cequiv_l lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_cequiv ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_cequiv_r lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* texc *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_texc ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_texc_l lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_texc ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_texc_r lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* union *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_union ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_union_l lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_union ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_union_r lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* eunion *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_eunion ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eunion_l lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_eunion ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eunion_r lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* image *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_image ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_image_l lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_image ?A ?B),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_image_r lib ts T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* partial *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_partial ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_partial_l lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_partial ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_partial_r lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* admiss *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_admiss ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_admiss_l lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_admiss ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_admiss_r lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* mono *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_mono ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_mono_l lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_mono ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_mono_r lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* free_from_atom *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_free_from_atom ?A ?x ?a),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatom_l lib ts T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_free_from_atom ?A ?x ?a),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatom_r lib ts T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* efree_from_atom *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_efree_from_atom ?A ?x ?a),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_effatom_l lib ts T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_efree_from_atom ?A ?x ?a),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_effatom_r lib ts T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* free_from_atoms *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_free_from_atoms ?A ?x),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatoms_l lib ts T A x T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_free_from_atoms ?A ?x),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatoms_r lib ts T A x T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pertype *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pertype ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pertype_l lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pertype ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pertype_r lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* ipertype *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_ipertype ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ipertype_l lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_ipertype ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ipertype_r lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* spertype *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_spertype ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_spertype_l lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_spertype ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_spertype_r lib ts T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* equality *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_equality ?a ?b ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_l lib ts T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_equality ?a ?b ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_r lib ts T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* requality *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_requality ?a ?b ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_requality_l lib ts T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_requality ?a ?b ?A),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_requality_r lib ts T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* tequality *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tequality ?a ?b),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tequality_l lib ts T a b T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tequality ?a ?b),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tequality_r lib ts T a b T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* base *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T mkc_base,
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_l lib ts T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_base,
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_r lib ts T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* int *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T mkc_int,
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_l lib ts T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_int,
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_r lib ts T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* atom *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T mkc_atom,
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_l lib ts T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_atom,
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_r lib ts T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* uatom *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T mkc_uatom,
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_l lib ts T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_uatom,
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_r lib ts T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* uni *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_uni ?i),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uni_l lib ts T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_uni ?i),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uni_r lib ts T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* tuni *)
    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tuni ?i),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tuni_l lib ts T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?lib ?ts,
        H2 : defines_only_universes ?lib ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tuni ?i),
        H4 : close ?lib ?ts ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tuni_r lib ts T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

  end.

Ltac dclose_lr := repeat (let h := fresh "h" in dest_close_lr h).
