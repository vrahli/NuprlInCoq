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
Require Export bar.
Require Export decompose_alphaeq.


Ltac close_diff_bar :=
  allunfold_per;
  match goal with
  | [ comp1 : computes_to_valc ?lib ?T _,
      bar   : BarLib ?M ?lib,
      comp2 : all_in_bar ?bar (fun v => ccomputes_to_valc v ?T _)
    |- _ ] =>

    let h1   := fresh "h1" in
    let h2   := fresh "h2" in
    let h3   := fresh "h3" in
    let xxx  := fresh "xxx" in
    let lib' := fresh "lib'" in
    pose proof (bar_non_empty bar) as h1;
    destruct h1 as [lib' h1];
    pose proof (comp2 lib' h1 lib' (lib_extends_refl M lib')) as h2; simpl in h2; spcast;
    pose proof (computes_to_valc_preserves_lib_extends M lib lib') as h3;
    autodimp h3 xxx; eauto 2 with slow;[];
    apply h3 in comp1; exrepnd; clear h3;
    try alphaeqc_decompose;
    try computes_to_valc_diff
  end.

Ltac close_diff_ext :=
  allunfold_per;
  match goal with
  | [ comp1 : computes_to_valc ?lib ?T _,
      comp2 : in_ext ?M ?lib (fun v => ccomputes_to_valc v ?T _)
    |- _ ] =>

    let h1  := fresh "h1" in
    let xxx := fresh "xxx" in
    pose proof (comp2 lib) as h1; simpl in h1;
      autodimp h1 xxx; eauto 2 with slow;[]; spcast;
    try computes_to_valc_diff
  end.

Ltac close_diff_all :=
  first [ complete auto
        | close_diff
        | close_diff_bar
        | close_diff_ext
        ].

Lemma dest_close_per_func_l {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_function A v B)
    -> close M ts lib T T' eq
    -> per_func_ext M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; clear cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_r {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_function A v B)
    -> close M ts lib T T' eq
    -> per_func_ext M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_isect_l {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_isect A v B)
    -> close M ts lib T T' eq
    -> per_isect M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_isect_r {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_isect A v B)
    -> close M ts lib T T' eq
    -> per_isect M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

(*Lemma dest_close_per_eisect_l {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_eisect A v B)
    -> close M ts lib T T' eq
    -> per_eisect (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_eisect_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_eisect A v B)
    -> close lib ts T T' eq
    -> per_eisect lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.*)

Lemma dest_close_per_product_l {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_product A v B)
    -> close M ts lib T T' eq
    -> per_product_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_product_r {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_product A v B)
    -> close M ts lib T T' eq
    -> per_product_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_w_l {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_w A v B)
    -> close M ts lib T T' eq
    -> per_w M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_w_r {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_w A v B)
    -> close M ts lib T T' eq
    -> per_w M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_m_l {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_m A v B)
    -> close M ts lib T T' eq
    -> per_m M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_m_r {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_m A v B)
    -> close M ts lib T T' eq
    -> per_m M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pw_l {p} :
  forall M (ts : cts(p)) lib T P ap A bp ba B cp ca cb C p T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_pw P ap A bp ba B cp ca cb C p)
    -> close M ts lib T T' eq
    -> per_pw M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pw_r {p} :
  forall M (ts : cts(p)) lib T P ap A bp ba B cp ca cb C p T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_pw P ap A bp ba B cp ca cb C p)
    -> close M ts lib T T' eq
    -> per_pw M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pm_l {p} :
  forall M (ts : cts(p)) lib T P ap A bp ba B cp ca cb C p T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_pm P ap A bp ba B cp ca cb C p)
    -> close M ts lib T T' eq
    -> per_pm M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pm_r {p} :
  forall M (ts : cts(p)) lib T P ap A bp ba B cp ca cb C p T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_pm P ap A bp ba B cp ca cb C p)
    -> close M ts lib T T' eq
    -> per_pm M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_disect_l {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_disect A v B)
    -> close M ts lib T T' eq
    -> per_disect M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_disect_r {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_disect A v B)
    -> close M ts lib T T' eq
    -> per_disect M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_set_l {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_set A v B)
    -> close M ts lib T T' eq
    -> per_set M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_set_r {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_set A v B)
    -> close M ts lib T T' eq
    -> per_set M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tunion_l {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_tunion A v B)
    -> close M ts lib T T' eq
    -> per_tunion M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tunion_r {p} :
  forall M (ts : cts(p)) lib T A v B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_tunion A v B)
    -> close M ts lib T T' eq
    -> per_tunion M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_approx_l {p} :
  forall M (ts : cts(p)) lib T A B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_approx A B)
    -> close M ts lib T T' eq
    -> per_approx_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_approx_r {p} :
  forall M (ts : cts(p)) lib T A B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_approx A B)
    -> close M ts lib T T' eq
    -> per_approx_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_cequiv_l {p} :
  forall M (ts : cts(p)) lib T A B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_cequiv A B)
    -> close M ts lib T T' eq
    -> per_cequiv_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_cequiv_r {p} :
  forall M (ts : cts(p)) lib T A B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_cequiv A B)
    -> close M ts lib T T' eq
    -> per_cequiv_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_texc_l {p} :
  forall M (ts : cts(p)) lib T A B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_texc A B)
    -> close M ts lib T T' eq
    -> per_texc M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_texc_r {p} :
  forall M (ts : cts(p)) lib T A B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_texc A B)
    -> close M ts lib T T' eq
    -> per_texc M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_union_l {p} :
  forall M (ts : cts(p)) lib T A B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_union A B)
    -> close M ts lib T T' eq
    -> per_union_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_union_r {p} :
  forall M (ts : cts(p)) lib T A B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_union A B)
    -> close M ts lib T T' eq
    -> per_union_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

(*Lemma dest_close_per_eunion_l {p} :
  forall M (ts : cts(p)) lib T A B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_eunion A B)
    -> close M ts lib T T' eq
    -> per_eunion M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_eunion_r {p} :
  forall M (ts : cts(p)) lib T A B T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_eunion A B)
    -> close M ts lib T T' eq
    -> per_eunion M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.*)

Lemma dest_close_per_image_l {p} :
  forall M (ts : cts(p)) lib T A f T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_image A f)
    -> close M ts lib T T' eq
    -> per_image M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_image_r {p} :
  forall M (ts : cts(p)) lib T A f T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_image A f)
    -> close M ts lib T T' eq
    -> per_image M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_partial_l {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_partial A)
    -> close M ts lib T T' eq
    -> per_partial M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_partial_r {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_partial A)
    -> close M ts lib T T' eq
    -> per_partial M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_admiss_l {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_admiss A)
    -> close M ts lib T T' eq
    -> per_admiss M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_admiss_r {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_admiss A)
    -> close M ts lib T T' eq
    -> per_admiss M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_mono_l {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_mono A)
    -> close M ts lib T T' eq
    -> per_mono M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_mono_r {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_mono A)
    -> close M ts lib T T' eq
    -> per_mono M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ffatom_l {p} :
  forall M (ts : cts(p)) lib T A x a T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_free_from_atom A x a)
    -> close M ts lib T T' eq
    -> per_ffatom M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ffatom_r {p} :
  forall M (ts : cts(p)) lib T A x a T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_free_from_atom A x a)
    -> close M ts lib T T' eq
    -> per_ffatom M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_effatom_l {p} :
  forall M (ts : cts(p)) lib T A x a T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_efree_from_atom A x a)
    -> close M ts lib T T' eq
    -> per_effatom M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_effatom_r {p} :
  forall M (ts : cts(p)) lib T A x a T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_efree_from_atom A x a)
    -> close M ts lib T T' eq
    -> per_effatom M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ffatoms_l {p} :
  forall M (ts : cts(p)) lib T A x T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_free_from_atoms A x)
    -> close M ts lib T T' eq
    -> per_ffatoms M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ffatoms_r {p} :
  forall M (ts : cts(p)) lib T A x T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_free_from_atoms A x)
    -> close M ts lib T T' eq
    -> per_ffatoms M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pertype_l {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_pertype A)
    -> close M ts lib T T' eq
    -> per_pertype M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pertype_r {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_pertype A)
    -> close M ts lib T T' eq
    -> per_pertype M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ipertype_l {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_ipertype A)
    -> close M ts lib T T' eq
    -> per_ipertype M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ipertype_r {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_ipertype A)
    -> close M ts lib T T' eq
    -> per_ipertype M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_spertype_l {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_spertype A)
    -> close M ts lib T T' eq
    -> per_spertype M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_spertype_r {p} :
  forall M (ts : cts(p)) lib T A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_spertype A)
    -> close M ts lib T T' eq
    -> per_spertype M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_l {p} :
  forall M (ts : cts(p)) lib T a b A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_equality a b A)
    -> close M ts lib T T' eq
    -> per_eq_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_r {p} :
  forall M (ts : cts(p)) lib T a b A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_equality a b A)
    -> close M ts lib T T' eq
    -> per_eq_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_requality_l {p} :
  forall M (ts : cts(p)) lib T a b A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_requality a b A)
    -> close M ts lib T T' eq
    -> per_req M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_requality_r {p} :
  forall M (ts : cts(p)) lib T a b A T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_requality a b A)
    -> close M ts lib T T' eq
    -> per_req M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tequality_l {p} :
  forall M (ts : cts(p)) lib T a b T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_tequality a b)
    -> close M ts lib T T' eq
    -> per_teq M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tequality_r {p} :
  forall M (ts : cts(p)) lib T a b T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_tequality a b)
    -> close M ts lib T T' eq
    -> per_teq M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_base_l {p} :
  forall M (ts : cts(p)) lib T T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T mkc_base
    -> close M ts lib T T' eq
    -> per_base_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_base_r {p} :
  forall M (ts : cts(p)) lib T T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' mkc_base
    -> close M ts lib T T' eq
    -> per_base_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_int_l {p} :
  forall M (ts : cts(p)) lib T T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T mkc_int
    -> close M ts lib T T' eq
    -> per_int_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_int_r {p} :
  forall M (ts : cts(p)) lib T T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' mkc_int
    -> close M ts lib T T' eq
    -> per_int_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_atom_l {p} :
  forall M (ts : cts(p)) lib T T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T mkc_atom
    -> close M ts lib T T' eq
    -> per_atom_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_atom_r {p} :
  forall M (ts : cts(p)) lib T T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' mkc_atom
    -> close M ts lib T T' eq
    -> per_atom_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_uatom_l {p} :
  forall M (ts : cts(p)) lib T T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T mkc_uatom
    -> close M ts lib T T' eq
    -> per_uatom_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_uatom_r {p} :
  forall M (ts : cts(p)) lib T T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' mkc_uatom
    -> close M ts lib T T' eq
    -> per_uatom_bar M (close M ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_uni_l {p} :
  forall M (ts : cts(p)) lib T i T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_uni i)
    -> close M ts lib T T' eq
    -> ts lib  T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_uni_r {p} :
  forall M (ts : cts(p)) lib T i T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_uni i)
    -> close M ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tuni_l {p} :
  forall M (ts : cts(p)) lib T i T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_tuni i)
    -> close M ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tuni_r {p} :
  forall M (ts : cts(p)) lib T i T' eq,
    type_system M ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_tuni i)
    -> close M ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.


Ltac dest_close_lr h :=
  match goal with

    (* function *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_function ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_l M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_function ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_r M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* isect *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_isect ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_isect_l M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_isect ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_isect_r M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

(*    (* eisect *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_eisect ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eisect_l M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_eisect ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eisect_r M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h
 *)

    (* disect*)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_disect ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_disect_l M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_disect ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_disect_r M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* product *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_product ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_product_l M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_product ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_product_r M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* w *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_w ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_w_l M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_w ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_w_r M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* m *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_m ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_m_l M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_m ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_m_r M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pw *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pw ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pw_l M ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pw ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pw_r M ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pm *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pm ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pm_l M ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pm ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pm_r M ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (*  set *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_set ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_set_l M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_set ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_set_r M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (*  tunion *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tunion ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tunion_l M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tunion ?A ?v ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tunion_r M ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* approx *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_approx ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_approx_l M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_approx ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_approx_r M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* cequiv *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_cequiv ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_cequiv_l M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_cequiv ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_cequiv_r M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* texc *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_texc ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_texc_l M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_texc ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_texc_r M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* union *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_union ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_union_l M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_union ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_union_r M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

(*    (* eunion *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_eunion ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eunion_l M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_eunion ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eunion_r M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h
*)

    (* image *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_image ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_image_l M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_image ?A ?B),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_image_r M ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* partial *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_partial ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_partial_l M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_partial ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_partial_r M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* admiss *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_admiss ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_admiss_l M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_admiss ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_admiss_r M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* mono *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_mono ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_mono_l M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_mono ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_mono_r M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* free_from_atom *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_free_from_atom ?A ?x ?a),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatom_l M ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_free_from_atom ?A ?x ?a),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatom_r M ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* efree_from_atom *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_efree_from_atom ?A ?x ?a),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_effatom_l M ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_efree_from_atom ?A ?x ?a),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_effatom_r M ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* free_from_atoms *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_free_from_atoms ?A ?x),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatoms_l M ts lib T A x T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_free_from_atoms ?A ?x),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatoms_r M ts lib T A x T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pertype *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pertype ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pertype_l M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pertype ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pertype_r M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* ipertype *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_ipertype ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ipertype_l M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_ipertype ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ipertype_r M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* spertype *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_spertype ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_spertype_l M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_spertype ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_spertype_r M ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* equality *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_equality ?a ?b ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_l M ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_equality ?a ?b ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_r M ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* requality *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_requality ?a ?b ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_requality_l M ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_requality ?a ?b ?A),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_requality_r M ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* tequality *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tequality ?a ?b),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tequality_l M ts lib T a b T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tequality ?a ?b),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tequality_r M ts lib T a b T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* base *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_base,
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_l M ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_base,
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_r M ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* int *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_int,
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_l M ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_int,
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_r M ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* atom *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_atom,
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_l M ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_atom,
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_r M ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* uatom *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_uatom,
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_l M ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_uatom,
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_r M ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* uni *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_uni ?i),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uni_l M ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_uni ?i),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uni_r M ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* tuni *)
    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tuni ?i),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tuni_l M ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?M ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tuni ?i),
        H4 : close ?M ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tuni_r M ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

  end.

Ltac dclose_lr := repeat (let h := fresh "h" in dest_close_lr h).
