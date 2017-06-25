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
  allunfold_per; spcast;
  match goal with
  | [ comp1 : computes_to_valc ?lib ?T _,
      bar   : BarLib ?lib,
      comp2 : all_in_bar ?bar (fun v => ccomputes_to_valc v ?T _)
    |- _ ] =>

    let h1   := fresh "h1" in
    let h2   := fresh "h2" in
    let h3   := fresh "h3" in
    let xxx  := fresh "xxx" in
    let lib' := fresh "lib'" in
    pose proof (bar_non_empty bar) as h1;
    destruct h1 as [lib' h1];
    pose proof (comp2 lib' h1 lib' (lib_extends_refl lib')) as h2; simpl in h2; spcast;
    pose proof (computes_to_valc_preserves_lib_extends lib lib') as h3;
    autodimp h3 xxx; eauto 2 with slow;[];
    apply h3 in comp1; exrepnd; clear h3;
    try alphaeqc_decompose;
    try computes_to_valc_diff
  end.

Ltac close_diff_ext :=
  allunfold_per; spcast;
  match goal with
  | [ comp1 : computes_to_valc ?lib ?T _,
      comp2 : in_ext ?lib (fun v => ccomputes_to_valc v ?T _)
    |- _ ] =>

    let h1  := fresh "h1" in
    let xxx := fresh "xxx" in
    pose proof (comp2 lib) as h1; simpl in h1;
      autodimp h1 xxx; eauto 2 with slow;[]; spcast;
    try computes_to_valc_diff
  end.

Ltac close_diff_bar_bar :=
  allunfold_per;
  match goal with
  | [ H1 : all_in_bar ?bar1 (fun lib => ?T ===>(lib) _),
      H2 : all_in_bar ?bar2 (fun lib => ?T ===>(lib) _) |- _ ] =>
    let h    := fresh "h" in
    let a1   := fresh "a1" in
    let b1   := fresh "b1" in
    let a2   := fresh "a2" in
    let b2   := fresh "b2" in
    let lib1 := fresh "lib1" in
    let lib2 := fresh "lib2" in
    let lib' := fresh "lib'" in
    let xxx  := fresh "xxx" in
    pose proof (ex_extends_two_bars bar1 bar2) as h;
      destruct h as [lib1 h];
      destruct h as [lib2 h];
      destruct h as [lib' h];
      exrepnd;
      pose proof (H1 lib1) as a1; autodimp a1 xxx;
        pose proof (H2 lib2) as b1; autodimp b1 xxx;
          pose proof (a1 lib') as a2; autodimp a2 xxx;
            pose proof (b1 lib') as b2; autodimp b2 xxx;
              simpl in a2,b2;
              try (spcast; computes_to_valc_diff)
  end.

Ltac close_diff_ext_bar :=
  allunfold_per;
  match goal with
  | [ H1 : in_ext ?lib (fun lib => ?T ===>(lib) _),
      H2 : all_in_bar ?bar (fun lib => ?T ===>(lib) _) |- _ ] =>
    let h    := fresh "h" in
    let a1   := fresh "a1" in
    let b1   := fresh "b1" in
    let b2   := fresh "b2" in
    let lib' := fresh "lib'" in
    let xxx  := fresh "xxx" in
    pose proof (bar_non_empty bar) as h;
    destruct h as [lib' h];
    pose proof (H1 lib') as a1; autodimp a1 xxx; eauto 2 with slow; simpl in a1;
    pose proof (H2 lib') as b1; autodimp b1 xxx;
    pose proof (b1 lib') as b2; autodimp b2 xxx; eauto 2 with slow; simpl in b2;
    spcast;
    try computes_to_valc_diff
  end.

Ltac close_diff_init_bar_left :=
  allunfold_per;
  match goal with
  | [ M  : type_monotone ?ts,
      H1 : ?ts ?lib ?T ?T' ?per,
      H2 : all_in_bar ?bar (fun lib => ?T ===>(lib) _) |- _ ] =>
    let h    := fresh "h"    in
    let a1   := fresh "a1"   in
    let b1   := fresh "b1"   in
    let b2   := fresh "b2"   in
    let lib' := fresh "lib'" in
    let xxx  := fresh "xxx"  in
    let eq'  := fresh "eq'"  in
    pose proof (bar_non_empty bar) as h;
    destruct h as [lib' h];
    pose proof (M lib lib' T T' per) as a1;
    repeat (autodimp a1 xxx); eauto 2 with slow;
    clear H1;
    destruct a1 as [eq' a1];
    try (apply_defines_only_universes);
    uncast;
    pose proof (H2 lib') as b1; autodimp b1 xxx; eauto 2 with slow; simpl in b1;
    pose proof (b1 lib') as b2; autodimp b2 xxx; eauto 2 with slow; simpl in b2;
    spcast;
    try computes_to_valc_diff
  end.

Ltac close_diff_init_bar_right :=
  allunfold_per;
  match goal with
  | [ M  : type_monotone ?ts,
      H1 : ?ts ?lib ?T' ?T ?per,
      H2 : all_in_bar ?bar (fun lib => ?T ===>(lib) _) |- _ ] =>
    let h    := fresh "h"    in
    let a1   := fresh "a1"   in
    let b1   := fresh "b1"   in
    let b2   := fresh "b2"   in
    let lib' := fresh "lib'" in
    let xxx  := fresh "xxx"  in
    let eq'  := fresh "eq'"  in
    pose proof (bar_non_empty bar) as h;
    destruct h as [lib' h];
    pose proof (M lib lib' T' T per) as a1;
    repeat (autodimp a1 xxx); eauto 2 with slow;
    clear H1;
    destruct a1 as [eq' a1];
    try (apply_defines_only_universes);
    uncast;
    pose proof (H2 lib') as b1; autodimp b1 xxx; eauto 2 with slow; simpl in b1;
    pose proof (b1 lib') as b2; autodimp b2 xxx; eauto 2 with slow; simpl in b2;
    spcast;
    try computes_to_valc_diff
  end.

Ltac close_diff_all :=
  first [ complete auto
        | close_diff
        | close_diff_bar
        | close_diff_ext
        | close_diff_bar_bar
        | close_diff_ext_bar
        | close_diff_init_bar_left
        | close_diff_init_bar_right
        ].

Lemma dest_close_per_int_l {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T mkc_int
    -> close ts lib T T' eq
    -> per_int_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_int_r {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' mkc_int
    -> close ts lib T T' eq
    -> per_int_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_int_bar_l {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) mkc_int)
    -> close ts lib T T' eq
    -> per_int_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  inversion cl; clear cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_int_bar_r {p} :
  forall (ts : cts(p)) lib T T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T' ===>(lib) mkc_int)
    -> close ts lib T T' eq
    -> per_int_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_function A v B)
    -> close ts lib T T' eq
    -> per_func_ext (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; clear cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_function A v B)
    -> close ts lib T T' eq
    -> per_func_ext (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_bar_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) (mkc_function A v B))
    -> close ts lib T T' eq
    -> per_func_ext (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  inversion cl; clear cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_bar_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T' ===>(lib) (mkc_function A v B))
    -> close ts lib T T' eq
    -> per_func_ext (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_isect_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_isect A v B)
    -> close ts lib T T' eq
    -> per_isect (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_isect_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_isect A v B)
    -> close ts lib T T' eq
    -> per_isect (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

(*Lemma dest_close_per_eisect_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_eisect A v B)
    -> close ts lib T T' eq
    -> per_eisect (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_eisect_r {p} :
  forall lib (ts : cts(p)) T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_eisect A v B)
    -> close lib ts T T' eq
    -> per_eisect lib (close lib ts) T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.*)

Lemma dest_close_per_product_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_product A v B)
    -> close ts lib T T' eq
    -> per_product_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_product_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_product A v B)
    -> close ts lib T T' eq
    -> per_product_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_w_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_w A v B)
    -> close ts lib T T' eq
    -> per_w (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_w_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_w A v B)
    -> close ts lib T T' eq
    -> per_w (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_m_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_m A v B)
    -> close ts lib T T' eq
    -> per_m (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_m_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_m A v B)
    -> close ts lib T T' eq
    -> per_m (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pw_l {p} :
  forall (ts : cts(p)) lib T P ap A bp ba B cp ca cb C p T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_pw P ap A bp ba B cp ca cb C p)
    -> close ts lib T T' eq
    -> per_pw (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pw_r {p} :
  forall (ts : cts(p)) lib T P ap A bp ba B cp ca cb C p T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_pw P ap A bp ba B cp ca cb C p)
    -> close ts lib T T' eq
    -> per_pw (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pm_l {p} :
  forall (ts : cts(p)) lib T P ap A bp ba B cp ca cb C p T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_pm P ap A bp ba B cp ca cb C p)
    -> close ts lib T T' eq
    -> per_pm (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pm_r {p} :
  forall (ts : cts(p)) lib T P ap A bp ba B cp ca cb C p T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_pm P ap A bp ba B cp ca cb C p)
    -> close ts lib T T' eq
    -> per_pm (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_disect_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_disect A v B)
    -> close ts lib T T' eq
    -> per_disect (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_disect_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_disect A v B)
    -> close ts lib T T' eq
    -> per_disect (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_set_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_set A v B)
    -> close ts lib T T' eq
    -> per_set (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_set_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_set A v B)
    -> close ts lib T T' eq
    -> per_set (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tunion_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_tunion A v B)
    -> close ts lib T T' eq
    -> per_tunion (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tunion_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_tunion A v B)
    -> close ts lib T T' eq
    -> per_tunion (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_approx_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_approx_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_approx_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_approx_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_cequiv_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_cequiv A B)
    -> close ts lib T T' eq
    -> per_cequiv_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_cequiv_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_cequiv A B)
    -> close ts lib T T' eq
    -> per_cequiv_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_texc_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_texc A B)
    -> close ts lib T T' eq
    -> per_texc (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_texc_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_texc A B)
    -> close ts lib T T' eq
    -> per_texc (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_union_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_union A B)
    -> close ts lib T T' eq
    -> per_union_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_union_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_union A B)
    -> close ts lib T T' eq
    -> per_union_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

(*Lemma dest_close_per_eunion_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_eunion A B)
    -> close ts lib T T' eq
    -> per_eunion (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_eunion_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_eunion A B)
    -> close ts lib T T' eq
    -> per_eunion (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.*)

Lemma dest_close_per_image_l {p} :
  forall (ts : cts(p)) lib T A f T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_image A f)
    -> close ts lib T T' eq
    -> per_image (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_image_r {p} :
  forall (ts : cts(p)) lib T A f T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_image A f)
    -> close ts lib T T' eq
    -> per_image (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_partial_l {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_partial A)
    -> close ts lib T T' eq
    -> per_partial (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_partial_r {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_partial A)
    -> close ts lib T T' eq
    -> per_partial (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_admiss_l {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_admiss A)
    -> close ts lib T T' eq
    -> per_admiss (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_admiss_r {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_admiss A)
    -> close ts lib T T' eq
    -> per_admiss (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_mono_l {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_mono A)
    -> close ts lib T T' eq
    -> per_mono (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_mono_r {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_mono A)
    -> close ts lib T T' eq
    -> per_mono (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ffatom_l {p} :
  forall (ts : cts(p)) lib T A x a T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_free_from_atom A x a)
    -> close ts lib T T' eq
    -> per_ffatom (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ffatom_r {p} :
  forall (ts : cts(p)) lib T A x a T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_free_from_atom A x a)
    -> close ts lib T T' eq
    -> per_ffatom (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_effatom_l {p} :
  forall (ts : cts(p)) lib T A x a T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_efree_from_atom A x a)
    -> close ts lib T T' eq
    -> per_effatom (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_effatom_r {p} :
  forall (ts : cts(p)) lib T A x a T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_efree_from_atom A x a)
    -> close ts lib T T' eq
    -> per_effatom (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ffatoms_l {p} :
  forall (ts : cts(p)) lib T A x T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_free_from_atoms A x)
    -> close ts lib T T' eq
    -> per_ffatoms (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ffatoms_r {p} :
  forall (ts : cts(p)) lib T A x T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_free_from_atoms A x)
    -> close ts lib T T' eq
    -> per_ffatoms (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pertype_l {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_pertype A)
    -> close ts lib T T' eq
    -> per_pertype (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_pertype_r {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_pertype A)
    -> close ts lib T T' eq
    -> per_pertype (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ipertype_l {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_ipertype A)
    -> close ts lib T T' eq
    -> per_ipertype (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_ipertype_r {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_ipertype A)
    -> close ts lib T T' eq
    -> per_ipertype (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_spertype_l {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_spertype A)
    -> close ts lib T T' eq
    -> per_spertype (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_spertype_r {p} :
  forall (ts : cts(p)) lib T A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_spertype A)
    -> close ts lib T T' eq
    -> per_spertype (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_l {p} :
  forall (ts : cts(p)) lib T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_eq_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_r {p} :
  forall (ts : cts(p)) lib T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_eq_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_requality_l {p} :
  forall (ts : cts(p)) lib T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_requality a b A)
    -> close ts lib T T' eq
    -> per_req (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_requality_r {p} :
  forall (ts : cts(p)) lib T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_requality a b A)
    -> close ts lib T T' eq
    -> per_req (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tequality_l {p} :
  forall (ts : cts(p)) lib T a b T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_tequality a b)
    -> close ts lib T T' eq
    -> per_teq (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tequality_r {p} :
  forall (ts : cts(p)) lib T a b T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_tequality a b)
    -> close ts lib T T' eq
    -> per_teq (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_base_l {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T mkc_base
    -> close ts lib T T' eq
    -> per_base_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_base_r {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' mkc_base
    -> close ts lib T T' eq
    -> per_base_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_atom_l {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T mkc_atom
    -> close ts lib T T' eq
    -> per_atom_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_atom_r {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' mkc_atom
    -> close ts lib T T' eq
    -> per_atom_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_uatom_l {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T mkc_uatom
    -> close ts lib T T' eq
    -> per_uatom_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_uatom_r {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' mkc_uatom
    -> close ts lib T T' eq
    -> per_uatom_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_uni_l {p} :
  forall (ts : cts(p)) lib T i T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_uni i)
    -> close ts lib T T' eq
    -> ts lib  T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_uni_r {p} :
  forall (ts : cts(p)) lib T i T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_uni i)
    -> close ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tuni_l {p} :
  forall (ts : cts(p)) lib T i T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_tuni i)
    -> close ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_tuni_r {p} :
  forall (ts : cts(p)) lib T i T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_tuni i)
    -> close ts lib T T' eq
    -> ts lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.


Ltac dest_close_lr h :=
  match goal with

    (* function *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_function ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_function ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* function bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T ===>(lib) (mkc_function ?A ?v ?B)),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_bar_l ts lib T A v B T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T' ===>(lib) (mkc_function ?A ?v ?B)),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_func_bar_r ts lib T A v B T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* isect *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_isect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_isect_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_isect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_isect_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

(*    (* eisect *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_eisect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eisect_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_eisect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eisect_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h
 *)

    (* disect*)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_disect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_disect_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_disect ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_disect_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* product *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_product ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_product_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_product ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_product_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* w *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_w ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_w_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_w ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_w_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* m *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_m ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_m_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_m ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_m_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pw *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pw ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pw_l ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pw ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pw_r ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pm *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pm ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pm_l ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pm ?P ?ap ?A ?bp ?ba ?B ?cp ?ca ?cb ?C ?p),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pm_r ts lib T P ap A bp ba B cp ca cb C p T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (*  set *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_set ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_set_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_set ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_set_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (*  tunion *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tunion ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tunion_l ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tunion ?A ?v ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tunion_r ts lib T A v B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* approx *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_approx ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_approx_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_approx ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_approx_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* cequiv *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_cequiv ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_cequiv_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_cequiv ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_cequiv_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* texc *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_texc ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_texc_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_texc ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_texc_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* union *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_union ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_union_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_union ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_union_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

(*    (* eunion *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_eunion ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eunion_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_eunion ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_eunion_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h
*)

    (* image *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_image ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_image_l ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_image ?A ?B),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_image_r ts lib T A B T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* partial *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_partial ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_partial_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_partial ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_partial_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* admiss *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_admiss ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_admiss_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_admiss ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_admiss_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* mono *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_mono ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_mono_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_mono ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_mono_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* free_from_atom *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_free_from_atom ?A ?x ?a),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatom_l ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_free_from_atom ?A ?x ?a),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatom_r ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* efree_from_atom *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_efree_from_atom ?A ?x ?a),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_effatom_l ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_efree_from_atom ?A ?x ?a),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_effatom_r ts lib T A x a T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* free_from_atoms *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_free_from_atoms ?A ?x),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatoms_l ts lib T A x T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_free_from_atoms ?A ?x),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ffatoms_r ts lib T A x T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* pertype *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_pertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pertype_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_pertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_pertype_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* ipertype *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_ipertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ipertype_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_ipertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_ipertype_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* spertype *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_spertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_spertype_l ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_spertype ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_spertype_r ts lib T A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* equality *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_equality ?a ?b ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_l ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_equality ?a ?b ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_equality_r ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* requality *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_requality ?a ?b ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_requality_l ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_requality ?a ?b ?A),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_requality_r ts lib T a b A T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* tequality *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tequality ?a ?b),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tequality_l ts lib T a b T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tequality ?a ?b),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tequality_r ts lib T a b T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* base *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_base,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_l ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_base,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_base_r ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* int *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_int,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_l ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_int,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_r ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* int bar *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T ===>(lib) mkc_int),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_bar_l ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : type_monotone ?ts,
        H4 : all_in_bar ?bar (fun lib => ?T' ===>(lib) mkc_int),
        H5 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_int_bar_r ts lib T T' eq bar H1 H2 H3 H4 H5); intro h; no_duplicate h

    (* atom *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_atom,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_l ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_atom,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_atom_r ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* uatom *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T mkc_uatom,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_l ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' mkc_uatom,
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uatom_r ts lib T T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* uni *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_uni ?i),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uni_l ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_uni ?i),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_uni_r ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    (* tuni *)
    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T (mkc_tuni ?i),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tuni_l ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

    | [ H1 : type_system ?ts,
        H2 : defines_only_universes ?ts,
        H3 : computes_to_valc ?lib ?T' (mkc_tuni ?i),
        H4 : close ?ts ?lib ?T ?T' ?eq
      |- _ ] =>
      generalize (dest_close_per_tuni_r ts lib T i T' eq H1 H2 H3 H4); intro h; no_duplicate h

  end.

Ltac dclose_lr := repeat (let h := fresh "h" in dest_close_lr h).
