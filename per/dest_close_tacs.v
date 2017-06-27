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
