(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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
Require Export nuprl_mon.
(*Require Export local.*)


(*Ltac close_diff_bar :=
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
  end.*)

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

(*Ltac close_diff_bar_bar :=
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
  end.*)


(*Ltac close_diff_bar_ceq_bar :=
  allunfold_per;
  match goal with
  | [ H1 : all_in_bar ?bar1 (fun lib => ?T ===>(lib) _),
      H2 : computes_to_valc_ceq_bar ?bar2 ?T _ |- _ ] =>
    let h    := fresh "h" in
    let a1   := fresh "a1" in
    let b1   := fresh "b1" in
    let a2   := fresh "a2" in
    let b2   := fresh "b2" in
    let lib1 := fresh "lib1" in
    let lib2 := fresh "lib2" in
    let lib' := fresh "lib'" in
    let xxx  := fresh "xxx" in
    let t'   := fresh "t'" in
    let b3   := fresh "b3'" in
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
    destruct b2 as [t' [b2 b3] ];
    spcast;
    apply_cequivc_val;
    try (spcast; computes_to_valc_diff)
  end.*)

(*Ltac close_diff_ceq_bar_ceq_bar0 :=
  match goal with
  | [ H1 : computes_to_valc_ceq_bar ?bar1 ?T _,
      H2 : computes_to_valc_ceq_bar ?bar2 ?T _ |- _ ] =>
    let h    := fresh "h" in
    let a1   := fresh "a1" in
    let b1   := fresh "b1" in
    let a2   := fresh "a2" in
    let b2   := fresh "b2" in
    let lib1 := fresh "lib1" in
    let lib2 := fresh "lib2" in
    let lib' := fresh "lib'" in
    let xxx  := fresh "xxx" in
    let ta   := fresh "ta" in
    let tb   := fresh "tb" in
    let a3   := fresh "a3'" in
    let b3   := fresh "b3'" in
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
    destruct a2 as [ta [a2 a3] ];
    destruct b2 as [tb [b2 b3] ];
    spcast;
    repeat apply_cequivc_val;
    try (spcast; computes_to_valc_diff)
  end.*)

(*Ltac close_diff_ceq_bar_ceq_bar :=
  allunfold_per;
  close_diff_ceq_bar_ceq_bar0.*)

(*Ltac close_diff_ext_bar :=
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
  end.*)

(*Ltac close_diff_ext_ceq_bar :=
  allunfold_per;
  match goal with
  | [ H1 : in_ext ?lib (fun lib => ?T ===>(lib) _),
      H2 : computes_to_valc_ceq_bar ?bar ?T _ |- _ ] =>
    let h    := fresh "h" in
    let a1   := fresh "a1" in
    let b1   := fresh "b1" in
    let b2   := fresh "b2" in
    let lib' := fresh "lib'" in
    let xxx  := fresh "xxx" in
    let t'   := fresh "t'" in
    let b3   := fresh "b3" in
    pose proof (bar_non_empty bar) as h;
    destruct h as [lib' h];
    pose proof (H1 lib') as a1; autodimp a1 xxx; eauto 2 with slow; simpl in a1;
    pose proof (H2 lib') as b1; autodimp b1 xxx;
    pose proof (b1 lib') as b2; autodimp b2 xxx; eauto 2 with slow; simpl in b2;
    spcast;
    destruct b2 as [t' [b2 b3] ];
    spcast;
    apply_cequivc_val;
    try computes_to_valc_diff
  end.*)

(*Ltac close_diff_init_bar_left :=
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
  end.*)

(*Ltac close_diff_init_bar_right :=
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
  end.*)

Ltac close_diff_init_ext :=
  match goal with
  | [ H : in_ext ?lib (fun lib => ?T ===>(lib) _) |- _ ] =>
    let h   := fresh "h"   in
    let xxx := fresh "xxx" in
    pose proof (H lib) as h; autodimp h xxx; eauto 2 with slow; simpl in h; spcast;
    apply_defines_only_universes; spcast;
    computes_to_valc_diff
  end.

(*Ltac close_diff_ceq_bar :=
  allunfold_per; spcast;
  match goal with
  | [ comp1 : computes_to_valc ?lib ?T _,
      bar   : BarLib ?lib,
      comp2 : computes_to_valc_ceq_bar ?bar ?T _
    |- _ ] =>

    let h1   := fresh "h1" in
    let h2   := fresh "h2" in
    let h2'  := fresh "h2'" in
    let h3   := fresh "h3" in
    let xxx  := fresh "xxx" in
    let lib' := fresh "lib'" in
    let t'   := fresh "t'" in
    pose proof (bar_non_empty bar) as h1;
    destruct h1 as [lib' h1];
    pose proof (comp2 lib' h1 lib' (lib_extends_refl lib')) as h2; simpl in h2; spcast;
    destruct h2 as [t' [ h2 h2' ] ]; spcast;
    apply_cequivc_val;
    pose proof (computes_to_valc_preserves_lib_extends lib lib') as h3;
    autodimp h3 xxx; eauto 2 with slow;[];
    apply h3 in comp1; exrepnd; clear h3;
    try alphaeqc_decompose;
    try computes_to_valc_diff
  end.*)

Ltac close_diff_ceq :=
  allunfold_per;
  try (apply_defines_only_universes);
  uncast;
  first [ (*close_diff_bar*)
        (*| close_diff_ceq_bar*)
        ].

Ltac close_diff_all :=
  first [ complete auto
        | complete close_diff
        | complete close_diff_diff
        | complete close_diff_ceq
        (*| complete close_diff_bar*)
        (*| complete close_diff_ceq_bar*)
        | complete close_diff_ext
        (*| complete close_diff_bar_bar*)
        (*| complete close_diff_bar_ceq_bar*)
        (*| complete close_diff_ceq_bar_ceq_bar0*)
        (*| complete close_diff_ceq_bar_ceq_bar*)
        (*| complete close_diff_ext_bar*)
        (*| complete close_diff_ext_ceq_bar*)
        (*| complete close_diff_init_bar_left*)
        (*| complete close_diff_init_bar_right*)
        | complete close_diff_init_ext
        ].

Lemma cequivc_ext_mkc_approx_right {o} :
  forall lib (a b c d : @CTerm o),
    ccequivc_ext lib (mkc_approx a b) (mkc_approx c d)
    -> ccequivc_ext lib a c # ccequivc_ext lib b d.
Proof.
  introv ceq; dands; introv ext; pose proof (ceq lib' ext) as q; simpl in q;
    clear ceq; spcast; apply cequivc_decomp_approx in q; sp.
Qed.

Lemma approx_decomp_cequiv {p} :
  forall lib a b c d,
    approx lib (mk_cequiv a b) (@mk_cequiv p c d)
    <=> approx lib a c # approx lib b d.
Proof.
  split; unfold mk_approx; introv Hyp.
  - applydup @approx_relates_only_progs in Hyp. repnd.
    apply  approx_canonical_form2 in Hyp.
    unfold lblift in Hyp. repnd. allsimpl.
    alpharelbtd. GC.
    eapply blift_approx_open_nobnd in Hyp1bt; eauto 3 with slow.
    eapply blift_approx_open_nobnd in Hyp0bt; eauto 3 with slow.
  - repnd. applydup @approx_relates_only_progs in Hyp. repnd.
    applydup @approx_relates_only_progs in Hyp0. repnd.
    apply approx_canonical_form3.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      dorn Hin;[| dorn Hin]; sp;[|];
      subst; apply implies_isprogram_bt0; eauto with slow.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      dorn Hin;[| dorn Hin]; sp;[|];
      subst; apply implies_isprogram_bt0; eauto with slow.
    + unfold lblift. allsimpl. split; auto.
      introv Hin. unfold selectbt.
      repeat(destruct n; try (omega;fail); allsimpl);
      apply blift_approx_open_nobnd2; sp.
Qed.

Lemma cequiv_decomp_cequiv {p} :
  forall lib a b c d,
    cequiv lib (mk_cequiv a b) (@mk_cequiv p c d)
    <=> cequiv lib a c # cequiv lib b d.
Proof.
  intros.
  unfold cequiv.
  generalize (approx_decomp_cequiv lib a b c d); intro.
  trewrite X; clear X.
  generalize (approx_decomp_cequiv lib c d a b); intro.
  trewrite X; clear X.
  split; sp.
Qed.

Lemma cequivc_decomp_cequiv {p} :
  forall lib a b c d,
    cequivc lib (mkc_cequiv a b) (@mkc_cequiv p c d)
    <=> cequivc lib a c # cequivc lib b d.
Proof.
  destruct a, b, c, d.
  unfold cequivc, mkc_cequiv; simpl.
  apply cequiv_decomp_cequiv.
Qed.

Lemma cequivc_ext_mkc_cequiv_right {o} :
  forall lib (a b c d : @CTerm o),
    ccequivc_ext lib (mkc_cequiv a b) (mkc_cequiv c d)
    -> ccequivc_ext lib a c # ccequivc_ext lib b d.
Proof.
  introv ceq; dands; introv ext; pose proof (ceq lib' ext) as q; simpl in q;
    clear ceq; spcast; apply cequivc_decomp_cequiv in q; sp.
Qed.

Ltac ccequivc_ext_same_left :=
  match goal with
  | [ H1 : ccequivc_ext ?lib ?t (mkc_approx ?a ?b),
           H2 : ccequivc_ext ?lib ?t (mkc_approx ?c ?d) |- _  ] =>
    apply ccequivc_ext_sym in H1;
    eapply ccequivc_ext_trans in H2;[|exact H1];
    clear H1;
    try (apply cequivc_ext_mkc_approx_right in H2; repnd)

  | [ H1 : ccequivc_ext ?lib ?t (mkc_cequiv ?a ?b),
           H2 : ccequivc_ext ?lib ?t (mkc_cequiv ?c ?d) |- _  ] =>
    apply ccequivc_ext_sym in H1;
    eapply ccequivc_ext_trans in H2;[|exact H1];
    clear H1;
    try (apply cequivc_ext_mkc_cequiv_right in H2; repnd)
  end.

(*Ltac computes_to_eqbars_step :=
  match goal with
(*  | [ B  : BarLib ?lib,
      H1 : all_in_bar ?bar (fun lib => ?T ===>(lib) ?T1),
      H2 : all_in_bar ?bar (fun lib => ?T ===>(lib) ?T2) |- _ ] =>
    let h    := fresh "h"    in
    let q    := fresh "q"    in
    let w    := fresh "w"    in
    let u    := fresh "u"    in
    let v    := fresh "v"    in
    let lib' := fresh "lib'" in
    let xxx  := fresh "xxx"  in
    pose proof (bar_non_empty bar) as h;
    destruct h as [lib' h]; simpl in h;
    pose proof (H1 lib') as q;
    pose proof (H2 lib') as w;
    autodimp q xxx;
    autodimp w xxx;
    pose proof (q lib') as u;
    pose proof (w lib') as v;
    autodimp u xxx;
    autodimp v xxx;
    eauto 2 with slow;
    simpl in u, v;
    spcast;
    clear q w;
    computes_to_eqval;
    try (hide_hyp H1)*)

(*  | [ H1 : all_in_bar ?bar1 (fun lib => ?T ===>(lib) ?T1),
      H2 : all_in_bar ?bar2 (fun lib => ?T ===>(lib) ?T2) |- _ ] =>
    let h    := fresh "h"    in
    let q    := fresh "q"    in
    let w    := fresh "w"    in
    let u    := fresh "u"    in
    let v    := fresh "v"    in
    let lib  := fresh "lib"  in
    let lib1 := fresh "lib1" in
    let lib2 := fresh "lib2" in
    let xxx  := fresh "xxx"  in
    pose proof (bar_non_empty (intersect_bars bar1 bar2)) as h;
    destruct h as [lib h]; simpl in h;
    destruct h as [lib1 h];
    destruct h as [lib2 h];
    repnd;
    pose proof (H1 lib1) as q;
    pose proof (H2 lib2) as w;
    autodimp q xxx;
    autodimp w xxx;
    pose proof (q lib) as u;
    pose proof (w lib) as v;
    autodimp u xxx;
    autodimp v xxx;
    simpl in u, v;
    spcast;
    clear q w;
    computes_to_eqval;
    try (hide_hyp H1)*)

(*  | [ H1 : computes_to_valc_ceq_bar ?bar1 ?T _,
      H2 : computes_to_valc_ceq_bar ?bar2 ?T _ |- _ ] =>
    let h    := fresh "h"    in
    let q    := fresh "q"    in
    let w    := fresh "w"    in
    let u    := fresh "u"    in
    let v    := fresh "v"    in
    let lib  := fresh "lib"  in
    let lib1 := fresh "lib1" in
    let lib2 := fresh "lib2" in
    let xxx  := fresh "xxx"  in
    let t1   := fresh "t1"   in
    let t2   := fresh "t2"   in
    let u'   := fresh "u'"   in
    let v'   := fresh "v'"   in
    pose proof (bar_non_empty (intersect_bars bar1 bar2)) as h;
    destruct h as [lib h]; simpl in h;
    destruct h as [lib1 h];
    destruct h as [lib2 h];
    repnd;
    pose proof (H1 lib1) as q;
    pose proof (H2 lib2) as w;
    autodimp q xxx;
    autodimp w xxx;
    pose proof (q lib) as u;
    pose proof (w lib) as v;
    autodimp u xxx;
    autodimp v xxx;
    simpl in u, v;
    destruct u as [t1 [u' u] ];
    destruct v as [t2 [v' v] ];
    spcast;
    clear q w;
    computes_to_eqval;
    ccequivc_ext_same_left;
    (*repeat apply_cequivc_val;
    computes_to_eqval;*)
    try (hide_hyp H1)*)
  end.
*)

(*Ltac computes_to_eqbars :=
  repeat computes_to_eqbars_step;
  repeat match goal with
         | [ H : Something |- _ ] => show_hyp H
         end.*)

Hint Resolve iscvalue_mkc_approx : slow.
Hint Resolve iscvalue_mkc_cequiv : slow.

Lemma computes_to_valc_implies_iscvalue {o} :
  forall lib (t1 t2 : @CTerm o),
    computes_to_valc lib t1 t2 -> iscvalue t2.
Proof.
  introv comp.
  rw @computes_to_valc_iff_reduces_toc in comp; tcsp.
Qed.
Hint Resolve computes_to_valc_implies_iscvalue : slow.
