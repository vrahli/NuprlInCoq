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

  Authors: Vincent Rahli

*)


Require Export bar.
Require Export ebar.


Lemma choice_sequence_vals_extend_preserves_inf_choice_sequence_vals_extend {o} :
  forall (entry0 entry1 : @ChoiceSeqEntry o) entry,
    choice_sequence_vals_extend entry0 entry1
    -> inf_choice_sequence_vals_extend entry entry0
    -> inf_choice_sequence_vals_extend entry entry1.
Proof.
  introv ext1 ext2 sel.
  apply ext2.
  unfold choice_sequence_vals_extend in *; exrepnd.
  rewrite ext0.
  rewrite select_app_left; auto.
  apply select_lt in sel; auto.
Qed.
Hint Resolve choice_sequence_vals_extend_preserves_inf_choice_sequence_vals_extend : slow.

Lemma choice_sequence_entry_extend_preserves_inf_choice_sequence_entry_extend {o} :
  forall (entry0 entry1 : @ChoiceSeqEntry o) entry,
    choice_sequence_entry_extend entry0 entry1
    -> inf_choice_sequence_entry_extend entry entry0
    -> inf_choice_sequence_entry_extend entry entry1.
Proof.
  introv ext1 ext2.
  unfold inf_choice_sequence_entry_extend in *; repnd.
  unfold choice_sequence_entry_extend in *; repnd.
  dands; try congruence; eauto 3 with slow.
Qed.
Hint Resolve choice_sequence_entry_extend_preserves_inf_choice_sequence_entry_extend : slow.

Lemma entry_extends_preserves_inf_entry_extends {o} :
  forall (e' e : @library_entry o) ie,
    entry_extends e' e
    -> inf_entry_extends ie e'
    -> inf_entry_extends ie e.
Proof.
  introv ext1 ext2.
  destruct ie, e', e; simpl in *; repnd; subst; dands; tcsp; ginv; eauto 3 with slow;
    try (complete (inversion ext1; subst; auto)).
Qed.
Hint Resolve entry_extends_preserves_inf_entry_extends : slow.

Lemma entry_extends_preserves_inf_matching_entries {o} :
  forall (e' e : @library_entry o) ie,
    entry_extends e' e
    -> inf_matching_entries ie e
    -> inf_matching_entries ie e'.
Proof.
  introv ext m.
  unfold inf_matching_entries in *.
  destruct ie, e, e'; simpl in *; repnd; subst; tcsp; ginv;
    try (complete (inversion ext; auto)).
Qed.
Hint Resolve entry_extends_preserves_inf_matching_entries : slow.

Lemma entry_extends_preserves_entry_in_inf_library_extends {o} :
  forall n (entry' entry : @library_entry o) infLib,
    entry_extends entry' entry
    -> entry_in_inf_library_extends entry' n infLib
    -> entry_in_inf_library_extends entry n infLib.
Proof.
  induction n; introv ext i; simpl in *; tcsp.
  repndors; tcsp; eauto 3 with slow.
  right; repnd.
  dands; eauto 3 with slow.
  introv m; destruct i0; eauto 3 with slow.
Qed.
Hint Resolve entry_extends_preserves_entry_in_inf_library_extends : slow.

Lemma choice_sequence_entry_extend_preserves_is_default_choice_seq_entry {o} :
  forall (entry' entry : @ChoiceSeqEntry o),
    choice_sequence_entry_extend entry' entry
    -> is_default_choice_seq_entry entry'
    -> is_default_choice_seq_entry entry.
Proof.
  introv h q.
  unfold is_default_choice_seq_entry, choice_sequence_entry_extend in *; repnd.
  unfold choice_sequence_vals_extend in *; exrepnd.
  destruct entry', entry; simpl in *; subst; eauto 3 with slow.
  unfold is_default_choice_sequence, same_restrictions in *.
  destruct cse_restriction, cse_restriction0; simpl in *; repnd; tcsp; introv s.

  - pose proof (q n v) as q.
    rewrite select_app_l in q; eauto 3 with slow.
    autodimp q hyp; subst; eauto.

  - pose proof (q n v) as q.
    rewrite select_app_l in q; eauto 3 with slow.
    autodimp q hyp; subst; eauto.
Qed.
Hint Resolve choice_sequence_entry_extend_preserves_is_default_choice_seq_entry : slow.

Lemma entry_extends_preserves_is_cs_default_entry {o} :
  forall (entry entry' : @library_entry o),
    entry_extends entry' entry
    -> is_cs_default_entry entry'
    -> is_cs_default_entry entry.
Proof.
  introv h q.
  unfold is_cs_default_entry, entry_extends in *.
  destruct entry, entry'; repnd; subst; tcsp; dands; ginv; eauto 3 with slow.
Qed.
Hint Resolve entry_extends_preserves_is_cs_default_entry : slow.

Lemma entry_extends_preserves_entry_in_inf_library_default {o} :
  forall (entry entry' : @library_entry o) infLib,
    entry_extends entry' entry
    -> entry_in_inf_library_default entry' infLib
    -> entry_in_inf_library_default entry infLib.
Proof.
  introv h w.
  unfold entry_in_inf_library_default in *; repnd.
  dands; eauto 3 with slow.
  introv xx; destruct (w0 n); eauto 3 with slow.
Qed.
Hint Resolve entry_extends_preserves_entry_in_inf_library_default : slow.

(*Lemma inf_lib_extends_lib_extends_trans {o} :
  forall infLib (lib' lib : @library o),
    inf_lib_extends infLib lib'
    -> lib_extends lib' lib
    -> inf_lib_extends infLib lib.
Proof.
  introv inf ext.
  destruct inf as [inf safe].
  split.

  - introv i.
    applydup ext in i.
    apply entry_in_library_extends_implies_entry_in_library in i0; exrepnd.
    applydup inf in i0; exrepnd.
    repndors; exrepnd; eauto 3 with slow;[].
    left; exists n; eauto 3 with slow.

  - introv s.
    eapply lib_extends_safe in s;[|eauto]; tcsp.
Qed.
Hint Resolve inf_lib_extends_lib_extends_trans : slow.*)

(*Definition raise_bar {o} {lib lib'}
           (bar : @BarLib o lib)
           (ext : lib_extends lib' lib) : @BarLib o lib'.
Proof.
  exists (fun (lib0 : library) =>
            exists lib1,
              bar_lib_bar bar lib1
              /\ lib_extends lib0 lib1
              /\ lib_extends lib0 lib').

  - introv e.
    destruct bar as [bar1 bars1 ext1].
    simpl in *.

    pose proof (bars1 infLib) as q; autodimp q hyp; eauto 3 with slow.
    exrepnd.

    pose proof (intersect_inf_lib_extends2 infLib lib' lib'0) as h.
    repeat (autodimp h hyp).
    exrepnd.
    exists lib0; dands; eauto 3 with slow.
    exists lib'0; dands; eauto 3 with slow.

  - introv h; exrepnd; auto.
Defined.*)

(*Lemma implies_all_in_bar_raise_bar {o} :
  forall {lib lib'} (bar : @BarLib o lib) (ext : lib_extends lib' lib) F,
    all_in_bar bar F
    -> all_in_bar (raise_bar bar ext) F.
Proof.
  introv alla br e.
  simpl in *; exrepnd.
  apply (alla lib1 br1); eauto 3 with slow.
Qed.
Hint Resolve implies_all_in_bar_raise_bar : slow.*)

(*Lemma implies_e_all_in_bar_raise_bar {o} :
  forall {lib lib'} (bar : @BarLib o lib) (ext : lib_extends lib' lib) F,
    e_all_in_bar bar F
    -> e_all_in_bar (raise_bar bar ext) F.
Proof.
  introv alla br e.
  simpl in *; exrepnd.
  apply (alla lib1 br1); eauto 3 with slow.
Qed.
Hint Resolve implies_e_all_in_bar_raise_bar : slow.*)

(*Lemma e_all_in_ex_bar_ext_pres_ext {o} :
  forall (lib lib' : @library o)
         (F : forall lib' (x : lib_extends lib' lib), Prop)
         (G : forall lib'' (x : lib_extends lib'' lib'), Prop),
    lib_extends lib' lib
    -> (forall (bar : BarLib lib)
               lib1 (br : bar_lib_bar bar lib1)
               lib2 (x : lib_extends lib2 lib1)
               (y : lib_extends lib2 lib)
               (z : lib_extends lib2 lib'),
           F lib2 y
           -> G lib2 z)
    -> e_all_in_ex_bar_ext lib F
    -> e_all_in_ex_bar_ext lib' G.
Proof.
  introv ext imp h.
  unfold e_all_in_ex_bar_ext in *; exrepnd.
  exists (raise_bar bar ext); introv br; introv.
  simpl in *; exrepnd.
  assert (lib_extends lib'1 lib1) as xt by eauto 3 with slow.
  pose proof (h0 _ br1 _ xt) as h0.
  eapply ex_finite_ext_ext_pres; eauto.
  introv xta z; introv; eauto.
  assert (lib_extends lib'2 lib) as xt' by eauto 3 with slow.
  assert (lib_extends lib'2 lib1) as xt'' by eauto 3 with slow.
  apply (imp _ _ br1 _ xt'' xt' x); auto.
Qed.*)

(*Lemma e_all_in_ex_bar_pres_ext {o} :
  forall (lib lib' : @library o)
         (F G : library -> Prop),
    lib_extends lib' lib
    -> (forall (bar : BarLib lib)
               lib' (br : bar_lib_bar bar lib')
               lib'' (x : lib_extends lib'' lib'),
           F lib''
           -> G lib'')
    -> e_all_in_ex_bar lib F
    -> e_all_in_ex_bar lib' G.
Proof.
  introv ext imp h.
  unfold e_all_in_ex_bar in *; exrepnd.
  exists (raise_bar bar ext); introv br e; introv.
  simpl in *; exrepnd.
  assert (lib_extends lib'1 lib1) as xt by eauto 3 with slow;[].
  pose proof (h0 _ br1 _ xt) as h0.
  eapply ex_finite_ext_pres;[|eauto].
  introv xta z; introv; eauto.
  eapply imp; eauto; eauto 3 with slow.
Qed.*)

(*Lemma e_all_in_bar_ext_raise_bar_pres {o} :
  forall (lib lib' : @library o)
         (bar : BarLib lib)
         (xt1 xt2 : lib_extends lib' lib)
         (F G : forall lib'' (x : lib_extends lib'' lib'), Prop),
    (forall lib1 (br : bar_lib_bar bar lib1)
               lib2 (x : lib_extends lib2 lib1)
               (z : lib_extends lib2 lib'),
           F lib2 z
           -> G lib2 z)
    -> e_all_in_bar_ext (raise_bar bar xt2) F
    -> e_all_in_bar_ext (raise_bar bar xt1) G.
Proof.
  introv imp h.
  introv br; introv; simpl in *; exrepnd.
  assert (lib_extends lib'1 lib1) as xt by eauto 3 with slow.
  pose proof (h lib'0) as h; autodimp h hyp.
  { exists lib1; dands; auto; eauto 3 with slow. }
  pose proof (h lib'1 e) as h.
  eapply ex_finite_ext_ext_pres; eauto.
  introv xta z; introv; eauto.
  assert (lib_extends lib'2 lib) as xt' by eauto 3 with slow.
  assert (lib_extends lib'2 lib1) as xt'' by eauto 3 with slow.
  apply (imp _ br1 _ xt'' x); eauto.
Qed.*)

(*Lemma e_all_in_bar_ext_pres {o} :
  forall (lib : @library o)
         (bar : BarLib lib)
         (F G : forall lib'' (x : lib_extends lib'' lib), Prop),
    (forall lib1 (br : bar_lib_bar bar lib1)
               lib2 (x : lib_extends lib2 lib1)
               (z : lib_extends lib2 lib),
           F lib2 z
           -> G lib2 z)
    -> e_all_in_bar_ext bar F
    -> e_all_in_bar_ext bar G.
Proof.
  introv imp h.
  introv br; introv; simpl in *; exrepnd.
  pose proof (h _ br _ e) as h.
  eapply ex_finite_ext_ext_pres; eauto.
  introv xta z; introv; eauto.
  eapply imp; eauto; eauto 3 with slow.
Qed.*)

(*Lemma e_all_in_bar_ext_raise_bar_pres2 {o} :
  forall (lib lib' : @library o)
         (bar : BarLib lib)
         (xt : lib_extends lib' lib)
         (F : forall lib'' (x : lib_extends lib'' lib), Prop)
         (G : forall lib'' (x : lib_extends lib'' lib'), Prop),
    (forall lib1 (br : bar_lib_bar bar lib1)
               lib2 (x : lib_extends lib2 lib1)
               (y : lib_extends lib2 lib)
               (z : lib_extends lib2 lib'),
           F lib2 y
           -> G lib2 z)
    -> e_all_in_bar_ext bar F
    -> e_all_in_bar_ext (raise_bar bar xt) G.
Proof.
  introv imp h.
  introv br; introv; simpl in *; exrepnd.
  assert (lib_extends lib'1 lib1) as xt' by eauto 3 with slow.
  pose proof (h _ br1 _ xt') as h.
  eapply ex_finite_ext_ext_pres; eauto.
  introv xta z; introv; eauto.
  assert (lib_extends lib'2 lib) as xa by eauto 3 with slow.
  assert (lib_extends lib'2 lib1) as xb by eauto 3 with slow.
  apply (imp _ br1 _ xb xa x); auto.
Qed.*)

(*Lemma e_all_in_bar_ext_raise_bar_pres3 {o} :
  forall (lib lib' lib'' : @library o)
         (bar : BarLib lib)
         (xt1 : lib_extends lib' lib)
         (xt2 : lib_extends lib'' lib)
         (F : forall lib0 (x : lib_extends lib0 lib'), Prop)
         (G : forall lib0 (x : lib_extends lib0 lib''), Prop),
    lib_extends lib'' lib'
    -> (forall lib1 (br : bar_lib_bar bar lib1)
               lib2 (x : lib_extends lib2 lib1)
               (y : lib_extends lib2 lib')
               (z : lib_extends lib2 lib''),
           F lib2 y
           -> G lib2 z)
    -> e_all_in_bar_ext (raise_bar bar xt1) F
    -> e_all_in_bar_ext (raise_bar bar xt2) G.
Proof.
  introv xt3 imp h.
  introv br; introv; simpl in *; exrepnd.
  assert (lib_extends lib'1 lib1) as xt by eauto 3 with slow.
  pose proof (h lib'0) as h; autodimp h hyp.
  { exists lib1; dands; auto; eauto 3 with slow. }
  pose proof (h lib'1 e) as h.
  eapply ex_finite_ext_ext_pres; eauto.
  introv xta z; introv; eauto.
  assert (lib_extends lib'2 lib') as xt' by eauto 3 with slow.
  assert (lib_extends lib'2 lib1) as xt'' by eauto 3 with slow.
  apply (imp _ br1 _ xt'' xt' x); auto.
Qed.*)


(* xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx *)
(*
  We now show here how to get rid of full bars using these e_xxx
  abstractions on top of bars.  We obtain open bars, which no longer
  mention bars but simply world extensions.
 *)

Definition in_open_bar {o} (lib : @library o) F :=
  forall lib',
    lib_extends lib' lib
    -> exists (lib'' : library) (xt : lib_extends lib'' lib'),
      in_ext lib'' F.

(*Lemma e_all_in_ex_bar_as {o} :
  forall (lib : @library o) F,
    e_all_in_ex_bar lib F
    <-> in_open_bar lib F.
Proof.
  introv; split; intro h.

  { introv ext.
    unfold e_all_in_ex_bar in h; exrepnd.

    pose proof (bar_non_empty (raise_bar bar ext)) as q.
    simpl in *; exrepnd.
    pose proof (h0 _ q0 lib'0) as h0; autodimp h0 hyp.
    unfold ex_finite_ext in h0; exrepnd.
    exists lib'1; auto; dands; auto; eauto 3 with slow. }

  { exists (trivial_bar lib).
    introv br ext; simpl in *.
    pose proof (h _ (lib_extends_trans ext br)) as h; exrepnd.
    exists lib'' xt; auto. }
Qed.*)

(*Lemma e_all_in_bar_as {o} :
  forall {lib} (bar : @BarLib o lib) F,
    e_all_in_bar bar F
    <-> in_open_bar lib F.
Proof.
  introv; split; intro h.

  { introv ext.

    pose proof (bar_non_empty (raise_bar bar ext)) as q.
    simpl in *; exrepnd.
    pose proof (h _ q0 lib'0) as h; autodimp h hyp.
    unfold ex_finite_ext in h; exrepnd.
    exists lib'1; auto; dands; auto; eauto 3 with slow. }

  { introv br ext; simpl in *.
    assert (lib_extends lib' lib) as xt by eauto 3 with slow.
    pose proof (h _ (lib_extends_trans ext xt)) as h; exrepnd.
    exists lib'' xt0; auto. }
Qed.*)

Definition in_open_bar_ext {o}
           (lib : @library o)
           (F : forall (lib' : @library o), lib_extends lib' lib -> Prop) :=
  forall lib' (x : lib_extends lib' lib),
  exists (lib'' : library) (y : lib_extends lib'' lib'),
    in_ext_ext lib'' (fun lib0 x0 => forall (z : lib_extends lib0 lib), F lib0 z).

(*Lemma e_all_in_ex_bar_ext_as {o} :
  forall (lib : @library o) F,
    e_all_in_ex_bar_ext lib F
    <-> in_open_bar_ext lib F.
Proof.
  introv; split; intro h.

  { introv ext.
    unfold e_all_in_ex_bar_ext in h; exrepnd.

    pose proof (bar_non_empty (raise_bar bar ext)) as q.
    simpl in *; exrepnd.
    pose proof (h0 _ q0 lib'0 q2) as h0.
    unfold ex_finite_ext_ext in h0; exrepnd.
    assert (lib_extends lib'' lib') as xta by eauto 3 with slow.
    assert (lib_extends lib'' lib) as xtb by eauto 3 with slow.
    exists lib'' xta; auto; dands; auto; eauto 3 with slow. }

  { exists (trivial_bar lib).
    introv br; repeat introv; simpl in *.
    pose proof (h _ (lib_extends_trans e br)) as h; exrepnd.
    exists lib'' y; eauto. }
Qed.*)

(*Lemma e_all_in_bar_ext_as {o} :
  forall {lib} (bar : @BarLib o lib) F,
    e_all_in_bar_ext bar F
    <-> in_open_bar_ext lib F.
Proof.
  introv; split; intro h.

  { introv ext.
    pose proof (bar_non_empty (raise_bar bar ext)) as q.
    simpl in *; exrepnd.
    pose proof (h _ q0 lib'0 q2) as h.
    unfold ex_finite_ext_ext in h; exrepnd.
    assert (lib_extends lib'' lib') as xta by eauto 3 with slow.
    assert (lib_extends lib'' lib) as xtb by eauto 3 with slow.
    exists lib'' xta; auto; dands; auto; eauto 3 with slow. }

  { unfold in_open_bar_ext in h.
    introv br; repeat introv; simpl in *.
    assert (lib_extends lib' lib) as xt by eauto 3 with slow.
    pose proof (h _ (lib_extends_trans e xt)) as h; exrepnd.
    exists lib'' y.
    introv; auto. }
Qed.*)

Lemma lib_extends_preserves_in_open_bar {o} :
  forall (lib1 lib2 : @library o) F,
    lib_extends lib2 lib1
    -> in_open_bar lib1 F
    -> in_open_bar lib2 F.
Proof.
  introv ext h xt.
  apply h; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_in_open_bar : slow.

Lemma in_open_bar_ext_and {o} :
  forall (lib : @library o) F G,
    in_open_bar_ext lib (fun lib x => F lib x /\ G lib x)
    -> (in_open_bar_ext lib F /\ in_open_bar_ext lib G).
Proof.
  introv h; dands; introv ext; pose proof (h _ ext) as h; exrepnd;
    exists lib'' y; introv; apply h1.
Qed.

Lemma in_open_bar_ext_prod {o} :
  forall (lib : @library o) (F G : forall lib' (x : lib_extends lib' lib), Prop),
    in_open_bar_ext lib (fun lib x => F lib x # G lib x)
    -> (in_open_bar_ext lib F # in_open_bar_ext lib G).
Proof.
  introv h; dands; introv ext; pose proof (h _ ext) as h; exrepnd;
    exists lib'' y; introv; apply h1.
Qed.

Lemma in_open_bar_pres {o} :
  forall (lib : @library o) (F G : library -> Prop),
    in_ext lib (fun lib' => F lib' -> G lib')
    -> in_open_bar lib F
    -> in_open_bar lib G.
Proof.
  introv imp h ext.
  pose proof (h _ ext) as h; exrepnd.
  exists lib'' xt.
  introv y; apply imp; eauto 3 with slow.
Qed.
Hint Resolve in_open_bar_pres : slow.

Lemma in_open_bar_ext_pres {o} :
  forall (lib : @library o) (F G : forall lib' (x : lib_extends lib' lib), Prop),
    in_ext_ext lib (fun lib' x => F lib' x -> G lib' x)
    -> in_open_bar_ext lib F
    -> in_open_bar_ext lib G.
Proof.
  introv imp h ext.
  pose proof (h _ ext) as h; exrepnd.
  exists lib'' y.
  introv z; introv; apply imp; eauto 3 with slow.
Qed.
Hint Resolve in_open_bar_ext_pres : slow.

(* Similar to intersect_bars but on open bars *)
Lemma in_open_bar_ext_pres2 {o} :
  forall (lib : @library o) (F G H : forall lib' (x : lib_extends lib' lib), Prop),
    in_ext_ext lib (fun lib' x => F lib' x -> G lib' x -> H lib' x)
    -> in_open_bar_ext lib F
    -> in_open_bar_ext lib G
    -> in_open_bar_ext lib H.
Proof.
  introv imp h q ext.
  pose proof (h _ ext) as h; exrepnd.
  pose proof (q _ (lib_extends_trans y ext)) as q; exrepnd.
  exists lib''0 (lib_extends_trans y0 y).
  introv z; introv; apply imp; eauto 3 with slow.
Qed.
Hint Resolve in_open_bar_ext_pres2 : slow.

Lemma lib_extends_preserves_in_open_bar_ext {o} :
  forall (lib2 lib1 : @library o)
         (F : forall lib' (x : lib_extends lib' lib1), Prop)
         (ext : lib_extends lib2 lib1),
    in_open_bar_ext lib1 F
    -> in_open_bar_ext lib2 (fun lib' x => F lib' (lib_extends_trans x ext)).
Proof.
  introv h xt.
  pose proof (h _ (lib_extends_trans xt ext)) as h; exrepnd.
  exists lib'' y.
  introv z; introv; apply h1; eauto 3 with slow.
Qed.

Lemma in_open_bar_ext_comb {o} :
  forall (lib : @library o) (F G : forall lib' (x : lib_extends lib' lib), Prop),
    in_open_bar_ext lib (fun lib' x => F lib' x -> G lib' x)
    -> in_open_bar_ext lib F
    -> in_open_bar_ext lib G.
Proof.
  introv h q ext.
  pose proof (h _ ext) as h; exrepnd.
  pose proof (q _ (lib_extends_trans y ext)) as q; exrepnd.
  exists lib''0 (lib_extends_trans y0 y).
  introv z; introv; apply h1; eauto 3 with slow.
Qed.
Hint Resolve in_open_bar_ext_comb : slow.

Lemma in_open_bar_ext_comb2 {o} :
  forall (lib : @library o) (F : library -> Prop) (G : forall lib' (x : lib_extends lib' lib), Prop),
    in_open_bar_ext lib (fun lib' x => F lib' -> G lib' x)
    -> in_open_bar lib F
    -> in_open_bar_ext lib G.
Proof.
  introv h q ext.
  pose proof (h _ ext) as h; exrepnd.
  pose proof (q _ (lib_extends_trans y ext)) as q; exrepnd.
  exists lib''0 (lib_extends_trans xt y).
  introv z; introv; apply h1; eauto 3 with slow.
Qed.
Hint Resolve in_open_bar_ext_comb2 : slow.

Lemma in_ext_ext_implies_in_open_bar_ext {o} :
  forall (lib : @library o) (F : forall lib' (x : lib_extends lib' lib), Prop),
    in_ext_ext lib F
    -> in_open_bar_ext lib F.
Proof.
  introv h ext.
  exists lib' (lib_extends_refl lib').
  introv xt; introv; eauto.
Qed.
Hint Resolve in_ext_ext_implies_in_open_bar_ext : slow.

Lemma in_ext_implies_in_open_bar {o} :
  forall (lib : @library o) (F : library -> Prop),
    in_ext lib F
    -> in_open_bar lib F.
Proof.
  introv h ext.
  exists lib' (lib_extends_refl lib').
  introv xt; introv; eauto 3 with slow.
Qed.
Hint Resolve in_ext_implies_in_open_bar : slow.

Lemma in_open_bar_comb2 {o} :
  forall (lib : @library o) (F : forall lib' (x : lib_extends lib' lib), Prop) (G : library -> Prop),
    in_open_bar_ext lib (fun lib' x => F lib' x -> G lib')
    -> in_open_bar_ext lib F
    -> in_open_bar lib G.
Proof.
  introv h q ext.
  pose proof (h _ ext) as h; exrepnd.
  pose proof (q _ (lib_extends_trans y ext)) as q; exrepnd.
  exists lib''0 (lib_extends_trans y0 y).
  introv z; introv.
  assert (lib_extends lib'0 lib) as xt by eauto 4 with slow.
  apply (h1 _ (lib_extends_trans z y0) xt); auto.
Qed.
Hint Resolve in_open_bar_comb2 : slow.

Lemma in_open_bar_ext_in_open_bar {o} :
  forall (lib : @library o) (F : library -> Prop),
    in_open_bar_ext lib (fun lib' x => in_open_bar lib' F)
    <-> in_open_bar lib F.
Proof.
  introv; split; intro h.

  { introv ext.
    pose proof (h _ ext) as h; exrepnd; simpl in *.
    apply in_ext_ext_implies in h1.
    autodimp h1 hyp; eauto 3 with slow.
    pose proof (h1 _ (lib_extends_refl _)) as h1; exrepnd.
    exists lib''0 (lib_extends_trans xt y); auto. }

  { apply in_ext_ext_implies_in_open_bar_ext.
    introv ext; eauto 3 with slow. }
Qed.
Hint Rewrite @in_open_bar_ext_in_open_bar : slow.

Lemma in_open_bar_ext_dup {o} :
  forall (lib : @library o) (F : forall lib' (x : lib_extends lib' lib), Prop),
    in_open_bar_ext
      lib
      (fun lib1 x1 =>
         in_open_bar_ext
           lib1
           (fun lib2 x2 =>
              forall (z : lib_extends lib2 lib),
                F lib2 z))
    -> in_open_bar_ext lib F.
Proof.
  introv h.
  introv ext.
  pose proof (h _ ext) as h; exrepnd; simpl in *.
  apply in_ext_ext_implies in h1.
  pose proof (h1 (lib_extends_trans y ext)) as h1.
  pose proof (h1 _ (lib_extends_refl _)) as h1; exrepnd.
  exists lib''0 (lib_extends_trans y0 y); auto.
  introv xt; introv.
  pose proof (h1 _ xt (lib_extends_trans xt y0) z) as h1; simpl in *; auto.
Qed.

Lemma in_open_bar_ext_twice {o} :
  forall (lib : @library o) (F : forall lib' (x : lib_extends lib' lib), Prop),
    in_open_bar_ext lib F
    -> in_open_bar_ext
         lib
         (fun lib1 x1 =>
            in_open_bar_ext
              lib1
              (fun lib2 x2 => F lib2 (lib_extends_trans x2 x1))).
Proof.
  introv h.
  apply in_ext_ext_implies_in_open_bar_ext.
  introv ext.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ e) in h.
  apply h; eauto 3 with slow.
Qed.

Lemma in_open_bar_comb {o} :
  forall (lib : @library o) (F G : library -> Prop),
    in_open_bar lib (fun lib' => F lib' -> G lib')
    -> in_open_bar lib F
    -> in_open_bar lib G.
Proof.
  introv h q ext.
  pose proof (h _ ext) as h; exrepnd.
  pose proof (q _ (lib_extends_trans xt ext)) as q; exrepnd.
  exists lib''0 (lib_extends_trans xt0 xt).
  introv z; introv.
  apply h1; eauto 3 with slow.
Qed.

(* xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx *)
