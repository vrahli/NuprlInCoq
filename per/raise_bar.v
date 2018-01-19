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

Lemma inf_lib_extends_lib_extends_trans {o} :
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
Hint Resolve inf_lib_extends_lib_extends_trans : slow.

Definition raise_bar {o} {lib lib'}
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
Defined.

Lemma implies_all_in_bar_raise_bar {o} :
  forall {lib lib'} (bar : @BarLib o lib) (ext : lib_extends lib' lib) F,
    all_in_bar bar F
    -> all_in_bar (raise_bar bar ext) F.
Proof.
  introv alla br e.
  simpl in *; exrepnd.
  apply (alla lib1 br1); eauto 3 with slow.
Qed.
Hint Resolve implies_all_in_bar_raise_bar : slow.
