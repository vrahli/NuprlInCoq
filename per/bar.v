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


Require Export per.



Lemma fresh_choice_sequence_name : FreshFun choice_sequence_name.
Proof.
  unfold FreshFun.
  introv.

  exists (String.append "x" (append_string_list l)).
  remember ("x") as extra.
  assert (0 < String.length extra)%nat as len by (subst; simpl; auto).
  clear Heqextra.
  revert dependent extra.
  induction l; introv s; allsimpl; tcsp.
  rw string_append_assoc.
  introv k; repndors;[|apply IHl in k;auto;rw string_length_append; omega].

  assert (String.length a
          = String.length
              (String.append
                 (String.append extra a)
                 (append_string_list l))) as e.
  { rewrite k at 1; auto. }
  allrw string_length_append.
  omega.
Defined.

Fixpoint library2choice_sequence_names {o} (lib : @library o) : list choice_sequence_name :=
  match lib with
  | [] => []
  | lib_cs name _ :: entries => name :: library2choice_sequence_names entries
  | _ :: entries => library2choice_sequence_names entries
  end.

Lemma not_in_library2choice_sequence_names_iff_find_cs_none {o} :
  forall (lib : @library o) (name : choice_sequence_name),
    !LIn name (library2choice_sequence_names lib)
    <-> find_cs lib name = None.
Proof.
  induction lib; simpl; introv; split; intro h; tcsp; destruct a; simpl in *; tcsp.

  - allrw not_over_or; repnd.
    boolvar; subst; tcsp.
    apply IHlib; auto.

  - apply IHlib; auto.

  - boolvar; tcsp.
    allrw not_over_or; dands; tcsp.
    apply IHlib; auto.

  - apply IHlib; auto.
Qed.

Definition choice_seq_vals2inf {o} (vals : @ChoiceSeqVals o) f : InfChoiceSeqVals :=
  fun n =>
    match select n vals with
    | Some v => v
    | None => (f n)
    end.

Definition restriction2default {o}
           (r : @ChoiceSeqRestriction o) : nat -> ChoiceSeqVal :=
  match r with
  | csc_no => fun n => mkc_zero
  | csc_type d _ => fun n => d
  | csc_coq_law f => fun n => f n
  end.

Definition choice_seq_entry2inf {o} (e : @ChoiceSeqEntry o) : InfChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    MkInfChoiceSeqEntry
      _
      (choice_seq_vals2inf vals (restriction2default restr))
      restr
  end.

Definition library_entry2inf {o} (e : @library_entry o) : inf_library_entry :=
  match e with
  | lib_cs name entry => inf_lib_cs name (choice_seq_entry2inf entry)
  | lib_abs abs vars rhs correct => inf_lib_abs abs vars rhs correct
  end.

Definition library2inf {o} (lib : @library o) (d : inf_library_entry) : inf_library :=
  fun n =>
    match select n lib with
    | Some entry => library_entry2inf entry
    | None => d
    end.

Lemma fresh_choice_seq_name_in_library {o} :
  forall (lib : @library o),
  exists (name : choice_sequence_name),
    find_cs lib name = None.
Proof.
  introv.
  pose proof (fresh_choice_sequence_name (library2choice_sequence_names lib)) as q.
  exrepnd.
  exists x.
  apply not_in_library2choice_sequence_names_iff_find_cs_none; auto.
Qed.

Definition simple_inf_choice_seq {o} (name : choice_sequence_name) : @inf_library_entry o :=
  inf_lib_cs name (MkInfChoiceSeqEntry _ (fun _ => mkc_zero) csc_no).

Lemma inf_choice_sequence_entry_extend_choice_seq_entry2inf {o} :
  forall (entry : @ChoiceSeqEntry o),
    inf_choice_sequence_entry_extend (choice_seq_entry2inf entry) entry.
Proof.
  introv; destruct entry; simpl.
  unfold inf_choice_sequence_entry_extend; simpl.
  dands; auto.
  introv i.
  unfold choice_seq_vals2inf.
  allrw; auto.
Qed.
Hint Resolve inf_choice_sequence_entry_extend_choice_seq_entry2inf : slow.

Lemma inf_matching_entries_library_entry2inf_implies {o} :
  forall (entry1 entry2 : @library_entry o),
    inf_matching_entries (library_entry2inf entry1) entry2
    -> matching_entries entry1 entry2.
Proof.
  introv h.
  destruct entry1; simpl in *; unfold inf_matching_entries in h; simpl in *;
    destruct entry2; simpl in *; tcsp.
Qed.
Hint Resolve inf_matching_entries_library_entry2inf_implies : slow.

Lemma implies_safe_inf_choice_sequence_entry2inf {o} :
  forall M (entry : @ChoiceSeqEntry o),
    safe_choice_sequence_entry M entry
    -> safe_inf_choice_sequence_entry M (choice_seq_entry2inf entry).
Proof.
  introv h; destruct entry as [vals restr]; simpl in *.
  introv.
  destruct restr; simpl in *; auto; GC.

  - exrepnd.
    dands; auto.
    introv.
    unfold choice_seq_vals2inf.
    remember (select n vals) as s; symmetry in Heqs.
    destruct s; auto.
    apply h.
    apply select_in in Heqs; apply LIn_implies_In in Heqs; auto.

  - introv.
    unfold choice_seq_vals2inf.
    remember (select n vals) as s; symmetry in Heqs.
    destruct s; auto.
    rewrite (h n) in Heqs;[inversion Heqs; auto|].
    eapply select_lt; eauto.
Qed.
Hint Resolve implies_safe_inf_choice_sequence_entry2inf : slow.

Lemma implies_safe_inf_library_library2inf {o} :
  forall M (lib : @library o) d,
    safe_library M lib
    -> safe_inf_library_entry M d
    -> safe_inf_library M (library2inf lib d).
Proof.
  introv sl sd; introv.
  unfold safe_inf_library_entry, library2inf.
  remember (select n lib) as e; symmetry in Heqe; destruct e; auto.
  apply select_in in Heqe; apply LIn_implies_In in Heqe.
  apply sl in Heqe.
  remember (library_entry2inf l) as h; symmetry in Heqh.
  destruct h; auto.
  destruct l; simpl in *; ginv; eauto 3 with slow.
Qed.
Hint Resolve implies_safe_inf_library_library2inf : slow.

Lemma inf_entry_extends_library_entry2inf {o} :
  forall (entry : @library_entry o),
    inf_entry_extends (library_entry2inf entry) entry.
Proof.
  introv; unfold inf_entry_extends, library_entry2inf.
  destruct entry; tcsp.
  dands; auto.
  unfold inf_choice_sequence_entry_extend; simpl.
  destruct entry; simpl; dands; auto.
  introv sel.
  unfold choice_seq_vals2inf; allrw; auto.
Qed.
Hint Resolve inf_entry_extends_library_entry2inf : slow.

Lemma matching_entries_trans {o} :
  forall (e1 e2 e3 : @library_entry o),
    matching_entries e1 e2
    -> matching_entries e2 e3
    -> matching_entries e1 e3.
Proof.
  introv h q; unfold matching_entries in *.
  eapply same_entry_name_trans; eauto.
Qed.

Lemma matching_entries_sym {o} :
  forall (e1 e2 : @library_entry o),
    matching_entries e1 e2
    -> matching_entries e2 e1.
Proof.
  introv h; unfold matching_entries in *.
  eapply same_entry_name_sym; eauto.
Qed.
Hint Resolve matching_entries_sym : slow.

Lemma inf_lib_extends_library2inf {o} :
  forall M (lib : @library o) d,
    safe_inf_library_entry M d
    -> inf_lib_extends M (library2inf lib d) lib.
Proof.
  introv safed.
  split; eauto 2 with slow.

  {
    introv i.
    exists (length lib).
    induction lib; simpl in *; tcsp.

    repndors; subst; tcsp.

    - left.
      destruct a; simpl; tcsp.
      dands; auto; eauto 2 with slow.

    - repnd.
      autodimp IHlib hyp.
      right.
      dands; auto.
      intro h; destruct i0.
      unfold library2inf in h; simpl in h; eauto 3 with slow.
  }

(*  {
    introv i.
    apply list_in_implies_select in i; exrepnd.
    unfold library2inf.
    exists n.
    allrw; simpl; eauto 2 with slow.
  }*)
Qed.
Hint Resolve inf_lib_extends_library2inf : slow.

Lemma inf_lib_extends_implies_safe_inf_library {o} :
  forall {M} (lib : @library o) (infl : inf_library),
    safe_library M lib
    -> inf_lib_extends M infl lib
    -> safe_inf_library M infl.
Proof.
  introv safe ext.
  dup ext as h.
  destruct h as [ext1 safe1 sub1]; tcsp.
Qed.
Hint Resolve inf_lib_extends_implies_safe_inf_library : slow.

Lemma safe_inf_library_entry_simple_inf_choice_seq {o} :
  forall (M : @Mem o) name, safe_inf_library_entry M (simple_inf_choice_seq name).
Proof.
  introv; unfold safe_inf_library_entry; simpl; auto.
Qed.
Hint Resolve safe_inf_library_entry_simple_inf_choice_seq : slow.

Lemma bar_non_empty {o} :
  forall {M} {lib} (bar : @BarLib o M lib),
  exists (lib' : library), bar_lib_bar bar lib'.
Proof.
  introv.
  destruct bar as [bar cond].

  pose proof (fresh_choice_seq_name_in_library lib) as h; exrepnd.

  pose proof (cond (library2inf lib (simple_inf_choice_seq name))) as q.
  repeat (autodimp q hyp); eauto 3 with slow; exrepnd; simpl in *; tcsp;[].
  exists lib'; auto.
Qed.

Lemma in_bar_implies_extends {o} :
  forall {M} {lib} (bar : @BarLib o M lib) lib',
    bar_lib_bar bar lib' -> lib_extends M lib' lib.
Proof.
  introv b.
  destruct bar as [bar cond ext]; simpl in *; tcsp.
Qed.
Hint Resolve in_bar_implies_extends : slow.
