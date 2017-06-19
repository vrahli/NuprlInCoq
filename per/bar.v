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

Lemma entry_extends_preserves_matching_entries_left {o}:
  forall (entry1 entry2 entry : @library_entry o),
    entry_extends entry1 entry2
    -> matching_entries entry1 entry
    -> matching_entries entry2 entry.
Proof.
  introv h m; unfold entry_extends in h.
  unfold matching_entries in *.
  destruct entry1; simpl in *.
  - destruct entry2; simpl in *; repnd; subst; tcsp; ginv.
  - subst; simpl in *; auto.
Qed.
Hint Resolve entry_extends_preserves_matching_entries_left : slow.

Lemma entry_in_library_extends_implies_entry_in_library {o} :
  forall (entry : @library_entry o) lib,
    entry_in_library_extends entry lib
    ->
    exists entry',
      entry_in_library entry' lib
      /\ entry_extends entry' entry.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  repndors; repnd; tcsp.

  - exists a; dands; tcsp.

  - autodimp IHlib hyp.
    exrepnd.
    exists entry'; dands; tcsp.
    right; dands; auto.
    intro q; destruct h0; eauto 2 with slow.
Qed.

Lemma entry_extends_preserves_matching_entries_left_rev {o}:
  forall (entry1 entry2 entry : @library_entry o),
    entry_extends entry2 entry1
    -> matching_entries entry1 entry
    -> matching_entries entry2 entry.
Proof.
  introv h m; unfold entry_extends in h.
  unfold matching_entries in *.
  destruct entry2; simpl in *.
  - destruct entry1; simpl in *; repnd; subst; tcsp; ginv.
  - subst; simpl in *; auto.
Qed.
Hint Resolve entry_extends_preserves_matching_entries_left_rev : slow.

Lemma choice_sequence_entry_extend_trans {o} :
  forall (entry1 entry2 entry3 : @ChoiceSeqEntry o),
    choice_sequence_entry_extend entry1 entry2
    -> choice_sequence_entry_extend entry2 entry3
    -> choice_sequence_entry_extend entry1 entry3.
Proof.
  introv h1 h2; unfold choice_sequence_entry_extend in *.
  repnd; allrw; dands; auto.
  destruct entry1, entry2, entry3; simpl in *.
  unfold choice_sequence_vals_extend in *; exrepnd; subst.
  eexists.
  rewrite <- app_assoc; eauto.
Qed.
Hint Resolve choice_sequence_entry_extend_trans : slow.

Lemma entry_extends_trans {o} :
  forall (entry1 entry2 entry3 : @library_entry o),
    entry_extends entry1 entry2
    -> entry_extends entry2 entry3
    -> entry_extends entry1 entry3.
Proof.
  introv h1 h2; unfold entry_extends in *.
  destruct entry1; simpl in *; tcsp.
  - destruct entry2; simpl in *; repnd; subst; tcsp.
    destruct entry3; simpl in *; repnd; subst; tcsp; ginv.
    dands; auto; eauto 2 with slow.
  - destruct entry2; simpl in *; repnd; subst; tcsp.
    destruct entry3; simpl in *; repnd; subst; tcsp; ginv.
Qed.
Hint Resolve entry_extends_trans : slow.

Lemma subset_library_trans {o} :
  forall (lib1 lib2 lib3 : @library o),
    subset_library lib1 lib2
    -> subset_library lib2 lib3
    -> subset_library lib1 lib3.
Proof.
  introv h1 h2 i; unfold subset_library in *.
  applydup h1 in i; exrepnd.
  applydup h2 in i0; exrepnd.
  eexists; dands; eauto 2 with slow.
Qed.
Hint Resolve subset_library_trans : slow.

Lemma entry_extends_preserves_entry_in_library_extends {o} :
  forall (entry1 entry2 : @library_entry o) lib,
    entry_extends entry1 entry2
    -> entry_in_library_extends entry1 lib
    -> entry_in_library_extends entry2 lib.
Proof.
  induction lib; introv ext i; simpl in *; tcsp.
  repndors; repnd; tcsp.

  - left; eauto 2 with slow.

  - right; dands; auto.
    intro q; destruct i0; eauto 2 with slow.
Qed.
Hint Resolve entry_extends_preserves_entry_in_library_extends : slow.

Lemma lib_extends_trans {o} :
  forall M (lib1 lib2 lib3 : @library o),
    lib_extends M lib1 lib2
    -> lib_extends M lib2 lib3
    -> lib_extends M lib1 lib3.
Proof.
  introv ext1 ext2.
  destruct ext1 as [ext1 safe1 ss1].
  destruct ext2 as [ext2 safe2 ss2].

  split; dands; eauto 2 with slow.

  - introv i.
    apply ext2 in i.

    apply entry_in_library_extends_implies_entry_in_library in i.
    exrepnd.
    apply ext1 in i1; eauto 2 with slow.

  - introv safe3.
    applydup safe2 in safe3; tcsp.
Qed.
Hint Resolve lib_extends_trans : slow.

Lemma nil_subset_library {o} :
  forall (lib : @library o), subset_library [] lib.
Proof.
  introv i; simpl in *; tcsp.
Qed.
Hint Resolve nil_subset_library : slow.

Lemma lib_extends_nil {o} :
  forall M (lib : @library o), safe_library M lib -> lib_extends M lib [].
Proof.
  introv safe; split; simpl; tcsp; eauto 2 with slow.
Qed.
Hint Resolve lib_extends_nil : slow.

Lemma safe_library_cons_iff {o} :
  forall (M : @Mem o) entry lib,
    safe_library M (entry :: lib) <-> (safe_library_entry M entry /\ safe_library M lib).
Proof.
  introv; split; intro h; repnd; dands; tcsp.

  - apply h; simpl; tcsp.

  - introv i; apply h; simpl; tcsp.

  - introv i; simpl in *; repndors; subst; tcsp.
Qed.

Lemma list_in_snoc :
  forall {A} x (l : list A) a,
    List.In x (snoc l a) <-> (List.In x l \/ x = a).
Proof.
  induction l; introv; simpl in *; split; intro h; repndors; repnd; subst; tcsp.

  - apply IHl in h; repndors; tcsp.

  - right; apply IHl; tcsp.

  - right; apply IHl; tcsp.
Qed.

Lemma safe_library_snoc_iff {o} :
  forall (M : @Mem o) e lib,
    safe_library M (snoc lib e) <-> (safe_library M lib /\ safe_library_entry M e).
Proof.
  introv; split; intro h; repnd; dands; tcsp.

  - introv i; apply h; apply list_in_snoc; tcsp.

  - apply h; apply list_in_snoc; tcsp.

  - introv i; apply list_in_snoc in i; repndors; subst; tcsp.
Qed.

Lemma implies_entry_in_library_snoc {o} :
  forall entry (lib : @library o) e,
    entry_in_library entry lib
    -> entry_in_library entry (snoc lib e).
Proof.
  induction lib; introv i; simpl in *; tcsp.
Qed.
Hint Resolve implies_entry_in_library_snoc : slow.

Lemma inf_lib_extends_snoc_implies_head {o} :
  forall {M} infLib (lib : @library o) e,
    safe_library_entry M e
    -> inf_lib_extends M infLib (snoc lib e)
    -> inf_lib_extends M infLib lib.
Proof.
  introv safee i.
  destruct i as [ext safe].
  split.

  - introv i; apply ext; eauto 2 with slow.

  - introv safel.
    apply safe.
    apply safe_library_snoc_iff; dands; auto.
Qed.
Hint Resolve inf_lib_extends_snoc_implies_head : slow.

Lemma entry_in_library_snoc_implies {o} :
  forall entry (lib : @library o) e,
    entry_in_library entry (snoc lib e)
    -> entry_in_library entry lib \/ entry = e.
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.
  apply IHlib in i; repndors; tcsp.
Qed.

Lemma implies_inf_lib_extends_snoc {o} :
  forall {M} (infLib : @inf_library o) lib e k,
    inf_lib_extends M infLib lib
    -> entry_in_inf_library_extends e k infLib
    -> inf_lib_extends M infLib (snoc lib e).
Proof.
  introv ext i.
  destruct ext as [ext safe].
  split; eauto 2 with slow.

  - introv j; apply entry_in_library_snoc_implies in j; repndors; subst; tcsp.
    exists k; auto.

  - introv safe'; apply safe.
    allrw @safe_library_snoc_iff; tcsp.
Qed.
Hint Resolve implies_inf_lib_extends_snoc : slow.

Definition diff_entry_names {o} (e1 e2 : @library_entry o) : bool :=
  if same_entry_name_dec (entry2name e1) (entry2name e2)
  then false else true.

Lemma matching_entries_iff_diff_entry_names_false {o} :
  forall (e1 e2 : @library_entry o),
    matching_entries e1 e2 <-> diff_entry_names e1 e2 = false.
Proof.
  introv; unfold matching_entries, diff_entry_names.
  boolvar; split; intro h; tcsp.
Qed.

Lemma diff_entry_names_sym {o} :
  forall (e1 e2 : @library_entry o),
    diff_entry_names e1 e2 = diff_entry_names e2 e1.
Proof.
  introv; unfold diff_entry_names.
  boolvar; tcsp; apply same_entry_name_sym in s; tcsp.
Qed.

Lemma diff_entry_names_false_trans {o} :
  forall (e1 e2 e3 : @library_entry o),
    diff_entry_names e1 e2 = false
    -> diff_entry_names e2 e3 = false
    -> diff_entry_names e1 e3 = false.
Proof.
  introv m1 m2; allrw <- @matching_entries_iff_diff_entry_names_false.
  eapply matching_entries_trans; eauto.
Qed.

Lemma entry_in_library_snoc_shadowed_implies {o} :
  forall entry (lib : @library o) e,
    entry_in_library entry (snoc lib e)
    -> forallb (diff_entry_names e) lib = false
    -> entry_in_library entry lib.
Proof.
  induction lib; introv i h; simpl in *; tcsp.
  allrw andb_false_iff.
  repndors; repnd; subst; tcsp.

  - apply matching_entries_iff_diff_entry_names_false in h.
    right; dands; auto.
    apply entry_in_library_snoc_implies in i; repndors; subst; tcsp.

  - apply IHlib in h; auto.
Qed.
Hint Resolve entry_in_library_snoc_shadowed_implies : slow.

Lemma implies_inf_lib_extends_snoc_shadowed {o} :
  forall {M} (infLib : @inf_library o) lib e,
    inf_lib_extends M infLib lib
    -> forallb (diff_entry_names e) lib = false
    -> inf_lib_extends M infLib (snoc lib e).
Proof.
  introv ext i.
  destruct ext as [ext safe].
  split; eauto 2 with slow.

  - introv j.
    apply entry_in_library_snoc_shadowed_implies in j; auto.

  - introv safe'; apply safe.
    allrw @safe_library_snoc_iff; tcsp.
Qed.
Hint Resolve implies_inf_lib_extends_snoc_shadowed : slow.

Lemma entry_extends_preserves_forallb_diff_entry_names_false {o} :
  forall (e1 e2 : @library_entry o) lib,
    entry_extends e1 e2
    -> forallb (diff_entry_names e2) lib = false
    -> forallb (diff_entry_names e1) lib = false.
Proof.
  induction lib; introv ext h; simpl in *; tcsp.
  allrw andb_false_iff.
  repndors; repnd; subst; tcsp.
  left.
  allrw <- @matching_entries_iff_diff_entry_names_false.
  eauto 2 with slow.
Qed.

Lemma implies_entry_in_library_extends_snoc {o} :
  forall entry e (lib : @library o),
    entry_in_library_extends entry lib
    -> entry_in_library_extends entry (snoc lib e).
Proof.
  induction lib; introv i; simpl in *; tcsp.
Qed.
Hint Resolve implies_entry_in_library_extends_snoc : slow.

Lemma implies_entry_in_library_extends_tail_if_all_diff {o} :
  forall e (lib : @library o),
    forallb (diff_entry_names e) lib = true
    -> entry_in_library_extends e (snoc lib e).
Proof.
  induction lib; introv h; simpl in *; tcsp.

  - left; eauto 2 with slow.

  - allrw andb_true; repnd.
    right.
    dands; tcsp.

    introv m; apply matching_entries_iff_diff_entry_names_false in m.
    rewrite h0 in m; ginv.
Qed.
Hint Resolve implies_entry_in_library_extends_tail_if_all_diff : slow.

Lemma implies_lib_extends_snoc_lr_if_all_diff {o} :
  forall M (lib lib1 : @library o) e,
    lib_extends M lib lib1
    -> forallb (diff_entry_names e) lib = true
    -> lib_extends M (snoc lib e) (snoc lib1 e).
Proof.
  introv ext allt.
  destruct ext as [ext safe sub].
  split; simpl.

  - introv i.
    apply entry_in_library_snoc_implies in i; repndors; subst; eauto 2 with slow.
    apply ext in i; eauto 2 with slow.

  - introv safe1.
    allrw @safe_library_snoc_iff; repnd; dands; auto.

  - introv i; allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; allrw @list_in_snoc; tcsp.

    + exists e; allrw @list_in_snoc; dands; tcsp; eauto 2 with slow.
Qed.
Hint Resolve implies_lib_extends_snoc_lr_if_all_diff : slow.

Lemma implies_lib_extends_snoc_left {o} :
  forall M e (lib lib2 : @library o),
    safe_library_entry M e
    -> lib_extends M lib lib2
    -> lib_extends M (snoc lib e) lib2.
Proof.
  introv safee ext.
  destruct ext as [ext safe sub].
  split; simpl.

  - introv i.
    apply ext in i; eauto 2 with slow.

  - introv safe1.
    allrw @safe_library_snoc_iff; repnd; dands; auto.

  - introv i.
    apply sub in i; exrepnd.
    exists entry2; allrw @list_in_snoc; tcsp.
Qed.
Hint Resolve implies_lib_extends_snoc_left : slow.

Lemma implies_lib_extends_cons_left_snoc_right {o} :
  forall M e (lib : @library o) lib1,
    forallb (diff_entry_names e) lib1 = true
    -> lib_extends M lib lib1
    -> lib_extends M (e :: lib) (snoc lib1 e).
Proof.
  introv allt ext.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_implies in i; repndors; subst; eauto 2 with slow.
    applydup ext in i.
    right; dands; auto.
    introv m.
    rewrite forallb_forall in allt.
    pose proof (allt entry) as q.
    apply matching_entries_sym in m.
    apply matching_entries_iff_diff_entry_names_false in m.
    rewrite m in q.
    autodimp q hyp; eauto 2 with slow.

  - introv safe1.
    allrw @safe_library_snoc_iff.
    allrw @safe_library_cons_iff; repnd; dands; auto.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; dands; tcsp.

    + exists e; dands; tcsp; eauto 2 with slow.
Qed.
Hint Resolve implies_lib_extends_cons_left_snoc_right : slow.

Lemma implies_lib_extends_cons_left {o} :
  forall M e (lib lib2 : @library o),
    lib_extends M lib lib2
    -> safe_library_entry M e
    -> forallb (diff_entry_names e) lib2 = true
    -> lib_extends M (e :: lib) lib2.
Proof.
  introv ext safee allt.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    applydup ext in i; right; dands; auto.
    introv m.
    rewrite forallb_forall in allt.
    pose proof (allt entry) as q.
    apply matching_entries_sym in m.
    apply matching_entries_iff_diff_entry_names_false in m.
    rewrite m in q.
    autodimp q hyp; eauto 2 with slow.

  - introv safe1.
    rw @safe_library_cons_iff.
    apply safe in safe1; dands; auto.

  - introv i; simpl.
    apply sub in i; exrepnd.
    exists entry2; tcsp.
Qed.
Hint Resolve implies_lib_extends_cons_left : slow.

Lemma lib_extends_snoc_lr_if_all_diff_false {o} :
  forall M e (lib lib1 : @library o),
    lib_extends M lib lib1
    -> forallb (diff_entry_names e) lib1 = false
    -> lib_extends M (snoc lib e) (snoc lib1 e).
Proof.
  introv ext allt.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i; auto.
    apply ext in i.
    apply implies_entry_in_library_extends_snoc; auto.

  - introv safe1.
    allrw @safe_library_snoc_iff; repnd.
    apply safe in safe0; dands; auto.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; dands; auto.
      allrw @list_in_snoc; tcsp.

    + exists e; dands; eauto 2 with slow.
      allrw @list_in_snoc; tcsp.
Qed.
Hint Resolve lib_extends_snoc_lr_if_all_diff_false : slow.

Lemma forallb_false :
  forall {A} (f : A -> bool) (l : list A),
    forallb f l = false <-> exists (x : A), List.In x l /\ f x = false.
Proof.
  induction l; simpl; split; intro h; exrepnd; ginv; tcsp.

  - allrw @andb_false_iff; repndors; tcsp.

    + exists a; tcsp.

    + apply IHl in h; exrepnd.
      exists x; dands; auto.

  - apply andb_false_iff.
    repndors; subst; tcsp.
    right; apply IHl; exists x; tcsp.
Qed.

Lemma implies_matching_entries_refl {o} :
  forall (e x : @library_entry o),
    matching_entries e x
    -> matching_entries e e.
Proof.
  introv m.
  eapply matching_entries_trans;[eauto|].
  apply matching_entries_sym; auto.
Qed.
Hint Resolve implies_matching_entries_refl : slow.

Lemma dec_matching_entries {o} :
  forall (e1 e2 : @library_entry o),
    decidable (matching_entries e1 e2).
Proof.
  introv.
  remember (diff_entry_names e1 e2) as b; symmetry in Heqb; destruct b.

  - right; intro m.
    apply matching_entries_iff_diff_entry_names_false in m.
    rewrite m in Heqb; ginv.

  - left.
    apply matching_entries_iff_diff_entry_names_false; auto.
Qed.

Lemma in_implies_entry_in_library {o} :
  forall (x e : @library_entry o) (lib : library),
    matching_entries e x
    -> List.In e lib
    -> exists e', entry_in_library e' lib /\ matching_entries e e'.
Proof.
  induction lib; introv me i; simpl in *; tcsp; repndors; repnd; subst; tcsp.

  - exists e; dands; tcsp; eauto 2 with slow.

  - repeat (autodimp IHlib hyp); exrepnd.
    destruct (dec_matching_entries e a).

    + exists a; dands; tcsp.

    + exists e'; dands; tcsp.
      right; dands; auto.
      introv m; destruct n.
      eapply matching_entries_trans; eauto.
Qed.

Lemma entry_in_library_snoc_tail {o} :
  forall (lib : @library o) e,
    (forall x, List.In x lib -> diff_entry_names e x = true)
    -> entry_in_library e (snoc lib e).
Proof.
  induction lib; introv imp; simpl in *; tcsp.
  pose proof (imp a) as q; autodimp q hyp.
  right; dands; tcsp.
  intro m.
  apply matching_entries_iff_diff_entry_names_false in m; rewrite m in q; ginv.
Qed.
Hint Resolve entry_in_library_snoc_tail : slow.

Lemma entry_in_library_snoc_tail2 {o} :
  forall (lib : @library o) e,
    forallb (diff_entry_names e) lib = true
    -> entry_in_library e (snoc lib e).
Proof.
  introv h; apply entry_in_library_snoc_tail.
  rewrite forallb_forall in h; auto.
Qed.
Hint Resolve entry_in_library_snoc_tail2 : slow.

Lemma inf_library_extends_implies {o} :
  forall (e : @library_entry o) n inflib,
    entry_in_inf_library_extends e n inflib
    -> exists k,
        k <= n
        /\ inf_entry_extends (inflib k) e
        /\ forall j, j < k -> ~ inf_matching_entries (inflib j) e.
Proof.
  induction n; introv h; simpl in *; tcsp.
  repndors; repnd; tcsp.

  - exists 0; dands; auto; try omega.
    introv q; try omega.

  - applydup IHn in h; exrepnd.
    exists (S k); simpl; dands; auto; try omega.
    introv q.
    destruct j; auto.
    apply h2; try omega.
Qed.

Lemma inf_entry_extends_implies_inf_matching_entries {o} :
  forall ie (e x : @library_entry o),
    matching_entries e x
    -> inf_entry_extends ie e
    -> inf_matching_entries ie e.
Proof.
  introv m h; unfold inf_entry_extends in h.
  unfold inf_matching_entries.
  unfold matching_entries in m.
  destruct ie, e, x; simpl in *; repnd; subst; tcsp.
  rewrite <- matching_entry_sign_is_same_opabs in *.
  eapply implies_matching_entry_sign_refl; eauto.
Qed.

Lemma matching_entries_preserves_inf_matching_entries {o} :
  forall (ie : @inf_library_entry o) (e1 e2 : library_entry),
    matching_entries e1 e2
    -> inf_matching_entries ie e1
    -> inf_matching_entries ie e2.
Proof.
  introv m w.
  unfold matching_entries in *.
  unfold inf_matching_entries in *.
  destruct ie, e1, e2; simpl in *; subst; tcsp.
  eapply same_opabs_trans;[eauto|]; auto.
Qed.
Hint Resolve matching_entries_preserves_inf_matching_entries : slow.

Lemma inf_library_extends_two_matching_entries {o} :
  forall (e1 e2 : @library_entry o) n1 n2 inflib,
    matching_entries e1 e2
    -> entry_in_inf_library_extends e1 n1 inflib
    -> entry_in_inf_library_extends e2 n2 inflib
    -> exists n,
        n <= n1
        /\ n <= n2
        /\ inf_entry_extends (inflib n) e1
        /\ inf_entry_extends (inflib n) e2
        /\ forall m, m < n -> ~ inf_matching_entries (inflib m) e1.
Proof.
  introv m ext1 ext2.
  apply inf_library_extends_implies in ext1.
  apply inf_library_extends_implies in ext2.
  exrepnd.

  pose proof (Nat.lt_trichotomy k k0) as w; repndors; subst.

  - pose proof (ext4 k) as q; autodimp q hyp.
    destruct q.
    eapply inf_entry_extends_implies_inf_matching_entries in ext3;
      [|apply matching_entries_sym;eauto].
    eapply matching_entries_preserves_inf_matching_entries;[|eauto].
    apply matching_entries_sym; auto.

  - exists k0; dands; auto.

  - pose proof (ext0 k0) as q; autodimp q hyp.
    destruct q.
    eapply inf_entry_extends_implies_inf_matching_entries in ext5;[|eauto].
    eapply matching_entries_preserves_inf_matching_entries;[|eauto]; auto.
Qed.

Fixpoint combine_choice_seq_vals {o}
         (vals1 vals2 : @ChoiceSeqVals o) : ChoiceSeqVals :=
  match vals1, vals2 with
  | [], _ => vals2
  | _, [] => vals1
  | v :: vs1, _ :: vs2 => v :: combine_choice_seq_vals vs1 vs2
  end.

Lemma exists_combine_choice_seq_vals_1 {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) vals,
    (forall n v, select n vals1 = Some v -> vals n = v)
    -> (forall n v, select n vals2 = Some v -> vals n = v)
    -> exists vals0, combine_choice_seq_vals vals1 vals2 = vals1 ++ vals0.
Proof.
  induction vals1; introv imp1 imp2; simpl in *.

  - exists vals2; auto.

  - destruct vals2; simpl.

    + exists ([] : @ChoiceSeqVals o); autorewrite with slow; auto.

    + pose proof (IHvals1 vals2 (fun n => vals (S n))) as q; clear IHvals1.
      repeat (autodimp q hyp).
      exrepnd; allrw.
      exists vals0; auto.
Qed.

Lemma exists_combine_choice_seq_vals_2 {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) vals,
    (forall n v, select n vals1 = Some v -> vals n = v)
    -> (forall n v, select n vals2 = Some v -> vals n = v)
    -> exists vals0, combine_choice_seq_vals vals1 vals2 = vals2 ++ vals0.
Proof.
  induction vals1; introv imp1 imp2; simpl in *.

  - exists ([] : @ChoiceSeqVals o); autorewrite with slow; auto.

  - destruct vals2; simpl.

    + exists (a :: vals1); auto.

    + pose proof (IHvals1 vals2 (fun n => vals (S n))) as q; clear IHvals1.
      repeat (autodimp q hyp).
      exrepnd; allrw.
      exists vals0; auto.

      pose proof (imp1 0 a) as z; simpl in z; autodimp z hyp.
      pose proof (imp2 0 c) as w; simpl in w; autodimp w hyp.
      subst; auto.
Qed.

Lemma inf_entry_extends_two_entries_implies_entry_extends_sp {o} :
  forall (ie : @inf_library_entry o) e1 e2,
    inf_entry_extends ie e1
    -> inf_entry_extends ie e2
    ->
    exists e,
      entry_extends e e1
      /\ entry_extends e e2.
Proof.
  destruct ie, e1, e2; introv ext1 ext2; simpl in *; repnd; repeat (subst; tcsp);
    [|assert (correct1 = correct0) as xx by (apply correct_abs_proof_irrelevance); subst;
      assert (correct0 = correct) as xx by (apply correct_abs_proof_irrelevance); subst;
      exists (lib_abs opabs1 vars1 rhs1 correct); dands; unfold entry_extends; auto];[].

  destruct entry as [vals restr].
  destruct entry0 as [vals1 restr1].
  destruct entry1 as [vals2 restr2].
  unfold inf_choice_sequence_entry_extend in *; simpl in *.
  repnd; repeat subst.
  unfold inf_choice_sequence_vals_extend in *.

  exists (lib_cs name1 (MkChoiceSeqEntry _ (combine_choice_seq_vals vals1 vals2) restr2)).
  simpl; dands; auto; unfold choice_sequence_entry_extend; simpl; dands; auto;
    unfold choice_sequence_vals_extend.

  - eapply exists_combine_choice_seq_vals_1; eauto.

  - eapply exists_combine_choice_seq_vals_2; eauto.
Qed.

Lemma select_combine_choice_seq_vals_implies_or {o} :
  forall n (vals1 vals2 : @ChoiceSeqVals o) v,
    select n (combine_choice_seq_vals vals1 vals2) = Some v
    -> (select n vals1 = Some v \/ select n vals2 = Some v).
Proof.
  induction n; introv h; simpl in *;
    destruct vals1; simpl in *; destruct vals2; ginv.
  apply IHn in h; tcsp.
Qed.

Lemma inf_entry_extends_two_entries_implies_entry_extends {o} :
  forall (ie : @inf_library_entry o) e1 e2,
    inf_entry_extends ie e1
    -> inf_entry_extends ie e2
    ->
    exists e,
      entry_extends e e1
      /\ entry_extends e e2
      /\ inf_entry_extends ie e.
Proof.
  destruct ie, e1, e2; introv ext1 ext2; simpl in *; repnd; repeat (subst; tcsp);
    [|assert (correct1 = correct0) as xx by (apply correct_abs_proof_irrelevance); subst;
      assert (correct0 = correct) as xx by (apply correct_abs_proof_irrelevance); subst;
      exists (lib_abs opabs1 vars1 rhs1 correct); dands; unfold entry_extends; auto];[].

  destruct entry as [vals restr].
  destruct entry0 as [vals1 restr1].
  destruct entry1 as [vals2 restr2].
  unfold inf_choice_sequence_entry_extend in *; simpl in *.
  repnd; repeat subst.
  unfold inf_choice_sequence_vals_extend in *.

  exists (lib_cs name1 (MkChoiceSeqEntry _ (combine_choice_seq_vals vals1 vals2) restr2)).
  simpl; dands; auto; unfold choice_sequence_entry_extend; simpl; dands; auto;
    unfold choice_sequence_vals_extend.

  - eapply exists_combine_choice_seq_vals_1; eauto.

  - eapply exists_combine_choice_seq_vals_2; eauto.

  - introv i; apply select_combine_choice_seq_vals_implies_or in i; repndors; tcsp.
Qed.

Lemma entry_extends_implies_matching_entries {o} :
  forall (e1 e2 e : @library_entry o),
    matching_entries e1 e
    -> entry_extends e1 e2
    -> matching_entries e1 e2.
Proof.
  introv m ext.
  destruct e1, e2, e; simpl in *; tcsp; ginv;
    unfold matching_entries in *; simpl in *; tcsp.
  inversion ext; subst; clear ext.
  eapply same_opabs_trans;[eauto|].
  apply same_opabs_sym;auto.
Qed.

Lemma lib_extend_cons_snoc_diff {o} :
  forall M e a (lib lib1 : @library o),
    entry_extends e a
    -> safe_library_entry M e
    -> forallb (diff_entry_names a) lib1 = true
    -> lib_extends M lib lib1
    -> lib_extends M (e :: lib) (snoc lib1 a).
Proof.
  introv exte safee allt ext.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_implies in i; repndors; subst; tcsp.
    applydup ext in i.
    right; dands; auto.
    introv m.
    eapply entry_extends_implies_matching_entries in exte;
      [|apply matching_entries_sym;eauto].
    eapply matching_entries_trans in exte;[|eauto].
    rewrite forallb_forall in allt.
    apply entry_in_library_implies_in in i.
    apply allt in i.
    apply matching_entries_sym in exte.
    apply matching_entries_iff_diff_entry_names_false in exte.
    rewrite exte in i; ginv.

  - introv safe1.
    allrw @safe_library_snoc_iff; repnd.
    apply safe in safe0; dands; auto.
    apply safe_library_cons_iff; dands; auto.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; dands; auto.

    + exists e; dands; eauto 2 with slow.
Qed.
Hint Resolve lib_extend_cons_snoc_diff : slow.

Lemma list_in_implies_select_some :
  forall {A} (l : list A) a,
    List.In a l -> exists n, select n l = Some a.
Proof.
  induction l; introv i; simpl in *; tcsp.
  repndors; subst; tcsp.

  - exists 0; simpl; auto.

  - apply IHl in i; exrepnd.
    exists (S n); auto.
Qed.

Lemma inf_entry_extends_preserves_safe_library_entry {o} :
  forall M (inf_entry : @inf_library_entry o) entry,
    inf_entry_extends inf_entry entry
    -> safe_inf_library_entry M inf_entry
    -> safe_library_entry M entry.
Proof.
  introv ext safe; destruct inf_entry, entry; simpl in *; simpl in *; tcsp.
  repnd; subst.
  destruct entry0 as [vals1 restr1].
  destruct entry as [vals2 restr2].
  simpl in *.
  unfold inf_choice_sequence_entry_extend in *; simpl in *; repnd; subst.
  unfold inf_choice_sequence_satisfies_restriction in safe.
  unfold inf_choice_sequence_vals_extend in *.
  unfold choice_sequence_satisfies_restriction.
  destruct restr2; simpl in *; repnd; dands; tcsp.

  - introv i.
    apply list_in_implies_select_some in i; exrepnd.
    apply ext in i0; subst; tcsp.

  - introv j.
    pose proof (nth_select1 i vals2 mkc_axiom j) as q.
    rewrite q.
    apply ext in q.
    rewrite <- q.
    rewrite safe; auto.
Qed.
Hint Resolve inf_entry_extends_preserves_safe_library_entry : slow.

Lemma two_entry_in_library_implies_or {o} :
  forall (e1 e2 : @library_entry o) lib,
    entry_in_library e1 lib
    -> entry_in_library e2 lib
    -> e1 = e2 \/ ~ matching_entries e1 e2.
Proof.
  induction lib; introv i1 i2; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.
  right; introv m; apply matching_entries_sym in m; tcsp.
Qed.

Lemma implies_lib_extends_cons_left_if_extends {o} :
  forall M e e' a (lib lib2 : @library o),
    lib_extends M lib lib2
    -> entry_extends e e'
    -> entry_in_library e' lib2
    -> safe_library_entry M e
    -> safe_library_entry M a
    -> lib_extends M (e :: lib) lib2.
Proof.
  introv ext exte ei safee safea.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    pose proof (two_entry_in_library_implies_or e' entry lib2) as q.
    repeat (autodimp q hyp).
    repndors; subst; tcsp.

    apply ext in i.
    right; dands; auto; eauto 2 with slow.

    introv m.
    eapply entry_extends_implies_matching_entries in exte;
      [|apply matching_entries_sym;eauto].
    eapply matching_entries_trans in exte;[|eauto].
    apply matching_entries_sym in exte; tcsp.

  - introv safe1.
    allrw @safe_library_cons_iff; dands; auto.

  - introv i; simpl.
    apply sub in i; exrepnd.
    exists entry2; dands; auto.
Qed.
Hint Resolve implies_lib_extends_cons_left_if_extends : slow.

Lemma implies_lib_extends_cons_snoc_left_if_extends {o} :
  forall M e e' a (lib lib2 : @library o),
    lib_extends M lib lib2
    -> entry_extends e e'
    -> entry_in_library e' lib2
    -> safe_library_entry M e
    -> safe_library_entry M a
    -> lib_extends M (e :: snoc lib a) lib2.
Proof.
  introv ext exte ei safee safea.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    pose proof (two_entry_in_library_implies_or e' entry lib2) as q.
    repeat (autodimp q hyp).
    repndors; subst; tcsp.

    apply ext in i.
    right; dands; auto; eauto 2 with slow.

    introv m.
    eapply entry_extends_implies_matching_entries in exte;
      [|apply matching_entries_sym;eauto].
    eapply matching_entries_trans in exte;[|eauto].
    apply matching_entries_sym in exte; tcsp.

  - introv safe1.
    allrw @safe_library_cons_iff; dands; auto.
    allrw @safe_library_snoc_iff; dands; auto.

  - introv i; simpl.
    apply sub in i; exrepnd.
    exists entry2; dands; auto.
    rewrite list_in_snoc; tcsp.
Qed.
Hint Resolve implies_lib_extends_cons_snoc_left_if_extends : slow.

Lemma lib_extends_cons_snoc_if_in {o} :
  forall M e e1 a (lib lib1 : @library o),
    safe_library_entry M e
    -> matching_entries a e1
    -> entry_extends e e1
    -> entry_in_library e1 lib1
    -> lib_extends M lib lib1
    -> lib_extends M (e :: snoc lib a) (snoc lib1 a).
Proof.
  introv safee m exte ei ext.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i;
      [|rewrite forallb_false;
        exists e1; rewrite <- matching_entries_iff_diff_entry_names_false;
        dands; auto;
        apply entry_in_library_implies_in; auto].

    applydup ext in i.
    destruct (dec_matching_entries entry e) as [d|d]; tcsp;
      [|right; dands; eauto 2 with slow].

    dup i as j.
    eapply two_entry_in_library_implies_or in j;[|exact ei].
    repndors; subst; tcsp.
    right; dands; eauto 2 with slow.
    introv m'.
    destruct j.
    eapply entry_extends_implies_matching_entries in exte;
      [|apply matching_entries_sym;eauto].
    apply matching_entries_sym.
    eapply matching_entries_trans;eauto.

  - introv safe1.
    allrw @safe_library_snoc_iff; repnd.
    allrw @safe_library_cons_iff; dands; auto.
    allrw @safe_library_snoc_iff; dands; auto.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    { apply sub in i; exrepnd.
      exists entry2; dands; auto.
      rewrite list_in_snoc; tcsp. }

    { exists a.
      rewrite list_in_snoc; dands; tcsp; eauto 2 with slow. }
Qed.
Hint Resolve lib_extends_cons_snoc_if_in : slow.

Lemma intersect_inf_lib_extends {o} :
  forall M infLib (lib1 lib2 : @library o),
    safe_library M lib1
    -> safe_library M lib2
    -> inf_lib_extends M infLib lib1
    -> inf_lib_extends M infLib lib2
    -> exists lib,
        lib_extends M lib lib1
        /\ lib_extends M lib lib2.
Proof.
  induction lib1 using rev_list_ind; introv safe1 safe2 ext1 ext2; simpl in *.

  - exists lib2; dands; eauto 2 with slow.

  - allrw @safe_library_snoc_iff; repnd.
    pose proof (IHlib1 lib2) as q; repeat (autodimp q hyp); eauto 2 with slow;[].
    exrepnd.

    remember (forallb (diff_entry_names a) lib) as b; symmetry in Heqb; destruct b.

    + (* [a] is not in [lib] *)

      exists (snoc lib a); dands; eauto 2 with slow.

    + (* [a] is in [lib] *)

      remember (forallb (diff_entry_names a) lib2) as w; symmetry in Heqw; destruct w.

      * (* [a] is not in [lib2] *)

        remember (forallb (diff_entry_names a) lib1) as z; symmetry in Heqz; destruct z.

        { (* [a] is not in [lib1] *)

          exists (a :: lib); dands; eauto 2 with slow.

        }

        { (* [a] is in [lib1] *)

          exists (snoc lib a); dands; eauto 2 with slow.
        }

      * (* [a] is in [lib2] *)

        remember (forallb (diff_entry_names a) lib1) as z; symmetry in Heqz; destruct z.

        { (* [a] is not in [lib1] *)

          (* since [a] is in [lib] and [lib2] but not in [lib1] we need
             to build a library that shadows [a] with a library that extends both
             the entry in [lib] and [lib2] *)

          dup Heqw as inlib2.
          apply forallb_false in Heqw; exrepnd.
          apply matching_entries_iff_diff_entry_names_false in Heqw0.

          (* we need to find the entry that actually gets used---it might not be x *)

          eapply in_implies_entry_in_library in Heqw1;
            [|apply matching_entries_sym;eauto].
          exrepnd.
          applydup q0 in Heqw1.

          pose proof (inf_lib_extends_ext _ _ _ ext1 a) as q.
          autodimp q hyp; exrepnd; eauto 2 with slow;[].
          pose proof (inf_lib_extends_ext _ _ _ ext2 e') as w.
          autodimp w hyp; exrepnd.
          pose proof (inf_library_extends_two_matching_entries a e' n n0 infLib) as h.
          repeat (autodimp h hyp).
          { eapply matching_entries_trans; eauto. }
          exrepnd.

          pose proof (inf_entry_extends_two_entries_implies_entry_extends (infLib n1) a e') as q.
          repeat (autodimp q hyp); exrepnd.

          assert (safe_library_entry M e) as safee.
          {
            applydup @inf_lib_extends_implies_safe_inf_library in ext2; auto.
            pose proof (ext0 n1) as q; eauto 2 with slow.
          }

          exists (e :: lib); dands; eauto 2 with slow.
        }

        { (* [a] is in [lib1] *)

          dup Heqw as in2lib.
          apply forallb_false in in2lib; exrepnd.
          apply matching_entries_iff_diff_entry_names_false in in2lib0.

          eapply in_implies_entry_in_library in in2lib1;
            [|apply matching_entries_sym;eauto].
          exrepnd.
          rename e' into e2.
          eapply matching_entries_trans in in2lib2;[|eauto].
          clear dependent x.
          applydup q0 in in2lib1.

          dup Heqz as in1lib.
          apply forallb_false in in1lib; exrepnd.
          apply matching_entries_iff_diff_entry_names_false in in1lib0.

          eapply in_implies_entry_in_library in in1lib1;
            [|apply matching_entries_sym;eauto].
          exrepnd.
          rename e' into e1.
          eapply matching_entries_trans in in1lib2;[|eauto].
          clear dependent x.
          applydup q1 in in1lib1.

          pose proof (inf_lib_extends_ext _ _ _ ext1 e1) as q.
          autodimp q hyp; exrepnd; eauto 2 with slow;[].
          pose proof (inf_lib_extends_ext _ _ _ ext2 e2) as w.
          autodimp w hyp; exrepnd.
          pose proof (inf_library_extends_two_matching_entries e1 e2 n n0 infLib) as h.
          repeat (autodimp h hyp).
          { eapply matching_entries_trans; eauto.
            apply matching_entries_sym; auto. }
          exrepnd.

          pose proof (inf_entry_extends_two_entries_implies_entry_extends (infLib n1) e1 e2) as q.
          repeat (autodimp q hyp); exrepnd.

          assert (safe_library_entry M e) as safee.
          {
            applydup @inf_lib_extends_implies_safe_inf_library in ext2; auto.
            pose proof (ext0 n1) as q; eauto 2 with slow.
          }

          exists (e :: snoc lib a); dands; eauto 3 with slow.
        }
Qed.

Lemma inf_lib_extends_snoc_implies_entry_ext {o} :
  forall M infLib (lib : @library o) e,
    forallb (diff_entry_names e) lib = true
    -> inf_lib_extends M infLib (snoc lib e)
    -> exists k, entry_in_inf_library_extends e k infLib.
Proof.
  introv allt ext.
  destruct ext as [ext safe].
  pose proof (ext e) as q; autodimp q hyp; eauto 2 with slow.
Qed.

Lemma forallb_diff_entry_names_false_implies_exists_entry {o} :
  forall e (lib : @library o),
    forallb (diff_entry_names e) lib = false
    ->
    exists a,
      entry_in_library a lib
      /\ matching_entries a e.
Proof.
  introv allt.
  rewrite forallb_false in allt; exrepnd.
  rewrite <- matching_entries_iff_diff_entry_names_false in allt0.
  eapply in_implies_entry_in_library in allt1;[|apply matching_entries_sym;eauto].
  exrepnd.
  exists e'; dands; auto.
  apply matching_entries_sym; eapply matching_entries_trans; eauto.
Qed.

Lemma inf_lib_extends_snoc_implies_entry_ext2 {o} :
  forall M infLib (lib : @library o) e,
    forallb (diff_entry_names e) lib = false
    -> inf_lib_extends M infLib (snoc lib e)
    -> exists a k,
        matching_entries a e
        /\ entry_in_library a lib
        /\ entry_in_inf_library_extends a k infLib.
Proof.
  introv allt ext.
  destruct ext as [ext safe].
  applydup @forallb_diff_entry_names_false_implies_exists_entry in allt; exrepnd.
  pose proof (ext a) as q; autodimp q hyp; eauto 2 with slow.
  exrepnd.
  exists a n; dands; auto.
Qed.

Lemma exists_entry_implies_forallb_diff_entry_names_false {o} :
  forall (e a : library_entry) (lib : @library o),
    entry_in_library e lib
    -> matching_entries e a
    -> forallb (diff_entry_names a) lib = false.
Proof.
  introv ei m.
  rewrite forallb_false.
  exists e; dands; eauto 2 with slow.
  apply matching_entries_iff_diff_entry_names_false; eauto 2 with slow.
Qed.

Lemma implies_lib_extends_snoc_snoc_snoc {o} :
  forall M e a (lib lib1 : @library o),
    lib_extends M lib lib1
    -> matching_entries e a
    -> entry_in_library e lib1
    -> forallb (diff_entry_names a) lib = true
    -> safe_library_entry M e
    -> lib_extends M (snoc (snoc lib e) a) (snoc lib1 a).
Proof.
  introv ext m ei allt safee.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i;
      [|eapply exists_entry_implies_forallb_diff_entry_names_false;eauto].
    applydup ext in i; eauto 3 with slow.

  - introv safe1.
    allrw @safe_library_snoc_iff; repnd; dands; auto.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    { apply sub in i; exrepnd.
      exists entry2; dands; auto.
      allrw @list_in_snoc; tcsp. }

    { exists a.
      rewrite list_in_snoc; dands; tcsp; eauto 2 with slow. }
Qed.
Hint Resolve implies_lib_extends_snoc_snoc_snoc : slow.

Lemma entry_in_library_implies_safe_library_entry {o} :
  forall M e (lib : @library o),
    entry_in_library e lib
    -> safe_library M lib
    -> safe_library_entry M e.
Proof.
  induction lib; introv i safe; simpl in *; tcsp.
  allrw @safe_library_cons_iff; repnd.
  repndors; subst; tcsp.
Qed.
Hint Resolve entry_in_library_implies_safe_library_entry : slow.

Lemma implies_forallb_diff_entry_names_snoc_false {o} :
  forall (e a : @library_entry o) lib,
    matching_entries e a
    -> forallb (diff_entry_names a) (snoc lib e) = false.
Proof.
  introv m.
  rewrite forallb_false.
  exists e.
  rewrite <- matching_entries_iff_diff_entry_names_false.
  rewrite list_in_snoc; dands; tcsp; eauto 2 with slow.
Qed.
Hint Resolve implies_forallb_diff_entry_names_snoc_false : slow.

Lemma implies_inf_lib_extends_snoc_snoc {o} :
  forall M infLib e a k (lib : @library o),
    inf_lib_extends M infLib lib
    -> matching_entries e a
    -> entry_in_inf_library_extends e k infLib
    -> inf_lib_extends M infLib (snoc (snoc lib e) a).
Proof.
  introv ext m ei.
  destruct ext as [ext safe].
  split; auto.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i; eauto 2 with slow.
    apply entry_in_library_snoc_implies in i; repndors; subst; tcsp; eauto.

  - introv safe'.
    allrw @safe_library_snoc_iff; repnd.
    applydup safe in safe'1; auto.
Qed.
Hint Resolve implies_inf_lib_extends_snoc_snoc : slow.

Lemma implies_inf_lib_extends_cons {o} :
  forall {M} (infLib : @inf_library o) lib e k,
    inf_lib_extends M infLib lib
    -> entry_in_inf_library_extends e k infLib
    -> inf_lib_extends M infLib (e :: lib).
Proof.
  introv ext i.
  destruct ext as [ext safe].
  split; eauto 2 with slow.

  - introv j; simpl in *; repndors; repnd; subst; tcsp.
    exists k; auto.

  - introv safe'; apply safe.
    allrw @safe_library_cons_iff; tcsp.
Qed.
Hint Resolve implies_inf_lib_extends_cons : slow.

Lemma inf_entry_extends_implies_entry_in_inf_library_extends {o} :
  forall n e a (infLib : @inf_library o),
    inf_entry_extends (infLib n) e
    -> matching_entries e a
    -> (forall m : nat, m < n -> ~ inf_matching_entries (infLib m) a)
    -> entry_in_inf_library_extends e (S n) infLib.
Proof.
  induction n; introv ext m imp; simpl in *; tcsp.
  pose proof (imp 0) as q; autodimp q hyp; try omega.
  right.
  dands; auto.

  { introv m'; destruct q; eauto 2 with slow. }

  pose proof (IHn e a (fun n => infLib (S n))) as h; simpl in h.
  repeat (autodimp h hyp).
  introv ltmn.
  apply imp; auto; try omega.
Qed.
Hint Resolve inf_entry_extends_implies_entry_in_inf_library_extends : slow.

Lemma entry_extends_implies_matching_entries_right {o} :
  forall (e1 e2 e : @library_entry o),
    matching_entries e2 e
    -> entry_extends e1 e2
    -> matching_entries e1 e2.
Proof.
  introv m ext.
  destruct e1, e2, e; simpl in *; tcsp; ginv;
    unfold matching_entries in *; simpl in *; tcsp.
  inversion ext; subst; clear ext.
  eapply same_opabs_trans;[eauto|].
  apply same_opabs_sym;auto.
Qed.

Lemma intersect_inf_lib_extends2 {o} :
  forall M infLib (lib1 lib2 : @library o),
    safe_library M lib1
    -> safe_library M lib2
    -> inf_lib_extends M infLib lib1
    -> inf_lib_extends M infLib lib2
    -> exists lib,
        lib_extends M lib lib1
        /\ lib_extends M lib lib2
        /\ inf_lib_extends M infLib lib.
Proof.
  induction lib1 using rev_list_ind; introv safe1 safe2 ext1 ext2; simpl in *.

  - exists lib2; dands; eauto 2 with slow.

  - allrw @safe_library_snoc_iff; repnd.
    pose proof (IHlib1 lib2) as q; repeat (autodimp q hyp); eauto 2 with slow;[].
    exrepnd.

    remember (forallb (diff_entry_names a) lib) as b; symmetry in Heqb; destruct b.

    + (* [a] is not in [lib] *)

      remember (forallb (diff_entry_names a) lib1) as z; symmetry in Heqz; destruct z.

      * (* [a] is not in [lib1] *)

        pose proof (inf_lib_extends_snoc_implies_entry_ext M infLib lib1 a) as q.
        repeat (autodimp q hyp).
        exrepnd.
        exists (snoc lib a); dands; eauto 2 with slow.

      * (* [a] is in [lib1] *)

        pose proof (inf_lib_extends_snoc_implies_entry_ext2 M infLib lib1 a) as q.
        repeat (autodimp q hyp); exrepnd.
        exists (snoc (snoc lib a0) a); dands; eauto 4 with slow.

    + (* [a] is in [lib] *)

      remember (forallb (diff_entry_names a) lib2) as w; symmetry in Heqw; destruct w.

      * (* [a] is not in [lib2] *)

        remember (forallb (diff_entry_names a) lib1) as z; symmetry in Heqz; destruct z.

        { (* [a] is not in [lib1] *)

          pose proof (inf_lib_extends_snoc_implies_entry_ext M infLib lib1 a) as q.
          repeat (autodimp q hyp); exrepnd.
          exists (a :: lib); dands; eauto 3 with slow.
        }

        { (* [a] is in [lib1] *)

          exists (snoc lib a); dands; eauto 2 with slow.
        }

      * (* [a] is in [lib2] *)

        remember (forallb (diff_entry_names a) lib1) as z; symmetry in Heqz; destruct z.

        { (* [a] is not in [lib1] *)

          (* since [a] is in [lib] and [lib2] but not in [lib1] we need
             to build a library that shadows [a] with a library that extends both
             the entry in [lib] and [lib2] *)

          dup Heqw as inlib2.
          apply forallb_false in Heqw; exrepnd.
          apply matching_entries_iff_diff_entry_names_false in Heqw0.

          (* we need to find the entry that actually gets used---it might not be x *)

          eapply in_implies_entry_in_library in Heqw1;
            [|apply matching_entries_sym;eauto].
          exrepnd.
          applydup q2 in Heqw1.

          pose proof (inf_lib_extends_ext _ _ _ ext1 a) as q.
          autodimp q hyp; exrepnd; eauto 2 with slow;[].
          pose proof (inf_lib_extends_ext _ _ _ ext2 e') as w.
          autodimp w hyp; exrepnd.
          pose proof (inf_library_extends_two_matching_entries a e' n n0 infLib) as h.

          repeat (autodimp h hyp).
          { eapply matching_entries_trans; eauto. }
          exrepnd.

          pose proof (inf_entry_extends_two_entries_implies_entry_extends (infLib n1) a e') as q.
          repeat (autodimp q hyp); exrepnd.

          assert (safe_library_entry M e) as safee.
          {
            applydup @inf_lib_extends_implies_safe_inf_library in ext2; auto.
            pose proof (ext0 n1) as q; eauto 2 with slow.
          }

          exists (e :: lib); dands; eauto 2 with slow.

          eapply implies_inf_lib_extends_cons; auto.
          eapply inf_entry_extends_implies_entry_in_inf_library_extends;
            eauto 2 with slow.
          introv lemn m'; apply h0 in lemn; destruct lemn; eauto 3 with slow.
        }

        { (* [a] is in [lib1] *)

          dup Heqw as in2lib.
          apply forallb_false in in2lib; exrepnd.
          apply matching_entries_iff_diff_entry_names_false in in2lib0.

          eapply in_implies_entry_in_library in in2lib1;
            [|apply matching_entries_sym;eauto].
          exrepnd.
          rename e' into e2.
          eapply matching_entries_trans in in2lib2;[|eauto].
          clear dependent x.
          applydup q2 in in2lib1.

          dup Heqz as in1lib.
          apply forallb_false in in1lib; exrepnd.
          apply matching_entries_iff_diff_entry_names_false in in1lib0.

          eapply in_implies_entry_in_library in in1lib1;
            [|apply matching_entries_sym;eauto].
          exrepnd.
          rename e' into e1.
          eapply matching_entries_trans in in1lib2;[|eauto].
          clear dependent x.
          applydup q1 in in1lib1.

          pose proof (inf_lib_extends_ext _ _ _ ext1 e1) as q.
          autodimp q hyp; exrepnd; eauto 2 with slow;[].
          pose proof (inf_lib_extends_ext _ _ _ ext2 e2) as w.
          autodimp w hyp; exrepnd.
          pose proof (inf_library_extends_two_matching_entries e1 e2 n n0 infLib) as h.
          repeat (autodimp h hyp).
          { eapply matching_entries_trans; eauto.
            apply matching_entries_sym; auto. }
          exrepnd.

          pose proof (inf_entry_extends_two_entries_implies_entry_extends (infLib n1) e1 e2) as q.
          repeat (autodimp q hyp); exrepnd.

          assert (safe_library_entry M e) as safee.
          {
            applydup @inf_lib_extends_implies_safe_inf_library in ext2; auto.
            pose proof (ext0 n1) as q; eauto 2 with slow.
          }

          exists (e :: snoc lib a); dands; eauto 3 with slow.

          apply (implies_inf_lib_extends_snoc_shadowed _ (e :: lib)).

          { eapply implies_inf_lib_extends_cons; auto.
            eapply inf_entry_extends_implies_entry_in_inf_library_extends;
              eauto 3 with slow.
            introv lemn m'; apply h0 in lemn; destruct lemn; eauto 3 with slow. }

          { simpl; apply andb_false_iff; left.
            apply matching_entries_iff_diff_entry_names_false.
            eapply matching_entries_trans;[exact in1lib2|].
            apply matching_entries_sym.
            eapply entry_extends_implies_matching_entries_right; auto.
            apply matching_entries_sym; eauto. }
        }
Qed.

Definition intersect_bars {o} {M} {lib}
           (safe : @safe_library o M lib)
           (bar1 bar2 : @BarLib o M lib) : BarLib M lib.
Proof.
  exists (fun (lib' : library) =>
            exists lib1 lib2,
              bar_lib_bar bar1 lib1
              /\ bar_lib_bar bar2 lib2
              /\ lib_extends M lib' lib1
              /\ lib_extends M lib' lib2).

  - introv ext.

    destruct bar1 as [bar1 bars1 ext1].
    destruct bar2 as [bar2 bars2 ext2].
    simpl in *.

    pose proof (bars1 infLib) as q; autodimp q hyp.
    pose proof (bars2 infLib) as h; autodimp h hyp.
    destruct q as [lib1 q]; repnd.
    destruct h as [lib2 h]; repnd.

    pose proof (intersect_inf_lib_extends2 M infLib lib1 lib2) as w.
    repeat (autodimp w hyp); eauto 2 with slow;[].

    exrepnd.
    exists lib0; dands; auto; eauto 2 with slow.

    exists lib1 lib2; dands; auto.

  - introv h; exrepnd.

    destruct bar1 as [bar1 bars1 ext1].
    destruct bar2 as [bar2 bars2 ext2].
    simpl in *.
    eauto 3 with slow.
Defined.
