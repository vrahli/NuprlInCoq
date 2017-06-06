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


Require Export nuprl.
Require Export nat_defs.


Definition memNat {o} : @Mem o :=
  fun c T => exists (n : nat), c = mkc_nat n.

Definition nmember {o} := @member o memNat.

Definition const0 {o} : nat -> @CTerm o := fun n => mkc_nat 0.

Definition seq0 : choice_sequence_name := "seq0".

Definition law0 {o} : @ChoiceSeqRestriction o := csc_coq_law const0.

Definition cs_entry0 {o} : @ChoiceSeqEntry o := MkChoiceSeqEntry _ [] law0.

Definition lib_entry0 {o} : @library_entry o := lib_cs seq0 cs_entry0.

Definition lib0 {o} : @library o := [lib_entry0].

Lemma isprog_mk_choice_seq {o} :
  forall (n : choice_sequence_name), @isprog o (mk_choice_seq n).
Proof.
  introv; apply isprog_eq; apply isprogram_mk_choice_seq.
Qed.

Definition mkc_choice_seq {o} name : @CTerm o :=
  exist isprog (mk_choice_seq name) (isprog_mk_choice_seq name).

Definition Nat2Nat {o} : @CTerm o := mkc_fun mkc_Nat mkc_Nat.

Lemma iscvalue_mkc_Nat {o} : @iscvalue o mkc_Nat.
Proof.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscvalue_mkc_Nat : slow.

Hint Rewrite @csubst_mk_cv : slow.

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

Definition choice_seq_vals2inf {o} (vals : @ChoiceSeqVals o) f : InfChoiceSeqVals :=
  fun n =>
    match select n vals with
    | Some v => v
    | None => (f n)
    end.

Definition restriction2default {o}
           (M : Mem)
           (r : @ChoiceSeqRestriction o) : ex_choice M r -> nat -> ChoiceSeqVal :=
  match r with
  | csc_no => fun p n => mkc_zero
  | csc_type _ => fun p n => projT1 p
  | csc_coq_law f => fun p n => f n
  end.

Definition choice_seq_entry2inf {o} M (e : @ChoiceSeqEntry o) : InfChoiceSeqEntry M :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    MkInfChoiceSeqEntry
      _
      M
      restr
      (fun p => choice_seq_vals2inf vals (restriction2default M restr p))
  end.

Definition library_entry2inf {o} M (e : @library_entry o) : inf_library_entry M :=
  match e with
  | lib_cs name entry => inf_lib_cs M name (choice_seq_entry2inf M entry)
  | lib_abs abs vars rhs correct => inf_lib_abs _ abs vars rhs correct
  end.

Definition library2inf {o} M (lib : @library o) (d : inf_library_entry M) : inf_library M :=
  fun n =>
    match select n lib with
    | Some entry => library_entry2inf M entry
    | None => d
    end.

Definition simple_choice_seq {o} (name : choice_sequence_name) : @library_entry o :=
  lib_cs name (MkChoiceSeqEntry _ [] csc_no).

(*Lemma shift_inf_lib_library2infinite_cons {o} :
  forall entry (lib : @library o) d,
    shift_inf_lib (library2infinite (entry :: lib) d)
    = library2infinite lib d.
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold shift_inf_lib; simpl; auto.
Qed.*)

Lemma entry_not_in_lib_cons_implies_entry_not_in_lib {o} :
  forall d entry (lib : @library o),
    entry_not_in_lib d (entry :: lib)
    -> entry_not_in_lib d lib.
Proof.
  introv e i.
  apply e; simpl; clear e.
  unfold in_lib in *; simpl.
  exrepnd.
  exists e; tcsp.
Qed.

Lemma inf_choice_sequence_entry_extend_choice_seq_entry2inf {o} :
  forall M (entry : @ChoiceSeqEntry o),
    inf_choice_sequence_entry_extend (choice_seq_entry2inf M entry) entry.
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
  forall M (entry1 entry2 : @library_entry o),
    inf_matching_entries (library_entry2inf M entry1) entry2
    -> matching_entries entry1 entry2.
Proof.
  introv h.
  destruct entry1; simpl in *; unfold inf_matching_entries in h; simpl in *;
    destruct entry2; simpl in *; tcsp.
Qed.
Hint Resolve inf_matching_entries_library_entry2inf_implies : slow.

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
    inf_lib_extends (library2inf M lib d) lib.
Proof.
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
Qed.
Hint Resolve inf_lib_extends_library2inf : slow.

Lemma implies_safe_inf_choice_sequence_entry2inf {o} :
  forall M (entry : @ChoiceSeqEntry o),
    safe_choice_sequence_entry M entry
    -> safe_inf_choice_sequence_entry (choice_seq_entry2inf M entry).
Proof.
  introv h; destruct entry as [vals restr]; simpl in *.
  introv.
  destruct restr; simpl in *; auto; GC.

  - exrepnd.
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
    -> safe_inf_library_entry d
    -> safe_inf_library (library2inf M lib d).
Proof.
  introv sl sd; introv.
  unfold safe_inf_library_entry, library2inf.
  remember (select n lib) as e; symmetry in Heqe; destruct e; auto.
  apply select_in in Heqe; apply LIn_implies_In in Heqe.
  apply sl in Heqe.
  remember (library_entry2inf M l) as h; symmetry in Heqh.
  destruct h; auto.
  destruct l; simpl in *; ginv; eauto 3 with slow.
Qed.
Hint Resolve implies_safe_inf_library_library2inf : slow.

Lemma safe_library_entry_simple_choice_seq {o} :
  forall (M : @Mem o) name, safe_library_entry M (simple_choice_seq name).
Proof.
  introv; unfold safe_library_entry; simpl; auto.
Qed.
Hint Resolve safe_library_entry_simple_choice_seq : slow.

Definition simple_inf_choice_seq {o} M (name : choice_sequence_name) : @inf_library_entry o M :=
  inf_lib_cs _ name (MkInfChoiceSeqEntry _ M csc_no (fun _ _ => mkc_zero)).

Lemma safe_inf_library_entry_simple_inf_choice_seq {o} :
  forall (M : @Mem o) name, safe_inf_library_entry (simple_inf_choice_seq M name).
Proof.
  introv; unfold safe_inf_library_entry; simpl; auto.
Qed.
Hint Resolve safe_inf_library_entry_simple_inf_choice_seq : slow.

Lemma bar_non_empty {o} :
  forall {M} {lib} (bar : @BarLib o M lib),
  exists (lib' : library),
    List.In lib' (bar_lib_bar bar).
Proof.
  introv.
  destruct bar as [bar cond].
  destruct bar as [|lib' bar]; simpl in *;[|exists lib'; tcsp].
  assert False; tcsp.
  unfold BarLibCond in cond.

  pose proof (fresh_choice_seq_name_in_library lib) as h; exrepnd.

  pose proof (cond (library2inf M lib (simple_inf_choice_seq M name))) as q; clear cond.
  repeat (autodimp q hyp); eauto 3 with slow; exrepnd; simpl in *; tcsp.
Qed.

Lemma safe_library_lib0 {o} : forall M, @safe_library o M lib0.
Proof.
  introv i.
  unfold lib0 in i; simpl in i; repndors; tcsp; subst.
  simpl; introv k; omega.
Qed.

Lemma BarLibCond_refl {o} :
  forall M (lib : @library o), BarLibCond M [lib] lib.
Proof.
  introv i h.
  exists lib; simpl; dands; tcsp; eauto 2 with slow.
Qed.
Hint Resolve BarLibCond_refl : slow.

Lemma find_cs_some_implies_list_in {o} :
  forall (lib : @library o) name e,
    find_cs lib name = Some e
    -> List.In (lib_cs name e) lib.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  destruct a; simpl in *; tcsp.
  boolvar; ginv; tcsp.
Qed.
Hint Resolve find_cs_some_implies_list_in : slow.

Lemma find_value_of_cs_at_vals_as_select {o} :
  forall (vals : @ChoiceSeqVals o) n,
    find_value_of_cs_at vals n = select n vals.
Proof.
  induction vals; simpl; auto; introv.
  - destruct n; simpl in *; tcsp.
  - destruct n; simpl in *; tcsp.
Qed.

Fixpoint follow_coq_law {o} (pos len : nat) (f : nat -> CTerm) : @ChoiceSeqVals o :=
  match len with
  | 0 => []
  | S n => f pos :: follow_coq_law (S pos) n f
  end.

Lemma length_follow_coq_law {o} :
  forall len pos (f : nat -> @CTerm o),
    length (follow_coq_law pos len f) = len.
Proof.
  induction len; introv; simpl in *; tcsp.
Qed.
Hint Rewrite @length_follow_coq_law : slow.

Definition extend_choice_seq_entry_upto {o}
           (e : @ChoiceSeqEntry o)
           (n : nat) : ChoiceSeqEntry :=
  match e with
  | MkChoiceSeqEntry _ vals (csc_coq_law f) =>
    MkChoiceSeqEntry
      _
      (vals ++ follow_coq_law (length vals) (n - length vals) f)
      (csc_coq_law f)
  | _ => e
  end.

Definition extend_library_entry_upto {o}
           (e    : @library_entry o)
           (name : choice_sequence_name)
           (n    : nat) : library_entry :=
  match e with
  | lib_cs name' x =>
    if choice_sequence_name_deq name name' then
      lib_cs name' (extend_choice_seq_entry_upto x n)
    else e
  | _ => e
  end.

Fixpoint extend_library_upto {o}
           (lib  : @library o)
           (name : choice_sequence_name)
           (n    : nat) : library :=
  match lib with
  | [] => []
  | entry :: entries =>
    extend_library_entry_upto entry name n :: extend_library_upto entries name n
  end.

Lemma choice_sequence_entry_extend_extend_choice_seq_entry_upto {o} :
  forall (entry : @ChoiceSeqEntry o) n,
    choice_sequence_entry_extend (extend_choice_seq_entry_upto entry n) entry.
Proof.
  introv; unfold choice_sequence_entry_extend; simpl.
  destruct entry as [vals restr]; simpl.
  destruct restr; simpl; dands; auto; eauto 2 with slow.
  eexists; eauto.
Qed.
Hint Resolve choice_sequence_entry_extend_extend_choice_seq_entry_upto : slow.

Lemma entry_extends_extend_library_entry_upto {o} :
  forall (entry : @library_entry o) name n,
    entry_extends (extend_library_entry_upto entry name n) entry.
Proof.
  introv; destruct entry; simpl in *; tcsp.
  boolvar; subst; eauto 2 with slow.
  unfold entry_extends; dands; auto; eauto 2 with slow.
Qed.
Hint Resolve entry_extends_extend_library_entry_upto : slow.

Lemma matching_entries_extend_library_entry_upto {o} :
  forall (e a : @library_entry o) name n,
    matching_entries (extend_library_entry_upto e name n) a
    -> matching_entries (extend_library_entry_upto e name n) e.
Proof.
  introv h; unfold matching_entries, extend_library_entry_upto in *.
  destruct e; simpl; eauto 2 with slow.
  - boolvar; subst; simpl in *; tcsp.
  - simpl in *.
    destruct a; simpl in *; tcsp.
    unfold same_opabs in *.
    eapply implies_matching_entry_sign_refl; eauto.
Qed.
Hint Resolve matching_entries_extend_library_entry_upto : slow.

Lemma implies_entry_in_library_extends_extend_library_upto {o} :
  forall entry (lib : @library o) name n,
    entry_in_library entry lib
    -> entry_in_library_extends entry (extend_library_upto lib name n).
Proof.
  induction lib; introv h; simpl in *; tcsp.
  repndors; subst; tcsp; eauto 2 with slow.

  repnd.
  right; dands; auto.
  intro q; destruct h0.
  eapply matching_entries_trans;[eauto|]; eauto 3 with slow.
Qed.
Hint Resolve implies_entry_in_library_extends_extend_library_upto : slow.

Lemma select_app_l :
  forall {T} i (l1 l2 : list T),
    i < length l1
    -> select i (l1 ++ l2) = select i l1.
Proof.
  induction i; introv h; simpl in *; tcsp.
  - destruct l1; simpl in *; try omega; auto.
  - destruct l1; simpl in *; try omega; tcsp.
    apply IHi; auto; try omega.
Qed.

Lemma implies_select_none :
  forall {T} n (l : list T),
    length l <= n -> select n l = None.
Proof.
  introv h; apply nth_select2; auto.
Qed.

Lemma select_nil :
  forall {T} n, @select T n [] = None.
Proof.
  introv; destruct n; simpl; auto.
Qed.
Hint Rewrite @select_nil : slow.

Lemma select_app_r :
  forall {T} i (l1 l2 : list T),
    length l1 <= i
    -> select i (l1 ++ l2) = select (i - length l1) l2.
Proof.
  induction i; introv h; simpl in *; tcsp.
  - destruct l1; simpl in *; try omega; auto.
  - destruct l1; simpl in *; try omega; tcsp.
    apply IHi; auto; try omega.
Qed.

Lemma select_follow_coq_low {o} :
  forall k p i (f : nat -> @CTerm o),
    k < i
    -> select k (follow_coq_law p i f) = Some (f (k + p)).
Proof.
  induction k; introv h; simpl in *.
  - destruct i; simpl in *; try omega; auto.
  - destruct i; simpl in *; try omega; auto.
    rewrite IHk; try omega.
    rewrite <- plus_n_Sm; auto.
Qed.

Lemma safe_library_cons_implies_tail {o} :
  forall M e (lib : @library o),
    safe_library M (e :: lib)
    -> safe_library M lib.
Proof.
  introv h i.
  apply h; simpl; tcsp.
Qed.
Hint Resolve safe_library_cons_implies_tail : slow.

Lemma implies_safe_library_extend_library_upto {o} :
  forall M (lib : @library o) name n,
    safe_library M lib
    -> safe_library M (extend_library_upto lib name n).
Proof.
  induction lib; introv safe i; simpl in *; tcsp.
  repndors; subst; tcsp; simpl in *.

  - destruct a; simpl in *; tcsp.

    pose proof (safe (lib_cs name0 entry)) as s; simpl in s; autodimp s hyp.

    boolvar; subst; simpl in *; tcsp.

    destruct entry as [vals restr]; simpl in *.
    destruct restr; simpl in *; tcsp.

    introv j.
    allrw length_app; autorewrite with slow in *.
    destruct (lt_dec i (length vals)) as [d|d].

    + applydup s in d.
      rewrite select_app_l; auto.

    + rewrite select_app_r; try omega.
      pose proof (Nat.le_exists_sub (length vals) i) as q.
      autodimp q hyp; try omega.
      exrepnd; subst.
      rewrite Nat.add_sub.
      rewrite le_plus_minus_r in j; try omega.
      rewrite select_follow_coq_low; auto; try omega.

  - eapply IHlib;[|eauto]; eauto 2 with slow.
Qed.
Hint Resolve implies_safe_library_extend_library_upto : slow.

Lemma subset_library_extend_library_upto {o} :
  forall (lib : @library o) name n,
    subset_library lib (extend_library_upto lib name n).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; subst; simpl in *; tcsp.

  - eexists; dands;[left;reflexivity|]; eauto 2 with slow.

  - apply (IHlib name n) in i; exrepnd.
    exists entry2; dands; auto.
Qed.
Hint Resolve subset_library_extend_library_upto : slow.

Lemma extend_library_upto_extends {o} :
  forall M name n (lib : @library o),
    lib_extends M (extend_library_upto lib name n) lib.
Proof.
  introv.
  split; auto; eauto 3 with slow.
Qed.
Hint Resolve extend_library_upto_extends : slow.

Lemma restriction_extend_choice_seq_entry_upto {o} :
  forall (entry : @ChoiceSeqEntry o) m,
    cse_restriction (extend_choice_seq_entry_upto entry m)
    = cse_restriction entry.
Proof.
  introv; destruct entry as [vals restr]; simpl; auto.
  destruct restr; simpl in *; tcsp.
Qed.
Hint Rewrite @restriction_extend_choice_seq_entry_upto : slow.

Lemma select_follow_coq_low_ite {o} :
  forall k p i (f : nat -> @CTerm o),
    select k (follow_coq_law p i f) =
    if lt_dec k i then Some (f (k + p))
    else None.
Proof.
  induction k; introv; simpl in *.
  - destruct i; simpl in *; try omega; auto.
  - destruct i; simpl in *; try omega; auto.
    rewrite IHk; try omega.
    boolvar; try omega; auto.
    rewrite <- plus_n_Sm; auto.
Qed.

Lemma implies_inf_choice_sequence_entry_extend_extend_choice_seq_entry_upto {o} :
  forall M (entry1 : @InfChoiceSeqEntry o M) entry2 m,
    safe_inf_choice_sequence_entry entry1
    -> inf_choice_sequence_entry_extend entry1 entry2
    -> inf_choice_sequence_entry_extend entry1 (extend_choice_seq_entry_upto entry2 m).
Proof.
  introv safe h; unfold inf_choice_sequence_entry_extend in *;
    repnd; simpl in *; dands; autorewrite with slow in *; auto.
  introv i.
  pose proof (h c) as q; clear h.
  destruct entry2 as [vals restr]; simpl in *.
  destruct restr; simpl in *; tcsp;[].
  destruct (le_dec (length vals) n) as [d|d].

  - rewrite select_app_r in i; auto.
    rewrite select_follow_coq_low_ite in i; try omega.
    boolvar; ginv.
    inversion i; subst; clear i; autorewrite with num slow in *.
    rewrite Nat.sub_add; auto.

    unfold safe_inf_choice_sequence_entry in safe.
    destruct entry1 as [restr vals1]; simpl in *.
    pose proof (safe c) as s; clear safe.
    rewrite h0 in s; simpl in s; tcsp.

  - rewrite select_app_l in i; try omega; tcsp.
Qed.
Hint Resolve implies_inf_choice_sequence_entry_extend_extend_choice_seq_entry_upto : slow.

Lemma implies_inf_entry_extends_extend_library_entry_upto {o} :
  forall M (inf_entry : @inf_library_entry o M) entry name m,
    safe_inf_library_entry inf_entry
    -> inf_entry_extends inf_entry entry
    -> inf_entry_extends inf_entry (extend_library_entry_upto entry name m).
Proof.
  introv safe h; destruct inf_entry; simpl in *; GC.

  - destruct entry; simpl in *; repnd; subst; tcsp.
    boolvar; subst; simpl in *; tcsp.
    dands; auto; eauto 2 with slow.

  - destruct entry; simpl in *; tcsp.
Qed.
Hint Resolve implies_inf_entry_extends_extend_library_entry_upto : slow.

Lemma entry2name_extend_library_entry_upto {o} :
  forall (entry : @library_entry o) name m,
    entry2name (extend_library_entry_upto entry name m)
    = entry2name entry.
Proof.
  introv; destruct entry; simpl in *; boolvar; tcsp.
Qed.
Hint Rewrite @entry2name_extend_library_entry_upto : slow.

Lemma inf_matching_entries_extend_library_entry_upto_r_implies {o} :
  forall M (inf_entry : @inf_library_entry o M) entry name m,
    inf_matching_entries inf_entry (extend_library_entry_upto entry name m)
    -> inf_matching_entries inf_entry entry.
Proof.
  introv h; unfold inf_matching_entries in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve inf_matching_entries_extend_library_entry_upto_r_implies : slow.

Lemma implies_safe_inf_library {o} :
  forall M (infLib : @inf_library o M),
    safe_inf_library infLib
    -> safe_inf_library (shift_inf_lib infLib).
Proof.
  introv safe; introv.
  unfold shift_inf_lib; tcsp.
Qed.
Hint Resolve implies_safe_inf_library : slow.

Lemma implies_entry_in_inf_library_extends_extend_library_entry_upto {o} :
  forall M n entry (infLib : @inf_library o M) name m,
    safe_inf_library infLib
    -> entry_in_inf_library_extends entry n infLib
    -> entry_in_inf_library_extends (extend_library_entry_upto entry name m) n infLib.
Proof.
  induction n; introv safe h; simpl in *; tcsp.
  repndors; repnd; simpl in *.

  - left.
    pose proof (safe 0) as s0; eauto 2 with slow.

  - right; dands; auto.

    + intro q; destruct h0; eauto 2 with slow.

    + eapply IHn; eauto 2 with slow.
Qed.
Hint Resolve implies_entry_in_inf_library_extends_extend_library_entry_upto : slow.

Lemma implies_matching_entries_extend_library_entry_upto {o} :
  forall (entry1 entry2 : @library_entry o) name n,
    matching_entries entry1 entry2
    -> matching_entries
         (extend_library_entry_upto entry1 name n)
         (extend_library_entry_upto entry2 name n).
Proof.
  introv h; destruct entry1, entry2; simpl in *; tcsp; boolvar;
    subst; unfold matching_entries; auto.
Qed.
Hint Resolve implies_matching_entries_extend_library_entry_upto : slow.

Lemma matching_entries_extend_library_entry_upto_implies {o} :
  forall (entry1 entry2 : @library_entry o) name n,
    matching_entries
      (extend_library_entry_upto entry1 name n)
      (extend_library_entry_upto entry2 name n)
    -> matching_entries entry1 entry2.
Proof.
  introv h; destruct entry1, entry2; simpl in *; tcsp; boolvar;
    subst; unfold matching_entries; auto.
Qed.
Hint Resolve matching_entries_extend_library_entry_upto_implies : slow.

Lemma entry_in_library_extend_library_upto_implies {o} :
  forall entry (lib : @library o) name n,
    entry_in_library entry (extend_library_upto lib name n)
    <->
    exists entry',
      entry_in_library entry' lib
      /\ entry = extend_library_entry_upto entry' name n.
Proof.
  induction lib; introv; split; intro h; simpl in *; tcsp.

  - repndors; repnd; subst; tcsp.

    + eexists; dands;[left;reflexivity|]; auto.

    + apply IHlib in h; exrepnd; subst.
      exists entry'; dands; tcsp.
      right; dands; auto.
      introv q; destruct h0; eauto 3 with slow.

  - exrepnd; repndors; repnd; subst; simpl in *; tcsp.

    right; dands; auto; eauto 2 with slow.

    + introv q; destruct h2; eauto 2 with slow.

    + apply IHlib.
      eexists; dands; eauto.
Qed.

Lemma implies_inf_lib_extends_extend_library_upto {o} :
  forall M (lib : @library o) name n (infLib : inf_library M),
    safe_inf_library infLib
    -> inf_lib_extends infLib lib
    -> inf_lib_extends infLib (extend_library_upto lib name n).
Proof.
  introv safe h i.
  apply entry_in_library_extend_library_upto_implies in i; exrepnd; subst.
  applydup h in i1.
  exrepnd.
  exists n0.
  eauto 2 with slow.
Qed.
Hint Resolve implies_inf_lib_extends_extend_library_upto : slow.

Lemma BarLibCond_extend_library_upto {o} :
  forall M (lib : @library o) name n,
    safe_library M lib
    -> BarLibCond M [extend_library_upto lib name n] lib.
Proof.
  introv safe i h.
  simpl.
  eexists; dands;[left;reflexivity| |]; simpl in *; eauto 2 with slow.
  autodimp h hyp; eauto 2 with slow.
Qed.
Hint Resolve BarLibCond_refl : slow.

Lemma find_cs_same_extend_library_upto {o} :
  forall (lib : @library o) name n,
    find_cs (extend_library_upto lib name n) name
    = match find_cs lib name with
      | Some entry => Some (extend_choice_seq_entry_upto entry n)
      | None => None
      end.
Proof.
  induction lib; introv; simpl; auto.
  destruct a; simpl; tcsp;[].
  boolvar; subst; tcsp.
Qed.

Lemma exists_bar_coq_law {o} :
  forall (M    : Mem)
         (lib  : @library o)
         (name : choice_sequence_name)
         (e    : ChoiceSeqEntry)
         (n    : nat)
         (f    : nat -> CTerm),
    safe_library M lib
    -> find_cs lib name = Some e
    -> entry2restriction e = csc_coq_law f
    ->
    exists (bar : BarLib M lib),
    forall (lib' : library),
      List.In lib' (bar_lib_bar bar)
      -> find_cs_value_at lib' name n = Some (f n).
Proof.
  introv safe find law.

  pose proof (safe (lib_cs name e)) as q; autodimp q hyp; eauto 2 with slow;[].

  destruct e as [vals restr]; simpl in *; subst.

  destruct (lt_dec n (length vals)) as [d|d].

  - exists (MkBarLib _ M lib [lib] (BarLibCond_refl _ lib)); simpl.
    introv i; repndors; subst; tcsp.
    unfold find_cs_value_at.
    allrw; simpl in *.
    applydup q in d; clear q.
    allrw <-; apply find_value_of_cs_at_vals_as_select.

  - exists (MkBarLib
              _ M lib
              [extend_library_upto lib name (S n)]
              (BarLibCond_extend_library_upto M lib name (S n) safe)).
    simpl; introv i; repndors; subst; simpl in *; tcsp.
    unfold find_cs_value_at.
    rewrite find_cs_same_extend_library_upto; allrw.
    simpl.
    rewrite find_value_of_cs_at_vals_as_select.
    rewrite select_app_r; try omega;[].
    rewrite select_follow_coq_low_ite; boolvar; try omega.

    { rewrite Nat.sub_add; auto; try omega. }

    { remember (length vals) as lv; destruct lv; simpl in *; try omega. }
Qed.

Lemma implies_compute_to_valc_apply_choice_seq {o} :
  forall lib (a : @CTerm o) name n v,
    computes_to_valc lib a (mkc_nat n)
    -> find_cs_value_at lib name n = Some v
    -> iscvalue v
    -> computes_to_valc lib (mkc_apply (mkc_choice_seq name) a) v.
Proof.
  introv comp find iscv.
  destruct_cterms.
  unfold computes_to_valc in *; simpl in *.
  eapply computes_to_value_step;[|csunf; simpl; reflexivity].
  split; eauto 2 with slow.
  eapply extensional_eapply.implies_reduces_to_eapply_choice_seq;[eauto| |eauto].
  apply computes_to_value_isvalue_refl; eauto 2 with slow.
Qed.

Lemma computes_to_valc_preserves_lib_extends {o} :
  forall M
         (lib1 lib2 : library)
         (ext  : lib_extends M lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @CTerm o)
         (comp : computes_to_valc lib1 a b),
    {b' : CTerm & computes_to_valc lib2 a b' # alphaeqc b b'}.
Proof.
  introv ext r.
  destruct_cterms; unfold computes_to_valc in *; simpl in *.
  unfold computes_to_value in *; repnd.
  unfold alphaeqc.
  dup r0 as comp.
  eapply reduces_to_preserves_lib_extends in r0;[|eauto|]; eauto 2 with slow.
  exrepnd.
  applydup @reduces_to_preserves_program in comp; eauto 2 with slow.
  applydup @alphaeq_preserves_program in r1.
  apply r2 in comp0; clear r2.
  allrw @isprogram_eq.
  exists (mk_ct b' comp0); simpl; dands; eauto 2 with slow.
Qed.

Lemma alphaeqc_mkc_nat_implies {o} :
  forall n (t : @CTerm o),
    alphaeqc (mkc_nat n) t -> t = mkc_nat n.
Proof.
  introv aeq; destruct_cterms; unfold alphaeqc in aeq; simpl in *.
  apply cterm_eq; simpl.
  apply alpha_eq_mk_nat in aeq; auto.
Qed.

Lemma computes_to_valc_nat_if_lib_extends {o} :
  forall M (lib1 lib2 : @library o) t n,
    lib_extends M lib1 lib2
    -> computes_to_valc lib2 t (mkc_nat n)
    -> computes_to_valc lib1 t (mkc_nat n).
Proof.
  introv ext comp.
  pose proof (computes_to_valc_preserves_lib_extends
                M lib2 lib1 ext t (mkc_nat n) comp) as h.
  exrepnd.
  apply alphaeqc_mkc_nat_implies in h0; subst; auto.
Qed.

Lemma in_bar_implies_extends {o} :
  forall M (lib lib' : @library o) (bar : BarLib M lib),
    List.In lib' (bar_lib_bar bar)
    -> lib_extends M lib' lib.
Proof.
  introv i.
  destruct bar as [bar cond]; simpl in *.
  unfold BarLibCond in cond.
Qed.

Lemma seq0_in_nat2nat {o} :
  @nmember o lib0 (mkc_choice_seq seq0) Nat2Nat.
Proof.
  unfold Nat2Nat, nmember, member, equality.
  eexists; dands.

  {
    apply CL_func.
    unfold per_func_ext.
    eexists; eexists.
    dands;[|apply eq_term_equals_refl].

    unfold type_family_ext.
    allrw <- @fold_mkc_fun.
    eexists; eexists; eexists; eexists; eexists; eexists.
    dands.

    {
      introv i.
      spcast.
      apply computes_to_valc_refl; eauto 2 with slow.
    }

    {
      introv i.
      spcast.
      apply computes_to_valc_refl; eauto 2 with slow.
    }

    {
      introv i.
      apply CL_nat.
      unfold per_nat_bar.
      dands.

      {
        assert (BarLib memNat lib') as bar.
        {
          exists [lib'].
          unfold BarLibCond.
          introv j.
          exists lib'; simpl; dands; tcsp.
          eauto 2 with slow.
        }
        exists bar.
        dands; auto.

        {
          introv j.
          spcast.
          apply computes_to_valc_refl; eauto 2 with slow.
        }

        {
          introv j.
          spcast.
          apply computes_to_valc_refl; eauto 2 with slow.
        }
      }

      {
        apply eq_term_equals_refl.
      }
    }

    {
      introv i; introv.
      autorewrite with slow.
      apply CL_nat.
      unfold per_nat_bar.
      dands.

      {
        assert (BarLib memNat lib') as bar.
        {
          exists [lib'].
          unfold BarLibCond.
          introv j.
          exists lib'; simpl; dands; tcsp.
          eauto 2 with slow.
        }
        exists bar.
        dands; auto.

        {
          introv j.
          spcast.
          apply computes_to_valc_refl; eauto 2 with slow.
        }

        {
          introv j.
          spcast.
          apply computes_to_valc_refl; eauto 2 with slow.
        }
      }

      {
        apply eq_term_equals_refl.
      }
    }
  }

  {
    unfold per_func_eq.
    introv i e.
    unfold equality_of_nat_bar in *; exrepnd.

    pose proof (bar_non_empty bar) as q; exrepnd.
    applydup e0 in q0; exrepnd; clear e0; spcast.

    match goal with
    | [ H : lib_extends _ _ _ |- _ ] =>
      dup H as safe; apply lib_extends_preserves_safe in safe;[|apply safe_library_lib0]
    end.

    pose proof (lib_extends_preserves_find_cs memNat lib0 lib' seq0 cs_entry0) as h.
    repeat (autodimp h hyp).
    exrepnd.

    pose proof (exists_bar_coq_law memNat lib' seq0 entry2 n const0) as q.
    repeat (autodimp q hyp);[].
    exrepnd.
    exists bar0.
    introv j.
    applydup q3 in j.
    unfold const0 in j0.
    exists 0.
    dands; spcast; eapply implies_compute_to_valc_apply_choice_seq; eauto;
      eapply (computes_to_valc_nat_if_lib_extends memNat); eauto.

  }

Qed.
