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

  Authors: Vincent Rahli

*)


Require Export nuprl.
Require Export nat_defs.
Require Export computation_choice_seq.
Require Export computation_lib_extends2.


Definition memNat {o} : @Mem o :=
  fun c => exists (n : nat), c = mkc_nat n.

(*Definition nmember {o} := @member o memNat.*)

Definition const_0 {o} : nat -> @CTerm o := fun n => mkc_nat 0.

Definition seq_0 : choice_sequence_name := "seq0".

Definition law_0 {o} : @ChoiceSeqRestriction o := csc_coq_law const_0.

Definition cs_entry_0 {o} : @ChoiceSeqEntry o := MkChoiceSeqEntry _ [] law_0.

Definition lib_entry_0 {o} : @library_entry o := lib_cs seq_0 cs_entry_0.

Definition lib_0 {o} : @library o := [lib_entry_0].

Definition Nat2Nat {o} : @CTerm o := mkc_fun mkc_Nat mkc_Nat.

Lemma iscvalue_mkc_Nat {o} : @iscvalue o mkc_Nat.
Proof.
  repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscvalue_mkc_Nat : slow.

Hint Rewrite @csubst_mk_cv : slow.

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

Lemma list_in_implies_select :
  forall {A} (a : A) l,
    List.In a l -> exists n, select n l = Some a.
Proof.
  induction l; introv i; simpl in *; tcsp.
  repndors; subst.
  - exists 0; simpl; auto.
  - apply IHl in i; exrepnd.
    exists (S n); simpl; auto.
Qed.

Lemma safe_library_entry_simple_choice_seq {o} :
  forall name, @safe_library_entry o (simple_choice_seq name).
Proof.
  introv; unfold safe_library_entry; simpl; auto.
Qed.
Hint Resolve safe_library_entry_simple_choice_seq : slow.

Lemma safe_library_lib0 {o} : @safe_library o lib_0.
Proof.
  introv i.
  unfold lib_0 in i; simpl in i; repndors; tcsp; subst.
  simpl; introv k; omega.
Qed.
Hint Resolve safe_library_lib0 : slow.

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

Definition extend_choice_seq_entry_following_coq_law_upto {o}
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

Definition extend_library_entry_following_coq_law_upto {o}
           (e    : @library_entry o)
           (name : choice_sequence_name)
           (n    : nat) : library_entry :=
  match e with
  | lib_cs name' x =>
    if choice_sequence_name_deq name name' then
      lib_cs name' (extend_choice_seq_entry_following_coq_law_upto x n)
    else e
  | _ => e
  end.

Fixpoint extend_library_following_coq_law_upto {o}
           (lib  : @library o)
           (name : choice_sequence_name)
           (n    : nat) : library :=
  match lib with
  | [] => []
  | entry :: entries =>
    (extend_library_entry_following_coq_law_upto entry name n)
      :: extend_library_following_coq_law_upto entries name n
  end.

Lemma choice_sequence_entry_extend_extend_choice_seq_entry_following_coq_law_upto {o} :
  forall (entry : @ChoiceSeqEntry o) n,
    choice_sequence_entry_extend
      (extend_choice_seq_entry_following_coq_law_upto entry n)
      entry.
Proof.
  introv; unfold choice_sequence_entry_extend; simpl.
  destruct entry as [vals restr]; simpl.
  destruct restr; simpl; dands; auto; eauto 2 with slow.
  eexists; eauto.
Qed.
Hint Resolve choice_sequence_entry_extend_extend_choice_seq_entry_following_coq_law_upto : slow.

Lemma entry_extends_extend_library_entry_following_coq_law_upto {o} :
  forall (entry : @library_entry o) name n,
    entry_extends (extend_library_entry_following_coq_law_upto entry name n) entry.
Proof.
  introv; destruct entry; simpl in *; tcsp.
  boolvar; subst; eauto 2 with slow.
  unfold entry_extends; dands; auto; eauto 2 with slow.
Qed.
Hint Resolve entry_extends_extend_library_entry_following_coq_law_upto : slow.

Lemma matching_entries_extend_library_entry_following_coq_law_upto {o} :
  forall (e a : @library_entry o) name n,
    matching_entries (extend_library_entry_following_coq_law_upto e name n) a
    -> matching_entries (extend_library_entry_following_coq_law_upto e name n) e.
Proof.
  introv h; unfold matching_entries, extend_library_entry_following_coq_law_upto in *.
  destruct e; simpl; eauto 2 with slow.
  - boolvar; subst; simpl in *; tcsp.
  - simpl in *.
    destruct a; simpl in *; tcsp.
    unfold same_opabs in *.
    eapply implies_matching_entry_sign_refl; eauto.
Qed.
Hint Resolve matching_entries_extend_library_entry_following_coq_law_upto : slow.

Lemma implies_entry_in_library_extends_extend_library_following_coq_law_upto {o} :
  forall entry (lib : @library o) name n,
    entry_in_library entry lib
    -> entry_in_library_extends entry (extend_library_following_coq_law_upto lib name n).
Proof.
  induction lib; introv h; simpl in *; tcsp.
  repndors; subst; tcsp; eauto 2 with slow.

  repnd.
  right; dands; auto.
  intro q; destruct h0.
  eapply matching_entries_trans;[eauto|]; eauto 3 with slow.
Qed.
Hint Resolve implies_entry_in_library_extends_extend_library_following_coq_law_upto : slow.

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

(*Lemma safe_library_cons_implies_tail {o} :
  forall e (lib : @library o),
    safe_library (e :: lib)
    -> safe_library lib.
Proof.
  introv h i.
  apply h; simpl; tcsp.
Qed.
Hint Resolve safe_library_cons_implies_tail : slow.*)

Lemma implies_matching_entries_extend_library_entry_following_coq_law_upto {o} :
  forall (e1 e2 : @library_entry o) name n,
    matching_entries e1 e2
    -> matching_entries
         (extend_library_entry_following_coq_law_upto e1 name n)
         (extend_library_entry_following_coq_law_upto e2 name n).
Proof.
  introv m.
  destruct e1, e2; simpl in *; boolvar; subst; tcsp.
Qed.
Hint Resolve implies_matching_entries_extend_library_entry_following_coq_law_upto : slow.

Lemma entry_in_library_extend_library_following_coq_law_upto_implies {o} :
  forall entry (lib : @library o) name n,
    entry_in_library entry (extend_library_following_coq_law_upto lib name n)
    ->
    exists e,
      entry_in_library e lib
      /\ entry = extend_library_entry_following_coq_law_upto e name n.
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.

  - exists a; dands; tcsp.

  - apply IHlib in i; exrepnd; subst.
    exists e; dands; tcsp.
    right; dands; auto.
    intro m; destruct i0; eauto 2 with slow.
Qed.

Lemma safe_library_entry_extend_library_entry_following_coq_law_upto {o} :
  forall (e : @library_entry o) name n,
    safe_library_entry e
    -> safe_library_entry (extend_library_entry_following_coq_law_upto e name n).
Proof.
  introv safe; destruct e; simpl in *; boolvar; subst; tcsp.
  destruct entry as [vals restr]; simpl in *.
  destruct restr; simpl in *; tcsp.

  introv j.
  allrw length_app; autorewrite with slow in *.
  destruct (lt_dec i (length vals)) as [d|d].

  - applydup safe in d.
    rewrite select_app_l; auto.

  - rewrite select_app_r; try omega.
    pose proof (Nat.le_exists_sub (length vals) i) as q.
    autodimp q hyp; try omega.
    exrepnd; subst.
    rewrite Nat.add_sub.
    rewrite le_plus_minus_r in j; try omega.
    rewrite select_follow_coq_low; auto; try omega.
Qed.
Hint Resolve safe_library_entry_extend_library_entry_following_coq_law_upto : slow.

Lemma implies_safe_library_extend_library_following_coq_law_upto {o} :
  forall (lib : @library o) name n,
    safe_library lib
    -> safe_library (extend_library_following_coq_law_upto lib name n).
Proof.
  introv safe i.
  apply entry_in_library_extend_library_following_coq_law_upto_implies in i.
  exrepnd; subst.
  apply safe in i1; eauto 2 with slow.
Qed.
Hint Resolve implies_safe_library_extend_library_following_coq_law_upto : slow.

Lemma subset_library_extend_library_following_coq_law_upto {o} :
  forall (lib : @library o) name n,
    subset_library lib (extend_library_following_coq_law_upto lib name n).
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; subst; simpl in *; tcsp.

  - eexists; dands;[left;reflexivity|]; eauto 2 with slow.

  - apply (IHlib name n) in i; exrepnd.
    exists entry2; dands; auto.
Qed.
Hint Resolve subset_library_extend_library_following_coq_law_upto : slow.

Lemma extend_library_following_coq_law_upto_extends {o} :
  forall name n (lib : @library o),
    lib_extends (extend_library_following_coq_law_upto lib name n) lib.
Proof.
  introv.
  split; auto; eauto 2 with slow;[].
  introv i; eauto 2 with slow.
Qed.
Hint Resolve extend_library_following_coq_law_upto_extends : slow.

Lemma restriction_extend_choice_seq_entry_following_coq_law_upto {o} :
  forall (entry : @ChoiceSeqEntry o) m,
    cse_restriction (extend_choice_seq_entry_following_coq_law_upto entry m)
    = cse_restriction entry.
Proof.
  introv; destruct entry as [vals restr]; simpl; auto.
  destruct restr; simpl in *; tcsp.
Qed.
Hint Rewrite @restriction_extend_choice_seq_entry_following_coq_law_upto : slow.

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

Lemma implies_inf_choice_sequence_entry_extend_extend_choice_seq_entry_following_coq_law_upto {o} :
  forall (entry1 : @InfChoiceSeqEntry o) entry2 m,
    safe_inf_choice_sequence_entry entry1
    -> inf_choice_sequence_entry_extend entry1 entry2
    -> inf_choice_sequence_entry_extend
         entry1
         (extend_choice_seq_entry_following_coq_law_upto entry2 m).
Proof.
  introv safe h; unfold inf_choice_sequence_entry_extend in *;
    repnd; simpl in *; dands; autorewrite with slow in *; auto.
  introv i.
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
    rewrite h0 in safe; simpl in safe; tcsp.

  - rewrite select_app_l in i; try omega; tcsp.
Qed.
Hint Resolve implies_inf_choice_sequence_entry_extend_extend_choice_seq_entry_following_coq_law_upto : slow.

Lemma implies_inf_entry_extends_extend_library_entry_following_coq_law_upto {o} :
  forall (inf_entry : @inf_library_entry o) entry name m,
    safe_inf_library_entry inf_entry
    -> inf_entry_extends inf_entry entry
    -> inf_entry_extends
         inf_entry
         (extend_library_entry_following_coq_law_upto entry name m).
Proof.
  introv safe h; destruct inf_entry; simpl in *; GC.

  - destruct entry; simpl in *; repnd; subst; tcsp.
    boolvar; subst; simpl in *; tcsp.
    dands; auto; eauto 2 with slow.

  - destruct entry; simpl in *; tcsp.
Qed.
Hint Resolve implies_inf_entry_extends_extend_library_entry_following_coq_law_upto : slow.

Lemma entry2name_extend_library_entry_following_coq_law_upto {o} :
  forall (entry : @library_entry o) name m,
    entry2name (extend_library_entry_following_coq_law_upto entry name m)
    = entry2name entry.
Proof.
  introv; destruct entry; simpl in *; boolvar; tcsp.
Qed.
Hint Rewrite @entry2name_extend_library_entry_following_coq_law_upto : slow.

Lemma inf_matching_entries_extend_library_entry_following_coq_law_upto_r_implies {o} :
  forall (inf_entry : @inf_library_entry o) entry name m,
    inf_matching_entries inf_entry (extend_library_entry_following_coq_law_upto entry name m)
    -> inf_matching_entries inf_entry entry.
Proof.
  introv h; unfold inf_matching_entries in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve inf_matching_entries_extend_library_entry_following_coq_law_upto_r_implies : slow.

(*Lemma implies_safe_inf_library {o} :
  forall (infLib : @inf_library o),
    safe_inf_library infLib
    -> safe_inf_library (shift_inf_lib infLib).
Proof.
  introv safe i.
  unfold shift_inf_lib in i.
  apply safe in i.
Qed.
Hint Resolve implies_safe_inf_library : slow.*)

Lemma same_names_preserves_inf_matching_entries {o} :
  forall (e1 e2 : @library_entry o) ie,
    entry2name e1 = entry2name e2
    -> inf_matching_entries ie e1
    -> inf_matching_entries ie e2.
Proof.
  introv h i.
  destruct ie, e1, e2; simpl in *; ginv; tcsp.
Qed.
Hint Resolve same_names_preserves_inf_matching_entries : slow.

Lemma inf_entry_extends_implies_entry_in_inf_library_extends_same_names {o} :
  forall n e a (infLib : @inf_library o),
    inf_entry_extends (infLib n) e
    -> entry2name e = entry2name a
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
Hint Resolve inf_entry_extends_implies_entry_in_inf_library_extends_same_names : slow.

Lemma inf_entry_extends_implies_entry_in_inf_library_extends_same_names_lt {o} :
  forall n k e a (infLib : @inf_library o),
    n < k
    -> inf_entry_extends (infLib n) e
    -> entry2name e = entry2name a
    -> (forall m : nat, m < n -> ~ inf_matching_entries (infLib m) a)
    -> entry_in_inf_library_extends e k infLib.
Proof.
  introv ltnk i m imp.
  eapply le_preserves_entry_in_inf_library_extends;
    [|eapply inf_entry_extends_implies_entry_in_inf_library_extends_same_names; eauto];
    try omega.
Qed.
Hint Resolve inf_entry_extends_implies_entry_in_inf_library_extends_same_names_lt : slow.

Lemma implies_entry_in_inf_library_extends_extend_library_entry_following_coq_law_upto {o} :
  forall n entry (infLib : @inf_library o) name m,
    safe_inf_library infLib
    -> entry_in_inf_library_extends entry n infLib
    -> entry_in_inf_library_extends (extend_library_entry_following_coq_law_upto entry name m) n infLib.
Proof.
  introv safe i.
  apply inf_library_extends_implies in i; exrepnd.
  eapply inf_entry_extends_implies_entry_in_inf_library_extends_same_names_lt;
    [| | |eauto]; eauto 3 with slow; autorewrite with slow in *; auto.

  apply implies_inf_entry_extends_extend_library_entry_following_coq_law_upto; auto.
  apply safe.
  apply implies_entry_in_inf_library.
  introv h.
  apply i0 in h.
  intro m'; destruct h; eauto 4 with slow.
Qed.
Hint Resolve implies_entry_in_inf_library_extends_extend_library_entry_following_coq_law_upto : slow.

(*Lemma implies_matching_entries_extend_library_entry_following_coq_law_upto {o} :
  forall (entry1 entry2 : @library_entry o) name n,
    matching_entries entry1 entry2
    -> matching_entries
         (extend_library_entry_following_coq_law_upto entry1 name n)
         (extend_library_entry_following_coq_law_upto entry2 name n).
Proof.
  introv h; destruct entry1, entry2; simpl in *; tcsp; boolvar;
    subst; unfold matching_entries; auto.
Qed.
Hint Resolve implies_matching_entries_extend_library_entry_following_coq_law_upto : slow.*)

Lemma matching_entries_extend_library_entry_following_coq_law_upto_implies {o} :
  forall (entry1 entry2 : @library_entry o) name n,
    matching_entries
      (extend_library_entry_following_coq_law_upto entry1 name n)
      (extend_library_entry_following_coq_law_upto entry2 name n)
    -> matching_entries entry1 entry2.
Proof.
  introv h; destruct entry1, entry2; simpl in *; tcsp; boolvar;
    subst; unfold matching_entries; auto.
Qed.
Hint Resolve matching_entries_extend_library_entry_following_coq_law_upto_implies : slow.

Lemma entry_in_library_extend_library_following_coq_law_upto_iff {o} :
  forall entry (lib : @library o) name n,
    entry_in_library entry (extend_library_following_coq_law_upto lib name n)
    <->
    exists entry',
      entry_in_library entry' lib
      /\ entry = extend_library_entry_following_coq_law_upto entry' name n.
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

Lemma in_library_extend_library_following_coq_law_upto_implies {o} :
  forall entry (lib : @library o) name n,
    List.In entry (extend_library_following_coq_law_upto lib name n)
    <->
    exists entry',
      List.In entry' lib
      /\ entry = extend_library_entry_following_coq_law_upto entry' name n.
Proof.
  induction lib; introv; split; intro h; simpl in *; tcsp.

  - repndors; repnd; subst; tcsp.

    + eexists; dands;[left;reflexivity|]; auto.

    + apply IHlib in h; exrepnd; subst.
      exists entry'; dands; tcsp.

  - exrepnd; repndors; repnd; subst; simpl in *; tcsp.

    right; dands; auto; eauto 2 with slow.
    apply IHlib.
    eexists; dands; eauto.
Qed.

Lemma implies_inf_lib_extends_extend_library_following_coq_law_upto {o} :
  forall (lib : @library o) name n (infLib : inf_library),
    safe_inf_library infLib
    -> inf_lib_extends infLib lib
    -> inf_lib_extends infLib (extend_library_following_coq_law_upto lib name n).
Proof.
  introv safe h.
  destruct h as [ext1 safe1 sub1].
  split; auto.

  {
    introv i.
    apply entry_in_library_extend_library_following_coq_law_upto_implies in i; exrepnd; subst.
    applydup ext1 in i1.
    exrepnd.
    exists n0.
    eauto 2 with slow.
  }

(*  {
    introv i.
    apply in_library_extend_library_following_coq_law_upto_implies in i; exrepnd; subst.
    apply sub1 in i1; exrepnd.
    exists n0; eauto 2 with slow.
  }*)
Qed.
Hint Resolve implies_inf_lib_extends_extend_library_following_coq_law_upto : slow.

Lemma BarLibBars_extend_library_following_coq_law_upto {o} :
  forall (lib : @library o) name n,
    safe_library lib
    -> BarLibBars (const_bar (extend_library_following_coq_law_upto lib name n)) lib.
Proof.
  introv safe i.
  unfold const_bar.
  eexists; dands; eauto; eauto 3 with slow.
Qed.
Hint Resolve BarLibBars_extend_library_following_coq_law_upto : slow.

Lemma BarLibExt_extend_library_following_coq_law_upto {o} :
  forall (lib : @library o) name n,
    BarLibExt (const_bar (extend_library_following_coq_law_upto lib name n)) lib.
Proof.
  introv b.
  unfold const_bar in b; simpl; subst.
  simpl in *; repndors; subst; tcsp; eauto 2 with slow.
Qed.
Hint Resolve BarLibExt_extend_library_following_coq_law_upto : slow.

Lemma find_cs_same_extend_library_following_coq_law_upto {o} :
  forall (lib : @library o) name n,
    find_cs (extend_library_following_coq_law_upto lib name n) name
    = match find_cs lib name with
      | Some entry => Some (extend_choice_seq_entry_following_coq_law_upto entry n)
      | None => None
      end.
Proof.
  induction lib; introv; simpl; auto.
  destruct a; simpl; tcsp;[].
  boolvar; subst; tcsp.
Qed.

Lemma exists_bar_coq_law {o} :
  forall (lib  : @library o)
         (name : choice_sequence_name)
         (e    : ChoiceSeqEntry)
         (n    : nat)
         (f    : nat -> CTerm),
    safe_library lib
    -> find_cs lib name = Some e
    -> entry2restriction e = csc_coq_law f
    ->
    exists (bar : BarLib lib),
    forall (lib' : library),
      bar_lib_bar bar lib'
      -> find_cs_value_at lib' name n = Some (f n).
Proof.
  introv safe find law.

  pose proof (safe (lib_cs name e)) as q; autodimp q hyp; eauto 2 with slow;[].

  destruct e as [vals restr]; simpl in *; subst.

  destruct (lt_dec n (length vals)) as [d|d].

  - exists (MkBarLib _ lib (const_bar lib) (BarLibBars_refl lib) (BarLibExt_refl lib)); simpl.
    introv b; repndors; subst; tcsp.
    unfold const_bar in b; subst; simpl.
    unfold find_cs_value_at.
    allrw; simpl in *.
    applydup q in d; clear q.
    allrw <-; apply find_value_of_cs_at_vals_as_select.

  - exists (MkBarLib
              _ lib
              (const_bar (extend_library_following_coq_law_upto lib name (S n)))
              (BarLibBars_extend_library_following_coq_law_upto lib name (S n) safe)
              (BarLibExt_extend_library_following_coq_law_upto lib name (S n))).
    simpl; introv b; repndors; subst; simpl in *; tcsp.
    unfold const_bar in b; subst; simpl.
    unfold find_cs_value_at.
    rewrite find_cs_same_extend_library_following_coq_law_upto; allrw.
    simpl.
    rewrite find_value_of_cs_at_vals_as_select.
    rewrite select_app_r; try omega;[].
    rewrite select_follow_coq_low_ite; boolvar; try omega.

    { rewrite Nat.sub_add; auto; try omega. }

    { remember (length vals) as lv; destruct lv; simpl in *; try omega. }
Qed.

Fixpoint map_in {A B} (l : list A) : (forall a : A, List.In a l -> B) -> list B :=
  match l with
    | [] => fun _ => []
    | x :: xs =>
      fun f =>
        f x (@or_introl (x = x) (List.In x xs) eq_refl)
          :: map_in xs (fun a i => f a (or_intror i))
  end.

Definition equality_of_nat_tt {o} lib (n m : @CTerm o) :=
  {k : nat
  & computes_to_valc lib n (mkc_nat k)
  # computes_to_valc lib m (mkc_nat k)}.

Definition reducek_pair {o} lib (t1 t2 : @NTerm o) (k : nat) (n : nat) :=
    reduces_in_atmost_k_steps lib t1 (mk_nat k) n
  # reduces_in_atmost_k_steps lib t2 (mk_nat k) n.

Definition equality_of_nat_p_2 {o} lib (n m : @NTerm o) :=
  {x : nat # nat , reducek_pair lib n m (fst x) (snd x)}.

Definition equality_of_nat_p_2_c {o} lib (n m : @CTerm o) :=
  equality_of_nat_p_2 lib (get_cterm n) (get_cterm m).

Lemma equality_of_nat_imp1 {o} :
  forall lib (n m : @CTerm o),
    equality_of_nat lib n m
    <-> equality_of_nat_p_2_c lib n m.
Proof.
  introv; split.

  - introv e.
    unfold equality_of_nat in e; exrepnd; spcast.
    allunfold @computes_to_valc; allsimpl.
    allunfold @computes_to_value; repnd.
    allunfold @reduces_to; exrepnd.
    allunfold @reduces_in_atmost_k_steps.
    Check no_change_after_value2.
    pose proof (no_change_after_value2 lib
                  (get_cterm n) k0 (mk_nat n0) e2 e1 (Peano.max k0 k)) as h1.
    autodimp h1 hyp; try (apply max_prop1).
    pose proof (no_change_after_value2 lib
                (get_cterm m) k (mk_nat n0) e4 e0 (Peano.max k0 k)) as h2.
    autodimp h2 hyp; try (apply max_prop2).
    exists ((n0,Peano.max k0 k)); simpl; sp.
    unfold reducek_pair; sp.

  - introv e.
    unfold equality_of_nat.
    unfold equality_of_nat_p_2_c, equality_of_nat_p_2, reducek_pair in e.
    exrepnd; allsimpl.
    exists x0; dands; spcast;
    unfold computes_to_valc, computes_to_value; simpl;
    dands; try (apply isvalue_mk_nat);
    exists x; auto.
Qed.

Inductive before_witness (P : nat -> nat -> Prop) (k : nat) : Prop :=
  | stop : forall (z n : nat), k = z + n -> P z n -> before_witness P k
  | next : before_witness P (S k) -> before_witness P k.

Lemma leS:
  forall n m : nat, n <= S m -> n <= m [+] n = S m.
Proof.
  introv; revert n.
  induction m; simpl; introv e.
  - destruct n; sp.
    destruct n; sp.
    provefalse.
    inversion e as [|x h].
    inversion h.
  - apply leb_correct in e.
    destruct n; allsimpl.
    + left; omega.
    + apply leb_complete in e.
      apply IHm in e; dorn e.
      left; omega.
      right; omega.
Qed.

Lemma P_search :
  forall (P : nat -> nat -> Prop)
         (dec : forall z n, P z n [+] !P z n)
         (k : nat),
    {x : nat # nat & P (fst x) (snd x)}
    [+]
    (forall z n : nat, k = (z + n)%nat -> ~ P z n).
Proof.
  intros P dec k.

  assert (forall k z,
            {x : nat # nat & P (fst x) (snd x)}
              [+]
              (forall n : nat, n <= k -> ~ P z n)) as hyp1.
  {
    clear k.
    introv.
    induction k.

    - pose proof (dec z 0) as h.
      dorn h.

      + left; exists (z,0); simpl; sp.

      + right; introv e.
        assert (n = 0) by omega; subst; simpl; sp.

    - dorn IHk.

      + left; auto.

      + pose proof (dec z (S k)) as h.
        dorn h.

        * left; exists (z,S k); simpl; sp.

        * right; introv e; simpl.
          apply leS in e.
          dorn e.
          { apply IHk in e; sp. }
          subst; sp.
  }

  assert (forall k n,
            {x : nat # nat & P (fst x) (snd x)}
              [+]
              (forall z : nat, z <= k -> ~ P z n)) as hyp2.
  {
    clear k.
    introv.
    induction k.

    - pose proof (dec 0 n) as h.
      dorn h.

      + left; exists (0,n); simpl; sp.

      + right; introv e.
        assert (z = 0) by omega; subst; simpl; sp.

    - dorn IHk.

      + left; auto.

      + pose proof (dec (S k) n) as h.
        dorn h.

        * left; exists (S k,n); simpl; sp.

        * right; introv e; simpl.
          apply leS in e.
          dorn e.
          { apply IHk in e; sp. }
          subst; sp.
  }

  assert ({x : nat # nat & P (fst x) (snd x)}
            [+]
            (forall z n : nat, z <= k -> n <= k -> ~ P z n)) as hyp.
  {
    induction k.

    - pose proof (dec 0 0) as h.
      dorn h.
      + left; exists (0,0); simpl; sp.
      + right; introv e1 e2.
        assert (z = 0) by omega; assert (n = 0) by omega; subst; simpl; sp.
    - dorn IHk.
      + left; auto.
      + pose proof (hyp1 (S k) (S k)) as h1.
        dorn h1.
        * left; auto.
        * pose proof (hyp2 (S k) (S k)) as h2.
          dorn h2.
          { left; auto. }
          right; introv e1 e2.
          apply leS in e1.
          apply leS in e2.
          dorn e1; dorn e2; subst.
          { apply IHk; auto. }
          { apply h2; auto. }
          { apply h1; auto. }
          { apply h1; sp. }
  }

  dorn hyp.
  { left; auto. }
  right.
  introv e; subst.
  apply hyp; omega.
Qed.

Definition inv_before_witness :
  forall (P : nat -> nat -> Prop) (k : nat),
    before_witness P k
    -> (forall z n : nat, k = z + n -> ~ P z n)
    -> before_witness P (S k) :=
  fun P k b =>
    match b
          in before_witness _ _
          return (forall z n, k = z + n -> ~ P z n)
                 -> before_witness P (S k) with
      | stop _ _ z n e p => fun f => match f z n e p with end
      | next _ _ b => fun _ => b
    end.

Fixpoint linear_search
      (P : nat -> nat -> Prop)
      (dec : forall z n, P z n [+] !P z n)
      (k : nat)
      (b : before_witness P k) : {x : nat # nat & P (fst x) (snd x)} :=
  match P_search P dec k with
    | inl p => p
    | inr a => linear_search P dec (S k) (inv_before_witness P k b a)
  end.

Lemma deq_nterm_nat {p} :
  forall (t : @NTerm p) z, {t = mk_nat z} + {t <> mk_nat z}.
Proof.
  introv.
  nterm_ind1 t as [v1|f1 ind|o1 lbt1 Hind] Case; intros.

  - Case "vterm".
    right; intro k; inversion k.

  - Case "sterm".
    right; intro k; inversion k.

  - Case "oterm".
    destruct o1; try (complete (right; intro k; inversion k)).
    destruct c; try (complete (right; intro k; inversion k)).
    destruct lbt1; try (complete (right; intro k; inversion k)).
    assert ({Z.of_nat z < z0} + {Z.of_nat z > z0} + {Z.of_nat z = z0})%Z as h by (apply Z_dec).
    destruct h as [ h | h ]; subst.
    + destruct h as [ h | h ]; sp; right; sp; inversion H; omega.
    + left; sp.
Qed.

Lemma compute_step_dec {o} :
  forall lib (t : @NTerm o),
    {u : NTerm $ compute_step lib t = csuccess u}
    [+]
    !{u : NTerm $ compute_step lib t = csuccess u}.
Proof.
  introv.
  remember (compute_step lib t); destruct c.
  - left.
    exists n; sp.
  - right; intro k; exrepnd; inversion k0.
Qed.

Lemma reduces_in_atmost_k_steps_nat_dec {o} :
  forall lib k (t : @NTerm o) z,
    reduces_in_atmost_k_steps lib t (mk_nat z) k
    [+]
    !(reduces_in_atmost_k_steps lib t (mk_nat z) k).
Proof.
  induction k; introv.

  - rw @reduces_in_atmost_k_steps_0.
    pose proof (deq_nterm_nat t z) as h; sp.

  - rw @reduces_in_atmost_k_steps_S.
    pose proof (compute_step_dec lib t) as h.
    dorn h.

    + exrepnd.
      pose proof (IHk u z) as j.
      dorn j.

      * left.
        exists u; sp.

      * right.
        intro c; exrepnd.
        rw h0 in c1; inversion c1; subst; sp.

    + right; intro j; exrepnd.
      apply h.
      exists u; sp.
Qed.

Lemma reducek_pair_dec {o} :
  forall lib (t1 t2 : @NTerm o) z n,
    reducek_pair lib t1 t2 z n [+] !(reducek_pair lib t1 t2 z n).
Proof.
  introv.
  unfold reducek_pair.
  pose proof (reduces_in_atmost_k_steps_nat_dec lib n t1 z) as h1.
  pose proof (reduces_in_atmost_k_steps_nat_dec lib n t2 z) as h2.
  dorn h1; dorn h2.
  - left; sp.
  - right; sp.
  - right; sp.
  - right; sp.
Qed.

Fixpoint O_witness
         (P : nat -> nat -> Prop)
         (k : nat) : before_witness P k -> before_witness P 0 :=
  match k return (before_witness P k -> before_witness P 0) with
    | 0 => fun b => b
    | S n => fun b => O_witness P n (next P n b)
  end.

Definition constructive_indefinite_ground_description_nat {o}
           lib (t1 t2 : @CTerm o) :
  equality_of_nat_p_2_c lib t1 t2
  -> {x : nat # nat & reducek_pair lib (get_cterm t1) (get_cterm t2) (fst x) (snd x)}.
Proof.
  introv pex.
  apply linear_search with (k := 0).
  apply reducek_pair_dec; auto.
  unfold equality_of_nat_p_2_c, equality_of_nat_p_2 in pex; auto.
  exrepnd; allsimpl.
  apply O_witness with (k := x0 + x).
  apply stop with (z := x0) (n := x); auto.
Qed.

Lemma equality_of_nat_imp_tt {o} :
  forall {lib} {n m : @CTerm o},
    equality_of_nat lib n m
    -> equality_of_nat_tt lib n m.
Proof.
  introv e.
  apply equality_of_nat_imp1 in e.
  apply constructive_indefinite_ground_description_nat in e; auto.
  exrepnd; allsimpl.
  unfold equality_of_nat_tt.
  unfold reducek_pair in e0; repnd.
  exists x0; dands; spcast;
  unfold computes_to_valc, computes_to_value; simpl;
  dands; try (apply isvalue_mk_integer);
  exists x; auto.
Qed.

Lemma in_map_in :
  forall {A B}
         (l : list A)
         (f : forall a : A, List.In a l -> B)
         (b : B),
    List.In b (map_in l f) <-> {a : A , {i : List.In a l , b = f a i}}.
Proof.
  induction l; introv; simpl; auto.
  - split; sp.
  - split; intro k; exrepnd; subst; repndors; subst; allsimpl; tcsp.
    + eexists; eexists; eauto.
    + apply IHl in k; exrepnd; subst.
      eexists; eexists; eauto.
    + right; apply IHl.
      eexists; eexists; eauto.
Defined.

Definition extend_bar_nat_following_coq_law_upto {o} {lib} {a} {a'}
           (bar  : @BarLib o lib)
           (safe : safe_library lib)
           (F    : all_in_bar bar (fun lib => equality_of_nat lib a a'))
  : BarLib lib.
Proof.
  exists (fun (lib' : library) =>
            exists (lib0 : library) (b : bar_lib_bar bar lib0),
              lib' = extend_library_following_coq_law_upto
                       lib0
                       seq_0
                       (S (projT1 (equality_of_nat_imp_tt (F lib0 b lib0 (lib_extends_refl lib0)))))).

  - introv ext'; simpl.
    destruct bar as [bar cond ext]; simpl in *.
    pose proof (cond infLib ext') as q.

    exrepnd.

    exists (extend_library_following_coq_law_upto
              lib' seq_0
              (S (projT1 (equality_of_nat_imp_tt (F lib' q1 lib' (lib_extends_refl lib')))))).
    dands; eauto 3 with slow.

  - introv b; exrepnd; subst.
    remember (equality_of_nat_imp_tt (F lib0 b lib0 _)) as z; symmetry in Heqz.
    unfold equality_of_nat_tt in z.
    exrepnd.
    eauto 3 with slow.
Defined.

Lemma bar_preserves_safe {o} :
  forall {lib} (bar : @BarLib o lib) (lib' : library) (b : bar_lib_bar bar lib'),
    safe_library lib
    -> safe_library lib'.
Proof.
  introv b safe.
  apply in_bar_implies_extends in b; auto.
  eauto 2 with slow.
Qed.

Lemma extend_library_follow_coq_law_upto_implies_find_cs {o} :
  forall (lib1 lib2 : @library o) name k vals f,
    safe_library lib2
    -> find_cs lib2 name = Some (MkChoiceSeqEntry _ vals (csc_coq_law f))
    -> lib_extends lib1 (extend_library_following_coq_law_upto lib2 name (S k))
    -> find_cs_value_at lib1 name k = Some (f k).
Proof.
  introv safe i ext.

  pose proof (find_cs_same_extend_library_following_coq_law_upto
                lib2 name (S k)) as ext2.
  rewrite i in ext2.

  dup ext as ext1.
  eapply lib_extends_preserves_find_cs in ext;[|eauto].

  remember (S k) as m.
  hide_hyp Heqm.

  simpl in *.
  exrepnd.
  unfold find_cs_value_at; allrw.

  rewrite find_value_of_cs_at_vals_as_select.
  destruct entry2 as [vals2 restr2]; simpl in *.
  destruct restr2; simpl in *; ginv.

  unfold choice_sequence_vals_extend in *; exrepnd; subst; simpl in *.

  destruct (lt_dec k (length vals)) as [d|d].

  + rewrite select_app_l; auto; allrw length_app; try omega;[].
    rewrite select_app_l; auto; allrw length_app; try omega;[].
    apply find_cs_some_implies_entry_in_library in i.
    apply safe in i; simpl in i.
    apply i in d; simpl in d; auto.

  + pose proof (Nat.le_exists_sub (length vals) k) as q.
    autodimp q hyp; try omega.
    exrepnd; subst.

    show_hyp Heqm.
    subst.
    rewrite <- plus_Sn_m.
    rewrite Nat.add_sub.

    rewrite select_app_l; allrw length_app; allrw @length_follow_coq_law; try omega;[].
    rewrite select_app_r; try omega;[].

    rewrite Nat.add_sub.
    rewrite select_follow_coq_low; auto; try omega.
Qed.



Definition equality_of_nat_bar_lib_per_fam {o}
           (lib : @library o)
           (eqa : lib-per(lib,o)) : lib-per-fam(lib,eqa,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) (a b : CTerm) (p : eqa lib' x a b) => equality_of_nat_bar lib').
  introv x z; tcsp.
Defined.

Definition equality_of_nat_lib_per {o}
           (lib : @library o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => equality_of_nat lib').
  introv x y; tcsp.
Defined.

(*Lemma all_in_bar_ext_intersect_bars_trivial_left_implies {o} :
  forall {lib} (bar : @BarLib o lib) F,
    all_in_bar_ext (intersect_bars (trivial_bar lib) bar) F
    -> all_in_bar_ext bar F.
Proof.
  introv alla; repeat introv.
  pose proof (alla lib') as alla. ; autodimp alla hyp.
  simpl.
  exists lib' lib'; dands; eauto 3 with slow.
Qed.*)

Hint Resolve computes_to_valc_refl : slow.

(*

  We prove here that the lawlike choice sequence seq_0 is in the type [nat -> nat]
  even without having filled any of its values

 *)

Lemma seq0_in_nat2nat {o} :
  @member o lib_0 (mkc_choice_seq seq_0) Nat2Nat.
Proof.
  unfold Nat2Nat, member, equality.
  eexists; dands.

  {
    apply CL_func.
    unfold per_func_ext.
    exists (@equality_of_nat_bar_lib_per o lib_0)
           (equality_of_nat_bar_lib_per_fam
              lib_0
              (@equality_of_nat_bar_lib_per o lib_0)).
    dands;[|apply eq_term_equals_refl].

    unfold type_family_ext.
    allrw <- @fold_mkc_fun.
    eexists; eexists; eexists; eexists; eexists; eexists.
    dands.

    {
      try (introv i).
      spcast.
      apply computes_to_valc_refl; eauto 2 with slow.
    }

    {
      try (introv i).
      spcast.
      apply computes_to_valc_refl; eauto 2 with slow.
    }

    {
      repeat introv.
      apply CL_nat.
      unfold per_nat; dands; spcast; eauto 3 with slow.
    }

    {
      try (introv i); introv.
      autorewrite with slow.
      apply CL_nat.
      unfold per_nat.
      dands; spcast; eauto 3 with slow.
    }
  }

  {
    unfold per_func_eq.
    try (exists (@trivial_bar o lib_0)); simpl.
    introv xt1 xt2 x en; simpl in *.

    unfold equality_of_nat_bar in *; exrepnd.

    applydup @lib_extends_preserves_safe in xt2 as safe; eauto 3 with slow.

    exists (extend_bar_nat_following_coq_law_upto bar safe en0).
    introv b z; simpl in *.
    exrepnd; subst.

    remember (equality_of_nat_imp_tt (en0 _ b lib0 _)) as w; symmetry in Heqw.
    unfold equality_of_nat_tt in w; exrepnd.
    simpl in *.

    first[assert (lib_extends lib'2 lib0) as ext1 by eauto 2 with slow
         |assert (lib_extends lib'1 lib0) as ext1 by eauto 2 with slow
         |assert (lib_extends lib'0 lib0) as ext1 by eauto 2 with slow].
    first[assert (lib_extends lib'2 lib_0) as ext2 by eauto 4 with slow
         |assert (lib_extends lib'1 lib_0) as ext2 by eauto 4 with slow
         |assert (lib_extends lib'0 lib_0) as ext2 by eauto 4 with slow].
    assert (lib_extends lib0 lib_0) as ext3 by eauto 4 with slow.

    clear Heqw.

    first[eapply (computes_to_valc_nat_if_lib_extends lib'2 lib0) in w1; eauto 2 with slow
         |eapply (computes_to_valc_nat_if_lib_extends lib'1 lib0) in w1; eauto 2 with slow
         |eapply (computes_to_valc_nat_if_lib_extends lib'0 lib0) in w1; eauto 2 with slow].
    first[eapply (computes_to_valc_nat_if_lib_extends lib'2 lib0) in w0; eauto 2 with slow
         |eapply (computes_to_valc_nat_if_lib_extends lib'1 lib0) in w0; eauto 2 with slow
         |eapply (computes_to_valc_nat_if_lib_extends lib'0 lib0) in w0; eauto 2 with slow].

    pose proof (bar_preserves_safe bar lib0) as safe1.
    repeat (autodimp safe1 hyp);[].

    applydup @lib_extends_safe in ext1 as safe2; auto;[].

    eapply (lib_extends_preserves_find_cs _ _ seq_0) in ext3;[|simpl; eauto].
    exrepnd.
    simpl in *.
    unfold choice_sequence_vals_extend in ext0; exrepnd; simpl in *; subst.
    destruct entry2 as [vals2 restr2]; simpl in *.
    unfold law_0 in ext4.
    destruct restr2; simpl in *; ginv.

    dup z as ee.
    eapply extend_library_follow_coq_law_upto_implies_find_cs in ee;
      [|auto|allrw; eauto].
    unfold const_0 in ee.

    exists 0; simpl.
    dands; spcast;
      eapply implies_compute_to_valc_apply_choice_seq; eauto; simpl;
        try (complete (eapply (computes_to_valc_nat_if_lib_extends memNat); try (exact ext1); eauto 2 with slow)).
  }
Qed.



Definition seq_1 : choice_sequence_name := "seq1".

Lemma memNat0 {o} : @memNat o (mkc_nat 0).
Proof.
  eexists; eauto.
Qed.
Hint Resolve memNat0 : slow.

Definition law_1 {o} : @ChoiceSeqRestriction o := csc_type (mkc_nat 0) memNat memNat0.

Definition cs_entry_1 {o} : @ChoiceSeqEntry o := MkChoiceSeqEntry _ [] law_1.

Definition lib_entry_1 {o} : @library_entry o := lib_cs seq_1 cs_entry_1.

Definition lib_1 {o} : @library o := [lib_entry_1].

Lemma safe_library_lib1 {o} : @safe_library o lib_1.
Proof.
  introv i.
  unfold lib_1 in i; simpl in i; repndors; tcsp; subst.
  simpl; dands; auto; tcsp; eauto 2 with slow.
Qed.
Hint Resolve safe_library_lib1 : slow.

Fixpoint ntimes {T} (n : nat) (t : T) : list T :=
  match n with
  | 0 => []
  | S n => t :: ntimes n t
  end.

Definition extend_choice_seq_entry_lawless_upto {o}
           (e1 : @ChoiceSeqEntry o)
           (e2 : @ChoiceSeqEntry o)
           (n  : nat) : Prop :=
  match e1, e2 with
  | MkChoiceSeqEntry _ vals1 (csc_type d1 M1 Md1),
    MkChoiceSeqEntry _ vals2 (csc_type d2 M2 Md2) =>
    exists (p : M1 = M2) (q : d1 = d2),
    eq_rect d1 (fun d => M2 d) (eq_rect M1 (fun M => M d1) Md1 M2 p) d2 q = Md2
    /\ exists vals,
        vals1 = vals2 ++ vals
        /\ length vals = n - length vals2
        /\ forall v, List.In v vals -> M1 v (*exists k, v = mkc_nat k*)
  | _, _ => e1 = e2
  end.

Definition extend_library_entry_lawless_upto {o}
           (e1   : @library_entry o)
           (e2   : @library_entry o)
           (name : choice_sequence_name)
           (n    : nat) : Prop :=
  match e1, e2 with
  | lib_cs name1 x1, lib_cs name2 x2 =>
    if choice_sequence_name_deq name name1 then
      if choice_sequence_name_deq name name2 then
        extend_choice_seq_entry_lawless_upto x1 x2 n
      else False
    else e1 = e2
  | _, _ => e1 = e2
  end.

(* [lib1] extend [lib2] *)
Fixpoint extend_library_lawless_upto {o}
         (lib1 : @library o)
         (lib2 : @library o)
         (name : choice_sequence_name)
         (n    : nat) : Prop :=
  match lib1, lib2 with
  | [], [] => True
  | entry1 :: entries1, entry2 :: entries2 =>
    extend_library_entry_lawless_upto entry1 entry2 name n
    /\ extend_library_lawless_upto entries1 entries2 name n
  | _, _ => False
  end.

Fixpoint canonicalize_library {o} (lib : @library o) : library :=
  match lib with
  | [] => []
  | entry :: entries =>
    entry :: filter (diff_entry_names entry) (canonicalize_library entries)
  end.

Fixpoint is_canonical_library {o} (lib : @library o) : Prop :=
  match lib with
  | [] => True
  | entry :: entries =>
    is_canonical_library entries
    /\ forall e, List.In e entries -> ~matching_entries e entry
  end.

Lemma implies_is_canonical_library_filter {o} :
  forall f (lib : @library o),
    is_canonical_library lib
    -> is_canonical_library (filter f lib).
Proof.
  induction lib; introv h; simpl in *; tcsp.
  repnd.
  autodimp IHlib hyp.
  destruct (f a); simpl; dands; auto.
  introv i.
  apply filter_In in i; repnd.
  apply h; auto.
Qed.
Hint Resolve implies_is_canonical_library_filter : slow.

Lemma is_canonical_canonicalize_library {o} :
  forall (lib : @library o),
    is_canonical_library (canonicalize_library lib).
Proof.
  induction lib; simpl in *; auto.
  dands; eauto 2 with slow.
  introv i h.
  apply filter_In in i; repnd.
  apply matching_entries_sym in h.
  apply matching_entries_iff_diff_entry_names_false in h.
  rewrite i in h; ginv.
Qed.
Hint Resolve is_canonical_canonicalize_library : slow.

Fixpoint bsplit {A} (f : A -> bool) (l : list A) : list A * list A :=
  match l with
  | [] => ([],[])
  | x :: xs =>
    let (l1,l2) := bsplit f xs in
    if f x then (x :: l1, l2) else (l1, x :: l2)
  end.

Fixpoint can_lib {o} (lib : @library o) : library * library :=
  match lib with
  | [] => ([], [])
  | entry :: entries =>
    let (l1, l2) := can_lib entries in
    let (l1a,l1b) := bsplit (diff_entry_names entry) l1 in
    (entry :: l1a, l1b ++ l2)
  end.

Definition canLib {o} (lib : @library o) :=
  let (l1,l2) := can_lib lib in l1 ++ l2.

Inductive sublist {A} : list A -> list A -> Prop :=
| sublist_nil : forall l, sublist [] l
| sublist_cons_in : forall a l1 l2, sublist l1 l2 -> sublist (a :: l1) (a :: l2)
| sublist_cons_out : forall a l1 l2, sublist l1 l2 -> sublist l1 (a :: l2).
Hint Constructors sublist.

Lemma bsplit_sublist :
  forall {A} f (l : list A) l1 l2,
    bsplit f l = (l1,l2)
    -> sublist l1 l /\ sublist l2 l.
Proof.
  induction l; introv e; simpl in *; ginv; dands; auto.

  - remember (bsplit f l) as b; repnd.
    destruct (f a); ginv; tcsp.

    + pose proof (IHl b0 l2) as q; autodimp q hyp; clear IHl; repnd; auto.

    + pose proof (IHl l1 b) as q; autodimp q hyp; clear IHl; repnd; auto.

  - remember (bsplit f l) as b; repnd.
    destruct (f a); ginv; tcsp.

    + pose proof (IHl b0 l2) as q; autodimp q hyp; clear IHl; repnd; auto.

    + pose proof (IHl l1 b) as q; autodimp q hyp; clear IHl; repnd; auto.
Qed.

Lemma sublist_preserves_list_in :
  forall {A} l2 (l1 : list A) a,
    sublist l1 l2 -> List.In a l1 -> List.In a l2.
Proof.
  induction l2; introv sl i; simpl in *; tcsp.

  - inversion sl; subst; simpl in *; tcsp.

  - inversion sl; subst; simpl in *; tcsp; clear sl; repndors; subst; tcsp;
      right; eapply IHl2; eauto.
Qed.

Lemma sublist_preserves_is_canonical_library {o} :
  forall lib2 (lib1 : @library o),
    sublist lib1 lib2
    -> is_canonical_library lib2
    -> is_canonical_library lib1.
Proof.
  induction lib2; introv sl isc; simpl in *; tcsp.

  - inversion sl; subst; simpl in *; tcsp.

  - inversion sl as [|? ? ? sl'|xxx]; clear sl; subst; simpl in *; tcsp.
    repnd.
    applydup IHlib2 in sl'; auto;[].
    dands; auto.

    introv i m.
    eapply sublist_preserves_list_in in sl';[|eauto].
    apply isc in sl'; tcsp.
Qed.
Hint Resolve sublist_preserves_is_canonical_library : slow.

Lemma bsplit_prop :
  forall {A} f (l : list A) l1 l2,
    bsplit f l = (l1,l2)
    -> (forall a, List.In a l1 -> f a = true)
       /\ (forall a, List.In a l2 -> f a = false).
Proof.
  induction l; introv h; simpl in *; ginv; simpl in *; tcsp.
  remember (bsplit f l) as b; symmetry in Heqb; repnd.
  pose proof (IHl b0 b) as q; clear IHl; autodimp q hyp; repnd.
  remember (f a) as z; symmetry in Heqz; destruct z; ginv; simpl in *; tcsp;
    dands; introv i; repndors; subst; tcsp.
Qed.

Lemma fst_can_lib_is_canonical {o} :
  forall (lib : @library o),
    is_canonical_library (fst (can_lib lib)).
Proof.
  induction lib; simpl in *; auto.
  remember (can_lib lib) as clib; repnd; simpl in *.
  remember (bsplit (diff_entry_names a) clib0) as blib; repnd; simpl in *.
  symmetry in Heqblib.

  applydup @bsplit_sublist in Heqblib; repnd.
  applydup @bsplit_prop in Heqblib; repnd.

  dands; eauto 2 with slow.

  introv i m.

  applydup Heqblib3 in i.
  apply matching_entries_iff_diff_entry_names_false in m.
  rewrite diff_entry_names_sym in m.
  rewrite m in i0; ginv.
Qed.
Hint Resolve fst_can_lib_is_canonical : slow.

Lemma can_lib_implies_is_canonical {o} :
  forall (lib : @library o) lib1 lib2,
    can_lib lib = (lib1,lib2)
    -> is_canonical_library lib1.
Proof.
  introv can.
  pose proof (fst_can_lib_is_canonical lib) as h.
  rewrite can in h; simpl in can; auto.
Qed.
Hint Resolve can_lib_implies_is_canonical : slow.

Lemma entry_in_library_middle_implies {o} :
  forall (entry : @library_entry o) e x l1 l2,
    matching_entries e x
    -> ~ matching_entries entry e
    -> entry_in_library entry (l1 ++ e :: l2)
    -> entry_in_library entry (l1 ++ l2).
Proof.
  induction l1; introv m d i; simpl in *; repndors; repnd; subst; tcsp.
  destruct d.
  eapply implies_matching_entries_refl; eauto.
Qed.

Lemma entry_in_library_middle_implies2 {o} :
  forall (entry : @library_entry o) e x l1 l2,
    matching_entries e x
    -> ~ matching_entries entry e
    -> entry_in_library entry (l1 ++ l2)
    -> entry_in_library entry (l1 ++ e :: l2).
Proof.
  induction l1; introv m d i; simpl in *; repndors; repnd; subst; tcsp.
Qed.

Lemma bsplit_diff_entry_names_preserves_entry_in_library {o} :
  forall entry (e : @library_entry o) w1 w2 b1 b2,
    ~ matching_entries entry e
    -> bsplit (diff_entry_names e) w1 = (b1, b2)
    -> entry_in_library entry (b1 ++ b2 ++ w2)
    -> entry_in_library entry (w1 ++ w2).
Proof.
  induction w1; simpl in *; introv d bs i; ginv; simpl in *; auto.
  remember (bsplit (diff_entry_names e) w1) as bd; symmetry in Heqbd; repnd.
  remember (diff_entry_names e a) as z; symmetry in Heqz; destruct z; ginv;
    simpl in *; repndors; repnd; tcsp.

  - right; dands; tcsp.
    eapply IHw1; eauto.

  - apply matching_entries_iff_diff_entry_names_false in Heqz.
    right; dands; tcsp.

    + intro u; destruct d.
      eapply matching_entries_trans;[eauto|]; eauto 2 with slow.

    + eapply IHw1; eauto.
      eapply entry_in_library_middle_implies;[| |eauto];
        [apply matching_entries_sym;eauto|].
      introv w; destruct d.
      eapply matching_entries_trans; eauto.
      apply matching_entries_sym; auto.
Qed.

Lemma bsplit_diff_entry_names_preserves_entry_in_library2 {o} :
  forall entry (e : @library_entry o) w1 w2 b1 b2,
    ~ matching_entries entry e
    -> bsplit (diff_entry_names e) w1 = (b1, b2)
    -> entry_in_library entry (w1 ++ w2)
    -> entry_in_library entry (b1 ++ b2 ++ w2).
Proof.
  induction w1; simpl in *; introv d bs i; ginv; simpl in *; auto.
  remember (bsplit (diff_entry_names e) w1) as bd; symmetry in Heqbd; repnd.
  remember (diff_entry_names e a) as z; symmetry in Heqz; destruct z; ginv;
    simpl in *; repndors; repnd; subst; tcsp.

  - apply matching_entries_iff_diff_entry_names_false in Heqz.
    apply matching_entries_sym in Heqz; tcsp.

  - apply matching_entries_iff_diff_entry_names_false in Heqz.
    pose proof (IHw1 w2 b1 bd) as q; repeat (autodimp q hyp).
    eapply entry_in_library_middle_implies2; eauto.
    apply matching_entries_sym; eauto.
Qed.

Lemma can_lib_preserves_entry_in_library {o} :
  forall entry (lib : @library o) lib1 lib2,
    can_lib lib = (lib1, lib2)
    -> entry_in_library entry (lib1 ++ lib2)
    -> entry_in_library entry lib.
Proof.
  induction lib; introv h i; simpl in *; ginv.

  - inversion h; subst; simpl in *; GC; tcsp.

  - remember (can_lib lib) as w; repnd; symmetry in Heqw.
    rename w0 into w1; rename w into w2.
    remember (bsplit (diff_entry_names a) w1) as b; symmetry in Heqb; repnd.
    rename b0 into b1; rename b into b2.
    inversion h; subst; clear h.
    simpl in *.
    repndors; repnd; tcsp.
    pose proof (IHlib w1 w2) as q; autodimp q hyp; clear IHlib.
    right; dands; auto.
    apply q; clear q.

    eapply bsplit_diff_entry_names_preserves_entry_in_library;eauto.
Qed.
Hint Resolve can_lib_preserves_entry_in_library : slow.

Lemma can_lib_preserves_entry_in_library2 {o} :
  forall entry (lib : @library o) lib1 lib2,
    can_lib lib = (lib1, lib2)
    -> entry_in_library entry lib
    -> entry_in_library entry (lib1 ++ lib2).
Proof.
  induction lib; introv h i; simpl in *; ginv.

  - inversion h; subst; simpl in *; GC; tcsp.

  - remember (can_lib lib) as w; repnd; symmetry in Heqw.
    rename w0 into w1; rename w into w2.
    remember (bsplit (diff_entry_names a) w1) as b; symmetry in Heqb; repnd.
    rename b0 into b1; rename b into b2.
    inversion h; subst; clear h.
    simpl in *.
    repndors; repnd; tcsp.
    pose proof (IHlib w1 w2) as q; autodimp q hyp; clear IHlib.
    autodimp q hyp.
    right; dands; auto.

    eapply bsplit_diff_entry_names_preserves_entry_in_library2;eauto.
Qed.
Hint Resolve can_lib_preserves_entry_in_library2 : slow.

Lemma bsplit_preserves_list_in :
  forall {A} f x (l : list A) l1 l2,
    bsplit f l = (l1, l2)
    -> List.In x l
    -> List.In x l1 \/ List.In x l2.
Proof.
  induction l; introv h i; simpl in *; ginv; tcsp.
  remember (bsplit f l) as b; symmetry in Heqb; repnd.
  destruct (f a); ginv; simpl in *; tcsp.

  - repndors; tcsp.
    eapply IHl in i;[|eauto]; tcsp.

  - repndors; tcsp.
    eapply IHl in i;[|eauto]; tcsp.
Qed.

Lemma bsplit_preserves_list_in_l :
  forall {A} f x (l : list A) l1 l2,
    bsplit f l = (l1, l2)
    -> List.In x l1
    -> List.In x l.
Proof.
  induction l; introv h i; simpl in *; ginv; tcsp.
  remember (bsplit f l) as b; symmetry in Heqb; repnd.
  destruct (f a); ginv; simpl in *; tcsp.

  - repndors; tcsp.
    eapply IHl in i;[|eauto]; tcsp.

  - repndors; tcsp.
    eapply IHl in i;[|eauto]; tcsp.
Qed.

Lemma bsplit_preserves_list_in_r :
  forall {A} f x (l : list A) l1 l2,
    bsplit f l = (l1, l2)
    -> List.In x l2
    -> List.In x l.
Proof.
  induction l; introv h i; simpl in *; ginv; tcsp.
  remember (bsplit f l) as b; symmetry in Heqb; repnd.
  destruct (f a); ginv; simpl in *; tcsp.

  - repndors; tcsp.
    eapply IHl in i;[|eauto]; tcsp.

  - repndors; tcsp.
    eapply IHl in i;[|eauto]; tcsp.
Qed.

Lemma can_lib_preserves_list_in {o} :
  forall entry (lib : @library o) lib1 lib2,
    can_lib lib = (lib1, lib2)
    -> List.In entry lib
    -> List.In entry (lib1 ++ lib2).
Proof.
  induction lib; introv can i; simpl in *; ginv; tcsp.
  remember (can_lib lib) as c; symmetry in Heqc; repnd.
  remember (bsplit (diff_entry_names a) c0) as b; symmetry in Heqb; repnd.
  inversion can; subst; clear can; simpl in *.
  repndors; tcsp.
  right.
  pose proof (IHlib c0 c) as q; repeat (autodimp q hyp).
  allrw List.in_app_iff; repndors; tcsp.
  eapply bsplit_preserves_list_in in Heqb;[|eauto].
  tcsp.
Qed.
Hint Resolve can_lib_preserves_list_in : slow.

Lemma can_lib_preserves_list_in2 {o} :
  forall entry (lib : @library o) lib1 lib2,
    can_lib lib = (lib1, lib2)
    -> List.In entry (lib1 ++ lib2)
    -> List.In entry lib.
Proof.
  induction lib; introv can i; simpl in *; ginv; tcsp.

  { inversion can; subst; simpl in *; tcsp. }

  remember (can_lib lib) as c; symmetry in Heqc; repnd.
  remember (bsplit (diff_entry_names a) c0) as b; symmetry in Heqb; repnd.
  inversion can; subst; clear can; simpl in *.
  repndors; tcsp.
  right.
  pose proof (IHlib c0 c) as q; repeat (autodimp q hyp).
  allrw List.in_app_iff; repndors; tcsp.

  - eapply bsplit_preserves_list_in_l in Heqb;[|eauto]; tcsp.

  - eapply bsplit_preserves_list_in_r in Heqb;[|eauto]; tcsp.
Qed.
Hint Resolve can_lib_preserves_list_in2 : slow.

Lemma can_lib_preserves_safe_library {o} :
  forall (lib : @library o) lib1 lib2,
    can_lib lib = (lib1, lib2)
    -> safe_library (lib1 ++ lib2)
    -> safe_library lib.
Proof.
  introv can safe i.
  apply safe; eauto 2 with slow.
Qed.
Hint Resolve can_lib_preserves_safe_library : slow.

Lemma can_lib_preserves_safe_library2 {o} :
  forall (lib : @library o) lib1 lib2,
    can_lib lib = (lib1, lib2)
    -> safe_library lib
    -> safe_library (lib1 ++ lib2).
Proof.
  introv can safe i.
  apply safe; eauto 2 with slow.
Qed.
Hint Resolve can_lib_preserves_safe_library2 : slow.

Lemma implies_entry_in_library_app_if_left {o} :
  forall entry (lib1 lib2 : @library o),
    entry_in_library entry lib1
    -> entry_in_library entry (lib1 ++ lib2).
Proof.
  induction lib1; introv h; simpl in *; tcsp.
Qed.
Hint Resolve implies_entry_in_library_app_if_left : slow.

Lemma can_lib_preserves_safe_library_left {o} :
  forall (lib : @library o) lib1 lib2,
    can_lib lib = (lib1, lib2)
    -> safe_library lib
    -> safe_library lib1.
Proof.
  introv can safe i.
  apply safe; eauto 3 with slow.
Qed.
Hint Resolve can_lib_preserves_safe_library_left : slow.

(*Lemma can_lib_preserves_safe_library_right {o} :
  forall (lib : @library o) lib1 lib2,
    can_lib lib = (lib1, lib2)
    -> safe_library lib
    -> safe_library lib2.
Proof.
  introv can safe i.
  apply safe.
  eapply can_lib_preserves_entry_in_library;[eauto|].
Qed.
Hint Resolve can_lib_preserves_safe_library_right : slow.*)

Lemma can_lib_preserves_lib_extends {o} :
  forall (lib : @library o) lib1 lib2 lib',
    can_lib lib = (lib1, lib2)
    -> lib_extends lib' (lib1 ++ lib2)
    -> lib_extends lib' lib.
Proof.
  introv can ext.
  destruct ext as [ext safe sub].
  split; eauto 2 with slow.

  - introv i; apply ext; eauto 2 with slow.

  - introv safe'; apply safe; eauto 2 with slow.

  - introv i; apply sub; eauto 2 with slow.
Qed.

Lemma can_lib_preserves_inf_lib_extends {o} :
  forall (infLib : @inf_library o) lib lib1 lib2,
    can_lib lib = (lib1, lib2)
    -> inf_lib_extends infLib lib
    -> inf_lib_extends infLib (lib1 ++ lib2).
Proof.
  introv h i.
  destruct i as [ext safe].
  split.

  - introv i.
    dup i as j; eapply can_lib_preserves_entry_in_library in j;[|eauto]; tcsp.

  - introv safe'; apply safe.
    eapply can_lib_preserves_safe_library; eauto.
Qed.

Lemma inf_lib_extends_cons_implies {o} :
  forall (infLib : @inf_library o) entry lib,
    safe_library_entry entry
    -> inf_lib_extends infLib (entry :: lib)
    -> (forall e, List.In e lib -> ~ matching_entries e entry)
    -> inf_lib_extends infLib lib.
Proof.
  introv safee ext imp.
  destruct ext as [ext safe]; simpl in *.
  split.

  - introv i.
    apply ext; right; dands; auto.
    apply imp; eauto 2 with slow.

  - introv safe'.
    apply safe.
    introv i; simpl in *; repndors; subst; tcsp.
Qed.

Lemma extend_choice_seq_entry_lawless_upto_implies_choice_sequence_entry_extend {o} :
  forall (entry1 entry2 : @ChoiceSeqEntry o) n,
    extend_choice_seq_entry_lawless_upto entry1 entry2 n
    -> choice_sequence_entry_extend entry1 entry2.
Proof.
  destruct entry1 as [vals1 restr1], entry2 as [vals2 restr2]; introv h; simpl in *.
  destruct restr1; ginv; unfold choice_sequence_entry_extend; simpl; tcsp; dands; tcsp;
    eauto 2 with slow.

  - destruct restr2; ginv; exrepnd; subst; auto.

  - destruct restr2; ginv; exrepnd; subst; eauto 2 with slow.
    unfold choice_sequence_vals_extend.
    eexists; eauto.
Qed.
Hint Resolve extend_choice_seq_entry_lawless_upto_implies_choice_sequence_entry_extend : slow.

Lemma extend_library_entry_lawless_upto_implies_entry_extends {o} :
  forall (entry1 entry2 : @library_entry o) name n,
    extend_library_entry_lawless_upto entry1 entry2 name n
    -> entry_extends entry1 entry2.
Proof.
  introv e; destruct entry1, entry2; simpl in *; boolvar;
    subst; tcsp; subst; tcsp; dands; auto; ginv; auto; eauto 2 with slow.
Qed.
Hint Resolve extend_library_entry_lawless_upto_implies_entry_extends : slow.

Definition memNat_restriction {o} (restr : @ChoiceSeqRestriction o) : Prop :=
  match restr with
  | csc_no => True
  | csc_type d M Md => forall x, M x <-> memNat x
  | csc_coq_law f => True
  end.

Definition has_memNat_restriction {o} (e : @library_entry o) name : Prop :=
  match e with
  | lib_cs name' x =>
    if choice_sequence_name_deq name name' then
      memNat_restriction (cse_restriction x)
    else True
  | _ => True
  end.

Fixpoint lib_has_memNat_restriction {o} (lib : @library o) name : Prop :=
  match lib with
  | [] => True
  | e :: es => has_memNat_restriction e name /\ lib_has_memNat_restriction es name
  end.

Lemma extend_library_entry_lawless_upto_preserves_safe_library {o} :
  forall (entry1 entry2 : @library_entry o) name n,
    extend_library_entry_lawless_upto entry1 entry2 name n
    -> safe_library_entry entry2
    -> safe_library_entry entry1.
Proof.
  introv ext safe; destruct entry1, entry2; simpl in *; tcsp;
    boolvar; repeat subst; tcsp; ginv; tcsp.

  destruct entry as [vals1 restr1], entry0 as [vals2 restr2]; simpl in *.
  destruct restr1; simpl in *; ginv; simpl in *; tcsp.

  destruct restr2; simpl in *; ginv; exrepnd; subst; tcsp; dands; auto.
  introv i; apply List.in_app_iff in i; repndors; tcsp.
Qed.
Hint Resolve extend_library_entry_lawless_upto_preserves_safe_library : slow.

Lemma extend_library_lawless_upto_preserves_entry_in_library_extends {o} :
  forall entry (lib1 lib2 : @library o) name n,
    extend_library_lawless_upto lib1 lib2 name n
    -> entry_in_library entry lib2
    -> entry_in_library_extends entry lib1.
Proof.
  induction lib1; introv ext i; simpl in *.

  - destruct lib2; tcsp.

  - destruct lib2; tcsp.
    repnd.
    simpl in *.

    repndors; repnd; subst; tcsp.

    + applydup @extend_library_entry_lawless_upto_implies_entry_extends in ext0; tcsp.

    + applydup @extend_library_entry_lawless_upto_implies_entry_extends in ext0; tcsp.
      right; dands; tcsp;[|eapply IHlib1; eauto].
      introv m.
      eapply entry_extends_preserves_matching_entries_left in ext1;
        [|apply matching_entries_sym;eauto].
      apply matching_entries_sym in ext1; tcsp.
Qed.
Hint Resolve extend_library_lawless_upto_preserves_entry_in_library_extends : slow.

Lemma extend_library_lawless_upto_preserves_lib_extends_entries {o} :
  forall (lib1 lib2 : @library o) name n,
    extend_library_lawless_upto lib1 lib2 name n
    -> lib_extends_entries lib1 lib2.
Proof.
  introv ext i; eauto 2 with slow.
Qed.
Hint Resolve extend_library_lawless_upto_preserves_lib_extends_entries : slow.

Lemma extend_library_entry_lawless_upto_preserves_matching_entries_lr {o} :
  forall (e1 e2 e : @library_entry o) name n,
    extend_library_entry_lawless_upto e1 e2 name n
    -> matching_entries e1 e
    -> matching_entries e2 e.
Proof.
  introv ext m; destruct e1, e2, e; simpl in *; boolvar; repeat (subst; tcsp); ginv.
Qed.
Hint Resolve extend_library_entry_lawless_upto_preserves_matching_entries_lr : slow.

Lemma extend_library_entry_lawless_upto_preserves_matching_entries_rl {o} :
  forall (e1 e2 e : @library_entry o) name n,
    extend_library_entry_lawless_upto e1 e2 name n
    -> matching_entries e2 e
    -> matching_entries e1 e.
Proof.
  introv ext m; destruct e1, e2, e; simpl in *; boolvar; repeat (subst; tcsp); ginv.
Qed.
Hint Resolve extend_library_entry_lawless_upto_preserves_matching_entries_rl : slow.

Lemma extend_library_lawless_upto_implies {o} :
  forall (lib1 lib2 : @library o) name n entry,
    extend_library_lawless_upto lib1 lib2 name n
    -> entry_in_library entry lib1
    ->
    exists e,
      entry_in_library e lib2
      /\ extend_library_entry_lawless_upto entry e name n.
Proof.
  induction lib1; introv ext i; simpl in *; tcsp.
  destruct lib2; tcsp.
  repnd.
  repndors; repnd; subst; simpl in *; tcsp.

  - exists l; dands; tcsp.

  - eapply IHlib1 in ext;[|eauto].
    exrepnd.
    exists e; dands; tcsp.
    right; dands; auto.
    introv m; destruct i0.
    eauto 5 with slow.
Qed.

Lemma extend_library_lawless_upto_preserves_safe_library {o} :
  forall (lib1 lib2 : @library o) name n,
    extend_library_lawless_upto lib1 lib2 name n
    -> safe_library lib2
    -> safe_library lib1.
Proof.
  introv ext safe i.
  eapply extend_library_lawless_upto_implies in ext;[|eauto].
  exrepnd.
  apply safe in ext1; eauto 2 with slow.
Qed.
Hint Resolve extend_library_lawless_upto_preserves_safe_library : slow.

Lemma extend_library_lawless_upto_implies_subset_library {o} :
  forall (lib1 lib2 : @library o) name n,
    extend_library_lawless_upto lib1 lib2 name n
    -> subset_library lib2 lib1.
Proof.
  induction lib1; introv ext i; simpl in *; destruct lib2; simpl in *; tcsp.
  repnd.
  applydup IHlib1 in ext; clear ext.
  repndors; subst; tcsp.

  - exists a; dands; tcsp; eauto 2 with slow.

  - applydup ext1 in i; exrepnd.
    exists entry2; dands; tcsp.
Qed.
Hint Resolve extend_library_lawless_upto_implies_subset_library : slow.

Lemma extend_library_lawless_upto_implies_lib_extends {o} :
  forall (lib1 lib2 : @library o) name n,
    extend_library_lawless_upto lib1 lib2 name n
    -> lib_extends lib1 lib2.
Proof.
  introv ext.
  split; eauto 2 with slow.
Qed.
Hint Resolve extend_library_lawless_upto_implies_lib_extends : slow.

Definition shift_inf_choice_seq_vals {o} (iseq : @InfChoiceSeqVals o) : InfChoiceSeqVals :=
  fun n => iseq (S n).

Fixpoint shift_inf_choice_seq_vals_ntimes {o}
         (iseq : @InfChoiceSeqVals o)
         (n    : nat) : InfChoiceSeqVals :=
  match n with
  | 0 => iseq
  | S n => shift_inf_choice_seq_vals_ntimes (shift_inf_choice_seq_vals iseq) n
  end.

Fixpoint inf_choice_seq_vals2choice_seq_vals {o}
         (iseq : @InfChoiceSeqVals o)
         (n    : nat) : ChoiceSeqVals :=
  match n with
  | 0 => []
  | S n => iseq 0 :: inf_choice_seq_vals2choice_seq_vals (shift_inf_choice_seq_vals iseq) n
  end.

Lemma inf_choice_seq_vals2choice_seq_vals_length_eq {o} :
  forall (vals : ChoiceSeqVals) (ivals : @InfChoiceSeqVals o),
    (forall n v, select n vals = Some v -> ivals n = v)
    -> inf_choice_seq_vals2choice_seq_vals ivals (length vals) = vals.
Proof.
  induction vals; introv imp; simpl in *; auto.
  rewrite (imp 0 a); simpl; auto.
  f_equal; tcsp.
  apply IHvals.
  introv e.
  compute; tcsp.
Qed.

Lemma inf_choice_seq_vals2choice_seq_vals_shift {o} :
  forall (vals : ChoiceSeqVals) (ivals : @InfChoiceSeqVals o) k,
    (forall n v, select n vals = Some v -> ivals n = v)
    -> inf_choice_seq_vals2choice_seq_vals ivals (Init.Nat.max (length vals) k)
       = vals
           ++
           inf_choice_seq_vals2choice_seq_vals
           (shift_inf_choice_seq_vals_ntimes ivals (length vals))
           (k - length vals).
Proof.
  induction vals; introv imp; simpl; autorewrite with num; auto.
  destruct k; simpl in *; autorewrite with slow.

  - rewrite (imp 0 a); simpl; auto.
    f_equal; tcsp.
    apply inf_choice_seq_vals2choice_seq_vals_length_eq.
    introv e.
    compute; tcsp.

  - rewrite (imp 0 a); simpl; auto.
    f_equal; tcsp.
    apply IHvals.
    introv e.
    compute; tcsp.
Qed.

Lemma length_inf_choice_seq_vals2choice_seq_vals {o} :
  forall k (iseq : @InfChoiceSeqVals o),
    length (inf_choice_seq_vals2choice_seq_vals iseq k) = k.
Proof.
  induction k; introv; simpl; auto.
Qed.
Hint Rewrite @length_inf_choice_seq_vals2choice_seq_vals : slow.

Lemma list_in_inf_choice_seq_vals2choice_seq_vals_implies {o} :
  forall v k (iseq : @InfChoiceSeqVals o),
    List.In v (inf_choice_seq_vals2choice_seq_vals iseq k)
    -> exists n, n < k /\ v = iseq n.
Proof.
  induction k; introv i; simpl in *; tcsp.
  repndors; subst; tcsp.

  - exists 0; dands; tcsp; try omega.

  - apply IHk in i; exrepnd; subst; clear IHk.
    exists (S n); simpl; dands; tcsp; try omega.
Qed.

Lemma shift_inf_choice_seq_vals_ntimes_app {o} :
  forall n k (iseq : @InfChoiceSeqVals o),
    shift_inf_choice_seq_vals_ntimes iseq n k = iseq (n + k).
Proof.
  induction n; introv; simpl; auto.
  rewrite IHn; clear IHn; simpl; auto.
Qed.
Hint Rewrite @shift_inf_choice_seq_vals_ntimes_app : slow.

Lemma inf_choice_sequence_vals_extend_inf_choice_seq_vals2choice_seq_vals {o} :
  forall k (iseq : @InfChoiceSeqVals o),
    inf_choice_sequence_vals_extend
      iseq
      (inf_choice_seq_vals2choice_seq_vals iseq k).
Proof.
  introv i.
  revert iseq v k i.
  induction n; introv h; simpl in *; destruct k; simpl in *; ginv; auto.
  apply IHn in h; auto.
Qed.
Hint Resolve inf_choice_sequence_vals_extend_inf_choice_seq_vals2choice_seq_vals : slow.

Lemma select_inf_choice_seq_vals2choice_seq_vals {o} :
  forall n k (iseq : @InfChoiceSeqVals o),
    select n (inf_choice_seq_vals2choice_seq_vals iseq k) =
    if lt_dec n k then Some (iseq n) else None.
Proof.
  induction n; introv; simpl; destruct k; simpl; auto.
  rewrite IHn.
  unfold shift_inf_choice_seq_vals; boolvar; try omega; auto.
Qed.

Lemma entry_extends_preserves_inf_matching_entries {o} :
  forall (entry1 entry2 : @library_entry o) infl,
    entry_extends entry1 entry2
    -> inf_matching_entries infl entry1
    -> inf_matching_entries infl entry2.
Proof.
  introv ext m.
  destruct entry1, entry2, infl; unfold inf_matching_entries in *;
    simpl in *; repnd; subst; tcsp; ginv.
  inversion ext; subst; auto.
Qed.
Hint Resolve entry_extends_preserves_inf_matching_entries : slow.

Lemma entry_in_inf_library_extends_implies_extend_library_entry_lawless_upto {o} :
  forall n (infLib : @inf_library o) entry name k,
    safe_inf_library infLib
    -> entry_in_inf_library_extends entry n infLib
    ->
    exists entry',
      extend_library_entry_lawless_upto entry' entry name k
      /\ entry_in_inf_library_extends entry' n infLib.
Proof.
  introv safe i.
  applydup @inf_library_extends_implies in i.
  exrepnd.

  remember (infLib k0) as infentry.
  destruct infentry, entry; simpl in *; tcsp; repnd; subst;
    [|exists (lib_abs opabs0 vars0 rhs0 correct0); simpl; dands; auto].

  destruct (choice_sequence_name_deq name name1) as [d|d]; subst;
    [|exists (lib_cs name1 entry); simpl; boolvar; subst; tcsp];[].

  destruct entry as [vals restr].
  destruct restr;
    [ exists (lib_cs name1 (MkChoiceSeqEntry _ vals csc_no)); simpl; boolvar; subst; tcsp
    |
    | exists (lib_cs name1 (MkChoiceSeqEntry _ vals (csc_coq_law f))); simpl; boolvar; subst; tcsp];[].

  destruct entry0 as [ivals irestr].
  unfold inf_choice_sequence_entry_extend in i2; simpl in *; repnd; subst.

  unfold inf_choice_sequence_vals_extend in i2.

  exists (lib_cs
            name1
            (MkChoiceSeqEntry
               _
               (inf_choice_seq_vals2choice_seq_vals
                  ivals
                  (Peano.max (length vals) k))
                   (csc_type d typ typd))).
  simpl; boolvar; subst; tcsp; GC.

  dands; tcsp.

  - exists (eq_refl : typ = typ) (eq_refl : d = d); simpl; dands; auto.
    exists (inf_choice_seq_vals2choice_seq_vals (shift_inf_choice_seq_vals_ntimes ivals (length vals)) (k - length vals)).
    dands; auto; autorewrite with slow; auto.

    { apply inf_choice_seq_vals2choice_seq_vals_shift; auto. }

    { introv j.
      apply list_in_inf_choice_seq_vals2choice_seq_vals_implies in j.
      exrepnd; subst; autorewrite with slow.
      pose proof (safe (infLib k0)) as h.

      autodimp h hyp.
      {
        apply implies_entry_in_inf_library.
        rewrite <- Heqinfentry; simpl.
        eauto 2 with slow.
      }

      rewrite <- Heqinfentry in h; simpl in h; repnd.
      pose proof (h (length vals + n0)) as w; clear h; auto. }

  - eapply inf_entry_extends_implies_entry_in_inf_library_extends_same_names_lt;
      simpl; eauto; simpl; auto.
    rewrite <- Heqinfentry; simpl; dands; auto.
    unfold inf_choice_sequence_entry_extend; simpl; dands; auto.
    introv h.
    rewrite select_inf_choice_seq_vals2choice_seq_vals in h; boolvar; ginv.
Qed.

(*Lemma exists_extend_library_lawless_upto_following_infinite_can {o} :
  forall lib (infLib : @inf_library o) name n,
    safe_library lib
    -> is_canonical_library lib
    -> inf_lib_extends infLib lib
    ->
    exists lib',
      extend_library_lawless_upto lib' lib name n
      /\ inf_lib_extends infLib lib'.
Proof.
  induction lib; introv safeL can ext; simpl in *; GC.

  - exists ([] : @library o); simpl; dands; eauto 2 with slow.

  - repnd.
    apply safe_library_cons_iff in safeL; repnd.
    applydup @inf_lib_extends_cons_implies in ext; auto;[].
    destruct ext as [ext safe sub]; simpl in *.
    autodimp safe hyp;[apply safe_library_cons_iff;tcsp|];[].
    pose proof (ext a) as q; autodimp q hyp; exrepnd; clear ext.

    pose proof (IHlib infLib name n) as q; repeat (autodimp q hyp).
    exrepnd.

    pose proof (entry_in_inf_library_extends_implies_extend_library_entry_lawless_upto n0 infLib a name n) as h.
    repeat (autodimp h hyp).
    exrepnd.
    exists (entry' :: lib').
    simpl; dands; auto.

    constructor; tcsp.
    introv j; simpl in *; repndors; repnd; subst; tcsp.

    + exists n0; auto.

    + destruct q1 as [ext1 safe1].
      apply ext1; auto.
Qed.*)

(*Lemma implies_safe_library_app {o} :
  forall (lib1 lib2 : @library o),
    safe_library lib1
    -> safe_library lib2
    -> safe_library (lib1 ++ lib2).
Proof.
  introv safe1 safe2 i; allrw List.in_app_iff; tcsp.
Qed.
Hint Resolve implies_safe_library_app : slow.*)

(*Lemma inf_lib_extends_app_implies_left {o} :
  forall (infLib : @inf_library o) lib1 lib2,
    safe_library lib2
    -> inf_lib_extends infLib (lib1 ++ lib2)
    -> inf_lib_extends infLib lib1.
Proof.
  introv safe2 ext.
  destruct ext as [ext safe].
  split.

  - introv i; apply ext; eauto 2 with slow.

  - introv safe'; apply safe; eauto 2 with slow.
Qed.*)

Lemma length_ntimes :
  forall {A} (d : A) n, length (ntimes n d) = n.
Proof.
  induction n; simpl; tcsp.
Qed.
Hint Rewrite @length_ntimes : slow.

Lemma in_ntimes_implies :
  forall {A} (d : A) n x, List.In x (ntimes n d) -> x = d.
Proof.
  induction n; simpl; tcsp.
Qed.

Lemma exists_extend_library_entry_lawless_upto_default {o} :
  forall name n (entry : @library_entry o),
  exists entry',
    extend_library_entry_lawless_upto entry' entry name n.
Proof.
  introv; destruct entry;
    [|exists (lib_abs opabs vars rhs correct); simpl; auto];[].

  destruct (choice_sequence_name_deq name name0) as [dn|dn]; subst;
    [|exists (lib_cs name0 entry); simpl; boolvar; subst; tcsp];[].

  destruct entry as [vals restr].

  destruct restr;
    [ exists (lib_cs name0 (MkChoiceSeqEntry _ vals csc_no)); simpl; boolvar; subst; tcsp
    |
    | exists (lib_cs name0 (MkChoiceSeqEntry _ vals (csc_coq_law f))); simpl; boolvar; subst; tcsp];[].

  exists (lib_cs
            name0
            (MkChoiceSeqEntry
               _
               (vals ++ ntimes (n - length vals) d)
               (csc_type d typ typd))).
  simpl; boolvar; subst; tcsp; GC.
  dands; auto.
  exists (eq_refl : typ = typ) (eq_refl : d = d).
  dands; eauto; autorewrite with slow; auto;[].

  simpl in *; repnd.
  eexists; dands; eauto; autorewrite with slow; auto;[].
  introv i; apply in_ntimes_implies in i; subst; auto.
Qed.

(*Lemma exists_extend_library_lawless_upto_default {o} :
  forall name n (lib : @library o),
    safe_library lib
    ->
    exists lib',
      extend_library_lawless_upto lib' lib name n.
Proof.
  induction lib; introv safe; simpl in *; GC.

  - exists ([] : @library o); simpl; auto.

  - allrw @safe_library_cons_iff; repnd.

    repeat (autodimp IHlib hyp).
    exrepnd; simpl.

    pose proof (exists_extend_library_entry_lawless_upto_default name n a) as h.
    repeat (autodimp h hyp).
    exrepnd.
    exists (entry' :: lib').
    simpl; dands; auto.
Qed.*)

Lemma can_lib_nil_l_implies {o} :
  forall (lib : @library o) lib2,
    can_lib lib = ([], lib2) -> lib = [].
Proof.
  destruct lib as [|entry lib]; introv can; simpl in *; auto.
  remember (can_lib lib) as c; symmetry in Heqc; destruct c as [c1 c2].
  remember (bsplit (diff_entry_names entry) c1) as b; symmetry in Heqb; destruct b as [b1 b2].
  ginv.
Qed.

Lemma can_lib_cons_l_implies {o} :
  forall (lib : @library o) entry lib1 lib2,
    can_lib lib = (entry :: lib1, lib2) ->
    exists lib' l1 l2 k,
      lib = entry :: lib'
      /\ can_lib lib' = (l1,l2)
      /\ bsplit (diff_entry_names entry) l1 = (lib1,k)
      /\ lib2 = k ++ l2.
Proof.
  destruct lib as [|entry lib]; introv can; simpl in *; auto; ginv.

  remember (can_lib lib) as c; symmetry in Heqc; destruct c as [c1 c2].
  remember (bsplit (diff_entry_names entry) c1) as b; symmetry in Heqb; destruct b as [b1 b2].
  inversion can; subst; clear can.

  exists lib c1 c2 b2; tcsp.
Qed.

Lemma extend_library_entry_lawless_upto_preserves_safe_library_entry {o} :
  forall (entry1 entry2 : @library_entry o) name n,
    extend_library_entry_lawless_upto entry1 entry2 name n
    -> safe_library_entry entry2
    -> safe_library_entry entry1.
Proof.
  introv ext safe.
  destruct entry1, entry2; simpl; auto;
    unfold extend_library_entry_lawless_upto in ext; ginv;[].
  simpl in *.
  boolvar; repeat subst; tcsp; ginv; tcsp;[].
  destruct entry as [vals1 restr1], entry0 as [vals2 restr2]; simpl in *.
  destruct restr1; simpl in *; ginv; tcsp;[].
  destruct restr2; simpl in *; ginv; tcsp;[].
  exrepnd; subst; dands; auto.
  introv i; apply List.in_app_iff in i; repndors; tcsp.
Qed.
Hint Resolve extend_library_entry_lawless_upto_preserves_safe_library_entry : slow.

Lemma extend_library_entry_lawless_upto_preserves_matching_entries {o} :
  forall (entry entry1 entry2 : @library_entry o) name n,
    extend_library_entry_lawless_upto entry1 entry2 name n
    -> matching_entries entry entry1
    -> matching_entries entry entry2.
Proof.
  introv ext m; destruct entry1, entry2; simpl in *; ginv; boolvar; simpl in *;
    ginv; subst; simpl in *; subst; tcsp.
Qed.
Hint Resolve extend_library_entry_lawless_upto_preserves_matching_entries : slow.

Lemma in_extend_library_lawless_upto_implies {o} :
  forall (lib1 lib2 : @library o) name n entry,
    extend_library_lawless_upto lib2 lib1 name n
    -> List.In entry lib2
    -> exists entry',
        List.In entry' lib1
        /\ extend_library_entry_lawless_upto entry entry' name n.
Proof.
  induction lib1; introv ext i; simpl in *; destruct lib2; simpl in *; tcsp.
  repnd.
  repndors; subst; tcsp.

  - exists a; dands; tcsp.

  - eapply IHlib1 in ext;[|eauto].
    exrepnd.
    exists entry'; dands; tcsp.
Qed.

(* [lib1] is shadowed by [lib2] *)
Definition shadowed_library {o} (lib1 lib2 : @library o) : Prop :=
  forall entry,
    List.In entry lib1
    -> exists entry', List.In entry' lib2 /\ matching_entries entry entry'.

Lemma can_lib_left_prop {o} :
  forall (lib : @library o) lib1 lib2,
    can_lib lib = (lib1, lib2)
    -> shadowed_library lib2 lib1.
Proof.
  induction lib; introv can i; simpl in *.

  - inversion can; subst; simpl in *; tcsp.

  - remember (can_lib lib) as c; symmetry in Heqc; destruct c as [c1 c2].
    remember (bsplit (diff_entry_names a) c1) as b; symmetry in Heqb; destruct b as [b1 b2].
    inversion can; subst; clear can.
    apply List.in_app_iff in i; repndors; tcsp.

    + applydup @bsplit_prop in Heqb; repnd.
      applydup Heqb0 in i.
      exists a; simpl; dands; tcsp.
      apply matching_entries_iff_diff_entry_names_false in i0.
      apply matching_entries_sym; auto.

    + pose proof (IHlib c1 c2) as q; autodimp q hyp; clear IHlib.
      applydup q in i; clear q.
      exrepnd.

      dup Heqb as s; eapply bsplit_preserves_list_in in s;[|eauto].
      repndors.

      * exists entry'; simpl; tcsp.

      * apply bsplit_prop in Heqb; repnd.
        applydup Heqb in s.
        apply matching_entries_iff_diff_entry_names_false in s0.
        exists a; simpl; dands; tcsp.
        eapply matching_entries_trans;[eauto|].
        apply matching_entries_sym; auto.
Qed.

Lemma implies_extend_library_lawless_upto_app {o} :
  forall name n (lib1 lib1' lib2 lib2' : @library o),
    extend_library_lawless_upto lib1' lib1 name n
    -> extend_library_lawless_upto lib2' lib2 name n
    -> extend_library_lawless_upto (lib1' ++ lib2') (lib1 ++ lib2) name n.
Proof.
  induction lib1; introv ext1 ext2; destruct lib1'; simpl in *; tcsp.
Qed.
Hint Resolve implies_extend_library_lawless_upto_app : slow.

Lemma shadowed_library_nil_r_implies {o} :
  forall (lib : @library o),
    shadowed_library lib [] -> lib = [].
Proof.
  introv sh; destruct lib as [|entry lib]; auto.
  pose proof (sh entry) as q; clear sh; simpl in q; autodimp q hyp.
  exrepnd; tcsp.
Qed.

Lemma shadowed_library_nil_l {o} :
  forall (lib : @library o), shadowed_library [] lib.
Proof.
  introv i; simpl in *; tcsp.
Qed.
Hint Resolve shadowed_library_nil_l : slow.

Lemma shadowed_library_cons_l_iff {o} :
  forall (entry : @library_entry o) lib1 lib2,
    shadowed_library (entry :: lib1) lib2
    <->
    (
      (exists entry', List.In entry' lib2 /\ matching_entries entry entry')
      /\
      shadowed_library lib1 lib2
    ).
Proof.
  introv; split; intro h.

  - pose proof (h entry) as q; simpl in q; autodimp q hyp; dands; tcsp.
    introv i; apply h; simpl; tcsp.

  - exrepnd.
    introv i; simpl in i; repndors; subst; tcsp.
    eexists; eauto.
Qed.

Lemma in_right_extend_library_lawless_upto_implies {o} :
  forall (lib1 lib2 : @library o) name n entry,
    extend_library_lawless_upto lib2 lib1 name n
    -> List.In entry lib1
    -> exists entry',
        List.In entry' lib2
        /\ extend_library_entry_lawless_upto entry' entry name n.
Proof.
  induction lib1; introv ext i; simpl in *; destruct lib2; simpl in *; tcsp.
  repnd.
  repndors; subst; tcsp.

  - exists l; dands; tcsp.

  - eapply IHlib1 in ext;[|eauto].
    exrepnd.
    exists entry'; dands; tcsp.
Qed.

Lemma extend_library_entry_lawless_upto_preserves_matching_entries2 {o} :
  forall (entry entry1 entry2 : @library_entry o) name n,
    extend_library_entry_lawless_upto entry1 entry2 name n
    -> matching_entries entry entry2
    -> matching_entries entry entry1.
Proof.
  introv ext m; destruct entry1, entry2; simpl in *; ginv; boolvar; simpl in *;
    ginv; subst; simpl in *; subst; tcsp.
Qed.
Hint Resolve extend_library_entry_lawless_upto_preserves_matching_entries2 : slow.

Definition extend_library_lawless_upto_preserves_shadowed {o} :
  forall name n (lib2 lib2' lib1 lib1' : @library o),
    shadowed_library lib2 lib1
    -> extend_library_lawless_upto lib1' lib1 name n
    -> extend_library_lawless_upto lib2' lib2 name n
    -> shadowed_library lib2' lib1'.
Proof.
  induction lib2; introv sh ext1 ext2; destruct lib2'; simpl in *; tcsp; GC; eauto 2 with slow.
  repnd.
  allrw @shadowed_library_cons_l_iff; exrepnd.
  dands; tcsp.

  - eapply in_right_extend_library_lawless_upto_implies in ext1;[|eauto].
    exrepnd.
    exists entry'0; dands; auto.
    eapply extend_library_entry_lawless_upto_preserves_matching_entries2;[eauto|].
    apply matching_entries_sym.
    eapply extend_library_entry_lawless_upto_preserves_matching_entries2;[eauto|].
    apply matching_entries_sym; auto.

  - eapply IHlib2; eauto.
Qed.

Lemma entry_in_library_app_implies {o} :
  forall entry (lib1 lib2 : @library o),
    entry_in_library entry (lib1 ++ lib2)
    ->
    (
      entry_in_library entry lib1
      \/
      (
        entry_in_library entry lib2
        /\
        forall e, List.In e lib1 -> ~matching_entries entry e
      )
    ).
Proof.
  induction lib1; introv i; simpl in *; tcsp.
  repndors; repnd; tcsp.
  apply IHlib1 in i; repndors; repnd; tcsp.
  right; dands; auto.
  introv j; repndors; subst; tcsp.
  applydup i in j; tcsp.
Qed.

Lemma entry_in_library_app_shadowed_library {o} :
  forall entry (lib1 lib2 : @library o),
    shadowed_library lib2 lib1
    -> entry_in_library entry (lib1 ++ lib2)
    -> entry_in_library entry lib1.
Proof.
  introv sh i.
  apply entry_in_library_app_implies in i; repndors; repnd; tcsp.
  apply entry_in_library_implies_in in i0; apply sh in i0; exrepnd.
  apply i in i0; tcsp.
Qed.

Inductive permutation {A} : list A -> list A -> Prop :=
| perm_nil : permutation [] []
| perm_cons :
    forall l1 l2 l3 a,
      permutation l1 (l2 ++ l3)
      -> permutation (a :: l1) (l2 ++ a :: l3).
Hint Constructors permutation.

(* compared to [permutation], [strict_permutation] takes out the first a in the 2nd list *)
Inductive strict_permutation {A} : list A -> list A -> Prop :=
| str_perm_nil : strict_permutation [] []
| str_perm_cons :
    forall l1 l2 l3 a,
      ~ List.In a l2
      -> strict_permutation l1 (l2 ++ l3)
      -> strict_permutation (a :: l1) (l2 ++ a :: l3).
Hint Constructors strict_permutation.

Lemma strict_permutation_refl :
  forall {A} (l : list A), strict_permutation l l.
Proof.
  induction l; auto.
  apply (str_perm_cons _ []); simpl; auto.
Qed.
Hint Resolve strict_permutation_refl : slow.

Lemma app_eq_app_cond_implies :
  forall {A} (l1 l2 l3 l4 : list A) a,
    l1 ++ l2 = l3 ++ a :: l4
    -> if le_dec (length l1) (length l3) then
         exists l,
           l2 = l ++ a :: l4
           /\ l3 = l1 ++ l
       else
         exists l,
           l1 = l3 ++ a :: l
           /\ l4 = l ++ l2.
Proof.
  induction l1; introv h; simpl in *; subst; tcsp.

  - exists l3; dands; auto.

  - boolvar.

    + destruct l3; simpl in *; ginv; try omega.
      apply le_S_n in l.
      inversion h; subst; clear h.
      match goal with
      | [ H : _ = _ |- _ ] => rename H into h
      end.
      apply IHl1 in h; boolvar; try omega.
      exrepnd; subst.
      exists l5; dands; auto.

    + assert (length l3 < S (length l1)) as q by omega; clear n.
      destruct l3; simpl in *; ginv.

      * exists l1; dands; auto.

      * inversion h; subst; clear h.
        match goal with
        | [ H : _ = _ |- _ ] => rename H into h
        end.
        apply IHl1 in h; boolvar; try omega.
        exrepnd; subst.
        exists l; dands; auto.
Qed.

Definition ext_libraries {o} (lib1 lib2 : @library o) : Prop :=
  forall entry,
    entry_in_library entry lib1 <-> entry_in_library entry lib2.

Lemma permutation_cons_lr :
  forall {A} (a : A) l1 l2,
    permutation l1 l2
    -> permutation (a :: l1) (a :: l2).
Proof.
  introv perm.
  pose proof (perm_cons l1 [] l2 a) as q; simpl in *; tcsp.
Qed.
Hint Resolve permutation_cons_lr : slow.

Fixpoint insert_after {A} (l : list A) (x : A) n : list A :=
  match n with
  | 0 => x :: l
  | S n =>
    match l with
    | [] => [x]
    | a :: l => a :: insert_after l x n
    end
  end.

Lemma firstn_length :
  forall {A} (l1 l2 : list A),
    firstn (length l1) (l1 ++ l2) = l1.
Proof.
  induction l1; introv; simpl; tcsp.
  f_equal; apply IHl1; auto.
Qed.
Hint Rewrite @firstn_length : slow.

Lemma permutation_middle_left_implies :
  forall {A} a (l1 l2 l : list A),
    permutation (l1 ++ a :: l2) l
    ->
    exists l3 l4,
      l = l3 ++ a :: l4
      /\ permutation (l1 ++ l2) (l3 ++ l4).
Proof.
  induction l1; introv p; simpl in *.

  - inversion p; subst; clear p.
    exists l0 l3; dands; auto.

  - inversion p as [|? ? ? ? p']; subst; clear p.
    apply IHl1 in p'; exrepnd; clear IHl1.
    apply app_eq_app_cond_implies in p'0; boolvar; exrepnd; subst.

    + exists (l3 ++ a0 :: l6) l5; dands; simpl; auto.

      * rewrite <- app_assoc; simpl; auto.

      * rewrite <- app_assoc; simpl; auto.
        rewrite <- app_assoc in p'1.
        pose proof (perm_cons (l1 ++ l2) l3 (l6 ++ l5) a0) as q; simpl in *; tcsp.

    + rewrite <- app_assoc; simpl; auto.
      exists l0 (l ++ a0 :: l4); dands; auto.
      pose proof (perm_cons (l1 ++ l2) (l0 ++ l) l4 a0) as q; simpl in *; tcsp.
      repeat (rewrite <- app_assoc in q); tcsp.
Qed.

Lemma permutation_refl :
  forall {A} (l : list A), permutation l l.
Proof.
  induction l; tcsp.
  pose proof (perm_cons l [] l a) as q; simpl in q; tcsp.
Qed.
Hint Resolve permutation_refl : slow.

Lemma permutation_trans :
  forall {A} (l1 l2 l3 : list A),
    permutation l1 l2
    -> permutation l2 l3
    -> permutation l1 l3.
Proof.
  induction l1; introv p1 p2.

  - inversion p1; subst; clear p1; auto.

  - inversion p1; subst; clear p1.
    apply permutation_middle_left_implies in p2; exrepnd; subst.

    match goal with
    | [ H : permutation l1 _ |- _ ] => rename H into p
    end.
    apply perm_cons; auto.
    eapply IHl1; eauto.
Qed.
Hint Resolve permutation_trans : slow.

Definition bsplit_permutation :
  forall {A} f (l l1 l2 : list A),
    bsplit f l = (l1, l2)
    -> permutation l (l1 ++ l2).
Proof.
  induction l; introv b; simpl in *; ginv; simpl in *; auto.
  remember (bsplit f l) as w; symmetry in Heqw; destruct w as [w1 w2].
  destruct (f a); ginv; simpl in *; tcsp.
  apply permutation_cons_lr; apply IHl; auto.
Qed.

Lemma permutation_cancel_right :
  forall {A} (l1 l2 l : list A),
    permutation l1 l2
    -> permutation (l1 ++ l) (l2 ++ l).
Proof.
  induction l1; introv p; simpl in *; tcsp.

  - inversion p; simpl in *; subst; tcsp; eauto 2 with slow.

  - inversion p as [|? ? ? ? p']; subst; clear p.
    apply (IHl1 _ l) in p'; clear IHl1.
    rewrite <- app_assoc; simpl.
    apply perm_cons.
    rewrite app_assoc; auto.
Qed.

Definition can_lib_permutation {o} :
  forall (lib lib1 lib2 : @library o),
    can_lib lib = (lib1, lib2)
    -> permutation lib (lib1 ++ lib2).
Proof.
  induction lib; introv can; simpl in *.

  - inversion can; subst; simpl; auto.

  - remember (can_lib lib) as c; symmetry in Heqc; destruct c as [c1 c2].
    remember (bsplit (diff_entry_names a) c1) as b; symmetry in Heqb; destruct b as [b1 b2].
    inversion can; subst; clear can; simpl.

    pose proof (IHlib c1 c2) as q; autodimp q hyp; clear IHlib.
    apply bsplit_permutation in Heqb.
    apply permutation_cons_lr.
    eapply permutation_trans; eauto.
    rewrite app_assoc.
    apply permutation_cancel_right; auto.
Qed.

Lemma strict_permutation_cons_lr :
  forall {A} (a : A) l1 l2,
    strict_permutation l1 l2
    -> strict_permutation (a :: l1) (a :: l2).
Proof.
  introv perm.
  pose proof (str_perm_cons l1 [] l2 a) as q; simpl in *; tcsp.
Qed.
Hint Resolve strict_permutation_cons_lr : slow.

Definition bsplit_strict_permutation :
  forall {A} f (l l1 l2 : list A),
    bsplit f l = (l1, l2)
    -> strict_permutation l (l1 ++ l2).
Proof.
  induction l; introv b; simpl in *; ginv; simpl in *; auto.
  remember (bsplit f l) as w; symmetry in Heqw; destruct w as [w1 w2].
  remember (f a) as z; symmetry in Heqz; destruct z; ginv; simpl in *; tcsp.
  - apply strict_permutation_cons_lr; apply IHl; auto.
  - apply str_perm_cons; auto.
    intro i.
    apply bsplit_prop in Heqw; repnd.
    apply Heqw0 in i; rewrite Heqz in i; ginv.
Qed.

Lemma strict_permutation_middle_left_implies :
  forall {A} a (l1 l2 l : list A),
    ~ List.In a l1
    -> strict_permutation (l1 ++ a :: l2) l
    ->
    exists l3 l4,
      l = l3 ++ a :: l4
      /\ ~ List.In a l3
      /\ strict_permutation (l1 ++ l2) (l3 ++ l4).
Proof.
  induction l1; introv ni p; simpl in *.

  - inversion p; subst; clear p.
    exists l0 l3; dands; auto.

  - inversion p as [|? ? ? ? ni' p']; subst; clear p.
    apply not_or in ni; repnd.
    apply IHl1 in p'; exrepnd; clear IHl1; auto.
    apply app_eq_app_cond_implies in p'0; boolvar; exrepnd; subst.

    + allrw List.in_app_iff.
      apply not_or in p'2; repnd.
      exists (l3 ++ a0 :: l6) l5; dands; simpl; auto.

      * rewrite <- app_assoc; simpl; auto.

      * allrw List.in_app_iff; simpl; tcsp.

      * rewrite <- app_assoc; simpl; auto.
        rewrite <- app_assoc in p'1.
        pose proof (str_perm_cons (l1 ++ l2) l3 (l6 ++ l5) a0) as q; simpl in *; tcsp.

    + rewrite <- app_assoc; simpl; auto.
      exists l0 (l ++ a0 :: l4); dands; auto.
      pose proof (str_perm_cons (l1 ++ l2) (l0 ++ l) l4 a0) as q; simpl in *; tcsp.
      repeat (rewrite <- app_assoc in q); tcsp.
      repeat (autodimp q hyp).
      allrw List.in_app_iff; simpl in *.
      apply not_or in ni'; repnd.
      apply not_or in ni'; tcsp.
Qed.

Lemma strict_permutation_trans :
  forall {A} (l1 l2 l3 : list A),
    strict_permutation l1 l2
    -> strict_permutation l2 l3
    -> strict_permutation l1 l3.
Proof.
  induction l1; introv p1 p2.

  - inversion p1; subst; clear p1; auto.

  - inversion p1; subst; clear p1.

    apply strict_permutation_middle_left_implies in p2; exrepnd; subst; auto.

    match goal with
    | [ H : strict_permutation l1 _ |- _ ] => rename H into p
    end.
    apply str_perm_cons; auto.
    eapply IHl1; eauto.
Qed.
Hint Resolve strict_permutation_trans : slow.

Lemma strict_permutation_cancel_right :
  forall {A} (l1 l2 l : list A),
    strict_permutation l1 l2
    -> strict_permutation (l1 ++ l) (l2 ++ l).
Proof.
  induction l1; introv p; simpl in *; tcsp.

  - inversion p; simpl in *; subst; tcsp; eauto 2 with slow.

  - inversion p as [|? ? ? ? ni' p']; subst; clear p.
    apply (IHl1 _ l) in p'; clear IHl1.
    rewrite <- app_assoc; simpl.
    apply str_perm_cons; auto.
    rewrite app_assoc; auto.
Qed.

Definition can_lib_strict_permutation {o} :
  forall (lib lib1 lib2 : @library o),
    can_lib lib = (lib1, lib2)
    -> strict_permutation lib (lib1 ++ lib2).
Proof.
  induction lib; introv can; simpl in *.

  - inversion can; subst; simpl; auto.

  - remember (can_lib lib) as c; symmetry in Heqc; destruct c as [c1 c2].
    remember (bsplit (diff_entry_names a) c1) as b; symmetry in Heqb; destruct b as [b1 b2].
    inversion can; subst; clear can; simpl.

    pose proof (IHlib c1 c2) as q; autodimp q hyp; clear IHlib.

    apply bsplit_strict_permutation in Heqb.
    apply strict_permutation_cons_lr.
    eapply strict_permutation_trans; eauto.
    rewrite app_assoc.
    apply strict_permutation_cancel_right; auto.
Qed.

Lemma ext_libraries_nil {o} : @ext_libraries o [] [].
Proof.
  introv; simpl; tcsp.
Qed.
Hint Resolve ext_libraries_nil : slow.

Definition can_lib_ext_libraries {o} :
  forall (lib lib1 lib2 : @library o),
    can_lib lib = (lib1, lib2)
    -> ext_libraries lib (lib1 ++ lib2).
Proof.
  introv can; introv; split; intro h; eauto 2 with slow.
Qed.

Definition ext_libraries_sym {o} :
  forall (lib1 lib2 : @library o),
    ext_libraries lib1 lib2
    -> ext_libraries lib2 lib1.
Proof.
  introv ext; introv.
  symmetry; tcsp.
Qed.

Lemma implies_permutation_middle :
  forall {A} (a : A) (l1 l2 l3 l4 : list A),
    permutation (l1 ++ l2) (l3 ++ l4)
    -> permutation (l1 ++ a :: l2) (l3 ++ a :: l4).
Proof.
  induction l1; introv p; simpl in *; tcsp.
  inversion p as [|? ? ? ? p']; subst; clear p.
  match goal with
  | [ H : _ = _ |- _ ] => rename H into h
  end.
  symmetry in h.
  apply app_eq_app_cond_implies in h; boolvar; exrepnd; subst; simpl in *.

  - pose proof (perm_cons (l1 ++ a :: l2) (l3 ++ a :: l0) l6 a0) as q.
    rewrite <- app_assoc in p'.
    repeat (rewrite <- app_assoc in q); simpl in q; apply q; clear q.
    apply IHl1; auto.

  - rewrite <- app_assoc; simpl.
    apply perm_cons.
    rewrite app_assoc.
    apply IHl1.
    rewrite <- app_assoc; auto.
Qed.

Definition permutation_sym {o} :
  forall (lib1 lib2 : @library o),
    permutation lib1 lib2
    -> permutation lib2 lib1.
Proof.
  induction lib1; introv p.

  - inversion p; subst; auto.

  - inversion p as [|? ? ? ? p']; subst; clear p.
    apply IHlib1 in p'; clear IHlib1.
    apply (implies_permutation_middle _ _ _ []); simpl; auto.
Qed.

Lemma implies_strict_permutation_middle :
  forall {A} (a : A) (l1 l2 l3 : list A),
    ~ List.In a l1
    -> strict_permutation (l1 ++ l2) l3
    -> strict_permutation (l1 ++ a :: l2) (a :: l3).
Proof.
  induction l1; introv ni p; simpl in *; tcsp; eauto 2 with slow.

  inversion p as [|? ? ? ? ni' p']; subst; clear p.
  apply not_or in ni; repnd.
  apply (str_perm_cons _ (a :: l4)); auto; simpl in *; tcsp.
Qed.

Definition strict_permutation_sym {o} :
  forall (lib1 lib2 : @library o),
    strict_permutation lib1 lib2
    -> strict_permutation lib2 lib1.
Proof.
  induction lib1; introv p.

  - inversion p; subst; auto.

  - inversion p as [|? ? ? ? ni' p']; subst; clear p.
    apply IHlib1 in p'; clear IHlib1.

    apply implies_strict_permutation_middle; simpl; auto.
Qed.

Lemma extend_library_lawless_upto_middle_right_implies {o} :
  forall (lib1 lib2 : @library o) lib entry name n,
    extend_library_lawless_upto lib (lib1 ++ entry :: lib2) name n
    ->
    exists l1 l2 e,
      lib = l1 ++ e :: l2
      /\ extend_library_lawless_upto l1 lib1 name n
      /\ extend_library_lawless_upto l2 lib2 name n
      /\ extend_library_entry_lawless_upto e entry name n.
Proof.
  induction lib1; introv ext; simpl in *;
    destruct lib; simpl in *; tcsp; repnd.

  - exists ([] : @library o) lib l; simpl; dands; auto.

  - dup ext as ext'; eapply IHlib1 in ext'; exrepnd; subst.
    exists (l :: l1) l2 e; simpl; dands; auto.
Qed.

Lemma entry_in_library_implies_middle {o} :
  forall e (lib : @library o),
    entry_in_library e lib
    ->
    exists l1 l2,
      lib = l1 ++ e :: l2
      /\ forall x, List.In x l1 -> ~matching_entries x e.
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.

  - exists ([] : @library o) lib; simpl; dands; auto.

  - autodimp IHlib hyp; exrepnd; subst.
    exists (a :: l1) l2; simpl; dands; auto.
    introv j; repndors; subst; tcsp.

    + intro m; destruct i0; apply matching_entries_sym; auto.

    + apply IHlib1; auto.
Qed.

Lemma bsplit_implies_filter_first {o} :
  forall (a : @library_entry o) l l1 l2,
    bsplit (diff_entry_names a) l = (l1, l2)
    -> l1 = filter (diff_entry_names a) l.
Proof.
  induction l; introv b; simpl in *.

  - inversion b; subst; auto.

  - remember (bsplit (diff_entry_names a) l) as w; symmetry in Heqw; destruct w as [w1 w2].
    pose proof (IHl w1 w2) as q; clear IHl; autodimp q hyp; subst.
    destruct (diff_entry_names a a0); ginv.
Qed.

Lemma canonicalize_library_can_lib1 {o} :
  forall (lib lib1 lib2 : @library o),
    can_lib lib = (lib1,lib2)
    -> lib1 = canonicalize_library lib.
Proof.
  induction lib; introv can; simpl in *.

  - inversion can; subst; simpl in *; tcsp.

  - remember (can_lib lib) as c; symmetry in Heqc; destruct c as [c1 c2].
    remember (bsplit (diff_entry_names a) c1) as b; symmetry in Heqb; destruct b as [b1 b2].
    inversion can; subst; clear can; simpl.

    pose proof (IHlib c1 c2) as q; clear IHlib; autodimp q hyp.
    repnd.
    dands; f_equal.

    rewrite <- q.
    apply bsplit_implies_filter_first in Heqb; auto.
Qed.

Lemma matching_entries_preserves_filter_diff_entry_names {o} :
  forall (e1 e2 : @library_entry o) l,
    matching_entries e1 e2
    -> filter (diff_entry_names e1) l
       = filter (diff_entry_names e2) l.
Proof.
  induction l; introv m; simpl in *; auto.

  remember (diff_entry_names e1 a) as b; symmetry in Heqb; destruct b;
    remember (diff_entry_names e2 a) as z; symmetry in Heqz; destruct z; auto.

  - f_equal; apply IHl; auto.

  - apply matching_entries_iff_diff_entry_names_false in m.
    eapply diff_entry_names_false_trans in Heqz;[|eauto].
    rewrite Heqb in Heqz; ginv.

  - apply matching_entries_sym in m.
    apply matching_entries_iff_diff_entry_names_false in m.
    eapply diff_entry_names_false_trans in Heqb;[|eauto].
    rewrite Heqb in Heqz; ginv.
Qed.

Lemma filter_twice :
  forall {A} f (l : list A),
    filter f (filter f l) = filter f l.
Proof.
  induction l; introv; simpl; auto.
  remember (f a) as b; symmetry in Heqb; destruct b; simpl; allrw; tcsp.
Qed.
Hint Rewrite @filter_twice : slow.

Lemma filter_swap :
  forall {A} f1 f2 (l : list A),
    filter f1 (filter f2 l) = filter f2 (filter f1 l).
Proof.
  induction l; introv; simpl; auto.
  remember (f1 a) as b; symmetry in Heqb; destruct b;
    remember (f2 a) as w; symmetry in Heqw; destruct w;
      simpl; allrw; tcsp.
Qed.

Lemma filter_canonicalize_library_remove_middle {o} :
  forall (a e : @library_entry o) lib1 lib2,
    matching_entries a e
    -> filter (diff_entry_names e) (canonicalize_library (lib1 ++ a :: lib2))
       = filter (diff_entry_names e) (canonicalize_library (lib1 ++ lib2)).
Proof.
  induction lib1; introv m; simpl in *.

  - remember (diff_entry_names e a) as b; symmetry in Heqb; destruct b.

    {
      apply matching_entries_sym in m.
      apply matching_entries_iff_diff_entry_names_false in m.
      rewrite m in Heqb; ginv.
    }

    {
      rewrite (matching_entries_preserves_filter_diff_entry_names a e); auto.
      autorewrite with slow; auto.
    }

  - remember (diff_entry_names e a0) as b; symmetry in Heqb; destruct b.

    {
      f_equal.
      rewrite filter_swap.
      symmetry; rewrite filter_swap.
      symmetry.
      f_equal; apply IHlib1; auto.
    }

    {
      rewrite filter_swap.
      symmetry; rewrite filter_swap.
      symmetry.
      f_equal; apply IHlib1; auto.
    }
Qed.

Lemma canonicalize_library_remove_middle {o} :
  forall (a e : @library_entry o) lib1 lib2,
    List.In e lib1
    -> matching_entries a e
    -> canonicalize_library (lib1 ++ a :: lib2) = canonicalize_library (lib1 ++ lib2).
Proof.
  induction lib1; introv i m; simpl in *; tcsp.
  repndors; subst; tcsp.

  - f_equal.
    apply filter_canonicalize_library_remove_middle; auto.

  - f_equal.
    f_equal.
    apply IHlib1; auto.
Qed.

Lemma canonicalize_library_can_lib2 {o} :
  forall (lib lib1 lib2 : @library o),
    can_lib lib = (lib1,lib2)
    -> canonicalize_library (lib1 ++ lib2) = canonicalize_library lib1.
Proof.
  introv can.
  apply can_lib_left_prop in can.

  induction lib2; simpl in *; autorewrite with slow in *; auto.
  allrw @shadowed_library_cons_l_iff; repnd.
  autodimp IHlib2 hyp.
  exrepnd.
  rewrite <- IHlib2; clear IHlib2.
  eapply canonicalize_library_remove_middle; eauto.
Qed.

Lemma filter_trivial :
  forall {A} f (l : list A),
    (forall x, List.In x l -> f x = true)
    -> filter f l = l.
Proof.
  induction l; introv imp; simpl in *; tcsp.
  remember (f a) as b; symmetry in Heqb; destruct b; tcsp.

  - f_equal.
    apply IHl; introv i.
    apply imp; tcsp.

  - pose proof (imp a) as q; autodimp q hyp; rewrite Heqb in q; ginv.
Qed.

Lemma canonicalize_library_is_canonical {o} :
  forall (lib : @library o),
    is_canonical_library lib
    -> canonicalize_library lib = lib.
Proof.
  induction lib; introv isc; simpl in *; tcsp.
  repnd.
  autodimp IHlib hyp.
  f_equal; allrw.
  apply filter_trivial.
  introv i; apply isc in i.
  remember (diff_entry_names a x) as b; symmetry in Heqb; destruct b; auto.
  apply matching_entries_iff_diff_entry_names_false in Heqb.
  destruct i; apply matching_entries_sym; auto.
Qed.

Lemma extends_snoc_implies_entry_in_inf_library_extends {o} :
  forall (infLib : @inf_library o) lib e,
    inf_lib_extends infLib (snoc lib e)
    -> (forall x, List.In x lib -> diff_entry_names e x = true)
    -> exists k, entry_in_inf_library_extends e k infLib.
Proof.
  introv ext imp.
  destruct ext as [ext safe].
  apply (ext e); clear ext; eauto 2 with slow.
Qed.

Lemma implies_extend_library_lawless_upto_snoc {o} :
  forall (lib1 lib2 : @library o) e1 e2 name n,
    extend_library_entry_lawless_upto e1 e2 name n
    -> extend_library_lawless_upto lib1 lib2 name n
    -> extend_library_lawless_upto (snoc lib1 e1) (snoc lib2 e2) name n.
Proof.
  induction lib1; introv ext1 ext2; simpl in *; tcsp; destruct lib2; simpl in *; tcsp.
Qed.
Hint Resolve implies_extend_library_lawless_upto_snoc : slow.

Lemma extend_library_entry_lawless_upto_preserves_diff_entry_names_false {o} :
  forall (e1 e2 : @library_entry o) name n e,
    extend_library_entry_lawless_upto e1 e2 name n
    -> diff_entry_names e e2 = false
    -> diff_entry_names e e1 = false.
Proof.
  introv ext h; destruct e1, e2; simpl in *; boolvar; ginv; repeat subst; tcsp.
Qed.
Hint Resolve extend_library_entry_lawless_upto_preserves_diff_entry_names_false : slow.

Lemma extend_library_lawless_upto_preserves_forallb_diff_entry_names_false {o} :
  forall (lib1 lib2 : @library o) name n e,
    extend_library_lawless_upto lib1 lib2 name n
    -> forallb (diff_entry_names e) lib2 = false
    -> forallb (diff_entry_names e) lib1 = false.
Proof.
  induction lib1; introv ext h; simpl in *; destruct lib2; simpl in *; tcsp.
  allrw andb_false_iff.
  repnd.
  repndors; tcsp.

  - left; eauto 2 with slow.

  - right; eapply IHlib1; eauto.
Qed.

Lemma lib_has_memNat_restriction_snoc {o} :
  forall (lib : @library o) e name,
    lib_has_memNat_restriction (snoc lib e) name
    <-> (lib_has_memNat_restriction lib name /\ has_memNat_restriction e name).
Proof.
  induction lib; introv; simpl; split; intro h; repnd; dands; tcsp.

  - apply IHlib in h; tcsp.

  - apply IHlib in h; tcsp.

  - apply IHlib; tcsp.
Qed.

Lemma exists_extend_library_lawless_upto_following_infinite {o} :
  forall (infLib : @inf_library o) name n lib,
    safe_library lib
    -> inf_lib_extends infLib lib
    ->
    exists lib',
      extend_library_lawless_upto lib' lib name n
      /\ inf_lib_extends infLib lib'.
Proof.
  induction lib using rev_list_ind; introv safe ext; simpl in *.

  { exists ([] : @library o); simpl; tcsp. }

  apply safe_library_snoc_implies in safe; repnd.
  allrw @lib_has_memNat_restriction_snoc; repnd.
  applydup @inf_lib_extends_snoc_implies_head in ext as ext'; auto;[].
  repeat (autodimp IHlib hyp).
  exrepnd.

  remember (forallb (diff_entry_names a) lib) as b; symmetry in Heqb; destruct b.

  - (* [a] is accessible *)

    rewrite forallb_forall in Heqb.
    pose proof (extends_snoc_implies_entry_in_inf_library_extends infLib lib a) as q.
    repeat (autodimp q hyp); exrepnd.

    pose proof (entry_in_inf_library_extends_implies_extend_library_entry_lawless_upto k infLib a name n) as h.
    repeat (autodimp h hyp); eauto 2 with slow.
    exrepnd.

    exists (snoc lib' entry'); dands; auto; eauto 2 with slow.

  - (* [a] is not accessible  *)

    pose proof (exists_extend_library_entry_lawless_upto_default name n a) as z.
    repeat (autodimp z hyp).
    exrepnd.
    exists (snoc lib' entry'); dands; eauto 2 with slow.
    apply implies_inf_lib_extends_snoc_shadowed; auto.
    apply extend_library_entry_lawless_upto_implies_entry_extends in z0.
    eapply entry_extends_preserves_forallb_diff_entry_names_false in z0;[|eauto].
    eapply extend_library_lawless_upto_preserves_forallb_diff_entry_names_false; eauto.
Qed.

(*
Lemma lib_extends_preserves_lib_has_memNat_restriction {o} :
  forall name (lib1 lib2 : @library o),
    lib_extends lib2 lib1
    -> lib_has_memNat_restriction lib1 name
    -> lib_has_memNat_restriction lib2 name.
Proof.

Qed.
*)

Definition extend_bar_nat_lawless_upto {o} {lib} {a} {a'}
           (bar  : @BarLib o lib)
           (safe : safe_library lib)
           (F    : all_in_bar bar (fun lib => equality_of_nat lib a a'))
  : BarLib lib.
Proof.
  exists (fun (lib' : library) =>
            exists (lib0 : library) (b : bar_lib_bar bar lib0),
              extend_library_lawless_upto
                lib'
                lib0
                seq_1
                (S (projT1 (equality_of_nat_imp_tt (F lib0 b lib0 (lib_extends_refl lib0)))))).

  - introv ext'; simpl.

    destruct bar as [bar cond ext]; simpl in *.
    pose proof (cond infLib ext') as q.

    exrepnd.
    rename lib' into lib1.
    applydup @lib_extends_safe in q2 as safe1; auto;[].

    assert (exists lib',
               extend_library_lawless_upto
                 lib' lib1 seq_1
                 (S (projT1 (equality_of_nat_imp_tt (F lib1 q1 lib1 (lib_extends_refl lib1)))))
               /\ lib_extends lib' lib
               /\ inf_lib_extends infLib lib') as exlib;
      [|exrepnd; exists lib'; dands; auto; exists lib1 q1; auto];[].

    remember (equality_of_nat_imp_tt (F lib1 q1 lib1 (lib_extends_refl lib1))) as w; symmetry in Heqw.
    unfold equality_of_nat_tt in w; exrepnd; simpl in *.
    clear Heqw.

    assert (exists lib',
               extend_library_lawless_upto lib' lib1 seq_1 (S k)
               /\ lib_extends lib' lib1
               /\ inf_lib_extends infLib lib') as exlib;
      [|exrepnd; exists lib'; dands; auto; eapply lib_extends_trans; eauto];[].

    assert (exists lib',
               extend_library_lawless_upto lib' lib1 seq_1 (S k)
               /\ inf_lib_extends infLib lib') as exlib;
      [|exrepnd; exists lib'; dands; eauto 2 with slow];[].

    apply exists_extend_library_lawless_upto_following_infinite; eauto 2 with slow.

  - introv j; exrepnd.

    remember (equality_of_nat_imp_tt (F lib0 b lib0 (lib_extends_refl lib0))) as z; symmetry in Heqz.
    unfold equality_of_nat_tt in z.
    exrepnd; simpl in *.
    eauto 4 with slow.
Defined.

Lemma select_lt_length :
  forall {A} (l : list A) k,
    k < length l
    -> exists a, select k l = Some a.
Proof.
  induction l; introv h; simpl in *; try omega.
  destruct k; simpl in *; eauto.
  apply IHl; try omega.
Qed.

Lemma select_some_implies_list_in :
  forall {A} (l : list A) k a,
    select k l = Some a
    -> List.In a l.
Proof.
  induction l; introv h; simpl in *; try omega; destruct k; simpl in *; eauto; ginv; tcsp.
Qed.

Lemma extend_library_lawless_upto_implies_right {o} :
  forall (lib1 lib2 : @library o) name n entry,
    extend_library_lawless_upto lib1 lib2 name n
    -> entry_in_library entry lib2
    ->
    exists e,
      entry_in_library e lib1
      /\ extend_library_entry_lawless_upto e entry name n.
Proof.
  induction lib1; introv ext i; simpl in *; tcsp.

  { destruct lib2; simpl in *; tcsp. }

  destruct lib2; repnd; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; tcsp.

  - exists a; dands; tcsp.

  - eapply IHlib1 in ext;[|eauto].
    exrepnd.
    exists e; dands; tcsp.
    right; dands; auto.
    introv m; destruct i0.
    eauto 5 with slow.
Qed.

Lemma entry_in_library_implies_find_cs_some {o} :
  forall (lib : @library o) (name : choice_sequence_name) (vals : ChoiceSeqEntry),
    entry_in_library (lib_cs name vals) lib -> find_cs lib name = Some vals.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  repndors; repnd; subst; simpl in *; boolvar; tcsp.
  destruct a; simpl in *; auto; boolvar; subst; tcsp.
  destruct h0; tcsp.
Qed.

Lemma extend_library_lawless_upto_implies_find_cs {o} :
  forall (lib1 lib2 : @library o) name k vals d T Td,
    safe_library lib2
    -> entry_in_library (lib_cs name (MkChoiceSeqEntry _ vals (csc_type d T Td))) lib2
    -> extend_library_lawless_upto lib1 lib2 name (S k)
    -> exists n, find_cs_value_at lib1 name k = Some n /\ T n.
Proof.
  introv safe i ext.
  eapply extend_library_lawless_upto_implies_right in ext;[|eauto].
  exrepnd.
  destruct e; simpl in *; boolvar; subst; GC; ginv; tcsp.
  remember (S k) as m.
  destruct entry as [vals1 restr1]; simpl in *.
  destruct restr1; simpl in *; tcsp; ginv.
  exrepnd; subst.

  apply entry_in_library_implies_find_cs_some in ext1; simpl in ext1.
  unfold find_cs_value_at.
  allrw; simpl in i; simpl.

  rewrite find_value_of_cs_at_vals_as_select.
  destruct (le_dec (length vals) k) as [d1|d1].

  - rewrite select_app_r; auto.
    pose proof (select_lt_length vals0 (k - length vals)) as h; autodimp h hyp; try omega;[].
    exrepnd; allrw.
    apply select_some_implies_list_in in h0.
    apply ext3 in h0; exrepnd; subst; eauto.

  - rewrite select_app_l; auto; try omega.
    pose proof (select_lt_length vals k) as h; autodimp h hyp; try omega;[].
    exrepnd; allrw.
    apply select_some_implies_list_in in h0.
    exists a; dands; auto.
    apply safe in i; simpl in i; apply i; auto.
Qed.

Lemma entry_in_library_extends_lib_entry_1_implies_entry_in_library {o} :
  forall (lib : @library o),
    entry_in_library_extends lib_entry_1 lib
    ->
    exists vals,
      entry_in_library (lib_cs seq_1 (MkChoiceSeqEntry _ vals (csc_type (mkc_nat 0) memNat memNat0))) lib.
Proof.
  induction lib; introv ext; simpl in *; tcsp.
  repndors; exrepnd; tcsp.

  - destruct a; simpl in *; repnd; subst; tcsp; ginv.
    destruct entry as [vals restr]; simpl in *.
    unfold choice_sequence_entry_extend in ext; simpl in *; repnd; subst.
    exists vals; tcsp.

  - autodimp IHlib hyp; exrepnd.
    exists vals; tcsp.
Qed.

Lemma lib_extends_lib1_implies_entry_in_library {o} :
  forall (lib : @library o),
    lib_extends lib lib_1
    ->
    exists vals,
      entry_in_library (lib_cs seq_1 (MkChoiceSeqEntry _ vals (csc_type (mkc_nat 0) memNat memNat0))) lib.
Proof.
  introv ext.
  destruct ext as [ext safe sub].
  pose proof (ext lib_entry_1) as q.
  autodimp q hyp; simpl; tcsp.
  apply entry_in_library_extends_lib_entry_1_implies_entry_in_library; auto.
Qed.

(*Lemma lib_extends_preserves_extend_library_lawless_upto {o} :
  forall (lib1 lib2 lib : @library o) name k,
    lib_extends memNat lib1 lib2
    -> extend_library_lawless_upto lib2 lib name k
    -> extend_library_lawless_upto lib1 lib name k.
Proof.
  induction lib1; introv ext1 ext2; simpl in *.

  - destruct lib; auto.
    destruct lib2; simpl in *; tcsp; repnd.
    destruct ext1 as [ext safe sub]; simpl in *.
    pose proof (ext l0) as q; tcsp.

  - destruct lib; simpl in *; tcsp.

    + destruct lib2; simpl in *; tcsp.
      destruct ext1 as [ext safe sub]; simpl in *.
      pose proof (ext l0) as q; tcsp.
Qed*)

Lemma seq1_in_nat2nat {o} :
  @member o lib_1 (mkc_choice_seq seq_1) Nat2Nat.
Proof.
  unfold Nat2Nat, member, equality.
  eexists; dands.

  {
    apply CL_func.
    unfold per_func_ext.
    exists (@equality_of_nat_bar_lib_per o lib_1)
           (equality_of_nat_bar_lib_per_fam
              lib_1
              (@equality_of_nat_bar_lib_per o lib_1)).
    dands;[|apply eq_term_equals_refl].

    unfold type_family_ext.
    allrw <- @fold_mkc_fun.
    eexists; eexists; eexists; eexists; eexists; eexists.
    dands.

    {
      try introv i.
      spcast.
      apply computes_to_valc_refl; eauto 2 with slow.
    }

    {
      try introv i.
      spcast.
      apply computes_to_valc_refl; eauto 2 with slow.
    }

    {
      repeat introv.
      apply CL_nat.
      unfold per_nat; dands; spcast; eauto 3 with slow.
    }

    {
      repeat introv.
      autorewrite with slow.
      apply CL_nat.
      unfold per_nat; dands; spcast; eauto 3 with slow.
    }
  }

  {
    unfold per_func_eq.
    try (exists (@trivial_bar o lib_1)); simpl.
    introv xt1 xt2 x en; introv; simpl in *.

    unfold equality_of_nat_bar in *; exrepnd.

    applydup @lib_extends_preserves_safe in xt2 as safe; eauto 3 with slow.

    exists (extend_bar_nat_lawless_upto bar safe en0).
    introv b; simpl in *.
    exrepnd; subst.

    remember (equality_of_nat_imp_tt (en0 _ b lib0 _)) as w; symmetry in Heqw.
    unfold equality_of_nat_tt in w; exrepnd; simpl in *.

    introv lext.

    clear Heqw.
    eapply (computes_to_valc_nat_if_lib_extends lib'1 lib0) in w1; eauto 3 with slow;[].
    eapply (computes_to_valc_nat_if_lib_extends lib'1 lib0) in w0; eauto 3 with slow;[].

    pose proof (bar_preserves_safe bar lib0) as safe1.
    repeat (autodimp safe1 hyp);[].

    applydup @extend_library_lawless_upto_preserves_safe_library in b1 as safe2; auto;[].

    assert (lib_extends lib0 lib_1) as ext by (eauto 4 with slow).
    apply lib_extends_lib1_implies_entry_in_library in ext; exrepnd.

    pose proof (extend_library_lawless_upto_implies_find_cs lib'1 lib0 seq_1 k vals (mkc_nat 0) memNat memNat0) as q.
    repeat (autodimp q hyp); exrepnd.
    eapply lib_extends_preserves_find_cs_value_at in q1;[|eauto].

    unfold memNat in q0; exrepnd; subst.
    exists n0; simpl.
    dands; spcast;
      eapply implies_compute_to_valc_apply_choice_seq; eauto; simpl;
        try (complete (eapply (computes_to_valc_nat_if_lib_extends memNat);[|eauto];eauto 2 with slow));
        eauto 3 with slow.
  }
Qed.
