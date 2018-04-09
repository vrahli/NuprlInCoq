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


Require Export computation_lib_extends.



Definition InfChoiceSeqVals {o} := nat -> @ChoiceSeqVal o.

Definition inf_choice_sequence_satisfies_restriction {o}
           (vals       : @InfChoiceSeqVals o)
           (constraint : ChoiceSeqRestriction) : Prop :=
  match constraint with
  | csc_type d M Md => forall n, M n (vals n)
  | csc_coq_law f => forall n, vals n = f n
  end.

(*Definition ex_choice {o}
           (restr : @ChoiceSeqRestriction o) : Type :=
  match restr with
  | csc_type d M Md => {v : @ChoiceSeqVal o & M v}
  end.*)

Record InfChoiceSeqEntry {o} (*(M : Mem)*) :=
  MkInfChoiceSeqEntry
    {
      icse_vals :> (*@ex_choice o M icse_restriction ->*) @InfChoiceSeqVals o;
      icse_restriction : @ChoiceSeqRestriction o;
    }.

Inductive inf_library_entry {o} (*M*) :=
(* a choice sequence *)
| inf_lib_cs
    (name : choice_sequence_name)
    (entry : @InfChoiceSeqEntry o (*M*))
(* a reference *)
| inf_lib_ref
    (name : reference_name)
    (entry : @ReferenceEntry o (*M*))
(* a regular abstraction *)
| inf_lib_abs
    (opabs : opabs)
    (vars  : list sovar_sig)
    (rhs   : @SOTerm o)
    (correct : correct_abs opabs vars rhs).

Definition inf_library {o} (*M*) := nat -> @inf_library_entry o (*M*).

Definition safe_inf_choice_sequence_entry {o} (name : choice_sequence_name) (e : @InfChoiceSeqEntry o (*M*)) :=
  match e with
  | MkInfChoiceSeqEntry _ vals restriction =>
    correct_cs_restriction name restriction
    /\ inf_choice_sequence_satisfies_restriction vals restriction
  end.

Definition upd_restr_inf_entry {o} (name : choice_sequence_name) (e : @InfChoiceSeqEntry o) :=
  if is0kind name then
    match e with
    | MkInfChoiceSeqEntry _ vals restriction => MkInfChoiceSeqEntry o vals csc_nat
    end
  else e.

Definition safe_inf_library_entry {o} (e : @inf_library_entry o (*M*)) :=
  match e with
  | inf_lib_cs name cse => safe_inf_choice_sequence_entry name ((*upd_restr_inf_entry name*) cse)
  | inf_lib_ref name restr => safe_reference_entry name restr
  | _ => True
  end.

Definition inf_entry2name {o} (*{M}*) (e : @inf_library_entry o (*M*)) : EntryName :=
  match e with
  | inf_lib_cs name _ => entry_name_cs name
  | inf_lib_ref name _ => entry_name_ref name
  | inf_lib_abs opabs _ _ _ => entry_name_abs opabs
  end.

Definition inf_matching_entries {o}
           (entry1 : @inf_library_entry o)
           (entry2 : @library_entry o) : Prop :=
  same_entry_name (inf_entry2name entry1) (entry2name entry2).

Definition matching_inf_entries {o} (entry1 entry2 : @inf_library_entry o) : Prop :=
  same_entry_name (inf_entry2name entry1) (inf_entry2name entry2).

Definition shift_inf_lib {o} (*{M}*) (l : @inf_library o (*M*)) : inf_library (*M*) :=
  fun n => l (S n).

Fixpoint entry_in_inf_library_n {o}
         (n      : nat)
         (entry  : @inf_library_entry o)
         (inflib : inf_library) : Prop :=
  match n with
  | 0 => False
  | S n =>
    entry = inflib 0
    \/
    (~ matching_inf_entries (inflib 0) entry
       # entry_in_inf_library_n n entry (shift_inf_lib inflib))
  end.

Definition is_default_inf_choice_sequence {o}
           (vals       : @InfChoiceSeqVals o)
           (constraint : ChoiceSeqRestriction) : Prop :=
  match constraint with
  | csc_type d M Md => forall n, vals n = d n
  | csc_coq_law f => forall n, vals n = f n
  end.

Definition is_default_inf_choice_seq_entry {o}
           (e    : @InfChoiceSeqEntry o) :=
  match e with
  | MkInfChoiceSeqEntry _ vals restr => is_default_inf_choice_sequence vals restr
  end.

Definition is_nat_or_seq_kind (name : choice_sequence_name) :=
  match csn_kind name with
  | cs_kind_nat n => n = 0
  | cs_kind_seq _ => True
  end.

Definition is_nat_ref_kind (name : reference_name) :=
  match rf_kind name with
  | ref_kind_nat n => n = 0
  end.

Definition is_default_reference {o}
           (v     : @CTerm o)
           (restr : RefRestriction) : Prop :=
  match restr with
  | rr_type d M Md => v = d
  end.

Definition is_default_ref_entry {o}
           (e : @ReferenceEntry o) :=
  match e with
  | MkReferenceEntry _ v restr => is_default_reference v restr
  end.

Definition is_cs_default_inf_entry {o} (e : @inf_library_entry o) :=
  match e with
  | inf_lib_cs name cs =>
    is_nat_or_seq_kind name
    /\ is_default_inf_choice_seq_entry cs
  | inf_lib_ref name cs => False
  | inf_lib_abs _ _ _ _ => False
  end.

Definition is_ref_default_inf_entry {o} (e : @inf_library_entry o) :=
  match e with
  | inf_lib_cs name cs => False
  | inf_lib_ref name cs =>
    is_nat_ref_kind name
    (*/\ is_default_ref_entry cs*)
  | inf_lib_abs _ _ _ _ => False
  end.

Definition inf_entry_in_inf_library_cs_default {o}
           (entry  : @inf_library_entry o)
           (inflib : inf_library) :=
  (forall n, ~ matching_inf_entries (inflib n) entry)
  /\ safe_inf_library_entry entry
  /\ is_cs_default_inf_entry entry.

Definition inf_entry_in_inf_library_ref_default {o}
           (entry  : @inf_library_entry o)
           (inflib : inf_library) :=
  (forall n, ~ matching_inf_entries (inflib n) entry)
  /\ safe_inf_library_entry entry
  /\ is_ref_default_inf_entry entry.

Definition entry_in_inf_library {o}
           (entry  : @inf_library_entry o)
           (inflib : inf_library) : Prop :=
  (exists n, entry_in_inf_library_n n entry inflib)
  \/
  (* NEW---this is to ensure that all choice sequences are in the infinite library
     A better way would be to enforce that in definition of infinite sequences
     but then that means that we have to enumerate all choice sequence names to
     build an infinite sequence to prove that bars are non-empty... *)
  inf_entry_in_inf_library_cs_default entry inflib
  \/
  inf_entry_in_inf_library_ref_default entry inflib.

Definition safe_inf_library {o} (inflib : @inf_library o (*M*)) :=
  forall entry, entry_in_inf_library entry inflib -> safe_inf_library_entry entry.

Definition inf_choice_sequence_vals_extend {o}
           (vals1 : @InfChoiceSeqVals o)
           (vals2 : @ChoiceSeqVals o) : Prop :=
  forall n v,
    select n vals2 = Some v
    -> vals1 n = v.

(* [entry1] extends [entry2] *)
Definition inf_choice_sequence_entry_extend {o} (*{M}*)
           (entry1 : @InfChoiceSeqEntry o (*M*))
           (entry2 : @ChoiceSeqEntry o) : Prop :=
  (* the extension has the same restriction has the current sequence *)
  (*icse_restriction entry1 = cse_restriction entry2*)
  same_restrictions (icse_restriction entry1) (cse_restriction entry2)
  (* the extension is an extension *)
  /\
  inf_choice_sequence_vals_extend entry1 entry2.

(* [entry1] extends [entry2] *)
Definition inf_entry_extends {o} (*{M}*)
           (entry1 : @inf_library_entry o (*M*))
           (entry2 : @library_entry o) : Prop :=
  match entry1, entry2 with
  | inf_lib_cs name1 entry1, lib_cs name2 entry2 =>
    name1 = name2 /\ inf_choice_sequence_entry_extend entry1 entry2

  | inf_lib_ref name1 entry1, lib_ref name2 entry2 =>
    name1 = name2 /\ reference_entry_extend entry1 entry2

  | inf_lib_abs abs1 vars1 rhs1 cor1, lib_abs abs2 vars2 rhs2 cor2 =>
    abs1 = abs2 /\ vars1 = vars2 /\ rhs1 = rhs2

  | _, _ => False
  end.

Fixpoint entry_in_inf_library_extends {o} (*{M}*)
         (entry  : @library_entry o)
         (n      : nat)
         (inflib : inf_library (*M*)) : Prop :=
  match n with
  | 0 => False
  | S n =>
    inf_entry_extends (inflib 0) entry
    \/
    (~ inf_matching_entries (inflib 0) entry
       # entry_in_inf_library_extends entry n (shift_inf_lib inflib))
  end.

(*Definition subset_inf_library {o} (*{M}*) (lib : @library o) (infl : @inf_library o (*M*)) :=
  forall entry,
    List.In entry lib
    -> exists n, inf_entry_extends (infl n) entry.*)

Definition is_default_choice_sequence {o}
           (vals       : @ChoiceSeqVals o)
           (constraint : ChoiceSeqRestriction) : Prop :=
  match constraint with
  | csc_type d M Md => forall n v, select n vals = Some v -> v = d n
  | csc_coq_law f => forall n v, select n vals = Some v -> v = f n
  end.

Definition is_default_choice_seq_entry {o}
           (e : @ChoiceSeqEntry o) :=
  match e with
  | MkChoiceSeqEntry _ vals restr => is_default_choice_sequence vals restr
  end.

Definition is_cs_default_entry {o} (e : @library_entry o) :=
  match e with
  | lib_cs name cs =>
    is_nat_or_seq_kind name
    /\ is_default_choice_seq_entry cs
  | lib_ref name cs => False
  | lib_abs _ _ _ _ => False
  end.

Definition entry_in_inf_library_cs_default {o}
           (entry  : @library_entry o)
           (inflib : inf_library) :=
  (forall n, ~ inf_matching_entries (inflib n) entry)
  /\ safe_library_entry entry
  /\ is_cs_default_entry entry.

Definition is_ref_default_entry {o} (e : @library_entry o) :=
  match e with
  | lib_cs name cs => False
  | lib_ref name cs =>
    is_nat_ref_kind name
    (*/\ is_default_ref_entry cs*)
  | lib_abs _ _ _ _ => False
  end.

Definition entry_in_inf_library_ref_default {o}
           (entry  : @library_entry o)
           (inflib : inf_library) :=
  (forall n, ~ inf_matching_entries (inflib n) entry)
  /\ safe_library_entry entry
  /\ is_ref_default_entry entry.

Definition inf_lib_extends_ext_entries {o} (infl : @inf_library o) (lib : @library o) :=
  forall entry,
    entry_in_library entry lib
    ->
    (exists n, entry_in_inf_library_extends entry n infl)
    \/ entry_in_inf_library_cs_default entry infl
    \/ entry_in_inf_library_ref_default entry infl.


(*Lemma is_cs_default_inf_entry_implies_safe {o} :
  forall (entry : @inf_library_entry o),
    is_cs_default_inf_entry entry
    -> safe_inf_library_entry entry.
Proof.
  introv ics.
  unfold safe_inf_library_entry.
  destruct entry; simpl in *; repnd; auto; eauto 3 with slow.


Lemma is_default_inf_choice_seq_entry_implies_safe {o} :
  forall name (entry : @InfChoiceSeqEntry o),
    is_nat_or_seq_kind name
    -> is_default_inf_choice_seq_entry entry
    -> safe_inf_choice_sequence_entry name entry.
Proof.
  introv isn isd.
  destruct entry; simpl in *.
  dands; eauto 3 with slow.

Lemma is_default_inf_choice_sequence_implies_correct {o} :
  forall name vals (restr : @ChoiceSeqRestriction o),
    is_nat_or_seq_kind name
    -> is_default_inf_choice_sequence vals restr
    -> correct_restriction name restr.
Proof.
  introv isn isd.
  unfold correct_restriction.
  destruct name as [name k]; simpl in *.
  unfold is_nat_or_seq_kind in *; simpl in *.
  destruct k as [n|seq]; simpl in *; eauto 3 with slow; boolvar; subst; auto.

Lemma is_default_inf_choice_sequence_implies_is_nat_restriction {o} :
  forall vals (restr : @ChoiceSeqRestriction o),
    is_default_inf_choice_sequence vals restr
    -> is_nat_restriction restr.
Proof.
  introv isd.
  unfold is_default_inf_choice_sequence in isd.
  destruct restr; simpl in *; tcsp.

  Focus 2.
Qed.
Hint Resolve is_default_inf_choice_sequence_implies_is_nat_restriction : slow.
g

Qed.
Hint Resolve is_default_inf_choice_sequence_implies_correct : slow.


Qed.
Hint Resolve is_default_inf_choice_seq_entry_implies_safe : slow.

Qed.
*)


Record inf_lib_extends {o} (infl : @inf_library o) (lib : @library o) :=
  MkInfLibExtends
    {
      inf_lib_extends_ext  : inf_lib_extends_ext_entries infl lib;
      inf_lib_extends_safe : safe_library lib -> safe_inf_library infl;

(*      inf_lib_extends_sub : subset_inf_library lib infl;*)
    }.

(* Do bars have to be decidable (i.e., bool instead of Prop)?
   If they do, then we're in trouble because we can't decide whether 2 terms are
   equal.  We would have to get rid of all our undecidable stuff *)
Definition bar_lib {o} := @library o -> Prop.


(*Definition MR {o} (ts : cts(o)) (lib : @library o) :=
  fun v T => exists per, ts lib T T per /\ per v v.*)


(* This states that [bar] is a bar of [lib] *)
Definition BarLibBars {o}
           (bar : @bar_lib o)
           (lib : @library o) :=
  forall (infLib : inf_library (*M*)),
    inf_lib_extends infLib lib
    ->
    exists (lib' : library),
      bar lib'
      /\ lib_extends lib' lib
      /\ inf_lib_extends infLib lib'.

Definition BarLibExt {o}
           (bar : @bar_lib o)
           (lib : @library o) :=
  forall (lib' : library),  bar lib' -> lib_extends lib' lib.

(* The bar is non-empty.  This is useful for example when
   We know that a type [T] computes to [Nat] at a bar, then we can
   at least get one such library at the bar at which [T] computes to [Nat] *)
Definition BarLibMem {o}
           (bar : @bar_lib o) :=
  exists (lib' : library), bar lib'.

Record BarLib {o} (lib : @library o) :=
  MkBarLib
    {
      bar_lib_bar  :> @bar_lib o;
      bar_lib_bars : BarLibBars bar_lib_bar lib;
      bar_lib_ext  : BarLibExt bar_lib_bar lib;
(*      bar_lib_mem  : BarLibMem bar_lib_bar;*)
    }.
Arguments bar_lib_bar  [o] [lib] _ _.
Arguments bar_lib_bars [o] [lib] _ _ _.
Arguments bar_lib_ext  [o] [lib] _ _ _.
(*Arguments bar_lib_mem  [o] [M] [lib] _.*)

Definition all_in_bar0 {o} {lib} (bar : BarLib lib) (F : @library o -> Prop) :=
  forall (lib' : library), bar_lib_bar bar lib' -> F lib'.

(* As opposed to [all_in_bar0], here we require that the property be true in all
   extensions of the bar *)

Definition all_in_bar {o} {lib} (bar : BarLib lib) (F : @SL o -> Prop) :=
  forall (lib' : SL), bar_lib_bar bar lib' -> in_ext lib' F.

Definition in_bar {o} (lib : @SL o) (F : @SL o -> Prop) :=
  exists (bar : BarLib lib), all_in_bar bar F.



Lemma fresh_choice_sequence_name : FreshFun choice_sequence_name.
Proof.
  unfold FreshFun.
  introv.

  exists (MkChoiceSequenceName (String.append "x" (append_string_list (map csn_name l))) (cs_kind_nat 0)).
  remember ("x") as extra.
  assert (0 < String.length extra)%nat as len by (subst; simpl; auto).
  clear Heqextra.
  revert dependent extra.
  induction l; introv s; allsimpl; tcsp.
  rw string_append_assoc.
  introv k; repndors;[|apply IHl in k;auto;rw string_length_append; omega].
  destruct a as [nm ki].
  inversion k as [xx]; clear k.
  subst ki.

  assert (String.length nm
          = String.length
              (String.append
                 (String.append extra nm)
                 (append_string_list (map csn_name l)))) as e.
  { rewrite xx at 1; auto. }
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

  - boolvar; tcsp.
    allrw not_over_or; dands; tcsp.
    apply IHlib; auto.

  - apply IHlib; auto.

  - boolvar; tcsp.
    allrw not_over_or; dands; tcsp.
    apply IHlib; auto.
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
  | csc_type d _ _ => d
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
  | lib_ref name entry => inf_lib_ref name entry
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

Definition natSeq2default {o} (l : list nat) : nat -> @ChoiceSeqVal o :=
  fun n =>
    match select n l with
    | Some i => mkc_nat i
    | None => mkc_zero
    end.

Definition natSeq2restrictionPred {o} (l : list nat) : @RestrictionPred o :=
  fun n v =>
    match select n l with
    | Some i => v = mkc_nat i
    | None => is_nat n v
    end.

Lemma natSeq2default_restr {o} (l : list nat) :
  forall n, @natSeq2restrictionPred o l n (natSeq2default l n).
Proof.
  introv.
  unfold natSeq2restrictionPred, natSeq2default.
  remember (select n l) as k; destruct k; auto; eauto 3 with slow.
Qed.
Hint Resolve natSeq2default_restr : slow.

Definition natSeq2restriction {o} (l : list nat) : @ChoiceSeqRestriction o :=
  @csc_type o (natSeq2default l) (natSeq2restrictionPred l) (natSeq2default_restr l).

Definition simple_inf_choice_seq_entry {o}
           (name : choice_sequence_name) : @InfChoiceSeqEntry o :=
  match csn_kind name with
  | cs_kind_nat _ => MkInfChoiceSeqEntry _ (fun _ => mkc_zero) csc_nat
  | cs_kind_seq l => MkInfChoiceSeqEntry _ (natSeq2default l) (natSeq2restriction l)
  end.

Definition simple_inf_choice_seq {o} (name : choice_sequence_name) : @inf_library_entry o :=
  inf_lib_cs name (simple_inf_choice_seq_entry name).

Lemma inf_choice_sequence_entry_extend_choice_seq_entry2inf {o} :
  forall (entry : @ChoiceSeqEntry o),
    inf_choice_sequence_entry_extend (choice_seq_entry2inf entry) entry.
Proof.
  introv; destruct entry; simpl.
  unfold inf_choice_sequence_entry_extend; simpl.
  dands; auto; eauto 3 with slow;[].
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
  forall name (entry : @ChoiceSeqEntry o),
    safe_choice_sequence_entry name entry
    -> safe_inf_choice_sequence_entry name (choice_seq_entry2inf entry).
Proof.
  introv h; destruct entry as [vals restr]; simpl in *; repnd; dands; auto.

  destruct restr; simpl in *; auto; GC; introv.

  - unfold choice_seq_vals2inf.
    remember (select n vals) as s; symmetry in Heqs.
    destruct s; auto.

  - unfold choice_seq_vals2inf.
    remember (select n vals) as s; symmetry in Heqs.
    destruct s; auto.
    rewrite (h n) in Heqs;[inversion Heqs; auto|].
    eapply select_lt; eauto.
Qed.
Hint Resolve implies_safe_inf_choice_sequence_entry2inf : slow.

Lemma shift_inf_lib_library2inf_cons {o} :
  forall e (lib : @library o) d,
    shift_inf_lib (library2inf (e :: lib) d)
    = library2inf lib d.
Proof.
  introv; apply functional_extensionality; introv; simpl; auto.
Qed.
Hint Rewrite @shift_inf_lib_library2inf_cons : slow.

Lemma entry_in_inf_library_n_const {o} :
  forall n (entry : @inf_library_entry o) d,
    entry_in_inf_library_n n entry (fun _ => d) -> entry = d.
Proof.
  induction n; introv i; simpl in *; tcsp.
Qed.

Lemma matching_entries_implies_matching_inf_entries {o} :
  forall (e1 e2 : @library_entry o),
    matching_entries e1 e2
    -> matching_inf_entries (library_entry2inf e1) (library_entry2inf e2).
Proof.
  introv m.
  destruct e1, e2; simpl in *; tcsp.
Qed.
Hint Resolve matching_entries_implies_matching_inf_entries : slow.

Lemma matching_entries_trans {o} :
  forall (e1 e2 e3 : @library_entry o),
    matching_entries e1 e2
    -> matching_entries e2 e3
    -> matching_entries e1 e3.
Proof.
  introv h q; unfold matching_entries in *.
  eapply same_entry_name_trans; eauto.
Qed.
Hint Resolve matching_entries_trans : slow.

Lemma matching_entries_sym {o} :
  forall (e1 e2 : @library_entry o),
    matching_entries e1 e2
    -> matching_entries e2 e1.
Proof.
  introv h; unfold matching_entries in *.
  eapply same_entry_name_sym; eauto.
Qed.
Hint Resolve matching_entries_sym : slow.

Lemma entry_in_inf_library_n_library2inf_implies {o} :
  forall n entry d (lib : @library o),
    entry_in_inf_library_n n entry (library2inf lib d)
    -> entry = d
       \/ exists e, entry_in_library e lib /\ entry = library_entry2inf e.
Proof.
  induction n; introv i; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.

  { unfold library2inf; simpl.
    destruct lib; simpl; tcsp.
    right; exists l; tcsp. }

  destruct lib; simpl in *; autorewrite with slow in *.

  { unfold shift_inf_lib, library2inf in i; simpl in i.
    apply entry_in_inf_library_n_const in i; tcsp. }

  unfold library2inf in i0; simpl in i0.
  apply IHn in i; clear IHn.

  repndors; exrepnd; subst; tcsp.
  right; exists e; dands; tcsp.
  right; dands; auto.
  introv m; apply matching_entries_sym in m; destruct i0; eauto 2 with slow.
Qed.

Lemma implies_safe_inf_library_library2inf {o} :
  forall (lib : @library o) d,
    safe_library lib
    -> safe_inf_library_entry d
    -> safe_inf_library (library2inf lib d).
Proof.
  introv sl sd i.
  unfold entry_in_inf_library in i; repndors; exrepnd.

  - apply entry_in_inf_library_n_library2inf_implies in i0.
    repndors; exrepnd; subst; auto.

    apply sl in i0.
    destruct e; simpl in *; eauto 2 with slow.

  - unfold inf_entry_in_inf_library_cs_default in *; tcsp.

  - unfold inf_entry_in_inf_library_ref_default in *; tcsp.
Qed.
Hint Resolve implies_safe_inf_library_library2inf : slow.

Lemma inf_entry_extends_library_entry2inf {o} :
  forall (entry : @library_entry o),
    inf_entry_extends (library_entry2inf entry) entry.
Proof.
  introv; unfold inf_entry_extends, library_entry2inf.
  destruct entry; tcsp; dands; eauto 3 with slow.
Qed.
Hint Resolve inf_entry_extends_library_entry2inf : slow.

Lemma inf_lib_extends_library2inf {o} :
  forall (lib : @library o) d,
    safe_inf_library_entry d
    -> inf_lib_extends (library2inf lib d) lib.
Proof.
  introv safed.
  split; eauto 2 with slow.

  {
    introv i.
    left.
    exists (length lib).
    induction lib; simpl in *; tcsp.

    repndors; subst; tcsp.

    - left.
      destruct a; simpl; tcsp; dands; auto; eauto 2 with slow.

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
  forall (lib : @library o) (infl : inf_library),
    safe_library lib
    -> inf_lib_extends infl lib
    -> safe_inf_library infl.
Proof.
  introv safe ext.
  dup ext as h.
  destruct h as [ext1 safe1 sub1]; tcsp.
Qed.
Hint Resolve inf_lib_extends_implies_safe_inf_library : slow.

Lemma is_nat_restriction_csc_nat {o} :
  @is_nat_cs_restriction o csc_nat.
Proof.
  introv.
  unfold is_nat_cs_restriction; simpl; dands; tcsp.
Qed.
Hint Resolve is_nat_restriction_csc_nat : slow.

Definition is_nat_choice_sequence_name (n : choice_sequence_name) :=
  match csn_kind n with
  | cs_kind_nat _ => True
  | cs_kind_seq _ => False
  end.

Definition is_seq_choice_sequence_name (n : choice_sequence_name) :=
  match csn_kind n with
  | cs_kind_nat _ => False
  | cs_kind_seq _ => True
  end.

Definition is_this_seq_choice_sequence_name (l : list nat) (n : choice_sequence_name) :=
  csn_kind n = cs_kind_seq l.

Lemma is_nat_choice_sequence_name_cs_kind_nat :
  forall x n,
    is_nat_choice_sequence_name (MkChoiceSequenceName x (cs_kind_nat n)).
Proof.
  introv; simpl; compute; auto.
Qed.
Hint Resolve is_nat_choice_sequence_name_cs_kind_nat : slow.

Lemma is_seq_choice_sequence_name_cs_kind_seq :
  forall x s,
    is_seq_choice_sequence_name (MkChoiceSequenceName x (cs_kind_seq s)).
Proof.
  introv; simpl; compute; auto.
Qed.
Hint Resolve is_seq_choice_sequence_name_cs_kind_seq : slow.

Lemma is_this_seq_choice_sequence_name_cs_kind_seq :
  forall x s,
    is_this_seq_choice_sequence_name s (MkChoiceSequenceName x (cs_kind_seq s)).
Proof.
  introv; simpl; compute; auto.
Qed.
Hint Resolve is_this_seq_choice_sequence_name_cs_kind_seq : slow.

Lemma correct_restriction_csc_nat {o} :
  forall n,
    is_nat_choice_sequence_name n
    -> @correct_cs_restriction o n csc_nat.
Proof.
  introv isn; unfold correct_cs_restriction.
  destruct n as [name kind], kind as [n|seq]; simpl;
    boolvar; dands; introv; tcsp; eauto 3 with slow;
      try (complete (inversion isn)).
Qed.
Hint Resolve correct_restriction_csc_nat : slow.

Lemma cterm_is_nth_natSeq2default {o} :
  forall seq n,
    n < length seq
    -> @cterm_is_nth o (natSeq2default seq n) n seq.
Proof.
  introv len; unfold cterm_is_nth, natSeq2default.
  apply (nth_select1 _ _ 0) in len.
  allrw.
  eexists; dands; eauto.
Qed.
Hint Resolve cterm_is_nth_natSeq2default : slow.

Lemma natSeq2default_eq_zero {o} :
  forall seq n,
    length seq <= n
    -> @natSeq2default o seq n = mkc_zero.
Proof.
  introv len.
  unfold natSeq2default.
  apply nth_select2 in len; allrw; auto.
Qed.
Hint Resolve natSeq2default_eq_zero : slow.

Lemma natSeq2restrictionPred_iff_cterm_is_nth {o} :
  forall n seq v,
    n < length seq
    -> @natSeq2restrictionPred o seq n v <-> cterm_is_nth v n seq.
Proof.
  introv len.
  apply (nth_select1 _ _ 0) in len.
  unfold natSeq2restrictionPred, cterm_is_nth.
  allrw; split; introv h; subst.
  - eexists; dands; eauto.
  - exrepnd; subst; auto.
    rw h1 in len; ginv.
Qed.
Hint Resolve natSeq2restrictionPred_iff_cterm_is_nth : slow.

Lemma natSeq2restrictionPred_iff_is_nat {o} :
  forall seq n v,
    length seq <= n
    -> @natSeq2restrictionPred o seq n v <-> is_nat n v.
Proof.
  introv len.
  unfold natSeq2restrictionPred.
  apply nth_select2 in len; allrw; tcsp.
Qed.
Hint Resolve natSeq2restrictionPred_iff_is_nat : slow.

Lemma correct_restriction_natSeqs2restriction {o} :
  forall n seq,
    is_this_seq_choice_sequence_name seq n
    -> @correct_cs_restriction o n (natSeq2restriction seq).
Proof.
  introv iss; unfold correct_cs_restriction.
  unfold is_this_seq_choice_sequence_name in iss; ginv.
  destruct n as [name kind], kind as [n|s]; simpl in *; ginv;
    dands; introv; tcsp; eauto 3 with slow.
Qed.
Hint Resolve correct_restriction_natSeqs2restriction : slow.

Lemma safe_inf_choice_sequence_entry_simple_inf_choice_seq_entry {o} :
  forall name, @safe_inf_choice_sequence_entry o name (simple_inf_choice_seq_entry name).
Proof.
  introv; unfold safe_inf_choice_sequence_entry; simpl.
  unfold simple_inf_choice_seq_entry; simpl.
  destruct name as [name kind], kind as [n|seq]; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve safe_inf_choice_sequence_entry_simple_inf_choice_seq_entry : slow.

Lemma safe_inf_library_entry_simple_inf_choice_seq {o} :
  forall name, @safe_inf_library_entry o (simple_inf_choice_seq name).
Proof.
  introv; unfold safe_inf_library_entry; simpl; eauto 3 with slow.
Qed.
Hint Resolve safe_inf_library_entry_simple_inf_choice_seq : slow.

Lemma bar_non_empty {o} :
  forall {lib} (bar : @BarLib o lib),
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
  forall {lib} (bar : @BarLib o lib) lib',
    bar_lib_bar bar lib' -> lib_extends lib' lib.
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
  - destruct entry1; simpl in *; repnd; subst; tcsp; ginv.
  - subst; simpl in *; auto.
Qed.
Hint Resolve entry_extends_preserves_matching_entries_left_rev : slow.

Lemma same_restrictions_trans {o} :
  forall (r1 r2 r3 : @ChoiceSeqRestriction o),
    same_restrictions r1 r2
    -> same_restrictions r2 r3
    -> same_restrictions r1 r3.
Proof.
  introv h q; destruct r1, r2, r3; simpl in *; repnd; tcsp; dands; introv.
  { rewrite h0; auto. }
  { rewrite h; auto. }
  { rewrite h; auto. }
Qed.
Hint Resolve same_restrictions_trans : slow.

Lemma same_ref_restrictions_trans {o} :
  forall (r1 r2 r3 : @RefRestriction o),
    same_ref_restrictions r1 r2
    -> same_ref_restrictions r2 r3
    -> same_ref_restrictions r1 r3.
Proof.
  introv h q; destruct r1, r2, r3; simpl in *; repnd; tcsp; dands; introv; subst; auto;[].
  rewrite h; auto.
Qed.
Hint Resolve same_ref_restrictions_trans : slow.

Lemma same_ref_restrictions_sym {o} :
  forall (r1 r2 : @RefRestriction o),
    same_ref_restrictions r1 r2
    -> same_ref_restrictions r2 r1.
Proof.
  introv h; destruct r1, r2; simpl in *; repnd; tcsp; dands; introv; subst; auto;[].
  rewrite h; tcsp.
Qed.
Hint Resolve same_ref_restrictions_sym : slow.

Lemma choice_sequence_entry_extend_trans {o} :
  forall (entry1 entry2 entry3 : @ChoiceSeqEntry o),
    choice_sequence_entry_extend entry1 entry2
    -> choice_sequence_entry_extend entry2 entry3
    -> choice_sequence_entry_extend entry1 entry3.
Proof.
  introv h1 h2; unfold choice_sequence_entry_extend in *.
  repnd; allrw; dands; auto; eauto 3 with slow;[].
  destruct entry1, entry2, entry3; simpl in *.
  unfold choice_sequence_vals_extend in *; exrepnd; subst.
  eexists.
  rewrite <- app_assoc; eauto.
Qed.
Hint Resolve choice_sequence_entry_extend_trans : slow.

Lemma reference_entry_extend_trans {o} :
  forall (entry1 entry2 entry3 : @ReferenceEntry o),
    reference_entry_extend entry1 entry2
    -> reference_entry_extend entry2 entry3
    -> reference_entry_extend entry1 entry3.
Proof.
  introv h1 h2; unfold reference_entry_extend in *.
  repnd; allrw; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve reference_entry_extend_trans : slow.

Lemma reference_entry_extend_sym {o} :
  forall (entry1 entry2 : @ReferenceEntry o),
    reference_entry_extend entry1 entry2
    -> reference_entry_extend entry2 entry1.
Proof.
  introv h; unfold reference_entry_extend in *; eauto 3 with slow.
Qed.
Hint Resolve reference_entry_extend_sym : slow.

Lemma entry_extends_trans {o} :
  forall (entry1 entry2 entry3 : @library_entry o),
    entry_extends entry1 entry2
    -> entry_extends entry2 entry3
    -> entry_extends entry1 entry3.
Proof.
  introv h1 h2; unfold entry_extends in *.
  destruct entry1; simpl in *; tcsp.
  - destruct entry2; simpl in *; repnd; subst; tcsp;
      destruct entry3; simpl in *; repnd; subst; tcsp; ginv.
    dands; auto; eauto 2 with slow.
  - destruct entry2; simpl in *; repnd; subst; tcsp;
      destruct entry3; simpl in *; repnd; subst; tcsp; ginv.
    dands; auto; eauto 2 with slow.
  - destruct entry2; simpl in *; repnd; subst; tcsp;
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
  forall {lib1 lib2 lib3 : @library o},
    lib_extends lib1 lib2
    -> lib_extends lib2 lib3
    -> lib_extends lib1 lib3.
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

Lemma lib_extends_entries_nil_r {o} :
  forall (lib : @library o), lib_extends_entries lib [].
Proof.
  introv i; simpl in *; tcsp.
Qed.
Hint Resolve lib_extends_entries_nil_r : slow.

Lemma lib_extends_nil {o} :
  forall (lib : @library o), safe_library lib -> lib_extends lib [].
Proof.
  introv safe; split; simpl; tcsp; eauto 2 with slow.
Qed.
Hint Resolve lib_extends_nil : slow.

Lemma implies_safe_library_cons {o} :
  forall entry (lib : @library o),
    safe_library_entry entry
    -> safe_library lib
    -> safe_library (entry :: lib).
Proof.
  introv se sl i; simpl in *; repndors; subst; tcsp.
Qed.
Hint Resolve implies_safe_library_cons : slow.

(*Lemma safe_library_cons_iff {o} :
  forall entry (lib : @library o),
    safe_library (entry :: lib) <-> (safe_library_entry entry /\ safe_library lib).
Proof.
  introv; split; intro h; repnd; dands; tcsp.

  - apply h; simpl; tcsp.

  - introv i; apply h; simpl; tcsp.

  - introv i; simpl in *; repndors; subst; tcsp.
Qed.*)

Lemma list_in_snoc :
  forall {A} x (l : list A) a,
    List.In x (snoc l a) <-> (List.In x l \/ x = a).
Proof.
  induction l; introv; simpl in *; split; intro h; repndors; repnd; subst; tcsp.

  - apply IHl in h; repndors; tcsp.

  - right; apply IHl; tcsp.

  - right; apply IHl; tcsp.
Qed.

(*Lemma safe_library_snoc_iff {o} :
  forall e (lib : @library o),
    safe_library (snoc lib e) <-> (safe_library lib /\ safe_library_entry e).
Proof.
  introv; split; intro h; repnd; dands; tcsp.

  - introv i; apply h; apply list_in_snoc; tcsp.

  - apply h; apply list_in_snoc; tcsp.

  - introv i; apply list_in_snoc in i; repndors; subst; tcsp.
Qed.*)

Lemma implies_entry_in_library_snoc {o} :
  forall entry (lib : @library o) e,
    entry_in_library entry lib
    -> entry_in_library entry (snoc lib e).
Proof.
  induction lib; introv i; simpl in *; tcsp.
Qed.
Hint Resolve implies_entry_in_library_snoc : slow.

Definition diff_entry_names {o} (e1 e2 : @library_entry o) : bool :=
  if same_entry_name_dec (entry2name e1) (entry2name e2)
  then false else true.

Definition shadowed_entry {o} (e : @library_entry o) lib :=
  forallb (diff_entry_names e) lib = false.

Definition non_shadowed_entry {o} (e : @library_entry o) lib :=
  forallb (diff_entry_names e) lib = true.

Lemma non_shadowed_entry_nil {o} :
  forall (e : @library_entry o), non_shadowed_entry e [].
Proof.
  introv; unfold non_shadowed_entry; simpl; auto.
Qed.
Hint Resolve non_shadowed_entry_nil : slow.

Lemma non_shadowed_entry_nil_iff {o} :
  forall (e : @library_entry o), non_shadowed_entry e [] <-> True.
Proof.
  introv; unfold non_shadowed_entry; simpl; split; intro h; tcsp.
Qed.
Hint Rewrite @non_shadowed_entry_nil_iff : slow.

Lemma shadowed_entry_nil_iff {o} :
  forall (e : @library_entry o), shadowed_entry e [] <-> False.
Proof.
  introv; unfold shadowed_entry; simpl; split; intro h; tcsp.
Qed.
Hint Rewrite @shadowed_entry_nil_iff : slow.

Lemma matching_entries_iff_diff_entry_names_false {o} :
  forall (e1 e2 : @library_entry o),
    matching_entries e1 e2 <-> diff_entry_names e1 e2 = false.
Proof.
  introv; unfold matching_entries, diff_entry_names.
  boolvar; split; intro h; tcsp.
Qed.

Lemma non_matching_entries_iff_diff_entry_names_true {o} :
  forall (e1 e2 : @library_entry o),
    ~ matching_entries e1 e2 <-> diff_entry_names e1 e2 = true.
Proof.
  introv; unfold matching_entries, diff_entry_names.
  boolvar; split; intro h; tcsp.
Qed.

Lemma non_shadowed_entry_cons {o} :
  forall (e a : @library_entry o) lib,
    non_shadowed_entry e (a :: lib)
    <-> (~matching_entries e a /\ non_shadowed_entry e lib).
Proof.
  introv; unfold non_shadowed_entry; simpl.
  rewrite andb_true_iff.
  rewrite non_matching_entries_iff_diff_entry_names_true; tcsp.
Qed.
Hint Rewrite @non_shadowed_entry_cons : slow.

Lemma shadowed_entry_cons {o} :
  forall (e a : @library_entry o) lib,
    shadowed_entry e (a :: lib)
    <-> (matching_entries e a \/ shadowed_entry e lib).
Proof.
  introv; unfold shadowed_entry; simpl.
  rewrite andb_false_iff.
  rewrite matching_entries_iff_diff_entry_names_false; tcsp.
Qed.
Hint Rewrite @shadowed_entry_cons : slow.

Lemma entry_in_library_snoc_implies {o} :
  forall entry (lib : @library o) e,
    entry_in_library entry (snoc lib e)
    -> entry_in_library entry lib
       \/
       (
         entry = e
         /\
         non_shadowed_entry entry lib
       ).
Proof.
  induction lib; introv i; simpl in *; repndors; repnd; subst; tcsp.

  - right; dands; eauto 2 with slow.

  - apply IHlib in i; repndors; repnd; subst; tcsp.
    allrw @non_shadowed_entry_cons; tcsp.
Qed.

(*Lemma entry_in_library_snoc_implies {o} :
  forall entry (lib : @library o) e,
    entry_in_library entry (snoc lib e)
    -> entry_in_library entry lib \/ entry = e.
Proof.
  induction lib; introv i; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.
  apply IHlib in i; repndors; tcsp.
Qed.*)

Lemma implies_safe_library_snoc {o} :
  forall e (lib : @library o),
    safe_library lib
    -> (non_shadowed_entry e lib -> safe_library_entry e)
    -> safe_library (snoc lib e).
Proof.
  introv safe1 safe2 i.
  apply entry_in_library_snoc_implies in i; repndors; repnd; subst; tcsp.
Qed.
Hint Resolve implies_safe_library_snoc : slow.

Lemma inf_lib_extends_snoc_implies_head {o} :
  forall infLib (lib : @library o) e,
    (non_shadowed_entry e lib -> safe_library_entry e)
    -> inf_lib_extends infLib (snoc lib e)
    -> inf_lib_extends infLib lib.
Proof.
  introv safee i.
  destruct i as [ext safe].
  split.

  - introv i; apply ext; eauto 2 with slow.

  - introv safel.
    apply safe; eauto 2 with slow.
Qed.
Hint Resolve inf_lib_extends_snoc_implies_head : slow.

Lemma safe_library_snoc_implies_head {o} :
  forall (lib : @library o) e,
    safe_library (snoc lib e)
    -> safe_library lib.
Proof.
  introv safe i; apply safe; eauto 2 with slow.
Qed.
Hint Resolve safe_library_snoc_implies_head : slow.

Lemma implies_inf_lib_extends_snoc {o} :
  forall (infLib : @inf_library o) lib e k,
    inf_lib_extends infLib lib
    -> entry_in_inf_library_extends e k infLib
    -> inf_lib_extends infLib (snoc lib e).
Proof.
  introv ext i.
  destruct ext as [ext safe].
  split; eauto 2 with slow.

  - introv j; apply entry_in_library_snoc_implies in j; repndors; repnd; subst; tcsp.
    left; exists k; auto.

  - introv safe'; apply safe; eauto 2 with slow.
Qed.
Hint Resolve implies_inf_lib_extends_snoc : slow.

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
    -> shadowed_entry e lib
    -> entry_in_library entry lib.
Proof.
  induction lib; introv i h; simpl in *; autorewrite with slow in *; tcsp.
  repndors; repnd; subst; tcsp.

  - right; dands; auto.
    apply entry_in_library_snoc_implies in i; repndors; repnd; subst; tcsp.

  - apply IHlib in h; auto.
Qed.
Hint Resolve entry_in_library_snoc_shadowed_implies : slow.

Lemma implies_inf_lib_extends_snoc_shadowed {o} :
  forall (infLib : @inf_library o) lib e,
    inf_lib_extends infLib lib
    -> shadowed_entry e lib
    -> inf_lib_extends infLib (snoc lib e).
Proof.
  introv ext i.
  destruct ext as [ext safe].
  split; eauto 2 with slow.

  - introv j.
    apply entry_in_library_snoc_shadowed_implies in j; auto.

  - introv safe'; apply safe; eauto 2 with slow.
Qed.
Hint Resolve implies_inf_lib_extends_snoc_shadowed : slow.

Lemma entry_extends_preserves_forallb_diff_entry_names_false {o} :
  forall (e1 e2 : @library_entry o) lib,
    entry_extends e1 e2
    -> shadowed_entry e2 lib
    -> shadowed_entry e1 lib.
Proof.
  induction lib; introv ext h; simpl in *; tcsp.
  autorewrite with slow in *; repndors; tcsp.
  left; eauto 2 with slow.
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
    non_shadowed_entry e lib
    -> entry_in_library_extends e (snoc lib e).
Proof.
  induction lib; introv h; simpl in *; autorewrite with slow in *; tcsp; GC.
  left; eauto 2 with slow.
Qed.
Hint Resolve implies_entry_in_library_extends_tail_if_all_diff : slow.

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
    non_shadowed_entry e lib
    -> entry_in_library e (snoc lib e).
Proof.
  introv h.
  apply entry_in_library_snoc_tail.
  introv i.
  unfold non_shadowed_entry in h.
  rewrite forallb_forall in h; auto.
Qed.
Hint Resolve entry_in_library_snoc_tail2 : slow.

Lemma safe_library_snoc_implies {o} :
  forall (lib : @library o) (e : library_entry),
    safe_library (snoc lib e)
    ->
    (
      safe_library lib
      /\
      (non_shadowed_entry e lib -> safe_library_entry e)
    ).
Proof.
  introv safe; dands; eauto 2 with slow.
  introv nsh.
  apply safe; eauto 2 with slow.
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

Lemma lib_extends_entries_preserves_non_shadowed_entry {o} :
  forall (e : @library_entry o) lib1 lib2,
    lib_extends_entries lib2 lib1
    -> non_shadowed_entry e lib2
    -> non_shadowed_entry e lib1.
Proof.
  introv ext h.
  unfold non_shadowed_entry in *.
  allrw @forallb_forall.
  introv i.

  match goal with
  | [ |- ?x = _ ] => remember x as b; destruct b; symmetry in Heqb; auto
  end.
  assert False; tcsp.

  allrw <- @matching_entries_iff_diff_entry_names_false.
  eapply in_implies_entry_in_library in i;[|apply matching_entries_sym;eauto].
  exrepnd.

  apply ext in i1.
  apply entry_in_library_extends_implies_entry_in_library in i1.
  exrepnd.
  pose proof (h entry') as q; autodimp q hyp; eauto 2 with slow.

  eapply entry_extends_implies_matching_entries_right in i2;
    [|apply matching_entries_sym;eauto].
  apply matching_entries_sym in i2.

  apply non_matching_entries_iff_diff_entry_names_true in q; destruct q.
  eauto 3 with slow.
Qed.
Hint Resolve lib_extends_entries_preserves_non_shadowed_entry : slow.

Lemma lib_extends_preserves_non_shadowed_entry {o} :
  forall (e : @library_entry o) lib1 lib2,
    lib_extends lib2 lib1
    -> non_shadowed_entry e lib2
    -> non_shadowed_entry e lib1.
Proof.
  introv ext nsh; destruct ext as [ext safe sub]; eauto 2 with slow.
Qed.
Hint Resolve lib_extends_preserves_non_shadowed_entry : slow.

Lemma implies_lib_extends_snoc_lr_if_all_diff {o} :
  forall (lib lib1 : @library o) e,
    lib_extends lib lib1
    -> non_shadowed_entry e lib
    -> lib_extends (snoc lib e) (snoc lib1 e).
Proof.
  introv ext allt.
  destruct ext as [ext safe sub].
  split; simpl.

  - introv i.
    apply entry_in_library_snoc_implies in i; repndors; repnd; subst; eauto 2 with slow.
    apply ext in i; eauto 2 with slow.

  - introv safe1.
    apply safe_library_snoc_implies in safe1; repnd.
    apply implies_safe_library_snoc; repnd; dands; auto.
    introv i; apply safe1; GC; eauto 2 with slow.

  - introv i; allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; allrw @list_in_snoc; tcsp.

    + exists e; allrw @list_in_snoc; dands; tcsp; eauto 2 with slow.
Qed.
Hint Resolve implies_lib_extends_snoc_lr_if_all_diff : slow.

Lemma implies_lib_extends_snoc_left {o} :
  forall e (lib lib2 : @library o),
    (non_shadowed_entry e lib -> safe_library_entry e)
    -> lib_extends lib lib2
    -> lib_extends (snoc lib e) lib2.
Proof.
  introv safee ext.
  destruct ext as [ext safe sub].
  split; simpl.

  - introv i.
    apply ext in i; eauto 2 with slow.

  - introv safe1.
    apply implies_safe_library_snoc; auto.

  - introv i.
    apply sub in i; exrepnd.
    exists entry2; allrw @list_in_snoc; tcsp.
Qed.
Hint Resolve implies_lib_extends_snoc_left : slow.

Lemma non_shadowed_and_in_library_implies_non_matching {o} :
  forall e entry (lib : @library o),
    non_shadowed_entry e lib
    -> entry_in_library entry lib
    -> ~ matching_entries entry e.
Proof.
  introv nsh i m.
  unfold non_shadowed_entry in nsh.
  rewrite forallb_forall in nsh.
  apply entry_in_library_implies_in in i.
  apply nsh in i.
  apply non_matching_entries_iff_diff_entry_names_true in i.
  apply matching_entries_sym in m; tcsp.
Qed.
Hint Resolve non_shadowed_and_in_library_implies_non_matching : slow.

Lemma implies_lib_extends_cons_left_snoc_right {o} :
  forall e (lib : @library o) lib1,
    non_shadowed_entry e lib1
    -> lib_extends lib lib1
    -> lib_extends (e :: lib) (snoc lib1 e).
Proof.
  introv allt ext.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_implies in i; repndors; repnd; subst; simpl; eauto 2 with slow.
    applydup ext in i.
    right; dands; eauto 2 with slow.

  - introv safe1.
    apply safe_library_snoc_implies in safe1; repnd.
    apply implies_safe_library_cons; auto.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; dands; tcsp.

    + exists e; dands; tcsp; eauto 2 with slow.
Qed.
Hint Resolve implies_lib_extends_cons_left_snoc_right : slow.

Lemma implies_lib_extends_cons_left {o} :
  forall e (lib lib2 : @library o),
    lib_extends lib lib2
    -> safe_library_entry e
    -> non_shadowed_entry e lib2
    -> lib_extends (e :: lib) lib2.
Proof.
  introv ext safee allt.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    applydup ext in i; right; dands; auto.
    introv m.
    unfold non_shadowed_entry in allt; rewrite forallb_forall in allt.
    pose proof (allt entry) as q.
    apply matching_entries_sym in m.
    apply matching_entries_iff_diff_entry_names_false in m.
    rewrite m in q.
    autodimp q hyp; eauto 2 with slow.

  - introv safe1.
    apply implies_safe_library_cons; auto.

  - introv i; simpl.
    apply sub in i; exrepnd.
    exists entry2; tcsp.
Qed.
Hint Resolve implies_lib_extends_cons_left : slow.

Lemma lib_extends_snoc_lr_if_all_diff_false {o} :
  forall e (lib lib1 : @library o),
    lib_extends lib lib1
    -> shadowed_entry e lib1
    -> lib_extends (snoc lib e) (snoc lib1 e).
Proof.
  introv ext allt.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i; auto.
    apply ext in i.
    apply implies_entry_in_library_extends_snoc; auto.

  - introv safe1.
    apply safe_library_snoc_implies in safe1; repnd.
    apply implies_safe_library_snoc; auto.
    introv nsh; apply safe1; eauto 2 with slow.

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

Lemma inf_library_extends_implies {o} :
  forall (e : @library_entry o) n inflib,
    entry_in_inf_library_extends e n inflib
    -> exists k,
        k < n
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
        n < n1
        /\ n < n2
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

  - exists k0; dands; auto; try omega.

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

Lemma same_restrictions_sym {o} :
  forall (r1 r2 : @ChoiceSeqRestriction o),
    same_restrictions r1 r2
    -> same_restrictions r2 r1.
Proof.
  introv same; destruct r1, r2; simpl in *; repnd; dands; tcsp.
  introv; symmetry; auto.
Qed.
Hint Resolve same_restrictions_sym : slow.

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
    [| |assert (correct1 = correct0) as xx by (apply correct_abs_proof_irrelevance); subst;
        assert (correct0 = correct) as xx by (apply correct_abs_proof_irrelevance); subst;
        exists (lib_abs opabs1 vars1 rhs1 correct); dands; unfold entry_extends; auto];[|].

  {
    destruct entry as [vals restr].
    destruct entry0 as [vals1 restr1].
    destruct entry1 as [vals2 restr2].
    unfold inf_choice_sequence_entry_extend in *; simpl in *.
    repnd; repeat subst.
    unfold inf_choice_sequence_vals_extend in *.

    exists (lib_cs name1 (MkChoiceSeqEntry _ (combine_choice_seq_vals vals1 vals2) restr2)).
    simpl; dands; auto; unfold choice_sequence_entry_extend; simpl; dands; auto;
      unfold choice_sequence_vals_extend; eauto 3 with slow;[|].

    - eapply exists_combine_choice_seq_vals_1; eauto.

    - eapply exists_combine_choice_seq_vals_2; eauto.
  }

  {
    exists (lib_ref name1 entry); dands; simpl; auto.
  }
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
    [| |assert (correct1 = correct0) as xx by (apply correct_abs_proof_irrelevance); subst;
        assert (correct0 = correct) as xx by (apply correct_abs_proof_irrelevance); subst;
        exists (lib_abs opabs1 vars1 rhs1 correct); dands; unfold entry_extends; auto];[|].

  {
    destruct entry as [vals restr].
    destruct entry0 as [vals1 restr1].
    destruct entry1 as [vals2 restr2].
    unfold inf_choice_sequence_entry_extend in *; simpl in *.
    repnd; repeat subst.
    unfold inf_choice_sequence_vals_extend in *.

    exists (lib_cs name1 (MkChoiceSeqEntry _ (combine_choice_seq_vals vals1 vals2) restr2)).
    simpl; dands; auto; unfold choice_sequence_entry_extend; simpl; dands; auto;
      unfold choice_sequence_vals_extend; eauto 3 with slow;[| |].

    - eapply exists_combine_choice_seq_vals_1; eauto.

    - eapply exists_combine_choice_seq_vals_2; eauto.

    - introv i; apply select_combine_choice_seq_vals_implies_or in i; repndors; tcsp.
  }

  {
    exists (lib_ref name1 entry); dands; simpl; auto; eauto 3 with slow.
  }
Qed.

Lemma lib_extends_cons_snoc_diff {o} :
  forall e a (lib lib1 : @library o),
    entry_extends e a
    -> (safe_library_entry a -> safe_library_entry e)
    -> non_shadowed_entry a lib1
    -> lib_extends lib lib1
    -> lib_extends (e :: lib) (snoc lib1 a).
Proof.
  introv exte safee allt ext.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_implies in i; repndors; repnd; subst; tcsp.
    applydup ext in i.
    right; dands; auto.
    introv m.
    eapply entry_extends_implies_matching_entries in exte;
      [|apply matching_entries_sym;eauto].
    eapply matching_entries_trans in exte;[|eauto].
    unfold non_shadowed_entry in allt; rewrite forallb_forall in allt.
    apply entry_in_library_implies_in in i.
    apply allt in i.
    apply matching_entries_sym in exte.
    apply matching_entries_iff_diff_entry_names_false in exte.
    rewrite exte in i; ginv.

  - introv safe1.
    apply safe_library_snoc_implies in safe1; repnd.
    apply implies_safe_library_cons; auto.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; dands; auto.

    + exists e; dands; eauto 2 with slow.
Qed.
Hint Resolve lib_extends_cons_snoc_diff : slow.

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

Lemma same_restrictions_preserves_is_nat_restriction {o} :
  forall (r1 r2 : @ChoiceSeqRestriction o),
    same_restrictions r1 r2
    -> is_nat_cs_restriction r1
    -> is_nat_cs_restriction r2.
Proof.
  introv same isn; unfold is_nat_cs_restriction in *.
  destruct r1, r2; simpl in *; repnd; dands; introv; tcsp;
    try (complete (rewrite <- same0; auto));
    try (complete (rewrite <- same; auto)).
Qed.
Hint Resolve same_restrictions_preserves_is_nat_restriction : slow.

Lemma same_restrictions_preserves_is_nat_seq_restriction {o} :
  forall seq (r1 r2 : @ChoiceSeqRestriction o),
    same_restrictions r1 r2
    -> is_nat_seq_restriction seq r1
    -> is_nat_seq_restriction seq r2.
Proof.
  introv same isn; unfold is_nat_seq_restriction in *.
  destruct r1, r2; simpl in *; repnd; dands; tcsp; introv len;
    try (complete (rewrite <- same0; auto));
    try (complete (rewrite <- same; auto)).
Qed.
Hint Resolve same_restrictions_preserves_is_nat_seq_restriction : slow.

Lemma same_restrictions_preserves_correct_restriction {o} :
  forall (r1 r2 : @ChoiceSeqRestriction o) name,
    same_restrictions r1 r2
    -> correct_cs_restriction name r1
    -> correct_cs_restriction name r2.
Proof.
  introv same cor.
  destruct name as [name kind]; simpl in *.
  destruct kind as [n|seq]; simpl in *;
    unfold correct_cs_restriction in *; simpl in *; boolvar; subst; eauto 3 with slow.
Qed.
Hint Resolve same_restrictions_preserves_correct_restriction : slow.

Lemma same_ref_restrictions_preserve_correct_ref_restriction {o} :
  forall name (restr1 restr2 : @RefRestriction o),
    same_ref_restrictions restr1 restr2
    -> correct_ref_restriction name restr1
    -> correct_ref_restriction name restr2.
Proof.
  introv same cor.
  unfold same_ref_restrictions in *.
  unfold correct_ref_restriction in *.
  destruct name as [nm kind]; simpl in *.
  destruct kind; simpl in *; boolvar; subst; auto.
  destruct restr1; simpl in *; repnd; subst.
  destruct restr2; simpl in *; repnd; subst.
  dands; auto; introv.
  rw <- same; auto.
Qed.
Hint Resolve same_ref_restrictions_preserve_correct_ref_restriction : slow.

(* This is not true for references because the infinite library might contain
   a different value than the entry, which does not ensure that the entry is safe *)

(*Lemma inf_entry_extends_preserves_safe_library_entry {o} :
  forall (inf_entry : @inf_library_entry o) entry,
    inf_entry_extends inf_entry entry
    -> safe_inf_library_entry inf_entry
    -> safe_library_entry entry.
Proof.
  introv ext safe; destruct inf_entry, entry; simpl in *; simpl in *; tcsp.

  {
    repnd; subst.
    destruct entry0 as [vals1 restr1].
    destruct entry as [vals2 restr2].
    simpl in *.
    unfold inf_choice_sequence_entry_extend in *; simpl in *; repnd; subst.
    unfold inf_choice_sequence_satisfies_restriction in safe.
    unfold inf_choice_sequence_vals_extend in *.
    unfold choice_sequence_satisfies_restriction.
    destruct restr2; simpl in *; repnd; dands; tcsp; eauto 3 with slow;[|].

    - introv i.
      destruct restr1; simpl in *; repnd; tcsp.
      rewrite <- ext0.
      apply ext in i; subst; tcsp.

    - introv j.
      destruct restr1; simpl in *; repnd; tcsp.
      rewrite <- ext0.
      pose proof (nth_select1 i vals2 mkc_axiom j) as q.
      rewrite q.
      apply ext in q.
      rewrite <- q.
      rewrite safe; auto.
  }

  {
    repnd; subst; auto; GC.
    destruct entry0 as [v1 restr1]; simpl in *; repnd.
    destruct entry as [v2 restr2]; simpl in *; repnd.
    unfold reference_entry_extend in *; simpl in *.
    dands; eauto 3 with slow.

XXXXXX
    unfold same_ref_restrictions in *.
    destrucft ref_
    unfold safe_reference_entry.
Qed.
Hint Resolve inf_entry_extends_preserves_safe_library_entry : slow.*)

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
  forall (e e' : @library_entry o) (lib lib2 : @library o),
    lib_extends lib lib2
    -> entry_extends e e'
    -> entry_in_library e' lib2
    -> (safe_library_entry e' -> safe_library_entry e)
    -> lib_extends (e :: lib) lib2.
Proof.
  introv ext exte ei safee.
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
    apply implies_safe_library_cons; dands; auto.

  - introv i; simpl.
    apply sub in i; exrepnd.
    exists entry2; dands; auto.
Qed.
Hint Resolve implies_lib_extends_cons_left_if_extends : slow.

Lemma implies_lib_extends_cons_snoc_left_if_extends {o} :
  forall e e' a (lib lib2 : @library o),
    lib_extends lib lib2
    -> entry_extends e e'
    -> entry_in_library e' lib2
    -> (safe_library_entry e' -> safe_library_entry e)
    -> (non_shadowed_entry a (e :: lib) -> safe_library_entry a)
    -> lib_extends (e :: snoc lib a) lib2.
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
    apply (implies_safe_library_snoc _ (e :: lib)); auto.
    apply implies_safe_library_cons; dands; auto.

  - introv i; simpl.
    apply sub in i; exrepnd.
    exists entry2; dands; auto.
    rewrite list_in_snoc; tcsp.
Qed.
Hint Resolve implies_lib_extends_cons_snoc_left_if_extends : slow.

Lemma matching_entries_implies_not_non_shadowed_entry {o} :
  forall a e (lib : @library o),
    matching_entries a e
    -> ~ non_shadowed_entry a (e :: lib).
Proof.
  introv m nsh.
  unfold non_shadowed_entry in nsh.
  rewrite forallb_forall in nsh; simpl in nsh.
  pose proof (nsh e) as q; clear nsh; autodimp q hyp.
  apply non_matching_entries_iff_diff_entry_names_true in q; tcsp.
Qed.

Lemma lib_extends_cons_snoc_if_in {o} :
  forall e e1 a (lib lib1 : @library o),
    (safe_library_entry e1 -> safe_library_entry e)
    -> matching_entries a e1
    -> entry_extends e e1
    -> entry_in_library e1 lib1
    -> lib_extends lib lib1
    -> lib_extends (e :: snoc lib a) (snoc lib1 a).
Proof.
  introv safee m exte ei ext.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i;
      [|unfold shadowed_entry; rewrite forallb_false;
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
    apply safe_library_snoc_implies in safe1; repnd.
    apply (implies_safe_library_snoc _ (e :: lib)); dands.

    { apply implies_safe_library_cons; auto. }

    introv nsh; apply matching_entries_implies_not_non_shadowed_entry in nsh; tcsp.
    eapply entry_extends_implies_matching_entries_right in exte;[|apply matching_entries_sym;eauto].
    apply matching_entries_sym in exte; eauto 2 with slow.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    { apply sub in i; exrepnd.
      exists entry2; dands; auto.
      rewrite list_in_snoc; tcsp. }

    { exists a.
      rewrite list_in_snoc; dands; tcsp; eauto 2 with slow. }
Qed.
Hint Resolve lib_extends_cons_snoc_if_in : slow.

Lemma implies_entry_in_inf_library_n {o} :
  forall k n (infLib : @inf_library o),
    n < k
    -> (forall m, m < n -> ~ matching_inf_entries (infLib m) (infLib n))
    -> entry_in_inf_library_n k (infLib n) infLib.
Proof.
  induction k; introv ltnk imp; simpl in *; try omega.
  destruct n; simpl; tcsp.
  right; dands; auto.

  { apply imp; omega. }

  apply (IHk n (fun n => infLib (S n))); try omega.
  introv ltmn; apply imp; omega.
Qed.
Hint Resolve implies_entry_in_inf_library_n : slow.

Lemma implies_entry_in_inf_library {o} :
  forall n (infLib : @inf_library o),
    (forall m, m < n -> ~ matching_inf_entries (infLib m) (infLib n))
    -> entry_in_inf_library (infLib n) infLib.
Proof.
  introv imp.
  left; exists (S n).
  apply implies_entry_in_inf_library_n; auto.
Qed.
Hint Resolve implies_entry_in_inf_library : slow.

Lemma matching_inf_entries_preserves_inf_matching_entries {o} :
  forall ie1 ie2 (e : @library_entry o),
    inf_matching_entries ie1 e
    -> matching_inf_entries ie2 ie1
    -> inf_matching_entries ie2 e.
Proof.
  introv im mi.
  unfold inf_matching_entries in *; simpl in *.
  unfold matching_inf_entries in *; simpl in *.
  destruct ie1, ie2, e; simpl in *; tcsp; ginv.
  eapply same_opabs_trans;eauto.
Qed.
Hint Resolve matching_inf_entries_preserves_inf_matching_entries : slow.

Lemma is_cs_default_entry_implies_matching_entries_sym {o} :
  forall (e1 e2 : @library_entry o),
    is_cs_default_entry e1
    -> matching_entries e1 e2
    -> matching_entries e2 e1.
Proof.
  destruct e1, e2; introv h q; simpl in *; repnd; tcsp;
    unfold matching_entries in *; simpl in *; subst; auto.
Qed.

Lemma is_ref_default_entry_implies_matching_entries_sym {o} :
  forall (e1 e2 : @library_entry o),
    is_ref_default_entry e1
    -> matching_entries e1 e2
    -> matching_entries e2 e1.
Proof.
  destruct e1, e2; introv h q; simpl in *; repnd; tcsp;
    unfold matching_entries in *; simpl in *; subst; auto.
Qed.

Lemma matching_entries_preserves_entry_in_inf_library_cs_default {o} :
  forall (e1 e2 : @library_entry o) n infLib,
    matching_entries e1 e2
    -> entry_in_inf_library_cs_default e1 infLib
    -> ~ entry_in_inf_library_extends e2 n infLib.
Proof.
  introv m h q.
  unfold entry_in_inf_library_cs_default in *; repnd.
  apply inf_library_extends_implies in q; exrepnd.
  pose proof (h0 k) as h0.
  eapply inf_entry_extends_implies_inf_matching_entries in q2;
    [|eapply is_cs_default_entry_implies_matching_entries_sym; eauto].
  eapply matching_entries_preserves_inf_matching_entries in q2;
    [|eapply is_cs_default_entry_implies_matching_entries_sym; eauto].
  tcsp.
Qed.

Lemma matching_entries_preserves_entry_in_inf_library_ref_default {o} :
  forall (e1 e2 : @library_entry o) n infLib,
    matching_entries e1 e2
    -> entry_in_inf_library_ref_default e1 infLib
    -> ~ entry_in_inf_library_extends e2 n infLib.
Proof.
  introv m h q.
  unfold entry_in_inf_library_ref_default in *; repnd.
  apply inf_library_extends_implies in q; exrepnd.
  pose proof (h0 k) as h0.
  eapply inf_entry_extends_implies_inf_matching_entries in q2;
    [|eapply is_ref_default_entry_implies_matching_entries_sym; eauto];[].
  eapply matching_entries_preserves_inf_matching_entries in q2;
    [|eapply is_ref_default_entry_implies_matching_entries_sym; eauto];[].
  tcsp.
Qed.

Definition csc_seq {o} (l : list nat) : @ChoiceSeqRestriction o :=
  csc_type (natSeq2default l) (natSeq2restrictionPred l) (natSeq2default_restr l).

Definition choice_sequence_name2restriction {o} (name : choice_sequence_name) : @ChoiceSeqRestriction o :=
  match csn_kind name with
  | cs_kind_nat n => csc_nat
  | cs_kind_seq l => csc_seq l
  end.

Definition choice_sequence_name2inf_choice_seq_vals {o} (name : choice_sequence_name) : @InfChoiceSeqVals o :=
  match csn_kind name with
  | cs_kind_nat n => fun _ => mkc_zero
  | cs_kind_seq l => natSeq2default l
  end.

Definition choice_sequence_name2inf_choice_seq_entry {o} (name : choice_sequence_name) : @InfChoiceSeqEntry o :=
  MkInfChoiceSeqEntry
    _
    (choice_sequence_name2inf_choice_seq_vals name)
    (choice_sequence_name2restriction name).

Definition choice_sequence_name2inf_entry {o} (name : choice_sequence_name) : @inf_library_entry o :=
  inf_lib_cs name (choice_sequence_name2inf_choice_seq_entry name).

Definition reference_name2ref_entry {o} (name : reference_name) : @ReferenceEntry o :=
  MkReferenceEntry _ mkc_zero rr_nat.

Definition reference_name2inf_entry {o} (name : reference_name) : @inf_library_entry o :=
  inf_lib_ref name (reference_name2ref_entry name).

Definition reference_name2entry {o} (name : reference_name) : @library_entry o :=
  lib_ref name (reference_name2ref_entry name).

Definition mk_ref_inf_entry {o} (name : reference_name) a restr : @inf_library_entry o :=
  inf_lib_ref name (MkReferenceEntry _ a restr).

Definition mk_ref_entry {o} (name : reference_name) a restr : @library_entry o :=
  lib_ref name (MkReferenceEntry _ a restr).

Lemma correct_restriction_choice_sequence_name2restriction {o} :
  forall name, @correct_cs_restriction o name (choice_sequence_name2restriction name).
Proof.
  introv.
  unfold correct_cs_restriction; destruct name as [name k]; simpl; auto.
  destruct k; simpl; auto.

  - boolvar; auto; dands; tcsp.

  - dands; introv len; tcsp; eauto 3 with slow.
Qed.
Hint Resolve correct_restriction_choice_sequence_name2restriction : slow.

Lemma inf_choice_sequence_satisfies_restrictionchoice_sequence_name2inf {o} :
  forall name,
    @inf_choice_sequence_satisfies_restriction
      o
      (choice_sequence_name2inf_choice_seq_vals name)
      (choice_sequence_name2restriction name).
Proof.
  introv.
  unfold inf_choice_sequence_satisfies_restriction.
  unfold choice_sequence_name2restriction.
  destruct name as [name k]; simpl.
  destruct k as [n|seq]; simpl; introv;
    unfold choice_sequence_name2inf_choice_seq_vals;
    simpl; eauto 3 with slow.
Qed.
Hint Resolve inf_choice_sequence_satisfies_restrictionchoice_sequence_name2inf : slow.

Lemma safe_inf_library_entry_choice_sequence_name2inf_entry {o} :
  forall name, @safe_inf_library_entry o (choice_sequence_name2inf_entry name).
Proof.
  introv.
  unfold safe_inf_library_entry; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve safe_inf_library_entry_choice_sequence_name2inf_entry : slow.

Lemma is_default_inf_choice_sequence_choice_sequence_name2inf {o} :
  forall name,
    @is_default_inf_choice_sequence
      o
      (choice_sequence_name2inf_choice_seq_vals name)
      (choice_sequence_name2restriction name).
Proof.
  introv.
  unfold is_default_inf_choice_sequence; simpl.
  unfold choice_sequence_name2restriction.
  destruct name as [name k]; simpl.
  destruct k; simpl; introv; simpl; eauto 3 with slow.
Qed.
Hint Resolve is_default_inf_choice_sequence_choice_sequence_name2inf : slow.

Lemma is_cs_default_inf_entry_choice_sequence_name2inf_entry {o} :
  forall name,
    is_nat_or_seq_kind name
    -> @is_cs_default_inf_entry o (choice_sequence_name2inf_entry name).
Proof.
  introv ins.
  unfold is_cs_default_inf_entry; simpl.
  dands; eauto 3 with slow.
Qed.
Hint Resolve is_cs_default_inf_entry_choice_sequence_name2inf_entry : slow.

Lemma inf_entry_in_inf_library_default_choice_sequence_name2inf_entry {o} :
  forall name (inflib : @inf_library o),
    is_nat_or_seq_kind name
    -> ~ (exists n, same_entry_name (inf_entry2name (inflib n)) (entry_name_cs name))
    -> inf_entry_in_inf_library_cs_default (choice_sequence_name2inf_entry name) inflib.
Proof.
  introv ins h.
  unfold inf_entry_in_inf_library_cs_default; dands; eauto 3 with slow;[].
  introv x; destruct h; exists n; auto.
Qed.
Hint Resolve inf_entry_in_inf_library_default_choice_sequence_name2inf_entry : slow.

Hint Resolve select_lt : slow.

Lemma is_default_choice_seq_entry_implies_extends {o} :
  forall name (e : @ChoiceSeqEntry o),
    is_default_choice_seq_entry e
    -> is_nat_or_seq_kind name
    -> safe_choice_sequence_entry name e
    -> inf_entry_extends (choice_sequence_name2inf_entry name) (lib_cs name e).
Proof.
  introv h isn safe.
  unfold inf_entry_extends.
  destruct name as [name k]; simpl in *; dands; auto.
  unfold inf_choice_sequence_entry_extend; simpl.
  unfold safe_choice_sequence_entry in safe.
  unfold choice_sequence_name2restriction; simpl.
  unfold is_default_choice_seq_entry in h.
  destruct e as [vals restr]; simpl in *; repnd.
  unfold correct_cs_restriction in *; simpl in *.
  destruct k as [n|seq]; simpl in *; boolvar; subst; tcsp;[|].

  - destruct restr in *; simpl in *; tcsp; repnd.
    dands; tcsp.
    { introv; symmetry; eauto. }
    unfold choice_sequence_name2inf_choice_seq_vals; simpl.
    unfold inf_choice_sequence_vals_extend; introv x.
    applydup h in x; subst.
    rewrite safe1; auto.

  - destruct restr in *; simpl in *; tcsp; repnd.
    dands; tcsp.

    { introv; unfold natSeq2default.
      remember (select n seq) as x; symmetry in Heqx; destruct x.
      - pose proof (safe1 n) as q; autodimp q hyp; eauto 3 with slow.
        unfold cterm_is_nth in q; exrepnd.
        rewrite Heqx in q1; ginv.
      - rewrite safe2; auto; eauto 3 with slow.
        apply nth_select2; auto. }

    { introv; unfold natSeq2restrictionPred.
      remember (select n seq) as x; symmetry in Heqx; destruct x.
      - pose proof (safe3 n v) as q; autodimp q hyp; eauto 3 with slow.
        rewrite q; clear q; split; intro w; subst.
        + pose proof (safe1 n) as w; autodimp w hyp; eauto 3 with slow.
          unfold cterm_is_nth in *; exrepnd.
          rewrite Heqx in w1; ginv.
          rewrite Heqx.
          eexists; dands; eauto.
        + unfold cterm_is_nth in w; exrepnd; subst.
          rewrite Heqx in w1; ginv.
      - rewrite safe0; eauto 3 with slow; tcsp.
        apply nth_select2; auto. }

    { unfold inf_choice_sequence_vals_extend; introv w; simpl.
      unfold choice_sequence_name2inf_choice_seq_vals; simpl.
      unfold natSeq2default.
      applydup h in w; subst.
      remember (select n seq) as x; symmetry in Heqx; destruct x.
      - pose proof (safe1 n) as q; autodimp q hyp; eauto 3 with slow.
        unfold cterm_is_nth in q; exrepnd.
        rewrite Heqx in q1; ginv.
      - rewrite safe2; auto; eauto 3 with slow.
        apply nth_select2; auto. }
Qed.
Hint Resolve is_default_choice_seq_entry_implies_extends : slow.

Definition choice_sequence_name2choice_seq_entry {o} (name : choice_sequence_name) : @ChoiceSeqEntry o :=
  MkChoiceSeqEntry
    _
    []
    (choice_sequence_name2restriction name).

Definition choice_sequence_name2entry {o} (name : choice_sequence_name) : @library_entry o :=
  lib_cs name (choice_sequence_name2choice_seq_entry name).

Fixpoint ntimes {T} (n : nat) (t : T) : list T :=
  match n with
  | 0 => []
  | S n => t :: ntimes n t
  end.

Fixpoint fun2list {T} n (f : nat -> T) : list T :=
  match n with
  | 0 => []
  | S m => snoc (fun2list m f) (f m)
  end.

Definition choice_sequence_name2choice_seq_vals_upto {o} n (name : choice_sequence_name) : @ChoiceSeqVals o :=
  match csn_kind name with
  | cs_kind_nat _ => fun2list n (fun _ => mkc_zero)
  | cs_kind_seq l => fun2list n (natSeq2default l)
  end.

Definition choice_sequence_name2choice_seq_entry_upto {o}
           (n     : nat)
           (name  : choice_sequence_name)
           (restr : ChoiceSeqRestriction) : @ChoiceSeqEntry o :=
  MkChoiceSeqEntry
    _
    (choice_sequence_name2choice_seq_vals_upto n name)
    restr (*(choice_sequence_name2restriction name)*).

Definition choice_sequence_name2entry_upto {o}
           (n     : nat)
           (name  : choice_sequence_name)
           (restr : ChoiceSeqRestriction) : @library_entry o :=
  lib_cs name (choice_sequence_name2choice_seq_entry_upto n name restr).

Lemma entry_in_inf_library_cs_default_two_matching_entries {o} :
  forall (e1 e2 : @library_entry o) inflib,
    matching_entries e1 e2
    -> entry_in_inf_library_cs_default e1 inflib
    -> entry_in_inf_library_cs_default e2 inflib
    -> exists name e,
        entry2name e1 = entry_name_cs name
        /\ e = choice_sequence_name2inf_entry name
        /\ inf_entry_extends e e1
        /\ inf_entry_extends e e2.
Proof.
  introv m h q.
  unfold entry_in_inf_library_cs_default in *; exrepnd.
  destruct e1 as [name1 e1|name1 e1|], e2 as [name2 e2|name2 e2|]; simpl in *;tcsp;repnd;GC;
    try (complete (unfold matching_entries in *; simpl in *; tcsp)).

  assert (name1 = name2) as eqn by tcsp.

  exists name1 (@choice_sequence_name2inf_entry o name1).
  dands; eauto 3 with slow.
  subst; eauto 3 with slow.
Qed.

Lemma inf_entry_extends_reference_name2inf_entry {o} :
  forall name (e : @ReferenceEntry o),
    is_nat_ref_kind name
    -> safe_reference_entry name e
    -> is_default_ref_entry e
    -> inf_entry_extends (reference_name2inf_entry name) (lib_ref name e).
Proof.
  introv isn safe isd.
  unfold inf_entry_extends; simpl; dands; eauto 3 with slow.
  unfold is_default_ref_entry in *.
  destruct e; simpl in *; repnd.
  unfold reference_entry_extend; simpl.
  destruct ref_restriction; simpl in  *; subst.
  unfold correct_ref_restriction in *.
  destruct name as [name kind]; simpl in *.
  unfold is_nat_ref_kind in *; simpl in *.
  destruct kind; subst; simpl in *; repnd; dands; auto.
  introv; rw safe0; tcsp.
Qed.
Hint Resolve inf_entry_extends_reference_name2inf_entry : slow.

Lemma inf_entry_extends_reference_name2inf_entry_lib_ref {o} :
  forall name (e : @ReferenceEntry o),
    safe_reference_entry name e
    -> is_nat_ref_kind name
    -> inf_entry_extends (reference_name2inf_entry name) (lib_ref name e).
Proof.
  introv safe isn.
  unfold inf_entry_extends; simpl; dands; auto.
  unfold reference_entry_extend; simpl.
  destruct e as [v restr]; simpl in *; repnd.
  destruct restr; simpl in *.
  unfold correct_ref_restriction in *.
  unfold is_nat_ref_kind in *.
  destruct name as [name kind]; simpl in *.
  destruct kind; simpl in *; subst; simpl in *; repnd; dands; tcsp.
  introv; rw safe0; tcsp.
Qed.
Hint Resolve inf_entry_extends_reference_name2inf_entry_lib_ref : slow.

Lemma entry_in_inf_library_ref_default_two_matching_entries {o} :
  forall (e1 e2 : @library_entry o) inflib,
    matching_entries e1 e2
    -> entry_in_inf_library_ref_default e1 inflib
    -> entry_in_inf_library_ref_default e2 inflib
    -> exists (name : reference_name) (e : @inf_library_entry o) (v : @CTerm o),
        entry2name e1 = entry_name_ref name
        /\ e = mk_ref_inf_entry name v rr_nat
        /\ inf_entry_extends e e1
        /\ inf_entry_extends e e2.
Proof.
  introv m h q.
  unfold entry_in_inf_library_ref_default in *; exrepnd.
  destruct e1 as [name1 e1|name1 e1|], e2 as [name2 e2|name2 e2|]; simpl in *;tcsp;repnd;GC;
    try (complete (unfold matching_entries in *; simpl in *; tcsp)).

  assert (name1 = name2) as eqn by tcsp; subst.

  exists name2 (@reference_name2inf_entry o name2) (@mkc_zero o).
  dands; eauto 3 with slow.
Qed.

Lemma select_implies_eq_lists :
  forall {A} (l1 l2 : list A),
    length l1 = length l2
    -> (forall n, select n l1 = select n l2)
    -> l1 = l2.
Proof.
  induction l1; introv h q; simpl in *; cpx.
  destruct l2; simpl in *; cpx.
  pose proof (q 0) as w; simpl in *; ginv.
  f_equal.
  apply IHl1; auto.
  introv; apply (q (S n)).
Qed.

Lemma length_fun2list :
  forall {A} n (f : nat -> A),
    length (fun2list n f) = n.
Proof.
  induction n; introv; simpl; auto.
  rewrite length_snoc.
  rewrite IHn; auto.
Qed.
Hint Rewrite @length_fun2list : slow.

Lemma fun2list_lt0 :
  forall {A} n (f : nat -> A),
    0 < n -> fun2list n f = f 0 :: fun2list (pred n) (fun m => f (S m)).
Proof.
  induction n; introv lt0; simpl in *; try omega.
  destruct (lt_dec 0 n).
  - rewrite IHn; auto; simpl.
    f_equal.
    destruct n; simpl; auto; try omega.
  - destruct n; try omega; simpl; auto.
Qed.

Lemma select_fun2list :
  forall {A} n m (f : nat -> A),
    select n (fun2list m f) = if lt_dec n m then Some (f n) else None.
Proof.
  induction n; introv; simpl; boolvar.

  - rewrite fun2list_lt0; auto.

  - assert (m = 0) by omega; subst; simpl; auto.

  - rewrite fun2list_lt0; auto; try omega.
    rewrite IHn; boolvar; try omega; auto.

  - destruct (lt_dec 0 m).
    + rewrite fun2list_lt0; auto; simpl.
      apply nth_select2; autorewrite with slow; omega.
    + assert (m = 0) by omega; subst; simpl; auto.
Qed.

Lemma select_none :
  forall {A} n (l : list A), length l <= n -> select n l = None.
Proof.
  introv h.
  apply nth_select2; auto.
Qed.
Hint Resolve select_none : slow.

Lemma entry_in_inf_library_cs_default_implies_exists {o} :
  forall (e : @library_entry o) inflib,
    entry_in_inf_library_cs_default e inflib
    ->
    exists name n restr,
      is_nat_or_seq_kind name
      /\ entry2name e = entry_name_cs name
      /\ e = choice_sequence_name2entry_upto n name restr
      /\ correct_cs_restriction name restr.
Proof.
  introv h.
  unfold entry_in_inf_library_cs_default in *; exrepnd.
  destruct e as [name e| |]; simpl in *;tcsp;repnd;[].
  destruct e as [vals restr]; simpl in *; repnd.

  exists name (length vals) restr; dands; auto.
  unfold choice_sequence_name2entry_upto; simpl.
  unfold choice_sequence_name2choice_seq_entry_upto; simpl.
  f_equal; f_equal.

  unfold choice_sequence_name2choice_seq_vals_upto.
  destruct name as [name k]; simpl; auto; simpl in *.
  unfold correct_cs_restriction in *; simpl in *.
  destruct k as [n|seq]; simpl in *; boolvar; subst; tcsp.

  - destruct restr; simpl in *; tcsp; repnd.
    apply select_implies_eq_lists; autorewrite with slow; auto.
    introv.

    rewrite select_fun2list; boolvar;[|apply nth_select2; try omega].
    apply (nth_select1 _ _ mkc_zero) in l.
    unfold ChoiceSeqVal; rewrite l.
    apply h in l; rewrite l.
    rewrite h4; auto.

  - destruct restr; simpl in *; tcsp; repnd.
    apply select_implies_eq_lists; autorewrite with slow; auto.
    introv.

    rewrite select_fun2list; boolvar;[|apply nth_select2; try omega].
    unfold natSeq2default.
    apply (nth_select1 _ _ mkc_zero) in l.
    unfold ChoiceSeqVal; rewrite l.
    apply h in l; rewrite l.
    remember (select n seq) as s; symmetry in Heqs; destruct s.

    + pose proof (h4 n) as q; autodimp q hyp; eauto 3 with slow.
      unfold cterm_is_nth in q; exrepnd; allrw.
      rewrite q1 in *; ginv.

    + pose proof (h5 n) as q; autodimp q hyp;[apply nth_select2; auto|].
      allrw; auto.
Qed.

Lemma matching_entries_choice_sequence_name2entry_implies {o} :
  forall (e : @library_entry o) n name restr,
    matching_entries e (choice_sequence_name2entry_upto n name restr)
    -> entry2name e = entry_name_cs name.
Proof.
  introv m.
  unfold matching_entries in m; simpl in *.
  destruct e; simpl in *; tcsp; subst; auto.
Qed.
Hint Resolve matching_entries_choice_sequence_name2entry_implies : slow.

Lemma entry_in_inf_library_ref_default_implies_exists {o} :
  forall (e : @library_entry o) inflib,
    entry_in_inf_library_ref_default e inflib
    ->
    exists (name : reference_name) (restr : @RefRestriction o) v,
      is_nat_ref_kind name
      /\ entry2name e = entry_name_ref name
      /\ e = mk_ref_entry name v restr
      /\ correct_ref_restriction name restr.
Proof.
  introv h.
  unfold entry_in_inf_library_ref_default in *; exrepnd.
  destruct e as [|name e|]; simpl in *;tcsp;repnd;[].
  destruct e as [v restr]; simpl in *; repnd.

  exists name restr v; dands; auto.
Qed.

Lemma entry_in_inf_library_cs_ref_default_matching_false {o} :
  forall (e1 e2 : @library_entry o) infLib,
    entry_in_inf_library_cs_default e1 infLib
    -> entry_in_inf_library_ref_default e2 infLib
    -> matching_entries e1 e2
    -> False.
Proof.
  introv i j m.
  unfold entry_in_inf_library_cs_default in *.
  unfold entry_in_inf_library_ref_default in *.
  destruct e1, e2; tcsp.
Qed.

Lemma entry_in_inf_library_cs_default_implies_exists2 {o} :
  forall infLib (lib : @library o) e,
    inf_lib_extends infLib lib
    -> forallb (diff_entry_names e) lib = false
    -> entry_in_inf_library_cs_default e infLib
    ->
    exists name n restr,
      is_nat_or_seq_kind name
      /\ entry2name e = entry_name_cs name
      /\ entry_in_library (choice_sequence_name2entry_upto n name restr) lib
      /\ correct_cs_restriction name restr.
Proof.
  introv ext allf i.
  allrw @forallb_false; exrepnd.
  apply matching_entries_iff_diff_entry_names_false in allf0.

  eapply in_implies_entry_in_library in allf1;
    [|apply matching_entries_sym;eauto].
  exrepnd.
  applydup ext in allf1.
  repndors; exrepnd.

  { eapply matching_entries_preserves_entry_in_inf_library_cs_default in i;
      [apply i in allf4;tcsp|]; eauto 3 with slow. }

  { apply entry_in_inf_library_cs_default_implies_exists in allf3; exrepnd; subst.
    simpl in *; GC.
    eapply matching_entries_trans in allf2;[|exact allf0].
    exists name n restr; dands; auto; eauto 3 with slow. }

  { eapply matching_entries_trans in allf2;[|eauto].
    eapply entry_in_inf_library_cs_ref_default_matching_false in allf3; eauto; tcsp. }
Qed.

Lemma correct_restriction_implies_same_restrictions {o} :
  forall (r1 r2 : @ChoiceSeqRestriction o) (name : choice_sequence_name),
    is_nat_or_seq_kind name
    -> correct_cs_restriction name r1
    -> correct_cs_restriction name r2
    -> same_restrictions r1 r2.
Proof.
  introv ins cora corb.
  unfold correct_cs_restriction in *.
  unfold is_nat_or_seq_kind in *.
  unfold same_restrictions.
  destruct name as [name k]; simpl in *.
  destruct k as [n|seq]; simpl in *; boolvar; tcsp; subst; GC;[|].

  - unfold is_nat_cs_restriction in *.
    destruct r1, r2; simpl in *; repnd; dands; introv; allrw; tcsp.

  - unfold is_nat_seq_restriction in *.
    destruct r1, r2; simpl in *; repnd; dands; introv; tcsp.

    { destruct (le_dec (length seq) n).
      - rw cora1; auto.
        rw corb1; auto.
      - pose proof (cora0 n) as q; autodimp q hyp; try omega.
        pose proof (corb0 n) as h; autodimp h hyp; try omega.
        unfold cterm_is_nth in *; exrepnd.
        rw q1 in h1; ginv. }

    { destruct (le_dec (length seq) n).
      - rw cora; auto.
        rw corb; tcsp.
      - pose proof (cora2 n v) as q; autodimp q hyp; try omega.
        pose proof (corb2 n v) as h; autodimp h hyp; try omega.
        allrw; tcsp. }
Qed.
Hint Resolve correct_restriction_implies_same_restrictions : slow.

Hint Rewrite Nat.add_0_r : nat.
Hint Rewrite minus0 : nat.

Lemma fun2list_eta :
  forall {A} n (f g : nat -> A),
    (forall m, m < n -> f m = g m)
    -> fun2list n f = fun2list n g.
Proof.
  induction n; introv h; simpl in *; auto.
  f_equal; eauto.
Qed.

Lemma fun2list_lt0_snoc :
  forall {A} n (f : nat -> A),
    0 < n -> fun2list n f = snoc (fun2list (pred n) f) (f (pred n)).
Proof.
  destruct n; simpl; introv lt0; try omega; auto.
Qed.

Lemma pred_sub_add_succ :
  forall n m,
    0 < n - m
    -> pred (n - m) + S m = n.
Proof.
  introv ltn; omega.
Qed.

Lemma fun2list_split :
  forall {A} n m (f : nat -> A),
    m <= n
    -> fun2list n f
       = fun2list m f ++ fun2list (n - m) (fun k => f (k + m)).
Proof.
  induction n; introv ltn; simpl; autorewrite with slow nat.

  { assert (m = 0) by omega; subst; simpl; auto. }

  destruct m; simpl; autorewrite with slow nat.

  { f_equal; apply fun2list_eta; introv q; autorewrite with slow nat; auto. }

  rewrite (IHn m); try omega; clear IHn.
  rewrite <- snoc_append_l.
  rewrite snoc_append_r.
  f_equal.

  destruct (lt_dec 0 (n - m)) as [d|d].

  { rewrite fun2list_lt0 at 1; auto; simpl.
    f_equal.
    rewrite (fun2list_lt0_snoc (n - m)); auto; simpl.
    rewrite pred_sub_add_succ; auto.
    f_equal.
    apply fun2list_eta; introv q; autorewrite with slow nat; auto. }

  assert (n - m = 0) as xx by omega; rewrite xx; simpl; auto.
  assert (n = m) as xxx by omega; subst; auto.
Qed.

Lemma entry_extends_choice_sequence_name2entry_upto {o} :
  forall n m name (restr1 restr2 : @ChoiceSeqRestriction o),
    m <= n
    -> same_restrictions restr1 restr2
    -> entry_extends
         (choice_sequence_name2entry_upto n name restr1)
         (choice_sequence_name2entry_upto m name restr2).
Proof.
  introv ltn same.
  unfold entry_extends; simpl; dands; auto.
  unfold choice_sequence_entry_extend; simpl; dands; auto.
  unfold choice_sequence_vals_extend.
  unfold choice_sequence_name2choice_seq_vals_upto.
  destruct name as [name k], k as [k|seq]; simpl.

  - exists (fun2list (n - m) (fun _ => @mkc_zero o)).
    apply fun2list_split; auto.

  - exists (fun2list (n - m) (fun k => @natSeq2default o seq (k + m))).
    apply fun2list_split; auto.
Qed.
Hint Resolve entry_extends_choice_sequence_name2entry_upto : slow.

Hint Resolve Max.le_max_l : slow.
Hint Resolve Max.le_max_r : slow.

Lemma is_nat_natSeq2default {o} :
  forall n seq, @is_nat o n (natSeq2default seq n).
Proof.
  introv.
  unfold is_nat, natSeq2default.
  rewrite mkc_zero_eq.
  remember (select n seq) as x; symmetry in Heqx; destruct x; simpl; eexists; eauto.
Qed.
Hint Resolve is_nat_natSeq2default : slow.

Lemma safe_library_entry_choice_sequence_name2entry_upto {o} :
  forall n name (restr : @ChoiceSeqRestriction o),
    is_nat_or_seq_kind name
    -> correct_cs_restriction name restr
    -> safe_library_entry (choice_sequence_name2entry_upto n name restr).
Proof.
  introv ins cor.
  unfold safe_library_entry; simpl; dands; auto.
  unfold choice_sequence_satisfies_restriction.
  unfold correct_cs_restriction in *.
  unfold is_nat_or_seq_kind in *.
  destruct name as [name k], k as [k|seq]; simpl in *; boolvar; subst; tcsp; GC;[|].

  - destruct restr; simpl in *; tcsp; repnd.
    introv h.
    unfold choice_sequence_name2choice_seq_vals_upto in *; simpl in *.
    rewrite select_fun2list in h; boolvar; tcsp; ginv.
    allrw; eauto 3 with slow.

  - destruct restr; simpl in *; tcsp; repnd.
    introv h.
    unfold choice_sequence_name2choice_seq_vals_upto in *; simpl in *.
    rewrite select_fun2list in h; boolvar; tcsp; ginv.
    destruct (lt_dec n0 (length seq)) as [xx|xx].
    { apply cor2; auto; eauto 3 with slow. }
    { apply cor; eauto 3 with slow; try omega. }
Qed.
Hint Resolve safe_library_entry_choice_sequence_name2entry_upto : slow.

Lemma matching_entries_preserve_forallb_diff_entry_names_false {o} :
  forall (e1 e2 : @library_entry o) lib,
    matching_entries e2 e1
    -> forallb (diff_entry_names e2) lib = false
    -> forallb (diff_entry_names e1) lib = false.
Proof.
  introv m h.
  allrw @forallb_false; exrepnd.
  exists x; dands; eauto 3 with slow.
  allrw <- @matching_entries_iff_diff_entry_names_false.
  eauto 3 with slow.
Qed.
Hint Resolve matching_entries_preserve_forallb_diff_entry_names_false : slow.

Lemma safe_library_entry_implies_safe_inf_library_entry {o} :
  forall infLib n (e : @library_entry o),
    safe_inf_library infLib
    -> inf_matching_entries (infLib n) e
    -> (forall m, m < n -> ~ inf_matching_entries (infLib m) e)
    -> safe_inf_library_entry (infLib n).
Proof.
  introv safe m d.
  apply safe.
  unfold entry_in_inf_library; left.
  exists (S n).
  apply implies_entry_in_inf_library_n; auto.
  introv h q; apply d in h; clear d; destruct h; eauto 3 with slow.
Qed.
Hint Resolve safe_library_entry_implies_safe_inf_library_entry : slow.


(*
Lemma safe_inf_library_entry_implies_safe_library_entry {o} :
  forall ie (e : @library_entry o),
    inf_entry_extends ie e
    -> safe_inf_library_entry ie
    -> safe_library_entry e.
Proof.
  introv ext safe.
  destruct ie, e; simpl in *; repnd; subst; tcsp.

  {
    unfold inf_choice_sequence_entry_extend in *; repnd.
    destruct entry as [e1 restr1], entry0 as [e2 restr2]; simpl in *; repnd.
    dands; eauto 3 with slow.
    destruct restr1, restr2; simpl in *; tcsp; repnd.

    - introv h; apply ext0.
      apply ext in h; subst; auto.

    - introv h; dup h as len.
      apply (nth_select1 _ _ mkc_zero) in h.
      apply ext in h.
      rewrite safe in h; rewrite ext0 in h; rewrite h.
      apply nth_select1; auto.
  }

  {
    unfold reference_entry_extend in *.
    destruct entry as [e1 restr1], entry0 as [e2 restr2]; simpl in *; repnd.
    dands; eauto 3 with slow.
    destruct restr1, restr2; simpl in *; repnd; subst; tcsp.
    apply ext.

  }
Qed.
*)

Lemma lt_length_combine_choice_seq_vals_implies {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) i,
    i < length (combine_choice_seq_vals vals1 vals2)
    ->
    (
      i < length vals1
      /\ select i (combine_choice_seq_vals vals1 vals2) = select i vals1
    )
    \/
    (
      length vals1 <= i
      /\ i < length vals2
      /\ select i (combine_choice_seq_vals vals1 vals2) = select i vals2
    ).
Proof.
  induction vals1; introv h; simpl in *; tcsp.

  - autorewrite with nat; right; dands; auto; try omega.

  - destruct vals2; simpl in *; tcsp.

    destruct i; simpl.

    + left; dands; tcsp; try omega.

    + apply S_lt_inj in h.
      apply IHvals1 in h; repndors; repnd; tcsp.

      * left; dands; auto; try omega.

      * right; dands; auto; try omega.
Qed.

Lemma implies_choice_sequence_satisfies_restriction {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) restr1 restr2,
    choice_sequence_satisfies_restriction vals1 restr1
    -> choice_sequence_satisfies_restriction vals2 restr2
    -> same_restrictions restr1 restr2
    -> choice_sequence_satisfies_restriction (combine_choice_seq_vals vals1 vals2) restr1.
Proof.
  introv sat1 sat2 same.
  destruct restr1, restr2; simpl in *; tcsp; repnd.

  - introv h.
    apply select_combine_choice_seq_vals_implies_or in h; repndors; eauto;[].
    apply sat2 in h; apply same; auto.

  - introv h.
    apply lt_length_combine_choice_seq_vals_implies in h; repndors; repnd; rewrite h.
    { apply sat1; auto. }
    { rewrite same; apply sat2; auto. }
Qed.

Lemma implies_choice_sequence_satisfies_restriction2 {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) restr1 restr2,
    choice_sequence_satisfies_restriction vals1 restr1
    -> choice_sequence_satisfies_restriction vals2 restr2
    -> same_restrictions restr1 restr2
    -> choice_sequence_satisfies_restriction (combine_choice_seq_vals vals1 vals2) restr2.
Proof.
  introv sat1 sat2 same.
  destruct restr1, restr2; simpl in *; tcsp; repnd.

  - introv h.
    apply select_combine_choice_seq_vals_implies_or in h; repndors; eauto;[].
    apply same; apply sat1; auto.

  - introv h.
    apply lt_length_combine_choice_seq_vals_implies in h; repndors; repnd; rewrite h.
    { rewrite <- same; apply sat1; auto. }
    { apply sat2; auto. }
Qed.

Lemma inf_entry_extends_two_entries_implies_entry_extends_safe {o} :
  forall (ie : @inf_library_entry o) e1 e2,
    safe_library_entry e1
    -> safe_library_entry e2
    -> inf_entry_extends ie e1
    -> inf_entry_extends ie e2
    ->
    exists e,
      entry_extends e e1
      /\ entry_extends e e2
      /\ inf_entry_extends ie e
      /\ safe_library_entry e.
Proof.
  destruct ie, e1, e2; introv safee1 safee2 ext1 ext2; simpl in *; repnd; repeat (subst; tcsp);
    [| |assert (correct1 = correct0) as xx by (apply correct_abs_proof_irrelevance); subst;
        assert (correct0 = correct) as xx by (apply correct_abs_proof_irrelevance); subst;
        exists (lib_abs opabs1 vars1 rhs1 correct); dands; unfold entry_extends; auto];[|].

  {
    destruct entry as [vals restr].
    destruct entry0 as [vals1 restr1].
    destruct entry1 as [vals2 restr2].
    unfold inf_choice_sequence_entry_extend in *; simpl in *.
    repnd; repeat subst.
    unfold inf_choice_sequence_vals_extend in *.

    exists (lib_cs name1 (MkChoiceSeqEntry _ (combine_choice_seq_vals vals1 vals2) restr2)).
    simpl; dands; auto; unfold choice_sequence_entry_extend; simpl; dands; auto;
      unfold choice_sequence_vals_extend; eauto 3 with slow;[| | |].

    - eapply exists_combine_choice_seq_vals_1; eauto.

    - eapply exists_combine_choice_seq_vals_2; eauto.

    - introv i; apply select_combine_choice_seq_vals_implies_or in i; repndors; tcsp.

    - eapply implies_choice_sequence_satisfies_restriction2; eauto; eauto 3 with slow.
  }

  {
    exists (lib_ref name1 entry0); dands; simpl; auto; dands; eauto 3 with slow.
  }
Qed.

Lemma same_entry_name_entry_name_ref_left_implies_eq :
  forall n name,
    same_entry_name n (entry_name_ref name)
    -> n = entry_name_ref name.
Proof.
  introv h.
  destruct n; simpl in *; subst; tcsp.
Qed.
Hint Resolve same_entry_name_entry_name_ref_left_implies_eq : slow.

Lemma entry_in_inf_library_ref_default_implies_exists2 {o} :
  forall infLib (lib : @library o) e,
    inf_lib_extends infLib lib
    -> forallb (diff_entry_names e) lib = false
    -> entry_in_inf_library_ref_default e infLib
    ->
    exists name restr v,
      is_nat_ref_kind name
      /\ entry2name e = entry_name_ref name
      /\ entry_in_library (mk_ref_entry name v restr) lib
      /\ correct_ref_restriction name restr.
Proof.
  introv ext allf i.
  allrw @forallb_false; exrepnd.
  apply matching_entries_iff_diff_entry_names_false in allf0.

  eapply in_implies_entry_in_library in allf1;
    [|apply matching_entries_sym;eauto].
  exrepnd.
  applydup ext in allf1.
  repndors; exrepnd.

  { eapply matching_entries_preserves_entry_in_inf_library_ref_default in i;
      [apply i in allf4;tcsp|]; eauto 3 with slow. }

  { eapply matching_entries_trans in allf2;[|eauto].
    eapply entry_in_inf_library_cs_ref_default_matching_false in allf3; eauto; tcsp.
    eauto 3 with slow. }

  { apply entry_in_inf_library_ref_default_implies_exists in allf3; exrepnd; subst.
    simpl in *; GC.
    eapply matching_entries_trans in allf2;[|exact allf0].
    exists name restr v; dands; auto; eauto 3 with slow. }
Qed.

Lemma correct_ref_restriction_implies_same_ref_restrictions {o} :
  forall (r1 r2 : @RefRestriction o) (name : reference_name),
    is_nat_ref_kind name
    -> correct_ref_restriction name r1
    -> correct_ref_restriction name r2
    -> same_ref_restrictions r1 r2.
Proof.
  introv ins cora corb.
  unfold correct_ref_restriction in *.
  unfold is_nat_ref_kind in *.
  unfold same_ref_restrictions.
  destruct name as [name k]; simpl in *.
  destruct k as [n]; simpl in *; boolvar; tcsp; subst; GC;[].

  unfold is_nat_ref_restriction in *.
  destruct r1, r2; simpl in *; repnd; dands; introv; allrw; tcsp.
Qed.
Hint Resolve correct_ref_restriction_implies_same_ref_restrictions : slow.

Lemma entry_extends_lib_ref {o} :
  forall name (a b : @CTerm o) r1 r2,
    same_ref_restrictions r1 r2
    -> entry_extends
         (mk_ref_entry name a r1)
         (mk_ref_entry name b r2).
Proof.
  introv same.
  unfold mk_ref_entry, entry_extends; dands; auto.
Qed.
Hint Resolve entry_extends_lib_ref : slow.

Lemma intersect_inf_lib_extends {o} :
  forall infLib (lib1 lib2 : @library o),
    safe_library lib1
    -> safe_library lib2
    -> inf_lib_extends infLib lib1
    -> inf_lib_extends infLib lib2
    -> exists lib,
        lib_extends lib lib1
        /\ lib_extends lib lib2.
Proof.
  induction lib1 using rev_list_ind; introv safe1 safe2 ext1 ext2; simpl in *.

  - exists lib2; dands; eauto 2 with slow.

  - apply safe_library_snoc_implies in safe1; repnd.
    pose proof (IHlib1 lib2) as q; repeat (autodimp q hyp); eauto 2 with slow;[].
    exrepnd.

    remember (forallb (diff_entry_names a) lib) as b; symmetry in Heqb; destruct b.

    + (* [a] is not in [lib] *)

      exists (snoc lib a); dands; eauto 4 with slow.

    + (* [a] is in [lib] *)

      remember (forallb (diff_entry_names a) lib2) as w; symmetry in Heqw; destruct w.

      * (* [a] is not in [lib2] *)

        remember (forallb (diff_entry_names a) lib1) as z; symmetry in Heqz; destruct z.

        { (* [a] is not in [lib1] *)

          exists (a :: lib); dands; eauto 4 with slow.
        }

        { (* [a] is in [lib1] *)

          exists (snoc lib a); dands; eauto 4 with slow.
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

          pose proof (inf_lib_extends_ext _ _ ext1 a) as q.
          autodimp q hyp; exrepnd; eauto 2 with slow;[].
          pose proof (inf_lib_extends_ext _ _ ext2 e') as w.
          autodimp w hyp; exrepnd.

          repndors; exrepnd.

          {
            pose proof (inf_library_extends_two_matching_entries a e' n0 n infLib) as h.
            repeat (autodimp h hyp).
            { eapply matching_entries_trans; eauto. }
            exrepnd.

            assert (safe_library_entry a) as safea by eauto 3 with slow.
            assert (safe_library_entry e') as safee' by eauto 3 with slow.
            assert (safe_inf_library infLib) as safeil by eauto 2 with slow.
            assert (safe_inf_library_entry (infLib n1)) as safeie.
            { eapply safe_library_entry_implies_safe_inf_library_entry; eauto.
              eapply inf_entry_extends_implies_inf_matching_entries; eauto. }

            pose proof (inf_entry_extends_two_entries_implies_entry_extends_safe (infLib n1) a e') as q.
            repeat (autodimp q hyp); exrepnd.

            exists (e :: lib); dands; eauto 2 with slow.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in w0;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in q;
              [apply q in w0|]; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in q2;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            pose proof (entry_in_inf_library_cs_default_implies_exists2 infLib lib2 a) as z.
            repeat (autodimp z hyp); exrepnd.
            apply entry_in_inf_library_cs_default_implies_exists in q.
            exrepnd.
            rewrite q4 in z2; ginv; simpl in *.
            exists ((choice_sequence_name2entry_upto (Peano.max n n0) name restr) :: lib); dands; eauto 5 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in q2;
              tcsp; eauto; eauto 3 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            pose proof (entry_in_inf_library_ref_default_implies_exists2 infLib lib2 a) as z.
            repeat (autodimp z hyp); exrepnd.
            apply entry_in_inf_library_ref_default_implies_exists in q.
            exrepnd.
            rewrite q4 in z2; ginv; simpl in *.
            exists ((mk_ref_entry name v restr)
                      :: lib); dands; eauto 5 with slow.
          }
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

          pose proof (inf_lib_extends_ext _ _ ext1 e1) as q.
          autodimp q hyp; exrepnd; eauto 2 with slow;[].
          pose proof (inf_lib_extends_ext _ _ ext2 e2) as w.
          autodimp w hyp; exrepnd.

          repndors; exrepnd.

          {
            pose proof (inf_library_extends_two_matching_entries e1 e2 n0 n infLib) as h.
            repeat (autodimp h hyp).
            { eapply matching_entries_trans; eauto.
              apply matching_entries_sym; auto. }
            exrepnd.

            assert (safe_library_entry e1) as safee1 by eauto 3 with slow.
            assert (safe_library_entry e2) as safee2 by eauto 3 with slow.
            assert (safe_inf_library infLib) as safeil by eauto 2 with slow.
            assert (safe_inf_library_entry (infLib n1)) as safeie.
            { eapply safe_library_entry_implies_safe_inf_library_entry; eauto.
              eapply inf_entry_extends_implies_inf_matching_entries; eauto.
              eauto 3 with slow. }

            pose proof (inf_entry_extends_two_entries_implies_entry_extends_safe (infLib n1) e1 e2) as q.
            repeat (autodimp q hyp); exrepnd.

            exists (e :: snoc lib a); dands; eauto 5 with slow.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in w0;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in q;
              [apply q in w0|]; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in q2;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            pose proof (entry_in_inf_library_cs_default_implies_exists e2 infLib) as z.
            repeat (autodimp z hyp); exrepnd; eauto 3 with slow.

            pose proof (entry_in_inf_library_cs_default_implies_exists e1 infLib) as u.
            repeat (autodimp u hyp); exrepnd; eauto 3 with slow.

            assert (same_entry_name (entry2name e1) (entry2name e2)) as xx by eauto 3 with slow.
            rewrite z2 in xx; rewrite u2 in xx; simpl in xx; subst.

            exists ((choice_sequence_name2entry_upto (Peano.max n n0) name restr) :: snoc lib a); dands; eauto 3 with slow.
            { eapply lib_extends_cons_snoc_if_in; try exact in1lib1; eauto 3 with slow. }
            { eapply implies_lib_extends_cons_left_if_extends; try exact in2lib1; eauto 4 with slow. }
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in w;
              tcsp; eauto; eauto 3 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            pose proof (entry_in_inf_library_ref_default_implies_exists2 infLib lib2 e2) as z.
            repeat (autodimp z hyp); exrepnd; eauto 3 with slow.

            assert (same_entry_name (entry2name e1) (entry2name e2)) as xx by eauto 3 with slow.

            apply entry_in_inf_library_ref_default_implies_exists in w.
            exrepnd; subst; ginv; simpl in *.

            apply entry_in_inf_library_ref_default_implies_exists in q.
            exrepnd; subst; ginv; simpl in *.

            subst.

            exists ((mk_ref_entry name v restr)
                      :: snoc lib a); dands; eauto 3 with slow.
            { eapply lib_extends_cons_snoc_if_in; try exact in1lib1; eauto 3 with slow. }
            { eapply implies_lib_extends_cons_left_if_extends; try exact in2lib1; eauto 4 with slow. }
          }
        }
Qed.

Lemma inf_lib_extends_snoc_implies_entry_ext {o} :
  forall infLib (lib : @library o) e,
    non_shadowed_entry e lib
    -> inf_lib_extends infLib (snoc lib e)
    -> (exists k, entry_in_inf_library_extends e k infLib)
       \/ entry_in_inf_library_cs_default e infLib
       \/ entry_in_inf_library_ref_default e infLib.
Proof.
  introv allt ext.
  destruct ext as [ext safe].
  pose proof (ext e) as q; autodimp q hyp; eauto 2 with slow.
Qed.

Lemma forallb_diff_entry_names_false_implies_exists_entry {o} :
  forall e (lib : @library o),
    shadowed_entry e lib
    ->
    exists a,
      entry_in_library a lib
      /\ matching_entries a e.
Proof.
  introv allt.
  unfold shadowed_entry in allt; rewrite forallb_false in allt; exrepnd.
  rewrite <- matching_entries_iff_diff_entry_names_false in allt0.
  eapply in_implies_entry_in_library in allt1;[|apply matching_entries_sym;eauto].
  exrepnd.
  exists e'; dands; auto.
  apply matching_entries_sym; eapply matching_entries_trans; eauto.
Qed.

Lemma inf_lib_extends_snoc_implies_entry_ext2 {o} :
  forall infLib (lib : @library o) e,
    shadowed_entry e lib
    -> inf_lib_extends infLib (snoc lib e)
    -> (exists a k,
           matching_entries a e
           /\ entry_in_library a lib
           /\ entry_in_inf_library_extends a k infLib)
       \/ (exists a,
              entry_in_library a lib
              /\ matching_entries a e
              /\ entry_in_inf_library_cs_default a infLib)
       \/ (exists a,
              entry_in_library a lib
              /\ matching_entries a e
              /\ entry_in_inf_library_ref_default a infLib).
Proof.
  introv allt ext.
  destruct ext as [ext safe].
  applydup @forallb_diff_entry_names_false_implies_exists_entry in allt; exrepnd.
  pose proof (ext a) as q; autodimp q hyp; eauto 2 with slow.
  repndors; exrepnd.
  { left; exists a n; dands; auto. }
  { right; left; exists a; dands; auto. }
  { right; right; exists a; dands; auto. }
Qed.

Lemma exists_entry_implies_forallb_diff_entry_names_false {o} :
  forall (e a : library_entry) (lib : @library o),
    entry_in_library e lib
    -> matching_entries e a
    -> shadowed_entry a lib.
Proof.
  introv ei m.
  unfold shadowed_entry; rewrite forallb_false.
  exists e; dands; eauto 2 with slow.
  apply matching_entries_iff_diff_entry_names_false; eauto 2 with slow.
Qed.

Hint Rewrite andb_true_r : slow.

Lemma forallb_snoc :
  forall {A} f (l : list A) a,
    forallb f (snoc l a) = forallb f l && f a.
Proof.
  induction l; introv; simpl; autorewrite with slow; auto.
  rewrite IHl.
  rewrite andb_assoc; auto.
Qed.

Lemma non_shadowed_entry_snoc {o} :
  forall a e (lib : @library o),
    non_shadowed_entry a (snoc lib e)
    <-> (non_shadowed_entry a lib /\ ~matching_entries a e).
Proof.
  introv; unfold non_shadowed_entry.
  rewrite forallb_snoc.
  rewrite andb_true_iff.
  rewrite <- non_matching_entries_iff_diff_entry_names_true; tcsp.
Qed.

Lemma implies_lib_extends_snoc_snoc_snoc {o} :
  forall e a (lib lib1 : @library o),
    lib_extends lib lib1
    -> matching_entries e a
    -> entry_in_library e lib1
    -> non_shadowed_entry a lib
    -> (non_shadowed_entry e lib -> safe_library_entry e)
    -> lib_extends (snoc (snoc lib e) a) (snoc lib1 a).
Proof.
  introv ext m ei allt safee.
  destruct ext as [ext safe sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i;
      [|eapply exists_entry_implies_forallb_diff_entry_names_false;eauto].
    applydup ext in i; eauto 3 with slow.

  - introv safe1.
    apply safe_library_snoc_implies in safe1; repnd.
    repeat (apply implies_safe_library_snoc; auto).
    rewrite non_shadowed_entry_snoc.
    introv nsh; repnd; apply safe1; tcsp.
    eauto 2 with slow.

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
  forall e (lib : @library o),
    entry_in_library e lib
    -> safe_library lib
    -> safe_library_entry e.
Proof.
  tcsp.
Qed.
Hint Resolve entry_in_library_implies_safe_library_entry : slow.

Lemma implies_forallb_diff_entry_names_snoc_false {o} :
  forall (e a : @library_entry o) lib,
    matching_entries e a
    -> shadowed_entry a (snoc lib e).
Proof.
  introv m.
  unfold shadowed_entry; rewrite forallb_false.
  exists e.
  rewrite <- matching_entries_iff_diff_entry_names_false.
  rewrite list_in_snoc; dands; tcsp; eauto 2 with slow.
Qed.
Hint Resolve implies_forallb_diff_entry_names_snoc_false : slow.

Lemma implies_inf_lib_extends_snoc_snoc {o} :
  forall infLib e a k (lib : @library o),
    inf_lib_extends infLib lib
    -> matching_entries e a
    -> entry_in_inf_library_extends e k infLib
    -> inf_lib_extends infLib (snoc (snoc lib e) a).
Proof.
  introv ext m ei.
  destruct ext as [ext safe].
  split; auto.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i; eauto 2 with slow.
    apply entry_in_library_snoc_implies in i; repndors; repnd; subst; tcsp; eauto.

  - introv safe'.
    apply safe_library_snoc_implies in safe'; repnd.
    apply safe_library_snoc_implies in safe'0; repnd.
    applydup safe in safe'1; auto.
Qed.
Hint Resolve implies_inf_lib_extends_snoc_snoc : slow.

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

Lemma le_preserves_entry_in_inf_library_extends {o} :
  forall k n e (infLib : @inf_library o),
    n <= k
    -> entry_in_inf_library_extends e n infLib
    -> entry_in_inf_library_extends e k infLib.
Proof.
  induction k; introv lenk i; simpl in *.

  - assert (n = 0) as xx by omega; subst; simpl in *; tcsp.

  - destruct n; simpl in *; tcsp.
    repndors; repnd; tcsp.
    pose proof (IHk n e (shift_inf_lib infLib)) as q.
    repeat (autodimp q hyp); try omega.
Qed.

Lemma inf_entry_extends_implies_entry_in_inf_library_extends_lt {o} :
  forall n k e a (infLib : @inf_library o),
    n < k
    -> inf_entry_extends (infLib n) e
    -> matching_entries e a
    -> (forall m : nat, m < n -> ~ inf_matching_entries (infLib m) a)
    -> entry_in_inf_library_extends e k infLib.
Proof.
  introv ltnk i m imp.
  eapply le_preserves_entry_in_inf_library_extends;
    [|eapply inf_entry_extends_implies_entry_in_inf_library_extends; eauto];
    try omega.
Qed.
Hint Resolve inf_entry_extends_implies_entry_in_inf_library_extends_lt : slow.

Lemma implies_inf_lib_extends_cons {o} :
  forall (infLib : @inf_library o) lib e k,
    inf_lib_extends infLib lib
    -> safe_library lib
    -> entry_in_inf_library_extends e k infLib
    -> inf_lib_extends infLib (e :: lib).
Proof.
  introv ext safel i.
  destruct ext as [ext safe].
  split; eauto 2 with slow;[].

  introv j; simpl in *; repndors; repnd; subst; tcsp.
  left; exists k; auto.
Qed.
Hint Resolve implies_inf_lib_extends_cons : slow.

Lemma inf_entry_extends_implies_inf_matching_entries2 {o} :
  forall (ie ie' : @inf_library_entry o) (e : library_entry),
    matching_inf_entries ie ie'
    -> inf_entry_extends ie e
    -> inf_matching_entries ie e.
Proof.
  introv m h; unfold inf_entry_extends in h.
  unfold inf_matching_entries.
  unfold matching_inf_entries in m.
  destruct ie, ie', e; simpl in *; repnd; subst; tcsp.
  rewrite <- matching_entry_sign_is_same_opabs in *.
  eapply implies_matching_entry_sign_refl; eauto.
Qed.
Hint Resolve inf_entry_extends_implies_inf_matching_entries2 : slow.

Lemma matching_inf_entries_sym {o} :
  forall (e1 e2 : @inf_library_entry o),
    matching_inf_entries e1 e2
    -> matching_inf_entries e2 e1.
Proof.
  introv h; unfold matching_inf_entries in *.
  eapply same_entry_name_sym; eauto.
Qed.
Hint Resolve matching_inf_entries_sym : slow.

Lemma entry_in_inf_library_default_implies_safe {o} :
  forall (entry : @library_entry o) infLib,
    entry_in_inf_library_cs_default entry infLib
    -> safe_library_entry entry.
Proof.
  introv h; unfold entry_in_inf_library_cs_default in h; tcsp.
Qed.
Hint Resolve entry_in_inf_library_default_implies_safe : slow.


(* This is not true for references because the infinite library might contain
   a different value than the entry, which does not ensure that the entry is safe *)

(*Lemma inf_lib_extends_implies_safe_library {o} :
  forall infLib (lib : @library o),
    inf_lib_extends infLib lib
    -> safe_inf_library infLib
    -> safe_library lib.
Proof.
  introv ext safe i.
  apply ext in i.
  repndors; exrepnd; eauto 3 with slow;[|].

  {
    apply inf_library_extends_implies in i0.
    exrepnd.
    eapply inf_entry_extends_preserves_safe_library_entry; eauto.

    apply (safe (infLib k)).
    apply implies_entry_in_inf_library.
    introv ltmn.
    pose proof (i1 m ltmn) as q; clear i1.
    introv minf; destruct q.

    eapply matching_inf_entries_preserves_inf_matching_entries;[|eauto].
    eauto 3 with slow.
  }
Qed.
Hint Resolve inf_lib_extends_implies_safe_library : slow.*)


(*Lemma inf_lib_extends_ext_entries_preserves_safe_library {o} :
  forall infLib (lib : @library o),
    inf_lib_extends_ext_entries infLib lib
    -> safe_inf_library infLib
    -> safe_library lib.
Proof.
  introv ext safe i.
  applydup ext in i; repndors; exrepnd; eauto 3 with slow;[].
  applydup @inf_library_extends_implies in i1; exrepnd.
  eapply inf_entry_extends_preserves_safe_library_entry;[eauto|].
  apply safe.
  apply implies_entry_in_inf_library.
  introv ltmk.
  pose proof (i2 m) as q; autodimp q hyp.
  introv ma; destruct q; eauto 4 with slow.
Qed.
Hint Resolve inf_lib_extends_ext_entries_preserves_safe_library : slow.*)


Lemma select_app_left :
  forall {A} (l1 l2 : list A) n,
    n < length l1 -> select n (l1 ++ l2) = select n l1.
Proof.
  induction l1; introv h; simpl in *; try omega.
  destruct n; simpl in *; auto.
  pose proof (IHl1 l2 n) as q; autodimp q hyp; try omega.
Qed.

(*Lemma entry_extends_preserves_safe_library_entry {o} :
  forall (entry entry' : @library_entry o),
    entry_extends entry' entry
    -> safe_library_entry entry'
    -> safe_library_entry entry.
Proof.
  introv ext safe.
  destruct entry, entry'; simpl in *; repnd; subst; tcsp; ginv.

  unfold choice_sequence_entry_extend in *; repnd.
  destruct entry as [vals1 restr1], entry0 as [vals2 restr2]; simpl in *; subst; auto.
  unfold choice_sequence_vals_extend in *; exrepnd; subst.
  unfold choice_sequence_satisfies_restriction in *.
  destruct restr1, restr2; dands; tcsp; eauto 3 with slow;
    simpl in *; repnd; tcsp;[|].

  - introv i.
    apply ext0.
    apply safe.
    rewrite select_app_left; auto.
    eapply select_lt; eauto.

  - introv h.
    pose proof (safe i) as q.
    allrw length_app.
    autodimp q hyp; try omega.
    rewrite ext0 in q.
    rewrite select_app_left in q; auto.
Qed.
Hint Resolve entry_extends_preserves_safe_library_entry : slow.*)

Record pre_lib_extends {o} (lib1 lib0 : @library o) : Prop :=
  MkPreLibExtends
    {
      pre_lib_extends_ext : lib_extends_entries lib1 lib0;
      pre_lib_extends_sub : subset_library lib0 lib1;
    }.
Arguments MkPreLibExtends [o] [lib1] [lib0] _ _.

Lemma pre_lib_extends_refl {o} :
  forall (lib : @library o), pre_lib_extends lib lib.
Proof.
  introv; split; eauto 2 with slow.
Qed.
Hint Resolve pre_lib_extends_refl : slow.

Lemma pre_lib_extends_nil {o} :
  forall (lib : @library o), pre_lib_extends lib [].
Proof.
  introv; split; simpl; tcsp; eauto 2 with slow.
Qed.
Hint Resolve pre_lib_extends_nil : slow.

Lemma inf_lib_extends_implies_inf_lib_extends_ext_entries {o} :
  forall infLib (lib : @library o),
    inf_lib_extends infLib lib
    -> inf_lib_extends_ext_entries infLib lib.
Proof.
  introv ext; destruct ext; auto.
Qed.
Hint Resolve inf_lib_extends_implies_inf_lib_extends_ext_entries : slow.

Lemma inf_lib_extends_ext_entries_snoc_implies_head {o} :
  forall infLib (lib : @library o) e,
    inf_lib_extends_ext_entries infLib (snoc lib e)
    -> inf_lib_extends_ext_entries infLib lib.
Proof.
  introv ext; introv i; apply ext; eauto 2 with slow.
Qed.
Hint Resolve inf_lib_extends_ext_entries_snoc_implies_head : slow.

Lemma inf_lib_extends_ext_entries_snoc_implies_entry_ext {o} :
  forall infLib (lib : @library o) e,
    non_shadowed_entry e lib
    -> inf_lib_extends_ext_entries infLib (snoc lib e)
    -> (exists k, entry_in_inf_library_extends e k infLib)
       \/ entry_in_inf_library_cs_default e infLib
       \/ entry_in_inf_library_ref_default e infLib.
Proof.
  introv allt ext.
  pose proof (ext e) as q; autodimp q hyp; repndors; eauto 2 with slow.
Qed.

Lemma implies_pre_lib_extends_snoc_lr_if_all_diff {o} :
  forall (lib lib1 : @library o) (e : library_entry),
    pre_lib_extends lib lib1
    -> non_shadowed_entry e lib
    -> pre_lib_extends (snoc lib e) (snoc lib1 e).
Proof.
  introv ext allt.
  destruct ext as [ext sub].
  split; simpl.

  - introv i.
    apply entry_in_library_snoc_implies in i; repndors; repnd; subst; eauto 2 with slow.
    apply ext in i; eauto 2 with slow.

  - introv i; allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; allrw @list_in_snoc; tcsp.

    + exists e; allrw @list_in_snoc; dands; tcsp; eauto 2 with slow.
Qed.
Hint Resolve implies_pre_lib_extends_snoc_lr_if_all_diff : slow.

Lemma implies_pre_lib_extends_snoc_left {o} :
  forall e (lib lib2 : @library o),
    pre_lib_extends lib lib2
    -> pre_lib_extends (snoc lib e) lib2.
Proof.
  introv ext.
  destruct ext as [ext sub].
  split; simpl.

  - introv i.
    apply ext in i; eauto 2 with slow.

  - introv i.
    apply sub in i; exrepnd.
    exists entry2; allrw @list_in_snoc; tcsp.
Qed.
Hint Resolve implies_pre_lib_extends_snoc_left : slow.

Lemma implies_inf_lib_extends_ext_entries_snoc {o} :
  forall (infLib : @inf_library o) lib e k,
    inf_lib_extends_ext_entries infLib lib
    -> entry_in_inf_library_extends e k infLib
    -> inf_lib_extends_ext_entries infLib (snoc lib e).
Proof.
  introv ext i.
  introv j; apply entry_in_library_snoc_implies in j; repndors; repnd; subst; tcsp.
  left; exists k; auto.
Qed.
Hint Resolve implies_inf_lib_extends_ext_entries_snoc : slow.

Lemma inf_lib_extends_ext_entries_snoc_implies_entry_ext2 {o} :
  forall infLib (lib : @library o) e,
    shadowed_entry e lib
    -> inf_lib_extends_ext_entries infLib (snoc lib e)
    -> (exists a k,
           matching_entries a e
           /\ entry_in_library a lib
           /\ entry_in_inf_library_extends a k infLib)
       \/ (exists a,
              entry_in_library a lib
              /\ matching_entries a e
              /\ entry_in_inf_library_cs_default a infLib)
       \/ (exists a,
              entry_in_library a lib
              /\ matching_entries a e
              /\ entry_in_inf_library_ref_default a infLib).
Proof.
  introv allt ext.
  applydup @forallb_diff_entry_names_false_implies_exists_entry in allt; exrepnd.
  pose proof (ext a) as q; autodimp q hyp; eauto 2 with slow.
  repndors; exrepnd.
  { left; exists a n; dands; auto. }
  { right; left; exists a; dands; auto. }
  { right; right; exists a; dands; auto. }
Qed.

Lemma implies_pre_lib_extends_snoc_snoc_snoc {o} :
  forall e a (lib lib1 : @library o),
    pre_lib_extends lib lib1
    -> matching_entries e a
    -> entry_in_library e lib1
    -> non_shadowed_entry a lib
    -> pre_lib_extends (snoc (snoc lib e) a) (snoc lib1 a).
Proof.
  introv ext m ei alltc.
  destruct ext as [ext sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i;
      [|eapply exists_entry_implies_forallb_diff_entry_names_false;eauto].
    applydup ext in i; eauto 3 with slow.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    { apply sub in i; exrepnd.
      exists entry2; dands; auto.
      allrw @list_in_snoc; tcsp. }

    { exists a.
      rewrite list_in_snoc; dands; tcsp; eauto 2 with slow. }
Qed.
Hint Resolve implies_pre_lib_extends_snoc_snoc_snoc : slow.

Lemma implies_inf_lib_extends_ext_entries_snoc_snoc {o} :
  forall infLib e a k (lib : @library o),
    inf_lib_extends_ext_entries infLib lib
    -> matching_entries e a
    -> entry_in_inf_library_extends e k infLib
    -> inf_lib_extends_ext_entries infLib (snoc (snoc lib e) a).
Proof.
  introv ext m ei.
  introv i.
  apply entry_in_library_snoc_shadowed_implies in i; eauto 2 with slow.
  apply entry_in_library_snoc_implies in i; repndors; repnd; subst; tcsp; eauto.
Qed.
Hint Resolve implies_inf_lib_extends_ext_entries_snoc_snoc : slow.

Lemma implies_pre_lib_extends_cons_left_snoc_right {o} :
  forall e (lib : @library o) lib1,
    non_shadowed_entry e lib1
    -> pre_lib_extends lib lib1
    -> pre_lib_extends (e :: lib) (snoc lib1 e).
Proof.
  introv allt ext.
  destruct ext as [ext sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_implies in i; repndors; repnd; subst; simpl; eauto 2 with slow.
    applydup ext in i.
    right; dands; eauto 2 with slow.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; dands; tcsp.

    + exists e; dands; tcsp; eauto 2 with slow.
Qed.
Hint Resolve implies_pre_lib_extends_cons_left_snoc_right : slow.

Lemma implies_pre_lib_extends_cons_left {o} :
  forall e (lib lib2 : @library o),
    pre_lib_extends lib lib2
    -> non_shadowed_entry e lib2
    -> pre_lib_extends (e :: lib) lib2.
Proof.
  introv ext allt.
  destruct ext as [ext sub].
  split; simpl in *.

  - introv i.
    applydup ext in i; right; dands; auto.
    introv m.
    unfold non_shadowed_entry in allt; rewrite forallb_forall in allt.
    pose proof (allt entry) as q.
    apply matching_entries_sym in m.
    apply matching_entries_iff_diff_entry_names_false in m.
    rewrite m in q.
    autodimp q hyp; eauto 2 with slow.

  - introv i; simpl.
    apply sub in i; exrepnd.
    exists entry2; tcsp.
Qed.
Hint Resolve implies_pre_lib_extends_cons_left : slow.

Lemma implies_inf_lib_extends_ext_entries_cons {o} :
  forall (infLib : @inf_library o) lib e k,
    inf_lib_extends_ext_entries infLib lib
    -> entry_in_inf_library_extends e k infLib
    -> inf_lib_extends_ext_entries infLib (e :: lib).
Proof.
  introv ext i.
  introv j; simpl in *; repndors; repnd; subst; tcsp.
  left; exists k; auto.
Qed.
Hint Resolve implies_inf_lib_extends_ext_entries_cons : slow.

Lemma pre_lib_extends_snoc_lr_if_all_diff_false {o} :
  forall e (lib lib1 : @library o),
    pre_lib_extends lib lib1
    -> shadowed_entry e lib1
    -> pre_lib_extends (snoc lib e) (snoc lib1 e).
Proof.
  introv ext allt.
  destruct ext as [ext sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i; auto.
    apply ext in i.
    apply implies_entry_in_library_extends_snoc; auto.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; dands; auto.
      allrw @list_in_snoc; tcsp.

    + exists e; dands; eauto 2 with slow.
      allrw @list_in_snoc; tcsp.
Qed.
Hint Resolve pre_lib_extends_snoc_lr_if_all_diff_false : slow.

Lemma implies_inf_lib_extends_ext_entries_snoc_shadowed {o} :
  forall (infLib : @inf_library o) lib e,
    inf_lib_extends_ext_entries infLib lib
    -> shadowed_entry e lib
    -> inf_lib_extends_ext_entries infLib (snoc lib e).
Proof.
  introv ext i.
  introv j.
  apply entry_in_library_snoc_shadowed_implies in j; auto.
Qed.
Hint Resolve implies_inf_lib_extends_ext_entries_snoc_shadowed : slow.

Lemma pre_lib_extends_cons_snoc_diff {o} :
  forall e a (lib lib1 : @library o),
    entry_extends e a
    -> non_shadowed_entry a lib1
    -> pre_lib_extends lib lib1
    -> pre_lib_extends (e :: lib) (snoc lib1 a).
Proof.
  introv exte allt ext.
  destruct ext as [ext sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_implies in i; repndors; repnd; subst; tcsp.
    applydup ext in i.
    right; dands; auto.
    introv m.
    eapply entry_extends_implies_matching_entries in exte;
      [|apply matching_entries_sym;eauto].
    eapply matching_entries_trans in exte;[|eauto].
    unfold non_shadowed_entry in allt; rewrite forallb_forall in allt.
    apply entry_in_library_implies_in in i.
    apply allt in i.
    apply matching_entries_sym in exte.
    apply matching_entries_iff_diff_entry_names_false in exte.
    rewrite exte in i; ginv.

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    + apply sub in i; exrepnd.
      exists entry2; dands; auto.

    + exists e; dands; eauto 2 with slow.
Qed.
Hint Resolve pre_lib_extends_cons_snoc_diff : slow.

Lemma implies_pre_lib_extends_cons_left_if_extends {o} :
  forall (e e' : @library_entry o) (lib lib2 : @library o),
    pre_lib_extends lib lib2
    -> entry_extends e e'
    -> entry_in_library e' lib2
    -> pre_lib_extends (e :: lib) lib2.
Proof.
  introv ext exte ei.
  destruct ext as [ext sub].
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

  - introv i; simpl.
    apply sub in i; exrepnd.
    exists entry2; dands; auto.
Qed.
Hint Resolve implies_pre_lib_extends_cons_left_if_extends : slow.

Lemma implies_inf_lib_extends_ext_entries_snoc_default {o} :
  forall (infLib : @inf_library o) lib e,
    inf_lib_extends_ext_entries infLib lib
    -> entry_in_inf_library_cs_default e infLib
    -> inf_lib_extends_ext_entries infLib (snoc lib e).
Proof.
  introv ext i.
  introv j; apply entry_in_library_snoc_implies in j; repndors; repnd; subst; tcsp.
Qed.
Hint Resolve implies_inf_lib_extends_ext_entries_snoc_default : slow.

Lemma implies_inf_lib_extends_ext_entries_cons_default {o} :
  forall (infLib : @inf_library o) lib e,
    inf_lib_extends_ext_entries infLib lib
    -> entry_in_inf_library_cs_default e infLib
    -> inf_lib_extends_ext_entries infLib (e :: lib).
Proof.
  introv ext i.
  introv j; simpl in *; repndors; repnd; subst; tcsp.
Qed.
Hint Resolve implies_inf_lib_extends_ext_entries_cons_default : slow.

Lemma entry_in_inf_library_cs_default_implies_exists3 {o} :
  forall infLib (lib : @library o) e,
    inf_lib_extends_ext_entries infLib lib
    -> forallb (diff_entry_names e) lib = false
    -> entry_in_inf_library_cs_default e infLib
    ->
    exists name n restr,
      is_nat_or_seq_kind name
      /\ entry2name e = entry_name_cs name
      /\ entry_in_library (choice_sequence_name2entry_upto n name restr) lib
      /\ correct_cs_restriction name restr.
Proof.
  introv ext allf i.
  allrw @forallb_false; exrepnd.
  apply matching_entries_iff_diff_entry_names_false in allf0.

  eapply in_implies_entry_in_library in allf1;
    [|apply matching_entries_sym;eauto].
  exrepnd.
  applydup ext in allf1.
  repndors; exrepnd.

  { eapply matching_entries_preserves_entry_in_inf_library_cs_default in i;
      [apply i in allf4;tcsp|]; eauto 3 with slow. }

  {
    apply entry_in_inf_library_cs_default_implies_exists in allf3; exrepnd; subst.
    simpl in *; GC.
    eapply matching_entries_trans in allf2;[|exact allf0].
    exists name n restr; dands; auto; eauto 3 with slow.
  }

  {
    eapply entry_in_inf_library_cs_ref_default_matching_false in allf3;
      eauto; tcsp; eauto 3 with slow.
  }
Qed.

Lemma entry_in_inf_library_ref_default_implies_exists3 {o} :
  forall infLib (lib : @library o) e,
    inf_lib_extends_ext_entries infLib lib
    -> forallb (diff_entry_names e) lib = false
    -> entry_in_inf_library_ref_default e infLib
    ->
    exists name restr v,
      is_nat_ref_kind name
      /\ entry2name e = entry_name_ref name
      /\ entry_in_library (mk_ref_entry name v restr) lib
      /\ correct_ref_restriction name restr.
Proof.
  introv ext allf i.
  allrw @forallb_false; exrepnd.
  apply matching_entries_iff_diff_entry_names_false in allf0.

  eapply in_implies_entry_in_library in allf1;
    [|apply matching_entries_sym;eauto].
  exrepnd.
  applydup ext in allf1.
  repndors; exrepnd.

  { eapply matching_entries_preserves_entry_in_inf_library_ref_default in i;
      [apply i in allf4;tcsp|]; eauto 3 with slow. }

  {
    eapply entry_in_inf_library_cs_ref_default_matching_false in allf3;
      eauto; tcsp; eauto 3 with slow.
  }

  {
    apply entry_in_inf_library_ref_default_implies_exists in allf3; exrepnd; subst.
    simpl in *; GC.
    eapply matching_entries_trans in allf2;[|exact allf0].
    exists name restr v; dands; auto; eauto 3 with slow.
  }
Qed.

Lemma is_cs_default_entry_choice_sequence_name2entry_upto {o} :
  forall n name (restr : @ChoiceSeqRestriction o),
    is_nat_or_seq_kind name
    -> correct_cs_restriction name restr
    -> is_cs_default_entry (choice_sequence_name2entry_upto n name restr).
Proof.
  introv isns cor.
  unfold is_cs_default_entry; simpl; dands; auto; eauto 3 with slow.
  unfold is_default_choice_sequence.
  unfold is_nat_or_seq_kind in isns.
  unfold correct_cs_restriction in *.
  destruct name as [name k]; simpl in *.
  unfold choice_sequence_name2choice_seq_vals_upto.
  destruct k as [k|seq]; simpl in *; boolvar; subst; tcsp; GC;
    destruct restr; simpl in *; simpl; introv h; repnd;
      rewrite select_fun2list in h; boolvar; tcsp; ginv;
        try (complete (allrw; auto)).
  unfold natSeq2default.

  remember (select n0 seq) as s; symmetry in Heqs; destruct s.

  - pose proof (cor0 n0) as q; autodimp q hyp; eauto 3 with slow.
    unfold cterm_is_nth in *; exrepnd.
    rewrite q1 in *; ginv.

  - pose proof (cor1 n0) as q; autodimp q hyp; eauto 3 with slow.
    apply nth_select2; auto.
Qed.
Hint Resolve is_cs_default_entry_choice_sequence_name2entry_upto : slow.

Lemma entry_in_inf_library_default_choice_sequence_name2entry_upto {o} :
  forall n name restr (infLib : @inf_library o) e x n1 restr1,
    entry_in_inf_library_cs_default e infLib
    -> matching_entries (choice_sequence_name2entry_upto n1 name restr1) x
    -> matching_entries x e
    -> is_nat_or_seq_kind name
    -> correct_cs_restriction name restr
    -> entry_in_inf_library_cs_default
         (choice_sequence_name2entry_upto n name restr)
         infLib.
Proof.
  introv ee me mx isns cor.
  unfold entry_in_inf_library_cs_default; dands; eauto 3 with slow.

  introv xx.
  unfold entry_in_inf_library_cs_default in ee; repnd.
  pose proof (ee0 n0) as ee0; destruct ee0.
  unfold inf_matching_entries, matching_entries in *; simpl in *.
  destruct e; simpl in *; tcsp; subst; eauto 3 with slow.
Qed.
Hint Resolve entry_in_inf_library_default_choice_sequence_name2entry_upto : slow.

Lemma pre_lib_extends_cons_snoc_if_in {o} :
  forall e e1 a (lib lib1 : @library o),
    matching_entries a e1
    -> entry_extends e e1
    -> entry_in_library e1 lib1
    -> pre_lib_extends lib lib1
    -> pre_lib_extends (e :: snoc lib a) (snoc lib1 a).
Proof.
  introv m exte ei ext.
  destruct ext as [ext sub].
  split; simpl in *.

  - introv i.
    apply entry_in_library_snoc_shadowed_implies in i;
      [|unfold shadowed_entry; rewrite forallb_false;
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

  - introv i; simpl.
    allrw @list_in_snoc; repndors; subst; tcsp.

    { apply sub in i; exrepnd.
      exists entry2; dands; auto.
      rewrite list_in_snoc; tcsp. }

    { exists a.
      rewrite list_in_snoc; dands; tcsp; eauto 2 with slow. }
Qed.
Hint Resolve pre_lib_extends_cons_snoc_if_in : slow.

Lemma implies_inf_lib_extends_ext_entries_snoc_ref_default {o} :
  forall (infLib : @inf_library o) lib e,
    inf_lib_extends_ext_entries infLib lib
    -> entry_in_inf_library_ref_default e infLib
    -> inf_lib_extends_ext_entries infLib (snoc lib e).
Proof.
  introv ext i.
  introv j; apply entry_in_library_snoc_implies in j; repndors; repnd; subst; tcsp.
Qed.
Hint Resolve implies_inf_lib_extends_ext_entries_snoc_ref_default : slow.

Lemma implies_inf_lib_extends_ext_entries_cons_ref_default {o} :
  forall (infLib : @inf_library o) lib e,
    inf_lib_extends_ext_entries infLib lib
    -> entry_in_inf_library_ref_default e infLib
    -> inf_lib_extends_ext_entries infLib (e :: lib).
Proof.
  introv ext i.
  introv j; simpl in *; repndors; repnd; subst; tcsp.
Qed.
Hint Resolve implies_inf_lib_extends_ext_entries_cons_ref_default : slow.

Lemma safe_library_entry_mk_ref_entry {o} :
  forall name (restr : @RefRestriction o),
    is_nat_ref_kind name
    -> correct_ref_restriction name restr
    -> safe_library_entry (mk_ref_entry name mkc_zero restr).
Proof.
  introv isn cor; unfold safe_library_entry; simpl; dands; auto.
  destruct restr; simpl in *.
  destruct name as [name kind], kind; simpl in *.
  unfold correct_ref_restriction in *; simpl in *; boolvar; tcsp; repnd; subst.
  apply cor; eauto 3 with slow.
Qed.
Hint Resolve safe_library_entry_mk_ref_entry : slow.

Lemma is_ref_default_entry_mk_ref_entry {o} :
  forall name (restr : @RefRestriction o) v,
    is_nat_ref_kind name
    -> correct_ref_restriction name restr
    -> is_ref_default_entry (mk_ref_entry name v restr).
Proof.
  introv isn cor.
  unfold is_ref_default_entry; simpl; dands; auto.
Qed.
Hint Resolve is_ref_default_entry_mk_ref_entry : slow.

Lemma entry_in_inf_library_ref_default_mk_ref_entry {o} :
  forall name restr (infLib : @inf_library o) e x restr1 v1,
    entry_in_inf_library_ref_default e infLib
    -> matching_entries (lib_ref name (MkReferenceEntry _ v1 restr1)) x
    -> matching_entries x e
    -> is_nat_ref_kind name
    -> correct_ref_restriction name restr
    -> entry_in_inf_library_ref_default
         (mk_ref_entry name mkc_zero restr)
         infLib.
Proof.
  introv ee me mx isns cor.
  unfold entry_in_inf_library_ref_default; dands; eauto 3 with slow;[].

  introv xx.
  unfold entry_in_inf_library_ref_default in ee; repnd.
  pose proof (ee0 n) as ee0; destruct ee0.
  unfold inf_matching_entries, matching_entries in *; simpl in *.
  destruct e; simpl in *; tcsp; subst; eauto 3 with slow.
Qed.
Hint Resolve entry_in_inf_library_ref_default_mk_ref_entry : slow.

Lemma non_shadowed_entry_snoc_matching_implies_safe {o} :
  forall (a b : @library_entry o) lib,
    matching_entries b a
    -> non_shadowed_entry a (snoc lib b)
    -> safe_library_entry a.
Proof.
  introv h q.
  apply non_shadowed_entry_snoc in q; repnd.
  apply matching_entries_sym in h; tcsp.
Qed.
Hint Resolve non_shadowed_entry_snoc_matching_implies_safe : slow.

Lemma implies_safe_library_cons_snoc {o} :
  forall (a b : @library_entry o) lib,
    safe_library_entry a
    -> safe_library lib
    -> matching_entries a b
    -> safe_library (a :: snoc lib b).
Proof.
  introv sa safe m.
  rewrite cons_snoc.
  apply implies_safe_library_snoc; eauto 3 with slow.
  introv h.
  apply matching_entries_implies_not_non_shadowed_entry in h; tcsp; eauto 3 with slow.
Qed.
Hint Resolve implies_safe_library_cons_snoc : slow.

Lemma intersect_inf_lib_extends2 {o} :
  forall infLib (lib1 lib2 : @library o),
    safe_library lib1
    -> safe_library lib2
    -> inf_lib_extends infLib lib1
    -> inf_lib_extends infLib lib2
    -> exists lib,
        lib_extends lib lib1
        /\ lib_extends lib lib2
        /\ inf_lib_extends infLib lib.
Proof.
  introv safel1 safel2 ext1 ext2.

  let x := constr:(exists lib,
                      safe_library lib
                      /\ pre_lib_extends lib lib1
                      /\ pre_lib_extends lib lib2
                      /\ inf_lib_extends_ext_entries infLib lib) in
  match goal with
  | [ |- ?c ] => assert (x -> c) as h;[intro h|apply h;clear h]
  end.

  {
    exrepnd.
    destruct h2 as [ext_1 sub_1].
    destruct h3 as [ext_2 sub_2].
    exists lib.
    dands; split; auto.
    introv safe; destruct ext1 as [ext1 safe1 sub1]; apply safe1.
    eauto 2 with slow; introv i; apply ext_1 in i.
  }

  destruct ext1 as [ext1 safe1].
  destruct ext2 as [ext2 safe2].

  autodimp safe1 hyp.
  clear safe2.

  revert lib1 lib2 safel1 safel2 ext1 ext2.

  induction lib1 using rev_list_ind; introv safel1 safel2 ext1 ext2; simpl in *.

  - exists lib2; dands; eauto 2 with slow.

  - pose proof (IHlib1 lib2) as q; repeat (autodimp q hyp); eauto 2 with slow; clear IHlib1.
    exrepnd.
    apply safe_library_snoc_implies in safel1; repnd.

    remember (forallb (diff_entry_names a) lib) as b; symmetry in Heqb; destruct b.

    + (* [a] is not in [lib] *)

      remember (forallb (diff_entry_names a) lib1) as z; symmetry in Heqz; destruct z.

      * (* [a] is not in [lib1] *)

        pose proof (inf_lib_extends_ext_entries_snoc_implies_entry_ext infLib lib1 a) as q.
        repeat (autodimp q hyp).
        repndors; exrepnd; try (complete (exists (snoc lib a); dands; eauto 3 with slow)).

      * (* [a] is in [lib1] *)

        pose proof (inf_lib_extends_ext_entries_snoc_implies_entry_ext2 infLib lib1 a) as q.
        repeat (autodimp q hyp); repndors; exrepnd; try (complete (exists (snoc (snoc lib a0) a); dands; eauto 6 with slow)).

    + (* [a] is in [lib] *)

      remember (forallb (diff_entry_names a) lib2) as w; symmetry in Heqw; destruct w.

      * (* [a] is not in [lib2] *)

        remember (forallb (diff_entry_names a) lib1) as z; symmetry in Heqz; destruct z.

        { (* [a] is not in [lib1] *)

          pose proof (inf_lib_extends_ext_entries_snoc_implies_entry_ext infLib lib1 a) as q.
          repeat (autodimp q hyp); repndors; exrepnd; try (complete (exists (a :: lib); dands; eauto 3 with slow)).
        }

        { (* [a] is in [lib1] *)

          exists (snoc lib a); dands; eauto 5 with slow.
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
          applydup q3 in Heqw1.

          pose proof (ext1 a) as q.
          autodimp q hyp; exrepnd; eauto 2 with slow;[].
          pose proof (ext2 e') as w.
          autodimp w hyp; exrepnd.

          repndors; exrepnd.

          {
            pose proof (inf_library_extends_two_matching_entries a e' n0 n infLib) as h.

            repeat (autodimp h hyp).
            { eapply matching_entries_trans; eauto. }
            exrepnd.

            assert (safe_library_entry a) as safea by eauto 3 with slow.
            assert (safe_library_entry e') as safee' by eauto 3 with slow.
            assert (safe_inf_library_entry (infLib n1)) as safeie.
            { eapply safe_library_entry_implies_safe_inf_library_entry; eauto.
              eapply inf_entry_extends_implies_inf_matching_entries; eauto. }

            pose proof (inf_entry_extends_two_entries_implies_entry_extends_safe (infLib n1) a e') as q.
            repeat (autodimp q hyp); exrepnd.

            exists (e :: lib); dands; eauto 2 with slow.

            eapply implies_inf_lib_extends_ext_entries_cons; auto; eauto 2 with slow.
            eapply inf_entry_extends_implies_entry_in_inf_library_extends;
              eauto 2 with slow.
            introv lemn m'; apply h0 in lemn; destruct lemn; eauto 3 with slow.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in w0;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in q;
              [apply q in w0|]; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in q4;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            pose proof (entry_in_inf_library_cs_default_implies_exists3 infLib lib2 a) as z.
            repeat (autodimp z hyp); exrepnd;[].
            apply entry_in_inf_library_cs_default_implies_exists in q.
            exrepnd.
            rewrite q6 in z2; ginv; simpl in *.
            exists ((choice_sequence_name2entry_upto (Peano.max n n0) name restr) :: lib); dands; eauto 5 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in w;
              tcsp; eauto; eauto 3 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            pose proof (entry_in_inf_library_ref_default_implies_exists3 infLib lib2 a) as z.
            repeat (autodimp z hyp); exrepnd;[].
            apply entry_in_inf_library_ref_default_implies_exists in q.
            exrepnd.
            rewrite q6 in z2; ginv; simpl in *.
            exists ((mk_ref_entry name mkc_zero restr) :: lib); dands; eauto 5 with slow.
          }
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
          applydup q3 in in2lib1.

          dup Heqz as in1lib.
          apply forallb_false in in1lib; exrepnd.
          apply matching_entries_iff_diff_entry_names_false in in1lib0.

          eapply in_implies_entry_in_library in in1lib1;
            [|apply matching_entries_sym;eauto].
          exrepnd.
          rename e' into e1.
          eapply matching_entries_trans in in1lib2;[|eauto].
          clear dependent x.
          applydup q2 in in1lib1.

          pose proof (ext1 e1) as q.
          autodimp q hyp; exrepnd; eauto 2 with slow;[].
          pose proof (ext2 e2) as w.
          autodimp w hyp; exrepnd.

          repndors; exrepnd.

          {
            pose proof (inf_library_extends_two_matching_entries e1 e2 n0 n infLib) as h.
            repeat (autodimp h hyp).
            { eapply matching_entries_trans; eauto.
              apply matching_entries_sym; auto. }
            exrepnd.

            assert (safe_library_entry e1) as safee1 by eauto 3 with slow.
            assert (safe_library_entry e2) as safee2 by eauto 3 with slow.
            assert (safe_inf_library_entry (infLib n1)) as safeie.
            { eapply safe_library_entry_implies_safe_inf_library_entry; eauto.
              eapply inf_entry_extends_implies_inf_matching_entries; eauto.
              eauto 3 with slow. }

            pose proof (inf_entry_extends_two_entries_implies_entry_extends_safe (infLib n1) e1 e2) as q.
            repeat (autodimp q hyp); exrepnd.

            exists (e :: snoc lib a); dands; eauto 6 with slow;[].

            apply (implies_inf_lib_extends_ext_entries_snoc_shadowed _ (e :: lib)).

            { eapply implies_inf_lib_extends_ext_entries_cons; eauto 2 with slow;[].
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

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in w0;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in q;
              [apply q in w0|]; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in q4;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            pose proof (entry_in_inf_library_cs_default_implies_exists e2 infLib) as z.
            repeat (autodimp z hyp); exrepnd; eauto 3 with slow.

            pose proof (entry_in_inf_library_cs_default_implies_exists e1 infLib) as u.
            repeat (autodimp u hyp); exrepnd; eauto 3 with slow.

            assert (same_entry_name (entry2name e1) (entry2name e2)) as xx by eauto 3 with slow.
            rewrite z2 in xx; rewrite u2 in xx; simpl in xx; subst.

            exists ((choice_sequence_name2entry_upto (Peano.max n n0) name restr) :: snoc lib a); dands; eauto 4 with slow.
            apply implies_inf_lib_extends_ext_entries_cons_default; eauto 3 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in w;
              tcsp; eauto; eauto 3 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            pose proof (entry_in_inf_library_ref_default_implies_exists e2 infLib) as z.
            repeat (autodimp z hyp); exrepnd; eauto 3 with slow.

            pose proof (entry_in_inf_library_ref_default_implies_exists e1 infLib) as u.
            repeat (autodimp u hyp); exrepnd; eauto 3 with slow.

            assert (same_entry_name (entry2name e1) (entry2name e2)) as xx by eauto 3 with slow.
            rewrite z2 in xx; rewrite u2 in xx; simpl in xx; subst.
            simpl in *; GC.

            exists ((mk_ref_entry name v restr) :: snoc lib a); dands; eauto 4 with slow.
            eapply pre_lib_extends_cons_snoc_if_in; try exact in1lib1; eauto 3 with slow.
          }
        }
Qed.

Lemma safe_library_cond1 {o} :
  forall (lib lib1 lib2 : @library o) a,
    (safe_library lib1 -> safe_library lib2 -> safe_library lib)
    -> forallb (diff_entry_names a) lib1 = true
    -> safe_library (snoc lib1 a)
    -> safe_library lib2
    -> safe_library (snoc lib a).
Proof.
  introv imp fall safe1 safe2.
  apply safe_library_snoc_implies in safe1; repnd.
  autodimp safe1 hyp; eauto 2 with slow.
  repeat (autodimp imp hyp).
  eauto 2 with slow.
Qed.
Hint Resolve safe_library_cond1 : slow.

Lemma safe_library_cond2 {o} :
  forall (lib lib1 lib2 : @library o) a b,
    (safe_library lib1 -> safe_library lib2 -> safe_library lib)
    -> entry_in_library b lib1
    -> matching_entries b a
    -> safe_library (snoc lib1 a)
    -> safe_library lib2
    -> safe_library (snoc (snoc lib b) a).
Proof.
  introv imp fall m safe1 safe2.
  apply safe_library_snoc_implies_head in safe1.
  repeat (autodimp imp hyp).
  repeat apply implies_safe_library_snoc; eauto 3 with slow.
Qed.
Hint Resolve safe_library_cond2 : slow.

Lemma safe_library_cond3 {o} :
  forall (lib lib1 lib2 : @library o) a,
    (safe_library lib1 -> safe_library lib2 -> safe_library lib)
    -> forallb (diff_entry_names a) lib1 = true
    -> safe_library (snoc lib1 a)
    -> safe_library lib2
    -> safe_library (a :: lib).
Proof.
  introv imp fall safe1 safe2.
  apply safe_library_snoc_implies in safe1; repnd.
  autodimp safe1 hyp; eauto 2 with slow.
  repeat (autodimp imp hyp).
  eauto 2 with slow.
Qed.
Hint Resolve safe_library_cond3 : slow.

Lemma safe_library_cond4 {o} :
  forall (lib lib1 lib2 : @library o) a,
    (safe_library lib1 -> safe_library lib2 -> safe_library lib)
    -> forallb (diff_entry_names a) lib = false
    -> forallb (diff_entry_names a) lib1 = false
    -> safe_library (snoc lib1 a)
    -> safe_library lib2
    -> safe_library (snoc lib a).
Proof.
  introv imp fall1 fall2 safe1 safe2.
  apply safe_library_snoc_implies_head in safe1.
  repeat (autodimp imp hyp).
  repeat apply implies_safe_library_snoc; eauto 3 with slow.
  introv h.
  rewrite h in fall1; ginv.
Qed.
Hint Resolve safe_library_cond4 : slow.

Lemma inf_entry_extends_two_entries_implies_entry_extends_safe2 {o} :
  forall (ie : @inf_library_entry o) e1 e2,
    inf_entry_extends ie e1
    -> inf_entry_extends ie e2
    ->
    exists e,
      entry_extends e e1
      /\ entry_extends e e2
      /\ inf_entry_extends ie e
      /\ (safe_library_entry e1 -> safe_library_entry e2-> safe_library_entry e).
Proof.
  destruct ie, e1, e2; introv ext1 ext2; simpl in *; repnd; repeat (subst; tcsp);
    [| |assert (correct1 = correct0) as xx by (apply correct_abs_proof_irrelevance); subst;
        assert (correct0 = correct) as xx by (apply correct_abs_proof_irrelevance); subst;
        exists (lib_abs opabs1 vars1 rhs1 correct); dands; unfold entry_extends; auto];[|].

  {
    destruct entry as [vals restr].
    destruct entry0 as [vals1 restr1].
    destruct entry1 as [vals2 restr2].
    unfold inf_choice_sequence_entry_extend in *; simpl in *.
    repnd; repeat subst.
    unfold inf_choice_sequence_vals_extend in *.

    exists (lib_cs name1 (MkChoiceSeqEntry _ (combine_choice_seq_vals vals1 vals2) restr2)).
    simpl; dands; auto; unfold choice_sequence_entry_extend; simpl; dands; auto;
      unfold choice_sequence_vals_extend; eauto 3 with slow;[| | |].

    - eapply exists_combine_choice_seq_vals_1; eauto.

    - eapply exists_combine_choice_seq_vals_2; eauto.

    - introv i; apply select_combine_choice_seq_vals_implies_or in i; repndors; tcsp.

    - introv safe1 safe2; repnd; dands; auto.
      eapply implies_choice_sequence_satisfies_restriction2; eauto; eauto 3 with slow.
  }

  {
    exists (lib_ref name1 entry0); dands; simpl; auto; dands; eauto 3 with slow.
  }
Qed.

Lemma safe_library_cond5 {o} :
  forall (lib lib1 lib2 : @library o) a e e',
    (safe_library lib1 -> safe_library lib2 -> safe_library lib)
    -> (safe_library_entry a -> safe_library_entry e' -> safe_library_entry e)
    -> entry_in_library e' lib2
    -> forallb (diff_entry_names a) lib1 = true
    -> safe_library (snoc lib1 a)
    -> safe_library lib2
    -> safe_library (e :: lib).
Proof.
  introv imp1 imp2 i fall safe1 safe2.
  apply safe_library_snoc_implies in safe1; repnd.
  autodimp safe1 hyp; eauto 2 with slow.
  repeat (autodimp imp1 hyp).
  repeat (autodimp imp2 hyp).
  apply implies_safe_library_cons; eauto 3 with slow.
Qed.
Hint Resolve safe_library_cond5 : slow.

Lemma safe_library_cond6 {o} :
  forall (lib lib1 lib2 : @library o) e e1 e2 a,
    (safe_library lib1 -> safe_library lib2 -> safe_library lib)
    -> (safe_library_entry e1 -> safe_library_entry e2 -> safe_library_entry e)
    -> forallb (diff_entry_names a) lib = false
    -> entry_in_library e1 lib1
    -> entry_in_library e2 lib2
    -> safe_library (snoc lib1 a)
    -> safe_library lib2
    -> safe_library (e :: snoc lib a).
Proof.
  introv imp1 imp2 fall i j safe1 safe2.
  apply safe_library_snoc_implies in safe1; repnd.
  repeat (autodimp imp1 hyp).
  repeat (autodimp imp2 hyp).
  apply implies_safe_library_cons; eauto 3 with slow.
  apply implies_safe_library_snoc; eauto 3 with slow.
  introv xx.
  rewrite xx in fall; ginv.
Qed.
Hint Resolve safe_library_cond6 : slow.

Lemma safe_library_empty {o} :
  @safe_library o [].
Proof.
  introv i; simpl in *; tcsp.
Qed.
Hint Resolve safe_library_empty : slow.

Lemma safe_library_cond7 {o} :
  forall (lib lib1 : @library o) a b,
    (safe_library lib -> safe_library lib1)
    -> forallb (diff_entry_names a) lib1 = false
    -> safe_library (snoc (snoc lib b) a)
    -> safe_library (snoc lib1 a).
Proof.
  introv imp fall safe.
  apply safe_library_snoc_implies_head in safe.
  apply safe_library_snoc_implies_head in safe.
  repeat (autodimp imp hyp).
  repeat apply implies_safe_library_snoc; eauto 3 with slow.
  introv h.
  rewrite h in fall; ginv.
Qed.
Hint Resolve safe_library_cond7 : slow.

Lemma intersect_inf_lib_extends3 {o} :
  forall infLib (lib1 lib2 : @library o),
    inf_lib_extends_ext_entries infLib lib1
    -> inf_lib_extends_ext_entries infLib lib2
    -> exists lib,
        (safe_library lib1 -> safe_library lib2 -> safe_library lib)
(*        /\ (safe_library lib -> safe_library lib1)*)
        /\ pre_lib_extends lib lib1
        /\ pre_lib_extends lib lib2
        /\ inf_lib_extends_ext_entries infLib lib.
Proof.
  induction lib1 using rev_list_ind; introv ext1 ext2; simpl in *.

  - exists lib2; dands; eauto 2 with slow.

  - pose proof (IHlib1 lib2) as q; repeat (autodimp q hyp); eauto 2 with slow; clear IHlib1.
    exrepnd.

    remember (forallb (diff_entry_names a) lib) as b; symmetry in Heqb; destruct b.

    + (* [a] is not in [lib] *)

      remember (forallb (diff_entry_names a) lib1) as z; symmetry in Heqz; destruct z.

      * (* [a] is not in [lib1] *)

        pose proof (inf_lib_extends_ext_entries_snoc_implies_entry_ext infLib lib1 a) as q.
        repeat (autodimp q hyp).
        repndors; exrepnd; try (complete (exists (snoc lib a); dands; eauto 3 with slow)).

      * (* [a] is in [lib1] *)

        pose proof (inf_lib_extends_ext_entries_snoc_implies_entry_ext2 infLib lib1 a) as q.
        repeat (autodimp q hyp); repndors; exrepnd; try (complete (exists (snoc (snoc lib a0) a); dands; eauto 4 with slow)).

    + (* [a] is in [lib] *)

      remember (forallb (diff_entry_names a) lib2) as w; symmetry in Heqw; destruct w.

      * (* [a] is not in [lib2] *)

        remember (forallb (diff_entry_names a) lib1) as z; symmetry in Heqz; destruct z.

        { (* [a] is not in [lib1] *)

          pose proof (inf_lib_extends_ext_entries_snoc_implies_entry_ext infLib lib1 a) as q.
          repeat (autodimp q hyp); repndors; exrepnd; try (complete (exists (a :: lib); dands; eauto 3 with slow)).
        }

        { (* [a] is in [lib1] *)

          exists (snoc lib a); dands; eauto 4 with slow.
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
          applydup q3 in Heqw1.

          pose proof (ext1 a) as q.
          autodimp q hyp; exrepnd; eauto 2 with slow;[].
          pose proof (ext2 e') as w.
          autodimp w hyp; exrepnd.

          repndors; exrepnd.

          {
            pose proof (inf_library_extends_two_matching_entries a e' n0 n infLib) as h.

            repeat (autodimp h hyp).
            { eapply matching_entries_trans; eauto. }
            exrepnd.

            pose proof (inf_entry_extends_two_entries_implies_entry_extends_safe2 (infLib n1) a e') as q.
            repeat (autodimp q hyp); exrepnd.

            exists (e :: lib); dands; eauto 2 with slow.

            eapply implies_inf_lib_extends_ext_entries_cons; auto; eauto 2 with slow.
            eapply inf_entry_extends_implies_entry_in_inf_library_extends;
              eauto 2 with slow.
            introv lemn m'; apply h0 in lemn; destruct lemn; eauto 3 with slow.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in w0;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in q;
              [apply q in w0|]; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in q4;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            pose proof (entry_in_inf_library_cs_default_implies_exists3 infLib lib2 a) as z.
            repeat (autodimp z hyp); exrepnd;[].
            apply entry_in_inf_library_cs_default_implies_exists in q.
            exrepnd.
            rewrite q6 in z2; ginv; simpl in *.
            exists ((choice_sequence_name2entry_upto (Peano.max n n0) name restr) :: lib); dands; eauto 5 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in w;
              tcsp; eauto; eauto 3 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            pose proof (entry_in_inf_library_ref_default_implies_exists3 infLib lib2 a) as z.
            repeat (autodimp z hyp); exrepnd;[].
            apply entry_in_inf_library_ref_default_implies_exists in q.
            exrepnd.
            rewrite q6 in z2; ginv; simpl in *.
            exists ((mk_ref_entry name mkc_zero restr) :: lib); dands; eauto 5 with slow.
          }
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
          applydup q3 in in2lib1.

          dup Heqz as in1lib.
          apply forallb_false in in1lib; exrepnd.
          apply matching_entries_iff_diff_entry_names_false in in1lib0.

          eapply in_implies_entry_in_library in in1lib1;
            [|apply matching_entries_sym;eauto].
          exrepnd.
          rename e' into e1.
          eapply matching_entries_trans in in1lib2;[|eauto].
          clear dependent x.
          applydup q2 in in1lib1.

          pose proof (ext1 e1) as q.
          autodimp q hyp; exrepnd; eauto 2 with slow;[].
          pose proof (ext2 e2) as w.
          autodimp w hyp; exrepnd.

          repndors; exrepnd.

          {
            pose proof (inf_library_extends_two_matching_entries e1 e2 n0 n infLib) as h.
            repeat (autodimp h hyp).
            { eapply matching_entries_trans; eauto.
              apply matching_entries_sym; auto. }
            exrepnd.

            pose proof (inf_entry_extends_two_entries_implies_entry_extends_safe2 (infLib n1) e1 e2) as q.
            repeat (autodimp q hyp); exrepnd.

            exists (e :: snoc lib a); dands; eauto 3 with slow;[].

            apply (implies_inf_lib_extends_ext_entries_snoc_shadowed _ (e :: lib)).

            { eapply implies_inf_lib_extends_ext_entries_cons; eauto 2 with slow;[].
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

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in w0;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in q;
              [apply q in w0|]; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_cs_default in q4;
              [| |eauto]; eauto 3 with slow;tcsp.
          }

          {
            pose proof (entry_in_inf_library_cs_default_implies_exists e2 infLib) as z.
            repeat (autodimp z hyp); exrepnd; eauto 3 with slow.

            pose proof (entry_in_inf_library_cs_default_implies_exists e1 infLib) as u.
            repeat (autodimp u hyp); exrepnd; eauto 3 with slow.

            assert (same_entry_name (entry2name e1) (entry2name e2)) as xx by eauto 3 with slow.
            rewrite z2 in xx; rewrite u2 in xx; simpl in xx; subst.

            exists ((choice_sequence_name2entry_upto (Peano.max n n0) name restr) :: snoc lib a); dands; eauto 4 with slow.
            apply implies_inf_lib_extends_ext_entries_cons_default; eauto 3 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            eapply matching_entries_preserves_entry_in_inf_library_ref_default in w;
              tcsp; eauto; eauto 3 with slow.
          }

          {
            eapply entry_in_inf_library_cs_ref_default_matching_false in q;
              try exact w; eauto 3 with slow; tcsp.
          }

          {
            pose proof (entry_in_inf_library_ref_default_implies_exists e2 infLib) as z.
            repeat (autodimp z hyp); exrepnd; eauto 3 with slow.

            pose proof (entry_in_inf_library_ref_default_implies_exists e1 infLib) as u.
            repeat (autodimp u hyp); exrepnd; eauto 3 with slow.

            assert (same_entry_name (entry2name e1) (entry2name e2)) as xx by eauto 3 with slow.
            rewrite z2 in xx; rewrite u2 in xx; simpl in xx; subst.
            simpl in *; GC.

            exists ((mk_ref_entry name v restr) :: snoc lib a); dands; eauto 4 with slow.
            eapply pre_lib_extends_cons_snoc_if_in; try exact in1lib1; eauto 3 with slow.
          }
        }
Qed.

(*
Lemma intersect_inf_lib_extends4 {o} :
  forall infLib (lib1 lib2 : @library o),
    inf_lib_extends infLib lib1
    -> inf_lib_extends infLib lib2
    -> exists lib,
        lib_extends lib lib1
        /\ lib_extends lib lib2
        /\ inf_lib_extends infLib lib.
Proof.
  introv ext1 ext2.

  let x := constr:(exists lib,
                      (safe_library lib1 -> safe_library lib)
                      /\ (safe_library lib2 -> safe_library lib)
                      /\ (safe_library lib -> safe_library lib1)
                      /\ (safe_library lib -> safe_library lib2)
                      /\ pre_lib_extends lib lib1
                      /\ pre_lib_extends lib lib2
                      /\ inf_lib_extends_ext_entries infLib lib) in
  match goal with
  | [ |- ?c ] => assert (x -> c) as h;[intro h|apply h;clear h]
  end.

  {
    exrepnd.
    destruct h5 as [ext_1 sub_1].
    destruct h6 as [ext_2 sub_2].
    exists lib.
    dands; split; auto.
    introv safe.
    destruct ext1 as [ext1 safe1].
    destruct ext2 as [ext2 safe2].
    eauto.
  }

  destruct ext1 as [ext1 safe1].
  destruct ext2 as [ext2 safe2].

  revert lib1 lib2 safe1 safe2 ext1 ext2.
Qed.
 *)

Lemma pre_lib_extends_implies_lib_extends {o} :
  forall (lib1 lib2 : @library o),
    pre_lib_extends lib1 lib2
    -> (safe_library lib2 -> safe_library lib1)
    -> lib_extends lib1 lib2.
Proof.
  introv ext imp.
  destruct ext.
  split; auto.
Qed.
Hint Resolve pre_lib_extends_implies_lib_extends : slow.

Lemma lib_extends_implies_pre_lib_extends {o} :
  forall (lib1 lib2 : @library o),
    lib_extends lib1 lib2
    -> pre_lib_extends lib1 lib2.
Proof.
  introv ext.
  destruct ext.
  split; auto.
Qed.
Hint Resolve lib_extends_implies_pre_lib_extends : slow.

Lemma pre_lib_extends_trans {o} :
  forall (lib1 lib2 lib3 : @library o),
    pre_lib_extends lib1 lib2
    -> pre_lib_extends lib2 lib3
    -> pre_lib_extends lib1 lib3.
Proof.
  introv ext1 ext2.
  destruct ext1 as [ext1 ss1].
  destruct ext2 as [ext2 ss2].
  split; eauto 3 with slow.

  introv i.
  apply ext2 in i.

  apply entry_in_library_extends_implies_entry_in_library in i.
  exrepnd.
  apply ext1 in i1; eauto 2 with slow.
Qed.
Hint Resolve pre_lib_extends_trans : slow.

Lemma pre_inf_lib_extends_implies_inf_lib_extends {o} :
  forall ilib (lib : @library o),
    inf_lib_extends_ext_entries ilib lib
    -> (safe_library lib -> safe_inf_library ilib)
    -> inf_lib_extends ilib lib.
Proof.
  introv ext imp.
  split; auto.
Qed.
Hint Resolve pre_inf_lib_extends_implies_inf_lib_extends : slow.

Lemma inf_lib_extends_implies_pre_inf_lib_extends {o} :
  forall ilib (lib : @library o),
    inf_lib_extends ilib lib
    -> inf_lib_extends_ext_entries ilib lib.
Proof.
  introv ext.
  destruct ext; auto.
Qed.
Hint Resolve inf_lib_extends_implies_pre_inf_lib_extends : slow.

Definition intersect_bars {o} {lib : SL} (bar1 bar2 : @BarLib o lib) : BarLib lib.
Proof.
  exists (fun (lib' : library) =>
            exists lib1 lib2,
              bar_lib_bar bar1 lib1
              /\ bar_lib_bar bar2 lib2
              /\ lib_extends lib' lib1
              /\ lib_extends lib' lib2).

  - introv ext.

    destruct bar1 as [bar1 bars1 ext1].
    destruct bar2 as [bar2 bars2 ext2].
    simpl in *.

    pose proof (bars1 infLib) as q; autodimp q hyp.
    pose proof (bars2 infLib) as h; autodimp h hyp.
    destruct q as [lib1 q]; repnd.
    destruct h as [lib2 h]; repnd.

    pose proof (intersect_inf_lib_extends2 infLib lib1 lib2) as w.
    repeat (autodimp w hyp); eauto 2 with slow;[].
    exrepnd.

    exists lib0; dands; auto; eauto 3 with slow.
    exists lib1 lib2; dands; auto.

  - introv h; exrepnd.

    destruct bar1 as [bar1 bars1 ext1].
    destruct bar2 as [bar2 bars2 ext2].
    simpl in *.
    eauto 3 with slow.
Defined.

Lemma ex_extends_two_bars {o} :
  forall {lib : @SL o} (bar1 bar2 : BarLib lib),
  exists (lib1 lib2 lib' : @library o),
    bar_lib_bar bar1 lib1
    /\ bar_lib_bar bar2 lib2
    /\ lib_extends lib' lib1
    /\ lib_extends lib' lib2.
Proof.
  introv.
  pose proof (bar_non_empty (intersect_bars bar1 bar2)) as ne.
  exrepnd.
  simpl in *; exrepnd.
  exists lib1 lib2 lib'; tcsp.
Qed.

Definition ext2SL {o} {lib : SL} {lib' : @library o} (ext : lib_extends lib' lib) : @SL o :=
  MkSL lib' (lib_extends_safe _ _ ext (slib_safe lib)).

Lemma implies_all_in_bar_intersect_bars_left {o} :
  forall {lib : SL} (bar bar' : @BarLib o lib) F,
    all_in_bar bar F
    -> all_in_bar (intersect_bars bar bar') F.
Proof.
  introv a i j.
  simpl in *; exrepnd.
  assert (lib_extends lib1 lib) as ext1 by eauto 3 with slow.
  eapply (a (ext2SL ext1));simpl;auto; eauto 2 with slow.
Qed.
Hint Resolve implies_all_in_bar_intersect_bars_left : slow.

Lemma implies_all_in_bar_intersect_bars_right {o} :
  forall {lib : SL} (bar bar' : @BarLib o lib) F,
    all_in_bar bar F
    -> all_in_bar (intersect_bars bar' bar) F.
Proof.
  introv a i j.
  simpl in *; exrepnd.
  assert (lib_extends lib2 lib) as ext1 by eauto 3 with slow.
  eapply (a (ext2SL ext1));simpl;auto; eauto 2 with slow.
Qed.
Hint Resolve implies_all_in_bar_intersect_bars_right : slow.


(* the bar that contains everything *)
Definition trivial_bar {o} (lib : @library o) : BarLib lib.
Proof.
  exists (fun (lib' : library) => lib_extends lib' lib).

  - introv ext.
    exists lib; dands; eauto 2 with slow.

  - introv ext; auto.
Defined.

Definition const_bar {o} (lib : @library o) : bar_lib :=
  fun lib' => lib = lib'.

Lemma BarLibBars_refl {o} :
  forall (lib : @library o), BarLibBars (const_bar lib) lib.
Proof.
  introv i.
  exists lib; dands; tcsp; eauto 2 with slow.
Qed.
Hint Resolve BarLibBars_refl : slow.

Lemma BarLibExt_refl {o} :
  forall (lib : @library o), BarLibExt (const_bar lib) lib.
Proof.
  introv b; unfold const_bar in *; simpl in *; repndors; subst; tcsp; eauto 2 with slow.
Qed.
Hint Resolve BarLibExt_refl : slow.

Definition is_zero_choice_sequence_name (n : choice_sequence_name) :=
  match csn_kind n with
  | cs_kind_nat 0 => True
  | _ => False
  end.

Fixpoint name_in_library {o} (name : choice_sequence_name) (lib : @library o) : Prop :=
  match lib with
  | [] => False
  | entry :: entries =>
    same_entry_name (entry_name_cs name) (entry2name entry)
    \/
    (~ same_entry_name (entry_name_cs name) (entry2name entry)
       # name_in_library name entries)
  end.

(*Definition csc_seq_default {o} (l : list nat) : nat -> @ChoiceSeqVal o :=
  fun n => if lt_dec n (length l) then mkc_nat (nth n l 0) else mkc_zero.*)

(*Definition csc_seq_restr {o} (l : list nat) : @RestrictionPred o :=
  fun n t =>
    if lt_dec n (length l)
    then t = mkc_nat (nth n l 0)
    else exists (i : nat), t = mkc_nat i.

Lemma csc_seq_restr_default {o} (l : list nat) :
  forall n, @csc_seq_restr o l n (natSeq2default l n).
Proof.
  introv; simpl.
  unfold csc_seq_restr, csc_seq_default.
  boolvar; tcsp.
  exists 0.
  apply cterm_eq; simpl; auto.
Qed.
Hint Resolve csc_seq_restr_default : slow.*)

Definition is_cs_entry {o} (e : @inf_library_entry o) :=
  match e with
  | inf_lib_cs _ _ => True
  | _ => False
  end.

Lemma is_cs_entry_implies_same_entry_name {o} :
  forall (e : @inf_library_entry o),
    is_cs_entry e
    -> same_entry_name (inf_entry2name e) (inf_entry2name e).
Proof.
  introv isc.
  destruct e; simpl in *; tcsp.
Qed.
Hint Resolve is_cs_entry_implies_same_entry_name : slow.

Lemma entry_in_inf_library_shift_inf_lib_implies {o} :
  forall (entry : @inf_library_entry o) inflib,
    entry_in_inf_library entry (shift_inf_lib inflib)
    -> ~ same_entry_name (inf_entry2name (inflib 0)) (inf_entry2name entry)
    -> entry_in_inf_library entry inflib.
Proof.
  introv i d.
  unfold entry_in_inf_library in *; repndors; exrepnd.

  - left.
    exists (S n); simpl; right; dands; auto.

  - right; left.
    unfold inf_entry_in_inf_library_cs_default in *; repnd; dands; auto.
    introv.
    destruct n; simpl; auto; apply i0.

  - right; right.
    unfold inf_entry_in_inf_library_ref_default in *; repnd; dands; auto.
    introv.
    destruct n; simpl; auto; apply i0.
Qed.
Hint Resolve entry_in_inf_library_shift_inf_lib_implies : slow.

Lemma nth_entry_in_inf_library {o} :
  forall n (inflib : @inf_library o),
    is_cs_entry (inflib n)
    -> exists entry,
      same_entry_name (inf_entry2name entry) (inf_entry2name (inflib n))
      /\ entry_in_inf_library entry inflib.
Proof.
  induction n; introv iscs.

  - exists (inflib 0); dands; eauto 3 with slow.
    left; exists 1; simpl; tcsp.

  - pose proof (IHn (shift_inf_lib inflib)) as IHn.
    repeat (autodimp IHn hyp); exrepnd.

    destruct (same_entry_name_dec (inf_entry2name (inflib 0)) (inf_entry2name entry)) as [d|d].

    + exists (inflib 0); dands; eauto 3 with slow.
      left; exists 1; simpl; tcsp.

    + exists entry; dands; eauto 3 with slow.
Qed.

Lemma same_entry_name_entry_name_cs_implies_is_cs_entry {o} :
  forall name (e : @inf_library_entry o),
    same_entry_name (entry_name_cs name) (inf_entry2name e)
    -> is_cs_entry e.
Proof.
  introv h.
  destruct e; simpl in *; subst; tcsp.
Qed.
Hint Resolve same_entry_name_entry_name_cs_implies_is_cs_entry : slow.

Lemma same_entry_name_cs_implies_eq :
  forall name n,
    same_entry_name (entry_name_cs name) n
    -> n = entry_name_cs name.
Proof.
  introv h.
  destruct n; simpl in *; subst; tcsp.
Qed.

Lemma same_entry_name_cs_implies_eq_rev :
  forall name n,
    same_entry_name n (entry_name_cs name)
    -> n = entry_name_cs name.
Proof.
  introv h.
  destruct n; simpl in *; subst; tcsp.
Qed.

Require Export Classical_Prop.

Lemma all_choice_sequence_names_in_inf_lib {o} :
  forall (inflib : @inf_library o) (name : choice_sequence_name),
    is_nat_or_seq_kind name
    ->
    exists entry,
      entry_in_inf_library entry inflib
      /\ entry_name_cs name = inf_entry2name entry.
Proof.
  introv ins.

  destruct (classic (exists n, same_entry_name (inf_entry2name (inflib n)) (entry_name_cs name))) as [d|d].

  {
    exrepnd.
    pose proof (nth_entry_in_inf_library n inflib) as q.
    repeat (autodimp q hyp); eauto 3 with slow;[]; exrepnd.
    exists entry; dands; auto.
    apply same_entry_name_cs_implies_eq_rev in d0.
    rewrite d0 in *.
    apply same_entry_name_cs_implies_eq_rev in q1; auto.
  }

  {
    exists (@choice_sequence_name2inf_entry o name); simpl; dands; auto.
    right; eauto 3 with slow.
  }
Qed.

Definition extend_choice_seq_entry_lawless_upto {o}
           (e1 : @ChoiceSeqEntry o)
           (e2 : @ChoiceSeqEntry o)
           (n  : nat) : Prop :=
  match e1, e2 with
  | MkChoiceSeqEntry _ vals1 (csc_type d1 M1 Md1),
    MkChoiceSeqEntry _ vals2 (csc_type d2 M2 Md2) =>
    same_restrictions (csc_type d1 M1 Md1) (csc_type d2 M2 Md2)
    /\ exists vals,
        vals1 = vals2 ++ vals
        /\ length vals = n - length vals2
        /\ forall n v, select n vals = Some v -> M1 (length vals2 + n) v (*exists k, v = mkc_nat k*)
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

Definition add_cs_if_not_in {o} name (lib : @library o) :=
  match find_cs lib name with
  | Some e => lib
  | None => choice_sequence_name2entry name :: lib
  end.

Lemma select_nil :
  forall {A} n, @select A n [] = None.
Proof.
  introv; destruct n; simpl; auto.
Qed.
Hint Rewrite @select_nil : slow list.

Lemma choice_sequence_satisfies_restriction_nil {o} :
  forall r, @choice_sequence_satisfies_restriction o [] r.
Proof.
  introv.
  unfold choice_sequence_satisfies_restriction.
  destruct r; simpl in *; introv; autorewrite with slow list; tcsp.
Qed.
Hint Resolve choice_sequence_satisfies_restriction_nil : slow.

Lemma safe_library_entry_choice_sequence_name2entry {o} :
  forall name,
    @safe_library_entry o (choice_sequence_name2entry name).
Proof.
  introv.
  unfold safe_library_entry; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve safe_library_entry_choice_sequence_name2entry : slow.

Lemma find_cs_none_implies_diff_entry_names {o} :
  forall name (e : @library_entry o) lib,
    find_cs lib name = None
    -> List.In e lib
    -> diff_entry_names (choice_sequence_name2entry name) e = true.
Proof.
  induction lib; introv f i; simpl; tcsp.
  simpl in *; repndors; subst; tcsp.

  - destruct e; simpl in *; ginv.
    boolvar; subst; tcsp.
    unfold diff_entry_names; simpl; boolvar;tcsp.

  - destruct a; simpl in *; tcsp.
    boolvar; subst; tcsp.
Qed.
Hint Resolve find_cs_none_implies_diff_entry_names : slow.

Lemma find_cs_none_implies_non_shadowed_entry_choice_sequence_name2entry {o} :
  forall name (lib : @library o),
    find_cs lib name = None
    -> non_shadowed_entry (choice_sequence_name2entry name) lib.
Proof.
  introv f.
  unfold non_shadowed_entry.
  rewrite forallb_forall; introv i; eauto 3 with slow.
Qed.
Hint Resolve find_cs_none_implies_non_shadowed_entry_choice_sequence_name2entry : slow.

Lemma find_cs_none_implies_lib_extends_choice_sequence_name2entry {o} :
  forall name (lib : @library o),
    find_cs lib name = None
    -> lib_extends (choice_sequence_name2entry name :: lib) lib.
Proof.
  introv f.
  Print lib_extends.
  apply implies_lib_extends_cons_left; eauto 3 with slow.
Qed.
Hint Resolve find_cs_none_implies_lib_extends_choice_sequence_name2entry : slow.

Lemma lib_extends_add_cs_if_not_in_name {o} :
  forall name (lib : @library o),
    lib_extends (add_cs_if_not_in name lib) lib.
Proof.
  introv.
  unfold add_cs_if_not_in.
  remember (find_cs lib name) as w; symmetry in Heqw; destruct w; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_add_cs_if_not_in_name : slow.

Lemma find_cs_some_implies_name_in_library {o} :
  forall name (lib : @library o) c,
    find_cs lib name = Some c
    -> name_in_library name lib.
Proof.
  induction lib; introv h; simpl in *; ginv.
  destruct a; simpl in *; boolvar; tcsp; right; dands; eauto.
Qed.
Hint Resolve find_cs_some_implies_name_in_library : slow.

Lemma name_in_library_add_cs_if_not_in {o} :
  forall name (lib : @library o),
    name_in_library name (add_cs_if_not_in name lib).
Proof.
  introv.
  unfold add_cs_if_not_in.
  remember (find_cs lib name) as f; symmetry in Heqf; destruct f; simpl; tcsp; eauto 3 with slow.
Qed.
Hint Resolve name_in_library_add_cs_if_not_in : slow.

Lemma inf_entry_extends_implies_matching_inf_entries {o} :
  forall (entry : @inf_library_entry o) e x,
    inf_entry_extends entry e
    -> inf_matching_entries x e
    -> matching_inf_entries x entry.
Proof.
  introv h q.
  unfold matching_inf_entries.
  unfold inf_matching_entries in *.
  unfold inf_entry_extends in *.
  destruct entry; simpl in *; tcsp; destruct e; repndors; repnd; subst; tcsp.
Qed.
Hint Resolve inf_entry_extends_implies_matching_inf_entries : slow.

Lemma entry_in_inf_library_n_implies_entry_in_inf_library_extends {o} :
  forall n (entry : @inf_library_entry o) e infLib,
    entry_in_inf_library_n n entry infLib
    -> inf_entry_extends entry e
    -> entry_in_inf_library_extends e n infLib.
Proof.
  induction n; introv h q; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.
  right; dands; eauto 3 with slow.
  introv xx; destruct h0; eauto 3 with slow.
Qed.
Hint Resolve entry_in_inf_library_n_implies_entry_in_inf_library_extends : slow.

Lemma is_default_inf_choice_sequence_implies_is_default_choice_sequence {o} :
  forall (ivals : @InfChoiceSeqVals o) vals restr1 restr2,
    is_default_inf_choice_sequence ivals restr1
    -> same_restrictions restr1 restr2
    -> inf_choice_sequence_vals_extend ivals vals
    -> is_default_choice_sequence vals restr2.
Proof.
  introv h q w.
  unfold is_default_inf_choice_sequence in *.
  unfold is_default_choice_sequence.
  unfold same_restrictions in *.
  unfold inf_choice_sequence_vals_extend in *.
  destruct restr1, restr2 in *; repnd; tcsp; introv z.
  - applydup w in z; subst.
    rewrite <- q0; auto.
  - applydup w in z; subst.
    rewrite <- q; eauto.
Qed.
Hint Resolve is_default_inf_choice_sequence_implies_is_default_choice_sequence : slow.

Lemma is_default_inf_choice_seq_entry_implies_is_default_choice_seq_entry {o} :
  forall (entry : @InfChoiceSeqEntry o) e,
    is_default_inf_choice_seq_entry entry
    -> inf_choice_sequence_entry_extend entry e
    -> is_default_choice_seq_entry e.
Proof.
  introv h q.
  unfold is_default_inf_choice_seq_entry in *.
  unfold inf_choice_sequence_entry_extend in *; repnd.
  unfold is_default_choice_seq_entry.
  destruct entry, e; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve is_default_inf_choice_seq_entry_implies_is_default_choice_seq_entry: slow.

Lemma is_cs_default_inf_entry_implies_is_cs_default_entry {o} :
  forall (entry : @inf_library_entry o) e,
    is_cs_default_inf_entry entry
    -> inf_entry_extends entry e
    -> is_cs_default_entry e.
Proof.
  introv h q.
  unfold is_cs_default_inf_entry in *.
  unfold is_cs_default_entry.
  unfold inf_entry_extends in *.
  destruct entry, e in *; repnd; dands; subst; tcsp; eauto 3 with slow.
Qed.
Hint Resolve is_cs_default_inf_entry_implies_is_cs_default_entry : slow.

Lemma inf_entry_in_inf_library_default_implies_entry_in_inf_library_cs_default {o} :
  forall (entry : @inf_library_entry o) e infLib,
    safe_library_entry e
    -> inf_entry_in_inf_library_cs_default entry infLib
    -> inf_entry_extends entry e
    -> entry_in_inf_library_cs_default e infLib.
Proof.
  introv safe h q.
  unfold inf_entry_in_inf_library_cs_default in *; repnd.
  unfold entry_in_inf_library_cs_default; dands; eauto 3 with slow;[].
  { introv xx; destruct (h0 n); eauto 3 with slow. }
Qed.
Hint Resolve inf_entry_in_inf_library_default_implies_entry_in_inf_library_cs_default : slow.

Lemma is_ref_default_inf_entry_implies_is_ref_default_entry {o} :
  forall (entry : @inf_library_entry o) e,
    is_ref_default_inf_entry entry
    -> inf_entry_extends entry e
    -> is_ref_default_entry e.
Proof.
  introv h q.
  unfold is_ref_default_inf_entry in *.
  unfold is_ref_default_entry.
  unfold inf_entry_extends in *.
  destruct entry, e in *; repnd; dands; subst; tcsp; eauto 3 with slow.
Qed.
Hint Resolve is_ref_default_inf_entry_implies_is_ref_default_entry : slow.

Lemma inf_entry_in_inf_library_default_implies_entry_in_inf_library_ref_default {o} :
  forall (entry : @inf_library_entry o) e infLib,
    safe_library_entry e
    -> inf_entry_in_inf_library_ref_default entry infLib
    -> inf_entry_extends entry e
    -> entry_in_inf_library_ref_default e infLib.
Proof.
  introv safe h q.
  unfold inf_entry_in_inf_library_ref_default in *; repnd.
  unfold entry_in_inf_library_ref_default; dands; eauto 3 with slow;[].
  { introv xx; destruct (h0 n); eauto 3 with slow. }
Qed.
Hint Resolve inf_entry_in_inf_library_default_implies_entry_in_inf_library_ref_default : slow.

Lemma implies_inf_lib_extends_cons2 {o} :
  forall (infLib : @inf_library o) lib e entry,
    safe_library_entry e
    -> inf_lib_extends infLib lib
    -> safe_library lib
    -> entry_in_inf_library entry infLib
    -> inf_entry_extends entry e
    -> inf_lib_extends infLib (e :: lib).
Proof.
  introv safee ext safel i ie.
  destruct ext as [ext safe].
  split; eauto 2 with slow;[].

  introv j; simpl in *; repndors; repnd; subst; tcsp.

  unfold  entry_in_inf_library in *; repndors; exrepnd.

  { left; exists n; auto; eauto 3 with slow. }

  { right; left; eauto 3 with slow. }

  { right; right; eauto 3 with slow. }
Qed.
Hint Resolve implies_inf_lib_extends_cons2 : slow.

Lemma inf_choice_sequence_vals_extend_nil {o} :
  forall (entry : @InfChoiceSeqVals o),
    inf_choice_sequence_vals_extend entry [].
Proof.
  introv; unfold inf_choice_sequence_vals_extend; introv h; autorewrite with slow in *; ginv.
Qed.
Hint Resolve inf_choice_sequence_vals_extend_nil : slow.

Lemma correct_cs_restriction_implies_same_restrictions2 {o} :
  forall name (restr : @ChoiceSeqRestriction o),
    is_nat_or_seq_kind name
    -> correct_cs_restriction name restr
    -> same_restrictions restr (choice_sequence_name2restriction name).
Proof.
  introv isn cor.
  unfold correct_cs_restriction in *.
  unfold same_restrictions.
  unfold is_nat_or_seq_kind in *.
  destruct name as [name k]; simpl in *.
  destruct k; boolvar; subst; tcsp.
  unfold is_nat_seq_restriction in *.
  destruct restr; simpl in *; repnd; dands; tcsp; introv.

  - unfold natSeq2default.
    remember (select n l) as s; symmetry in Heqs; destruct s.

    + pose proof (cor0 n) as q; autodimp q hyp; eauto 3 with slow.
      unfold cterm_is_nth in *; exrepnd.
      rewrite q1 in *; ginv.

    + pose proof (cor1 n) as q; autodimp q hyp; eauto 3 with slow.
      apply nth_select2; auto.

  - unfold natSeq2restrictionPred.
    remember (select n l) as s; symmetry in Heqs; destruct s.

    + pose proof (cor2 n v) as q; autodimp q hyp; eauto 3 with slow.
      rewrite q.
      unfold cterm_is_nth.
      split; intro h; exrepnd.

      * rewrite h1 in *; ginv.

      * subst; eexists; dands; eauto.

    + pose proof (cor n v) as q; autodimp q hyp; eauto 3 with slow.
      apply nth_select2; auto.
Qed.
Hint Resolve correct_cs_restriction_implies_same_restrictions2 : slow.

Lemma implies_inf_entry_extends_choice_sequence_name2entry {o} :
  forall name (e : @inf_library_entry o),
    is_nat_or_seq_kind name
    -> safe_inf_library_entry e
    -> entry_name_cs name = inf_entry2name e
    -> inf_entry_extends e (choice_sequence_name2entry name).
Proof.
  introv isn safe h; destruct e; simpl in *; tcsp; ginv; dands; auto; eauto 3 with slow.
  unfold inf_choice_sequence_entry_extend; simpl; dands; eauto 3 with slow.

  unfold safe_inf_choice_sequence_entry in *.
  destruct entry; simpl in *; repnd; auto.
  apply correct_cs_restriction_implies_same_restrictions2; auto.
Qed.

Lemma inf_lib_extends_add_cs_if_not_in {o} :
  forall name inflib (lib : @library o),
    is_nat_or_seq_kind name
    -> safe_library lib
    -> safe_inf_library inflib
    -> inf_lib_extends inflib lib
    -> inf_lib_extends inflib (add_cs_if_not_in name lib).
Proof.
  introv ins safe safei h.
  unfold add_cs_if_not_in.
  remember (find_cs lib name) as f; symmetry in Heqf; destruct f; auto.
  pose proof (all_choice_sequence_names_in_inf_lib inflib name) as q.
  repeat (autodimp q hyp); exrepnd.
  eapply implies_inf_lib_extends_cons2; eauto; eauto 3 with slow.
  apply implies_inf_entry_extends_choice_sequence_name2entry; auto; eauto 3 with slow.
Qed.
Hint Resolve inf_lib_extends_add_cs_if_not_in : slow.

Lemma exists_extend_library_with_name {o} :
  forall (infLib : @inf_library o) name lib,
    is_nat_or_seq_kind name
    -> safe_library lib
    -> inf_lib_extends infLib lib
    ->
    exists lib',
      lib_extends lib' lib
      /\ name_in_library name lib'
      /\ inf_lib_extends infLib lib'.
Proof.
  introv ins safe ext.
  assert (safe_inf_library infLib) as safei by eauto 3 with slow.
  exists (add_cs_if_not_in name lib); dands; eauto 3 with slow.
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

Lemma implies_preserves_correct_restriction_name_csc_type {o} :
  forall name d1 d2 (M1 M2 : @RestrictionPred o) Md1 Md2,
    (forall n, d1 n = d2 n)
    -> (forall n v, M1 n v <-> M2 n v)
    -> correct_cs_restriction name (csc_type d1 M1 Md1)
    -> correct_cs_restriction name (csc_type d2 M2 Md2).
Proof.
  introv h w cor.
  destruct name as [name kind], kind as [n|seq]; simpl in *; tcsp.

  - unfold correct_cs_restriction in *; simpl in *; boolvar; tcsp.
    repnd; dands; introv.
    { rewrite <- h; auto. }
    { rewrite <- w; auto. }

  - unfold correct_cs_restriction in *; simpl in *; dands; repnd; introv len.
    { rewrite <- h; auto. }
    { rewrite <- h; auto. }
    { rewrite <- w; auto. }
    { rewrite <- w; auto. }
Qed.
Hint Resolve implies_preserves_correct_restriction_name_csc_type : slow.

Lemma implies_preserves_correct_restriction_name_csc_type2 {o} :
  forall name d1 d2 (M1 M2 : @RestrictionPred o) Md1 Md2,
    (forall n, d2 n = d1 n)
    -> (forall n v, M2 n v <-> M1 n v)
    -> correct_cs_restriction name (csc_type d1 M1 Md1)
    -> correct_cs_restriction name (csc_type d2 M2 Md2).
Proof.
  introv h w cor.
  eapply implies_preserves_correct_restriction_name_csc_type;[| |eauto]; tcsp.
  introv; symmetry; auto.
Qed.
Hint Resolve implies_preserves_correct_restriction_name_csc_type2 : slow.

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

  destruct restr2; simpl in *; ginv; exrepnd; subst; tcsp; dands; eauto 3 with slow.
  introv i.

  destruct (lt_dec n0 (length vals2)) as [z|z].

  { rewrite select_app_left in i; auto.
    apply ext0; apply safe; auto. }

  { rewrite select_app_r in i; try omega.
    apply ext2 in i.
    rewrite le_plus_minus_r in i; auto; try omega. }
Qed.
Hint Resolve extend_library_entry_lawless_upto_preserves_safe_library : slow.

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

Lemma implies_extend_library_lawless_upto_app {o} :
  forall name n (lib1 lib1' lib2 lib2' : @library o),
    extend_library_lawless_upto lib1' lib1 name n
    -> extend_library_lawless_upto lib2' lib2 name n
    -> extend_library_lawless_upto (lib1' ++ lib2') (lib1 ++ lib2) name n.
Proof.
  induction lib1; introv ext1 ext2; destruct lib1'; simpl in *; tcsp.
Qed.
Hint Resolve implies_extend_library_lawless_upto_app : slow.

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

(* [lib1] is shadowed by [lib2] *)
Definition shadowed_library {o} (lib1 lib2 : @library o) : Prop :=
  forall entry,
    List.In entry lib1
    -> exists entry', List.In entry' lib2 /\ matching_entries entry entry'.

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

Definition memNat_restriction {o} (restr : @ChoiceSeqRestriction o) : Prop :=
  match restr with
  | csc_type d M Md => forall n x, M n x <-> is_nat n x
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

Lemma extends_snoc_implies_entry_in_inf_library_extends {o} :
  forall (infLib : @inf_library o) lib e,
    inf_lib_extends infLib (snoc lib e)
    -> (forall x, List.In x lib -> diff_entry_names e x = true)
    -> (exists k, entry_in_inf_library_extends e k infLib)
       \/ entry_in_inf_library_cs_default e infLib
       \/ entry_in_inf_library_ref_default e infLib.
Proof.
  introv ext imp.
  destruct ext as [ext safe].
  apply (ext e); clear ext; eauto 2 with slow.
Qed.

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

Lemma select_inf_choice_seq_vals2choice_seq_vals_implies {o} :
  forall k n v (iseq : @InfChoiceSeqVals o),
    select n (inf_choice_seq_vals2choice_seq_vals iseq k) = Some v
    -> n < k /\ v = iseq n.
Proof.
  induction k; introv i; simpl in *; tcsp; autorewrite with list in *; ginv;[].
  destruct n; simpl in *; ginv.

  - dands; tcsp; try omega.

  - applydup IHk in i; exrepnd; subst.
    dands; auto; try omega.
Qed.

Lemma same_restrictions_preserves_inf_choice_sequence_satisfies_restriction {o} :
  forall (restr1 restr2 : @ChoiceSeqRestriction o) ivals,
    same_restrictions restr1 restr2
    -> inf_choice_sequence_satisfies_restriction ivals restr1
    -> inf_choice_sequence_satisfies_restriction ivals restr2.
Proof.
  introv same sat.
  destruct restr1, restr2; simpl in *; repnd; tcsp; introv.
  { apply same; eauto. }
  { rewrite <- same; eauto. }
Qed.
Hint Resolve same_restrictions_preserves_inf_choice_sequence_satisfies_restriction : slow.

Lemma shift_inf_choice_seq_vals_ntimes_app {o} :
  forall n k (iseq : @InfChoiceSeqVals o),
    shift_inf_choice_seq_vals_ntimes iseq n k = iseq (n + k).
Proof.
  induction n; introv; simpl; auto.
  rewrite IHn; clear IHn; simpl; auto.
Qed.
Hint Rewrite @shift_inf_choice_seq_vals_ntimes_app : slow.

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
    [|exists (lib_ref name1 entry); simpl; dands; auto
     |exists (lib_abs opabs0 vars0 rhs0 correct0); simpl; dands; auto];[].

  {
    destruct (choice_sequence_name_deq name name1) as [d|d]; subst;
      [|exists (lib_cs name1 entry); simpl; boolvar; subst; tcsp];[].

    destruct entry as [vals restr].
    destruct restr;
      [|exists (lib_cs name1 (MkChoiceSeqEntry _ vals (csc_coq_law f))); simpl; boolvar; subst; tcsp];[].

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

    - exists (inf_choice_seq_vals2choice_seq_vals (shift_inf_choice_seq_vals_ntimes ivals (length vals)) (k - length vals)).
      dands; auto; autorewrite with slow; auto.

      { apply inf_choice_seq_vals2choice_seq_vals_shift; auto. }

      { introv j.
        applydup @select_inf_choice_seq_vals2choice_seq_vals_implies in j.
        exrepnd; subst; autorewrite with slow.
        pose proof (safe (infLib k0)) as h.

        autodimp h hyp.
        {
          apply implies_entry_in_inf_library.
          rewrite <- Heqinfentry; simpl.
          eauto 2 with slow.
        }

        rewrite <- Heqinfentry in h; simpl in h; repnd.
        eapply same_restrictions_preserves_inf_choice_sequence_satisfies_restriction in h;[|eauto].
        pose proof (h (length vals + n0)) as w; clear h; auto. }

    - eapply inf_entry_extends_implies_entry_in_inf_library_extends_same_names_lt;
        simpl; eauto; simpl; auto.
      rewrite <- Heqinfentry; simpl; dands; auto.
      unfold inf_choice_sequence_entry_extend; simpl; dands; auto.
      introv h.
      rewrite select_inf_choice_seq_vals2choice_seq_vals in h; boolvar; ginv.
  }
Qed.

Lemma extend_library_entry_lawless_upto_choice_sequence_name2entry_upto_same {o} :
  forall n m name (restr : @ChoiceSeqRestriction o),
    m <= n
    -> is_nat_or_seq_kind name
    -> correct_cs_restriction name restr
    -> extend_library_entry_lawless_upto
         (choice_sequence_name2entry_upto n name restr)
         (choice_sequence_name2entry_upto m name restr)
         name
         n.
Proof.
  introv lena isn cor.
  unfold extend_library_entry_lawless_upto; simpl; boolvar; auto; tcsp; GC.
  unfold is_nat_or_seq_kind in *.
  unfold correct_cs_restriction in *.
  destruct name as [name kd]; simpl in *.
  destruct kd as [kd|seq]; subst; boolvar; tcsp;[|].

  - unfold is_nat_cs_restriction in *.
    destruct restr; auto; tcsp; repnd; GC; simpl in *; autorewrite with slow.
    dands; tcsp.
    unfold choice_sequence_name2choice_seq_vals_upto; simpl.
    exists (fun2list (n - m) (fun _ => @mkc_zero o)); autorewrite with slow.
    dands; auto; try omega.

    + apply fun2list_split; auto; try omega.

    + introv h.
      rewrite select_fun2list in h; boolvar; ginv.
      apply cor; eauto 3 with slow.

  - unfold is_nat_seq_restriction in *; GC.
    destruct restr; auto; tcsp; simpl in *; autorewrite with slow in *; repnd.
    dands; tcsp.
    unfold choice_sequence_name2choice_seq_vals_upto; simpl.
    exists (fun2list (n - m) (fun k => @natSeq2default o seq (k + m))).
    dands; auto; autorewrite with slow; try omega.

    + apply fun2list_split; auto.

    + introv h.
      rewrite select_fun2list in h; boolvar; ginv.
      unfold natSeq2default.
      rewrite (Nat.add_comm m n0).
      remember (select (n0 + m) seq) as s; symmetry in Heqs; destruct s.

      * apply cor2; eauto 3 with slow.
        unfold cterm_is_nth; exists n1; eauto.

      * apply cor; eauto 3 with slow.
        apply nth_select2; auto.
Qed.
Hint Resolve extend_library_entry_lawless_upto_choice_sequence_name2entry_upto_same : slow.

Hint Rewrite Nat.sub_diag : slow nat.
Hint Rewrite Max.max_0_r : slow nat.

Lemma extend_library_entry_lawless_upto_choice_sequence_name2entry_upto_same_max {o} :
  forall n m name (restr : @ChoiceSeqRestriction o),
    is_nat_or_seq_kind name
    -> correct_cs_restriction name restr
    -> extend_library_entry_lawless_upto
         (choice_sequence_name2entry_upto (Peano.max n m) name restr)
         (choice_sequence_name2entry_upto m name restr)
         name
         n.
Proof.
  introv isn cor.
  unfold extend_library_entry_lawless_upto; simpl; boolvar; auto; tcsp; GC.
  unfold is_nat_or_seq_kind in *.
  unfold correct_cs_restriction in *.
  destruct name as [name kd]; simpl in *.
  destruct kd as [kd|seq]; subst; boolvar; tcsp;[|].

  - unfold is_nat_cs_restriction in *.
    destruct restr; auto; tcsp; repnd; GC; simpl in *; autorewrite with slow.
    dands; tcsp.
    unfold choice_sequence_name2choice_seq_vals_upto; simpl.
    exists (fun2list ((Peano.max n m) - m) (fun _ => @mkc_zero o)); autorewrite with slow.
    dands; auto; try omega.

    + apply fun2list_split; auto; try omega; eauto 3 with slow.

    + rewrite <- Nat.sub_max_distr_r; autorewrite with slow nat; auto.

    + introv h.
      rewrite select_fun2list in h; boolvar; ginv.
      apply cor; eauto 3 with slow.

  - unfold is_nat_seq_restriction in *; GC.
    destruct restr; auto; tcsp; simpl in *; autorewrite with slow in *; repnd.
    dands; tcsp.
    unfold choice_sequence_name2choice_seq_vals_upto; simpl.
    exists (fun2list ((Peano.max n m) - m) (fun k => @natSeq2default o seq (k + m))).
    dands; auto; autorewrite with slow; try omega; eauto 3 with slow.

    + apply fun2list_split; auto; eauto 3 with slow.

    + rewrite <- Nat.sub_max_distr_r; autorewrite with slow nat; auto.

    + introv h.
      rewrite select_fun2list in h; boolvar; ginv.
      unfold natSeq2default.
      rewrite (Nat.add_comm m n0).
      remember (select (n0 + m) seq) as s; symmetry in Heqs; destruct s.

      * apply cor2; eauto 3 with slow.
        unfold cterm_is_nth; exists n1; eauto.

      * apply cor; eauto 3 with slow.
        apply nth_select2; auto.
Qed.
Hint Resolve extend_library_entry_lawless_upto_choice_sequence_name2entry_upto_same_max : slow.

Lemma implies_inf_lib_extends_snoc_default {o} :
  forall (infLib : @inf_library o) lib e,
    inf_lib_extends infLib lib
    -> entry_in_inf_library_cs_default e infLib
    -> inf_lib_extends infLib (snoc lib e).
Proof.
  introv ext i.
  destruct ext as [ext safe].
  split; eauto 2 with slow.
  introv safe'; apply safe; eauto 2 with slow.
Qed.
Hint Resolve implies_inf_lib_extends_snoc_default : slow.

Lemma matching_entries_choice_sequence_name2entry_upto_refl {o} :
  forall n name (restr : @ChoiceSeqRestriction o),
    matching_entries
      (choice_sequence_name2entry_upto n name restr)
      (choice_sequence_name2entry_upto n name restr).
Proof.
  introv; tcsp.
Qed.

Lemma extend_library_entry_lawless_upto_choice_sequence_name2entry_upto_diff {o} :
  forall name1 name2 n1 n2 (restr : @ChoiceSeqRestriction o),
    name1 <> name2
    -> extend_library_entry_lawless_upto
         (choice_sequence_name2entry_upto n2 name2 restr)
         (choice_sequence_name2entry_upto n2 name2 restr)
         name1
         n1.
Proof.
  introv extend_library_entry_lawless_upto; simpl; boolvar; tcsp.
Qed.
Hint Resolve extend_library_entry_lawless_upto_choice_sequence_name2entry_upto_diff : slow.

Fixpoint ntimes_fun {T} (pos : nat) (n : nat) (t : nat -> T) : list T :=
  match n with
  | 0 => []
  | S n => t pos :: ntimes_fun (S pos) n t
  end.

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

Lemma length_ntimes_fun :
  forall {A} (d : nat -> A) n pos, length (ntimes_fun pos n d) = n.
Proof.
  induction n; simpl; tcsp.
Qed.
Hint Rewrite @length_ntimes_fun : slow.

Lemma select_ntimes_fun_implies :
  forall {A} (d : nat -> A) n pos x m,
    select m (ntimes_fun pos n d) = Some x -> x = d (pos + m).
Proof.
  induction n; introv i; autorewrite with slow in *; ginv.
  simpl in *.
  destruct m; simpl in *; ginv; tcsp.
  apply IHn in i; simpl in *.
  rewrite <- plus_n_Sm; auto.
Qed.

Lemma exists_extend_library_entry_lawless_upto_default {o} :
  forall name n (entry : @library_entry o),
  exists entry',
    extend_library_entry_lawless_upto entry' entry name n.
Proof.
  introv; destruct entry;
    [|exists (lib_ref name0 entry); simpl; auto
     |exists (lib_abs opabs vars rhs correct); simpl; auto];[].

  destruct (choice_sequence_name_deq name name0) as [dn|dn]; subst;
    [|exists (lib_cs name0 entry); simpl; boolvar; subst; tcsp];[].

  destruct entry as [vals restr].

  destruct restr;
    [|exists (lib_cs name0 (MkChoiceSeqEntry _ vals (csc_coq_law f))); simpl; boolvar; subst; tcsp];[].

  exists (lib_cs
            name0
            (MkChoiceSeqEntry
               _
               (vals ++ ntimes_fun (length vals) (n - length vals) d)
               (csc_type d typ typd))).
  simpl; boolvar; subst; tcsp; GC.
  dands; auto; tcsp;[].

  eexists; dands; eauto; autorewrite with slow; auto;[].
  introv i.
  apply select_ntimes_fun_implies in i; subst; auto.
Qed.

Lemma implies_inf_lib_extends_snoc_ref_default {o} :
  forall (infLib : @inf_library o) lib e,
    inf_lib_extends infLib lib
    -> entry_in_inf_library_ref_default e infLib
    -> inf_lib_extends infLib (snoc lib e).
Proof.
  introv ext i.
  destruct ext as [ext safe].
  split; eauto 2 with slow.
  introv safe'; apply safe; eauto 2 with slow.
Qed.
Hint Resolve implies_inf_lib_extends_snoc_ref_default : slow.

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

    repndors; exrepnd.

    {
      pose proof (entry_in_inf_library_extends_implies_extend_library_entry_lawless_upto k infLib a name n) as h.
      repeat (autodimp h hyp); eauto 2 with slow.
      exrepnd.

      exists (snoc lib' entry'); dands; auto; eauto 2 with slow.
    }

    {
      dup q as w.
      apply entry_in_inf_library_cs_default_implies_exists in q; exrepnd.
      destruct (choice_sequence_name_deq name name0); subst.
      - exists (snoc lib' (choice_sequence_name2entry_upto (Peano.max n n0) name0 restr)); dands; eauto 3 with slow.
        apply implies_inf_lib_extends_snoc_default; eauto 3 with slow.
        eapply entry_in_inf_library_default_choice_sequence_name2entry_upto; try exact w; auto;
          apply matching_entries_choice_sequence_name2entry_upto_refl.
      - exists (snoc lib' (choice_sequence_name2entry_upto n0 name0 restr)); dands; eauto 3 with slow.
    }

    {
      dup q as w.
      apply entry_in_inf_library_ref_default_implies_exists in q; exrepnd.
      subst; simpl in *; GC.
      exists (snoc lib' (mk_ref_entry name0 v restr)); dands; eauto 3 with slow.
      apply implies_extend_library_lawless_upto_snoc; eauto 3 with slow;tcsp.
    }

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

Lemma extend_library_lawless_upto_preserves_name_in_library {o} :
  forall (lib1 lib2 : @library o) name k,
    extend_library_lawless_upto lib1 lib2 name k
    -> name_in_library name lib2
    -> name_in_library name lib1.
Proof.
  induction lib1; introv ext n; simpl in *.

  - destruct lib2; tcsp.

  - destruct lib2; simpl in *; tcsp; repnd.
    repndors; repnd; tcsp.

    + unfold extend_library_entry_lawless_upto in *.
      destruct a; simpl in *; tcsp; ginv.
      destruct l; simpl in *; tcsp; boolvar; subst; tcsp; ginv; tcsp.

    + destruct a; simpl in *; subst; simpl in *; tcsp;
        try (complete (right; dands; tcsp; eauto 3 with slow));[].

      destruct l; simpl in *; tcsp; ginv; boolvar; subst; tcsp; ginv.
      right; dands; eauto 3 with slow.
Qed.
Hint Resolve extend_library_lawless_upto_preserves_name_in_library : slow.



Definition extend_seq_to_bar {o}
           (lib  : @library o)
           (safe : safe_library lib)
           (k    : nat)
           (name : choice_sequence_name)
           (isn  : is_nat_or_seq_kind name)
  : BarLib lib.
Proof.
  exists (fun (lib' : library) =>
            exists lib'',
              lib_extends lib'' lib
              /\ name_in_library name lib'
              /\ extend_library_lawless_upto lib' lib'' name k).

  - introv ext'; simpl.
    pose proof (exists_extend_library_with_name infLib name lib) as q.
    repeat (autodimp q hyp);[].
    exrepnd.

    pose proof (exists_extend_library_lawless_upto_following_infinite infLib name k lib') as w.
    repeat (autodimp w hyp); eauto 3 with slow.
    exrepnd.

    exists lib'0; dands; auto; eauto 3 with slow.
    exists lib'; dands; eauto 3 with slow.

  - introv j; exrepnd; eauto 3 with slow.
Defined.

Definition csc_seq_default {o} (l : list nat) : nat -> @ChoiceSeqVal o :=
  fun n => if lt_dec n (length l) then mkc_nat (nth n l 0) else mkc_zero.

Definition csc_seq_restr {o} (l : list nat) : @RestrictionPred o :=
  fun n t =>
    if lt_dec n (length l)
    then t = mkc_nat (nth n l 0)
    else exists (i : nat), t = mkc_nat i.

Lemma csc_seq_restr_default {o} (l : list nat) :
  forall n, @csc_seq_restr o l n (csc_seq_default l n).
Proof.
  introv; simpl.
  unfold csc_seq_restr, csc_seq_default.
  boolvar; tcsp.
  exists 0.
  apply cterm_eq; simpl; auto.
Qed.
Hint Resolve csc_seq_restr_default : slow.
