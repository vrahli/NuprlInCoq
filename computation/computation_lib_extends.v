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


Require Export terms_union.
Require Export computation_preserves_lib.
Require Import computation_choice_seq.
Require Export List.
Require Export list. (* Why? *)


(* This is entry2name *)

(*Definition opabs_of_lib_entry {o} (e : @library_entry o) : opabs :=
  match e with
  | lib_abs oa _ _ _ => oa
  end.*)

Definition matching_entries {o} (entry1 entry2 : @library_entry o) : Prop :=
  same_entry_name (entry2name entry1) (entry2name entry2).
(*  matching_entry_sign (opabs_of_lib_entry entry1) (opabs_of_lib_entry entry2).*)

Fixpoint entry_in_library {o} (entry : @library_entry o) (lib : library) : Prop :=
  match lib with
  | [] => False
  | entry' :: entries =>
    entry = entry'
    \/
    (~ matching_entries entry entry'
       # entry_in_library entry entries)
  end.


(* [vals1] extends [vals2] is [vals2] is an initial segment of [vals1] *)
Definition choice_sequence_vals_extend {o} (vals1 vals2 : @ChoiceSeqVals o) : Prop :=
  exists vals, vals1 = vals2 ++ vals.

(*

   TODO: We have to make sure that extensions satisfy the choice sequence
   restrictions!

 *)

(*(* MOVE: Move to library.v and use it in [csc_type]'s definition! *)
Definition Mem {o} := @ChoiceSeqVal o -> Prop.*)

Definition choice_sequence_satisfies_restriction {o}
           (vals       : @ChoiceSeqVals o)
           (constraint : ChoiceSeqRestriction) : Prop :=
  match constraint with
  | csc_type M =>
    forall n v, select n vals = Some v -> M n v (* TODO: Is that going to be enough? *)
  | csc_coq_law f =>
    forall (i : nat), i < length vals -> select i vals = Some (f i)
  | csc_res M =>
    forall n v, select n vals = Some v -> M n v
  end.


(* =============== *)
(* nat restriction *)
Definition is_nat {o} : @RestrictionPred o :=
  fun n t => exists (i : nat), t = mkc_nat i.

Lemma is_nat_zero {o} : forall n, @is_nat o n mkc_zero.
Proof.
  introv.
  exists 0.
  apply cterm_eq; simpl; auto.
Qed.
Hint Resolve is_nat_zero : slow.

Definition csc_nat {o} : @ChoiceSeqRestriction o :=
  csc_type is_nat.
(* =============== *)

(* =============== *)
(* bool restriction *)
Definition mkc_boolean {o} (b : bool) : @CTerm o :=
  if b then tt else ff.

Definition is_bool {o} : @RestrictionPred o :=
  fun n t => exists b, t = mkc_boolean b.

Lemma is_bool_true {o} : forall n, @is_bool o n tt.
Proof.
  introv; exists true; tcsp.
Qed.
Hint Resolve is_bool_true : slow.

Definition csc_bool {o} : @ChoiceSeqRestriction o :=
  csc_type is_bool.
(* =============== *)

(*(*
  (M v T) is meant to be (v is a member of T)

  [entry1] extends [entry2]
 *)
Definition extension_satisfies_restriction {o}
           (entry1 entry2 : @ChoiceSeqEntry o) : Prop :=
  choice_sequence_satisfies_restriction entry2 (cse_restriction entry2)
  -> choice_sequence_satisfies_restriction entry1 (cse_restriction entry1).

Lemma extension_satisfies_restriction_refl {o} :
  forall (entry : @ChoiceSeqEntry o), extension_satisfies_restriction entry entry.
Proof.
  introv.
  unfold extension_satisfies_restriction; tcsp.
Qed.
Hint Resolve extension_satisfies_restriction_refl : slow.*)

Definition same_restrictions {o} (restr1 restr2 : @ChoiceSeqRestriction o) :=
  match restr1, restr2 with
  | csc_type M1, csc_type M2 => forall n v, M1 n v <-> M2 n v
  | csc_coq_law f1, csc_coq_law f2 => forall n, f1 n = f2 n
  | csc_res M1, csc_res M2 => forall n v, M1 n v <-> M2 n v
  | _, _ => False
  end.

(*(* [entry1] extends [entry2] *)
Definition choice_sequence_entry_extend {o} (entry1 entry2 : @ChoiceSeqEntry o) : Prop :=
  (* the extension has the same restriction has the current sequence *)
  (*cse_restriction entry1 = cse_restriction entry2*)
  same_restrictions (cse_restriction entry1) (cse_restriction entry2)
  (* the extension is an extension *)
  /\ choice_sequence_vals_extend entry1 entry2
(* -- This is now part of lib_extends -- *)
(*  (* the extension satisfies the restriction *)
  /\ extension_satisfies_restriction M entry1 entry2*).*)

(* [entry1] extends [entry2] *)
Inductive entry_extends {o} : @library_entry o -> @library_entry o -> Prop :=
| entry_extends_same : forall entry, entry_extends entry entry
| entry_extends_ext :
    forall name vals vals' restr,
      entry_extends
        (lib_cs name (MkChoiceSeqEntry _ (vals ++ vals') restr))
        (lib_cs name (MkChoiceSeqEntry _ vals restr)).
Hint Constructors entry_extends.

(* true if there is an extended version of [entry] in [lib] *)
Fixpoint entry_in_library_extends {o}
         (entry : @library_entry o)
         (lib   : library) : Prop :=
  match lib with
  | [] => False
  | entry' :: entries =>
    entry_extends entry' entry
    \/
    (~ matching_entries entry entry'
       # entry_in_library_extends entry entries)
  end.

(* I used to have only the lib_extends_ext part but then it
   complicated some stuff such as, there might some names in lib0
   that are not in lib1... *)

Definition lsubset {A} (l1 l2 : list A) : Prop :=
  forall a, List.In a l1 -> List.In a l2.

Definition is0kind (name : choice_sequence_name) : bool :=
  match csn_kind name with
  | cs_kind_nat n => if deq_nat n 0 then true else false
  | _ => false
  end.

Definition is_nat_restriction {o} (restr : @ChoiceSeqRestriction o) :=
  match restr with
  | csc_type M => forall n v, M n v <-> is_nat n v
  | csc_coq_law f => forall n, is_nat n (f n)
  | csc_res M => forall n v, M n v <-> is_nat n v
  end.

Definition is_bool_restriction {o} (restr : @ChoiceSeqRestriction o) :=
  match restr with
  | csc_type M => forall n v, M n v <-> is_bool n v
  | csc_coq_law f => forall n, is_bool n (f n)
  | csc_res M => forall n v, M n v <-> is_bool n v
  end.

Definition cterm_is_nth {o} (t : @CTerm o) n l :=
  exists i, select n l = Some i /\ t = mkc_nat i.

Definition is_nat_seq_restriction {o} (l : list nat) (restr : @ChoiceSeqRestriction o) :=
  match restr with
  | csc_type M =>
    (* [M] restricts the choice sequence to [l] up to [length l] *)
    (forall n v, n < length l -> (M n v <-> cterm_is_nth v n l))
    (* above [length l], the choice sequence can return any integer *)
    /\ (forall n v, length l <= n -> (M n v <-> is_nat n v))
  | csc_coq_law _ => False
  | csc_res _ => False
  end.

Definition correct_restriction {o} (name : choice_sequence_name) (restr : @ChoiceSeqRestriction o) :=
  match csn_kind name with
  | cs_kind_nat n =>
    if deq_nat n 0 then is_nat_restriction restr
    else if deq_nat n 1 then is_bool_restriction restr
         else True
  | cs_kind_seq l => is_nat_seq_restriction l restr
  end.

Definition safe_choice_sequence_entry {o} (name : choice_sequence_name) (e : @ChoiceSeqEntry o) :=
  match e with
  | MkChoiceSeqEntry _ vals restriction =>
    correct_restriction name restriction
    /\ choice_sequence_satisfies_restriction vals restriction
  end.

Definition upd_restr_entry {o} (name : choice_sequence_name) (e : @ChoiceSeqEntry o) :=
  if is0kind name then
    match e with
    | MkChoiceSeqEntry _ vals restriction => MkChoiceSeqEntry o vals csc_nat
    end
  else e.

Definition safe_library_entry {o} (e : @library_entry o) :=
  match e with
  | lib_cs name cse =>
    safe_choice_sequence_entry name ((*upd_restr_entry name*) cse)
  | _ => True
  end.

Definition safe_library {o} (lib : @library o) :=
  forall entry, entry_in_library entry lib -> safe_library_entry entry.

Definition subset_library {o} (lib1 lib2 : @library o) :=
  forall entry1,
    List.In entry1 lib1
    ->
    exists entry2,
      List.In entry2 lib2
      /\ entry_extends entry2 entry1.

Definition lib_extends_entries {o} (lib1 lib0 : @library o) :=
  forall entry,
    entry_in_library entry lib0
    -> entry_in_library_extends entry lib1.

Definition add_entry {o} (e : @library_entry o) (lib : @library o) : library := e :: lib.

Definition add_cs {o} (name : choice_sequence_name) (r : ChoiceSeqRestriction) (lib : @library o) : library :=
  lib_cs name (MkChoiceSeqEntry _ [] r) :: lib.

Fixpoint add_choice {o} (name : choice_sequence_name) (t : @ChoiceSeqVal o) (lib : @library o) : option (nat * ChoiceSeqRestriction * library) :=
  match lib with
  | [] => None
  | entry :: entries =>
    match entry with
    | lib_cs name' (MkChoiceSeqEntry _ vals r) =>
      if choice_sequence_name_deq name name'
      then Some (length vals, r, lib_cs name' (MkChoiceSeqEntry _ (snoc vals t) r) :: entries)
      else
        match add_choice name t entries with
        | Some (t, r, entries') => Some (t, r, entry :: entries')
        | None => None
        end
    | lib_abs _ _ _ _ =>
        match add_choice name t entries with
        | Some (t, r, entries') => Some (t, r, entry :: entries')
        | None => None
        end
    end
  end.

Inductive lib_extends {o} : @library o -> @library o -> Prop :=
| lib_extends_ref :
    forall (lib : library),
      lib_extends lib lib
| lib_extends_trans :
    forall (lib1 lib2 lib3 : library),
      lib_extends lib1 lib2
      -> lib_extends lib2 lib3
      -> lib_extends lib1 lib3
| lib_extends_new_abs :
    forall (lib : library) op vars rhs correct,
      !in_lib (entry_name_abs op) lib
      -> lib_extends (lib_abs op vars rhs correct :: lib) lib
| lib_extends_new_cs :
    forall (lib : library) name restr,
      correct_restriction name restr
      -> !in_lib (entry_name_cs name) lib
      -> lib_extends (add_cs name restr lib) lib
| lib_extends_cs :
    forall lib name v n M lib',
      add_choice name v lib = Some (n, csc_type M, lib')
      -> M n v
      -> lib_extends lib' lib
| lib_extends_law :
    forall lib name v n f lib',
      add_choice name v lib = Some (n, csc_coq_law f, lib')
      -> f n = v
      -> lib_extends lib' lib
| lib_extends_res :
    forall lib name v n P lib',
      add_choice name v lib = Some (n, csc_res P, lib')
      -> P n v
      -> lib_extends lib' lib.
Hint Constructors lib_extends.

Arguments lib_extends_trans [o] [lib1] [lib2] [lib3] _.

Tactic Notation "lib_ext_ind" ident(ext) ident(c) ident(cor) ident(ni) ident(addc) ident(cond) :=
  induction ext as [|
                    |? ? ? ? ? ni
                    |? ? ? cor ni
                    |? ? ? ? ? ? addc cond
                    |? ? ? ? ? ? addc cond
                    |? ? ? ? ? ? addc cond];
  [ Case_aux c "lib_ext_refl"
  | Case_aux c "lib_ext_trans"
  | Case_aux c "lib_ext_new_abs"
  | Case_aux c "lib_ext_new_cs"
  | Case_aux c "lib_ext_cs"
  | Case_aux c "lib_ext_law"
  | Case_aux c "lib_ext_res"
  ];
  simpl; eauto 3 with slow.

Tactic Notation "lib_ext_ind" ident(ext) ident(c) :=
  let cor  := fresh "cor"  in
  let ni   := fresh "ni"   in
  let addc := fresh "addc" in
  let cond := fresh "cond" in
  lib_ext_ind ext c cor ni addc cond.

(*
(* [lib1] extends [lib0] *)
Record lib_extends {o} (lib1 lib0 : @library o) : Prop :=
  MkLibExtends
    {
      lib_extends_ext  : lib_extends_entries lib1 lib0;
      lib_extends_safe : safe_library lib0 -> safe_library lib1;
      lib_extends_sub  : subset_library lib0 lib1;
    }.
Arguments MkLibExtends [o] [lib1] [lib0] _ _ _.
*)

Definition in_ext {o} (lib : @library o) (F : @library o -> Prop) :=
  forall (lib' : library),
    lib_extends lib' lib
    -> F lib'.

Definition inExt {o} (lib : @library o) (F : @library o -> Type) :=
  forall (lib' : library),
    lib_extends lib' lib
    -> F lib'.

Lemma add_choice_implies {o} :
  forall name v (lib : @library o) n r lib' entry,
    add_choice name v lib = Some (n, r, lib')
    -> entry_in_library entry lib
    -> (entry_in_library entry lib' /\ entry2name entry <> entry_name_cs name)
       \/
       (exists vals,
           entry = lib_cs name (MkChoiceSeqEntry _ vals r)
           /\ length vals = n
           /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ (snoc vals v) r)) lib').
Proof.
  induction lib; introv add i; simpl in *; tcsp.
  destruct a; boolvar; subst; simpl in *; repndors; repnd; tcsp; subst; simpl in *; tcsp;
    try (destruct entry0 as [vals restr]); simpl in *.

  { inversion add; subst; simpl in *; tcsp.
    right.
    exists vals; dands; tcsp. }

  { inversion add; subst; simpl in *; tcsp.
    left; dands; tcsp.
    intro xx; destruct i0.
    destruct entry; simpl in *; ginv; eauto 3 with slow; tcsp. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; repnd; simpl in *; ginv.
    inversion add; subst; clear add.
    simpl.
    left; dands; tcsp.
    intro xx; inversion xx; tcsp. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; repnd; simpl in *; ginv.
    inversion add; subst; clear add.
    eapply IHlib in i; try reflexivity.
    repndors; repnd; simpl in *; tcsp.
    exrepnd; subst.
    right.
    exists vals0; dands; tcsp. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; repnd; simpl in *; ginv.
    inversion add; subst; clear add.
    simpl; left; dands; tcsp.
    introv xx; ginv. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; repnd; simpl in *; ginv.
    inversion add; subst; clear add.
    eapply IHlib in i; try reflexivity.
    repndors; repnd; simpl in *; tcsp.
    exrepnd; subst.
    right.
    exists vals; dands; tcsp. }
Qed.

Lemma add_choice_implies2 {o} :
  forall name v (lib : @library o) n r lib' entry,
    add_choice name v lib = Some (n, r, lib')
    -> entry_in_library entry lib'
    -> (entry_in_library entry lib /\ entry2name entry <> entry_name_cs name)
       \/
       (exists vals,
           entry = lib_cs name (MkChoiceSeqEntry _ (snoc vals v) r)
           /\ length vals = n
           /\ entry_in_library (lib_cs name (MkChoiceSeqEntry _ vals r)) lib).
Proof.
  induction lib; introv add i; simpl in *; tcsp.
  destruct a; boolvar; subst; simpl in *; repndors; repnd; tcsp; subst; simpl in *; tcsp;
    try destruct entry0 as [vals restr]; simpl in *; ginv.

  { inversion add; subst; simpl in *; clear add.
    repndors; repnd; subst; simpl in *; tcsp.

    { right.
      exists vals; dands; tcsp. }

    { left; dands; tcsp.
      intro xx; destruct i0.
      destruct entry; simpl in *; ginv; eauto 3 with slow; tcsp. } }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; simpl in *; repnd; inversion add; subst; clear add.
    simpl in *; repndors; repnd; subst; simpl in *; tcsp.

    { left; dands; tcsp.
      intro xx; inversion xx; tcsp. }

    { eapply IHlib in i; try reflexivity.
      repndors; repnd; simpl in *; tcsp.
      exrepnd; subst.
      right.
      exists vals0; dands; tcsp. } }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; simpl in *; repnd; inversion add; subst; clear add.
    simpl in *; repndors; repnd; subst; simpl in *; tcsp.

    { left; dands; tcsp.
      introv xx; ginv. }

    { eapply IHlib in i; try reflexivity.
      repndors; repnd; simpl in *; tcsp.
      exrepnd; subst.
      right.
      exists vals; dands; tcsp. } }
Qed.

Hint Rewrite length_snoc : slow.

Lemma select_nil :
  forall {A} n, @select A n [] = None.
Proof.
  introv; destruct n; simpl; auto.
Qed.
Hint Rewrite @select_nil : list.

Lemma select_snoc_eq :
  forall {A} n (l : list A) x,
    select n (snoc l x) =
    if lt_dec n (length l)
    then select n l
    else if deq_nat n (length l) then Some x else None.
Proof.
  induction n; introv; simpl in *.

  { destruct l; simpl; auto. }

  destruct l; simpl in *; autorewrite with slow list; auto.
  rewrite IHn.
  boolvar; tcsp; try omega.
Qed.

Lemma add_choice_csc_type_preserves_safe {o} :
  forall name v (lib : @library o) n M lib',
    add_choice name v lib = Some (n, csc_type M, lib')
    -> M n v
    -> safe_library lib
    -> safe_library lib'.
Proof.
  introv add p safe i; simpl in *.
  eapply add_choice_implies2 in add; eauto.
  repndors; exrepnd; subst; tcsp; simpl in *; tcsp; ginv.
  apply safe in add0; simpl in *; exrepnd; dands; tcsp.
  introv sel; rewrite select_snoc_eq in sel; boolvar; ginv; tcsp.
Qed.
Hint Resolve add_choice_csc_type_preserves_safe : slow.

Lemma add_choice_csc_coq_law_preserves_safe {o} :
  forall name v (lib : @library o) n f lib',
    add_choice name v lib = Some (n, csc_coq_law f, lib')
    -> f n = v
    -> safe_library lib
    -> safe_library lib'.
Proof.
  introv add p safe i.
  eapply add_choice_implies2 in add; eauto.
  repndors; exrepnd; subst; tcsp; simpl in *; tcsp; ginv.
  apply safe in add0; simpl in *; exrepnd; dands; tcsp.
  introv h; autorewrite with slow in *.
  rewrite select_snoc_eq; boolvar; tcsp; subst; tcsp; try omega.
Qed.
Hint Resolve add_choice_csc_coq_law_preserves_safe : slow.

Lemma add_choice_csc_res_preserves_safe {o} :
  forall name v (lib : @library o) n M lib',
    add_choice name v lib = Some (n, csc_res M, lib')
    -> M n v
    -> safe_library lib
    -> safe_library lib'.
Proof.
  introv add p safe i.
  eapply add_choice_implies2 in add; eauto.
  repndors; exrepnd; subst; tcsp; simpl in *; tcsp; ginv.
  apply safe in add0; simpl in *; exrepnd; dands; tcsp.
  introv h; autorewrite with slow in *.
  rewrite select_snoc_eq in h; boolvar; tcsp; subst; try omega; ginv; auto.
Qed.
Hint Resolve add_choice_csc_res_preserves_safe : slow.

Lemma choice_sequence_satisfies_restriction_nil {o} :
  forall (restr : @ChoiceSeqRestriction o), choice_sequence_satisfies_restriction [] restr.
Proof.
  introv; unfold choice_sequence_satisfies_restriction.
  destruct restr; introv; autorewrite with slow list; simpl; tcsp.
Qed.
Hint Resolve choice_sequence_satisfies_restriction_nil : slow.

Lemma safe_library_add_cs {o} :
  forall name restr (lib : @library o),
    correct_restriction name restr
    -> safe_library lib
    -> safe_library (add_cs name restr lib).
Proof.
  introv cor safe i; simpl in *.
  repndors; repnd; subst; simpl in * ; boolvar; subst; tcsp; eauto 2 with slow.
Qed.
Hint Resolve safe_library_add_cs : slow.

Lemma safe_library_add_abs {o} :
  forall op vars rhs correct (lib : @library o),
    safe_library lib
    -> safe_library (lib_abs op vars rhs correct :: lib).
Proof.
  introv safe i; simpl in *.
  repndors; repnd; subst; simpl in * ; boolvar; subst; tcsp; eauto 2 with slow.
Qed.
Hint Resolve safe_library_add_abs : slow.

Lemma lib_extends_preserves_safe {o} :
  forall (lib1 lib2 : @library o),
    lib_extends lib1 lib2
    -> safe_library lib2
    -> safe_library lib1.
Proof.
  introv ext; lib_ext_ind ext Case; introv safe.
Qed.
Hint Resolve lib_extends_preserves_safe : slow.

(*Definition in_lib {o}
           (opabs : opabs)
           (lib   : @library o) :=
  exists (e : library_entry),
    List.In e lib
    /\ matching_entry_sign opabs (opabs_of_lib_entry e).*)

Definition entry_not_in_lib {o} (e : @library_entry o) (l : @library o) :=
  !in_lib (entry2name e) l.

Hint Resolve matching_entry_sign_sym : slow.

Lemma entry_in_library_implies_in {o} :
  forall (entry : @library_entry o) lib,
    entry_in_library entry lib -> List.In entry lib.
Proof.
  induction lib; auto; introv h; simpl in *.
  repndors; subst; tcsp.
Qed.
Hint Resolve entry_in_library_implies_in : slow.

Lemma matching_entries_implies_same_entry_name {o} :
  forall (entry1 entry2 : @library_entry o),
    matching_entries entry1 entry2
    -> same_entry_name (entry2name entry1) (entry2name entry2).
Proof.
  introv m; destruct entry1, entry2; simpl in *; tcsp.
Qed.
Hint Resolve matching_entries_implies_same_entry_name : slow.

Hint Resolve same_entry_name_sym : slow.

Lemma lsubset_cons_left_implies_lsubset :
  forall {A} (a : A) l1 l2,
    lsubset (a :: l1) l2
    -> lsubset l1 l2.
Proof.
  introv ss i; apply ss; simpl; tcsp.
Qed.
Hint Resolve lsubset_cons_left_implies_lsubset : slow.

Lemma lsubset_refl :
  forall {A} (l : list A), lsubset l l.
Proof.
  introv i; auto.
Qed.
Hint Resolve lsubset_refl : slow.

(*Lemma lib_extends_cons_implies {o} :
  forall M (e : @library_entry o) (lib lib0 : library),
    entry_not_in_lib e lib0
    -> lib_extends M lib (e :: lib0)
    -> lib_extends M lib lib0.
Proof.
  introv ni ext.
  destruct ext as [ext safe ss].
  split; eauto 4 with slow.
  Focus 2.
  intro h; apply safe.


  introv i.
  apply ext; simpl; clear ext.
  right; dands; auto; intro m.
  destruct ni.

  exists entry.
  dands; eauto 3 with slow.
Qed.*)

Lemma choice_sequence_vals_extend_refl {o} :
  forall (vals : @ChoiceSeqVals o), choice_sequence_vals_extend vals vals.
Proof.
  introv; exists ([] : @ChoiceSeqVals o); autorewrite with slow; auto.
Qed.
Hint Resolve choice_sequence_vals_extend_refl : slow.

Lemma same_restrictions_refl {o} :
  forall (r : @ChoiceSeqRestriction o), same_restrictions r r.
Proof.
  introv; destruct r; simpl; tcsp.
Qed.
Hint Resolve same_restrictions_refl : slow.

(*Lemma choice_sequence_entry_extend_refl {o} :
  forall (entry : @ChoiceSeqEntry o), choice_sequence_entry_extend entry entry.
Proof.
  introv.
  unfold choice_sequence_entry_extend; dands; eauto 2 with slow.
Qed.
Hint Resolve choice_sequence_entry_extend_refl : slow.*)

Lemma entry_extends_refl {o} :
  forall (entry : @library_entry o), entry_extends entry entry.
Proof.
  destruct entry; simpl in *; tcsp.
Qed.
Hint Resolve entry_extends_refl : slow.

Lemma entry_in_library_implies_entry_in_library_extends {o} :
  forall entry (lib : @library o),
    entry_in_library entry lib
    -> entry_in_library_extends entry lib.
Proof.
  induction lib; introv e; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.
Qed.
Hint Resolve entry_in_library_implies_entry_in_library_extends : slow.

Lemma subset_library_refl {o} :
  forall (lib : @library o), subset_library lib lib.
Proof.
  introv i.
  exists entry1; dands; auto; eauto 2 with slow.
Qed.
Hint Resolve subset_library_refl : slow.

Lemma lib_extends_entries_refl {o} :
  forall (lib : @library o), lib_extends_entries lib lib.
Proof.
  introv i; eauto 2 with slow.
Qed.
Hint Resolve lib_extends_entries_refl : slow.

Lemma lib_extends_refl {o} :
  forall (lib : @library o), lib_extends lib lib.
Proof.
  eauto.
Qed.
Hint Resolve lib_extends_refl : slow.

Lemma entry_in_library_implies_find_entry {o} :
  forall (lib : @library o) abs opabs vars bs rhs correct,
    matching_entry abs opabs vars bs
    -> entry_in_library (lib_abs opabs vars rhs correct) lib
    -> find_entry lib abs bs = Some (lib_abs opabs vars rhs correct).
Proof.
  induction lib; introv m e; simpl in *; tcsp.
  destruct a.

  { repndors; repnd; tcsp; ginv. }

  repndors; repnd.

  - inversion e; subst; clear e.
    boolvar; tcsp.

    + pose proof (correct_abs_proof_irrelevance _ _ _ correct correct0) as xx; subst; auto.

    + apply not_matching_entry_iff in n; tcsp.

  - boolvar; tcsp.
    apply matching_entry_implies_sign in m.
    apply matching_entry_implies_sign in m0.
    destruct e0.
    unfold matching_entries; simpl.

    eapply matching_entry_sign_trans;[|eauto].
    eapply matching_entry_sign_sym;auto.
Qed.

Lemma find_entry_some_decomp {o} :
  forall (lib : @library o) abs bs e,
    find_entry lib abs bs = Some e
    <=> {lib1 : library
         & {lib2 : library
         & {oa : opabs
         & {vars : list sovar_sig
         & {rhs : SOTerm
         & {correct : correct_abs oa vars rhs
         & lib = lib1 ++ e :: lib2
         # e = lib_abs oa vars rhs correct
         # matching_entry abs oa vars bs
         # find_entry lib1 abs bs = None }}}}}}.
Proof.
  induction lib; introv; split; introv h; simpl in *; ginv.

  - exrepnd.
    destruct lib1; ginv.

  - destruct a.

    {
      apply IHlib in h; exrepnd; subst; clear IHlib.
      exists (lib_cs name entry :: lib1) lib2 oa vars rhs correct.
      dands; auto.
    }

    boolvar; ginv.

    + exists ([] : @library o) lib opabs vars rhs correct; simpl.
      dands; auto.

    + apply IHlib in h; exrepnd; subst; clear IHlib.
      exists (lib_abs opabs vars rhs correct :: lib1) lib2 oa vars0 rhs0 correct0.
      dands; auto.
      simpl; boolvar; auto.
      apply not_matching_entry_iff in n; tcsp.

  - exrepnd; subst.
    destruct a.

    {
      destruct lib1; simpl in *; ginv.
      apply IHlib.
      exists lib1 lib2 oa vars rhs correct.
      dands; auto.
    }

    destruct lib1; simpl in *; ginv.

    + inversion h0; subst; clear h0.
      pose proof (correct_abs_proof_irrelevance _ _ _ correct correct0) as xx; subst; auto.
      boolvar; auto.
      apply not_matching_entry_iff in n; tcsp.

    + boolvar; ginv.
      apply IHlib.
      exists lib1 lib2 oa vars rhs correct; dands; auto.
Qed.

Lemma implies_entry_in_library_app_right {o} :
  forall (lib1 lib2 : @library o) e,
    entry_in_library e lib2
    -> (forall e', LIn e' lib1 -> ~ matching_entries e e')
    -> entry_in_library e (lib1 ++ lib2).
Proof.
  induction lib1; introv h q; simpl in *; auto.
  right; dands; auto.
Qed.

Lemma matching_entry_trans_right {o} :
  forall abs1 abs2 abs3 vars1 vars2 (bs : list (@BTerm o)),
    matching_entry abs1 abs2 vars1 bs
    -> matching_entry abs2 abs3 vars2 bs
    -> matching_entry abs1 abs3 vars2 bs.
Proof.
  introv m1 m2; unfold matching_entry in *; repnd; dands; tcsp;
    try (complete (allrw; auto)).
  eapply matching_parameters_trans; eauto.
Qed.

Lemma matching_entry_sym {o} :
  forall abs1 abs2 vars (bs : list (@BTerm o)),
    matching_entry abs1 abs2 vars bs
    -> matching_entry abs2 abs1 vars bs.
Proof.
  introv m; unfold matching_entry in *; repnd; dands; tcsp;
    try (complete (allrw; auto)).
  apply matching_parameters_sym; auto.
Qed.

Lemma matching_entry_preserves_find_entry {o} :
  forall (lib : @library o) abs1 abs2 vars bs,
    matching_entry abs1 abs2 vars bs
    -> find_entry lib abs1 bs = find_entry lib abs2 bs.
Proof.
  induction lib; introv m; simpl in *; auto.
  destruct a; eauto;[].

  boolvar; auto.
  - apply not_matching_entry_iff in n.
    apply matching_entry_sym in m.
    eapply matching_entry_trans_right in m0;[|exact m]; tcsp.
  - apply not_matching_entry_iff in n.
    eapply matching_entry_trans_right in m0;[|exact m]; tcsp.
  - eapply IHlib; eauto.
Qed.

Lemma matching_entry_sign_implies_matching_entry {o} :
  forall (abs1 abs2 : opabs) (vars : list sovar_sig) (bs : list (@BTerm o)),
    matching_bterms vars bs
    -> matching_entry_sign abs1 abs2
    -> matching_entry abs1 abs2 vars bs.
Proof.
  introv h m; unfold matching_entry_sign in m; unfold matching_entry.
  repnd; dands; auto.
Qed.

Lemma matching_entry_implies_matching_bterms {o} :
  forall (abs1 abs2 : opabs) (vars : list sovar_sig) (bs : list (@BTerm o)),
    matching_entry abs1 abs2 vars bs
    -> matching_bterms vars bs.
Proof.
  introv m; unfold matching_entry in m; tcsp.
Qed.

Lemma correct_abs_implies_matching_sign {o} :
  forall abs vars (t : @SOTerm o),
    correct_abs abs vars t
    -> matching_sign vars (opabs_sign abs).
Proof.
  introv cor.
  unfold correct_abs in cor; tcsp.
Qed.

Lemma matching_entry_sign_implies_eq_opabs_signs :
  forall abs1 abs2,
    matching_entry_sign abs1 abs2
    -> opabs_sign abs1 = opabs_sign abs2.
Proof.
  introv m; unfold matching_entry_sign in m; tcsp.
Qed.

Lemma find_entry_none_implies {o} :
  forall (lib : @library o) abs bs e vars rhs correct,
    matching_sign vars (opabs_sign abs)
    -> matching_sign vars (map num_bvars bs)
    -> find_entry lib abs bs = None
    -> LIn e lib
    -> ~ matching_entries (lib_abs abs vars rhs correct) e.
Proof.
  induction lib; introv ms1 ms2 fe i; simpl in *; tcsp.
  destruct a; repndors; subst; boolvar; tcsp; eauto;[].

  unfold matching_entries; simpl; intro h.
  apply not_matching_entry_iff in n.
  destruct n.
  apply matching_entry_sign_implies_matching_entry; auto.
  apply matching_bterms_as_matching_sign.
  apply correct_abs_implies_matching_sign in correct0.
  unfold matching_sign in *.

  apply matching_entry_sign_implies_eq_opabs_signs in h.
  rewrite correct0.
  rewrite <- h.
  rewrite <- ms1; rewrite <- ms2; auto.
Qed.

Lemma entry_in_libray_implies_find_entry_some {o} :
  forall lib abs oa vars (t : @SOTerm o) bs correct,
    matching_entry abs oa vars bs
    -> entry_in_library (lib_abs oa vars t correct) lib
    -> find_entry lib abs bs = Some (lib_abs oa vars t correct).
Proof.
  induction lib; introv m i; simpl in *; tcsp.
  destruct a; simpl in *.

  { repndors; tcsp; ginv. }

  repndors; repnd.

  - inversion i; subst; clear i.
    pose proof (correct_abs_proof_irrelevance _ _ _ correct correct0) as xx; subst; auto.
    boolvar; auto.
    apply not_matching_entry_iff in n; tcsp.

  - unfold matching_entries in i0; simpl in i0.
    boolvar; ginv.

    + destruct i0.
      eapply matching_entry_implies_sign.
      eapply matching_entry_trans_right;[|exact m0].
      apply matching_entry_sym;eauto.

    + apply IHlib; auto.
Qed.
Hint Resolve entry_in_libray_implies_find_entry_some : slow.

Lemma entry_abs_in_library_extends_implies_entry_in_library {o} :
  forall oa vars rhs correct (lib : @library o),
    entry_in_library_extends (lib_abs oa vars rhs correct) lib
    -> entry_in_library (lib_abs oa vars rhs correct) lib.
Proof.
  induction lib; introv e; simpl in *; tcsp.
  repndors; repnd; tcsp.
  destruct a; simpl in *; tcsp; eauto; inversion e; subst.
  rewrite (correct_abs_proof_irrelevance _ _ _ correct0 correct) in *; tcsp.
Qed.
Hint Resolve entry_abs_in_library_extends_implies_entry_in_library : slow.

Lemma entry_extends_preserves_matching_entries_left {o}:
  forall (entry1 entry2 entry : @library_entry o),
    entry_extends entry1 entry2
    -> matching_entries entry1 entry
    -> matching_entries entry2 entry.
Proof.
  introv h m; inversion h as [|]; subst; auto.
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

Lemma choice_sequence_vals_extend_trans {o} :
  forall (vals1 vals2 vals3 : @ChoiceSeqVals o),
    choice_sequence_vals_extend vals1 vals2
    -> choice_sequence_vals_extend vals2 vals3
    -> choice_sequence_vals_extend vals1 vals3.
Proof.
  introv h1 h2; unfold choice_sequence_vals_extend in *; exrepnd; subst.
  exists (vals ++ vals0); rewrite app_assoc; auto.
Qed.
Hint Resolve choice_sequence_vals_extend_trans : slow.

Lemma same_restrictions_trans {o} :
  forall (r1 r2 r3 : @ChoiceSeqRestriction o),
    same_restrictions r1 r2
    -> same_restrictions r2 r3
    -> same_restrictions r1 r3.
Proof.
  introv h q; destruct r1, r2, r3; simpl in *; repnd; tcsp; dands; introv;
    try (complete (rewrite h; auto));
    try (complete (rewrite h0; auto)).
Qed.
Hint Resolve same_restrictions_trans : slow.

(*Lemma choice_sequence_entry_extend_trans {o} :
  forall (e1 e2 e3 : @ChoiceSeqEntry o),
    choice_sequence_entry_extend e1 e2
    -> choice_sequence_entry_extend e2 e3
    -> choice_sequence_entry_extend e1 e3.
Proof.
  introv h1 h2.
  destruct e1, e2, e3; unfold choice_sequence_entry_extend in *;
    simpl in *; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve choice_sequence_entry_extend_trans : slow.*)

Lemma entry_extends_trans {o} :
  forall (entry1 entry2 entry3 : @library_entry o),
    entry_extends entry1 entry2
    -> entry_extends entry2 entry3
    -> entry_extends entry1 entry3.
Proof.
  introv h1 h2.
  inversion h1 as [|]; subst; auto; clear h1.
  inversion h2 as [|]; subst; auto; clear h2.
  rewrite <- app_assoc; eauto.
Qed.
Hint Resolve entry_extends_trans : slow.

Lemma entry_extends_preserves_matching_entries_left_rev {o}:
  forall (entry1 entry2 entry : @library_entry o),
    entry_extends entry2 entry1
    -> matching_entries entry1 entry
    -> matching_entries entry2 entry.
Proof.
  introv h m.
  inversion h; subst; eauto.
Qed.
Hint Resolve entry_extends_preserves_matching_entries_left_rev : slow.

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

Lemma entry_in_library_implies_in_lib_cs {o} :
  forall entry name (lib : @library o),
    same_entry_name (entry2name entry) (entry_name_cs name)
    -> entry_in_library entry lib
    -> in_lib (entry2name entry) lib.
Proof.
  introv same h; exists entry; dands; eauto 3 with slow.
Qed.

Lemma entry_in_library_implies_in_lib_abs {o} :
  forall entry op (lib : @library o),
    same_entry_name (entry2name entry) (entry_name_abs op)
    -> entry_in_library entry lib
    -> in_lib (entry2name entry) lib.
Proof.
  introv same h; exists entry; dands; eauto 3 with slow.
Qed.

Lemma choice_sequence_vals_extend_snoc {o} :
  forall (vals : @ChoiceSeqVals o) v,
    choice_sequence_vals_extend (snoc vals v) vals.
Proof.
  introv.
  exists [v].
  rewrite snoc_as_append; auto.
Qed.
Hint Resolve choice_sequence_vals_extend_snoc : slow.

Lemma add_choice_preserves_lib_extends_entries {o} :
  forall name v (lib : @library o) n r lib',
    add_choice name v lib = Some (n, r, lib')
    -> lib_extends_entries lib' lib.
Proof.
  induction lib; introv h i; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; repndors; repnd; subst; tcsp;
    try destruct entry0 as [vals restr]; simpl in *; ginv.

  { inversion h; clear h; subst; simpl in *.
    left; dands; eauto 3 with slow.
    rewrite snoc_as_append; eauto. }

  { inversion h; subst; simpl in *.
    right; dands; eauto 3 with slow. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; simpl in *; repnd; simpl in *; inversion h; subst; clear h; simpl; tcsp. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; simpl in *; repnd; simpl in *; inversion h; subst; clear h; simpl; tcsp.
    eapply IHlib in i; eauto. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; simpl in *; repnd; simpl in *; inversion h; subst; clear h; simpl; tcsp. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; simpl in *; repnd; simpl in *; inversion h; subst; clear h; simpl; tcsp.
    eapply IHlib in i; eauto. }
Qed.
Hint Resolve add_choice_preserves_lib_extends_entries : slow.

Lemma add_choice_preserves_subset_library {o} :
  forall name v (lib : @library o) n r lib',
    add_choice name v lib = Some (n, r, lib')
    -> subset_library lib lib'.
Proof.
  induction lib; introv h i; simpl in *; tcsp.
  destruct a; simpl in *; boolvar; repndors; repnd; subst; tcsp;
    try destruct entry as [vals restr]; simpl in *.

  { inversion h; clear h; subst; simpl in *.
    exists (lib_cs name0 (MkChoiceSeqEntry _ (snoc vals v) r)); simpl; dands; tcsp; eauto 3 with slow.
    rewrite snoc_as_append; eauto. }

  { inversion h; subst; simpl in *.
    exists entry1; simpl; dands; tcsp; eauto 3 with slow. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; simpl in *; repnd; simpl in *; inversion h; subst; clear h; simpl; tcsp.
    exists (lib_cs name0 (MkChoiceSeqEntry _ vals restr)); simpl; dands; tcsp; eauto 3 with slow. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; simpl in *; repnd; simpl in *; inversion h; subst; clear h; simpl; tcsp.
    eapply IHlib in i; eauto; exrepnd.
    exists entry2; dands; tcsp. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; simpl in *; repnd; simpl in *; inversion h; subst; clear h; simpl; tcsp.
    exists (lib_abs opabs vars rhs correct); simpl; dands; tcsp. }

  { remember (add_choice name v lib) as w; symmetry in Heqw; destruct w; simpl in *; repnd; simpl in *; inversion h; subst; clear h; simpl; tcsp.
    eapply IHlib in i; eauto; exrepnd.
    exists entry2; dands; tcsp. }
Qed.
Hint Resolve add_choice_preserves_subset_library : slow.

Lemma implies_lib_extends_ext {o} :
  forall (lib1 lib0 : @library o),
    lib_extends lib1 lib0
    -> lib_extends_entries lib1 lib0.
Proof.
  introv ext.
  lib_ext_ind ext Case.

  { Case "lib_ext_trans".
    introv i.
    apply IHext2 in i; tcsp.
    apply entry_in_library_extends_implies_entry_in_library in i; exrepnd.
    apply IHext1 in i1; eauto 3 with slow. }

  { Case "lib_ext_new_abs".
    introv i; simpl in *.
    right; dands; eauto 3 with slow.
    introv xx; simpl in *; apply matching_entries_implies_same_entry_name in xx; simpl in *.
    eapply entry_in_library_implies_in_lib_abs in i; eauto.
    eapply same_entry_name_preserves_in_lib in i; eauto. }

  { Case "lib_ext_new_cs".
    introv i; simpl in *.
    right; dands; eauto 3 with slow.
    introv xx; simpl in *; apply matching_entries_implies_same_entry_name in xx; simpl in *.
    eapply entry_in_library_implies_in_lib_cs in i; eauto.
    eapply same_entry_name_preserves_in_lib in i; eauto. }
Qed.
Hint Resolve implies_lib_extends_ext : slow.

Lemma lib_extends_preserves_find_entry {o} :
  forall (lib1 lib2 : @library o) abs bs (e : library_entry),
    lib_extends lib2 lib1
    -> find_entry lib1 abs bs = Some e
    -> find_entry lib2 abs bs = Some e.
Proof.
  introv ext fe.
  apply find_entry_some_decomp in fe; exrepnd; subst.

  pose proof (implies_lib_extends_ext _ _ ext (lib_abs oa vars rhs correct)) as h.
  simpl in h; autodimp h hyp; eauto 3 with slow;[].

  apply implies_entry_in_library_app_right;[simpl; tcsp|].
  pose proof (matching_entry_preserves_find_entry lib0 abs oa vars bs) as q.
  autodimp q hyp.
  rewrite q in fe1; clear q.
  applydup @matching_entry_implies_matching_bterms in fe3.
  dup correct as ms.
  apply correct_abs_implies_matching_sign in ms.
  rw @matching_bterms_as_matching_sign in fe0.
  introv i; eapply find_entry_none_implies; eauto.
Qed.

Lemma in_get_utokens_library_iff {o} :
  forall (lib : @library o) a,
    LIn a (get_utokens_library lib)
    <=> {entry : library_entry & LIn entry lib # LIn a (get_utokens_library_entry entry) }.
Proof.
  introv; unfold get_utokens_library.
  rw lin_flat_map; tcsp.
Qed.

Lemma list_in_get_utokens_library_iff {o} :
  forall (lib : @library o) a,
    List.In a (get_utokens_library lib)
    <-> exists (entry : library_entry), List.In entry lib /\ List.In a (get_utokens_library_entry entry).
Proof.
  introv; unfold get_utokens_library.
  rewrite in_flat_map; tcsp.
Qed.

Definition LIn_iff_In :
  forall {A} (deq : Deq A) (a : A) (l : list A),
    LIn a l <=> List.In a l.
Proof.
  induction l; simpl in *; split; intro h; tcsp; repndors; tcsp.

  - apply IHl in h; tcsp.

  - destruct (deq a0 a) as [d|d]; subst; tcsp.
    right; apply IHl.
    repndors; tcsp.
Qed.

Definition LIn_iff_In_name {o} :
  forall (a : get_patom_set o) l,
    LIn a l <=> List.In a l.
Proof.
  introv; apply LIn_iff_In.
  apply get_patom_deq.
Qed.

Lemma list_in_app :
  forall {T} (a : T) l1 l2,
    List.In a (l1 ++ l2) <-> List.In a l1 \/ List.In a l2.
Proof.
  induction l1; introv; simpl in *; tcsp; split; intro h; tcsp; repndors; subst; tcsp.
  - apply IHl1 in h; repndors; tcsp.
  - right; apply IHl1; tcsp.
  - right; apply IHl1; tcsp.
Qed.

Lemma entry_extends_preserves_get_utokens_library_entry {o} :
  forall (entry1 entry2 : @library_entry o) a,
    entry_extends entry2 entry1
    -> List.In a (get_utokens_library_entry entry1)
    -> List.In a (get_utokens_library_entry entry2).
Proof.
  introv ext i; inversion ext; clear ext; subst; auto.
  simpl in *; rw flat_map_app; rewrite list_in_app; tcsp.
Qed.
Hint Resolve entry_extends_preserves_get_utokens_library_entry : slow.

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

Lemma implies_lib_extends_sub {o} :
  forall (lib1 lib0 : @library o),
    lib_extends lib1 lib0
    -> subset_library lib0 lib1.
Proof.
  introv ext.
  lib_ext_ind ext Case;
    try (complete (introv i; simpl in *; exists entry1; dands; tcsp; eauto 3 with slow)).
Qed.
Hint Resolve implies_lib_extends_sub : slow.

Lemma lib_extends_implies_subset_get_utokens_library {o} :
  forall (lib1 lib2 : @library o),
    lib_extends lib2 lib1
    -> subset (get_utokens_library lib1) (get_utokens_library lib2).
Proof.
  introv ext i.
  allrw @LIn_iff_In_name.
  allrw @list_in_get_utokens_library_iff; exrepnd.
  apply (implies_lib_extends_sub _ _ ext) in i1.
  exrepnd.
  exists entry2; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_implies_subset_get_utokens_library : slow.

(*
(*

  We should be able to prove equality!

 *)
Lemma compute_step_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (comp : compute_step lib1 a = csuccess b),
    compute_step lib2 a = csuccess b.
Proof.
  nterm_ind1s a as [v|f ind|op bs ind] Case; introv comp.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv.

          SSCase "NEApply".

          apply compute_step_eapply_success in comp; exrepnd; subst.
          repndors; exrepnd; allsimpl; subst.

          + apply compute_step_eapply2_success in comp1; repnd; subst.
            repndors; exrepnd; subst; ginv.
            csunf; simpl.
            dcwf h; simpl.
            boolvar; try omega.
            rewrite Znat.Nat2Z.id; auto.

          + csunf; simpl.
            apply isexc_implies2 in comp0; exrepnd; subst.
            dcwf h; simpl; auto.

          + fold_terms.
            rewrite compute_step_eapply_iscan_isnoncan_like; auto.
            pose proof (ind arg2 arg2 []) as h; clear ind.
            repeat (autodimp h hyp); eauto 3 with slow.
            apply h in comp1; clear h.
            rewrite comp1; auto.

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; allsimpl.
              apply compute_step_apply_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NEApply".

              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; allsimpl; auto.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.

                + unfold mk_lam in *; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  apply iscan_implies in comp0; repndors; exrepnd; subst; simpl; auto.

                + unfold mk_nseq in *; allsimpl; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try omega.
                  rewrite Znat.Nat2Z.id; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isexc; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; auto.

                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp1; clear q.
                rewrite comp1; auto.
            }

            {
              SSSCase "NFix".

              csunf comp; allsimpl.
              apply compute_step_fix_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NSpread".

              csunf comp; allsimpl.
              apply compute_step_spread_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NDsup".

              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NDecide".

              csunf comp; allsimpl.
              apply compute_step_decide_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NCbv".

              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NSleep".

              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NTUni".

              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              unfold compute_step_tuni; simpl.
              boolvar; try omega.
              rewrite Znat.Nat2Z.id; auto.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NFresh".

              csunf comp; allsimpl; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; allsimpl.
              apply compute_step_try_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.

              - rewrite compute_step_ncompop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q.
                rewrite comp4; auto.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.

              - rewrite compute_step_narithop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q.
                rewrite comp4; auto.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
            }

            {
              SSSCase "NCanTest".

              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp.
              repndors; exrepnd; subst; auto.
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step lib1 (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q.
            csunf; simpl.
            rewrite Heqc; auto.

          + SSCase "Exc".

            csunf comp; allsimpl.
            apply compute_step_catch_success in comp.
            repndors; exrepnd; subst; allsimpl; ginv.

            * csunf; simpl; auto.

            * csunf; simpl; auto.
              rewrite compute_step_catch_if_diff; auto.

          + SSCase "Abs".

            csunf comp; allsimpl.
            remember (compute_step lib1 (oterm (Abs abs2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q.
            csunf; simpl.
            rewrite Heqc; auto.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; ginv.

        - csunf; simpl; boolvar; auto.

        - rewrite compute_step_fresh_if_isvalue_like2; auto.

        - fold (mk_fresh n t).
          rewrite compute_step_fresh_if_isnoncan_like; auto.

          pose proof (ind t (subst t n (mk_utoken (get_fresh_atom t))) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { rewrite simple_osize_subst; eauto 2 with slow. }
          apply q in comp2; clear q.
          remember (get_fresh_atom t) as a; simpl.
          rewrite comp2; simpl; auto.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.

      csunf; simpl.

      apply (found_entry_implies_compute_step_lib_success _ _ _ _ _ _ correct).
      eapply lib_extends_preserves_find_entry; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (n : nat)
         (comp : reduces_in_atmost_k_steps lib1 a b n),
    reduces_in_atmost_k_steps lib2 a b n.
Proof.
  introv ext r.
  revert dependent a.
  induction n; introv r.

  - allrw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    exists u; dands; auto.
    eapply compute_step_preserves_lib_extends; eauto.
Qed.

Lemma reduces_to_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (comp : reduces_to lib1 a b),
    reduces_to lib2 a b.
Proof.
  introv ext r.
  unfold reduces_to in *; exrepnd.
  exists k.
  eapply reduces_in_atmost_k_steps_preserves_lib_extends; eauto.
Qed.
 *)

(*Lemma choice_sequence_entry_extend_implies_choice_sequence_vals_extend {o} :
  forall (entry1 entry2 : @ChoiceSeqEntry o),
    choice_sequence_entry_extend entry1 entry2
    -> choice_sequence_vals_extend entry1 entry2.
Proof.
  introv h; unfold choice_sequence_entry_extend in h; tcsp.
Qed.
Hint Resolve choice_sequence_entry_extend_implies_choice_sequence_vals_extend : slow.*)

Definition entry2restriction {o} (e : @ChoiceSeqEntry o) : ChoiceSeqRestriction :=
  match e with
  | MkChoiceSeqEntry _ vals restriction => restriction
  end.

(*Lemma choice_sequence_entry_extend_preserves_entry2restriction {o} :
  forall (entry1 entry2 : @ChoiceSeqEntry o),
    choice_sequence_entry_extend entry1 entry2
    -> same_restrictions (entry2restriction entry1) (entry2restriction entry2).
Proof.
  introv h; destruct entry1, entry2; simpl in *.
  unfold choice_sequence_entry_extend in h; simpl in *; repnd; auto.
Qed.
Hint Resolve choice_sequence_entry_extend_preserves_entry2restriction : slow.*)

Lemma lib_cs_in_library_extends_implies {o} :
  forall (lib : @library o) name entry,
    entry_in_library_extends (lib_cs name entry) lib
    ->
    exists (vals' : ChoiceSeqVals),
      find_cs lib name = Some (MkChoiceSeqEntry _ vals' (entry2restriction entry))
      /\ choice_sequence_vals_extend vals' entry.
Proof.
  induction lib; introv h; simpl in *; tcsp.
  destruct a; simpl in *; tcsp; repndors; repnd; subst; boolvar; subst; tcsp; GC;
    try (complete (eapply IHlib; eauto));
    try (complete (inversion h; clear h; subst; simpl in *; eauto; tcsp));
    try (complete (unfold matching_entries in *; simpl in *; tcsp)).

  inversion h; clear h; subst; simpl in *.
  destruct entry as [vals1 restr1]; simpl in *.
  { exists vals1; dands; tcsp; eauto 3 with slow. }
  exists (vals ++ vals'); dands; eauto 3 with slow.
  eexists; eauto.
Qed.
Hint Resolve lib_cs_in_library_extends_implies : slow.

Lemma find_cs_some_implies_entry_in_library {o} :
  forall (lib : @library o) name vals,
    find_cs lib name = Some vals
    -> entry_in_library (lib_cs name vals) lib.
Proof.
  induction lib; simpl; introv fcs; tcsp.
  destruct a; simpl in *; boolvar; ginv; GC; tcsp.
Qed.
Hint Resolve find_cs_some_implies_entry_in_library : slow.

Lemma lib_extends_preserves_find_cs {o} :
  forall (lib1 lib2 : @library o) name entry1,
    lib_extends lib2 lib1
    -> find_cs lib1 name = Some entry1
    ->
    exists (vals2 : ChoiceSeqVals),
      find_cs lib2 name = Some (MkChoiceSeqEntry _ vals2 (entry2restriction entry1))
      /\ choice_sequence_vals_extend vals2 entry1.
Proof.
  introv ext fcs.
  apply find_cs_some_implies_entry_in_library in fcs.
  eapply implies_lib_extends_ext in fcs; eauto; eauto 3 with slow.
Qed.

Hint Rewrite minus0 : num.

Lemma find_value_of_cs_at_app {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) n,
    find_value_of_cs_at (vals1 ++ vals2) n
    = match find_value_of_cs_at vals1 n with
      | Some v => Some v
      | None => find_value_of_cs_at vals2 (n - length vals1)
      end.
Proof.
  induction vals1; introv; simpl; autorewrite with num in *; tcsp.
  destruct n; simpl in *; auto.
Qed.

Lemma choice_sequence_vals_extend_preserves_find_value_of_cs_at {o} :
  forall (vals1 vals2 : @ChoiceSeqVals o) n v,
    choice_sequence_vals_extend vals2 vals1
    -> find_value_of_cs_at vals1 n = Some v
    -> find_value_of_cs_at vals2 n = Some v.
Proof.
  introv h fcs.
  unfold choice_sequence_vals_extend in h; exrepnd; subst.
  rewrite find_value_of_cs_at_app.
  allrw; auto.
Qed.
Hint Resolve choice_sequence_vals_extend_preserves_find_value_of_cs_at : slow.

Lemma lib_extends_preserves_find_cs_value_at {o} :
  forall (lib1 lib2 : @library o) name n v,
    lib_extends lib2 lib1
    -> find_cs_value_at lib1 name n = Some v
    -> find_cs_value_at lib2 name n = Some v.
Proof.
  introv ext find.
  unfold find_cs_value_at in *.
  remember (find_cs lib1 name) as fcs; symmetry in Heqfcs; destruct fcs; ginv.
  eapply lib_extends_preserves_find_cs in Heqfcs;[|eauto].
  exrepnd; allrw; eauto 2 with slow.
Qed.
Hint Resolve lib_extends_preserves_find_cs_value_at : slow.

Lemma subset_get_utokens_library_implies_subset_get_utokens_lib {o} :
  forall (lib1 lib2 : @library o) t,
    subset (get_utokens_library lib1) (get_utokens_library lib2)
    -> subset (get_utokens_lib lib1 t) (get_utokens_lib lib2 t).
Proof.
  introv ss i; allrw in_app_iff; repndors; tcsp.
Qed.
Hint Resolve subset_get_utokens_library_implies_subset_get_utokens_lib : slow.

Lemma unfold_abs_iff_find_entry {o} :
  forall (lib : @library o) oa bs t,
    unfold_abs lib oa bs = Some t
    <=> {oa' : opabs
         & {vars : list sovar_sig
         & {rhs : SOTerm
         & {correct : correct_abs oa' vars rhs
         & find_entry lib oa bs = Some (lib_abs oa' vars rhs correct)
         # matching_entry oa oa' vars bs
         # t = mk_instance vars bs rhs}}}}.
Proof.
  induction lib; simpl in *; introv; split; intro h; exrepnd; ginv.

  - remember (unfold_abs_entry a oa bs) as ua; symmetry in Hequa; destruct ua; ginv.

    + destruct a; simpl in *; ginv.
      boolvar; ginv.
      eexists; eexists; eexists; eexists; dands; eauto.

    + apply IHlib in h; exrepnd; subst.
      destruct a; simpl in *; boolvar; tcsp; GC;
        eexists; eexists; eexists; eexists; dands; eauto.

  - destruct a; subst; simpl in *; tcsp.

    + apply IHlib.
      eexists; eexists; eexists; eexists; dands; eauto.

    + boolvar; tcsp; auto.

      * inversion h0; subst; clear h0; auto.

      * apply IHlib.
        eexists; eexists; eexists; eexists; dands; eauto.
Qed.

Lemma lib_extends_preserves_unfold_abs {o} :
  forall (lib1 lib2 : @library o) abs bs t,
    lib_extends lib2 lib1
    -> unfold_abs lib1 abs bs = Some t
    -> unfold_abs lib2 abs bs = Some t.
Proof.
  introv ext ua.
  allrw @unfold_abs_iff_find_entry.
  exrepnd; subst.

  eapply lib_extends_preserves_find_entry in ua0;[|eauto].
  eexists; eexists; eexists; eexists; dands; eauto.
Qed.

Lemma lib_extends_preserves_compute_step_lib {o} :
  forall (lib1 lib2 : @library o) abs bs t,
    lib_extends lib2 lib1
    -> compute_step_lib lib1 abs bs = csuccess t
    -> compute_step_lib lib2 abs bs = csuccess t.
Proof.
  introv ext comp.
  unfold compute_step_lib in *.
  remember (unfold_abs lib1 abs bs) as ua; symmetry in Hequa; destruct ua; ginv.
  erewrite lib_extends_preserves_unfold_abs;[|eauto|eauto]; auto.
Qed.

(*
(*

  We should be able to prove equality!
  I left the lemma above.
  See computation_preserves_utok.v

 *)
Lemma compute_step_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wf   : wf_term a)
         (comp : compute_step lib1 a = csuccess b),
    {b' : NTerm & compute_step lib2 a = csuccess b' # alpha_eq b' b}.
Proof.
  nterm_ind1s a as [v|op bs ind] Case; introv wfa comp.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "oterm".
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv.
      csunf; simpl; eexists; dands; eauto.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      { destruct t as [x|op bts]; try (complete (allsimpl; ginv));[].

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; allsimpl.
              apply compute_step_apply_success in comp.
              repndors; exrepnd; subst; auto;
                csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NEApply".

              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; allsimpl; auto.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.

                + unfold mk_lam in *; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  apply iscan_implies in comp0; repndors; exrepnd; subst; simpl; auto;
                    eexists; dands; eauto.

                + unfold mk_choice_seq in *; allsimpl; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try omega.
                  rewrite Znat.Nat2Z.id; auto.
                  erewrite lib_extends_preserves_find_cs_value_at;eauto.

              - fold_terms; rewrite compute_step_eapply_iscan_isexc; auto.
                eexists; dands; eauto.

              - fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; auto.

                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp1; clear q; eauto 2 with slow wf.
                exrepnd; allrw; simpl.
                eexists; dands; eauto; repeat prove_alpha_eq4.
            }

            {
              SSSCase "NFix".

              csunf comp; allsimpl.
              apply compute_step_fix_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NSpread".

              csunf comp; allsimpl.
              apply compute_step_spread_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NDsup".

              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NDecide".

              csunf comp; allsimpl.
              apply compute_step_decide_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; auto;
                csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NCbv".

              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto.
            }

            {
              SSSCase "NSleep".

              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto; tcsp.
            }

            {
              SSSCase "NTUni".

              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              unfold compute_step_tuni; simpl.
              boolvar; try omega.
              rewrite Znat.Nat2Z.id; auto.
              eexists; dands; eauto.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto; tcsp.
            }

            {
              SSSCase "NFresh".

              csunf comp; allsimpl; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; allsimpl.
              apply compute_step_try_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto; tcsp.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto; tcsp.
            }

            {
              SSSCase "NCompSeq1".

              csunf comp; allsimpl.
              apply compute_step_comp_seq1_success in comp; exrepnd; subst.
              repndors; repnd; subst; csunf; simpl.
              { eexists; dands; eauto. }
              boolvar; autorewrite with slow in *; try omega.
              eexists; dands; eauto.
            }

            {
              SSSCase "NCompSeq2".

              csunf comp; allsimpl.
              apply compute_step_comp_seq2_success in comp; exrepnd; subst.
              repndors; repnd; subst; csunf; simpl.
              { boolvar; autorewrite with slow in *; try omega.
                eexists; dands; eauto. }
              { boolvar; autorewrite with slow in *; try omega.
                eexists; dands; eauto. }
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.
                simpl; allrw; eexists; dands; eauto.

              - rewrite compute_step_ncompop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q; eauto 2 with slow wf.
                exrepnd; allrw; eexists; dands; eauto; repeat prove_alpha_eq4.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
                eexists; dands; eauto.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.
                simpl; allrw; eexists; dands; eauto.

              - rewrite compute_step_narithop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q; eauto 3 with wf slow.
                exrepnd; allrw; eexists; dands; eauto; repeat prove_alpha_eq4.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
                eexists; dands; eauto.
            }

            {
              SSSCase "NCanTest".

              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl; eexists; dands; eauto; tcsp.
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step lib1 (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q; eauto 3 with slow wf.
            csunf; simpl.
            exrepnd; allrw; simpl; eexists; dands; eauto; tcsp; repeat prove_alpha_eq4.

          + SSCase "Exc".

            csunf comp; allsimpl.
            apply compute_step_catch_success in comp.
            repndors; exrepnd; subst; allsimpl; ginv.

            * csunf; simpl; auto.
              eexists; dands; eauto.

            * csunf; simpl; auto.
              rewrite compute_step_catch_if_diff; auto.
              eexists; dands; eauto.

          + SSCase "Abs".

            csunf comp; allsimpl.
            remember (compute_step lib1 (oterm (Abs abs2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q; eauto 3 with wf slow.
            csunf; simpl.
            exrepnd; allrw; simpl; eexists; dands; eauto; repeat prove_alpha_eq4.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; ginv.

        - csunf; simpl; boolvar; auto.
          eexists; dands; eauto.

        - rewrite compute_step_fresh_if_isvalue_like2; auto.
          eexists; dands; eauto.

        - fold (mk_fresh n t).
          rewrite compute_step_fresh_if_isnoncan_like; auto.

          remember (get_fresh_atom lib1 t) as a.
          pose proof (get_fresh_atom_prop_and_lib lib1 t) as prop; rewrite <- Heqa in prop.
          clear Heqa.

          remember (get_fresh_atom lib2 t) as a'.
          pose proof (get_fresh_atom_prop_and_lib lib2 t) as prop'; rewrite <- Heqa' in prop'.
          clear Heqa'.

          simpl.

          pose proof (compute_step_subst_utoken lib1 t x [(n,mk_utoken a)]) as q.
          repeat (autodimp q hyp); eauto 3 with wf;
            [autorewrite with slow; simpl; apply disjoint_singleton_l; auto|];[].
          exrepnd.
          autorewrite with slow in *; simpl in *; allrw disjoint_singleton_l.

          pose proof (q0 [(n,mk_utoken a')]) as z.
          autorewrite with slow in z; simpl in z; allrw disjoint_singleton_l.
          repeat (autodimp z hyp); eauto 5 with slow;[].
          exrepnd.

          pose proof (ind t (subst t n (mk_utoken a')) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow;[|].
          { rewrite simple_osize_subst; eauto 2 with slow. }
          fold_terms.
          apply q in z1; clear q; eauto 2 with wf;[].

          exrepnd.
          allrw; simpl.
          eexists; dands; eauto.
          unfold mk_fresh.
          repeat prove_alpha_eq4.
          apply alpha_eq_bterm_congr.

          eapply alpha_eq_trans in z0;[|exact z2].
          eapply alpha_eq_trans;
            [apply alpha_eq_subst_utokens;
             [eauto|apply alphaeq_utok_sub_refl] |].
          eapply alpha_eq_trans;
            [|apply alpha_eq_sym;apply alpha_eq_subst_utokens;
              [eauto|apply alphaeq_utok_sub_refl] ].

          eapply alpha_eq_trans;[apply simple_alphaeq_subst_utokens_subst;eauto 6 with slow|];[].

          eapply alpha_eq_trans;[|apply alpha_eq_sym;apply simple_alphaeq_subst_utokens_subst;eauto 4 with slow].
          auto.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.
      csunf; simpl; eexists; dands; eauto.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.
      csunf; simpl.

      apply found_entry_implies_compute_step_lib_success in comp0.
      eapply lib_extends_preserves_compute_step_lib in comp0;[|eauto].
      rewrite comp0.
      eexists; dands; eauto.
Qed.
*)

(*
Lemma reduces_in_atmost_k_steps_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wfa  : wf_term a)
         (n    : nat)
         (comp : reduces_in_atmost_k_steps lib1 a b n),
    {b' : NTerm & reduces_in_atmost_k_steps lib2 a b' n # alpha_eq b b'}.
Proof.
  introv ext wf comp.

  revert dependent a.
  induction n; introv wf comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists b; allrw @reduces_in_atmost_k_steps_0; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    applydup @compute_step_preserves_wf in comp1; auto.
    apply IHn in comp0; exrepnd; auto; clear IHn.
    apply (compute_step_preserves_lib_extends lib1 lib2) in comp1; auto; exrepnd.

    pose proof (reduces_in_atmost_k_steps_alpha lib2 u b'0) as w.
    repeat (autodimp w hyp); eauto 3 with slow wf.
    applydup w in comp0; clear w; exrepnd.

    eexists; dands;[rw @reduces_in_atmost_k_steps_S;eexists; dands; eauto|].
    eauto 2 with slow.
Qed.
*)

(*
Lemma reduces_to_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
         (a b  : @NTerm o)
         (wf   : wf_term a)
         (comp : reduces_to lib1 a b),
    {b' : NTerm & reduces_to lib2 a b' # alpha_eq b b'}.
Proof.
  introv ext wf r.
  unfold reduces_to in *; exrepnd.
  eapply reduces_in_atmost_k_steps_preserves_lib_extends in r0; eauto.
  exrepnd.
  eexists; eexists; dands; eauto.
Qed.
*)

(*
Lemma computes_to_valc_preserves_lib_extends {o} :
  forall (lib1 lib2 : library)
         (ext  : lib_extends lib2 lib1) (* lib2 extends lib1 *)
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
*)

Lemma alphaeqc_mkc_nat_implies {o} :
  forall n (t : @CTerm o),
    alphaeqc (mkc_nat n) t -> t = mkc_nat n.
Proof.
  introv aeq; destruct_cterms; unfold alphaeqc in aeq; simpl in *.
  apply cterm_eq; simpl.
  apply alpha_eq_mk_nat in aeq; auto.
Qed.

(*
Lemma computes_to_valc_nat_if_lib_extends {o} :
  forall (lib1 lib2 : @library o) t n,
    lib_extends lib1 lib2
    -> computes_to_valc lib2 t (mkc_nat n)
    -> computes_to_valc lib1 t (mkc_nat n).
Proof.
  introv ext comp.
  pose proof (computes_to_valc_preserves_lib_extends
                lib2 lib1 ext t (mkc_nat n) comp) as h.
  exrepnd.
  apply alphaeqc_mkc_nat_implies in h0; subst; auto.
Qed.
 *)
