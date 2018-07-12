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




(*

  We want to say that a property is true w.r.t. a library [lib] if there exists
  a finite finite extension of the library [lib'] (containing only choice sequences)
  and an infinite number of renamings [n->ren(n)] such that the property is true
  in [lib + ren(n)(lib')] and this for all [n].

 *)

Record ChoiceSequenceEntry {o} :=
  MkChoiceSequenceEntry
    {
      cseqe_name  : choice_sequence_name;
      cseqe_entry : @ChoiceSeqEntry o;
      cseqe_safe  : safe_choice_sequence_entry cseqe_name cseqe_entry
    }.
Arguments MkChoiceSequenceEntry [o] _ _ _.

Definition cs_ren := list (cs_name * cs_name).


Definition one_cs_swap (a b : cs_name) (v : cs_name) : cs_name :=
  if String.string_dec v a then b
  else if String.string_dec v b then a
       else v.

Fixpoint swap_cs_name (l : cs_ren) (name : cs_name) : cs_name :=
  match l with
  | [] => name
  | (a,b) :: rest => swap_cs_name rest (one_cs_swap a b name)
  end.

Definition cs_swap_choice_sequence_name
           (ren  : cs_ren)
           (name : choice_sequence_name)
  : choice_sequence_name :=
  match name with
  | MkChoiceSequenceName csn csk =>
    MkChoiceSequenceName (swap_cs_name ren csn) csk
  end.

Lemma safe_swap_choice_sequence_name {o} :
  forall (ren  : cs_ren)
         {name : choice_sequence_name}
         {e    : @ChoiceSeqEntry o},
    safe_choice_sequence_entry name e
    -> safe_choice_sequence_entry (cs_swap_choice_sequence_name ren name) e.
Proof.
  introv safe.
  unfold safe_choice_sequence_entry in *.
  destruct e; simpl in *; repnd; dands; auto.
  unfold correct_restriction in *; tcsp.
  destruct name as [name kind]; simpl in *; tcsp.
Qed.
Hint Resolve safe_swap_choice_sequence_name : slow.


Definition cs_ren_ChoiceSequenceEntry {o}
           (ren : cs_ren)
           (e : @ChoiceSequenceEntry o)
  : ChoiceSequenceEntry :=
  match e with
  | MkChoiceSequenceEntry name e safe =>
    MkChoiceSequenceEntry
      (cs_swap_choice_sequence_name ren name)
      e
      (safe_swap_choice_sequence_name ren safe)
  end.

Definition cs_ren_ChoiceSequenceEntries {o}
           (ren : cs_ren)
           (l   : list (@ChoiceSequenceEntry o))
  : list ChoiceSequenceEntry :=
  map (cs_ren_ChoiceSequenceEntry ren) l.

Definition ChoiceSequenceEntry2entry {o} (e : @ChoiceSequenceEntry o) : library_entry :=
  match e with
  | MkChoiceSequenceEntry name e safe => lib_cs name e
  end.

Definition ChoiceSequenceEntries2lib {o} (l : list (@ChoiceSequenceEntry o)) : library :=
  map ChoiceSequenceEntry2entry l.

(* do we need to say that the renamings cover the extension? *)
Definition ex_finite_ext {o}
           (lib : @library o)
           (F   : @library o -> Prop) :=
  exists (ext : list ChoiceSequenceEntry),
  exists (rens : nat -> cs_ren),
  forall n,
    F (lib ++ ChoiceSequenceEntries2lib (cs_ren_ChoiceSequenceEntries (rens n) ext)).

Definition e_in_ext {o} (lib : @library o) (F : @library o -> Prop) :=
  forall (lib' : library),
    lib_extends lib' lib
    -> ex_finite_ext lib' F.

Definition e_all_in_bar {o} {lib} (bar : BarLib lib) (F : @library o -> Prop) :=
  forall (lib' : library), bar_lib_bar bar lib' -> e_in_ext lib' F.


Definition e_in_bar {o} (lib : @library o) (F : @library o -> Prop) :=
  exists (bar : BarLib lib), e_all_in_bar bar F.


Lemma implies_e_all_in_bar_intersect_bars_left {o} :
  forall {lib} (bar bar' : @BarLib o lib) F,
    e_all_in_bar bar F
    -> e_all_in_bar (intersect_bars bar bar') F.
Proof.
  introv a i j.
  simpl in *; exrepnd.
  eapply a; eauto 2 with slow.
Qed.
Hint Resolve implies_e_all_in_bar_intersect_bars_left : slow.

Lemma implies_e_all_in_bar_intersect_bars_right {o} :
  forall {lib} (bar bar' : @BarLib o lib) F,
    e_all_in_bar bar F
    -> e_all_in_bar (intersect_bars bar' bar) F.
Proof.
  introv a i j.
  simpl in *; exrepnd.
  eapply a; eauto 2 with slow.
Qed.
Hint Resolve implies_e_all_in_bar_intersect_bars_right : slow.




Lemma implies_lib_extends_entries_app_l {o} :
  forall (lib1 lib2 : @library o),
    lib_extends_entries (lib1 ++ lib2) lib1.
Proof.
  introv h.
  induction lib1; simpl in *; tcsp.
  repndors; repnd; subst; tcsp;[].
  left; eauto 3 with slow.
Qed.
Hint Resolve implies_lib_extends_entries_app_l : slow.

Lemma implies_safe_library_app {o} :
  forall (lib1 lib2 : @library o),
    safe_library lib1 -> safe_library lib2 -> safe_library (lib1 ++ lib2).
Proof.
  introv safe1 safe2 i.
  apply entry_in_library_app_implies in i; repndors; repnd; tcsp.
Qed.
Hint Resolve implies_safe_library_app : slow.

Lemma subset_library_app_l {o} :
  forall (lib1 lib2 : @library o),
    subset_library lib1 (lib1 ++ lib2).
Proof.
  introv i; exists entry1; dands; eauto 3 with slow.
  apply in_or_app; tcsp.
Qed.
Hint Resolve subset_library_app_l : slow.

Lemma implies_lib_extends_app_r {o} :
  forall (lib1 : @library o) {lib2},
    safe_library lib2
    -> lib_extends (lib1 ++ lib2) lib1.
Proof.
  introv safe; split; eauto 3 with slow.
Qed.
Hint Resolve implies_lib_extends_app_r : slow.

Lemma safe_ren_ChoiceSequenceEntries2lib {o} :
  forall (ext : list (@ChoiceSequenceEntry o)) ren,
    safe_library (ChoiceSequenceEntries2lib (cs_ren_ChoiceSequenceEntries ren ext)).
Proof.
  introv i.

  unfold ChoiceSequenceEntries2lib in i.
  apply entry_in_library_implies_in in i.
  apply List.in_map_iff in i; exrepnd; subst.

  unfold cs_ren_ChoiceSequenceEntries in i0.
  apply List.in_map_iff in i0; exrepnd; subst.

  destruct x0 as [name e safe]; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve safe_ren_ChoiceSequenceEntries2lib : slow.

Definition ex_finite_ext_ext {o}
           (lib lib' : @library o)
           (xt  : lib_extends lib' lib)
           (F   : forall (lib' : @library o), lib_extends lib' lib -> Prop) :=
  exists (ext : list ChoiceSequenceEntry),
  exists (rens : nat -> cs_ren),
  forall n,
    F (lib' ++ ChoiceSequenceEntries2lib (cs_ren_ChoiceSequenceEntries (rens n) ext))
      (lib_extends_trans
         (implies_lib_extends_app_r
            lib'
            (safe_ren_ChoiceSequenceEntries2lib ext (rens n)))
         xt).

Definition e_in_ext_ext {o} (lib : @library o) (F : forall (lib' : @library o), lib_extends lib' lib -> Prop) :=
  forall (lib' : library) (e : lib_extends lib' lib),
    ex_finite_ext_ext lib lib' e F.

Definition e_all_in_bar_ext {o} {lib}
           (bar : BarLib lib)
           (F : forall (lib' : @library o), lib_extends lib' lib -> Prop) :=
  forall (lib' : library) (b : bar_lib_bar bar lib'),
    e_in_ext_ext
      lib'
      (fun l e =>
         forall (x : lib_extends l lib),
           F l x).
