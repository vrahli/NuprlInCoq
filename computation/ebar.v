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

Definition ChoiceSequenceEntries2lib {o} (l : list (@ChoiceSequenceEntry o)) : plibrary :=
  map ChoiceSequenceEntry2entry l.

Definition ChoiceSequenceEntries {o} := list (@ChoiceSequenceEntry o).

Record CsRens :=
  MkCsRens
    {
      csr_ren :> nat -> cs_ren;
    }.

Definition ext_ren {o}
           (lib  : @plibrary o)
           (lext : ChoiceSequenceEntries)
           (rens : CsRens)
           (n    : nat) :=
  lib ++ ChoiceSequenceEntries2lib (cs_ren_ChoiceSequenceEntries (rens n) lext).

(* QUESTION:
   (1) We probably need to say that the renamings cover the extension.
   (2) We probably need to say that all renamings are different from each other *)
Definition ex_finite_ext {o}
           (lib : @library o)
           (F   : @library o -> Prop) :=
  exists (lib' : library) (xt : lib_extends lib' lib),
    in_ext lib' F.

(*  exists (lext : ChoiceSequenceEntries),
  exists (rens : CsRens),
  forall n,
    F (ext_ren lib lext rens n).*)

Definition e_in_ext {o} (lib : @library o) (F : @library o -> Prop) :=
  forall (lib' : library),
    lib_extends lib' lib
    -> ex_finite_ext lib' F.

(*Definition e_all_in_bar {o} {lib} (bar : BarLib lib) (F : @library o -> Prop) :=
  forall (lib' : library), bar_lib_bar bar lib' -> e_in_ext lib' F.
*)

(*Definition e_in_bar {o} (lib : @library o) (F : @library o -> Prop) :=
  exists (bar : BarLib lib), e_all_in_bar bar F.
*)

(*Lemma implies_e_all_in_bar_intersect_bars_left {o} :
  forall {lib} (bar bar' : @BarLib o lib) F,
    e_all_in_bar bar F
    -> e_all_in_bar (intersect_bars bar bar') F.
Proof.
  introv a i j.
  simpl in *; exrepnd.
  eapply a; eauto 2 with slow.
Qed.
Hint Resolve implies_e_all_in_bar_intersect_bars_left : slow.*)

(*Lemma implies_e_all_in_bar_intersect_bars_right {o} :
  forall {lib} (bar bar' : @BarLib o lib) F,
    e_all_in_bar bar F
    -> e_all_in_bar (intersect_bars bar' bar) F.
Proof.
  introv a i j.
  simpl in *; exrepnd.
  eapply a; eauto 2 with slow.
Qed.
Hint Resolve implies_e_all_in_bar_intersect_bars_right : slow.*)




Lemma implies_lib_extends_entries_app_l {o} :
  forall (lib1 lib2 : @plibrary o),
    lib_extends_entries (lib1 ++ lib2) lib1.
Proof.
  introv h.
  induction lib1; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.
Qed.
Hint Resolve implies_lib_extends_entries_app_l : slow.

Lemma implies_safe_library_app {o} :
  forall (lib1 lib2 : @plibrary o),
    safe_library lib1 -> safe_library lib2 -> safe_library (lib1 ++ lib2).
Proof.
  introv safe1 safe2 i.
  apply entry_in_library_app_implies in i; repndors; repnd; tcsp.
Qed.
Hint Resolve implies_safe_library_app : slow.

Lemma subset_library_app_l {o} :
  forall (lib1 lib2 : @plibrary o),
    subset_library lib1 (lib1 ++ lib2).
Proof.
  introv i; exists entry1; dands; eauto 3 with slow.
  apply in_or_app; tcsp.
Qed.
Hint Resolve subset_library_app_l : slow.

(*Lemma implies_lib_extends_app_r {o} :
  forall (lib1 : @library o) {lib2},
    safe_library lib2
    -> lib_extends (lib1 ++ lib2) lib1.
Proof.
  introv safe; split; eauto 3 with slow.
Qed.
Hint Resolve implies_lib_extends_app_r : slow.*)

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

(*Lemma lib_extends_ext_ren {o} :
  forall (lib : @library o) lext rens n,
    lib_extends (ext_ren lib lext rens n) lib.
Proof.
  introv; apply implies_lib_extends_app_r; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_ext_ren : slow.*)

(*Definition all_in_ex_bar {o} (lib : @library o) F :=
  exists (bar : BarLib lib), all_in_bar bar F.*)

Definition in_ext_ext {o} (lib : @library o) (F : forall (lib' : @library o), lib_extends lib' lib -> Prop) :=
  forall (lib' : library) (e : lib_extends lib' lib), F lib' e.

(*Definition all_in_bar_ext {o} {lib}
           (bar : BarLib lib)
           (F : forall (lib' : @library o), lib_extends lib' lib -> Prop) :=
  forall (lib' : library) (b : bar_lib_bar bar lib'),
    in_ext_ext
      lib'
      (fun l e =>
         forall (x : lib_extends l lib),
                F l x).*)

(*Definition all_in_ex_bar_ext {o} (lib : @library o) F :=
  exists (bar : BarLib lib), all_in_bar_ext bar F.*)

Definition ex_finite_ext_ext {o}
           (lib lib' : @library o)
           (xt  : lib_extends lib' lib)
           (F   : forall (lib' : @library o), lib_extends lib' lib -> Prop) :=
  exists (lib'' : library) (xt' : lib_extends lib'' lib'),
    in_ext_ext lib'' (fun lib0 x => F lib0 (lib_extends_trans (lib_extends_trans x xt') xt)).

(*  exists (lext : ChoiceSequenceEntries),
  exists (rens : CsRens),
  forall n,
    F (ext_ren lib' lext rens n)
      (lib_extends_trans
         (implies_lib_extends_app_r
            lib'
            (safe_ren_ChoiceSequenceEntries2lib lext (rens n)))
         xt).*)

Definition e_in_ext_ext {o}
           (lib : @library o)
           (F : forall (lib' : @library o), lib_extends lib' lib -> Prop) :=
  forall (lib' : library) (e : lib_extends lib' lib),
    ex_finite_ext_ext lib lib' e F.

(*Definition e_all_in_bar_ext {o} {lib}
           (bar : BarLib lib)
           (F : forall (lib' : @library o), lib_extends lib' lib -> Prop) :=
  forall (lib' : library) (b : bar_lib_bar bar lib'),
    e_in_ext_ext
      lib'
      (fun l e =>
         forall (x : lib_extends l lib),
           F l x).*)

(*Definition e_all_in_ex_bar {o} (lib : @library o) F :=
  exists (bar : BarLib lib), e_all_in_bar bar F.*)

(* MOVE *)
(*Definition e_all_in_ex_bar_ext {o} (lib : @library o) F :=
  exists (bar : BarLib lib), e_all_in_bar_ext bar F.*)

(* MOVE *)
Definition emCsRens : CsRens := MkCsRens (fun (n : nat) => []).


Lemma ext_ren_nil {o} :
  forall (lib : @plibrary o) rens n,
    ext_ren lib [] rens n = lib.
Proof.
  unfold ext_ren; introv; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @ext_ren_nil : slow.

Lemma lib_extends_preserves_in_ext {o} :
  forall (lib1 lib2 : @library o) F,
    lib_extends lib2 lib1
    -> in_ext lib1 F
    -> in_ext lib2 F.
Proof.
  introv ext h xt.
  apply h; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_in_ext : slow.

(*Lemma all_in_bar_implies_e_all_in_bar {o} :
  forall (lib : @library o) (bar : BarLib lib) F,
    all_in_bar bar F
    -> e_all_in_bar bar F.
Proof.
  introv h b e.
  pose proof (h _ b) as h.
  exists lib'0 (lib_extends_refl lib'0); auto; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_implies_e_all_in_bar : slow.*)

(*Lemma all_in_ex_bar_implies_e_all_in_ex_bar {o} :
  forall (lib : @library o) F,
    all_in_ex_bar lib F
    -> e_all_in_ex_bar lib F.
Proof.
  introv h.
  unfold e_all_in_ex_bar.
  unfold all_in_ex_bar in h; exrepnd.
  exists bar; eauto 3 with slow.
Qed.
Hint Resolve all_in_ex_bar_implies_e_all_in_ex_bar : slow.*)

(*Lemma all_in_bar_ext_implies_e_all_in_bar_ext {o} :
  forall (lib : @library o) (bar : BarLib lib) F,
    all_in_bar_ext bar F
    -> e_all_in_bar_ext bar F.
Proof.
  introv h b; introv.
  pose proof (h _ b) as h; simpl in *.
  exists lib'0 (lib_extends_refl lib'0); auto.
  introv xt; introv.
  apply h; eauto 3 with slow.
Qed.
Hint Resolve all_in_bar_ext_implies_e_all_in_bar_ext : slow.*)

(*Lemma all_in_ex_bar_ext_implies_e_all_in_ex_bar_ext {o} :
  forall (lib : @library o) F,
    all_in_ex_bar_ext lib F
    -> e_all_in_ex_bar_ext lib F.
Proof.
  introv h.
  unfold e_all_in_ex_bar_ext.
  unfold all_in_ex_bar_ext in h; exrepnd.
  exists bar; eauto 3 with slow.
Qed.
Hint Resolve all_in_ex_bar_implies_e_all_in_ex_bar : slow.*)


(*Lemma e_all_in_bar_modus_ponens1 {o} :
  forall (lib : @library o) (bar : BarLib lib) (F G : library -> Prop),
    in_ext lib (fun lib => G lib -> F lib)
    -> e_all_in_bar bar G
    -> e_all_in_bar bar F.
Proof.
  introv h q b e; repeat introv.
  pose proof (q _ b _ e) as q.
  unfold ex_finite_ext in *; exrepnd; simpl in *.
  exists lib'1 xt; auto.
  introv xt'.
  apply h; auto; eauto 5 with slow.
Qed.*)

(*Lemma e_all_in_bar_ext_modus_ponens1 {o} :
  forall (lib : @library o) (bar : BarLib lib) (F G : forall (lib' : library) (e : lib_extends lib' lib), Prop),
    in_ext_ext lib (fun lib' (e : lib_extends lib' lib) => G lib' e -> F lib' e)
    -> e_all_in_bar_ext bar G
    -> e_all_in_bar_ext bar F.
Proof.
  introv h q b; introv.
  pose proof (q _ b _ e) as q.
  unfold ex_finite_ext_ext in *; exrepnd; simpl in *.
  exists lib'' xt'; auto.
  introv xt; introv; apply h; eauto.
Qed.*)

(*Lemma e_all_in_ex_bar_modus_ponens1 {o} :
  forall (lib : @library o) (F G : library -> Prop),
    in_ext lib (fun lib => G lib -> F lib)
    -> e_all_in_ex_bar lib G
    -> e_all_in_ex_bar lib F.
Proof.
  introv h q; repeat introv.
  unfold e_all_in_ex_bar in *; exrepnd; exists bar.
  eapply e_all_in_bar_modus_ponens1;[|eauto]; auto.
Qed.*)

(*Lemma e_all_in_ex_bar_ext_modus_ponens1 {o} :
  forall (lib : @library o) (F G : forall (lib' : library) (e : lib_extends lib' lib), Prop),
    in_ext_ext lib (fun lib' (e : lib_extends lib' lib) => G lib' e -> F lib' e)
    -> e_all_in_ex_bar_ext lib G
    -> e_all_in_ex_bar_ext lib F.
Proof.
  introv h q; repeat introv.
  unfold e_all_in_ex_bar_ext in *; exrepnd; exists bar.
  eapply e_all_in_bar_ext_modus_ponens1;[|eauto]; auto.
Qed.*)

Lemma ex_finite_ext_pres {o} :
  forall (lib : @library o) (F G : @library o -> Prop),
    in_ext lib (fun lib' => F lib' -> G lib')
    -> ex_finite_ext lib F
    -> ex_finite_ext lib G.
Proof.
  introv imp h.
  unfold ex_finite_ext in *; exrepnd.
  exists lib' xt; eauto.
  introv x; apply imp; eauto 3 with slow.
Qed.

Lemma ex_finite_ext_ext_pres {o} :
  forall (lib1 lib2 lib3 : @library o)
         (xt1 : lib_extends lib3 lib1)
         (xt2 : lib_extends lib3 lib2)
         (F : forall lib', lib_extends lib' lib1 -> Prop)
         (G : forall lib', lib_extends lib' lib2 -> Prop),
    in_ext_ext
      lib3
      (fun lib' (x : lib_extends lib' lib3) =>
         F lib' (lib_extends_trans x xt1)
         -> G lib' (lib_extends_trans x xt2))
    -> ex_finite_ext_ext lib1 lib3 xt1 F
    -> ex_finite_ext_ext lib2 lib3 xt2 G.
Proof.
  introv imp h.
  unfold ex_finite_ext_ext in *; exrepnd.
  exists lib'' xt'; eauto.
  introv; eapply imp; eauto.
Qed.

(*Lemma e_all_in_ex_bar_ext_pres {o} :
  forall (lib : @library o)
         (F G : forall lib' (x : lib_extends lib' lib), Prop),
    (forall (bar : BarLib lib)
            lib' (br : bar_lib_bar bar lib')
            lib'' (x : lib_extends lib'' lib')
            (y : lib_extends lib'' lib),
        F lib'' y
        -> G lib'' y)
    -> e_all_in_ex_bar_ext lib F
    -> e_all_in_ex_bar_ext lib G.
Proof.
  introv imp h.
  unfold e_all_in_ex_bar_ext in *; exrepnd.
  exists bar; introv br; introv.
  pose proof (h0 _ br _ e) as h0.
  eapply ex_finite_ext_ext_pres; eauto.
  introv xta z; introv; eauto.
  eapply imp; eauto; eauto 3 with slow.
Qed.*)

(*Lemma e_all_in_ex_bar_pres {o} :
  forall (lib : @library o)
         (F G : library -> Prop),
    (forall (bar : BarLib lib)
            lib' (br : bar_lib_bar bar lib')
            lib'' (x : lib_extends lib'' lib'),
        F lib''
        -> G lib'')
    -> e_all_in_ex_bar lib F
    -> e_all_in_ex_bar lib G.
Proof.
  introv imp h.
  unfold e_all_in_ex_bar in *; exrepnd.
  exists bar; introv br e; introv.
  pose proof (h0 _ br _ e) as h0.
  eapply ex_finite_ext_pres;[|eauto].
  introv xta z; introv; eauto.
  eapply imp; eauto; eauto 3 with slow.
Qed.*)

Lemma in_ext_implies {o} :
  forall (lib : @library o) F,
    in_ext lib F -> F lib.
Proof.
  introv h; apply h; eauto 3 with slow.
Qed.

Lemma in_ext_ext_implies {o} :
  forall (lib : @library o) F,
    in_ext_ext lib F -> F lib (lib_extends_refl lib).
Proof.
  introv h; apply h.
Qed.
