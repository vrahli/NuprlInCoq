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


Require Export substc_more.
Require Export sequents_tacs.
Require Export per_props_product.
Require Export per_props_function.
Require Export per_props_squash.
Require Export per_props_equality.
Require Export per_props_nat2.
Require Export lsubstc_vars.



Hint Resolve nat_in_nat : slow.

Lemma implies_ccequivc_ext_apply2 {o} :
  forall lib (f g a b c d : @CTerm o),
    ccequivc_ext lib f g
    -> ccequivc_ext lib a b
    -> ccequivc_ext lib c d
    -> ccequivc_ext lib (mkc_apply2 f a c) (mkc_apply2 g b d).
Proof.
  introv ceqa ceqb ceqc x.
  pose proof (ceqa _ x) as ceqa.
  pose proof (ceqb _ x) as ceqb.
  pose proof (ceqc _ x) as ceqc.
  simpl in *; spcast.
  apply implies_cequivc_apply2; auto.
Qed.
Hint Resolve implies_ccequivc_ext_apply2 : slow.

Definition at_open_bar {o} (lib : @library o) F :=
  forall lib',
    lib_extends lib' lib
    -> exists (lib'' : library) (xt : lib_extends lib'' lib'), F lib''.

Lemma in_open_bar_implies_at_open_bar {o} :
  forall (lib : @library o) F,
    in_open_bar lib F
    -> at_open_bar lib F.
Proof.
  introv h ext.
  pose proof (h _ ext) as h; exrepnd.
  exists lib'' xt; apply h1; eauto 3 with slow.
Qed.

Lemma lib_extends_preserves_inhabited_type_bar {o} :
  forall {lib lib'} (x : lib_extends lib' lib) (T : @CTerm o),
    inhabited_type_bar lib T
    -> inhabited_type_bar lib' T.
Proof.
  introv x inh.
  unfold inhabited_type_bar in *; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_inhabited_type_bar : slow.

Definition FunLib {o} (lib : @library o) :=
  forall (lib' : @library o), LibExt lib'.

Definition FunLibProp {o} (lib : @library o) :=
  forall (lib' : @library o), Prop.

Definition NatFunLib {o} (lib : @library o) :=
  forall (n : nat) (lib' : @library o), LibExt lib'.

Definition NatFunLibProp {o} (lib : @library o) :=
  forall (n : nat) (lib' : @library o), Prop.

Definition NatFunLibExt {o} (lib : @library o) :=
  forall (n : nat) lib' (x : lib_extends lib' lib), LibExt lib'.

Definition NatFunLibExtProp {o} (lib : @library o) :=
  forall (n : nat) lib' (x : lib_extends lib' lib), Prop.

Lemma in_open_bar_choice {o} :
  forall (lib : @library o) (F : FunLibProp lib),
    in_open_bar lib F
    -> exists (Flib : FunLibExt lib),
      in_ext_ext
        lib
        (fun lib' x =>
           in_ext_ext (Flib lib' x) (fun lib0 x0 => forall (z : lib_extends lib0 lib), F lib0)).
Proof.
  introv h.
  apply in_open_bar_implies_in_open_bar_ext in h.
  apply in_open_bar_ext_choice in h; auto.
Qed.

Lemma nat_in_open_bar_ext_choice {o} :
  forall (lib : @library o) (F : NatFunLibExtProp lib),
    (forall (k : nat), in_open_bar_ext lib (F k))
    -> exists (Flib : NatFunLibExt lib),
      forall (k : nat),
        in_ext_ext
          lib
          (fun lib' x =>
             in_ext_ext (Flib k lib' x) (fun lib0 x0 => forall (z : lib_extends lib0 lib), F k lib0 z)).
Proof.
  introv h.

  assert (forall (k : nat),
             exists (Flib : FunLibExt lib),
               in_ext_ext
                 lib
                 (fun lib' x =>
                    in_ext_ext (Flib lib' x) (fun lib0 x0 => forall (z : lib_extends lib0 lib), F k lib0 z))) as q.
  {
    introv.
    pose proof (h k) as h.
    apply in_open_bar_ext_choice in h; auto.
  }
  clear h.

  pose proof (FunctionalChoice_on
                nat
                (FunLibExt lib)
                (fun k Flib =>
                   in_ext_ext
                     lib
                     (fun lib1 ext1 =>
                        in_ext_ext
                          (Flib lib1 ext1)
                          (fun lib2 ext2 =>
                             forall z : lib_extends lib2 lib,
                               F k lib2 z)))) as C.
  simpl in C.
  repeat (autodimp C hyp).
Qed.

Lemma nat_in_open_bar_choice {o} :
  forall (lib : @library o) (F : NatFunLibProp lib),
    (forall (k : nat), in_open_bar lib (F k))
    -> exists (Flib : NatFunLibExt lib),
      forall (k : nat),
        in_ext_ext
          lib
          (fun lib' x =>
             in_ext_ext (Flib k lib' x) (fun lib0 x0 => forall (z : lib_extends lib0 lib), F k lib0)).
Proof.
  introv h.
  apply nat_in_open_bar_ext_choice.
  introv.
  apply in_open_bar_implies_in_open_bar_ext; auto.
Qed.

Definition NatFunLibExtNat {o}
           {lib  : @library o}
           (Flib : NatFunLibExt lib) :=
  forall (n : nat)
         lib1 (ext1 : lib_extends lib1 lib)
         lib2 (ext2 : lib_extends lib2 (Flib n lib1 ext1))
         (z : lib_extends lib2 lib),
    nat.

Definition NatFunLibExtNatProp {o}
           {lib  : @library o}
           (Flib : NatFunLibExt lib) :=
  forall (n : nat)
         lib1 (ext1 : lib_extends lib1 lib)
         lib2 (ext2 : lib_extends lib2 (Flib n lib1 ext1))
         (z : lib_extends lib2 lib)
         (n : nat),
    Prop.

Record NatDepLibExt {o} (lib : @library o) (F : NatFunLibExt lib) :=
  MkNatDepLibExt
    {
      nat_dep_lib_ext_nat  : nat;
      nat_dep_lib_ext_lib1 : @library o;
      nat_dep_lib_ext_ext1 : lib_extends nat_dep_lib_ext_lib1 lib;
      nat_dep_lib_ext_lib2 : @library o;
      nat_dep_lib_ext_ext2 : lib_extends nat_dep_lib_ext_lib2 (F nat_dep_lib_ext_nat nat_dep_lib_ext_lib1 nat_dep_lib_ext_ext1);
      nat_dep_lib_ext_extz : lib_extends nat_dep_lib_ext_lib2 lib;
    }.
Arguments MkNatDepLibExt [o] [lib] [F] _ _ _ _ _.
Arguments nat_dep_lib_ext_nat  [o] [lib] [F] _.
Arguments nat_dep_lib_ext_lib1 [o] [lib] [F] _.
Arguments nat_dep_lib_ext_ext1 [o] [lib] [F] _.
Arguments nat_dep_lib_ext_lib2 [o] [lib] [F] _.
Arguments nat_dep_lib_ext_ext2 [o] [lib] [F] _.
Arguments nat_dep_lib_ext_extz [o] [lib] [F] _.

Lemma nat_in_open_bar_choice_nat {o} :
  forall (lib  : @library o)
         (Flib : NatFunLibExt lib)
         (P    : NatFunLibExtNatProp Flib),
    (forall k : nat,
        in_ext_ext
          lib
          (fun lib1 ext1 =>
             in_ext_ext
               (Flib k lib1 ext1)
               (fun lib2 ext2 =>
                  forall (z : lib_extends lib2 lib),
                    exists (j : nat), P k lib1 ext1 lib2 ext2 z j)))
    -> exists (Fnat : NatFunLibExtNat Flib),
    forall k : nat,
      in_ext_ext
        lib
        (fun lib1 ext1 =>
           in_ext_ext
             (Flib k lib1 ext1)
             (fun lib2 ext2 =>
                forall (z : lib_extends lib2 lib),
                P k lib1 ext1 lib2 ext2 z (Fnat k lib1 ext1 lib2 ext2 z))).
Proof.
  introv h.

  pose proof (FunctionalChoice_on
                (NatDepLibExt lib Flib)
                nat
                (fun x n =>
                   P (nat_dep_lib_ext_nat  x)
                     (nat_dep_lib_ext_lib1 x)
                     (nat_dep_lib_ext_ext1 x)
                     (nat_dep_lib_ext_lib2 x)
                     (nat_dep_lib_ext_ext2 x)
                     (nat_dep_lib_ext_extz x)
                     n)) as C.
  simpl in C.
  repeat (autodimp C hyp).
  { introv.
    destruct a as [k lib1 ext1 lib2 ext2 extz]; simpl in *.
    apply h. }
  exrepnd.
  exists (fun k lib1 ext1 lib2 ext2 extz => f (MkNatDepLibExt k lib1 ext1 lib2 ext2 extz)); simpl.
  repeat introv.
  apply (C0 (MkNatDepLibExt k lib' e lib'0 e0 z)).
Qed.

Lemma fresh_choice_seq_name_in_library_with_kind {o} :
  forall (lib : @library o) k,
  exists (name : choice_sequence_name),
    find_cs lib name = None
    /\ csn_kind name = k.
Proof.
  introv.
  pose proof (fresh_string (map csn_name (library2choice_sequence_names lib))) as q.
  exrepnd.
  exists (MkChoiceSequenceName x k); simpl; dands; auto.
  apply not_in_library2choice_sequence_names_iff_find_cs_none; auto.
  introv xx; destruct q0.
  apply in_map_iff; eexists; eauto.
Qed.

Lemma member_nat2nat {o} :
  forall (lib : @library o) f,
    member lib f nat2nat
    <=> in_ext lib (fun lib => forall (k : nat), member lib (mkc_apply f (mkc_nat k)) mkc_tnat).
Proof.
  introv.
  rw @equality_in_fun.
  split; introv h; repnd; dands; eauto 3 with slow.

  { introv ext; introv.
    apply h; eauto 3 with slow. }

  { introv ext q.
    apply equality_in_tnat in q.
    apply all_in_ex_bar_equality_implies_equality.
    eapply in_open_bar_pres; eauto; clear q; introv xta q.
    unfold equality_of_nat in q; exrepnd.
    eapply equality_respects_cequivc_left;
      [apply implies_ccequivc_ext_apply;
       [apply ccequivc_ext_refl
       |apply ccequivc_ext_sym;
        apply ccomputes_to_valc_ext_implies_ccequivc_ext;
        eauto]|].
    eapply equality_respects_cequivc_right;
      [apply implies_ccequivc_ext_apply;
       [apply ccequivc_ext_refl
       |apply ccequivc_ext_sym;
        apply ccomputes_to_valc_ext_implies_ccequivc_ext;
        eauto]|].
    apply h; eauto 3 with slow. }
Qed.

Hint Rewrite @mkcv_apply_substc : slow.
Hint Rewrite @substc2_apply : slow.

Definition lam_ax {o} := @mkc_lam o nvarx (mkcv_axiom nvarx).

Fixpoint to_list {T} i k (f : nat -> T) : list T :=
  match k with
  | 0 => []
  | S m => f i :: to_list (S i) m f
  end.

Lemma entry_extends_preserves_matching_entries_right_rev {o} :
  forall (e1 e2 e : @library_entry o),
    entry_extends e1 e2
    -> matching_entries e e1
    -> matching_entries e e2.
Proof.
  introv ext m.
  destruct e1, e2; simpl in *; tcsp; repnd; subst; eauto 3 with slow; ginv.
Qed.

Lemma entry_extends_preserves_matching_entries_right_rev2 {o} :
  forall (e1 e2 e : @library_entry o),
    entry_extends e1 e2
    -> matching_entries e e2
    -> matching_entries e e1.
Proof.
  introv ext m.
  destruct e1, e2, e; simpl in *; tcsp; repnd; subst; ginv; eauto 3 with slow.
Qed.

Fixpoint select_with_iseg {A} (n : nat) (iseg : list A) (l : list A) {struct n} : option (list A * A) :=
  match n with
  | 0 => match l with
         | [] => None
         | x :: _ => Some (iseg, x)
         end
  | S m => match l with
           | [] => None
           | x :: t => select_with_iseg m (snoc iseg x) t
           end
  end.

Definition safe_choice_seq_restriction_upto2 {o}
           (name  : choice_sequence_name)
           (vals  : @ChoiceSeqVals o)
           (restr : @ChoiceSeqRestriction o)
           (lib   : @library o) :=
  match restr with
  | csc_res M =>
    forall n v iseg,
      select_with_iseg n [] vals = Some (iseg, v)
      -> exists (Q : nat -> ChoiceSeqVal -> library -> Prop)
                (e : M n v = {l : @library o & Q n v l})
                (p : M n v),
        lib_extends
          (lib_cs name (MkChoiceSeqEntry _ iseg restr) :: lib)
          (projT1 (eq_rect _ (fun n => n) p _ e))
  | _ => True
  end.

Definition safe_choice_sequence_entry_upto2 {o}
           (name : choice_sequence_name)
           (e    : @ChoiceSeqEntry o)
           (lib  : @library o) :=
  match e with
  | MkChoiceSeqEntry _ vals restr =>
    correct_restriction name restr
    /\ choice_sequence_satisfies_restriction vals restr
    /\ safe_choice_seq_restriction_upto2 name vals restr lib
  end.

Definition safe_library_entry_upto2 {o} (e : @library_entry o) (lib : @library o) :=
  match e with
  | lib_cs name restr => safe_choice_sequence_entry_upto2 name restr lib
  | _ => True
  end.

Lemma implies_lib_extends_cons_same {o} :
  forall e1 e2 (lib : @library o),
    safe_library_entry_upto e1 lib
    -> entry_extends e1 e2
    -> lib_extends (e1 :: lib) (e2 :: lib).
Proof.
  introv safee1 ext.
  destruct e1, e2; simpl in *; repnd; subst; tcsp; ginv.
  unfold choice_sequence_entry_extend in *; repnd.
  destruct entry as [vals1 restr1]; simpl in *; repnd.
  destruct entry0 as [vals2 restr2]; simpl in *.
  unfold choice_sequence_vals_extend in *; exrepnd; subst.

  destruct restr1, restr2; simpl in *; GC; repnd; tcsp.

  { induction vals using rev_list_ind; simpl in *; autorewrite with slow; eauto.
    {

Print safe_choice_seq_restriction_upto.

XXXXX
  split; simpl in *.

  - introv i; simpl in *; repndors; repnd; subst; tcsp.
    right; dands; tcsp; eauto 3 with slow.
    intro xx.
    eapply entry_extends_preserves_matching_entries_right_rev in ext; eauto.

  - introv safe1 i; simpl in *; repndors; repnd; subst; tcsp.
    apply safe1; simpl; tcsp.
    right; dands; tcsp.
    introv xx.
    eapply entry_extends_preserves_matching_entries_right_rev2 in ext; eauto.

  - introv i; simpl in *; repndors; subst; tcsp.
    { exists e1; tcsp. }
    exists entry1; dands; tcsp; eauto 3 with slow.
Qed.
Hint Resolve implies_lib_extends_cons_same : slow.

Lemma select_app :
  forall {A} (l1 l2 : list A) (n : nat),
    select n (l1 ++ l2) = if lt_dec n (length l1) then select n l1 else select (n - length l1) l2.
Proof.
  induction n; introv; simpl; destruct l1; simpl in *; tcsp.
  boolvar; try omega; tcsp.
  { rewrite select_app_l; auto; try omega. }
  { rewrite select_app_r; auto; try omega. }
  { rewrite select_app_r; auto; try omega. }
Qed.

Lemma lib_extends_nat_fun_lib_ext {o} {lib} (k : nat) (Flib : @NatFunLibExt o lib) {lib'} (ext : lib_extends lib' lib) :
  lib_extends (Flib k lib' ext) lib.
Proof.
  eauto 3 with slow.
Qed.

Definition lib_extends_LibExt {o}
           {lib' lib : @library o}
           (ext : lib_extends lib' lib)
           (h   : LibExt lib') : LibExt lib :=
  MkLibExt h (lib_extends_trans (lib_ext_ext h) ext).

Definition app2LibExt {o}
           {lib : @library o}
           (F : forall lib' (x : lib_extends lib' lib), LibExt lib')
           (h : LibExt lib) : LibExt lib :=
  lib_extends_LibExt (lib_ext_ext h) (F h (lib_ext_ext h)).

Fixpoint lib_extends_stack {o}
         (k    : nat)
         {lib  : @library o}
         {lib' : library}
         (ext  : lib_extends lib' lib)
         (Flib : NatFunLibExt lib) : LibExt lib :=
  app2LibExt
    (Flib k)
    (match k with
     | 0 => MkLibExt _ ext
     | S m => lib_extends_stack m ext Flib
     end).

Fixpoint old_lib_extends_stack {o}
         (k    : nat)
         (i    : nat)
         {lib  : @library o}
         {lib' : library}
         (ext  : lib_extends lib' lib)
         (Flib : NatFunLibExt lib) : LibExt lib :=
  match k with
  | 0 => lib_extends_LibExt ext (Flib i lib' ext)
  | S m => old_lib_extends_stack m (S i) (lib_extends_nat_fun_lib_ext i Flib ext) Flib
  end.

Fixpoint lib_extends_lib_extends_stack {o}
         (k    : nat)
         {lib  : @library o}
         {lib' : library}
         (ext  : lib_extends lib' lib)
         (Flib : NatFunLibExt lib) : lib_extends (lib_extends_stack k ext Flib) lib' :=
  match k return lib_extends (lib_extends_stack k ext Flib) lib' with
  | 0 => lib_ext_ext (Flib 0 lib' ext)
  | S m => lib_extends_trans
             (lib_ext_ext (Flib (S m) (lib_extends_stack m ext Flib) (lib_ext_ext (lib_extends_stack m ext Flib))))
             (lib_extends_lib_extends_stack m ext Flib)
  end.
Hint Resolve lib_extends_lib_extends_stack : slow.

Lemma select_to_list_some_implies :
  forall n {A} (f : nat -> A) i j v,
    select n (to_list i j f) = Some v
    -> v = f (n + i).
Proof.
  induction n; introv h; simpl in *.
  { destruct j; simpl in *; tcsp; ginv; auto. }
  destruct j; simpl in *; tcsp.
  apply IHn in h; simpl in *.
  rewrite Nat.add_succ_r in h; auto.
Qed.

Lemma implies_lib_extends_cons_diff {o} :
  forall e1 e2 (lib1 lib2 : @library o),
    safe_library_entry e1
    -> entry_extends e1 e2
    -> lib_extends (lib1 ++ e1 :: lib2) (lib1 ++ e2 :: lib2).
Proof.
  introv safee1 ext.
  split; simpl in *.

  - introv i; simpl in *; repndors; repnd; subst; tcsp.
    apply entry_in_library_app_implies in i; repndors; repnd; eauto 3 with slow;[].
    apply implies_entry_in_library_extends_app_right; tcsp.
    { simpl in *; repndors; repnd; subst; tcsp; eauto 3 with slow;[].
      right; dands; tcsp; eauto 3 with slow.
      intro xx.
      eapply entry_extends_preserves_matching_entries_right_rev in ext; eauto. }
    introv j; apply i; apply LIn_implies_In; auto.

  - introv safe1 i; simpl in *; repndors; repnd; subst; tcsp.
    apply entry_in_library_app_implies in i; repndors; repnd; eauto 3 with slow;[].
    simpl in *; repndors; repnd; subst; tcsp;[].
    apply safe1; simpl; tcsp.
    apply implies_entry_in_library_app_right; tcsp; simpl; tcsp.
    { right; dands; tcsp.
      introv xx.
      eapply entry_extends_preserves_matching_entries_right_rev2 in ext; eauto. }
    introv j; apply i; apply LIn_implies_In; auto.

  - introv i; simpl in *; repndors; subst; tcsp.
    apply List.in_app_iff in i; simpl in *; repndors; subst; tcsp; eauto.
    { exists entry1; rewrite List.in_app_iff; simpl; dands; tcsp; eauto 3 with slow. }
    { exists e1; tcsp; rewrite List.in_app_iff; simpl; dands; tcsp; eauto 3 with slow. }
    { exists entry1; rewrite List.in_app_iff; simpl; dands; tcsp; eauto 3 with slow. }
Qed.
Hint Resolve implies_lib_extends_cons_diff : slow.

Lemma lib_ext_lib_lib_extends_LibExt {o} :
  forall {lib lib'} (ext : lib_extends lib' lib) (x : @LibExt o lib'),
    lib_ext_lib (lib_extends_LibExt ext x) = x.
Proof.
  introv; destruct x; simpl; auto.
Qed.
Hint Rewrite @lib_ext_lib_lib_extends_LibExt : slow.

Lemma extend_lib_cs_res {o} :
  forall k (F : nat -> ChoiceSeqVal) (lib : @library o) name vals typ,
    correct_restriction name (csc_res typ)
    -> (forall n v, select n vals = Some v -> typ n v)
    -> (forall n, length vals <= n -> typ n (F n))
    -> find_cs lib name = Some (MkChoiceSeqEntry _ vals (csc_res typ))
    -> exists lib' lib1 lib2,
        lib_extends lib' lib
        /\ find_cs lib' name = Some (MkChoiceSeqEntry _ (vals ++ to_list (length vals) (k - length vals) F) (csc_res typ))
        /\ lib = lib1 ++ lib_cs name (MkChoiceSeqEntry _ vals (csc_res typ)) :: lib2
        /\ lib' = lib1 ++ lib_cs name (MkChoiceSeqEntry _ (vals ++ to_list (length vals) (k - length vals) F) (csc_res typ)) :: lib2.
Proof.
  induction lib; introv cor sel typf h; simpl in *; tcsp.
  destruct a; simpl in *; tcsp; boolvar; subst; tcsp; ginv; GC.

  { exists (lib_cs name0 (MkChoiceSeqEntry _ (vals ++ to_list (length vals) (k - length vals) F) (csc_res typ)) :: lib)
           ([] : @library o)
           lib.
    simpl; boolvar; tcsp.
    dands; tcsp; eauto 3 with slow;[].
    apply implies_lib_extends_cons_same; simpl; dands; eauto 3 with slow.

    { unfold safe_library_entry; simpl; dands; tcsp.
      introv xx.
      rewrite select_app in xx; boolvar.
      { apply sel; auto. }
      applydup select_to_list_some_implies in xx; subst.
      apply Nat.nlt_ge in n0.
      rewrite Nat.sub_add; auto. }

    { unfold choice_sequence_entry_extend; simpl; dands; tcsp.
      unfold choice_sequence_vals_extend; eexists; eauto. } }

  { apply IHlib in h; auto.
    exrepnd.
    exists (lib_cs name0 entry :: lib') (lib_cs name0 entry :: lib1) lib2.
    simpl; boolvar; tcsp; GC;[].
    dands; tcsp; try congruence;[].
    subst; simpl.
    repeat rewrite (app_comm_cons _ _ (lib_cs name0 entry)).
    apply implies_lib_extends_cons_diff; simpl; dands; eauto 3 with slow;[|].

    { unfold safe_library_entry; simpl; dands; tcsp.
      introv xx.
      rewrite select_app in xx; boolvar.
      { apply sel; auto. }
      applydup select_to_list_some_implies in xx; subst.
      apply Nat.nlt_ge in n1.
      rewrite Nat.sub_add; auto. }

    { unfold choice_sequence_entry_extend; simpl; dands; tcsp.
      unfold choice_sequence_vals_extend; eexists; eauto. } }

  { apply IHlib in h; auto.
    exrepnd.
    exists (lib_abs opabs vars rhs correct :: lib') (lib_abs opabs vars rhs correct :: lib1) lib2.
    simpl; tcsp; GC;[].
    dands; tcsp; try congruence;[].
    subst; simpl.
    repeat rewrite (app_comm_cons _ _ (lib_abs opabs vars rhs correct)).
    apply implies_lib_extends_cons_diff; simpl; dands; eauto 3 with slow;[|].

    { unfold safe_library_entry; simpl; dands; tcsp.
      introv xx.
      rewrite select_app in xx; boolvar.
      { apply sel; auto. }
      applydup select_to_list_some_implies in xx; subst.
      apply Nat.nlt_ge in n0.
      rewrite Nat.sub_add; auto. }

    { unfold choice_sequence_entry_extend; simpl; dands; tcsp.
      unfold choice_sequence_vals_extend; eexists; eauto. } }
Qed.

Lemma implies_select_to_list_some :
  forall n {A} (f : nat -> A) i j,
    n < j
    -> select n (to_list i j f) = Some (f (n + i)).
Proof.
  induction n; introv h; simpl in *.
  { destruct j; simpl in *; tcsp; ginv; auto. }
  destruct j; simpl in *; tcsp.
  rewrite IHn; try omega.
  rewrite Nat.add_succ_r; auto.
Qed.




Definition mk_cs_res_entry {o}
           {lib  : @library o}
           {Flib : NatFunLibExt lib}
           (Fnat : NatFunLibExtNat Flib) : @ChoiceSeqEntry o :=
  MkChoiceSeqEntry
    o
    []
    (csc_res
       (fun i t =>
          exists (lib1 : library)
                 (ext1 : lib_extends lib1 lib)
                 (lib2 : library)
                 (ext2 : lib_extends lib2 (Flib i lib1 ext1))
                 (extz : lib_extends lib2 lib),
            t = mkc_nat (Fnat i lib1 ext1 lib2 ext2 extz))).

Definition mk_cs_res {o}
           (name : choice_sequence_name)
           {lib  : @library o}
           {Flib : NatFunLibExt lib}
           (Fnat : NatFunLibExtNat Flib) : library_entry :=
  lib_cs name (mk_cs_res_entry Fnat).

Lemma safe_library_entry_mk_cs_ren {o} :
  forall (name : choice_sequence_name)
         {lib  : @library o}
         {Flib : NatFunLibExt lib}
         (Fnat : NatFunLibExtNat Flib),
    csn_kind name = cs_kind_nat 2
    -> safe_library_entry (mk_cs_res name Fnat).
Proof.
  introv eqk.
  unfold safe_library_entry; simpl.
  unfold correct_restriction; simpl.
  allrw; simpl; dands; auto.
  introv h; autorewrite with list in *; ginv.
Qed.
Hint Resolve safe_library_entry_mk_cs_ren : slow.

Lemma find_cs_none_implies_non_shadowed_entry_mk_cs_res {o} :
  forall (name : choice_sequence_name)
         {lib  : @library o}
         {Flib : NatFunLibExt lib}
         (Fnat : NatFunLibExtNat Flib)
         (lib' : library),
    find_cs lib' name = None
    -> non_shadowed_entry (mk_cs_res name Fnat) lib'.
Proof.
  introv h.
  unfold non_shadowed_entry.
  apply forallb_forall; introv i.
  eapply find_cs_none_implies_diff_entry_names; eauto.
Qed.
Hint Resolve find_cs_none_implies_non_shadowed_entry_mk_cs_res : slow.

Lemma ext_lib_extends_stack_implies_ex_nat {o} :
  forall (name : choice_sequence_name)
         {lib  : @library o}
         (safe : safe_library lib)
         {Flib : NatFunLibExt lib}
         (Fnat : NatFunLibExtNat Flib)
         (k    : nat)
         (k'   : nat)
         (ltk  : k < k')
         (lib1 : library)
         (ext1 : lib_extends lib1 lib)
         (ext' : lib_extends lib1 (mk_cs_res name Fnat :: lib))
         (lib2 : library)
         (ext2 : lib_extends lib2 (lib_extends_stack k' ext1 Flib)),
  exists (lib3 : library) i,
    lib_extends lib3 lib2
    /\ find_cs_value_at lib3 name k = Some (mkc_nat i)
    /\ exists (liba : library) (exta : lib_extends liba lib)
              (libb : library) (extb : lib_extends libb (Flib k liba exta))
              (extz : lib_extends libb lib),
        i = Fnat k liba exta libb extb extz.
Proof.
  introv safe ltk ext' ext2.

  pose proof (lib_extends_preserves_find_cs
                (mk_cs_res name Fnat :: lib)
                lib2
                name
                (mk_cs_res_entry Fnat)) as q.
  simpl in q; boolvar; tcsp;[]; GC.
  repeat (autodimp q hyp); eauto 3 with slow;[].
  exrepnd.
  destruct entry2 as [vals restr]; simpl in *.
  unfold same_restrictions in q2.
  destruct restr; tcsp.

  assert (lib_extends lib2 lib) as ext by eauto 3 with slow.
  assert (safe_library lib2) as safe2 by eauto 3 with slow.

  remember (fun n => match n with
                     | 0 =>
                       Fnat
                         0
                         lib1
                         ext1
                         (Flib 0 lib1 ext1)
                         (lib_extends_refl _)
                         (lib_extends_trans (lib_ext_ext (Flib 0 lib1 ext1)) ext1)
                     | S m =>
                       Fnat
                         (S m)
                         (lib_extends_stack m ext1 Flib)
                         (lib_ext_ext (lib_extends_stack m ext1 Flib))
                         (Flib (S m)
                               (lib_extends_stack m ext1 Flib)
                               (lib_ext_ext (lib_extends_stack m ext1 Flib)))
                         (lib_extends_refl _)
                         (lib_ext_ext (lib_extends_stack (S m) ext1 Flib))
                     end) as f.

  assert (correct_restriction name (csc_res typ)) as cor.
  { apply find_cs_some_implies_entry_in_library in q1.
    apply safe2 in q1; simpl in *; tcsp. }

  assert (forall (n : nat) (v : CTerm), select n vals = Some v -> typ n v) as sel.
  { apply find_cs_some_implies_entry_in_library in q1.
    apply safe2 in q1; simpl in *; repnd; tcsp. }

  assert (forall n : nat, length vals <= n -> typ n (mkc_nat (f n))) as typf.
  { introv len.
    apply q2.
    subst f.
    destruct n; repeat eexists. }

  apply (extend_lib_cs_res k' (fun n => mkc_nat (f n))) in q1; auto.

  exrepnd.
  exists lib'.
  unfold find_cs_value_at; rewrite q4; simpl.
  rewrite find_value_of_cs_at_is_select.
  destruct (lt_dec k (length vals)) as [d|d].

  { applydup @select_lt_length in d; exrepnd.
    applydup sel in d1.
    apply q2 in d0; exrepnd; subst a.
    exists (Fnat k lib4 ext0 lib5 ext3 extz).
    dands; auto.
    { rewrite select_app_l; auto. }
    { repeat eexists. } }

  { apply Nat.nlt_ge in d.
    exists (f k); dands; auto.
    { rewrite select_app_r; auto;try omega;[].
      rewrite implies_select_to_list_some; try omega;
        [|apply Nat.lt_add_lt_sub_r; rewrite Nat.sub_add; auto];[].
      rewrite Nat.sub_add; auto. }
    { subst; destruct k; simpl; repeat eexists. } }
Qed.

Lemma mk_cs_ren_in_nat2nat {o} :
  forall (name : choice_sequence_name)
         {lib  : @library o}
         {Flib : NatFunLibExt lib}
         (Fnat : NatFunLibExtNat Flib)
         (lib' : library),
    safe_library lib
    -> find_cs lib name = None
    -> csn_kind name = cs_kind_nat 2
    -> lib_extends lib' (mk_cs_res name Fnat :: lib)
    -> member lib' (mkc_choice_seq name) nat2nat.
Proof.
  introv safe fnd eqk ext.
  apply member_nat2nat.
  introv xta; introv.
  apply member_tnat_iff.

  assert (lib_extends (mk_cs_res name Fnat :: lib) lib) as xtb.
  { apply implies_lib_extends_cons_left; eauto 3 with slow. }

  apply collapse_all_in_ex_bar.
  introv xtc.
  assert (lib_extends lib'1 lib) as xtd by eauto 4 with slow.
  assert (lib_extends lib'1 lib') as xte by eauto 4 with slow.

  exists (lib_extends_stack (S k) xtd Flib) (lib_extends_lib_extends_stack (S k) xtd Flib).
  introv xtf xtg.

  assert (lib_extends lib'1 (mk_cs_res name Fnat :: lib)) as xth by eauto 3 with slow.
  assert (lib_extends lib'3 (lib_extends_stack (S k) xtd Flib)) as xti by eauto 3 with slow.

  pose proof (ext_lib_extends_stack_implies_ex_nat name safe Fnat k (S k)) as q.
  autodimp q hyp;[].
  pose proof (q lib'1 xtd xth lib'3 xti) as q.
  exrepnd.
  exists lib3 q0.
  introv xtj.
  exists i.

  apply (implies_ccomputes_to_valc_ext_apply_cs lib3 lib'4 name (mkc_nat k) k i); eauto 3 with slow.
Qed.

Lemma mkc_apply_lam_ax_comp_ax {o} :
  forall (lib : @library o) a,
    (mkc_apply lam_ax a) ===b>(lib) mkc_axiom.
Proof.
  introv.
  apply in_ext_implies_in_open_bar; introv xta xtb.
  exists (@mkc_axiom o); dands; spcast; eauto 3 with slow.
  apply computes_to_valc_iff_reduces_toc; dands; eauto 3 with slow.
  destruct_cterms; unfold reduces_toc; simpl.
  apply reduces_to_if_step; tcsp.
Qed.
Hint Resolve mkc_apply_lam_ax_comp_ax : slow.


(*

   forall m : nat, squash (exists n : nat, P(m,n))

   implies

   squash (exists f : nat -> nat, forall m : nat, squash (P (m, f m)))

 *)
Lemma axiom_of_choice_00 {o} :
  forall lib f m n (P : @CTerm o),
    n <> m
    -> f <> m
    -> safe_library lib
    -> (forall a b,
          member lib a mkc_tnat
          -> member lib b mkc_tnat
          -> type lib (mkc_apply2 P a b))
    -> inhabited_type
         lib
         (mkc_forall
            mkc_tnat
            m
            (mkcv_squash
               [m]
               (mkcv_exists
                  [m]
                  (mkcv_tnat [m])
                  n
                  (mkcv_apply2 [n,m]
                               (mk_cv [n,m] P)
                               (mk_cv_app_l [n] [m] (mkc_var m))
                               (mk_cv_app_r [m] [n] (mkc_var n))))))
    -> inhabited_type_bar
         lib
         (mkc_exists
            nat2nat
            f
            (mkcv_forall
               [f]
               (mk_cv [f] mkc_tnat)
               m
               (mkcv_squash
                  [m,f]
                  (mkcv_apply2 [m,f]
                               (mk_cv [m,f] P)
                               (mk_cv_app_r [f] [m] (mkc_var m))
                               (mkcv_apply [m,f]
                                           (mk_cv_app_l [m] [f] (mkc_var f))
                                           (mk_cv_app_r [f] [m] (mkc_var m))))))).
Proof.
  introv d1 d2 safe impp inh.

  unfold mkc_forall in inh.
  apply inhabited_function in inh.
  repnd.
  clear inh0 inh1.
  exrepnd.

  assert (forall k : CTerm,
            member lib k mkc_tnat
            -> inhabited_type_bar
                 lib
                 (mkc_exists
                    mkc_tnat
                    n
                    (mkcv_apply2
                       [n]
                       (mk_cv [n] P)
                       (mk_cv [n] k)
                       (mkc_var n)))) as q.
  { introv mem.
    pose proof (inh0 _ (lib_extends_refl _) k k) as h.
    autodimp h hyp.
    allrw @substc_mkcv_squash.
    rw @equality_in_mkc_squash in h.
    repnd.
    rw @mkcv_exists_substc in h; auto.
    allrw @mkcv_tnat_substc.
    allrw @substc2_apply2.
    allrw @substc2_mk_cv_app_l.
    rw @substc2_mk_cv_app_r in h; auto.
    allrw @substc2_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear inh0.

  introv ext.

  assert (forall (k : nat),
             in_open_bar
               lib'
               (fun lib =>
                  exists (j : nat),
                    inhabited_type lib (mkc_apply2 P (mkc_nat k) (mkc_nat j)))) as xx.
  {
    introv.
    pose proof (q (mkc_nat k)) as q; autodimp q hyp; eauto 3 with slow;[].
    eapply lib_extends_preserves_inhabited_type_bar in q; eauto.
    clear dependent lib.
    apply collapse_all_in_ex_bar.
    eapply in_open_bar_pres; eauto; clear q; introv ext q.
    apply inhabited_exists in q; repnd; exrepnd.
    apply collapse_all_in_ex_bar.
    eapply in_open_bar_pres; try exact q2; clear q2; introv xta q2; exrepnd.
    apply member_tnat_iff in q4.
    eapply in_open_bar_pres; try exact q4; clear q4; introv xtb q4; exrepnd.
    exists k0.
    autorewrite with slow in *; eauto 3 with slow.
    eapply member_monotone in q2; eauto.
    eapply member_respects_cequivc_type in q2;
      [|apply implies_ccequivc_ext_apply2;
        [apply ccequivc_ext_refl|apply ccequivc_ext_refl|];
        apply ccomputes_to_valc_ext_implies_ccequivc_ext; eauto].
    eauto 2 with slow.
  }

(*
  assert (forall (k : nat),
             at_open_bar
               lib'
               (fun lib =>
                  exists (j : nat),
                    inhabited_type lib (mkc_apply2 P (mkc_nat k) (mkc_nat j)))) as yy.
  { introv; apply in_open_bar_implies_at_open_bar; eauto. }
  unfold at_open_bar in yy.

  assert (forall (k : nat),
             exists (j     : nat)
                    (lib'' : library)
                    (ext   : lib_extends lib'' lib'),
               inhabited_type lib'' (mkc_apply2 P (mkc_nat k) (mkc_nat j))) as zz.
  { introv; pose proof (yy k _ (lib_extends_refl _)) as h; exrepnd; eauto. }
*)

  apply @nat_in_open_bar_choice in xx; exrepnd.
  apply nat_in_open_bar_choice_nat in xx0; exrepnd.


  pose proof (fresh_choice_seq_name_in_library_with_kind lib' (cs_kind_nat 2)) as w; exrepnd.

  (* WARNING *)
  exists (mk_cs_res name Fnat :: lib').

  assert (lib_extends (mk_cs_res name Fnat :: lib') lib') as xta.
  { apply implies_lib_extends_cons_left; eauto 3 with slow. }
  exists xta.

  introv xtb.
  apply inhabited_exists; dands; eauto 3 with slow.
  { admit. }

  exists (@mkc_pair o (mkc_choice_seq name) lam_ax).
  apply in_ext_implies_in_open_bar; introv xtc.
  exists (@mkc_choice_seq o name) (@lam_ax o).
  dands; eauto 3 with slow.

  { apply (mk_cs_ren_in_nat2nat name Fnat); auto; eauto 3 with slow. }

  unfold mkcv_forall.
  repeat (rw @substc_mkcv_function; auto).
  autorewrite with slow.
  apply equality_in_function3; dands; eauto 3 with slow;[].

  introv xtd eqn.
  dands.

  { admit. }

  allrw @substcv_as_substc2.
  autorewrite with slow.
  repeat (rewrite substc2_mk_cv_app_r; tcsp;[]).
  autorewrite with slow.
  apply equality_in_tnat in eqn; apply e_all_in_ex_bar_as in eqn.
  apply all_in_ex_bar_equality_implies_equality.
  eapply in_open_bar_pres; try exact eqn; clear eqn; introv xte eqn.
  unfold equality_of_nat in eqn; exrepnd.
  rename n0 into k.
  apply equality_in_mkc_squash.
  dands; eauto 3 with slow;[].

  pose proof (xx1 k) as xx1.

(* XX *)
  apply collapse_all_in_ex_bar.
  introv xtf.
  assert (lib_extends lib'4 lib') as xtg by eauto 6 with slow.
  assert (safe_library lib') as safe' by eauto 3 with slow.
  assert (lib_extends (lib_extends_stack (S k) xtg Flib) lib'4) as xth by eauto 3 with slow.
  exists (lib_extends_stack (S k) xtg Flib) xth.
  assert (lib_extends lib'4 (mk_cs_res name Fnat :: lib')) as xti by eauto 5 with slow.
  introv xtj xtk.

  pose proof (ext_lib_extends_stack_implies_ex_nat name safe' Fnat k (S k)) as z.
  autodimp z hyp.
  pose proof (z lib'4 xtg xti lib'6 (lib_extends_trans xtk xtj)) as z.
  exrepnd.

  pose proof (xx1 liba exta libb extb extz) as xx1; simpl in xx1.



(* XX *)
(* First, we need to extend [lib'4] so that we have [S(k)] choices *)
(* expand [ext_lib_extends_stack_implies_ex_nat], so that we get a characterization
   of [i] in terms of [name]'s restriction *)


  pose proof (xx1 _ xtg) as xx1; simpl in xx1.
  assert (lib_extends (Flib k lib'4 xtg) lib'4) as xth by eauto 3 with slow.
  (* We have to get [S(k)] choices *)
  exists (Flib k lib'4 xtg) xth.
  introv xti.
  assert (lib_extends lib'5 lib') as xtj by eauto 3 with slow.
  pose proof (xx1 _ xti xtj) as xx1; simpl in xx1.

XXXXXXXXXX

  assert (forall k : CTerm,
            member lib k mkc_tnat
            -> {j : CTerm
                , member lib j mkc_tnat
                # inhabited_type_bar lib (mkc_apply2 P k j)}) as h.
  { introv mem.
    apply q in mem; clear q.
    apply inhabited_exists in mem; repnd.
    clear mem0 mem1.
    exrepnd.
    exists a; dands; auto.
    allrw @mkcv_apply2_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear q.

  (* First use FunctionalChoice_on to get an existential (a Coq function from terms to terms) *)

  pose proof (FunctionalChoice_on
                {k : CTerm & member lib k mkc_tnat}
                (@CTerm o)
                (fun k j => member lib j mkc_tnat # inhabited_type lib (mkc_apply2 P (projT1 k) j)))
    as fc.
  simphyps.
  autodimp fc hyp; tcsp;[].
  exrepnd.
  clear h.
  rename fc0 into fc.

  assert {c : nat -> nat
          & forall a : CTerm,
              member lib a mkc_tnat
              -> (member lib (mkc_eapply (mkc_nseq c) a) mkc_tnat
                  # inhabited_type lib (mkc_apply2 P a (mkc_eapply (mkc_nseq c) a)))} as fs.
  { exists (fun n =>
              match member_tnat_implies_computes
                      lib
                      (f1 (existT _ (mkc_nat n) (nat_in_nat lib n)))
                      (fst (fc (existT _ (mkc_nat n) (nat_in_nat lib n)))) with
                | existT _ k _ => k
              end).
    introv mem.
    dands.

    - apply member_tnat_iff in mem; exrepnd.
      allrw @computes_to_valc_iff_reduces_toc; repnd.
      eapply member_respects_reduces_toc;[apply reduces_toc_eapply_nseq;exact mem1|].

      remember (member_tnat_implies_computes
                  lib
                  (f1 exI(mkc_nat k, nat_in_nat lib k))
                  (fst (fc exI(mkc_nat k, nat_in_nat lib k)))) as mt.
      exrepnd.

      apply (member_respects_reduces_toc _ _ (mkc_nat k0)).

      + unfold reduces_toc; simpl.
        apply reduces_to_if_step.
        csunf; allsimpl; dcwf h; simpl.
        boolvar; try omega.
        rw @Znat.Nat2Z.id.
        rewrite <- Heqmt; auto.

      + apply member_tnat_iff.
        exists k0.
        apply computes_to_valc_refl; eauto 3 with slow.

    - apply member_tnat_iff in mem; exrepnd.
      pose proof (nat_in_nat lib k) as mk.

      remember (member_tnat_implies_computes
                  lib
                  (f1 exI(mkc_nat k, nat_in_nat lib k))
                  (fst (fc exI(mkc_nat k, nat_in_nat lib k)))) as q.
      exrepnd.
      remember (fc exI(mkc_nat k, nat_in_nat lib k)) as fck.
      exrepnd.
      allsimpl.

      allunfold @inhabited_type; exrepnd.
      exists t.
      allsimpl.

      eapply member_respects_cequivc_type;[|exact fck1].
      apply implies_cequivc_apply2; auto.

      + apply cequivc_sym.
        apply computes_to_valc_implies_cequivc; auto.

      + apply cequivc_sym.
        allrw @computes_to_valc_iff_reduces_toc; repnd.
        eapply cequivc_trans;
          [apply reduces_toc_implies_cequivc;
            apply reduces_toc_eapply_nseq;exact mem1
          |].

        eapply cequivc_trans;
          [|apply cequivc_sym;
             apply computes_to_valc_implies_cequivc;
             exact q0].
        apply reduces_toc_implies_cequivc.
        unfold reduces_toc; simpl.
        apply reduces_to_if_step.
        csunf; simpl; dcwf h; simpl.
        boolvar; try omega.
        allrw @Znat.Nat2Z.id.
        allsimpl.
        rw <- Heqfck; simpl.
        rw <- Heqq; auto.
  }
  clear f1 fc.
  exrepnd.

  (* then "convert" the Coq function into a Nuprl function *)

  apply inhabited_product.

  dands.

  { apply type_nat2nat. }

  { introv eqf.
    unfold mkcv_forall.
    repeat (rw @substc_mkcv_function; auto).
    allrw @csubst_mk_cv.
    apply tequality_function.
    dands.
    { apply tnat_type. }

    introv eqn.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc_mkcv_squash.
    allrw @mkcv_apply2_substc.
    allrw @substc2_mk_cv.
    allrw @csubst_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @substc2_apply.
    repeat (rw @substc2_mk_cv_app_l; auto).
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv.

    apply tequality_mkc_squash.
    apply type_respects_cequivc_left.

    { apply implies_cequivc_apply2; auto.
      { apply equality_int_nat_implies_cequivc; auto.
        apply equality_sym; auto. }
      { eapply equality_nat2nat_apply in eqf;[|exact eqn].
        apply equality_int_nat_implies_cequivc; auto.
        apply equality_sym; auto. }
    }

    { apply impp; eauto 3 with slow.
      { apply equality_sym in eqn; apply equality_refl in eqn; auto. }
      { eapply equality_nat2nat_apply in eqf;[|exact eqn].
        apply equality_sym in eqf; apply equality_refl in eqf; auto. }
    }
  }

  { exists (@mkc_nseq o c).
    unfold mkcv_forall.
    repeat (rw @substc_mkcv_function; auto).
    allrw @csubst_mk_cv.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc2_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @substc2_apply.
    repeat (rw @substc2_mk_cv_app_l; auto).
    repeat (rw @substc2_mk_cv_app_r; auto).
    allrw @mkc_var_substc.

    dands.

    { apply member_nseq_nat2nat. }

    { apply inhabited_function; dands; eauto 3 with slow.

      - introv eqn.
        allrw @substc_mkcv_squash.
        allrw @mkcv_apply2_substc.
        allrw @mkcv_apply_substc.
        allrw @csubst_mk_cv.
        allrw @mkc_var_substc.

        apply tequality_mkc_squash.
        apply type_respects_cequivc_left.

        { apply implies_cequivc_apply2; auto.
          { apply equality_int_nat_implies_cequivc; auto.
            apply equality_sym; auto. }
          { apply implies_cequivc_apply; auto.
            apply equality_int_nat_implies_cequivc; auto.
            apply equality_sym; auto. }
        }

        { apply impp; eauto 3 with slow.
          { apply equality_sym in eqn; apply equality_refl in eqn; auto. }
          { pose proof (member_nseq_nat2nat lib c) as eqf.
            eapply equality_nat2nat_apply in eqf;[|exact eqn].
            apply equality_sym in eqf; apply equality_refl in eqf; auto. }
        }

      - exists (@mkc_lam o nvarx (mkcv_axiom nvarx)).
        introv eqn.
        allrw @substc_mkcv_squash.
        allrw @mkcv_apply2_substc.
        allrw @mkcv_apply_substc.
        allrw @csubst_mk_cv.
        allrw @mkc_var_substc.

        applydup @equality_int_nat_implies_cequivc in eqn.
        apply equality_refl in eqn.
        eapply equality_respects_cequivc_right;
          [apply implies_cequivc_apply;
            [apply cequivc_refl
            |exact eqn0]
          |].
        rw @member_eq.

        eapply member_respects_cequivc;
          [apply cequivc_sym;
            apply cequivc_beta
          |].
        rw @substc_mkcv_axiom.

        apply equality_in_mkc_squash; dands; spcast;
        try (apply computes_to_valc_refl; eauto 3 with slow).

        pose proof (fs0 a eqn) as q; repnd.

        eapply inhabited_type_cequivc;[|exact q].
        apply implies_cequivc_apply2; auto.
        apply cequivc_sym.
        apply reduces_toc_implies_cequivc.
        destruct_cterms.
        unfold reduces_toc; simpl.
        apply reduces_to_if_step; csunf; simpl; auto.
    }
  }
Qed.
*)


Definition rule_AC00 {o}
           (P e : @NTerm o)
           (f m n : NVar)
           (H : barehypotheses)
           (i : nat) :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_squash (mk_exists (mk_nat2nat) f (mk_forall mk_tnat n (mk_squash (mk_apply2 P (mk_var n) (mk_apply (mk_var f) (mk_var n)))))))))
      [ mk_baresequent H (mk_concl (mk_forall mk_tnat n (mk_squash (mk_exists mk_tnat m (mk_apply2 P (mk_var n) (mk_var m))))) e),
        mk_baresequent H (mk_conclax (mk_member P (mk_fun mk_tnat (mk_fun mk_tnat (mk_uni i))))) ]
      [].

Lemma rule_AC00_true {p} :
  forall lib
         (P e : NTerm)
         (f m n : NVar)
         (H : @barehypotheses p)
         (i : nat)
         (d1 : n <> m)
         (d2 : f <> n)
         (d3 : !LIn f (free_vars P))
         (d4 : !LIn m (free_vars P))
         (d5 : !LIn n (free_vars P)),
    rule_true lib (rule_AC00 P e f m n H i).
Proof.
  unfold rule_AC00, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  rename Hyp0 into hyp2.
  destruct hyp2 as [wc2 hyp2].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  exists (@covered_axiom p (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 _ ext s1 s2 eqh sim) as hh; exrepnd; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 _ ext s1 s2 eqh sim) as qq; exrepnd; clear hyp2.

  allunfold @mk_forall.
  allunfold @mk_exists.
  allunfold @mk_nat2nat.

  lsubst_tac.
  allapply @member_if_inhabited.
  apply tequality_mkc_member_implies_sp in qq0; auto;[].
  allrw @tequality_mkc_member_sp; repnd.

  lsubst_tac.
  allrw @lsubstc_mkc_tnat.

  dands.

  - apply tequality_mkc_squash.

    eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        apply lsubstc_mk_nat2nat
      |].
    eapply tequality_respects_alphaeqc_right;
      [apply alphaeqc_mkc_product1;
        apply alphaeqc_sym;
        apply lsubstc_mk_nat2nat
      |].
    apply tequality_product; dands.
    { apply type_nat2nat. }

    introv ext' eqf.
    repeat lsubstc_vars_as_mkcv.
    repeat (rw @substc_mkcv_function; auto;[]).
    autorewrite with slow.
    allrw @substcv_as_substc2.
    allrw @substc2_squash.
    allrw @substc2_apply2.
    allrw @substc2_apply.
    allrw @substc2_mk_cv.
    repeat (rw @substc2_mk_cv_app_r; auto;[]).
    repeat (rw @substc2_mk_cv_app_l; auto;[]).
    allrw @mkc_var_substc.

    apply tequality_function; dands; eauto 3 with slow.
    { apply tnat_type. }

    introv ext'' eqn.
    allrw @substc_mkcv_squash.
    allrw @mkcv_apply2_substc.
    allrw @mkcv_apply_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.

    apply tequality_mkc_squash.
    apply equality_in_fun in qq0; repnd.
    applydup qq0 in eqn; eauto 3 with slow;[].
    lsubst_tac.
    apply equality_in_fun in eqn0; repnd.
    pose proof (eqn0 _ (lib_extends_refl _) (mkc_apply a a0) (mkc_apply a' a'0)) as q.
    allrw @lsubstc_mkc_tnat.
    autodimp q hyp.
    { apply equality_nat2nat_apply; eauto 3 with slow. }
    allrw <- @mkc_apply2_eq.
    apply equality_in_uni in q; auto.

  - apply equality_in_mkc_squash; dands; spcast; eauto 3 with slow.

    SearchAbout equality mkc_squash.

    pose proof (axiom_of_choice_00 lib f n m (lsubstc P wt s1 ct1)) as ac.
    repeat (autodimp ac hyp).

    + (* from qq1 *)
      introv m1 m2.
      apply equality_in_fun in qq1; repnd.
      pose proof (qq1 a a) as h.
      autodimp h hyp.
      lsubst_tac.
      allrw @lsubstc_mkc_tnat.
      apply equality_in_fun in h; repnd.
      pose proof (h b b) as q.
      autodimp q hyp.
      apply equality_in_uni in q; auto.
      allrw <- @mkc_apply2_eq; auto.

    + (* from hh1 *)
      apply equality_refl in hh1.
      exists (lsubstc e wfce1 s1 pt0).

      repeat lsubstc_vars_as_mkcv.
      auto.

    + repeat lsubstc_vars_as_mkcv.

      dands;
        [|allunfold @mkc_exists; allunfold @mkcv_forall;
          eapply inhabited_type_respects_alphaeqc;[|exact ac];
          apply alphaeqc_mkc_product1;
          apply alphaeqc_sym; apply lsubstc_mk_nat2nat].
Qed.


(*

   forall f : nat -> nat, squash exists n : nat, P(f,n)

   implies

   squash exists F : (nat -> nat) -> nat, forall f : nat -> nat, P (f, F f)

 *)
Lemma axiom_of_choice_10 {o} :
  forall lib F f n (P : @CTerm o),
    n <> f
    -> inhabited_type
         lib
         (mkc_forall
            nat2nat
            f
            (mkcv_squash
               [f]
               (mkcv_exists
                  [f]
                  (mkcv_tnat [f])
                  n
                  (mkcv_apply2 [n,f]
                               (mk_cv [n,f] P)
                               (mk_cv_app_l [n] [f] (mkc_var f))
                               (mk_cv_app_r [f] [n] (mkc_var n))))))
    -> inhabited_type
         lib
         (mkc_squash
            (mkc_exists
               (mkc_fun nat2nat mkc_tnat)
               F
               (mkcv_forall
                  [F]
                  (mk_cv [F] nat2nat)
                  f
                  (mkcv_apply2 [f,F]
                               (mk_cv [f,F] P)
                               (mk_cv_app_r [F] [f] (mkc_var f))
                               (mkcv_apply [f,F]
                                           (mk_cv_app_l [f] [F] (mkc_var F))
                                           (mk_cv_app_r [F] [f] (mkc_var f))))))).
Proof.
  introv d1 inh.
  apply inhabited_squash.

  unfold mkc_forall in inh.
  apply inhabited_function in inh.
  repnd.
  clear inh0 inh1.
  exrepnd.

  assert (forall f : CTerm,
            member lib f nat2nat
            -> inhabited_type
                 lib
                 (mkc_exists
                    mkc_tnat
                    n
                    (mkcv_apply2
                       [n]
                       (mk_cv [n] P)
                       (mk_cv [n] f)
                       (mkc_var n)))) as q.
  { introv mem.
    pose proof (inh0 f1 f1) as h.
    autodimp h hyp.
    allrw @substc_mkcv_squash.
    rw @equality_in_mkc_squash in h.
    repnd.
    rw @mkcv_exists_substc in h; auto.
    allrw @mkcv_tnat_substc.
    allrw @substc2_apply2.
    allrw @substc2_mk_cv_app_l.
    rw @substc2_mk_cv_app_r in h; auto.
    allrw @substc2_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear inh0.

  assert (forall f : CTerm,
            member lib f nat2nat
            -> {k : CTerm
                , member lib k mkc_tnat
                # inhabited_type lib (mkc_apply2 P f k)}) as h.
  { introv mem.
    apply q in mem; clear q.
    apply inhabited_exists in mem; repnd.
    clear mem0 mem1.
    exrepnd.
    exists a; dands; auto.
    allrw @mkcv_apply2_substc.
    allrw @csubst_mk_cv.
    allrw @mkc_var_substc.
    auto.
  }
  clear q.

Abort.
