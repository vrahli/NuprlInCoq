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


Require Export nuprl_props.


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
    exists n; eauto 3 with slow.

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

Lemma implies_computes_to_valc_seq_bar_raise_bar {o} :
  forall {lib lib'} (bar : @BarLib o lib) (ext : lib_extends lib' lib) t v,
    t ==b==>(bar) v
    -> t ==b==>(raise_bar bar ext) v.
Proof.
  introv comp br e.
  simpl in *; exrepnd.
  apply (comp lib1 br1); eauto 3 with slow.
Qed.
Hint Resolve implies_computes_to_valc_seq_bar_raise_bar : slow.

Lemma per_int_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_int_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_int_bar ts lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_int_bar in *; exrepnd.
  exists (equality_of_int_bar lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma per_nat_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_nat_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_nat_bar ts lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_nat_bar in *; exrepnd.
  exists (equality_of_nat_bar lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma per_csname_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_csname_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_csname_bar ts lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_csname_bar in *; exrepnd.
  exists (equality_of_csname_bar lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma per_atom_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_atom_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_atom_bar ts lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_atom_bar in *; exrepnd.
  exists (equality_of_atom_bar lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma per_uatom_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_uatom_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_uatom_bar ts lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_uatom_bar in *; exrepnd.
  exists (equality_of_uatom_bar lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma per_base_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_base_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_base_bar ts lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_base_bar in *; exrepnd.
  exists (per_base_eq lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma per_approx_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_approx_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_approx_bar ts lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_approx_bar in *; exrepnd.
  exists (per_approx_eq_bar lib' a b) a b c d; dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma per_cequiv_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_cequiv_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_cequiv_bar ts lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_cequiv_bar in *; exrepnd.
  exists (per_cequiv_eq_bar lib' a b) a b c d; dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma per_eq_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_eq_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_eq_bar (close ts) lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_eq_bar in *; exrepnd.
  exists (per_eq_eq lib' a1 a2 eqa) A B a1 a2 b1 b2.
  exists eqa; dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Definition raise_lib_per {o} {lib lib'}
           (per : lib-per(lib,o))
           (ext : lib_extends lib' lib) : lib-per(lib',o).
Proof.
  introv e.
  apply (per lib'0).
  eapply lib_extends_trans; eauto.
Defined.

Notation "lib-per-fam ( lib , eqa , o )" :=
  (forall (lib' : @library o) (ext : @lib_extends o lib' lib) a a' (p : eqa lib' ext a a'), per(o)) (at level 0).

Definition raise_lib_per_fam
           {o}
           {lib lib' : @library o}
           {eqa : lib-per(lib,o)}
           (per : lib-per-fam(lib,eqa,o))
           (ext : lib_extends lib' lib) : lib-per-fam(lib',raise_lib_per eqa ext,o).
Proof.
  introv e.
  simpl in *.
  unfold raise_lib_per in e.
  apply (per lib'0 (lib_extends_trans lib'0 lib' lib ext0 ext) a a'); auto.
Defined.

Lemma implies_in_ext_ext_ts_raise_lib_per {o} :
  forall (ts : cts(o)) lib lib' (ext : lib_extends lib' lib) A A' eqa,
    in_ext_ext lib (fun lib' x => ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A A' (raise_lib_per eqa ext lib'' x)).
Proof.
  introv ie; repeat introv; apply ie.
Qed.
Hint Resolve implies_in_ext_ext_ts_raise_lib_per : slow.

Lemma implies_in_ext_ext_ts_raise_lib_per_fam {o} :
  forall (ts : cts(o)) lib lib' (ext : lib_extends lib' lib) v v' B B' (eqa : lib-per(lib,o)) eqb,
    in_ext_ext
      lib
      (fun lib' x =>
         forall a a' (e : eqa lib' x a a'),
           ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> in_ext_ext
         lib'
         (fun lib'' x =>
            forall a a' (e : raise_lib_per eqa ext lib'' x a a'),
              ts lib'' (B)[[v\\a]] (B')[[v'\\a']] (raise_lib_per_fam eqb ext lib'' x a a' e)).
Proof.
  introv ie; repeat introv; apply ie.
Qed.
Hint Resolve implies_in_ext_ext_ts_raise_lib_per_fam : slow.

Lemma implies_type_family_ext_raise_lib_per {o} :
  forall C (ts : cts(o)) lib lib' (ext : lib_extends lib' lib) T T' eqa eqb,
    type_family_ext C ts lib T T' eqa eqb
    -> type_family_ext C ts lib' T T' (raise_lib_per eqa ext) (raise_lib_per_fam eqb ext).
Proof.
  introv tf.
  unfold type_family_ext in *; exrepnd.
  exists A A' v v' B B'; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve implies_type_family_ext_raise_lib_per : slow.

Lemma per_func_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_func_ext (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_func_ext (close ts) lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_func_ext in *; exrepnd.

  exists (per_func_ext_eq lib' (raise_lib_per eqa ext) (raise_lib_per_fam eqb ext))
         (raise_lib_per eqa ext)
         (raise_lib_per_fam eqb ext).
  dands; eauto 3 with slow.
Qed.

Lemma per_union_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_union_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_union_bar (close ts) lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_union_bar in *; exrepnd.
  exists (per_union_eq_bar lib' eqa eqb) eqa eqb A1 A2 B1 B2.
  dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma per_product_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_product_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_product_bar (close ts) lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_product_bar in *; exrepnd.

  exists (per_product_eq_bar lib' (raise_lib_per eqa ext) (raise_lib_per_fam eqb ext))
         (raise_lib_per eqa ext)
         (raise_lib_per_fam eqb ext).
  dands; eauto 3 with slow.
Qed.

Lemma close_monotone {o} :
  forall (ts : cts(o)), type_monotone ts -> type_monotone (close ts).
Proof.
  introv m cl.
  close_cases (induction cl using @close_ind') Case; introv ext.

  - Case "CL_init".
    pose proof (m lib lib' T T' eq) as h; repeat (autodimp h hyp).
    exrepnd.
    exists eq'.
    apply CL_init; auto.

  - Case "CL_int".
    pose proof (per_int_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_int; auto.

  - Case "CL_nat".
    pose proof (per_nat_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_nat; auto.

  - Case "CL_csname".
    pose proof (per_csname_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_csname; auto.

  - Case "CL_atom".
    pose proof (per_atom_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_atom; auto.

  - Case "CL_uatom".
    pose proof (per_uatom_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_uatom; auto.

  - Case "CL_base".
    pose proof (per_base_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_base; auto.

  - Case "CL_approx".
    pose proof (per_approx_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_approx; auto.

  - Case "CL_cequiv".
    pose proof (per_cequiv_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_cequiv; auto.

  - Case "CL_eq".
    pose proof (per_eq_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_eq; auto.

  - Case "CL_func".
    pose proof (per_func_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_func; auto.

  - Case "CL_union".
    pose proof (per_union_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_union; auto.

  - Case "CL_product".
    pose proof (per_product_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_product; auto.
Qed.

Lemma nuprl_monotone {o} : @type_monotone o nuprl.
Proof.
  unfold nuprl.
  apply close_monotone; eauto 3 with slow.
Qed.

Lemma tequality_monotone {o} :
  forall lib lib' (A B : @CTerm o),
    lib_extends lib' lib
    -> tequality lib A B
    -> tequality lib' A B.
Proof.
  introv ext teq.
  unfold tequality in *; exrepnd.
  apply (nuprl_monotone lib lib') in teq0; auto.
Qed.
Hint Resolve tequality_monotone : slow.

Definition sub_per {o} (per1 per2 : per(o)) :=
  forall a b, per1 a b -> per2 a b.

Definition type_monotone2 {p} (ts : cts(p)) :=
  forall lib lib' T1 T2 eq,
    ts lib T1 T2 eq
    -> lib_extends lib' lib
    -> exists eq',
        ts lib' T1 T2 eq' # sub_per eq eq'.

Lemma sub_per_eq_eq_term_equals_left {o} :
  forall (per1 per2 per3 : per(o)),
    (per1 <=2=> per2)
    -> sub_per per2 per3
    -> sub_per per1 per3.
Proof.
  introv eqiff s h.
  apply s; apply eqiff; auto.
Qed.
Hint Resolve sub_per_eq_eq_term_equals_left : slow.

Lemma sub_per_equality_of_int_bar {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib),
    sub_per (equality_of_int_bar lib) (equality_of_int_bar lib').
Proof.
  introv ext h.
  unfold equality_of_int_bar, equality_of_int_bar1 in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_int_bar : slow.

Lemma per_int_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_int_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_int_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_int_bar in *; exrepnd.
  exists (equality_of_int_bar lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_equality_of_nat_bar {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib),
    sub_per (equality_of_nat_bar lib) (equality_of_nat_bar lib').
Proof.
  introv ext h.
  unfold equality_of_nat_bar, equality_of_nat in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_nat_bar : slow.

Lemma per_nat_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_nat_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_nat_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_nat_bar in *; exrepnd.
  exists (equality_of_nat_bar lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_equality_of_csname_bar {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib),
    sub_per (equality_of_csname_bar lib) (equality_of_csname_bar lib').
Proof.
  introv ext h.
  unfold equality_of_csname_bar, equality_of_csname in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_csname_bar : slow.

Lemma per_csname_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_csname_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_csname_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_csname_bar in *; exrepnd.
  exists (equality_of_csname_bar lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_equality_of_atom_bar {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib),
    sub_per (equality_of_atom_bar lib) (equality_of_atom_bar lib').
Proof.
  introv ext h.
  unfold equality_of_atom_bar, equality_of_atom_bar1 in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_atom_bar : slow.

Lemma per_atom_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_atom_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_atom_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_atom_bar in *; exrepnd.
  exists (equality_of_atom_bar lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_equality_of_uatom_bar {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib),
    sub_per (equality_of_uatom_bar lib) (equality_of_uatom_bar lib').
Proof.
  introv ext h.
  unfold equality_of_uatom_bar, equality_of_uatom_bar1 in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_equality_of_uatom_bar : slow.

Lemma per_uatom_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_uatom_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_uatom_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_uatom_bar in *; exrepnd.
  exists (equality_of_uatom_bar lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_base_eq {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib),
    sub_per (per_base_eq lib) (per_base_eq lib').
Proof.
  introv ext h.
  unfold per_base_eq, per_base_eq1 in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_base_eq : slow.

Lemma per_base_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_base_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_base_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_base_bar in *; exrepnd.
  exists (per_base_eq lib'); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_approx_eq_bar {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib) a b,
    sub_per (per_approx_eq_bar lib a b) (per_approx_eq_bar lib' a b).
Proof.
  introv ext h.
  unfold per_approx_eq_bar, per_approx_eq_bar1 in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_approx_eq_bar : slow.

Lemma per_approx_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_approx_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_approx_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_approx_bar in *; exrepnd.
  exists (per_approx_eq_bar lib' a b); dands; auto; eauto 3 with slow.
  exists a b c d; dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_cequiv_eq_bar {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib) a b,
    sub_per (per_cequiv_eq_bar lib a b) (per_cequiv_eq_bar lib' a b).
Proof.
  introv ext h.
  unfold per_cequiv_eq_bar, per_cequiv_eq_bar1 in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_cequiv_eq_bar : slow.

Lemma per_cequiv_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_cequiv_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_cequiv_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_cequiv_bar in *; exrepnd.
  exists (per_cequiv_eq_bar lib' a b); dands; auto; eauto 3 with slow.
  exists a b c d; dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_per_eq_eq {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib) a b eqa,
    sub_per (per_eq_eq lib a b eqa) (per_eq_eq lib' a b eqa).
Proof.
  introv ext h.
  unfold per_eq_eq, per_eq_eq1 in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_per_eq_eq : slow.

Lemma per_eq_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_eq_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_eq_bar (close ts) lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_eq_bar in *; exrepnd.
  exists (per_eq_eq lib' a1 a2 eqa); dands; eauto 3 with slow.
  exists A B a1 a2 b1 b2.
  exists eqa; dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_per_func_ext_eq {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib) eqa eqb,
    sub_per (per_func_ext_eq lib eqa eqb)
            (per_func_ext_eq lib' (raise_lib_per eqa ext) (raise_lib_per_fam eqb ext)).
Proof.
  introv h; repeat introv.
  unfold raise_lib_per in *.
  unfold raise_lib_per_fam; simpl in *; tcsp.
Qed.
Hint Resolve sub_per_per_func_ext_eq : slow.

Lemma per_func_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_func_ext (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_func_ext (close ts) lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_func_ext in *; exrepnd.

  exists (per_func_ext_eq lib' (raise_lib_per eqa ext) (raise_lib_per_fam eqb ext)).
  dands; eauto 3 with slow.

  exists (raise_lib_per eqa ext)
         (raise_lib_per_fam eqb ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_per_union_eq_bar {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib) eqa eqb,
    sub_per (per_union_eq_bar lib eqa eqb) (per_union_eq_bar lib' eqa eqb).
Proof.
  introv ext h.
  unfold per_union_eq_bar in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_per_union_eq_bar : slow.

Lemma per_union_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_union_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_union_bar (close ts) lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_union_bar in *; exrepnd.
  exists (per_union_eq_bar lib' eqa eqb); dands; eauto 3 with slow.
  exists eqa eqb A1 A2 B1 B2.
  dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_per_product_bar_eq {o} :
  forall (lib lib' : @library o) (ext : lib_extends lib' lib) eqa eqb,
    term_equality_change_lib_extends eqa
    -> term_equality_change_lib_extends_fam eqb
    -> sub_per (per_product_eq_bar lib eqa eqb)
               (per_product_eq_bar lib' (raise_lib_per eqa ext) (raise_lib_per_fam eqb ext)).
Proof.
  introv cha chb h; repeat introv.
  unfold raise_lib_per in *.
  unfold raise_lib_per_fam; simpl in *; tcsp.
  unfold per_product_eq_bar, per_product_eq in *; exrepnd.
  exists (raise_bar bar ext).
  repeat introv; simpl in *; exrepnd.
  pose proof (h0 lib1 b0 lib'1 (lib_extends_trans lib'1 lib'0 lib1 e b2)) as q; simpl in q.
  exrepnd.

  remember (lib_extends_trans
              lib'1 lib1 lib
              (lib_extends_trans lib'1 lib'0 lib1 e b2)
              (bar_lib_ext bar lib1 b0)) as x1; clear Heqx1.

  remember (lib_extends_trans
              lib'1 lib' lib
              (lib_extends_trans lib'1 lib'0 lib' e b1)
              ext) as x2; clear Heqx2.
  exists a0 a' b3 b'.
  GC.

  pose proof (cha lib'1 x1 x2 a0 a') as z1; autodimp z1 hyp.
  exists z1; dands; auto.
  eapply chb; eauto.
Qed.
Hint Resolve sub_per_per_product_bar_eq : slow.

Lemma type_system_implies_in_ext_ext_type_sys_props4 {o} :
  forall (ts : cts(o)) lib A A' eqa,
    type_system ts
    -> in_ext_ext lib (fun lib' x => ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x)).
Proof.
  introv tsts i; repeat introv.
  pose proof (i lib' e) as h; simpl in h; clear i.
  apply type_system_prop4 in tsts.
  apply tsts; auto.
Qed.
Hint Resolve type_system_implies_in_ext_ext_type_sys_props4 : slow.

Lemma type_family_ext_implies_term_equality_change_lib_extends {o} :
  forall (ts : cts(o)) lib T T' eqa eqb,
    type_system ts
    -> type_family_ext mkc_product ts lib T T' eqa eqb
    -> term_equality_change_lib_extends eqa.
Proof.
  introv tsts tf.
  unfold type_family_ext in *; exrepnd.
  apply (in_ext_ext_type_sys_props4_implies_change_lib_extends ts lib A A'); eauto 3 with slow.
Qed.
Hint Resolve type_family_ext_implies_term_equality_change_lib_extends : slow.

Lemma type_system_implies_in_ext_ext_type_sys_props4_fam {o} :
  forall (ts : cts(o)) lib eqa eqb v B v' B',
    type_system ts
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e)).
Proof.
  introv tsts i; repeat introv.
  pose proof (i lib' e) as h; simpl in h; clear i.
  apply type_system_prop4 in tsts.
  apply tsts; auto.
Qed.
Hint Resolve type_system_implies_in_ext_ext_type_sys_props4_fam : slow.

Lemma type_family_ext_implies_term_equality_change_lib_extends_fam {o} :
  forall (ts : cts(o)) lib T T' eqa eqb,
    type_system ts
    -> type_family_ext mkc_product ts lib T T' eqa eqb
    -> term_equality_change_lib_extends_fam eqb.
Proof.
  introv tsts tf.
  unfold type_family_ext in *; exrepnd.
  apply (in_ext_ext_type_sys_props4_fam_implies_change_lib_extends_fam ts lib v B v' B'); eauto 3 with slow.
Qed.
Hint Resolve type_family_ext_implies_term_equality_change_lib_extends_fam : slow.

Lemma per_product_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    type_system (close ts)
    -> per_product_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_product_bar (close ts) lib' T T' eq' # sub_per eq eq'.
Proof.
  introv tsts per ext.
  unfold per_product_bar in *; exrepnd.

  exists (per_product_eq_bar lib' (raise_lib_per eqa ext) (raise_lib_per_fam eqb ext)).
  dands; eauto 3 with slow.

  { exists (raise_lib_per eqa ext)
           (raise_lib_per_fam eqb ext).
    dands; eauto 3 with slow. }

  { eapply sub_per_eq_eq_term_equals_left;[eauto|].
    apply sub_per_per_product_bar_eq; eauto 3 with slow. }
Qed.

Lemma close_monotone2 {o} :
  forall (ts : cts(o)),
    type_system (close ts)
    -> type_monotone2 ts
    -> type_monotone2 (close ts).
Proof.
  introv tscl m cl.
  close_cases (induction cl using @close_ind') Case; introv ext.

  - Case "CL_init".
    pose proof (m lib lib' T T' eq) as h; repeat (autodimp h hyp).
    exrepnd.
    exists eq'; dands; auto.

  - Case "CL_int".
    pose proof (per_int_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_nat".
    pose proof (per_nat_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_csname".
    pose proof (per_csname_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_atom".
    pose proof (per_atom_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_uatom".
    pose proof (per_uatom_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_base".
    pose proof (per_base_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_approx".
    pose proof (per_approx_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_cequiv".
    pose proof (per_cequiv_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_eq".
    pose proof (per_eq_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_func".
    pose proof (per_func_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_union".
    pose proof (per_union_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_product".
    pose proof (per_product_monotone2 ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.
Qed.

Hint Resolve close_type_system : slow.

Lemma univi_monotone2 {o} :
  forall i, @type_monotone2 o (univi i).
Proof.
  induction i as [? ind] using comp_ind_type.
  introv h ext.
  allrw @univi_exists_iff; exrepnd.
  exists (fun A A' => (exists eqa, close (univi j) lib' A A' eqa)).
  allrw @univi_exists_iff.
  dands.

  { exists j; dands; tcsp; spcast; eauto 3 with slow. }

  { introv h.
    apply h0 in h; exrepnd.

    pose proof (@close_monotone2 o (univi j)) as q.
    repeat (autodimp q hyp); eauto 3 with slow;[].
    pose proof (q lib lib' a b eqa) as q.
    repeat (autodimp q hyp); exrepnd.
    exists eq'; dands; auto. }
Qed.
Hint Resolve univi_monotone2 : slow.

Lemma univ_monotone2 {o} : @type_monotone2 o univ.
Proof.
  introv u e.
  unfold univ in *; exrepnd.
  eapply univi_monotone2 in u0; autodimp u0 hyp; eauto.
  exrepnd.
  exists eq'; dands; auto.
  exists i; auto.
Qed.
Hint Resolve univ_monotone2 : slow.

Lemma nuprl_monotone2 {o} : @type_monotone2 o nuprl.
Proof.
  introv u e.
  unfold nuprl in *; exrepnd.
  pose proof (@close_monotone2 o univ) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve nuprl_monotone2 : slow.

Lemma equality_monotone {o} :
  forall lib lib' (a b A : @CTerm o),
    lib_extends lib' lib
    -> equality lib a b A
    -> equality lib' a b A.
Proof.
  introv ext equ.
  unfold equality in *; exrepnd.
  apply (nuprl_monotone2 lib lib') in equ1; exrepnd; auto.
  exists eq'; dands; tcsp.
Qed.
Hint Resolve equality_monotone : slow.
