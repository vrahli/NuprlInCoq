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



Require Export computation_lib_extends2.
Require Export raise_bar.


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

Lemma implies_in_ext_ext_ts_raise_lib_per {o} :
  forall (ts : cts(o)) lib lib' (ext : lib_extends lib' lib) A A' eqa,
    in_ext_ext lib (fun lib' x => ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A A' (raise_lib_per eqa ext lib'' x)).
Proof.
  introv ie; repeat introv; apply ie.
Qed.
Hint Resolve implies_in_ext_ext_ts_raise_lib_per : slow.

Lemma implies_all_in_bar_ext_ts_raise_lib_per {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) lib' (ext : lib_extends lib' lib) A A' eqa,
    all_in_bar_ext bar (fun lib' x => ts lib' A A' (eqa lib' x))
    -> all_in_bar_ext (raise_bar bar ext) (fun lib'' x => ts lib'' A A' (raise_lib_per eqa ext lib'' x)).
Proof.
  introv ie b lex; repeat introv; simpl in *; exrepnd.
  eapply ie; eauto 3 with slow.
Qed.
Hint Resolve implies_all_in_bar_ext_ts_raise_lib_per : slow.

Lemma implies_all_in_bar_ext_eqorceq_raise_lib_per {o} :
  forall lib (bar : BarLib lib) lib' (ext : lib_extends lib' lib) a b (eqa : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => eqorceq lib' (eqa lib' x) a b)
    -> all_in_bar_ext (raise_bar bar ext) (fun lib'' x => eqorceq lib'' (raise_lib_per eqa ext lib'' x) a b).
Proof.
  introv ie br lex; repeat introv; simpl in *; exrepnd.
  eapply ie; eauto 3 with slow.
Qed.
Hint Resolve implies_all_in_bar_ext_eqorceq_raise_lib_per : slow.

Lemma per_eq_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_eq_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_eq_bar (close ts) lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_eq_bar in *; exrepnd.
  exists (per_eq_eq lib' a1 a2 (raise_lib_per eqa ext)) A B a1 a2 b1 b2.
  exists (raise_lib_per eqa ext); dands; eauto 3 with slow.
  exists (raise_bar bar ext).
  dands; eauto 3 with slow.
Qed.

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
  apply (per lib'0 (lib_extends_trans ext0 ext) a a'); auto.
Defined.

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

Definition per_bar_monotone {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_bar (close ts) lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_bar (close ts) lib' T T' eq'.
Proof.
  introv per ext.
  unfold per_bar in *; exrepnd.

  exists (per_bar_eq (raise_bar bar ext) (raise_lib_per eqa ext))
         (raise_bar bar ext) (raise_lib_per eqa ext).
  dands; tcsp; eauto 3 with slow.
Qed.

Definition type_monotone {p} (ts : cts(p)) :=
  forall lib lib' T1 T2 eq,
    ts lib T1 T2 eq
    -> lib_extends lib' lib
    -> exists eq', ts lib' T1 T2 eq'.
(* it should be that [subset eq eq'] *)

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

  - Case "CL_bar".
    pose proof (per_bar_monotone ts lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'.
    apply CL_bar; auto.

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

Lemma monotone_univi {o} :
  forall i, @type_monotone o (univi i).
Proof.
  introv h ext.
  allrw @univi_exists_iff; exrepnd.
  exists (fun A A' => (exists eqa, close (univi j) lib' A A' eqa)).
  allrw @univi_exists_iff.
  exists j; dands; tcsp; spcast; eauto 3 with slow.
Qed.
Hint Resolve monotone_univi : slow.

Lemma monotone_univi_bar {o} :
  forall i, @type_monotone o (univi_bar i).
Proof.
  introv h ext.
  unfold univi_bar, per_bar in *; exrepnd.
  exists (per_bar_eq (raise_bar bar ext) (raise_lib_per eqa ext))
         (raise_bar bar ext)
         (raise_lib_per eqa ext).
  dands; tcsp;[].
  introv br w; introv; simpl in *; exrepnd.
  eapply h0; eauto 3 with slow.
Qed.
Hint Resolve monotone_univi_bar : slow.

Lemma monotone_univ {o} : @type_monotone o univ.
Proof.
  introv u e.
  unfold univ in *; exrepnd.
  eapply monotone_univi_bar in u0; autodimp u0 hyp; eauto.
  exrepnd.
  exists eq' i; auto.
Qed.
Hint Resolve monotone_univ : slow.

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
    per_int_bar ts lib T T' eq
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
    per_nat_bar ts lib T T' eq
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
    per_csname_bar ts lib T T' eq
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
    per_atom_bar ts lib T T' eq
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
    per_uatom_bar ts lib T T' eq
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
    per_base_bar ts lib T T' eq
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
    per_approx_bar ts lib T T' eq
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
    per_cequiv_bar ts lib T T' eq
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
    sub_per (per_eq_eq lib a b eqa) (per_eq_eq lib' a b (raise_lib_per eqa ext)).
Proof.
  introv h.
  unfold per_eq_eq, per_eq_eq1 in *; exrepnd.
  exists (raise_bar bar ext).
  introv br e; introv; simpl in *; exrepnd.
  apply (h0 lib1 br1 lib'1); eauto 3 with slow.
Qed.
Hint Resolve sub_per_per_eq_eq : slow.

Lemma per_eq_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_eq_bar ts lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_eq_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_eq_bar in *; exrepnd.
  exists (per_eq_eq lib' a1 a2 (raise_lib_per eqa ext)); dands; eauto 3 with slow.
  exists A B a1 a2 b1 b2.
  exists (raise_lib_per eqa ext); dands; eauto 3 with slow.
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
    per_func_ext ts lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_func_ext ts lib' T T' eq' # sub_per eq eq'.
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
    per_union_bar ts lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_union_bar ts lib' T T' eq' # sub_per eq eq'.
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
    sub_per (per_product_eq_bar lib eqa eqb)
            (per_product_eq_bar lib' (raise_lib_per eqa ext) (raise_lib_per_fam eqb ext)).
Proof.
  introv h; repeat introv.
  unfold raise_lib_per in *.
  unfold raise_lib_per_fam; simpl in *; tcsp.
  unfold per_product_eq_bar, per_product_eq in *; exrepnd.
  exists (raise_bar bar ext).
  introv br lex; introv; simpl in *; exrepnd.
  pose proof (h0 lib1 br1 lib'1 (lib_extends_trans lex br2) (lib_extends_trans x ext)) as q; simpl in q.
  exrepnd.

  exists a0 a' b0 b' e; dands; auto.
Qed.
Hint Resolve sub_per_per_product_bar_eq : slow.

(*Lemma type_system_implies_in_ext_ext_type_sys_props4 {o} :
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
Hint Resolve type_system_implies_in_ext_ext_type_sys_props4 : slow.*)

(*Lemma type_family_ext_implies_term_equality_change_lib_extends {o} :
  forall (ts : cts(o)) lib T T' eqa eqb,
    type_system ts
    -> type_family_ext mkc_product ts lib T T' eqa eqb
    -> term_equality_change_lib_extends eqa.
Proof.
  introv tsts tf.
  unfold type_family_ext in *; exrepnd.
  apply (in_ext_ext_type_sys_props4_implies_change_lib_extends ts lib A A'); eauto 3 with slow.
Qed.
Hint Resolve type_family_ext_implies_term_equality_change_lib_extends : slow.*)

(*Lemma type_system_implies_in_ext_ext_type_sys_props4_fam {o} :
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
Hint Resolve type_system_implies_in_ext_ext_type_sys_props4_fam : slow.*)

(*Lemma type_family_ext_implies_term_equality_change_lib_extends_fam {o} :
  forall (ts : cts(o)) lib T T' eqa eqb,
    type_system ts
    -> type_family_ext mkc_product ts lib T T' eqa eqb
    -> term_equality_change_lib_extends_fam eqb.
Proof.
  introv tsts tf.
  unfold type_family_ext in *; exrepnd.
  apply (in_ext_ext_type_sys_props4_fam_implies_change_lib_extends_fam ts lib v B v' B'); eauto 3 with slow.
Qed.
Hint Resolve type_family_ext_implies_term_equality_change_lib_extends_fam : slow.*)

Lemma per_product_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_product_bar ts lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_product_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_product_bar in *; exrepnd.

  exists (per_product_eq_bar lib' (raise_lib_per eqa ext) (raise_lib_per_fam eqb ext)).
  dands; eauto 3 with slow.

  exists (raise_lib_per eqa ext)
         (raise_lib_per_fam eqb ext).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_per_bar_eq {o} :
  forall {lib} {lib'} (bar : @BarLib o lib) (ext : lib_extends lib' lib) eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> sub_per eq (per_bar_eq (raise_bar bar ext) (raise_lib_per eqa ext)).
Proof.
  introv eqiff h.
  apply eqiff in h; clear eqiff.
  introv br e; introv; simpl in *; exrepnd.
  eapply h; eauto 3 with slow.
Qed.
Hint Resolve sub_per_per_bar_eq : slow.

Lemma per_bar_monotone2 {o} :
  forall (ts : cts(o)) lib lib' T T' eq,
    per_bar ts lib T T' eq
    -> lib_extends lib' lib
    -> exists eq', per_bar ts lib' T T' eq' # sub_per eq eq'.
Proof.
  introv per ext.
  unfold per_bar in *; exrepnd.

  exists (per_bar_eq (raise_bar bar ext) (raise_lib_per eqa ext)); dands; eauto 3 with slow.
  exists (raise_bar bar ext) (raise_lib_per eqa ext); dands; eauto 3 with slow.
Qed.

Lemma close_monotone2 {o} :
  forall (ts : cts(o)),
    type_monotone2 ts
    -> type_monotone2 (close ts).
Proof.
  introv m cl.
  close_cases (induction cl using @close_ind') Case; introv ext.

  - Case "CL_init".
    pose proof (m lib lib' T T' eq) as h; repeat (autodimp h hyp).
    exrepnd.
    exists eq'; dands; auto.

  - Case "CL_bar".
    pose proof (per_bar_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_int".
    pose proof (per_int_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_nat".
    pose proof (per_nat_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_csname".
    pose proof (per_csname_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_atom".
    pose proof (per_atom_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_uatom".
    pose proof (per_uatom_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_base".
    pose proof (per_base_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_approx".
    pose proof (per_approx_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_cequiv".
    pose proof (per_cequiv_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_eq".
    pose proof (per_eq_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_func".
    pose proof (per_func_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_union".
    pose proof (per_union_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.

  - Case "CL_product".
    pose proof (per_product_monotone2 (close ts) lib lib' T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; dands; auto.
Qed.

(*Hint Resolve close_type_system : slow.*)

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
    unfold univi_eq in *.
    apply h0 in h; exrepnd.

    pose proof (@close_monotone2 o (univi j)) as q.
    repeat (autodimp q hyp); eauto 3 with slow;[].
    pose proof (q lib lib' a b eqa) as q.
    repeat (autodimp q hyp); exrepnd.
    exists eq'; dands; auto. }
Qed.
Hint Resolve univi_monotone2 : slow.

Lemma univi_bar_monotone2 {o} :
  forall i, @type_monotone2 o (univi_bar i).
Proof.
  introv h ext.
  unfold univi_bar in *.
  eapply per_bar_monotone2; eauto.
Qed.
Hint Resolve univi_bar_monotone2 : slow.

Lemma univ_monotone2 {o} : @type_monotone2 o univ.
Proof.
  introv u e.
  unfold univ in *; exrepnd.
  eapply univi_bar_monotone2 in u0; autodimp u0 hyp; eauto.
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

Lemma nuprli_monotone2 {o} : forall i, @type_monotone2 o (nuprli i).
Proof.
  introv u e.
  unfold nuprli in *; exrepnd.
  pose proof (@close_monotone2 o (univi_bar i)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve nuprli_monotone2 : slow.

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

Lemma member_monotone {o} :
  forall lib lib' (a A : @CTerm o),
    lib_extends lib' lib
    -> member lib a A
    -> member lib' a A.
Proof.
  introv ext equ.
  eapply equality_monotone in equ; eauto.
Qed.
Hint Resolve member_monotone : slow.

Lemma meta_type_monotone {o} :
  forall lib lib' (A : @CTerm o),
    lib_extends lib' lib
    -> type lib A
    -> type lib' A.
Proof.
  introv ext equ.
  eapply tequality_monotone in equ; eauto.
Qed.
Hint Resolve meta_type_monotone : slow.
