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



Require Export nuprl_mon_func.


Definition sub_lib_per {o} {lib lib'} (eqa : lib-per(lib,o)) (x : lib_extends lib' lib) :=
  forall lib'' (y : lib_extends lib'' lib') (w : lib_extends lib'' lib),
    sub_per (eqa lib' x) (eqa lib'' w).

Definition type_monotone_func2 {o} (ts : cts(o)) :=
  forall lib T1 T2 eq,
    ts lib T1 T2 eq
    -> exists (eq' : lib-per(lib,o)),
      forall lib' x,
        ts lib' T1 T2 (eq' lib' x)
        # sub_per eq (eq' lib' x)
        # sub_lib_per eq' x.

Lemma sub_lib_per_equality_of_int_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib),
    sub_lib_per (equality_of_int_bar_lib_per lib) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_equality_of_int_bar;[|eauto]; eauto.
Qed.
Hint Resolve sub_lib_per_equality_of_int_bar_lib_per : slow.

Lemma per_int_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_int ts).
Proof.
  introv per.
  unfold per_int in *; exrepnd.
  exists (equality_of_int_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_lib_per_equality_of_nat_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib),
    sub_lib_per (equality_of_nat_bar_lib_per lib) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_equality_of_nat_bar;[|eauto]; eauto.
Qed.
Hint Resolve sub_lib_per_equality_of_nat_bar_lib_per : slow.

Lemma per_nat_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_nat ts).
Proof.
  introv per.
  unfold per_nat in *; exrepnd.
  exists (equality_of_nat_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_lib_per_equality_of_csname_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib),
    sub_lib_per (equality_of_csname_bar_lib_per lib) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_equality_of_csname_bar;[|eauto]; eauto.
Qed.
Hint Resolve sub_lib_per_equality_of_csname_bar_lib_per : slow.

Lemma per_csname_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_csname ts).
Proof.
  introv per.
  unfold per_csname in *; exrepnd.
  exists (equality_of_csname_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_lib_per_equality_of_atom_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib),
    sub_lib_per (equality_of_atom_bar_lib_per lib) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_equality_of_atom_bar;[|eauto]; eauto.
Qed.
Hint Resolve sub_lib_per_equality_of_atom_bar_lib_per : slow.

Lemma per_atom_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_atom ts).
Proof.
  introv per.
  unfold per_atom in *; exrepnd.
  exists (equality_of_atom_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_lib_per_equality_of_uatom_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib),
    sub_lib_per (equality_of_uatom_bar_lib_per lib) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_equality_of_uatom_bar;[|eauto]; eauto.
Qed.
Hint Resolve sub_lib_per_equality_of_uatom_bar_lib_per : slow.

Lemma per_uatom_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_uatom ts).
Proof.
  introv per.
  unfold per_uatom in *; exrepnd.
  exists (equality_of_uatom_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_lib_per_per_base_eq_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib),
    sub_lib_per (per_base_eq_lib_per lib) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_base_eq;[|eauto]; auto.
Qed.
Hint Resolve sub_lib_per_per_base_eq_lib_per : slow.

Lemma per_base_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_base ts).
Proof.
  introv per.
  unfold per_base in *; exrepnd.
  exists (per_base_eq_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_lib_per_per_approx_eq_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) a b,
    sub_lib_per (per_approx_eq_bar_lib_per lib a b) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_approx_eq_bar;[|eauto]; auto.
Qed.
Hint Resolve sub_lib_per_per_approx_eq_bar_lib_per : slow.

Lemma per_approx_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_approx ts).
Proof.
  introv per.
  unfold per_approx in *; exrepnd.
  exists (per_approx_eq_bar_lib_per lib a b); introv; simpl.
  dands; spcast; eauto 3 with slow.
  exists a b c d; dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_lib_per_per_cequiv_eq_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) a b,
    sub_lib_per (per_cequiv_eq_bar_lib_per lib a b) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_cequiv_eq_bar;[|eauto]; auto.
Qed.
Hint Resolve sub_lib_per_per_cequiv_eq_bar_lib_per : slow.

Lemma per_cequiv_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_cequiv ts).
Proof.
  introv per.
  unfold per_cequiv in *; exrepnd.
  exists (per_cequiv_eq_bar_lib_per lib a b); introv; simpl.
  dands; spcast; eauto 3 with slow.
  exists a b c d; dands; spcast; eauto 3 with slow.
Qed.

Lemma sub_per_per_func_ext_eq2 {o} :
  forall (lib lib' lib'' : @library o)
         (x : lib_extends lib' lib)
         (y : lib_extends lib'' lib')
         (w : lib_extends lib'' lib) eqa eqb,
    sub_per (per_func_ext_eq lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x))
            (per_func_ext_eq lib'' (raise_lib_per eqa w) (raise_lib_per_fam eqb w)).
Proof.
  introv y h; repeat introv.
  unfold per_func_ext_eq in *; exrepnd.
  exists (raise_bar bar y).
  introv br xt; repeat introv.
  unfold raise_lib_per, raise_ext_per in *; simpl in *; exrepnd.
  unfold raise_lib_per_fam, raise_ext_per_fam; simpl in *; tcsp.
  assert (eqa lib'1 (lib_extends_trans (lib_extends_trans x0 y) x) a0 a') as f by (eapply (lib_per_cond _ eqa); eauto).
  pose proof (h0 _ br1 lib'1 (lib_extends_trans xt br2) (lib_extends_trans x0 y) a0 a' f) as h0; simpl in *.
  eapply (lib_per_fam_cond _ eqb).
  eapply h0; eauto 3 with slow.
Qed.
Hint Resolve sub_per_per_func_ext_eq2 : slow.

Lemma sub_lib_per_per_func_ext_eq_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) eqa eqb,
    sub_lib_per (per_func_ext_eq_bar_lib_per lib eqa eqb) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_per_func_ext_eq2;[|eauto];auto.
Qed.
Hint Resolve sub_lib_per_per_func_ext_eq_bar_lib_per : slow.

Lemma per_func_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_func_ext ts).
Proof.
  introv per.
  unfold per_func_ext in *; exrepnd.

  exists (per_func_ext_eq_bar_lib_per lib eqa eqb); introv; simpl; dands; eauto 3 with slow.

  exists (raise_lib_per eqa x)
         (raise_lib_per_fam eqb x).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_per_bar_eq2 {o} :
  forall {lib lib' lib''}
         (bar : @BarLib o lib)
         (x : lib_extends lib' lib)
         (y : lib_extends lib'' lib')
         (w : lib_extends lib'' lib) eqa,
    sub_per (per_bar_eq (raise_bar bar x) (raise_lib_per eqa x))
            (per_bar_eq (raise_bar bar w) (raise_lib_per eqa w)).
Proof.
  introv y h.
  unfold per_bar_eq in *; exrepnd.
  introv br' e; introv; simpl in *; exrepnd.
  unfold raise_ext_per.

  pose proof (h lib'0) as h; simpl in *; autodimp h hyp.
  { exists lib1; dands; auto; eauto 3 with slow. }
  pose proof (h lib'1 e (lib_extends_trans x0 y)) as h; simpl in *.
  exrepnd.
  exists bar'.
  introv br'' e''; introv.
  pose proof (h0 _ br'' _ e'' x1) as h0; simpl in *.
  eapply (lib_per_cond _ eqa); eauto.
Qed.
Hint Resolve sub_per_per_bar_eq2 : slow.

Lemma sub_lib_per_per_bar_eq_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) bar eqa,
    sub_lib_per (per_bar_eq_bar_lib_per lib bar eqa) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_per_bar_eq2;[|eauto]; auto.
Qed.
Hint Resolve sub_lib_per_per_bar_eq_bar_lib_per : slow.

Definition per_bar_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_bar ts).
Proof.
  introv per.
  unfold per_bar in *; exrepnd.
  exists (per_bar_eq_bar_lib_per lib bar eqa); introv.
  dands; simpl; eauto 3 with slow.
  exists (raise_bar bar x) (raise_lib_per eqa x).
  dands; tcsp; eauto 3 with slow.
Qed.

Lemma sub_per_per_set_bar_eq2 {o} :
  forall (lib lib' lib'' : @library o)
         (x : lib_extends lib' lib)
         (y : lib_extends lib'' lib')
         (w : lib_extends lib'' lib) eqa eqb,
    sub_per (per_set_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x))
            (per_set_eq_bar lib'' (raise_lib_per eqa w) (raise_lib_per_fam eqb w)).
Proof.
  introv y h; repeat introv.
  unfold per_set_eq_bar, per_set_eq in *; exrepnd.
  exists (raise_bar bar y).
  introv br xt; repeat introv.
  unfold raise_lib_per, raise_ext_per in *; simpl in *; exrepnd.
  unfold raise_lib_per_fam, raise_ext_per_fam; simpl in *; tcsp.
  pose proof (h0 _ br1 lib'1 (lib_extends_trans xt br2) (lib_extends_trans x0 y)) as h0; simpl in *.
  exrepnd.
  assert (eqa lib'1 (lib_extends_trans x0 w) a b) as f by (eapply (lib_per_cond _ eqa); eauto).
  exists f.
  eapply eq_term_equals_preserves_inhabited;[|eauto].
  apply lib_per_fam_cond.
Qed.
Hint Resolve sub_per_per_set_bar_eq2 : slow.

Lemma sub_lib_per_per_set_eq_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) eqa eqb,
    sub_lib_per (per_set_eq_bar_lib_per lib eqa eqb) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_per_set_bar_eq2;[|eauto];auto.
Qed.
Hint Resolve sub_lib_per_per_set_eq_bar_lib_per : slow.

Lemma per_set_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_set ts).
Proof.
  introv per.
  unfold per_set in *; exrepnd.

  exists (per_set_eq_bar_lib_per lib eqa eqb).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists (raise_lib_per eqa x)
         (raise_lib_per_fam eqb x).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_per_product_bar_eq2 {o} :
  forall (lib lib' lib'' : @library o)
         (x : lib_extends lib' lib)
         (y : lib_extends lib'' lib')
         (w : lib_extends lib'' lib) eqa eqb,
    sub_per (per_product_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x))
            (per_product_eq_bar lib'' (raise_lib_per eqa w) (raise_lib_per_fam eqb w)).
Proof.
  introv y h; repeat introv.
  unfold per_product_eq_bar, per_product_eq in *; exrepnd.
  exists (raise_bar bar y).
  introv br xt; repeat introv.
  unfold raise_lib_per, raise_ext_per in *; simpl in *; exrepnd.
  unfold raise_lib_per_fam, raise_ext_per_fam; simpl in *; tcsp.
  pose proof (h0 _ br1 lib'1 (lib_extends_trans xt br2) (lib_extends_trans x0 y)) as h0; simpl in *.
  exrepnd.
  assert (eqa lib'1 (lib_extends_trans x0 w) a0 a') as f by (eapply (lib_per_cond _ eqa); eauto).
  exists a0 a' b0 b' f; dands; auto.
  eapply (lib_per_fam_cond _ eqb); eauto.
Qed.
Hint Resolve sub_per_per_product_bar_eq2 : slow.

Lemma sub_lib_per_per_product_eq_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) eqa eqb,
    sub_lib_per (per_product_eq_bar_lib_per lib eqa eqb) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_per_product_bar_eq2;[|eauto];auto.
Qed.
Hint Resolve sub_lib_per_per_product_eq_bar_lib_per : slow.

Lemma per_product_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_product_bar ts).
Proof.
  introv per.
  unfold per_product_bar in *; exrepnd.

  exists (per_product_eq_bar_lib_per lib eqa eqb).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists (raise_lib_per eqa x)
         (raise_lib_per_fam eqb x).
  dands; eauto 3 with slow.
Qed.

Lemma sub_per_eq_per_eq_bar2 {o} :
  forall {lib lib' lib''}
         (x : lib_extends lib' lib)
         (y : lib_extends lib'' lib')
         (w : lib_extends lib'' lib)
         a b (eqa : lib-per(lib,o)),
    sub_per (eq_per_eq_bar lib' a b (raise_lib_per eqa x))
            (eq_per_eq_bar lib'' a b (raise_lib_per eqa w)).
Proof.
  introv y h.
  unfold eq_per_eq_bar in *; exrepnd.
  exists (raise_bar bar y).
  introv br xt; introv; simpl in *; exrepnd.
  pose proof (h0 _ br1 lib'1 (lib_extends_trans xt br2) (lib_extends_trans x0 y)) as h0; simpl in *.
  unfold eq_per_eq in *; repnd; dands; auto; simpl in *.
  unfold raise_ext_per in *.
  eapply (lib_per_cond _ eqa); eauto.
Qed.
Hint Resolve sub_per_eq_per_eq_bar2 : slow.

Lemma sub_lib_per_eq_per_eq_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) a1 a2 eqa,
    sub_lib_per (eq_per_eq_bar_lib_per lib a1 a2 eqa) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_eq_per_eq_bar2;[|eauto];auto.
Qed.
Hint Resolve sub_lib_per_eq_per_eq_bar_lib_per : slow.

Lemma per_eq_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_eq ts).
Proof.
  introv per.
  unfold per_eq in *; exrepnd.

  exists (eq_per_eq_bar_lib_per lib a1 a2 eqa).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists A B a1 a2 b1 b2 (raise_lib_per eqa x).
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_eq_monotone_func : slow.

Lemma sub_per_per_image_eq_bar2 {o} :
  forall {lib lib' lib''}
         (x : lib_extends lib' lib)
         (y : lib_extends lib'' lib')
         (w : lib_extends lib'' lib)
         (eqa : lib-per(lib,o)) f,
    sub_per (per_image_eq_bar lib' (raise_lib_per eqa x) f)
            (per_image_eq_bar lib'' (raise_lib_per eqa w) f).
Proof.
  introv y h.
  unfold per_image_eq_bar in *; exrepnd.
  exists (raise_bar bar y).
  introv br xt; introv; simpl in *; exrepnd.
  pose proof (h0 _ br1 lib'1 (lib_extends_trans xt br2) (lib_extends_trans x0 y)) as h0; simpl in *.
  eapply implies_eq_term_equals_eq_image_eq;[|eauto].
  apply lib_per_cond.
Qed.
Hint Resolve sub_per_per_image_eq_bar2 : slow.

Lemma sub_lib_per_per_image_eq_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) (eqa : lib-per(lib,o)) f,
    sub_lib_per (per_image_eq_bar_lib_per lib eqa f) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_per_image_eq_bar2;[|eauto];auto.
Qed.
Hint Resolve sub_lib_per_per_image_eq_bar_lib_per : slow.

Lemma per_image_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_image ts).
Proof.
  introv per.
  unfold per_image in *; exrepnd.

  exists (per_image_eq_bar_lib_per lib eqa f1).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists (raise_lib_per eqa x) A1 A2 f1 f2.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_image_monotone_func2 : slow.

Lemma sub_per_per_union_eq_bar2 {o} :
  forall {lib lib' lib''}
         (x : lib_extends lib' lib)
         (y : lib_extends lib'' lib')
         (w : lib_extends lib'' lib)
         (eqa eqb : lib-per(lib,o)),
    sub_per (per_union_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per eqb x))
            (per_union_eq_bar lib'' (raise_lib_per eqa w) (raise_lib_per eqb w)).
Proof.
  introv y h.
  unfold per_union_eq_bar in *; exrepnd.
  exists (raise_bar bar y).
  introv br xt; introv; simpl in *; exrepnd.
  pose proof (h0 _ br1 lib'1 (lib_extends_trans xt br2) (lib_extends_trans x0 y)) as h0; simpl in *.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R in *; repndors; exrepnd;
    [left|right]; eexists; eexists; dands; eauto; unfold raise_ext_per in *;
      try eapply (lib_per_cond _ eqa); eauto;
        try eapply (lib_per_cond _ eqb); eauto.
Qed.
Hint Resolve sub_per_per_union_eq_bar2 : slow.

Lemma sub_lib_per_per_union_eq_bar_lib_per {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) eqa eqb,
    sub_lib_per (per_union_eq_bar_lib_per lib eqa eqb) x.
Proof.
  introv h z; simpl in *.
  eapply sub_per_per_union_eq_bar2;[|eauto];auto.
Qed.
Hint Resolve sub_lib_per_per_union_eq_bar_lib_per : slow.

Lemma per_union_monotone_func2 {o} :
  forall (ts : cts(o)), type_monotone_func2 (per_union ts).
Proof.
  introv per.
  unfold per_union in *; exrepnd.

  exists (per_union_eq_bar_lib_per lib eqa eqb).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists (raise_lib_per eqa x) (raise_lib_per eqb x) A1 A2 B1 B2.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_union_monotone_func2 : slow.

Lemma close_monotone_func2 {o} :
  forall (ts : cts(o)),
    type_monotone_func2 ts
    -> type_monotone_func2 (close ts).
Proof.
  introv m cl.
  close_cases (induction cl using @close_ind') Case; introv.

  - Case "CL_init".
    pose proof (m lib T T' eq) as h; repeat (autodimp h hyp).
    exrepnd.
    exists eq'; introv.
    pose proof (h0 _ x) as h0; repnd; dands; auto.

  - Case "CL_bar".
    pose proof (per_bar_monotone_func2 (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_int".
    pose proof (per_int_monotone_func2 ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_nat".
    pose proof (per_nat_monotone_func2 ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_csname".
    pose proof (per_csname_monotone_func2 ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_atom".
    pose proof (per_atom_monotone_func2 ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_uatom".
    pose proof (per_uatom_monotone_func2 ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_base".
    pose proof (per_base_monotone_func2 ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_approx".
    pose proof (per_approx_monotone_func2 ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_cequiv".
    pose proof (per_cequiv_monotone_func2 ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_eq".
    pose proof (per_eq_monotone_func2 (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_func".
    pose proof (per_func_monotone_func2 (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_union".
    pose proof (per_union_monotone_func2 (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_image".
    pose proof (per_image_monotone_func2 (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_set".
    pose proof (per_set_monotone_func2 (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_product".
    pose proof (per_product_monotone_func2 (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.
Qed.

Lemma sub_lib_per_univi_eq_lib_per {o} :
  forall {lib' lib} (x : @lib_extends o lib' lib) j,
    @type_monotone o (univi j)
    -> sub_lib_per (univi_eq_lib_per lib j) x.
Proof.
  introv mon y h; simpl in *.
  unfold univi_eq in *; exrepnd.
  pose proof (@close_monotone o (univi_bar j)) as q; autodimp q hyp; eauto 3 with slow.
  eapply q in h0; autodimp h0 hyp; eauto.
  exrepnd; eauto.
Qed.
Hint Resolve sub_lib_per_univi_eq_lib_per : slow.

Lemma univi_monotone_func2_implies_univi_bar_monotone_func2 {o} :
  forall i,
    @type_monotone_func2 o (univi i)
    -> @type_monotone_func2 o (univi_bar i).
Proof.
  introv mon h.
  unfold univi_bar, per_bar in *; exrepnd.
  exists (per_bar_eq_bar_lib_per lib bar eqa); introv; simpl.
  dands; auto; eauto 3 with slow;[].
  exists (raise_bar bar x) (raise_lib_per eqa x).
  dands; tcsp;[].
  introv br xt; introv; simpl in *; exrepnd.
  eapply type_extensionality_univi;[apply (h0 lib1 br1 lib'1 (lib_extends_trans xt br2))|].
  introv; split; intro h; eauto.
Qed.
Hint Resolve univi_monotone_func2_implies_univi_bar_monotone_func2 : slow.

Lemma univi_monotone_func2 {o} :
  forall i, @type_monotone_func2 o (univi i).
Proof.
  induction i as [? ind] using comp_ind_type.
  introv h.
  allrw @univi_exists_iff; exrepnd.
  exists (univi_eq_lib_per lib j); introv.
  allrw @univi_exists_iff.
  dands; simpl; eauto 3 with slow.

  { exists j; dands; tcsp; spcast; eauto 3 with slow. }

  { introv h.
    unfold univi_eq in *.
    apply h0 in h; exrepnd.

    pose proof (@close_monotone o (univi_bar j)) as q.
    repeat (autodimp q hyp); eauto 3 with slow;[].
    pose proof (q lib lib' a b eqa) as q.
    repeat (autodimp q hyp); exrepnd.
    exists eq'; dands; auto. }
Qed.
Hint Resolve univi_monotone_func2 : slow.

Lemma univi_bar_monotone_func2 {o} :
  forall i, @type_monotone_func2 o (univi_bar i).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve univi_bar_monotone_func2 : slow.

Lemma univ_monotone_func2 {o} : @type_monotone_func2 o univ.
Proof.
  introv u.
  unfold univ in *; exrepnd.
  apply per_bar_monotone_func2 in u; exrepnd.
  exists eq'; auto.
Qed.
Hint Resolve univ_monotone_func2 : slow.

Lemma nuprl_monotone_func2 {o} : @type_monotone_func2 o nuprl.
Proof.
  unfold nuprl.
  apply close_monotone_func2; eauto 3 with slow.
Qed.
Hint Resolve nuprl_monotone_func2 : slow.

Lemma nuprli_monotone_func2 {o} : forall i, @type_monotone_func2 o (nuprli i).
Proof.
  introv u.
  unfold nuprli in *; exrepnd.
  pose proof (@close_monotone_func2 o (univi_bar i)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve nuprli_monotone_func2 : slow.
