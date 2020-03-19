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



Require Export nuprl_mon.



Definition type_monotone_func {o} (ts : cts(o)) :=
  forall lib T1 T2 eq,
    ts lib T1 T2 eq
    -> exists (eq' : lib-per(lib,o)),
      forall lib' x,
        ts lib' T1 T2 (eq' lib' x)
        # sub_per eq (eq' lib' x).

Lemma per_int_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_int ts).
Proof.
  introv per.
  unfold per_int in *; exrepnd.
  exists (equality_of_int_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_nat_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_nat ts).
Proof.
  introv per.
  unfold per_nat in *; exrepnd.
  exists (equality_of_nat_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_qnat_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_qnat ts).
Proof.
  introv per.
  unfold per_qnat in *; exrepnd.
  exists (equality_of_qnat_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_csname_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_csname ts).
Proof.
  introv per.
  unfold per_csname in *; exrepnd.
  exists (equality_of_csname_bar_lib_per lib n); introv; simpl.
  dands; spcast; eauto 3 with slow; exists n; dands; spcast; eauto 3 with slow.
Qed.

Lemma per_atom_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_atom ts).
Proof.
  introv per.
  unfold per_atom in *; exrepnd.
  exists (equality_of_atom_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_uatom_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_uatom ts).
Proof.
  introv per.
  unfold per_uatom in *; exrepnd.
  exists (equality_of_uatom_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_base_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_base ts).
Proof.
  introv per.
  unfold per_base in *; exrepnd.
  exists (per_base_eq_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_approx_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_approx ts).
Proof.
  introv per.
  unfold per_approx in *; exrepnd.
  exists (per_approx_eq_bar_lib_per lib a b); introv; simpl.
  dands; spcast; eauto 3 with slow.
  exists a b c d; dands; spcast; eauto 3 with slow.
Qed.

Lemma per_cequiv_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_cequiv ts).
Proof.
  introv per.
  unfold per_cequiv in *; exrepnd.
  exists (per_cequiv_eq_bar_lib_per lib a b); introv; simpl.
  dands; spcast; eauto 3 with slow.
  exists a b c d; dands; spcast; eauto 3 with slow.
Qed.

Definition per_func_ext_eq_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o))
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' x => per_func_ext_eq lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x)).
  repeat introv.
  unfold per_func_ext_eq; split; intro h; exrepnd;
    eapply in_open_bar_ext_pres; eauto; clear h; introv h; simpl in *.

  - unfold per_func_eq, raise_ext_per_fam, raise_ext_per in *; simpl in *; introv.
    pose proof (lib_per_cond _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as e'.
    dup e1 as e2; apply e' in e2; clear e'.
    eapply (lib_per_fam_cond _ eqb lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e) a a' e1 e2); eauto; apply q.

  - unfold per_func_eq, raise_ext_per_fam, raise_ext_per in *; simpl in *; introv.
    pose proof (lib_per_cond _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as e'.
    dup e1 as e2; apply e' in e2; clear e'.
    eapply (lib_per_fam_cond _ eqb lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e) a a' e2 e1); eauto; apply q.
Defined.

Lemma per_func_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_func_ext ts).
Proof.
  introv per.
  unfold per_func_ext in *; exrepnd.

  exists (per_func_ext_eq_bar_lib_per lib eqa eqb); introv; simpl; dands; eauto 3 with slow.

  exists (raise_lib_per eqa x)
         (raise_lib_per_fam eqb x).
  dands; eauto 3 with slow.
Qed.

Definition per_qtime_eq_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' x => per_qtime_eq_bar lib' (raise_lib_per eqa x)).
  repeat introv.
  unfold per_qtime_eq_bar; split; intro h; exrepnd;
    eapply in_open_bar_ext_pres; eauto; clear h; introv h; simpl in *.

  - unfold per_qtime_eq, raise_ext_per in *; simpl in *; introv; exrepnd.
    pose proof (lib_per_cond _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as e1.
    dup h1 as e2; apply e1 in e2; clear e1.
    exists x y0; dands; auto.

  - unfold per_qtime_eq, raise_ext_per in *; simpl in *; introv; exrepnd.
    pose proof (lib_per_cond _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as e1.
    dup h1 as e2; apply e1 in e2; clear e1.
    exists x y0; dands; auto.
Defined.

Lemma per_qtime_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_qtime ts).
Proof.
  introv per.
  unfold per_qtime in *; exrepnd.

  exists (per_qtime_eq_bar_lib_per lib eqa); introv; simpl; dands; eauto 3 with slow.

  exists (raise_lib_per eqa x) A B.
  dands; eauto 3 with slow.
Qed.

Definition equality_of_qlt_bar_lib_per {o}
           (lib : @library o) (a b : @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => equality_of_qlt_bar lib' a b).
  introv x y; tcsp.
Defined.

Lemma per_qlt_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_qlt ts).
Proof.
  introv per.
  unfold per_qlt in *; exrepnd.

  exists (equality_of_qlt_bar_lib_per lib a b); introv; simpl; dands; eauto 3 with slow.
  eexists; eexists; eexists; eexists; dands; eauto 3 with slow.
Qed.

Definition per_union_eq_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o))
           (eqb : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' x => per_union_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per eqb x)).
  repeat introv.
  unfold per_union_eq_bar; split; intro h; exrepnd;
    eapply in_open_bar_ext_pres; eauto; introv q.

  - unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x y0; dands; spcast; eauto 3 with slow.
    { eapply (lib_per_cond _ eqa); eauto. }
    { eapply (lib_per_cond _ eqb); eauto. }

  - unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x y0; dands; spcast; eauto 3 with slow.
    { eapply (lib_per_cond _ eqa); eauto. }
    { eapply (lib_per_cond _ eqb); eauto. }
Defined.

Lemma per_union_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_union ts).
Proof.
  introv per.
  unfold per_union in *; exrepnd.
(*
  exists (per_union_eq_bar_lib_per lib eqa eqb); introv; simpl; dands; eauto 3 with slow.

  exists (raise_lib_per eqa x)
         (raise_lib_per_fam eqb x).
  dands; eauto 3 with slow.
*)
Abort.

Definition per_bar_eq_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => per_bar_eq lib' (raise_lib_per eqa x)).
  repeat introv.
  unfold per_bar_eq; split; introv h;
    eapply in_open_bar_ext_pres; eauto; clear h; introv h; simpl in *;
      unfold raise_lib_per, raise_ext_per in *; simpl in *; exrepnd;
        eapply (lib_per_cond _ eqa); eauto.
Defined.

Definition per_bar_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_bar ts).
Proof.
  introv per.
  unfold per_bar in *; exrepnd.
  exists (per_bar_eq_bar_lib_per lib eqa); introv.
  dands; simpl; eauto 3 with slow.
  exists (raise_lib_per eqa x).
  dands; tcsp; eauto 3 with slow.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in per1; simpl in *; auto.
Qed.

Lemma eq_term_equals_preserves_inhabited {o} :
  forall (e1 e2 : per(o)),
    (e1 <=2=> e2)
    -> inhabited e1
    -> inhabited e2.
Proof.
  unfold inhabited; introv h q; exrepnd; exists t; apply h; auto.
Qed.
Hint Resolve eq_term_equals_preserves_inhabited : slow.

Definition per_set_eq_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o))
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' x => per_set_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x)).
  repeat introv.
  unfold per_set_eq_bar, per_set_eq; split; intro h;
    eapply in_open_bar_ext_pres; eauto; introv q; exrepnd; simpl in *.

  - unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as e'.
    dup e1 as e2; apply e' in e2; clear e'.
    exists e2; auto.
    eapply eq_term_equals_preserves_inhabited;[|eauto].
    apply lib_per_fam_cond.

  - unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as e'.
    dup e1 as e2; apply e' in e2; clear e'.
    exists e2; auto.
    eapply eq_term_equals_preserves_inhabited;[|eauto].
    apply lib_per_fam_cond.
Defined.

Lemma per_set_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_set ts).
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

Definition per_product_eq_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o))
           (eqb : lib-per-fam(lib,eqa,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' x => per_product_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per_fam eqb x)).
  repeat introv.
  unfold per_product_eq_bar, per_product_eq; split; intro h;
    eapply in_open_bar_ext_pres; eauto; introv q; exrepnd.

  - unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as e'.
    dup e1 as e2; apply e' in e2; clear e'.
    exists a a' b b' e2; dands; auto.
    eapply (lib_per_fam_cond _ eqb lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e) a a' e2 e1); eauto.

  - unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as e'.
    dup e1 as e2; apply e' in e2; clear e'.
    exists a a' b b' e2; dands; auto.
    eapply (lib_per_fam_cond _ eqb lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e) a a' e1 e2); eauto.
Defined.

Lemma per_product_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_product_bar ts).
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

Definition eq_per_eq_bar_lib_per {o}
           (lib : @library o)
           (a1 a2 : @CTerm o)
           (eqa : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => eq_per_eq_bar lib' a1 a2 (raise_lib_per eqa x)).
  repeat introv.
  unfold eq_per_eq_bar, eq_per_eq; split; introv h;
    eapply in_open_bar_ext_pres; eauto; introv q;
      repnd; dands; auto.

  - unfold raise_lib_per in *; eapply (lib_per_cond _ eqa); eauto.

  - unfold raise_lib_per in *; eapply (lib_per_cond _ eqa); eauto.
Defined.

Definition eq_per_union_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o))
           (eqb : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' x => eq_per_union_bar lib' (eqa lib' x) (eqb lib' x)).
  introv; introv.
  unfold eq_per_union_bar; split; intro h; exrepnd;
    eapply in_open_bar_pres; eauto; clear h; introv xt q.

  - unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x y0; dands; spcast; eauto 3 with slow.
    { eapply (lib_per_cond _ eqa); eauto. }
    { eapply (lib_per_cond _ eqb); eauto. }

  - unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x y0; dands; spcast; eauto 3 with slow.
    { eapply (lib_per_cond _ eqa); eauto. }
    { eapply (lib_per_cond _ eqb); eauto. }
Defined.

Lemma per_eq_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_eq ts).
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

Lemma implies_eq_term_equals_eq_image_eq {o} :
  forall lib (eqa eqb : per(o)) f,
    (eqa <=2=> eqb)
    -> (per_image_eq lib eqa f) <=2=> (per_image_eq lib eqb f).
Proof.
  introv h; introv; split; intro p; induction p; auto.

  - eapply image_eq_cl; eauto.

  - eapply image_eq_eq; eauto; apply h; auto.

  - eapply image_eq_cl; eauto.

  - eapply image_eq_eq; eauto; apply h; auto.
Qed.

Definition per_image_eq_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o))
           (f   : @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' x => per_image_eq_bar lib' (raise_lib_per eqa x) f).
  introv; introv.
  unfold per_image_eq_bar; split; intro h; exrepnd;
    eapply in_open_bar_ext_pres; eauto; introv q; clear h.

  - eapply implies_eq_term_equals_eq_image_eq;[|eauto]; simpl.
    eapply lib_per_cond.

  - eapply implies_eq_term_equals_eq_image_eq;[|eauto]; simpl.
    eapply lib_per_cond.
Defined.

Lemma per_image_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_image ts).
Proof.
  introv per.
  unfold per_image in *; exrepnd.

  exists (per_image_eq_bar_lib_per lib eqa f1).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists (raise_lib_per eqa x) A1 A2 f1 f2.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_image_monotone_func : slow.

Lemma per_union_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_union ts).
Proof.
  introv per.
  unfold per_union in *; exrepnd.

  exists (per_union_eq_bar_lib_per lib eqa eqb).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists (raise_lib_per eqa x) (raise_lib_per eqb x) A1 A2 B1 B2.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_union_monotone_func : slow.

Lemma ex_nodefsc_change_per {o} :
  forall (eqa : per(o))
         (eqb : per(o))
         t,
    (eqa <=2=> eqb)
    -> ex_nodefsc eqa t
    -> ex_nodefsc eqb t.
Proof.
  introv imp h.
  unfold ex_nodefsc in *; exrepnd.
  exists u; dands; auto; apply imp; auto.
Qed.
Hint Resolve ex_nodefsc_change_per : slow.

Lemma ex_nodefsc_change_lib_per {o} :
  forall lib lib'
         (eqa : lib-per(lib,o))
         (eqb : lib-per(lib,o))
         (x1  : lib_extends lib' lib)
         (x2  : lib_extends lib' lib)
         t,
    (forall lib' x, (eqa lib' x) <=2=> (eqb lib' x))
    -> ex_nodefsc (eqa lib' x1) t
    -> ex_nodefsc (eqb lib' x2) t.
Proof.
  introv imp h.
  unfold ex_nodefsc in *; exrepnd.
  exists u; dands; auto.
  apply imp.
  eapply lib_per_cond; eauto.
Qed.
Hint Resolve ex_nodefsc_change_lib_per : slow.

Lemma ex_nodefsc_change_ext {o} :
  forall lib lib'
         (eqa : lib-per(lib,o))
         (x1  : lib_extends lib' lib)
         (x2  : lib_extends lib' lib)
         t,
    ex_nodefsc (eqa lib' x1) t
    -> ex_nodefsc (eqa lib' x2) t.
Proof.
  introv h.
  unfold ex_nodefsc in *; exrepnd.
  exists u; dands; auto.
  eapply lib_per_cond; eauto.
Qed.
Hint Resolve ex_nodefsc_change_ext : slow.

Lemma ex_nodefsc_raise_ext_per_change_ext {o} :
  forall lib lib1 lib2
         (eqa  : lib-per(lib,o))
         (e1   : lib_extends lib1 lib)
         (e2   : lib_extends lib2 lib)
         (lib3 : @library o)
         (x1   : lib_extends lib3 lib1)
         (x2   : lib_extends lib3 lib2)
         t,
    ex_nodefsc (raise_ext_per eqa e1 lib3 x1) t
    -> ex_nodefsc (raise_ext_per eqa e2 lib3 x2) t.
Proof.
  introv h.
  eapply ex_nodefsc_change_ext; eauto.
Qed.
Hint Resolve ex_nodefsc_raise_ext_per_change_ext : slow.

Definition per_ffdefs_eq_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o))
           (t   : @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => per_ffdefs_eq_bar lib' (raise_lib_per eqa x) t).
  introv; introv.
  unfold per_ffdefs_eq_bar, per_ffdefs_eq; split; introv h;
    eapply in_open_bar_ext_pres; eauto; introv q;
      repnd; dands; auto; simpl in *;
        repnd; dands; auto; eauto 3 with slow.
Defined.

Lemma per_ffdefs_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_ffdefs ts).
Proof.
  introv per.
  unfold per_ffdefs in *; exrepnd.

  exists (per_ffdefs_eq_bar_lib_per lib eqa x1).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists A1 A2 x1 x2 (raise_lib_per eqa x).
  dands; spcast; eauto 3 with slow.

  simpl; introv; unfold raise_ext_per; eapply per4.
Qed.
Hint Resolve per_ffdefs_monotone_func : slow.

Lemma close_monotone_func {o} :
  forall (ts : cts(o)),
    type_monotone_func ts
    -> type_monotone_func (close ts).
Proof.
  introv m cl.
  close_cases (induction cl using @close_ind') Case; introv.

  - Case "CL_init".
    pose proof (m lib T T' eq) as h; repeat (autodimp h hyp).
    exrepnd.
    exists eq'; introv.
    pose proof (h0 _ x) as h0; repnd; dands; auto.

  - Case "CL_bar".
    pose proof (per_bar_monotone_func (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_int".
    pose proof (per_int_monotone_func ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_nat".
    pose proof (per_nat_monotone_func ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_qnat".
    pose proof (per_qnat_monotone_func ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_csname".
    pose proof (per_csname_monotone_func ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_atom".
    pose proof (per_atom_monotone_func ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_uatom".
    pose proof (per_uatom_monotone_func ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_base".
    pose proof (per_base_monotone_func ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_approx".
    pose proof (per_approx_monotone_func ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_cequiv".
    pose proof (per_cequiv_monotone_func ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_eq".
    pose proof (per_eq_monotone_func (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_qtime".
    pose proof (per_qtime_monotone_func (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_qlt".
    pose proof (per_qlt_monotone_func (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_func".
    pose proof (per_func_monotone_func (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_union".
    pose proof (per_union_monotone_func (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_image".
    pose proof (per_image_monotone_func (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_ffdefs".
    pose proof (per_ffdefs_monotone_func (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_set".
    pose proof (per_set_monotone_func (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_product".
    pose proof (per_product_monotone_func (close ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.
Qed.

Definition univi_eq_lib_per {o}
           (lib : @library o)
           (i : nat) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => univi_eq (univi_bar i) lib').
  introv x y; introv; tcsp.
Defined.

Lemma univi_monotone_func_implies_univi_bar_monotone_func {o} :
  forall i,
    @type_monotone_func o (univi i)
    -> @type_monotone_func o (univi_bar i).
Proof.
  introv mon h.
  unfold univi_bar, per_bar in *; exrepnd.
  exists (per_bar_eq_bar_lib_per lib eqa); introv; simpl.
  dands; auto; eauto 3 with slow;[].
  exists (raise_lib_per eqa x).
  dands; tcsp;[].
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ x) in h1; simpl in *; auto.
Qed.
Hint Resolve univi_monotone_func_implies_univi_bar_monotone_func : slow.

Lemma univi_monotone_func {o} :
  forall i, @type_monotone_func o (univi i).
Proof.
  induction i as [? ind] using comp_ind_type.
  introv h.
  allrw @univi_exists_iff; exrepnd.
  exists (univi_eq_lib_per lib j); introv.
  allrw @univi_exists_iff.
  dands; simpl.

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
Hint Resolve univi_monotone_func : slow.

Lemma univi_bar_monotone_func {o} :
  forall i, @type_monotone_func o (univi_bar i).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve univi_bar_monotone_func : slow.

Lemma univ_monotone_func {o} : @type_monotone_func o univ.
Proof.
  introv u.
  unfold univ in *; exrepnd.
  apply per_bar_monotone_func in u; exrepnd.
  exists eq'; auto.
Qed.
Hint Resolve univ_monotone_func : slow.

Lemma nuprl_monotone_func {o} : @type_monotone_func o nuprl.
Proof.
  unfold nuprl.
  apply close_monotone_func; eauto 3 with slow.
Qed.
Hint Resolve nuprl_monotone_func : slow.

Lemma nuprli_monotone_func {o} : forall i, @type_monotone_func o (nuprli i).
Proof.
  introv u.
  unfold nuprli in *; exrepnd.
  pose proof (@close_monotone_func o (univi_bar i)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve nuprli_monotone_func : slow.
