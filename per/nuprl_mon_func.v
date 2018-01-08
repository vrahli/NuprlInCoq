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

Lemma per_csname_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_csname ts).
Proof.
  introv per.
  unfold per_csname in *; exrepnd.
  exists (equality_of_csname_bar_lib_per lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
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
    exists bar; introv br ext; introv.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *.
    unfold per_func_eq, raise_ext_per_fam, raise_ext_per in *; simpl in *; introv.
    pose proof (lib_per_cond _ eqa lib'1 (lib_extends_trans x y) (lib_extends_trans x e)) as e1.
    dup e0 as e2; apply e1 in e2; clear e1.
    eapply (lib_per_fam_cond _ eqb lib'1 (lib_extends_trans x y) (lib_extends_trans x e) a a' e0 e2); eauto.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *.
    unfold per_func_eq, raise_ext_per_fam, raise_ext_per in *; simpl in *; introv.
    pose proof (lib_per_cond _ eqa lib'1 (lib_extends_trans x y) (lib_extends_trans x e)) as e1.
    dup e0 as e2; apply e1 in e2; clear e1.
    eapply (lib_per_fam_cond _ eqb lib'1 (lib_extends_trans x y) (lib_extends_trans x e) a a' e2 e0); eauto.
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

Definition per_union_eq_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o))
           (eqb : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' x => per_union_eq_bar lib' (raise_lib_per eqa x) (raise_lib_per eqb x)).
  repeat introv.
  unfold per_union_eq_bar; split; intro h; exrepnd;
    exists bar; introv br ext; introv.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x0 y0; dands; spcast; eauto 3 with slow.
    { eapply (lib_per_cond _ eqa); eauto. }
    { eapply (lib_per_cond _ eqb); eauto. }

  - pose proof (h0 _ br _ ext x) as h0; simpl in *.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x0 y0; dands; spcast; eauto 3 with slow.
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
           (bar : @BarLib o lib)
           (eqa : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) => per_bar_eq (raise_bar bar x) (raise_lib_per eqa x)).
  repeat introv.
  unfold per_bar_eq; split; introv h br ext; introv; exrepnd.

  - unfold raise_lib_per, raise_ext_per; simpl in *; exrepnd.
    pose proof (h lib'0) as h; autodimp h hyp; simpl in *.
    { exists lib1; dands; eauto 4 with slow. }
    pose proof (h lib'1 ext x) as h; simpl in *.
    unfold raise_ext_per in h; exrepnd.

    exists bar'.
    introv br' e'; introv.
    pose proof (h0 _ br' _ e' x0) as h0; simpl in *.
    eapply (lib_per_cond _ eqa); eauto.

  - unfold raise_lib_per, raise_ext_per; simpl in *; exrepnd.
    pose proof (h lib'0) as h; autodimp h hyp; simpl in *.
    { exists lib1; dands; eauto 4 with slow. }
    pose proof (h lib'1 ext x) as h; simpl in *.
    unfold raise_ext_per in h; exrepnd.

    exists bar'.
    introv br' e'; introv.
    pose proof (h0 _ br' _ e' x0) as h0; simpl in *.
    eapply (lib_per_cond _ eqa); eauto.
Defined.

Definition per_bar_monotone_func {o} :
  forall (ts : cts(o)), type_monotone_func (per_bar ts).
Proof.
  introv per.
  unfold per_bar in *; exrepnd.
  exists (per_bar_eq_bar_lib_per lib bar eqa); introv.
  dands; simpl; eauto 3 with slow.
  exists (raise_bar bar x) (raise_lib_per eqa x).
  dands; tcsp; eauto 3 with slow.
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
  unfold per_set_eq_bar, per_set_eq; split; intro h; exrepnd;
    exists bar; introv br ext; introv.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *; exrepnd.
    unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ eqa lib'1 (lib_extends_trans x y) (lib_extends_trans x e)) as e1.
    dup e0 as e2; apply e1 in e2; clear e1.
    exists e2; auto.
    eapply eq_term_equals_preserves_inhabited;[|eauto].
    apply lib_per_fam_cond.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *; exrepnd.
    unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ eqa lib'1 (lib_extends_trans x y) (lib_extends_trans x e)) as e1.
    dup e0 as e2; apply e1 in e2; clear e1.
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
  unfold per_product_eq_bar, per_product_eq; split; intro h; exrepnd;
    exists bar; introv br ext; introv.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *; exrepnd.
    unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ eqa lib'1 (lib_extends_trans x y) (lib_extends_trans x e)) as e1.
    dup e0 as e2; apply e1 in e2; clear e1.
    exists a a' b b' e2; dands; auto.
    eapply (lib_per_fam_cond _ eqb lib'1 (lib_extends_trans x y) (lib_extends_trans x e) a a' e2 e0); eauto.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *; exrepnd.
    unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ eqa lib'1 (lib_extends_trans x y) (lib_extends_trans x e)) as e1.
    dup e0 as e2; apply e1 in e2; clear e1.
    exists a a' b b' e2; dands; auto.
    eapply (lib_per_fam_cond _ eqb lib'1 (lib_extends_trans x y) (lib_extends_trans x e) a a' e0 e2); eauto.
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
  unfold eq_per_eq_bar, eq_per_eq; split; introv h; exrepnd; exists bar; introv br ext; introv.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *; repnd; dands; auto.
    eapply (lib_per_cond _ eqa); eauto.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *; repnd; dands; auto.
    eapply (lib_per_cond _ eqa); eauto.
Defined.

Definition eq_per_union_bar_lib_per {o}
           (lib : @library o)
           (eqa : lib-per(lib,o))
           (eqb : lib-per(lib,o)) : lib-per(lib,o).
Proof.
  exists (fun lib' x => eq_per_union_bar lib' (eqa lib' x) (eqb lib' x)).
  repeat introv.
  unfold eq_per_union_bar; split; intro h; exrepnd;
    exists bar; introv br ext; introv.

  - pose proof (h0 _ br _ ext) as h0; simpl in *.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x y0; dands; spcast; eauto 3 with slow.
    { eapply (lib_per_cond _ eqa); eauto. }
    { eapply (lib_per_cond _ eqb); eauto. }

  - pose proof (h0 _ br _ ext) as h0; simpl in *.
    unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
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
  repeat introv.
  unfold per_image_eq_bar; split; intro h; exrepnd;
    exists bar; introv br ext; introv.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *.
    eapply implies_eq_term_equals_eq_image_eq;[|eauto]; simpl.
    eapply lib_per_cond.

  - pose proof (h0 _ br _ ext x) as h0; simpl in *.
    eapply implies_eq_term_equals_eq_image_eq;[|eauto]; simpl.
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
  exists (per_bar_eq_bar_lib_per lib bar eqa); introv; simpl.
  dands; auto; eauto 3 with slow;[].
  exists (raise_bar bar x) (raise_lib_per eqa x).
  dands; tcsp;[].
  introv br xt; introv; simpl in *; exrepnd.
  eapply type_extensionality_univi;[apply (h0 lib1 br1 lib'1 (lib_extends_trans xt br2))|].
  introv; split; intro h; eauto.
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
