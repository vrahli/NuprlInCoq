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



Definition type_monotone_func {o} inh (ts : cts(o)) :=
  forall lib T1 T2 eq,
    ts lib T1 T2 eq
    -> exists (eq' : lib-per(inh,lib,o)),
      forall lib' x,
        ts lib' T1 T2 (eq' lib' x)
        # sub_per eq (eq' lib' x).

Lemma per_int_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_int inh ts).
Proof.
  introv per.
  unfold per_int in *; exrepnd.
  exists (equality_of_int_bar_lib_per inh lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_nat_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_nat inh ts).
Proof.
  introv per.
  unfold per_nat in *; exrepnd.
  exists (equality_of_nat_bar_lib_per inh lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_qnat_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_qnat inh ts).
Proof.
  introv per.
  unfold per_qnat in *; exrepnd.
  exists (equality_of_qnat_bar_lib_per inh lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_csname_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_csname inh ts).
Proof.
  introv per.
  unfold per_csname in *; exrepnd.
  exists (equality_of_csname_bar_lib_per inh lib n); introv; simpl.
  dands; spcast; eauto 3 with slow; exists n; dands; spcast; eauto 3 with slow.
Qed.

Lemma per_atom_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_atom inh ts).
Proof.
  introv per.
  unfold per_atom in *; exrepnd.
  exists (equality_of_atom_bar_lib_per inh lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_uatom_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_uatom inh ts).
Proof.
  introv per.
  unfold per_uatom in *; exrepnd.
  exists (equality_of_uatom_bar_lib_per inh lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_base_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_base inh ts).
Proof.
  introv per.
  unfold per_base in *; exrepnd.
  exists (per_base_eq_lib_per inh lib); introv; simpl.
  dands; spcast; eauto 3 with slow.
Qed.

Lemma per_approx_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_approx inh ts).
Proof.
  introv per.
  unfold per_approx in *; exrepnd.
  exists (per_approx_eq_bar_lib_per inh lib a b); introv; simpl.
  dands; spcast; eauto 3 with slow.
  exists a b c d; dands; spcast; eauto 3 with slow.
Qed.

Lemma per_cequiv_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_cequiv inh ts).
Proof.
  introv per.
  unfold per_cequiv in *; exrepnd.
  exists (per_cequiv_eq_bar_lib_per inh lib a b); introv; simpl.
  dands; spcast; eauto 3 with slow.
  exists a b c d; dands; spcast; eauto 3 with slow.
Qed.

Definition per_func_ext_eq_bar_lib_per {o}
           inh
           (lib : @library o)
           (eqa : lib-per(inh,lib,o))
           (eqb : lib-per-fam(inh,lib,eqa,o)) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' x => per_func_ext_eq inh lib' (raise_lib_per inh eqa x) (raise_lib_per_fam inh eqb x)).
  repeat introv.
  unfold per_func_ext_eq; split; intro h; exrepnd; eapply in_open_bar_ext_pres; eauto; clear h;
    introv h; simpl.

  - unfold per_func_eq, raise_ext_per_fam, raise_ext_per in *; simpl in *; introv.
    pose proof (lib_per_cond _ _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as z1.
    dup e1 as e2; apply z1 in e2; clear z1.
    eapply (lib_per_fam_cond _ _ eqb lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e) a a' e1 e2); eauto; apply h.

  - unfold per_func_eq, raise_ext_per_fam, raise_ext_per in *; simpl in *; introv.
    pose proof (lib_per_cond _ _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as z1.
    dup e1 as e2; apply z1 in e2; clear z1.
    eapply (lib_per_fam_cond _ _ eqb lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e) a a' e2 e1); eauto; apply h.
Defined.

Lemma per_func_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_func_ext inh ts).
Proof.
  introv per.
  unfold per_func_ext in *; exrepnd.

  exists (per_func_ext_eq_bar_lib_per inh lib eqa eqb); introv; simpl; dands; eauto 3 with slow.

  exists (raise_lib_per inh eqa x)
         (raise_lib_per_fam inh eqb x).
  dands; eauto 3 with slow.
Qed.

Definition per_qtime_eq_bar_lib_per {o}
           inh
           (lib : @library o)
           (eqa : lib-per(inh,lib,o)) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' x => per_qtime_eq_bar inh lib' (raise_lib_per inh eqa x)).
  repeat introv.
  unfold per_qtime_eq_bar; split; intro h; exrepnd;
    eapply in_open_bar_ext_pres; eauto; clear h; introv h.

  - unfold per_qtime_eq, raise_ext_per in *; simpl in *; introv; exrepnd.
    pose proof (lib_per_cond _ _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as e1.
    dup h1 as e2; apply e1 in e2; clear e1.
    exists x y0; dands; auto.

  - unfold per_qtime_eq, raise_ext_per in *; simpl in *; introv; exrepnd.
    pose proof (lib_per_cond _ _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as e1.
    dup h1 as e2; apply e1 in e2; clear e1.
    exists x y0; dands; auto.
Defined.

Lemma per_qtime_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_qtime inh ts).
Proof.
  introv per.
  unfold per_qtime in *; exrepnd.

  exists (per_qtime_eq_bar_lib_per inh lib eqa); introv; simpl; dands; eauto 3 with slow.

  exists (raise_lib_per inh eqa x) A B.
  dands; eauto 3 with slow.
Qed.

Definition per_union_eq_bar_lib_per {o}
           inh
           (lib : @library o)
           (eqa : lib-per(inh,lib,o))
           (eqb : lib-per(inh,lib,o)) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' x => per_union_eq_bar inh lib' (raise_lib_per inh eqa x) (raise_lib_per inh eqb x)).
  repeat introv.
  unfold per_union_eq_bar; split; intro h; exrepnd;
    eapply in_open_bar_ext_pres; eauto; clear h; introv q.

  - unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x y0; dands; spcast; eauto 3 with slow.
    { eapply (lib_per_cond _ _ eqa); eauto. }
    { eapply (lib_per_cond _ _ eqb); eauto. }

  - unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x y0; dands; spcast; eauto 3 with slow.
    { eapply (lib_per_cond _ _ eqa); eauto. }
    { eapply (lib_per_cond _ _ eqb); eauto. }
Defined.

Lemma per_union_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_union inh ts).
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
           inh
           (lib : @library o)
           (eqa : lib-per(inh,lib,o)) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' (x : lib_extends inh lib' lib) => per_bar_eq inh lib' (raise_lib_per inh eqa x)).
  repeat introv.
  unfold per_bar_eq; split; introv h;
    eapply in_open_bar_ext_pres; eauto; clear h; introv h; simpl in *;
      unfold raise_lib_per, raise_ext_per in *; simpl in *; exrepnd;
        eapply (lib_per_cond _ _ eqa); eauto.
Defined.

Definition per_bar_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_bar inh ts).
Proof.
  introv per.
  unfold per_bar in *; exrepnd.
  exists (per_bar_eq_bar_lib_per inh lib eqa); introv.
  dands; simpl; eauto 3 with slow.
  exists (raise_lib_per inh eqa x).
  dands; tcsp; eauto 3 with slow.
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ x) in per1; simpl in *; auto.
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
           inh
           (lib : @library o)
           (eqa : lib-per(inh,lib,o))
           (eqb : lib-per-fam(inh,lib,eqa,o)) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' x => per_set_eq_bar inh lib' (raise_lib_per inh eqa x) (raise_lib_per_fam inh eqb x)).
  repeat introv.
  unfold per_set_eq_bar, per_set_eq; split; intro h;
    eapply in_open_bar_ext_pres; eauto; clear h; introv q; exrepnd.

  - unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as z.
    dup e1 as e2; apply z in e2; clear z.
    exists e2; auto.
    eapply eq_term_equals_preserves_inhabited;[|eauto].
    apply lib_per_fam_cond.

  - unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as z.
    dup e1 as e2; apply z in e2; clear z.
    exists e2; auto.
    eapply eq_term_equals_preserves_inhabited;[|eauto].
    apply lib_per_fam_cond.
Defined.

Lemma per_set_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_set inh ts).
Proof.
  introv per.
  unfold per_set in *; exrepnd.

  exists (per_set_eq_bar_lib_per inh lib eqa eqb).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists (raise_lib_per inh eqa x)
         (raise_lib_per_fam inh eqb x).
  dands; eauto 3 with slow.
Qed.

Definition per_product_eq_bar_lib_per {o}
           inh
           (lib : @library o)
           (eqa : lib-per(inh,lib,o))
           (eqb : lib-per-fam(inh,lib,eqa,o)) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' x => per_product_eq_bar inh lib' (raise_lib_per inh eqa x) (raise_lib_per_fam inh eqb x)).
  repeat introv.
  unfold per_product_eq_bar, per_product_eq; split; intro h;
    eapply in_open_bar_ext_pres; eauto; clear h; introv q; exrepnd.

  - unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as z.
    dup e1 as e2; apply z in e2; clear z.
    exists a a' b b' e2; dands; auto.
    eapply (lib_per_fam_cond _ _ eqb lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e) a a' e2 e1); eauto.

  - unfold raise_ext_per in *; simpl in *.
    pose proof (lib_per_cond _ _ eqa lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e)) as z.
    dup e1 as e2; apply z in e2; clear z.
    exists a a' b b' e2; dands; auto.
    eapply (lib_per_fam_cond _ _ eqb lib'0 (lib_extends_trans e0 y) (lib_extends_trans e0 e) a a' e1 e2); eauto.
Defined.

Lemma per_product_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_product_bar inh ts).
Proof.
  introv per.
  unfold per_product_bar in *; exrepnd.

  exists (per_product_eq_bar_lib_per inh lib eqa eqb).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists (raise_lib_per inh eqa x)
         (raise_lib_per_fam inh eqb x).
  dands; eauto 3 with slow.
Qed.

Definition eq_per_eq_bar_lib_per {o}
           inh
           (lib : @library o)
           (a1 a2 : @CTerm o)
           (eqa : lib-per(inh,lib,o)) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' (x : lib_extends inh lib' lib) => eq_per_eq_bar inh lib' a1 a2 (raise_lib_per inh eqa x)).
  repeat introv.
  unfold eq_per_eq_bar, eq_per_eq; split; introv h;
    eapply in_open_bar_ext_pres; eauto; clear h; introv q;
      repnd; dands; auto.

  - unfold raise_lib_per in *; eapply (lib_per_cond _ _ eqa); eauto.

  - unfold raise_lib_per in *; eapply (lib_per_cond _ _ eqa); eauto.
Defined.

Definition eq_per_union_bar_lib_per {o}
           inh
           (lib : @library o)
           (eqa : lib-per(inh,lib,o))
           (eqb : lib-per(inh,lib,o)) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' x => eq_per_union_bar inh lib' (eqa lib' x) (eqb lib' x)).
  repeat introv.
  unfold eq_per_union_bar; split; intro h; exrepnd;
    eapply in_open_bar_pres; eauto; clear h; introv xt q.

  - unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x y0; dands; spcast; eauto 3 with slow.
    { eapply (lib_per_cond _ _ eqa); eauto. }
    { eapply (lib_per_cond _ _ eqb); eauto. }

  - unfold per_union_eq, per_union_eq_L, per_union_eq_R, raise_ext_per in *; simpl in *; introv.
    repndors; exrepnd; spcast;[left|right]; exists x y0; dands; spcast; eauto 3 with slow.
    { eapply (lib_per_cond _ _ eqa); eauto. }
    { eapply (lib_per_cond _ _ eqb); eauto. }
Defined.

Lemma per_eq_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_eq inh ts).
Proof.
  introv per.
  unfold per_eq in *; exrepnd.

  exists (eq_per_eq_bar_lib_per inh lib a1 a2 eqa).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists A B a1 a2 b1 b2 (raise_lib_per inh eqa x).
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_eq_monotone_func : slow.

Lemma implies_eq_term_equals_eq_image_eq {o} :
  forall inh lib (eqa eqb : per(o)) f,
    (eqa <=2=> eqb)
    -> (per_image_eq inh lib eqa f) <=2=> (per_image_eq inh lib eqb f).
Proof.
  introv h; introv; split; intro p; induction p; auto.

  - eapply image_eq_cl; eauto.

  - eapply image_eq_eq; eauto; apply h; auto.

  - eapply image_eq_cl; eauto.

  - eapply image_eq_eq; eauto; apply h; auto.
Qed.

Definition per_image_eq_bar_lib_per {o}
           inh
           (lib : @library o)
           (eqa : lib-per(inh,lib,o))
           (f   : @CTerm o) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' x => per_image_eq_bar inh lib' (raise_lib_per inh eqa x) f).
  repeat introv.
  unfold per_image_eq_bar; split; intro h; exrepnd;
    eapply in_open_bar_ext_pres; eauto; clear h; introv q.

  - eapply implies_eq_term_equals_eq_image_eq;[|eauto]; simpl.
    eapply lib_per_cond.

  - eapply implies_eq_term_equals_eq_image_eq;[|eauto]; simpl.
    eapply lib_per_cond.
Defined.

Lemma per_image_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_image inh ts).
Proof.
  introv per.
  unfold per_image in *; exrepnd.

  exists (per_image_eq_bar_lib_per inh lib eqa f1).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists (raise_lib_per inh eqa x) A1 A2 f1 f2.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_image_monotone_func : slow.

Lemma per_union_monotone_func {o} :
  forall inh (ts : cts(o)), type_monotone_func inh (per_union inh ts).
Proof.
  introv per.
  unfold per_union in *; exrepnd.

  exists (per_union_eq_bar_lib_per inh lib eqa eqb).
  introv; simpl in *.
  dands; eauto 3 with slow;[].

  exists (raise_lib_per inh eqa x) (raise_lib_per inh eqb x) A1 A2 B1 B2.
  dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve per_union_monotone_func : slow.

Lemma close_monotone_func {o} :
  forall inh (ts : cts(o)),
    type_monotone_func inh ts
    -> type_monotone_func inh (close inh ts).
Proof.
  introv m cl.
  close_cases (induction cl using @close_ind') Case; introv.

  - Case "CL_init".
    pose proof (m lib T T' eq) as h; repeat (autodimp h hyp).
    exrepnd.
    exists eq'; introv.
    pose proof (h0 _ x) as h0; repnd; dands; auto.

  - Case "CL_bar".
    pose proof (per_bar_monotone_func inh (close inh ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_int".
    pose proof (per_int_monotone_func inh ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_nat".
    pose proof (per_nat_monotone_func inh ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_qnat".
    pose proof (per_qnat_monotone_func inh ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_csname".
    pose proof (per_csname_monotone_func inh ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_atom".
    pose proof (per_atom_monotone_func inh ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_uatom".
    pose proof (per_uatom_monotone_func inh ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_base".
    pose proof (per_base_monotone_func inh ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_approx".
    pose proof (per_approx_monotone_func inh ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_cequiv".
    pose proof (per_cequiv_monotone_func inh ts lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_eq".
    pose proof (per_eq_monotone_func inh (close inh ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_qtime".
    pose proof (per_qtime_monotone_func inh (close inh ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_func".
    pose proof (per_func_monotone_func inh (close inh ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_union".
    pose proof (per_union_monotone_func inh (close inh ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_image".
    pose proof (per_image_monotone_func inh (close inh ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_set".
    pose proof (per_set_monotone_func inh (close inh ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.

  - Case "CL_product".
    pose proof (per_product_monotone_func inh (close inh ts) lib T T' eq) as q.
    repeat (autodimp q hyp).
    exrepnd; exists eq'; introv; pose proof (q0 _ x) as q0;
      repnd; dands; eauto 3 with slow.
Qed.

Definition univi_eq_lib_per {o}
           inh (uni : cts(o))
           (lib : @library o)
           (i : nat) : lib-per(inh,lib,o).
Proof.
  exists (fun lib' (x : lib_extends inh lib' lib) => univi_eq i inh uni lib').
  introv x y; introv; tcsp.
Defined.

Lemma univi_monotone_func_implies_univi_bar_monotone_func {o} :
  forall inh uni i,
    @type_monotone_func o inh (univi i inh uni)
    -> @type_monotone_func o inh (univi_bar i inh uni).
Proof.
  introv mon h.
  unfold univi_bar, per_bar in *; exrepnd.
  exists (per_bar_eq_bar_lib_per inh lib eqa); introv; simpl.
  dands; auto; eauto 3 with slow;[].
  exists (raise_lib_per inh eqa x).
  dands; tcsp;[].
  apply (lib_extends_preserves_in_open_bar_ext _ _ _ _ x) in h1; simpl in *; auto.
Qed.
Hint Resolve univi_monotone_func_implies_univi_bar_monotone_func : slow.

Lemma univi_monotone_func {o} :
  forall inh uni i,
    @type_monotone_func o inh (univi i inh uni).
Proof.
  induction i as [? ind] using comp_ind_type.
  introv h.
  allrw @univi_exists_iff; exrepnd.
  exists (univi_eq_lib_per inh uni lib j); introv.
  allrw @univi_exists_iff.
  dands; simpl.

  { exists j; dands; tcsp; spcast; eauto 3 with slow. }

  { introv h.
    apply h0 in h; clear h0.
    unfold univi_eq, close_ex_eq in *; exrepnd.

    pose proof (@close_monotone o inh (univi_bar j inh uni)) as q.
    repeat (autodimp q hyp); eauto 3 with slow;[].
    pose proof (q lib lib' a b eqa) as q.
    repeat (autodimp q hyp); exrepnd.
    exists eq'; dands; auto. }
Qed.
Hint Resolve univi_monotone_func : slow.

Lemma univi_bar_monotone_func {o} :
  forall inh uni i,
    @type_monotone_func o inh (univi_bar i inh uni).
Proof.
  introv; eauto 3 with slow.
Qed.
Hint Resolve univi_bar_monotone_func : slow.

Lemma univ_monotone_func {o} : @type_monotone_func o nuprla_ex_inh univ.
Proof.
  introv u.
  unfold univ in *; exrepnd.
  apply per_bar_monotone_func in u; exrepnd.
  exists eq'; auto.
Qed.
Hint Resolve univ_monotone_func : slow.

Lemma univia_monotone_func {o} : @type_monotone_func o nuprla_ex_inh univia.
Proof.
  introv u; unfold univia in *.
  apply per_bar_monotone_func in u; exrepnd.
  exists eq'; dands; introv; pose proof (u0 _ x) as u0; repnd; dands; tcsp.
Qed.
Hint Resolve univia_monotone_func : slow.

Lemma nuprl_monotone_func {o} : @type_monotone_func o nuprla_ex_inh nuprl.
Proof.
  apply close_monotone_func; eauto 3 with slow.
Qed.
Hint Resolve nuprl_monotone_func : slow.

Lemma univia_i_monotone_func {o} :
  forall i, @type_monotone_func o nuprla_ex_inh (univia_i i).
Proof.
  introv u.
  apply per_bar_monotone_func in u; exrepnd.
  exists eq'; dands; introv; pose proof (u0 _ x) as u0; repnd; dands; tcsp.
Qed.
Hint Resolve univia_i_monotone_func : slow.

Lemma nuprli_monotone_func {o} :
  forall i, @type_monotone_func o nuprla_ex_inh (nuprli i).
Proof.
  introv u.
  unfold nuprli in *; exrepnd.
  pose proof (@close_monotone_func o nuprla_ex_inh (univia_i i)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve nuprli_monotone_func : slow.
