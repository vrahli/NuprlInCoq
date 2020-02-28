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


  Website: https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

 *)


Require Export library.


Definition CSLe (a b : cs_name) : Prop := string_le a b.
Definition CSLt (a b : cs_name) : Prop := string_lt a b.

Lemma CSLt_implies_CSLe :
  forall v1 v2, CSLt v1 v2 -> CSLe v1 v2.
Proof.
  induction v1; introv h; simpl in *; destruct v2; tcsp.
Qed.
Hint Resolve CSLt_implies_CSLe : cs.

Lemma CSLe_refl : forall v, CSLe v v.
Proof.
  induction v; simpl in *; introv; tcsp.
Qed.
Hint Resolve CSLe_refl : cs.

Lemma CSLt_dec :
  forall (a b : cs_name), {CSLt a b} + {~ CSLt a b}.
Proof.
  induction a; introv; destruct b; simpl in *; tcsp.
  destruct (lt_dec (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii a1)); tcsp.
  destruct (eq_nat_dec (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii a1)); tcsp.
  - destruct (IHa b) as [q|q]; tcsp.
    right; intro xx; repndors; tcsp.
  - right; intro xx; repndors; tcsp.
Defined.

Definition extend_cs (v : cs_name) : cs_name := String.append v "a".

Lemma CSLe_trans :
  forall v1 v2 v3, CSLe v1 v2 -> CSLe v2 v3 -> CSLe v1 v3.
Proof.
  induction v1; simpl in *; introv h1 h2; tcsp.
  destruct v2; simpl in *; tcsp.
  destruct v3; simpl in *; tcsp.
  repndors; repnd; tcsp; try (complete (left; omega)).
  right; dands; auto; try omega.
  eapply IHv1; eauto.
Qed.
Hint Resolve CSLe_trans : cs.

Lemma CSLt_trans :
  forall v1 v2 v3, CSLt v1 v2 -> CSLt v2 v3 -> CSLt v1 v3.
Proof.
  induction v1; simpl in *; introv h1 h2; tcsp.
  { destruct v2; simpl in *; tcsp.
    destruct v3; simpl in *; tcsp. }
  destruct v2; simpl in *; tcsp.
  destruct v3; simpl in *; tcsp.
  repndors; repnd; tcsp; try (complete (left; omega)).
  right; dands; auto; try omega.
  eapply IHv1; eauto.
Qed.
Hint Resolve CSLt_trans : cs.

Lemma CSLe_CSLt_trans :
  forall v1 v2 v3, CSLe v1 v2 -> CSLt v2 v3 -> CSLt v1 v3.
Proof.
  induction v1; simpl in *; introv h1 h2; tcsp.
  { destruct v2; simpl in *; tcsp.
    destruct v3; simpl in *; tcsp. }
  destruct v2; simpl in *; tcsp.
  destruct v3; simpl in *; tcsp.
  repndors; repnd; tcsp; try (complete (left; omega)).
  right; dands; auto; try omega.
  eapply IHv1; eauto.
Qed.
Hint Resolve CSLe_CSLt_trans : cs.

Lemma CSLe_extend_var : forall v, CSLe v (extend_cs v).
Proof.
  induction v; simpl; tcsp.
Qed.
Hint Resolve CSLe_extend_var : cs.

Lemma CSLt_extend_var : forall v, CSLt v (extend_cs v).
Proof.
  induction v; simpl; tcsp.
Qed.
Hint Resolve CSLt_extend_var : cs.

Fixpoint fresh_cs_aux (v : cs_name) (vars : list cs_name) : cs_name :=
  match vars with
    | [] => v
    | x :: xs =>
      if CSLt_dec v x then v
      else if String.string_dec v x
           then fresh_cs_aux (extend_cs v) xs
           else fresh_cs_aux v xs
  end.

Lemma fresh_cs_aux_le :
  forall vars v,
    CSLe v (fresh_cs_aux v vars).
Proof.
  induction vars; simpl; sp; eauto 2 with cs.
  destruct (CSLt_dec v a); eauto 2 with cs.
  destruct (String.string_dec v a); subst; auto.
  pose proof (IHvars (extend_cs a)) as q.
  eapply CSLe_trans;[|exact q]; eauto 2 with cs.
Qed.

Lemma not_CSLt_refl :
  forall v, ~ CSLt v v.
Proof.
  induction v; introv h; simpl in *; tcsp.
  repndors; repnd; tcsp; try omega.
Qed.

Lemma CSLe_implies_CSLt :
  forall v1 v2, v1 <> v2 -> CSLe v1 v2 -> CSLt v1 v2.
Proof.
  induction v1; introv h1 h2; simpl in *; destruct v2; tcsp.
  repndors; repnd; tcsp.
  right; dands; tcsp.
  apply IHv1; auto.
  introv xx; subst.
  apply eq_nat_of_ascii_implies in h0; subst; tcsp.
Qed.

Fixpoint insert_cs (v : cs_name) (vars : list cs_name) : list cs_name :=
  match vars with
  | [] => [v]
  | x :: xs =>
    if CSLt_dec x v then x :: insert_cs v xs
    else if String.string_dec x v then vars
         else v :: vars
  end.

Lemma insert_cs_in : forall v vars, LIn v (insert_cs v vars).
Proof.
  induction vars; simpl; sp.
  destruct (CSLt_dec a v); simpl; sp.
  destruct (String.string_dec a v); subst; simpl; sp.
Qed.
Hint Resolve insert_cs_in : cs.

Fixpoint sort_cs (vars : list cs_name) : list cs_name :=
  match vars with
    | [] => []
    | x :: xs => insert_cs x (sort_cs xs)
  end.

Inductive issorted_cs : list cs_name -> Type :=
| issorted_cs_nil : issorted_cs []
| issorted_cs_cons :
    forall v vs,
      (forall x, LIn x vs -> CSLe v x)
      -> issorted_cs vs
      -> issorted_cs (v :: vs).
Hint Constructors issorted_cs.

Lemma fresh_cs_aux_sorted_not_in :
  forall vars,
    issorted_cs vars
    -> forall n, ! LIn (fresh_cs_aux n vars) vars.
Proof.
  intros vars H.
  induction H; simpl; sp.

  - destruct (CSLt_dec n v); ginv; try subst v.

    + apply not_CSLt_refl in c0; tcsp.

    + destruct (String.string_dec n v); try subst n; tcsp.

      * clear n0.
        inversion e as [xx]; clear e.
        pose proof (fresh_cs_aux_le vs (extend_cs v)) as q.
        rewrite <- xx in q.
        pose proof (CSLt_extend_var v) as h.
        eapply CSLe_CSLt_trans in h;[|exact q].
        apply not_CSLt_refl in h; tcsp.

      * inversion e as [xx]; clear e.
        pose proof (fresh_cs_aux_le vs n) as q.
        rewrite <- xx in q; clear xx.
        destruct n0.
        apply CSLe_implies_CSLt; auto.

  - destruct (CSLt_dec n v); tcsp.

    + apply c in l.
      eapply CSLe_CSLt_trans in c0;[|exact l].
      apply not_CSLt_refl in c0; tcsp.

    + destruct (String.string_dec n v); subst; tcsp.
Qed.

Definition csx : cs_name := "x".

Definition fresh_cs (vars : list cs_name) : cs_name :=
  fresh_cs_aux csx (sort_cs vars).

Lemma in_insert_cs :
  forall v x vars,
    LIn v (insert_cs x vars)
    <=> (v = x [+] LIn v vars).
Proof.
  induction vars; simpl; split; intro h; repndors; subst; ginv; tcsp.
  - destruct (CSLt_dec a x); simpl in *; tcsp; repndors; subst; tcsp.
    + apply IHvars in h; tcsp.
    + destruct (String.string_dec a x); subst; simpl in *; tcsp.
  - destruct (CSLt_dec a x); simpl in *; tcsp.
    + right; apply IHvars; tcsp.
    + destruct (String.string_dec a x); subst; simpl in *; tcsp.
  - destruct (CSLt_dec v x); simpl in *; tcsp.
    destruct (String.string_dec v x); simpl in *; tcsp.
  - destruct (CSLt_dec a x); simpl in *; tcsp.
    + right; apply IHvars; tcsp.
    + destruct (String.string_dec a x); subst; simpl in *; tcsp.
Qed.

Lemma sort_cs_eqset :
  forall vars,
    eqset vars (sort_cs vars).
Proof.
  induction vars; simpl; sp.
  introv; simpl.
  rw in_insert_cs.
  rw IHvars; split; intro h; repndors; tcsp.
Qed.

Lemma not_CSLt_implies_CSLe :
  forall v1 v2, ~ CSLt v1 v2 -> CSLe v2 v1.
Proof.
  induction v1; simpl in *; introv; destruct v2; intro h; tcsp.
  apply not_or in h; repnd; simpl.
  apply Decidable.not_and in h; auto;
    [|destruct (eq_nat_dec (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii a0)); tcsp].
  repndors; tcsp.
  - left; omega.
  - destruct (eq_nat_dec (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii a0)); tcsp.
    left; omega.
Qed.

Lemma sort_cs_issorted_cs :
  forall vars,
    issorted_cs (sort_cs vars).
Proof.
  induction vars; simpl; sp.
  induction IHvars; simpl; sp.
  { constructor; simpl; sp. }
  destruct (CSLt_dec v a).
  { constructor; simpl; tcsp; introv i.
    allrw in_insert_cs; repndors; subst; tcsp; eauto 3 with cs. }
  destruct (String.string_dec v a); subst; simpl in *; tcsp.
  constructor; auto.
  introv i; simpl in *; repndors; subst; tcsp.
  { apply not_CSLt_implies_CSLe in n; auto. }
  { apply c in i; clear c.
    apply not_CSLt_implies_CSLe in n; auto.
    eapply CSLe_trans; eauto. }
Qed.
Hint Resolve sort_cs_issorted_cs : cs.

Lemma fresh_cs_not_in :
  forall vars,
    ! LIn (fresh_cs vars) vars.
Proof.
  unfold fresh_cs; introv h.
  apply sort_cs_eqset in h.
  apply fresh_cs_aux_sorted_not_in in h; eauto 3 with cs.
Qed.

Lemma ex_fresh_cs :
  forall vars, {v : cs_name $ !LIn v vars}.
Proof.
  introv.
  exists (fresh_cs vars); apply fresh_cs_not_in.
Qed.

Definition choice_seq_names_in_entry {o} (e : @library_entry o) : list choice_sequence_name :=
  match e with
  | lib_cs n l => [n]
  | lib_abs _ _ _ _ => []
  end.

Fixpoint choice_seq_names_in_lib {o} (lib : @plibrary o) : list choice_sequence_name :=
  match lib with
  | [] => []
  | e :: es =>
    (choice_seq_names_in_entry e) ++ (choice_seq_names_in_lib es)
  end.

Definition fresh_cs_in_lib {o} (lib : @plibrary o) : cs_name :=
  fresh_cs (map csn_name (choice_seq_names_in_lib lib)).
