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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export list.
Require Export Eqdep_dec.


(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing &  $\times$ #×# *)

(* ------ variables ------ *)

(** We define our variables exactly as that in Software Foundations
  %  \footnote{\url{http://www.cis.upenn.edu/~bcpierce/sf/}} %.
  Basically, variables are wrappers around numbers.
  We could have defined them as wrappers around any (countably) infinite
  type with decidable equality.
 *)

Definition Var : Set := String.string.

Definition var0 : Var := "0".
Definition varx : Var := "x".

Definition extend_var (v : Var) : Var := String.append v "a".

Lemma VarDeq : Deq Var.
Proof.
  introv.
  destruct (String.string_dec x y); subst; auto.
Defined.

Definition VarBeq (a b : Var) : bool := if VarDeq a b then true else false.

Lemma VarBeq_refl : forall v, VarBeq v v = true.
Proof.
  introv.
  unfold VarBeq.
  destruct (VarDeq v v) as [d|d]; auto.
Defined.
Hint Rewrite VarBeq_refl : var.

Lemma VarBeq_true_implies : forall v1 v2, VarBeq v1 v2 = true -> v1 = v2.
Proof.
  introv h.
  unfold VarBeq in h.
  destruct (VarDeq v1 v2) as [d|d]; auto; ginv.
Defined.

Lemma VarBeq_false_implies : forall v1 v2, VarBeq v1 v2 = false -> v1 <> v2.
Proof.
  introv h.
  unfold VarBeq in h.
  destruct (VarDeq v1 v2) as [d|d]; auto; ginv.
Defined.

Lemma VarBeq_sym : forall v1 v2, VarBeq v1 v2 = VarBeq v2 v1.
Proof.
  introv.
  unfold VarBeq.
  destruct (VarDeq v1 v2) as [d1|d1]; destruct (VarDeq v2 v1) as [d2|d2]; tcsp.
Defined.

Fixpoint string_lt (a b : String.string) :=
  match a, b with
  | String.EmptyString, String.String _ _  => True
  | String.String x xs, String.String y ys =>
    Ascii.nat_of_ascii x < Ascii.nat_of_ascii y
    \/
    (Ascii.nat_of_ascii x = Ascii.nat_of_ascii y
     /\
     string_lt xs ys)
  | _, _ => False
  end.

Fixpoint string_le (a b : String.string) :=
  match a, b with
  | String.EmptyString, _  => True
  | String.String x xs, String.String y ys =>
    Ascii.nat_of_ascii x < Ascii.nat_of_ascii y
    \/
    (Ascii.nat_of_ascii x = Ascii.nat_of_ascii y
     /\
     string_le xs ys)
  | _, _ => False
  end.

Definition VarLe (a b : Var) : Prop := string_le a b.
Definition VarLt (a b : Var) : Prop := string_lt a b.

Lemma VarLt_implies_VarLe :
  forall v1 v2, VarLt v1 v2 -> VarLe v1 v2.
Proof.
  induction v1; introv h; simpl in *; destruct v2; tcsp.
Qed.
Hint Resolve VarLt_implies_VarLe : var.

Lemma VarLe_refl : forall v, VarLe v v.
Proof.
  induction v; simpl in *; introv; tcsp.
Qed.
Hint Resolve VarLe_refl : var.

Lemma eq_nat_of_ascii_implies :
  forall a1 a2, Ascii.nat_of_ascii a1 = Ascii.nat_of_ascii a2 -> a1 = a2.
Proof.
  introv h.
  pose proof (Ascii.ascii_nat_embedding a1) as h1.
  pose proof (Ascii.ascii_nat_embedding a2) as h2.
  rewrite h in h1.
  rewrite h1 in h2; auto.
Qed.

Lemma VarLe_implies_VarLt :
  forall v1 v2, v1 <> v2 -> VarLe v1 v2 -> VarLt v1 v2.
Proof.
  induction v1; introv h1 h2; simpl in *; destruct v2; tcsp.
  repndors; repnd; tcsp.
  right; dands; tcsp.
  apply IHv1; auto.
  introv xx; subst.
  apply eq_nat_of_ascii_implies in h0; subst; tcsp.
Qed.

Lemma VarLe_iff_VarLt :
  forall v1 v2, VarLe v1 v2 <-> (VarLt v1 v2 \/ v1 = v2).
Proof.
  induction v1; split; intro h; repnd; simpl in *; destruct v2; tcsp.
  - repndors; repnd; tcsp.
    apply eq_nat_of_ascii_implies in h0; subst.
    apply IHv1 in h; repndors; subst; tcsp.
  - repndors; tcsp.
    inversion h.
  - repndors; repnd; tcsp.
    + apply eq_nat_of_ascii_implies in h0; subst.
      right; dands; tcsp; eauto 2 with var.
    + inversion h; subst; clear h; tcsp.
      right; dands; eauto 2 with var.
Qed.

Lemma not_VarLt_refl :
  forall v, ~ VarLt v v.
Proof.
  induction v; introv h; simpl in *; tcsp.
  repndors; repnd; tcsp; try omega.
Qed.

Lemma VarLt_dec :
  forall (a b : Var), {VarLt a b} + {~ VarLt a b}.
Proof.
  induction a; introv; destruct b; simpl in *; tcsp.
  destruct (lt_dec (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii a1)); tcsp.
  destruct (eq_nat_dec (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii a1)); tcsp.
  - destruct (IHa b) as [q|q]; tcsp.
    right; intro xx; repndors; tcsp.
  - right; intro xx; repndors; tcsp.
Defined.

Lemma VarLe_dec :
  forall (a b : Var), {VarLe a b} + {~ VarLe a b}.
Proof.
  induction a; introv; destruct b; simpl in *; tcsp.
  destruct (lt_dec (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii a1)); tcsp.
  destruct (eq_nat_dec (Ascii.nat_of_ascii a) (Ascii.nat_of_ascii a1)); tcsp.
  - destruct (IHa b) as [q|q]; tcsp.
    right; intro xx; repndors; tcsp.
  - right; intro xx; repndors; tcsp.
Defined.

Lemma not_VarLt_implies_VarLe :
  forall v1 v2, ~ VarLt v1 v2 -> VarLe v2 v1.
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

Lemma VarLe_trans :
  forall v1 v2 v3, VarLe v1 v2 -> VarLe v2 v3 -> VarLe v1 v3.
Proof.
  induction v1; simpl in *; introv h1 h2; tcsp.
  destruct v2; simpl in *; tcsp.
  destruct v3; simpl in *; tcsp.
  repndors; repnd; tcsp; try (complete (left; omega)).
  right; dands; auto; try omega.
  eapply IHv1; eauto.
Qed.
Hint Resolve VarLe_trans : var.

Lemma VarLt_trans :
  forall v1 v2 v3, VarLt v1 v2 -> VarLt v2 v3 -> VarLt v1 v3.
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
Hint Resolve VarLt_trans : var.

Lemma VarLe_VarLt_trans :
  forall v1 v2 v3, VarLe v1 v2 -> VarLt v2 v3 -> VarLt v1 v3.
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
Hint Resolve VarLe_VarLt_trans : var.

Lemma VarLe_extend_var : forall v, VarLe v (extend_var v).
Proof.
  induction v; simpl; tcsp.
Qed.
Hint Resolve VarLe_extend_var : var.

Lemma VarLt_extend_var : forall v, VarLt v (extend_var v).
Proof.
  induction v; simpl; tcsp.
Qed.
Hint Resolve VarLt_extend_var : var.

Inductive NVar : Set :=
| nvar : Var -> NVar.

Theorem eq_var_dec: forall (x y : NVar), {x = y} + {x <> y}.
Proof.
  introv.
  destruct x, y.
  destruct (VarDeq v v0); subst; tcsp.
  right; intro xx; ginv; tcsp.
Defined.

Theorem deq_nvar: Deq NVar.
Proof.
  exact eq_var_dec.
Defined.
Hint Immediate deq_nvar.
Hint Resolve deq_nvar : Deq.

(** %\noindent% Here are some examples of variables.

 *)

(* begin hide *)

Definition nvara := nvar "a".
Definition nvarb := nvar "b".
Definition nvarc := nvar "c".
Definition nvard := nvar "d".
Definition nvare := nvar "e".
Definition nvarf := nvar "f".
Definition nvarg := nvar "g".
Definition nvarh := nvar "h".
Definition nvari := nvar "i".
Definition nvarj := nvar "j".
Definition nvark := nvar "k".
Definition nvarl := nvar "l".
Definition nvarm := nvar "m".
Definition nvarn := nvar "n".
Definition nvaro := nvar "o".
Definition nvarp := nvar "p".
Definition nvarq := nvar "q".
Definition nvarr := nvar "r".
Definition nvars := nvar "s".
Definition nvart := nvar "t".
Definition nvaru := nvar "u".
Definition nvarv := nvar "v".
Definition nvarw := nvar "w".
Definition nvarx := nvar "x".
Definition nvary := nvar "y".
Definition nvarz := nvar "z".

Definition nvarA := nvar "A".
Definition nvarB := nvar "B".
Definition nvarC := nvar "C".
Definition nvarD := nvar "D".
Definition nvarE := nvar "E".
Definition nvarF := nvar "F".
Definition nvarG := nvar "G".
Definition nvarH := nvar "H".
Definition nvarI := nvar "I".
Definition nvarJ := nvar "J".
Definition nvarK := nvar "K".
Definition nvarL := nvar "L".
Definition nvarM := nvar "M".
Definition nvarN := nvar "N".
Definition nvarO := nvar "O".
Definition nvarP := nvar "P".
Definition nvarQ := nvar "Q".
Definition nvarR := nvar "R".
Definition nvarS := nvar "S".
Definition nvarT := nvar "T".
Definition nvarU := nvar "U".
Definition nvarV := nvar "V".
Definition nvarW := nvar "W".
Definition nvarX := nvar "X".
Definition nvarY := nvar "Y".
Definition nvarZ := nvar "Z".

Definition beq_var (v1 v2 : NVar) : bool :=
  match v1, v2 with
  | nvar n1, nvar n2 => VarBeq n1 n2
  end.

Definition le_var v1 v2 :=
  match v1, v2 with
  | nvar n1, nvar n2 => VarLe n1 n2
  end.

Definition lt_var v1 v2 :=
  match v1, v2 with
  | nvar n1, nvar n2 => VarLt n1 n2
  end.

(* After we "wrap" numbers as identifiers in this way, it is
    convenient to recapitulate a few properties of numbers as
    analogous properties of identifiers, so that we can work with
    identifiers in definitions and proofs abstractly, without
    unwrapping them to expose the underlying numbers.  Since all we
    need to know about identifiers is whether they are the same or
    different, just a few basic facts are all we need. *)

Theorem beq_var_refl : forall X,
  true = beq_var X X.
Proof.
  introv.
  destruct X; simpl; autorewrite with var; auto.
Qed.

Theorem beq_var_refl2 : forall X, beq_var X X = true.
Proof.
  introv; symmetry; apply beq_var_refl.
Qed.
Hint Rewrite beq_var_refl2 : var.

Theorem beq_var_eq : forall i1 i2,
  true = beq_var i1 i2 -> i1 = i2.
Proof.
 introv h.
 destruct i1, i2; simpl in *.
 symmetry in h; apply VarBeq_true_implies in h; subst; auto.
Defined.

(* same as beq_var_eq *)
Theorem beq_var_true :
  forall i1 i2,
    true = beq_var i1 i2 -> i1 = i2.
Proof.
  apply beq_var_eq.
Qed.

Theorem beq_var_false_not_eq : forall i1 i2,
  beq_var i1 i2 = false -> i1 <> i2.
Proof.
 introv h q; subst.
 destruct i2; simpl in *.
 apply VarBeq_false_implies in h; tcsp.
Defined.

(* same as beq_var_false_not_eq *)
Theorem beq_var_false :
  forall i1 i2,
    false = beq_var i1 i2 -> i1 <> i2.
Proof.
  sp; symmetry in H.
  apply beq_var_false_not_eq in H; sp.
Qed.

Theorem not_eq_beq_var_false : forall i1 i2,
  i1 <> i2 -> beq_var i1 i2 = false.
Proof.
  introv h; destruct i1, i2; simpl in *.
  remember (VarBeq v v0) as b; symmetry in Heqb; destruct b; auto.
  apply VarBeq_true_implies in Heqb; subst; tcsp.
Qed.

Theorem beq_var_sym: forall i1 i2,
  beq_var i1 i2 = beq_var i2 i1.
Proof.
  introv; destruct i1, i2; simpl in *.
  rewrite VarBeq_sym; auto.
Qed.

Lemma true_eq_nvar : forall t : NVar, t = t <=> True.
Proof. sp; split; sp. Qed.

(* end hide *)

(** We need decidable equality on variables so that
  many useful relations on our future definitions of Terms, like equality,
  alpha equality, etc. will be decidable.
  Also our substitution function will need this decidable equality to
  decide whether it needs to come up with fresh variables.
  Decidable equality on variables is a  straightforward consequence
  of decidable equality on the underlying type.

*)

Lemma in_nvar_list_dec: forall (x : NVar) l, LIn x l [+] ! LIn x l.
Proof.
  induction l; simpl; sp. try (complete (right; sp)).
  destruct (eq_var_dec a x); subst; sp.
  right; sp.
Defined.



(** boolean membership of variable in a list of variables *)
Definition memvar := memberb eq_var_dec.

Lemma assert_memvar :
  forall v vars,
    assert (memvar v vars) <=> LIn v vars.
Proof.
  unfold memvar; intros.
  apply assert_memberb.
Qed.

Lemma memvar_app :
  forall v vs1 vs2,
    memvar v (vs1 ++ vs2) = memvar v vs1 || memvar v vs2.
Proof.
  unfold memvar; sp.
  apply memberb_app.
Qed.

Lemma memvar_singleton :
  forall a b,
    memvar a [b] = beq_var a b.
Proof.
  sp.
  unfold memvar; simpl.
  destruct (eq_var_dec b a); subst; sp.
  apply beq_var_refl.
  symmetry; apply not_eq_beq_var_false; sp.
Qed.


(** removes the elements of l1 from l2 *)
Definition remove_nvars (l1 l2 : list NVar) :=
 @diff _ eq_var_dec l1 l2.

Definition remove_nvar (l : list NVar) (v : NVar) :=
 remove_nvars [v] l.

Lemma null_remove_nvars :
  forall l1 l2,
    null (remove_nvars l1 l2) <=> forall x, LIn x l2 -> LIn x l1.
Proof.
  unfold remove_nvars.
  apply null_diff.
Qed.

Lemma in_remove_nvars :
  forall x l1 l2,
    LIn x (remove_nvars l1 l2) <=> (LIn x l2 # ! LIn x l1).
Proof.
  intros; apply in_diff.
Qed.

Lemma in_remove_nvar :
  forall x v l,
    LIn x (remove_nvar l v) <=> (LIn x l # x <> v).
Proof.
  intros; unfold remove_nvar; trw in_remove_nvars; simpl; split; sp.
Qed.

Lemma remove_nvar_nil : forall v, remove_nvar [] v = [].
Proof.
  sp.
Qed.
Hint Rewrite remove_nvar_nil : var.

Lemma remove_nvars_unchanged :
  forall l1 l2,
    disjoint l2 l1 <=> remove_nvars l1 l2 = l2.
Proof.
  unfold remove_nvars.
  apply disjoint_iff_diff.
Qed.

Lemma remove_nvars_nil_l : forall l, remove_nvars [] l = l.
Proof.
  unfold remove_nvars; simpl; auto.
Qed.

Hint Rewrite remove_nvars_nil_l.

(* same as remove_nvars_nil_l *)
Lemma remove_var_nil : forall l, remove_nvars [] l = l.
Proof.
  sp; autorewrite with core.
Qed.

Lemma remove_nvars_nil_r : forall l, remove_nvars l [] = [].
Proof.
  unfold remove_nvars. apply diff_nil.
Qed.

Hint Rewrite remove_nvars_nil_r.

Lemma remove_nvars_app_r :
  forall l1 l2 l3,
    remove_nvars l1 (l2 ++ l3) = remove_nvars l1 l2 ++ remove_nvars l1 l3.
Proof.
  unfold remove_nvars.
  apply diff_app_r.
Qed.

Lemma remove_nvars_app_l :
  forall l1 l2 l3,
     remove_nvars l1 (remove_nvars l2 l3) = remove_nvars (l1 ++ l2) l3.
Proof.
  unfold remove_nvars.
  apply diff_app_l.
Qed.

Lemma remove_nvars_flat_map :
  forall T,
  forall f : T -> list NVar,
  forall l : list T,
  forall vars : list NVar,
   remove_nvars vars (flat_map f l) =
   flat_map (compose (fun vs => remove_nvars vars vs) f) l.
Proof.
  induction l; simpl; sp.
  apply remove_nvars_nil_r.
  rewrite remove_nvars_app_r.
  rewrite IHl.
  unfold compose.
  auto.
Qed.

Lemma remove_nvars_comm :
  forall l1 l2 l3,
    remove_nvars l1 (remove_nvars l2 l3) = remove_nvars l2 (remove_nvars l1 l3).
Proof.
  unfold remove_nvars; apply diff_comm.
Qed.

Lemma remove_nvars_dup :
  forall l1 l2 x l3,
    LIn x l1 -> remove_nvars (l1 ++ l2) l3 = remove_nvars (l1 ++ x :: l2) l3.
Proof.
  unfold remove_nvars; intros.
  apply diff_dup2; auto.
Qed.

Lemma remove_nvars_move :
  forall l1 l2 l3 x,
    remove_nvars (l1 ++ x :: l2) l3 = remove_nvars (x :: l1 ++ l2) l3.
Proof.
  unfold remove_nvars; intros.
  apply diff_move; auto.
Qed.

Lemma remove_nvars_cons :
  forall v l1 l2,
    remove_nvars (v :: l1) l2 = remove_nvars l1 (remove eq_var_dec v l2).
Proof.
  unfold remove_nvars; simpl; auto.
Qed.

Lemma remove_nvars_cons_l_weak :
  forall v vs vars,
    !LIn v vars
    -> remove_nvars (v :: vs) vars
       = remove_nvars vs vars.
Proof.
  intros; unfold remove_nvars.
  rewrite diff_cons_r_ni; auto.
Qed.

Lemma remove_nvars_cons_r :
  forall l v vars,
    remove_nvars l (v :: vars)
    = if memvar v l then remove_nvars l vars
      else v :: remove_nvars l vars.
Proof.
  intros; unfold remove_nvars.
  rewrite diff_cons_r; auto.
Qed.

Lemma remove_nvar_cons :
  forall v x xs,
    remove_nvar (x :: xs) v
    = if beq_var v x then remove_nvar xs v
      else x :: remove_nvar xs v.
Proof.
  unfold remove_nvar; sp.
  rewrite remove_nvars_cons_r; simpl.
  rewrite memvar_singleton.
  rewrite beq_var_sym; sp.
Qed.

Lemma remove_nvar_cons2 :
  forall v x xs,
    remove_nvar (x :: xs) v
    = if deq_nvar v x then remove_nvar xs v
      else x :: remove_nvar xs v.
Proof.
  unfold remove_nvar; sp.
Qed.

Lemma disjoint_remove_nvars_l :
  forall l1 l2 l3,
    disjoint (remove_nvars l1 l2) l3 <=> disjoint l2 (remove_nvars l1 l3).
Proof.
  unfold remove_nvars; intros.
  apply disjoint_diff_l.
Qed.

Lemma remove_nvars_eq :
  forall l,
    remove_nvars l l = [].
Proof.
  unfold remove_nvars; sp.
  rw <- null_iff_nil.
  apply null_diff; sp.
Qed.


(** equals variable sets *)
Definition eq_vars := eqsetb eq_var_dec.

Definition eqvars (vs1 vs2 : list NVar) :=
  assert (eq_vars vs1 vs2).

Lemma eqvars_proof_irrelevance :
  forall vs1 vs2,
  forall x y : eqvars vs1 vs2,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : eqvars ?vs1 ?vs2 , H2 : eqvars ?vs1 ?vs2 |- _ ] =>
    pose proof (eqvars_proof_irrelevance vs1 vs2 H2 H1) as h; subst
end : pi.

Lemma assert_eq_vars :
  forall vs1 vs2,
    assert (eq_vars vs1 vs2) <=> forall x, LIn x vs1 <=> LIn x vs2.
Proof.
  sp; unfold eq_vars.
  trw assert_eqsetb; sp.
Qed.

Lemma eqvars_prop :
  forall vs1 vs2,
    eqvars vs1 vs2 <=> forall x, LIn x vs1 <=> LIn x vs2.
Proof.
  sp; unfold eqvars, eq_vars.
  trw assert_eqsetb; sp.
Qed.

Lemma eqvars_sym :
  forall s1 s2, eqvars s1 s2 <=> eqvars s2 s1.
Proof.
  introv.
  repeat (rw eqvars_prop); split; intro k; introv.
  rw k; sp.
  rw <- k; sp.
Qed.

Lemma eqvars_disjoint :
  forall s1 s2 s3,
    eqvars s1 s2
    -> disjoint s1 s3
    -> disjoint s2 s3.
Proof.
  introv eqv disj.
  unfold disjoint.
  unfold disjoint in disj.
  introv i.
  rw eqvars_prop in eqv.
  apply eqv in i.
  apply disj in i; sp.
Qed.

Lemma eqvars_cons_l_iff :
  forall v vs1 vs2,
    eqvars (v :: vs1) vs2
    <=> (LIn v vs2 # eqvars (remove_nvar vs1 v) (remove_nvar vs2 v)).
Proof.
  sp; repeat (rw eqvars_prop).
  split; intro i; sp; allrw in_remove_nvar; allsimpl.
  rw <- i; sp.
  split; sp.
  rw <- i; sp.
  apply_in_hyp p; sp; subst; sp.
  split; sp; subst; sp.
  destruct (eq_var_dec v x); subst; sp.
  gen_some x; allrw in_remove_nvar.
  discover; sp.
  destruct (eq_var_dec v x); subst; sp.
  gen_some x; allrw in_remove_nvar.
  discover; sp.
Qed.

Lemma eqvars_remove_nvar :
  forall vars1 vars2 v,
    eqvars vars1 vars2
    -> eqvars (remove_nvar vars1 v) (remove_nvar vars2 v).
Proof.
  introv.
  trw eqvars_prop.
  allrw eqvars_prop; sp.
  allrw in_remove_nvar.
  allrw; sp.
Qed.

(** insertion of a nat in a list of variables in an ordered way *)
Fixpoint insert (v : Var) (vars : list NVar) : list NVar :=
  match vars with
  | [] => [nvar v]
  | nvar x :: xs =>
    if VarLt_dec x v then nvar x :: insert v xs
    else if VarDeq x v then vars
         else nvar v :: vars
  end.

Lemma insert_in : forall v vars, LIn (nvar v) (insert v vars).
Proof.
  induction vars; simpl; sp.
  destruct a.
  destruct (VarLt_dec v0 v); simpl; sp.
  destruct (VarDeq v0 v); subst; simpl; sp.
Qed.

Ltac invs2 :=
  match goal with
    | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; try subst; GC
    | [ H : nvar _ = nvar _ |- _ ] => inversion H; try subst; GC
  end.

Lemma in_insert :
  forall v x vars,
    LIn (nvar v) (insert x vars)
    <=> (v = x [+] LIn (nvar v) vars).
Proof.
  induction vars; simpl; split; intro h; repndors; subst; ginv; tcsp.
  - destruct a; simpl in *.
    destruct (VarLt_dec v0 x); simpl in *; tcsp.
    + repndors; tcsp.
      apply IHvars in h; tcsp.
    + destruct (VarDeq v0 x); subst; simpl in *; tcsp.
      repndors; tcsp; ginv; tcsp.
  - destruct a.
    destruct (VarLt_dec v x); simpl in *; tcsp.
    + right; apply IHvars; tcsp.
    + destruct (VarDeq v x); subst; simpl in *; tcsp.
  - destruct (VarLt_dec v x); simpl in *; tcsp.
    destruct (VarDeq v x); simpl in *; tcsp.
  - destruct a; simpl in *.
    destruct (VarLt_dec v0 x); simpl in *; tcsp.
    + right; apply IHvars; tcsp.
    + destruct (VarDeq v0 x); subst; simpl in *; tcsp.
Qed.

Lemma VarDeq_refl : forall v, VarDeq v v = left eq_refl.
Proof.
  introv.
  destruct (VarDeq v v); tcsp.
  f_equal.
  apply UIP_dec.
  apply VarDeq.
Qed.
Hint Rewrite VarDeq_refl : var.

Lemma remove_nvar_insert :
  forall vars n,
    remove_nvar (insert n vars) (nvar n)
    = remove_nvar vars (nvar n).
Proof.
  induction vars; simpl; sp.
  - autorewrite with var.
    rewrite remove_nvar_cons; autorewrite with var; auto.
  - destruct a.
    destruct (VarLt_dec v n); simpl in *; tcsp.
    + repeat (rewrite remove_nvar_cons2; simpl).
      destruct (VarDeq n v); subst; simpl in *; tcsp.
      f_equal; tcsp.
    + destruct (VarDeq v n); subst; simpl in *; tcsp.
      repeat (rewrite remove_nvar_cons2; simpl; autorewrite with var).
      destruct (VarDeq n v); tcsp.
Qed.

Fixpoint sort (vars : list NVar) : list NVar :=
  match vars with
    | [] => []
    | (nvar x) :: xs => insert x (sort xs)
  end.

Inductive issorted : list NVar -> Type :=
  | issorted_nil : issorted []
  | issorted_cons :
    forall v vs,
      (forall x, LIn x vs -> le_var v x)
      -> issorted vs
      -> issorted (v :: vs).

Hint Constructors issorted.

Lemma sort_eqvars :
  forall vars,
    eqvars vars (sort vars).
Proof.
  induction vars; simpl; sp.
  destruct a.
  trw eqvars_cons_l_iff; sp.
  apply insert_in.
  rewrite remove_nvar_insert.
  apply eqvars_remove_nvar; sp.
Qed.

Lemma sort_issorted :
  forall vars,
    issorted (sort vars).
Proof.
  induction vars; simpl; sp.
  destruct a.
  induction IHvars; simpl; sp.
  { constructor; simpl; sp. }
  destruct v0.
  destruct (VarLt_dec v0 v).
  { constructor; simpl; tcsp; introv i.
    destruct x.
    allrw in_insert; repndors; subst; tcsp.
    - apply VarLt_implies_VarLe; auto.
    - apply l in i; simpl in *; clear l; auto. }
  destruct (VarDeq v0 v); subst; simpl in *; tcsp.
  constructor; auto.
  introv i; simpl in *; repndors; subst; tcsp.
  { apply not_VarLt_implies_VarLe in n; auto. }
  { apply l in i; clear l; tcsp.
    destruct x.
    apply not_VarLt_implies_VarLe in n; auto.
    eapply VarLe_trans; eauto. }
Qed.
Hint Resolve sort_issorted : var.

Fixpoint fresh_var_aux (v : Var) (vars : list NVar) : Var :=
  match vars with
    | [] => v
    | (nvar x) :: xs =>
      if VarLt_dec v x then v
      else if VarDeq v x
           then fresh_var_aux (extend_var v) xs
           else fresh_var_aux v xs
  end.

Lemma fresh_var_aux_le :
  forall vars v,
    VarLe v (fresh_var_aux v vars).
Proof.
  induction vars; simpl; sp; eauto 2 with var.
  destruct a.
  destruct (VarLt_dec v v0); eauto 2 with var.
  destruct (VarDeq v v0); subst; auto.
  pose proof (IHvars (extend_var v0)) as q.
  eapply VarLe_trans;[|exact q]; eauto 2 with var.
Qed.

Lemma fresh_var_aux_sorted_not_in :
  forall vars,
    issorted vars
    -> forall n, ! LIn (nvar (fresh_var_aux n vars)) vars.
Proof.
  intros vars H.
  induction H; simpl; sp.

  - destruct v.
    destruct (VarLt_dec n v); ginv.

    + apply not_VarLt_refl in v0; tcsp.

    + destruct (VarDeq n v); subst; tcsp.

      * clear n0.
        inversion e as [xx]; clear e.
        pose proof (fresh_var_aux_le vs (extend_var v)) as q.
        rewrite <- xx in q.
        pose proof (VarLt_extend_var v) as h.
        eapply VarLe_VarLt_trans in h;[|exact q].
        apply not_VarLt_refl in h; tcsp.

      * inversion e as [xx]; clear e.
        pose proof (fresh_var_aux_le vs n) as q.
        rewrite <- xx in q; clear xx.
        destruct n0.
        apply VarLe_implies_VarLt; auto.

  - destruct v; simpl in *.
    destruct (VarLt_dec n v); tcsp.

    + apply l in l0.
      eapply VarLe_VarLt_trans in v0;[|exact l0].
      apply not_VarLt_refl in v0; tcsp.

    + destruct (VarDeq n v); subst; tcsp.
Qed.

Definition fresh_var (vars : list NVar) : NVar :=
  nvar (fresh_var_aux varx (sort vars)).

Lemma fresh_var_not_in :
  forall vars,
    ! LIn (fresh_var vars) vars.
Proof.
  unfold fresh_var; introv X.
  generalize (sort_eqvars vars); introv H.
  trw_h eqvars_prop  H.
  trw_h H  X.
  apply fresh_var_aux_sorted_not_in in X. sp.
  apply sort_issorted.
Qed.

Lemma ex_fresh_var :
  forall vars, {v : NVar $ !LIn v vars}.
Proof.
  introv.
  exists (fresh_var vars); apply fresh_var_not_in.
Qed.

Lemma fresh_var_aux_v :
  forall v vars,
    ! LIn (nvar v) vars
    -> issorted vars
    -> fresh_var_aux v vars = v.
Proof.
  introv nin iss.
  induction iss; simpl in *; tcsp.
  destruct v0.
  apply not_over_or in nin; repnd.
  destruct (VarLt_dec v v0); auto.
  destruct (VarDeq v v0); subst; tcsp.
Qed.

Lemma fresh_var_aux_0 :
  forall vars,
    ! LIn (nvar var0) vars
    -> issorted vars
    -> fresh_var_aux var0 vars = var0.
Proof.
  introv nin iss.
  apply fresh_var_aux_v; auto.
Qed.

Lemma fresh_var_nvarx :
  forall vars,
    ! LIn nvarx vars
    -> fresh_var vars = nvarx.
Proof.
  introv ni.
  unfold fresh_var.
  rewrite fresh_var_aux_v; auto; eauto 2 with var.
  intro xx.
  pose proof (sort_eqvars vars) as eqv.
  alltrewrite eqvars_prop.
  apply eqv in xx; tcsp.
Qed.

Lemma fresh_var_nil :
  fresh_var [] = nvarx.
Proof.
  sp.
Qed.

Hint Immediate fresh_var_nil.

Fixpoint fresh_distinct_vars (n:nat) (lv_avoid : list NVar) : (list NVar) :=
  match n with
    | O => []
    | S m =>
      let newvar := fresh_var lv_avoid in
      newvar :: (fresh_distinct_vars m (newvar :: lv_avoid))
  end.

Lemma fresh_distinct_vars_spec :
  forall n lv,
    let op := fresh_distinct_vars n lv in
    (no_repeats op) # (disjoint  op lv) # length(op)=n.
Proof. induction n as [ | n Hind]; introv. 
  simpl; split; sp. 
  allsimpl. pose proof (Hind ((fresh_var lv :: lv))) as Hind1; clear Hind.
  repnd. split; [| split]. 
  - constructor; auto. apply disjoint_sym in Hind2. apply Hind2. left. auto. 
  - apply disjoint_cons_l. split;[ | (apply fresh_var_not_in)]. 
    apply disjoint_cons_r in Hind2. repnd; auto. 
  - rewrite Hind1; reflexivity. 
Qed. 

(**another form of above which can be applied to remembered ops*)
Lemma fresh_distinct_vars_spec1 : forall n lv op, 
    (op = fresh_distinct_vars n lv) 
    -> (no_repeats op) # (disjoint  op lv) # length(op)=n.
Proof. intros. subst. apply fresh_distinct_vars_spec. 
Qed.

Lemma length_fresh_distinct_vars :
  forall n lv,
    length (fresh_distinct_vars n lv) = n.
Proof.
  introv; pose proof (fresh_distinct_vars_spec n lv); allsimpl; sp.
Qed.

(* end hide *)

(** Another key requirement for a sensible formalization of variables
  is to have an unbounded supply of fresh variables. Hence,
  we prove the following lemma. 
  % The notation \coqdocnotation{\{\_:\_ $\times$ \_\}} denotes sigma types
  (\coqexternalref{sigT}
  {http://coq.inria.fr/V8.1/stdlib/Coq.Init.Specif}{\coqdocinductive{sigT}})%
  To those who are unfamiliar
  with constructive logic, the following lemma might just
  say that that for any [n] and [lv], there exists a list [lvn] 
  of length [n] of distinct variables  such that the members of [lvn]
  are disjoint from the members of [lv].

  However, because of the propositions as types principle%\footnote{we are not using Prop.}%,
  We are actually defining a function [fresh_vars] that takes a number
  [n] and a list [lv] of variables and returns a 4-tuple.
  The first member of that tuple is [lvn], a list of variables with
  the above mentioned properties. The next three members are proofs
  of the desired properties of [lvn].

 An important use [free_vars] of it will be in defining
 the substitution function.

*)

Lemma fresh_vars :
  forall (n: nat) (lv : list NVar),
    {lvn : (list NVar) & no_repeats lvn # disjoint lvn lv # length lvn = n}.
Proof.
  intros.
  exists (fresh_distinct_vars n lv).
  apply fresh_distinct_vars_spec.
Qed.

(* begin hide *)

Ltac rem_fresh_vars :=
  match goal with
    | [ |- context[fresh_vars ?n ?lv] ] =>
      remember (fresh_vars n lv)
  end.


(*
Definition list_vars (vars : list NVar) : list nat :=
  map (fun x => match x with nvar n => n end) vars.

Definition fresh_var (vars : list NVar) : NVar :=
  let nats := list_vars vars in
  if nullb nats then nvar 0
  else let n := maxl nats in nvar (S n).

Lemma list_vars_eq :
  forall vars : list NVar,
    exists nats, vars = map nvar nats.
Proof.
  induction vars; simpl; sp.
  exists (nil : list nat); simpl; auto.
  destruct a.
  exists (n :: nats); simpl.
  rewrite <- H; auto.
 Qed.

Lemma list_vars_eq2 :
  forall nats : list nat,
    list_vars (map (fun n => nvar n) nats) = nats.
Proof.
  induction nats; simpl; sp.
  rewrite IHnats; auto.
 Qed.

Lemma fresh_var_in :
  forall vars,
    ! LIn (fresh_var vars) vars.
Proof.
  unfold fresh_var; intros.
  assert (exists nats, vars = map (fun n => nvar n) nats)
    by apply list_vars_eq; sp.
  rewrite H in H0.
  rewrite in_map_iff in H0; sp.
  rewrite list_vars_eq2 in H0.
  remember (nullb nats); symmetry in Heqb; destruct b; inversion H0; subst; GC.
  rewrite fold_assert in Heqb.
  rewrite assert_nullb in Heqb.
  rewrite null_iff_nil in Heqb; subst; allsimpl; sp.
  apply maxl_prop in H1; omega.
Qed.
*)

Definition sub_vars := subsetb eq_var_dec.

Definition subvars (vs1 vs2 : list NVar) :=
  assert (sub_vars vs1 vs2).


Lemma subvars_proof_irrelevance :
  forall vs1 vs2,
  forall x y : subvars vs1 vs2,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : subvars ?vs1 ?vs2 , H2 : subvars ?vs1 ?vs2 |- _ ] =>
    pose proof (subvars_proof_irrelevance vs1 vs2 H2 H1) as h; subst
end : pi.


Lemma assert_sub_vars :
  forall vs1 vs2,
    assert (sub_vars vs1 vs2) <=> forall x, LIn x vs1 -> LIn x vs2.
Proof.
  sp; unfold sub_vars.
  trw assert_subsetb; sp.
Qed.

Lemma subvars_eq :
  forall vs1 vs2,
    subvars vs1 vs2 <=> subset vs1 vs2.
Proof.
  sp; unfold subvars, sub_vars.
  trw assert_subsetb; sp.
Qed.

Lemma subvars_refl :
  forall vs,
    subvars vs vs.
Proof.
  sp.
  trw subvars_eq.
  apply subset_refl.
Qed.

Hint Immediate subvars_refl.

Lemma subvars_prop :
  forall vs1 vs2,
    subvars vs1 vs2 <=> forall x, LIn x vs1 -> LIn x vs2.
Proof.
  sp; trw subvars_eq; unfold subset; split; sp.
Qed.

Tactic Notation "prove_subvars" ident(h) :=
  let v := fresh "v" in
  let x := fresh "x" in
    trw_h subvars_prop h;
  trw subvars_prop;
  intros v x;
  apply h in x.

Ltac provesv :=
  match goal with
    | [ H : subvars ?v ?vs1 |- subvars ?v ?vs2 ] =>
        let v := fresh "v" in
        let x := fresh "x" in
        let y := fresh "y" in
          trw_h subvars_prop H;
        trw subvars_prop;
        intros v x;
        applydup H in x as y
  end.

Lemma subvars_app_weak_l :
  forall vs1 vs2 vs3, subvars vs1 vs2 -> subvars vs1 (vs2 ++ vs3).
Proof.
  intros.
  allrw subvars_prop; sp; discover; allrw in_app_iff; sp.
Qed.
Hint Resolve subvars_app_weak_l : slow.

Lemma subvars_app_weak_r :
  forall vs1 vs2 vs3, subvars vs1 vs3 -> subvars vs1 (vs2 ++ vs3).
Proof.
  intros.
  allrw subvars_prop; sp; discover; allrw in_app_iff; sp.
Qed.
Hint Resolve subvars_app_weak_r : slow.

Lemma subvars_singleton_l :
  forall v vs,
    subvars [v] vs <=> LIn v vs.
Proof.
  intros; rw subvars_prop; simpl; split; sp; subst; sp.
Qed.

Lemma subvars_singleton_r :
  forall v vs, subvars vs [v] <=> (forall x, LIn x vs -> x = v).
Proof.
  intros; rw subvars_prop; simpl; split; sp; apply_in_hyp p; sp.
Qed.

Lemma subvars_comm_r :
  forall vs vs1 vs2,
    subvars vs (vs1 ++ vs2) <=> subvars vs (vs2 ++ vs1).
Proof.
  introv. trw subvars_prop.  alltrewrite subvars_prop; split; introv Hyp Hin;
  apply Hyp in Hin; alltrewrite in_app_iff; sp; auto.
Qed.

Lemma subvars_flat_map :
  forall A,
  forall f : A -> list NVar,
  forall l k,
    subvars (flat_map f l) k
    <=>
    forall x, LIn x l -> subvars (f x) k.
Proof.
  intros.
  unfold subvars, sub_vars.
  repeat (trw subsetb_subset).
  trw subset_flat_map; split; sp.
  repeat (trw subsetb_subset).
  apply_hyp; sp.
  apply_in_hyp p.
  repeat (allrw subsetb_subset); auto.
Qed.

Lemma subvars_flat_map2 :
  forall A (f g : A -> list NVar) (l : list A),
    (forall x, LIn x l -> subvars (f x) (g x))
    -> subvars (flat_map f l) (flat_map g l).
Proof.
  introv h.
  rw subvars_eq.
  apply subset_flat_map2.
  introv i.
  apply subvars_eq; apply h; auto.
Qed.

Lemma subvars_remove_nvars :
  forall vs1 vs2 vs3,
    subvars (remove_nvars vs1 vs2) vs3
    <=>
    subvars vs2 (vs3 ++ vs1).
Proof.
  sp; repeat (trw subvars_eq); unfold remove_nvars.
  trw subset_diff; sp.
Qed.

Lemma null_remove_nvars_subvars :
  forall vs1 vs2,
    null (remove_nvars vs1 vs2) <=> subvars vs2 vs1.
Proof.
  unfold remove_nvars; sp.
  trw subvars_eq.
  trw null_diff_subset; split; sp.
Qed.

Lemma subvars_cons_l :
  forall v vs1 vs2,
    subvars (v :: vs1) vs2 <=> LIn v vs2 # subvars vs1 vs2.
Proof.
  sp; alltrewrite subvars_eq.
  apply subset_cons_l.
Qed.

Lemma subvars_cons_r :
  forall v vs1 vs2,
    subvars vs1 vs2
    -> subvars vs1 (v :: vs2).
Proof.
  sp; alltrewrite subvars_eq.
  apply subset_cons1; sp.
Qed.
Hint Resolve subvars_cons_r : slow.

Lemma subvars_nil_l :
  forall s, subvars [] s.
Proof.
  sp; trw subvars_eq.
  apply subset_nil_l.
Qed.

Hint Immediate subvars_nil_l.

Lemma subvars_nil_l_iff :
  forall s, subvars [] s <=> True.
Proof.
  sp; rewrite subvars_eq; split; sp; auto.
Qed.

Hint Rewrite subvars_nil_l_iff.

Lemma subvars_snoc_weak :
  forall vs1 vs2 v,
    subvars vs1 vs2
    -> subvars vs1 (snoc vs2 v).
Proof.
  intros.
  alltrewrite subvars_eq.
  apply subset_snoc_r; auto.
Qed.

Lemma subvars_app_l :
  forall vs1 vs2 vs,
    subvars (vs1 ++ vs2) vs <=> subvars vs1 vs # subvars vs2 vs.
Proof.
  sp; alltrewrite subvars_eq.
  trw subset_app; sp.
Qed.

Lemma subvars_app_remove_nvars_r :
  forall vs1 vs2 vs,
    subvars vs (vs1 ++ remove_nvars vs1 vs2) <=> subvars vs (vs1 ++ vs2).
Proof.
  sp; alltrewrite subvars_eq; unfold subset; split; sp.
  apply_in_hyp p; alltrewrite in_app_iff; sp.
  alltrewrite in_remove_nvars; sp.
  apply_in_hyp p; alltrewrite in_app_iff; sp.
  alltrewrite in_remove_nvars; sp.
  destruct (in_nvar_list_dec x vs1); sp.
Qed.

Lemma subvars_swap_r :
  forall vs1 vs2 vs,
    subvars vs (vs1 ++ vs2) <=> subvars vs (vs2 ++ vs1).
Proof.
  sp; alltrewrite subvars_eq; unfold subset; split; sp; alltrewrite in_app_iff;
  apply_in_hyp p; allrw in_app_iff; sp.
Qed.

Lemma subvars_trans :
  forall vs1 vs2 vs3,
    subvars vs1 vs2
    -> subvars vs2 vs3
    -> subvars vs1 vs3.
Proof.
  sp; alltrewrite subvars_eq.
  apply subset_trans with (l2 := vs2); sp.
Qed.

Theorem subvars_app_trivial_l :
  forall vs1 vs2, subvars vs1 (vs1++vs2).
Proof.
  intros. apply subvars_prop. intros.
  apply in_app_iff; sp.
Qed.

Theorem subvars_app_trivial_r :
  forall vs1 vs2, subvars vs2 (vs1++vs2).
Proof.
  intros. apply subvars_prop. intros.
  apply in_app_iff; sp.
Qed.

Lemma memvar_singleton_diff_r :
  forall x z, x <> z -> memvar x [z] = false.
Proof.
  sp.
  rw not_of_assert.
  rw assert_memvar; simpl; sp.
Qed.

Lemma eqvars_refl :
  forall vs, eqvars vs vs.
Proof.
  sp.
  rw eqvars_prop; sp.
Qed.

Hint Immediate eqvars_refl.

Lemma remove_nvar_comm :
  forall vs a b,
    remove_nvar (remove_nvar vs a) b
    = remove_nvar (remove_nvar vs b) a.
Proof.
  sp.
  unfold remove_nvar.
  rewrite remove_nvars_comm; sp.
Qed.


(* Some tactics *)

Tactic Notation "simpl_vlist" :=
       repeat (progress (try (allrewrite remove_var_nil);
                         try (allapply app_eq_nil);repnd;
                         try (allrewrite app_nil_r);
                         try (allrewrite null_iff_nil))).

Lemma dmemvar :
  forall (v: NVar) lv,  (LIn v lv) + (notT (LIn v lv)).
Proof.
  apply (in_deq NVar deq_nvar).
Qed.

Theorem assert_memvar_false:
  forall (v : NVar) (vars : list NVar),
    memvar v vars = false <=> ! LIn v vars.
Proof.
  intros.
  rw <- assert_memvar.
  rw <- not_of_assert; sp.
Qed.

Lemma memvar_dmemvar : forall T v lv (ct cf:T) ,
  (if (memvar v lv)  then ct else cf) = (if (dmemvar v lv)  then ct else cf).
  intros. cases_if as  Hb; auto; cases_if as Hd ; auto; subst.
  apply assert_memvar in Hb. sp.
  apply assert_memvar_false in Hb.
  sp; try contradiction.
Qed.

Lemma eq_vars_nil: forall lv, eqvars [] lv -> lv=[].
Proof.
  introv Heq. rw eqvars_prop in Heq.
  destruct lv;sp;[].
  pose proof (Heq n).
  allsimpl.
  discover; sp.
Qed.

Lemma eqvars_nil : forall lva lvb,
  lva=[] -> eqvars lva lvb -> lvb=[].
Proof.
  introv  Ha Heq.
  rw Ha in Heq.
  apply eq_vars_nil in Heq. auto.
Qed.
Lemma eqvars_trans : forall lva lvb lvc,
  eqvars lva lvb
  -> eqvars lvb lvc
  -> eqvars lva lvc.
Proof.
  introv He1 He2.
  allrw (eqvars_prop).
  split; intro Hin;
  repeat (try(apply He1 in Hin); try(apply He2 in Hin); auto).
Qed.

Lemma eq_vars_sym: forall lv1 lv2,
  eqvars lv1 lv2 -> eqvars lv2 lv1.
Proof.
  introv. rw eqvars_prop. rw eqvars_prop.
  intros X x. rw X.
  dtiffs2. split; auto.
Qed.


(*
Ltac inj :=
  repeat match goal with
             [ H : _ |- _ ] =>
             (apply pair_inj in H
              || apply S_inj in H
              || apply S_lt_inj in H
              || apply snoc_inj in H);
               repd; subst; GC
         end; try (complete sp).
*)



Lemma eqvars_remove_nvars :
  forall la lb ra rb,
    eqvars la lb
    -> eqvars ra rb
    -> eqvars (remove_nvars la ra) (remove_nvars lb rb).
Proof.
  introv Ha Hb. allrw eqvars_prop.
  dtiffs2.
  split; introv Hin; apply in_remove_nvars in Hin; repnd;
  apply in_remove_nvars; split; cpx; eauto.
Qed.

Lemma eqvars_app :
  forall la lb ra rb,
    eqvars la lb
    -> eqvars ra rb
    -> eqvars (app la ra) (app lb rb).
Proof.
  introv Ha Hb. allrw eqvars_prop.
  dtiffs2.
  split; introv Hin; apply in_app_iff; apply in_app_iff in Hin;
  dorn Hin; try (left;eauto;fail) ; try (right;eauto;fail).
Qed.

Hint Resolve eqvars_trans eq_vars_sym eqvars_refl eqvars_remove_nvar eqvars_remove_nvars eqvars_app: eqvars.

Definition dec_disjointv := dec_disjoint deq_nvar.

Lemma disjoint_remove_nvars: forall lva lvb,
  disjoint (remove_nvars lva lvb) lva.
Proof.
  introv Hin Hc.
  apply in_remove_nvars in Hin.
  sp.
Qed.

Lemma disjoint_remove_nvars2: forall lva lvb lvc,
  disjoint lvb lva
  -> disjoint (remove_nvars lvc lvb) lva.
Proof.
  introv Hin Hc.
  apply in_remove_nvars in Hc.
  exrepnd.
  introv Hinc. disjoint_lin_contra.
Qed.

Ltac sp3 :=
  (repeat match goal with
  | [ H: _ <=> _ |- _ ] => destruct H end); spc.


Lemma subvars_cons_r_weak_if_not_in :
  forall vs1 v vs2,
    subvars vs1 (v :: vs2)
    -> !LIn v vs1
    -> subvars vs1 vs2.
Proof.
  introv sv ni.
  allrw subvars_prop.
  introv i.
  applydup sv in i as j.
  allsimpl; sp; subst; sp.
Qed.

Lemma subvars_nil_r :
  forall vs,
    subvars vs [] <=> vs = [].
Proof.
  introv; split; intro k; allrw; sp.
  allrw subvars_prop.
  apply null_iff_nil.
  unfold null; introv i.
  discover; sp.
Qed.

Lemma eq_var_iff :
  forall v : NVar, v = v <=> True.
Proof. sp. Qed.

Lemma subvars_eqvars :
  forall s1 s2 s3,
    subvars s1 s2 -> eqvars s1 s3 -> subvars s3 s2.
Proof.
  introv s e.
  allrw subvars_prop.
  allrw eqvars_prop.
  introv i.
  apply e in i.
  apply s in i; auto.
Qed.

Lemma subvars_not_in :
  forall vs1 vs2 v, subvars vs2 vs1 -> !LIn v vs1 -> !LIn v vs2.
Proof.
  introv sv ni1 ni2.
  rw subvars_prop in sv.
  discover; sp.
Qed.

Lemma not_over_not_lin_nvar :
  forall (v : NVar) l t,
    !(LIn v l # t) <=> (!LIn v l [+] !t).
Proof.
  introv; split; intro k; repnd; sp.
  generalize (in_deq NVar deq_nvar v l); intro o; destruct o; tcsp.
  right; intro j.
  apply k; sp.
Qed.

Lemma subvars_cons_lr :
  forall v vs1 vs2,
    subvars vs1 vs2
    -> subvars (v :: vs1) (v :: vs2).
Proof.
  introv sv.
  allrw subvars_prop; introv i; allsimpl; sp.
Qed.

Lemma eqvars_disjoint_r:
  forall s s1 s2 : list NVar,
    eqvars s1 s2 -> disjoint s s1 -> disjoint s s2.
Proof.
  unfold disjoint.
  introv eqv disj i k.
  rw eqvars_prop in eqv.
  applydup disj in i as j.
  apply eqv in k; sp.
Qed.

Lemma subvars_disjoint_l :
  forall (l1 l2 l3 : list NVar),
    subvars l1 l2
    -> disjoint l2 l3
    -> disjoint l1 l3.
Proof.
  introv.
  rw subvars_eq.
  pose proof (subset_disjoint NVar l1 l2 l3); sp.
Qed.

Lemma subvars_disjoint_r :
  forall l1 l2 l3 : list NVar,
    subvars l1 l2 -> disjoint l3 l2 -> disjoint l3 l1.
Proof.
  introv sv disj.
  allrw subvars_prop.
  introv i j.
  apply sv in j.
  apply disj in i; sp.
Qed.

Lemma eqvars_cons_lr :
  forall v vs1 vs2,
    eqvars vs1 vs2 -> eqvars (v :: vs1) (v :: vs2).
Proof.
  introv.
  allrw eqvars_prop; split; intro k;
  allsimpl; sp; discover; sp.
Qed.

Lemma eqvars_remove_nvars_implies :
  forall vs1 vs2 vs3,
    eqvars vs1 (remove_nvars vs2 vs3)
    -> disjoint vs1 vs2 # subvars vs1 vs3.
Proof.
  introv eqv.
  allrw eqvars_prop.
  unfold disjoint.
  rw subvars_prop; dands; introv i;
  apply eqv in i; rw in_remove_nvars in i; sp.
Qed.

Lemma intersect_vars (l1 l2 : list NVar) :
  intersect l1 l2 [+] disjoint l1 l2.
Proof.
  induction l1; simpl; introv; auto.
  destruct (dmemvar a l2).
  - left.
    exists a; sp.
  - dorn IHl1.
    + left.
      unfold intersect in IHl1; exrepnd.
      exists x; sp.
    + right.
      rw disjoint_cons_l; sp.
Qed.

Ltac dest_intersect_vars :=
  match goal with
    | [ |- context[intersect_vars ?l1 ?l2] ] =>
      destruct (intersect_vars l1 l2)
  end.

Lemma fresh_var_lt :
  forall vs v,
    (forall x, LIn (nvar x) vs -> VarLt v x)
    -> fresh_var_aux v vs = v.
Proof.
  induction vs; introv i; allsimpl; tcsp.
  destruct a.
  destruct (VarLt_dec v v0); auto.
  destruct (VarDeq v v0); subst; tcsp.
  pose proof (i v0) as h; autodimp h hyp; sp.
Qed.

Lemma le_var_implies_eq :
  forall a b, le_var a b -> le_var b a -> a = b.
Proof.
  introv k1 k2.
  destruct a, b.
  allunfold le_var.
  apply VarLe_iff_VarLt in k1; repndors; subst; tcsp.
  eapply VarLe_VarLt_trans in k2;[|exact k1].
  apply not_VarLt_refl in k2; tcsp.
Qed.

Lemma extend_var_not_VarLt :
  forall v, ~ VarLt (extend_var v) v.
Proof.
  introv h.
  pose proof (VarLt_extend_var v) as q.
  eapply VarLt_trans in q;[|exact h].
  apply not_VarLt_refl in q; auto.
Qed.

Lemma implies_VarLe_extend_var :
  forall v1 v2, VarLe v1 v2 -> VarLe v1 (extend_var v2).
Proof.
  introv h.
  pose proof (VarLe_extend_var v2) as q.
  eapply VarLe_trans; eauto.
Qed.

Lemma extend_var_diff :
  forall v, extend_var v <> v.
Proof.
  unfold extend_var; induction v; simpl in *; intro h; tcsp; ginv.
  inversion h; tcsp.
Qed.

Lemma extend_var_not_VarLe :
  forall v, ~ VarLe (extend_var v) v.
Proof.
  introv h.
  pose proof (VarLt_extend_var v) as q.
  eapply VarLe_VarLt_trans in q;[|exact h].
  apply not_VarLt_refl in q; auto.
Qed.

Lemma VarLt_VarLe_trans :
  forall v1 v2 v3, VarLt v1 v2 -> VarLe v2 v3 -> VarLt v1 v3.
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
Hint Resolve VarLt_VarLe_trans : var.

Lemma fresh_var_aux_eq_S :
  forall vs n,
    issorted vs
    -> LIn (nvar n) vs
    -> fresh_var_aux (extend_var n) vs = fresh_var_aux n vs.
Proof.
  induction vs; introv iss i; allsimpl; tcsp.
  destruct a.
  inversion iss as [|? ? imp iss1]; subst; clear iss.
  repndors; ginv.
  - destruct (VarLt_dec (extend_var n) n) as [d|d];
      [apply extend_var_not_VarLt in d; tcsp|];[].
    clear d.
    destruct (VarDeq (extend_var n) n) as [d|d];
      [apply extend_var_diff in d; tcsp|];[].
    clear d.
    destruct (VarLt_dec n n) as [d|d];
      [apply not_VarLt_refl in d; tcsp|];[].
    clear d.
    destruct (VarDeq n n); tcsp.
  - applydup imp in i as j; simpl in j.
    destruct (VarLt_dec (extend_var n) v) as [d|d].
    + apply implies_VarLe_extend_var in j.
      eapply VarLe_VarLt_trans in j;[|exact d].
      apply not_VarLt_refl in j; tcsp.
    + clear d.
      destruct (VarDeq (extend_var n) v) as [d|d]; subst; tcsp;
        [apply extend_var_not_VarLe in j; tcsp|];[].
      clear d.
      destruct (VarLt_dec n v) as [d|d];
        [eapply VarLe_VarLt_trans in j;[|exact d];
         apply not_VarLt_refl in j; tcsp|];[].
      clear d.
      destruct (VarDeq n v) as [d|d]; subst; tcsp.
Qed.

(* end hide *)
