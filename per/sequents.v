(*

  Copyright 2014 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export per_props_more.
Require Export nuprl.
Require Export list.  (* Why do I have to do that? *)
Require Export csubst.
(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ #⪯# *)
(** printing ~=~  $\sim$ #~# *)
(* printing ===>  $\longmapsto$ *)
(** printing ===>  $\Downarrow$ #⇓# *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)
(* begin hide *)

(*
Lemma rev_list_ind :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (snoc l a)) ->
    forall l : list A, P l.
Proof.
  intros.
  assert (exists n, length l = n) by (exists (length l); auto); sp.
  revert l H1.
  induction n; intros.
  destruct l; simpl in H1; auto; inversion H1.
  assert (l = [] \/ exists (a : A), exists (k : list A), l = snoc k a) by apply snoc_cases.
  sp; subst; auto.
  apply H0.
  apply IHn.
  rewrite length_snoc in H1; inversion H1; auto.
Qed.

Lemma rev_list_dest :
  forall T,
  forall l : list T,
    l = [] \/ exists u v, l = snoc u v.
Proof.
  induction l using rev_list_ind.
  left; auto.
  right; auto.
  exists l a; auto.
Qed.

Ltac rev_list_dest l :=
  let name := fresh "or" in
    ((assert (l = [] \/ exists u v, l = snoc u v) as name
             by apply rev_list_dest);
     destruct name;
     try exrepd;
     subst).
*)


(* --- sequents and rules --- *)


(* end hide *)

(**

  Let us now define the syntax and semantics of sequents and rules.
  As we did for terms, we first define the concept of a ``bare''
  sequent, and we then define a sequent as a ``bare'' sequent that is
  well-formed.

  A sequent is defined as a pair of a list of hypotheses and a
  conclusion.  A sequent is then true if the conclusion is a true
  statement in the context of the given hypotheses.  Therefore, we
  first define our syntax for ``bare'' and well-formed hypotheses; for
  ``bare'' and well-formed conclusions; and finally, for ``bare'' and
  well-formed sequents.

*)

(**

  An hypothesis is a variable [hvar] (also called the name of the
  hypothesis), a type [htyp], a Boolean [hidden] which says whether or
  not the hypothesis is hidden, and a level annotation that can
  provide the level of the type.  The hiding mechanism is used to make
  it explicit in a sequent which variables can occur in the extract of
  the sequent.

*)

(* hidden is true for hidden hypotheses *)
Record hypothesis {p} :=
  {hvar : NVar; hidden : bool; htyp : @NTerm p; lvl : lvlop}.

(* begin hide *)

Lemma equal_hyps {p} :
  forall v h (t1 t2 : @NTerm p) l,
    t1 = t2
    -> {| hvar := v ; hidden := h; htyp := t1; lvl := l |}
       = {| hvar := v ; hidden := h; htyp := t2; lvl := l |}.
Proof.
  introv e; rw e; sp.
Qed.

(*Definition hyp_free_vars h := free_vars (get_wterm (htyp h)).*)
Definition hyp_free_vars {p} h := free_vars (@htyp p h).

(* Is not a hidden hypothesis: *)
Definition is_nh {p} (hs : @hypothesis p) := negb (hidden hs).

(* By default an hypothesis is not hidden *)
Definition mk_hyp {p} v t : @hypothesis p :=
  {| hvar := v; hidden := false; htyp := t; lvl := nolvl |}.

(* By default an hypothesis is not hidden + lvl *)
Definition mk_lhyp {p} v t l : @hypothesis p :=
  {| hvar := v; hidden := false; htyp := t; lvl := atlvl l |}.

(* mk_hhyp builds a hidden hypothesis *)
Definition mk_hhyp {p} v t : @hypothesis p :=
  {| hvar := v; hidden := true; htyp := t; lvl := nolvl |}.

(* mk_hhyp builds a hidden hypothesis + lvl *)
Definition mk_lhhyp {p} v t l : @hypothesis p :=
  {| hvar := v; hidden := true; htyp := t; lvl := atlvl l |}.

Definition mk_nlhyp {p} b v t : @hypothesis p :=
  {| hvar := v; hidden := b; htyp := t; lvl := nolvl |}.

Lemma hyp_free_vars_mk_hyp {p} :
  forall v t,
    hyp_free_vars (@mk_hyp p v t) = free_vars t.
Proof.
  sp.
Qed.

Hint Rewrite @hyp_free_vars_mk_hyp : core.

Lemma hyp_free_vars_mk_hhyp {p} :
  forall v t,
    hyp_free_vars (@mk_hhyp p v t) = free_vars t.
Proof.
  sp.
Qed.

Hint Rewrite @hyp_free_vars_mk_hhyp : core.

Lemma fold_mk_hyp {p} :
  forall v (t : @NTerm p),
    {| hvar := v; hidden := false; htyp := t; lvl := nolvl |} = mk_hyp v t.
Proof.
  unfold mk_hyp; auto.
Qed.

(* end hide *)

(**

  A barehypotheses is a list of hypotheses.  We say that such a list
  is ``bare'' because it is not yet accompanied with a proof that the
  list is well-formed (see below).

*)

Definition barehypotheses {p} := list (@hypothesis p).
Definition bhyps {p} := @barehypotheses p.

(**

  The following function extracts the variables from a list of hypotheses.

 *)

Definition vars_hyps {p} (hs : @barehypotheses p) := map hvar hs.

(* begin hide *)

(* Non-hidden variables *)
Definition nh_vars_hyps {p} (hs : @barehypotheses p) := vars_hyps (filter is_nh hs).

Lemma fold_nh_vars_hyps {p} :
  forall (hs : @barehypotheses p),
    vars_hyps (filter is_nh hs) = nh_vars_hyps hs.
Proof.
  sp.
Qed.

Lemma subvars_hs_vars_hyps {p} :
  forall hs,
    subvars (@nh_vars_hyps p hs) (vars_hyps hs).
Proof.
  unfold nh_vars_hyps, vars_hyps; sp.
  induction hs; sp; simpl.
  destruct (is_nh a); simpl.
  rw subvars_cons_l; sp.
  apply subvars_cons_r; sp.
  apply subvars_cons_r; sp.
Qed.

Hint Immediate subvars_hs_vars_hyps.

Lemma subset_hs_vars_hyps {p} :
  forall hs,
    subset (@nh_vars_hyps p hs) (vars_hyps hs).
Proof.
  intros; rw <- subvars_eq; sp.
Qed.

Hint Immediate subset_hs_vars_hyps.

Lemma htyp_mk_hyp {p} :
  forall x t,
    htyp (@mk_hyp p x t) = t.
Proof.
  simpl; sp.
Qed.

Hint Rewrite @htyp_mk_hyp : core.

Lemma hvar_mk_hyp {p} :
  forall x t,
    hvar (@mk_hyp p x t) = x.
Proof.
  simpl; sp.
Qed.

Hint Rewrite @hvar_mk_hyp : core.

Lemma htyp_mk_hhyp {p} :
  forall x t,
    htyp (@mk_hhyp p x t) = t.
Proof.
  simpl; sp.
Qed.

Hint Rewrite @htyp_mk_hhyp : core.

Lemma hvar_mk_hhyp {p} :
  forall x t,
    hvar (@mk_hhyp p x t) = x.
Proof.
  simpl; sp.
Qed.

Hint Rewrite @hvar_mk_hhyp : core.

Lemma vars_hyps_length {p} :
  forall hs,
    length (@vars_hyps p hs) = length hs.
Proof.
  unfold vars_hyps; sp.
  rewrite map_length; sp.
Qed.

Hint Rewrite @vars_hyps_length : core.

Lemma nh_vars_hyps_length {p} :
  forall hs,
    length (@nh_vars_hyps p hs) <= length hs.
Proof.
  unfold nh_vars_hyps; sp.
  autorewrite with core.
  apply length_filter.
Qed.

Lemma vars_hyps_app {p} :
  forall hs1 hs2 : @barehypotheses p,
    vars_hyps (hs1 ++ hs2) = vars_hyps hs1 ++ vars_hyps hs2.
Proof.
  induction hs1; simpl; intros; auto.
  rewrite IHhs1; auto.
Qed.

Lemma vars_hyps_snoc {p} :
  forall h : @hypothesis p,
  forall hs : barehypotheses,
    vars_hyps (snoc hs h) = snoc (vars_hyps hs) (hvar h).
Proof.
  induction hs; simpl; intros; auto.
  rewrite IHhs; auto.
Qed.

Lemma nh_vars_hyps_cons {p} :
  forall h hs,
    @nh_vars_hyps p (h :: hs)
    = if is_nh h
      then hvar h :: nh_vars_hyps hs
      else nh_vars_hyps hs.
Proof.
  unfold nh_vars_hyps, vars_hyps; simpl; sp.
  destruct (is_nh h); simpl; sp.
Qed.

Lemma nh_vars_hyps_app {p} :
  forall hs1 hs2 : @barehypotheses p,
    nh_vars_hyps (hs1 ++ hs2) = nh_vars_hyps hs1 ++ nh_vars_hyps hs2.
Proof.
  induction hs1; simpl; sp.
  repeat (rewrite nh_vars_hyps_cons).
  destruct (is_nh a); auto.
  rewrite IHhs1; simpl; sp.
Qed.

Lemma nh_vars_hyps_snoc {p} :
  forall hs h,
    @nh_vars_hyps p (snoc hs h)
    = if is_nh h
      then snoc (nh_vars_hyps hs) (hvar h)
      else nh_vars_hyps hs.
Proof.
  unfold nh_vars_hyps, vars_hyps; sp.
  rewrite filter_snoc.
  destruct (is_nh h); try (rewrite map_snoc); sp.
Qed.


(** This version considers the fact that in the context:
 *    H, x : A, G
 * x is bound in G *)
Fixpoint free_vars_hyps {p} (hs : @barehypotheses p) : list NVar :=
  match hs with
    | nil => nil
    | h :: hs => hyp_free_vars h ++ (remove_nvars [hvar h] (free_vars_hyps hs))
  end.

Lemma free_vars_hyps_snoc {p} :
  forall hs h,
    @free_vars_hyps p (snoc hs h)
    = free_vars_hyps hs ++ remove_nvars (vars_hyps hs) (hyp_free_vars h).
Proof.
  induction hs; simpl; sp.
  rewrite remove_nvars_nil_l.
  rewrite remove_nvars_nil_r.
  rewrite app_nil_r; sp.
  rewrite IHhs.
  rewrite remove_nvars_app_r.
  rewrite remove_nvars_app_l.
  rewrite app_assoc; simpl; sp.
Qed.

(** This version is similar to free_vars_hyps, but simply computes
 * the set of free_variables of all hypotheses *)
Fixpoint hyps_free_vars {p} (hs : @barehypotheses p) : list NVar :=
  match hs with
    | nil => nil
    | h :: hs => hyp_free_vars h ++ hyps_free_vars hs
  end.

Lemma hyps_free_vars_snoc {p} :
  forall hs h,
    @hyps_free_vars p (snoc hs h) = hyps_free_vars hs ++ hyp_free_vars h.
Proof.
  induction hs; simpl; sp.
  rewrite app_nil_r; sp.
  rewrite IHhs.
  rewrite app_assoc; sp.
Qed.

Lemma hyps_free_vars_app {p} :
  forall hs1 hs2,
    @hyps_free_vars p (hs1 ++ hs2) = hyps_free_vars hs1 ++ hyps_free_vars hs2.
Proof.
  induction hs1; simpl; sp.
  rw IHhs1; rewrite app_assoc; sp.
Qed.

(* end hide *)

(**

  The following predicate states when hypotheses are well-formed.  For
  a ``bare'' list of hypotheses of the form $(x_1:T1,\dots,x_n:T_n)$
  to be well-formed, each free variable $x$ occurring in a $T_i$ has
  to be one of the variables among $x_1,\dots,x_{i-1}$.  Also, all the
  $x_1,\dots,x_n$ have to be different from each other.

 *)

(* Here is another definition of well-formed hypotheses *)
(* When in Prop, to put wf_hypotheses in Prop, and because we want to prove
 * wf_hypotheses_snoc1 which implies subset which is defined using LIn,
 * then LIn has to be in Prop too. *)
Inductive wf_hypotheses {p} : @barehypotheses p -> Type :=
  | hyps_nil  : wf_hypotheses nil
  | hyps_cons :
      forall h  : hypothesis,
      forall hs : barehypotheses,
        isprog_vars (vars_hyps hs) (htyp h)
        -> ! LIn (hvar h) (vars_hyps hs)
        -> wf_hypotheses hs
        -> wf_hypotheses (snoc hs h).

(* begin hide *)

(** This is used to state wf_hypotheses_app *)
Inductive vs_wf_hypotheses {p} : list NVar -> @barehypotheses p -> Type :=
  | vs_hyps_nil  : forall vs, vs_wf_hypotheses vs nil
  | vs_hyps_cons :
      forall vs,
      forall h  : hypothesis,
      forall hs : barehypotheses,
        isprog_vars (vs ++ vars_hyps hs) (htyp h)
        -> ! LIn (hvar h) (vs ++ vars_hyps hs)
        -> vs_wf_hypotheses vs hs
        -> vs_wf_hypotheses vs (snoc hs h).
Hint Constructors vs_wf_hypotheses.

(** we prove the relation between wf_hypotheses and vs_wf_hypotheses *)
Lemma vs_wf_hypotheses_eq {p} :
  forall hs, @wf_hypotheses p hs <=> vs_wf_hypotheses [] hs.
Proof.
  induction hs using rev_list_indT; simpl; try (complete (split; sp)).
  sp_iff Case; intro w.

  - Case "->".
    inversion w; cpx.
    constructor; sp.
    apply IHhs; sp.

  - Case "<-".
    inversion w; cpx.
    constructor; sp.
    apply IHhs; sp.
Qed.

Lemma vs_wf_hypotheses_snoc_weak {p} :
  forall v vs hs,
    !LIn v (@vars_hyps p hs)
    -> vs_wf_hypotheses vs hs
    -> vs_wf_hypotheses (snoc vs v) hs.
Proof.
  introv iv vwh.
  induction vwh; allsimpl; sp.
  apply vs_hyps_cons.
  apply isprog_vars_snoc_swap.
  apply isprog_vars_weak_l; sp.
  allrw in_app_iff; allrw in_snoc.
  rw not_over_or; sp.
  subst.
  allrw @vars_hyps_snoc; allrw in_snoc.
  apply not_over_or in iv; sp.
  apply IHvwh.
  allrw @vars_hyps_snoc; allrw in_snoc.
  apply not_over_or in iv; sp.
Qed.

(** boolean version of vs_wf_hypotheses *)
Fixpoint vs_wf_hypothesesb {p} (vs : list NVar) (hs : @barehypotheses p) : obool :=
  match hs with
    | nil => otrue
    | h :: hs =>
      oball [bool2obool (sub_vars (free_vars (htyp h)) vs),
             wft (htyp h),
             bool2obool (negb (memvar (hvar h) vs)),
             vs_wf_hypothesesb (vs ++ [hvar h]) hs]
  end.

Definition hyps2otrue {o} (hs : @barehypotheses o) : obool :=
  oball (map (fun h => term2otrue (htyp h)) hs).

(* !!MOVE *)
Hint Rewrite oband_otrue : slow.

(* !!MOVE *)
Lemma oband_assoc :
  forall (o1 o2 o3 : obool),
    oband (oband o1 o2) o3 = oband o1 (oband o2 o3).
Proof.
  induction o1 as [|?|? ind]; introv; simpl; auto;[].
  destruct o2; simpl; auto;[].
  destruct o3; simpl; auto.
  f_equal.
  apply functional_extensionality.
  introv; auto.
Qed.

Lemma vs_wf_hypothesesb_snoc {p} :
  forall hs h vs,
    @vs_wf_hypothesesb p vs (snoc hs h)
    = oball [vs_wf_hypothesesb vs hs,
             bool2obool (sub_vars (free_vars (htyp h)) (vs ++ vars_hyps hs)),
             wft (htyp h),
             bool2obool (negb (memvar (hvar h) (vs ++ vars_hyps hs)))].
Proof.
  induction hs; introv; simpl; autorewrite with slow in *; auto.
  rw IHhs.
  simpl; autorewrite with slow in *.
  allrw @oband_assoc.
  repeat (rw <- app_assoc); simpl; auto.
Qed.

(** This definition is equivalent to vs_wf_hypotheses as we prove later *)
Definition vswf_hypotheses {p} (vs : list NVar) (hs : @barehypotheses p) :=
  vs_wf_hypothesesb vs hs = hyps2otrue hs.

Lemma hyps2otrue_cons {o} :
  forall h (hs : @barehypotheses o),
    hyps2otrue (h :: hs) = oband (term2otrue (htyp h)) (hyps2otrue hs).
Proof. sp. Qed.
Hint Rewrite @hyps2otrue_cons : slow.

Lemma hyps2otrue_nil {o} : @hyps2otrue o [] = otrue.
Proof. sp. Qed.
Hint Rewrite @hyps2otrue_nil : slow.

Lemma hyps2otrue_snoc {o} :
  forall (hs : @barehypotheses o) h,
    hyps2otrue (snoc hs h) = oband (hyps2otrue hs) (term2otrue (htyp h)).
Proof.
  induction hs; introv; simpl; autorewrite with slow.
  - unfold hyps2otrue; simpl; autorewrite with slow; auto.
  - allrw oband_assoc.
    rw IHhs; auto.
Qed.

Lemma oband_ofalse_r :
  forall (o : obool), oband o ofalse = ofalse.
Proof.
  destruct o; simpl; auto.
Qed.
Hint Rewrite oband_ofalse_r : slow.

Lemma isotrue_hyps2otrue {o} :
  forall (hs : @barehypotheses o), isotrue (hyps2otrue hs).
Proof.
  induction hs; simpl; auto.
  rw @hyps2otrue_cons.
  apply isotrue_oband; dands; auto.
  apply isotrue_term2otrue.
Qed.

Lemma oband_eq_ofalse :
  forall o1 o2 : obool, oband o1 o2 = ofalse -> (o1 = ofalse [+] o2 = ofalse).
Proof.
  introv h.
  destruct o1; allsimpl; autorewrite with slow in *; tcsp.
  destruct o2; allsimpl; autorewrite with slow in *; tcsp; ginv.
Qed.

Lemma hyps2otrue_eq_false_implies {o} :
  forall (hs : @barehypotheses o), hyps2otrue hs = ofalse -> False.
Proof.
  induction hs; introv h; allsimpl; autorewrite with slow in *; tcsp; ginv.
  apply oband_eq_ofalse in h; repndors; tcsp.
  allapply @term2otrue_not_ofalse; tcsp.
Qed.

Lemma isotrue_vs_wf_hypothesesb_implies_eq_hyps2otrue {o} :
  forall (hs : @barehypotheses o) vs,
    isotrue (vs_wf_hypothesesb vs hs)
    -> vs_wf_hypothesesb vs hs = hyps2otrue hs.
Proof.
  induction hs; introv h; allsimpl; auto; autorewrite with slow in *;
  allrw isotrue_oband; allrw @isotrue_bool2obool_iff; repnd; dands.
  allrw; simpl; tcsp.
  f_equal.
  apply isotrue_wft_implies_eq_term2otrue_iff; auto.
Qed.

Lemma isotrue_vs_wf_hypothesesb_iff_eq_hyps2otrue {o} :
  forall (hs : @barehypotheses o) vs,
    isotrue (vs_wf_hypothesesb vs hs)
    <=> vs_wf_hypothesesb vs hs = hyps2otrue hs.
Proof.
  introv; split; intro h.
  apply isotrue_vs_wf_hypothesesb_implies_eq_hyps2otrue; auto.
  rw h.
  apply isotrue_hyps2otrue.
Qed.

Lemma vswf_hypotheses_snoc {p} :
  forall hs h vs,
    @vswf_hypotheses p vs (snoc hs h)
    <=> vswf_hypotheses vs hs
        # isprog_vars (vs ++ vars_hyps hs) (htyp h)
        # ! LIn (hvar h) (vs ++ vars_hyps hs).
Proof.
  unfold vswf_hypotheses; simpl.
  introv.
  allrw <- @isotrue_vs_wf_hypothesesb_iff_eq_hyps2otrue.
  revert vs.

  induction hs; introv; allsimpl; autorewrite with slow;
  allrw isotrue_oband;
  allrw isotrue_bool2obool_iff;
  allrw negb_eq_true;
  allrw fold_assert;
  allrw not_of_assert;
  allrw assert_memvar;
  allrw @isotrue_wft_implies_eq_term2otrue_iff;
  allrw @isprog_vars_eq;
  allrw @nt_wf_eq;
  try (rw IHhs);
  split; intro q; repnd; dands; tcsp.

  - allrw @isprog_vars_eq; repnd; allsimpl.
    allrw <- app_assoc; allsimpl; tcsp.

  - allrw @isprog_vars_eq; repnd; allsimpl.
    allrw @nt_wf_eq; auto.

  - allrw <- app_assoc; allsimpl; tcsp.

  - apply isprog_vars_eq; rw @nt_wf_eq; dands; auto.
    allrw <- app_assoc; allsimpl; tcsp.

  - allrw <- app_assoc; allsimpl; tcsp.
Qed.

Lemma vswf_hypotheses_proof_irrelevance {p} :
  forall vs hs,
  forall x y : @vswf_hypotheses p vs hs,
    x = y.
Proof.
  sp.
  apply UIP.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : vswf_hypotheses ?vs ?hs , H2 : vswf_hypotheses ?vs ?hs |- _ ] =>
    pose proof (vswf_hypotheses_proof_irrelevance vs hs H2 H1) as h; subst
end : pi.

Lemma vswf_hypotheses_eq {p} :
  forall hs vs,
    @vs_wf_hypotheses p vs hs <=> vswf_hypotheses vs hs.
Proof.
  induction hs using rev_list_indT; simpl; intros; try (complete (split; sp)).
  sp_iff Case; intro k.

  - Case "->".
    inversion k; cpx.
    rw @vswf_hypotheses_snoc; sp.
    apply IHhs; auto.

  - Case "<-".
    allrw @vswf_hypotheses_snoc; sp.
    constructor; sp.
    apply IHhs; sp.
Qed.

Lemma vswf_hypotheses_nil_eq {p} :
  forall hs : @barehypotheses p, vswf_hypotheses [] hs <=> wf_hypotheses hs.
Proof.
  intro.
  rw <- @vswf_hypotheses_eq.
  rw @vs_wf_hypotheses_eq; sp.
Qed.

Lemma vswf_hypotheses_nil_implies {p} :
  forall hs : @barehypotheses p, vswf_hypotheses [] hs -> wf_hypotheses hs.
Proof.
  intro.
  rw <- @vswf_hypotheses_eq.
  rw @vs_wf_hypotheses_eq; sp.
Qed.
Hint Resolve vswf_hypotheses_nil_implies.

Lemma vswf_hypotheses_nil_if {p} :
  forall hs : @barehypotheses p, wf_hypotheses hs -> vswf_hypotheses [] hs.
Proof.
  intro.
  rw <- @vswf_hypotheses_eq.
  rw @vs_wf_hypotheses_eq; sp.
Qed.

Lemma vs_wf_hypotheses_implies {p} :
  forall hs vs,
    @vs_wf_hypotheses p vs hs
    -> disjoint vs (vars_hyps hs)
       # subvars (free_vars_hyps hs) vs
       # subvars (hyps_free_vars hs) (vs ++ vars_hyps hs).
Proof.
  induction hs using rev_list_indT; simpl; try (complete sp); introv k.
  inversion k; subst; cpx.
  allrw in_app_iff.
  allrw not_over_or; repd.
  discover.
  rw @vars_hyps_snoc.
  rw @free_vars_hyps_snoc.
  rw @hyps_free_vars_snoc.
  repeat (rw subvars_app_l).
  rw subvars_remove_nvars.
  rw disjoint_snoc_r.
  allrw @isprog_vars_eq; repd.
  rw snoc_append_l.
  sp; apply subvars_snoc_weak; sp.
Qed.

Lemma wfhn {p} : @wf_hypotheses p [].
Proof.
  sp.
Qed.
Hint Immediate wfhn.

Lemma vs_wf_hypotheses_app {p} :
  forall vs hs1 hs2,
    @vs_wf_hypotheses p vs (hs1 ++ hs2)
    <=> vs_wf_hypotheses vs hs1 # vs_wf_hypotheses (vs ++ vars_hyps hs1) hs2.
Proof.
  induction hs2 using rev_list_indT; sp; simpl.
  - rewrite app_nil_r; split; sp.
  - rewrite snoc_append_l; split; intro k; repnd.
    + inversion k; cpx.
      discover; sp.
      constructor; auto; allrw @vars_hyps_app; auto; rw <- app_assoc; auto.
    + inversion k; cpx.
      constructor; allrw @vars_hyps_app; try (rw app_assoc; auto).
      apply IHhs2; sp.
Qed.

Lemma vs_wf_hypotheses_snoc {p} :
  forall vs hs h,
    @vs_wf_hypotheses p vs (snoc hs h)
    <=> isprog_vars (vs ++ vars_hyps hs) (htyp h)
        # !LIn (hvar h) (vs ++ vars_hyps hs)
        # vs_wf_hypotheses vs hs.
Proof.
  sp; split; intro k; tcsp; inversion k; cpx.
Qed.

Lemma wf_hypotheses_app {p} :
  forall hs1 hs2,
    @wf_hypotheses p (hs1 ++ hs2)
    <=> wf_hypotheses hs1 # vs_wf_hypotheses (vars_hyps hs1) hs2.
Proof.
  induction hs2 using rev_list_indT; sp; simpl.
  rewrite app_nil_r; split; sp.
  rewrite snoc_append_l; split; intro k; repnd.
  - inversion k; cpx.
    discover; sp.
    constructor; auto; allrw <- @vars_hyps_app; auto.
  - inversion k; cpx.
    constructor; sp; allrw @vars_hyps_app; sp.
    apply IHhs2; sp.
Qed.

Lemma wf_hypotheses_snoc {p} :
  forall hs h,
    @wf_hypotheses p (snoc hs h)
    <=> isprog_vars (vars_hyps hs) (htyp h)
        # !LIn (hvar h) (vars_hyps hs)
        # wf_hypotheses hs.
Proof.
  sp; split; intro k; tcsp; inversion k; cpx.
Qed.

Lemma wf_hypotheses_app1 {p} :
  forall hs1 hs2,
    @wf_hypotheses p (hs1 ++ hs2)
    -> wf_hypotheses hs1
    # disjoint (vars_hyps hs1) (vars_hyps hs2)
    # subvars (free_vars_hyps hs2) (vars_hyps hs1)
    # subvars (hyps_free_vars hs2) (vars_hyps hs1 ++ vars_hyps hs2).
Proof.
  induction hs2 using rev_list_indT; simpl; introv w.

  - autorewrite with core.
    allrewrite app_nil_r; auto.

  - allrw snoc_append_l.
    inversion w; cpx.
    discover; repnd.
    rewrite vars_hyps_snoc.
    rewrite free_vars_hyps_snoc.
    rewrite hyps_free_vars_snoc.
    repeat (rw subvars_app_l).
    rw disjoint_snoc_r.
    allrewrite @vars_hyps_app.
    allrw in_app_iff.
    allrw not_over_or; repd.
    rw subvars_remove_nvars.
    allrw @isprog_vars_eq; repd.
    allfold (hyp_free_vars a).
    rewrite snoc_append_l.

    sp; apply subvars_snoc_weak; sp.
Qed.

Lemma wf_hypotheses_snoc1 {p} :
  forall hs h,
    @wf_hypotheses p (snoc hs h)
    -> subset (hyp_free_vars h) (vars_hyps hs).
Proof.
  introv w.
  inversion w; cpx.
  allrw @isprog_vars_eq; sp.
  allrw subvars_eq.
  unfold hyp_free_vars; sp.
Qed.

Lemma wf_hypotheses_snoc2 {p} :
  forall hs h,
    @wf_hypotheses p (snoc hs h)
    -> wf_hypotheses hs
       # subset (hyp_free_vars h) (vars_hyps hs)
       # !LIn (hvar h) (vars_hyps hs)
       # !LIn (hvar h) (hyp_free_vars h).
Proof.
  introv w.
  inversion w; cpx.
  allrw @isprog_vars_eq; repd.
  allrw subvars_eq.
  unfold hyp_free_vars; sp.
Qed.

Lemma wf_hypotheses_disj {p} :
  forall G x A J,
    wf_hypotheses (snoc G (@mk_hyp p x A) ++ J)
    -> disjoint (free_vars A) (vars_hyps J)
       # !LIn x (vars_hyps J)
       # !LIn x (vars_hyps G)
       # !LIn x (free_vars A).
Proof.
  introv w.
  apply wf_hypotheses_app1 in w; repd.
  apply wf_hypotheses_snoc2 in w.
  unfold hyp_free_vars in w; allsimpl.
  allrw @vars_hyps_snoc; allsimpl.
  allrw disjoint_snoc_l; sp.
  apply subset_disjoint with (l2 := vars_hyps G); auto.
Qed.

Lemma wf_hypotheses_not_in_sp {p} :
  forall G z T J,
    wf_hypotheses (snoc G (@mk_hyp p z T) ++ J)
    -> wf_hypotheses (G ++ J)
    -> !LIn z (hyps_free_vars J).
Proof.
  introv w1 w2 i.
  apply wf_hypotheses_app1 in w1; repnd.
  apply wf_hypotheses_app1 in w2; repnd.
  allrw subvars_eq.
  apply w2 in i.
  allrw @vars_hyps_snoc; allsimpl.
  allrw disjoint_snoc_l; repnd.
  rw in_app_iff in i; dorn i; tcsp.
  apply wf_hypotheses_snoc2 in w0; sp.
Qed.

Lemma wf_hypotheses_not_in {p} :
  forall G H z T J,
    wf_hypotheses (snoc G (@mk_hyp p z T) ++ J)
    -> wf_hypotheses (H ++ J)
    -> vars_hyps G = vars_hyps H
    -> !LIn z (hyps_free_vars J).
Proof.
  introv w1 w2 e i.
  apply wf_hypotheses_app1 in w1; repnd.
  apply wf_hypotheses_app1 in w2; repnd.
  allrw subvars_eq.
  apply w2 in i.
  allrw @vars_hyps_snoc; allsimpl.
  allrw disjoint_snoc_l; repnd.
  rw in_app_iff in i; dorn i; tcsp.
  apply wf_hypotheses_snoc2 in w0; repnd; allsimpl.
  rw <- e in i; sp.
Qed.

Lemma wf_hypotheses_not_in_nh {p} :
  forall G H z T J,
    wf_hypotheses (snoc G (@mk_hhyp p z T) ++ J)
    -> wf_hypotheses (H ++ J)
    -> vars_hyps G = vars_hyps H
    -> !LIn z (hyps_free_vars J).
Proof.
  introv w1 w2 e i.
  apply wf_hypotheses_app1 in w1; repnd.
  apply wf_hypotheses_app1 in w2; repnd.
  allrw subvars_eq.
  apply w2 in i.
  allrw @vars_hyps_snoc; allsimpl.
  allrw disjoint_snoc_l; repnd.
  rw in_app_iff in i; dorn i; tcsp.
  apply wf_hypotheses_snoc2 in w0; repnd; allsimpl.
  rw <- e in i; sp.
Qed.

Lemma wf_hypotheses_hyps_free_vars_tail {p} :
  forall G J x,
    @wf_hypotheses p (G ++ J)
    -> LIn x (hyps_free_vars J)
    -> LIn x (vars_hyps G) [+] LIn x (vars_hyps J).
Proof.
  introv w i.
  apply wf_hypotheses_app1 in w; repnd.
  allrw subvars_eq.
  apply w in i; rw in_app_iff in i; sp.
Qed.

(* end hide *)

(**

  A well-formed list of hypotheses is a ``bare'' list of hypotheses
  along with a proof that these hypotheses are well-formed.

*)

Definition hypotheses {p} := { hs : @barehypotheses p & vswf_hypotheses [] hs }.

(* begin hide *)

Definition mk_hyps {o} (hs : @barehypotheses o) (p : wf_hypotheses hs) : hypotheses :=
  existT (vswf_hypotheses []) hs (vswf_hypotheses_nil_if hs p).

Definition vars_hypotheses {p} (hyps : @hypotheses p) : list NVar :=
  vars_hyps (projT1 hyps).
Definition length_hs {p} (hyps : @hypotheses p) : nat :=
  length (projT1 hyps).

Lemma nwf_add_hyp {o}
      (h  : @hypothesis o)
      (hs : barehypotheses)
      (p  : wf_hypotheses hs)
      (d  : ! LIn (hvar h) (vars_hyps hs))
      (s  : isprog_vars (vars_hyps hs) (htyp h))
: wf_hypotheses (snoc hs h).
Proof.
  constructor; auto.
Qed.

Lemma nwf_add_hyp2 {o}
      (h  : @hypothesis o)
      (hs : hypotheses)
      (d  : ! LIn (hvar h) (vars_hypotheses hs))
      (s  : isprog_vars (vars_hypotheses hs) (htyp h))
: wf_hypotheses (snoc (projT1 hs) h).
Proof.
  destruct hs.
  constructor; auto.
Qed.

Definition add_hyp {o}
           (h : @hypothesis o)
           (hs : hypotheses)
           (d  : ! LIn (hvar h) (vars_hypotheses hs))
           (s  : isprog_vars (vars_hypotheses hs) (htyp h))
: hypotheses :=
  mk_hyps
    (snoc (projT1 hs) h)
    (nwf_add_hyp2 h hs d s).

Lemma combine_nwfhyps {o}
             (hs1 hs2 : @barehypotheses o)
             (p1 : wf_hypotheses hs1)
             (p2 : wf_hypotheses hs2)
             (d : disjoint (vars_hyps hs1) (vars_hyps hs2))
  : wf_hypotheses (hs1 ++ hs2).
Proof.
  revert hs1 p1 d.
  induction p2; intros.
  rewrite app_nil_r; auto.
  rewrite snoc_append_l.
  constructor; try apply IHp2; auto.
  rewrite vars_hyps_app.
  apply isprog_vars_app_l; auto.
  rewrite vars_hyps_app.
  rw in_app_iff; sp.
  rewrite vars_hyps_snoc in d.
  apply disjoint_snoc_r in d; sp.
  rewrite vars_hyps_snoc in d.
  apply disjoint_snoc_r in d; sp.
Qed.

Lemma combine_nwfhyps2 {o}
             (hs1 hs2 : @hypotheses o)
             (d : disjoint (vars_hypotheses hs1) (vars_hypotheses hs2))
  : wf_hypotheses (projT1 hs1 ++ projT1 hs2).
Proof.
  destruct hs1; destruct hs2; simpl.
  apply combine_nwfhyps; auto.
Qed.

Definition combine_hypotheses {o}
             (hyps1 hyps2 : @hypotheses o)
             (d : disjoint (vars_hypotheses hyps1) (vars_hypotheses hyps2))
  : hypotheses :=
    mk_hyps
      (projT1 hyps1 ++ projT1 hyps2)
      (combine_nwfhyps2 hyps1 hyps2 d).

(* end hide *)

(**

  We have two forms of sequents.  Some sequents have extracts and some
  do not.  If a sequent with an extract is true then the extract
  provides an evidence of the truth of the type, and the type is a
  type of the Nuprl type system.  If a sequent without an extract is
  true then the type is a type of the Nuprl type system.  The current
  Nuprl version has only one kind of sequent.  However, we feel that
  it is sometimes useful to prove that types are indeed types without
  having to deal with levels.  Currently in Nuprl, to prove that a
  type [T] is a type one has to prove that [mkc_member T (mkc_uni i)]
  is true for some level [i].

*)

Inductive conclusion {o} :=
| concl_ext : forall (ctype : @NTerm o) (extract : @NTerm o), conclusion
| concl_typ : forall (ctype : @NTerm o), conclusion.

(**

  The following [ctype] function returns the type of a conclusion.

*)

Definition ctype {o} (c : @conclusion o) :=
  match c with
    | concl_ext t e => t
    | concl_typ t => t
  end.

(**

  The following [extract] function returns the extract of a conclusion
  whenever it exists.  We then define several operations that are
  simple maps on options.

*)

Definition extract {o} (c : @conclusion o) :=
  match c with
    | concl_ext t e => Some e
    | concl_typ t => None
  end.

Definition wf_term_op {o} (top : option (@NTerm o)) :=
  match top with
    | Some t => wf_term t
    | None => true = true
  end.

Definition covered_op {o} (top : option (@NTerm o)) vs :=
  match top with
    | Some t => covered t vs
    | None => true = true
  end.

Definition cover_vars_op {o} (top : option (@NTerm o)) sub :=
  match top with
    | Some t => cover_vars t sub
    | None => true = true
  end.

(* begin hide *)

Definition mk_concl_t {p} (typ : @NTerm p) : conclusion := concl_typ typ.

Definition mk_concl {p} (typ e : @NTerm p) : conclusion := concl_ext typ e.
Definition mk_conclax {p} (typ : @NTerm p) : conclusion := mk_concl typ mk_axiom.

Definition mk_concleq {p} (t1 t2 T : @NTerm p) : conclusion :=
  mk_conclax (mk_equality t1 t2 T).

Lemma wf_term_op_proof_irrelevance {p} :
  forall c,
  forall x y : @wf_term_op p c,
    x = y.
Proof.
  intros.
  allunfold @wf_term_op; destruct c; sp; clear_irr; sp.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : wf_term_op ?c , H2 : wf_term_op ?c |- _ ] =>
    pose proof (wf_term_op_proof_irrelevance c H2 H1) as h; subst
end : pi.

Lemma covered_op_proof_irrelevance {p} :
  forall c vs,
  forall x y : @covered_op p c vs,
    x = y.
Proof.
  intros.
  destruct c; allsimpl; sp.
  apply UIP_dec.
  apply bool_dec.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : covered_op ?c ?vs , H2 : covered_op ?c ?vs |- _ ] =>
    pose proof (covered_op_proof_irrelevance c vs H2 H1) as h; subst
end : pi.

Lemma cover_vars_op_proof_irrelevance {p} :
  forall c sub,
  forall x y : @cover_vars_op p c sub,
    x = y.
Proof.
  intros.
  destruct c; allsimpl; sp.
  apply UIP_dec.
  apply bool_dec.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : cover_vars_op ?c ?s , H2 : cover_vars_op ?c ?s |- _ ] =>
    pose proof (cover_vars_op_proof_irrelevance c s H2 H1) as h; subst
end : pi.

Lemma cover_vars_op_covered_op {o} :
  forall top sub,
    @cover_vars_op o top sub <=> covered_op top (dom_csub sub).
Proof.
  intros; destruct top; simpl; sp.
Qed.

Lemma covered_op_subvars {o} :
  forall top vs1 vs2,
    @covered_op o top vs1
    -> subvars vs1 vs2
    -> covered_op top vs2.
Proof.
  intros; destruct top; simpl; sp.
  apply @covered_subvars with (vs1 := vs1); sp.
Qed.

(* end hide *)

(**

  We say that a conclusion is well-formed if its type and extract are
  well-formed.

*)

Definition wf_concl {p} (c : @conclusion p) : Type :=
  wf_term (ctype c) # wf_term_op (extract c).

(**

  A conclusion depends on hypotheses.  For a conclusion to be closed
  w.r.t. a list of hypotheses, means that the variables of the type
  have to be covered by the hypotheses.

 *)

Definition closed_type {p} (hs : @barehypotheses p) (c : @conclusion p) : Type :=
  covered (ctype c) (vars_hyps hs).

(**

  In addition the variables of the extract also have to be covered by
  the non-hidden hypotheses.

 *)

Definition closed_extract {p} (hs : @barehypotheses p) (c : @conclusion p) : Type :=
  covered_op (extract c) (nh_vars_hyps hs).

(* begin hide *)

Lemma wf_concl_proof_irrelevance {p} :
  forall c,
  forall x y : @wf_concl p c,
    x = y.
Proof.
  intros.
  allunfold @wf_concl; sp.
  f_equal; try (apply UIP).
  destruct c; allsimpl; apply UIP.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : wf_concl ?c , H2 : wf_concl ?c |- _ ] =>
    pose proof (wf_concl_proof_irrelevance c H2 H1) as h; subst
end : pi.

Lemma closed_extract_proof_irrelevance {p} :
  forall hs c,
  forall x y : @closed_extract p hs c,
    x = y.
Proof.
  intros.
  destruct c; allsimpl.
  apply UIP_dec.
  apply bool_dec.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : closed_extract ?hs ?c , H2 : closed_extract ?hs ?c |- _ ] =>
    pose proof (closed_extract_proof_irrelevance hs c H2 H1) as h; subst
end : pi.

Lemma closed_type_proof_irrelevance {p} :
  forall hs c,
  forall x y : @closed_type p hs c,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : closed_type ?hs ?c , H2 : closed_type ?hs ?c |- _ ] =>
    pose proof (closed_type_proof_irrelevance hs c H2 H1) as h; subst
end : pi.

(* end hide *)

(**

  We can now define sequents.  A ``bare'' sequent is a pair of a
  ``bare'' list of hypotheses and a ``bare'' conclusion (which are
  just called [conclusion]s here).

*)

Record baresequent {p} := {hyps : @barehypotheses p; concl : @conclusion p}.

(* begin hide *)

Definition mk_baresequent {p} (hyps : barehypotheses) (concl : @conclusion p) : baresequent :=
  {| hyps := hyps; concl := concl |}.

Definition mk_bsequent {p} := @mk_baresequent p.
Definition mk_bseq {p} := @mk_baresequent p.

Notation "H ||- C" := (mk_baresequent H C) (at level 0).

(*
Definition wf_conclusion (hs : hypotheses) (c : conclusion) :=
  wf_concl (projT1 hs) c.
*)

(* end hide *)

(**

  A sequent is well-formed if its hypotheses and conclusion are
  well-formed.

*)

Definition wf_sequent {p} (S : @baresequent p) :=
  vswf_hypotheses [] (hyps S)
  # wf_concl (concl S).

(* begin hide *)

Lemma wf_hypotheses_proof_irrelevance {p} :
  forall h,
  forall x y : @wf_hypotheses p h,
    x = y.
Proof.
  sp.
  induction x.
Abort.

(* end hide *)

(**

  A sequent is a ``bare'' sequent along with a proof that it is
  well-formed.

*)

Definition sequent {p} := { s : @baresequent p & wf_sequent s}.

(* begin hide *)

Definition mk_wf_seq {p}
           (s : @baresequent p)
           (w : wf_sequent s) : sequent :=
  existT wf_sequent s w.

Definition mk_sequent {p}
           (hs : @barehypotheses p)
           (c  : conclusion)
           (hp : wf_hypotheses hs)
           (cp : wf_concl c) : sequent :=
  existT wf_sequent (mk_baresequent hs c) (pair (vswf_hypotheses_nil_if hs hp) cp).

(* end hide *)

(**

  Let us now define a few concepts that are useful to define various
  degrees of well-formedness of sequents.  A ``bare'' sequent is said
  to be closed if its conclusion is closed w.r.t. to the hypotheses.
  First we define the notion of a [ctsequent] which is a sequent where
  its type is closed.  Then, we define the notion of a [csequent]
  (closed sequent) which is a ctsequent where its extract is closed.

*)

Definition closed_type_baresequent {p} (s : @baresequent p) :=
  closed_type (hyps s) (concl s).
Hint Unfold closed_type_baresequent.

Definition closed_type_sequent {p} (s : @sequent p) :=
  closed_type_baresequent (projT1 s).
Hint Unfold closed_type_sequent.

Definition ctsequent {p} := { s : @sequent p & closed_type_sequent s}.

Definition closed_extract_baresequent {p} (S : @baresequent p) :=
  closed_extract (hyps S) (concl S).
Hint Unfold closed_extract_baresequent.

Definition closed_extract_sequent {p} (s : @sequent p) :=
  closed_extract_baresequent (projT1 s).
Hint Unfold closed_extract_sequent.

Definition closed_extract_ctsequent {p} (s : @ctsequent p) :=
  closed_extract_sequent (projT1 s).
Hint Unfold closed_extract_ctsequent.

Definition csequent {p} := {s : @ctsequent p & closed_extract_ctsequent s}.

(* begin hide *)

Definition mk_ctseq {p} (s : @sequent p) (c : closed_type_sequent s) : ctsequent :=
  existT closed_type_sequent s c.

Definition mk_ctsequent {p}
           (hs : @barehypotheses p)
           (c  : conclusion)
           (wh : wf_hypotheses hs)
           (wc : wf_concl c)
           (ct : closed_type hs c) : ctsequent :=
  existT closed_type_sequent (mk_sequent hs c wh wc) ct.

Definition mk_cseq {p} (s : @ctsequent p) (c : closed_extract_ctsequent s) : csequent :=
  existT closed_extract_ctsequent s c.

Definition mk_csequent {p}
           (hs : @barehypotheses p)
           (c  : conclusion)
           (wh : wf_hypotheses hs)
           (wc : wf_concl c)
           (ct : closed_type hs c)
           (cl : closed_extract hs c) : csequent :=
  mk_cseq (mk_ctsequent hs c wh wc ct) cl.

Definition wf_csequent {p} (s : @baresequent p) :=
  wf_sequent s
  # closed_type (hyps s) (concl s)
  # closed_extract (hyps s) (concl s).

Lemma eq_baresequent {o} :
  forall s1 s2 : @baresequent o,
    hyps s1 = hyps s2 -> concl s1 = concl s2 -> s1 = s2.
Proof.
  introv e1 e2; destruct s1, s2; allsimpl; subst; auto.
Qed.

Lemma eq_concl_ext {o} :
  forall t1 t2 e1 e2 : @NTerm o,
    t1 = t2 -> e1 = e2 -> concl_ext t1 e1 = concl_ext t2 e2.
Proof.
  sp; subst; auto.
Qed.

Lemma eq_concl_typ {o} :
  forall t1 t2 : @NTerm o,
    t1 = t2 -> concl_typ t1 = concl_typ t2.
Proof.
  sp; subst; auto.
Qed.

Lemma closed_extract_ctsequent_proof_irrelevance {p} :
  forall s : @ctsequent p,
  forall x y : closed_extract_ctsequent s,
    x = y.
Proof.
  intros.
  destruct s; allsimpl.
  allunfold @closed_extract_ctsequent; allsimpl.
  destruct x0; allsimpl.
  allunfold @closed_extract_sequent; allsimpl.
  destruct x0; allsimpl.
  allunfold @closed_extract_baresequent; allsimpl.
  apply closed_extract_proof_irrelevance.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : closed_extract_ctsequent ?s , H2 : closed_extract_ctsequent ?s |- _ ] =>
    pose proof (closed_extract_ctsequent_proof_irrelevance s H2 H1) as h; subst
end : pi.

Lemma eq_csequent {o} :
  forall s1 s2 : @csequent o,
    projT1 s1 = projT1 s2 -> s1 = s2.
Proof.
  introv e.
  destruct s1, s2; allsimpl; subst.
  eauto with pi.
Qed.

Lemma closed_type_sequent_proof_irrelevance {p} :
  forall s : @sequent p,
  forall x y : closed_type_sequent s,
    x = y.
Proof.
  intros.
  destruct s; allsimpl.
  allunfold @closed_type_sequent; allsimpl.
  destruct x0; allsimpl.
  allunfold @closed_type_baresequent; allsimpl.
  apply closed_type_proof_irrelevance.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : closed_type_sequent ?s , H2 : closed_type_sequent ?s |- _ ] =>
    pose proof (closed_type_sequent_proof_irrelevance s H2 H1) as h; subst
end : pi.

Lemma eq_ctsequent {o} :
  forall s1 s2 : @ctsequent o,
    projT1 s1 = projT1 s2 -> s1 = s2.
Proof.
  introv e.
  destruct s1, s2; allsimpl; subst.
  eauto with pi.
Qed.

Lemma wf_sequent_proof_irrelevance {p} :
  forall s : @baresequent p,
  forall x y : wf_sequent s,
    x = y.
Proof.
  intros.
  destruct s; allsimpl.
  allunfold @wf_sequent; allsimpl; repnd.
  pose proof (wf_concl_proof_irrelevance concl0 x y); subst.
  pose proof (vswf_hypotheses_proof_irrelevance [] hyps0 x0 y0); subst; auto.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : wf_sequent ?s , H2 : wf_sequent ?s |- _ ] =>
    pose proof (wf_sequent_proof_irrelevance s H2 H1) as h; subst
end : pi.

Lemma eq_sequent {o} :
  forall s1 s2 : @sequent o,
    projT1 s1 = projT1 s2 -> s1 = s2.
Proof.
  introv e.
  destruct s1, s2; allsimpl; subst.
  eauto with pi.
Qed.

Lemma wf_csequent_proof_irrelevance {p} :
  forall s : @baresequent p,
  forall x y : wf_csequent s,
    x = y.
Proof.
  intros.
  allunfold @wf_csequent; allsimpl; repnd.
  eauto with pi.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : wf_csequent ?s , H2 : wf_csequent ?s |- _ ] =>
    pose proof (wf_csequent_proof_irrelevance s H2 H1) as h; subst
end : pi.


Ltac proof_irr :=
  repeat (first
            [ progress clear_irr
            | match goal with
                | [ H1 : wf_concl ?a,           H2 : wf_concl ?a           |- _ ] => assert (H2 = H1) by apply wf_concl_proof_irrelevance; subst
                | [ H1 : wf_term_op ?a,         H2 : wf_term_op ?a         |- _ ] => assert (H2 = H1) by apply wf_term_op_proof_irrelevance; subst
                | [ H1 : covered_op ?a ?b,      H2 : covered_op ?a ?b      |- _ ] => assert (H2 = H1) by apply covered_op_proof_irrelevance; subst
                | [ H1 : cover_vars_op ?a ?b,   H2 : cover_vars_op ?a ?b   |- _ ] => assert (H2 = H1) by apply covered_op_proof_irrelevance; subst
                | [ H1 : closed_extract ?a ?b,  H2 : closed_extract ?a ?b  |- _ ] => assert (H2 = H1) by apply closed_extract_proof_irrelevance; subst
                | [ H1 : closed_type ?a ?b,     H2 : closed_type ?a ?b     |- _ ] => assert (H2 = H1) by apply closed_type_proof_irrelevance; subst
                (*| [ H1 : wf_hypotheses ?a,      H2 : wf_hypotheses ?a      |- _ ] => assert (H2 = H1) by apply wf_hypotheses_proof_irrelevance; subst*)
                | [ H1 : vswf_hypotheses ?a ?b, H2 : vswf_hypotheses ?a ?b |- _ ] => assert (H2 = H1) by apply vswf_hypotheses_proof_irrelevance; subst
                (*| [ H1 : wf_sequent ?a,         H2 : wf_sequent ?a         |- _ ] => assert (H2 = H1) by apply wf_sequent_proof_irrelevance; subst*)
                (*| [ H1 : wf_csequent ?a,        H2 : wf_csequent ?a        |- _ ] => assert (H2 = H1) by apply wf_csequent_proof_irrelevance; subst*)
              end
         ]).

Ltac PI :=
  repeat (first
            [ progress clear_irr
            | progress proof_irr
            | match goal with
                | [ H1 : wf_sequent ?a,  H2 : wf_sequent ?a  |- _ ] => assert (H2 = H1) by apply wf_sequent_proof_irrelevance;  subst
                | [ H1 : wf_csequent ?a, H2 : wf_csequent ?a |- _ ] => assert (H2 = H1) by apply wf_csequent_proof_irrelevance; subst

                | [ H1 : closed_type_sequent      ?a, H2 : closed_type_sequent      ?a |- _ ] => assert (H2 = H1) by apply closed_type_sequent_proof_irrelevance;      subst
                | [ H1 : closed_extract_ctsequent ?a, H2 : closed_extract_ctsequent ?a |- _ ] => assert (H2 = H1) by apply closed_extract_ctsequent_proof_irrelevance; subst
              end
         ]).

Definition mk_wcseq {p}
           (s : @baresequent p)
           (w : wf_csequent s) : csequent :=
  mk_csequent (hyps s)
              (concl s)
              (vswf_hypotheses_nil_implies (hyps s) (fst (fst w)))
              (snd (fst w))
              (fst (snd w))
              (snd (snd w)).

Definition baresequent_type {p} (s : @baresequent p) : NTerm :=
  ctype (concl s).

(*
Inductive sequent' : Type :=
  | seq : forall hyps : hypotheses,
          forall c : conclusion,
            assert (subsetb eq_dec_var (free_vars (ctype   c)) (vars_hypotheses hyps))
            -> assert (subsetb eq_dec_var (free_vars (extract c)) (vars_hypotheses hyps))
            -> sequent'.
*)

(*Definition mk_sequent (s : baresequent) (p : wf_sequent s) : sequent :=
  exist wf_sequent s p.*)

(*
Definition mk_seq
           (hs : hypotheses)
           (c  : conclusion)
           (p  : wf_conclusion hs c) : sequent :=
  existT wf_sequent (mk_baresequent hs c) p.
*)

(* end hide *)

(**

  We now define rules.  A non ``bare'' rule (simply called a [rule]
  here) is a main sequent called [goal], a list of subgoals and a list
  of arguments or side-conditions.  A side-condition can either be a
  condition on a variable [v], which means that the variable [v] has
  to be fresh (we have not had to use these yet), or a condition on a
  term [t], which means that the free variables of [t] have to be
  declared as non-hidden in the hypotheses of the main goal of the
  rule.

*)

Inductive sarg {p} :=
  | sarg_var : NVar -> sarg
  | sarg_term : @NTerm p -> sarg.

Record rule {p} :=
  {goal       : @baresequent p
   ; subgoals : list (@baresequent p)
   ; sargs    : list (@sarg p)
  }.

Definition mk_rule {p}
             (goal     : @baresequent p)
             (subgoals : list baresequent)
             (args     : list sarg) :=
  {| goal := goal; subgoals := subgoals; sargs := args |}.

(* begin hide *)


(* --- Substitutions over hypotheses *)


(* end hide *)

(**

  We now provide the definition of what it means for sequents and
  rules to be true.  There have been several definitions over the
  years.  We present four versions: one that is presented in the Nuprl
  book%~\cite{Allen+al:2006}%, one that is presented by Karl Crary in
  his thesis%~\cite{Crary:1998}%, one that is presented by Aleksey
  Nogin in his thesis%~\cite{Nogin:2002}%, and finally one which we
  obtained by simplifying Nogin's definition.  We then show that all
  these definitions are equivalent.  We are then free to use the one
  we want.  Crary's definition is similar to the one provided in
  Nuprl's Book.  The main difference is that Crary uses substitutions
  while the definition from the Book uses lists of terms
  (substitutions are then built from lists of terms and lists of
  hypotheses).  Nogin's definition differs by having not a pointwise
  requirement on each hypothesis but instead a more global pointwise
  requirement on the entire list of hypotheses.

  In order to introduce these definitions, we first need various
  abstractions on hypotheses:

  - [hyps_true_at H ts] which is used by the Book's definition and
    should be read: ``the list of hypotheses [H] is true at the list
    of terms [ts]''.

  - [equal_terms_in_hyps ts1 ts2 H] which is also use by the Book's
    definition and should be read: ``the two lists of terms [ts1] and
    [ts2] are equal in the list of hypotheses [H].  This can be seen
    as a lifting operation of the [equality] relation from types to
    lists of hypotheses.

  - [pw_assign_eq s1 s2 H] which is used in Crary's definition and
    should be read: ``the two substitutions [s1] and [s2] are
    pointwise equal in the list of hypotheses [H]''.

  - [similarity s1 s2 H] which is used in both Crary and Nogin's
    definitions and should be read: ``the two substitutions [s1] and
    [s2] are similar in [H]''.  This can be seen as a simple lifting
    operation of the [equality] relation from types to lists of
    hypotheses.

  - [eq_hyps s1 s2 H] which is used in Nogin's definition and is a
    simple lifting operation of the [tequality] relation from types to
    lists of hypotheses.

  - [hyps_functionality s H] which is also used in Nogin's definition
    and should be read: ``the hypotheses [H] are functional w.r.t. the
    substitution [s]''.

*)

(**

  Along the way we also define a few other useful abstractions.  For
  example, [mk_hs_subst] is used in the Book's definition to build a
  substitution from a list of terms and a list of hypotheses.

*)

Fixpoint mk_hs_subst {p}
           (ts : list CTerm)
           (hs : @barehypotheses p) : @CSub p :=
  match ts, hs with
  | nil, _ => nil
  | _, nil => nil
  | t :: ts, h :: hs => (hvar h, t) :: mk_hs_subst ts hs
  end.

(* begin hide *)

Lemma mk_hs_subst_nil_hs {p} :
  forall ts, @mk_hs_subst p ts [] = [].
Proof.
  destruct ts; simpl; auto.
Qed.

Lemma mk_hs_subst_nil_ts {p} :
  forall hs, @mk_hs_subst p [] hs = [].
Proof.
  destruct hs; simpl; auto.
Qed.

Lemma in_mk_hs_subst {p} :
  forall ts hs v u,
    LIn (v, u) (@mk_hs_subst p ts hs)
    -> LIn u ts.
Proof.
  induction ts; simpl; sp.
  destruct hs; simpl in X; sp; cpx.
  apply IHts in l; sp.
Qed.

Lemma mk_hs_subst_snoc {p} :
  forall ts hs t h,
    length hs = length ts ->
    @mk_hs_subst p (snoc ts t) (snoc hs h) = snoc (mk_hs_subst ts hs) (hvar h, t).
Proof.
  induction ts; simpl; sp; destruct hs; simpl in H; simpl; auto; inversion H.
  apply IHts with (t := t) (h := h) in H1.
  rewrite H1; auto.
Qed.

Lemma mk_hs_subst_app {p} :
  forall ts1 ts2 hs1 hs2,
    length hs1 = length ts1
    -> @mk_hs_subst p (ts1 ++ ts2) (hs1 ++ hs2)
       = mk_hs_subst ts1 hs1 ++ mk_hs_subst ts2 hs2.
Proof.
  induction ts1; simpl; sp; destruct hs1; simpl; sp; simpl in H; inversion H.
  rewrite IHts1; auto.
Qed.

Lemma dom_mk_hs_subst {p} :
  forall G ts,
    length ts = length G
    -> @vars_hyps p G = dom_csub (mk_hs_subst ts G).
Proof.
  induction G; simpl; sp; destruct ts; allsimpl; auto; inversion H.
  apply IHG in H1.
  rewrite H1; auto.
Qed.

Lemma cover_vars_mk_hs_subst {p} :
  forall t ts hs,
    length ts = length hs
    -> (cover_vars t (@mk_hs_subst p ts hs) <=> covered t (vars_hyps hs)).
Proof.
  intros.
  rw @cover_vars_eq.
  unfold covered.
  rewrite <- dom_mk_hs_subst; sp.
Qed.

Lemma cover_vars_sub {p} :
  forall t s hs,
    @vars_hyps p hs = dom_csub s
    -> (cover_vars t s <=> cover_vars t (mk_hs_subst (crange s) hs)).
Proof.
  sp.
  rw @cover_vars_covered.
  symm. (* huh??? *)
  rw @cover_vars_covered.
  rewrite <- dom_mk_hs_subst.
  rewrite H; sp.
  rewrite <- vars_hyps_length.
  rewrite H.
  rewrite dom_csub_length.
  rewrite <- crange_length.
  rewrite crange_length; sp.
Qed.

Lemma mk_hs_subst_crange {p} :
  forall hs s,
    @vars_hyps p hs = dom_csub s
    -> mk_hs_subst (crange s) hs = s.
Proof.
  induction hs; simpl; sp; destruct s; allsimpl; sp; inversion H; subst; allsimpl.
  apply IHhs in H2.
  rewrite H2; sp.
Qed.

Lemma length_mk_hs_subst {p} :
  forall hs ts,
    length (@mk_hs_subst p ts hs) = length hs
    -> length ts >= length hs.
Proof.
  induction hs; simpl; sp; destruct ts; allsimpl; sp; try omega; inj.
  apply_in_hyp pp; omega.
Qed.

Lemma wf_hypotheses_disj_subst {p} :
  forall G x A J ts1 ts2,
    length ts1 = length G
    -> length ts2 = length J
    -> wf_hypotheses (snoc G (@mk_hyp p x A) ++ J)
    -> disjoint (free_vars A) (dom_csub (mk_hs_subst ts2 J))
       # disjoint (free_vars (@mk_var p x)) (dom_csub (mk_hs_subst ts2 J))
       # disjoint (free_vars (@mk_var p x)) (dom_csub (mk_hs_subst ts1 G))
       # !LIn x (free_vars A).
Proof.
  intros.
  allapply @wf_hypotheses_disj; repd.
  repeat (rewrite <- dom_mk_hs_subst); auto; sp;
  unfold disjoint; simpl; sp; subst; auto.
Qed.

(** mk_hyps_subst is the same as mk_hs_subst but on wf hypotheses *)
Definition mk_hyps_subst {p} (ts : list (@CTerm p)) (hyps : hypotheses) : CSub :=
  mk_hs_subst ts (projT1 hyps).

(** substitute_hyp applies a substitution to the type of an hypothesis *)
Definition substitute_hyp {p} (sub : @CSub p) (h : hypothesis) : hypothesis :=
  match h with
  | {| hvar := hv; hidden := hi; htyp := ht; lvl := l |} =>
      {| hvar := hv; hidden := hi; htyp := csubst ht sub; lvl := l |}
  end.

(** substitute_hyps applies a substitution to all the types of a list of
 * hypotheses. *)
Fixpoint substitute_hyps {p} (sub : @CSub p) (hs : barehypotheses) : barehypotheses :=
  match hs with
    | [] => []
    | h :: hs => substitute_hyp sub h :: substitute_hyps sub hs
  end.

Lemma is_nh_substitute_hyp {p} :
  forall sub a,
    is_nh (@substitute_hyp p sub a) = is_nh a.
Proof.
  intros.
  destruct a; simpl; sp.
Qed.

Lemma substitute_hyp_nil_sub {p} :
  forall h, @substitute_hyp p [] h = h.
Proof.
  intro; unfold substitute_hyp.
  destruct h.
  rewrite csubst_nil; auto.
Qed.

Lemma substitute_hyps_nil_sub {p} :
  forall hs, @substitute_hyps p [] hs = hs.
Proof.
  induction hs; simpl; auto.
  repeat (rewrite IHhs).
  rewrite substitute_hyp_nil_sub; auto.
Qed.

Lemma substitute_hyps_snoc {p} :
  forall sub hs h, @substitute_hyps p sub (snoc hs h) = snoc (substitute_hyps sub hs) (substitute_hyp sub h).
Proof.
  induction hs; simpl; auto; intros.
  repeat (rewrite IHhs); auto.
Qed.

Lemma substitute_hyps_cons {p} :
  forall sub h hs,
    @substitute_hyps p sub (h :: hs)
    = substitute_hyp sub h :: substitute_hyps sub hs.
Proof.
  simpl; auto.
Qed.

Lemma mk_hs_subst_substitute_hyps {p} :
  forall ts sub hs,
    mk_hs_subst ts (@substitute_hyps p sub hs) = mk_hs_subst ts hs.
Proof.
  induction ts; simpl; intros; auto.
  destruct hs; simpl; auto.
  rewrite IHts.
  destruct h; simpl; auto.
Qed.

Lemma hvar_substitute_hyp {p} :
  forall sub a,
    hvar (@substitute_hyp p sub a) = hvar a.
Proof.
  destruct a; sp.
Qed.

Hint Rewrite @hvar_substitute_hyp : core.

Lemma htyp_substitute_hyp {p} :
  forall sub a,
    htyp (@substitute_hyp p sub a) = csubst (htyp a) sub.
Proof.
  destruct a; sp.
Qed.

Hint Rewrite @htyp_substitute_hyp : core.

Lemma lvl_substitute_hyp {p} :
  forall sub a,
    lvl (@substitute_hyp p sub a) = lvl a.
Proof.
  destruct a; sp.
Qed.

Hint Rewrite @lvl_substitute_hyp : core.

Lemma vars_hyps_substitute_hyps {p} :
  forall sub hs,
    vars_hyps (@substitute_hyps p sub hs) = vars_hyps hs.
Proof.
  induction hs; simpl; sp.
  rewrite IHhs.
  rewrite hvar_substitute_hyp; sp.
Qed.

Hint Rewrite @vars_hyps_substitute_hyps : core.

Lemma nh_vars_hyps_substitute_hyps {p} :
  forall sub hs,
    nh_vars_hyps (@substitute_hyps p sub hs) = nh_vars_hyps hs.
Proof.
  induction hs; simpl; sp.
  repeat (rewrite nh_vars_hyps_cons).
  rewrite IHhs.
  rewrite is_nh_substitute_hyp.
  rewrite hvar_substitute_hyp; sp.
Qed.

Hint Rewrite @nh_vars_hyps_substitute_hyps : core.

Lemma length_substitute_hyps {p} :
  forall sub hs,
    length (@substitute_hyps p sub hs) = length hs.
Proof.
  induction hs; simpl; sp.
Qed.

Hint Rewrite @length_substitute_hyps : core.

Lemma substitute_hyp_snoc_sub_weak {p} :
  forall h sub v t,
    ! LIn v (free_vars (@htyp p h))
    -> substitute_hyp (snoc sub (v, t)) h
       = substitute_hyp sub h.
Proof.
  destruct h; unfold hyp_free_vars; simpl; sp.
  assert (csubst htyp0 (snoc sub (v, t)) = csubst htyp0 sub) as eq;
    try (rewrite eq); sp.
  apply subset_free_vars_csub_snoc; sp.
Qed.

Lemma substitute_hyps_snoc_sub_weak {p} :
  forall hs sub v t,
    ! LIn v (@free_vars_hyps p hs)
    -> ! LIn v (vars_hyps hs)
    -> substitute_hyps (snoc sub (v, t)) hs
       = substitute_hyps sub hs.
Proof.
  induction hs; simple; sp.
  allrewrite subvars_app_l; sp.
  allrewrite subvars_remove_nvars; sp.
  rewrite IHhs; sp.
  rewrite substitute_hyp_snoc_sub_weak; sp.
  rw in_app_iff in H.
  apply H; left; auto.
  rw in_app_iff in H.
  rw in_remove_nvars in H; allsimpl.
  apply H; right; sp.
Qed.


(* --- Equality on and truth of hypotheses *)


(* end hide *)

(**

  As mentioned above, Crary (as well as Nogin) defines a relation
  called ``assignment similarity''%~\cite[page~56]{Crary:1998}% which
  we call [similarity].  The Nuprl book defines a similar relation
  that we call [equal_terms_in_hyps].

  Two substitutions [s1] and [s2] are similar in a list of hypotheses
  [H] if [s1] is of the form [[(x1,t1),...,(xn,tn)]], [s2] is of the
  form [[(x1,u1),...,(xn,un)]], [H] is of the form
  [[(x1,T1),...,(xn,Tn)]], and [t1] = [u1] in [T1], [t2] = [u2] in
  [T2[(x1,t1)]], [t3] = [u3] in [T3[(x1,t1),(x2,t2)]],...

 *)

Inductive similarity {o} (lib : @library o) : @CSub o -> @CSub o -> @bhyps o -> [U] :=
  | sim_nil : similarity lib nil nil nil
  | sim_cons :
      forall t1 t2 : CTerm,
      forall s1 s2 : CSubstitution,
      forall h   : hypothesis,
      forall hs  : barehypotheses,
      forall w   : wf_term (htyp h),
      forall p   : cover_vars (htyp h) s1,
      forall e   : equality lib t1 t2 (lsubstc (htyp h) w s1 p),
      forall sim : similarity lib s1 s2 hs,
        similarity lib
                   (snoc s1 (hvar h, t1))
                   (snoc s2 (hvar h, t2))
                   (snoc hs h).

(* begin hide *)

Lemma similarity_refl {o} :
  forall lib (hs : @bhyps o) s1 s2,
    similarity lib s1 s2 hs
    -> similarity lib s1 s1 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv sim;
  inversion sim; subst; allsimpl; cpx.

  discover.
  apply @sim_cons with (w := w) (p := p); sp.
  rewrite member_eq.
  apply @equality_refl with (t2 := t2); sp.
Qed.

Lemma similarity_dom {o} :
  forall lib (hs : @bhyps o) s1 s2,
    similarity lib s1 s2 hs
    -> dom_csub s1 = vars_hyps hs
       # dom_csub s2 = vars_hyps hs.
Proof.
  induction hs using rev_list_indT; simpl; introv sim;
  inversion sim; subst; allsimpl; cpx.

  repeat (rewrite dom_csub_snoc); simpl.
  rewrite vars_hyps_snoc.
  discover; repnd; allrw; sp.
Qed.

Lemma similarity_cover_vars {o} :
  forall lib (hs : @bhyps o) s1 s2 t,
    similarity lib s1 s2 hs
    -> cover_vars t s1
    -> cover_vars t s2.
Proof.
  introv sim c.
  apply similarity_dom in sim; repd.
  allrw @cover_vars_eq.
  rw e0; rw <- e; sp.
Qed.

Lemma similarity_cover_vars_upto {o} :
  forall lib (hs : @bhyps o) s1 s2 vs t,
    similarity lib s1 s2 hs
    -> cover_vars_upto t (csub_filter s1 vs) vs
    -> cover_vars_upto t (csub_filter s2 vs) vs.
Proof.
  introv sim c.
  apply similarity_dom in sim; repd.
  allunfold @cover_vars_upto.
  allrw @dom_csub_csub_filter.
  rw e0; rw <- e; sp.
Qed.

Lemma subvars_if_cover_vars_sim {o} :
  forall lib t s1 s2 (H : @bhyps o),
    cover_vars t s1
    -> similarity lib s1 s2 H
    -> subvars (free_vars t) (vars_hyps H).
Proof.
  introv cv sim.
  allapply @similarity_dom; repnd.
  allrw @cover_vars_eq.
  provesv.
  rw <- sim0; sp.
Qed.

Lemma similarity_length {o} :
  forall lib (hs : @bhyps o) s1 s2,
    similarity lib s1 s2 hs
    -> (length s1 = length hs # length s2 = length hs).
Proof.
  induction hs using rev_list_indT; simpl; introv sim; inversion sim; subst; cpx.

  repeat (rewrite length_snoc).
  discover; sp.
Qed.

Lemma similarity_app {o} :
  forall lib (hs1 hs2 : @bhyps o) s1 s2,
    similarity lib s1 s2 (hs1 ++ hs2)
    <=>
    {s1a, s1b, s2a, s2b : CSub ,
      s1 = s1a ++ s1b
      # s2 = s2a ++ s2b
      # length s1a = length hs1
      # length s2a = length hs1
      # similarity
           lib
           s1a
           s2a
           hs1
      # similarity
           lib
           s1b
           s2b
           (substitute_hyps s1a hs2)}.
Proof.
  induction hs2 using rev_list_indT; simpl; introv.

  - rewrite app_nil_r; split; intro k; exrepnd; subst.

    + allapplydup @similarity_length; repnd.
      exists s1 (nil : @CSub o) s2 (nil : @CSub o); simpl; sp;
      allrewrite app_nil_r; auto.

    + inversion k1; subst; allrewrite app_nil_r; auto; cpx.

  - rewrite snoc_append_l; split; intro k; exrepnd; subst.

    + inversion k; cpx.
      allapplydup IHhs2; exrepnd; subst.
      exists s1a (snoc s1b (hvar a, t1)) s2a (snoc s2b (hvar a, t2)).
      repeat (rewrite snoc_append_l); sp.
      rewrite substitute_hyps_snoc; simpl.
      assert (hvar a = hvar (substitute_hyp s1a a))
        as heq
          by (destruct a; simpl; auto).
      rewrite heq.

      assert (wf_term (htyp (substitute_hyp s1a a)))
        as w0
          by (destruct a; allsimpl;
              apply csubst_preserves_wf_term; sp;
              allapply in_csub2sub; allunfold isprogram; rw wf_term_eq; sp).

      assert (cover_vars (htyp (substitute_hyp s1a a)) s1b)
        as c0
          by (destruct a; allsimpl; rw <- @cover_vars_csubst; auto).

      apply @sim_cons with (w := w0) (p := c0); sp.
      destruct a; allsimpl.
      rewrite lsubstc_csubst_eq with (w' := w) (p' := p); auto.

    + allrewrite @substitute_hyps_snoc.
      inversion k1; subst; cpx.
      allrewrite @hvar_substitute_hyp.
      repeat (rewrite snoc_append_l).

      assert (wf_term (htyp a))
        as w0
          by (destruct a; allsimpl;
              clear_dependents w;
              apply csubst_wf_term in w; auto).

      assert (cover_vars (htyp a) (s1a ++ s1))
        as c0
          by (destruct a; allsimpl;
              allrw @cover_vars_csubst; sp).

      apply @sim_cons with (w := w0) (p := c0); sp.

      revert_dependents w.
      revert_dependents p.
      rw @htyp_substitute_hyp; introv e.
      rewrite lsubstc_csubst_eq with (w' := w0) (p' := c0) in e; sp.

      rw IHhs2.
      exists s1a s1 s2a s2; sp.
Qed.

Lemma similarity_snoc {o} :
  forall lib (hs : @bhyps o) h s1 s2,
    similarity lib s1 s2 (snoc hs h)
    <=>
    {s1a, s2a : CSub
     , {t1, t2 : CTerm
     , {w : wf_term (htyp h)
     , {p : cover_vars (htyp h) s1a
        , s1 = snoc s1a (hvar h, t1)
        # s2 = snoc s2a (hvar h, t2)
        # similarity lib s1a s2a hs
        # equality lib t1 t2 (lsubstc (htyp h) w s1a p)}}}}.
Proof.
  sp.
  rewrite snoc_as_append.
  rw @similarity_app; simpl; split; intro k; exrepnd; subst.

  - inversion k1 as [| t1 t2 h0 hs0 h1 hs1 w p e sim]; subst.
    destruct hs1; allsimpl; cpx.
    inversion sim; subst; allsimpl; cpx.
    revert_dependents w; revert_dependents p.
    rewrite htyp_substitute_hyp; introv e.

    duplicate w as w0.
    apply csubst_wf_term in w.
    duplicate p as p0.
    rw <- @cover_vars_csubst in p.
    rewrite lsubstc_csubst_eq with (w' := w) (p' := p) in e.
    revert_dependents p.
    rewrite app_nil_r; sp.
    exists s1a s2a t1 t2 w p.
    repeat (rewrite <- snoc_as_append).
    rewrite hvar_substitute_hyp; sp.

  - exists s1a [(hvar h, t1)] s2a [(hvar h, t2)].
    allrw <- snoc_as_append.
    allapplydup @similarity_length; repnd; sp.

    allrw singleton_as_snoc.

    assert (hvar h = hvar (substitute_hyp s1a h))
      as heq
        by (rewrite hvar_substitute_hyp; sp).
    rewrite heq.

    assert (wf_term (htyp (substitute_hyp s1a h)))
      as w0
        by (rewrite htyp_substitute_hyp; apply wf_term_csubst; sp).

    assert (cover_vars (htyp (substitute_hyp s1a h)) [])
      as c0
        by (rewrite htyp_substitute_hyp;
            rw <- @cover_vars_csubst;
            rewrite app_nil_r; sp).

    apply @sim_cons with (w := w0) (p := c0); sp; try constructor.
    revert w0 c0.
    rewrite htyp_substitute_hyp; sp.

    assert (cover_vars (htyp h) (s1a ++ [])) as p1 by (rewrite app_nil_r; sp).
    rewrite lsubstc_csubst_eq with (w' := w) (p' := p1).
    revert p1; rewrite app_nil_r; sp.
    clear_irr; sp.
Qed.

Lemma similarity_hhyp {o} :
  forall lib s1 s2 (H : @bhyps o) x A J,
    similarity lib s1 s2 (snoc H (mk_hyp x A) ++ J)
    <=>
    similarity lib s1 s2 (snoc H (mk_hhyp x A) ++ J).
Proof.
  sp; sp_iff Case.

  - Case "->"; intro.
    allrw @similarity_app; sp; subst; cpx.
    exists s1a s1b s2a s2b; rewrite length_snoc; sp.
    allrw @similarity_snoc; sp.

  - Case "<-"; intros.
    allrw @similarity_app; sp; subst; cpx.
    exists s1a s1b s2a s2b; rewrite length_snoc; sp.
    allrw @similarity_snoc; sp.
Qed.


(* end hide *)

(**

  The [equal_terms_in_hyps] relation is used in the Book's definition
  and is similar to the [similarity] relation except that it is
  defined on lists of terms rather than on substitutions.

 *)

Inductive equal_terms_in_hyps {o} (lib : @library o) :
  list (@CTerm o)
  -> list (@CTerm o)
  -> (@bhyps o) -> [U] :=
| EqInHyps_nil : equal_terms_in_hyps lib nil nil nil
| EqInHyps_cons :
    forall t1  t2  : CTerm,
    forall ts1 ts2 : list CTerm,
    forall h       : hypothesis,
    forall hs      : barehypotheses,
    forall w       : wf_term (htyp h),
    forall p       : cover_vars (htyp h) (mk_hs_subst ts1 hs),
    forall e       : equality lib t1 t2 (lsubstc (htyp h) w (mk_hs_subst ts1 hs) p),
    forall eqt     : equal_terms_in_hyps lib ts1 ts2 hs,
      equal_terms_in_hyps lib (snoc ts1 t1) (snoc ts2 t2) (snoc hs h).

(* begin hide *)

Lemma equal_terms_in_hyps_length {o} :
  forall lib (hs : @bhyps o) ts1 ts2,
    equal_terms_in_hyps lib ts1 ts2 hs
    -> (length hs = length ts1 # length hs = length ts2).
Proof.
  introv e; induction e; simpl; auto.
  repeat (rewrite length_snoc); sp.
Qed.

Lemma equal_terms_in_hyps_app {o} :
  forall lib (hs1 hs2 : @bhyps o) ts1 ts2,
    equal_terms_in_hyps lib ts1 ts2 (hs1 ++ hs2)
    -> {ts1a, ts1b, ts2a, ts2b : list CTerm ,
         ts1 = ts1a ++ ts1b
         # ts2 = ts2a ++ ts2b
         # length ts1a = length hs1
         # length ts2a = length hs1
         # equal_terms_in_hyps
              lib
              ts1a
              ts2a
              hs1
         # equal_terms_in_hyps
              lib
              ts1b
              ts2b
              (substitute_hyps (mk_hs_subst ts1a hs1) hs2)}.
Proof.
  induction hs2 using rev_list_indT; simpl; introv e.

  - exists ts1 (nil : list (@CTerm o)) ts2 (nil : list (@CTerm o)); simpl; sp;
           allrewrite app_nil_r; auto.
           apply equal_terms_in_hyps_length in e; sp.
           apply equal_terms_in_hyps_length in e; sp.

  - rewrite snoc_append_l in e.

    rev_list_dest ts1.
    apply equal_terms_in_hyps_length in e; simpl in e; sp.
    allrw length_snoc; sp.

    rev_list_dest ts2.
    apply equal_terms_in_hyps_length in e; simpl in e; sp.
    allrw length_snoc; sp.

    inversion e; subst; cpx.
    discover; exrepnd; subst.
    exists ts1a (snoc ts1b v) ts2a (snoc ts2b v0); sp; subst;
    try (complete (rewrite snoc_append_l; auto)).

    rewrite substitute_hyps_snoc.

    assert (wf_term (htyp (substitute_hyp (mk_hs_subst ts1a hs1) a))) as w'.
    destruct a; allsimpl.
    apply lsubst_preserves_wf_term; sp.
    allapply @in_csub2sub; allunfold @isprogram; allrw @nt_wf_eq; sp.

    assert (cover_vars (htyp (substitute_hyp (mk_hs_subst ts1a hs1) a))
                       (mk_hs_subst ts1b (substitute_hyps (mk_hs_subst ts1a hs1) hs2))) as c.
    destruct a; allsimpl.
    rw <- @cover_vars_csubst.
    rewrite mk_hs_subst_substitute_hyps.
    clear_dependents p.
    rewrite mk_hs_subst_app in p; auto.

    apply @EqInHyps_cons with (w := w') (p := c); auto.

    revert w' c.
    rw @mk_hs_subst_substitute_hyps.
    rw @htyp_substitute_hyp; sp.
    revert_dependents p.
    rewrite mk_hs_subst_app; sp.
    rewrite @lsubstc_csubst_eq with (w' := w) (p' := p); sp.
Qed.

Lemma equal_terms_in_hyps_app_implies {o} :
  forall lib (hs1 hs2 : @bhyps o) ts1a ts1b ts2a ts2b,
    equal_terms_in_hyps
      lib
      ts1a
      ts2a
      hs1
    -> equal_terms_in_hyps
         lib
         ts1b
         ts2b
         (substitute_hyps (mk_hs_subst ts1a hs1) hs2)
    -> equal_terms_in_hyps lib (ts1a ++ ts1b) (ts2a ++ ts2b) (hs1 ++ hs2).
Proof.
  induction hs2 using rev_list_indT; simpl; introv e1 e2.

  - apply equal_terms_in_hyps_length in e2; allsimpl; sp; cpx.
    repeat (rewrite app_nil_r); auto.

  - allrw @substitute_hyps_snoc.
    inversion e2 as [| t1 t2 ts1 ts2 h hs w p e etih ]; subst; cpx; clear e2.
    repeat (rewrite snoc_append_l).
    revert_dependents w.
    revert_dependents p.
    allrw @htyp_substitute_hyp.
    rw @mk_hs_subst_substitute_hyps.
    introv e.
    allapplydup @equal_terms_in_hyps_length; repnd.

    assert (wf_term (htyp a))
      as wf
        by (destruct a; allsimpl;
            clear_dependents w;
            apply csubst_wf_term in w; auto).

    assert (cover_vars (htyp a) (mk_hs_subst (ts1a ++ ts1) (hs1 ++ hs2)))
      as cv
        by (destruct a; allsimpl;
            clear_dependents p;
            rw <- @cover_vars_csubst in p;
            rw @mk_hs_subst_app; auto).

    assert (cover_vars (htyp a) (mk_hs_subst ts1a hs1 ++ mk_hs_subst ts1 hs2))
      as cv2
        by (clear e; destruct a; allsimpl;
            rw <- @mk_hs_subst_app; sp).

    apply @EqInHyps_cons with (w := wf) (p := cv); sp.

    rewrite lsubstc_csubst_eq with (w' := wf) (p' := cv2) in e; auto.
    revert cv.
    rw @mk_hs_subst_app; sp; clear_irr; sp.
Qed.

Lemma equal_terms_in_hyps_cons {o} :
  forall lib h (hs : @bhyps o) ts1 ts2,
    equal_terms_in_hyps lib ts1 ts2 (h :: hs)
    -> {t1, t2 : CTerm
        , {ts1', ts2' : list CTerm
        , {w : wf_term (htyp h)
        , {p : cover_vars (htyp h) []
           , ts1 = t1 :: ts1'
           # ts2 = t2 :: ts2'
           # equality lib t1 t2 (lsubstc (htyp h) w [] p)
           # equal_terms_in_hyps
               lib
               ts1'
               ts2'
               (substitute_hyps [(hvar h, t1)] hs)}}}}.
Proof.
  introv e.
  rewrite cons_as_app in e.
  apply equal_terms_in_hyps_app in e; exrepnd.
  allsimpl; cpx.
  exists x0 x ts1b ts2b; simpl; sp.
  inversion e5; allsimpl; cpx.
  revert_dependents w.
  revert_dependents p.
  rewrite mk_hs_subst_nil_ts; sp.
  exists w p; sp.
Qed.

Lemma equal_terms_in_hyps_snoc {o} :
  forall lib h (hs : @bhyps o) ts1 ts2,
    equal_terms_in_hyps lib ts1 ts2 (snoc hs h)
    -> {t1, t2 : CTerm
        , {ts1', ts2' : list CTerm
        , {w : wf_term (htyp (substitute_hyp (mk_hs_subst ts1' hs) h))
        , {p : cover_vars (htyp (substitute_hyp (mk_hs_subst ts1' hs) h)) []
           , ts1 = snoc ts1' t1
           # ts2 = snoc ts2' t2
           # equal_terms_in_hyps lib ts1' ts2' hs
           # equality lib t1 t2 (lsubstc (htyp (substitute_hyp (mk_hs_subst ts1' hs) h)) w [] p)}}}}.
Proof.
  introv e.
  allrewrite snoc_as_append.
  apply equal_terms_in_hyps_app in e; exrepnd; allsimpl; subst.
  allapplydup @equal_terms_in_hyps_length; allsimpl; sp; cpx.
  inversion e1; cpx.
  exists x0 x ts1a ts2a w p; repeat (rewrite snoc_as_append); sp.
Qed.

(* end hide *)

(**

  This is the ``Assignment equality with pointwise functionality''
  relation that Crary defines on page 57 of his thesis.  This is
  different from the [hyps_true_at] relation defined in the Nuprl
  book.  The relation defined in the Nuprl book relates a list of
  terms to a list of hypotheses while Crary's relation related a pairs
  of lists of terms to a list of hypotheses.

  This relation is closer to the [similarity] relation.  However, it
  is more complicated because it has a ``pointwise'' condition that
  says that each hypothesis has to be functional w.r.t. to the
  preceding hypotheses.

 *)

Inductive pw_assign_eq {o} (lib : @library o) : @CSub o -> @CSub o -> @bhyps o -> [U] :=
  | pw_eq_nil : pw_assign_eq lib [] [] []
  | pw_eq_cons :
      forall t1 t2 : CTerm,
      forall s1 s2 : CSubstitution,
      forall h  : hypothesis,
      forall hs : barehypotheses,
      forall w  : wf_term (htyp h),
      forall p  : cover_vars (htyp h) s1,
      forall e  : equality lib t1 t2 (lsubstc (htyp h) w s1 p),
      forall hf : (forall s' : CSubstitution,
                   forall p' : cover_vars (htyp h) s',
                     similarity lib s1 s' hs
                     -> eqtypes lib
                                (lvl h)
                                (lsubstc (htyp h) w s1 p)
                                (lsubstc (htyp h) w s' p')),
      forall pw : pw_assign_eq lib s1 s2 hs,
        pw_assign_eq lib
                     (snoc s1 (hvar h, t1))
                     (snoc s2 (hvar h, t2))
                     (snoc hs h).

(* begin hide *)

Lemma pw_assign_eq_dom {o} :
  forall lib (hs : @bhyps o) s1 s2,
    pw_assign_eq lib s1 s2 hs
    -> vars_hyps hs = dom_csub s1
       # vars_hyps hs = dom_csub s2.
Proof.
  induction hs using rev_list_indT; simpl; introv pw;
  inversion pw; subst; allsimpl; sp; cpx;
  rewrite vars_hyps_snoc;
  rewrite dom_csub_snoc; simpl;
  discover; sp;
  allrw <-; sp.
Qed.

Lemma pw_assign_eq_length {o} :
  forall lib (hs : @bhyps o) s1 s2,
    pw_assign_eq lib s1 s2 hs
    -> length hs = length s1
       # length hs = length s2.
Proof.
  intros.
  allapply @pw_assign_eq_dom; repd.
  rewrite <- vars_hyps_length.
  repeat (rewrite <- dom_csub_length).
  rewrite <- e; rewrite <- e0; sp.
Qed.

(* end hide *)

(**

  Nogin can do without [pw_assign_eq] and simply use [similarity]
  because he ``lifts'' the functionality requirement so that it is not
  required to be proved for every single hypothesis but instead for
  the entire list of hypotheses.  This is achieved by the [eq_hyps]
  and [hyps_functionality] abstractions.  Having a more ``global''
  pointwise functionality requirement greatly simplifies the proofs.

 *)

Inductive eq_hyps {o} (lib : @library o) : @CSub o -> @CSub o -> @bhyps o -> [U] :=
  | eq_hyps_nil : eq_hyps lib [] [] []
  | eq_hyps_cons :
      forall t1 t2 : CTerm,
      forall s1 s2 : CSubstitution,
      forall h  : hypothesis,
      forall hs : barehypotheses,
      forall w  : wf_term (htyp h),
      forall p1 : cover_vars (htyp h) s1,
      forall p2 : cover_vars (htyp h) s2,
      forall eqt : eqtypes lib
                           (lvl h)
                           (lsubstc (htyp h) w s1 p1)
                           (lsubstc (htyp h) w s2 p2),
      forall eqh : eq_hyps lib s1 s2 hs,
        eq_hyps lib (snoc s1 (hvar h, t1)) (snoc s2 (hvar h, t2)) (snoc hs h).
Hint Constructors eq_hyps.

Definition hyps_functionality {o} lib (s : @CSub o) (H : @bhyps o) :=
  forall s' : CSubstitution,
    similarity lib s s' H -> eq_hyps lib s s' H.

(* begin hide *)

(** We now generalize Aleksey's definition to handle extra substitutions.
 * This is needed to state eq_hyps_app. *)
Inductive sub_eq_hyps {o} (lib : @library o) :
  @CSub o -> @CSub o
  -> @CSub o -> @CSub o
  -> @bhyps o
  -> [U] :=
| sub_eq_hyps_nil : forall s1 s2, sub_eq_hyps lib s1 s2 [] [] []
| sub_eq_hyps_cons :
    forall t1 t2 : CTerm,
    forall s1 s2 s3 s4 : CSubstitution,
    forall h  : hypothesis,
    forall hs : barehypotheses,
    forall w  : wf_term (htyp h),
    forall p1 : cover_vars (htyp h) (s3 ++ s1),
    forall p2 : cover_vars (htyp h) (s4 ++ s2),
    (*        tequality (lsubstc (htyp h) w (s3 ++ s1) p1)
                  (lsubstc (htyp h) w (s4 ++ s2) p2)*)
    forall eqt : eqtypes lib
                         (lvl h)
                         (lsubstc (htyp h) w (s3 ++ s1) p1)
                         (lsubstc (htyp h) w (s4 ++ s2) p2),
    forall seh : sub_eq_hyps lib s3 s4 s1 s2 hs,
      sub_eq_hyps lib s3 s4 (snoc s1 (hvar h, t1)) (snoc s2 (hvar h, t2)) (snoc hs h).
Hint Constructors sub_eq_hyps.

Lemma eq_hyps_length {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eq_hyps lib s1 s2 hs
    -> (length s1 = length hs # length s2 = length hs).
Proof.
  induction hs using rev_list_indT; simpl; introv eh;
  inversion eh; subst; simpl; cpx.

  repeat (rewrite length_snoc).
  discover; sp.
Qed.

Lemma eq_hyps_refl {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eq_hyps lib s1 s2 hs
    -> eq_hyps lib s1 s1 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv eh; inversion eh; subst; allsimpl; cpx.
  discover.
  apply @eq_hyps_cons with (w := w) (p1 := p1) (p2 := p1); sp.
  allapply @eqtypes_refl; sp.
Qed.

Lemma eq_hyps_dom {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eq_hyps lib s1 s2 hs
    -> dom_csub s1 = vars_hyps hs
       # dom_csub s2 = vars_hyps hs.
Proof.
  induction hs using rev_list_indT; simpl; introv eh; inversion eh; subst; allsimpl; cpx.
  repeat (rewrite dom_csub_snoc); simpl.
  rewrite vars_hyps_snoc.
  discover; repnd.
  allrw; sp.
Qed.

Lemma sub_eq_hyps_dom {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4,
    sub_eq_hyps lib s3 s4 s1 s2 hs
    -> dom_csub s1 = vars_hyps hs
       # dom_csub s2 = vars_hyps hs.
Proof.
  induction hs using rev_list_indT; simpl; introv seh; inversion seh; subst; allsimpl; cpx.
  repeat (rewrite dom_csub_snoc); simpl.
  rewrite vars_hyps_snoc.
  discover; repnd.
  allrw; sp.
Qed.

Lemma subvars_if_cover_vars_eq_hyps {o} :
  forall lib t s1 s2 (H : @bhyps o),
    cover_vars t s1
    -> eq_hyps lib s1 s2 H
    -> subvars (free_vars t) (vars_hyps H).
Proof.
  introv cv eqh.
  allapply @eq_hyps_dom; repnd.
  allrw @cover_vars_eq.
  provesv.
  rw <- eqh0; sp.
Qed.

Lemma sub_eq_hyps_snoc_weak {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4 x t1 t2,
    ! LIn x (hyps_free_vars hs)
    -> sub_eq_hyps lib s1 s2 s3 s4 hs
    -> sub_eq_hyps lib (snoc s1 (x, t1)) (snoc s2 (x, t2)) s3 s4 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv nih seh;
  inversion seh; subst; cpx.

  assert (cover_vars (htyp a) (snoc s1 (x, t1) ++ s0))
    as p1' by (apply cover_vars_weak; sp).

  assert (cover_vars (htyp a) (snoc s2 (x, t2) ++ s5))
    as p2' by (apply cover_vars_weak; sp).

  allrewrite @hyps_free_vars_snoc.
  allrw in_app_iff.

  apply @sub_eq_hyps_cons with (w := w) (p1 := p1') (p2 := p2').
  generalize (lsubstc_csubst_ex2 (htyp a) (snoc s1 (x, t1)) s0 w p1'); sp.
  rewrite <- e.
  generalize (lsubstc_csubst_ex2 (htyp a) (snoc s2 (x, t2)) s5 w p2'); sp.
  rewrite <- e0.

  assert (wf_term (csubst (htyp a) s1)) as w1.
  apply wf_term_csubst; sp.
  assert (wf_term (csubst (htyp a) s2)) as w2.
  apply wf_term_csubst; sp.
  assert (cover_vars (csubst (htyp a) s1) s0) as c1.
  rw <- @cover_vars_csubst; sp.
  assert (cover_vars (csubst (htyp a) s2) s5) as c2.
  rw <- @cover_vars_csubst; sp.

  assert (lsubstc (csubst (htyp a) (snoc s1 (x, t1))) w' s0 p'
          = lsubstc (csubst (htyp a) s1) w1 s0 c1) as eq1.
  apply lsubstc_eq; sp.
  apply subset_free_vars_csub_snoc; sp.
  rewrite eq1.

  assert (lsubstc (csubst (htyp a) (snoc s2 (x, t2))) w'0 s5 p'0
          = lsubstc (csubst (htyp a) s2) w2 s5 c2) as eq2.
  apply lsubstc_eq; sp.
  apply subset_free_vars_csub_snoc; sp.
  rewrite eq2.

  generalize (lsubstc_csubst_ex (htyp a) s1 s0 w1 c1); sp.
  generalize (lsubstc_csubst_ex (htyp a) s2 s5 w2 c2); sp.
  rewrite e1; rewrite e2.

  clear_irr; sp.

  apply IHhs; sp.
Qed.

Lemma sub_eq_hyps_snoc_weak2 {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4 x t1 t2,
    ! LIn x (hyps_free_vars hs)
    -> sub_eq_hyps lib (snoc s1 (x, t1)) (snoc s2 (x, t2)) s3 s4 hs
    -> sub_eq_hyps lib s1 s2 s3 s4 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv nixh seh;
  inversion seh; subst; sp; cpx.

  allrewrite @hyps_free_vars_snoc.
  allrw in_app_iff.
  allrw not_over_or; repd.

  assert (cover_vars (htyp a) (s1 ++ s0))
    as p1' by (apply cover_vars_add with (v := x) (t := t1); sp).

  assert (cover_vars (htyp a) (s2 ++ s5))
    as p2' by (apply cover_vars_add with (v := x) (t := t2); sp).

  apply @sub_eq_hyps_cons with (w := w) (p1 := p1') (p2 := p2').
  generalize (lsubstc_csubst_ex2 (htyp a) (snoc s1 (x, t1)) s0 w p1); sp.
  rw <- e in eqt.
  generalize (lsubstc_csubst_ex2 (htyp a) (snoc s2 (x, t2)) s5 w p2); sp.
  rw <- e0 in eqt.

  assert (wf_term (csubst (htyp a) s1)) as w1 by (apply wf_term_csubst; sp).
  assert (wf_term (csubst (htyp a) s2)) as w2 by (apply wf_term_csubst; sp).
  assert (cover_vars (csubst (htyp a) s1) s0) as c1 by (rw <- @cover_vars_csubst; sp).
  assert (cover_vars (csubst (htyp a) s2) s5) as c2 by (rw <- @cover_vars_csubst; sp).

  assert (lsubstc (csubst (htyp a) (snoc s1 (x, t1))) w' s0 p'
          = lsubstc (csubst (htyp a) s1) w1 s0 c1)
    as eq1
      by (apply lsubstc_eq; sp;
          apply subset_free_vars_csub_snoc; sp;
          allrw eq1).
  rw eq1 in eqt.

  assert (lsubstc (csubst (htyp a) (snoc s2 (x, t2))) w'0 s5 p'0
          = lsubstc (csubst (htyp a) s2) w2 s5 c2)
    as eq2
      by (apply lsubstc_eq; sp;
          apply subset_free_vars_csub_snoc; sp;
          allrw eq2).
  rw eq2 in eqt.

  generalize (lsubstc_csubst_ex (htyp a) s1 s0 w1 c1); sp.
  generalize (lsubstc_csubst_ex (htyp a) s2 s5 w2 c2); sp.
  rw e1 in eqt.
  rw e2 in eqt.
  clear_irr; auto.

  apply IHhs in seh0; sp.
Qed.

Lemma sub_eq_hyps_snoc_weak_iff {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4 x t1 t2,
    ! LIn x (hyps_free_vars hs)
    -> (sub_eq_hyps lib (snoc s1 (x, t1)) (snoc s2 (x, t2)) s3 s4 hs
        <=> sub_eq_hyps lib s1 s2 s3 s4 hs).
Proof.
  introv nixh; split; intro k.
  apply sub_eq_hyps_snoc_weak2 in k; sp.
  apply sub_eq_hyps_snoc_weak; sp.
Qed.

Lemma eq_hyps_snoc {o} :
  forall lib (hs : @bhyps o) h s1 s2,
    eq_hyps lib s1 s2 (snoc hs h)
    <=>
    {s1a, s2a : CSub
     , {t1, t2 : CTerm
     , {w : wf_term (htyp h)
     , {p1 : cover_vars (htyp h) s1a
     , {p2 : cover_vars (htyp h) s2a
        , s1 = snoc s1a (hvar h, t1)
        # s2 = snoc s2a (hvar h, t2)
        # eq_hyps lib s1a s2a hs
        # eqtypes lib (lvl h) (lsubstc (htyp h) w s1a p1) (lsubstc (htyp h) w s2a p2)}}}}}.
Proof.
  introv; split; intro k; exrepnd; subst.
  inversion k; subst; cpx.
  exists s0 s3 t1 t2 w.
  exists p1 p2; sp.
  apply @eq_hyps_cons with (w := w) (p1 := p1) (p2 := p2); sp.
Qed.

Lemma eq_hyps_app {o} :
  forall lib (hs1 hs2 : @bhyps o) s1 s2,
    eq_hyps lib s1 s2 (hs1 ++ hs2)
    <=>
    {s1a, s1b, s2a, s2b : CSub
      , s1 = s1a ++ s1b
      # s2 = s2a ++ s2b
      # length s1a = length hs1
      # length s2a = length hs1
      # eq_hyps lib s1a s2a hs1
      # sub_eq_hyps lib s1a s2a s1b s2b hs2}.
Proof.
  induction hs2 using rev_list_indT; simpl; sp.

  rewrite app_nil_r; split; intro k; exrepnd; subst.
  applydup @eq_hyps_length in k; sp.
  exists s1 (nil : (@CSub o)) s2 (nil : (@CSub o)); simpl; sp;
  allrewrite app_nil_r; auto.
  inversion k1; subst; allrewrite app_nil_r; auto; cpx.

  rewrite snoc_append_l; split; intro k; exrepnd; subst.

  inversion k; cpx.

  rw IHhs2 in eqh; sp; subst.
  exists s1a (snoc s1b (hvar a, t1)) s2a (snoc s2b (hvar a, t2)).
  repeat (rewrite snoc_append_l); sp.

  apply @sub_eq_hyps_cons with (w := w) (p1 := p1) (p2 := p2); sp.

  inversion k1; cpx.
  repeat (rewrite snoc_append_l).
  apply @eq_hyps_cons with (w := w) (p1 := p1) (p2 := p2); sp.
  rw IHhs2.
  exists s1a s1 s2a s2; sp.
Qed.

Lemma eq_hyps_hhyp {o} :
  forall lib s1 s2 (H : @bhyps o) x A J,
   eq_hyps lib s1 s2 (snoc H (mk_hyp x A) ++ J)
   <=>
   eq_hyps lib s1 s2 (snoc H (mk_hhyp x A) ++ J).
Proof.
  sp; sp_iff Case.

  - Case "->"; intro.
    allrw @eq_hyps_app; sp; subst; cpx.
    exists s1a s1b s2a s2b; rewrite length_snoc; sp.
    allrw @eq_hyps_snoc; sp.

  - Case "<-"; intros.
    allrw @eq_hyps_app; sp; subst; cpx.
    exists s1a s1b s2a s2b; rewrite length_snoc; sp.
    allrw @eq_hyps_snoc; sp.
Qed.

Lemma hyps_functionality_nil {o} :
  forall lib, @hyps_functionality o lib [] [].
Proof.
  introv sim.
  inversion sim; cpx.
Qed.
Hint Immediate hyps_functionality_nil.

(*Lemma similarity_imp_eq_hyps_init_seg :*)
Lemma hyps_functionality_init_seg {o} :
  forall lib s1a s1b (H : @bhyps o) J s3,
    hyps_functionality lib (s1a ++ s1b) (H ++ J)
    -> similarity lib s1b s3 (substitute_hyps s1a J)
    -> hyps_functionality lib s1a H.
Proof.
  introv imp simj.
  intros s2 sim.
  generalize (imp (s2 ++ s3)); intro eqh.
  dest_imp eqh hyp.
  rw @similarity_app.
  exists s1a s1b s2 s3; sp; try (complete (allapply @similarity_length; sp)).
  rw @eq_hyps_app in eqh; exrepnd.
  apply app_split in eqh0; try (complete (allapply @similarity_length; repd; omega)).
  apply app_split in eqh2; try (complete (allapply @similarity_length; repd; omega)).
  sp; subst; sp.
Qed.

Lemma hyps_functionality_init_seg_snoc {o} :
  forall lib s t t' (H : @bhyps o) h w c,
    hyps_functionality lib (snoc s (hvar h, t)) (snoc H h)
    -> equality lib t t' (lsubstc (htyp h) w s c)
    -> hyps_functionality lib s H.
Proof.
  introv.
  repeat (rw snoc_as_append).
  generalize (hyps_functionality_init_seg lib s [(hvar h,t)] H [h] [(hvar h,t')]).
  intros i func eq.
  repeat (dest_imp i hyp); simpl.
  repeat (rw singleton_as_snoc).
  assert (hvar h = hvar (substitute_hyp s h)) as e by (destruct h; simpl; sp).
  rw e.
  assert (wf_term (htyp (substitute_hyp s h)))
    as w' by (destruct h; allsimpl; apply wf_term_csubst; sp).
  assert (cover_vars (htyp (substitute_hyp s h)) [])
    as c' by (destruct h; allsimpl; rw <- @cover_vars_csubst; rw app_nil_r; sp).
  apply @sim_cons with (w := w') (p := c'); sp.
  destruct h; allsimpl.
  generalize (lsubstc_csubst_ex htyp0 s [] w' c').
  rw app_nil_r; sp; clear_irr.
  rw e0; sp.
Qed.

Lemma hyps_functionality_init_seg_snoc2 {o} :
  forall lib s t t' (H : @bhyps o) v u w c,
    hyps_functionality lib (snoc s (v, t)) (snoc H (mk_hyp v u))
    -> equality lib t t' (lsubstc u w s c)
    -> hyps_functionality lib s H.
Proof.
  introv hf e sim.
  generalize (hf (snoc s' (v, t'))); intro eqh.
  dest_imp eqh hyp.
  rw @similarity_snoc; simpl.
  exists s s' t t' w c; sp.
  rw @eq_hyps_snoc in eqh; exrepnd; cpx.
Qed.

Lemma hyps_functionality_snoc {o} :
  forall lib (H : @bhyps o) h s t,
    (forall t' s' w c c',
       equality lib t t' (lsubstc (htyp h) w s c)
       -> similarity lib s s' H
       -> eqtypes lib (lvl h) (lsubstc (htyp h) w s c) (lsubstc (htyp h) w s' c'))
    -> hyps_functionality lib s H
    -> hyps_functionality lib (snoc s (hvar h, t)) (snoc H h).
Proof.
  introv imp hf sim.
  rw @similarity_snoc in sim; exrepnd; subst; cpx.
  rw @eq_hyps_snoc; simpl.

  assert (cover_vars (htyp h) s2a)
    as c
      by (clear sim1;
          allrw @cover_vars_covered; allapply @similarity_dom; exrepnd; allrw; sp;
          rw <- sim0; sp).

  exists s1a s2a t1 t2 w p c; sp.
  apply imp with (t' := t2); sp.
Qed.

Lemma hyps_functionality_snoc2 {o} :
  forall lib (H : @bhyps o) h s t v,
    (forall t' s' w c c',
       equality lib t t' (lsubstc (htyp h) w s c)
       -> similarity lib s s' H
       -> eqtypes lib (lvl h) (lsubstc (htyp h) w s c) (lsubstc (htyp h) w s' c'))
    -> hyps_functionality lib s H
    -> v = hvar h
    -> hyps_functionality lib (snoc s (v, t)) (snoc H h).
Proof.
  intros; subst.
  apply hyps_functionality_snoc; sp.
Qed.

Lemma similarity_sym {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eq_hyps lib s1 s2 hs
    -> similarity lib s1 s2 hs
    -> similarity lib s2 s1 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv eqh sim;
  inversion eqh; subst; allsimpl; cpx.
  inversion sim; cpx.
  apply IHhs in sim0; auto; clear_irr.
  apply @sim_cons with (w := w) (p := p2); sp.

  apply eqtypes_preserving_equality with (B := lsubstc (htyp a) w s3 p2) (l := lvl a) in e; auto.
  apply equality_sym; auto.
Qed.

Lemma similarity_trans0 {o} :
  forall lib (hs : @bhyps o) s1 s2 s3,
    similarity lib s1 s2 hs
    -> similarity lib s2 s3 hs
    -> similarity lib s1 s3 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv sim1 sim2;
  inversion sim1; subst; allsimpl; cpx.
  inversion sim2; cpx.
  apply IHhs with (s1 := s0) in sim0; auto.
  apply @sim_cons with (w := w0) (p := p); sp.
Abort.

Lemma similarity_trans {o} :
  forall lib (hs : @bhyps o) s1 s2 s3,
    eq_hyps lib s1 s2 hs
    -> similarity lib s1 s2 hs
    -> similarity lib s2 s3 hs
    -> similarity lib s1 s3 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv eqh sim1 sim2;
  inversion sim1; subst; allsimpl; cpx.
  inversion sim2; cpx.
  inversion eqh; cpx.
  apply IHhs with (s1 := s0) in sim0; auto; clear_irr.
  apply @sim_cons with (w := w) (p := p); sp.
  apply eqtypes_preserving_equality with (B := lsubstc (htyp a) w s0 p) (l := lvl a) in e0.
  apply @equality_trans with (t2 := t2); auto.
  apply eqtypes_sym; auto.
Qed.

Lemma eq_hyps_trans {o} :
  forall lib (hs : @bhyps o) s1 s2 s3,
    eq_hyps lib s1 s2 hs
    -> eq_hyps lib s2 s3 hs
    -> eq_hyps lib s1 s3 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv eqh1 eqh2;
  inversion eqh1; subst; allsimpl; cpx.
  inversion eqh2; cpx.
  apply IHhs with (s1 := s0) in eqh0; auto; clear_irr.
  apply @eq_hyps_cons with (w := w) (p1 := p1) (p2 := p3); sp.
  apply @eqtypes_trans with (t2 := lsubstc (htyp a) w s4 p2); sp.
Qed.

Lemma eq_hyps_sym {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eq_hyps lib s1 s2 hs
    -> eq_hyps lib s2 s1 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv eqh;
  inversion eqh; subst; allsimpl; cpx.
  apply IHhs in eqh0; auto; clear_irr.
  apply @eq_hyps_cons with (w := w) (p1 := p2) (p2 := p1); sp.
  apply eqtypes_sym; auto.
Qed.

(*Lemma similarity_eq_hyps_trans :*)
Lemma similarity_hyps_functionality_trans {o} :
  forall lib s1 s2 (H : @bhyps o),
    similarity lib s1 s2 H
    -> hyps_functionality lib s1 H
    -> hyps_functionality lib s2 H.
Proof.
  introv sim imp sim3.
  applydup imp in sim.
  assert (similarity lib s1 s' H) as sim1
         by (apply @similarity_trans with (s2 := s2); auto).
  apply imp in sim1.
  apply @eq_hyps_trans with (s2 := s1); auto.
  apply eq_hyps_sym; auto.
Qed.

(** This lemma is just wrong because the last clause is false.
 * Instead we have to use sub_eq_hyps. *)
Lemma wrong_eq_hyps_app {o} :
  forall lib (hs1 hs2 : @bhyps o) s1 s2,
    eq_hyps lib s1 s2 (hs1 ++ hs2)
    <=>
    {s1a, s1b, s2a, s2b : CSub
      , s1 = s1a ++ s1b
      # s2 = s2a ++ s2b
      # length s1a = length hs1
      # length s2a = length hs1
      # eq_hyps
           lib
           s1a
           s2a
           hs1
      # eq_hyps
           lib
           s1b
           s2b
           (substitute_hyps s1a hs2)}.
Proof.
  induction hs2 using rev_list_indT; simpl; introv.

  rewrite app_nil_r; split; intro k; exrepnd; subst.
  allapplydup @eq_hyps_length; exrepnd.
  exists s1 (nil : (@CSub o)) s2 (nil : (@CSub o)); simpl; sp;
  allrewrite app_nil_r; auto.
  inversion k1; subst; allrewrite app_nil_r; cpx.

  rewrite snoc_append_l; split; intro k; exrepnd; subst.

  inversion k; cpx.

  rw IHhs2 in eqh; exrepnd; subst.
  exists s1a (snoc s1b (hvar a, t1)) s2a (snoc s2b (hvar a, t2)).
  repeat (rewrite snoc_append_l); sp.
  rewrite substitute_hyps_snoc; simpl.

  assert (hvar a = hvar (substitute_hyp s1a a)) as heq
    by (destruct a; simpl; auto).
  rewrite heq.

  assert (wf_term (htyp (substitute_hyp s1a a))) as w0
    by (destruct a; allsimpl;
        apply lsubst_preserves_wf_term; sp;
        apply in_csub2sub in X2; destruct X2; rw wf_term_eq; sp).

  assert (cover_vars (htyp (substitute_hyp s1a a)) s1b) as c1
    by (destruct a; allsimpl;
        rw <- @cover_vars_csubst; auto).

  assert (cover_vars (htyp (substitute_hyp s1a a)) s2b) as c2
    by (allrewrite @htyp_substitute_hyp;
        rw <- @cover_vars_csubst;
        rw <- @cover_vars_csubst in c1;
        allrw @cover_vars_covered;
        allrewrite @dom_csub_app;
        allapply @eq_hyps_dom; sp;
        rewrite eqh1;
        rewrite <- eqh0; auto).

  apply @eq_hyps_cons with (w := w0) (p1 := c1) (p2 := c2); sp.
  revert w0 c1 c2.
  rewrite htyp_substitute_hyp; sp.

  duplicate c2.
  rw <- @cover_vars_csubst in c2.
  rewrite lsubstc_csubst_eq with (w' := w) (p' := p1).
  rewrite lsubstc_csubst_eq with (w' := w) (p' := c2).
Abort.

(*
Definition sub_weak (ts : candidate_type_system) :=
  forall t  : NTerm,
  forall s1a s1b s2a s2b : CSub,
  forall eq : term_equality,
  forall w  : wf_term t,
  forall p1 : cover_vars t (s1a ++ s1b),
  forall p2 : cover_vars t (s2a ++ s2b),
  forall p3 : cover_vars t (s1a ++ s2b),
    dom_csub s1a = dom_csub s2a
    -> dom_csub s1b = dom_csub s2b
    -> ts (lsubstc t w (s1a ++ s1b) p1)
          (lsubstc t w (s2a ++ s2b) p2)
          eq
    -> ts (lsubstc t w (s1a ++ s1b) p1)
          (lsubstc t w (s1a ++ s2b) p3)
          eq.

Lemma close_sub_weak :
  forall ts : candidate_type_system,
    sub_weak ts
    -> defines_only_universes ts
    -> sub_weak (close ts).
Proof.
  intros; unfold sub_weak; intros.

  remember (lsubstc t w (s1a ++ s1b) p1) as T1.
  remember (lsubstc t w (s2a ++ s2b) p2) as T2.
  revert t w s1a s1b s2a s2b p1 p2 p3 H1 H2 HeqT1 HeqT2.
  close_cases (induction H3 using close_ind') Case; sp; subst.

  - Case "CL_init".
    apply CL_init.
    unfold sub_weak in H.
    apply H with (s2a := s2a) (p2 := p2); sp.

  - Case "CL_void".
    apply CL_void.
    allunfold per_void; sp.
    allunfold computes_to_valc; allsimpl.
    admit.
    apply H6 in H4; sp.

  - Case "CL_int".
    admit.

  - Case "CL_base".
    admit.

  - Case "CL_sqle".
    admit.

  - Case "CL_sqeq".
    admit.

  - Case "CL_eq".
    apply CL_eq.
    unfold per_eq.
    allunfold computes_to_valc; allsimpl.
Abort.

Lemma tequality_weak :
  forall t s1a s1b s2a s2b,
  forall w : wf_term t,
  forall p1 : cover_vars t (s1a ++ s1b),
  forall p2 : cover_vars t (s2a ++ s2b),
  forall p3 : cover_vars t (s1a ++ s2b),
    length s1a = length s2a
    -> tequality (lsubstc t w (s1a ++ s1b) p1)
                 (lsubstc t w (s2a ++ s2b) p2)
    -> tequality (lsubstc t w (s1a ++ s1b) p1)
                 (lsubstc t w (s1a ++ s2b) p3).
Proof.
Abort.

(*
  rewrite lsubstc_csubst_eq with (w' := w) (p' := p2); sp.

  destruct a; allsimpl.
  rewrite lsubstc_csubst_eq with (w' := w) (p' := p); auto.

  rewrite substitute_hyps_snoc in H4.
  inversion H4; subst.
  apply nil_snoc_false in H6; sp.
  allapply snoc_inj; sp; subst.
  allrewrite hvar_substitute_hyp.
  repeat (rewrite snoc_append_l).

  assert (wf_term (htyp a)) as w0
    by (destruct a; allsimpl;
        clear H0;
        apply csubst_wf_term in w; auto).

  assert (cover_vars (htyp a) (s1a ++ s1)) as c0
    by (destruct a; allsimpl;
        allrewrite cover_vars_csubst; sp).

  apply sim_cons with (w := w0) (p := c0); sp.
  revert w p H0.
  rewrite htyp_substitute_hyp; sp.
  rewrite lsubstc_csubst_eq with (w' := w0) (p' := c0) in H0; sp.

  rewrite IHhs2.
  exists s1a s1 s2a s2; sp.
Qed.
*)
*)


(** Now we combine eq_hyps and similarity into one relation *)
Inductive eqhyps {o} (lib : @library o) : @CSub o -> @CSub o -> @bhyps o -> [U] :=
  | eqhyps_nil : eqhyps lib [] [] []
  | eqhyps_cons :
      forall t1 t2 : CTerm,
      forall s1 s2 : CSubstitution,
      forall h  : hypothesis,
      forall hs : barehypotheses,
      forall w  : wf_term (htyp h),
      forall p1 : cover_vars (htyp h) s1,
      forall p2 : cover_vars (htyp h) s2,
      forall e  : equality lib t1 t2 (lsubstc (htyp h) w s1 p1),
(*        -> tequality (lsubstc (htyp h) w s1 p1) (lsubstc (htyp h) w s2 p2)*)
      forall eqt : eqtypes lib (lvl h) (lsubstc (htyp h) w s1 p1) (lsubstc (htyp h) w s2 p2),
      forall eqh : eqhyps lib s1 s2 hs,
        eqhyps lib (snoc s1 (hvar h, t1)) (snoc s2 (hvar h, t2)) (snoc hs h).

Lemma eqhyps_refl {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eqhyps lib s1 s2 hs
    -> eqhyps lib s1 s1 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv eqh;
  inversion eqh; subst; allsimpl; cpx.

  apply IHhs in eqh0; repd.
  apply @eqhyps_cons with (w := w) (p1 := p1) (p2 := p1); sp.
  rewrite member_eq.
  apply @equality_refl with (t2 := t2); sp.
  allapply @eqtypes_refl; sp.
Qed.

Lemma eqhyps_implies_similarity {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eqhyps lib s1 s2 hs
    -> similarity lib s1 s2 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv eqh;
  inversion eqh; subst; allsimpl; cpx.
  apply_in_hyp p; repd.
  apply @sim_cons with (w := w) (p := p1); sp.
Qed.

Lemma eqhyps_implies_eq_hyps {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eqhyps lib s1 s2 hs
    -> eq_hyps lib s1 s2 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv eqh;
  inversion eqh; subst; allsimpl; cpx.
  apply_in_hyp p; repd.
  apply @eq_hyps_cons with (w := w) (p1 := p1) (p2 := p2); sp.
Qed.

Lemma eqhyps_if {o} :
  forall lib (hs : @bhyps o) s1 s2,
    similarity lib s1 s2 hs
    -> eq_hyps lib s1 s2 hs
    -> eqhyps lib s1 s2 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv sim eqh;
  inversion sim; subst; allsimpl; cpx.
  inversion eqh; cpx.
  apply @eqhyps_cons with (w := w) (p1 := p1) (p2 := p2); sp.
  clear_irr; sp. clear_irr; sp.
Qed.

Lemma eqhyps_dom {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eqhyps lib s1 s2 hs
    -> dom_csub s1 = vars_hyps hs
       # dom_csub s2 = vars_hyps hs.
Proof.
  intros; allapply @eqhyps_implies_similarity.
  allapply @similarity_dom; sp.
Qed.

Lemma eqhyps_length {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eqhyps lib s1 s2 hs
    -> (length s1 = length hs # length s2 = length hs).
Proof.
  intros; allapply @eqhyps_implies_similarity.
  allapply @similarity_length; sp.
Qed.

(* end hide *)

(**

  This [hyps_true_at] abstraction is used in the Book's definition.
  It is similar to [pw_assign_eq] but uses lists of terms instead of
  substitutions, and does not relate two substitutions---this is dealt
  with using [equal_terms_in_hyps] which is presented above.

 *)

Inductive hyps_true_at {o} (lib : @library o) : @bhyps o -> list (@CTerm o) -> [U] :=
  | InHyp_nil : hyps_true_at lib [] []
  | InHyp_cons :
      forall t  : CTerm,
      forall ts : list CTerm,
      forall h  : hypothesis,
      forall hs : barehypotheses,
      forall w  : wf_term (htyp h),
      forall p  : cover_vars (htyp h) (mk_hs_subst ts hs),
      forall m  : member lib t (lsubstc (htyp h) w (mk_hs_subst ts hs) p),
      forall hf :
             (forall ts' : list CTerm,
              forall p'  : cover_vars (htyp h) (mk_hs_subst ts' hs),
                equal_terms_in_hyps lib ts ts' hs
                -> eqtypes lib
                           (lvl h)
                           (lsubstc (htyp h) w (mk_hs_subst ts hs)  p)
                           (lsubstc (htyp h) w (mk_hs_subst ts' hs) p')),
      forall hta : hyps_true_at lib hs ts,
        hyps_true_at lib (snoc hs h) (snoc ts t).
Hint Constructors hyps_true_at.

(* begin hide *)

Lemma hyps_true_at_length {o} :
  forall lib (hs : @bhyps o) ts,
    hyps_true_at lib hs ts -> length hs = length ts.
Proof.
  introv hta; induction hta; simpl; auto.
  repeat (rewrite length_snoc); sp.
Qed.

Lemma hyps_true_at_app {o} :
  forall lib (hs1 hs2 : @bhyps o) ts,
    hyps_true_at lib (hs1 ++ hs2) ts
    -> {ts1, ts2 : list CTerm
         , ts = ts1 ++ ts2
         # length ts1 = length hs1
         # length ts2 = length hs2
         # hyps_true_at lib hs1 ts1}.
Proof.
  induction hs2 using rev_list_indT; simpl; introv hta.

  allrw app_nil_r.
  exists ts ([] : list (@CTerm o)); sp.
  rewrite app_nil_r; auto.
  allapplydup @hyps_true_at_length; auto.

  rev_list_dest ts.
  apply hyps_true_at_length in hta; allsimpl.
  allrw length_app; allrw length_snoc.
  omega.

  allrw snoc_append_l.
  inversion hta; cpx.
  apply IHhs2 in hta0; sp; subst.
  exists ts1 (snoc ts2 v); sp.
  rewrite snoc_append_l; auto.
  repeat (rewrite length_snoc); sp.
Qed.

Lemma hyps_true_at_implies_equal {o} :
  forall lib (hs : @bhyps o) ts,
    hyps_true_at lib hs ts
    -> equal_terms_in_hyps lib ts ts hs.
Proof.
  induction hs using rev_list_indT; introv hta; inversion hta; cpx.
  apply @EqInHyps_cons with (w := w) (p := p); sp.
Qed.

Lemma hyps_true_at_app2 {o} :
  forall lib (hs1 hs2 : @bhyps o) ts,
    hyps_true_at lib (hs1 ++ hs2) ts
    -> {ts1, ts2 : list CTerm
         , ts = ts1 ++ ts2
         # length ts1 = length hs1
         # length ts2 = length hs2
         # hyps_true_at lib hs1 ts1
         # hyps_true_at lib (substitute_hyps (mk_hs_subst ts1 hs1) hs2) ts2}.
Proof.
  induction hs2 using rev_list_indT; simpl; introv hta.

  allrw app_nil_r.
  exists ts ([] : list (@CTerm o)); sp; auto.
  rewrite app_nil_r; auto.
  allapplydup @hyps_true_at_length; auto.

  rev_list_dest ts.
  allapplydup @hyps_true_at_length; allsimpl.
  allrw length_app; allrw length_snoc.
  omega.

  allrw snoc_append_l.
  inversion hta; cpx.
  apply IHhs2 in hta0; sp; subst.
  exists ts1 (snoc ts2 v); sp.
  rewrite snoc_append_l; auto.
  repeat (rewrite length_snoc); omega.
  rewrite substitute_hyps_snoc.

  assert (wf_term (htyp (substitute_hyp (mk_hs_subst ts1 hs1) a))) as wh
    by (destruct a; allsimpl; apply wf_term_csubst; auto).

  assert (cover_vars (htyp (substitute_hyp (mk_hs_subst ts1 hs1) a))
                     (mk_hs_subst ts2 (substitute_hyps (mk_hs_subst ts1 hs1) hs2))) as ph
    by (destruct a; allsimpl;
        rewrite mk_hs_subst_substitute_hyps;
        clear_dependents p;
        rewrite mk_hs_subst_app in p; auto;
        rw <- @cover_vars_csubst; auto).

  apply @InHyp_cons with (w := wh) (p := ph); sp.
  revert wh ph; rewrite htyp_substitute_hyp; rewrite mk_hs_subst_substitute_hyps; sp.
  duplicate p.
  rewrite mk_hs_subst_app in p; sp.
  rewrite lsubstc_csubst_eq with (w' := w) (p' := p).
  revert p.
  rewrite <- mk_hs_subst_app; sp.
  clear_irr; sp.

  revert wh ph p'.
  rewrite htyp_substitute_hyp; repeat (rewrite mk_hs_subst_substitute_hyps); sp.

  duplicate ph.
  rw <- @cover_vars_csubst in ph.
  duplicate p'.
  rw <- @cover_vars_csubst in p'.
  rewrite @lsubstc_csubst_eq with (w' := w) (p' := ph).
  rewrite @lsubstc_csubst_eq with (w' := w) (p' := p').
  revert ph p'.
  repeat (rewrite <- mk_hs_subst_app); sp.
  clear_irr; sp.
  autorewrite with core.

  apply hf.
  apply equal_terms_in_hyps_app_implies; auto.
  apply hyps_true_at_implies_equal; auto.
Qed.

(*
Lemma hyps_true_at_app_implies :
  forall (hs : @bhyps o)1 hs2 ts1 ts2,
    hyps_true_at lib hs1 ts1
    -> (forall ts1',
          equal_terms_in_hyps ts1 ts1' hs1
          -> hyps_true_at (substitute_hyps (mk_hs_subst ts1' hs1) hs2) ts2)
    -> hyps_true_at (hs1 ++ hs2) (ts1 ++ ts2).
Proof.
  induction hs2 using rev_list_indT; simpl; sp.

  generalize (H0 ts1); sp.
  applydup hyps_true_at_implies_equal in H; sp.
  inversion H1; subst.
  repeat (rewrite app_nil_r); auto.
  symmetry in H3.
  apply nil_snoc_false in H3; sp.

  applydup hyps_true_at_implies_equal in H; sp.
  applydup hyps_true_at_length in H.

  generalize (H0 ts1); sp.
  rewrite substitute_hyps_snoc in H3.
  inversion H3.
  apply nil_snoc_false in H5; sp.
  clear H6 H7.
  apply snoc_inj in H4; repd; subst.
  repeat (rewrite snoc_append_l).
  revert H5.
  revert w p.
  rewrite htyp_substitute_hyp; sp.

  duplicate w.
  apply csubst_wf_term in w.
  duplicate p.
  rewrite <- cover_vars_csubst in p.
  rewrite mk_hs_subst_substitute_hyps in p.

  revert p0 H5.
  rewrite mk_hs_subst_substitute_hyps; sp.
  rewrite lsubstc_csubst_eq with (w' := w) (p' := p) in H5.
  clear w0 p0.
  revert p H5.
  rewrite <- mk_hs_subst_app; sp.

  apply InHyp_cons with (w := w) (p := p); intros; auto.

  - (* -- tequality proposition *)
    apply equal_terms_in_hyps_app in H4; sp; subst.
    applydup equal_terms_in_hyps_length in H9; sp.
    apply app_split in H4; sp; subst; sp; GC.

    generalize (H0 ts2a); sp.
    rewrite substitute_hyps_snoc in H2.
    inversion H2.
    apply nil_snoc_false in H13; sp.
    allapply snoc_inj; repd; subst; GC.

    inversion H3.
    apply nil_snoc_false in H16; sp.
    allapply snoc_inj; repd; subst; GC.

    revert w1 p1 H13 H14.
    rewrite htyp_substitute_hyp; sp.
    generalize (H14 ts2b); sp.
    clear H14.
    revert p0 p1 H0 H5 H13.
    repeat (rewrite mk_hs_subst_substitute_hyps); sp.


(*
    XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

      generalize (H0 ts2a); sp.
    clear H0.
    rewrite substitute_hyps_snoc in H4.
    inversion H4.
    apply nil_snoc_false in H13; sp.
    allapply snoc_inj; repd; subst.
    GC.
    revert w1 p1 H13 H14.
    rewrite htyp_substitute_hyp; sp.
    generalize (H14 ts2b); sp.
    clear H14.
    revert p0 p1 H0 H5 H13.
    repeat (rewrite mk_hs_subst_substitute_hyps); sp.

    assert (equal_terms_in_hyps
              ts1b
              ts2b
              (substitute_hyps (mk_hs_subst ts2a hs1) hs2)).

    xxx

      (* follows from p': *)
      assert (cover_vars (csubst (htyp a) (mk_hs_subst ts2a hs1))
                         (mk_hs_subst ts2b hs2)) as p2
      by (rewrite <- cover_vars_csubst;
          rewrite <- mk_hs_subst_app; auto).
    generalize (H0 p2); sp.
*)

    admit.

  - (* -- hyps_true_at proposition *)
    apply IHhs2; sp.
    generalize (H0 ts1'); sp.
    rewrite substitute_hyps_snoc in H6.
    inversion H6.
    apply nil_snoc_false in H9; sp.
    allapply snoc_inj; repd; subst; auto.
Qed.
*)

Lemma hyps_true_at_snoc {o} :
  forall lib h (hs : @bhyps o) ts,
    hyps_true_at lib (snoc hs h) ts
    -> {t : CTerm
        , {ts1 : list CTerm
        , {w : wf_term (htyp h)
        , {p : cover_vars (htyp h) (mk_hs_subst ts1 hs)
           , ts = snoc ts1 t
           # member lib t (lsubstc (htyp h) w (mk_hs_subst ts1 hs) p)
           # (forall ts2 : list CTerm,
              forall p2  : cover_vars (htyp h) (mk_hs_subst ts2 hs),
                equal_terms_in_hyps lib ts1 ts2 hs
                -> eqtypes lib
                           (lvl h)
                           (lsubstc (htyp h) w (mk_hs_subst ts1 hs) p)
                           (lsubstc (htyp h) w (mk_hs_subst ts2 hs) p2)
(*                -> tequality (lsubstc (htyp h) w (mk_hs_subst ts1 hs) p)
                             (lsubstc (htyp h) w (mk_hs_subst ts2 hs) p2)*))
           # hyps_true_at lib hs ts1}}}}.
Proof.
  introv hta.
  rev_list_dest ts.
  allapplydup @hyps_true_at_length; allsimpl; cpx.
  inversion hta; cpx.
  exists v u w p; sp.
Qed.


(*
Lemma hyps_true_at_eq :
  forall (hs : @bhyps o) ts, hyps_true_at lib hs ts <=> hyps_true_at2 hs ts.
Proof.
  induction hs; sp; split; sp; destruct ts.
  constructor.
  inversion H.
  constructor.
  inversion H.
  symmetry in H0; apply nil_snoc_false in H0; sp.
  inversion H.
  inversion H; subst; allsimpl.
Qed.
*)

Definition hypotheses_true_at {o}
           (lib : library)
           (hyps : hypotheses)
           (ts : list (@CTerm o)) : Type :=
  hyps_true_at lib (projT1 hyps) ts.

Lemma hypotheses_true_at_length {o} :
  forall lib (hs : @hypotheses o) ts,
    hypotheses_true_at lib hs ts -> length_hs hs = length ts.
Proof.
  intros.
  destruct hs.
  allunfold @hypotheses_true_at; sp.
  simpl.
  eapply hyps_true_at_length; eauto.
Qed.

(*
Lemma equal_terms_in_hyps_true :
  forall (hs : @bhyps o) ts ts',
    equal_terms_in_hyps ts ts' hs
    -> hyps_true_at lib hs ts
    -> hyps_true_at lib hs ts'.
Proof.
  induction hs using rev_list_indT; simpl; sp.
  inversion H0; subst.
  inversion H; subst.
  constructor.
  symmetry in H1; apply nil_snoc_false in H1; sp.
  symmetry in H1; apply nil_snoc_false in H1; sp.
  applydup equal_terms_in_hyps_snoc in H; sp; subst.
  applydup hyps_true_at_snoc in H0; sp; subst.
  apply snoc_inj in H1; sp; subst.
  apply IHhs with (ts' := ts2') in H6; sp.

  assert (cover_vars (htyp a) (mk_hs_subst ts2' hs)).
  allunfold cover_vars; allunfold over_vars.
  clear H2 H5.
  apply hyps_true_at_length in H6.
  apply equal_terms_in_hyps_length in H3; sp.
  rewrite <- dom_mk_hs_subst in p0; sp.
  rewrite <- dom_mk_hs_subst; sp.
  symmetry; sp.
  symmetry; sp.

  apply InHyp_cons with (w := w0) (p := H1); sp.
Qed.
*)


(* --- Hypotheses covered by terms *)

Definition cover_hyps {o} (ts : list (@CTerm o)) (hyps : @bhyps o) :=
  length ts = length hyps.

(*
Definition cover_hypotheses (ts : list CTerm) (hyps : hypotheses) :=
  cover_hyps ts (projT1 hyps).
*)

Lemma cover_hyps_eq {o} :
  forall lib ts ts' (H : @bhyps o),
    cover_hyps ts H
    -> equal_terms_in_hyps lib ts ts' H
    -> cover_hyps ts' H.
Proof.
  unfold cover_hyps; introv cvh eqt.
  allapplydup @equal_terms_in_hyps_length; sp.
Qed.

(*
Lemma cover_hypotheses_eq :
  forall ts ts' H,
    cover_hypotheses ts H
    -> equal_terms_in_hyps ts ts' (projT1 H)
    -> cover_hypotheses ts' H.
Proof.
  destruct H.
  unfold cover_hypotheses; allsimpl; sp.
  apply cover_hyps_eq with (ts := ts); auto.
Qed.
*)

Definition cover_sequent {o} (ts : list CTerm) (S : @sequent o) :=
  cover_hyps ts (hyps (projT1 S)).

Definition cover_ctsequent {o} (ts : list CTerm) (S : @ctsequent o) :=
  cover_sequent ts (projT1 S).

Definition cover_csequent {o} (ts : list CTerm) (S : @csequent o) :=
  cover_ctsequent ts (projT1 S).

(*
Lemma cover_hypotheses_member :
  forall (hs : @bhyps o) : barehypotheses,
  forall ts : list CTerm,
  forall p  : wf_hypotheses hs,
  forall v  : NVar,
    cover_hypotheses ts (mk_hyps hs p)
    -> LIn v (vars_hyps hs)
    -> {u : CTerm & LIn (v, u) (mk_hs_subst ts hs)}.
Proof.
  unfold cover_hypotheses, length_hs; simpl.
  induction hs using rev_list_indT; simpl; sp.
  allrw length_snoc.
  destruct ts using rev_list_indT; cpx.
  rewrite vars_hyps_snoc in X.
  allrw in_snoc; sp.

  inversion p; cpx.
  duplicate H as leq.
  apply IHhs with (v := v) in leq; auto; sp.
  rewrite mk_hs_subst_snoc; auto.
  exists u.
  rw in_snoc; sp.
  exists a0; subst.
  rewrite mk_hs_subst_snoc; auto.
  rw in_snoc; sp.
Qed.
*)


(* --- Well-formedness of sequents *)

(*
Lemma seq_cl :
  forall s : csequent,
    wf_term (ctype (concl (projT1 (projT1 (projT1 s))))).
Proof.
  destruct s.
  destruct x.
  destruct x.
  destruct x.
  unfold_closed.
  inversion w.
  inversion X; allsimpl; sp.
Qed.

Lemma seq_ex :
  forall s : csequent,
    wf_term_op (extract (concl (projT1 (projT1 (projT1 s))))).
Proof.
  destruct s.
  destruct x.
  destruct x.
  destruct x.
  unfold_closed.
  inversion w.
  inversion X; allsimpl; sp.
Qed.

Lemma seq_cover :
  forall s  : csequent,
  forall ts : list CTerm,
    hyps_true_at (hyps (projT1 (projT1 (projT1 s)))) ts
    -> cover_vars (ctype (concl (projT1 (projT1 (projT1 s)))))
                  (mk_hs_subst ts (hyps (projT1 (projT1 (projT1 s))))).
Proof.
  destruct s.
  destruct x.
  destruct x.
  destruct x.
  unfold_closed; sp.
  rw cover_vars_covered.
  rw <- dom_mk_hs_subst; sp.
  allapply hyps_true_at_length; sp.
Qed.

Lemma seq_cover_ex :
  forall s  : csequent,
  forall ts : list CTerm,
    hyps_true_at (hyps (projT1 (projT1 (projT1 s)))) ts
    -> cover_vars_op (extract (concl (projT1 (projT1 (projT1 s)))))
                     (mk_hs_subst ts (hyps (projT1 (projT1 (projT1 s))))).
Proof.
  destruct s.
  destruct x.
  destruct x.
  destruct x.
  unfold_closed; sp.
  rw cover_vars_op_covered_op.
  rw <- dom_mk_hs_subst; sp.
  apply covered_op_subvars with (vs1 := nh_vars_hyps hyps0); sp.
  allapply hyps_true_at_length; sp.
Qed.

Lemma seq_cover2 :
  forall s : csequent,
  forall ts ts' : list CTerm,
    hyps_true_at (hyps (projT1 (projT1 (projT1 s)))) ts
    -> equal_terms_in_hyps ts ts' (hyps (projT1 (projT1 (projT1 s))))
    -> cover_vars (ctype (concl (projT1 (projT1 (projT1 s)))))
                  (mk_hs_subst ts' (hyps (projT1 (projT1 (projT1 s))))).
Proof.
  destruct s; destruct x; destruct x; destruct x.
  unfold_closed; sp.
  rw cover_vars_covered.
  rw <- dom_mk_hs_subst; sp.
  allapply equal_terms_in_hyps_length; sp.
Qed.

Lemma seq_cover2_ex :
  forall s : csequent,
  forall ts ts' : list CTerm,
    hyps_true_at (hyps (projT1 (projT1 (projT1 s)))) ts
    -> equal_terms_in_hyps ts ts' (hyps (projT1 (projT1 (projT1 s))))
    -> cover_vars_op (extract (concl (projT1 (projT1 (projT1 s)))))
                     (mk_hs_subst ts' (hyps (projT1 (projT1 (projT1 s))))).
Proof.
  destruct s; destruct x; destruct x; destruct x.
  unfold_closed; sp.
  rw cover_vars_op_covered_op.
  rw <- dom_mk_hs_subst; sp.
  apply covered_op_subvars with (vs1 := nh_vars_hyps hyps0); sp.
  allapply equal_terms_in_hyps_length; sp.
Qed.

Lemma scover1 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    pw_assign_eq s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars (ctype (concl (projT1 (projT1 (projT1 seq))))) s1.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_covered.
  allapply pw_assign_eq_dom; sp.
  rw <- X0; sp.
Qed.

Lemma scover2 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    pw_assign_eq s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars (ctype (concl (projT1 (projT1 (projT1 seq))))) s2.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_covered.
  allapply pw_assign_eq_dom; sp.
  rw <- X; sp.
Qed.

Lemma scover_ex1 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    pw_assign_eq s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars_op (extract (concl (projT1 (projT1 (projT1 seq))))) s1.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_op_covered_op.
  allapply pw_assign_eq_dom; sp.
  rw <- X0; sp.
  apply covered_op_subvars with (vs1 := nh_vars_hyps hyps0); sp.
Qed.

Lemma scover_ex2 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    pw_assign_eq s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars_op (extract (concl (projT1 (projT1 (projT1 seq))))) s2.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_op_covered_op.
  allapply pw_assign_eq_dom; sp.
  rw <- X; sp.
  apply covered_op_subvars with (vs1 := nh_vars_hyps hyps0); sp.
Qed.

Lemma s_cover1 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    similarity lib s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars (ctype (concl (projT1 (projT1 (projT1 seq))))) s1.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_covered.
  allapply similarity_dom; sp.
  allrw; sp.
Qed.

Lemma s_cover2 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    similarity lib s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars (ctype (concl (projT1 (projT1 (projT1 seq))))) s2.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_covered.
  allapply similarity_dom; sp.
  allrw; sp.
Qed.

Lemma s_cover_ex1 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    similarity lib s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars_op (extract (concl (projT1 (projT1 (projT1 seq))))) s1.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_op_covered_op.
  allapply similarity_dom; sp.
  allrw; sp.
  apply covered_op_subvars with (vs1 := nh_vars_hyps hyps0); sp.
Qed.

Lemma s_cover_ex2 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    similarity lib s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars_op (extract (concl (projT1 (projT1 (projT1 seq))))) s2.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_op_covered_op.
  allapply similarity_dom; sp.
  allrw; sp.
  apply covered_op_subvars with (vs1 := nh_vars_hyps hyps0); sp.
Qed.

Lemma s_cover_1 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    eqhyps lib s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars (ctype (concl (projT1 (projT1 (projT1 seq))))) s1.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_covered.
  allapply eqhyps_dom; sp.
  allrw; sp.
Qed.

Lemma s_cover_2 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    eqhyps lib s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars (ctype (concl (projT1 (projT1 (projT1 seq))))) s2.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_covered.
  allapply eqhyps_dom; sp.
  allrw; sp.
Qed.

Lemma s_cover_ex_1 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    eqhyps lib s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars_op (extract (concl (projT1 (projT1 (projT1 seq))))) s1.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_op_covered_op.
  allapply eqhyps_dom; sp.
  allrw; sp.
  apply covered_op_subvars with (vs1 := nh_vars_hyps hyps0); sp.
Qed.

Lemma s_cover_ex_2 :
  forall seq : csequent,
  forall s1 s2 : CSubstitution,
    eqhyps lib s1 s2 (hyps (projT1 (projT1 (projT1 seq))))
    -> cover_vars_op (extract (concl (projT1 (projT1 (projT1 seq))))) s2.
Proof.
  destruct seq; destruct x; destruct x; destruct x; destruct w.
  unfold_closed; sp.
  rw cover_vars_op_covered_op.
  allapply eqhyps_dom; sp.
  allrw; sp.
  apply covered_op_subvars with (vs1 := nh_vars_hyps hyps0); sp.
Qed.
*)


(* --- Truth of sequents *)

(*
Definition extract_eq eop T S sub1 sub2 ts ts' p :=
  match eop with
    | Some e =>
      equality (lsubstc e (seq_ex S) sub1 (seq_cover_ex S ts p))
               (lsubstc e (seq_ex S) sub2 (seq_cover2_ex S ts ts' p e))
               T
    | None => True
  end.
*)

Ltac destseq_step :=
  match goal with
    | [ H : vswf_hypotheses [] _ |- _ ] =>
      apply vswf_hypotheses_nil_implies in H
    | [ H : csequent      |- _ ] =>
        let ce := fresh "ce" in
          destruct H as [ H ce ]
    | [ H : ctsequent     |- _ ] =>
        let ce := fresh "ct" in
          destruct H as [ H ct ]
    | [ H : sequent       |- _ ] =>
        let wfs := fresh "wfs" in
          destruct H as [ H wfs ]
    | [ H : wf_csequent _ |- _ ] =>
        let wfs  := fresh "wfs"  in
        let wfs' := fresh "wfs'" in
        let ct   := fresh "ct"   in
        let ce   := fresh "ce"   in
          destruct H as [ wfs wfs' ]; destruct wfs' as [ ct ce ]
    | [ H : wf_sequent _  |- _ ] =>
        let wfh := fresh "wfh" in
        let wfc := fresh "wfc" in
          destruct H as [ wfh wfc ]
    | [ H : wf_concl _    |- _ ] =>
        let wfct := fresh "wfct" in
        let wfce := fresh "wfce" in
          destruct H as [ wfct wfce ]
    | [ H : closed_type_sequent _        |- _ ] => unfold closed_type_sequent        in H; simpl in H
    | [ H : closed_type_baresequent _    |- _ ] => unfold closed_type_baresequent    in H; simpl in H
    | [ H : closed_type _ _              |- _ ] => unfold closed_type                in H; simpl in H
    | [ H : closed_extract_ctsequent _   |- _ ] => unfold closed_extract_ctsequent   in H; simpl in H
    | [ H : closed_extract_sequent _     |- _ ] => unfold closed_extract_sequent     in H; simpl in H
    | [ H : closed_extract_baresequent _ |- _ ] => unfold closed_extract_baresequent in H; simpl in H
    | [ H : closed_extract _ _           |- _ ] => unfold closed_extract             in H; simpl in H
  end.

Ltac destseq := repeat (destseq_step; exrepnd).

Lemma seq_ex2 {o} :
  forall s : @csequent o,
    match extract (concl (projT1 (projT1 (projT1 s)))) with
      | Some e => wf_term e
      | None => true = true
    end.
Proof.
  introv.
  destseq; sp.
Qed.

Definition extract_op_to_op_extract {o}
           (top : option (@NTerm o))
           (vs : list NVar) : wf_term_op top
                              -> covered_op top vs
                              -> option {t : NTerm & wf_term t # covered t vs} :=
  match top
        as o
        return (wf_term_op o
                -> covered_op o vs
                -> option {t : NTerm & wf_term t # covered t vs}) with
    | Some n =>
      fun (w : wf_term n) (c : covered n vs) =>
        Some (existT (fun t : NTerm => wf_term t # covered t vs) n (w, c))
    | None => fun (_ : true = true) (_ : true = true) => None
  end.

Inductive csequent_components {o} :=
| cseq_comps :
    forall (hs : @bhyps o),
    forall (T  : @NTerm o),
    forall (wh : wf_hypotheses hs),
    forall (wt : wf_term T),
    forall (ct : covered T (vars_hyps hs)),
    forall (ec : option {t : @NTerm o & wf_term t # covered t (nh_vars_hyps hs)}),
      csequent_components.

Definition destruct_csequent {o} (cs : @csequent o) : csequent_components :=
  cseq_comps
    (hyps (projT1 (projT1 (projT1 cs))))
    (ctype (concl (projT1 (projT1 (projT1 cs)))))
    (vswf_hypotheses_nil_implies (hyps (projT1 (projT1 (projT1 cs)))) (fst (projT2 (projT1 (projT1 cs)))))
    (fst (snd (projT2 (projT1 (projT1 cs)))))
    (projT2 (projT1 cs))
    (extract_op_to_op_extract
       (extract (concl (projT1 (projT1 (projT1 cs)))))
       (nh_vars_hyps (hyps (projT1 (projT1 (projT1 cs)))))
       (snd (snd (projT2 (projT1 (projT1 cs)))))
       (projT2 cs)).

Lemma seq_cover_typ1 {o} :
  forall lib t ts ts' (hs : @bhyps o),
    covered t (vars_hyps hs)
    -> equal_terms_in_hyps lib ts ts' hs
    -> cover_vars t (mk_hs_subst ts hs).
Proof.
  introv cv eqt.
  rw @cover_vars_covered.
  rw <- @dom_mk_hs_subst; sp.
  allapply @equal_terms_in_hyps_length; sp.
Qed.

Lemma seq_cover_typ2 {o} :
  forall lib t ts ts' (hs : @bhyps o),
    covered t (vars_hyps hs)
    -> equal_terms_in_hyps lib ts ts' hs
    -> cover_vars t (mk_hs_subst ts' hs).
Proof.
  introv cv eqt.
  rw @cover_vars_covered.
  rw <- @dom_mk_hs_subst; sp.
  allapply @equal_terms_in_hyps_length; sp.
Qed.

Lemma seq_cover_ex1 {o} :
  forall lib e ts ts' (hs : @bhyps o),
    covered e (nh_vars_hyps hs)
    -> equal_terms_in_hyps lib ts ts' hs
    -> cover_vars e (mk_hs_subst ts hs).
Proof.
  introv cv eqt; sp; allsimpl.
  rw @cover_vars_covered.
  rw <- @dom_mk_hs_subst; sp.
  apply covered_subvars with (vs1 := nh_vars_hyps hs); sp.
  allapply @equal_terms_in_hyps_length; sp.
Qed.

Lemma seq_cover_ex2 {o} :
  forall lib e ts ts' (hs : @bhyps o),
    covered e (nh_vars_hyps hs)
    -> equal_terms_in_hyps lib ts ts' hs
    -> cover_vars e (mk_hs_subst ts' hs).
Proof.
  introv cv eqt; sp; allsimpl.
  rw @cover_vars_covered.
  rw <- @dom_mk_hs_subst; sp.
  apply covered_subvars with (vs1 := nh_vars_hyps hs); sp.
  allapply @equal_terms_in_hyps_length; sp.
Qed.

(* end hide *)

(**

  The Nuprl book defines the truth of a sequent as follows: A sequent
  [S] with hypotheses [H], type [T], and extract [ext], is true if for
  all list of terms [ts] that cover [H] (i.e., [cover_csequent ts S]),
  and for all list of term [ts'], if [H] is true at [ts] (i.e.,
  [hyps_true_at ts H]), and the two lists of terms are equal in [H]
  (i.e., [equal_terms_in_hyps lib ts ts' H]), and [s1] and [s2] are two
  substitutions built from [ts], [ts'], and [H], then [s1(T)] is equal
  to [s2(T)] and [s1(ext)] and [s2(ext)] are equal in [s1(T)].

 *)

Definition sequent_true_at {o}
           (lib : library)
           (S : @csequent o)
           (ts : list CTerm) : Type :=
  forall ts' : list CTerm,
    match destruct_csequent S with
      | cseq_comps hs T wh wt ct ec =>
          forall p : hyps_true_at lib hs ts,
          forall e : equal_terms_in_hyps lib ts ts' hs,
            let sub1 := mk_hs_subst ts  hs in
            let sub2 := mk_hs_subst ts' hs in
              (
                tequality lib
                  (lsubstc T wt sub1 (seq_cover_typ1 lib T ts ts' hs ct e))
                  (lsubstc T wt sub2 (seq_cover_typ2 lib T ts ts' hs ct e))
                #
                match ec with
                  | Some (existT _ ext (we, ce)) =>
                      equality lib
                        (lsubstc ext we sub1 (seq_cover_ex1 lib ext ts ts' hs ce e))
                        (lsubstc ext we sub2 (seq_cover_ex2 lib ext ts ts' hs ce e))
                        (lsubstc T wt sub1 (seq_cover_typ1 lib T ts ts' hs ct e))
                  | None => True
                end
              )
    end.

Definition sequent_true {o} lib (S : @csequent o) : Type :=
  forall ts : list CTerm,
    cover_csequent ts S
    -> sequent_true_at lib S ts.

(* begin hide *)

(*
Definition sequent_true_at (S : csequent) (ts : list CTerm) : Type :=
  let s  := projT1 (projT1 (projT1 S)) in
  let hs := hyps s in
  let G  := concl s in
  forall ts' : list CTerm,
  forall p : hyps_true_at lib hs ts,
  forall e : equal_terms_in_hyps lib ts ts' hs,
    let sub1 := mk_hs_subst ts  hs in
    let sub2 := mk_hs_subst ts' hs in
    let C := ctype G in
      (
        tequality
          (lsubstc C (seq_cl S) sub1 (seq_cover S ts p))
          (lsubstc C (seq_cl S) sub2 (seq_cover2 S ts ts' p e))
        #
        equality (lsubstc t (seq_ex S) sub1 (seq_cover_ex S ts p))
                 (lsubstc t (seq_ex S) sub2 (seq_cover2_ex S ts ts' p e))
                 (lsubstc C (seq_cl S) sub1 (seq_cover S ts p))
      ).
*)

Lemma sequent_true_at_all {o} :
  forall lib S ts,
    sequent_true_at lib S ts
    <=>
    forall ts' : list (@CTerm o),
      match destruct_csequent S with
        | cseq_comps hs T wh wt ct ec =>
          forall p : hyps_true_at lib hs ts,
          forall e : equal_terms_in_hyps lib ts ts' hs,
            let sub1 := mk_hs_subst ts  hs in
            let sub2 := mk_hs_subst ts' hs in
            forall pC1 : cover_vars T sub1,
            forall pC2 : cover_vars T sub2,
              match ec with
                | Some (existT _ ext (we, ce)) =>
                    forall pt1 : cover_vars ext sub1,
                    forall pt2 : cover_vars ext sub2,
                      tequality lib (lsubstc T wt sub1 pC1)
                                (lsubstc T wt sub2 pC2)
                      #
                      equality lib (lsubstc ext we sub1 pt1)
                               (lsubstc ext we sub2 pt2)
                               (lsubstc T wt sub1 pC1)
                | None =>
                    tequality lib (lsubstc T wt sub1 pC1)
                              (lsubstc T wt sub2 pC2)
              end
      end.
Proof.
  unfold sequent_true_at; split; introv h;
  destruct (destruct_csequent S); destruct ec; exrepnd; intros; auto.

  generalize (h ts' p e); intro equs.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in equs; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in equs; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in equs; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in equs; auto.

  generalize (h ts' p e); intro equs.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in equs; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in equs; auto.
  sp.
Qed.

Lemma sequent_true_at_ex {o} :
  forall lib S ts,
    sequent_true_at lib S ts
    <=>
    forall ts' : list (@CTerm o),
      match destruct_csequent S with
        | cseq_comps hs T wh wt ct ec =>
          forall p : hyps_true_at lib hs ts,
          forall e : equal_terms_in_hyps lib ts ts' hs,
            let sub1 := mk_hs_subst ts  hs in
            let sub2 := mk_hs_subst ts' hs in
            {pC1 : cover_vars T sub1
             & {pC2 : cover_vars T sub2
                & tequality lib (lsubstc T wt sub1 pC1)
                            (lsubstc T wt sub2 pC2)
                  #
                  match ec with
                    | Some (existT _ ext (we, ce)) =>
                        {pt1 : cover_vars ext sub1
                         & {pt2 : cover_vars ext sub2
                         & equality lib (lsubstc ext we sub1 pt1)
                                    (lsubstc ext we sub2 pt2)
                                    (lsubstc T wt sub1 pC1)}}
                    | None => True
                  end}}
      end.
Proof.
  unfold sequent_true_at; split; introv h;
  destruct (destruct_csequent S); destruct ec; exrepnd; intros; auto.

  generalize (h ts' p e); intros; clear h; repnd.

  exists (seq_cover_typ1 lib T ts ts' hs ct e)
         (seq_cover_typ2 lib T ts ts' hs ct e); sp.
  exists (seq_cover_ex1 lib t ts ts' hs s0 e)
         (seq_cover_ex2 lib t ts ts' hs s0 e); sp.

  generalize (h ts' p e); intros; clear h; repnd.

  exists (seq_cover_typ1 lib T ts ts' hs ct e)
         (seq_cover_typ2 lib T ts ts' hs ct e); sp.

  generalize (h ts' p e); intros; clear h; exrepd.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1); auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2); auto.

  generalize (h ts' p e); intros; clear h; exrepd.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
Qed.

Lemma cover_csequent_change_wf {o} :
  forall (ts : list (@CTerm o)) s w1 w2,
    cover_csequent ts (mk_wcseq s w1) <=> cover_csequent ts (mk_wcseq s w2).
Proof.
  eauto with pi.
Qed.

Lemma sequent_true_at_change_wf {o} :
  forall lib (ts : list (@CTerm o)) s w1 w2,
    sequent_true_at lib (mk_wcseq s w1) ts <=> sequent_true_at lib (mk_wcseq s w2) ts.
Proof.
  eauto with pi.
Qed.

Lemma sequent_true_change_wf {o} :
  forall lib (s : @baresequent o) w1 w2,
    sequent_true lib (mk_wcseq s w1) <=> sequent_true lib (mk_wcseq s w2).
Proof.
  eauto with pi.
Qed.

Lemma scover_typ1 {o} :
  forall lib t s1 s2 (H : @bhyps o),
    covered t (vars_hyps H)
    -> pw_assign_eq lib s1 s2 H
    -> cover_vars t s1.
Proof.
  introv cv pw.
  rw @cover_vars_covered.
  allapply @pw_assign_eq_dom; sp; allrw <-; sp.
Qed.

Lemma scover_typ2 {o} :
  forall lib t s1 s2 (H : @bhyps o),
    covered t (vars_hyps H)
    -> pw_assign_eq lib s1 s2 H
    -> cover_vars t s2.
Proof.
  introv cv pw.
  rw @cover_vars_covered.
  allapply @pw_assign_eq_dom; sp; allrw <-; sp.
Qed.

Lemma scover_ex1 {o} :
  forall lib e s1 s2 (H : @bhyps o),
    covered e (nh_vars_hyps H)
    -> pw_assign_eq lib s1 s2 H
    -> cover_vars e s1.
Proof.
  introv cv pw; sp; allsimpl.
  rw @cover_vars_covered.
  allapply @pw_assign_eq_dom; sp; allrw <-.
  apply covered_subvars with (vs1 := nh_vars_hyps H); sp.
Qed.

Lemma scover_ex2 {o} :
  forall lib e s1 s2 (H : @bhyps o),
    covered e (nh_vars_hyps H)
    -> pw_assign_eq lib s1 s2 H
    -> cover_vars e s2.
Proof.
  introv cv pw; sp; allsimpl.
  rw @cover_vars_covered.
  allapply @pw_assign_eq_dom; sp; allrw <-.
  apply covered_subvars with (vs1 := nh_vars_hyps H); sp.
Qed.

(* end hide *)

(**

  Karl Crary defines the truth of a sequent as follows: A sequent [S]
  with hypotheses [H], type [T], and extract [ext], is true if for all
  substitutions [s1] and [s2], if the two substitutions are pointwise
  equal in [H], i.e., [pw_assign_eq lib s1 s2 H], then [s1(T)] is
  equal to [s2(T)] and [s1(ext)] and [s2(ext)] are equal in [s1(T)].

 *)

Definition KC_sequent_true {o} lib (S : @csequent o) : Type :=
  forall s1 s2 : CSubstitution,
    match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
          forall p : pw_assign_eq lib s1 s2 H,
            tequality lib (lsubstc T wt s1 (scover_typ1 lib T s1 s2 H ct p))
                      (lsubstc T wt s2 (scover_typ2 lib T s1 s2 H ct p))
            #
            match ec with
              | Some (existT _ ext (we, ce)) =>
                  equality lib (lsubstc ext we s1 (scover_ex1 lib ext s1 s2 H ce p))
                           (lsubstc ext we s2 (scover_ex2 lib ext s1 s2 H ce p))
                           (lsubstc T wt s1 (scover_typ1 lib T s1 s2 H ct p))
              | None => True
            end
    end.

(* begin hide *)

Lemma KC_sequent_true_all {o} :
  forall lib (S : @csequent o),
    KC_sequent_true lib S
    <=>
    forall s1 s2 : CSubstitution,
      match destruct_csequent S with
        | cseq_comps H T wh wt ct ec =>
            forall p : pw_assign_eq lib s1 s2 H,
            forall pC1 : cover_vars T s1,
            forall pC2 : cover_vars T s2,
              match ec with
                | Some (existT _ ext (we, ce)) =>
                    forall pt1 : cover_vars ext s1,
                    forall pt2 : cover_vars ext s2,
                      tequality lib (lsubstc T wt s1 pC1)
                                (lsubstc T wt s2 pC2)
                      # equality lib (lsubstc ext we s1 pt1)
                                 (lsubstc ext we s2 pt2)
                                 (lsubstc T wt s1 pC1)
                | None => tequality lib (lsubstc T wt s1 pC1)
                                    (lsubstc T wt s2 pC2)
              end
      end.
Proof.
  unfold KC_sequent_true; split; intro h;
  destruct (destruct_csequent S); destruct ec; exrepnd; intros; auto.

  generalize (h s2 s3 p); intro equs.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in equs; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in equs; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in equs; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in equs; auto.

  generalize (h s1 s2 p); intro equs.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in equs; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in equs; auto; sp.
Qed.

Lemma KC_sequent_true_ex {o} :
  forall lib (S : @csequent o),
    KC_sequent_true lib S
    <=>
    forall s1 s2 : CSubstitution,
      match destruct_csequent S with
        | cseq_comps H T wh wt ct ec =>
            forall p : pw_assign_eq lib s1 s2 H,
              {pC1 : cover_vars T s1
               & {pC2 : cover_vars T s2
               & tequality lib (lsubstc T wt s1 pC1)
                           (lsubstc T wt s2 pC2)
                 #
                 match ec with
                    | Some (existT _ ext (we, ce)) =>
                        {pt1 : cover_vars ext s1
                          & {pt2 : cover_vars ext s2
                             & equality lib (lsubstc ext we s1 pt1)
                                        (lsubstc ext we s2 pt2)
                                        (lsubstc T wt s1 pC1)}}
                    | None => True
                 end}}
               end.
Proof.
  unfold KC_sequent_true; split; intro h;
  destruct (destruct_csequent S); destruct ec; exrepnd; intros; auto.

  generalize (h s2 s3 p); intros; clear h.

  exists (scover_typ1 lib T s2 s3 hs ct p)
         (scover_typ2 lib T s2 s3 hs ct p); sp.
  exists (scover_ex1 lib t s2 s3 hs s0 p)
         (scover_ex2 lib t s2 s3 hs s0 p); sp.

  generalize (h s1 s2 p); intros; clear h.

  exists (scover_typ1 lib T s1 s2 hs ct p)
         (scover_typ2 lib T s1 s2 hs ct p); sp.

  generalize (h s2 s3 p); intros; exrepd.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1); auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2); auto.

  generalize (h s1 s2 p); intros; exrepd.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
Qed.

Lemma s_cover_typ1 {o} :
  forall lib t s1 s2 (H : @bhyps o),
    covered t (vars_hyps H)
    -> similarity lib s1 s2 H
    -> cover_vars t s1.
Proof.
  introv cv pw.
  rw @cover_vars_covered.
  allapply @similarity_dom; sp; allrw; sp.
Qed.

Lemma s_cover_typ2 {o} :
  forall lib t s1 s2 (H : @bhyps o),
    covered t (vars_hyps H)
    -> similarity lib s1 s2 H
    -> cover_vars t s2.
Proof.
  introv cv pw.
  rw @cover_vars_covered.
  allapply @similarity_dom; sp; allrw; sp.
Qed.

Lemma s_cover_ex1 {o} :
  forall lib e s1 s2 (H : @bhyps o),
    covered e (nh_vars_hyps H)
    -> similarity lib s1 s2 H
    -> cover_vars e s1.
Proof.
  introv cv pw; sp; allsimpl.
  rw @cover_vars_covered.
  allapply @similarity_dom; sp; allrw.
  apply covered_subvars with (vs1 := nh_vars_hyps H); sp.
Qed.

Lemma s_cover_ex2 {o} :
  forall lib e s1 s2 (H : @bhyps o),
    covered e (nh_vars_hyps H)
    -> similarity lib s1 s2 H
    -> cover_vars e s2.
Proof.
  introv cv pw; sp; allsimpl.
  rw @cover_vars_covered.
  allapply @similarity_dom; sp; allrw.
  apply covered_subvars with (vs1 := nh_vars_hyps H); sp.
Qed.

(* end hide *)

(**

  Aleksey Nogin defines the truth of a sequent as follows: A sequent
  [S] with hypotheses [H], type [T], and extract [ext], is true if for
  all substitution [s1], if [similarity lib s1 s1 H], and
  [hyps_functionality lib s1 H], then for all substitution [s2],
  if [similarity lib s1 s2 H] then [s1(T)] is equal to [s2(T)] and
  [s1(ext)] and [s2(ext)] are equal in [s1(T)].

 *)

Definition AN_sequent_true {o} lib (S : @csequent o) : Type :=
  forall s1,
    match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
          similarity lib s1 s1 H
          -> hyps_functionality lib s1 H
          -> forall s2,
             forall p : similarity lib s1 s2 H,
               tequality lib
                 (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                 (lsubstc T wt s2 (s_cover_typ2 lib T s1 s2 H ct p))
               #
               match ec with
                 | Some (existT _ ext (we, ce)) =>
                     equality lib
                       (lsubstc ext we s1 (s_cover_ex1 lib ext s1 s2 H ce p))
                       (lsubstc ext we s2 (s_cover_ex2 lib ext s1 s2 H ce p))
                       (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                 | None => True
               end
  end.

(**

  We slightly simplify Nogin's definition of a truth of a sequent by
  removing the [similarity lib s1 s1 H], which is redundant.  We say that
  a sequent [S] with hypotheses [H], type [T], and extract [ext], is
  true if for all substitutions [s1] and [s2], if [similarity lib s1 s2 H]
  and [hyps_functionality lib s1 H] are true then [s1(T)] is equal to
  [s2(T)] and [s1(ext)] and [s2(ext)] are equal in [s1(T)].

 *)

Definition VR_sequent_true {o} lib (S : @csequent o) : Type :=
  forall s1 s2,
    match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
          forall p : similarity lib s1 s2 H,
            hyps_functionality lib s1 H
            -> tequality lib
                 (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                 (lsubstc T wt s2 (s_cover_typ2 lib T s1 s2 H ct p))
               # match ec with
                   | Some (existT _ ext (we, ce)) =>
                       equality lib
                         (lsubstc ext we s1 (s_cover_ex1 lib ext s1 s2 H ce p))
                         (lsubstc ext we s2 (s_cover_ex2 lib ext s1 s2 H ce p))
                         (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                   | None => True
                 end
    end.

(* begin hide *)

(** Pairwise functionality *)
Definition AN_sequent_true_pairwise {o} lib (S : @csequent o) : Type :=
  forall s1 s2,
    match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
          forall p : similarity lib s1 s2 H,
            eq_hyps lib s1 s2 H
            -> tequality lib (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                         (lsubstc T wt s2 (s_cover_typ2 lib T s1 s2 H ct p))
               # match ec with
                   | Some (existT _ ext (we, ce)) =>
                       equality lib (lsubstc ext we s1 (s_cover_ex1 lib ext s1 s2 H ce p))
                                (lsubstc ext we s2 (s_cover_ex2 lib ext s1 s2 H ce p))
                                (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                   | None => True
                 end
    end.

Lemma s_cover_typ_1 {o} :
  forall lib t s1 s2 (H : @bhyps o),
    covered t (vars_hyps H)
    -> eqhyps lib s1 s2 H
    -> cover_vars t s1.
Proof.
  introv cv pw.
  rw @cover_vars_covered.
  allapply @eqhyps_dom; sp; allrw; sp.
Qed.

Lemma s_cover_typ_2 {o} :
  forall lib t s1 s2 (H : @bhyps o),
    covered t (vars_hyps H)
    -> eqhyps lib s1 s2 H
    -> cover_vars t s2.
Proof.
  introv cv pw.
  rw @cover_vars_covered.
  allapply @eqhyps_dom; sp; allrw; sp.
Qed.

Lemma s_cover_ex_1 {o} :
  forall lib e s1 s2 (H : @bhyps o),
    covered e (nh_vars_hyps H)
    -> eqhyps lib s1 s2 H
    -> cover_vars e s1.
Proof.
  introv cv pw; sp; allsimpl.
  rw @cover_vars_covered.
  allapply @eqhyps_dom; sp; allrw.
  apply covered_subvars with (vs1 := nh_vars_hyps H); sp.
Qed.

Lemma s_cover_ex_2 {o} :
  forall lib e s1 s2 (H : @bhyps o),
    covered e (nh_vars_hyps H)
    -> eqhyps lib s1 s2 H
    -> cover_vars e s2.
Proof.
  introv cv pw; sp; allsimpl.
  rw @cover_vars_covered.
  allapply @eqhyps_dom; sp; allrw.
  apply covered_subvars with (vs1 := nh_vars_hyps H); sp.
Qed.

(** AN_sequent_true is implied by that simpler form: *)
Definition AN_sp_sequent_true {o} lib (S : @csequent o) : Type :=
  forall s1 s2,
    match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
          forall p : eqhyps lib s1 s2 H,
            tequality lib (lsubstc T wt s1 (s_cover_typ_1 lib T s1 s2 H ct p))
                      (lsubstc T wt s2 (s_cover_typ_2 lib T s1 s2 H ct p))
            # match ec with
                | Some (existT _ ext (we, ce)) =>
                    equality lib (lsubstc ext we s1 (s_cover_ex_1 lib ext s1 s2 H ce p))
                             (lsubstc ext we s2 (s_cover_ex_2 lib ext s1 s2 H ce p))
                             (lsubstc T wt s1 (s_cover_typ_1 lib T s1 s2 H ct p))
                | None => True
              end
    end.

Lemma AN_sequent_true_all {o} :
  forall lib (S : @csequent o),
    AN_sequent_true lib S
    <=>
    forall s1,
      match destruct_csequent S with
        | cseq_comps H T wh wt ct ec =>
              similarity lib s1 s1 H
              -> hyps_functionality lib s1 H
              -> forall s2,
                 forall pC1 : cover_vars T s1,
                 forall pC2 : cover_vars T s2,
                   similarity lib s1 s2 H
                   -> match ec with
                        | Some (existT _ ext (we, ce)) =>
                            forall pt1 : cover_vars ext s1,
                            forall pt2 : cover_vars ext s2,
                              tequality lib (lsubstc T wt s1 pC1)
                                        (lsubstc T wt s2 pC2)
                              # equality lib (lsubstc ext we s1 pt1)
                                         (lsubstc ext we s2 pt2)
                                         (lsubstc T wt s1 pC1)
                        | None => tequality lib (lsubstc T wt s1 pC1)
                                            (lsubstc T wt s2 pC2)
                      end
      end.
Proof.
  unfold AN_sequent_true; split; intro h;
  destruct (destruct_csequent S); destruct ec; exrepnd; introv sim hf; auto.

  introv sim2; introv.
  generalize (h s2); clear h; introv hyp; repd.
  apply hyp with (s3 := s3) (p := sim2) in hf; auto.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in hf; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in hf; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in hf; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in hf; auto.

  generalize (h s1); clear h; introv hyp sim2; repd.
  apply hyp with (s2 := s2) (p := sim2) in hf; auto.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in hf; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in hf; auto; sp.
Qed.

Lemma AN_sequent_true_ex {o} :
  forall lib (S : @csequent o),
    AN_sequent_true lib S
    <=>
    forall s1,
      match destruct_csequent S with
        | cseq_comps H T wh wt ct ec =>
              similarity lib s1 s1 H
              -> hyps_functionality lib s1 H
              -> forall s2,
                   similarity lib s1 s2 H
                   -> {pC1 : cover_vars T s1
                       & {pC2 : cover_vars T s2
                          & tequality lib (lsubstc T wt s1 pC1)
                                      (lsubstc T wt s2 pC2)
                            #
                            match ec with
                              | Some (existT _ ext (we, ce)) =>
                                  {pt1 : cover_vars ext s1
                                   & {pt2 : cover_vars ext s2
                                      & equality lib (lsubstc ext we s1 pt1)
                                                 (lsubstc ext we s2 pt2)
                                                 (lsubstc T wt s1 pC1)}}
                              | None => True
                            end}}
      end.
Proof.
  unfold AN_sequent_true; split; intro h;
  destruct (destruct_csequent S); destruct ec; exrepnd; introv sim hf; introv; auto.

  introv sim2.
  generalize (h s2); intros hyp; clear h.
  apply hyp with (s3 := s3) (p := sim2) in hf; auto.

  exists (s_cover_typ1 lib T s2 s3 hs ct sim2)
         (s_cover_typ2 lib T s2 s3 hs ct sim2); sp.
  exists (s_cover_ex1 lib t s2 s3 hs s0 sim2)
         (s_cover_ex2 lib t s2 s3 hs s0 sim2); sp.

  introv sim2.
  generalize (h s1); intro hyp; clear h.
  apply hyp with (s2 := s2) (p := sim2) in hf; auto.

  exists (s_cover_typ1 lib T s1 s2 hs ct sim2)
         (s_cover_typ2 lib T s1 s2 hs ct sim2); sp.

  generalize (h s2); intro hyp.
  apply hyp with (s3 := s3) in hf; exrepd; auto.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1); auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2); auto.

  generalize (h s1); intro hyp.
  apply hyp with (s2 := s2) in hf; exrepd; auto.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
Qed.

Lemma VR_sequent_true_all {o} :
  forall lib (S : @csequent o),
    VR_sequent_true lib S
    <=>
    forall s1 s2,
      match destruct_csequent S with
        | cseq_comps H T wh wt ct ec =>
            forall pC1 : cover_vars T s1,
            forall pC2 : cover_vars T s2,
              similarity lib s1 s2 H
              -> hyps_functionality lib s1 H
              -> match ec with
                   | Some (existT _ ext (we, ce)) =>
                       forall pt1 : cover_vars ext s1,
                       forall pt2 : cover_vars ext s2,
                         tequality lib (lsubstc T wt s1 pC1)
                                   (lsubstc T wt s2 pC2)
                         # equality lib (lsubstc ext we s1 pt1)
                                    (lsubstc ext we s2 pt2)
                                    (lsubstc T wt s1 pC1)
                   | None => tequality lib (lsubstc T wt s1 pC1)
                                       (lsubstc T wt s2 pC2)
                 end
      end.
Proof.
  unfold VR_sequent_true; split; intro h;
  destruct (destruct_csequent S); destruct ec; exrepnd; introv sim; auto; introv hf.

  introv.
  generalize (h s2 s3 sim); clear h; intro hyp; repd.
  apply hyp in hf.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in hf; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in hf; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in hf; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in hf; auto.

  generalize (h s1 s2 sim); clear h; intro hyp; repd.
  apply hyp in hf.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in hf; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in hf; auto; sp.
Qed.

Lemma VR_sequent_true_ex {o} :
  forall lib (S : @csequent o),
    VR_sequent_true lib S
    <=>
    forall s1 s2,
      match destruct_csequent S with
        | cseq_comps H T wh wt ct ec =>
              hyps_functionality lib s1 H
              -> similarity lib s1 s2 H
              -> {pC1 : cover_vars T s1
                  & {pC2 : cover_vars T s2
                     & tequality lib (lsubstc T wt s1 pC1)
                                 (lsubstc T wt s2 pC2)
                       #
                       match ec with
                         | Some (existT _ ext (we, ce)) =>
                             {pt1 : cover_vars ext s1
                               & {pt2 : cover_vars ext s2
                                  & equality lib (lsubstc ext we s1 pt1)
                                             (lsubstc ext we s2 pt2)
                                             (lsubstc T wt s1 pC1)}}
                         | None => True
                       end}}
      end.
Proof.
  unfold VR_sequent_true; split; intro h;
  destruct (destruct_csequent S); destruct ec; exrepnd; introv hf; auto.

  intro sim.
  generalize (h s2 s3 sim); intro hyp; clear h.
  apply hyp in hf.

  exists (s_cover_typ1 lib T s2 s3 hs ct sim)
         (s_cover_typ2 lib T s2 s3 hs ct sim); sp.
  exists (s_cover_ex1 lib t s2 s3 hs s0 sim)
         (s_cover_ex2 lib t s2 s3 hs s0 sim); sp.

  intro sim.
  generalize (h s1 s2 sim); intro hyp; clear h.
  apply hyp in hf.

  exists (s_cover_typ1 lib T s1 s2 hs ct sim)
         (s_cover_typ2 lib T s1 s2 hs ct sim); sp.

  generalize (h s2 s3); intro hyp.
  repeat (dest_imp hyp hyp'); exrepnd.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1); auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2); auto.

  generalize (h s1 s2); intro hyp.
  repeat (dest_imp hyp hyp'); exrepnd.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
Qed.

Lemma AN_sp_sequent_true_all {o} :
  forall lib (S : @csequent o),
    AN_sp_sequent_true lib S
    <=>
    forall s1 s2,
    match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
          forall p : eqhyps lib s1 s2 H,
          forall pC1 : cover_vars T s1,
          forall pC2 : cover_vars T s2,
            match ec with
              | Some (existT _ ext (we, ce)) =>
                  forall pt1 : cover_vars ext s1,
                  forall pt2 : cover_vars ext s2,
                    tequality lib (lsubstc T wt s1 pC1)
                              (lsubstc T wt s2 pC2)
                    # equality lib (lsubstc ext we s1 pt1)
                               (lsubstc ext we s2 pt2)
                               (lsubstc T wt s1 pC1)
              | None => tequality lib (lsubstc T wt s1 pC1)
                                  (lsubstc T wt s2 pC2)
            end
    end.
Proof.
  unfold AN_sp_sequent_true; split; intro h;
  destruct (destruct_csequent S); destruct ec; exrepnd; introv; auto; introv eqh; introv.

  generalize (h s2 s3 eqh); intro equs.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in equs; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in equs; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in equs; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in equs; auto.

  generalize (h s1 s2 eqh); intro equs.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in equs; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in equs; auto; sp.
Qed.

Lemma AN_sp_sequent_true_ex {o} :
  forall lib (S : @csequent o),
    AN_sp_sequent_true lib S
    <=>
    forall s1 s2,
    match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
          forall p : eqhyps lib s1 s2 H,
            {pC1 : cover_vars T s1
             & {pC2 : cover_vars T s2
                & tequality lib (lsubstc T wt s1 pC1)
                            (lsubstc T wt s2 pC2)
                  #
                  match ec with
                    | Some (existT _ ext (we, ce)) =>
                        {pt1 : cover_vars ext s1
                      & {pt2 : cover_vars ext s2
                      & equality lib (lsubstc ext we s1 pt1)
                                 (lsubstc ext we s2 pt2)
                                 (lsubstc T wt s1 pC1)}}
                    | None => True
                  end}}
    end.
Proof.
  unfold AN_sp_sequent_true; split; intro h;
  destruct (destruct_csequent S); destruct ec; exrepnd; introv; auto.

  intro eqh.
  generalize (h s2 s3 eqh); sp.

  exists (s_cover_typ_1 lib T s2 s3 hs ct eqh)
         (s_cover_typ_2 lib T s2 s3 hs ct eqh); sp.
  exists (s_cover_ex_1 lib t s2 s3 hs s0 eqh)
         (s_cover_ex_2 lib t s2 s3 hs s0 eqh); sp.

  intro eqh.
  generalize (h s1 s2 eqh); sp.

  exists (s_cover_typ_1 lib T s1 s2 hs ct eqh)
         (s_cover_typ_2 lib T s1 s2 hs ct eqh); sp.

  generalize (h s2 s3 p); intros; exrepd.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1); auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2); auto.

  generalize (h s1 s2 p); intros; exrepd.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
Qed.

Lemma AN_sp_sequent_true_implies_AN {o} :
  forall lib (S : @csequent o),
    AN_sp_sequent_true lib S -> AN_sequent_true lib S.
Proof.
  intros.
  rw @AN_sp_sequent_true_ex in X; allsimpl.
  rw @AN_sequent_true_ex; allsimpl; intros.
  allunfold @hyps_functionality.
  apply_in_hyp p.
  applydup @eqhyps_if in p; auto.
Qed.

(* This is not provable *)
Lemma AN_sequent_true_implies_AN_sp {o} :
  forall lib (S : @csequent o),
    AN_sequent_true lib S -> AN_sp_sequent_true lib (S).
Proof.
  intros.
  rw @AN_sp_sequent_true_ex; simpl; sp.
  rw @AN_sequent_true_ex in X; allsimpl; sp.
  apply X; sp;
  try (apply similarity_refl with (s2 := s2));
  try (apply eqhyps_implies_similarity; sp).

  (* That's the subgoal we can't prove. *)
Abort.

(* end hide *)

(**

  It is straightforward to prove that Nogin's definition is equivalent
  to ours.

*)

Lemma AN_sequent_true_eq_VR {o} :
  forall lib (S : @csequent o),
    AN_sequent_true lib S <=> VR_sequent_true lib S.
Proof.
  intros.
  rw @AN_sequent_true_ex; allsimpl.
  rw @VR_sequent_true_ex; allsimpl; split; sp.

  allapplydup @similarity_refl; sp.
Qed.

(* begin hide *)



(* --------- *)

Lemma equal_terms_in_hyps_implies_similarity {o} :
  forall lib (hs : @bhyps o) s ts,
    length ts = length hs
    -> vars_hyps hs = dom_csub s
    -> equal_terms_in_hyps lib (crange s) ts hs
    -> similarity lib s (mk_hs_subst ts hs) hs.
Proof.
  induction hs using rev_list_indT; simpl; introv leq vheq e; sp; cpx.

  inversion e; subst; allsimpl; cpx.
  destruct s; allsimpl; sp.

  inversion e; subst; cpx.
  allrewrite @vars_hyps_snoc.
  generalize (snoc_cases (NVar * CTerm) s); sp; subst; allsimpl; cpx.
  allrewrite @crange_snoc.
  allrewrite @dom_csub_snoc; cpx; allsimpl; subst.
  rewrite mk_hs_subst_snoc; sp.

  apply IHhs in eqt; auto.

  duplicate p as p'.
  (* rw does not work here? *)
  apply cover_vars_sub in p; sp.

  apply @sim_cons with (w := w) (p := p); sp.

  assert (lsubstc (htyp a) w (mk_hs_subst (crange k) hs) p'
          = lsubstc (htyp a) w k p) as eq.
  apply lsubstc_eq; auto.
  apply mk_hs_subst_crange; auto.
  rewrite eq in e0; auto.
Qed.

Lemma similarity_implies_equal_terms_in_hyps {o} :
  forall lib (hs : @bhyps o) s ts,
    length ts = length hs
    -> similarity lib (mk_hs_subst ts hs) s hs
    -> equal_terms_in_hyps lib ts (crange s) hs.
Proof.
  induction hs using rev_list_indT; simpl; introv leq sim; cpx;
  inversion sim; subst; allsimpl; sp; cpx.

  rev_list_dest ts; cpx.
  rw @mk_hs_subst_snoc in sim; cpx.
  onerw @mk_hs_subst_snoc; cpx.
  rewrite crange_snoc; simpl.
  inversion sim; cpx; clear_irr.

  apply IHhs in sim0; sp.
  apply @EqInHyps_cons with (w := w) (p := p); sp.
Qed.

Lemma pw_assign_eq_implies_hyps_true_at {o} :
  forall lib (hs : @bhyps o) s1 s2,
    pw_assign_eq lib s1 s2 hs
    -> hyps_true_at lib hs (crange s1).
Proof.
  induction hs using rev_list_indT; simpl; introv pw;
  inversion pw; subst; allsimpl; cpx.

  rewrite crange_snoc; simpl.
  allapplydup IHhs.
  allapplydup @pw_assign_eq_dom; sp.
  duplicate p as p0.
  apply @cover_vars_sub with (hs := hs) in p; sp.

  apply @InHyp_cons with (w := w) (p := p); sp.

  assert (lsubstc (htyp a) w (mk_hs_subst (crange s0) hs) p
          = lsubstc (htyp a) w s0 p0)
    by (apply lsubstc_eq; sp; apply mk_hs_subst_crange; sp).

  allrw; allapply @equality_refl; sp.

  assert (lsubstc (htyp a) w (mk_hs_subst (crange s0) hs) p
          = lsubstc (htyp a) w s0 p0)
    by (apply lsubstc_eq; sp; apply mk_hs_subst_crange; sp).
  allrw.

  apply hf.
  apply equal_terms_in_hyps_implies_similarity; sp.
  allapply @equal_terms_in_hyps_length; sp.
Qed.

Lemma pw_assign_eq_implies_equal_terms_in_hyps {o} :
  forall lib (hs : @bhyps o) s1 s2,
    pw_assign_eq lib s1 s2 hs
    -> equal_terms_in_hyps lib (crange s1) (crange s2) hs.
Proof.
  induction hs using rev_list_indT; simpl; introv pw;
  inversion pw; subst; allsimpl; cpx.

  allapplydup IHhs.
  repeat (rewrite crange_snoc); allsimpl.

  allapplydup @pw_assign_eq_dom; sp.

  duplicate p as p0.
  apply @cover_vars_sub with (hs := hs) in p; sp.

  apply @EqInHyps_cons with (w := w) (p := p); sp.

  assert (lsubstc (htyp a) w s0 p0
          = lsubstc (htyp a) w (mk_hs_subst (crange s0) hs) p).
  apply lsubstc_eq; sp.
  rewrite mk_hs_subst_crange; sp.
  rewrite <- H; sp.
Qed.

Lemma equal_terms_in_hyps_implies_pw_assign_eq {o} :
  forall lib (hs : @bhyps o) ts1 ts2,
    hyps_true_at lib hs ts1
    -> equal_terms_in_hyps lib ts1 ts2 hs
    -> pw_assign_eq lib (mk_hs_subst ts1 hs) (mk_hs_subst ts2 hs) hs.
Proof.
  induction hs using rev_list_indT; simpl; introv hta eqt;
  inversion eqt; subst; allsimpl; cpx.

  allapplydup @equal_terms_in_hyps_length; sp.
  repeat (rewrite mk_hs_subst_snoc); sp.
  inversion hta; cpx.

  apply @pw_eq_cons with (w := w) (p := p); sp.

  assert (cover_vars (htyp a) (mk_hs_subst (crange s') hs)) as c1
    by (allapply @similarity_length; repd;
        clear_dependents p0;
        apply cover_vars_mk_hs_subst in p0; sp;
        apply cover_vars_mk_hs_subst; auto;
        try (rewrite crange_length; sp)).

  generalize (hf (crange s') c1); intro eqtyp.
  dest_imp eqtyp hyp.
  apply similarity_implies_equal_terms_in_hyps; sp.

  assert (lsubstc (htyp a) w0 (mk_hs_subst (crange s') hs) c1
          = lsubstc (htyp a) w s' p') as leq.
  apply lsubstc_eq; sp.
  apply mk_hs_subst_crange.
  allapply @similarity_dom; sp.
  rewrite leq in eqtyp.

  assert (lsubstc (htyp a) w0 (mk_hs_subst ts0 hs) p0
          = lsubstc (htyp a) w (mk_hs_subst ts0 hs) p) as leq2.
  apply lsubstc_eq; sp.
  rewrite leq2 in eqtyp; sp.
Qed.

Lemma eqhyps_implies_pw_assign_eq {o} :
  forall lib (hs : @bhyps o) s1 s2,
    eqhyps lib s1 s2 hs
    -> hyps_functionality lib s1 hs
    -> pw_assign_eq lib s1 s2 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv eqh hf;
  inversion eqh; subst; allsimpl; cpx.

  applydup IHhs in eqh0; sp.

  apply @pw_eq_cons with (w := w) (p := p1); sp.

  generalize (hf (snoc s' (hvar a, t2))); intro eqhyp.
  dest_imp eqhyp hyp.
  apply @sim_cons with (w := w) (p := p1); sp.
  inversion eqhyp; cpx.
  clear_irr; sp.

  introv sim.

  generalize (hf (snoc s' (hvar a, t2))); intro eqhyp.
  dest_imp eqhyp typ.
  apply @sim_cons with (w := w) (p := p1); sp.
  inversion eqhyp; cpx.
Qed.

Lemma pw_assign_eq_implies_similarity {o} :
  forall lib (hs : @bhyps o) s1 s2,
    pw_assign_eq lib s1 s2 hs
    -> similarity lib s1 s2 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv pw;
  inversion pw; subst; allsimpl; cpx.
  allapplydup IHhs; sp.
  apply @sim_cons with (w := w) (p := p); sp.
Qed.

Lemma pw_assign_eq_implies_hyps_functionality {o} :
  forall lib (hs : @bhyps o) s1 s2,
    pw_assign_eq lib s1 s2 hs
    -> hyps_functionality lib s1 hs.
Proof.
  induction hs using rev_list_indT; simpl; introv pw;
  inversion pw; subst; allsimpl; cpx.

  introv sim.
  rev_list_dest s'; inversion sim; cpx; clear_irr.

  assert (cover_vars (htyp a) u) as c'
    by (apply similarity_cover_vars with (t := htyp a) in sim0; sp).

  duplicate sim0 as sim1.
  apply hf with (p' := c') in sim1.

  duplicate pw0 as pw1.
  apply IHhs in pw1; sp.
  apply @eq_hyps_cons with (w := w) (p1 := p) (p2 := c'); auto.
Qed.

(* end hide *)

(**

  We now prove that Crary's notion of truth of a sequent is
  equivalent to the one defined in the Nuprl book.

 *)

Lemma sequent_true_eq_KC {o} :
  forall lib (S : @csequent o),
    sequent_true lib S <=> KC_sequent_true lib S.
Proof.
  introv; unfold sequent_true, cover_csequent, cover_ctsequent, cover_sequent, cover_hyps.
  destseq; simpl.
  sp_iff Case; intros.

  - Case "->".
    rw @KC_sequent_true_all; simpl; intros.
    generalize (X (crange s1)); intros imp.
    dest_imp imp hyp.
    unfold crange; rewrite map_length.
    allapply @pw_assign_eq_length; sp.

    rw @sequent_true_at_ex in imp; allsimpl.
    generalize (imp (crange s2)); clear imp; intro imp.
    dest_imp imp hyp.
    apply @pw_assign_eq_implies_hyps_true_at with (s2 := s2); auto.

    revert imp; allrw @mk_hs_subst_crange;
    try (complete (allapply @pw_assign_eq_dom; sp)); intro imp.

    dest_imp imp hyp; exrepnd; clear_irr.
    apply pw_assign_eq_implies_equal_terms_in_hyps; sp.

    destruct (extract_op_to_op_extract
                (extract (concl S))
                (nh_vars_hyps (hyps S))
                wfce
                ce);
      allsimpl; exrepnd; intros; proof_irr; sp.

  - Case "<-".
    rw @sequent_true_at_all; simpl; intros.
    rw @KC_sequent_true_ex in X; allsimpl.

    generalize (X (mk_hs_subst ts (hyps S)) (mk_hs_subst ts' (hyps S))); intros.
    dest_imp X0 hyp; exrepd; clear_irr; sp.
    apply equal_terms_in_hyps_implies_pw_assign_eq; sp.

    destruct (extract_op_to_op_extract
                (extract (concl S))
                (nh_vars_hyps (hyps S))
                wfce
                ce);
      allsimpl; exrepnd; intros; proof_irr; sp.
 Qed.

(**

  Finally, we prove that Nogin's notion of truth of a sequent is
  equivalent to the one defined by Crary.

 *)

Lemma sequent_true_KC_eq_AN {o} :
  forall lib (S : @csequent o),
    KC_sequent_true lib S <=> AN_sequent_true lib S.
Proof.
  destruct S; allsimpl; split; intro k.

  - rw @KC_sequent_true_ex in k; allsimpl.
    rw @AN_sequent_true_ex; allsimpl; introv sim1 hf sim2.
    applydup hf in sim2.
    apply k.
    applydup @eqhyps_if in sim0; auto.
    apply eqhyps_implies_pw_assign_eq; sp.

  - rw @AN_sequent_true_ex in k; allsimpl.
    rw @KC_sequent_true_ex; allsimpl; sp.
    apply k; sp.
    apply @similarity_refl with (s2 := s2).
    apply pw_assign_eq_implies_similarity; sp.
    apply pw_assign_eq_implies_hyps_functionality in p; sp.
    apply pw_assign_eq_implies_similarity; sp.
Qed.

(* begin hide *)

Lemma sequent_true_eq_VR {o} :
  forall lib (S : @csequent o),
    sequent_true lib S <=> VR_sequent_true lib S.
Proof.
  introv.
  rw @sequent_true_eq_KC.
  rw @sequent_true_KC_eq_AN.
  rw @AN_sequent_true_eq_VR.
  sp.
Qed.

Lemma sequent_true_assume_types {o} :
  forall lib (S : @csequent o),
    ((forall h H J,
        hyps (projT1 (projT1 (projT1 S))) = snoc H h ++ J
        -> {s1 : CSub
            , {w : wf_term (htyp h)
            , {c : cover_vars (htyp h) s1
            , {sim : similarity lib s1 s1 H
               , ltype lib (lvl h) (lsubstc (htyp h) w s1 c)}}}})
     -> sequent_true lib S)
    -> sequent_true lib S.
Proof.
  introv imp.
  destruct S; allsimpl.
  destruct x; allsimpl.
  destruct x; allsimpl.
  allrw @sequent_true_eq_VR.
  rw @VR_sequent_true_all; simpl.
  introv sim hf.
  rw @VR_sequent_true_all in imp; simpl.
  apply imp; clear imp; try (complete auto).
  introv eqh.
  rw eqh in sim.
  rw eqh in hf.
  duplicate sim as sim'.
  apply hf in sim.
  rw @eq_hyps_app in sim; exrepnd; subst.
  rw @eq_hyps_snoc in sim5; exrepnd; subst.
  rw @similarity_app in sim'; exrepnd; subst.
  apply app_split in sim'0; repnd; subst; try (complete (allrw length_snoc; allrw; sp)).
  apply app_split in sim'2; repnd; subst; try (complete (allrw length_snoc; allrw; sp)).
  rw @similarity_snoc in sim'5; exrepnd; subst; cpx; clear_irr.
  apply similarity_refl in sim'6.
  exists s1a w0 p sim'6.
  allapply @eqtypes_refl; sp.
Qed.

Definition arg_constraints {o} (arg : @sarg o) (hs : @bhyps o) :=
  match arg with
    | sarg_var v => True
    | sarg_term t => subvars (free_vars t) (nh_vars_hyps hs)
  end.

Definition args_constraints {o} (args : list (@sarg o)) (hs : @bhyps o) :=
  forall a : sarg, LIn a args -> arg_constraints a hs.

Definition ext_wf_cseq {o}
             (s : @baresequent o)
             (ws : wf_sequent s)
             (t : closed_type_baresequent s)
             (e : closed_extract_baresequent s) : wf_csequent s :=
  (ws, (t, e)).

(* end hide *)

(**

  We are now ready to define what it means for a rule to be valid.  A
  rule is valid if assuming that the main goal is well-formed (but not
  necessarily closed), and its type is closed w.r.t. the hypotheses,
  and each subgoal is well-formed, closed (both types and extracts),
  and true, then we can prove that the extract of the main goal is
  closed w.r.t. the non-hidden hypotheses of the sequent, and that the
  main goal is true.

 *)

Definition rule_true {o} lib (R : @rule o) : Type :=
  forall wg : wf_sequent (goal R),
  forall cg : closed_type_baresequent (goal R),
  forall cargs: args_constraints (sargs R) (hyps (goal R)),
  forall hyps : (forall s : baresequent,
                   LIn s (subgoals R)
                   -> {c : wf_csequent s & sequent_true lib (mk_wcseq s c)}),
    {c : closed_extract_baresequent (goal R)
     & sequent_true lib (mk_wcseq (goal R) (ext_wf_cseq (goal R) wg cg c))}.
Hint Unfold rule_true.

(**

  Equivalently, we say that a rule is valid if it satisfies
  [rule_true2] below.  The reason for having two definitions is that
  we had already proved several rules at the time we stated the
  simpler [rule_true2] definition.  The difference with [rule_true] is
  that in [rule_true2] we use an abstraction ([sequent_true2]) for the
  pair of proofs that a sequent is well-formed
  ([wf_csequent]) and true ([sequent_true]).

*)

Definition sequent_true2 {o} lib (s : @baresequent o) :=
  {c : wf_csequent s & sequent_true lib (mk_wcseq s c)}.
Definition pwf_sequent {o} (s : @baresequent o) :=
  wf_sequent s # closed_type_baresequent s.

Definition rule_true2 {o} lib (R : @rule o) : Type :=
  forall pwf   : pwf_sequent (goal R),
  forall cargs : args_constraints (sargs R) (hyps (goal R)),
  forall hyps  : (forall s, LIn s (subgoals R) -> sequent_true2 lib s),
    sequent_true2 lib (goal R).

(**

  The proof that the two definitions are equal is trivial.

*)

Lemma rule_true_iff_rule_true2 {o} :
  forall lib (R : @rule o), rule_true lib R <=> rule_true2 lib R.
Proof.
  introv; split; unfold rule_true, rule_true2; intro rt.

  - introv pwf args hs.
    destruct pwf as [wg cg].
    generalize (rt wg cg args); clear rt; intro rt.
    dest_imp rt hyp.
    exrepnd.
    unfold sequent_true2.
    exists (wg,(cg,c)); sp.

  - introv args hs.
    generalize (rt (wg,cg) args); clear rt; intro rt.
    dest_imp rt hyp.
    unfold sequent_true2 in rt; exrepnd.
    destruct c; repnd.
    exists p; sp.
    apply (sequent_true_change_wf lib (goal R) (w, (p0, p)) (ext_wf_cseq (goal R) wg cg p)); auto.
Qed.

(**

  Let us now define the following [nuprove] abstraction, which we use
  to prove Nuprl lemmas in Coq using the proofs that the Nuprl rules
  are valid and the definition of validity of rules.  It says that we
  have to prove that the provided [goal] is a true Nuprl type.

*)

Definition nuprove {o} lib (goal : @NTerm o) :=
  {t : NTerm
   & pwf_sequent (mk_baresequent [] (mk_concl goal t))
   # sequent_true2 lib (mk_baresequent [] (mk_concl goal t))}.


(**

  Because to prove [nuprove] expressions we also have to prove the
  well-formedness of sequents and because often, in a sequent, the
  subgoals are well-formed if the main goal is well-formed, we define
  the following [wf_rule] abstraction, which we use to simplify the
  process of proving Nuprl lemmas in Coq.

*)

Definition wf_subgoals {o} (R : @rule o) :=
  forall s, LIn s (subgoals R) -> pwf_sequent s.

Lemma fold_wf_subgoals {o} :
  forall R : @rule o,
    (forall s, LIn s (subgoals R) -> pwf_sequent s) = wf_subgoals R.
Proof. sp. Qed.

Definition wf_rule {o} (R : @rule o) :=
  pwf_sequent (goal R) -> wf_subgoals R.

(* begin hide *)

Definition wf_goal {o} lib (R : @rule o) :=
  wf_sequent (goal R)
  -> closed_type_baresequent (goal R)
  -> args_constraints (sargs R) (hyps (goal R))
  -> (forall s : baresequent,
        LIn s (subgoals R)
        -> {c : wf_csequent s & sequent_true lib (mk_wcseq s c)})
  -> closed_extract_baresequent (goal R).

Definition rule_true_if {o} lib (R : @rule o) : Type :=
  forall wg : wf_sequent (goal R),
  forall cg : closed_type_baresequent (goal R),
  (* for the subgoals we don't assume wf_hypotheses which we should be able to prove (f) *)
  forall whyps : (forall s : baresequent, LIn s (subgoals R) -> wf_csequent s),
  forall cargs : args_constraints (sargs R) (hyps (goal R)),
    (forall s : baresequent,
     forall p : LIn s (subgoals R),
     forall c : wf_csequent s,
       sequent_true lib (mk_wcseq s c))
    -> forall c : wf_csequent (goal R), sequent_true lib (mk_wcseq (goal R) c).

Definition rule_true_ex {o} lib (R : @rule o) : Type :=
  (* For the main goal we'll have to prove closed_extract (c) *)
  {c : wf_goal lib R & rule_true_if lib R}.

Lemma rule_true_eq_ex {o} :
  forall lib (R : @rule o), rule_true_ex lib R <=> rule_true lib R.
Proof.
  unfold rule_true, rule_true_ex, rule_true_if; sp; split; sp.

  unfold wf_goal in c; sp.
  exists c; sp.
  apply s; sp.
  apply hyps0 in X; sp.
  apply hyps0 in p; sp.
  revert s1.
  unfold sequent_true.
  unfold cover_csequent, cover_ctsequent, cover_sequent; allsimpl; sp.
  apply s1 in H.
  destseq; proof_irr.
  rw @sequent_true_at_all in H; allsimpl.
  rw @sequent_true_at_all; simpl; sp.

  exists (fun wg cg cargs hyps => projT1 (X wg cg cargs hyps)); sp.
  assert (forall s : baresequent,
            LIn s (subgoals R) ->
            {c:wf_csequent s & sequent_true lib (mk_wcseq s c)}) as hyps; sp.
  applydup whyps in X1.
  generalize (X0 s X1 X2); sp.
  exists X2; sp.
  generalize (X wg cg cargs hyps); sp.
  allunfold @sequent_true.
  allunfold @cover_csequent; allunfold @cover_ctsequent; allunfold @cover_sequent; allsimpl.
  sp.
  apply s in H.
  destseq; proof_irr.
  rw @sequent_true_at_all in H; allsimpl.
  rw @sequent_true_at_all; simpl; sp.
Qed.


(* --------- Now we prove that there is a simple way to prove that
 * sequents are true when the hypotheses don't change between the
 * main sequent and the sub-sequents. *)

(*
Lemma sp_rule_true :
  forall (hs : @bhyps o)   : barehypotheses,
  forall C    : NTerm,
  forall seqs : list baresequent,
    (forall s : baresequent, LIn s seqs -> hyps s = hs # extract (concl s) = mk_axiom)
    -> (forall s1 s2 : CSub,
          (forall C : NTerm,
           forall m : LIn C (map baresequent_type seqs),
             {pC : wf_term C
              & {c1 : cover_vars C s1
              & {c2 : cover_vars C s2
                 & tequality (lsubstc C pC s1 c1) (lsubstc C pC s2 c2)
                 # member mkc_axiom (lsubstc C pC s1 c1)}}})
          -> forall pC : wf_term C,
             forall c1 : cover_vars C s1,
             forall c2 : cover_vars C s2,
               (tequality (lsubstc C pC s1 c1) (lsubstc C pC s2 c2)
                          # member mkc_axiom (lsubstc C pC s1 c1)))
    -> rule_true (mk_rule (mk_baresequent hs (mk_conclax C)) seqs []).
Proof.
  unfold rule_true.
  introv ss imp cargs hyps; allsimpl.
  clear cargs.

  assert (closed_extract_baresequent (mk_baresequent hs (mk_conclax C))) as wc
         by (unfold closed_extract_baresequent, closed_extract; simpl; sp).
  exists wc.

  rw sequent_true_eq_VR.
  rw VR_sequent_true_all; allsimpl.
  introv sim eqh.
  repeat (rewrite lsubstc_mk_axiom).
  rewrite member_eq.
  apply imp; sp.
  allrw in_map_iff; sp; subst.

  destruct a; unfold baresequent_type; simpl.
  applydup hyps in p0; allsimpl; sp.
  inversion c; repd; allsimpl.
  inversion X; allsimpl.
  inversion X0; allsimpl.
  applydup similarity_dom in sim; sp.
  applydup ss in p0; allsimpl; sp; subst.
  allunfold closed_type; allsimpl.
  duplicate c0 as c2.
  rewrite <- sim1 in c0.
  rewrite <- sim0 in c2.
  rw <- cover_vars_covered in c0.
  rw <- cover_vars_covered in c2.

  exists H0 c0 c2.

  generalize (hyps ({| hyps := hs;
                       concl := concl0 |})
                   p0); intros; exrepd.
  rw sequent_true_eq_VR in s0.
  rw VR_sequent_true_ex in s0; allsimpl.

  generalize (s0 s1 s2); clear s0; intro hyp.
  repeat (dest_imp hyp h).
  exrepd; clear_irr; sp.
  revert pt3 pt0 H1 e.
  rw p1; sp; clear_irr.
  repeat (rewrite lsubstc_mk_axiom in e).
  rewrite member_eq in e; sp.
Qed.
*)


(* !! THIS HAS TO BE FIXED *)

(*
Lemma sp_rule_true_no_hyps :
  forall H : hypotheses,
  forall C : NTerm,
  forall p : wf_conclusion H (mk_conclax C),
    (forall s1 s2 : CSub,
     forall pC : wf_term C,
     forall c1 : cover_vars C s1,
     forall c2 : cover_vars C s2,
       (tequality (lsubstc C pC s1 c1) (lsubstc C pC s2 c2)
        # member mkc_axiom (lsubstc C pC s1 c1)))
    -> rule_true (mk_rule (mk_seq H (mk_conclax C) p) []).
Proof.
  sp.
  assert ([] = map (fun x : { c : NTerm & wf_conclusion H (mk_conclax c) }
                    => mk_seq H (mk_conclax (projT1 x)) (projT2 x)) [])
         by (simpl; auto).
  rewrite H0.
  apply sp_rule_true; simpl; intros.
  apply X.
Qed.
*)




(* begin hide *)






(* ============== GARBAGE =============== *)

(*
Lemma simple_rule_true :
  forall H  : hypotheses,
  forall C  : NTerm,
  forall p  : wf_conclusion H (mk_conclax C),
  forall Cs : list { c : NTerm & wf_conclusion H (mk_conclax c) },
    (forall ts1 ts2 : list CTerm,
       (forall C : NTerm,
        forall m : LIn C (map (fun x => projT1 x) Cs),
          {pC : wf_term C
           & {c1 : cover_vars C (mk_hyps_subst ts1 H)
           & {c2 : cover_vars C (mk_hyps_subst ts2 H)
              & tequality (lsubstc C pC (mk_hyps_subst ts1 H) c1)
                          (lsubstc C pC (mk_hyps_subst ts2 H) c2)
              # member mkc_axiom (lsubstc C pC (mk_hyps_subst ts1 H) c1)}}})
       -> forall pC : wf_term C,
          forall c1 : cover_vars C (mk_hyps_subst ts1 H),
          forall c2 : cover_vars C (mk_hyps_subst ts2 H),
            (tequality (lsubstc C pC (mk_hyps_subst ts1 H) c1)
                       (lsubstc C pC (mk_hyps_subst ts2 H) c2)
             # member mkc_axiom (lsubstc C pC (mk_hyps_subst ts1 H) c1)))
    -> rule_true (mk_rule (mk_seq H (mk_conclax C) p)
                          (map (fun x => mk_seq H (mk_conclax (projT1 x)) (projT2 x)) Cs)).
Proof.
  unfold rule_true, sequent_true; sp.
  rw sequent_true_at_eq; allsimpl; intros.
  repeat (rewrite lsubstc_mk_axiom).
  rewrite member_eq.
  apply X; sp.
  rw in_map_iff in m; sp; subst.

  assert (LIn (mk_seq H (mk_conclax c) w)
             (map
                (fun x : {c : NTerm & wf_conclusion H (mk_conclax c)} =>
                   mk_seq H (mk_conclax (projT1 x)) (projT2 x)) Cs)) as lin
    by (rw in_map_iff;
        exists (existT (fun c : NTerm => wf_conclusion H (mk_conclax c)) c w); sp).

  apply X0 with (ts := ts) in lin; sp.

  rw sequent_true_at_eq_ex in lin; allsimpl; sp.
  generalize (lin ts'); sp.
  repeat (rewrite lsubstc_mk_axiom in p1).
  rewrite member_eq in p1.
  exists wC0 pC0 pC3; sp.
Qed.
*)

(*
Lemma wf_cl_cl :
  forall C H,
    wf_conclusion H (mk_conclax C)
    -> wf_term C.
Proof.
  intros C H X.
  inversion X; sp; allsimpl.
Qed.

Lemma wf_cl_cover :
  forall C H ts,
    wf_conclusion H (mk_conclax C)
    -> cover_hypotheses ts H
    -> cover_vars C (mk_hyps_subst ts H).
Proof.
  sp.
  inversion X; sp; allsimpl.
  unfold cover_vars, over_vars.
  allunfold covered.
  destruct H; allsimpl.
  unfold mk_hyps_subst; simpl.
  rewrite <- dom_mk_hs_subst; auto.
Qed.

Lemma wf_cl_cl_lst :
  forall C H,
  forall Cs : list { c : NTerm & wf_conclusion H (mk_conclax c) },
    LIn C (map (fun x => projT1 x) Cs)
    -> wf_term C.
Proof.
  sp.
  allrw in_map_iff; sp; subst.
  apply wf_cl_cl with (H := H); auto.
Qed.

Lemma wf_cl_cover_lst :
  forall C H ts,
  forall Cs : list { c : NTerm & wf_conclusion H (mk_conclax c) },
    LIn C (map (fun x => projT1 x) Cs)
    -> cover_hypotheses ts H
    -> cover_vars C (mk_hyps_subst ts H).
Proof.
  sp.
  allrw in_map_iff; sp; subst.
  apply wf_cl_cover; auto.
Qed.

Lemma cover_vars_eq_terms_in_hyps :
  forall ts1 ts2 H t,
    equal_terms_in_hyps lib ts1 ts2 H
    -> cover_vars t (mk_hs_subst ts1 H)
    -> cover_vars t (mk_hs_subst ts2 H).
Proof.
  intros ts1 ts2 H t e.
  apply equal_terms_in_hyps_length in e; repd.
  unfold cover_vars, over_vars.
  repeat (rewrite <- dom_mk_hs_subst); sp; symmetry; sp.
Qed.
*)

(*
Lemma lsubstc_seq_cl_eq :
  forall H  : hypotheses,
  forall C  : NTerm,
  forall p  : wf_conclusion H (mk_conclax C),
  forall ts : list CTerm,
  forall c  : cover_hypotheses ts H,
  forall a  : hyps_true_at (projT1 H) ts,
    lsubstc C
            (seq_cl (mk_seq H (mk_conclax C) p))
            (mk_hs_subst ts (projT1 H))
            (seq_cover (mk_seq H (mk_conclax C) p) ts a)
    =
    lsubstc C
            (wf_cl_cl C H p)
            (mk_hyps_subst ts H)
            (wf_cl_cover C H ts p c).
Proof.
  sp; unfold lsubstc.
  destruct H; allsimpl.
  rewrite dep_pair_eq_prop
  with (eq0 := eq_refl)
         (pb := isprog_lcsubst C (mk_hs_subst ts x)
                               (wf_cl_cl C (exist (fun hs : barehypotheses => wf_hypotheses hs) x w)
                                         p)
                               (wf_cl_cover C
                                            (exist (fun hs : barehypotheses => wf_hypotheses hs) x w) ts p c)); sp.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma lsubstc_seq_cl_eq2 :
  forall H  : hypotheses,
  forall C  : NTerm,
  forall p  : wf_conclusion H (mk_conclax C),
  forall ts ts' : list CTerm,
  forall c  : cover_hypotheses ts H,
  forall a  : hyps_true_at (projT1 H) ts,
  forall e  : equal_terms_in_hyps lib ts ts' (projT1 H),
    lsubstc C
            (seq_cl (mk_seq H (mk_conclax C) p))
            (mk_hs_subst ts' (projT1 H))
            (seq_cover2 (mk_seq H (mk_conclax C) p) ts ts' a e)
    =
    lsubstc C
            (wf_cl_cl C H p)
            (mk_hyps_subst ts' H)
            (wf_cl_cover C H ts' p (cover_hypotheses_eq ts ts' H c e)).
Proof.
  sp; unfold lsubstc.
  destruct H; allsimpl.
  rewrite dep_pair_eq_prop
  with (eq0 := eq_refl)
         (pb := isprog_lcsubst C (mk_hs_subst ts' x)
                               (wf_cl_cl C (exist (fun hs : barehypotheses => wf_hypotheses hs) x w)
                                         p)
                               (wf_cl_cover C
                                            (exist (fun hs : barehypotheses => wf_hypotheses hs) x w) ts' p
                                            (cover_hypotheses_eq ts ts'
                                                                 (exist (fun hs : barehypotheses => wf_hypotheses hs) x w) c e))); sp.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma lsubstc_seq_cl_lst :
  forall C  : NTerm,
  forall H  : hypotheses,
  forall ts : list CTerm,
  forall Cs : list {c : NTerm & wf_conclusion H (mk_conclax c)},
  forall wc : wf_conclusion H (mk_conclax C),
  forall ch : cover_hypotheses ts H,
  forall m  : LIn C
                 (map
                    (fun x : {c : NTerm & wf_conclusion H (mk_conclax c)} => projT1 x)
                    Cs),
    lsubstc C
            (wf_cl_cl_lst C H Cs m)
            (mk_hyps_subst ts H)
            (wf_cl_cover_lst C H ts Cs m ch)
    =
    lsubstc C
            (wf_cl_cl C H wc)
            (mk_hyps_subst ts H)
            (wf_cl_cover C H ts wc ch).
Proof.
  unfold lsubstc; sp.
  rewrite dep_pair_eq
  with (eq0 := eq_refl)
         (pb := isprog_lcsubst C (mk_hyps_subst ts H) (wf_cl_cl C H wc)
                               (wf_cl_cover C H ts wc ch)); sp.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma simple_rule_true :
  forall H  : hypotheses,
  forall C  : NTerm,
  forall p  : wf_conclusion H (mk_conclax C),
  forall Cs : list { c : NTerm & wf_conclusion H (mk_conclax c) },
    (forall ts1 ts2 : list CTerm,
     forall c1 : cover_hypotheses ts1 H,
     forall c2 : cover_hypotheses ts2 H,
       (forall C : NTerm,
        forall m : LIn C (map (fun x => projT1 x) Cs),
          tequality (lsubstc C
                             (wf_cl_cl_lst C H Cs m)
                             (mk_hyps_subst ts1 H)
                             (wf_cl_cover_lst C H ts1 Cs m c1))
                    (lsubstc C
                             (wf_cl_cl_lst C H Cs m)
                             (mk_hyps_subst ts2 H)
                             (wf_cl_cover_lst C H ts2 Cs m c2))
          # member mkc_axiom (lsubstc C
                                       (wf_cl_cl_lst C H Cs m)
                                       (mk_hyps_subst ts1 H)
                                       (wf_cl_cover_lst C H ts1 Cs m c1)))
       -> (tequality (lsubstc C
                              (wf_cl_cl C H p)
                              (mk_hyps_subst ts1 H)
                              (wf_cl_cover C H ts1 p c1))
                     (lsubstc C
                              (wf_cl_cl C H p)
                              (mk_hyps_subst ts2 H)
                              (wf_cl_cover C H ts2 p c2))
           # member mkc_axiom (lsubstc C
                                        (wf_cl_cl C H p)
                                        (mk_hyps_subst ts1 H)
                                        (wf_cl_cover C H ts1 p c1))))
    -> rule_true (mk_rule (mk_seq H (mk_conclax C) p)
                          (map (fun x => mk_seq H (mk_conclax (projT1 x)) (projT2 x)) Cs)).
Proof.
  unfold rule_true, sequent_true, sequent_true_at, cover_sequent; simpl; intros.
  repeat (rewrite lsubstc_mk_axiom).
  rewrite member_eq.
  rewrite lsubstc_seq_cl_eq with (c := H2).
  rewrite lsubstc_seq_cl_eq2 with (c := H2).

  apply H0; intros.

  assert (wf_conclusion H (mk_conclax C0)).
  allrewrite in_map_iff; sp; subst.
  destruct x; allsimpl; auto.

  assert (In (mk_seq H (mk_conclax C0) H3)
             (map
                (fun x : {c : NTerm & wf_conclusion H (mk_conclax c)} =>
                   mk_seq H (mk_conclax (projT1 x)) (projT2 x)) Cs)).
  allrewrite in_map_iff; sp; subst.
  destruct x; allsimpl.
  assert (w = H3) by apply wf_conclusion_proof_irrelevance.
  exists (existT (fun c => wf_conclusion H (mk_conclax c)) x H3); simpl; sp.
  rewrite <- H4; auto.

  apply H1 with (ts := ts) (ts' := ts') (p := p0) (e := e) in H4; allsimpl; auto.

  repeat (rewrite lsubstc_mk_axiom in H4).
  rewrite member_eq in H4.
  rewrite lsubstc_seq_cl_eq with (c := H2) in H4.
  rewrite lsubstc_seq_cl_eq2 with (c := H2) in H4.

  repeat (rewrite lsubstc_seq_cl_lst with (wc := H3)).
  auto.
Qed.
*)

(*
Lemma simple2_rule_true :
  forall H : hypotheses,
  forall T e : NTerm,
  forall Cs : list conclusion,
    (forall ts1 ts2 : list NTerm,
       length ts1 = length H
       -> length ts2 = length H
       -> (forall t, LIn t ts1 -> closed t)
       -> (forall t, LIn t ts2 -> closed t)
       -> (forall C : conclusion,
             LIn C Cs
             -> (tequality (lsubst (ctype C) (mk_hyp_sub ts1 H))
                           (lsubst (ctype C) (mk_hyp_sub ts2 H))
                           # equality (lsubst (extract C) (mk_hyp_sub ts1 H))
                                       (lsubst (extract C) (mk_hyp_sub ts2 H))
                                       (lsubst (ctype C) (mk_hyp_sub ts1 H))))
       -> (tequality (lsubst T (mk_hyp_sub ts1 H)) (lsubst T (mk_hyp_sub ts2 H))
                     # equality (lsubst e (mk_hyp_sub ts1 H))
                                 (lsubst e (mk_hyp_sub ts2 H))
                                 (lsubst T (mk_hyp_sub ts1 H))))
    -> rule_true (mk_rule (mk_sequent H (mk_concl T e))
                          (map (fun C => mk_sequent H C) Cs)).
Proof.
  intros.
  unfold rule_true, sequent_true; simpl; intros.
  unfold sequent_true_at; simpl; intros.
  apply H0; auto.
  apply equal_terms_in_hyps_length in H6; sp.
  rewrite <- H6; auto.
  intros.
  assert (In (mk_sequent H C) (map (fun C => mk_sequent H C) Cs))
         by (rewrite in_map_iff; exists C; sp).
  apply H1 with (ts := ts) in H8; auto.
Qed.
*)

(* end hide *)
