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


Require Export terms2.
Require Export terms_tacs.
Require Export lmap.
(** printing #  $\times$ #×# *)
(** printing $  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing &  $\times$ #×# *)

(* ---- substitution: td[x\ts] *) (*(\x.x+1)(x+2)*)

(*(\y.y+z)[z->y]*)
(** The goal of this section is to formalize the notion of simultaneous
    substitution([lsubst]) and alpha equality [alpha_eq].
    We needed many properties about substitution and alpha equality
    to formalize all of Nuprl. Proofs of all these properties run into
    several thousands of lines and took us several weeks to finish.
    These proofs are independent
    of the operators of the language and will work unchanged
    even if we formalize some different language, e.g. first order logic
    by merely changing the definition of [Opid]. Thus, we believe
    that we have accidentally created a fairly general-purpose
    library for nominal reasoning about virtually any language. *)


(** ** Substitution*)
(** The Substitution operation
    is a key concept in functional languages.
    Among other things, it is required to define the
    computation system and the semantics of dependent types.
    The goal of this subsection is to formalize [lsubst], a function
    that simultaneously substitutes some variables for some terms.

    We define a Substitution as a list of pairs:

[[
Definition Substitution   : Set := list (NVar # NTerm).
]]
 *)

(* begin hide *)
Definition Substitution   {p} : tuniv := lmap NVar (@NTerm p).
Definition WfSubstitution {p} : tuniv := lmap NVar (@WTerm p).
Definition CSubstitution  {p} : tuniv := lmap NVar (@CTerm p).
(* end hide *)

(** % \noindent %
  The function [var_ren] below provides a way to 
  define the specialized substitutions that are 
  variable renamings (substituting one variable for another).
  The %\coqslibref{combine}{Coq.Lists.List}{\coqdocdefinition{combine}}% function
  from the standard library takes two lists and zips them up.
 *)

Definition var_ren {p} (lvo lvn : list NVar) : @Substitution p :=
  combine lvo (map vterm lvn).

(* begin hide *)

Lemma var_ren_nil_l {p} :
  forall vs, @var_ren p [] vs = [].
Proof. sp. Qed.

Lemma var_ren_nil_r {p} :
  forall vs, @var_ren p vs [] = [].
Proof.
  induction vs; simpl; sp.
Qed.

Lemma var_ren_cons {p} :
  forall v1 v2 vs1 vs2,
    @var_ren p (v1 :: vs1) (v2 :: vs2)
    = (v1, vterm v2) :: (var_ren vs1 vs2).
Proof. sp. Qed.

Lemma fold_var_ren {p} :
  forall lvo lvn, combine lvo (map vterm lvn) = @var_ren p lvo lvn.
Proof. sp. Qed.

(* end hide *)


(** % \noindent \\* %
The domain and range of a substitution are defined as follows:

[[
Definition dom_sub  (sub : Substitution) : list NVar := map (fun x => fst x) sub.
]]

*)

(* begin hide *)
Definition Sub  {p} := @Substitution p.
Definition CSub {p} := @CSubstitution p.

Definition dom_sub {p} : @Substitution p -> (list NVar):= @dom_lmap NVar NTerm.
Definition dom_csub   {p} (sub : @CSubstitution p)  := map (fun x => fst x) sub.
Definition wf_dom_sub {p} (sub : @WfSubstitution p) := map (fun x => fst x) sub.
(* end hide *)
Definition range {p} (sub : @Substitution p)  : list NTerm := map (fun x => snd x) sub.

(** % \noindent \\*%
  We need to define some helper functions before defining the
  substitution function that simultaneously substitutes the
  in the first component([NVar]s) of the pairs with the second ones([NTerm]s).
*)

(* begin hide *)

Definition crange {p} (sub : @CSubstitution p) : list CTerm := map (fun x => snd x) sub.

(*
Lemma deq_in_sub {p} :
  dec_consts p
  -> forall v t (sub : @Substitution p),
       LIn (v,t) sub + !LIn (v,t) sub.
Proof.
  introv dc; introv.
  apply in_deq; sp.
  apply deq_prod; sp; try (apply deq_nvar); try (apply deq_nterm).
Qed.
*)

Definition sub_range_sat {p} (sub: @Substitution p) (P: NTerm -> Type) :=
  forall v t, LIn (v,t) sub -> P t.

(*
Definition sub_range_satb {p} (dc : dec_consts p) (sub: @Substitution p) (P: NTerm -> Type) :=
  forall t, assert (memberb (deq_nterm dc) t (range sub)) -> P t.
*)

Lemma in_range {p} :
  forall t sub, LIn t (@range p sub) -> {v : NVar $ LIn (v,t) sub}.
Proof.
  induction sub; allsimpl; sp; allsimpl; subst.
  exists a0; sp.
  exists v; sp.
Qed.

(*
Lemma in_range_t {p} :
  dec_consts p
  -> forall (t : @NTerm p) sub, LIn t (range sub) -> {v : NVar & LIn (v,t) sub}.
Proof.
  introv dc i.
  rw <- (@assert_memberb (@NTerm p) (deq_nterm dc)) in i.
  induction sub; allsimpl; sp; allsimpl.
  unfold assert in i; sp.
  destruct (deq_nterm dc a t); subst; sp.
  exists a0; sp.
  exists v; sp.
Qed.

Lemma in_range_t_iff {p} :
  dec_consts p
  -> forall (t : @NTerm p) sub, LIn t (range sub) <=> {v : NVar & LIn (v,t) sub}.
Proof.
  introv dc; introv; split; intro k.
  apply in_range_t; auto.
  exrepnd.
  unfold range.
  rw in_map_iff.
  exists (v,t); auto.
Qed.
*)

(*
Lemma sub_range_sat_implies_b {p} :
  forall dc : dec_consts p,
  forall sub P,
    @sub_range_sat p sub P -> sub_range_satb dc sub P.
Proof.
  unfold sub_range_sat, sub_range_satb; introv s a.
  rw (@assert_memberb (@NTerm p) (deq_nterm dc)) in a.
  allapply (@in_range_t p dc); sp.
  discover; sp.
Qed.
*)

Lemma sub_range_sat_implies {p} :
  forall (P Q : @NTerm p -> Type),
    (forall t, P t -> Q t)
    -> forall sub,
         sub_range_sat sub P
         -> sub_range_sat sub Q.
Proof.
  introv Himp Hsat Hin. apply Hsat in Hin.
  apply Himp in Hin. sp.
Qed.

Definition prog_sub {p} (sub : @Substitution p) := sub_range_sat sub isprogram.

Definition wf_sub {p} (sub : @Substitution p) := sub_range_sat sub nt_wf.

Lemma wf_sub_nil {o} : @wf_sub o [].
Proof.
  unfold wf_sub, sub_range_sat; simpl; sp.
Qed.
Hint Resolve wf_sub_nil : slow.

Lemma wf_sub_cons {o} :
  forall v (t : @NTerm o) sub,
    wf_term t -> wf_sub sub -> wf_sub ((v,t) :: sub).
Proof.
  introv wt ws.
  allunfold @wf_sub.
  allunfold @sub_range_sat; simpl; introv k; repndors; ginv.
  - rw @nt_wf_eq; auto.
  - eapply ws; eauto.
Qed.
Hint Resolve wf_sub_cons : slow.


(* will not specialize this lemma.. those are always trivial*)
Lemma sub_app_sat {p} :
  forall P sub1 sub2,
    @sub_range_sat p sub1 P
    -> sub_range_sat sub2 P
    -> sub_range_sat (sub1 ++ sub2) P.
Proof.
  introv sat1 sat2 Hin.
  apply in_app_iff in Hin.
  dorn Hin; [ apply sat1 in Hin | apply sat2 in Hin]; trivial.
Qed.

Lemma sub_app_sat_if {p} :
  forall P sub1 sub2,
    @sub_range_sat p (sub1 ++ sub2) P
    -> sub_range_sat sub1 P # sub_range_sat sub2 P.
Proof.
  introv  Hsat.
  split;
    introv Hin;
    assert (LIn (v, t) (sub1 ++ sub2))
      as Hx
        by (apply in_app_iff;((left;sp;fail) || (right;sp;fail)));
    apply Hsat in Hx;sp.
Qed.


(* end hide *)
Fixpoint sub_find {p} (sub : @Substitution p) (var : NVar) : option NTerm :=
  match sub with
  | nil => None
  | (v, t) :: xs => if beq_var v var then Some t else sub_find xs var
  end.
(* begin hide *)

Lemma beq_deq : forall T v1 v2 (ct cf:T) ,
  (if (beq_var v1 v2)  then ct else cf) = (if (deq_nvar v1 v2)  then ct else cf).
  intros. cases_if as Hb; auto; cases_if as Hd ; auto; subst.
  apply not_eq_beq_var_false in Hd. rewrite Hd in Hb; sp. 
  rewrite <- beq_var_refl in Hb. sp.
Qed.

Definition lmap_apply {A : Set} (eqdec: Deq A) (sub: lmap A A) (a:A): A :=
  match lmap_find eqdec sub a with
    | inl (existT _ a' _) =>  a'
    | inr _ => a
  end.

Definition lmap_lapply {A : Set} (eqdec: Deq A) (sub: lmap A A)  (la:list A): list A :=
  map (fun a:A =>  lmap_apply eqdec sub a) la.

Definition lvmap_lapply  (sub: lmap NVar NVar)  (la:list NVar): list NVar :=
  map (fun a:NVar =>  lmap_apply deq_nvar sub a) la.

Lemma sub_lmap_find {p} :
  forall sub v,
    @sub_find p sub v =
    proj_as_option (lmap_find deq_nvar sub v).
Proof.
  induction sub as [| a]; intros ; auto; simpl. 
  destruct a. rewrite beq_deq. 
  cases_if; subst; auto.
  rewrite IHsub. destruct ((lmap_find deq_nvar sub v)); simpl;
  try(destruct s; simpl); auto.
Qed.


Lemma sub_lmap_find_first {p} :
  forall sub v,
    @sub_find p sub v =
    proj_as_option (lmap_find_first deq_nvar sub v).
Proof.
  induction sub as [| a]; intros ; auto; simpl. 
  destruct a. rewrite beq_deq. 
  cases_if; subst; auto.
  rewrite IHsub. destruct ((lmap_find_first deq_nvar sub v)); simpl;
  exrepnd; auto.  
Qed.

(*
Lemma match_sub_lmap_find: forall sub v cs cn, 
  match (sub_find sub v)
  | Some t => cs t
  | None => cn
  end
    =
  match (sub_find sub v)
  | Some t => cs t
  | None => cn
  end
*)  


Definition csub2sub {p} (sub : @CSubstitution p) : Substitution :=
  map (fun x => (fst x, get_cterm (snd x))) sub.

Lemma csub2sub_app {p} :
  forall sub1 sub2,
    @csub2sub p sub1 ++ csub2sub sub2 = csub2sub (sub1 ++ sub2).
Proof.
  unfold csub2sub; sp.
  rewrite <- map_app; sp.
Qed.

Lemma csub2sub_snoc {p} :
  forall sub v t,
    @csub2sub p (snoc sub (v, t)) = snoc (csub2sub sub) (v, get_cterm t).
Proof.
  unfold csub2sub; sp.
  rewrite map_snoc; sp.
Qed.

Lemma in_csub2sub {p} :
  forall sub : @CSubstitution p,
  forall v : NVar,
  forall u : NTerm,
    LIn (v, u) (csub2sub sub)
    -> isprogram u.
Proof.
  induction sub; simpl; sp; destruct a; allsimpl.
  inj.
  allrw @isprogram_eq; sp.
  apply_in_hyp pp; sp.
Qed.

(* end hide *)

Definition over_vars {p} (vs : list NVar) (sub : @CSubstitution p) :=
  subvars vs (dom_csub sub).

(* begin hide *)

Lemma over_vars_proof_irrelevance {p} :
  forall vs s,
  forall x y : @over_vars p vs s,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : over_vars ?vs ?s , H2 : over_vars ?vs ?s |- _ ] =>
    pose proof (over_vars_proof_irrelevance vs s H2 H1) as h; subst
end : pi.

(* end hide *)

(**

  A term [t] is covered by a substitution [sub] if the free variables
  of [t] are all in the domain of [sub].

*)

Definition cover_vars {p} (t : @NTerm p) (sub : @CSubstitution p) :=
  over_vars (free_vars t) sub.

(* begin hide *)

Lemma cover_vars_proof_irrelevance {p} :
  forall t s,
  forall x y : @cover_vars p t s,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : cover_vars ?t ?s , H2 : cover_vars ?t ?s |- _ ] =>
    pose proof (cover_vars_proof_irrelevance t s H2 H1) as h; subst
end : pi.

(* end hide *)

(**

  We sometimes need the slightly more general definition that
  expresses that a term [t] is covered by a substitution [sub] up to a
  set of variables [vs], meaning that the free variables of [t] have
  to either be in [vs] or in the domain of [sub].  Such a concept is
  needed to deal with type families such as function or W types.

*)

Definition cover_vars_upto {p} (t : @NTerm p) (sub : @CSub p) (vs : list NVar) :=
  subvars (free_vars t) (vs ++ dom_csub sub).

(* begin hide *)

Lemma cover_vars_upto_proof_irrelevance {p} :
  forall t s vs,
  forall x y : @cover_vars_upto p t s vs,
    x = y.
Proof.
  intros.
  apply UIP_dec.
  apply bool_dec.
Qed.

Hint Extern 0 =>
let h := fresh "h" in
match goal with
  | [ H1 : cover_vars_upto ?t ?s ?vs , H2 : cover_vars_upto ?t ?s ?vs |- _ ] =>
    pose proof (cover_vars_upto_proof_irrelevance t s vs H2 H1) as h; subst
end : pi.

Lemma covered_free_from_atom {p} :
  forall a b c vs,
    @covered p (mk_free_from_atom a b c) vs
    <=> covered a vs
        # covered b vs
        # covered c vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_free_from_atoms {p} :
  forall a b vs,
    @covered p (mk_free_from_atoms a b) vs
    <=> covered a vs
        # covered b vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_equality {p} :
  forall a b T vs,
    @covered p (mk_equality a b T) vs
    <=> covered a vs
        # covered b vs
        # covered T vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_tequality {p} :
  forall a b vs,
    @covered p (mk_tequality a b) vs
    <=> covered a vs
        # covered b vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_axiom {p} :
  forall vs, @covered p mk_axiom vs.
Proof.
  unfold covered; sp; simpl.
Qed.

Hint Immediate covered_axiom.

Lemma covered_uni {p} :
  forall vs i, @covered p (mk_uni i) vs.
Proof.
  unfold covered; sp; simpl.
Qed.

Hint Immediate covered_uni.

Lemma covered_isect {p} :
  forall a v b vs,
    @covered p (mk_isect a v b) vs
    <=> covered a vs # covered b (v :: vs).
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_eisect {p} :
  forall a v b vs,
    @covered p (mk_eisect a v b) vs
    <=> covered a vs # covered b (v :: vs).
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_disect {p} :
  forall a v b vs,
    @covered p (mk_disect a v b) vs
    <=> covered a vs # covered b (v :: vs).
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_set {p} :
  forall a v b vs,
    @covered p (mk_set a v b) vs
    <=> covered a vs # covered b (v :: vs).
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_tunion {p} :
  forall a v b vs,
    @covered p (mk_tunion a v b) vs
    <=> covered a vs # covered b (v :: vs).
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_quotient {p} :
  forall a v1 v2 b vs,
    @covered p (mk_quotient a v1 v2 b) vs
    <=> covered a vs # covered b (v1 :: v2 :: vs).
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_var {p} :
  forall v vs, @covered p (mk_var v) vs <=> LIn v vs.
Proof.
  unfold covered; sp; simpl.
  rw subvars_prop; simpl; split; sp; subst; sp.
Qed.

Lemma covered_subvars {p} :
  forall t vs1 vs2,
    subvars vs1 vs2
    -> @covered p t vs1
    -> covered t vs2.
Proof.
  intros.
  allunfold @covered.
  apply subvars_trans with (vs2 := vs1); sp.
Qed.

Lemma covered_snoc_app_weak {p} :
  forall t vs1 vs2 v,
    @covered p t (vs1 ++ vs2)
    -> covered t (snoc vs1 v ++ vs2).
Proof.
  sp; allunfold @covered; allrw subvars_prop; sp.
  apply_in_hyp pp.
  allrw in_app_iff; allrw in_snoc; sp.
Qed.


(* filters out the mappings whose domain lies in vars *)
Fixpoint lmap_filter {A B: Set}
  (eqdec: Deq A) (sub: lmap A B)  (vars : list A) : lmap A B :=
  match sub with
  | nil => nil
  | (v, t) :: xs =>
      if in_deq A eqdec  v vars
      then lmap_filter eqdec xs vars
      else (v, t) :: lmap_filter eqdec xs vars
  end.

(* end hide *)
(* removes from sub the variables from vars *)
Fixpoint sub_filter {p} (sub : @Substitution p) (vars : list NVar) : Substitution :=
  match sub with
  | nil => nil
  | (v, t) :: xs =>
      if memvar v vars
      then sub_filter xs vars
      else (v, t) :: sub_filter xs vars
  end.
(* begin hide *)



(* Same as sub_filter but on a CSub *)
Fixpoint csub_filter {p} (sub : @CSub p) (vars : list NVar) : CSub :=
  match sub with
  | nil => nil
  | (v, t) :: xs =>
      if memvar v vars
      then csub_filter xs vars
      else (v, t) :: csub_filter xs vars
  end.

Lemma sub_filter_csub2sub {p} :
  forall sub vs,
    @sub_filter p (csub2sub sub) vs
    = csub2sub (csub_filter sub vs).
Proof.
  induction sub; simpl; sp.
  destruct a; allsimpl.
  destruct (memvar a0 vs); sp; simpl.
  rewrite IHsub; sp.
Qed.

Lemma sub_filter_subset {p} :
  forall sub vars,
    subset (@sub_filter p sub vars) sub.
Proof.
  induction sub; simpl; sp.
  destruct (memvar a0 vars).
  apply subset_cons1; auto.
  apply subset_cons2; auto.
Qed.

Lemma sub_filter_nil_r {p} :
  forall sub, @sub_filter p sub [] = sub.
Proof.
  induction sub; simpl; sp.
  rewrite IHsub; auto.
Qed.

Lemma in_sub_filter {p} :
  forall v t sub vars,
    LIn (v, t) (@sub_filter p sub vars)
    <=>
    (
      LIn (v, t) sub
      #
      ! LIn v vars
    ).
Proof.
  induction sub; simpl; sp.
  split; sp.
  boolvar; simpl; allrw; split; sp; cpx.
Qed.

Lemma sub_filter_sat {p} :
  forall P sub lv,
    @sub_range_sat p sub P
    -> sub_range_sat (sub_filter sub lv) P.
Proof. introv Hall hsub. apply in_sub_filter in hsub. repnd.
  apply Hall in hsub0; auto.
Qed.


Lemma sub_filter_app {p} :
  forall sub1 sub2 vars,
    @sub_filter p (sub1 ++ sub2) vars
    = sub_filter sub1 vars ++ sub_filter sub2 vars.
Proof.
  induction sub1; simpl; sp.
  rewrite IHsub1; auto.
  destruct (memvar a0 vars); sp.
Qed.

Lemma sub_filter_snoc {p} :
  forall sub v t vars,
    @sub_filter p (snoc sub (v, t)) vars
    = if memvar v vars
      then sub_filter sub vars
      else snoc (sub_filter sub vars) (v, t).
Proof.
  induction sub; simpl; sp; allsimpl.
  rewrite IHsub.
  destruct (eq_var_dec a0 v); subst.
  destruct (memvar v vars); sp.
  destruct (memvar v vars); sp.
  destruct (memvar a0 vars); sp.
Qed.

Lemma dom_sub_sub_filter {p} :
  forall l sub,
    remove_nvars l (@dom_sub p sub) = dom_sub (sub_filter sub l).
Proof.
  induction sub; simpl; sp; allsimpl.
  apply remove_nvars_nil_r.
  rewrite remove_nvars_cons_r.
  destruct (memvar a0 l); auto.
  rewrite IHsub.
  simpl; auto.
Qed.

Lemma dom_csub_csub_filter {p} :
  forall l sub,
    dom_csub (@csub_filter p sub l) = remove_nvars l (dom_csub sub).
Proof.
  induction sub; simpl; sp; allsimpl.
  rewrite remove_nvars_nil_r; sp.
  rewrite remove_nvars_cons_r.
  destruct (memvar a0 l); auto; simpl.
  rewrite IHsub; auto.
Qed.

Lemma sub_filter_app_r {p} :
  forall sub vs1 vs2,
    @sub_filter p sub (vs1 ++ vs2)
    = sub_filter (sub_filter sub vs1) vs2.
Proof.
  induction sub; simpl; sp.
  rewrite memvar_app.
  destruct (memvar a0 vs1); simpl.
  apply IHsub.
  destruct (memvar a0 vs2); simpl.
  apply IHsub.
  rewrite IHsub; auto.
Qed.

Lemma crange_snoc {p} :
  forall sub x,
    @crange p (snoc sub x) = snoc (crange sub) (snd x).
Proof.
  unfold crange; simpl; sp.
  rewrite map_snoc; sp.
Qed.

Lemma crange_length {p} :
  forall sub,
    length (@crange p sub) = length sub.
Proof.
  unfold crange; sp.
  rewrite map_length; sp.
Qed.

Lemma dom_csub_length {p} :
  forall sub,
    length (@dom_csub p sub) = length sub.
Proof.
  unfold dom_csub; sp.
  rewrite map_length; sp.
Qed.

Lemma cover_vars_covered {p} :
  forall t sub,
    @cover_vars p t sub <=> covered t (dom_csub sub).
Proof.
  sp.
Qed.


(** clear_irr removes the duplicates of proofs of propositions that
 * have proof irrelevance. *)
Ltac clear_irr :=
  repeat match goal with
           | [ H1 : covered ?a ?b, H2 : covered ?a ?b |- _ ] =>
             assert (H2 = H1) by apply covered_proof_irrelevance; subst
           | [ H1 : cover_vars ?a ?b, H2 : cover_vars ?a ?b |- _ ] =>
             assert (H2 = H1) by apply cover_vars_proof_irrelevance; subst
           | [ H1 : cover_vars_upto ?a ?b ?c, H2 : cover_vars_upto ?a ?b ?c |- _ ] =>
             assert (H2 = H1) by apply cover_vars_upto_proof_irrelevance; subst
           | [ H1 : wf_term ?a, H2 : wf_term ?a |- _ ] =>
             assert (H2 = H1) by apply wf_term_proof_irrelevance; subst
           | [ H1 : isprog ?a, H2 : isprog ?a |- _ ] =>
             assert (H2 = H1) by apply isprog_proof_irrelevance; subst
         end.

Lemma dom_sub_snoc {p} :
  forall s v t,
    @dom_sub p (snoc s (v, t)) = snoc (dom_sub s) v.
Proof.
  induction s; simpl; sp; simpl; allrw; sp.
Qed.

Lemma dom_csub_snoc {p} :
  forall sub x,
    @dom_csub p (snoc sub x) = snoc (dom_csub sub) (fst x).
Proof.
  induction sub; simpl; sp.
  rewrite IHsub; sp.
Qed.

Lemma cover_vars_upto_csub_filter_snoc_weak {p} :
  forall t x sub vs,
    @cover_vars_upto p t (csub_filter sub vs) vs
    -> cover_vars_upto t (csub_filter (snoc sub x) vs) vs.
Proof.
  introv cv.
  allunfold @cover_vars_upto.
  prove_subvars cv.
  allrw in_app_iff; sp.
  allrw @dom_csub_csub_filter.
  allrw in_remove_nvars; sp.
  allrw @dom_csub_snoc; allsimpl.
  allrw in_snoc; sp.
Qed.

Lemma cover_vars_upto_snoc_weak {p} :
  forall t x sub vs,
    @cover_vars_upto p t sub vs
    -> cover_vars_upto t (snoc sub x) vs.
Proof.
  introv cv.
  allunfold @cover_vars_upto.
  prove_subvars cv.
  allrw in_app_iff; sp.
  allrw @dom_csub_snoc; allsimpl.
  allrw in_snoc; sp.
Qed.

Lemma dom_csub_app {p} :
  forall sub1 sub2,
    @dom_csub p (sub1 ++ sub2) = dom_csub sub1 ++ dom_csub sub2.
Proof.
  unfold dom_csub; sp.
  rewrite map_app; sp.
Qed.

Lemma dom_csub_eq {p} :
  forall sub,
    @dom_sub p (csub2sub sub) = dom_csub sub.
Proof.
  induction sub; simpl; sp.
  rewrite IHsub; sp.
Qed.

Lemma over_vars_eq {p} :
  forall vs : list NVar,
  forall sub : @CSub p,
    over_vars vs sub <=> subvars vs (dom_csub sub).
Proof.
  unfold over_vars; sp.
Qed.

Lemma cover_vars_eq {p} :
  forall t : NTerm,
  forall sub : @CSub p,
    cover_vars t sub <=> subvars (free_vars t) (dom_csub sub).
Proof.
  unfold cover_vars; sp.
Qed.

Lemma cover_vars_cterm {p} :
  forall t s, @cover_vars p (get_cterm t) s.
Proof.
  introv; destruct_cterms; simpl.
  rw @cover_vars_eq.
  allrw @isprog_eq; allunfold @isprogram; repnd; allrw; sp.
Qed.
Hint Immediate cover_vars_cterm.

Lemma cover_vars_app_weak {p} :
  forall t sub1 sub2,
    @cover_vars p t sub1
    -> cover_vars t (sub1 ++ sub2).
Proof.
  intros.
  allrw @cover_vars_eq.
  allrw subvars_eq.
  rw @dom_csub_app.
  apply subset_app_r; auto.
Qed.

Lemma cover_vars_snoc_weak {p} :
  forall t x sub,
    @cover_vars p t sub
    -> cover_vars t (snoc sub x).
Proof.
  intros.
  allrw @cover_vars_eq.
  allrw subvars_eq.
  rw @dom_csub_snoc.
  apply subset_snoc_r; auto.
Qed.

Lemma cover_vars_snoc_weak_r {p} :
  forall t sub v u,
    (forall x, LIn x (free_vars t) -> x = v)
    -> @cover_vars p t (snoc sub (v,u)).
Proof.
  intros.
  rw @cover_vars_eq.
  rw subvars_eq.
  rw @dom_csub_snoc; simpl.
  apply subset_snoc_l; auto.
Qed.

Lemma cover_vars_axiom {p} :
  forall sub,
    @cover_vars p mk_axiom sub.
Proof.
  intro; rw @cover_vars_eq; rw subvars_eq; simpl.
  unfold subset; allsimpl; sp.
Qed.

Hint Immediate cover_vars_axiom.

Lemma cover_vars_axiom_iff {p} :
  forall sub,
    @cover_vars p mk_axiom sub <=> True.
Proof.
  sp; split; sp.
Qed.

Lemma cover_vars_base {p} :
  forall sub,
    @cover_vars p mk_base sub.
Proof.
  intro; rw @cover_vars_eq; rw subvars_eq; simpl; sp.
Qed.

Hint Immediate cover_vars_base.

Lemma cover_vars_base_iff {p} :
  forall sub,
    @cover_vars p mk_base sub <=> True.
Proof.
  sp.
Qed.

Lemma over_vars_app_l {p} :
  forall vs1 vs2 sub,
    @over_vars p (vs1 ++ vs2) sub <=> over_vars vs1 sub # over_vars vs2 sub.
Proof.
  sp; rw subvars_app_l; sp.
Qed.

Lemma cover_vars_free_from_atom {p} :
  forall a b c sub,
    @cover_vars p (mk_free_from_atom a b c) sub
    <=> cover_vars a sub
        # cover_vars b sub
        # cover_vars c sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_free_from_atoms {p} :
  forall a b sub,
    @cover_vars p (mk_free_from_atoms a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_equality {p} :
  forall a b T sub,
    @cover_vars p (mk_equality a b T) sub
    <=> cover_vars a sub
        # cover_vars b sub
        # cover_vars T sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_tequality {p} :
  forall a b sub,
    @cover_vars p (mk_tequality a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_approx {p} :
  forall a b sub,
    @cover_vars p (mk_approx a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_cequiv {p} :
  forall a b sub,
    @cover_vars p (mk_cequiv a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_apply {p} :
  forall a b sub,
    @cover_vars p (mk_apply a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_sup {p} :
  forall a b sub,
    @cover_vars p (mk_sup a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_member {p} :
  forall a T sub,
    @cover_vars p (mk_member a T) sub
    <=> cover_vars a sub
        # cover_vars T sub.
Proof.
  sp; unfold mk_member.
  rw @cover_vars_equality; split; sp.
Qed.

Lemma cover_vars_type {p} :
  forall a sub,
    @cover_vars p (mk_type a) sub
    <=> cover_vars a sub.
Proof.
  sp; unfold mk_type.
  rw @cover_vars_tequality; split; sp.
Qed.

Lemma cover_vars_function {p} :
  forall a v b sub,
    @cover_vars p (mk_function a v b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_product {p} :
  forall a v b sub,
    @cover_vars p (mk_product a v b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_w {p} :
  forall a v b sub,
    @cover_vars p (mk_w a v b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_m {p} :
  forall a v b sub,
    @cover_vars p (mk_m a v b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_pw {p} :
  forall P ap A bp ba B cp ca cb C q sub,
    @cover_vars p (mk_pw P ap A bp ba B cp ca cb C q) sub
    <=> cover_vars P sub
        # cover_vars_upto A (csub_filter sub [ap]) [ap]
        # cover_vars_upto B (csub_filter sub [bp,ba]) [bp,ba]
        # cover_vars_upto C (csub_filter sub [cp,ca,cb]) [cp,ca,cb]
        # cover_vars q sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.

  assert (ap :: remove_nvars [ap] (dom_csub sub)
          = [ap] ++ remove_nvars [ap] (dom_csub sub)) as eq by auto.
  rw eq; clear eq.

  assert (bp :: ba :: remove_nvars [bp,ba] (dom_csub sub)
          = [bp,ba] ++ remove_nvars [bp,ba] (dom_csub sub)) as eq by auto.
  rw eq; clear eq.

  assert (cp :: ca :: cb :: remove_nvars [cp,ca,cb] (dom_csub sub)
          = [cp,ca,cb] ++ remove_nvars [cp,ca,cb] (dom_csub sub)) as eq by auto.
  rw eq; clear eq.

  allrw subvars_app_remove_nvars_r.

  assert (forall vs1 vs2,
            subvars vs1 (vs2 ++ dom_csub sub)
                    <=> subvars vs1 (dom_csub sub ++ vs2))
         as eq by (intros; apply subvars_swap_r; sp).

  allrw eq; sp.
Qed.

Lemma cover_vars_pm {p} :
  forall P ap A bp ba B cp ca cb C q sub,
    @cover_vars p (mk_pm P ap A bp ba B cp ca cb C q) sub
    <=> cover_vars P sub
        # cover_vars_upto A (csub_filter sub [ap]) [ap]
        # cover_vars_upto B (csub_filter sub [bp,ba]) [bp,ba]
        # cover_vars_upto C (csub_filter sub [cp,ca,cb]) [cp,ca,cb]
        # cover_vars q sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.

  assert (ap :: remove_nvars [ap] (dom_csub sub)
          = [ap] ++ remove_nvars [ap] (dom_csub sub)) as eq by auto.
  rw eq; clear eq.

  assert (bp :: ba :: remove_nvars [bp,ba] (dom_csub sub)
          = [bp,ba] ++ remove_nvars [bp,ba] (dom_csub sub)) as eq by auto.
  rw eq; clear eq.

  assert (cp :: ca :: cb :: remove_nvars [cp,ca,cb] (dom_csub sub)
          = [cp,ca,cb] ++ remove_nvars [cp,ca,cb] (dom_csub sub)) as eq by auto.
  rw eq; clear eq.

  allrw subvars_app_remove_nvars_r.

  assert (forall vs1 vs2,
            subvars vs1 (vs2 ++ dom_csub sub)
                    <=> subvars vs1 (dom_csub sub ++ vs2))
         as eq by (intros; apply subvars_swap_r; sp).

  allrw eq; sp.
Qed.

Lemma cover_vars_upto_axiom {p} :
  forall vs sub, @cover_vars_upto p mk_axiom sub vs.
Proof.
  intros; unfold cover_vars_upto; simpl; sp.
Qed.
Hint Immediate cover_vars_upto_axiom.

Lemma cover_vars_image {p} :
  forall a b sub,
    @cover_vars p (mk_image a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_isect {p} :
  forall a v b sub,
    @cover_vars p (mk_isect a v b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_eisect {p} :
  forall a v b sub,
    @cover_vars p (mk_eisect a v b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_disect {p} :
  forall a v b sub,
    @cover_vars p (mk_disect a v b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_set {p} :
  forall a v b sub,
    @cover_vars p (mk_set a v b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_tunion {p} :
  forall a v b sub,
    @cover_vars p (mk_tunion a v b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_quotient {p} :
  forall a v1 v2 b sub,
    @cover_vars p (mk_quotient a v1 v2 b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v1,v2]) [v1,v2].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v1 :: v2 :: remove_nvars [v1,v2] (dom_csub sub)
          = [v1,v2] ++ remove_nvars [v1,v2] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_lam {p} :
  forall v b sub,
    @cover_vars p (mk_lam v b) sub
    <=> cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw app_nil_r.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_id {p} :
  forall sub, @cover_vars p mk_id sub.
Proof.
  unfold mk_id; sp.
  rw @cover_vars_lam; simpl.
  unfold cover_vars_upto.
  simpl.
  rw subvars_eq.
  unfold subset; simpl; sp.
Qed.
Hint Immediate cover_vars_id.

Lemma cover_vars_squash {p} :
  forall a sub, @cover_vars p (mk_squash a) sub <=> cover_vars a sub.
Proof.
  introv.
  rw @cover_vars_image; split; sp.
  apply cover_vars_lam; sp.
Qed.

Lemma cover_vars_subtype {p} :
  forall a b sub,
    @cover_vars p (mk_subtype a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  sp; unfold mk_subtype, mk_vsubtype.
  rw @cover_vars_member.
  rw @cover_vars_function.
  unfold cover_vars_upto.
  rw subvars_eq; simpl.
  rw subset_nil_l_iff.
  split; sp.

  rw @cover_vars_eq; allrw subvars_prop; sp.
  apply_in_hyp pp; allsimpl; sp; subst.
  allapply @newvar_prop; sp.
  allrewrite @dom_csub_csub_filter.
  allrw in_remove_nvars; sp.

  rw @dom_csub_csub_filter.
  allrw @cover_vars_eq.
  apply subvars_cons_r.
  allrw subvars_prop; sp.
  apply_in_hyp pp.
  rw in_remove_nvars; simpl; sp; subst.
  allapply @newvar_prop; sp.
Qed.

Lemma cover_vars_cbv {p} :
  forall a v b sub,
    @cover_vars p (mk_cbv a v b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_halts {p} :
  forall a sub,
    @cover_vars p (mk_halts a) sub
    <=> cover_vars a sub.
Proof.
  sp; unfold mk_halts; split; sp; allrw @cover_vars_eq; allsimpl;
  allrw remove_nvars_nil_l; allrw app_nil_r;
  allrw subvars_app_l; sp.
Qed.

Lemma cover_vars_uni {p} :
  forall i sub, @cover_vars p (mk_uni i) sub.
Proof.
  sp; rw @cover_vars_eq; simpl.
  autorewrite with core; sp.
Qed.

Hint Immediate cover_vars_uni.

Definition CSubOver {p} (vs : list NVar) : tuniv :=
  { s : @CSubstitution p | over_vars vs s }.

Definition csubo2csub {p} (vs : list NVar) (sub : CSubOver vs) : @CSubstitution p :=
  let (s,x) := sub in s.

Definition dom_csubo {p} (vs : list NVar) (sub : @CSubOver p vs) :=
  dom_csub (csubo2csub vs sub).

Definition csubo2sub {p} (vs : list NVar) (sub : @CSubOver p vs) : Substitution :=
  csub2sub (csubo2csub vs sub).

Lemma in_dom_sub {p} :
  forall v t sub,
    LIn (v, t) sub
    -> LIn v (@dom_sub p sub).
Proof.
  unfold dom_sub; sp.
  rw in_map_iff.
  exists (v, t); sp.
Qed.

Lemma dom_sub_app {p} :
  forall sub1 sub2,
    @dom_sub p (sub1 ++ sub2) = dom_sub sub1 ++ dom_sub sub2.
Proof.
  unfold dom_sub, dom_lmap; intros; rw map_app; auto.
Qed.

Lemma dom_sub_map_axiom {p} :
  forall vars,
    @dom_sub p (map (fun v => (v, mk_axiom)) vars) = vars.
Proof.
  induction vars; simpl; sp.
  rw IHvars; sp.
Qed.

Lemma in_dom_sub_exists {p} :
  forall v sub,
    LIn v (@dom_sub p sub)
    -> {t : NTerm $ sub_find sub v = Some t}.
Proof.
  induction sub; simpl; sp; allsimpl; subst; boolvar.
  exists a; sp.
  exists a; sp.
  exists t; sp.
Qed.

Lemma in_dom_csub_exists {p} :
  forall v sub,
    LIn v (@dom_csub p sub)
    -> {t : NTerm $ sub_find (csub2sub sub) v = Some t # isprogram t}.
Proof.
  induction sub; simpl; sp; destruct a; allsimpl; subst; boolvar; sp.
  exists x; sp; rw @isprogram_eq; sp.
  exists x; sp; rw @isprogram_eq; sp.
  exists t; auto.
Qed.

Definition insub {p} sub var : bool :=
  match @sub_find p sub var with
    | Some _ => true
    | None => false
  end.

Lemma sub_find_some {p} :
  forall sub : @Substitution p,
  forall v : NVar,
  forall u : NTerm,
    sub_find sub v = Some u
    -> LIn (v, u) sub.
Proof.
  induction sub; simpl; sp.
  inversion H.
  remember (beq_var a0 v).
  destruct b.
  inversion H; subst.
  apply beq_var_eq in Heqb; subst.
  left; auto.
  apply IHsub in H; right; auto.
Qed.

Lemma sub_find_some_eq {p} :
  forall sub : @Substitution p,
  forall v : NVar,
  forall u t : NTerm,
    sub_find sub v = Some t
    -> sub_find sub v = Some u
    -> t = u.
Proof.
  induction sub; simpl; sp.
  inversion H.
  remember (beq_var a0 v).
  destruct b.
  inversion H; subst.
  inversion H0; subst.
  auto.
  apply IHsub with (t := t) in H0; auto.
Qed.

Lemma sub_find_app {p} :
  forall v sub1 sub2,
    @sub_find p (sub1 ++ sub2) v
    = match sub_find sub1 v with
        | Some t => Some t
        | None => sub_find sub2 v
      end.
Proof.
  induction sub1; simpl; sp.
  destruct (beq_var a0 v); auto.
Qed.

Lemma sub_find_snoc {p} :
  forall v sub x t,
    @sub_find p (snoc sub (x, t)) v
    = match sub_find sub v with
        | Some t => Some t
        | None => if beq_var x v then Some t else None
      end.
Proof.
  induction sub; simpl; sp; allsimpl.
  destruct (beq_var a0 v); auto.
Qed.

Lemma sub_find_some_app {p} :
  forall v t sub1 sub2,
    @sub_find p sub1 v = Some t
    -> sub_find (sub1 ++ sub2) v = Some t.
Proof.
  intros.
  rw @sub_find_app.
  rw H; auto.
Qed.

Lemma sub_find_none {p} :
  forall sub : @Substitution p,
  forall v : NVar,
  forall u : @NTerm p,
    sub_find sub v = None
    -> forall u, ! LIn (v, u) sub.
Proof.
  induction sub; simpl; sp; inj.
  rw <- beq_var_refl in H; sp.
  remember (beq_var a0 v).
  destruct b; sp.
  apply IHsub with (u0 := u0) in H; auto.
Qed.

Lemma sub_find_none2 {p} :
  forall sub v,
    @sub_find p sub v = None
    -> ! LIn v (dom_sub sub).
Proof.
  induction sub; simpl; sp; subst; allsimpl.
  rw <- beq_var_refl in H; inversion H.
  remember (beq_var a0 v).
  destruct b.
  inversion H.
  apply IHsub in H; auto.
Qed.

Lemma sub_find_none_iff {p} :
  forall sub v,
    @sub_find p sub v = None
    <=> ! LIn v (dom_sub sub).
Proof.
  induction sub; simpl; sp; subst; split; sp; allsimpl; subst.
  rw <- beq_var_refl in H; inversion H.
  remember (beq_var a0 v); destruct b.
  inversion H.
  rw IHsub in H; auto.
  remember (beq_var a0 v); destruct b.
  provefalse; apply H.
  apply beq_var_eq in Heqb; left; auto.
  symmetry in Heqb.
  apply beq_var_false_not_eq in Heqb.
  rw IHsub; intro.
  apply H; right; auto.
Qed.

(* computes the set of free variables occurring in the co-domain of sub *)
Fixpoint sub_free_vars {p} (sub : @Substitution p) : list NVar :=
  match sub with
  | nil => nil
  | (v, t) :: xs => free_vars t ++ sub_free_vars xs
  end.

Lemma in_sub_free_vars {p} :
  forall sub v,
    LIn v (@sub_free_vars p sub)
    -> {x : NVar $ {t : NTerm $
         LIn (x,t) sub # LIn v (free_vars t) }}.
Proof.
  induction sub; simpl; sp; allsimpl.
  allrw in_app_iff; sp.
  exists a0 a; sp.
  discover; sp.
  exists x t; sp.
Qed.

Lemma in_sub_free_vars_iff {p} :
  forall sub v,
    LIn v (@sub_free_vars p sub)
    <=> {x : NVar $ {t : NTerm $
         LIn (x,t) sub # LIn v (free_vars t)}}.
Proof.
  induction sub; simpl; sp.
  split; sp.
  rw in_app_iff.
  rw IHsub; split; sp; inj; sp.
  exists a0 a; sp.
  exists x t; sp.
  right; exists x t; sp.
Qed.

Lemma subset_free_vars_mem {p} :
  forall v t sub,
    LIn (v, t) sub
    -> subset (@free_vars p t) (sub_free_vars sub).
Proof.
  induction sub; simpl; sp; inj.
  apply subset_app_r; apply subset_refl.
  apply subset_app_l; auto.
Qed.

Lemma subset_sub_free_vars {p} :
  forall sub1 sub2,
    subset sub1 sub2
    -> subset (@sub_free_vars p sub1) (sub_free_vars sub2).
Proof.
  induction sub1; simpl; sp.
  destruct sub2.
  allapply subset_cons_nil; sp.
  destruct p.
  simpl.
  allrw cons_subset; allsimpl; sp; inj.
  rw app_subset; sp.
  apply subset_app_r; apply subset_refl.
  apply_in_hyp p; allsimpl; sp.
  rw app_subset; sp.
  apply subset_app_l.
  apply subset_free_vars_mem with (v := a0); auto.
  apply_in_hyp p; allsimpl; sp.
Qed.

Lemma sub_free_vars_isprogram {p} :
  forall sub,
    (forall v t, LIn (v, t) sub -> @isprogram p t)
    -> null (sub_free_vars sub).
Proof.
  induction sub; simpl; intros k; sp.
  rw null_app; sp.
  generalize (k a0 a); intro i.
  dest_imp i hyp.
  unfold isprogram, closed in i; sp.
  allrw; sp.
  apply IHsub; sp.
  apply k with (v := v); sp.
Qed.

Definition sub_mk_rename (var : NVar) (fvars : list NVar) : NVar :=
  if memvar var fvars
  then fresh_var fvars
  else var.

(** chose new variables if for bvars if they are in fvars.
    if new variables have to be chose, make sure that
    the new choices are disjoint from lva.

    need not choose a new var if it is in lva but not in fvars.
    This is to avoid renamings as much as possible
*)
Fixpoint sub_mk_renames2 {p} (bvars : list NVar) (fvars : list NVar)
          (lva: list NVar): (list NVar) * @Substitution p :=
  match bvars with
  | nil => (nil, nil)
  | v :: vs =>
     let (vars, sub) := sub_mk_renames2 vs fvars lva in
     if memvar v fvars
     then let u := fresh_var (vars ++ fvars ++ lva) in
          (u :: vars, (v, vterm u) :: sub)
     else (v :: vars, sub)
  end.

(* generates renamings for all the variables in bvars that also occur in fvars *)
Fixpoint sub_mk_renames {p} (bvars : list NVar) (fvars : list NVar) :
    (list NVar) * @Substitution p :=
  match bvars with
  | nil => (nil, nil)
  | v :: vs =>
     let (vars, sub) := sub_mk_renames vs fvars in
     if memvar v fvars
     then let u := fresh_var (vars ++ fvars) in
          (u :: vars, (v, vterm u) :: sub)
     else (v :: vars, sub)
  end.


Lemma sub_mk_renames_eta {p} :
  forall vs frees,
    @sub_mk_renames p vs frees
    = (fst (@sub_mk_renames p vs frees), snd (sub_mk_renames vs frees)).
Proof.
  induction vs; simpl; sp.
  rw IHvs; simpl.
  destruct (memvar a frees).
  simpl; auto.
  simpl; auto.
Qed.

Lemma sub_mk_renames2_eta {p} :
  forall vs frees lva,
    sub_mk_renames2 vs frees lva
    = (fst (@sub_mk_renames2 p vs frees lva), snd (@sub_mk_renames2 p vs frees lva)).
Proof.
  induction vs; simpl; sp.
  rw IHvs; simpl.
  destruct (memvar a frees).
  simpl; auto.
  simpl; auto.
Qed.

Lemma sub_mk_renames_snd_vterm {p} :
  forall bvars fvars v t,
    LIn (v,t) (snd (sub_mk_renames bvars fvars))
    -> {x : NVar $ t = @vterm p x}.
Proof.
  induction bvars; simpl; introv k; sp.
  rw @sub_mk_renames_eta in k; allsimpl.
  destruct (memvar a fvars); allsimpl; sp; inj.
  exists (fresh_var (fst (@sub_mk_renames p bvars fvars) ++ fvars)); auto.
  discover; sp.
  discover; sp.
Qed.

Lemma sub_mk_renames2_snd_vterm {p} :
  forall bvars fvars v t lva,
    LIn (v,t) (snd (sub_mk_renames2 bvars fvars lva))
    -> {x : NVar $ t = @vterm p x}.
Proof.
  induction bvars; simpl; introv k; sp.
  rw @sub_mk_renames2_eta in k; allsimpl.
  destruct (memvar a fvars); allsimpl; sp; inj.
  eexists; eauto.
  discover; sp.
  discover; sp.
Qed.

Lemma sub_mk_renames2_nil {p} :
  forall vs lva,
    @sub_mk_renames2 p vs [] lva = (vs, []).
Proof.
  induction vs; simpl; sp.
  rw IHvs. sp.
Qed.

Lemma sub_mk_renames_nil {p} :
  forall vs,
    @sub_mk_renames p vs [] = (vs, []).
Proof.
  induction vs; simpl; sp.
  rw @sub_mk_renames_eta.
  rw IHvs; simpl; auto.
Qed.

Lemma sub_mk_renames_length {p} :
  forall vs frees,
    length (fst (@sub_mk_renames p vs frees)) = length vs.
Proof.
  induction vs; simpl; sp.
  rw @sub_mk_renames_eta; simpl.
  destruct (memvar a frees); simpl; rw IHvs; auto.
Qed.

Lemma sub_mk_renames2_length {p} :
  forall vs frees lva,
    length (fst (@sub_mk_renames2 p vs frees lva)) = length vs.
Proof.
  induction vs; simpl; sp.

  rw @sub_mk_renames2_eta; simpl.
  destruct (memvar a frees); simpl; rw IHvs; auto.
Qed.

Lemma in_snd_sub_mk_renames {p} :
  forall v t bvars fvars,
    LIn (v, t) (snd (sub_mk_renames bvars fvars))
    ->
    (
      LIn v bvars
      #
      LIn v fvars
      #
      {x : NVar $ (t = @vterm p x # ! LIn x fvars)}
    ).
Proof.
  induction bvars; simpl; introv k; sp.

  - rw @sub_mk_renames_eta in k; allsimpl.
    remember (memvar a fvars); destruct b; allsimpl; sp; inj; sp;
    apply_in_hyp pp; sp.

  - rw @sub_mk_renames_eta in k; allsimpl.
    remember (memvar a fvars); destruct b; allsimpl; sp; inj; sp.
    symmetry in Heqb.
    rw fold_assert in Heqb.
    rw assert_memvar in Heqb; auto.
    apply_in_hyp pp; sp.
    apply_in_hyp pp; sp.

  - rw @sub_mk_renames_eta in k; allsimpl.
    remember (memvar a fvars); destruct b; allsimpl; sp; inj; sp.
    symmetry in Heqb.
    rw fold_assert in Heqb.
    rw assert_memvar in Heqb; auto.
    exists (fresh_var (fst (@sub_mk_renames p bvars fvars) ++ fvars)); sp.
    assert (! (LIn (fresh_var (fst (@sub_mk_renames p bvars fvars) ++ fvars))
                  (fst (@sub_mk_renames p bvars fvars) ++ fvars))) as nin
      by apply fresh_var_not_in.
    apply nin.
    rw in_app_iff; sp.
    apply_in_hyp pp; sp.
    apply_in_hyp pp; sp.
Qed.


Lemma sub_mk_renames_not_in {p} :
  forall l v vs,
    ! LIn v l
    -> @sub_mk_renames p l vs = (l, [])
    -> @sub_mk_renames p l (v :: vs) = (l, []).
Proof.
  induction l; simpl; sp.
  allrw not_over_or; repd.

  remember (memvar a vs); destruct b; symmetry in Heqb.
  rw fold_assert in Heqb.
  rw assert_memvar in Heqb; allsimpl; sp; subst.
  rw @sub_mk_renames_eta in H0; cpx.

  rw @sub_mk_renames_eta in H0; cpx.
  invs2.
  assert (@sub_mk_renames p l vs = (l, [])) as seq by (rw @sub_mk_renames_eta; allrw; sp).
  allrw; allsimpl; sp.

  rw not_of_assert in Heqb.
  rw assert_memvar in Heqb.

  remember (memvar a (v :: vs)); destruct b; symmetry in Heqb0; sp.
  rw fold_assert in Heqb0.
  rw assert_memvar in Heqb0; allsimpl; sp.
Qed.

Lemma sub_mk_renames2_not_in {p} :
  forall l v vs lva,
    ! LIn v l
    -> @sub_mk_renames2 p l vs lva= (l, [])
    -> @sub_mk_renames2 p l (v :: vs) lva = (l, []).
Proof.
  induction l; simpl; sp.
  allrw not_over_or; repd.

  remember (memvar a vs); destruct b; symmetry in Heqb.
  rw fold_assert in Heqb.
  rw assert_memvar in Heqb; allsimpl; sp; subst.
  rw @sub_mk_renames2_eta in H0; cpx.

  rw @sub_mk_renames2_eta in H0; cpx.
  invs2.
  assert (@sub_mk_renames2 p l vs lva= (l, [])) as seq by (rw @sub_mk_renames2_eta; allrw; sp).
  allrw; allsimpl; sp.

  rw not_of_assert in Heqb.
  rw assert_memvar in Heqb.

  remember (memvar a (v :: vs)); destruct b; symmetry in Heqb0; sp.
  rw fold_assert in Heqb0.
  rw assert_memvar in Heqb0; allsimpl; sp.
Qed.

Lemma sub_mk_renames_trivial_vars {p} :
  forall vars l,
    @sub_mk_renames p
      l
      (sub_free_vars
         (sub_filter (map (fun v => (v, @vterm p v)) vars) l))
    = (l, []).
Proof.
  induction vars; simpl; sp.
  rw @sub_mk_renames_nil; simpl; sp.
  remember (memvar a l); destruct b; symmetry in Heqb; auto; simpl.
  rw not_of_assert in Heqb.
  rw assert_memvar in Heqb.
  apply sub_mk_renames_not_in; auto.
Qed.

Lemma sub_mk_renames2_trivial_vars {p} :
  forall vars l lva,
    @sub_mk_renames2 p
      l
      (sub_free_vars
         (sub_filter (map (fun v => (v, @vterm p v)) vars) l)) lva
    = (l, []).
Proof.
  induction vars; simpl; sp.
  rw @sub_mk_renames2_nil; simpl; sp.
  remember (memvar a l); destruct b; symmetry in Heqb; auto; simpl.
  rw not_of_assert in Heqb.
  rw assert_memvar in Heqb.
  apply sub_mk_renames2_not_in; auto.
Qed.

Lemma sub_find_sub_filter {p} :
  forall sub vars n,
    LIn n vars -> sub_find (@sub_filter p sub vars) n = None.
Proof.
  induction sub; simpl; sp.
  remember (memvar a0 vars); destruct b; simpl; symmetry in Heqb.
  apply_in_hyp pp; sp.
  remember (beq_var a0 n); destruct b.
  apply beq_var_eq in Heqb0; subst.
  rw not_of_assert in Heqb.
  rw assert_memvar in Heqb; sp.
  apply_in_hyp pp; sp.
Qed.

(*
Fixpoint update_bvar_subst (bvs: list NVar) (sub: Substitution) : Substitution :=
      match bvs with
      | [] =>  sub
      | v::tv =>
          let sub'  := sub_filter sub [v] in
          let frees := sub_free_vars sub' in
          let u     := sub_mk_rename v frees in
          (v, vterm u):: (update_bvar_subst tv sub)
       end.
*)

(*
Fixpoint bvar_renamings_subst' (bvs: list NVar) (sub: Substitution)
  : Substitution * (list NVar) :=
  match bvs with
    | [] => (sub,[])
    | v::tv =>
        let sub'  := sub_filter sub [v] in
        let frees := sub_free_vars sub' in
        let u     := sub_mk_rename v frees in
        let r     := bvar_renamings_subst' tv sub in
          ((v, vterm u) :: (fst r), u :: (snd r))
  end.
*)

(** bvar_renamings_subst returns three things:
 * 1) a list of variables computed from vs such that the ones that
 *    also occur in the free variables of sub get renamed
 * 2) a renamings for the bound variables in vs that also occur in sub
 * 3) a subset of sub that does not clash with vs
 *)
Definition bvar_renamings_subst {p} (vs: list NVar) (bd : @NTerm p) (sub: @Substitution p)
  : (list NVar) * @Substitution p * @Substitution p :=
  let sub1       := sub_filter sub vs in
  let (vs',sub2) := sub_mk_renames2 vs (sub_free_vars sub1) (dom_sub sub1++(all_vars bd)) in
  (vs', sub2, sub1).

Definition disjoint_bv_sub {p} (nt : @NTerm p) (sub: @Substitution p) :=
  sub_range_sat sub (fun t => disjoint (free_vars t) (bound_vars nt)).

Theorem prog_sub_disjoint_bv_sub {p} :
  forall nt sub, @prog_sub p sub -> disjoint_bv_sub nt sub.
Proof. intros nt. apply sub_range_sat_implies.
  introv Hpr. invertsn Hpr.
  rw Hpr. introv Hin. inverts Hin.
Qed.


Definition disjoint_bvbt_sub {p} (bt : @BTerm p) (sub: @Substitution p) :=
  sub_range_sat sub (fun t => disjoint (free_vars t) (bound_vars_bterm bt)).

(* Eval simpl in (lsubst (mk_lam nvarx (vterm nvary)) [(nvarz,vterm nvarx)]). 
 This was a bug in lsubst. it will return \lambda y.y because
 the new variables were not disjoint from the fvars of the body
*)

(*
Lemma disjoint_bvbt_sub_ot : forall op lbt bt sub,
  LIn bt lbt 
  -> disjoint_bv_sub (oterm op lbt) sub
  -> disjoint_bvbt_sub bt sub.
AdCmitted.

Fixpoint lsubstd (t : NTerm) (sub : Substitution) (p: disjoint_bv_sub t sub): NTerm :=
  (*if nullb sub then t else*)
  match t with
  | vterm var =>
      match sub_find sub var with
      | Some t => t
      | None => t
      end
  | oterm op bts => let btsp := pairInProofs bts in
      let f:= (fun ppp => match ppp with 
                         | existT bt  pp => lsubst_btermc bt sub _ 
                            (disjoint_bvbt_sub_ot _ _ _ _ pp p)
                         end) in
                            
    oterm op (map f bts)
  end
 with lsubst_btermc (bt : BTerm) (sub : Substitution) (p:disjoint_bvbt_sub bt sub): BTerm :=
  match bt with
  | bterm lv nt =>
      bterm lv (lsubstc nt (sub_filter sub lv) _)
  end.
*)

(* end hide *)

(** % \noindent \\* %
    The following function is an auxilliary one that performs a
    [Substitution] on an [NTerm] assuming that its bound
    variables of are already disjoint from the free variables
    of the range of the [Substitution].
    
  *)
  (*if nullb sub then t else*)

Fixpoint lsubst_aux {p} (nt : @NTerm p) (sub : Substitution) : NTerm :=
  match nt with
  | vterm var =>
      match sub_find sub var with
      | Some t => t
      | None => nt
      end
  | oterm op bts => oterm op (map (fun t => lsubst_bterm_aux t sub) bts)
  end
 with lsubst_bterm_aux {p} (bt : BTerm) (sub : Substitution) : BTerm :=
  match bt with
  | bterm lv nt => bterm lv (lsubst_aux nt (sub_filter sub lv))
  end.




(** % \noindent \\* %
  To define the actual substitution function, we just have to pre-process [t]
  such that its bound variables have been renamed to avoid
  the free variables of the range of [sub].
  Here is a function that does that.
*)


Fixpoint change_bvars_alpha {p} (lv : list NVar) (t : @NTerm p) :=
  match t with
    | vterm v => vterm v
    | oterm o lbt => oterm o (map (change_bvars_alphabt lv) lbt)
  end
with change_bvars_alphabt {p} lv bt:=
       match bt with
         | bterm blv bnt =>
           let bnt' := change_bvars_alpha lv bnt in
           let lvn  := fresh_distinct_vars (length blv) (lv++(all_vars bnt')) in
           bterm lvn (lsubst_aux bnt' (var_ren blv lvn))
       end.


(** % \noindent \\* %
  When we define alpha equality in the next section, we prove that
[change_bvars_alpha] returns a term which is alpha equal to the input.
Finally, here is the function that safely perfoms
  a [Substitution] on an [NTerm].

*)
Definition lsubst {p} (t : @NTerm p) (sub : Substitution) : NTerm :=
  let sfr := flat_map free_vars (range sub) in
    if dec_disjointv (bound_vars t) sfr
    then lsubst_aux t sub
    else lsubst_aux (change_bvars_alpha  sfr t) sub.

(** %\noindent% The following definition will be useful while
    defining the computation system.

*)

Definition apply_bterm {p} (bt : @BTerm p) (lnt: list NTerm) : NTerm :=
  lsubst (get_nt bt) (combine (get_vars bt) lnt).

(** %\noindent \\*% The formalization of Nuprl requires many lemmas about [lsubst].
    Because [lsubst] often renames bound variables, we
    need alpha equality to state many useful properties of substitution.
    We will first define alpha equality and then list some useful properties
    that we proved about [lsubst].
 *)
(* begin hide *)

Lemma lsubst_lsubst_aux {p} :
  forall t sub, disjoint (bound_vars t) (flat_map free_vars (@range p sub))
  -> lsubst t sub = lsubst_aux t sub.
Proof.
  introv Hdis. unfold lsubst. cases_if;sp.
Qed.


Lemma bvar_renamings_subst_trivial_vars {p} :
  forall l nt vars,
    bvar_renamings_subst l nt (map (fun v => (v, vterm v)) vars)
    = (l, [], sub_filter (map (fun v => (v, @vterm p v)) vars) l).
Proof.
  intros.
  unfold bvar_renamings_subst.
  rw @sub_mk_renames2_trivial_vars.
  auto.
Qed.

Lemma bvar_renamings_subst_eta' {p} :
  forall vs sub nt,
    {vs' : list NVar & {ren : Substitution & {sub' : @Substitution p &
      bvar_renamings_subst vs nt sub = (vs', ren, sub') }}}.
Proof.
  intros.
  unfold bvar_renamings_subst.
  rw @sub_mk_renames2_eta; simpl.
  eexists; eauto.
Qed.

Lemma bvar_renamings_subst_eta {p} :
  forall vs sub nt,
      @bvar_renamings_subst p vs nt sub
      = (fst (fst (bvar_renamings_subst vs nt sub)),
         snd (fst (bvar_renamings_subst vs nt sub)),
         snd (bvar_renamings_subst vs nt sub)).
Proof.
  intros.
  unfold bvar_renamings_subst.
  rw @sub_mk_renames2_eta; simpl.
  auto.
Qed.

Lemma bvar_renamings_subst_length {p} :
  forall l sub nt,
    length (fst (fst (@bvar_renamings_subst p l nt sub))) = length l.
Proof.
  intros; unfold bvar_renamings_subst.
  rw @sub_mk_renames2_eta; simpl.
  rw @sub_mk_renames2_length; auto.
Qed.

Lemma bvar_renamings_subst_nil {p} :
  forall l nt, @bvar_renamings_subst p l nt [] = (l, [], []).
Proof.
  intros; unfold bvar_renamings_subst; simpl.
  rw @sub_mk_renames2_eta; simpl.
  rw @sub_mk_renames2_nil; auto.
Qed.

Lemma bvar_renamings_subst_isprogram {p} :
  forall vars sub nt,
    (forall v t, LIn (v, t) sub -> @isprogram p t)
    -> bvar_renamings_subst vars nt sub = (vars, [], sub_filter sub vars).
Proof.
  intros.
  unfold bvar_renamings_subst.
  rw @sub_mk_renames2_eta; simpl.
  allapply @sub_free_vars_isprogram.
  assert (null (sub_free_vars (sub_filter sub vars)))
    by (assert (subset (sub_free_vars (sub_filter sub vars)) (sub_free_vars sub))
         by (apply subset_sub_free_vars; apply sub_filter_subset);
        apply null_subset with (l2 := sub_free_vars sub); sp).
  allrw null_iff_nil.
  allrw. simpl_vlist.
  rw @sub_mk_renames2_nil; simpl; auto.
Qed.

Fixpoint lsubst_vs {p} (vars : list NVar) (t : @NTerm p) (sub : Substitution) : NTerm :=
  (*if nullb sub then t else*)
  match t with
  | vterm var =>
      match sub_find sub var with
      | Some t => t
      | None => t
      end
  | oterm op bts => oterm op (map (fun t => lsubst_vs_bterm vars t sub) bts)
  end
 with lsubst_vs_bterm {p} (vars : list NVar) (bt : BTerm) (sub : Substitution) : BTerm :=
  match bt with
  | bterm lv nt =>
    let (x,s) := bvar_renamings_subst lv nt sub in
    let (vs,ren) := x in
      bterm vs (lsubst_vs (vars ++ vs) nt (ren ++ s))
  end.

(*
Lemma isprogram_lsubst_vars_implies :
  forall t sub vars,
    isprogram (lsubst_vs vars t sub)
    -> forall v,
         LIn v (free_vars t)
         -> ! LIn v vars
         -> exists u, sub_find sub v = Some u # isprogram u.
Proof.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    sp; subst.
    remember (sub_find sub v); destruct o; symmetry in Heqo.
    exists n; sp.
    rw isprogram_vterm in H; sp.

  - Case "oterm".
    rw in_flat_map in H1; sp.
    destruct x.
    simpl in H3.
    rw in_remove_nvars in H3; sp.
    apply H with (nt := n) (lv := l) (vars := vars ++ l); auto.
    unfold isprogram, closed in H0; sp; allsimpl.
    rw flat_map_empty in H0.
    inversion H5; subst.
    rw map_map in H9.
    unfold compose in H9.

    generalize (H0 (lsubst_vs_bterm vars (bterm l n) sub)).
    generalize (H8 (lsubst_vs_bterm vars (bterm l n) sub)).
    simpl.
    rw bvar_renamings_subst_eta.
    rw in_map_iff.
    sp.

    assert (exists x,
              lsubst_vs_bterm vars x sub =
              bterm (fst (fst (bvar_renamings_subst l sub)))
                    (lsubst_vs (vars ++ fst (fst (bvar_renamings_subst l sub))) n
                               (snd (fst (bvar_renamings_subst l sub)) ++
                                    snd (bvar_renamings_subst l sub))) #
              LIn x lbt) by
        (exists (bterm l n); simpl; rw bvar_renamings_subst_eta; simpl; auto).

    applydup H6 in H10.
    applydup H7 in H10.
    allsimpl.

    unfold isprogram, closed.
Abort.
*)


Definition csubst {p} (t : @NTerm p) (sub : CSubstitution) :=
  lsubst t (csub2sub sub).

Lemma fold_csubst {p} :
  forall t sub, lsubst t (@csub2sub p sub) = csubst t sub.
Proof.
  sp.
Qed.

Lemma csubst_mk_axiom {p} :
  forall sub, @csubst p mk_axiom sub = mk_axiom.
Proof.
  sp.
Qed.

Lemma csubst_mk_uni {p} :
  forall i sub, @csubst p (mk_uni i) sub = mk_uni i.
Proof.
  sp.
Qed.

Lemma csubst_mk_base {p} :
  forall sub, @csubst p mk_base sub = mk_base.
Proof.
  sp.
Qed.

Lemma lsubst_aux_nil {p} :
  forall t, @lsubst_aux p t [] = t.
Proof.
  nterm_ind t Case; simpl; auto.
  assert (map (fun t : BTerm => lsubst_bterm_aux t []) lbt = lbt);
  try (rw H0; auto).
  induction lbt; simpl; auto.
  rw IHlbt; auto.
  destruct a; simpl.
    f_equal; sp.
    f_equal; sp.
    eapply H; eauto.
    left; auto.

    intros. eapply H; eauto.
 right;sp.
 eauto.
Qed.


Lemma lsubst_nil {p} :
  forall t, @lsubst p t [] = t.
Proof.
  intros. unfold lsubst. simpl. cases_if.
  - apply lsubst_aux_nil.
  - disjoint_reasoning.
Qed.



Hint Rewrite @lsubst_nil.

Lemma csubst_nil {p} :
  forall t, @csubst p t [] = t.
Proof.
  unfold csubst; simpl; sp.
  rw @lsubst_nil; sp.
Qed.

Hint Rewrite @csubst_nil.

Lemma lsubst_aux_trivial {p} :
  forall t sub,
    (forall v u, LIn (v, u) sub -> @isprogram p u # ! LIn v (free_vars t))
    -> lsubst_aux t sub = t.
Proof.
  unfold lsubst.
  nterm_ind t as [|op lbt ind]  Case; simpl; introv imp; auto.

  - Case "vterm".
    allunfold @isprogram; allunfold @closed; sp.
    remember (sub_find sub n); destruct o; symmetry in Heqo; auto.
    apply sub_find_some in Heqo.
    apply_in_hyp pp; sp.
    allrw not_over_or; sp.

  - Case "oterm".
    assert (map (fun t : BTerm => lsubst_bterm_aux t sub) lbt = lbt) as eq;
    try (rw eq; auto).
    induction lbt; simpl; auto.
    rw IHlbt; sp.
    + destruct a; simpl.
      f_equal. f_equal.
      rewrite ind with (lv := l); sp.
      allrw @in_sub_filter; sp.
      apply_in_hyp pp; sp.
      allrw @in_sub_filter; sp.
      apply_in_hyp pp; sp; allsimpl.
      allrw in_app_iff.
      allrw not_over_or; sp.
      allrw in_remove_nvars; sp.
    + rewrite ind with (lv := lv); sp.
    + apply_in_hyp pp; sp.
    + apply_in_hyp pp; sp; allsimpl.
      allrw in_app_iff.
      allrw not_over_or; sp.
Qed.

Lemma prog_sub_flatmap_range {p} : forall sub, @prog_sub p sub
    -> flat_map free_vars (range sub) =[].
Proof.
  unfold prog_sub, isprogram,closed . introv Hps. apply flat_map_empty. cpx.
  introv Hin. rw in_map_iff in Hin. exrepnd. subst.
  simpl.
  apply Hps in Hin1. cpx.
Qed.


Theorem dom_range_is_split_snd {p} :
  forall sub, @range p sub = snd (split sub).
Proof.
  induction sub; auto. allsimpl.
  destruct (split sub) as [lv lnt].
  destruct (a) as [v nt].
  allsimpl. f_equal. auto.
Qed.

Theorem dom_range_combine {p} :
  forall lv lnt,
    length lv = length lnt
    -> @range p (combine lv lnt) = lnt.
Proof.
  intros. rw @dom_range_is_split_snd.
  rewrite combine_split; auto.
Qed.

Lemma sub_eta {p} : forall sub,
  sub = combine (@dom_sub p sub) (range sub).
Proof.
  induction sub as [| (v,t) Hind]; auto;simpl;congruence.
Qed.

Lemma sub_eta_length {p} : forall sub,
  length (@dom_sub p sub) = length (range sub).
Proof.
  induction sub as [| (v,t) Hind]; auto;simpl;congruence.
Qed.

Lemma in_sub_eta {p} : forall sub v t,
  LIn (v,t) sub -> (LIn v (@dom_sub p sub)) # (LIn t (range sub)).
Proof.
  introns HH.
  pose proof (sub_eta sub) as XX.
  rw XX in HH.
  apply in_combine in HH.
  trivial.
Qed.

Lemma disjoint_sub_as_flat_map {p} :
  forall (f: NTerm -> (list NVar)) sub lvd,
    (forall (v : NVar) (u : @NTerm p),
       LIn (v, u) sub -> disjoint (f u) lvd)  
      <=> disjoint (flat_map f (range sub)) lvd.
Proof.
  introv. sp_iff Case.
  Case "->".
  - introv Hin. apply disjoint_flat_map_l.
    intros nt Hinr. pose proof (sub_eta_length sub) as XXX.
    apply combine_in_right with (l1:=dom_sub sub) in Hinr;[| omega];[].
    exrepnd. rewrite <- sub_eta in Hinr0.
    apply Hin in Hinr0. sp.
  - introv Hdis. introv Hin. apply in_sub_eta in Hin. repnd.
    rw disjoint_flat_map_l in Hdis.
    apply Hdis in Hin. sp.
Qed.

Ltac false_disjoint :=
match goal with
| [ H: !( disjoint  _ _) |- _] => provefalse; apply H; clear H; disjoint_reasoningv
end.

Lemma flat_map_free_var_vterm {p} :
  forall lv, flat_map free_vars (map (@vterm p) lv)=lv.
Proof.
  induction lv;sp;simpl;f_equal;sp.
Qed.

Lemma flat_map_bound_var_vterm {p} :
  forall lv, flat_map bound_vars (map (@vterm p) lv)=[].
Proof.
  induction lv;sp;simpl;f_equal;sp.
Qed.

Lemma range_var_ren {p} : forall lvi lvo,
  length lvi=length lvo 
  -> range (var_ren lvi lvo) = map (@vterm p) lvo.
Proof.
  induction lvi as [|? ? Hind]; introv Hlen; allsimpl; destruct lvo; inverts Hlen;sp;[];simpl.
  f_equal. apply Hind; sp.
Qed.

Lemma flat_map_free_var_vars_range {p} : forall lvi lvo, 
  length lvi=length lvo 
  -> flat_map free_vars (range (@var_ren p lvi lvo)) = lvo.
Proof.
  intros. rw @range_var_ren;sp. apply  flat_map_free_var_vterm.
Qed.


Lemma flat_map_bound_var_vars_range {p} : forall lvi lvo, 
  length lvi=length lvo 
  -> flat_map bound_vars (range (@var_ren p lvi lvo)) = [].
Proof.  intros. rw @range_var_ren;sp. apply  flat_map_bound_var_vterm.
Qed.

Theorem dom_sub_is_split_snd {p} :
  forall sub, @dom_sub p sub = fst (split sub).
Proof.
 induction sub; auto. allsimpl. 
 destruct (split sub) as [lv lnt].
 destruct (a) as [v nt].
 allsimpl. f_equal. auto. 
Qed.

Theorem dom_sub_combine {p} :
  forall lv lnt,
    length lv = length lnt
    -> @dom_sub p (combine lv lnt) = lv.
Proof.
  intros.
  rw @dom_sub_is_split_snd.
  revert lnt H; induction lv; sp; simpl; destruct lnt; allsimpl; sp; try omega.
  rw split_eta; simpl; allrw; sp; omega.
Qed.

Theorem dom_sub_combine_le {p} :
  forall lv lnt,
    length lv <= length lnt
    -> @dom_sub p (combine lv lnt) = lv.
Proof.
  intros.
  rw @dom_sub_is_split_snd.
  revert lnt H; induction lv; sp; simpl; destruct lnt; allsimpl; sp; try omega.
  rw split_eta; simpl; allrw; sp; omega.
Qed.

Ltac simpl_sub :=
(match goal with
| [ H : context[dom_sub (combine _ _)] |- _] => rewrite dom_sub_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[dom_sub (combine _ _)] ] => rewrite dom_sub_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (combine _ _)] |- _] => rewrite dom_range_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[range (combine _ _)] ] => rewrite dom_range_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[range (var_ren _ _)] ] => unfold var_ren
| [ H : context[dom_sub (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[dom_sub (var_ren _ _)] ] => unfold var_ren
| [ H : context[flat_map free_vars (map vterm _)] |- _] => rewrite flat_map_free_var_vterm in H
| [ |-  context[flat_map free_vars (map vterm _)] ] => rewrite flat_map_free_var_vterm
| [ H : context[flat_map bound_vars (map vterm _)] |- _] => rewrite flat_map_bound_var_vterm in H
| [ |-  context[flat_map bound_vars (map vterm _)] ] => rewrite flat_map_bound_var_vterm
| [ H : isprogram _ |- _ ] => allrewrite (fst (H))
end).

Tactic Notation  "spcl" := spc;simpl_list.
Tactic Notation  "spcls" := repeat(simpl_list);sp;repeat(simpl_sub).

Lemma prog_sub_csub2sub {p} :
  forall sub, prog_sub (@csub2sub p sub).
Proof.
  introv hn; allapply @in_csub2sub; sp.
Qed.
Hint Immediate prog_sub_csub2sub.

Lemma wf_sub_csub2sub {p} :
  forall sub, wf_sub (@csub2sub p sub).
Proof.
  introv hn; allapply @in_csub2sub; sp.
  destruct hn; auto.
Qed.
Hint Immediate wf_sub_csub2sub.

Lemma prog_sub_implies_wf_sub {p} :
  forall sub, @prog_sub p sub -> wf_sub sub.
Proof.
  introv psub.
  introv k.
  apply psub in k.
  destruct k; auto.
Qed.

Lemma prog_sub_implies_wf {p} :
  forall sub, @prog_sub p sub -> wf_sub sub.
Proof.
  exact prog_sub_implies_wf_sub.
Qed.

Lemma prog_sub_cons {p} :
  forall sub v t,
    @prog_sub p ((v,t) :: sub) <=> (isprogram t # prog_sub sub).
Proof.
  introv.
  unfold prog_sub, sub_range_sat; simpl; split; intro k; sp; cpx; discover; sp.

  apply k with (v0 := v); sp.
  apply k with (v0 := v0); sp.
Qed.

Lemma in_range_iff {p} :
  forall (t : @NTerm p) (sub : Substitution),
    LIn t (range sub) <=> {v : NVar $ LIn (v, t) sub}.
Proof.
  induction sub; simpl; split; intro k; sp; allsimpl; subst; discover; sp; cpx.
  exists a0; sp.
  exists v; sp.
  right; allrw; exists v; sp.
Qed.

Lemma prog_sub_eq {p} :
  forall sub,
    (forall t, LIn t (@range p sub) -> isprogram t)
      <=> prog_sub sub.
Proof.
  induction sub; simpl; split; intro k; introv; sp; subst; allsimpl; sp; cpx.

  apply k; right; rw @in_range_iff; exists v; sp.

  allrw @prog_sub_cons; sp.

  allrw @prog_sub_cons; sp; discover; sp.
Qed.

Lemma prog_sub_exists_csub {p} :
  forall sub, @prog_sub p sub -> {s : CSub & csub2sub s = sub}.
Proof.
  induction sub; simpl.

  - exists ([] : @CSub p); sp.

  - intro ps.
    destruct a.
    rw @prog_sub_cons in ps; repnd.
    apply IHsub in ps; exrepnd.
    exists ((n,mk_cterm n0 ps0) :: s).
    simpl; rw ps1; sp.
Qed.


Definition hide_csub2sub {p} sub := @csub2sub p sub.

Ltac change_to_lsubst_aux4 :=
  unfold lsubst;
  allunfold disjoint_bv_sub;
  (repeat match goal with
            | [ |- context [csub2sub ?sub] ] =>
              let name := fresh "ps_csub2sub" in
              pose proof (prog_sub_csub2sub sub) as name;
            fold (hide_csub2sub sub)
          end);
  allunfold hide_csub2sub;
  allunfold prog_sub;
  allunfold sub_range_sat;
  (repeat match goal with
            | [ H:(forall _ _, LIn (_, _) _ -> isprogram _) |- _ ] =>
              progress(rw (prog_sub_flatmap_range _ H))
            | [ H:( forall _ _, LIn (_, _) _
                                -> disjoint (free_vars _) (bound_vars _)) |- _ ] =>
              apply disjoint_sub_as_flat_map in H;apply disjoint_sym in H
          end);
  repeat(cases_if;clears_last; [|sp;disjoint_reasoningv;spcls;try(false_disjoint)]).


Lemma lsubst_trivial {p} :
  forall t sub,
    (forall v u, LIn (v, u) sub -> @isprogram p u # ! LIn v (free_vars t))
    -> lsubst t sub = t.
Proof.
  introv Hpr. assert (prog_sub sub). introv Hin. apply Hpr in Hin;sp.
  change_to_lsubst_aux4.
  apply lsubst_aux_trivial;sp.
Qed.

Lemma lsubst_cterm {p} :
  forall t s,
    lsubst (get_cterm t) (@csub2sub p s) = get_cterm t.
Proof.
  introv.
  apply lsubst_trivial; introv i.
  rw @free_vars_cterm; simpl; sp.
  apply in_csub2sub in i; sp.
Qed.


(* This is not true because lsubst might renames some bound variables of t
that occur in the free variables of sub.

Lemma lsubst_trivial1 :
  forall t sub,
    (forall v u, LIn (v, u) sub -> ! LIn v (free_vars t))
    -> lsubst t sub = t.
Proof.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    allunfold isprogram; allunfold closed; sp.
    remember (sub_find sub n); destruct o; symmetry in Heqo; auto.
    apply sub_find_some in Heqo.
    apply H in Heqo; sp.
    provefalse; apply Heqo; left; auto.

  - Case "oterm".
    assert (map (fun t : BTerm => lsubst_bterm t sub) lbt = lbt);
    try (rw H1; auto).
    induction lbt; simpl; auto.
    rw IHlbt; sp.

    + destruct a; simpl.
      assert (bterm (snd (bvar_renamings_subst l sub))
                    (lsubst n (fst (bvar_renamings_subst l sub)))
              = bterm l n).

    + rw H with (lv := lv); sp; simpl.
      right; auto.

    + apply H0 in H1; sp.
      simpl in H1; rw in_app_iff in H1.
      apply H1; right; auto.
Qed.
*)

Lemma lsubst_aux_trivial2 {p} :
  forall t sub,
    (forall v u, LIn (v, u) sub -> @isprogram p u)
    -> isprogram t
    -> lsubst_aux t sub = t.
Proof.
  introv k isp; apply lsubst_aux_trivial; introv ins.
  apply_in_hyp pp.
  inversion isp as [c w].
  dands; try (complete sp).
  intro ivt.
  rw c in ivt; sp.
Qed.

Lemma lsubst_trivial2 {p} :
  forall t sub,
    (forall v u, LIn (v, u) sub -> @isprogram p u)
    -> isprogram t
    -> lsubst t sub = t.
Proof.
  intros. change_to_lsubst_aux4.
  apply lsubst_aux_trivial2;sp.
Qed.


Lemma csubst_get_cterm {p} :
  forall t sub,
    @csubst p (get_cterm t) sub = get_cterm t.
Proof.
  unfold csubst; sp.
  rw @lsubst_trivial2; sp.
  allapply @in_csub2sub; sp.
Qed.

Theorem disjoint_lbt_bt2 {p} : forall vs lbt lv nt,
    disjoint vs (flat_map (@bound_vars_bterm p) lbt)
    -> LIn (bterm lv nt) lbt
    -> disjoint vs lv # disjoint vs (bound_vars nt).
Proof. introv Hink1 Hin. apply disjoint_sym in Hink1;rw disjoint_flat_map_l in Hink1.
   apply Hink1 in Hin. simpl in Hin. rw disjoint_app_l in Hin. repnd.
   split; apply disjoint_sym; trivial.
Qed.


Ltac disjoint_flat := allunfold disjoint_bv_sub; allunfold sub_range_sat; allsimpl;
  repeat match goal with
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint (flat_map ?f (range ?sub)) ?l)  |- disjoint (?f ?t) ?l ] =>
  exact ((tiff_snd (disjoint_sub_as_flat_map _ _ _) H2 _ _ H))
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint ?l (flat_map ?f (range ?sub)))  |- disjoint (?f ?t) ?l ] =>
  exact ((tiff_snd (disjoint_sub_as_flat_map _ _ _) 
  (disjoint_sym_impl _ _ _ H2) _ _ H))
|[ H: (LIn (bterm ?lv _) ?lbt), H2 : (disjoint (flat_map free_vars (range ?sub)) 
      (flat_map bound_vars_bterm ?lbt))  |- _ ] => 
    pose proof (disjoint_lbt_bt2 _ _ _ _ H2 H); apply hide_hyp in H2
|[ H: (LIn (bterm ?lv _) ?lbt), H2 : (disjoint (flat_map bound_vars_bterm ?lbt)
      (flat_map free_vars (range ?sub)))  |- _ ] => 
      pose proof (disjoint_lbt_bt2 _ _ _ _ (disjoint_sym_impl _ _ _ H2) H);
      apply hide_hyp in H
| [ H:( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) |- _ ] =>
      apply disjoint_sub_as_flat_map in H
| [ |- ( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) ] =>
      apply disjoint_sub_as_flat_map
end ; allrw <- hide_hyp.


Theorem disjoint_sub_filter_r_flatmap {p} :
  forall {T:Type} lvi lnt lvis lnts lv 
  (ld: list T) (f:NTerm-> list T),
   @sub_filter p (combine lvi lnt) lv = combine lvis lnts
   -> length lvi =length lnt
   -> length lvis =length lnts
   -> disjoint (flat_map f lnt) ld
   -> disjoint (flat_map f lnts) ld.
Proof.
  introv Hsf Hlen Hle1n Hdis. introv Hin Hc.
  apply lin_flat_map in Hin. exrepnd.
  apply combine_in_right with (l1:=lvis) in Hin1; auto; [| omega];[].
  rename Hin1 into Hinc. exrepnd. rw <- Hsf in Hinc0.
  apply in_sub_filter in Hinc0. repnd. apply in_combine in Hinc1. repnd.
  assert({x : NTerm $ LIn x lnt # LIn t (f x)}) as XX by(eexists; eauto).
  allrw <- lin_flat_map.
  apply Hdis in XX. sp.
Qed.

Theorem disjoint_sub_filter_r_flatmap2 {p} : forall {T:Type} sub lv
  (ld: list T) (f:NTerm-> list T),
   disjoint (flat_map f (@range p sub)) ld
   -> disjoint (flat_map f (range (sub_filter sub lv))) ld.
Proof.
  introv.   pose proof (sub_eta (sub_filter sub lv)) as YY.
  pose proof (sub_eta sub) as XX.
  rewrite XX  in YY at 1.
  pose proof (sub_eta_length sub).
  pose proof (sub_eta_length (sub_filter sub lv)).
  eapply disjoint_sub_filter_r_flatmap; eauto.
Qed.


Ltac disjoint_flat_sf :=
repeat match goal with
| [|- disjoint (flat_map _ (range (sub_filter _ _))) _] =>
    apply disjoint_sub_filter_r_flatmap2
| [|- disjoint _ (flat_map _ (range (sub_filter _ _)))] =>
    apply disjoint_sym; apply disjoint_sub_filter_r_flatmap2
end.

Lemma simple_lsubst_aux_app {p} :
  forall t sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> isprogram u)
    -> (forall v u, LIn (v, u) sub2 -> @isprogram p u)
    -> lsubst_aux (lsubst_aux t sub1) sub2 = lsubst_aux t (sub1 ++ sub2).
Proof.
  nterm_ind t Case; simpl; intros; auto.

  - Case "vterm".
    remember (sub_find sub1 n); destruct o; symmetry in Heqo; simpl; sp.
    + rewrite sub_find_some_app with (t := n0); sp.
      apply sub_find_some in Heqo.
      apply_in_hyp pp.
      rw @lsubst_aux_trivial2; sp.

    + rw @sub_find_app.
      rw Heqo; auto.

  - Case "oterm". f_equal.
    induction lbt; simpl; auto.
    rw IHlbt; sp;
    try (rewrite H with (lv := lv); sp; simpl; sp).
    f_equal.
    destruct a; simpl.
    rewrite H with (lv := l); sp.
    rw @sub_filter_app; auto.
    allrw @in_sub_filter; sp.
    apply_in_hyp pp; sp.
    allrw @in_sub_filter; sp.
    apply_in_hyp pp; sp.
Defined.


Lemma simple_lsubst_app {p} :
  forall t sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> isprogram u)
    -> (forall v u, LIn (v, u) sub2 -> @isprogram p u)
    -> lsubst (lsubst t sub1) sub2 = lsubst t (sub1 ++ sub2).
Proof.
  intros. assert(prog_sub (sub1++sub2)) by (apply sub_app_sat;sp).
  change_to_lsubst_aux4.
  apply simple_lsubst_aux_app; sp.
Qed.




Lemma csubst_app {p} :
  forall t sub1 sub2,
    csubst (@csubst p t sub1) sub2 = csubst t (sub1 ++ sub2).
Proof.
  unfold csubst; sp.
  rw @simple_lsubst_app; sp; try (allapply @in_csub2sub; sp).
  rw @csub2sub_app; sp.
Defined.

(* This is not true because lsubst might renames some bound variables of t
that occur in the free variables of sub.
Lemma lsubst_isprogram :
  forall t sub,
    isprogram t
    -> lsubst t sub = t.
Proof.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    rw isprogram_vterm in H; sp.

  - Case "oterm".
Qed.
*)

Definition subst_aux {p} (t : @NTerm p) (v : NVar) (u : NTerm) : NTerm :=
  lsubst_aux t [(v,u)].

Definition subst {p} (t : @NTerm p) (v : NVar) (u : NTerm) : NTerm :=
  lsubst t [(v,u)].

Lemma axiom_sub_as_csubst {p} :
  forall t x,
    @subst p t x mk_axiom = csubst t [(x,mkc_axiom)].
Proof.
  sp.
Qed.

(* in a separate commit, we might want to make everything compatible with
Notation apply_bterm  (bt :BTerm) (lnt: list NTerm) : NTerm :=
  match bt with
  | bterm lv nt => lsubst nt (combine lv lnt)
  end.
*)


Lemma apply_bterm_nobnd {p} :
  forall t,
    apply_bterm (@nobnd p t) [] = t.
Proof.
  unfold apply_bterm, get_nt, nobnd; simpl; sp.
  rw @lsubst_nil; auto.
Qed.


Lemma num_bvars_bterm {p} :
  forall bt sub,
    num_bvars (@lsubst_bterm_aux p bt sub) = num_bvars bt.
Proof.
  destruct bt; unfold num_bvars; simpl; sp.
Qed.

Lemma map_num_bvars_bterms {p} :
  forall bts sub,
    map num_bvars (map (fun t : @BTerm p => lsubst_bterm_aux t sub) bts) =
    map num_bvars bts.
Proof.
  induction bts; simpl; sp.
  rw @num_bvars_bterm; rw IHbts; auto.
Qed.

Lemma remove_nvars_comb {p} :
  forall sub l vars,
    remove_nvars (l ++ dom_sub (@sub_filter p sub l)) vars
    = remove_nvars (l ++ dom_sub sub) vars.
Proof.
  induction sub; simpl; sp.
  remember (memvar a0 l); destruct b; symmetry in Heqb; simpl.
  rw fold_assert in Heqb.
  rw assert_memvar in Heqb.
  rw IHsub.
  rw <- remove_nvars_dup; auto.
  repeat (rw remove_nvars_move).
  repeat (rw remove_nvars_cons).
  rw IHsub; auto.
Qed.

Lemma isprogram_lsubst_aux1 {p} :
  forall t : NTerm,
  forall sub : @Substitution p,
    nt_wf t
    -> (forall v u, LIn (v, u) sub -> isprogram u)
    -> nt_wf (lsubst_aux t sub)
       # free_vars (lsubst_aux t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof.
  nterm_ind t as [|o lbt ind] Case; simpl; introv wf k; auto.

  - Case "vterm".
    remember (sub_find sub n); destruct o; symmetry in Heqo; simpl.
    + apply sub_find_some in Heqo.
      apply_in_hyp pp.
      unfold isprogram, closed in pp; sp.
      allrw.
      symmetry; rw <- null_iff_nil.
      rw null_remove_nvars; simpl; sp; subst.
      apply in_dom_sub in Heqo; sp.
    + sp.
      apply sub_find_none2 in Heqo.
      symmetry.
      rw <- remove_nvars_unchanged.
      unfold disjoint; simpl; sp; subst; auto.

  - Case "oterm".
    inversion wf; subst; sp.
    + constructor.
      introv i.
      allrw in_map_iff; exrepnd; subst.
      destruct a; simpl.
      constructor.
      apply ind with (sub := sub_filter sub l) in i1; sp.
      apply_in_hyp pp.
      inversion pp; subst; auto.
      apply k with (v := v).
      assert (subset (sub_filter sub l) sub) as s by apply sub_filter_subset.
      unfold subset in s.
      apply_in_hyp pp; sp.
      allrw <-.
      apply map_num_bvars_bterms.

    + auto.
      rw flat_map_map; unfold compose.
      rw remove_nvars_flat_map; unfold compose.
      apply eq_flat_maps; introv i.
      destruct x; simpl.
      apply_in_hyp pp.
      inversion pp as [vs t w]; subst.

      apply ind with (sub := sub_filter sub l) in i; sp.

      allrw.
      rw remove_nvars_app_l.
      rw remove_nvars_comm.
      rw remove_nvars_app_l.
      rw @remove_nvars_comb; auto.

      apply k with (v := v).
      assert (subset (sub_filter sub l) sub) as s by apply sub_filter_subset.
      unfold subset in s.
      discover; sp.
Qed.

Lemma isprogram_lsubst1 {p} :
  forall t : NTerm,
  forall sub : @Substitution p,
    nt_wf t
    -> (forall v u, LIn (v, u) sub -> isprogram u)
    -> nt_wf (lsubst t sub)
       # free_vars (lsubst t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof.
  intros. change_to_lsubst_aux4.
  apply isprogram_lsubst_aux1;sp.
Qed.


Lemma isprogram_lsubst_nt_wf {p} :
  forall t : WTerm,
  forall sub : @CSubstitution p,
    nt_wf (csubst (get_wterm t) sub).
Proof.
  sp; destruct t; allsimpl.
  apply isprogram_lsubst1; sp.
  rw @nt_wf_eq; sp.
  allapply @in_csub2sub; sp.
Qed.

Lemma isprogram_lsubst_wf_term {p} :
  forall t : @WTerm p,
  forall sub : CSubstitution,
    wf_term (csubst (get_wterm t) sub).
Proof.
  sp; rw @wf_term_eq.
  apply isprogram_lsubst_nt_wf.
Qed.

Definition wf_term_csubst {p} :
  forall t : NTerm,
  forall sub : @CSubstitution p,
    wf_term t
    -> wf_term (csubst t sub).
Proof.
  sp; allrw @wf_term_eq.
  apply isprogram_lsubst1; sp.
  allapply @in_csub2sub; sp.
Qed.

Definition lsubstw {p} (t : @WTerm p) (sub : CSubstitution) : WTerm :=
  exist wf_term (csubst (get_wterm t) sub) (isprogram_lsubst_wf_term t sub).

Lemma lsubstw_nil {p} :
  forall t, @lsubstw p t [] = t.
Proof.
  intro; destruct t; unfold lsubstw; simpl.
Abort.

Lemma isprogram_lsubst_aux2 {p} :
  forall t : @NTerm p,
  forall sub : Substitution,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> free_vars (lsubst_aux t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof.
  nterm_ind t as [|o lbt ind ] Case; simpl; introv k.

  - Case "vterm".
    remember (sub_find sub n); destruct o; symmetry in Heqo; simpl.
    + apply sub_find_some in Heqo.
      discover.
      allunfold @isprogram; allunfold @closed; sp.
      allrw.
      symmetry.
      rw <- null_iff_nil.
      rw null_remove_nvars; simpl; sp; subst.
      apply in_dom_sub in Heqo; sp.
    + apply sub_find_none2 in Heqo.
      symmetry.
      rw <- remove_nvars_unchanged.
      unfold disjoint; simpl; sp; subst; auto.

  - Case "oterm".
    auto.
    rw flat_map_map; unfold compose.
    rw remove_nvars_flat_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.

    apply ind with (sub := sub_filter sub l) in i; sp.

    allrw.
    rw remove_nvars_app_l.
    rw remove_nvars_comm.
    rw remove_nvars_app_l.
    rw @remove_nvars_comb; auto.

    apply k with (v := v).
    assert (subset (sub_filter sub l) sub) as s by apply sub_filter_subset.
    unfold subset in s.
    discover; sp.
Qed.

Lemma isprogram_lsubst2 {p} :
  forall t : @NTerm p,
  forall sub : Substitution,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> free_vars (lsubst t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof.
  intros. change_to_lsubst_aux4.
  apply isprogram_lsubst_aux2;sp.
Qed.

Lemma free_vars_csubst {p} :
  forall t : @NTerm p,
  forall sub : CSubstitution,
    free_vars (csubst t sub)
    = remove_nvars (dom_sub (csub2sub sub)) (free_vars t).
Proof.
  sp; apply isprogram_lsubst2; sp.
  allapply @in_csub2sub; sp.
Qed.

Lemma isprogram_lsubst {p} :
  forall t : @NTerm p,
  forall sub : Substitution,
    nt_wf t
    -> (forall v u, LIn (v, u) sub -> isprogram u)
    -> (forall v, LIn v (free_vars t) -> LIn v (dom_sub sub))
    -> isprogram (lsubst t sub).
Proof.
  introv w k1 k2.
  unfold isprogram.
  apply @isprogram_lsubst1 with (sub := sub) in w; sp.
  unfold closed.
  allrw.
  rw <- null_iff_nil.
  rw null_remove_nvars; simpl; sp.
Qed.

(*
Lemma isprogram_lcsubst0 :
  forall vs  : list NVar,
  forall t   : CVTerm vs,
  forall sub : CSubOver vs,
    isprogram (lsubst (get_cvterm vs t) (csubo2sub vs sub)).
Proof.
  sp.
  destruct t, sub; allunfold dom_csubo; allunfold csubo2sub; allsimpl.
  allrw isprog_vars_eq; sp.
  apply isprogram_lsubst; allsimpl; sp.
  apply in_csub2sub in H1; sp.
  allrw subvars_prop.
  apply H in H1.
  allrw over_vars_eq.
  allrw subvars_prop.
  apply o in H1.
  allapply in_dom_csub_exists; sp.
  allapply sub_find_some.
  exists t; sp.
Qed.

Lemma isprog_lcsubst0 :
  forall vs  : list NVar,
  forall t   : CVTerm vs,
  forall sub : CSubOver vs,
    isprog (lsubst (get_cvterm vs t) (csubo2sub vs sub)).
Proof.
  sp; rw isprog_eq; apply isprogram_lcsubst0.
Qed.

Definition lsubstc0 (vs  : list NVar)
                    (t   : CVTerm vs)
                    (sub : CSubOver vs) : CTerm :=
  exist isprog
         (lsubst (get_cvterm vs t) (csubo2sub vs sub))
         (isprog_lcsubst0 vs t sub).
*)

Lemma isprogram_csubst {p} :
  forall t   : @NTerm p,
  forall sub : CSubstitution,
    nt_wf t
    -> cover_vars t sub
    -> isprogram (csubst t sub).
Proof.
  sp.
  apply isprogram_lsubst; sp.
  allapply @in_csub2sub; sp.
  allrw @cover_vars_eq.
  allrw subvars_prop.
  apply_in_hyp pp.
  allapply @in_dom_csub_exists; sp.
  allapply @sub_find_some.
  allapply @in_dom_sub; sp.
Qed.

Lemma isprog_csubst {p} :
  forall t   : @NTerm p,
  forall sub : CSubstitution,
    wf_term t
    -> cover_vars t sub
    -> isprog (csubst t sub).
Proof.
  sp; allsimpl; rw @isprog_eq; apply isprogram_csubst; sp.
  rw @nt_wf_eq; sp.
Defined.

Lemma isprog_csubst_pi {p} :
  forall t sub w1 w2 c1 c2,
    @isprog_csubst p t sub w1 c1 = isprog_csubst t sub w2 c2.
Proof.
  sp.
  eauto with pi.
Qed.

Definition lsubstc {p}
                   (t   : @NTerm p)
                   (w   : wf_term t)
                   (sub : CSubstitution)
                   (p   : cover_vars t sub) : CTerm :=
  exist isprog
        (csubst t sub)
        (isprog_csubst t sub w p).

Lemma lsubstc_replace {p} :
  forall t w1 w2 s p1 p2,
    @lsubstc p t w1 s p1 = lsubstc t w2 s p2.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_cterm {p} :
  forall t w s c,
    @lsubstc p (get_cterm t) w s c = t.
Proof.
  introv.
  apply cterm_eq; simpl.
  unfold csubst.
  apply lsubst_trivial; introv i.
  rw @free_vars_cterm; simpl; sp.
  apply in_csub2sub in i; sp.
Qed.

Lemma lsubstc_eq {p} :
  forall t1 t2 w1 w2 s1 s2 p1 p2,
    t1 = t2
    -> s1 = s2
    -> @lsubstc p t1 w1 s1 p1 = lsubstc t2 w2 s2 p2.
Proof.
  sp.
  revert p1 p2 w1 w2.
  rewrite H, H0; sp.
  apply lsubstc_replace.
Qed.

Lemma lsubstc_ex {pp} :
  forall t w s p,
    {w' : @wf_term pp t & {p' : cover_vars t s &
      lsubstc t w s p = lsubstc t w' s p'}}.
Proof.
  sp; exists w p; auto.
Qed.

Lemma free_vars_csubst_sub {p} :
  forall t sub vs,
    subvars (free_vars (@csubst p t sub)) vs
    -> subvars (free_vars t) (dom_csub sub ++ vs).
Proof.
  sp; allrewrite @free_vars_csubst.
  allrw subvars_remove_nvars.
  allrewrite @dom_csub_eq.
  rw subvars_comm_r; sp.
Qed.

Lemma free_vars_csubst_sub_iff {p} :
  forall t sub vs,
    subvars (free_vars (@csubst p t sub)) vs
    <=> subvars (free_vars t) (dom_csub sub ++ vs).
Proof.
  sp; split; sp; try (apply free_vars_csubst_sub; auto).
  rw @free_vars_csubst.
  rw subvars_remove_nvars.
  rw @dom_csub_eq.
  rw subvars_comm_r; sp.
Qed.

Lemma cover_vars_csubst {p} :
  forall t sub1 sub2,
    @cover_vars p t (sub1 ++ sub2)
    <=>
    cover_vars (csubst t sub1) sub2.
Proof.
  intros.
  repeat (rw @cover_vars_eq).
  rw @dom_csub_app.
  rw @free_vars_csubst_sub_iff; sp.
Qed.

Lemma cover_vars_csubst2 {p} :
  forall t sub1 sub2,
    cover_vars (@csubst p t sub1) sub2
    <=>
    cover_vars_upto t sub2 (dom_csub sub1).
Proof.
  intros.
  rw <- @cover_vars_csubst.
  repeat (rw @cover_vars_eq).
  unfold cover_vars_upto.
  rw @dom_csub_app; sp.
Qed.

Lemma cover_vars_csubst3 {p} :
  forall t sub1 sub2,
    cover_vars (@csubst p t sub1) sub2
    <=>
    cover_vars_upto t (csub_filter sub2 (dom_csub sub1)) (dom_csub sub1).
Proof.
  intros.
  rw @cover_vars_csubst2.
  unfold cover_vars_upto.
  rewrite dom_csub_csub_filter.
  rw subvars_app_remove_nvars_r; sp.
Qed.

Lemma subst_preserves_program {p} :
  forall t v u,
    @nt_wf p t
    -> (forall x, LIn x (free_vars t) -> x = v)
    -> isprogram u
    -> isprogram (subst t v u).
Proof.
  introv w k isp.
  apply isprogram_lsubst with (sub := [(v,u)]) in w; allsimpl; sp; inj; sp.
  apply_in_hyp pp; subst; sp.
Qed.

Lemma subst_preserves_isprog {p} :
  forall t : @NTerm p,
  forall v : NVar,
  forall u : NTerm,
    isprog_vars [v] t
    -> isprog u
    -> isprog (subst t v u).
Proof.
  introv ispt ispu.
  allrw <- @isprogram_eq.
  allunfold @isprog_vars; repnd.
  allrw <- @nt_wf_eq.
  apply subst_preserves_program; tcsp.
  introv i.
  allrw assert_sub_vars.
  apply ispt0 in i; allsimpl; sp.
Qed.
Hint Resolve subst_preserves_isprog : isprog.

Definition substc {p} (u : @CTerm p) (v : NVar) (t : CVTerm [v]) : CTerm :=
  let (a,x) := t in
  let (b,y) := u in
    exist isprog (subst a v b) (subst_preserves_isprog a v b x y).

Tactic Notation "allrwxxx" constr(T) :=
  repeat match goal with
           | [ H : _ |- _ ] =>
             progress (trw_h T H || trw T || rewrite T in H || rewrite T)
          end.

Tactic Notation "allrwxxx" ident(T) :=
  let t := type of T in
  repeat match goal with
           | [ H1 : t, H : _ |- _ ] =>
             progress (trw_h T H || trw T || rewrite T in H || rewrite T)
         end.

Lemma substc_cvterm_var {p} :
  forall t v u,
    substc t v (@cvterm_var p v u) = u.
Proof.
  introv; destruct_cterms.
  apply cterm_eq; simpl.
  apply lsubst_trivial; simpl; introv h; repndors; tcsp; ginv.
  allrw <- @isprogram_eq; dands; auto.
  intro h.
  inversion i as [c w].
  unfold closed in c; rw c in h; allsimpl; sp.
Qed.

(** the lsubst version of this is best done after 
   we have the lemma that alpha_equality preserves wf 
    lsubst_wf_iff is proved in alphaeq.v*)

Lemma lsubst_aux_preserves_wf {p} :
  forall t : @NTerm p,
  forall sub : Substitution,
    nt_wf t
    -> (forall v u, LIn (v, u) sub -> nt_wf u)
    -> nt_wf (lsubst_aux t sub).
Proof.
  nterm_ind1 t as [?|o lbt Hind]Case; simpl; introv HX hwf; auto.

  - Case "vterm".
    remember (sub_find sub n); destruct o; symmetry in Heqo; sp.
    apply sub_find_some in Heqo.
    apply_in_hyp pp; sp.

  - Case "oterm".
    invertsna HX  Hwf; subst.
    allrw in_map_iff; sp; subst.
    constructor.
    Focus 2. rw @map_num_bvars_bterms;sp;fail.
    intros bt Hin.
    apply in_map_iff in Hin; exrepnd; destruct a as [lv nt].
    allsimpl. subst.
    constructor.
    eapply Hind; eauto;[|].
    + apply Hwf in Hin1.
      invertsn Hin1;sp.
    + introv Hin. apply in_sub_filter in Hin. sp.
      discover; sp.
Qed.

Lemma in_var_ren {p} : forall lvi lvo u t,
  LIn (u, t) (var_ren lvi lvo)
  -> (LIn u lvi) # {v:NVar & (t = @vterm p v) # (LIn v lvo)}.
Proof.
  introv Hl.
  apply in_combine in Hl.
  repnd. apply in_map_iff in Hl.
  exrepnd.
  split; cpx.
  eexists; eauto.
Defined.

(**This is a trivial consequence of the fact that
  its output is alpha equal to input. But lemma that comes
  way too late in alpha_eq.v. Hence, a direct proof here*)
Lemma change_bvars_alpha_preserves_wf {p} :
  forall (nt : @NTerm p) lv,
    nt_wf nt
    -> nt_wf (change_bvars_alpha lv nt).
Proof.
  nterm_ind1 nt as [v|o lbt Hind] Case; introv HX; auto;[].
  invertsna HX  Hwf; subst.
  simpl; constructor.
  - introv i.
    rw in_map_iff in i; exrepnd; subst.
    destruct a; simpl.
    remember (fresh_vars (length l) (lv ++ all_vars (change_bvars_alpha lv n))) as s.
    destruct s; allsimpl; repnd.
    constructor.
    apply lsubst_aux_preserves_wf; auto.
    + eapply Hind; eauto.
      apply Hwf in i1; inversion i1; subst; auto.
    + introv k.
      apply in_var_ren in k; exrepnd; subst; auto.
  - rw <- Hwf0.
    rw map_map.
    apply eq_maps; introv k.
    unfold compose, num_bvars.
    destruct x; simpl.
    pose proof (fresh_distinct_vars_spec
                  (length l)
                  (lv ++ all_vars (change_bvars_alpha lv n))) as h;
      simpl in h; sp.
Qed.

Definition wf_lsubst_to_lsubst {p} (sub : @WfSubstitution p) : Substitution :=
  map (fun x => (fst x, get_wterm (snd x))) sub.

(** TODO: non aux version *)
Lemma lsubst_aux_preserves_wf_term {p} :
  forall t : NTerm,
  forall sub : @Substitution p,
    wf_term t
    -> (forall v u, LIn (v, u) sub -> wf_term u)
    -> wf_term (lsubst_aux t sub).
Proof.
  sp.
  rw <- @nt_wf_eq.
  apply lsubst_aux_preserves_wf; sp.
  rw @nt_wf_eq; auto.
  apply_in_hyp pp.
  rw @nt_wf_eq; auto.
Qed.

(* Abhishek, is that easy to prove? *)
Lemma lsubst_preserves_wf_term {p} :
  forall t : NTerm,
  forall sub : @Substitution p,
    wf_term t
    -> (forall v u, LIn (v, u) sub -> wf_term u)
    -> wf_term (lsubst t sub).
Proof.
  sp.
  unfold lsubst.
  destruct (dec_disjointv (bound_vars t) (flat_map free_vars (range sub)));
    try (apply lsubst_aux_preserves_wf_term; sp).
Abort.

(*
(** TODO: non aux version *)
Lemma lsubst_aux_preserves_wf_term' {p} :
  forall t : NTerm,
  forall sub : @Substitution p,
    wf_term t
    -> assert (ball (map (fun x => wft (snd x)) sub))
    -> wf_term (lsubst_aux t sub).
Proof.
  intros.
  apply lsubst_aux_preserves_wf_term; sp.
  rw <- fold_assert in H0.
  rw ball_map_true in H0.
  apply_in_hyp pp.
  allfold (wf_term u); auto.
Qed.
 *)

(*
Definition wf_lsubst (t : WTerm) (sub : WfSubstitution) : WTerm :=
  let (a,w) := t in
  let s := wf_lsubst_to_lsubst sub in
    exist
      wf_term
      (lsubst a s)
      (lsubst_preserves_wf_term'
         a
         s
         w
         (eq_refl (ball (map (fun x => snd x) sub)))).
*)

(** TODO: non aux version *)
Lemma subst_aux_preserves_wf {p} :
  forall t : NTerm,
  forall v : NVar,
  forall u : @NTerm p,
    nt_wf t
    -> nt_wf u
    -> nt_wf (subst_aux t v u).
Proof.
  introv wt wu.
  apply lsubst_aux_preserves_wf with (sub := [(v,u)]) in wt; allsimpl; sp; inj.
Qed.

(** TODO: non aux version *)
Lemma subst_aux_preserves_wf_term {p} :
  forall t : @NTerm p,
  forall v : NVar,
  forall u : NTerm,
    wf_term t
    -> wf_term u
    -> wf_term (subst_aux t v u).
Proof.
  intros t v u.
  repeat (rw <- @nt_wf_eq); sp.
  apply subst_aux_preserves_wf; auto.
Qed.

(** TODO: non aux version *)
Definition substwf {p} (t : @WTerm p) (v : NVar) (u : WTerm) : WTerm :=
  let (a,x) := t in
  let (b,y) := u in
    exist wf_term (subst_aux a v b) (subst_aux_preserves_wf_term a v b x y).

(*

Lemma isprogram_bt_iff :
  forall vs t,
    (forall sub,
    (forall v u, LIn (v, u) sub -> isprogram u)
    -> (forall v, LIn v vs -> exists u, LIn (v, u) sub)
    -> isprogram (lsubst t sub))
    <=> isprogram_bt (bterm vs t).
Proof.
  unfold isprogram_bt, closed_bt, isprogram, closed; simpl; sp.
  rw <- null_nil.
  rw <- null_nil in H1.
  rw null_remove_nvars; sp.
  aXdmit.
  aXdmit.
Qed.

*)


Lemma isprogram_bt_implies2 {p} :
  forall (bt: @BTerm p),
    isprogram_bt bt
    -> forall lnt : list NTerm,
         (forall nt : NTerm, LIn nt lnt -> isprogram nt)
         -> num_bvars bt <= length lnt
         -> isprogram (apply_bterm bt lnt).
Proof.
 intros ? Hprog ?  Hprognt Hlen. inverts Hprog as Hclos Hwf.
 inverts Hwf. unfold num_bvars in Hlen. simpl in Hlen.
 unfold apply_bterm. simpl. apply isprogram_lsubst; auto.
 -  intros ? ? Htemp. apply in_combine in Htemp; sp.
 -  intros ?  Hin.
    inverts Hclos as Hrem.
    apply null_iff_nil in Hrem.
    unfold remove_nvars in Hrem. rw null_diff in Hrem.
    assert (LIn v lnv) as Hinv by (apply Hrem; auto).
    apply in_nth in Hinv; try (apply deq_nvar).
    destruct Hinv as [n Hp].
    rw @dom_sub_combine_le; sp.
Qed.

Lemma isprogram_bt_implies {p} :
 forall (bt:@BTerm p),
   isprogram_bt bt
   -> forall lnt : list NTerm,
        (forall nt : NTerm, LIn nt lnt -> isprogram nt)
        -> num_bvars bt = length lnt
        -> isprogram (apply_bterm bt lnt).
Proof.
  intros ? Hprog ?  Hprognt Hlen. apply isprogram_bt_implies2; auto. omega.
Qed.

(*
Lemma isprogram_lsubst_implies :
  forall t sub,
    isprogram (lsubst t sub)
    -> forall v u,
         alpha_eq [] t u
         -> LIn v (free_vars u)
         -> exists u, sub_find sub v = Some u # isprogram u.
Proof.


  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    unfold lsubst in H; simpl in H.
    sp; subst.
    remember (sub_find sub v); destruct o; symmetry in Heqo.
    exists n; sp.
    rw isprogram_vterm in H; sp.

  - Case "oterm".
    rw isprogram_ot_iff in H0; sp.
    rw in_flat_map in H1; sp.
    destruct x.
    simpl in H3.
    rw in_remove_nvars in H3; sp.
    generalize (H2 (lsubst_bterm (bterm l n) sub)); sp.
    dimp H5.
    rw in_map_iff. exists (bterm l n); sp.
    apply isprogram_bt_implies with (lnt := map (fun v => mk_axiom) (fst (fst (bvar_renamings_subst l sub)))) in hyp; sp.
    unfold apply_bterm in hyp.

    simpl in hyp.
    rw bvar_renamings_subst_eta in hyp.
    apply isprogram_bt_implies with (lnt := map (fun v => mk_axiom) (fst (fst (bvar_renamings_subst l sub)))) in hyp; sp.

    unfold apply_bterm in hyp; simpl in hyp.

    apply H with (lv := ) in hyp.

    rw in_map_iff in H6; sp; subst.
    apply isprogram_axiom.

    rw num_bvars_on_bterm.
    rw map_length; auto.


    apply H with (nt := n) (lv := l); auto.
Abort.
*)

Lemma subset_free_vars_sub_aux_app {p} :
  forall t sub1 sub2,
    (forall v t, LIn (v, t) (sub1 ++ sub2) -> @isprogram p t)
    -> disjoint (free_vars t) (dom_sub sub2)
    -> lsubst_aux t (sub1 ++ sub2) = lsubst_aux t sub1.
Proof.
  nterm_ind t Case; simpl; introv k d; auto.

  - Case "vterm".
    allrw disjoint_singleton_l; sp.
    remember (sub_find sub1 n); destruct o; symmetry in Heqo.
    apply @sub_find_some_app with (sub2 := sub2) in Heqo.
    rw Heqo; auto.
    rw @sub_find_none_iff in Heqo.
    assert (! LIn n (dom_sub (sub1 ++ sub2))) as nin
      by (rw @dom_sub_app; rw in_app_iff; intro; sp).
    rw <- @sub_find_none_iff in nin.
    rw nin; auto.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.
    repeat (rw bvar_renamings_subst_isprogram; auto); simpl;
    try (sp; apply X with (v := v); rw in_app_iff; sp).
    rw @sub_filter_app.

    rewrite H with (lv := l); sp.
    apply k with (v := v).
    allrw in_app_iff.
    allrw @in_sub_filter; sp.
    allrw disjoint_flat_map_l.
    apply_in_hyp pp.
    allsimpl.
    rw disjoint_remove_nvars_l in pp.
    rw <- @dom_sub_sub_filter; auto.
Qed.

Lemma subset_free_vars_sub_app {p} :
  forall t sub1 sub2,
    (forall v t, LIn (v, t) (sub1 ++ sub2) -> @isprogram p t)
    -> disjoint (free_vars t) (dom_sub sub2)
    -> lsubst t (sub1 ++ sub2) = lsubst t sub1.
Proof.
  introv Hpr. applydup (sub_app_sat_if (@isprogram p)) in Hpr. repnd.
  allfold (prog_sub sub1). intros.
  change_to_lsubst_aux4.
  apply subset_free_vars_sub_aux_app;sp.
Qed.

Lemma sub_find_member {p} :
  forall sub1 sub2 x t,
    ! LIn x (@dom_sub p sub1)
    -> sub_find (sub1 ++ (x, t) :: sub2) x = Some t.
Proof.
  induction sub1; simpl; sp.
  rw <- beq_var_refl; auto; allsimpl.
  remember (beq_var a0 x); destruct b.
  apply beq_var_eq in Heqb; subst.
  provefalse; apply H; left; auto.
  symmetry in Heqb.
  apply beq_var_false_not_eq in Heqb.
  apply IHsub1; sp.
Qed.

Lemma sub_filter_map_trivial_vars {p} :
  forall vars l,
    sub_filter (map (fun v : NVar => (v, vterm v)) vars) l
    = map (fun v : NVar => (v, @vterm p v)) (remove_nvars l vars).
Proof.
  induction vars; simpl; sp.
  rw remove_nvars_nil_r; simpl; auto.
  rw IHvars.
  rw remove_nvars_cons_r.
  destruct (memvar a l); auto.
Qed.

Lemma sub_find_sub_filter_some {p} :
  forall l v t sub,
    (sub_find (@sub_filter p sub l) v = Some t)
    <=> (sub_find sub v = Some t # ! LIn v l).
Proof.
  induction sub; simpl; sp; split; sp; allsimpl.

  remember (beq_var a0 v); destruct b.

  apply beq_var_eq in Heqb; subst.

  remember (memvar v l); destruct b; allsimpl.
  rw IHsub in H; sp.
  symmetry in Heqb.
  rw fold_assert in Heqb.
  rw assert_memvar in Heqb; sp.
  rw <- beq_var_refl in H; allsimpl; sp.

  symmetry in Heqb.
  applydup beq_var_false_not_eq in Heqb.
  remember (memvar a0 l); destruct b; allsimpl.
  rw IHsub in H; sp.
  rw Heqb in H.
  rw IHsub in H; sp.

  remember (memvar a0 l); destruct b; allsimpl.
  rw IHsub in H; sp.

  symmetry in Heqb.
  rw not_of_assert in Heqb.
  rw assert_memvar in Heqb.
  remember (beq_var a0 v); destruct b.
  apply beq_var_eq in Heqb0; subst; sp.
  rw IHsub in H; sp.

  remember (memvar a0 l); destruct b; allsimpl.

  symmetry in Heqb; rw fold_assert in Heqb; rw assert_memvar in Heqb.
  rw IHsub; sp.
  remember (beq_var a0 v); destruct b; sp.

  apply beq_var_eq in Heqb0; subst; sp.

  remember (beq_var a0 v); destruct b; sp.
  rw IHsub; sp.
Qed.

Lemma sub_find_sub_filter_none {p} :
  forall l v sub,
    (sub_find (@sub_filter p sub l) v = None)
    <=> (sub_find sub v = None [+] LIn v l).
Proof.
  induction sub; simpl; sp; split; sp; allsimpl;
  remember (memvar a0 l); destruct b; allsimpl;
  duplicate Heqb as eq;
  symmetry in Heqb;
  try (rw fold_assert in Heqb; rw assert_memvar in Heqb);
  try (rw not_of_assert in Heqb; rw assert_memvar in Heqb);
  remember (beq_var a0 v); destruct b;
  duplicate Heqb0 as eq2;
  try (apply beq_var_eq in Heqb0; subst);
  try (symmetry in Heqb0; apply beq_var_false_not_eq in Heqb0); sp;
  try (complete (apply IHsub; auto)).
Qed.

Lemma sub_filter_swap {p} :
  forall l1 l2 sub,
    sub_filter (@sub_filter p sub l1) l2
    = sub_filter (sub_filter sub l2) l1.
Proof.
  induction sub; simpl; sp.
  remember (memvar a0 l1); destruct b; remember (memvar a0 l2); destruct b; simpl; sp.
  rw <- Heqb; sp.
  rw <- Heqb0; sp.
  rw <- Heqb; sp.
  rw <- Heqb0; sp.
  rw IHsub; sp.
Qed.

Lemma sub_filter_app_as_remove_nvars {p} :
  forall sub l1 l2,
    @sub_filter p sub (l1 ++ l2)
    = sub_filter sub (l1 ++ remove_nvars l1 l2).
Proof.
  induction sub; simpl; sp; allsimpl.
  remember (memvar a0 (l1 ++ l2)); symmetry in Heqb; destruct b.

  rw fold_assert in Heqb; rw assert_memvar in Heqb.
  rw in_app_iff in Heqb; sp.

  remember (memvar a0 (l1 ++ remove_nvars l1 l2)); symmetry in Heqb; destruct b.

  rw fold_assert in Heqb; rw assert_memvar in Heqb; rw in_app_iff in Heqb; sp.

  rw not_of_assert in Heqb; rw assert_memvar in Heqb; rw in_app_iff in Heqb.
  apply not_over_or in Heqb; sp.

  remember (memvar a0 (l1 ++ remove_nvars l1 l2)); symmetry in Heqb; destruct b.

  rw fold_assert in Heqb; rw assert_memvar in Heqb; rw in_app_iff in Heqb; sp.

  rw not_of_assert in Heqb; rw assert_memvar in Heqb; rw in_app_iff in Heqb.
  apply not_over_or in Heqb; repnd.
  allrw in_remove_nvars.
  provefalse; apply Heqb; sp.

  rw not_of_assert in Heqb; rw assert_memvar in Heqb; rw in_app_iff in Heqb.
  apply not_over_or in Heqb; repnd.

  remember (memvar a0 (l1 ++ remove_nvars l1 l2)); symmetry in Heqb1; destruct b.

  rw fold_assert in Heqb1; rw assert_memvar in Heqb1; rw in_app_iff in Heqb1; sp.
  allrw in_remove_nvars; sp.

  rw <- IHsub; sp.
Qed.

Lemma sub_find_sub_filter_eta {p} :
  forall lv v sub,
    !LIn v lv
    -> sub_find (@sub_filter p sub lv) v
       = sub_find sub v.
Proof.
  intros.
  cases (sub_find (sub_filter sub lv) v) as Hl.
  - apply sub_find_sub_filter_some in Hl; repnd; auto.
  - apply sub_find_sub_filter_none in Hl. dorn Hl; sp.
Qed.

Lemma lsubst_aux_sub_filter_aux {o} :
  forall (t : @NTerm o) sub l,
    (forall v, LIn v (free_vars t) -> LIn v l -> !LIn v (dom_sub sub))
    -> lsubst_aux t (sub_filter sub l) = lsubst_aux t sub.
Proof.
  nterm_ind1 t as [v|op bs ind] Case; simpl; introv disj; auto.

  - Case "vterm".
    allrw disjoint_singleton_l.
    destruct (in_deq NVar deq_nvar v l) as [i|i].
    + pose proof (disj v) as h; repeat (autodimp h hyp).
      rw @sub_find_sub_filter; auto.
      apply sub_find_none_iff in h; rw h; auto.
    + rw @sub_find_sub_filter_eta; auto.

  - Case "oterm".
    f_equal.
    apply eq_maps; intros b i.
    destruct b as [vs t]; simpl.
    f_equal.

    rw @sub_filter_swap.
    eapply ind; eauto.
    introv a b c.
    allrw <- @dom_sub_sub_filter.
    allrw in_remove_nvars; repnd.
    pose proof (disj v) as h.
    autodimp h hyp; tcsp.
    rw lin_flat_map.
    eexists; dands; eauto; simpl.
    rw in_remove_nvars; sp.
Qed.

Lemma lsubst_aux_sub_filter {o} :
  forall (t : @NTerm o) sub l,
    disjoint (free_vars t) l
    -> lsubst_aux t (sub_filter sub l) = lsubst_aux t sub.
Proof.
  introv disj.
  apply lsubst_aux_sub_filter_aux.
  introv a b c.
  apply disj in a; sp.
Qed.

(*
(** TODO : use the stronger lemma lsubst_aux_sub_filter2 for a smaller and
    more maintainable proof*)
Lemma lsubst_aux_sub_filter {p} :
  forall t sub l,
    (forall v u, LIn (v, u) sub -> @isprogram p u)
    -> disjoint (free_vars t) l
    -> lsubst_aux t (sub_filter sub l) = lsubst_aux t sub.
Proof.
  nterm_ind t Case; simpl; intros.

  - Case "vterm".
    remember (sub_find (sub_filter sub l) n); symmetry in Heqo; destruct o.
    rw @sub_find_sub_filter_some in Heqo; sp.
    allrw; sp.
    rw @sub_find_sub_filter_none in Heqo; sp.
    allrw; sp.
    allrw disjoint_singleton_l; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.

    allrw disjoint_flat_map_l.
    apply_in_hyp pp; allsimpl.
    allrw disjoint_remove_nvars_l.

    repeat (rw bvar_renamings_subst_isprogram; sp).
    repeat (rw app_nil_l).
    rw @sub_filter_swap.
    rw <- @sub_filter_app_r.
    rw @sub_filter_app_as_remove_nvars.
    rw @sub_filter_app_r.
    rewrite H with (lv := l0); sp.

    allrw @in_sub_filter; sp.
    discover; sp.
Qed.
*)

Lemma lsubst_sub_filter {p} :
  forall t sub l,
    (forall v u, LIn (v, u) sub -> @isprogram p u)
    -> disjoint (free_vars t) l
    -> lsubst t (sub_filter sub l) = lsubst t sub.
Proof.
  introv Hpr. duplicate Hpr. eapply sub_filter_sat with (lv:=l) in Hpr; eauto.
  change_to_lsubst_aux4.
  apply lsubst_aux_sub_filter;sp.
Qed.

Lemma csubst_csub_filter {p} :
  forall t sub l,
    disjoint (free_vars t) l
    -> csubst t (@csub_filter p sub l) = csubst t sub.
Proof.
  unfold csubst; sp.
  rw <- @sub_filter_csub2sub.
  apply lsubst_sub_filter; sp.
  allapply @in_csub2sub; sp.
Qed.

(* XXXXXXXXXXXXXXXXXXX switch XXXXXXXXXXXXXXXXXXX *)

Lemma lsubst_aux_trivial_vars {p} :
  forall t vars,
    lsubst_aux t (map (fun v => (v, @vterm p v)) vars) = t.
Proof.
  nterm_ind t Case; simpl; intros; auto.

  - Case "vterm".
    remember (sub_find (map (fun v : NVar => (v, vterm v)) vars) n); destruct o; auto.
    symmetry in Heqo.
    applydup @sub_find_some in Heqo; rw in_map_iff in Heqo0; sp; inj.

  - Case "oterm".
    f_equal.
    induction lbt; simpl; sp.
    rw IHlbt; sp; try (rewrite H with (lv := lv); sp; simpl; sp).
    destruct a; simpl.
    f_equal. f_equal.
    rw @sub_filter_map_trivial_vars.
    rewrite H with (lv := l); sp.
Qed.

Lemma apply_bterm_append_program_id {p} :
  forall bt lnt lnta ,
    (isprogram (apply_bterm bt lnt))  ->
    (forall nt, LIn nt lnt -> isprogram nt) ->
    (forall nt, LIn nt lnta -> @isprogram p nt) ->
    (apply_bterm bt lnt = apply_bterm bt (lnt++lnta)).
Proof.
 intros ?  ? ? Hisp Hnt Hnta. destruct bt as [lv nt].
  unfold apply_bterm. simpl.
  assert(length lv <= length lnt \/ length lnt < length lv ) as Hdi by omega.
  destruct Hdi. rw <- combine_app_eq; auto.
  rw combine_app_app; auto; try omega.
  rw <- @simple_lsubst_app.
  unfold apply_bterm in Hisp.
  apply lsubst_trivial2 with
   (sub:= (combine (skipn (length lnt) lv) (firstn (length lv - length lnt) lnta)))
   in Hisp; auto.
  - intros ? ? Hin. apply in_combine in Hin; exrepnd.
    apply in_firstn in Hin; try omega; auto.
  - intros ? ? Hin. apply in_combine in Hin. sp.
  - intros ? ? Hin. apply in_combine in Hin. exrepnd.
    apply in_firstn in Hin; try omega; auto.
Qed.

Lemma lsubst_aux_nt_wf {p} :
  forall t sub,
    nt_wf (@lsubst_aux p t sub)
    -> nt_wf t.
Proof.
  nterm_ind t as [|o lbt ind] Case; simpl; introv w; auto.

  Case "oterm".
  inversion w as [|op lnt k e]; subst; auto.
  constructor.

  - introv i; destruct l.
    generalize (k (lsubst_bterm_aux (bterm l n) sub)); intro j.
    dest_imp j hyp.
    rw in_map_iff.
    exists (bterm l n); sp.
    simpl in j.
    inversion j; subst.

    apply ind with (sub := (sub_filter sub l)) in i; auto.

  - rw <- e; rw map_map; unfold compose.
    rewrite eq_maps with (g := fun x : BTerm => num_bvars (lsubst_bterm_aux x sub)); sp.
    destruct x.
    unfold num_bvars. simpl;refl.
Qed.


(*
Lemma isprog_lcsubst_pi2 :
  forall t sub1 sub2 w1 w2 c1 c2,
    isprog_lcsubst (csubst t sub1) sub2 w1 c1
    = isprog_lcsubst t (sub1 ++ sub2) w2 c2.
Proof.
Qed.
*)

(*
Lemma isprog_lcsubst_pi2 :
  forall t1 t2 : NTerm,
  forall sub,
  forall w1 : wf_term t1,
  forall w2 : wf_term t2,
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall e : t1 = t2,
    match e with eq_refl => isprog_lcsubst t1 sub w1 c1 end
    = isprog_lcsubst t2 sub w2 c2.
Proof.
  sp.
  apply isprog_proof_irrelevance.
Qed.
*)



Lemma lsubst_aux_snoc_dup {p} :
  forall t sub v u,
    (forall v t, LIn (v, t) sub -> isprogram t)
    -> @isprogram p u
    -> LIn v (dom_sub sub)
    -> lsubst_aux t (snoc sub (v, u)) = lsubst_aux t sub.
Proof.
  nterm_ind t Case; simpl; intros; auto.

  - Case "vterm".
    rw @sub_find_snoc.
    remember (sub_find sub n); destruct o; symmetry in Heqo; sp.
    applydup @sub_find_none2 in Heqo.
    remember (beq_var v n); destruct b; sp.
    apply beq_var_true in Heqb; subst; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.

    repeat (rw bvar_renamings_subst_isprogram; auto); simpl;
    try (complete (sp; allrw in_snoc; sp; allapply pair_inj; sp; subst; sp; apply_in_hyp p; sp)).

    rw @sub_filter_snoc.
    remember (memvar v l); symmetry in Heqb; destruct b; sp.
    rewrite H with (lv := l); sp.
    allrw @in_sub_filter; sp.
    apply_in_hyp pp; sp.
    rw <- @dom_sub_sub_filter.
    rw in_remove_nvars; sp.
    rw not_of_assert in Heqb.
    rw assert_memvar in Heqb; sp.
Qed.

Lemma lsubst_snoc_dup {p} :
  forall t sub v u,
    (forall v t, LIn (v, t) sub -> isprogram t)
    -> @isprogram p u
    -> LIn v (dom_sub sub)
    -> lsubst t (snoc sub (v, u)) = lsubst t sub.
Proof.
  introv k isp i. assert(prog_sub (snoc sub (v,u))). introv Hin.
  apply in_snoc in Hin. dorn Hin; auto.
  - apply k in Hin. sp.
  - inverts Hin. subst.  trivial.
  - change_to_lsubst_aux4.
    apply lsubst_aux_snoc_dup ;sp.
Qed.

Lemma csubst_snoc_dup {p} :
  forall t sub v u,
    LIn v (@dom_csub p sub)
    -> csubst t (snoc sub (v,u)) = csubst t sub.
Proof.
  intros.
  unfold csubst; simpl.
  rw @csub2sub_snoc.
  apply lsubst_snoc_dup; sp.
  allapply @in_csub2sub; sp.
  destruct u; allsimpl.
  rw @dom_csub_eq; sp.
Qed.

Lemma lsubst_aux_swap {p} :
  forall t sub v u,
    (forall v t, LIn (v, t) sub -> @isprogram p t)
    -> isprogram u
    -> ! LIn v (dom_sub sub)
    -> lsubst_aux t ((v, u) :: sub) = lsubst_aux t (snoc sub (v, u)).
Proof.
  nterm_ind t Case; simpl; intros; auto.

  - Case "vterm".
    rw @sub_find_snoc.
    remember (sub_find sub n); destruct o; symmetry in Heqo; sp.
    remember (beq_var v n); destruct b; sp.
    apply beq_var_true in Heqb; subst; sp.
    apply sub_find_some in Heqo.
    apply in_dom_sub in Heqo; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.

    repeat (rw bvar_renamings_subst_isprogram; auto); simpl;
    try (complete (sp; allrw in_snoc; sp; allapply pair_inj; sp; subst; sp; apply_in_hyp p; sp)).

    rw @sub_filter_snoc.
    remember (memvar v l); symmetry in Heqb; destruct b; sp; simpl.
    rewrite H with (lv := l); sp.
    allrw @in_sub_filter; sp.
    apply_in_hyp pp; sp.
    allrw <- @dom_sub_sub_filter.
    allrw in_remove_nvars; sp.
Qed.

Lemma lsubst_swap {p} :
  forall t sub v u,
    (forall v t, LIn (v, t) sub -> @isprogram p t)
    -> isprogram u
    -> ! LIn v (dom_sub sub)
    -> lsubst t ((v, u) :: sub) = lsubst t (snoc sub (v, u)).
Proof.
  introv k isp ni. assert(prog_sub (snoc sub (v,u))).
  - introv Hin.
    apply in_snoc in Hin. dorn Hin; auto.
    + apply k in Hin. sp.
    + inverts Hin. subst.  trivial.
  - assert(prog_sub (cons (v,u) sub)). introv Hin.
    dorn Hin; auto.
    + inverts Hin. subst.  trivial.
    + apply k in Hin. sp.

  + change_to_lsubst_aux4.
    apply lsubst_aux_swap ;sp.
Qed.

Lemma csubst_swap {p} :
  forall t sub v u,
    ! LIn v (@dom_csub p sub)
    -> csubst t ((v, u) :: sub) = csubst t (snoc sub (v, u)).
Proof.
  intros.
  unfold csubst; simpl.
  rw @csub2sub_snoc.
  apply lsubst_swap; sp.
  allapply @in_csub2sub; sp.
  destruct u; allsimpl.
  allrw @dom_csub_eq; sp.
Qed.

Lemma cover_vars_var {p} :
  forall v sub,
    LIn v (@dom_csub p sub)
    -> cover_vars (mk_var v) sub.
Proof.
  sp.
  rw @cover_vars_eq; simpl.
  rw subvars_eq.
  unfold subset; simpl; sp; subst; auto.
Qed.



Lemma lsubst_aux_shift {p} :
  forall t sub1 sub2 sub3,
    (forall v t, LIn (v, t) (sub1 ++ sub2 ++ sub3) -> @isprogram p t)
    -> disjoint (dom_sub sub1) (dom_sub sub2)
    -> lsubst_aux t (sub1 ++ sub2 ++ sub3) = lsubst_aux t (sub2 ++ sub1 ++ sub3).
Proof.
  nterm_ind t as [|o lbt ind] Case; simpl; introv k d; auto.

  - Case "vterm".
    repeat (rw @sub_find_app).
    remember (sub_find sub1 n); destruct o; symmetry in Heqo; auto.
    apply sub_find_some in Heqo.
    unfold disjoint in d.
    apply in_dom_sub in Heqo.
    apply d in Heqo.
    rw <- @sub_find_none_iff in Heqo; rw Heqo; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x; simpl.
    repeat (rw bvar_renamings_subst_isprogram; auto); simpl.

    repeat (rw @sub_filter_app).
    rewrite ind with (lv := l); sp.

    allrw in_app_iff; sp; allrw @in_sub_filter; sp;
    apply k with (v := v); rw in_app_iff; sp;
    rw in_app_iff; sp.

    repeat (rw <- @dom_sub_sub_filter).
    unfold disjoint; introv i1 i2.
    allrw in_remove_nvars; exrepnd.
    unfold disjoint in d; apply_in_hyp pp; sp.
Qed.

Lemma lsubst_shift {p} :
  forall t sub1 sub2 sub3,
    (forall v t, LIn (v, t) (sub1 ++ sub2 ++ sub3) -> @isprogram p t)
    -> disjoint (dom_sub sub1) (dom_sub sub2)
    -> lsubst t (sub1 ++ sub2 ++ sub3) = lsubst t (sub2 ++ sub1 ++ sub3).
Proof.
  introv Hpr. assert (prog_sub (sub2 ++ sub1 ++ sub3)).
  apply sub_app_sat_if in Hpr. repnd.
  apply sub_app_sat_if in Hpr. repnd.
  apply sub_app_sat;sp.
  apply sub_app_sat;sp.
  intros.
  change_to_lsubst_aux4.
  apply lsubst_aux_shift;sp.
Qed.

Lemma csubst_shift {p} :
  forall t sub1 sub2 sub3,
    disjoint (dom_csub sub1) (@dom_csub p sub2)
    -> csubst t (sub1 ++ sub2 ++ sub3) = csubst t (sub2 ++ sub1 ++ sub3).
Proof.
  unfold csubst; sp.
  repeat (rw <- @csub2sub_app).
  apply lsubst_shift; sp; allrw in_app_iff; sp;
  try (allapply @in_csub2sub; sp).
  repeat (rw @dom_csub_eq); sp.
Qed.

Lemma cover_vars_shift {p} :
  forall t sub1 sub2 sub3,
    @cover_vars p t (sub1 ++ sub2 ++ sub3)
    -> cover_vars t (sub2 ++ sub1 ++ sub3).
Proof.
  sp; allrw @cover_vars_eq; sp; allrw subvars_eq.
  unfold subset; unfold subset in H; sp.
  apply_in_hyp pp.
  allrw @dom_csub_app; allrw in_app_iff; sp.
Qed.

Lemma lsubstc_shift {pp} :
  forall t sub1 sub2 sub3 w p,
  forall d : disjoint (dom_csub sub1) (@dom_csub pp sub2),
    lsubstc t w (sub1 ++ sub2 ++ sub3) p
    = lsubstc t w (sub2 ++ sub1 ++ sub3) (cover_vars_shift t sub1 sub2 sub3 p).
Proof.
  sp; unfold lsubstc.
  apply cterm_eq; simpl.
  apply csubst_shift; auto.
Qed.

Lemma lsubstc_shift_ex {pp} :
  forall t sub1 sub2 sub3 w p,
  forall d : disjoint (@dom_csub pp sub1) (dom_csub sub2),
    {p' : cover_vars t (sub2 ++ sub1 ++ sub3)
     & lsubstc t w (sub1 ++ sub2 ++ sub3) p
          = lsubstc t w (sub2 ++ sub1 ++ sub3) p'}.
Proof.
  sp.
  exists (cover_vars_shift t sub1 sub2 sub3 p).
  apply lsubstc_shift; sp.
Qed.


Fixpoint lsubst_sub {p} (sub1 sub2 : @Substitution p) : Substitution :=
  match sub1 with
    | nil => nil
    | (v,t) :: sub => (v,lsubst t sub2) :: lsubst_sub sub sub2
  end.

Lemma lsubst_sub_cons {p} :
  forall v t sub1 sub2,
    @lsubst_sub p ((v, t) :: sub1) sub2
    = (v, lsubst t sub2) :: lsubst_sub sub1 sub2.
Proof.
  sp.
Qed.

Lemma lsubst_sub_nil {p} :
  forall sub, @lsubst_sub p [] sub = [].
Proof.
  sp.
Qed.

Hint Rewrite @lsubst_sub_nil.

Lemma sub_find_lsubst_sub_if_some {p} :
  forall v t sub1 sub2,
    @sub_find p sub1 v = Some t
    -> sub_find (lsubst_sub sub1 sub2) v = Some (lsubst t sub2).
Proof.
  induction sub1; simpl; sp; allsimpl.
  remember (beq_var a0 v); destruct b.
  inversion H; subst; sp.
  apply IHsub1 with (sub2 := sub2) in H; sp.
Qed.

Lemma sub_find_lsubst_sub_if_none {p} :
  forall v sub1 sub2,
    @sub_find p sub1 v = None
    -> sub_find (lsubst_sub sub1 sub2) v = None.
Proof.
  induction sub1; simpl; sp; allsimpl.
  remember (beq_var a0 v); destruct b; sp.
Qed.

Lemma in_lsubst_sub_implies {p} :
  forall v t sub1 sub2,
    LIn (v, t) (@lsubst_sub p sub1 sub2)
    -> {u : NTerm $ (LIn (v, u) sub1 # t = lsubst u sub2)}.
Proof.
  induction sub1; simpl; sp; allsimpl; sp; inj.

  exists a; sp.

  apply_in_hyp pp; sp; subst.
  exists u; sp.
Qed.

Lemma sub_filter_lsubst_sub {p} :
  forall sub1 sub2 l,
    sub_filter (@lsubst_sub p sub1 sub2) l
    = lsubst_sub (sub_filter sub1 l) sub2.
Proof.
  induction sub1; simpl; sp; allsimpl.
  destruct (memvar a0 l); sp; simpl.
  rw IHsub1; sp.
Qed.

Theorem disjoint_bv_sub_ot {p} :
  forall o lbt lv nt sub, disjoint_bv_sub (@oterm p o lbt) sub 
    -> LIn (bterm lv nt) lbt 
    -> disjoint_bv_sub nt (sub_filter sub lv).
Proof. unfold disjoint_bv_sub. introv Hdis Hin. introv Hins. 
   apply in_sub_filter in Hins. repnd. apply Hdis in Hins0. simpl in Hins0. 
   eapply disjoint_lbt_bt2 in Hins0. Focus 2. eauto. repnd; auto. 
Qed.

(*
Lemma lsubst_aux_sub_filter2 {p} :
  forall t sub l,
    @disjoint_bv_sub p t sub
    -> disjoint (free_vars t) l
    -> lsubst_aux t (sub_filter sub l) = lsubst_aux t sub.
Proof.
  nterm_ind1 t as [v| o lbt Hind] Case; simpl; introv Hbv Hd.

  - Case "vterm".
    remember (sub_find (sub_filter sub l) v); symmetry in Heqo; destruct o.
    rw @sub_find_sub_filter_some in Heqo; sp.
    allrw; sp.
    rw @sub_find_sub_filter_none in Heqo; sp.
    allrw; sp.
    allrw disjoint_singleton_l; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps. intros bt Hin.
    destruct bt as [lv nt]; simpl.
    pose proof (sub_eta_length (sub_filter sub l)) as X99X.

    f_equal. rw @sub_filter_swap.
    rw <- @sub_filter_app_r.
    rw @sub_filter_app_as_remove_nvars.
    rw @sub_filter_app_r.
    rewrite Hind with (lv := lv); sp; [
      eapply disjoint_bv_sub_ot in Hbv;eauto |].

    eapply disjoint_flat_map_l in Hd;eauto.
    allsimpl. apply disjoint_remove_nvars_l in Hd.
    sp.
Qed.
*)

Lemma lsubst_aux_sub_filter3 {p} :
  forall t sub vs,
    disjoint (remove_nvars vs (@dom_csub p sub)) (free_vars t)
    -> lsubst_aux t (sub_filter (csub2sub sub) vs) = t.
Proof.
  introv disj.
  apply lsubst_aux_trivial; introv i.
  apply in_sub_filter in i; repnd.
  dands; try (complete (apply in_csub2sub in i0; sp)).
  introv j.
  generalize (disj v); intro imp.
  dest_imp imp hyp.
  rw in_remove_nvars; sp.
  rw <- @dom_csub_eq.
  apply in_dom_sub in i0; sp.
Qed.

Lemma lsubst_sub_filter2 {p}:
  forall t sub l,
    @disjoint_bv_sub p t sub
    -> disjoint (free_vars t) l
    -> lsubst t (sub_filter sub l) = lsubst t sub.
Proof.
  intros. change_to_lsubst_aux4.
  apply lsubst_aux_sub_filter;try(sp;fail);
  try(rw @disjoint_sub_as_flat_map;disjoint_reasoning).
  apply @disjoint_sym. rw <- @disjoint_sub_as_flat_map.
  apply sub_filter_sat.
  rw @disjoint_sub_as_flat_map. disjoint_reasoning.
Qed.

Ltac disjoint_flat2 := allunfold disjoint_bv_sub; allunfold sub_range_sat; allsimpl;
  match goal with
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint (flat_map ?f (range ?sub)) ?l)  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) H2 _ _ H))
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint ?l (flat_map ?f (range ?sub)))  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) 
  (disjoint_sym_impl _ _ _ H2) _ _ H))
| [ H:( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) |- _ ] =>
      apply disjoint_sub_as_flat_map in H
| [ |- ( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) ] =>
      apply disjoint_sub_as_flat_map
end.

Lemma lsubst_sub_sub_filter_disjoint2 {p} :
  forall sub1 sub2 l,
    disjoint (flat_map bound_vars (range sub1)) 
            (flat_map free_vars (@range p sub2))
   -> disjoint l (flat_map free_vars (range sub1))
   ->  lsubst_sub (sub_filter sub1 l) (sub_filter sub2 l)
       = lsubst_sub (sub_filter sub1 l) sub2.
Proof.
  induction sub1 as [|(v,t) sub Hind]; introv H1dis H2dis; allsimpl;sp.
  rw memvar_dmemvar.
  cases_ifn Hm; allsimpl; rw Hind; disjoint_reasoningv;[].
  f_equal; f_equal;[].
  rw @lsubst_sub_filter2;sp; disjoint_reasoningv;[].
  disjoint_flat. disjoint_reasoningv.
Qed.


Lemma lsubst_sub_sub_filter_disjoint {p} :
  forall sub1 sub2 l,
    (forall v u, LIn (v, u) sub2 -> @isprogram p u)
    -> (forall v u, LIn (v, u) sub1 -> disjoint (free_vars u) l)
    -> lsubst_sub (sub_filter sub1 l) (sub_filter sub2 l)
       = lsubst_sub (sub_filter sub1 l) sub2.
Proof.
  intros. apply lsubst_sub_sub_filter_disjoint2;sp;
  disjoint_flat;
  change_to_lsubst_aux4;
  disjoint_reasoningv.
Qed.

Lemma sub_mk_renames_disjoint {p} :
  forall l1 l2,
    disjoint l1 l2
    -> @sub_mk_renames p l1 l2 = (l1, []).
Proof.
  induction l1; simpl; sp.
  allrw disjoint_cons_l; sp.
  apply_in_hyp pp.
  allrw.
  remember (memvar a l2); symmetry in Heqb; destruct b; sp.
  allrw fold_assert.
  rw assert_memvar in Heqb; sp.
Qed.

Lemma sub_mk_renames2_disjoint {p} :
  forall l1 l2 lva,
    disjoint l1 l2
    -> @sub_mk_renames2 p l1 l2 lva = (l1, []).
Proof.
  induction l1; simpl; try (complete sp); introv d.
  allrw disjoint_cons_l; exrepnd.
  apply IHl1 with (lva:=lva) in d0.
  allrw; boolvar; sp.
Qed.

(** This is similar to bvar_renamings_subst_isprogram (same conclusion)
 * but it has a diffrent hypothesis. *)
(** not needed anymore *)
Lemma bvar_renamings_subst_disjoint_bound_vars {p} :
  forall l sub nt,
    (forall v u, LIn (v, u) sub -> disjoint (@free_vars p u) l)
    -> bvar_renamings_subst l nt sub
       = (l, [], sub_filter sub l).
Proof.
  unfold bvar_renamings_subst; introv k.
  rw @sub_mk_renames2_eta; simpl.
  remember (sub_free_vars (sub_filter sub l)).

  assert (disjoint l0 l)
    as d
      by (subst; unfold disjoint; sp;
          allrw @in_sub_free_vars_iff; sp;
          allrw @in_sub_filter; sp;
          apply_in_hyp q;
          unfold disjoint in q;
          discover; sp).

  rw @sub_mk_renames2_disjoint; sp.
  apply disjoint_sym; sp.
Qed.

Ltac dsub_find sn :=
  match goal with
    | [  |- context[sub_find ?s ?v] ] =>
      let sns := fresh sn "s" in
      remember (sub_find s v) as sn;
        destruct sn as [sns |]
    | [ H: context[sub_find ?s ?v] |- _ ] =>
      let sns := fresh sn "s" in
      remember (sub_find s v) as sn;
        destruct sn as [sns |]
  end.

Lemma lsubst_aux_app {p} :
  forall t sub1 sub2,
    disjoint (flat_map bound_vars (range sub1)) (flat_map free_vars (@range p sub2))
    -> disjoint_bv_sub t sub1
    -> disjoint_bv_sub t sub2
    -> lsubst_aux (lsubst_aux t sub1) sub2 = lsubst_aux t (lsubst_sub sub1 sub2 ++ sub2).
Proof.
  nterm_ind1 t as [v|o lbt Hind] Case; simpl; introns Hss; auto.

  - Case "vterm".
    rw @sub_find_app.
    dsub_find s1v; symmetry in Heqs1v.
    + applydup @sub_find_some in Heqs1v.
      apply @sub_find_lsubst_sub_if_some with (sub2 := sub2) in Heqs1v.
      rw Heqs1v; sp. revert Heqs1v. change_to_lsubst_aux4; sp.
      disjoint_flat.
    + apply @sub_find_lsubst_sub_if_none with (sub2 := sub2) in Heqs1v.
      rw Heqs1v ; simpl; sp.

  - Case "oterm".
    f_equal. rw map_map.
    apply eq_maps. intros bt Hin.
    destruct bt as [lv nt]. unfold compose. simpl.
    f_equal.
    rw @sub_filter_app.
    rw @sub_filter_lsubst_sub.
    assert (lsubst_sub (sub_filter sub1 lv) (sub_filter sub2 lv)
            = lsubst_sub (sub_filter sub1 lv) sub2) as eq.
    + apply lsubst_sub_sub_filter_disjoint2; sp.
      disjoint_flat. disjoint_reasoning.
    + rw <- eq. sp. rewrite Hind with (lv := lv); sp;
      disjoint_flat;
      disjoint_flat_sf; disjoint_reasoningv.
Qed.


Lemma simple_lsubst_aux_lsubst_aux {p} :
  forall t sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> disjoint (free_vars u) (bound_vars t))
    -> (forall v u, LIn (v, u) sub2 -> @isprogram p u)
    -> lsubst_aux (lsubst_aux t sub1) sub2
       = lsubst_aux t ((lsubst_sub sub1 sub2) ++ sub2).
Proof.
  introv H1 H2. apply lsubst_aux_app; disjoint_flat; disjoint_reasoningv;
    change_to_lsubst_aux4; disjoint_reasoningv.
Qed.

Lemma disjoint_bv_sub_lsubst_sub {p} :
  forall t sub1 sub2,
  disjoint_bv_sub t sub1
  -> @prog_sub p sub2
  -> disjoint_bv_sub t (lsubst_sub sub1 sub2).
Proof.
  introv H1b H2b.
  unfold sub_range_sat. introv Hin. apply in_lsubst_sub_implies in Hin.
  exrepnd.
  subst. introv Hin.
  rw @isprogram_lsubst2 in Hin;[|sp;fail]. apply in_remove_nvars in Hin. repnd.
  apply H1b in Hin1. apply Hin1 in Hin0. sp.
Qed.

Lemma simple_lsubst_lsubst {p} :
  forall t sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> disjoint (free_vars u) (bound_vars t))
    -> (forall v u, LIn (v, u) sub2 -> @isprogram p u)
    -> lsubst (lsubst t sub1) sub2
       = lsubst t ((lsubst_sub sub1 sub2) ++ sub2).
Proof.
  introv Hd Hp.
  assert (disjoint_bv_sub t (lsubst_sub sub1 sub2 ++ sub2)).
  apply sub_app_sat;sp.
  - apply disjoint_bv_sub_lsubst_sub;sp.
  - apply prog_sub_disjoint_bv_sub;sp.
  - change_to_lsubst_aux4. apply simple_lsubst_aux_lsubst_aux; [|sp].
    apply disjoint_sub_as_flat_map;sp. disjoint_reasoning.
Qed.

Lemma lsubstc_eq_if_csubst {p} :
  forall t1 t2 w1 w2 s1 s2 p1 p2,
    csubst t1 s1 = @csubst p t2 s2
    -> lsubstc t1 w1 s1 p1 = lsubstc t2 w2 s2 p2.
Proof.
  unfold lsubstc; sp.
  apply cterm_eq; simpl; auto.
Qed.

Lemma csubst_eq_if_lsubst {p} :
  forall t1 t2 s1 s2,
    lsubst t1 (csub2sub s1) = lsubst t2 (@csub2sub p s2)
    -> csubst t1 s1 = csubst t2 s2.
Proof.
  unfold csubst; sp.
Qed.

(*
Lemma simple_csubst_lsubst :
  forall t sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> disjoint (free_vars u) (bound_vars t))
    -> csubst (lsubst t sub1) sub2
       = csubst t ((lsubst_sub sub1 sub2) ++ sub2).
Proof.
*)

(* keeps the variables from vars *)
Fixpoint sub_keep {p} (sub : @Substitution p) (vars : list NVar) : Substitution :=
  match sub with
  | nil => nil
  | (v, t) :: xs =>
      if memvar v vars
      then (v, t) :: sub_keep xs vars
      else sub_keep xs vars
  end.

Lemma sub_find_sub_keep_some {p} :
  forall sub vs v t,
    sub_find (@sub_keep p sub vs) v = Some t
    <=> sub_find sub v = Some t
        # LIn v vs.
Proof.
  induction sub; simpl; sp.
  split; sp.
  boolvar; simpl; allrw; boolvar; sp; split; sp.
Qed.

Lemma sub_find_sub_keep_none {p} :
  forall sub vs v,
    sub_find (@sub_keep p sub vs) v = None
    <=> sub_find sub v = None
        [+] ! LIn v vs.
Proof.
  induction sub; simpl; sp.
  boolvar; simpl; allrw; boolvar; sp; split; sp.
Qed.

Lemma sub_filter_sub_keep {p} :
  forall sub vs1 vs2,
    sub_filter (@sub_keep p sub vs1) vs2
    = sub_keep (sub_filter sub vs2) vs1.
Proof.
  induction sub; simpl; sp.
  remember (memvar a0 vs1); remember (memvar a0 vs2).
  symmetry in Heqb; symmetry in Heqb0.
  destruct b; destruct b0; allsimpl;
  try (rw Heqb); try (rw Heqb0); sp.
  rw IHsub; sp.
Qed.

Theorem in_sub_keep {p} :
  forall (sub : @Substitution p) (v : NVar) (t : NTerm)  (vars : list NVar),
    LIn (v, t) (sub_keep sub vars) <=> LIn (v, t) sub # LIn v vars.
Proof.
  induction sub. simpl; split; sp.
  simpl. destruct a as [v t]. introv.
  cases_if as Hmv;
    (applydup assert_memvar in Hmv || applydup assert_memvar_false in Hmv) ; simpl;
    split; introv Hor.
  - invertsn Hor. invertsn Hor; split; auto.  apply IHsub in Hor; repnd; auto.
  - inverts Hor as Hor Hin. invertsn Hor. invertsn Hor. left; reflexivity.   right. apply IHsub;  auto.
  - apply IHsub in Hor. repnd. split; trivial. right; trivial.
  - inverts Hor as Hor Hin. invertsn Hor. invertsn Hor. destruct Hmv0; trivial. apply IHsub; split; trivial.
Qed.

(* Theorem memvar2 (v:NVar) (vs:list NVar) : {LIn v vs}  + {! LIn v vs} := *)



Theorem sub_keep_nest {p} :
  forall  sub vs1 vs2,
    (forall v, LIn v vs2 -> LIn v vs1 [+] ! LIn v (@dom_sub p sub))
    -> sub_keep (sub_keep sub vs1) vs2 =sub_keep sub vs2.
Proof.
  induction sub as [| (hv,ht) sub]; introv Hin; [reflexivity | allsimpl].
  simpl. cases_if as Hmv1; cases_if as Hmv2; simpl; try rw Hmv1; try rw Hmv2; sp;
         (applydup assert_memvar in Hmv1 || applydup assert_memvar_false in Hmv1);
         (applydup assert_memvar in Hmv2 || applydup assert_memvar_false in Hmv2); sp;
         [f_equal | trivial | trivial | trivial] ;
         try(apply IHsub; introv Hinv; applydup Hin in Hinv; invertsn Hinv0;
             [left ;trivial | right; apply not_over_or in Hinv0; repnd; trivial]).
  apply Hin in Hmv3. invertsn Hmv3. apply Hmv0 in Hmv3; sp.
  apply not_over_or in Hmv3. repnd. destruct Hmv4. reflexivity.
Qed.

Lemma simple_lsubst_aux_trim {p} :
  forall t sub,
    (forall v u, LIn (v, u) sub -> disjoint (@free_vars p u) (bound_vars t))
    -> lsubst_aux t sub = lsubst_aux t (sub_keep sub (free_vars t)).
Proof.
  nterm_ind t Case;  introv Hdis; auto.
  Case "vterm". simpl.
    cases  (sub_find sub n) as Heqs.
    assert (sub_find (sub_keep sub [n]) n = Some n0) as Heqk.
    apply sub_find_sub_keep_some; split; simpl; auto.
    rw Heqk; reflexivity.
    assert (sub_find (sub_keep sub [n]) n = None) as Heqk.
    apply sub_find_sub_keep_none. left; trivial.
    rw Heqk; reflexivity.

  Case "oterm". simpl.  f_equal.
    apply eq_maps. intros bt Hin.
    destruct bt as [lv nt].
    simpl.
    repeat (rw bvar_renamings_subst_disjoint_bound_vars).

    repeat (rw app_nil_l); simpl.
    f_equal. 
    rw @sub_filter_sub_keep. 
    symmetry. 
    rewrite H with (lv := lv); eauto. Focus 2.
       introv Hink. rw @in_sub_keep in Hink. repnd. apply in_sub_filter in Hink0. repnd. 
       apply Hdis in Hink1. simpl in Hink1. apply disjoint_sym in Hink1;rw disjoint_flat_map_l in Hink1.  
       apply Hink1 in Hin. simpl in Hin. rw disjoint_app_l in Hin. repnd; apply disjoint_sym. trivial. 

       assert( (sub_keep (sub_keep (sub_filter sub lv) 
        (flat_map free_vars_bterm lbt)) (free_vars nt)) =
           sub_keep (sub_filter sub lv) (free_vars nt)) as Hskeq. 
       + apply sub_keep_nest. introv Hinf. destruct (in_nvar_list_dec v lv). 
          * right. rw <- @dom_sub_sub_filter. intro HC. apply in_remove_nvars in HC. sp. 
          * left. apply lin_flat_map. eexists; split; eauto. simpl. apply in_remove_nvars; split; trivial.  
       + rw Hskeq. 
           symmetry. eapply H; eauto. 
           introv Hinf. apply in_sub_filter in Hinf. repnd. apply  Hdis in Hinf0. 
           simpl in Hinf0. apply disjoint_sym in Hinf0. rw disjoint_flat_map_l in Hinf0. 
           apply Hinf0 in Hin. simpl in Hin. rw disjoint_app_l in Hin. repnd; apply disjoint_sym. trivial. 
Qed.

Lemma sub_keep_sat {p} :  forall P sub lv,
  @sub_range_sat p sub P
  -> sub_range_sat (sub_keep sub lv) P.
Proof. introv Hall hsub. apply in_sub_keep in hsub. repnd.
  apply Hall in hsub0; auto.
Qed.


Lemma simple_lsubst_trim {p} :
  forall t sub,
    (forall v u, LIn (v, u) sub -> disjoint (@free_vars p u) (bound_vars t))
    -> lsubst t sub = lsubst t (sub_keep sub (free_vars t)).
Proof.
  introv Hd. duplicate Hd as Hdd.
  apply sub_keep_sat with (lv:=(free_vars t))in Hd.
  change_to_lsubst_aux4.
  apply simple_lsubst_aux_trim;try(sp;fail);
  try(apply disjoint_sub_as_flat_map;disjoint_reasoning).
Qed.


Definition disjoint_bv2_sub {p} (nt1 nt2 : @NTerm p) (sub: @Substitution p) :=
  forall (v : NVar) (t : NTerm),
    LIn (v, t) sub
    -> disjoint (free_vars t) (bound_vars nt1 ++ bound_vars nt2).

Theorem wf_sub_filter {p} :
  forall lv sub, @wf_sub p sub -> wf_sub (sub_filter sub lv).
Proof.
  unfold wf_sub; introv s.
  introv Hin.
  allrw @in_sub_filter; exrepnd.
  apply s in Hin0; sp.
Qed.

Theorem wf_sub_keep {p} : forall lv sub, @wf_sub p sub -> wf_sub (sub_keep sub lv).
Proof.
  unfold wf_sub; introv s.
  introv Hin.
  allrw @in_sub_keep; exrepnd.
  apply s in Hin0; sp.
Qed.


(** TODO : use the stronger lemma free_vars_lsubst_aux2 for a shorter
    and more maintainable proof *)
Theorem free_vars_lsubst_aux {p} :
  forall nt sub,
    @disjoint_bv_sub p nt sub
    -> forall v,
         LIn v (free_vars (lsubst_aux nt sub))
         -> LIn v (free_vars nt)
            [+] {v' : NVar
                 $ {t : NTerm
                 $ LIn (v',t) sub # LIn v' (free_vars nt) # LIn v (free_vars t)}}.
Proof. nterm_ind1 nt as [vn|o lbt Hind] Case; introv Hdis Hin; auto.
   Case "vterm". induction sub as [| (vs,ts) sub].
   - rw @lsubst_aux_nil in Hin. left;auto.
   - destruct (eq_var_dec vn vs) as [? | Hneq];
      subst;simpl in Hin;
      ((rw <- beq_var_refl in Hin;auto)
          || (rw not_eq_beq_var_false in Hin;auto)).
      + right. exists vs ts. sp; auto.
      + cases (sub_find sub vn) as Hf.
          * applydup @sub_find_some in Hf.
             right; exists vn n; split; auto. right;auto. simpl. split; auto.
          * left; auto.
  - Case "oterm".
    simpl in Hin. rw lin_flat_map in Hin.
    destruct Hin as [bt' Hin]. repnd. apply in_map_iff in Hin0.
    destruct Hin0 as [bt Hin0]. repnd. subst. destruct bt as [lv nt].
    simpl in Hin.
    simpl in Hin. rw in_remove_nvars in Hin. repnd.
    apply Hind with (lv:=lv) in Hin0; auto.
    destruct Hin0 as [Hl | Hr].
    + left. simpl. apply lin_flat_map. eexists; split; eauto. simpl.
      apply in_remove_nvars. split; auto.
    + right. parallel vs Hr. parallel ts Hr. repnd. sp;auto.
      * rw @in_sub_filter in Hr0. repnd; auto.
      * simpl. apply lin_flat_map. eexists; split; eauto. simpl.
        apply in_remove_nvars. split; auto. rw @in_sub_filter in Hr0.
        repnd; auto.
    + eapply disjoint_bv_sub_ot in Hdis; eauto.
Qed.

Theorem free_vars_lsubst {p} :
  forall nt sub,
    @disjoint_bv_sub p nt sub
    -> forall v,
         LIn v (free_vars (lsubst nt sub))
         -> LIn v (free_vars nt)
            [+] {v' : NVar
                 $ {t : NTerm
                 $ LIn (v',t) sub # LIn v' (free_vars nt) # LIn v (free_vars t)}}.
Proof.
  introns XX. change_to_lsubst_aux4.
  apply free_vars_lsubst_aux;try(sp;fail).
  try(rw @disjoint_sub_as_flat_map;disjoint_reasoning).
  revert XX0. change_to_lsubst_aux4.
  sp.
Qed.


Theorem free_vars_lsubst_closed {p} : forall nt sub, @wf_sub p sub
  -> disjoint_bv_sub nt sub
  -> prog_sub sub
  -> subvars (free_vars (lsubst nt sub)) (free_vars nt).
Proof.
  introv Hwf Hdis Hcl. apply subvars_prop. intros v Hin.
  apply @free_vars_lsubst with (v:=v )in Hdis; auto.
  dorn Hdis; auto. exrepnd. apply Hcl in Hdis0.
  inverts Hdis0 as  Hpr ?. rw Hpr in Hdis1. inverts Hdis1.
Qed.

 Lemma simple_lsubst_trim2 {p} :
  forall t sub lv,
    @disjoint_bv_sub p t sub
    -> subvars (free_vars t) lv
    -> lsubst t sub = lsubst t (sub_keep sub lv).
Proof.
  introv Hdis Hsub.
  rw @simple_lsubst_trim; auto.
  symmetry. rw @simple_lsubst_trim; auto.
  rw @sub_keep_nest; try reflexivity.
  intros; left. rw subvars_prop in Hsub. auto.
  introv Hin. rw @in_sub_keep in Hin. repnd.
  apply Hdis in Hin0; auto.
Qed.



Lemma csubst_trivial {p} :
  forall t sub,
    disjoint (@dom_csub p sub) (free_vars t)
    -> csubst t sub = t.
Proof.
  sp.
  unfold csubst.
  apply lsubst_trivial; sp.
  allapply @in_csub2sub; sp.
  unfold disjoint in H.
  apply_in_hyp pp; sp.
  rewrite <- dom_csub_eq.
  allapply @in_dom_sub; sp.
Qed.

Lemma sub_find_none_if {p} :
  forall sub v,
    ! LIn v (@dom_sub p sub)
    -> sub_find sub v = None.
Proof.
  intros.
  apply sub_find_none_iff; auto.
Qed.

Lemma lsubst_sub_trivial_closed1 {p} :
  forall sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> isprogram u)
    -> (forall v u, LIn (v, u) sub2 -> @isprogram p u)
    -> lsubst_sub sub1 sub2 = sub1.
Proof.
  induction sub1; simpl; try (complete sp); introv k1 k2.
  destruct a as [a0 a]; allsimpl.
  rewrite lsubst_trivial; introv.
  rewrite IHsub1; sp.
  apply k1 with (v := v); sp.
  introv i; dands.
  apply k2 with (v := v); sp.
  generalize (k1 a0 a); intros k.
  dest_imp k hyp.
  unfold isprogram, closed in k; destruct k as [c w].
  rw c; sp.
Qed.

Lemma cover_vars_cvterm1 {p} :
  forall v t u,
    cover_vars (@get_cvterm p [v] t) [(v, u)].
Proof.
  destruct t; sp; simpl.
  rw @isprog_vars_eq in i; sp.
Qed.

Lemma substc_eq_lsubstc {p} :
  forall u v t,
    @substc p u v t
    = lsubstc (get_cvterm [v] t)
              (wf_cvterm [v] t)
              [(v, u)]
              (cover_vars_cvterm1 v t u).
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.

Lemma lsubst_sub_singleton {p} :
  forall x t sub,
    @lsubst_sub p [(x, t)] sub = [(x, lsubst t sub)].
Proof.
  sp.
Qed.

Lemma csub2sub_cons {p} :
  forall x a s,
    @csub2sub p ((x,a) :: s) = (x, get_cterm a) :: csub2sub s.
Proof.
  sp.
Qed.

Lemma csub_filter_snoc1 {p} :
  forall sub v t,
    @csub_filter p (snoc sub (v, t)) [v]
    = csub_filter sub [v].
Proof.
  sp.
  induction sub; sp; simpl.
  remember (memvar v [v]); destruct b; sp.
  symmetry in Heqb.
  rw not_of_assert in Heqb.
  rw assert_memvar in Heqb; allsimpl.
  rw not_over_or in Heqb; sp.
  destruct (memvar a0 [v]); sp.
  rewrite IHsub; sp.
Qed.

Lemma csub_filter_app_r {p} :
  forall sub vs1 vs2,
    @csub_filter p sub (vs1 ++ vs2)
    = csub_filter (csub_filter sub vs1) vs2.
Proof.
  induction sub; simpl; sp.
  rewrite memvar_app.
  destruct (memvar a0 vs1); simpl.
  apply IHsub.
  destruct (memvar a0 vs2); simpl.
  apply IHsub.
  rewrite IHsub; auto.
Qed.

Lemma csub_filter_swap {p} :
  forall l1 l2 sub,
    csub_filter (@csub_filter p sub l1) l2
    = csub_filter (csub_filter sub l2) l1.
Proof.
  induction sub; simpl; sp.
  remember (memvar a0 l1); destruct b; remember (memvar a0 l2); destruct b; simpl; sp.
  rw <- Heqb; sp.
  rw <- Heqb0; sp.
  rw <- Heqb; sp.
  rw <- Heqb0; sp.
  rw IHsub; sp.
Qed.

Lemma cover_vars_upto_eq_dom_csub {p} :
  forall t s1 s2 vs,
    cover_vars_upto t (csub_filter s1 vs) vs
    -> dom_csub s1 = @dom_csub p s2
    -> cover_vars_upto t (csub_filter s2 vs) vs.
Proof.
  unfold cover_vars_upto; sp.
  allrw subvars_prop; sp.
  apply_in_hyp pp.
  allrw in_app_iff; sp.
  allrw @dom_csub_csub_filter.
  allrw in_remove_nvars; sp.
  right; sp.
  rewrite <- H0; sp.
Qed.

Lemma sub_find_varsub {p} :
  forall lvo lvn vo vnt,
    sub_find (var_ren lvo  lvn) vo = Some vnt
    -> {vn : NVar $ vnt = @vterm p vn # LIn (vo,vn) (combine lvo lvn)}.
Proof.
  induction lvo as [| hvo  tlvo Hind]; introv Hsome;
  [inverts Hsome | ]. applydup @sub_find_some in Hsome.
  apply in_combine in Hsome0. repnd. apply in_map_iff in Hsome0.
  exrepnd.
  destruct lvn.
  inverts Hsome0. allsimpl.
  dorn Hsome1; subst. eexists; split; eauto. left. f_equal.
  rewrite <- beq_var_refl in Hsome. inverts Hsome. reflexivity.
  cases_if in Hsome as hbeq. invertsn Hsome.
  eexists; split; eauto. left. f_equal. apply beq_var_eq; auto.
  pose proof (Hind _ _ _ Hsome) as Hinds. clear Hind.
  exrepnd. exists vn. split; auto.
Qed.



Definition isvarc {p} (nt: @NTerm p) := {v : NVar $ nt = vterm v}.

Definition allvars_sub {p} (sub: @Substitution p) :=
  sub_range_sat sub isvarc.

Lemma sub_find_sat {p} : forall P sub vo vnt,
  @sub_range_sat p sub P
  -> sub_find sub vo = Some vnt
  -> P vnt.
Proof. introv Hall hsub. apply sub_find_some in hsub.
  applydup Hall in hsub. exrepnd. subst.  auto.
Qed.

Lemma sub_find_allvars {p} : forall sub vo vnt,
  allvars_sub sub
  -> sub_find sub vo = Some vnt
  -> {vn : NVar $ vnt = @vterm p vn}.
Proof. exact (sub_find_sat isvarc).
Qed.


Lemma sub_filter_allvars {p} :  forall sub lv,
  @allvars_sub p sub
  -> allvars_sub (sub_filter sub lv).
Proof. exact (sub_filter_sat isvarc).
Qed.


Definition get_sub_dom_vars {p} sub (pall: @allvars_sub p sub) : list NVar.
  refine (gmap sub (fun (t : NVar * NTerm) (p : LIn t sub) =>
                      projT1 (pall (fst t) (snd t) _))).
  destruct t. simpl. auto.
Defined.




Lemma sub_mk_renames_allvars {p} :
  forall lv1 lv2 lv sub,
    (lv, sub) = (@sub_mk_renames p lv1 lv2)
    -> allvars_sub sub.
Proof. induction lv1 as [|v lv1 Hind]; introv Heq.
  allsimpl. invertsn Heq. introv Hin. inverts Hin.
  allsimpl. remember (sub_mk_renames lv1 lv2) as recv.
  destruct recv. apply Hind in Heqrecv.
  cases_if in Heq; inverts Heq; trivial.
  introv Hin. allsimpl. dorn Hin. inverts Hin. eexists; eauto.
  apply Heqrecv in Hin; trivial.
Qed.


Lemma sub_mk_renames2_allvars {p} : forall lv1 lv2 lv sub lva,
  (lv, sub) = (@sub_mk_renames2 p lv1 lv2 lva)
   -> allvars_sub sub.
Proof. induction lv1 as [|v lv1 Hind]; introv Heq.
  allsimpl. invertsn Heq. introv Hin. inverts Hin.
  allsimpl. remember (sub_mk_renames2 lv1 lv2 lva) as recv.
  destruct recv. apply Hind in Heqrecv.
  cases_if in Heq; inverts Heq; trivial.
  introv Hin. allsimpl. dorn Hin. inverts Hin. eexists; eauto.
  apply Heqrecv in Hin; trivial.
Qed.

Lemma  bvar_renamings_subst_vars {p} :  forall lv nt sub sub1 sub2 lv',
   @allvars_sub p sub
   -> ((lv', sub1), sub2)=(bvar_renamings_subst lv nt sub)
   -> (allvars_sub sub1) # (allvars_sub sub2).
Proof. introv Hall Heq. allunfold @bvar_renamings_subst.
  remember (sub_mk_renames2 lv (sub_free_vars (sub_filter sub lv)) 
   (dom_sub (sub_filter sub lv) ++ all_vars nt)) as smr.
  destruct smr.
invertsn Heq. split; [ |apply sub_filter_allvars; trivial; fail].
  apply sub_mk_renames2_allvars in Heqsmr; auto.
Qed.


 Lemma lsubst_aux_allvars_preserves_size {p} : forall nt sub,
    @allvars_sub p sub
   -> size (lsubst_aux nt sub) = size nt.
Proof. nterm_ind1 nt as [v|o lbt Hind] Case; introv Hall; auto.
  Case "vterm". simpl.
    cases (sub_find sub v ) as Hsf; try reflexivity.
    apply sub_find_allvars in Hsf; trivial. exrepnd. subst; auto.
  Case "oterm". simpl. f_equal. f_equal.
    rewrite map_map. apply eq_maps. intros bt Hin.
    destruct bt as [lv nt]. unfold compose. simpl.
    repnd. eapply Hind; eauto. apply sub_filter_sat;sp.
Qed.


Theorem allvars_combine {p} : forall lvo lvn,
    allvars_sub (@var_ren p lvo lvn).
Proof. introv Hin. apply in_combine in Hin. repnd.
  apply in_map_iff in Hin. exrepnd. exists a; auto. 
Qed.

Lemma lsubst_aux_allvars_preserves_size2 {p} : forall nt lvo lvn,
   size (lsubst_aux nt (@var_ren p lvo lvn)) = size nt.
Proof.
  intros. apply lsubst_aux_allvars_preserves_size.
  apply allvars_combine.
Qed.

Theorem not_isvarc_ot {p} : forall op lbt,
  (isvarc (@oterm p op lbt)) <=> False.
Proof.
  split; try (sp; fail ). introv Hc. exrepnud Hc. inverts Hc0. 
Qed.

Theorem isvarc_lsubst_iff {p} : forall sub nt,
  @allvars_sub p sub
  -> (isvarc (lsubst nt sub) <=> isvarc nt).
Proof.
  destruct nt; introv Hal.
  - simpl. unfold lsubst. simpl. cases (sub_find sub n) as Hc.
    apply sub_find_allvars in Hc; auto. exrepnd. subst.
    split ;eexists; eauto.  apply t_iff_refl.
  - unfold lsubst.
    cases_if;simpl; allrw @not_isvarc_ot; apply t_iff_refl.
Qed.

Theorem isvarc_lsubst_vterm {p} : forall sub v,
  @allvars_sub p sub
  -> (isvarc (lsubst (vterm v) sub)).
Proof. intros.
  apply isvarc_lsubst_iff; auto.
  eexists; eauto.
Qed.


Theorem isvarc_lsubst_implies2 {p} : forall v nt sub,
  @allvars_sub p sub
  -> vterm v = (lsubst nt sub)
  -> isvarc nt.
Proof. intros. 
 assert (isvarc (lsubst nt sub)) as Hisv by (eexists; eauto).
 eapply isvarc_lsubst_iff; eauto. 
Qed.

Theorem isvarc_lsubst_ot {p} : forall v lbt sub o,
  @allvars_sub p sub 
     -> oterm o lbt = lsubst (vterm v) sub
     -> False.
Proof. introv Hall Heq. 
    assert (isvarc (@vterm p v)) as Hc by (eexists; eauto).
    apply (isvarc_lsubst_iff sub) in Hc; trivial.
    rw <- Heq in Hc. rw @not_isvarc_ot in Hc; sp.
Qed.


Lemma covered_app_weak_l {p} :
  forall t vs1 vs2,
    @covered p t vs1
    -> covered t (vs1 ++ vs2).
Proof.
  unfold covered; intros.
  allrw subvars_prop; sp.
  apply_in_hyp pp.
  allrw in_app_iff; sp.
Qed.

Lemma covered_app_weak_r {p} :
  forall t vs1 vs2,
    @covered p t vs2
    -> covered t (vs1 ++ vs2).
Proof.
  unfold covered; intros.
  allrw subvars_prop; sp.
  apply_in_hyp pp.
  allrw in_app_iff; sp.
Qed.

Lemma sub_find_some_implies_memvar_true {p} :
  forall sub v t,
    @sub_find p sub v = Some t
    -> memvar v (dom_sub sub) = true.
Proof.
  sp.
  apply sub_find_some in H.
  rewrite fold_assert.
  rw assert_memvar.
  apply in_dom_sub in H; auto.
Qed.

Lemma sub_find_none_implies_memvar_false {p} :
  forall sub v,
    @sub_find p sub v = None
    -> memvar v (dom_sub sub) = false.
Proof.
  sp.
  apply sub_find_none2 in H.
  rw not_of_assert.
  rw assert_memvar; auto.
Qed.

Fixpoint sub_keep_first {p} (sub : @Substitution p) (vars : list NVar) : Substitution :=
  match sub with
  | nil => nil
  | (v, t) :: xs =>
      if memvar v vars
      then (v, t) :: sub_keep_first xs (remove_nvar vars v)
      else sub_keep_first xs vars
  end.

Lemma sub_keep_first_nil_r {p} :
  forall sub,
    @sub_keep_first p sub [] = [].
Proof.
  induction sub; simpl; sp.
Qed.

Lemma sub_keep_first_singleton_r_some {p} :
  forall sub v t,
    @sub_find p sub v = Some t
    -> sub_keep_first sub [v] = [(v,t)].
Proof.
  induction sub; simpl; sp.
  rewrite remove_nvar_cons.
  rewrite memvar_singleton.
  rewrite remove_nvar_nil.
  destruct (eq_var_dec a0 v); subst.
  allrw <- beq_var_refl.
  inversion H; subst.
  rewrite sub_keep_first_nil_r; auto.
  rw not_eq_beq_var_false; auto.
  rw not_eq_beq_var_false in H; auto.
Qed.

Lemma sub_keep_first_singleton_r_none {p} :
  forall sub v,
    @sub_find p sub v = None
    -> sub_keep_first sub [v] = [].
Proof.
  induction sub; simpl; sp.
  rewrite remove_nvar_cons.
  rewrite memvar_singleton.
  rewrite remove_nvar_nil.
  destruct (eq_var_dec a0 v); subst.
  allrw <- beq_var_refl; sp.
  rw not_eq_beq_var_false; auto.
  rw not_eq_beq_var_false in H; auto.
Qed.

Lemma sub_filter_sub_keep_first_weak_in {p} :
  forall sub vs1 vs2 v,
    LIn v vs1
    -> sub_filter (@sub_keep_first p sub vs2) vs1
       = sub_filter (sub_keep_first sub (remove_nvar vs2 v)) vs1.
Proof.
  induction sub; simpl; sp.
  remember (memvar a0 (remove_nvar vs2 v)); symmetry in Heqb; destruct b;
  remember (memvar a0 vs2); symmetry in Heqb0; destruct b; simpl;
  remember (memvar a0 vs1); symmetry in Heqb1; destruct b; simpl; sp;
  allrw fold_assert;
  allrw not_of_assert;
  allrw assert_memvar;
  allrw in_remove_nvar; sp.

  - rewrite remove_nvar_comm; auto.

  - rewrite remove_nvar_comm.
    symmetry.
    rewrite <- IHsub; sp.

  - destruct (eq_var_dec a0 v); subst; sp.
    provefalse; apply Heqb; sp.

  - destruct (eq_var_dec a0 v); subst; sp.
    provefalse; apply Heqb; sp.
Qed.

Lemma sub_keep_first_sub_filter {p} :
  forall sub vs1 vs2,
    sub_keep_first (@sub_filter p sub vs1) vs2
    = sub_filter (sub_keep_first sub vs2) vs1.
Proof.
  induction sub; simpl; sp.
  remember (memvar a0 vs1); symmetry in Heqb; destruct b;
  remember (memvar a0 vs2); symmetry in Heqb0; destruct b; sp; simpl; allrw; sp.

  rw <- @sub_filter_sub_keep_first_weak_in; sp.
  allrw fold_assert; allrw assert_memvar; sp.
Qed.

Lemma in_sub_keep_first {p} :
  forall sub v vs t,
    LIn (v,t) (@sub_keep_first p sub vs)
    <=> (sub_find sub v = Some t # LIn v vs).
Proof.
  induction sub; simpl; sp.
  split; sp.

  destruct (eq_var_dec a0 v); subst;
  allrw <- beq_var_refl;
  allrw not_eq_beq_var_false; auto;
  try (remember (memvar v vs); symmetry in Heqb; destruct b);
  try (remember (memvar a0 vs); symmetry in Heqb; destruct b);
  allsimpl; rw IHsub; allrw in_remove_nvars; allsimpl; allrw not_over_or;
  split; sp; cpx.

  rw fold_assert in Heqb; rw assert_memvar in Heqb; auto.
  rw not_of_assert in Heqb; rw assert_memvar in Heqb; sp.
  rw not_of_assert in Heqb; rw assert_memvar in Heqb; sp.

  right; sp.
  right; sp.
Qed.

Lemma eqvars_free_vars_disjoint_aux {pp} :
  forall t : NTerm,
  forall sub : @Substitution pp,
    (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t))
    -> eqvars (free_vars (lsubst_aux t sub))
              (remove_nvars (dom_sub sub) (free_vars t)
               ++ sub_free_vars (sub_keep_first sub (free_vars t))).
Proof.
  nterm_ind t Case; simpl; intros; auto.

  - Case "vterm".
    remember (sub_find sub n); destruct o; symmetry in Heqo; simpl;
    rewrite remove_nvars_cons_r.
    + applydup @sub_find_some_implies_memvar_true in Heqo.
      rewrite Heqo0.
      rewrite remove_nvars_nil_r; simpl.
      applydup @sub_keep_first_singleton_r_some in Heqo.
      rewrite Heqo1; simpl.
      rewrite app_nil_r; auto.

    + applydup @sub_find_none_implies_memvar_false in Heqo.
      rewrite Heqo0.
      rewrite remove_nvars_nil_r.
      applydup @sub_keep_first_singleton_r_none in Heqo.
      rewrite Heqo1; simpl; sp.

  - Case "oterm".
    rewrite remove_nvars_flat_map.
    rewrite flat_map_map; unfold compose.

    rw eqvars_prop; sp.
    sp_iff SCase; intro.

    + SCase "->".

      allrw in_app_iff.
      allrw lin_flat_map; exrepd.
      destruct x0; allsimpl.

      allrw in_remove_nvars; sp.

      generalize (H n l1 l (sub_filter sub l1)); sp.
      dest_imp H1 hyp.
      sp.
      apply in_sub_filter in X; sp.
      apply H0 in X0.
      rw disjoint_flat_map_r in X0.
      apply X0 in l; allsimpl.
      rw disjoint_app_r in l; sp.

      rw eqvars_prop in H1.
      rw H1 in l2.
      allrw in_app_iff; sp.
      rw <- @dom_sub_sub_filter in l2.
      allrw in_remove_nvars; sp.

      left.
      exists (bterm l1 n); simpl; sp.
      allrw in_remove_nvars; sp.

      allrw @in_sub_free_vars_iff; sp.
      rewrite @sub_keep_first_sub_filter in p0.
      allrw @in_sub_filter; sp.
      allrw @in_sub_keep_first; sp.
      right.
      exists x0 t; sp.
      allrw @in_sub_keep_first; sp.
      rw lin_flat_map.
      exists (bterm l1 n); simpl; sp.
      rw in_remove_nvars; sp.

    + SCase "<-".

      allrw in_app_iff; sp; allrw lin_flat_map; exrepd;
      allrw in_remove_nvars; repd; allsimpl.

      destruct x0; allsimpl.
      allrw in_remove_nvars; sp.

      exists (bterm l1 n0); simpl; sp.
      rw in_remove_nvars; sp.
      generalize (H n0 l1 l (sub_filter sub l1)); sp.
      dest_imp H1 hyp; sp.
      allrw @in_sub_filter; sp.
      apply H0 in X0.
      allrw disjoint_flat_map_r.
      apply X0 in l; allsimpl.
      allrw disjoint_app_r; sp.

      rw eqvars_prop in H1.
      rw H1.
      rw in_app_iff.
      rw in_remove_nvars.
      rewrite <- dom_sub_sub_filter.
      rw in_remove_nvars.
      left; sp.


      allrw @in_sub_free_vars_iff; exrepd.
      allrw @in_sub_keep_first; sp.
      allrw lin_flat_map; sp.
      exists x1; sp.
      destruct x1; allsimpl.
      allrw in_remove_nvars; sp.

      generalize (H n l p0 (sub_filter sub l)); sp.
      dest_imp H1 hyp; sp.
      allrw @in_sub_filter; sp.
      apply H0 in X0.
      allrw disjoint_flat_map_r.
      apply X0 in p0; allsimpl.
      allrw disjoint_app_r; sp.

      allrw eqvars_prop.
      rw H1.
      rw in_app_iff.
      rw @in_sub_free_vars_iff; right.
      exists x0 t; sp.
      rw @in_sub_keep_first; sp.
      rw @sub_find_sub_filter_some; sp.
      applydup @sub_find_some in l1.
      apply H0 in l2.
      allrw disjoint_flat_map_r.
      apply l2 in p0; allsimpl.
      allrw disjoint_app_r; sp.
      unfold disjoint in p2.
      apply p2 in l0; sp.
Qed.






Theorem lmap_lapply_eq_implies: forall lv1 lvi1 lvo1 lv2 lvi2 lvo2,
         lvmap_lapply (combine lvi1 lvo1) lv1 
      = lvmap_lapply (combine lvi2 lvo2) lv2
              -> disjoint (lvo1++ lvo2) (lv1 ++ lv2)
              -> length lvi1=length lvo1
              -> length lvi2=length lvo2
              -> remove_nvars lvi1 lv1 = remove_nvars lvi2 lv2.
Proof.
   unfold lvmap_lapply. induction lv1 as [| v1 lv1 Hind]; introv Heq Hdis; auto.
   - simpl in Heq. symmetry in Heq. apply map_eq_nil in Heq. subst. 
      repeat( rewrite remove_nvars_nil_r). refl.
   - destruct lv2 as [| v2 lv2]; [ inverts Heq; fail | allsimpl].
     repeat(rewrite remove_nvars_cons_r). 
     repeat (rewrite memvar_dmemvar).
     apply disjoint_cons_r in Hdis. 
     rw disjoint_app_r in Hdis. 
     rw disjoint_cons_r in Hdis. 
     inverts Heq as Heq1 Heq2. unfold lmap_apply in Heq1.
       intros Hl1 Hl2. 
     destruct (lmap_find deq_nvar (combine lvi1 lvo1) v1)
          as [s1 | Hin1];
     [  destruct s1 as [b1 Hin1]; apply in_combine in Hin1 
        | rewrite combine_split in Hin1; auto; simpl];
     destruct (lmap_find deq_nvar (combine lvi2 lvo2) v2)
          as [s2 | Hin2]; repnd;
     try( destruct s2 as [? Hin2]; 
          apply in_combine in Hin2); 
     try (rewrite combine_split in Hin2; auto);
     repnd; allsimpl; subst.
     
     + (repeat cases_if; try contradiction). eapply Hind; eauto. 
        apply disjoint_app_r. split; trivial.
     + subst. provefalse. apply Hdis0. apply in_app_iff. sp.
     + subst. provefalse. apply Hdis. apply in_app_iff; sp.
     + subst. (repeat cases_if; try contradiction). f_equal.
        eapply Hind; eauto. 
        apply disjoint_app_r. split; trivial.
Qed.
(**lsubst_wf_iff proved in alpgaeq.v*)
Theorem lsubst_aux_wf_iff {p} :
  forall sub, 
  sub_range_sat sub (@nt_wf p)
  -> forall nt, (nt_wf nt <=> nt_wf (lsubst_aux nt sub)).
Proof.
 introv sr. sp_iff Case; introv hyp.
 - apply lsubst_aux_preserves_wf; auto. 
 - apply lsubst_aux_nt_wf in hyp; auto. 
Qed.

Theorem lsubst_aux_allvars_wf_iff {p}:
  forall sub, 
  @allvars_sub p sub
  -> forall nt, (nt_wf nt <=> nt_wf (lsubst_aux nt sub)).
Proof.
 introv sr. apply lsubst_aux_wf_iff.
 introv Hlin. apply sr in Hlin.
 exrepnud Hlin; subst; auto. 
Qed.


Lemma sub_app_sat_iff {p} :  forall P sub1 sub2,
  (@sub_range_sat p sub1 P
    # sub_range_sat  sub2 P)
  <=> sub_range_sat (sub1 ++ sub2) P.
Proof. sp_iff Case.
  - introv sat  Hin. repnd. apply in_app_iff in Hin.
    dorn Hin; [ apply sat0 in Hin | apply sat in Hin]; trivial.
  - introv  sat. allunfold @sub_range_sat. split; intros; eapply sat;
    apply in_app_iff; eauto.
Qed.


Lemma isvarc_fst_unique {p} : forall (t: @NTerm p) (p1 p2: isvarc t),
  projT1 p1=projT1 p2.
Proof. intros. 
  destruct p1. destruct p2. 
 simpl. rewrite e in e0. 
  inverts e0. refl.
Qed.

Definition get_sub_dom_varsd {p} sub (pall : @allvars_sub p sub) : list NVar :=
  gmapd sub (fun t => match t with (a, b) => fun (p : LIn (a,b) sub) => projT1 (pall a b p) end).

Lemma get_sub_dom_vars_eq_d {p} :
  forall sub (pall : @allvars_sub p sub),
    get_sub_dom_vars sub pall = get_sub_dom_varsd sub pall.
Proof.
  intros.
  unfold get_sub_dom_vars, get_sub_dom_varsd.
  rw <- gmap_eq_d; simpl.
  apply eq_gmaps.
  intros.
  destruct a; simpl; sp.
Qed.

Lemma get_sub_dom_vars_cons {p} :
  forall a b sub (pall : @allvars_sub p ((a,b)::sub)),
    get_sub_dom_vars ((a,b) :: sub) pall
    = projT1 (pall a b (inl eq_refl))
             :: get_sub_dom_vars sub (fun v t i => pall v t (inr i)).
Proof.
  introv.
  repeat (rw @get_sub_dom_vars_eq_d).
  unfold get_sub_dom_varsd; simpl.
  apply cons_eq.
  apply eq_gmapds; intros.
  dprods; simpl; sp.
Qed.

Theorem get_sub_dom_vars_spec {p} :
  forall sub (Hall: allvars_sub sub),
    sub = combine (fst (split sub)) (map (@vterm p) (get_sub_dom_vars sub Hall)).
Proof.
  introv.
  induction sub; introv; try (complete auto).
  dprods.
  rw split_cons; rw simpl_fst.
  rw @get_sub_dom_vars_cons.
  rw map_cons; rw combine_cons.
  destruct (Hall n n0 (inl eq_refl)); simpl; subst.
  apply cons_eq.
  generalize (IHsub (fun v t i => Hall v t (inr i))); sp.
Qed.

(*
Theorem get_sub_dom_vars_spec :
  forall sub (Hall: allvars_sub sub),
    sub = combine (fst (split sub)) (map vterm (get_sub_dom_vars sub Hall)).
Proof.
  induction sub as [| (v,t) sub Hind]; auto. intros ?. simpl.
  destruct (split sub) as [lv lnt]. simpl. f_equal. 
  - f_equal.
    (** wierd! if I dont specify implicit args,
    it guesses wrong ones and causes failure *)
    remember (Hall v t
           (@inl
              (@eq (prod NVar NTerm) (@pair NVar NTerm v t)
                 (@pair NVar NTerm v t))
              (@LIn (prod NVar NTerm) (@pair NVar NTerm v t) sub)
              (@eq_refl (prod NVar NTerm) (@pair NVar NTerm v t))))
     as Hisvar.
     destruct Hisvar. subst. simpl. reflexivity.
  - allsimpl. fold ([(v, t)] ++ sub) in Hall.
    pose proof (tiff_snd (sub_app_sat_iff _ _ _) Hall). repnd.
    assert (allvars_sub sub) as Hsub by auto.
    pose proof (Hind Hsub ) as Hw.
    allsimpl.
    symmetry in Hw.
    (** need to rewrite just the LHS. *)
    apply ( @ transport _ _ _
         (fun sub1 : Substitution =>
         sub1 =
         combine lv
           (map vterm
              (gmap sub
                 (fun (a0 : NVar # NTerm) (Hin : LIn a0 sub) =>
                  projT1
                    (Hall (fst a0) (snd a0)
                       ((let (n, n0) as p
                             return
                               ((v, t) = p[+]LIn p sub ->
                                (v, t) = (fst p, snd p)[+]LIn (fst p, snd p) sub) :=
                             a0 in
                         fun p : (v, t) = (n, n0)[+]LIn (n, n0) sub => p) (inr Hin)))))))
           Hw ).
      unfold get_sub_dom_vars.  repeat (f_equal).
      repeat (apply functional_extensionality_dep; intros).
      apply isvarc_fst_unique.
Qed.
*)

Theorem get_sub_dom_vars_eta {p} : forall sub
  (Hall: allvars_sub sub),
  {lvi,lvo: list NVar $ (sub = @var_ren p lvi lvo) # length lvi =length lvo}.
Proof.
  intros. exists (fst (split sub)).
  exists (get_sub_dom_vars sub Hall).
  split. apply get_sub_dom_vars_spec.
  rewrite split_length_l.
  unfold get_sub_dom_vars.
  rewrite gmap_length; auto.
Defined.


Theorem get_sub_dom_vars_ren {p} : forall lvi lvo
  (Hall: allvars_sub (@var_ren p lvi lvo)),
  length lvi=length lvo
  -> get_sub_dom_vars (var_ren lvi lvo) Hall = lvo.
Proof.
  introv H. 
  pose proof (get_sub_dom_vars_spec (var_ren lvi lvo) Hall) as HH.
  unfold var_ren in HH. 
  rewrite combine_split in HH; 
    [ | rewrite map_length; trivial].
  allsimpl. apply combine_eq in HH;
  try (rewrite map_length; auto).
  repnd. apply (@map_eq_lift_vterm p); auto.
  unfold get_sub_dom_vars. rewrite  gmap_length.
  rewrite combine_length.
  rewrite map_length.
  rewrite H. rewrite Min.min_idempotent; refl.
Qed.


Lemma allvars_sub_filter {p} :
  forall lvi lvo lv, allvars_sub (sub_filter (@var_ren p lvi lvo) lv).
Proof.
  intros. apply sub_filter_allvars.
  apply allvars_combine.
Defined.

Lemma allvars_sub_filter_cons {p} : forall lvi lvo lv vi vo,
   allvars_sub ((vi,vterm vo) :: (sub_filter (@var_ren p lvi lvo) lv)).
Proof.
  introv Hin. dorn Hin. inverts Hin; eexists; eauto.
  apply allvars_sub_filter in Hin; auto.
Defined.



Theorem no_repeats_sub_filter {p} :
  forall lvi lvo lvi0 lvo0 lv, 
  var_ren lvi0 lvo0 = sub_filter (@var_ren p lvi lvo) lv
  -> length lvi0 = length lvo0
  -> no_repeats lvo
  -> no_repeats lvo0.
Proof.
  induction lvi as [|vi lvi Hind]; introv Heq Heql Hnr.
  unfold var_ren in Heq. simpl in Heq.
  destruct lvi0; destruct lvo0; try (inverts Heql);
   try (inverts Heq).
   - constructor.
   - destruct lvo.
     + unfold var_ren in Heq.
       simpl in Heq. 
       destruct lvi0; 
       destruct lvo0; try (inverts Heql);
       try (inverts Heq). constructor.
     + simpl in Heq. rewrite memvar_dmemvar in Heq.
        inverts Hnr as Hnin Hnr.
        destruct (dmemvar vi lv).
        eapply Hind; eauto.
       destruct lvi0; 
       destruct lvo0; try (invertsn Heql);
       try (invertsn Heq). constructor; auto.
       Focus 2. eapply Hind; eauto.
       intro Hc.
       apply (@lin_lift_vterm p) in Hc.
       apply combine_in_right with (l1:=lvi0) in Hc.
       exrepnd.
       rewrite Heq in Hc0.
       apply in_sub_filter in Hc0.
       repnd. apply in_combine in Hc1. repnd. sp.
       apply lin_lift_vterm in Hc1. sp.
       rewrite map_length. omega.
Qed.

Fixpoint diff_vars {p} (l : list NVar) (ts : list (@NTerm p)) : list NTerm :=
  match ts with
    | [] => []
    | t :: ts =>
      if intersect_vars (free_vars t) l
      then diff_vars l ts
      else t :: diff_vars l ts
  end.

(*

  This is similar to map_removevars but does not need the equality
  decider and uses diff_vars instead of diff.

*)
Lemma map_removevars_l {p} :
  forall lvi lvr,
    map (@vterm p) (remove_nvars lvi lvr)
    = diff_vars lvi (map vterm lvr).
Proof.
  induction lvr; simpl.
  rw remove_nvars_nil_r; simpl; auto.
  rw remove_nvars_cons_r; boolvar; simpl; tcsp.
  - rw disjoint_cons_l in d; repnd; tcsp.
  - rw intersect_single_l in i; tcsp.
  - rw IHlvr; sp.
Qed.

Theorem freevars_lsubst_aux_allvars {pp} :
  forall (t : NTerm) sub
         (p : allvars_sub sub),
    no_repeats (get_sub_dom_vars sub p)
    -> disjoint (get_sub_dom_vars sub p) (all_vars t)
    -> map vterm (free_vars (lsubst_aux t sub))
       = map (fun t=> lsubst_aux t sub) (map (@vterm pp) (free_vars t)).
Proof.
  nterm_ind1 t as [v|o lbt Hind] Case; introv Hnr Hdis; auto.
  - Case "vterm".
    simpl.
    unfold lmap_apply.
    cases (sub_find sub v) as Hsf; auto.
    exrepnd. apply sub_find_some in Hsf.
      pose proof (p _ _ Hsf) as X; exrepnud X. 
      subst. refl.
  - Case "oterm".
    induction lbt as [|bt lbt IHlbt]; auto.
    allsimpl. repeat(rewrite map_app).
    rewrite IHlbt;
    [ | intros; eapply Hind; eauto; fail
           | (allrw disjoint_app_r); repnd;auto; fail].
    clear IHlbt.
     f_equal.
    destruct bt as [lv nt].
    simpl. unfold bvar_renamings_subst. simpl.
    remember ((sub_filter sub lv)) as sfio.
    remember (@sub_mk_renames2 pp lv (sub_free_vars sfio) (dom_sub sfio ++ all_vars nt) ) as H99.
    destruct H99 as [lvr subr].
    pose proof (get_sub_dom_vars_eta sub p).
    exrepnd. subst.
     duplicate Hdis.
     unfold all_vars in Hdis. simpl in Hdis. 
     repeat(rw disjoint_app_r in Hdis).
    rewrite sub_mk_renames2_disjoint in HeqH99.
    Focus 2.
       repnd. rewrite get_sub_dom_vars_ren in Hdis3; auto.
       apply disjoint_sym in Hdis3.
       introv Hc1 Hc2. apply Hdis3 in Hc1.
       apply in_sub_free_vars in Hc2. exrepnd.
       apply in_sub_filter in Hc0; repnd.
       apply in_combine in Hc3. repnd.
       apply in_map_iff in Hc3. exrepnd. subst.
       allsimpl. dorn Hc2; sp.
       subst; sp.

    inverts HeqH99. allsimpl.
    pose proof (@allvars_sub_filter pp lvi lvo lv) as Halv.

    rewrite map_removevars_l.
    erewrite Hind with (p:=Halv); eauto.
    clear Hind.
    unfold lvmap_lapply.
    remember (free_vars nt) as fnt.
    pose proof (@transport _ _ _ (fun vs => subvars fnt vs)
                           Heqfnt (subvars_refl fnt)) as Hsub.
    allsimpl.
     clear Heqfnt. repnd.
    induction fnt as [| vnt fnt Hfntind];
       [ complete (rw remove_nvars_nil_r; refl) | simpl ].
     apply subvars_cons_l in Hsub; repnd.
     rewrite Hfntind; auto. clear Hfntind.
     dest_intersect_vars.
     + f_equal. rewrite remove_nvars_cons_r.
        rewrite memvar_dmemvar.
        cases_if_sum Hmemdin;auto.
        rewrite sub_lmap_find in i.
        provefalse.
        apply disjoint_sym in Hdis3. 
        destruct (lmap_find deq_nvar (sub_filter (var_ren lvi lvo) lv)
           vnt) as [ex | ?]; exrepnd; allsimpl;
        [ | rw intersect_single_l in i; sp].
        subst. apply in_sub_filter in ex0; repnd.
        rewrite get_sub_dom_vars_ren in Hdis3; auto.
        clear Hdis Hdis1 Hdis2 Hdis4 Hdis0 Halv.
        apply in_combine in ex1. repnd.
        apply in_map_iff in ex1. exrepnd.
        subst; allsimpl.
        rw intersect_single_l in i.
        apply Hdis3 in i; sp.

     + rewrite remove_nvars_cons_r.
         rewrite memvar_dmemvar.
         cases_if_sum Hmemdin; auto.
         * provefalse.
           rewrite sub_lmap_find in d.
           destruct (lmap_find deq_nvar 
            (sub_filter (var_ren lvi lvo) lv) vnt) 
              as [ex | ?]; exrepnd; allsimpl.
           subst. apply in_sub_filter in ex0; repnd.
           apply in_combine in ex1. repnd. sp.
           rw disjoint_singleton_l in d; sp.
         * simpl. f_equal.
           rewrite sub_find_sub_filter_eta; auto.
     + clear Hfntind. rewrite get_sub_dom_vars_ren; auto.
       rewrite get_sub_dom_vars_ren in Hdis4; auto.
       rewrite remove_nvars_cons_r in Hdis4. 
       revert Hdis4. cases_if; auto.
       rw disjoint_cons_r; sp.
     + remember ((sub_filter (var_ren lvi lvo) lv)) as Hsb.
        pose proof  (get_sub_dom_vars_eta Hsb Halv) as ex. exrepnd.
        revert Halv. rewrite ex0.
        intro. rewrite ex0 in HeqHsb.
        rewrite get_sub_dom_vars_ren; auto.
        rewrite get_sub_dom_vars_ren in Hnr; auto.
        apply no_repeats_sub_filter in HeqHsb; trivial.
     + remember ((sub_filter (var_ren lvi lvo) lv)) as Hsb.
        pose proof  (get_sub_dom_vars_eta Hsb Halv) as ex. exrepnd.
        revert Halv. rewrite ex0.
        intro. rewrite ex0 in HeqHsb.
        rewrite get_sub_dom_vars_ren; auto.
        rewrite get_sub_dom_vars_ren in Hdis2; auto.
        rewrite get_sub_dom_vars_ren in Hdis4; auto.
        rewrite get_sub_dom_vars_ren in Hdis3; auto.
        clear Hdis Hdis1  Hdis0 .
        assert (disjoint lvo (all_vars nt)) as Hvo.
          * apply disjoint_app_r. split; auto.
            introv Hin Hc. applydup Hdis4 in Hin.
            apply Hin0. apply in_remove_nvars. split; auto.
          * introv Hin Hc. apply (@lin_lift_vterm pp) in Hin.
            apply combine_in_right with (l1:=lvi0) in Hin.
            exrepnd. unfold var_ren in HeqHsb.
            rewrite HeqHsb in Hin0.
            apply in_sub_filter in Hin0. repnd.
            apply in_combine in Hin1. repnd.
            apply lin_lift_vterm in Hin1.
            apply Hvo in Hin1. sp.
            rewrite map_length. omega.
Qed.


Theorem no_repeats_subvars : forall lvi lvo,
  no_repeats lvi 
  -> subvars  lvo lvi
  -> no_repeats lvo.
Proof.
  induction lvi; introv Hnr Hsub; auto; destruct lvo; cpx.
  - rw subvars_cons_l in Hsub. repnd. cpx.
  - constructor.
Abort. (**not true*)


(* Print Assumptions freevars_lsubst_allvars. *)


Lemma lmap_apply_var {p} : forall lvi lvo v,
 (fun t=> lsubst t (var_ren lvi lvo)) (vterm v)
  = @vterm p (lmap_apply deq_nvar (combine lvi lvo) v).
Proof.
 intros. simpl. unfold lsubst. simpl. rewrite sub_lmap_find.
  unfold lmap_apply.
  unfold var_ren. rewrite <- lmap_find_injection; [| introv H; inverts H;sp].
  cases(lmap_find deq_nvar (combine lvi lvo) v); exrepnd; simpl; auto.
Qed.

Lemma lmap_lapply_var_map {p} : forall lvi lvo lv,
 map (fun t=> lsubst_aux t (var_ren lvi lvo)) (map vterm lv)
  = map (@vterm p) (lmap_lapply deq_nvar (combine lvi lvo) lv).
Proof.
  induction lv as [|v lv Hind];auto.
  simpl. rewrite Hind. f_equal.
  rewrite <- lmap_apply_var; refl.
Qed.

Theorem freevars_lsubst_allvars2 {p} :
   forall (t : NTerm) (lvi lvo: list NVar),
      length lvi= length lvo
      -> no_repeats lvo
       -> disjoint lvo (all_vars t)
       -> free_vars (lsubst t (@var_ren p lvi lvo) )
          = lvmap_lapply (combine lvi lvo) (free_vars t).
Proof.
  introv Hleq Hnr Hdis.
  unfold lsubst. cases_ifn Hd.
  Focus 2. allunfold @var_ren. spcls. spcls.
  provefalse. apply Hd. disjoint_reasoningv.

  pose proof (freevars_lsubst_aux_allvars
   t (var_ren lvi lvo) (allvars_combine lvi lvo)) as HH.
   rewrite get_sub_dom_vars_ren in HH; auto.
   allsimpl. pose proof (HH Hnr Hdis) as HH1.
   clear HH.
   rewrite lmap_lapply_var_map in HH1.
   apply (@map_eq_lift_vterm p); trivial.
Qed.

Lemma lsubst_aux_trivial3 {p} :
  forall t sub,
    (forall v u, LIn (v, u) sub -> disjoint (@free_vars p u) (bound_vars t)
          # ! LIn v (free_vars t))
    -> lsubst_aux t sub = t.
Proof.
  nterm_ind t Case; simpl; intros; auto.

  - Case "vterm".
    allunfold @isprogram; allunfold @closed; sp.
    remember (sub_find sub n); destruct o; symmetry in Heqo; auto.
    apply sub_find_some in Heqo.
    apply_in_hyp pp; sp.
    apply not_over_or in pp; sp.

  - Case "oterm". f_equal.
    induction lbt; simpl; auto.
    rw IHlbt; sp.
    + destruct a; simpl. f_equal.
      * f_equal. f_equal. eapply H; try(left); eauto.
        introv Hin. apply in_sub_filter in Hin. repnd.
        rename H0 into Hdis. apply Hdis in Hin0. repnd.
        rw disjoint_app_r in Hin1.
        rw disjoint_app_r in Hin1.
        repnd. split; auto.
        intro Hc. apply Hin0.
        apply in_app_iff.
        left. apply in_remove_nvars; sp.
    + rewrite H with (lv := lv); sp.
    + apply_in_hyp pp; sp. allsimpl.
        rw disjoint_app_r in pp0. sp.
    + apply_in_hyp pp; sp; allsimpl.
      allrw in_app_iff.
      allrw not_over_or; sp.
Qed.

Lemma lsubst_trivial3 {p} :
  forall t sub,
    (forall v u, LIn (v, u) sub -> disjoint (@free_vars p u) (bound_vars t) 
          # ! LIn v (free_vars t))
    -> lsubst t sub = t.
Proof.
  introv HH. assert (disjoint_bv_sub t sub).
  introv Hin. apply HH in Hin. sp.
  change_to_lsubst_aux4.
  apply lsubst_aux_trivial3; try(sp;fail);
  try(apply disjoint_sub_as_flat_map;disjoint_reasoning).
Qed.

Lemma lsubst_trivial4 {p} :
  forall t sub, disjoint (@dom_sub p sub) (free_vars t) 
    -> (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t))
    -> lsubst t sub = t.
Proof.
  introv Hdis Hfr.
  apply lsubst_trivial3.
  introv Hin.
  applydup_clear Hfr in Hin.
  sp. apply disjoint_sym in Hdis.
  apply Hdis in X.
  apply in_dom_sub in Hin. sp.
Qed.

Lemma lsubst_aux_trivial4 {p} :
  forall t sub, disjoint (@dom_sub p sub) (free_vars t) 
    -> (forall v u, LIn (v, u) sub -> disjoint (free_vars u) (bound_vars t))
    -> lsubst_aux t sub = t.
Proof.
  introv Hdis Hfr.
  apply lsubst_aux_trivial3.
  introv Hin.
  applydup_clear Hfr in Hin.
  sp. apply disjoint_sym in Hdis.
  apply Hdis in X.
  apply in_dom_sub in Hin. sp.
Qed.


Lemma sub_filter_disjoint1 {p} :
  forall sub lf,
  disjoint (@dom_sub p sub) lf
  -> sub_filter sub lf
      = sub.
Proof.
  induction sub as [|(v,t) sub Hind]; introv K; auto.
  simpl. allsimpl. apply disjoint_cons_l in K.
  rewrite memvar_dmemvar.
  cases_if; [clear H | ];sp.
  f_equal. auto.
Qed.



Lemma sub_filter_disjoint {p} :
  forall lvi lvo lvf,
  length lvi = length lvo
  -> disjoint lvi lvf
  -> sub_filter (var_ren lvi lvo) lvf
      = @var_ren p lvi lvo.
Proof.
  intros. apply sub_filter_disjoint1.
  unfold var_ren. rewrite dom_sub_combine. auto.
  rewrite map_length; auto; try omega.
Qed.




Lemma in_combine_vars_vterm {p} : forall lvi lvo u v ,
  LIn (u,v) (combine lvi lvo) -> LIn (u, vterm v) (@var_ren p lvi lvo).
Proof.
  introv X.   assert (injective_fun (fun x:NVar => x))  as Hi by (introv;auto).
  pose proof (tiff_fst (lin_combine_injective (fun x : NVar => x) vterm
    Hi (@vterm_inj p) _ _ _ _) X) as XX. rewrite map_id in XX.
    auto.
Qed.



Theorem disjoint_sub_filter_vars_l {p} : forall  lvi lvo lvis lvos lv ld,
   sub_filter (var_ren lvi lvo) lv = @var_ren p lvis lvos
   -> length lvi =length lvo 
   -> length lvis =length lvos 
   -> disjoint lvi ld 
   -> disjoint lvis ld.
Proof.
  introv Hsf Hlen Hle1n Hdis. introv Hin.
  apply combine_in_left with (l2:=lvos) in Hin; auto.
  exrepnd. apply (@in_combine_vars_vterm p) in Hin0. rewrite <- Hsf in Hin0.
  apply in_sub_filter in Hin0. repnd. apply in_combine in Hin1. repnd.
  apply Hdis in Hin2. sp.
Qed.

Theorem disjoint_sub_filter_vars_r {p} : forall  lvi lvo lvis lvos lv ld,
   sub_filter (var_ren lvi lvo) lv = @var_ren p lvis lvos
   -> length lvi =length lvo 
   -> length lvis =length lvos 
   -> disjoint lvo ld 
   -> disjoint lvos ld.
Proof.
  introv Hsf Hlen Hle1n Hdis. introv Hin.
  apply combine_in_right with (l1:=lvis) in Hin; auto.
  exrepnd. apply (@in_combine_vars_vterm p) in Hin0. rewrite <- Hsf in Hin0.
  apply in_sub_filter in Hin0. repnd. apply in_combine in Hin1. repnd.
  apply in_map_iff in  Hin1. exrepnd. inverts Hin3.
  apply Hdis in Hin1. sp.
  omega.
Qed.

Theorem disjoint_sub_filter_l {p} : forall lvi lnt lvis lnts ld lv,
   @sub_filter p (combine lvi lnt) lv = combine lvis lnts
   -> length lvi =length lnt
   -> length lvis =length lnts
   -> disjoint lvi ld 
   -> disjoint lvis ld.
Proof.
  introv Hsf Hlen Hle1n Hdis. introv Hin Hc.
  apply combine_in_left with (l2:=lnts) in Hin ; auto.
  exrepnd.
  rw <- Hsf in Hin0.
  apply in_sub_filter in Hin0. repnd. apply in_combine in Hin1. repnd.
  apply Hdis in Hin2. sp.
Qed.

Theorem disjoint_sub_filter_vars {p} : forall  lvi lvo lvis lvos lv ld,
   sub_filter (var_ren lvi lvo) lv = @var_ren p lvis lvos
   -> length lvi =length lvo 
   -> length lvis =length lvos 
   -> disjoint (lvi++lvo) ld 
   -> disjoint (lvis++lvos) ld.
Proof.
  introv Hsf Hlen Hle1n Hdis. apply disjoint_app_l in Hdis. repnd.
  duplicate Hsf.
  apply @disjoint_sub_filter_vars_l with (ld:=ld) in Hsf; auto.
  apply @disjoint_sub_filter_vars_r with (ld:=ld) in Hsf0; auto.
  apply disjoint_app_l; auto.
Qed.

Lemma sub_find_first {p} : forall sub v t,
  @sub_find p sub v= Some t
  -> {n: nat & (n < length sub) # nth n sub (v,t) =(v,t) # 
      not_in_prefix (dom_sub sub) v n}.
Proof.
  introns K. rewrite (sub_lmap_find_first) in K.
  destruct (lmap_find_first deq_nvar sub v) as [s1s|n1n];
  exrepnd;  allsimpl; allfold (@dom_sub p); inverts K.
    exists n; sp.
Qed.

Lemma sub_find_some2_first {p} :
  forall lv lnt1 lnt2 v t1 t2,
    length lv = length lnt1
    -> length lv = length lnt2
    -> @sub_find p (combine lv lnt1) v = Some t1
    -> @sub_find p (combine lv lnt2) v = Some t2
    -> {n:nat & n< length lv #
           nth n lv v= v # not_in_prefix lv v n
           # nth n lnt1 t1= t1 # nth n lnt2 t2= t2}.
Proof.
  introv H1len H2len H1s H2s.
  apply sub_find_first in H1s.
  apply sub_find_first in H2s.
  exrepnd.
  rewrite_once combine_length.
  rewrite_once combine_length.
  rewrite_once @dom_sub_combine; cpx.
  rewrite_once @dom_sub_combine; cpx.
  rewrite_once combine_nth; cpx.
  rewrite_once combine_nth; cpx.
  rewrite_once min_eq; cpx.
  rewrite_once min_eq; cpx.
  assert (is_first_index lv v n) as H1isf by
   (unfolds_base;split;(try split);cpx; try(congruence)).
  assert (is_first_index lv v n0) as H2isf by
   (unfolds_base;split;(try split);cpx; try(congruence)).
  assert (n=n0) by (eapply is_first_index_unique; eauto).
  subst. rename n0 into n. GC.
  repeat (dpair_eq).
  exists n; dands; cpx; try congruence.
  rewrite H1s2l; auto.
  rewrite H1s2l; auto.
Qed.

Lemma sub_find_some_none_contra {p} : forall lv lnt1 lnt2 v t1,
  length lv = length lnt1
  -> length lv = length lnt2
  -> @sub_find p (combine lv lnt1) v = Some t1
  -> @sub_find p (combine lv lnt2) v = None
  -> False.
Proof.
  introv H1l H2n Hsfs Hsfn.
  apply sub_find_some in Hsfs. apply in_combine in Hsfs. repnd.
  apply sub_find_none2 in Hsfn. rewrite_once @dom_sub_combine; sp.
Qed.





Lemma disjoint_free_vars_lsubst {p} :
  forall (nt : NTerm) (sub : @Substitution p) lvdr,
  disjoint (flat_map free_vars (range sub)) (bound_vars nt)
  -> disjoint (free_vars nt ++ (flat_map free_vars (range sub))) lvdr
  -> disjoint (free_vars (lsubst nt sub)) lvdr.
Proof.
  introv H1dis H2dis.
  introv Hin Hc.
  apply free_vars_lsubst in Hin;
    [|unfold disjoint_bv_sub;rw @disjoint_sub_as_flat_map;sp];[].
  apply disjoint_app_l in H2dis; repnd.
  dorn Hin.
  - apply H2dis0 in Hin. sp.
  - exrepnd. rw <- @disjoint_sub_as_flat_map in H2dis.
    apply H2dis in Hin0.
    apply Hin0 in Hin1. sp.
Qed.


Lemma disjoint_free_vars_lsubst_aux {p} :
  forall (nt : NTerm) (sub : @Substitution p) lvdr,
  disjoint (flat_map free_vars (range sub)) (bound_vars nt)
  -> disjoint (free_vars nt ++ (flat_map free_vars (range sub))) lvdr
  -> disjoint (free_vars (lsubst_aux nt sub)) lvdr.
Proof.
  introv H1dis H2dis.
  introv Hin Hc.
  apply free_vars_lsubst_aux in Hin;
    [|unfold disjoint_bv_sub;rw @disjoint_sub_as_flat_map;sp];[].
  apply disjoint_app_l in H2dis; repnd.
  dorn Hin.
  - apply H2dis0 in Hin. sp.
  - exrepnd. rw <- @disjoint_sub_as_flat_map in H2dis.
    apply H2dis in Hin0.
    apply Hin0 in Hin1. sp.
Qed.




Lemma boundvars_lsubst_aux {p}:
  forall nt sub v,
  disjoint_bv_sub nt sub
  -> LIn v (bound_vars (lsubst_aux nt sub))
  -> LIn v (bound_vars nt)[+]
      {v' : NVar &
      {t : @NTerm p & sub_find sub v' =Some t # LIn v' (free_vars nt) # LIn v (bound_vars t)}}.
Proof.
  nterm_ind1s nt as [v|o lbt Hind] Case; introv  Hdis Hin; auto; auto.
  - Case "vterm". allsimpl. right. 
    allsimpl. dsub_find sn; cpx;[].
    exists v sns. split; auto.

  - Case "oterm". simpl. 
    simpl in Hin. rw lin_flat_map in Hin. 
    destruct Hin as [bt' Hin]. repnd. apply in_map_iff in Hin0. 
    destruct Hin0 as [bt Hin0]. repnd. subst. destruct bt as [lv nt]. 
    simpl in Hin. 
    simpl in Hin. apply in_app_iff in Hin. dorn Hin.
    + left. apply lin_flat_map. eexists; split; eauto. simpl. apply in_app_iff.
      left; sp.
    + apply Hind with (lv:=lv) (nt:=nt) in Hin; cpx;
        [|eapply disjoint_bv_sub_ot; eauto].
      dorn Hin.
      * left. simpl. apply lin_flat_map. eexists; split; eauto. simpl. 
        apply in_app_iff. right. auto.
      * exrepnd. right. rw @sub_find_sub_filter_some in Hin0.
        repnd. eexists; eauto. eexists; dands; eauto.
        apply lin_flat_map. eexists; split; eauto;[].
        simpl. apply in_remove_nvars. split; auto.
Qed.

Lemma boundvars_lsubst {p} :
  forall nt sub v,
  disjoint_bv_sub nt sub
  -> LIn v (bound_vars (lsubst nt sub))
  -> LIn v (bound_vars nt)[+]
      {v' : NVar &
      {t : @NTerm p & sub_find sub v' =Some t # LIn v' (free_vars nt) # LIn v (bound_vars t)}}.
Proof.
  introv Hd. change_to_lsubst_aux4. intros.
  apply boundvars_lsubst_aux;try(sp;fail);
  try(rw @disjoint_sub_as_flat_map;disjoint_reasoning).
Qed.


Lemma boundvars_lsubst_aux_vars {p} :
  forall nt lvi lvo,
  length lvi = length lvo
  -> disjoint lvo (bound_vars nt)
  -> bound_vars (lsubst_aux nt (@var_ren p lvi lvo))
     = bound_vars nt.
Proof.
  nterm_ind1s nt as [v|o lbt Hind] Case; introv Hl Hdis; auto.
  - Case "vterm". simpl. rewrite sub_lmap_find. 
    destruct (lmap_find deq_nvar (var_ren lvi lvo) v) as [s1s| n1n];auto; exrepnd.
    allsimpl. apply in_var_ren in s1s0. exrepnd. subst. auto.
  - Case "oterm". simpl. rewrite flat_map_map.
    apply eq_flat_maps. intros bt Hin. destruct bt as [lv nt].
    unfold compose. simpl. 
    eapply (@disjoint_lbt_bt2 p) in Hdis; eauto. repnd.
    + simpl. f_equal. pose proof (@allvars_sub_filter p lvi lvo lv) as X1X.
      apply get_sub_dom_vars_eta in X1X. exrepnd.
      rewrite X1X0. eapply Hind; eauto 3 with slow.
      eapply disjoint_sub_filter_vars_r  with (ld:= (bound_vars nt)) in X1X0
      ; eauto. 
Qed.



Lemma boundvars_lsubst_vars {p} :
  forall nt lvi lvo,
  length lvi = length lvo
  -> disjoint lvo (bound_vars nt)
  -> bound_vars (lsubst nt (@var_ren p lvi lvo))
     = bound_vars nt.
Proof.
  intros. change_to_lsubst_aux4.
  apply boundvars_lsubst_aux_vars;try(sp;fail);
  try(rw disjoint_sub_as_flat_map;disjoint_reasoningv).
Qed.

Lemma boundvars_lsubst_vars2 {p} :
  forall nt sub,
  @allvars_sub p sub
  -> disjoint_bv_sub nt sub
  -> bound_vars (lsubst nt sub)
     = bound_vars nt.
Proof.
  introv Ha Hd. change_to_lsubst_aux4.
  pose proof (get_sub_dom_vars_eta _ Ha) as XX.
  exrepnd. GC. revert Hd. intro Hd. allrw XX0.
  spcls.
  apply boundvars_lsubst_aux_vars;try(sp;fail).
  disjoint_reasoning.
Qed.

Lemma disjoint_bound_vars_lsubst {p} :
  forall (nt : NTerm) (sub : @Substitution p) lvdr,
  disjoint (flat_map free_vars (range sub)) (bound_vars nt)  
  -> disjoint (bound_vars nt ++ (flat_map bound_vars (range sub))) lvdr
  -> disjoint (bound_vars (lsubst nt sub)) lvdr.
Proof.
  introv H1dis H2dis.
  introv Hin Hc.
  apply boundvars_lsubst in Hin;
    [|unfold disjoint_bv_sub;rw @disjoint_sub_as_flat_map;sp];[].
  apply disjoint_app_l in H2dis; repnd.
  dorn Hin.
  - apply H2dis0 in Hin. sp.
  - exrepnd. rw <- @disjoint_sub_as_flat_map in H2dis.
    apply sub_find_some in Hin0.
    apply H2dis in Hin0.
    apply Hin0 in Hin1. sp.
Qed.

Lemma disjoint_bound_vars_lsubst_aux {p} :
  forall (nt : NTerm) (sub : @Substitution p) lvdr,
  disjoint (flat_map free_vars (range sub)) (bound_vars nt)  
  -> disjoint (bound_vars nt ++ (flat_map bound_vars (range sub))) lvdr
  -> disjoint (bound_vars (lsubst_aux nt sub)) lvdr.
Proof.
  introv H1dis H2dis.
  introv Hin Hc.
  apply boundvars_lsubst_aux in Hin;
    [|unfold disjoint_bv_sub;rw @disjoint_sub_as_flat_map;sp];[].
  apply disjoint_app_l in H2dis; repnd.
  dorn Hin.
  - apply H2dis0 in Hin. sp.
  - exrepnd. rw <- @disjoint_sub_as_flat_map in H2dis.
    apply sub_find_some in Hin0.
    apply H2dis in Hin0.
    apply Hin0 in Hin1. sp.
Qed.
  

(** 1 or less renaming subgoals. see lsubst_nest_swap2 for an example*)
Ltac almost_complete1 t :=
  ((t;fail) || (t;[])).

Ltac dis_almost_complete1 t :=
  try(almost_complete1 t);try (apply disjoint_sym; almost_complete1 t).

Hint Resolve prog_sub_implies_wf : slow.


Hint Resolve disjoint_sub_filter_r_flatmap2 : slow.
Hint Resolve disjoint_sym : slow.

Lemma disjoint_dom_sub_filt {p} : forall sub lv, 
  disjoint (dom_sub (@sub_filter p sub lv)) lv.
Proof. introv Hin Hinc.
  unfold dom_sub, dom_lmap in Hin.
  apply in_map_iff in Hin.
  exrepnd.
  allsimpl. subst.
  apply in_sub_filter in Hin1.
  repnd. sp.
Qed.

Lemma disjoint_dom_sub_filt2 {p} : forall sub lv1 lvn,
  disjoint (@dom_sub p sub) lvn
  -> disjoint (dom_sub (sub_filter sub lv1)) lvn.
Proof.
  introv Hdis Hin Hinc.
  unfold dom_sub, dom_lmap in Hin.
  apply in_map_iff in Hin.
  exrepnd.
  allsimpl. subst.
  apply in_sub_filter in Hin1.
  repnd. apply in_dom_sub in Hin0.
  disjoint_lin_contra.
Qed.

(** update it in substitution.v *)
Ltac disjoint_sub_filter :=
        let tac1:=(eapply disjoint_sub_filter_l;eauto) in 
        let tac2:=(eapply disjoint_sub_filter_r_flatmap;eauto) in 
          dis_almost_complete1 tac1;dis_almost_complete1 tac2;disjoint_reasoningv;
 (
  let maintac := apply disjoint_sub_filter_r_flatmap2; disjoint_reasoningv in
  match goal with 
  |[ |- (disjoint (flat_map _ (range (sub_filter _ _ ))) _ )]
    =>  maintac
  |[ |- ( disjoint _ (flat_map _ (range (sub_filter _ _ ))))]
    => apply disjoint_sym; maintac
  | [ |- disjoint (dom_sub (sub_filter ?sub ?lv)) ?lv ] 
      =>  apply disjoint_dom_sub_filt; fail
  | [ |- disjoint ?lv (dom_sub (sub_filter ?sub ?lv)) ] 
      =>  apply disjoint_sym; apply disjoint_dom_sub_filt; fail
  | [ H : (disjoint (dom_sub (sub_filter ?sub ?lv)) ?lv) |- _] 
      =>  clear H
  | [ H : ?lv (disjoint (dom_sub (sub_filter ?sub ?lv))) |- _] 
      =>  clear H
  | [ |- disjoint (dom_sub (sub_filter ?sub _)) _ ] 
      =>  apply disjoint_dom_sub_filt2; disjoint_reasoningv
  | [ |- disjoint _ (dom_sub (sub_filter ?sub _))] 
      =>  apply disjoint_sym; apply disjoint_dom_sub_filt2; disjoint_reasoningv
    
  end
  ).

  Ltac disjoint_lsubst :=
  let maintacf := apply disjoint_free_vars_lsubst_aux;
     disjoint_reasoningv;try(disjoint_sub_filter) in
  let maintacb := apply disjoint_bound_vars_lsubst_aux;
     disjoint_reasoningv;try(disjoint_sub_filter) in
  match goal with 
  |[ |- disjoint (free_vars (lsubst_aux _ _ ))  _ ]
    => maintacf  
  |[ |- disjoint _ (free_vars (lsubst_aux _ _ ))]
    =>  apply disjoint_sym ; maintacf
  |[ |- disjoint (bound_vars (lsubst_aux _ _ ))  _ ]
    => maintacb  
  |[ |- disjoint _ (bound_vars (lsubst_aux _ _ ))]
    =>  apply disjoint_sym ; maintacb
  end.



Lemma lsubst_aux_nest_swap2 {p} : forall t sub1 sub2,
  let lvi1 := @dom_sub p sub1 in
  let lvi2 := dom_sub sub2 in
  let lnt1 := range sub1 in
  let lnt2 := range sub2 in
  disjoint lvi1 (flat_map free_vars lnt2) (**o/w capture will occur in RHS*)
  -> disjoint lvi2 (flat_map free_vars lnt1) (**o/w capture will occur in LHS*)
  -> disjoint lvi1 lvi2 (**o/w order will matter*)
  -> disjoint (flat_map bound_vars lnt1) (flat_map free_vars lnt2) (**o/w renaming will occur in LHS*)
  -> disjoint (flat_map bound_vars lnt2) (flat_map free_vars lnt1) (**o/w renaming will occur in RHS*)
  -> disjoint (bound_vars t) ((flat_map free_vars lnt1) ++ (flat_map free_vars lnt2)) (**o/w renaming will occur*)
  -> lsubst_aux(lsubst_aux t sub1) sub2 = lsubst_aux(lsubst_aux t sub2) sub1.
Proof.
  nterm_ind1s t as [v|o lbt Hind] Case; auto;
  introv H1dis H2dis H3dis H4dis H5dis Hdist; simpl;
  pose proof (sub_eta sub1) as Xsub1eta;
  pose proof (sub_eta sub2) as Xsub2eta;
  pose proof (sub_eta_length sub1) as Xlen1;
  pose proof (sub_eta_length sub2) as Xlen2;
  remember (dom_sub sub1) as lvi1;
  remember (dom_sub sub2) as lvi2;
  remember (range sub1) as lnt1;
  remember (range sub2) as lnt2.
  Case "vterm".

  - simpl. destructr (sub_find sub1 v) as  [s1|n1].
    + symmetry in HeqHdeq. applydup @sub_find_some in HeqHdeq.
      simpl. rw Xsub1eta in HeqHdeq0.
      apply in_combine in HeqHdeq0. repnd.
      assert (disjoint lvi1 lvi2) as XX by   disjoint_reasoningv.
      apply XX in HeqHdeq1.
      destructr (sub_find (combine lvi2 lnt2) v) as  [s2|n2];
      [ symmetry in HeqHdeq2; applydup @sub_find_some in HeqHdeq2;
        apply in_combine in HeqHdeq3; repnd; sp | ];[].
      simpl. rw Xsub2eta. rewrite <- HeqHdeq2. simpl. rw  HeqHdeq.
        rewrite lsubst_aux_trivial4; auto.
      * rewrite dom_sub_combine; sp. disjoint_reasoningv.
        GC. allsimpl. clear Hdist Hdist0.
        apply disjoint_sym in H2dis. rw disjoint_flat_map_l in H2dis.
        apply H2dis in HeqHdeq0. allsimpl. disjoint_reasoningv.
      * rw @disjoint_sub_as_flat_map.
        try(rewrite dom_range_combine;try( congruence)).
        revert HeqHdeq0. clear HeqHdeq.
        revert s1. apply disjoint_flat_map_r.
        disjoint_reasoningv.
    + symmetry in HeqHdeq. rw Xsub2eta.
      destructr (sub_find (combine lvi2 lnt2) v) as  [s2|n2];simpl;
      [|rewrite HeqHdeq;rewrite <- HeqHdeq0; sp];[].
      simpl. rewrite <- HeqHdeq0.
      applysym @sub_find_some in HeqHdeq0.
      apply in_combine in HeqHdeq0. repnd.
      rewrite lsubst_aux_trivial4; auto.
      * rw <- Heqlvi1. revert HeqHdeq0. apply disjoint_flat_map_r.
        disjoint_reasoningv.
      * rw @disjoint_sub_as_flat_map.
        rw <- Heqlnt1.
        revert HeqHdeq0. clear HeqHdeq.
        apply disjoint_flat_map_r.
        disjoint_reasoningv.
  - Case "oterm".
    simpl. f_equal. repeat(rewrite map_map). 
    apply eq_maps. intros bt Hin.
    destruct bt as [lv nt].
    unfold compose.
    simpl.
    allsimpl. apply disjoint_sym in Hdist.
    eapply disjoint_lbt_bt2 in Hdist; eauto. repnd.
    apply disjoint_app_l in Hdist0. repnd.
    repeat (rewrite (bvar_renamings_subst_disjoint_bound_vars); [|
      apply disjoint_sub_as_flat_map;try (rewrite <-Heqlnt1);try (rewrite <-Heqlnt2); sp;
      disjoint_reasoning]).
    simpl.
    repeat (rewrite (bvar_renamings_subst_disjoint_bound_vars); [|
      apply disjoint_sub_as_flat_map;try (rewrite <-Heqlnt1);try (rewrite <-Heqlnt2); sp;
      disjoint_reasoningv]).
    simpl. f_equal. disjoint_reasoningv.
    erewrite Hind; eauto;[| | | | |]; eauto 3 with slow;
    pose proof (sub_eta (sub_filter sub1 lv)) as Xsf1eta;
    pose proof (sub_eta (sub_filter sub2 lv)) as Xssf2eta;
    pose proof (sub_eta_length (sub_filter sub1 lv)) as X1len;
    pose proof (sub_eta_length (sub_filter sub2 lv)) as X2len;
    remember (dom_sub (sub_filter sub1 lv)) as lsvi1;
    remember (dom_sub (sub_filter sub2 lv)) as lsvi2;
    remember (range (sub_filter sub1 lv)) as lsnt1;
    remember (range (sub_filter sub2 lv)) as lsnt2;
    rewrite_once Xsub1eta;
    rewrite_once Xsub1eta;
    rewrite_once Xsub1eta;
    rewrite_once Xsub1eta;
    rewrite_once Xsub2eta;
    rewrite_once Xsub2eta;
    rewrite_once Xsub2eta;
    rewrite_once Xsub2eta;[| | | | |]; disjoint_reasoningv; disjoint_sub_filter.
Qed.

Lemma lsubst_nest_swap2 {p} : forall t sub1 sub2,
  let lvi1 := @dom_sub p sub1 in
  let lvi2 := dom_sub sub2 in
  let lnt1 := range sub1 in
  let lnt2 := range sub2 in
  disjoint lvi1 (flat_map free_vars lnt2) (**o/w capture will occur in RHS*)
  -> disjoint lvi2 (flat_map free_vars lnt1) (**o/w capture will occur in LHS*)
  -> disjoint lvi1 lvi2 (**o/w order will matter*)
  -> disjoint (flat_map bound_vars lnt1) (flat_map free_vars lnt2) (**o/w renaming will occur in LHS*)
  -> disjoint (flat_map bound_vars lnt2) (flat_map free_vars lnt1) (**o/w renaming will occur in RHS*)
  -> disjoint (bound_vars t) ((flat_map free_vars lnt1) ++ (flat_map free_vars lnt2)) (**o/w renaming will occur*)
  -> lsubst(lsubst t sub1) sub2 = lsubst(lsubst t sub2) sub1.
Proof.
  intros. change_to_lsubst_aux4.
  apply lsubst_aux_nest_swap2;try(sp;fail);
  try(apply disjoint_sub_as_flat_map;disjoint_reasoning).
  - rw <- @lsubst_lsubst_aux;disjoint_reasoningv.
    apply disjoint_bound_vars_lsubst; disjoint_reasoningv.
  - rw <- @lsubst_lsubst_aux;disjoint_reasoningv.
    apply disjoint_bound_vars_lsubst; disjoint_reasoningv.
Qed.




Lemma lsubst_nest_swap {p} : forall t lvi1 lvo1 lvi2 lvo2,
  length lvi1=length lvo1
  -> length lvi2=length lvo2
  -> disjoint lvi1 lvi2 # disjoint lvi1 lvo2 # disjoint lvi2 lvo1
  -> disjoint (bound_vars t) (lvo1 ++ lvo2)
  -> let sub1:= @var_ren p lvi1 lvo1 in
       let sub2:= var_ren lvi2 lvo2 in
       lsubst(lsubst t sub1) sub2 = lsubst(lsubst t sub2) sub1.
Proof.
  simpl.
  intros.
  unfold var_ren.
  apply lsubst_nest_swap2; spcls; disjoint_reasoningv.
Qed.

Lemma lsubst_aux_nest_swap {p} : forall t lvi1 lvo1 lvi2 lvo2,
  length lvi1=length lvo1
  -> length lvi2=length lvo2
  -> disjoint lvi1 lvi2 # disjoint lvi1 lvo2 # disjoint lvi2 lvo1
  -> disjoint (bound_vars t) (lvo1 ++ lvo2)
  -> let sub1:= @var_ren p lvi1 lvo1 in
       let sub2:= var_ren lvi2 lvo2 in
       lsubst_aux(lsubst_aux t sub1) sub2 = lsubst_aux(lsubst_aux t sub2) sub1.
Proof.
 simpl. intros. unfold var_ren. apply lsubst_aux_nest_swap2;spcls; disjoint_reasoningv.
Qed.



Lemma disjoint_bv_vars {p} : forall t lvi lvo, 
  disjoint lvo (bound_vars t)
  -> disjoint_bv_sub t (@var_ren p lvi lvo).
Proof.
  introv Hdis XX. apply in_var_ren in XX; exrepnd; subst.
  simpl. apply disjoint_cons_l. split;[sp|].
  apply Hdis; auto.
Qed.


Lemma wf_sub_vars {p} : forall lvi lvo, wf_sub (@var_ren p lvi lvo).
Proof.
  introv Hin. apply in_var_ren in Hin; exrepnd; subst.
  constructor.
Qed.

Definition filt_var_ren {p} lvi lvo lv := sub_filter (@var_ren p lvi lvo) lv.


Lemma nth_var_ren_implies {p} : forall lvi lvo v b vd bd n,
  nth n (var_ren lvi lvo) (vd, bd) = (v, b)
  -> length lvi = length lvo
  -> n < length lvi
  -> (nth n lvi v= v) 
      # {vsr : NVar & (b = @vterm p vsr)
      # (nth n lvo vsr= vsr)}.
Proof.
  introv X1X X2X X3X. unfold var_ren in X1X. 
  rewrite combine_nth in X1X;[| rewrite map_length]; auto.
  inversion X1X . pose proof (nth_in _ n ((map (@vterm p) lvo)) ) as XX. 
  rewrite map_length in XX. rewrite <- X2X in XX. lapply (XX bd); auto.
  intro Hin. apply in_map_iff in Hin. exrepnd.
  split; auto. 
  apply nth_indep; auto.
  exists a; auto. sp.
  assert (nth n (map vterm lvo) bd =nth n (map vterm lvo) (vterm a))  as XXX by
     (apply nth_indep; repeat(rewrite map_length); auto;congruence ).
  rewrite XXX in Hin0. rewrite map_nth in Hin0. inversion Hin0. rewrite H2. auto.
Qed.


Definition filt_combine {p} lvi lnt lv := @sub_filter p (combine lvi lnt) lv.

(* instead of var_Ren, we will need swapping *)
Lemma lsubst_aux_nest_same_str {p} :
  forall t lvi lvio lnt lf,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map (@free_vars p) lnt)) (bound_vars t ++ lf)
  -> disjoint lvio (free_vars t)
  -> lsubst_aux (lsubst_aux t (filt_var_ren lvi lvio lf)) (filt_combine lvio lnt lf)
     = lsubst_aux t (filt_combine lvi lnt lf).
Proof.
  nterm_ind1s t as [v|o lbt Hind] Case; auto;
  introv Hl1 Hl2 Hnr Hdisb Hdisf.
  Focus 2.
  Case "oterm". (**this part is easier!!*)
    allsimpl. f_equal. rewrite map_map. eapply eq_maps; eauto.
    intros bt Hinb. destruct bt as [lv nt].
    unfold compose.
    allsimpl. apply disjoint_app_r in Hdisb. repnd.
    rename Hdisb into Hdisl.
    rename Hdisb0 into Hdisb.
    eapply disjoint_lbt_bt2 in Hdisb; eauto. repnd.
    apply disjoint_app_l in Hdisb0. repnd.
    simpl. f_equal.
    unfold filt_var_ren. unfold filt_combine.
    repeat(rewrite <- sub_filter_app_r).
    eapply Hind; eauto 3 with slow;[disjoint_reasoningv|].
    rw disjoint_flat_map_r in Hdisf. apply Hdisf in Hinb.
    simpl in Hinb. rw <- disjoint_remove_nvars_l in Hinb.
    apply remove_nvars_unchanged in Hdisb1.
    rewrite Hdisb1 in Hinb. trivial.


  Case "vterm".

  simpl. destructr (sub_find (@filt_var_ren p lvi lvio lf) v) as [s1st|n1n].
  - apply symmetry in HeqHdeq. rename HeqHdeq into s1s.
    apply sub_find_sub_filter_some in s1s. repnd.
    apply sub_find_first in s1s0. exrepnd.
    unfold var_ren in s1s1.
    rewrite dom_sub_combine in s1s1;
     [| rewrite map_length; congruence] .
    unfold var_ren in s1s0.
    rewrite length_combine_eq
    in s1s0;[| rewrite map_length]; auto. 
    apply nth_var_ren_implies in s1s2;auto. exrepnd. rename vsr into vio.
    simpl. rewrite s1s2. simpl.
    destructr (sub_find (filt_combine lvio lnt lf) vio) as [s2st|n2n].

    + apply symmetry in HeqHdeq. rename HeqHdeq into s2s.
      apply sub_find_sub_filter_some in s2s. repnd.
      apply sub_find_first in s2s0. exrepnd.
      unfold var_ren in s2s0. rewrite length_combine_eq
      in s2s0;spc.
      rw combine_nth in s2s2;spc. inverts s2s2 as s2s3 s2s4.
      simpl. rewrite <- Hl1 in s1s0.
     (** clear s2s1. it cannot rule out case when n>n0*) 
      pose proof (no_repeats_index_unique2
               _ _ _ _ _ _ Hnr s1s0 s2s0 s1s4 s2s3) as X99.
      destruct X99. GC.  clear s1s2. clear s1st.
      destructr (sub_find (filt_combine lvi lnt lf) v) as [s3st|n3n].
      * apply symmetry in HeqHdeq. rename HeqHdeq into s3s.
        apply sub_find_sub_filter_some in s3s. repnd.
        apply sub_find_first in s3s0. exrepnd.
        unfold var_ren in s3s0. rewrite length_combine_eq
        in s3s0;spc.
        rw combine_nth in s3s2;spc. inverts s3s2 as s3s3 s3s4.
        simpl.  rewrite  Hl1 in s1s0.
        allfold (@dom_sub p). 
        allunfold (@var_ren p). spcls. 
        assert (n0<n \/ n0=n \/ n<n0) as Htri by omega.
        (dorn Htri);[|(dorn Htri)];
          try (apply s1s1 in Htri); cpx;
          try (apply s3s1 in Htri); cpx.
        destruct Htri. GC. apply nth_select3 in s3s4;[| congruence].
        apply nth_select3 in s2s4; congruence.
      * rename HeqHdeq into n3n. symmetry in n3n. 
        apply sub_find_sub_filter_none in n3n. dorn n3n; [ |sp(**see s1s*)].
        apply sub_find_none2 in n3n.        
        clear s1s1. apply nth_in2 in s1s3;[| congruence]. allunfold (@var_ren).
        simpl. spcls. sp.
    + rename HeqHdeq into n2n. symmetry in n2n.
      apply sub_find_sub_filter_none in n2n. dorn n2n.
      * apply sub_find_none2 in n2n. 
        apply nth_in2 in s1s4;[| congruence]. allunfold (@var_ren).
        simpl. spcls. sp. 
      * apply nth_in2 in s1s4;[| congruence].
        assert (disjoint lvio lf) as X99 by disjoint_reasoningv.
        apply X99 in s1s4; sp.
  - apply disjoint_singleton_r in Hdisf. allfold @dom_sub.
    assert ((dom_sub (combine lvi lnt)) = lvi) as Xrw  by (spcls;sp).
    rename HeqHdeq into n1n. symmetry in n1n. 
    apply sub_find_sub_filter_none in n1n. 
    assert(sub_find (combine lvi lnt) v = None[+]LIn v lf) as X99.
     + dorn n1n;[left|right]; auto.
       apply sub_find_none2 in n1n. 
       unfold var_ren in n1n. rewrite dom_sub_combine in n1n
        ;[| rewrite map_length; congruence].
       rewrite <- Xrw in n1n. apply sub_find_none_iff in n1n. rewrite n1n.
       refl.
    + apply sub_find_sub_filter_none in X99. 
      unfold filt_combine. rewrite X99.
      assert ((dom_sub (combine lvio lnt)) = lvio) as X2rw by (spcls;sp).
      rewrite <- X2rw in Hdisf. apply sub_find_none_iff in Hdisf.
      simpl.
      assert(sub_find (combine lvio lnt) v = None[+]LIn v lf)
         as X98 by (left;sp).
      apply sub_find_sub_filter_none in X98.
      rewrite X98. refl.
Qed.

Lemma lsubst_nest_same_str {p} :
  forall t lvi lvio lnt lf,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map (@free_vars p) lnt)) (bound_vars t ++ lf)
  -> disjoint lvio (free_vars t)
  -> lsubst (lsubst t (filt_var_ren lvi lvio lf)) (filt_combine lvio lnt lf)
     = lsubst t (filt_combine lvi lnt lf).
Proof.
  intros. change_to_lsubst_aux4;
  try(apply lsubst_aux_nest_same_str;try(sp;fail));
  apply disjoint_sym;
    rw <- @disjoint_sub_as_flat_map;
  try(apply sub_filter_sat).
  - rw @disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
  - rw @disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
  - rw <- @lsubst_lsubst_aux; disjoint_reasoningv.
    rw @boundvars_lsubst_vars2; spcls; disjoint_reasoningv.
    + rw @disjoint_sub_as_flat_map. spcls. sp.
    + apply allvars_sub_filter.
    + apply sub_filter_sat. rw @disjoint_sub_as_flat_map.
      spcls. disjoint_reasoningv.
  - rw @disjoint_sub_as_flat_map; spcls; disjoint_reasoningv.
Qed.

Lemma lsubst_nest_vars_same_str {p} :
  forall t lvi lvio lvo lf,
  length lvio=length lvi
  -> length lvio=length lvo
  -> no_repeats lvio
  -> disjoint (lvio++lvo) (bound_vars t ++ lf)
  -> disjoint lvio (free_vars t)
  -> lsubst (lsubst t (filt_var_ren lvi lvio lf)) (filt_var_ren lvio lvo lf)
     = lsubst t (@filt_var_ren p lvi lvo lf).
Proof.
    intros. apply lsubst_nest_same_str;spc; spcls;sp.
Qed.

Lemma lsubst_nest_same {p} :
  forall t lvi lvio lnt,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map (@free_vars p) lnt)) (bound_vars t)
  -> disjoint lvio (free_vars t)
  -> lsubst (lsubst t (var_ren lvi lvio)) (combine lvio lnt)
     = lsubst t (combine lvi lnt).
Proof.
  intros.
  pose proof (sub_filter_nil_r (@var_ren p lvi lvio)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvio lnt)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvi lnt)) as K.
  rewrite <- K. clear K.
  apply lsubst_nest_same_str; simpl; auto.
  rewrite app_nil_r. auto.
Qed.

Lemma lsubst_aux_nest_same {p} :
  forall t lvi lvio lnt,
  length lvio=length lvi
  -> length lvio=length lnt
  -> no_repeats lvio
  -> disjoint (lvio++(flat_map (@free_vars p) lnt)) (bound_vars t)
  -> disjoint lvio (free_vars t)
  -> lsubst_aux (lsubst_aux t (var_ren lvi lvio)) (combine lvio lnt)
     = lsubst_aux t (combine lvi lnt).
Proof.
  intros.
  pose proof (sub_filter_nil_r (@var_ren p lvi lvio)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvio lnt)) as K.
  rewrite <- K. clear K.
  pose proof (sub_filter_nil_r (combine lvi lnt)) as K.
  rewrite <- K. clear K.
  apply lsubst_aux_nest_same_str; simpl; auto.
  rewrite app_nil_r. auto.
Qed.

Lemma lsubst_nest_vars_same {p} :
  forall t lvi lvio lvo,
  length lvio=length lvi
  -> length lvio=length lvo
  -> no_repeats lvio
  -> disjoint (lvio++lvo) (bound_vars t)
  -> disjoint lvio (free_vars t)
  -> lsubst (lsubst t (var_ren lvi lvio)) (var_ren lvio lvo)
     = lsubst t (@var_ren p lvi lvo).
Proof.
    intros. apply lsubst_nest_same;spc;spcls;sp.
Qed.

Lemma lsubst_aux_nest_vars_same {p} :
  forall t lvi lvio lvo,
  length lvio=length lvi
  -> length lvio=length lvo
  -> no_repeats lvio
  -> disjoint (lvio++lvo) (bound_vars t)
  -> disjoint lvio (free_vars t)
  -> lsubst_aux (lsubst_aux t (var_ren lvi lvio)) (var_ren lvio lvo)
     = lsubst_aux t (@var_ren p lvi lvo).
Proof.
    intros. apply lsubst_aux_nest_same;spc;spcls;sp.
Qed.



Theorem free_vars_lsubst_aux2 {p} :
  forall nt sub,
    @disjoint_bv_sub p nt sub
    -> forall v,
         LIn v (free_vars (lsubst_aux nt sub))
         -> (LIn v (free_vars nt) # ! LIn v (dom_sub sub))
                [+] {v' : NVar
                     & {t : NTerm
                     & LIn (v',t) sub # LIn v' (free_vars nt) # LIn v (free_vars t)}}.
Proof. nterm_ind1 nt as [vn|o lbt Hind] Case; introv Hdis Hin; auto.
   Case "vterm". induction sub as [| (vs,ts) sub]. 
   - rw @lsubst_aux_nil in Hin. left; split; auto. sp. 
   - destruct (eq_var_dec vn vs) as [? | Hneq];
      subst;simpl in Hin;
      ((rw <- beq_var_refl in Hin;auto) 
          || (rw not_eq_beq_var_false in Hin;auto)).
      + right. exists vs ts. sp; auto.
      + cases (sub_find sub vn) as Hf.
          * applydup @sub_find_some in Hf.
             right; exists vn n; split; auto. right;auto. simpl. split; auto.
          * left;split;auto. allsimpl;subst. introv Hc. dorn Hc; subst; sp.
            subst. apply sub_find_none2 in Hf. sp.
  - Case "oterm".
    simpl in Hin. rw lin_flat_map in Hin.
    destruct Hin as [bt' Hin]. repnd. apply in_map_iff in Hin0.
    destruct Hin0 as [bt Hin0]. repnd. subst. destruct bt as [lv nt].
    simpl in Hin.
    simpl in Hin. rw in_remove_nvars in Hin. repnd.
    apply Hind with (lv:=lv) in Hin0; auto.
    destruct Hin0 as [Hl | Hr].
    + left. simpl. repnd. split. 
       *  apply lin_flat_map. eexists; split; eauto. simpl.
          apply in_remove_nvars. split; auto.
       * introv Hc. apply Hl.
         rewrite <- dom_sub_sub_filter.
         apply in_remove_nvars. sp.
    + right. parallel vs Hr. parallel ts Hr. repnd. sp;auto.
      * rw @in_sub_filter in Hr0. repnd; auto.
      * simpl. apply lin_flat_map. eexists; split; eauto. simpl.
        apply in_remove_nvars. split; auto. rw @in_sub_filter in Hr0.
        repnd; auto.
    + eapply disjoint_bv_sub_ot in Hdis; eauto.
Qed.

Theorem free_vars_lsubst2 {p} :
  forall nt sub,
    @disjoint_bv_sub p nt sub
    -> forall v,
         LIn v (free_vars (lsubst nt sub))
         -> (LIn v (free_vars nt) # ! LIn v (dom_sub sub))
                [+] {v' : NVar
                     & {t : NTerm
                     & LIn (v',t) sub # LIn v' (free_vars nt) # LIn v (free_vars t)}}.
Proof.
  introns Hd. change_to_lsubst_aux4.
  apply free_vars_lsubst_aux2;try(sp;fail);
  try(apply disjoint_sub_as_flat_map;disjoint_reasoning).
  - rw @disjoint_sub_as_flat_map. disjoint_reasoningv.

  - rw <- @lsubst_lsubst_aux;sp; disjoint_reasoning.
Qed.


Lemma subst_mk_false {p} :
  forall v t,
    ! LIn nvarx (free_vars t)
    -> (subst mk_false v t = @mk_false p).
Proof.
  unfold subst. unfold lsubst. introv Hin.
  change_to_lsubst_aux4; simpl; disjoint_reasoningv;sp.
  allsimpl. rw memvar_dmemvar. clear d.
  cases_ifn Hmem;
  rw in_single_iff in Hmem;simpl;sp.
  rw beq_deq. cases_if; sp.
Qed.

Lemma covered_cequiv {p} :
  forall a b vs,
    covered (@mk_cequiv p a b) vs
    <=> covered a vs
        # covered b vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_approx {p} :
  forall a b vs,
    covered (@mk_approx p a b) vs
    <=> covered a vs
        # covered b vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_fix {p} :
  forall f s, covered (@mk_fix p f) s <=> covered f s.
Proof.
  unfold mk_fix, covered; intros; simpl.
  rw remove_nvars_nil_l; rw app_nil_r; sp.
Qed.

Lemma covered_id {p} :
  forall s, @covered p mk_id s.
Proof.
  unfold mk_id, covered; simpl; sp.
Qed.
Hint Immediate covered_id.

Lemma covered_bot {p} :
  forall s, @covered p mk_bot s.
Proof.
  unfold mk_bot, mk_bottom.
  intro; rw @covered_fix; sp.
Qed.
Hint Immediate covered_bot.

Lemma covered_mk_false {p} :
  forall s, @covered p mk_false s.
Proof.
  intro; rw @covered_approx; sp.
Qed.
Hint Immediate covered_mk_false.

Lemma covered_top {p} :
  forall s, @covered p mk_top s.
Proof.
  intro; rw @covered_isect; sp.
Qed.
Hint Immediate covered_top.

Lemma covered_lam {p} :
  forall v b vs,
    covered (@mk_lam p v b) vs
    <=> covered b (v :: vs).
Proof.
  unfold covered; sp; simpl.
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.


Lemma lsubst_lsubst_aux2 {p} : forall t lvi lvo, 
  disjoint (bound_vars t) (lvo)
  -> length lvi = length lvo
  -> lsubst t (var_ren lvi lvo) = lsubst_aux t (@var_ren p lvi lvo).
Proof.
  introv Hdis Hlen. unfold lsubst. rw @flat_map_free_var_vars_range;sp.
  cases_if; sp.
Qed.

Lemma sub_mk_renames2_length2 {p} : forall lva1 lva2 lv lsr ssr, 
(lsr, ssr) = @sub_mk_renames2 p lv lva1 lva2
  -> length lsr = length lv.
Proof.
introv HH. pose proof (@sub_mk_renames2_length p lv lva1 lva2) as XX.
  rw <- HH in XX. sp.
Qed.

Lemma cover_vars_dom_csub_eq {p} :
  forall t s1 s2,
    cover_vars t s1
    -> dom_csub s1 = @dom_csub p s2
    -> cover_vars t s2.
Proof.
  introv cv eq.
  allrw @cover_vars_eq.
  rw <- eq; sp.
Qed.

(*
Lemma cover_vars_esquash :
  forall T sub,
    cover_vars (mk_esquash T) sub <=> cover_vars T sub.
Proof.
  sp; repeat (rw cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.
*)

Lemma cover_vars_apply2 {p} :
  forall a b c sub,
    cover_vars (@mk_apply2 p a b c) sub
    <=> cover_vars a sub
        # cover_vars b sub
        # cover_vars c sub.
Proof.
  sp; repeat (rw cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l); sp; split; sp.
Qed.

Definition subst_axiom {p} (lv : list NVar) : @Substitution p :=
  map (fun v => (v,mk_axiom)) lv.

Definition csubst_axiom {p} (lv : list NVar) : @CSub p :=
  map (fun v => (v,mkc_axiom)) lv.

Hint Resolve isprogram_axiom.


Lemma prog_subst_axiom {p} : forall lv,
  prog_sub (@subst_axiom p lv).
Proof.
  introv Hin.
  rw in_map_iff in Hin.
  exrepnd. inverts Hin0.
  eauto.
Qed.

Hint Resolve prog_subst_axiom.

Lemma close_with_axiom {p} : forall t, 
  nt_wf t
  -> let sub := @subst_axiom p (free_vars t) in
      (prog_sub sub) # (isprogram (lsubst t sub)).
Proof.
  introv Hnt. pose proof (@prog_subst_axiom p (free_vars t)) as Hpr.
  simpl. split; auto;[].
  apply isprogram_lsubst;try(sp;fail).
  introv Hin. apply in_map_iff. exists (v, @mk_axiom p). split; auto.
    unfold subst_axiom. apply in_map_iff. eexists;eauto.
Qed.

Ltac dlmap_find sn :=
match goal with
| [  |- context[lmap_find deq_nvar ?s ?v]] => 
  let sns := fresh sn "s" in
  remember (lmap_find deq_nvar s v) as sn;
  destruct sn as [sns |]
| [  H:context[lmap_find deq_nvar ?s ?v] |- _ ] => 
  let sns := fresh sn "s" in
  remember (lmap_find deq_nvar s v) as sn;
  destruct sn as [sns |]
end.
  

Ltac dsub_find2 sn :=
match goal with
| [  |- context[sub_find ?s ?v]] => 
  let sns := fresh sn "s" in
  remember (sub_find s v) as sn;
  let H := get_last_hyp tt in
  let H' := fresh H "l" in
  (destruct sn as [sns |];
  symmetry in H;
  try (pose proof (sub_find_some _ _ _  H) as H');
  try (pose proof (sub_find_none2 _ _  H) as H'))
| [ H: context[sub_find ?s ?v] |- _ ] => 
  let sns := fresh sn "s" in
  remember (sub_find s v) as sn;
  destruct sn as [sns |]
end.

Lemma prog_lsubst_aux_app {p} : forall nt sub sub2,
  disjoint (free_vars (lsubst_aux nt sub)) (@dom_sub p sub2)
  -> disjoint_bv_sub nt sub
  -> prog_sub sub2
  -> lsubst_aux nt sub = lsubst_aux nt (sub++sub2).
Proof.
  nterm_ind1 nt as [v|o lbt Hind] Case. introv; auto.

  - Case "vterm".
    simpl. dsub_find2 sv.
    symmetry in Heqsv. 
    + rw @sub_find_app. rw <- Heqsv;sp.
    + simpl. introv Hdis Hdbv Hprog. disjoint_reasoningv.
      dsub_find sa;sp. applysym @sub_find_some in 
      Heqsa.  apply in_dom_sub in Heqsa;sp.
      rw @dom_sub_app in Heqsa.
      rw in_app_iff in Heqsa.
      cpx.

  - Case "oterm".
    introv Hpr Hbv Hps. simpl. f_equal. apply eq_maps.
    intros bt Hin. destruct bt as [blv bnt].
    simpl. f_equal. rw @sub_filter_app.
    Hint Resolve sub_filter_sat.
    eapply Hind; allunfold @prog_sub; allunfold @disjoint_bv_sub; eauto.
    + allsimpl. 
      apply lin_lift with (f:=fun t : BTerm => lsubst_bterm_aux t sub) in Hin.
    eapply disjoint_flat_map_l in Hpr; eauto;[].
      allsimpl. apply disjoint_remove_nvars_l in Hpr.
      rw @dom_sub_sub_filter in Hpr. sp.
    + apply sub_filter_sat. sp.
      eapply sub_range_sat_implies; eauto.
      introv Hdis. allsimpl.
      eapply disjoint_flat_map_r in Hdis; eauto.
      allsimpl. disjoint_reasoningv.
Qed.

Lemma range_app {p} : forall s1 s2, @range p (s1++s2) =
  (range s1) ++ (range s2).
Proof.
  introv. unfold range. rw map_app.
  sp.
Qed.

Lemma sub_keep_first_sat {p} : forall P sub lv,
  @sub_range_sat p sub P
  -> sub_range_sat (sub_keep_first sub lv) P.
Proof. introv Hall hsub. apply in_sub_keep_first in hsub. repnd.
  apply sub_find_some in hsub0. apply Hall in hsub0; auto.
Qed.


Theorem sub_keep_first_nest {p} :
  forall sub vs1 vs2,
    (forall v, LIn v vs2 -> LIn v vs1 [+] ! LIn v (@dom_sub p sub))
    -> sub_keep_first (sub_keep_first sub vs1) vs2 =sub_keep_first sub vs2.
Proof.
  induction sub as [| (hv,ht) sub Hind]; introv Hin; [reflexivity | allsimpl].
  simpl. allrw memvar_dmemvar. 
  cases_ifd h1v; simpl; repeat (rw memvar_dmemvar); cases_ifd h2v;
  repeat (rw memvar_dmemvar); try(cases_ifd h3v);cpx.
  - f_equal. rw Hind;try(spc;fail).  introv H2in.
    allrw in_remove_nvars. repnd. apply Hin in H2in0.
    dorn H2in0;[left;split|right];cpx.   
  - rw Hind;try(spc;fail).  introv H2in.
    allrw in_remove_nvars. repnd. applydup Hin in H2in.
    dorn H2in0;[left;split|right];cpx;[].
    simpl. introv Hc; dorn Hc; subst; sp.
  - provefalse. apply Hin in h2vt. dorn h2vt;sp. 
  - rw Hind;try(spc;fail).  introv H2in.
    allrw in_remove_nvars. repnd. applydup Hin in H2in.
    dorn H2in0;[left|right];cpx.
Qed.


(** w/o the hypothesis, this does not hold for lsubst
    might occur only in RHS. if it happens in both,
    the new variables might be different as
    RHS has to avoid more variables.
    w/o hypothesis, we can prove alpha equality *)
Lemma lsubst_aux_trim {p} :
  forall t sub,
    (forall v u, LIn (v, u) sub -> disjoint (@free_vars p u) (bound_vars t))
    -> lsubst_aux t sub = lsubst_aux t (sub_keep_first sub (free_vars t)).
Proof.
  nterm_ind1 t as [v|o lbt Hind] Case;  introv Hdis; auto.
  - Case "vterm". simpl.
    dsub_find2 ds.
    + apply sub_keep_first_singleton_r_some in Heqds.
      rw Heqds. simpl. rw beq_deq. cases_if; sp.
    + apply sub_keep_first_singleton_r_none in Heqds.
      rw Heqds; sp.

  - Case "oterm". simpl.  f_equal.
    apply eq_maps. intros bt Hin.
    destruct bt as [lv nt].
    simpl.
    f_equal.
    rw <- @sub_keep_first_sub_filter.
    symmetry.
    rewrite Hind with (lv := lv); eauto;
    [ |
        apply sub_keep_first_sat;
        apply sub_filter_sat;
        disjoint_flat; sp;fail].

       assert( (sub_keep_first (sub_keep_first (sub_filter sub lv) 
        (flat_map free_vars_bterm lbt)) (free_vars nt)) =
           sub_keep_first (sub_filter sub lv) (free_vars nt)) as Hskeq. 
       + apply sub_keep_first_nest. introv Hinf. destruct (in_nvar_list_dec v lv). 
          * right. rw <- @dom_sub_sub_filter. intro HC. apply in_remove_nvars in HC. sp. 
          * left. apply lin_flat_map. eexists; split; eauto. 
                    simpl. apply in_remove_nvars; split; trivial.  
       + rw Hskeq. 
           symmetry. eapply Hind; eauto. 
           apply sub_filter_sat. disjoint_flat. disjoint_reasoning.
Qed.


Lemma in_sub_keep_first_app {p} :
  forall lv1 lv2 sub v u,
  LIn (v,u) (@sub_keep_first p sub (lv1++lv2))
  -> LIn (v,u) (sub_keep_first sub lv1) [+]
     LIn (v,u) (sub_keep_first sub lv2). 
Proof. introv Hin.
  apply in_sub_keep_first in Hin.
  repnd.
  apply in_app_iff in Hin. dorn Hin;[left|right];
  apply in_sub_keep_first;sp.
Qed.

Ltac lsubst_lsubst_aux_eq H :=
match goal with
| [ |- context[lsubst ?t ?sub]] =>
  assert (lsubst t sub = lsubst_aux t sub) as H;
  [change_to_lsubst_aux4; sp ;fail | rw H]
end.

Ltac lsubst_lsubst_aux_eq_hyp H Hyp :=
let T := type of Hyp in 
match T with
|  context[lsubst ?t ?sub] => 
  assert (lsubst t sub = lsubst_aux t sub) as H;
  [change_to_lsubst_aux4; sp  | rewrite H in Hyp ]
end.

Lemma disjoint_sym_eauto: forall (T : [univ]) (l1 l2 : list T),
       disjoint l1 l2 -> disjoint l2 l1.
Proof.
  introv. apply disjoint_sym; auto.
Qed.

Fixpoint sub_range_rel {p} (R : bin_rel NTerm) (subl subr : @Sub p) : [univ] :=
match (subl, subr) with 
| ([],[]) => True
| ((vl,tl) :: sl , (vr,tr) :: sr) => (vl=vr # R tl tr # sub_range_rel R sl sr)
| ( _ , _) => False
end.


Lemma sub_range_rel_app {p} : forall R subl1 subl2 subr1 subr2,
  (@sub_range_rel p R subl1 subl2 # sub_range_rel  R subr1 subr2)
  ->   sub_range_rel R (subl1 ++ subr1)  (subl2 ++ subr2).
Proof.
  induction subl1 as [|(v1,t1) subl1 Hind]; introv Hsr;
  destruct subl2 as [|(v2,t2) subl2]; inverts Hsr; allsimpl;sp.
Qed.

Lemma sub_range_refl {p} : forall R,
  refl_rel R -> refl_rel (@sub_range_rel p R).
Proof.
  introv Hr. unfold refl_rel in Hr. unfold refl_rel.
  induction x as [|(v1,t1) subl1 Hind];  allsimpl;sp.
Qed.

Lemma sub_range_sat_nil {p} : forall P, @sub_range_sat p [] P.
Proof.
  unfold sub_range_sat. introv HH.
  inverts HH.
Qed.

Hint Resolve disjoint_sym_eauto disjoint_flat_map_r : slow.

Lemma cover_vars_upto_lam {p} :
  forall vs v b sub,
    @cover_vars_upto p (mk_lam v b) sub vs
    <=> cover_vars_upto b (csub_filter sub [v]) (v :: vs).
Proof.
  introv.
  unfold cover_vars_upto; simpl.
  rw app_nil_r.
  rw subvars_remove_nvars.
  rw @dom_csub_csub_filter.
  allrw subvars_prop; simpl; split; sp.
  apply_in_hyp pp; allrw in_app_iff; allrw in_single_iff; sp.
  rw in_remove_nvars; rw in_single_iff.
  generalize (deq_nvar v x); intro o; sp.
  right; right; sp.
  apply_in_hyp pp.
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
Qed.

Lemma cover_vars_upto_isect {p} :
  forall vs a v b sub,
    @cover_vars_upto p (mk_isect a v b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b (csub_filter sub [v]) (v :: vs).
Proof.
  sp; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw subvars_prop; simpl; split; sp; apply_in_hyp pp;
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  generalize (deq_nvar v x); intro o; sp.
  right; right; sp.
Qed.

Lemma cover_vars_upto_eisect {p} :
  forall vs a v b sub,
    @cover_vars_upto p (mk_eisect a v b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b (csub_filter sub [v]) (v :: vs).
Proof.
  sp; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw subvars_prop; simpl; split; sp; apply_in_hyp pp;
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  generalize (deq_nvar v x); intro o; sp.
  right; right; sp.
Qed.

Lemma cover_vars_upto_disect {p} :
  forall vs a v b sub,
    @cover_vars_upto p (mk_disect a v b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b (csub_filter sub [v]) (v :: vs).
Proof.
  sp; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw subvars_prop; simpl; split; sp; apply_in_hyp pp;
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  generalize (deq_nvar v x); intro o; sp.
  right; right; sp.
Qed.

Lemma cover_vars_upto_set {p} :
  forall vs a v b sub,
    @cover_vars_upto p (mk_set a v b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b (csub_filter sub [v]) (v :: vs).
Proof.
  sp; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw subvars_prop; simpl; split; sp; apply_in_hyp pp;
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  generalize (deq_nvar v x); intro o; sp.
  right; right; sp.
Qed.

Lemma cover_vars_upto_tunion {p} :
  forall vs a v b sub,
    @cover_vars_upto p (mk_tunion a v b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b (csub_filter sub [v]) (v :: vs).
Proof.
  sp; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw subvars_prop; simpl; split; sp; apply_in_hyp pp;
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  generalize (deq_nvar v x); intro o; sp.
  right; right; sp.
Qed.

Lemma cover_vars_upto_quotient {p} :
  forall vs a v1 v2 b sub,
    @cover_vars_upto p (mk_quotient a v1 v2 b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b (csub_filter sub [v1,v2]) (v1 :: v2 :: vs).
Proof.
  sp; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw subvars_prop; simpl; split; sp; apply_in_hyp pp;
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp;
  generalize (deq_nvar v1 x); generalize (deq_nvar v2 x); intro o; sp;
  right; right; right; allsimpl; sp.
Qed.

Lemma cover_vars_upto_base {p} :
  forall vs sub,
    @cover_vars_upto p mk_base sub vs.
Proof.
  unfold cover_vars_upto; sp.
Qed.
Hint Immediate cover_vars_upto_base.

Lemma cover_vars_upto_base_iff {p} :
  forall vs sub,
    @cover_vars_upto p mk_base sub vs <=> True.
Proof.
  intros; split; sp.
Qed.

Lemma cover_vars_upto_free_from_atom {p} :
  forall vs a b c sub,
    @cover_vars_upto p (mk_free_from_atom a b c) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs
        # cover_vars_upto c sub vs.
Proof.
  intros; unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma cover_vars_upto_free_from_atoms {p} :
  forall vs a b sub,
    @cover_vars_upto p (mk_free_from_atoms a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  intros; unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma cover_vars_upto_equality {p} :
  forall vs a b T sub,
    @cover_vars_upto p (mk_equality a b T) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs
        # cover_vars_upto T sub vs.
Proof.
  intros; unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma cover_vars_upto_tequality {p} :
  forall vs a b sub,
    @cover_vars_upto p (mk_tequality a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  intros; unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma cover_vars_upto_apply {p} :
  forall vs a b sub,
    @cover_vars_upto p (mk_apply a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  intros; unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma cover_vars_upto_var {p} :
  forall vs v sub,
    @cover_vars_upto p (mk_var v) sub vs
    <=> LIn v (vs ++ dom_csub sub).
Proof.
  intros; unfold cover_vars_upto; simpl.
  rw subvars_singleton_l; sp.
Qed.

Lemma cover_vars_upto_csub_filter_disjoint {p} :
  forall t s vs1 vs2,
    eqvars vs1 vs2
    -> disjoint (free_vars t) vs1
    -> (cover_vars_upto t (@csub_filter p s vs1) vs2
        <=> cover_vars t s).
Proof.
  introv eqv disj.
  unfold cover_vars_upto.
  rw @cover_vars_eq.
  allrw subvars_prop; split; sp; allrw in_app_iff;
  allrw @dom_csub_csub_filter; allrw in_remove_nvars.
  applydup X in X0; allrw in_app_iff; sp.
  apply disj in X0.
  allrw eqvars_prop.
  apply eqv in l; sp.
  allrw in_remove_nvars; sp.
  applydup X in X0.
  apply disj in X0; sp.
Qed.

Lemma le_sub_range_rel {p} : forall R1 R2, le_bin_rel R1 R2
  -> le_bin_rel (@sub_range_rel p R1) (sub_range_rel R2).
Proof.
  introv Hl. unfold le_bin_rel; induction a as [| (va,ta) suba Hind];
  intros subb Hs1; destruct subb as [| (vb,tb) subb]; simpl; invertsn Hs1;
  auto;[]; repnud Hl; dands; auto.
Qed.


Lemma le_binrel_sub_un {p} : forall R Rul Rur,
   le_bin_rel R (indep_bin_rel Rul Rur)
   -> le_bin_rel (@sub_range_rel p R)
    (indep_bin_rel (fun s => sub_range_sat s Rul) (fun s => sub_range_sat s Rur)).
Proof.
  introv Hle.
   unfold le_bin_rel, indep_bin_rel; induction a as [| (va,ta) suba Hind];
  intros subb Hs1; destruct subb as [| (vb,tb) subb]; dands; dands; 
  introv Hin; try(invertsn Hin); repnud Hle; allsimpl;
  unfold indep_bin_rel in Hle;cpx; subst;
  try(apply Hle in r); repnd; auto;
  apply Hind in Hs1;
  repnd;allunfold @sub_range_sat; eauto.
Qed.


Lemma isprogram_lsubst3 {p} :
  forall t : NTerm,
  forall sub : @Substitution p,
    isprogram t
    -> prog_sub sub
    -> isprogram (lsubst t sub).
Proof.
  introv Hpr Hps.
  apply isprogram_lsubst; eauto with slow;[].
  repnud Hpr.
  rw Hpr0.
  introv Hin; inverts Hin.
Qed.

Lemma sub_filter_pair_dom {p} : forall lvf R lvi lnta lntb,
  length lvi = length lnta
  ->  length lvi = length lntb
  -> bin_rel_nterm R lnta lntb
  ->  {lvi' : list NVar $ { lnta', lntb' : list (@NTerm p) $ sub_filter (combine lvi lnta) lvf = combine lvi' lnta'
                            # sub_filter (combine lvi lntb) lvf = combine lvi' lntb'
                            # length lvi' = length lnta'
                            # length lvi' = length lntb'
                            # bin_rel_nterm R lnta' lntb'
                                   (** pairwise relationships are preserved *)
                                                                                 } }.
Proof.
  induction lvi as [| v lvi Hind]; introns Hl.
  - repeat (eapply existT with (x:=nil)). dands; spc. apply binrel_list_nil.
  - simpl. destruct lnta as [|ha lnta];invertsn Hl;
     destruct lntb as [| hb  lntb];invertsn Hl0;  allsimpl.
    rw memvar_dmemvar. rw memvar_dmemvar. 
    apply binrel_list_cons in Hl1. repnd. duplicate Hl0.
    cases_ifd Ha; eapply Hind with (lnta := lnta) in Hl0 ; eauto;[].
    exrepnd. exists (v::lvi') (ha :: lnta') (hb :: lntb').
    allsimpl. dands; spc; try (f_equal;spc).
    apply binrel_list_cons; sp.
Qed.

Lemma lsubst_bterm_trivial {p} : forall bt sub,
  isprogram_bt bt
  -> @prog_sub p sub
  -> lsubst_bterm_aux bt sub = bt.
Proof.
  introv Hpr Hps.
  destruct bt as [lv nt].
  simpl. f_equal.
  rw @lsubst_aux_trivial. sp.
  introv Hin.
  apply in_sub_filter in Hin.
  repnd.
  apply Hps in Hin0.
  split; auto;[].
  repnud Hpr.
  invertsn Hpr0.
  rw nil_remove_nvars_iff in Hpr0.
  spc.
Qed.

Ltac disjoint_flat3 := allunfold disjoint_bv_sub; allunfold sub_range_sat; allsimpl;
  match goal with
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint (flat_map ?f (range ?sub)) ?l)  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) H2 _ _ H))
|[ H: (LIn (_,?t) ?sub), H2 : (disjoint ?l (flat_map ?f (range ?sub)))  |- disjoint (?f ?t) ?l ] =>
  exact ((snd (disjoint_sub_as_flat_map _ _ _) 
  (disjoint_sym_impl _ _ _ H2) _ _ H))
|[ H: (LIn _ ?tl), H2 : (disjoint _ (flat_map _ ?tl))  |- _ ] =>
    apply ((tiff_fst (disjoint_flat_map_r _ _ _ _ _)) H2) in H; hide_hyp H
|[ H: (LIn _ ?tl), H2 : (disjoint (flat_map _ ?tl) _)  |- _ ] =>
    apply ((tiff_fst (disjoint_flat_map_l _ _ _ _ _)) H2) in H; hide_hyp H
| [ H:( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) |- _ ] =>
      apply disjoint_sub_as_flat_map in H
| [ |- ( forall _ _, LIn (_, _) _
                    -> disjoint (free_vars _) _) ] =>
      apply disjoint_sub_as_flat_map
end.

Ltac fold_lsubst_ot :=
match goal with
[ |- context [ (oterm ?o (map (fun _ : BTerm => lsubst_bterm_aux _ ?sub) ?lbt))]]
  => let Hf := fresh "xxx" in
      let ts := eval simpl in (lsubst_aux (oterm o lbt) sub)  in
        assert (ts = lsubst_aux (oterm o lbt) sub) as Hf by refl;
        rewrite Hf; clear Hf
  end.

Ltac prove_sub_range_sat := 
  let Hin := fresh "Hin" in 
  introv Hin; simpl in Hin;
   repeat(dorn Hin;auto); try(inverts Hin); subst;auto.

Ltac lsubst_aux_ot_eq Hyp := let T := type of Hyp in
  let Hf := fresh Hyp "lseq" in
  match T with 
    context [ lsubst_aux (oterm ?o ?lbt) ?sub] =>
      let ts := eval simpl in (lsubst_aux (oterm o lbt) sub)  in
        assert (ts = lsubst_aux (oterm o lbt) sub) as Hf by refl 
  end.

Lemma lsubst_app_swap {p} : forall t sub1 sub2,
  prog_sub sub1
  -> @prog_sub p sub2
  -> disjoint (dom_sub sub1) (dom_sub sub2)
  -> lsubst t (sub1++sub2) = lsubst t (sub2++sub1).
Proof.
  introv H1p H2p Hdis.
  pose proof (sub_app_sat _ _ _ H1p H2p).
  pose proof (sub_app_sat _ _ _ H2p H1p).
  change_to_lsubst_aux4;[].
  pose proof (lsubst_aux_shift t sub1 sub2 []).
  simpl_vlist.
  eauto.
Qed.


Lemma lsubst_lsubst_aux_prog_sub {p} : forall t sub,
  @prog_sub p sub
  -> lsubst t sub = lsubst_aux t sub.
Proof.
  introv Hpr. change_to_lsubst_aux4. sp.
Qed.

Ltac fold_lsubst_subh Hyp := let T := type of Hyp in
match T with
  | [(?v1 ,lsubst ?t1 ?sub)] => fold (lsubst_sub [v1,t1] sub)
end.

Ltac fold_lsubst_sub :=
match goal with
| [ |- context [ [(?v1 ,lsubst ?t1 ?sub), (?v2 ,lsubst ?t2 ?sub)] ] ] => fold (lsubst_sub [(v1,t1),(v2,t2)] sub)
| [ |- context [ [(?v1 ,lsubst ?t1 ?sub)] ] ] => fold (lsubst_sub [(v1,t1)] sub)
end.

Lemma lsubst_bterm_aux_trim {p} : forall lvf o lbt,
  disjoint  (free_vars (@oterm p o lbt)) lvf
  -> forall sub bt,
       LIn bt lbt
       -> lsubst_bterm_aux bt sub = lsubst_bterm_aux bt (sub_filter sub lvf).
Proof.
  introv Hdis Hin.
  destruct bt as [lv nt].
  simpl. f_equal.
  rw @sub_filter_swap.
  rw <- @sub_filter_app_r.
  rw @sub_filter_app_as_remove_nvars.
  rw @sub_filter_app_r.
  rewrite <- lsubst_aux_sub_filter with (l:= (remove_nvars lv lvf));sp.
  simpl in Hdis. eapply disjoint_flat_map_l in Hdis;eauto.
  allsimpl. apply disjoint_remove_nvars_l in Hdis;sp.
Qed.

Lemma lsubst_bterm_aux_trivial {p} : forall bt,
  @lsubst_bterm_aux p bt [] = bt.
Proof.
  introv. destruct bt.
  simpl. f_equal. 
  apply lsubst_aux_nil.
Qed.

Lemma closed_sub {p} :
  forall sub,
    (forall v t, LIn (v, t) sub -> @isprogram p t)
    -> flat_map free_vars (range sub) = [].
Proof.
  induction sub; allsimpl; sp.
  generalize (X a0 a); sp.
  rw IHsub; allsimpl; sp.
  allunfold @isprogram; allunfold @closed; sp; allrw; sp.
  generalize (X v t); sp.
Qed.

Lemma disjoint_sub_if_program {p} :
  forall sub,
    (forall (v : NVar) (t : @NTerm p),
       LIn (v, t) sub -> isprogram t)
    -> forall t, disjoint (@bound_vars p t) (flat_map free_vars (range sub)).
Proof.
  intros.
  generalize (closed_sub sub); sp.
  rw H; sp.
Qed.

Lemma lsubst_lsubst_aux_prog {p} :
  forall t sub,
    (forall v t, LIn (v, t) sub -> @isprogram p t)
    -> lsubst t sub = lsubst_aux t sub.
Proof.
  intros.
  apply lsubst_lsubst_aux.
  apply disjoint_sub_if_program; sp.
Qed.

Lemma cover_vars_cvterm2 {p} :
  forall v1 v2 t u1 u2,
    cover_vars (@get_cvterm p [v1,v2] t) [(v1, u1), (v2, u2)].
Proof.
  destruct t; sp; simpl.
  rw (@isprog_vars_eq p) in i; sp.
Qed.

Lemma cover_vars_cvterm3 {p} :
  forall v1 v2 v3 t u1 u2 u3,
    cover_vars (@get_cvterm p [v1,v2,v3] t) [(v1, u1), (v2, u2), (v3, u3)].
Proof.
  destruct t; sp; simpl.
  rw @isprog_vars_eq in i; sp.
Qed.

Definition lsubstc2 {p}
                    (v1 : NVar) (u1 : @CTerm p)
                    (v2 : NVar) (u2 : CTerm)
                    (t : CVTerm [v1;v2]) :=
  lsubstc (get_cvterm [v1;v2] t)
          (wf_cvterm [v1;v2] t)
          [(v1,u1),(v2,u2)]
          (cover_vars_cvterm2 v1 v2 t u1 u2).

Definition lsubstc3 {p}
                    (v1 : NVar) (u1 : @CTerm p)
                    (v2 : NVar) (u2 : CTerm)
                    (v3 : NVar) (u3 : CTerm)
                    (t : CVTerm [v1;v2;v3]) :=
  lsubstc (get_cvterm [v1;v2;v3] t)
          (wf_cvterm [v1;v2;v3] t)
          [(v1,u1),(v2,u2),(v3,u3)]
          (cover_vars_cvterm3 v1 v2 v3 t u1 u2 u3).

Lemma substc_cnewvar {p} :
  forall a t,
    substc a (@cnewvar p t) (mk_cv [cnewvar t] t) = t.
Proof.
  introv; destruct_cterms.
  apply cterm_eq; simpl.
  unfold cnewvar; simpl.
  apply lsubst_trivial; simpl; sp; cpx.
  rw @isprogram_eq; sp.
  allapply @newvar_prop; sp.
Qed.

Lemma cover_vars_weak {p} :
  forall u s1 s2 v t,
    @cover_vars p u (s1 ++ s2)
    -> cover_vars u (snoc s1 (v, t) ++ s2).
Proof.
  introv cv.
  allrw @cover_vars_eq.
  allrw @dom_csub_app.
  allrw @dom_csub_snoc; allsimpl.
  allrw subvars_prop; introv nih.
  generalize (cv x); intro nia.
  dest_imp nia hyp.
  allrw in_app_iff; allrw in_snoc; sp.
Qed.

Lemma cover_vars_add {p} :
  forall u s1 s2 v t,
    !LIn v (@free_vars p u)
    -> cover_vars u (snoc s1 (v, t) ++ s2)
    -> cover_vars u (s1 ++ s2).
Proof.
  introv nivh cv.
  allrw @cover_vars_eq.
  allrw @dom_csub_app.
  allrw @dom_csub_snoc; allsimpl.
  allrw subvars_prop; introv nih.
  generalize (cv x); intro nia.
  dest_imp nia hyp.
  allrw in_app_iff; allrw in_snoc; sp; subst; sp.
Qed.

Lemma csubst_swap_app {p} :
  forall t sub1 sub2,
    disjoint (dom_csub sub1) (@dom_csub p sub2)
    -> csubst t (sub1 ++ sub2) = csubst t (sub2 ++ sub1).
Proof.
  introv disj.
  generalize (csubst_shift t sub1 sub2 []); allrw app_nil_r; sp.
Qed.

Lemma fold_subst {p} :
  forall t v u, @lsubst p t [(v,u)] = subst t v u.
Proof. auto. Qed.

Lemma simple_lsubst_cons {p} :
  forall t v u sub,
    isprogram u
    -> (forall v u, LIn (v, u) sub -> @isprogram p u)
    -> lsubst (subst t v u) sub = lsubst t ((v, u) :: sub).
Proof.
  intros.
  unfold subst.
  rw @simple_lsubst_app; simpl; sp; cpx.
Qed.

Definition map_sub_range {p} (f : NTerm -> @NTerm p) (sub : @Substitution p) :=
  map (fun p => (fst p, f (snd p))) sub.

Lemma dom_sub_map_range {p} : forall f sub,
   dom_sub (@map_sub_range p f sub) = dom_sub sub.
Proof.
  induction sub; auto.
  simpl. f_equal. auto.
Qed.


Lemma sub_range_sat_cons {p} : forall h t P,
  @sub_range_sat p (h::t) P  <=> (P (snd h) # sub_range_sat t P).
Proof.
  intros. rw cons_as_app. rw <- @sub_app_sat_iff.
  split; introv HH; repnd; dands; allunfold @sub_range_sat; allsimpl; eauto;[].
  introv Hin; in_reasoning. cpx. cpx.
Qed.

Ltac simpl_sub5 :=
(match goal with
| [ H : (prog_sub _) |- _ ] => (allrewrite (prog_sub_flatmap_range _ H))
| [ H : isprogram _ |- _ ] => allrewrite (fst (H))
| [ H : (forall _ _, LIn (_, _) _  -> isprogram _) |- _ ] => (allrewrite (prog_sub_flatmap_range _ H))
| [ H : context[dom_sub (combine _ _)] |- _] => rewrite dom_sub_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[dom_sub (combine _ _)] ] => rewrite dom_sub_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (combine _ _)] |- _] => rewrite dom_range_combine in H;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ |-  context[range (combine _ _)] ] => rewrite dom_range_combine;[|try(simpl_list);spc;idtac "check lengths in combine";fail]
| [ H : context[range (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[range (var_ren _ _)] ] => unfold var_ren
| [ H : context[dom_sub (var_ren _ _)] |- _] => unfold var_ren in H
| [ |-  context[dom_sub (var_ren _ _)] ] => unfold var_ren
| [ H : context[flat_map free_vars (map vterm _)] |- _] => rewrite flat_map_free_var_vterm in H
| [ |-  context[flat_map free_vars (map vterm _)] ] => rewrite flat_map_free_var_vterm
| [ H : context[flat_map bound_vars (map vterm _)] |- _] => rewrite flat_map_bound_var_vterm in H
| [ |-  context[flat_map bound_vars (map vterm _)] ] => rewrite flat_map_bound_var_vterm
end).

Lemma lsubst_nest_progs_swap {p} :
  forall (t : NTerm) (sub1 sub2 : @Substitution p),
  prog_sub sub1 ->
  prog_sub sub2 ->
  disjoint (dom_sub sub1) (dom_sub sub2) ->
  (lsubst (lsubst t sub1) sub2) = (lsubst (lsubst t sub2) sub1).
Proof.
  introv H1p H2p Hdis.
  change_to_lsubst_aux4.
  apply lsubst_aux_nest_swap2; spcls; repeat(simpl_sub5); auto;
  rewrite (prog_sub_flatmap_range _ H1p); spcls; auto.
Qed.

Lemma lsubst_nest_progs_swap_single {p} :
  forall (t st: @NTerm p) (sub : Substitution) (v: NVar),
  prog_sub sub ->
  isprogram st ->
  disjoint (dom_sub sub) [v] ->
  (lsubst (lsubst t sub) [(v,st)]) = (lsubst (lsubst t [(v,st)]) sub).
Proof.
  intros. apply lsubst_nest_progs_swap; auto.
  prove_sub_range_sat.
Qed.

Ltac fold_applybt := let XX := fresh "XX" in 
match goal with
[ |- context [lsubst ?e [(?v1, ?t1)]]] => 
  assert (apply_bterm (bterm [v1] e) [t1] = lsubst e [(v1, t1)]) as XX by auto;
    rewrite <- XX; clear XX
end.

Lemma simple_lsubst_cons2 {p} :
  forall t v u sub,
    @prog_sub p ((v, u) :: sub)
    -> lsubst (subst t v u) sub = lsubst t ((v, u) :: sub).
Proof.
  introv Hps.
  rw cons_as_app in Hps.
  apply sub_app_sat_if in Hps.
  repnd. unfold subst.
  rw @simple_lsubst_app; simpl; auto.
Qed.

Lemma simple_lsubst_cons3 {p} :
  forall t v u sub,
    @prog_sub p ((v, u) :: sub)
    -> (!LIn v (dom_sub sub))
    -> subst  (lsubst t sub) v u = lsubst t ((v, u) :: sub).
Proof.
  introv Hps Hd.
  rw cons_as_app in Hps.
  apply sub_app_sat_if in Hps.
  repnd.
  rw @lsubst_swap; auto;
    [ |repnud Hps0; eapply Hps0; left; eauto].
  rw snoc_as_append.
  rw <- @simple_lsubst_app; simpl; auto.
Qed.

Lemma cover_vars_disjoint {p} :
  forall u sub vs,
    @cover_vars p u sub
    -> disjoint (dom_csub sub) vs
    -> disjoint (free_vars u) vs.
Proof.
  introv cv disj.
  rw @cover_vars_eq in cv.
  unfold disjoint in disj.
  unfold disjoint.
  introv i.
  rw subvars_prop in cv.
  apply cv in i.
  apply disj in i; sp.
Qed.

Lemma csub_filter_trivial {p} :
  forall s vs,
    disjoint vs (@dom_csub p s)
    -> csub_filter s vs = s.
Proof.
  induction s; introv disj; sp; allsimpl.
  allrw disjoint_cons_r; repnd.
  discover; allrw.
  boolvar; sp.
Qed.

Lemma eqvars_sub_keep_first {p} :
  forall sub la lb,
    eqvars la lb
    -> (@sub_keep_first p sub la) = (sub_keep_first sub lb).
Proof.
  induction sub as [| (v,t) sub Hind]; introv Heq;auto.
  simpl. duplicate Heq. rw eqvars_prop in Heq.
  rw memvar_dmemvar.
  rw memvar_dmemvar.
  dtiffs2.
  cases_if; cases_if; try (provefalse; eauto;fail); erewrite Hind; eauto 2 with eqvars.
Qed.

Lemma simple_lsubst_snoc {p} :
  forall t v u sub,
    @isprogram p u
    -> (forall v u, LIn (v, u) sub -> isprogram u)
    -> subst (lsubst t sub) v u = lsubst t (snoc sub (v,u)).
Proof.
  intros.
  unfold subst.
  rw @simple_lsubst_app; simpl; sp; cpx.
  rw snoc_as_append; sp.
Qed.

Lemma simple_csubst_subst {p} :
  forall t x B s,
    disjoint (@free_vars p t) (bound_vars B)
    -> cover_vars t s
    -> wf_term t
    -> csubst (subst B x t) s
       = subst (csubst B (csub_filter s [x])) x (csubst t s).
Proof.
  introv disj cov wt.

  unfold csubst, subst; simpl.

  repeat (rw @simple_lsubst_lsubst; simpl);
    try (complete (intros; allapply @in_csub2sub; sp;
                   allunfold @isprogram; repnd; allrw; sp));
    try (complete (intros; sp; cpx; sp; apply @isprogram_csubst; sp; rw @nt_wf_eq; sp)).

  rw @lsubst_sub_trivial_closed1; simpl;
    try (complete (intros; allapply @in_csub2sub; sp;
                   allunfold @isprogram; repnd; allrw; sp));
    try (complete (intros; sp; cpx; sp; apply @isprogram_csubst; sp; rw @nt_wf_eq; sp)).

  rw <- snoc_as_append.
  rw <- @lsubst_swap; simpl;
    try (complete (intros; allapply @in_csub2sub; sp;
                   allunfold @isprogram; repnd; allrw; sp));
    try (complete (intros; sp; cpx; sp; apply @isprogram_csubst; sp; rw @nt_wf_eq; sp));
    try (complete (intro; allrw @dom_csub_eq; allrw @dom_csub_csub_filter;
                   allrw in_remove_nvars; allsimpl; sp)).

  rw @fold_csubst.

  repeat (rw <- @simple_lsubst_cons; simpl);
    try (complete (intros; allapply @in_csub2sub; sp;
                   allunfold @isprogram; repnd; allrw; sp));
    try (complete (intros; sp; cpx; sp; apply @isprogram_csubst; sp; rw @nt_wf_eq; sp)).

  rw <- @sub_filter_csub2sub.
  rw @lsubst_sub_filter; sp;
    try (complete (intros; allapply @in_csub2sub; sp;
                   allunfold @isprogram; repnd; allrw; sp));
    try (complete (intros; sp; cpx; sp; apply @isprogram_csubst; sp; rw @nt_wf_eq; sp)).

  rw disjoint_singleton_r; intro i.

  unfold subst in i; rw @isprogram_lsubst2 in i; allsimpl.
  rw in_remove_nvars in i; allsimpl; sp.
  intros; sp; cpx; apply isprogram_csubst; sp; rw @nt_wf_eq; sp.
Qed.

Lemma cover_vars_iff_closed_lsubstc {p} :
  forall t s,
    @cover_vars p t s <=> closed (csubst t s).
Proof.
  introv.
  unfold closed.
  rw @cover_vars_eq.
  unfold csubst.
  rw @isprogram_lsubst2; sp; allapply @in_csub2sub; sp.
  rw <- null_iff_nil.
  rw null_remove_nvars_subvars.
  rw @dom_csub_eq; sp.
Qed.

Lemma lsubst_aux_app_sub_filter {p} :
  forall s1 s2 t,
    prog_sub s1
    -> @prog_sub p s2
    -> lsubst t (s1 ++ s2)
       = lsubst t (s1 ++ sub_filter s2 (dom_sub s1)).
Proof.
  induction s1; simpl; introv ps1 ps2.
  rw @sub_filter_nil_r; sp.
  destruct a as [v u]; allsimpl.
  allrw @prog_sub_cons; repnd.
  repeat (rw <- @simple_lsubst_cons);
    try (complete sp);
    try (complete (introv i; allrw in_app_iff; sp; allrw <- @prog_sub_eq;
                   allrw @in_sub_filter; repnd; allsimpl; allrw not_over_or; repnd;
                   try (complete (apply ps1; rw @in_range_iff; exists v0; sp));
                   try (complete (apply ps2; rw @in_range_iff; exists v0; sp)))).

  rw IHs1; sp.

  generalize (lsubst_sub_filter (subst t v u) (s1 ++ sub_filter s2 (dom_sub s1)) [v]);
    intro eq1.
  dest_imp eq1 hyp.
  introv i; allrw in_app_iff; sp; allrw <- @prog_sub_eq;
  allrw @in_sub_filter; repnd; allsimpl; allrw not_over_or; repnd;
  try (complete (apply ps1; rw @in_range_iff; exists v0; sp));
  try (complete (apply ps2; rw @in_range_iff; exists v0; sp)).
  dest_imp eq1 hyp.
  unfold subst; rw @isprogram_lsubst2; simpl.
  rw disjoint_remove_nvars_l; rw remove_nvars_eq; sp.
  introv k; sp; cpx.

  generalize (lsubst_sub_filter (subst t v u) (s1 ++ sub_filter s2 (v :: dom_sub s1)) [v]);
    intro eq2.
  dest_imp eq2 hyp.
  introv i; allrw in_app_iff; sp; allrw <- @prog_sub_eq;
  allrw @in_sub_filter; repnd; allsimpl; allrw not_over_or; repnd;
  try (complete (apply ps1; rw @in_range_iff; exists v0; sp));
  try (complete (apply ps2; rw @in_range_iff; exists v0; sp)).
  dest_imp eq2 hyp.
  unfold subst; rw @isprogram_lsubst2; simpl.
  rw disjoint_remove_nvars_l; rw remove_nvars_eq; sp.
  introv k; sp; cpx.

  rw <- eq1; rw <- eq2.

  allrw @sub_filter_app; simpl.
  allrw <- @sub_filter_app_r.

  assert (sub_filter s2 (dom_sub s1 ++ [v]) = sub_filter s2 ((v :: dom_sub s1) ++ [v]))
         as eq; try (complete (rw eq; sp)).

  symmetry.
  rewrite sub_filter_app_as_remove_nvars; simpl.
  rw remove_nvars_cons_r; boolvar; try (complete (allrw not_over_or; sp)).
  rw remove_nvars_nil_r; rw app_nil_r.
  rw cons_as_app.
  allrw @sub_filter_app_r.
  rewrite sub_filter_swap; sp.
Qed.

Lemma prog_sub_sub_filter {p} :
  forall s vs, @prog_sub p s -> prog_sub (sub_filter s vs).
Proof.
  introv ps.
  allunfold @prog_sub.
  allunfold @sub_range_sat.
  introv i.
  apply in_sub_filter in i; repnd; discover; sp.
Qed.

Lemma prog_sub_snoc {p} :
  forall s v t,
    @prog_sub p (snoc s (v,t)) <=> (prog_sub s # isprogram t).
Proof.
  introv.
  unfold prog_sub, sub_range_sat; split; intro k.

  dands.
  introv i.
  generalize (k v0 t0); intro j; allrw in_snoc; sp.
  generalize (k v t); intro j; allrw in_snoc; sp.

  repnd.
  introv i; allrw in_snoc; sp; cpx; discover; sp.
Qed.

Lemma covered_apply {p} :
  forall a b vs,
    @covered p (mk_apply a b) vs
    <=> covered a vs
        # covered b vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_apply2 {p} :
  forall a b c vs,
    @covered p (mk_apply2 a b c) vs
    <=> covered a vs
        # covered b vs
        # covered c vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  repeat (rewrite app_nil_r).
  repeat (rw subvars_app_l); sp; split; sp.
Qed.

Lemma cover_vars_change_sub2 {p} :
  forall t sub1 sub2,
    subvars (@dom_csub p sub1) (dom_csub sub2)
    -> cover_vars t sub1
    -> cover_vars t sub2.
Proof.
  introv eq cv.
  allrw @cover_vars_eq.
  apply subvars_trans with (vs2 := dom_csub sub1); sp.
Qed.

Lemma cover_vars_upto_w {p} :
  forall A v B sub vs,
    @cover_vars_upto p (mk_w A v B) sub vs
    <=> cover_vars_upto A sub vs
        # cover_vars_upto B (csub_filter sub [v]) (v :: vs).
Proof.
  introv; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.

  split; sp; allrw subvars_prop; sp; discover; sp;
  allsimpl; allrw in_app_iff; allrw in_remove_nvars;
  allrw in_single_iff; sp.
  destruct (eq_var_dec v x); sp.
  right; right; sp.
Qed.

Lemma csubst_as_lsubst_aux {p} :
  forall t sub, @csubst p t sub = lsubst_aux t (csub2sub sub).
Proof.
  sp.
  unfold csubst, lsubst.
  change_to_lsubst_aux4; sp.
Qed.

Lemma lsubst_aux_lam_csub2sub {p} :
  forall v b s,
    lsubst_aux (mk_lam v b) (@csub2sub p s)
    = mk_lam v (lsubst_aux b (csub2sub (csub_filter s [v]))).
Proof.
  sp; simpl.
  rw @fold_lam.
  rw @sub_filter_csub2sub; sp.
Qed.

Lemma csub_filter_nil {p} :
  forall s, @csub_filter p s [] = s.
Proof.
  induction s; simpl; sp.
  rw IHs; sp.
Qed.

Lemma lsubst_aux_isect_csub2sub {p} :
  forall a v b s,
    lsubst_aux (mk_isect a v b) (@csub2sub p s)
    = mk_isect (lsubst_aux a (csub2sub s)) v (lsubst_aux b (csub2sub (csub_filter s [v]))).
Proof.
  sp; simpl.
  rw @fold_nobnd.
  rw @fold_isect.
  allrw @sub_filter_csub2sub.
  allrw @csub_filter_nil; sp.
Qed.

Lemma lsubst_aux_free_from_atom_csub2sub {p} :
  forall a b c s,
    lsubst_aux (mk_free_from_atom a b c) (@csub2sub p s)
    = mk_free_from_atom
        (lsubst_aux a (csub2sub s))
        (lsubst_aux b (csub2sub s))
        (lsubst_aux c (csub2sub s)).
Proof.
  sp; simpl.
  allrw @fold_nobnd.
  rw @fold_free_from_atom.
  allrw @sub_filter_csub2sub.
  allrw @csub_filter_nil; sp.
Qed.

Lemma lsubst_aux_free_from_atoms_csub2sub {p} :
  forall a b s,
    lsubst_aux (mk_free_from_atoms a b) (@csub2sub p s)
    = mk_free_from_atoms
        (lsubst_aux a (csub2sub s))
        (lsubst_aux b (csub2sub s)).
Proof.
  sp; simpl.
  allrw @fold_nobnd.
  rw @fold_free_from_atoms.
  allrw @sub_filter_csub2sub.
  allrw @csub_filter_nil; sp.
Qed.

Lemma lsubst_aux_equality_csub2sub {p} :
  forall a b T s,
    lsubst_aux (mk_equality a b T) (@csub2sub p s)
    = mk_equality
        (lsubst_aux a (csub2sub s))
        (lsubst_aux b (csub2sub s))
        (lsubst_aux T (csub2sub s)).
Proof.
  sp; simpl.
  allrw @fold_nobnd.
  rw @fold_equality.
  allrw @sub_filter_csub2sub.
  allrw @csub_filter_nil; sp.
Qed.

Lemma lsubst_aux_tequality_csub2sub {p} :
  forall a b s,
    lsubst_aux (mk_tequality a b) (@csub2sub p s)
    = mk_tequality
        (lsubst_aux a (csub2sub s))
        (lsubst_aux b (csub2sub s)).
Proof.
  sp; simpl.
  allrw @fold_nobnd.
  rw @fold_tequality.
  allrw @sub_filter_csub2sub.
  allrw @csub_filter_nil; sp.
Qed.

Lemma lsubst_aux_apply_csub2sub {p} :
  forall a b s,
    lsubst_aux (mk_apply a b) (@csub2sub p s)
    = mk_apply
        (lsubst_aux a (csub2sub s))
        (lsubst_aux b (csub2sub s)).
Proof.
  sp; simpl.
  allrw @fold_nobnd.
  rw @fold_apply.
  allrw @sub_filter_csub2sub.
  allrw @csub_filter_nil; sp.
Qed.

Lemma lsubst_aux_base_csub2sub {p} :
  forall s,
    lsubst_aux mk_base (csub2sub s) = @mk_base p.
Proof.
  sp.
Qed.

Lemma lsubst_aux_var_csub2sub_out {p} :
  forall v s,
    !LIn v (dom_csub s)
    -> lsubst_aux (mk_var v) (csub2sub s) = @mk_var p v.
Proof.
  introv ni; simpl.
  rw <- @dom_csub_eq in ni.
  apply sub_find_none_iff in ni.
  rw ni; sp.
Qed.

Lemma cover_vars_fun {p} :
  forall a b sub,
    cover_vars (@mk_fun p a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  introv.
  rw @cover_vars_function.
  generalize (cover_vars_upto_csub_filter_disjoint b sub [newvar b] [newvar b]).
  intro e.
  repeat (dest_imp e hyp).
  rw disjoint_singleton_r.
  apply newvar_prop.
  rw e; sp.
Qed.

Lemma cover_vars_ufun {p} :
  forall a b sub,
    cover_vars (@mk_ufun p a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  introv.
  rw @cover_vars_isect.
  generalize (cover_vars_upto_csub_filter_disjoint b sub [newvar b] [newvar b]).
  intro e.
  repeat (dest_imp e hyp).
  rw disjoint_singleton_r.
  apply newvar_prop.
  rw e; sp.
Qed.

Lemma cover_vars_eufun {p} :
  forall a b sub,
    cover_vars (@mk_eufun p a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  introv.
  rw @cover_vars_eisect.
  generalize (cover_vars_upto_csub_filter_disjoint b sub [newvar b] [newvar b]).
  intro e.
  repeat (dest_imp e hyp).
  rw disjoint_singleton_r.
  apply newvar_prop.
  rw e; sp.
Qed.

Lemma cover_vars_prod {p} :
  forall a b sub,
    cover_vars (@mk_prod p a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  introv.
  rw @cover_vars_product.
  generalize (cover_vars_upto_csub_filter_disjoint b sub [newvar b] [newvar b]).
  intro e.
  repeat (dest_imp e hyp).
  rw disjoint_singleton_r.
  apply newvar_prop.
  rw e; sp.
Qed.

Lemma cover_vars_void {p} :
  forall sub, @cover_vars p mk_void sub.
Proof.
  introv.
  rw @cover_vars_eq; simpl; sp.
Qed.
Hint Immediate cover_vars_void.

Lemma cover_vars_not {p} :
  forall a sub, cover_vars (@mk_not p a) sub <=> cover_vars a sub.
Proof.
  introv.
  rw @cover_vars_fun; split; sp.
Qed.

Lemma covered_function {p} :
  forall a v b vs,
    covered (@mk_function p a v b) vs
    <=> covered a vs # covered b (v :: vs).
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_product {p} :
  forall a v b vs,
    covered (@mk_product p a v b) vs
    <=> covered a vs # covered b (v :: vs).
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_fun {p} :
  forall a b vs,
    covered (@mk_fun p a b) vs
    <=> covered a vs # covered b vs.
Proof.
  introv; rw @covered_function; split; intro k; repnd; dands; auto.

  allunfold @covered.
  apply subvars_cons_r_weak_if_not_in in k; auto.
  apply newvar_prop.

  allunfold @covered.
  apply subvars_cons_r; auto.
Qed.

Lemma covered_ufun {p} :
  forall a b vs,
    covered (@mk_ufun p a b) vs
    <=> covered a vs # covered b vs.
Proof.
  introv; rw @covered_isect; split; intro k; repnd; dands; auto.

  allunfold @covered.
  apply subvars_cons_r_weak_if_not_in in k; auto.
  apply newvar_prop.

  allunfold @covered.
  apply subvars_cons_r; auto.
Qed.

Lemma covered_eufun {p} :
  forall a b vs,
    covered (@mk_eufun p a b) vs
    <=> covered a vs # covered b vs.
Proof.
  introv; rw @covered_eisect; split; intro k; repnd; dands; auto.

  allunfold @covered.
  apply subvars_cons_r_weak_if_not_in in k; auto.
  apply newvar_prop.

  allunfold @covered.
  apply subvars_cons_r; auto.
Qed.

Lemma covered_prod {p} :
  forall a b vs,
    covered (@mk_prod p a b) vs
    <=> covered a vs # covered b vs.
Proof.
  introv; rw @covered_product; split; intro k; repnd; dands; auto.

  allunfold @covered.
  apply subvars_cons_r_weak_if_not_in in k; auto.
  apply newvar_prop.

  allunfold @covered.
  apply subvars_cons_r; auto.
Qed.

Lemma covered_iff {p} :
  forall a b vs,
    covered (@mk_iff p a b) vs
    <=> covered a vs # covered b vs.
Proof.
  introv.
  rw @covered_prod.
  allrw @covered_fun; split; sp.
Qed.

Lemma isprog_vars_lsubst {p} :
  forall t : NTerm,
  forall vs : list NVar,
  forall sub : @Substitution p,
    nt_wf t
    -> (forall v u, LIn (v, u) sub -> isprogram u)
    -> (forall v, LIn v (free_vars t) -> LIn v (vs ++ dom_sub sub))
    -> isprog_vars vs (lsubst t sub).
Proof.
  introv w k1 k2.
  rw @isprog_vars_eq.
  apply @isprogram_lsubst1 with (sub := sub) in w; sp.
  allrw.
  rw subvars_remove_nvars.
  rw subvars_prop; auto.
Qed.

Lemma isprog_vars_csubst {p} :
  forall t : NTerm,
  forall vs : list NVar,
  forall sub : @CSub p,
    nt_wf t
    -> (forall v, LIn v (free_vars t) -> LIn v (vs ++ dom_csub sub))
    -> isprog_vars vs (csubst t sub).
Proof.
  introv w k.
  unfold csubst.
  apply isprog_vars_lsubst; sp;
  allapply @in_csub2sub; sp.
  rw @dom_csub_eq; sp.
Qed.

Lemma cover_vars_pertype {p} :
  forall a sub,
    cover_vars (@mk_pertype p a) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_ipertype {p} :
  forall a sub,
    cover_vars (@mk_ipertype p a) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_spertype {p} :
  forall a sub,
    cover_vars (@mk_spertype p a) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_tuni {p} :
  forall a sub,
    cover_vars (@mk_tuni p a) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma sub_find_some_app2 {p} :
  forall v t sub1 sub2,
    !LIn v (dom_sub sub1)
    -> @sub_find p sub2 v = Some t
    -> sub_find (sub1 ++ sub2) v = Some t.
Proof.
  introv niv sf.
  rw @sub_find_app.
  rw <- @sub_find_none_iff in niv.
  rw niv; sp.
Qed.

Lemma subset_free_vars_sub_aux_app2 {p} :
  forall t sub1 sub2,
    (forall v t, LIn (v, t) (sub1 ++ sub2) -> @isprogram p t)
    -> disjoint (free_vars t) (dom_sub sub1)
    -> lsubst_aux t (sub1 ++ sub2) = lsubst_aux t sub2.
Proof.
  nterm_ind t Case; simpl; introv k d; auto.

  - Case "vterm".
    allrw disjoint_singleton_l; sp.
    remember (sub_find sub2 n); destruct o; symmetry in Heqo.
    apply @sub_find_some_app2 with (sub1 := sub1) in Heqo; auto.
    rw Heqo; auto.
    rw @sub_find_none_iff in Heqo.
    assert (!LIn n (dom_sub (sub1 ++ sub2))) as nin
      by (rw @dom_sub_app; rw in_app_iff; intro; sp).
    rw <- @sub_find_none_iff in nin.
    rw nin; auto.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.
    repeat (rw bvar_renamings_subst_isprogram; auto); simpl;
    try (sp; apply X with (v := v); rw in_app_iff; sp).
    rw @sub_filter_app.

    rewrite H with (lv := l); sp.
    apply k with (v := v).
    allrw in_app_iff.
    allrw @in_sub_filter; sp.
    allrw disjoint_flat_map_l.
    apply_in_hyp pp.
    allsimpl.
    rw disjoint_remove_nvars_l in pp.
    rw <- @dom_sub_sub_filter; auto.
Qed.

Lemma subset_free_vars_sub_app2 {p} :
  forall t sub1 sub2,
    (forall v t, LIn (v, t) (sub1 ++ sub2) -> @isprogram p t)
    -> disjoint (free_vars t) (dom_sub sub1)
    -> lsubst t (sub1 ++ sub2) = lsubst t sub2.
Proof.
  introv Hpr.
  applydup (sub_app_sat_if (@isprogram p)) in Hpr.
  repnd.
  change_to_lsubst_aux4.
  apply subset_free_vars_sub_aux_app2; sp.
Qed.

Lemma subset_free_vars_csub_app2 {p} :
  forall t sub1 sub2,
    disjoint (free_vars t) (@dom_csub p sub1)
    -> csubst t (sub1 ++ sub2) = csubst t sub2.
Proof.
  unfold csubst; sp.
  rw <- @csub2sub_app.
  apply subset_free_vars_sub_app2; sp.
  allrw in_app_iff; sp; allapply @in_csub2sub; sp.
  rw @dom_csub_eq; auto.
Qed.

Lemma subset_free_vars_csub_cons {p} :
  forall t sub v u,
    !LIn v (@free_vars p t)
    -> csubst t ((v,u) :: sub) = csubst t sub.
Proof.
  intros.
  rw cons_as_app.
  rw @subset_free_vars_csub_app2; simpl; auto.
  unfold disjoint; simpl; sp; subst; sp.
Qed.

Lemma cover_vars_app_disjoint2 {p} :
  forall t sub1 sub2,
    @cover_vars p t (sub1 ++ sub2)
    -> disjoint (free_vars t) (dom_csub sub1)
    -> cover_vars t sub2.
Proof.
  introv cv disj.
  allrw @cover_vars_eq.
  rw @dom_csub_app in cv.
  provesv.
  allrw in_app_iff; sp.
  unfold disjoint in disj.
  discover; sp.
Qed.

Lemma cover_vars_cons_disjoint {p} :
  forall t sub v u,
    @cover_vars p t ((v,u) :: sub)
    -> !LIn v (free_vars t)
    -> cover_vars t sub.
Proof.
  introv cv ni.
  rw cons_as_app in cv.
  apply cover_vars_app_disjoint2 in cv; sp.
  simpl; unfold disjoint; simpl; sp; subst; sp.
Qed.

Lemma cover_vars_upto_csub_filter_app {p} :
  forall t s vs1 vs2 vs,
    eqvars vs1 vs2
    -> disjoint (free_vars t) vs1
    -> (cover_vars_upto t (@csub_filter p s vs1) (vs2 ++ vs)
        <=> cover_vars_upto t s vs).
Proof.
  introv eqv disj.
  unfold cover_vars_upto.
  allrw subvars_prop; split; intro k; introv i; allrw in_app_iff;
  allrw @dom_csub_csub_filter; allrw in_remove_nvars.

  applydup disj in i.
  apply k in i.
  allrw in_app_iff; allrw in_remove_nvars; repdors; try (complete sp).
  rw eqvars_prop in eqv.
  apply eqv in i2; sp.

  applydup disj in i.
  apply k in i.
  allrw in_app_iff; repdors; try (complete sp).
Qed.

Lemma covered_cons_weak_iff {p} :
  forall t v (ni : !LIn v (@free_vars p t)) vs,
    covered t (v :: vs) <=> covered t vs.
Proof.
  introv.
  unfold covered; split; intro k; provesv; allsimpl; repdors; subst; sp.
Qed.

Lemma cover_vars_upto_pertype {p} :
  forall a sub vs,
    cover_vars_upto (@mk_pertype p a) sub vs
    <=> cover_vars_upto a sub vs.
Proof.
  sp; unfold cover_vars_upto; split; intro k;
  allrw subvars_prop; introv i; apply k;
  allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r; sp.
Qed.

Lemma covered_pertype {p} :
  forall a vs,
    covered (@mk_pertype p a) vs
    <=> covered a vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_upto_ipertype {p} :
  forall a sub vs,
    cover_vars_upto (@mk_ipertype p a) sub vs
    <=> cover_vars_upto a sub vs.
Proof.
  sp; unfold cover_vars_upto; split; intro k;
  allrw subvars_prop; introv i; apply k;
  allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r; sp.
Qed.

Lemma covered_ipertype {p} :
  forall a vs,
    covered (@mk_ipertype p a) vs
    <=> covered a vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_upto_spertype {p} :
  forall a sub vs,
    cover_vars_upto (@mk_spertype p a) sub vs
    <=> cover_vars_upto a sub vs.
Proof.
  sp; unfold cover_vars_upto; split; intro k;
  allrw subvars_prop; introv i; apply k;
  allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r; sp.
Qed.

Lemma covered_spertype {p} :
  forall a vs,
    covered (@mk_spertype p a) vs
    <=> covered a vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_upto_tuni {p} :
  forall a sub vs,
    cover_vars_upto (@mk_tuni p a) sub vs
    <=> cover_vars_upto a sub vs.
Proof.
  sp; unfold cover_vars_upto; split; intro k;
  allrw subvars_prop; introv i; apply k;
  allsimpl; allrw remove_nvars_nil_l; allrw app_nil_r; sp.
Qed.

Lemma covered_tuni {p} :
  forall a vs,
    covered (@mk_tuni p a) vs
    <=> covered a vs.
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma covered_base {p} :
  forall vs, @covered p mk_base vs.
Proof.
  unfold covered; sp; simpl.
Qed.
Hint Immediate covered_base.

Lemma covered_base_iff {p} :
  forall vs, @covered p mk_base vs <=> True.
Proof.
  sp.
Qed.

Lemma covered_iff_cover_vars {p} :
  forall vs t s, @dom_csub p s = vs -> (covered t vs <=> cover_vars t s).
Proof.
  introv e.
  rw @cover_vars_eq.
  unfold covered; subst; sp.
Qed.

Lemma cover_vars_spread {p} :
  forall a v1 v2 b sub,
    cover_vars (@mk_spread p a v1 v2 b) sub
    <=> cover_vars a sub
        # cover_vars_upto b (csub_filter sub [v1,v2]) [v1,v2].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  rw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v1 :: v2 :: remove_nvars [v1,v2] (dom_csub sub)
          = [v1,v2] ++ remove_nvars [v1,v2] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma cover_vars_pair {p} :
  forall a b sub,
    @cover_vars p (mk_pair a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_ispair {p} :
  forall a b T sub,
    @cover_vars p (mk_ispair a b T) sub
    <=> cover_vars a sub
        # cover_vars b sub
        # cover_vars T sub.
Proof.
  sp; repeat (rw @cover_vars_eq); simpl.
  repeat (rw remove_nvars_nil_l).
  rw app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.

Lemma cover_vars_upto_ispair {p} :
  forall vs a b T sub,
    @cover_vars_upto p (mk_ispair a b T) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs
        # cover_vars_upto T sub vs.
Proof.
  intros; unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma subst_ispair {p} :
  forall t a b x u,
    @isprogram p u
    -> subst (mk_ispair t a b) x u
       = mk_ispair (subst t x u) (subst a x u) (subst b x u).
Proof.
  introv ipu.
  destruct ipu as [cl wf].
  unfold subst.
  change_to_lsubst_aux4; simpl; allrw app_nil_r; allrw; sp.
Qed.

Lemma cover_vars_eta_pair {p} :
  forall t s, cover_vars (@mk_eta_pair p t) s <=> cover_vars t s.
Proof.
  introv.
  rw @cover_vars_pair.
  allrw @cover_vars_spread.
  allrw @cover_vars_upto_var.
  allrw in_app_iff; simpl; split; sp.
Qed.

Lemma cover_vars_upto_approx {p} :
  forall a b sub vs,
    cover_vars_upto (@mk_approx p a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  unfold cover_vars_upto; introv; simpl.
  rw app_nil_r.
  allrw remove_nvars_nil_l.
  rw subvars_app_l; sp.
Qed.

Lemma cover_vars_upto_fix {p} :
  forall a sub vs,
    cover_vars_upto (@mk_fix p a) sub vs
    <=> cover_vars_upto a sub vs.
Proof.
  unfold cover_vars_upto; introv; simpl.
  rw app_nil_r.
  rw remove_nvars_nil_l; sp.
Qed.

Lemma cover_vars_upto_id {p} :
  forall sub vs, @cover_vars_upto p mk_id sub vs.
Proof.
  unfold cover_vars_upto; introv; simpl; sp.
Qed.
Hint Immediate cover_vars_upto_id.

Lemma cover_vars_upto_bot {p} :
  forall sub vs, @cover_vars_upto p mk_bot sub vs.
Proof.
  unfold mk_bot, mk_bottom.
  introv.
  apply cover_vars_upto_fix; sp.
Qed.
Hint Immediate cover_vars_upto_bot.

Lemma cover_vars_upto_false {p} :
  forall sub vs, @cover_vars_upto p mk_false sub vs.
Proof.
  introv.
  unfold mk_false.
  rw @cover_vars_upto_approx; sp.
Qed.
Hint Immediate cover_vars_upto_false.

Lemma cover_vars_upto_top {p} :
  forall sub vs, @cover_vars_upto p mk_top sub vs.
Proof.
  introv.
  unfold mk_top.
  rw @cover_vars_upto_isect; sp.
Qed.
Hint Immediate cover_vars_upto_top.

Lemma cover_vars_top {p} :
  forall sub, @cover_vars p mk_top sub.
Proof.
  introv.
  generalize (cover_vars_upto_csub_filter_disjoint mk_top sub [] []);
    intro k; repeat (autodimp k hyp).
  rw <- k; sp.
Qed.
Hint Immediate cover_vars_top.

Lemma lsubst_mk_bot {pp} :
  forall sub, {v : NVar & lsubst mk_bot sub = @mk_vbot pp v}.
Proof.
  introv.
  unfold lsubst.
  destruct (dec_disjointv (bound_vars mk_bot) (flat_map free_vars (range sub))).

  - simpl in d.
    rw disjoint_singleton_l in d.
    exists nvarx.
    simpl.
    rw @sub_filter_nil_r.
    rw @sub_find_sub_filter; simpl; sp.

  - simpl in n; rw disjoint_singleton_l in n.
    generalize (ex_fresh_var (flat_map free_vars (range sub))); intro k; exrepnd.
    simpl; unfold all_vars; simpl.
    rw @sub_filter_nil_r.
    rw @sub_find_sub_filter; simpl; tcsp.
    remember (fresh_var (flat_map free_vars (range sub) ++ [nvarx])) as fv.
    exists fv; sp.
Qed.

Lemma sub_free_vars_is_flat_map_free_vars_range {o} :
  forall sub : @Sub o,
    sub_free_vars sub = flat_map free_vars (range sub).
Proof.
  induction sub; simpl; auto.
  destruct a; simpl; rw IHsub; auto.
Qed.

(*
Lemma lsubst_mk_exception {o} :
  forall (a e : @NTerm o) sub,
    lsubst (mk_exception a e) sub = mk_exception (lsubst a sub) (lsubst e sub).
Proof.
  introv.
  unfold lsubst, mk_exception; simpl.
  allrw app_nil_r.
  allrw @sub_filter_nil_r.
  unfold var_ren; simpl.
  allrw @lsubst_aux_nil.
  unfold nobnd.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  boolvar; allrw disjoint_app_l; tcsp; try (complete (provefalse; sp)).
Qed.

Lemma subst_mk_exception {p} :
  forall e v t,
    subst (@mk_exception p e) v t = mk_exception (subst e v t).
Proof.
  introv.
  unfold subst.
  apply lsubst_mk_exception.
Qed.
*)

Lemma isprogram_bt_implies_isprogram_lsubst {p} :
  forall vs t sub,
    @dom_sub p sub = vs
    -> (forall v t, LIn (v,t) sub -> isprogram t)
    -> isprogram_bt (bterm vs t)
    -> isprogram (lsubst t sub).
Proof.
  introv domeq ispsub ispbt; subst.
  apply isprogram_lsubst; auto.
  inversion ispbt as [cl wf].
  inversion wf; subst; auto.
  introv i.
  inversion ispbt as [cl wf].
  inversion cl as [e].
  rw <- null_iff_nil in e.
  rw null_remove_nvars in e.
  discover; auto.
Qed.

(* The line below should be at the end of the file. Do NOT
  write anything below that is not supposed to be included in the Tech Report*)
(* end hide*)
