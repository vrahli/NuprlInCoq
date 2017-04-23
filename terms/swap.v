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


Require Import AssociationList.
Require Import alphaeq.


(* begin hide *)


(* end hide *)

(**

  This file presents another definition of alpha-equality that does
  not use substitution but uses swapping instead.

 *)

(**

  Let us now define swapping.  The [oneswapvar] function defines what
  it means to apply the swapping [(a,b)] to the variable [v].

 *)

Definition oneswapvar (a b : NVar) (v : NVar) : NVar :=
  if deq_nvar v a then b
  else if deq_nvar v b then a
       else v.

Definition swapping := AssocList NVar NVar.

(**

  [swapvar] generalizes [oneswapvar] to a list of swappings that gets
  applied from left to right.

 *)

Fixpoint swapvar (l : swapping) (v : NVar) : NVar :=
  match l with
    | [] => v
    | (a,b) :: rest => swapvar rest (oneswapvar a b v)
  end.

Definition swapbvars (l : swapping) (vs : list NVar) :=
  map (swapvar l) vs.

(**

  The [swap] operation is then defined as follows:

 *)

Fixpoint swap {p} (l : swapping) (t : @NTerm p) :=
  match t with
    | vterm v => vterm (swapvar l v)
    | oterm o bts => oterm o (map (swapbt l) bts)
  end
with swapbt {p} (l : swapping) (bt : BTerm) :=
  match bt with
    | bterm vs t => bterm (swapbvars l vs) (swap l t)
  end.

Definition mk_swapping (vs1 vs2 : list NVar) : swapping :=
  combine vs1 vs2.

(**

  Using [swap], we can now define alpha-equivalence as follows.  Our
  definition is parametrized by a list of variables [vs] which are
  variables that must be disjoint from the fresh variables we pick
  while building swappings.

 *)

Inductive alphaeq_vs {p} (l : list NVar) : @NTerm p -> @NTerm p -> Type :=
  | aeqv : forall v, alphaeq_vs l (vterm v) (vterm v)
  | aeqo :
      forall o bts1 bts2,
        length bts1 = length bts2
        -> (forall n,
              n < length bts1
              -> alphaeqbt_vs l (selectbt bts1 n) (selectbt bts2 n))
        -> alphaeq_vs l (oterm o bts1) (oterm o bts2)
with alphaeqbt_vs {p} (l : list NVar) : @BTerm p -> @BTerm p -> Type :=
 | aeqbt :
     forall vs vs1 vs2 t1 t2,
       length vs = length vs1
       -> length vs = length vs2
       -> disjoint vs (l ++ vs1 ++ vs2 ++ allvars t1 ++ allvars t2)
       -> no_repeats vs
       -> alphaeq_vs l (swap (mk_swapping vs1 vs) t1) (swap (mk_swapping vs2 vs) t2)
       -> alphaeqbt_vs l (bterm vs1 t1) (bterm vs2 t2).
Hint Constructors alphaeq_vs.

(**

  Finally, we define alpha-equality as follows.

 *)

Definition alphaeq {p} := @alphaeq_vs p [].
Definition alphaeqbt {p} := @alphaeqbt_vs p [].


(* begin hide *)


Lemma size_swap {p} :
  forall t l,
    size (@swap p l t) = size t.
Proof.
  nterm_ind1 t as [v|o bts Hind] Case; introv; simpl; auto.
  assert (map size_bterm (map (swapbt l) bts) = map size_bterm bts)
    as e; [| complete (rw e; auto)].
  rw map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x; simpl.
  apply Hind with (lv := l0); auto.
Qed.


Definition rename {p} (t : @NTerm p) (vs1 vs2 : list NVar) :=
  lsubst t (var_ren vs1 vs2).

Lemma fold_rename {p} :
  forall t vs1 vs2, lsubst t (@var_ren p vs1 vs2) = rename t vs1 vs2.
Proof. sp. Qed.

Definition rename_aux {p} (t : @NTerm p) (vs1 vs2 : list NVar) :=
  lsubst_aux t (var_ren vs1 vs2).

Lemma fold_rename_aux {p} :
  forall t vs1 vs2, lsubst_aux t (@var_ren p vs1 vs2) = rename_aux t vs1 vs2.
Proof. sp. Qed.

Definition swapping2sub {p} (s : swapping) : @Sub p :=
  map (fun x => match x with (v1,v2) => (v1, vterm v2) end) s.

Ltac dest_dec_disjointv :=
  match goal with
    | [ |- context[dec_disjointv ?x ?y] ] => destruct (dec_disjointv x y)
  end.

Definition ltruncate {T} (l1 l2 : list T) := firstn (length l1) l2.

Lemma range_combine_eq {p} :
  forall l1 l2,
    @range p (combine l1 l2) = firstn (length l1) l2.
Proof.
  induction l1; simpl; introv; auto.
  destruct l2; simpl; auto.
  rw IHl1; auto.
Qed.

Lemma range_swapping2sub_combine {p} :
  forall vs1 vs2,
    @range p (swapping2sub (combine vs1 vs2))
    = map vterm (firstn (length vs1) vs2).
Proof.
  induction vs1; introv; simpl; auto.
  destruct vs2; simpl; auto.
  rw IHvs1; auto.
Qed.

Lemma swapping2sub_combine {p} :
  forall vs1 vs2,
    swapping2sub (combine vs1 vs2) = combine vs1 (map (@vterm p) vs2).
Proof.
  induction vs1; simpl; introv; auto.
  destruct vs2; simpl; auto.
  rw IHvs1; auto.
Qed.

Lemma swapping2sub_mk_swapping_as_var_ren {p} :
  forall vs1 vs2,
    swapping2sub (mk_swapping vs1 vs2) = @var_ren p vs1 vs2.
Proof.
  unfold var_ren, mk_swapping.
  introv.
  rw @swapping2sub_combine; auto.
Qed.

Lemma rename_eq {p} :
  forall t vs1 vs2,
    rename t vs1 vs2 = lsubst t (@swapping2sub p (mk_swapping vs1 vs2)).
Proof.
  unfold rename; introv.
  rw @swapping2sub_mk_swapping_as_var_ren; sp.
Qed.

Lemma rename_aux_eq {p} :
  forall t vs1 vs2,
    rename_aux t vs1 vs2 = lsubst_aux t (@swapping2sub p (mk_swapping vs1 vs2)).
Proof.
  unfold rename_aux; introv.
  rw @swapping2sub_mk_swapping_as_var_ren; sp.
Qed.

Definition option_with_default {A} (o : option A) (e : A) :=
  match o with
    | Some x => x
    | None => e
  end.

Lemma lsubst_vterm {p} :
  forall v sub,
    lsubst (vterm v) sub
    = option_with_default (sub_find sub v) (@vterm p v).
Proof.
  introv; reflexivity.
Qed.

Lemma lsubst_aux_vterm {p} :
  forall v sub,
    lsubst_aux (vterm v) sub
    = option_with_default (sub_find sub v) (@vterm p v).
Proof.
  introv; reflexivity.
Qed.

Lemma sub_find_is_ALFind {p} :
  forall s v,
    @sub_find p s v = ALFind deq_nvar s v.
Proof.
  induction s; simpl; introv; auto.
  destruct a.
  boolvar; sp.
Qed.

Definition renFind (s : list (NVar * NVar)) v := ALFind deq_nvar s v.

Lemma sub_find_swapping2sub {p} :
  forall s v,
    @sub_find p (swapping2sub s) v
    = option_map vterm (renFind s v).
Proof.
  induction s; simpl; introv; auto.
  destruct a; boolvar; sp.
Qed.

Lemma swapvar_not_in :
  forall v vs1 vs2,
    !LIn v vs1
    -> !LIn v vs2
    -> swapvar (mk_swapping vs1 vs2) v = v.
Proof.
  induction vs1; simpl; introv ni1 ni2; auto.
  allrw not_over_or; repnd.
  destruct vs2; simpl; auto.
  allsimpl; allrw not_over_or; repnd.
  unfold oneswapvar; boolvar; sp.
Qed.

Lemma swapvar_eq :
  forall vs1 vs2 v,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> !LIn v vs2
    -> swapvar (mk_swapping vs1 vs2) v
       = option_with_default (renFind (mk_swapping vs1 vs2) v) v.
Proof.
  induction vs1; simpl; introv norep disj ni; auto.
  destruct vs2; simpl; auto.
  boolvar;
    allrw disjoint_cons_r;
    allrw disjoint_cons_l;
    allrw no_repeats_cons;
    allsimpl; allrw not_over_or; repnd.

  - unfold oneswapvar; boolvar; try (complete sp); GC.
    apply swapvar_not_in; auto.

  - unfold oneswapvar; boolvar; try (complete sp); GC.
Qed.

Lemma swap_is_vterm {p} :
  forall vs1 vs2 t v,
    vterm v = swap (mk_swapping vs1 vs2) t
    -> {u : NVar & t = @vterm p u}.
Proof.
  destruct t; simpl; introv e; inversion e; subst.
  exists n; auto.
Qed.

Lemma swap_is_oterm {p} :
  forall vs1 vs2 t o bts,
    oterm o bts = swap (mk_swapping vs1 vs2) t
    -> {bts' : list (@BTerm p) & t = oterm o bts'}.
Proof.
  destruct t; simpl; introv e; inversion e; subst.
  exists l; auto.
Qed.

Lemma lsubst_vterm_eq_aux {p} :
  forall s v,
    lsubst (@vterm p v) s = lsubst_aux (vterm v) s.
Proof.
  introv; unfold lsubst; dest_dec_disjointv; allsimpl; sp.
Qed.

Lemma lsubst_is_vterm {p} :
  forall t s v,
    vterm v = lsubst t s
    -> {u : NVar & t = @vterm p u}.
Proof.
  destruct t; introv; unfold lsubst; simpl.
  - intro k; exists n; auto.
  - dest_dec_disjointv; introv k; inversion k.
Qed.

Lemma lsubst_aux_is_vterm {p} :
  forall t s v,
    vterm v = lsubst_aux t s
    -> {u : NVar & t = @vterm p u}.
Proof.
  destruct t; introv; simpl.
  - intro k; exists n; auto.
  - introv k; inversion k.
Qed.

Lemma apply_to_option_with_default :
  forall A B (f : A -> B) (o : option A) (e : A),
    f (option_with_default o e)
    = option_with_default (option_map f o) (f e).
Proof.
  introv.
  unfold option_with_default.
  destruct o; simpl; auto.
Qed.

Lemma option_with_default_option_map :
  forall A B (f : A -> B) o e,
    option_with_default
      (option_map f o)
      (f e)
    = f (option_with_default o e).
Proof.
  introv.
  unfold option_with_default, option_map.
  destruct o; auto.
Qed.

Lemma length_swapbvars :
  forall l vs, length (swapbvars l vs) = length vs.
Proof.
  introv; unfold swapbvars; rw map_length; auto.
Qed.

Lemma swapvar_swapvar :
  forall s1 s2 v,
    swapvar s1 (swapvar s2 v) = swapvar (s2 ++ s1) v.
Proof.
  induction s2; simpl; introv; auto.
  destruct a; auto.
Qed.

Lemma swapbvars_swapbvars :
  forall s1 s2 l,
    swapbvars s1 (swapbvars s2 l) = swapbvars (s2 ++ s1) l.
Proof.
  unfold swapbvars; introv.
  rw map_map.
  unfold compose.
  apply eq_maps; introv i.
  apply swapvar_swapvar.
Qed.

Lemma swap_swap {p} :
  forall s1 s2 t,
    swap s1 (@swap p s2 t) = swap (s2 ++ s1) t.
Proof.
  nterm_ind1 t as [v| o lbt Hind] Case; simpl.

  - Case "vterm".
    rw swapvar_swapvar; auto.

  - Case "oterm".
    apply oterm_eq; auto.
    rw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x; simpl.
    apply Hind in i.
    rw i.
    rw swapbvars_swapbvars; auto.
Qed.

Lemma mk_swapping_app :
  forall vs1 vs2 vs3 vs4,
    length vs1 = length vs2
    -> mk_swapping vs1 vs2 ++ mk_swapping vs3 vs4
       = mk_swapping (vs1 ++ vs3) (vs2 ++ vs4).
Proof.
  unfold mk_swapping.
  induction vs1; introv; simpl; destruct vs2; simpl; intro len; cpx.
  rw IHvs1; auto.
Qed.

Lemma alphaeq_vs_implies_less {p} :
  forall t1 t2 l1 l2,
    @alphaeq_vs p l1 t1 t2
    -> subvars l2 l1
    -> alphaeq_vs l2 t1 t2.
Proof.
  nterm_ind1s t1 as [v1|o1 lbt1 Hind] Case; introv aeq sv.

  - Case "vterm".
    inversion aeq; subst; auto.

  - Case "oterm".
    inversion aeq as [|? ? ? len aeqbts]; subst; clear aeq.
    constructor; auto.
    introv i.
    applydup aeqbts in i as h.
    remember (selectbt lbt1 n) as bt1.
    remember (selectbt bts2 n) as bt2.
    assert (LIn bt1 lbt1) as ibt by (subst; apply selectbt_in; auto).
    clear dependent n.
    destruct bt1 as [vs1 t1].
    destruct bt2 as [vs2 t2].
    inversion h as [? ? ? ? ? len1 len2 disj norep a]; subst.

    pose proof (Hind
                  t1
                  (swap (mk_swapping vs1 vs) t1)
                  vs1
                  ibt) as a1.

    autodimp a1 hyp; try (complete (rw @size_swap; eauto 3 with slow)).

    pose proof (a1 (swap (mk_swapping vs2 vs) t2)
                   l1
                   l2
                   a
                   sv) as a2;
      clear a1.

    apply @aeqbt with (vs := vs); auto; try omega.
    allrw disjoint_app_r; repnd; dands; auto.

    unfold disjoint; introv i1 i2.
    rw subvars_prop in sv.
    apply disj0 in i1.
    apply sv in i2; auto.
Qed.

Lemma renFind_some :
  forall vs1 vs2 v1 v2,
    Some v2 = renFind (mk_swapping vs1 vs2) v1
    -> forall vs3,
         length vs3 = length vs2
         -> {v3 : NVar & Some v3 = renFind (mk_swapping vs1 vs3) v1}.
Proof.
  induction vs1; simpl; intros vs2 v1 v2 e vs3 len; try (complete (inversion e)).
  destruct vs2; allsimpl; try (complete (inversion e)).
  destruct vs3; allsimpl; cpx.
  revert e; boolvar; intro e.
  - inversion e; subst; GC.
    exists n0; auto.
  - apply IHvs1 with (vs3 := vs3) in e; auto.
Qed.

Lemma renFind_some_in_codom :
  forall v vs1 vs2 v1,
    Some v = renFind (mk_swapping vs1 vs2) v1
    -> LIn v vs2.
Proof.
  induction vs1; introv e; allsimpl; try (complete (inversion e)).
  destruct vs2; allsimpl; try (complete (inversion e)).
  revert e; boolvar; intro e.
  - inversion e; subst; sp.
  - apply IHvs1 in e; sp.
Qed.

Lemma renFind_some_eq :
  forall vs1 vs2 vs v v1 v2,
    no_repeats vs
    -> Some v = renFind (mk_swapping vs1 vs) v1
    -> Some v = renFind (mk_swapping vs2 vs) v2
    -> forall vs',
         length vs = length vs'
         -> {v' : NVar
             & Some v' = renFind (mk_swapping vs1 vs') v1
             # Some v' = renFind (mk_swapping vs2 vs') v2}.
Proof.
  induction vs1; simpl; intros vs2 vs v v1 v2 norep e1 e2 vs' len; try (complete (inversion e1)).
  destruct vs; allsimpl; try (complete (inversion e1)).
  destruct vs'; allsimpl; cpx.
  revert e1; boolvar; intro e1.
  - inversion e1; subst; GC.
    exists n0; dands; auto.
    destruct vs2; allsimpl; try (complete (inversion e2)).
    revert e2; boolvar; intro e2.
    rw no_repeats_cons in norep; repnd.
    applydup renFind_some_in_codom in e2; sp.
  - destruct vs2; allsimpl; try (complete (inversion e2)).
    revert e2; boolvar; intro e2.
    + inversion e2; subst; GC.
      rw no_repeats_cons in norep; repnd.
      applydup renFind_some_in_codom in e1; sp.
    + rw no_repeats_cons in norep; repnd.
      eapply IHvs1; eauto.
Qed.

Lemma renFind_none :
  forall vs1 vs2 v,
    None = renFind (mk_swapping vs1 vs2) v
    -> forall vs3,
         length vs3 = length vs2
         -> None = renFind (mk_swapping vs1 vs3) v.
Proof.
  induction vs1; simpl; intros vs2 v e vs3 len; auto.
  destruct vs2; allsimpl; try (complete (inversion e));
  destruct vs3; allsimpl; cpx.
  revert e; boolvar; intro e; try (complete (inversion e)).
  eapply IHvs1; eauto.
Qed.

Lemma swapping_change_vars :
  forall l1 l2 vs1 vs2 v1 v2,
    no_repeats vs1
    -> length vs1 = length vs2
    -> !LIn v1 vs1
    -> !LIn v2 vs1
    -> option_with_default (renFind (mk_swapping l1 vs1) v1) v1
       = option_with_default (renFind (mk_swapping l2 vs1) v2) v2
    -> option_with_default (renFind (mk_swapping l1 vs2) v1) v1
       = option_with_default (renFind (mk_swapping l2 vs2) v2) v2.
Proof.
  introv norep len ni1 ni2.
  unfold option_with_default.
  remember (renFind (mk_swapping l1 vs1) v1); destruct o;
  remember (renFind (mk_swapping l2 vs1) v2); destruct o.
  - intro e; subst.
    pose proof (renFind_some_eq l1 l2 vs1 n0 v1 v2 norep Heqo Heqo0 vs2 len) as h;
      exrepnd.
    rw <- h1; rw <- h0; auto.
  - intro e; subst.
    apply renFind_some_in_codom in Heqo; sp.
  - intro e; subst.
    apply renFind_some_in_codom in Heqo0; sp.
  - intro e; subst.
    apply renFind_none with (vs3 := vs2) in Heqo; auto.
    apply renFind_none with (vs3 := vs2) in Heqo0; auto.
    rw <- Heqo; rw <- Heqo0; auto.
Qed.

Lemma in_swapvar_disj_iff :
  forall vs1 vs2 v vs,
    disjoint vs1 vs2
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> (LIn (swapvar (mk_swapping vs1 vs2) v) vs
        <=>
        (LIn v vs # !LIn v vs1 # !LIn v vs2)).
Proof.
  induction vs1; introv disj1 disj2 disj3; allsimpl; split; intro i;
  repnd; auto.
  - dands; auto; sp.
  - destruct vs2; allsimpl; dands; auto; sp; subst;
    allrw disjoint_cons_r; allrw disjoint_cons_l; repnd;
    allsimpl; allrw not_over_or; repnd;
    try (complete sp);
    try (complete (apply disj4 in i; allsimpl; destruct i; sp));
    try (complete (revert i; unfold oneswapvar; boolvar; intro i;
                   apply IHvs1 in i; repnd; sp)).
  - destruct vs2; allsimpl; auto.
    allrw not_over_or; allrw disjoint_cons_l; allrw disjoint_cons_r; repnd.
    unfold oneswapvar; boolvar; sp.
    apply IHvs1; auto.
Qed.

Lemma in_swapvar_disj_iff2 :
  forall vs1 vs2 v vs,
    !LIn v vs
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> (LIn (swapvar (mk_swapping vs1 vs2) v) vs
        <=>
        False).
Proof.
  induction vs1; introv disj1 disj2 disj3; allsimpl; split; intro i;
  repnd; auto.
  - dands; auto; sp.
  - destruct vs2; allsimpl; dands; auto; sp; subst;
    allrw disjoint_cons_r; allrw disjoint_cons_l; repnd;
    allsimpl; allrw not_over_or; repnd;
    try (complete sp);
    try (complete (apply disj4 in i; allsimpl; destruct i; sp));
    try (complete (revert i; unfold oneswapvar; boolvar; intro i;
                   apply IHvs1 in i; repnd; sp)).
  - destruct vs2; allsimpl; auto; sp.
Qed.

Lemma disjoint_swapbvars_implies :
  forall bvs vs vs1 vs2 vs3,
    length vs2 = length vs3
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs vs3
    -> disjoint vs1 vs2
    -> disjoint vs1 vs3
    -> disjoint vs (swapbvars (mk_swapping vs1 vs2) bvs)
    -> disjoint vs (swapbvars (mk_swapping vs1 vs3) bvs).
Proof.
  induction bvs; introv len disjvs1 disjvs2 disjvs3 disjvs12 disjvs13 disj; allsimpl; auto.
  allrw disjoint_cons_r; repnd; dands.
  - eapply IHbvs; eauto.
  - intro i; destruct disj.
    apply in_swapvar_disj_iff in i; auto; repnd.
    apply in_swapvar_disj_iff; auto.
Qed.

Lemma disjoint_swapbvars :
  forall bvs vs vs1 vs2,
    length vs1 = length vs2
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs bvs
    -> disjoint vs (swapbvars (mk_swapping vs1 vs2) bvs).
Proof.
  induction bvs; introv len disj1 disj2 disj3; allsimpl; auto; try (complete sp).
  allrw disjoint_cons_r; repnd; dands.
  - eapply IHbvs; eauto.
  - intro i.
    apply in_swapvar_disj_iff2 in i; sp.
Qed.

Lemma disjoint_allvars_implies {p} :
  forall t vs vs1 vs2 vs3,
    length vs2 = length vs3
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs vs3
    -> disjoint vs1 vs2
    -> disjoint vs1 vs3
    -> disjoint vs (allvars (@swap p (mk_swapping vs1 vs2) t))
    -> disjoint vs (allvars (swap (mk_swapping vs1 vs3) t)).
Proof.
  nterm_ind1s t as [v|o lbt Hind] Case;
  introv len disj1 disj2 disj3 disj4 disj5 d; allsimpl; auto.

  - Case "vterm".
    allrw disjoint_singleton_r.
    intro k.
    destruct d.
    apply in_swapvar_disj_iff in k; auto; repnd.
    apply in_swapvar_disj_iff; dands; auto.

  - Case "oterm".
    rw flat_map_map.
    rw flat_map_map in d.
    rw disjoint_flat_map_r in d.
    apply disjoint_flat_map_r; introv i.
    applydup d in i as d'; clear d; rename d' into d.
    unfold compose in d; unfold compose.
    destruct x; allsimpl.
    allrw disjoint_app_r; repnd.
    dands; try (complete (eapply Hind; eauto 3 with slow));[].
    apply disjoint_swapbvars_implies with (vs2 := vs2); auto.
Qed.

Lemma disjoint_allvars_swap {p} :
  forall t vs vs1 vs2,
    length vs1 = length vs2
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs (@allvars p t)
    -> disjoint vs (allvars (swap (mk_swapping vs1 vs2) t)).
Proof.
  nterm_ind1s t as [v|o lbt Hind] Case; introv len disj1 disj2 disj3; allsimpl; auto.

  - Case "vterm".
    allrw disjoint_singleton_r.
    intro k.
    apply in_swapvar_disj_iff2 in k; sp.

  - Case "oterm".
    rw flat_map_map.
    rw disjoint_flat_map_r in disj3.
    apply disjoint_flat_map_r; introv i.
    applydup disj3 in i as d.
    destruct x; unfold compose; allsimpl.
    allrw disjoint_app_r; repnd.
    dands; try (complete (eapply Hind; eauto 3 with slow)).
    apply disjoint_swapbvars; auto.
Qed.

Lemma in_swapbvars :
  forall v sw vs,
    LIn v (swapbvars sw vs)
    <=> {v' : NVar & LIn v' vs # v = swapvar sw v'}.
Proof.
  introv.
  rw in_map_iff; sp.
Qed.

Lemma swapvar_implies :
  forall vs1 vs2 v,
    let w := swapvar (mk_swapping vs1 vs2) v in
    w = v [+] LIn w vs1 [+] LIn w vs2.
Proof.
  simpl; induction vs1; introv; introv; allsimpl; destruct vs2; allsimpl; cpx.
  unfold oneswapvar; boolvar; tcsp.
  - pose proof (IHvs1 vs2 n) as h; sp.
  - pose proof (IHvs1 vs2 a) as h; sp.
  - pose proof (IHvs1 vs2 v) as h; sp.
Qed.

Lemma swapvar_implies2 :
  forall vs1 vs2 v,
    let w := swapvar (mk_swapping vs1 vs2) v in
    w = v [+] LIn v vs1 [+] LIn v vs2.
Proof.
  simpl; induction vs1; introv; introv; allsimpl; destruct vs2; allsimpl; cpx.
  unfold oneswapvar; boolvar; tcsp.
  pose proof (IHvs1 vs2 v) as h; sp.
Qed.

Lemma swapvars_eq :
  forall vs1 vs2 v1 v2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> swapvar (mk_swapping vs1 vs2) v1
       = swapvar (mk_swapping vs1 vs2) v2
    -> v1 = v2.
Proof.
  induction vs1; introv norep2 disj e; allsimpl; auto.
  destruct vs2; allsimpl; auto.
  allrw no_repeats_cons; repnd.
  allrw disjoint_cons_l; allrw disjoint_cons_r; repnd.
  apply IHvs1 in e; auto.
  revert e.
  unfold oneswapvar; boolvar; intro e; subst; auto; try (complete sp).
Qed.

Lemma swapvars_eq2 :
  forall vs1 vs2 v1 v2,
    !LIn v1 vs2
    -> !LIn v2 vs2
    -> no_repeats vs2
    -> swapvar (mk_swapping vs1 vs2) v1
       = swapvar (mk_swapping vs1 vs2) v2
    -> v1 = v2.
Proof.
  induction vs1; introv ni1 ni2 norep e; allsimpl; auto.
  destruct vs2; allsimpl; auto.
  allrw no_repeats_cons; repnd.
  allrw not_over_or; repnd.
  revert e.
  unfold oneswapvar; boolvar; try (complete sp); intro e; apply IHvs1 in e; sp.
Qed.

Lemma swapvar_app_swap :
  forall vs1 vs2 vs3 vs4 v,
    length vs1 = length vs3
    -> length vs2 = length vs4
    -> no_repeats vs3
    -> no_repeats vs4
    -> disjoint vs3 vs1
    -> disjoint vs3 vs2
    -> disjoint vs3 vs4
    -> disjoint vs2 vs4
    -> !LIn v vs3
    -> swapvar (mk_swapping (vs1 ++ vs2) (vs3 ++ vs4)) v
       = swapvar
           (mk_swapping (vs2 ++ swapbvars (mk_swapping vs2 vs4) vs1)
                        (vs4 ++ vs3))
           v.
Proof.
  induction vs1; simpl;
  introv len1 len2 norep2 norep3;
  introv disj1 disj2 disj3 disj4 ni2;
  destruct vs3; allsimpl; cpx;
  allrw app_nil_r; auto.

  allrw disjoint_cons_r; allrw disjoint_cons_l; repnd.
  allsimpl; allrw not_over_or; repnd; GC.
  unfold oneswapvar; boolvar; try (complete sp).

  - allrw <- mk_swapping_app; auto.
    allrw <- swapvar_swapvar.
    remember (swapvar (mk_swapping vs2 vs4) a).
    simpl.
    unfold oneswapvar; boolvar; subst; GC.
    allrw no_repeats_cons; repnd.
    rw (swapvar_not_in n vs1 vs3); auto.
    rw (swapvar_not_in n vs2 vs4); auto.
    rw swapvar_not_in; auto; intro k.
    apply in_swapbvars in k; exrepnd.
    pose proof (swapvar_implies vs2 vs4 v') as h; simpl in h.
    dorn h;[|dorn h]; rw <- k0 in h; clear k0; subst; sp.

  - allrw <- mk_swapping_app; auto.
    allrw <- swapvar_swapvar; simpl.
    unfold oneswapvar; boolvar.
    apply swapvars_eq in e; auto; subst; sp.
    pose proof (swapvar_implies vs2 vs4 v) as h; simpl in h; rw e in h; sp.
    allrw swapvar_swapvar.
    allrw mk_swapping_app; auto.
    allrw no_repeats_cons; repnd.
    apply IHvs1; auto; rw disjoint_cons_r; sp.
Qed.

Lemma swapbvars_app_swap :
  forall l vs1 vs2 vs3 vs4,
    length vs1 = length vs3
    -> length vs2 = length vs4
    -> no_repeats vs3
    -> no_repeats vs4
    -> disjoint vs3 vs1
    -> disjoint vs3 vs2
    -> disjoint vs3 vs4
    -> disjoint vs2 vs4
    -> disjoint vs3 l
    -> swapbvars (mk_swapping (vs1 ++ vs2) (vs3 ++ vs4)) l =
       swapbvars
         (mk_swapping (vs2 ++ swapbvars (mk_swapping vs2 vs4) vs1) (vs4 ++ vs3))
         l.
Proof.
  induction l;
  introv len1 len2 norep2 norep3;
  introv disj1 disj2 disj3 disj4 disj5;
  allsimpl; auto.
  allrw disjoint_cons_r; repnd.
  rw <- IHl; auto.
  rw swapvar_app_swap; auto.
Qed.

Lemma swapvar_swapvar2 :
  forall vs1 vs2 vs3 vs4 v,
    length vs1 = length vs3
    -> disjoint vs3 vs2
    -> disjoint vs3 vs4
    -> disjoint vs2 vs4
    -> no_repeats vs4
    -> swapvar (mk_swapping vs2 vs4) (swapvar (mk_swapping vs1 vs3) v)
       = swapvar (mk_swapping (swapbvars (mk_swapping vs2 vs4) vs1) vs3)
                 (swapvar (mk_swapping vs2 vs4) v).
Proof.
    induction vs1 as [|v1 vs1]; introv len1 disj1 disj2 disj3 norep1;
    allsimpl; cpx; allrw app_nil_r; allsimpl; auto.
    destruct vs3 as [|v3 vs3]; allsimpl; cpx.
    allrw disjoint_cons_l; allrw disjoint_cons_r; repnd.
    allrw no_repeats_cons; repnd.
    allsimpl; allrw not_over_or; repnd.
    rw IHvs1; auto.
    f_equal.
    unfold oneswapvar; boolvar; auto; tcsp.
    + apply swapvar_not_in; auto.
    + apply swapvars_eq in e; auto; subst.
      apply swapvar_not_in; auto.
    + rw swapvar_not_in in n1; tcsp.
    + apply swapvars_eq in e; auto; subst; tcsp.
    + rw <- (swapvar_not_in v3 vs2 vs4) in e; tcsp.
      apply swapvars_eq in e; auto; subst; tcsp.
Qed.

Lemma swapbvars_swapbvars2 :
  forall l vs1 vs2 vs3 vs4,
    length vs1 = length vs3
    -> disjoint vs3 vs2
    -> disjoint vs3 vs4
    -> disjoint vs2 vs4
    -> no_repeats vs4
    -> swapbvars (mk_swapping (swapbvars (mk_swapping vs2 vs4) vs1) vs3)
                 (swapbvars (mk_swapping vs2 vs4) l)
       = swapbvars (mk_swapping vs2 vs4) (swapbvars (mk_swapping vs1 vs3) l).
Proof.
  induction l; introv len1 disj1 disj2 disj3 norep1; simpl; auto.
  f_equal.
  - rw <- swapvar_swapvar2; auto.
  - apply IHl; auto.
Qed.

Lemma swap_swap2 {o} :
  forall (t : @NTerm o) vs1 vs2 vs3 vs4,
    length vs1 = length vs3
    -> no_repeats vs4
    -> disjoint vs3 vs2
    -> disjoint vs3 vs4
    -> disjoint vs2 vs4
    -> swap (mk_swapping (swapbvars (mk_swapping vs2 vs4) vs1) vs3)
            (swap (mk_swapping vs2 vs4) t)
       = swap (mk_swapping vs2 vs4) (swap (mk_swapping vs1 vs3) t).
Proof.
  nterm_ind1s t as [v|op bs ind] Case;
  introv len1 norep1 disj1 disj2 disj3; auto.

  - Case "vterm".
    allsimpl; f_equal.
    rw <- swapvar_swapvar2; auto.

  - Case "oterm".
    simpl; f_equal.
    allrw map_map; allunfold @compose.
    apply eq_maps; introv i.
    destruct x as [l t]; allsimpl.
    rw swapbvars_swapbvars2; auto.
    f_equal.
    eapply ind; eauto 3 with slow.
Qed.

Lemma swap_app_swap {o} :
  forall (t : @NTerm o) vs1 vs2 vs3 vs4,
    length vs1 = length vs3
    -> length vs2 = length vs4
    -> no_repeats vs4
    -> disjoint vs3 vs2
    -> disjoint vs3 vs4
    -> disjoint vs2 vs4
    -> swap (mk_swapping (vs1 ++ vs2) (vs3 ++ vs4)) t
       = swap
           (mk_swapping (vs2 ++ swapbvars (mk_swapping vs2 vs4) vs1)
                        (vs4 ++ vs3))
           t.
Proof.
  introv len1 len2 norep1 disj1 disj2 disj3.
  allrw <- mk_swapping_app; auto.
  allrw <- @swap_swap.
  rw @swap_swap2; auto.
Qed.

Lemma alphaeq_add_swap {o} :
  forall vs vs1 vs2 (t1 t2 : @NTerm o),
    length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint vs2 vs1
    -> alphaeq_vs (vs1 ++ vs2 ++ vs) t1 t2
    -> alphaeq_vs
         (vs1 ++ vs2 ++ vs)
         (swap (mk_swapping vs1 vs2) t1)
         (swap (mk_swapping vs1 vs2) t2).
Proof.
  nterm_ind1s t1 as [v1|o1 lbt1 Hind] Case; introv len norep2 disj aeq; auto.

  - Case "vterm".
    inversion aeq; subst; allsimpl; auto.

  - Case "oterm".
    allsimpl.
    inversion aeq as [|? ? ? eqlens aeqbts e1 oeq]; subst; clear aeq.
    allsimpl.
    apply aeqo; allrw map_length; auto.
    introv lt.
    applydup aeqbts in lt; clear aeqbts.
    repeat (rw @selectbt_map; try omega).
    remember (selectbt lbt1 n) as bt1.
    remember (selectbt bts2 n) as bt2.
    assert (LIn bt1 lbt1) as ibt1 by (subst; apply selectbt_in; auto).
    assert (LIn bt2 bts2) as ibt2 by (subst; apply selectbt_in; omega).
    clear dependent n.
    destruct bt1 as [bvs1 t1].
    destruct bt2 as [bvs2 t2].
    allsimpl.
    inversion lt0 as [? ? ? ? ? leneq1 leneq2 d n a]; subst; clear lt0.
    allrw disjoint_app_r; repnd.
    allrw disjoint_flat_map_r.
    allsimpl; allrw disjoint_app_r; repnd.

    apply Hind with (lv := bvs1) (nt := t1) in a; auto;
    allrw @size_swap;
    eauto 3 with slow;
    try (complete (allrw disjoint_app_r; dands; auto;
                   apply disjoint_allvars_swap; auto;
                   try (apply disjoint_sym; auto))).

    repeat (rw @swap_swap in a).
    repeat (rw mk_swapping_app in a; auto).

    apply @aeqbt with (vs := vs0); auto;
    try (complete (rw length_swapbvars; omega)).

    { allrw disjoint_app_r; repnd.
      pose proof (disjoint_swapbvars bvs1 vs0 vs1 vs2) as h1;
        repeat (autodimp h1 hyp); try omega.
      pose proof (disjoint_swapbvars bvs2 vs0 vs1 vs2) as h2;
        repeat (autodimp h2 hyp); try omega.
      pose proof (disjoint_allvars_swap t1 vs0 vs1 vs2) as h3;
        repeat (autodimp h3 hyp); try omega.
      pose proof (disjoint_allvars_swap t2 vs0 vs1 vs2) as h4;
        repeat (autodimp h4 hyp); try omega. }

    rw @swap_swap.
    allrw @swap_swap.
    repeat (rw mk_swapping_app;[|complete omega]).

    rw <- @swap_app_swap; auto; try (complete (apply disjoint_sym; auto)).
    rw <- @swap_app_swap; auto; try (complete (apply disjoint_sym; auto)).
Qed.

Lemma swapvar_disj_chain :
  forall vs1 vs vs2 v,
    length vs = length vs1
    -> length vs = length vs2
    -> no_repeats vs
    -> no_repeats vs2
    -> disjoint vs (vs1 ++ vs2 ++ [v])
    -> disjoint vs2 (vs1 ++ [v])
    -> swapvar (mk_swapping (vs1 ++ vs) (vs ++ vs2)) v
       = swapvar (mk_swapping vs1 vs2) v.
Proof.
  induction vs1; introv len1 len2 norep1 norep2 disj1 disj2;
  allsimpl; destruct vs; allsimpl; cpx.
  destruct vs2; allsimpl; cpx.

  allrw disjoint_cons_l; allrw disjoint_cons_r;
  allrw disjoint_app_r;  allrw disjoint_cons_r;
  allrw disjoint_app_r;  allrw disjoint_singleton_r;
  allsimpl; allrw in_app_iff; allsimpl; allrw in_app_iff;
  allrw in_single_iff; allrw not_over_or;
  allrw no_repeats_cons; repnd; GC.

  unfold oneswapvar; boolvar; try (complete sp).

  - rw <- mk_swapping_app; auto.
    rw <- swapvar_swapvar; simpl.
    unfold oneswapvar; boolvar; auto.

    + repeat (rw swapvar_not_in; auto).

    + repeat (rw swapvar_not_in; auto).
      repeat (rw swapvar_not_in in e; auto).

    + provefalse; destruct n1.
      rw swapvar_not_in; auto.

  - rw <- mk_swapping_app; auto.
    rw <- swapvar_swapvar; simpl.
    unfold oneswapvar; boolvar; auto.

    + symmetry in len1.
      pose proof (swapvar_implies vs1 vs v) as o; simpl in o.
      rw e in o. sp.

    + symmetry in len1.
      pose proof (swapvar_implies vs1 vs v) as o; simpl in o.
      rw e in o; sp.

    + pose proof (@in_deq NVar deq_nvar v vs1) as h.
      dorn h; try (complete (repeat (rw swapvar_not_in; auto))).
      rw swapvar_swapvar.
      rw mk_swapping_app; auto.
      apply IHvs1; auto; allrw disjoint_app_r; allrw disjoint_singleton_r; auto.
Qed.

Lemma swapbvars_disj_chain :
  forall l vs1 vs vs2,
    length vs = length vs1
    -> length vs = length vs2
    -> no_repeats vs
    -> no_repeats vs2
    -> disjoint vs (vs1 ++ vs2 ++ l)
    -> disjoint vs2 (vs1 ++ l)
    -> swapbvars (mk_swapping (vs1 ++ vs) (vs ++ vs2)) l
       = swapbvars (mk_swapping vs1 vs2) l.
Proof.
  induction l; introv len1 len2 norep1 norep2 disj1 disj2; allsimpl; auto.
  allrw disjoint_app_r; allrw disjoint_cons_r; repnd.
  rw swapvar_disj_chain; auto;
  allrw disjoint_app_r; allrw disjoint_singleton_r; auto.
  rw IHl; auto; allrw disjoint_app_r; auto.
Qed.

Lemma swap_disj_chain {o} :
  forall (t : @NTerm o) vs1 vs vs2,
    length vs = length vs1
    -> length vs = length vs2
    -> no_repeats vs
    -> no_repeats vs2
    -> disjoint vs (vs1 ++ vs2 ++ allvars t)
    -> disjoint vs2 (vs1 ++ allvars t)
    -> swap (mk_swapping (vs1 ++ vs) (vs ++ vs2)) t
       = swap (mk_swapping vs1 vs2) t.
Proof.
  nterm_ind1s t as [v|op bs Hind] Case;
  introv len1 len2 norep1 norep2 disj1 disj2; allsimpl; auto.

  - Case "vterm".
    rw swapvar_disj_chain; auto.

  - Case "oterm".
    apply oterm_eq; auto.
    apply eq_maps; introv i.
    destruct x; allsimpl.
    allrw disjoint_app_r; repnd.
    allrw disjoint_flat_map_r.
    applydup disj1 in i; applydup disj2 in i; allsimpl.
    allrw disjoint_app_r; repnd.

    erewrite Hind; eauto 3 with slow; allrw disjoint_app_r; dands; auto.
    rw swapbvars_disj_chain; auto; allrw disjoint_app_r; dands; auto.
Qed.

Lemma alphaeq_implies_alphaeq_vs {p} :
  forall t1 t2, @alphaeq p t1 t2 -> forall l, alphaeq_vs l t1 t2.
Proof.
  nterm_ind1s t1 as [v1|o1 lbt1 Hind] Case; introv aeq; introv; auto.

  - Case "vterm".
    inversion aeq; subst; auto.

  - Case "oterm".
    inversion aeq as [| ? ? ? len aeqbts]; subst; clear aeq.
    constructor; auto.
    introv i.
    applydup aeqbts in i as h.
    remember (selectbt lbt1 n) as bt1.
    remember (selectbt bts2 n) as bt2.
    assert (LIn bt1 lbt1) as ibt by (subst; apply selectbt_in; auto).
    clear dependent n.
    destruct bt1 as [l1 t1].
    destruct bt2 as [l2 t2].
    inversion h as [? ? ? ? ? len1 len2 disj norep a]; subst.

    pose proof (fresh_vars (length vs)
                           (l ++ vs
                              ++ l1
                              ++ l2
                              ++ allvars t1
                              ++ allvars t2))
      as Hfresh.
    destruct Hfresh as [l' d]; repnd.

    apply @aeqbt with (vs := l'); auto; try omega.
    allrw disjoint_app_r; sp.

    pose proof (Hind
                  t1
                  (swap (mk_swapping l1 vs) t1)
                  l1
                  ibt) as a1.

    autodimp a1 hyp.
    { rw @size_swap; eauto 3 with slow. }

    pose proof (a1 (swap (mk_swapping l2 vs) t2)
                   a
                   (vs ++ l' ++ l)) as a2;
      clear a1.

    allsimpl.

    assert (disjoint l' vs) as disj1 by (allrw disjoint_app_r; sp).
    assert (disjoint l' (allvars (swap (mk_swapping l1 vs) t1)))
      as disj2 by (allrw disjoint_app_r; repnd;
                   apply disjoint_allvars_swap; auto).
    assert (disjoint l' (allvars (swap (mk_swapping l2 vs) t2)))
      as disj3 by (allrw disjoint_app_r; repnd;
                   apply disjoint_allvars_swap; auto).

    applydup @alphaeq_add_swap in a2; auto;
    try (complete (allrw disjoint_app_r; auto)).

    allrw @swap_swap.
    repeat (rw mk_swapping_app in a0; try omega).

    rw @swap_disj_chain in a0; auto;
    try (complete (allrw disjoint_app_r; sp; try (complete (apply disjoint_sym; auto)))).

    rw @swap_disj_chain in a0; auto;
    try (complete (allrw disjoint_app_r; sp; try (complete (apply disjoint_sym; auto)))).

    apply @alphaeq_vs_implies_less with (l1 := vs ++ l' ++ l); auto.
    rw app_assoc; apply subvars_app_trivial_r.
Qed.

Lemma alphaeq_vs_implies_more {p} :
  forall t1 t2 l1 l2,
    @alphaeq_vs p l1 t1 t2
    -> subvars l1 l2
    -> alphaeq_vs l2 t1 t2.
Proof.
  introv aeq sv.
  apply @alphaeq_vs_implies_less with (l2 := []) in aeq; auto.
  apply alphaeq_implies_alphaeq_vs; auto.
Qed.


(* end hide *)


Lemma alphaeq_all {p} :
  forall t1 t2, @alphaeq p t1 t2 <=> (forall l, alphaeq_vs l t1 t2).
Proof.
  introv; split; intro k.
  - introv; apply alphaeq_implies_alphaeq_vs; auto.
  - pose proof (k []); auto.
Qed.

Lemma alphaeq_exists {p} :
  forall t1 t2, @alphaeq p t1 t2 <=> {l : list NVar & alphaeq_vs l t1 t2}.
Proof.
  introv; split; intro k.
  - exists ([] : list NVar); auto.
  - exrepnd; apply alphaeq_vs_implies_less with (l1 := l); auto.
Qed.


(* begin hide *)


Lemma allvars_eq_all_vars {p} :
  forall t, eqvars (@allvars p t) (all_vars t).
Proof.
  nterm_ind1 t as [v|o lbt Hind] Case; simpl; auto.

  Case "oterm".
  unfold all_vars; simpl.
  rw eqvars_prop; introv; split; intro k.

  - rw in_app_iff; allrw lin_flat_map; exrepnd.
    destruct x0; allsimpl.
    allrw in_app_iff.
    applydup Hind in k1.
    rw eqvars_prop in k2.
    dorn k0.

    + right; exists (bterm l n); simpl; rw in_app_iff; sp.

    + applydup k2 in k0.
      unfold all_vars in k3; rw in_app_iff in k3.
      destruct (in_deq NVar deq_nvar x l).

      right; exists (bterm l n); simpl; rw in_app_iff; sp.

      dorn k3.

      left; exists (bterm l n); simpl; rw in_remove_nvars; sp.

      right; exists (bterm l n); simpl; rw in_app_iff; sp.

  - rw in_app_iff in k.
    allrw lin_flat_map.

    dorn k; exrepnd; exists x0; dands; auto; destruct x0; allsimpl;
    allrw in_remove_nvars; repnd;
    applydup Hind in k1 as e; allrw in_app_iff;
    rw eqvars_prop in e.

    + right.
      apply e.
      unfold all_vars; rw in_app_iff; sp.

    + dorn k0; try (complete sp).
      right; apply e.
      unfold all_vars; rw in_app_iff; sp.
Qed.
Hint Immediate allvars_eq_all_vars.

Lemma disjoint_to_all_vars_r {p} :
  forall s t, disjoint s (@allvars p t) -> disjoint s (all_vars t).
Proof.
  introv d.
  eapply eqvars_disjoint_r; eauto.
Qed.

Lemma disjoint_to_allvars_r {p} :
  forall s t, disjoint s (@all_vars p t) -> disjoint s (allvars t).
Proof.
  introv d.
  apply eqvars_disjoint_r with (s1 := all_vars t); auto.
  apply eqvars_sym; auto.
Qed.

Lemma disjoint_allvars_lsubst_aux {p} :
  forall t sub vs,
    disjoint vs (allvars t)
    -> disjoint vs (flat_map allvars (@range p sub))
    -> disjoint vs (allvars (lsubst_aux t sub)).
Proof.
  nterm_ind1 t as [v|o lbt Hind] Case; simpl;
  introv d1 d2; auto.

  - Case "vterm".
    remember (sub_find sub v); destruct o; simpl; symmetry in Heqo; auto.

    apply sub_find_some in Heqo.
    rw disjoint_flat_map_r in d2.
    pose proof (d2 n) as k.
    autodimp k hyp.
    apply in_range_iff; exists v; auto. (* this used to use in_range_t_iff *)

  - Case "oterm".
    allrw disjoint_flat_map_r; introv k.
    rw in_map_iff in k; exrepnd; subst.
    destruct a; allsimpl.
    applydup d1 in k1; allsimpl; allrw disjoint_app_r; repnd; dands; auto.
    apply Hind with (lv := l); auto.
    apply disjoint_flat_map_r; introv h.
    apply d2.
    allrw @in_range_iff; exrepnd.  (* this used to use in_range_t_iff *)
    exists v.
    apply in_sub_filter in h0; sp.
Qed.

Lemma in_swapping2sub {p} :
  forall v t s,
    LIn (v,t) (swapping2sub s)
    <=> {u : NVar & t = @vterm p u # LIn (v,u) s}.
Proof.
  induction s; simpl; split; intro k; exrepnd; subst; try (complete sp).
  - dorn k; cpx.
    + exists a; sp.
    + apply IHs in k; exrepnd; subst.
      exists u; sp.
  - dorn k0; cpx.
    right; apply IHs; exists u; sp.
Qed.

Lemma in_mk_swapping_implies :
  forall v1 v2 vs1 vs2,
    LIn (v1, v2) (mk_swapping vs1 vs2)
    -> LIn v1 vs1 # LIn v2 vs2.
Proof.
  introv i.
  unfold mk_swapping in i.
  apply in_combine in i; sp.
Qed.

Lemma sub_filter_var_ren_implies {p} :
  forall vs1 vs2 l,
    {vs3 : list NVar
     & {vs4 : list NVar
        & sub_filter (var_ren vs1 vs2) l = @var_ren p vs3 vs4
        # eqvars vs3 (remove_nvars l vs1)
        # subvars vs4 vs2
        # (length vs1 = length vs2 -> length vs3 = length vs4)}}.
Proof.
  induction vs1; simpl; introv.
  - exists ([] : list NVar) ([] : list NVar); simpl; sp.
    rw remove_nvars_nil_r; sp.
  - destruct vs2; simpl.
    + exists (remove_nvars l (a :: vs1)) ([] : list NVar); simpl; sp.
      rw @var_ren_nil_r; auto.
    + boolvar; simpl.
      * pose proof (IHvs1 vs2 l) as k; exrepnd.
        exists vs3 vs4; sp; try (apply subvars_cons_r; auto).
        rw remove_nvars_cons_r; boolvar; sp.
      * pose proof (IHvs1 vs2 l) as k; exrepnd.
        exists (a :: vs3) (n :: vs4); simpl; sp.
        allunfold @var_ren; simpl; rw k0; sp.
        rw remove_nvars_cons_r; boolvar; try (complete sp).
        apply eqvars_cons_lr; auto.
        apply subvars_cons_lr; auto.
Qed.

Lemma swap_vterm {p} :
  forall v s, swap s (vterm v) = @vterm p (swapvar s v).
Proof. sp. Qed.

Lemma sub_find_var_ren_as_option_map {p} :
  forall vs1 vs2 v,
    sub_find (var_ren vs1 vs2) v
    = option_map (@vterm p) (renFind (mk_swapping vs1 vs2) v).
Proof.
  introv.
  rw <- @sub_find_swapping2sub.
  rw @swapping2sub_combine.
  sp.
Qed.

Lemma swapvar_in :
  forall vs1 vs2 v,
    LIn v vs1
    -> !LIn v vs2
    -> length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint vs1 vs2
    -> LIn (swapvar (mk_swapping vs1 vs2) v) vs2.
Proof.
  induction vs1; simpl; introv i1 ni2 len norep disj; auto; try (complete sp).
  destruct vs2; allsimpl; cpx.
  allrw disjoint_cons_l; allrw disjoint_cons_r; repnd; allsimpl.
  allrw not_over_or; repnd.
  allrw no_repeats_cons; repnd.
  unfold oneswapvar; boolvar; try (complete sp).
  rw swapvar_not_in; auto.
Qed.

Lemma renFind_swapbvars_some :
  forall l vs1 vs2 vs v,
    let u := swapvar (mk_swapping vs1 vs2) v in
    LIn v vs1
    -> LIn u vs2
    -> !LIn u l
    -> !LIn u vs1
    -> disjoint vs2 l
    -> disjoint vs2 vs1
    -> no_repeats vs2
    -> renFind (mk_swapping (swapbvars (mk_swapping vs1 vs2) l) vs) u
       = renFind (combine l vs) v.
Proof.
  induction l as [|xl l]; introv i1 i2 ni1 ni2 disj1 disj2 norep; allsimpl; auto;
  try (remember (swapvar (mk_swapping vs1 vs2) v) as u).
  allrw not_over_or; repnd.
  allrw disjoint_cons_r; repnd.
  destruct vs as [|xvs vs]; allsimpl; auto.
  applydup disjoint_sym in disj2 as disj.
  applydup disj in i1.
  boolvar; try (complete sp);
  try (remember (swapvar (mk_swapping vs1 vs2) v) as u).

  - provefalse.
    rw Hequ in e.
    apply swapvars_eq2 in e; auto.

  - rw Hequ; apply IHl; try (complete sp); try (complete (rw <- Hequ; auto)).
Qed.

Lemma eq_option_with_default :
  forall A o1 o2 (e1 e2 : A),
    o1 = o2
    -> e1 = e2
    -> option_with_default o1 e1 = option_with_default o2 e2.
Proof. sp; subst; sp. Qed.

Lemma lsubst_swap_swap_var :
  forall l vs1 vs2 vs v,
    length vs1 = length vs2
    -> length l = length vs
    -> no_repeats vs2
    -> no_repeats vs
    -> disjoint vs l
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs2 l
    -> disjoint vs2 vs1
    -> !LIn v vs
    -> !LIn v vs2
    -> option_with_default
         (renFind (mk_swapping (swapbvars (mk_swapping vs1 vs2) l) vs)
                  (swapvar (mk_swapping vs1 vs2) v))
         (swapvar (mk_swapping vs1 vs2) v)
       = swapvar (mk_swapping vs1 vs2)
                 (option_with_default (renFind (combine l vs) v) v).
Proof.
  introv len1 len2 norep1 norep2;
  introv disj1 disj2 disj3 disj4 disj5 ni1 ni2.
  applydup disjoint_sym in disj5 as disj.

  destruct (in_deq NVar deq_nvar v vs1) as [d|d].

  - remember (swapvar (mk_swapping vs1 vs2) v) as u.
    pose proof (swapvar_in vs1 vs2 v d ni2 len1 norep1 disj) as i.
    rw <- Hequ in i.
    applydup disj4 in i.
    applydup disj5 in i.

    subst; rw renFind_swapbvars_some; auto.
    remember (renFind (combine l vs) v); destruct o; simpl; auto.
    apply renFind_some_in_codom in Heqo.
    applydup disj2 in Heqo.
    applydup disj3 in Heqo.
    rw swapvar_not_in; auto.

  - rewrite apply_to_option_with_default with (f := swapvar (mk_swapping vs1 vs2)).
    rw (swapvar_not_in v); auto.
    apply eq_option_with_default; auto.

    revert_all; induction l;
    introv len1 len2 rep1 rep2;
    introv disj1 disj2 disj3 disj4 disj5 ni1 ni2 disj6 ni3;
    allsimpl; auto.

    destruct vs; allsimpl; auto; cpx.

    allrw disjoint_cons_l; allrw disjoint_cons_r; allsimpl; repnd.
    allrw no_repeats_cons; repnd.
    allrw not_over_or; repnd; GC.

    boolvar; allsimpl; try (complete sp).

    + rw swapvar_not_in; auto.
    + pose proof (swapvar_implies vs1 vs2 a) as h; simpl in h; sp.
    + rw swapvar_not_in in n0; sp.
Qed.

Lemma lsubst_swap_swap_aux {p} :
  forall l vs1 vs2 vs bvs,
    length vs1 = length vs2
    -> length l = length vs
    -> no_repeats vs2
    -> no_repeats vs
    -> disjoint vs2 l
    -> disjoint vs2 vs1
    -> disjoint vs l
    -> disjoint vs vs1
    -> disjoint vs vs2
    -> disjoint vs2 bvs
    -> disjoint vs bvs
    -> {l' : list NVar
        & {vs' : list NVar
           & sub_filter
                (var_ren (swapbvars (mk_swapping vs1 vs2) l) vs)
                (swapbvars (mk_swapping vs1 vs2) bvs)
             = @var_ren p (swapbvars (mk_swapping vs1 vs2) l') vs'
           # sub_filter (var_ren l vs) bvs = @var_ren p l' vs'
           # subvars l' l
           # subvars vs' vs
           # length l' = length vs'
           # (no_repeats vs -> no_repeats vs')}}.
Proof.
  induction l as [|xl l];
  introv len1 len2 norep1 norep2;
  introv disj1 disj2 disj3 disj4 disj5 disj6 disj7;
  allsimpl; destruct vs as [|v vs]; allsimpl; cpx.

  - exists ([] : list NVar) ([] : list NVar); simpl; sp.

  - allrw no_repeats_cons; repnd.
    allrw disjoint_cons_l; allrw disjoint_cons_r; allsimpl; repnd.
    allrw not_over_or; repnd.

    boolvar; allsimpl; try (complete sp).

    + pose proof (IHl vs1 vs2 vs bvs) as h; repeat (autodimp h hyp); exrepnd.
      allrw @fold_var_ren.
      exists l' vs'; sp; apply subvars_cons_r; auto.
    + apply in_swapbvars in Heqb; exrepnd.
      applydup disjoint_sym in disj6 as d.
      applydup d in Heqb2 as i.
      apply swapvars_eq2 in Heqb1; subst; sp.
    + rw in_swapbvars in Heqb.
      destruct Heqb; exists xl; sp.
    + pose proof (IHl vs1 vs2 vs bvs) as h; repeat (autodimp h hyp); exrepnd.
      exists (xl :: l') (v :: vs'); simpl.
      allrw @fold_var_ren; allrw @var_ren_cons.
      rw h0; rw h2; dands; auto; try (apply subvars_cons_lr; auto).
      intro n; allrw no_repeats_cons; repnd; dands; auto.
      intro k; rw subvars_prop in h4; apply h4 in k; auto.
Qed.

Lemma lsubst_swap_swap {p} :
  forall t vs1 vs2 l vs,
    length vs1 = length vs2
    -> length l = length vs
    -> no_repeats vs2
    -> no_repeats vs
    -> disjoint vs (l ++ vs1 ++ vs2 ++ allvars t)
    -> disjoint vs2 (l ++ vs1 ++ allvars t)
    -> lsubst_aux (swap (mk_swapping vs1 vs2) t)
                  (var_ren (swapbvars (mk_swapping vs1 vs2) l) vs)
       = swap (mk_swapping vs1 vs2) (lsubst_aux t (@var_ren p l vs)).
Proof.
  nterm_ind1s t as [v|o lbt Hind] Case;
  introv len1 len2 norep1 norep2 disj1 disj2; auto.

  - Case "vterm".
    rw @swap_vterm.
    allrw @lsubst_aux_vterm.
    rw @sub_find_var_ren_as_option_map.
    rw <- apply_to_option_with_default.
    unfold var_ren; rw <- @swapping2sub_combine.
    rw @sub_find_swapping2sub.
    rw <- apply_to_option_with_default.
    rw @swap_vterm.
    allsimpl; allrw disjoint_app_r; allrw disjoint_singleton_r; repnd.
    rw lsubst_swap_swap_var; auto.

  - Case "oterm".
    simpl.
    apply oterm_eq; auto.
    allrw map_map; unfold compose; simpl.
    apply eq_maps; introv i.
    destruct x as [bvs t]; allsimpl.
    allrw disjoint_app_r; repnd.
    allrw disjoint_flat_map_r.
    applydup disj1 in i as d1.
    applydup disj2 in i as d2; allsimpl.
    allrw disjoint_app_r; repnd.
    apply bterm_eq; auto.

    pose proof (@lsubst_swap_swap_aux p l vs1 vs2 vs bvs) as h;
      repeat (autodimp h hyp); exrepnd.
    rw h0; rw h2.
    eapply Hind; eauto 3 with slow;
    allrw disjoint_app_r; dands; auto; eapply subvars_disjoint_l; eauto;
    eapply subvars_disjoint_r; eauto.
Qed.

Lemma dom_sub_var_ren {p} :
  forall vs1 vs2,
    length vs1 = length vs2
    -> dom_sub (@var_ren p vs1 vs2) = vs1.
Proof.
  induction vs1; introv len; simpl; auto.
  destruct vs2; allsimpl; cpx.
  allrw @fold_var_ren.
  rw IHvs1; sp.
Qed.

Lemma var_ren_is_none {p} :
  forall v vs1 vs2,
    !LIn v vs1
    -> sub_find (@var_ren p vs1 vs2) v = None.
Proof.
  induction vs1; introv i; allsimpl; auto.
  allrw not_over_or; repnd.
  destruct vs2; allsimpl; auto.
  boolvar; sp.
  allrw @fold_var_ren; sp.
Qed.

Lemma option_with_default_none :
  forall T (e : T), option_with_default None e = e.
Proof. sp. Qed.

Lemma eq_sub_filers {p} :
  forall vs1 vs2 l1 l2,
    eqvars (remove_nvars l1 vs1) (remove_nvars l2 vs1)
    -> sub_filter (var_ren vs1 vs2) l1 = sub_filter (@var_ren p vs1 vs2) l2.
Proof.
  induction vs1; introv eqv; allsimpl; auto.
  destruct vs2; allsimpl; auto; boolvar.
  - apply IHvs1.
    revert eqv.
    repeat (rw remove_nvars_cons_r; boolvar; try (complete sp)).
  - rw eqvars_prop in eqv.
    pose proof (eqv a) as k; allrw in_remove_nvars; allsimpl.
    destruct k as [k1 k2].
    autodimp k2 hyp; sp.
  - rw eqvars_prop in eqv.
    pose proof (eqv a) as k; allrw in_remove_nvars; allsimpl.
    destruct k as [k1 k2].
    autodimp k1 hyp; sp.
  - allrw @fold_var_ren.
    pose proof (IHvs1 vs2 l1 l2) as k.
    autodimp k hyp; try (complete (allrw; sp)).
    allrw eqvars_prop; introv.
    pose proof (eqv x) as h.
    allrw in_remove_nvars; allsimpl; split; intro k; repnd; dands; auto;
    destruct h as [h1 h2].
    autodimp h1 hyp; sp.
    autodimp h2 hyp; sp.
Qed.

Lemma lsubst_aux_lsubst_aux_sub_filter_var_ren {p} :
  forall t vs1 vs2 l vs,
    length vs1 = length vs2
    -> length l = length vs
    -> disjoint vs vs1
    -> disjoint vs2 l
    -> lsubst_aux (lsubst_aux t (sub_filter (var_ren vs1 vs2) l))
                  (var_ren l vs)
       = lsubst_aux (lsubst_aux t (var_ren l vs)) (@var_ren p vs1 vs2).
Proof.
  nterm_ind1s t as [v|o lbt Hind] Case;
  introv len1 len2 disj1 disj2; auto.

  - Case "vterm".
    repeat (rw @lsubst_aux_vterm).
    destruct (in_deq NVar deq_nvar v l).
    + rw @sub_find_sub_filter; auto; simpl.
      remember (sub_find (var_ren l vs) v); destruct o; simpl; symmetry in Heqo.
      * applydup @sub_find_varsub in Heqo; exrepnd; subst; allsimpl.
        applydup in_combine in Heqo1; repnd.
        applydup disj1 in Heqo0.
        rw @sub_find_none_if; auto.
        rw @dom_sub_var_ren; auto.
      * apply sub_find_none2 in Heqo; rw @dom_sub_var_ren in Heqo; sp.
    + rw @sub_find_sub_filter_eta; auto.
      rw (@var_ren_is_none p v l); auto.
      rw option_with_default_none; rw @lsubst_aux_vterm.
      remember (sub_find (var_ren vs1 vs2) v); destruct o; simpl; symmetry in Heqo.
      * applydup @sub_find_varsub in Heqo; exrepnd; subst; allsimpl.
        applydup in_combine in Heqo1; repnd.
        applydup disj2 in Heqo0.
        rw @sub_find_none_if; auto.
        rw @dom_sub_var_ren; auto.
      * rw @sub_find_none_if; auto.
        rw @dom_sub_var_ren; auto.

  - Case "oterm".
    simpl.
    repeat (rw map_map); unfold compose; simpl.
    apply oterm_eq; auto.
    apply eq_maps; introv i; destruct x; simpl.
    apply bterm_eq; auto.
    rw @sub_filter_swap.

    pose proof (@sub_filter_var_ren_implies p l vs l0) as h; exrepnd; rw h0.
    pose proof (@sub_filter_var_ren_implies p vs1 vs2 l0) as k; exrepnd; rw k0.

    assert (sub_filter (var_ren vs0 vs5) l = sub_filter (@var_ren p vs0 vs5) vs3) as e.
    (* begin proof of assert *)
    apply eq_sub_filers.
    allrw eqvars_prop; introv.
    pose proof (k2 x) as i1.
    pose proof (h2 x) as i2.
    allrw in_remove_nvars.
    split; intro k; repnd; dands; auto; intro j.
    rw i2 in j; repnd; auto.
    rw i1 in k4; repnd; rw i2 in k; destruct k; sp.
    (* end proof of assert *)

    rw e.
    eapply Hind; eauto 3 with slow.

    apply eqvars_disjoint_r with (s1 := remove_nvars l0 vs1); auto.
    apply eqvars_sym; auto.
    apply subvars_disjoint_l with (l2 := vs); auto.
    apply disjoint_sym; apply disjoint_remove_nvars2.
    apply disjoint_sym; auto.

    apply eqvars_disjoint_r with (s1 := remove_nvars l0 l); auto.
    apply eqvars_sym; auto.
    apply subvars_disjoint_l with (l2 := vs2); auto.
    apply disjoint_sym; apply disjoint_remove_nvars2.
    apply disjoint_sym; auto.
Qed.

Lemma alpha_eq_swap_and_rename {p} :
  forall t vs1 vs2,
    length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint vs1 vs2
    -> disjoint vs2 (@allvars p t)
    -> alpha_eq (swap (mk_swapping vs1 vs2) t)
                (rename_aux t vs1 vs2).
Proof.
  nterm_ind1s t as [v|o lbt Hind] Case;
  introv len norep disj1 disj2; allsimpl; auto.

  - Case "vterm".
    rw @rename_aux_eq.
    rw @lsubst_aux_vterm.
    allrw @sub_find_swapping2sub.
    allrw option_with_default_option_map.
    allrw disjoint_singleton_r.
    rw swapvar_eq; auto; try (apply disjoint_sym; complete auto).

  - Case "oterm".
    allrw disjoint_flat_map_r.
    rw @rename_aux_eq; simpl.
    apply al_oterm; allrw map_length; auto; introv i.
    repeat (rw @selectbt_map; try omega).

    remember (selectbt lbt n) as bt.
    assert (LIn bt lbt) as j by (subst; apply selectbt_in; auto).
    clear dependent n.
    destruct bt as [l u].
    allsimpl.

    applydup disj2 in j; allsimpl.
    allrw disjoint_app_r; repnd.

    pose proof (fresh_vars
                  (length l)
                  (l ++ vs1 ++ vs2 ++ allvars u))
      as vs; destruct vs as [vs vsc]; repnd.

    allrw disjoint_app_r; repnd.
    apply al_bterm with (lv := vs); auto; allrw length_swapbvars; try omega.

    { apply disjoint_app_r; dands; apply disjoint_to_all_vars_r.
      { apply disjoint_allvars_swap; auto. }
      apply disjoint_allvars_lsubst_aux; auto.
      apply disjoint_flat_map_r; introv k.
      apply in_range_iff in k; exrepnd. (* this used to use in_range_t_iff *)
      apply in_sub_filter in k0; repnd.
      apply in_swapping2sub in k1; exrepnd; subst; simpl.
      apply disjoint_singleton_r.
      apply in_mk_swapping_implies in k2; repnd.
      intro x; apply vsc4 in x; sp. }

    change_to_lsubst_aux4;
      try (complete (rw @swapping2sub_mk_swapping_as_var_ren;
                     apply disjoint_sym;
                     pose proof (@sub_filter_var_ren_implies p vs1 vs2 l) as e;
                     exrepnd; rw e0;
                     rw @boundvars_lsubst_aux_vars; auto;
                     apply disjoint_to_all_vars_r in vsc1; rw disjoint_app_r in vsc1; sp;
                     apply disjoint_to_all_vars_r in j0; rw disjoint_app_r in j0; sp;
                     apply subvars_disjoint_l with (l2 := vs2); auto));
      try (complete (rw disjoint_flat_map_r; introv k;
                     rw @in_range_iff in k; exrepnd; (* this used to use in_range_t_iff *)
                     apply in_combine in k0; repnd;
                     apply in_map_iff in k0; exrepnd; subst; simpl;
                     apply disjoint_singleton_r;
                     pose proof (disjoint_allvars_swap u vs vs1 vs2) as k; repeat (autodimp k hyp);
                     apply k in k0;
                     intro x; destruct k0;
                     pose proof (allvars_eq_all_vars (swap (mk_swapping vs1 vs2) u)) as q;
                     rw eqvars_prop in q;
                     apply q; rw in_app_iff; sp)).

    { applydup disjoint_sym in disj1.

      rw @lsubst_swap_swap; auto; try (complete (allrw disjoint_app_r; auto)).

      rw @swapping2sub_mk_swapping_as_var_ren.
      pose proof (lsubst_aux_lsubst_aux_sub_filter_var_ren
                    u vs1 vs2 l vs) as h;
        repeat (autodimp h hyp); rw h.
      eapply Hind; eauto 3 with slow.
      { rw @lsubst_aux_allvars_preserves_size2; eauto 3 with slow. }
      apply disjoint_allvars_lsubst_aux; auto.
      rw disjoint_flat_map_r; introv k.
      rw @range_var_ren in k; auto.
      rw in_map_iff in k; exrepnd; subst; simpl.
      rw disjoint_singleton_r.
      apply vsc4 in k1; auto. }
Qed.


(* end hide *)


(**

  We prove that our two definitions of alpha-equality are equivalent:

 *)

Lemma alphaeq_eq {p} :
  forall t1 t2,
    @alphaeq p t1 t2 <=> alpha_eq t1 t2.
Proof.
  nterm_ind1s t1 as [v|o lbt Hind] Case; introv; auto.

  - Case "vterm".
    split; intro aeq; inversion aeq; subst; constructor.

  - Case "oterm".
    split; intro aeq.

    + inversion aeq as [|? ? ? len aeqbts]; subst.
      constructor; auto.
      introv lt.
      applydup aeqbts in lt as abt; clear aeqbts.
      remember (selectbt lbt n) as bt1.
      remember (selectbt bts2 n) as bt2.
      assert (LIn bt1 lbt)  as i1 by (subst; apply selectbt_in; auto).
      assert (LIn bt2 bts2) as i2 by (subst; apply selectbt_in; omega).
      clear dependent n.
      destruct bt1 as [l1 t].
      destruct bt2 as [l2 u].
      destruct abt as [? ? ? ? ? leq1 leq2 disj norep aeqswap]; subst.
      allsimpl; allrw disjoint_app_r; repnd.

      apply al_bterm with (lv := vs); auto;
      try omega;
      try (complete (rw disjoint_app_r; dands; eapply eqvars_disjoint_r; eauto)).

      generalize (Hind t1 (swap (mk_swapping vs1 vs) t1) vs1 i1);
        intro iff; rw @size_swap in iff; autodimp iff hyp; eauto 3 with slow.
      pose proof (iff (swap (mk_swapping vs2 vs) t2)) as k; clear iff.
      apply k in aeqswap; clear k.
      change_to_lsubst_aux4;
        try (complete (apply disjoint_sym;
                       apply eqvars_disjoint_r with (s2 := all_vars t2) in disj;
                       auto; allunfold @all_vars; allrw disjoint_app_r; sp));
        try (complete (apply disjoint_sym;
                       apply eqvars_disjoint_r with (s2 := all_vars t1) in disj2;
                       auto; allunfold @all_vars; allrw disjoint_app_r; sp)).
      allrw @fold_rename_aux.

      pose proof (alpha_eq_swap_and_rename t1 vs1 vs) as h1.
      repeat (autodimp h1 hyp); try (apply disjoint_sym; complete auto).

      pose proof (alpha_eq_swap_and_rename t2 vs2 vs) as h2.
      repeat (autodimp h2 hyp); try (apply disjoint_sym; complete auto).

      apply alpha_eq_trans with (nt2 := swap (mk_swapping vs1 vs) t1); auto.
      apply alpha_eq_sym; auto.

      apply alpha_eq_trans with (nt2 := swap (mk_swapping vs2 vs) t2); auto.

    + inversion aeq as [|? ? ? len aeqbts]; subst.
      constructor; auto.
      introv lt.
      applydup aeqbts in lt as abt; clear aeqbts.
      remember (selectbt lbt n) as bt1.
      remember (selectbt lbt2 n) as bt2.
      assert (LIn bt1 lbt)  as i1 by (subst; apply selectbt_in; auto).
      assert (LIn bt2 lbt2) as i2 by (subst; apply selectbt_in; omega).
      clear dependent n.
      destruct bt1 as [l1 t].
      destruct bt2 as [l2 u].
      apply alphaeq_bterm3_if with (lva := l1 ++ l2 ) in abt.
      inversion abt as [? ? ? ? ? leq1 leq2 disj norep aeqswap]; subst; clear abt.
      allsimpl; allrw disjoint_app_r; repnd.
      apply alpha_eq_if3 in aeqswap.

      apply aeqbt with (vs := lv); auto; simpl;
      try omega;
      try (complete (allrw disjoint_app_r; dands; auto;
                     apply disjoint_to_allvars_r; rw disjoint_app_r; sp)).

      pose proof (Hind t (swap (mk_swapping l1 lv) t) l1 i1) as iff;
        rw @size_swap in iff; autodimp iff hyp; eauto 3 with slow.
      pose proof (iff (swap (mk_swapping l2 lv) u)) as k; clear iff.
      apply k; clear k.
      revert aeqswap.
      change_to_lsubst_aux4;
        try (complete (apply disjoint_sym;
                       apply eqvars_disjoint_r with (s2 := all_vars t2) in disj;
                       auto; allunfold all_vars; allrw disjoint_app_r; sp));
        try (complete (apply disjoint_sym;
                       apply eqvars_disjoint_r with (s2 := all_vars t1) in disj2;
                       auto; allunfold all_vars; allrw disjoint_app_r; sp)).
      allrw @fold_rename_aux.
      intro a.

      pose proof (alpha_eq_swap_and_rename t l1 lv) as h1.
      repeat (autodimp h1 hyp);
        try (apply disjoint_sym; complete auto);
        try (apply disjoint_to_allvars_r; rw disjoint_app_r; sp).

      pose proof (alpha_eq_swap_and_rename u l2 lv) as h2.
      repeat (autodimp h2 hyp);
        try (apply disjoint_sym; complete auto); try omega;
        try (apply disjoint_to_allvars_r; rw disjoint_app_r; sp).

      apply alpha_eq_trans with (nt2 := rename_aux t l1 lv); auto.

      apply alpha_eq_trans with (nt2 := rename_aux u l2 lv); auto.
      apply alpha_eq_sym; auto.
Qed.

(* begin hide *)

Lemma alphaeq_refl {o} :
  forall (t : @NTerm o), alphaeq t t.
Proof.
  introv; apply alphaeq_eq; auto.
Qed.
Hint Resolve alphaeq_refl : slow.

Lemma alphaeq_trans {o} :
  forall (t1 t2 t3 : @NTerm o),
    alphaeq t1 t2
    -> alphaeq t2 t3
    -> alphaeq t1 t3.
Proof.
  introv aeq1 aeq2.
  allrw @alphaeq_eq.
  eapply alpha_eq_trans; eauto.
Qed.
Hint Resolve alphaeq_trans : slow.

Lemma alphaeq_sym {o} :
  forall (t1 t2 : @NTerm o),
    alphaeq t1 t2
    -> alphaeq t2 t1.
Proof.
  introv aeq.
  allrw @alphaeq_eq.
  eapply alpha_eq_sym; eauto.
Qed.
Hint Resolve alphaeq_sym : slow.

Lemma alphaeqbt_eq {p} :
  forall (bt1 bt2 : @BTerm p),
    alphaeqbt bt1 bt2 <=> alpha_eq_bterm bt1 bt2.
Proof.
  introv.
  pose proof (alphaeq_eq (oterm Exc [bt1]) (oterm Exc [bt2])) as h.
  destruct h as [h1 h2].
  split; intro k.
  - autodimp h1 hyp.
    + constructor; allsimpl; auto; introv i; destruct n; sp; omega.
    + inversion h1; subst; allsimpl.
      assert (0 < 1) as x by auto.
      discover; allunfold @selectbt; allsimpl; auto.
  - autodimp h2 hyp.
    + constructor; allsimpl; auto; introv i; destruct n; sp; omega.
    + inversion h2; subst; allsimpl.
      assert (0 < 1) as x by auto.
      discover; allunfold @selectbt; allsimpl; auto.
Qed.

(*
Lemma alphaeq_vs_dec {o} :
  forall (t1 t2 : @NTerm o) vs,
    assert (no_const t1)
    -> decidable (alphaeq_vs vs t1 t2).
Proof.
  nterm_ind t1 as [|f ind| op lbt ind ] Case; introv nc; simpl; auto.

  - Case "vterm".
    destruct t2.
    + pose proof (deq_nvar n n0) as h; dorn h; subst.
      * left; auto.
      * right; intro k; inversion k; sp.
    + right; intro k; inversion k; sp.

  - destruct t2.
    + right; intro k; inversion k; sp.
    + simpl in nc.
      rw assert_of_andb in nc; repnd.

      pose proof (opid_dec_no_const op o0 nc0) as h; dorn h; subst;
      try (complete (right; intro k; inversion k; sp)).

      pose proof (deq_nat (length lbt) (length l)) as h; dorn h;
      try (complete (right; intro k; inversion k; sp)).

      assert (decidable
                (forall n,
                   n < length lbt
                   -> alphaeqbt_vs vs (selectbt lbt n) (selectbt l n))).

      * revert dependent l.
        induction lbt; introv len; allsimpl; try (complete (left; introv k; omega)).
        destruct l; allsimpl; cpx.
        rw assert_of_andb in nc; repnd.
        autodimp IHlbt hyp; try (complete (introv i n; eapply ind; eauto)).
        autodimp IHlbt hyp.
        pose proof (IHlbt l len) as h1; clear IHlbt.
        destruct a.
        pose proof (ind n l0) as h; autodimp h hyp.
Abort.
*)

Lemma nt_wf_swap_and_free_vars {o} :
  forall (t : @NTerm o) s,
    ((nt_wf t <=> nt_wf (swap s t))
     # (free_vars (swap s t) = swapbvars s (free_vars t))
     # (get_utokens (swap s t) = get_utokens  t)).
Proof.
  nterm_ind1 t as [v|op bts Hind] Case; introv; simpl; auto.

  - Case "vterm".
    dands; auto.
    split; introv wf; tcsp.

  - Case "oterm".

    dands.

    { split; intro wf; inversion wf as [|? ? imp e]; subst.
      + constructor; auto.
        * introv i.
          rw in_map_iff in i; exrepnd; subst.
          applydup imp in i1.
          destruct a.
          inversion i0; subst.
          simpl.
          constructor.
          eapply Hind in i1; eauto.
          apply i1; auto.
        * rw <- e.
          rw map_map; unfold compose.
          apply eq_maps; introv i.
          destruct x; allsimpl.
          unfold num_bvars; simpl.
          rw length_swapbvars; auto.
      + constructor; auto.
        * introv i; destruct l.
          pose proof (imp (bterm (swapbvars s l) (swap s n))) as h.
          autodimp h hyp.
          rw in_map_iff.
          exists (bterm l n); dands; auto.
          inversion h; subst; constructor.
          eapply Hind in i; eauto.
          eapply i; eauto.
        * rw <- e; rw map_map; unfold compose.
          apply eq_maps; introv i; destruct x; simpl.
          unfold num_bvars; simpl.
          rw length_swapbvars; auto.
    }

    { rw @flat_map_map.
      unfold swapbvars.
      rw @map_flat_map.
      unfold compose.
      apply eq_flat_maps; introv i.
      destruct x as [l t]; simpl.
      pose proof (Hind t l i s) as h; repnd.
      rw h1; clear h1.
      fold (swapbvars s (remove_nvars l (free_vars t))).
Abort.

Lemma nt_wf_swap {o} :
  forall (t : @NTerm o) s, nt_wf t <=> nt_wf (swap s t).
Proof.
  nterm_ind1 t as [v|op bts Hind] Case; introv; simpl; auto.

  - Case "vterm".
    split; introv wf; tcsp.

  - Case "oterm".

    { split; intro wf; inversion wf as [| ? ? imp e]; subst.
      + constructor; auto.
        * introv i.
          rw in_map_iff in i; exrepnd; subst.
          applydup imp in i1.
          destruct a.
          inversion i0; subst.
          simpl.
          constructor.
          eapply Hind in i1; eauto.
          apply i1; auto.
        * rw <- e.
          rw map_map; unfold compose.
          apply eq_maps; introv i.
          destruct x; allsimpl.
          unfold num_bvars; simpl.
          rw length_swapbvars; auto.
      + constructor; auto.
        * introv i; destruct l.
          pose proof (imp (bterm (swapbvars s l) (swap s n))) as h.
          autodimp h hyp.
          { rw in_map_iff.
            exists (bterm l n); dands; auto. }
          inversion h; subst; constructor.
          eapply Hind in i; eauto.
          eapply i; eauto.
        * rw <- e; rw map_map; unfold compose.
          apply eq_maps; introv i; destruct x; simpl.
          unfold num_bvars; simpl.
          rw length_swapbvars; auto.
    }
Qed.

Lemma wf_term_swap {o} :
  forall (t : @NTerm o) s,
    wf_term t <=> wf_term (swap s t).
Proof.
  introv.
  repeat (rw @wf_term_eq).
  apply nt_wf_swap.
Qed.

(* end hide *)
