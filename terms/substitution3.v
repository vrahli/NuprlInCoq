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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export substitution2.
Require Export sovar_alpha.


(* !! MOVE everything about cl_sub to some substitution file *)
Definition cl_sub {p} (sub : @Substitution p) := sub_range_sat sub closed.

Lemma implies_cl_sub_filter {o} :
  forall (sub : @Sub o) l,
    cl_sub sub -> cl_sub (sub_filter sub l).
Proof.
  introv cl.
  allunfold @cl_sub.
  allunfold @sub_range_sat.
  introv i.
  apply in_sub_filter in i; repnd.
  apply cl in i0; sp.
Qed.
Hint Resolve implies_cl_sub_filter : slow.

Lemma lsubst_aux_trivial_cl {p} :
  forall (t : @NTerm p) sub,
    cl_sub sub
    -> disjoint (dom_sub sub) (free_vars t)
    -> lsubst_aux t sub = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; introv cl disj; auto.

  - Case "vterm".
    allrw disjoint_singleton_r.
    remember (sub_find sub v) as f; symmetry in Heqf; destruct f; auto.
    apply sub_find_some in Heqf.
    apply in_dom_sub in Heqf; sp.

  - Case "oterm".
    f_equal.
    apply eq_map_l; introv i.
    destruct x; simpl.
    f_equal.
    eapply ind; eauto.

    + apply implies_cl_sub_filter; auto.

    + rw <- @dom_sub_sub_filter.
      rw disjoint_flat_map_r in disj.
      apply disj in i; simpl in i.
      rw disjoint_remove_nvars_l; auto.
Qed.

Lemma lsubst_aux_trivial_cl2 {p} :
  forall (t : @NTerm p) sub,
    cl_sub sub
    -> closed t
    -> lsubst_aux t sub = t.
Proof.
  introv clsub clt.
  apply lsubst_aux_trivial_cl; auto.
  rw clt; auto.
Qed.

Lemma cl_sub_nil {o} : @cl_sub o [].
Proof.
  unfold cl_sub, sub_range_sat; allsimpl; sp.
Qed.
Hint Resolve cl_sub_nil : slow.

Lemma cl_sub_cons {o} :
  forall v (t : @NTerm o) sub,
    cl_sub ((v,t) :: sub) <=> (closed t # cl_sub sub).
Proof.
  unfold cl_sub, sub_range_sat; introv; split; intro k; repnd; dands; introv.
  - apply (k v); simpl; sp.
  - intro i; apply (k v0); simpl; sp.
  - intro i; simpl in i; dorn i; cpx.
    apply (k v0); auto.
Qed.

Lemma implies_cl_sub_cons {o} :
  forall v (t : @NTerm o) sub,
    closed t
    -> cl_sub sub
    -> cl_sub ((v,t) :: sub).
Proof.
  introv clt cls.
  rw @cl_sub_cons; sp.
Qed.
Hint Resolve implies_cl_sub_cons : slow.

Lemma cl_sub_eq {p} :
  forall (sub : @Sub p),
    cl_sub sub <=> (forall t, LIn t (range sub) -> closed t).
Proof.
  induction sub; simpl; split; intro k; tcsp.

  - apply cl_sub_nil.

  - destruct a; apply cl_sub_cons in k; repnd.
    introv i; dorn i; subst; auto.
    rw IHsub in k; apply k in i; auto.

  - destruct a; apply cl_sub_cons; dands; auto.
    apply IHsub; introv i.
    apply k; sp.
Qed.

Lemma cl_sub_eq2 {p} :
  forall (sub : @Sub p),
    cl_sub sub <=> (forall v t, LIn (v,t) sub -> closed t).
Proof.
  induction sub; simpl; split; intro k; tcsp.
Qed.

Lemma cl_sub_csub2sub {o} :
  forall (s : @CSub o), cl_sub (csub2sub s).
Proof.
  induction s; simpl; eauto with slow.
Qed.
Hint Resolve cl_sub_csub2sub : slow.

Lemma free_vars_lsubst_aux_cl {p} :
  forall (t : @NTerm p) sub,
    cl_sub sub
    -> free_vars (lsubst_aux t sub) = remove_nvars (dom_sub sub) (free_vars t).
Proof.
  nterm_ind t as [v|op lbt ind] Case; simpl; introv k; auto.

  - Case "vterm".
    remember (sub_find sub v) as f; destruct f; symmetry in Heqf; simpl.
    + apply sub_find_some in Heqf.
      rw @cl_sub_eq in k.
      assert (LIn n (range sub)) as i by (apply in_range_iff; eexists; eauto).
      apply k in i; rw i.
      symmetry.
      rw <- null_iff_nil.
      rw null_remove_nvars; simpl; sp; subst.
      apply in_dom_sub in Heqf; sp.
    + apply sub_find_none2 in Heqf.
      symmetry.
      rw <- remove_nvars_unchanged.
      unfold disjoint; simpl; sp; subst; auto.

  - Case "oterm".
    rw flat_map_map; unfold compose.
    rw remove_nvars_flat_map; unfold compose.
    apply eq_flat_maps; introv i.
    destruct x; simpl.

    rw remove_nvars_comm.

    apply ind with (sub := sub_filter sub l) in i; sp;
    [|apply implies_cl_sub_filter; auto].
    rw i; clear i.
    repeat (rw remove_nvars_app_l).
    apply remove_nvars_comb.
Qed.

Lemma cl_sub_implies_disjoint_bv_sub {o} :
  forall (sub : @Sub o) t,
    cl_sub sub -> disjoint_bv_sub t sub.
Proof.
  introv cl.
  unfold cl_sub in cl.
  unfold disjoint_bv_sub.
  allunfold @sub_range_sat.
  introv i.
  apply cl in i; rw i; auto.
Qed.

Lemma sub_free_vars_if_cl_sub {o} :
  forall (sub : @Sub o),
    cl_sub sub -> sub_free_vars sub = [].
Proof.
  induction sub; introv cl; allsimpl; auto.
  destruct a; allrw @cl_sub_cons; repnd.
  rw IHsub; auto.
  rw cl0; auto.
Qed.

Lemma sub_free_vars_iff_cl_sub {o} :
  forall (sub : @Sub o),
    cl_sub sub <=> sub_free_vars sub = [].
Proof.
  induction sub; split; introv cl; allsimpl; auto.
  - apply cl_sub_nil.
  - destruct a; allrw @cl_sub_cons; repnd.
    apply IHsub in cl; rw cl; rw cl0; auto.
  - destruct a; allrw @cl_sub_cons.
    apply app_eq_nil_iff in cl; repnd.
    apply IHsub in cl; dands; auto.
Qed.

Lemma lsubst_oterm_cl_sub {o} :
  forall op bs (sub : @Sub o),
    cl_sub sub
    -> lsubst (oterm op bs) sub
       = oterm op (map (fun b => lsubst_bterm_aux b sub) bs).
Proof.
  introv cl.
  unfold lsubst.
  rw <- @sub_free_vars_is_flat_map_free_vars_range.
  rw @sub_free_vars_if_cl_sub; auto; boolvar; tcsp.
  provefalse; sp.
Qed.

Definition subst_bterm_aux {p} (b : @BTerm p) (v : NVar) (u : NTerm) : BTerm :=
  lsubst_bterm_aux b [(v,u)].

Lemma subst_oterm_cl_sub {o} :
  forall op bs v (t : @NTerm o),
    closed t
    -> subst (oterm op bs) v t
       = oterm op (map (fun b => subst_bterm_aux b v t) bs).
Proof.
  introv cl.
  unfold subst.
  rw @lsubst_oterm_cl_sub; eauto with slow.
Qed.

Lemma subst_aux_oterm {o} :
  forall op bs v (t : @NTerm o),
    subst_aux (oterm op bs) v t
    = oterm op (map (fun b => subst_bterm_aux b v t) bs).
Proof. sp. Qed.

Lemma sub_free_vars_app {o} :
  forall (s1 s2 : @Sub o),
    sub_free_vars (s1 ++ s2) = sub_free_vars s1 ++ sub_free_vars s2.
Proof.
  induction s1; introv; allsimpl; auto.
  destruct a; rw IHs1.
  rw app_assoc; auto.
Qed.

Lemma implies_cl_sub_app {o} :
  forall (s1 s2 : @Sub o),
    cl_sub s1
    -> cl_sub s2
    -> cl_sub (s1 ++ s2).
Proof.
  introv cl1 cl2.
  allrw @sub_free_vars_iff_cl_sub.
  rw @sub_free_vars_app.
  allrw; auto.
Qed.
Hint Resolve implies_cl_sub_app : slow.

Lemma cl_lsubst_aux_app_sub_filter {o} :
  forall (t : @NTerm o) s1 s2,
    lsubst_aux t (s1 ++ s2)
    = lsubst_aux t (s1 ++ sub_filter s2 (dom_sub s1)).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv; simpl; auto.

  - Case "vterm".
    allrw @sub_find_app.
    remember (sub_find s1 v) as sf1; symmetry in Heqsf1; destruct sf1; auto.
    rw @sub_find_sub_filter_eta; auto.
    apply sub_find_none_iff; auto.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl.
    allrw @sub_filter_app.
    rewrite (ind t l); eauto with slow.
    f_equal.
    rw <- @dom_sub_sub_filter.
    allrw <- @sub_filter_app_r.
    f_equal; f_equal.
    rw <- @sub_filter_app_as_remove_nvars.
    allrw @sub_filter_app_r.
    rw @sub_filter_swap; auto.
Qed.

Lemma cl_lsubst_app_sub_filter {o} :
  forall (t : @NTerm o) s1 s2,
    cl_sub s2
    -> lsubst t (s1 ++ s2)
       = lsubst t (s1 ++ sub_filter s2 (dom_sub s1)).
Proof.
  introv cl2.
  unfold lsubst.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @sub_free_vars_app.
  allrw (sub_free_vars_if_cl_sub s2); eauto with slow.
  allrw (sub_free_vars_if_cl_sub (sub_filter s2 (dom_sub s1))); eauto with slow.
  allrw app_nil_r.

  boolvar; tcsp; eauto with slow;
  try (complete (provefalse; sp));
  apply cl_lsubst_aux_app_sub_filter; auto.
Qed.

Lemma cl_lsubst_aux_app {o} :
  forall (t : @NTerm o) s1 s2,
    cl_sub s1
    -> cl_sub s2
    -> lsubst_aux t (s1 ++ s2)
       = lsubst_aux (lsubst_aux t s1) s2.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv cl1 cl2; simpl; auto.

  - Case "vterm".
    allrw @sub_find_app.
    remember (sub_find s1 v) as sf1; symmetry in Heqsf1; destruct sf1; auto.
    apply sub_find_some in Heqsf1.
    rw @lsubst_aux_trivial_cl2; auto.
    rw @cl_sub_eq2 in cl1.
    apply cl1 in Heqsf1; auto.

  - Case "oterm".
    f_equal.
    rw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl.
    allrw @sub_filter_app.
    rewrite (ind t l); eauto with slow.
Qed.

Lemma cl_lsubst_app {o} :
  forall (t : @NTerm o) s1 s2,
    cl_sub s1
    -> cl_sub s2
    -> lsubst t (s1 ++ s2)
       = lsubst (lsubst t s1) s2.
Proof.
  introv cl1 cl2.
  unfold lsubst.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @sub_free_vars_if_cl_sub; auto; boolvar; tcsp; eauto with slow;
  try (complete (provefalse; sp)).
  apply cl_lsubst_aux_app; auto.
Qed.

Lemma cl_lsubst_aux_swap {o} :
  forall (t : @NTerm o) s1 s2,
    cl_sub s1
    -> cl_sub s2
    -> disjoint (dom_sub s1) (dom_sub s2)
    -> lsubst_aux (lsubst_aux t s1) s2
       = lsubst_aux (lsubst_aux t s2) s1.
Proof.
  nterm_ind t as [v|op bs ind] Case; introv cl1 cl2 disj; simpl; auto.

  - Case "vterm".
    remember (sub_find s1 v) as sf1; symmetry in Heqsf1; destruct sf1; auto;
    remember (sub_find s2 v) as sf2; symmetry in Heqsf2; destruct sf2; auto;
    simpl; allrw; allapply @sub_find_some; auto.
    + allapply @in_dom_sub.
      apply disj in Heqsf1; sp.
    + rw @lsubst_aux_trivial_cl2; auto.
      rw @cl_sub_eq2 in cl1.
      apply cl1 in Heqsf1; auto.
    + rw @lsubst_aux_trivial_cl2; auto.
      rw @cl_sub_eq2 in cl2.
      apply cl2 in Heqsf2; auto.

  - Case "oterm".
    f_equal.
    allrw map_map; unfold compose.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl.
    rewrite (ind t l); eauto with slow.
    allrw <- @dom_sub_sub_filter.
    apply disjoint_remove_nvars2; apply disjoint_sym.
    apply disjoint_remove_nvars2; apply disjoint_sym; auto.
Qed.

Lemma cl_lsubst_swap {o} :
  forall (t : @NTerm o) s1 s2,
    cl_sub s1
    -> cl_sub s2
    -> disjoint (dom_sub s1) (dom_sub s2)
    -> lsubst (lsubst t s1) s2
       = lsubst (lsubst t s2) s1.
Proof.
  introv cl1 cl2 disj.
  unfold lsubst.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  allrw @sub_free_vars_if_cl_sub; auto; boolvar; tcsp; eauto with slow;
  try (complete (provefalse; sp)).
  apply cl_lsubst_aux_swap; auto.
Qed.

Lemma cl_lsubst_lsubst_aux {o} :
  forall (t : @NTerm o) sub,
    cl_sub sub -> lsubst t sub = lsubst_aux t sub.
Proof.
  introv cl.
  apply lsubst_lsubst_aux.
  rw <- @sub_free_vars_is_flat_map_free_vars_range.
  rw @sub_free_vars_if_cl_sub; auto.
Qed.

Lemma cl_subst_subst_aux {o} :
  forall (t : @NTerm o) v u,
    closed u -> subst t v u = subst_aux t v u.
Proof.
  introv cl.
  unfold subst, subst_aux.
  apply cl_lsubst_lsubst_aux; eauto with slow.
Qed.

Lemma lsubst_aux_trivial_cl_term {p} :
  forall (t : @NTerm p) sub,
    disjoint (free_vars t) (dom_sub sub)
    -> lsubst_aux t sub = t.
Proof.
  nterm_ind t as [v|op bs ind] Case; simpl; introv cl; auto.

  - Case "vterm".
    allrw disjoint_singleton_l.
    apply sub_find_none_iff in cl; rw cl; auto.

  - Case "oterm".
    f_equal.
    apply eq_map_l; introv i.
    destruct x; simpl.
    f_equal.
    eapply ind; eauto.
    rw <- @dom_sub_sub_filter.
    rw disjoint_flat_map_l in cl.
    apply cl in i; simpl in i.
    apply disjoint_remove_nvars_l in i; auto.
Qed.

Lemma lsubst_aux_trivial_cl_term2 {p} :
  forall (t : @NTerm p) sub,
    closed t
    -> lsubst_aux t sub = t.
Proof.
  introv cl; apply lsubst_aux_trivial_cl_term.
  rw cl; auto.
Qed.

Lemma cover_vars_iff_closed_lsubst_aux {o} :
  forall (t : @NTerm o) s,
    cover_vars t s <=> closed (lsubst_aux t (csub2sub s)).
Proof.
  introv; rw @cover_vars_iff_closed_lsubstc.
  unfold csubst.
  pose proof (unfold_lsubst (csub2sub s) t) as h; exrepnd.
  rw h0.
  unfold closed.
  repeat (rw @free_vars_lsubst_aux_cl; eauto with slow).
  apply alphaeq_preserves_free_vars in h1.
  rw h1; tcsp.
Qed.
