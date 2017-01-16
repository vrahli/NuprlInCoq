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


Require Export sequents_tacs.
Require Export list. (* why? *)



Lemma cover_vars_upto_if_cover_vars_lsubst {o} :
  forall (t : @NTerm o) sub s,
    cover_vars (lsubst t s) sub
    -> cover_vars_upto t (csub_filter sub (dom_sub s)) (dom_sub s).
Proof.
  introv c.

  allrw @cover_vars_eq.
  allunfold @cover_vars_upto.
  allrw subvars_prop.
  introv i.
  rw in_app_iff.
  rw @dom_csub_csub_filter.
  rw in_remove_nvars.
  generalize (in_deq NVar deq_nvar x (dom_sub s)); introv j.
  destruct j as [j | j]; try (complete sp).
  right; dands; auto.
  apply c.
  generalize (eqvars_free_vars_disjoint t s); introv e.
  rw eqvars_prop in e; apply e; clear e.
  rw in_app_iff; rw in_remove_nvars; sp.
Qed.

Lemma substc_lsubstc_type_family_codom {o} :
  forall (a : @NTerm o) x B f t s1 s2 wa wb ws ca cb cs,
    !LIn f (free_vars B)
    -> !LIn f (bound_vars B)
    -> disjoint (remove_nvars [x] (free_vars B)) (dom_csub s2)
    -> disjoint (dom_csub s1) (bound_vars B)
    -> disjoint (dom_csub s2) (bound_vars B)
    -> substc (lsubstc a wa (snoc s1 (f, t) ++ s2) ca) x
              (lsubstc_vars B wb (csub_filter s1 [x]) [x] cb)
       = lsubstc (subst B x a) ws (snoc s1 (f, t) ++ s2) cs.
Proof.
  introv nifb1 nifb2 disj1 disj2 disj3.
  rw @substc_eq_lsubstc.
  apply lsubstc_eq_if_csubst; simpl.
  rw @csubst_app; simpl.
  rw @csubst_swap_app.
  unfold csubst, subst.
  rw @simple_lsubst_lsubst; simpl.
  unfold csubst.
  rw @fold_csubst.
  repeat (rw <- @simple_lsubst_cons).
  remember (subst B x (csubst a (snoc s1 (f, t) ++ s2))).
  rw <- @sub_filter_csub2sub.
  rw @lsubst_sub_filter.
  rw <- @csub2sub_app.
  rw @csub2sub_snoc.
  rw @subset_free_vars_sub_app.
  rw snoc_as_append.
  rw @subset_free_vars_sub_app.
  auto.
  introv.
  rw in_app_iff; simpl; sp; cpx.
  allapply @in_csub2sub; sp.
  subst; unfold subst.
  rw @isprogram_lsubst2; simpl.
  rw disjoint_remove_nvars_l; simpl.
  rw remove_nvars_cons; simpl.
  destruct (eq_var_dec x f); subst; sp.
  rw remove_nvars_nil_l.
  apply disjoint_nil_r.
  rw disjoint_singleton_r; auto.
  sp; cpx.
  apply isprogram_csubst; sp; rw @nt_wf_eq; sp.
  introv.
  rw in_app_iff; simpl; rw in_snoc; sp; cpx.
  allapply @in_csub2sub; sp.
  allapply @in_csub2sub; sp.
  subst; unfold subst.
  rw @isprogram_lsubst2; simpl.
  rw @dom_csub_eq.
  insub.
  sp; cpx.
  apply isprogram_csubst; sp; rw @nt_wf_eq; sp.
  intros.
  allapply @in_csub2sub; sp.
  subst; unfold subst.
  rw @isprogram_lsubst2; simpl.
  rw disjoint_remove_nvars_l; simpl.
  rw remove_nvars_eq; sp.
  sp; cpx.
  apply isprogram_csubst; sp; rw @nt_wf_eq; sp.
  apply isprogram_csubst; sp; rw @nt_wf_eq; sp.
  sp.
  allapply @in_csub2sub; sp.
  apply isprogram_csubst; sp; rw @nt_wf_eq; sp.
  sp.
  allapply @in_csub2sub; sp.
  sp; cpx.
  apply cover_vars_disjoint with (sub := snoc s1 (f, t) ++ s2); sp.
  rw @dom_csub_app; rw @dom_csub_snoc; simpl.
  rw disjoint_app_l; rw disjoint_snoc_l; sp.
  insub.
  insub.
  sp.
  allapply @in_csub2sub; sp.
  simpl.
  rw @dom_csub_csub_filter.
  rw disjoint_remove_nvars_l; simpl.
  rw remove_nvars_eq; sp.
Qed.

Lemma lsubstc2_lsubstc_var {o} :
  forall bp ba (B : @NTerm o) p a wB s cvB vp va w c,
    !LIn vp (bound_vars B)
    -> !LIn va (bound_vars B)
    -> ((!LIn vp [bp,ba]) -> !LIn vp (free_vars B))
    -> ((!LIn va [bp,ba]) -> !LIn va (free_vars B))
    -> !LIn vp (dom_csub s)
    -> !LIn va (dom_csub s)
    -> !(ba = bp)
    -> !(va = vp)
    -> lsubstc2 bp p ba a
                (lsubstc_vars B wB (csub_filter s [bp, ba]) [bp, ba] cvB)
       = lsubstc (lsubst B [(bp, mk_var vp), (ba, mk_var va)]) w
                 (snoc (snoc s (vp, p)) (va, a)) c.
Proof.
  introv disj1 disj2 disj3 disj4 disj5 disj6 disj7 disj8.

  apply cterm_eq; simpl.
  unfold csubst; simpl.

  repeat (rw @simple_lsubst_lsubst; simpl);
    try (complete (sp; cpx; simpl; rw disjoint_singleton_l; sp));
    try (complete (sp; allapply @in_csub2sub; sp; allunfold @isprogram; sp; allrw; sp)).

  rw <- @sub_filter_csub2sub.
  rw <- @sub_filter_lsubst_sub; simpl.

  rw @lsubst_sub_trivial_closed1;
    try (complete (simpl; sp; cpx; allapply @in_csub2sub; sp)).

  generalize (lsubst_shift B
                           (sub_filter (csub2sub s) [bp, ba])
                           [(bp, get_cterm p), (ba, get_cterm a)]
                           []).
  intro eq.

  dest_imp eq hyp.
  simpl; introv i; allrw in_app_iff; allsimpl; sp; cpx;
  allrw @in_sub_filter; sp; allapply @in_csub2sub; sp.

  dest_imp eq hyp.
  simpl; rw <- @dom_sub_sub_filter; unfold disjoint; introv i;
  allrw in_remove_nvars; sp.

  allrw app_nil_r.
  rw eq; clear eq; simpl.

  assert (get_cterm p = lsubst (mk_var vp) (csub2sub (snoc (snoc s (vp, p)) (va, a)))) as eq1.
  (* begin proof of assert *)
  repeat (rw @csub2sub_snoc).
  change_to_lsubst_aux4; simpl; sp.
  repeat (rw @sub_find_snoc).
  boolvar.
  assert (!LIn vp (dom_sub (csub2sub s))) as nivp by (rw @dom_csub_eq; sp).
  rw <- @sub_find_none_iff in nivp; rw nivp; sp.
  assert (!LIn vp (dom_sub (csub2sub s))) as nivp by (rw @dom_csub_eq; sp).
  rw <- @sub_find_none_iff in nivp; rw nivp; sp.
  (* end proof of assert *)

  rw <- eq1; clear eq1.

  assert (get_cterm a = lsubst (mk_var va) (csub2sub (snoc (snoc s (vp, p)) (va, a)))) as eq2.
  (* begin proof of assert *)
  rw @csub2sub_snoc.
  change_to_lsubst_aux4; simpl; sp.
  rw @sub_find_snoc.
  boolvar.
  assert (!LIn va (dom_sub (csub2sub (snoc s (vp, p)))))
         as niva
         by (rw @dom_csub_eq; rw @dom_csub_snoc; simpl; rw in_snoc; sp).
  rw <- @sub_find_none_iff in niva; rw niva; sp.
  (* end proof of assert *)

  rw <- eq2; clear eq2.

  repeat (rw @csub2sub_snoc).

  assert (forall T (l : list T) x y, x :: y :: l = [x,y] ++ l) as eqc by sp.

  symmetry.
  rw eqc.
  rw @lsubst_aux_app_sub_filter; simpl;
    try (complete (allrw @prog_sub_cons; sp; unfold prog_sub, sub_range_sat; simpl; sp));
    try (complete (apply @prog_sub_sub_filter; sp));
    try (complete (repeat (rw @prog_sub_snoc; sp))).

  destruct (eq_var_dec vp bp); sp; subst.
  destruct (eq_var_dec va ba); sp; subst.

  repeat (rw @sub_filter_snoc); boolvar; sp; try (complete (allrw not_over_or; sp)).

  dest_imp disj4 hyp; try (complete (simpl; sp)).
  repeat (rw @sub_filter_snoc); boolvar; sp; allrw not_over_or; sp.

  generalize (lsubst_sub_filter
                B
                ((bp, get_cterm p)
                   :: (ba, get_cterm a)
                   :: snoc (sub_filter (csub2sub s) [bp, ba]) (va, get_cterm a))
                [va]); simpl; boolvar; try (complete sp); intro k.
  dest_imp k hyp.
  introv k; sp; cpx.
  allrw in_snoc; sp; cpx.
  allrw @in_sub_filter; sp.
  allapply @in_csub2sub; sp.
  dest_imp k hyp.
  rw disjoint_singleton_r; sp.
  rw <- k; clear k.

  rw @sub_filter_snoc; boolvar; sp; try (complete (allrw not_over_or; sp)).
  rw <- @sub_filter_app_r; simpl.
  symmetry.

  generalize (lsubst_sub_filter
                B
                ((bp, get_cterm p)
                   :: (ba, get_cterm a)
                   :: sub_filter (csub2sub s) [bp, ba])
                [va]); simpl; boolvar; try (complete sp); intro k.
  dest_imp k hyp.
  introv k; sp; cpx.
  allrw in_snoc; sp; cpx.
  allrw @in_sub_filter; sp.
  allapply @in_csub2sub; sp.
  dest_imp k hyp.
  rw disjoint_singleton_r; sp.
  rw <- k; clear k.

  rw <- @sub_filter_app_r; simpl; sp.

  destruct (eq_var_dec vp ba); sp; subst.
  destruct (eq_var_dec va bp); sp; subst.

  repeat (rw @sub_filter_snoc); boolvar; sp; try (complete (allrw not_over_or; sp)).

  repeat (rw @sub_filter_snoc); boolvar; sp; allrw not_over_or; sp.

  generalize (lsubst_sub_filter
                B
                ((bp, get_cterm p)
                   :: (ba, get_cterm a)
                   :: snoc (sub_filter (csub2sub s) [bp, ba]) (va, get_cterm a))
                [va]); simpl; boolvar; try (complete sp); intro k.
  dest_imp k hyp.
  introv k; sp; cpx.
  allrw in_snoc; sp; cpx.
  allrw @in_sub_filter; sp.
  allapply @in_csub2sub; sp.
  dest_imp k hyp.
  rw disjoint_singleton_r; sp.
  rw <- k; clear k.

  rw @sub_filter_snoc; boolvar; sp; try (complete (allrw not_over_or; sp)).
  rw <- @sub_filter_app_r; simpl.
  symmetry.

  generalize (lsubst_sub_filter
                B
                ((bp, get_cterm p)
                   :: (ba, get_cterm a)
                   :: sub_filter (csub2sub s) [bp, ba])
                [va]); simpl; boolvar; try (complete sp); intro k.
  dest_imp k hyp.
  introv k; sp; cpx.
  allrw in_snoc; sp; cpx.
  allrw @in_sub_filter; sp.
  allapply @in_csub2sub; sp.
  dest_imp k hyp.
  rw disjoint_singleton_r; sp.
  rw <- k; clear k.

  rw <- @sub_filter_app_r; simpl; sp.

  dest_imp disj3 hyp; try (complete (simpl; sp)).

  destruct (eq_var_dec va bp); sp; subst.

  repeat (rw @sub_filter_snoc); boolvar; sp; allrw not_over_or; sp.

  generalize (lsubst_sub_filter
                B
                ((bp, get_cterm p)
                   :: (ba, get_cterm a)
                   :: snoc (sub_filter (csub2sub s) [bp, ba]) (vp, get_cterm p))
                [vp]); simpl; boolvar; try (complete sp); intro k.
  dest_imp k hyp.
  introv k; sp; cpx.
  allrw in_snoc; sp; cpx.
  allrw @in_sub_filter; sp.
  allapply @in_csub2sub; sp.
  dest_imp k hyp.
  rw disjoint_singleton_r; sp.
  rw <- k; clear k.

  rw @sub_filter_snoc; boolvar; sp; try (complete (allrw not_over_or; sp)).
  rw <- @sub_filter_app_r; simpl.
  symmetry.

  generalize (lsubst_sub_filter
                B
                ((bp, get_cterm p)
                   :: (ba, get_cterm a)
                   :: sub_filter (csub2sub s) [bp, ba])
                [vp]); simpl; boolvar; try (complete sp); intro k.
  dest_imp k hyp.
  introv k; sp; cpx.
  allrw in_snoc; sp; cpx.
  allrw @in_sub_filter; sp.
  allapply @in_csub2sub; sp.
  dest_imp k hyp.
  rw disjoint_singleton_r; sp.
  rw <- k; clear k.

  rw <- @sub_filter_app_r; simpl; sp.

  destruct (eq_var_dec va ba); sp; subst.

  repeat (rw @sub_filter_snoc); boolvar; sp; allrw not_over_or; sp.

  generalize (lsubst_sub_filter
                B
                ((bp, get_cterm p)
                   :: (ba, get_cterm a)
                   :: snoc (sub_filter (csub2sub s) [bp, ba]) (vp, get_cterm p))
                [vp]); simpl; boolvar; try (complete sp); intro k.
  dest_imp k hyp.
  introv k; sp; cpx.
  allrw in_snoc; sp; cpx.
  allrw @in_sub_filter; sp.
  allapply @in_csub2sub; sp.
  dest_imp k hyp.
  rw disjoint_singleton_r; sp.
  rw <- k; clear k.

  rw @sub_filter_snoc; boolvar; sp; try (complete (allrw not_over_or; sp)).
  rw <- @sub_filter_app_r; simpl.
  symmetry.

  generalize (lsubst_sub_filter
                B
                ((bp, get_cterm p)
                   :: (ba, get_cterm a)
                   :: sub_filter (csub2sub s) [bp, ba])
                [vp]); simpl; boolvar; try (complete sp); intro k.
  dest_imp k hyp.
  introv k; sp; cpx.
  allrw in_snoc; sp; cpx.
  allrw @in_sub_filter; sp.
  allapply @in_csub2sub; sp.
  dest_imp k hyp.
  rw disjoint_singleton_r; sp.
  rw <- k; clear k.

  rw <- @sub_filter_app_r; simpl; sp.

  dest_imp disj4 hyp; try (complete (simpl; sp)).

  repeat (rw @sub_filter_snoc); boolvar; sp; allrw not_over_or; sp.

  generalize (lsubst_sub_filter
                B
                ((bp, get_cterm p)
                   :: (ba, get_cterm a)
                   :: snoc (snoc (sub_filter (csub2sub s) [bp, ba]) (vp, get_cterm p)) (va, get_cterm a))
                [vp,va]); simpl; boolvar; try (complete sp); intro k.
  dest_imp k hyp.
  introv k; sp; cpx.
  allrw in_snoc; sp; cpx.
  allrw @in_sub_filter; sp.
  allapply @in_csub2sub; sp.
  dest_imp k hyp.
  rw disjoint_cons_r; rw disjoint_singleton_r; sp.
  rw <- k; clear k.

  repeat (rw @sub_filter_snoc); boolvar; sp; try (complete (allrw not_over_or; sp)).
  rw <- @sub_filter_app_r; simpl.
  symmetry.

  generalize (lsubst_sub_filter
                B
                ((bp, get_cterm p)
                   :: (ba, get_cterm a)
                   :: sub_filter (csub2sub s) [bp, ba])
                [vp,va]); simpl; boolvar; try (complete sp); intro k.
  dest_imp k hyp.
  introv k; sp; cpx.
  allrw in_snoc; sp; cpx.
  allrw @in_sub_filter; sp.
  allapply @in_csub2sub; sp.
  dest_imp k hyp.
  rw disjoint_cons_r; rw disjoint_singleton_r; sp.
  rw <- k; clear k.

  rw <- @sub_filter_app_r; simpl; sp.
Qed.

Lemma simple_lsubst_app2 {o} :
  forall (t : @NTerm o) sub1 sub2,
    (forall v u, LIn (v, u) sub1 -> disjoint (free_vars u) (bound_vars t))
    -> (forall v u, LIn (v, u) sub2 -> isprogram u)
    -> (forall v,
          LIn v (dom_sub sub2)
          -> !LIn v (dom_sub sub1)
          -> !LIn v (free_vars t))
    -> lsubst t (sub1 ++ sub2) = lsubst t sub1.
Proof.
  introv hyp1 hyp2 hyp3.
  change_to_lsubst_aux4;
    try (complete (rw @range_app; rw flat_map_app;
                   rw disjoint_app_r; sp;
                   rw @prog_sub_flatmap_range; sp)).

  revert_dependents sub2.
  revert_dependents sub1.
  nterm_ind t as [| | oo lbt ind] Case; allsimpl;
  introv disj1 disj2 hyp1 hyp2 disj3; auto.

  - Case "vterm".
    rw @sub_find_app.
    cases (sub_find sub1 n); sp.
    rename_last sn1.
    cases (sub_find sub2 n); sp.
    rename_last sn2.
    apply sub_find_none2 in sn1.
    apply sub_find_some in sn2.
    apply in_dom_sub in sn2.
    generalize (hyp2 n); sp.
    allrw not_over_or; sp.

  - Case "oterm".
    apply oterm_eq; sp.
    apply eq_maps; introv i.
    destruct x; simpl.
    apply bterm_eq; sp.
    rw @sub_filter_app.
    apply ind with (lv := l); try (complete sp).

    + rw disjoint_flat_map_l in disj3.
      generalize (disj3 (bterm l n)); intro k; dest_imp k hyp.
      simpl in k.
      rw disjoint_app_l in k; repnd.
      unfold disjoint in k.
      unfold disjoint; introv j.
      apply k in j; intro x.
      allrw lin_flat_map; exrepnd.
      apply j; exists x0; sp.
      allrw @in_range_iff; exrepnd.
      allrw @in_sub_filter; repnd.
      exists v.
      rw in_app_iff; sp.

    + rw disjoint_flat_map_l in disj3.
      generalize (disj3 (bterm l n)); intro k; dest_imp k hyp.
      simpl in k.
      rw disjoint_app_l in k; repnd.
      unfold disjoint in k.
      unfold disjoint; introv j.
      apply k in j; intro x.
      allrw lin_flat_map; exrepnd.
      apply j; exists x0; sp.
      allrw @in_range_iff; exrepnd.
      allrw @in_sub_filter; repnd.
      exists v.
      rw in_app_iff; sp.

    + introv j.
      apply in_sub_filter in j; repnd.
      generalize (hyp1 v u); sp.

    + introv j k.
      rw <- @dom_sub_sub_filter in j.
      rw in_remove_nvars in j; repnd.
      rw <- @dom_sub_sub_filter in k.
      rw in_remove_nvars in k.
      generalize (hyp2 v); intro imp.
      intro x.
      repeat (dest_imp imp hyp).
      apply imp.
      rw lin_flat_map.
      exists (bterm l n); simpl; sp.
      rw in_remove_nvars; sp.

    + rw disjoint_flat_map_l in disj3.
      generalize (disj3 (bterm l n)); intro k; dest_imp k hyp.
      simpl in k.
      rw disjoint_app_l in k; repnd.
      unfold disjoint in k.
      unfold disjoint; introv j.
      apply k in j; intro x.
      allrw lin_flat_map; exrepnd.
      apply j; exists x0; sp.
      allrw @in_range_iff; exrepnd.
      allrw in_app_iff.
      allrw @in_sub_filter.
      exists v.
      rw in_app_iff; sp.
Qed.

Lemma lsubstc3_lsubstc_var1 {o} :
  forall cp ca cb (C : @NTerm o) p a b wC s cvC vp va w c,
    !LIn vp (bound_vars C)
    -> !LIn va (bound_vars C)
    -> ((!LIn vp [cp,ca,cb]) -> !LIn vp (free_vars C))
    -> ((!LIn va [cp,ca,cb]) -> !LIn va (free_vars C))
    -> !LIn vp (dom_csub s)
    -> !LIn va (dom_csub s)
    -> !(va = vp)
    -> lsubstc3 cp p ca a cb b
                (lsubstc_vars C wC (csub_filter s [cp, ca, cb]) [cp, ca, cb] cvC)
       = lsubstc (lsubst C [(cp, mk_var vp), (ca, mk_var va), (cb, get_cterm b)]) w
                 (snoc (snoc s (vp, p)) (va, a)) c.
Proof.
  introv h1 h2 h3 h4 h5 h6 h7.

  apply cterm_eq; simpl.
  unfold csubst; simpl.

  repeat (rw @simple_lsubst_lsubst; simpl);
    try (complete (sp; allapply @in_csub2sub; sp; allunfold @isprogram; sp; allrw; sp));
    try (complete (sp; cpx; simpl; try (rw disjoint_singleton_l; sp); rw @free_vars_cterm; sp)).

  rw <- @sub_filter_csub2sub.
  rw <- @sub_filter_lsubst_sub; simpl.

  rw @lsubst_sub_trivial_closed1;
    try (complete (simpl; sp; cpx; allapply @in_csub2sub; sp)).

  generalize (lsubst_shift C
                           (sub_filter (csub2sub s) [cp, ca, cb])
                           [(cp, get_cterm p), (ca, get_cterm a), (cb, get_cterm b)]
                           []).
  intro eq.

  dest_imp eq hyp.
  simpl; introv i; allrw in_app_iff; allsimpl; sp; cpx;
  allrw @in_sub_filter; sp; allapply @in_csub2sub; sp.

  dest_imp eq hyp.
  simpl; rw <- @dom_sub_sub_filter; unfold disjoint; introv i;
  allrw in_remove_nvars; sp.

  allrw app_nil_r.
  rw eq; clear eq; simpl.

  assert (get_cterm p
          = lsubst (mk_var vp) (csub2sub (snoc (snoc s (vp, p)) (va, a))))
         as eq1.
  (* begin proof of assert *)
  repeat (rw @csub2sub_snoc).
  change_to_lsubst_aux4; simpl; sp.
  repeat (rw @sub_find_snoc).
  boolvar.
  assert (!LIn vp (dom_sub (csub2sub s))) as nivp by (rw @dom_csub_eq; sp).
  rw <- @sub_find_none_iff in nivp; rw nivp; sp.
  assert (!LIn vp (dom_sub (csub2sub s))) as nivp by (rw @dom_csub_eq; sp).
  rw <- @sub_find_none_iff in nivp; rw nivp; sp.
  (* end proof of assert *)

  rw <- eq1; clear eq1.

  assert (get_cterm a
          = lsubst (mk_var va) (csub2sub (snoc (snoc s (vp, p)) (va, a))))
         as eq2.
  (* begin proof of assert *)
  rw @csub2sub_snoc.
  change_to_lsubst_aux4; simpl; sp.
  rw @sub_find_snoc.
  boolvar.
  assert (!LIn va (dom_sub (csub2sub (snoc s (vp, p)))))
         as niva
         by (rw @dom_csub_eq; rw @dom_csub_snoc; simpl; rw in_snoc; sp).
  rw <- @sub_find_none_iff in niva; rw niva; sp.
  (* end proof of assert *)

  rw <- eq2; clear eq2.

  rw @lsubst_cterm.
  repeat (rw @csub2sub_snoc).

  assert (forall T (l : list T) x y z, x :: y :: z :: l = [x,y,z] ++ l) as eqc by sp.

  rw eqc.
  rw <- @lsubst_aux_app_sub_filter;
    try (complete (sp; unfold prog_sub, sub_range_sat; simpl; sp; cpx)).
  rw <- @simple_lsubst_app; try (complete (simpl; sp; allapply @in_csub2sub; cpx)).

  symmetry.
  rw eqc.
  rw <- @simple_lsubst_app;
    try (complete (simpl; sp; allrw in_snoc; sp; allapply @in_csub2sub; cpx)).

  generalize (lsubst_sub_filter
                (lsubst C [(cp, get_cterm p), (ca, get_cterm a), (cb, get_cterm b)])
                (snoc (snoc (csub2sub s) (vp, get_cterm p)) (va, get_cterm a))
                [vp, va]); intro eq.
  dest_imp eq hyp;
    try (complete (intros; allrw in_snoc; sp; cpx; allapply @in_csub2sub; sp)).
  dest_imp eq hyp.
  generalize (eqvars_free_vars_disjoint C [(cp, get_cterm p), (ca, get_cterm a), (cb, get_cterm b)]);
    introv eqv.
  apply eqvars_sym in eqv.
  apply eqvars_disjoint with (s3 := [vp,va]) in eqv; sp.
  simpl; boolvar; simpl; repeat (rw @free_vars_cterm); simpl; allrw app_nil_r;
  apply disjoint_sym; unfold disjoint; intros v i k; simpl in i; repdors; subst;
  try (destruct (eq_var_dec vp v)); try (destruct (eq_var_dec va v)); try (complete sp);
  allrw in_remove_nvars; repnd; allrw in_single_iff; try (complete sp).

  rw <- eq.
  repeat (rw @sub_filter_snoc); boolvar; subst; sp; try (complete (allrw not_over_or; sp)).
  GC; clear eq.

  apply lsubst_sub_filter;
    try (complete (intros; allrw in_snoc; sp; cpx; allapply @in_csub2sub; sp)).

  generalize (eqvars_free_vars_disjoint C [(cp, get_cterm p), (ca, get_cterm a), (cb, get_cterm b)]);
    introv eqv.
  apply eqvars_sym in eqv.
  apply eqvars_disjoint with (s3 := [vp,va]) in eqv; sp.
  simpl; boolvar; simpl; repeat (rw @free_vars_cterm); simpl; allrw app_nil_r;
  apply disjoint_sym; unfold disjoint; intros v i k; simpl in i; repdors; subst;
  try (destruct (eq_var_dec vp v)); try (destruct (eq_var_dec va v)); try (complete sp);
  allrw in_remove_nvars; repnd; allrw in_single_iff; try (complete sp).
Qed.

Lemma csubst_subst_pw_Q {o} :
  forall (Q : @NTerm o) w f b t,
    !LIn b (bound_vars Q)
    -> !LIn f (bound_vars Q)
    -> !b = f
    -> !b = w
    -> !LIn b (free_vars Q)
    -> csubst (subst Q w (mk_apply (mk_var f) (mk_var b))) [(b, t)]
       = subst Q w (mk_apply (mk_var f) (get_cterm t)).
Proof.
  introv bc1 bc2 bc3 bc4 bc5.
  generalize (simple_lsubst_lsubst
                Q [(w, mk_apply (mk_var f) (mk_var b))] [(b, get_cterm t)]);
    introv eq.
  repeat (dest_imp eq hyp);
    try (complete (simpl; introv k; sp; cpx; simpl; repeat (rw disjoint_cons_l); sp)).

  unfold subst, csubst; simpl.
  rw eq; clear eq; simpl.

  rw @fold_csubst1.
  rw @csubst_mk_apply; simpl.
  rw (@csubst_var_not_in o f); simpl; sp.
  rw @csubst_mk_var_in.
  generalize (lsubst_sub_filter2
                Q [(w, mk_apply (mk_var f) (get_cterm t)), (b, get_cterm t)] [b]);
    intro e.
  repeat (dest_imp e hyp);
    try (complete (rw disjoint_singleton_r; sp));
    try (complete (unfold disjoint_bv_sub, sub_range_sat; simpl; sp; cpx; simpl;
                   allrw @free_vars_cterm; simpl;
                   try (rw disjoint_singleton_l); try (rw disjoint_singleton_r); sp)).
  simpl in e.
  rw <- e; clear e.

  boolvar; sp; allrw not_over_or; sp.
Qed.

Lemma lsubstc_snoc_snoc {o} :
  forall (t : @NTerm o) s v1 v2 t1 t2 w c,
    !LIn v1 (free_vars t)
    -> {c' : cover_vars t (snoc s (v2, t2))
        , lsubstc t w (snoc (snoc s (v1, t1)) (v2, t2)) c
          = lsubstc t w (snoc s (v2, t2)) c'}.
Proof.
  introv ni.
  assert (cover_vars t (snoc s (v2, t2)))
         as c'
         by (allrw @cover_vars_eq;
             allrw subvars_prop; introv i;
             applydup c in i as j; splst in j; splst; sp; subst; sp).
  exists c'.
  revert c.
  rw snoc_as_append; introv.
  generalize (lsubstc_csubst_ex2 t (snoc s (v1, t1)) [(v2, t2)] w c); intro eq; exrepnd.
  rw <- eq1; clear eq1.
  revert w' p'.
  lsubst_tac; introv.
  assert (cover_vars t (s ++ [(v2, t2)])) as c'' by (rw <- snoc_as_append; sp).
  generalize (lsubstc_csubst_ex2 t s [(v2, t2)] w c''); intro eq; exrepnd; proof_irr.
  rw eq1; clear eq1.
  revert c''.
  rw <- snoc_as_append; introv; proof_irr; sp.
Qed.
