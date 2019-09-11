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


Require Export csubst.


Lemma lsubstc_app_cover1 {o} :
  forall (t : @NTerm o) sub1 sub2 p c (c' : cover_vars t sub1),
    lsubstc t p (sub1 ++ sub2) c
    = lsubstc t p sub1 c'.
Proof.
  introv.
  apply cterm_eq; simpl.
  unfold csubst.
  rw <- @csub2sub_app.
  rw <- @simple_lsubst_app.
  - rw @lsubst_trivial; auto.
    introv i.
    applydup @in_csub2sub in i; dands; auto.
    introv k.
    pose proof (eqvars_free_vars_disjoint t (csub2sub sub1)) as h.
    eapply eqvars_prop in h; apply h in k; clear h.
    rw in_app_iff in k; rw in_remove_nvars in k.
    dorn k; repnd.
    + rw @cover_vars_eq in c'.
      rw subvars_prop in c'.
      apply c' in k0.
      rw @dom_csub_eq in k; auto.
    + apply in_sub_free_vars_iff in k; exrepnd.
      apply in_sub_keep_first in k0; repnd.
      apply sub_find_some in k2.
      apply in_csub2sub in k2.
      destruct k2 as [cl wf].
      rw cl in k1; sp.
  - introv i; apply in_csub2sub in i; sp.
  - introv i; apply in_csub2sub in i; sp.
Qed.

Lemma csubst_snoc_app_move_to_last {o} :
  forall (t : @NTerm o) s1 s2 x a,
    !LIn x (dom_csub s2)
    -> csubst t (snoc s1 (x, a) ++ s2)
       = csubst t (snoc (s1 ++ s2) (x, a)).
Proof.
  introv ni1.
  rw <- snoc_append_l.
  symmetry.
  rw <- @csubst_app.
  rewrite <- (csubst_swap (csubst t s1) s2); auto.
  rw @csubst_app.
  rw <- snoc_append_r; auto.
Qed.

Lemma lsubstc_snoc_app_move_to_last {o} :
  forall (t : @NTerm o) s1 s2 x a w c,
    !LIn x (dom_csub s2)
    -> {c' : cover_vars t (snoc (s1 ++ s2) (x,a))
        $ lsubstc t w (snoc s1 (x,a) ++ s2) c
          = lsubstc t w (snoc (s1 ++ s2) (x,a)) c'}.
Proof.
  introv ni.

  assert (cover_vars t (snoc (s1 ++ s2) (x,a))) as cv.
  allrw @cover_vars_eq; allrw subvars_eq.
  introv i; applydup c in i.
  allrw @dom_csub_app; allrw @dom_csub_snoc; allrw @dom_csub_app; allsimpl.
  allrw in_app_iff; allrw in_snoc; allrw in_app_iff.
  sp; subst; sp.

  exists cv.

  apply cterm_eq; simpl.
  apply csubst_snoc_app_move_to_last; auto.
Qed.

Lemma csubst_snoc_app_move_down {o} :
  forall (t : @NTerm o) s1 s2 s3 x a,
    !LIn x (dom_csub s2)
    -> csubst t ((snoc s1 (x, a) ++ s2) ++ s3)
       = csubst t (snoc (s1 ++ s2) (x, a) ++ s3).
Proof.
  introv ni1.
  rw <- @csubst_app.
  symmetry; rw <- @csubst_app.
  rw @csubst_snoc_app_move_to_last; auto.
Qed.

Lemma lsubstc_snoc_app_move_down {o} :
  forall (t : @NTerm o) s1 s2 s3 x a w c,
    !LIn x (dom_csub s2)
    -> {c' : cover_vars t (snoc (s1 ++ s2) (x,a) ++ s3)
        $ lsubstc t w ((snoc s1 (x,a) ++ s2) ++ s3) c
          = lsubstc t w (snoc (s1 ++ s2) (x,a) ++ s3) c'}.
Proof.
  introv ni.

  assert (cover_vars t (snoc (s1 ++ s2) (x,a) ++ s3)) as cv.
  allrw @cover_vars_eq; allrw subvars_eq.
  introv i; applydup c in i.
  allrw @dom_csub_app; allrw @dom_csub_snoc; allrw @dom_csub_app; allsimpl.
  allrw in_app_iff; allrw in_snoc; allrw in_app_iff.
  sp; subst; sp.

  exists cv.

  apply cterm_eq; simpl.
  apply csubst_snoc_app_move_down; auto.
Qed.

Lemma lsubstc_snoc_app_move_down2 {o} :
  forall (t : @NTerm o) s1 s2 s3 x a w c,
    !LIn x (dom_csub s2)
    -> {c' : cover_vars t ((snoc s1 (x,a) ++ s2) ++ s3)
        $ lsubstc t w (snoc (s1 ++ s2) (x,a) ++ s3) c
          = lsubstc t w ((snoc s1 (x,a) ++ s2) ++ s3) c'}.
Proof.
  introv ni.

  assert (cover_vars t ((snoc s1 (x,a) ++ s2) ++ s3)) as cv.
  allrw @cover_vars_eq; allrw subvars_eq.
  introv i; applydup c in i.
  allrw @dom_csub_app; allrw @dom_csub_snoc; allrw @dom_csub_app; allsimpl.
  allrw in_app_iff; allrw in_snoc; allrw in_app_iff.
  sp; subst; sp.

  exists cv.

  apply cterm_eq; simpl.
  symmetry; apply csubst_snoc_app_move_down; auto.
Qed.

Lemma subst_preserves_isprog_vars {p} :
  forall (t : @NTerm p) (v : NVar) (u : NTerm) vs,
    isprog_vars (v :: vs) t
    -> isprog_vars vs u
    -> isprog_vars vs (subst t v u).
Proof.
  introv ispt ispu.
  unfold lsubst.
  allrw @isprog_vars_eq; repnd; dands.
  - unfold subst.
    pose proof (eqvars_free_vars_disjoint t [(v,u)]) as eqv; simpl in eqv.
    allrw subvars_prop; introv i.
    eapply eqvars_prop in eqv.
    apply eqv in i; clear eqv.
    apply in_app_iff in i; dorn i.
    + apply in_remove_nvars in i; rw in_single_iff in i; repnd.
      discover; allsimpl; sp.
    + revert i; boolvar; intro i; allsimpl; tcsp.
      allrw app_nil_r.
      discover; sp.
  - apply lsubst_wf_iff; auto.
    unfold wf_sub, sub_range_sat; simpl; simpl; introv k; sp; cpx.
Qed.

Lemma cover_vars_isprog_vars {o} :
  forall (t : @NTerm o) sub vs1 vs2,
    wf_term t
    -> eqvars vs2 (vs1 ++ dom_csub sub)
    -> (cover_vars_upto t sub vs1 <=> isprog_vars vs2 t).
Proof.
  introv wf eqv.
  unfold cover_vars_upto.
  rw @isprog_vars_eq.
  rw eqvars_prop in eqv.
  split; intro k; repnd; dands; auto.
  - allrw subvars_prop; introv i.
    discover; auto.
  - apply nt_wf_eq; auto.
  - allrw subvars_prop; introv i.
    discover; auto.
Qed.

Lemma cover_vars_implies_isprog_vars {o} :
  forall (t : @NTerm o) sub vs1 vs2,
    wf_term t
    -> subvars (vs1 ++ dom_csub sub) vs2
    -> cover_vars_upto t sub vs1
    -> isprog_vars vs2 t.
Proof.
  introv wf eqv cv.
  unfold cover_vars_upto in cv.
  rw @isprog_vars_eq.
  allrw subvars_prop; dands.
  - introv i; discover; auto.
  - apply nt_wf_eq; auto.
Qed.

Lemma lsubstc_subst_snoc_eq_ex {o} :
  forall (s : @CSub o)
         (b : NTerm)
         (x y : NVar)
         (a : CTerm)
         (w1 : wf_term (subst b x (mk_var y)))
         (c1 : cover_vars (subst b x (mk_var y)) (snoc s (y, a))),
    !LIn y (bound_vars b)
    -> !LIn y (dom_csub s)
    -> (y <> x -> !LIn y (free_vars b))
    -> {w2 : wf_term b
        & {c2 : cover_vars_upto b (csub_filter s [x]) [x]
        & lsubstc (subst b x (mk_var y)) w1 (snoc s (y, a)) c1
          = substc a x (lsubstc_vars b w2 (csub_filter s [x]) [x] c2)}}.
Proof.
  introv ni1 ni2 ni3.

  assert (wf_term b) as w2 by (apply lsubst_wf_term in w1; auto).
  exists w2.

  assert (cover_vars_upto b (csub_filter s [x]) [x]) as c2.
  allrw @cover_vars_eq.
  unfold cover_vars_upto.
  allrw subvars_prop; introv i; simpl.
  destruct (deq_nvar x x0); subst; tcsp.
  right.
  rw @dom_csub_csub_filter; rw in_remove_nvars; rw in_single_iff; dands; tcsp.
  pose proof (c1 x0) as h; autodimp h hyp.
  pose proof (eqvars_free_vars_disjoint b [(x,mk_var y)]) as eqv.
  rw eqvars_prop in eqv; apply eqv; clear eqv; simpl.
  rw in_app_iff; rw in_remove_nvars; rw in_single_iff; left; sp.
  rw @dom_csub_snoc in h; simpl in h; rw in_snoc in h; dorn h; tcsp; subst.
  autodimp ni3 hyp; sp.

  exists c2.
  apply lsubstc_subst_snoc_eq; sp.
Qed.

Lemma lsubst_aux_swap_context {o} :
  forall t (s1 s2 s : @Sub o) v u,
    (forall v t, LIn (v, t) s -> isprogram t)
    -> isprogram u
    -> !LIn v (dom_sub s)
    -> lsubst_aux t ((s1 ++ (v, u) :: s) ++ s2) = lsubst_aux t ((s1 ++ snoc s (v, u)) ++ s2).
Proof.
  nterm_ind t as [v|f|op lbt ind] Case; simpl; intros; auto.

  - Case "vterm".
    repeat (rw @sub_find_app).
    rw @sub_find_snoc; simpl; boolvar.
    + remember (sub_find s1 v) as s1n; destruct s1n; symmetry in Heqs1n; auto.
      remember (sub_find s v) as sn; destruct sn; symmetry in Heqsn; auto.
      apply sub_find_some in Heqsn.
      apply in_dom_sub in Heqsn; sp.
    + remember (sub_find s1 v) as s1n; destruct s1n; symmetry in Heqs1n; auto.
      remember (sub_find s v) as sn; destruct sn; symmetry in Heqsn; auto.

  - Case "oterm".
    apply oterm_eq; auto.
    apply eq_maps; introv i.
    destruct x; simpl.
    apply bterm_eq; auto.

    repeat (rw @sub_filter_app); simpl.
    repeat (rw @sub_filter_snoc); boolvar; auto.

    eapply ind; eauto; introv;
    try (rw @in_sub_filter);
    try (rw <- @dom_sub_sub_filter);
    try (rw in_remove_nvars);
    intro k; repnd; discover; sp.
Qed.

Lemma range_snoc {p} :
  forall (s : @Sub p) v t,
    range (snoc s (v, t))
    = snoc (range s) t.
Proof.
  introv; unfold range; rw map_snoc; sp.
Qed.

Lemma lsubst_swap_context {o} :
  forall t (s1 s2 s : @Sub o) v u,
    (forall v t, LIn (v, t) s -> isprogram t)
    -> (forall v t, LIn (v, t) s1 -> isprogram t)
    -> (forall v t, LIn (v, t) s2 -> isprogram t)
    -> isprogram u
    -> !LIn v (dom_sub s)
    -> lsubst t ((s1 ++ (v, u) :: s) ++ s2) = lsubst t ((s1 ++ snoc s (v, u)) ++ s2).
Proof.
  introv k1 k2 k3 isp ni.
  change_to_lsubst_aux4;
    try (complete (allrw @range_app; allsimpl; try (rw @range_snoc);
                   allrw flat_map_app; allrw flat_map_snoc; allsimpl;
                   destruct isp as [cl w]; rw cl;
                   repeat (rw @closed_sub; auto); simpl; sp)).
  apply lsubst_aux_swap_context; auto.
Qed.

Lemma csubst_swap_context {o} :
  forall t (s1 s2 s : @CSub o) v u,
    !LIn v (dom_csub s)
    -> csubst t ((s1 ++ (v, u) :: s) ++ s2)
       = csubst t ((s1 ++ snoc s (v, u)) ++ s2).
Proof.
  intros.
  unfold csubst; simpl.
  repeat (rw <- @csub2sub_app); simpl.
  allrw @csub2sub_snoc.
  apply lsubst_swap_context; auto;
  try (complete (intros; allapply @in_csub2sub; sp)).
  rw @dom_csub_eq; auto.
Qed.

Lemma csubst_subst_snoc_eq2 {o} :
  forall s b x y (a : @CTerm o),
    !LIn y (bound_vars b)
    -> !LIn y (dom_csub s)
    -> !LIn x (dom_csub s)
    -> x <> y
    -> csubst (subst b x (mk_var y)) (snoc s (y, a))
       = csubst b (snoc (snoc s (x, a)) (y, a)).
Proof.
  introv ni1 ni2 ni3 ni4.
  unfold subst, csubst.
  rewrite simple_lsubst_lsubst; simpl;
  [
  | complete (intros; sp; cpx; simpl; rw disjoint_singleton_l; auto)
  | complete (intros; allapply @in_csub2sub; auto)].

  change_to_lsubst_aux4;
    [ |
      simpl;
        apply disjoint_app_r;
        rw disjoint_flat_map_r;
        dands; [remember (sub_find (csub2sub (snoc s (y,a))) y) as k; destruct k; symmetry in Heqk|]; simpl;
        [ complete (apply sub_find_some in Heqk; apply in_csub2sub in Heqk;
                    destruct Heqk as [cl k]; rw cl; sp)
        | complete (rw disjoint_singleton_r; auto)
        | ]; introv k;
        apply in_range in k; exrepnd;
        apply in_csub2sub in k0; auto; destruct k0 as [cl k]; rw cl; sp
    ].

  simpl.

  rw @csub2sub_snoc.
  rw @sub_find_snoc.

  pose proof (sub_find_none_iff (csub2sub s) y) as k.
  rw @dom_csub_eq in k; apply k in ni2; rw ni2; boolvar.

  rw snoc_as_append.
  pose proof (lsubst_aux_swap_context b []) as h; simpl in h.
  rw h; auto.
  rw <- snoc_as_append.
  repeat (rw @csub2sub_snoc); auto.
  intros; allapply @in_csub2sub; sp.
  rw @dom_csub_eq; auto.
Qed.

Lemma lsubstc_subst_snoc_eq2 {o} :
  forall (s : @CSub o) b x y a w1 w2 c1 c2,
    !LIn y (bound_vars b)
    -> !LIn y (dom_csub s)
    -> !LIn x (dom_csub s)
    -> x <> y
    -> lsubstc (subst b x (mk_var y)) w1 (snoc s (y, a)) c1
       = lsubstc b w2 (snoc (snoc s (x, a)) (y, a)) c2.
Proof.
  intros.

  apply cterm_eq; simpl.
  apply csubst_subst_snoc_eq2; auto.
Qed.

Lemma lsubstc_subst_snoc_eq2_ex {o} :
  forall (s : @CSub o)
         (b : NTerm)
         (x y : NVar)
         (a : CTerm)
         (w1 : wf_term (subst b x (mk_var y)))
         (c1 : cover_vars (subst b x (mk_var y)) (snoc s (y, a))),
    !LIn y (bound_vars b)
    -> !LIn y (dom_csub s)
    -> !LIn x (dom_csub s)
    -> x <> y
    -> {w2 : wf_term b
        & {c2 : cover_vars b (snoc (snoc s (x,a)) (y,a))
        & lsubstc (subst b x (mk_var y)) w1 (snoc s (y, a)) c1
          = lsubstc b w2 (snoc (snoc s (x,a)) (y,a)) c2}}.
Proof.
  introv ni1 ni2.

  assert (wf_term b) as w2 by (apply lsubst_wf_term in w1; auto).
  exists w2.

  assert (cover_vars b (snoc (snoc s (x,a)) (y,a))) as c2.
  allrw @cover_vars_eq; allrw subvars_prop; introv i; simpl.
  repeat (rw @dom_csub_snoc); simpl; repeat (rw in_snoc).
  destruct (deq_nvar x x0); subst; tcsp.
  pose proof (c1 x0) as h; autodimp h hyp.
  pose proof (eqvars_free_vars_disjoint b [(x,mk_var y)]) as eqv.
  rw eqvars_prop in eqv; apply eqv; clear eqv; simpl.
  rw in_app_iff; rw in_remove_nvars; rw in_single_iff; left; sp.
  rw @dom_csub_snoc in h; simpl in h; rw in_snoc in h; dorn h; tcsp; subst.

  exists c2.

  apply lsubstc_subst_snoc_eq2; auto.
Qed.

Lemma lsubst_aux_snoc_cover_vars {p} :
  forall (t : @NTerm p) sub v u,
    (LIn v (free_vars t) -> LIn v (dom_sub sub))
    -> lsubst_aux t (snoc sub (v, u)) = lsubst_aux t sub.
Proof.
  nterm_ind t as [v|f|o lbt ind] Case; simpl; introv ni; auto.

  - Case "vterm".
    allunfold @covered; allsimpl; allrw subvars_singleton_l.
    rw @sub_find_snoc.
    remember (sub_find sub v); destruct o; symmetry in Heqo; sp.
    boolvar; auto.
    applydup @sub_find_none2 in Heqo; sp.

  - Case "oterm".
    f_equal.
    apply eq_maps; sp.
    destruct x; simpl.

    rw @sub_filter_snoc; boolvar; auto.
    apply bterm_eq; auto.
    apply ind with (lv := l); auto.

    introv i.
    rw <- @dom_sub_sub_filter.
    apply in_remove_nvars; dands; auto.
    assert (LIn v (flat_map free_vars_bterm lbt)); discover; auto.
    apply lin_flat_map.
    exists (bterm l n); dands; auto.
    simpl; apply in_remove_nvars; sp.
Qed.

Lemma lsubst_snoc_cover_vars {p} :
  forall (t : @NTerm p) sub v u,
    disjoint (bound_vars t) (flat_map free_vars (range sub))
    -> disjoint (bound_vars t) (free_vars u)
    -> (LIn v (free_vars t) -> LIn v (dom_sub sub))
    -> lsubst t (snoc sub (v, u)) = lsubst t sub.
Proof.
  introv d1 d2 ni.
  change_to_lsubst_aux4.
  - apply lsubst_aux_snoc_cover_vars; auto.
  - allrw @range_snoc.
    allrw flat_map_snoc.
    allrw disjoint_app_r; sp.
Qed.

Lemma prog_sub_nil {o} : @prog_sub o [].
Proof.
  unfold prog_sub, sub_range_sat; simpl; sp.
Qed.
Hint Immediate prog_sub_nil.

Lemma closed_sub_cl {p} :
  forall (sub : @Sub p),
    (forall v t, LIn (v, t) sub -> closed t)
    -> flat_map free_vars (range sub) = [].
Proof.
  induction sub; allsimpl; introv h; auto.
  destruct a; allsimpl.
  pose proof (h n n0) as k; autodimp k hyp.
  rw k.
  rw IHsub; auto.
  introv i; eapply h; eauto.
Qed.

Lemma disjoint_sub_if_cl {p} :
  forall (sub : @Sub p),
    (forall v t, LIn (v, t) sub -> closed t)
    -> forall t : @NTerm p, disjoint (bound_vars t) (flat_map free_vars (range sub)).
Proof.
  introv i.
  rw @closed_sub_cl; auto.
Qed.

Lemma dom_sub_lsubst_sub {o} :
  forall (sub1 sub2 : @Sub o),
    dom_sub (lsubst_sub sub1 sub2) = dom_sub sub1.
Proof.
  induction sub1; introv; simpl; auto.
  destruct a; simpl.
  apply eq_cons; auto.
Qed.
