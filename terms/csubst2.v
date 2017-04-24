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


Require Export list_tacs.
Require Export swap_props.
Require Export csubst.
Require Export cvterm2.


Lemma subst_preserves_isprog_vars {o} :
  forall vs (t : @NTerm o) v u,
    isprog_vars (vs ++ [v]) t
    -> isprog u
    -> isprog_vars vs (subst t v u).
Proof.
  introv ispt ispu.
  allrw @isprog_vars_eq; repnd.

  pose proof (isprogram_lsubst1 t [(v,u)]) as h.
  simpl in h; repeat (autodimp h hyp).
  { introv k; repndors; cpx; apply isprogram_eq; auto. }

  repnd.
  unfold subst.
  rw h; clear h.
  dands; auto.

  apply subvars_remove_nvars; auto.
Qed.
Hint Resolve subst_preserves_isprog_vars : isprog.

Definition substcv {o} vs (u : @CTerm o) (v : NVar) (t : CVTerm (vs ++ [v])) : CVTerm vs :=
  let (a,x) := t in
  let (b,y) := u in
    exist (isprog_vars vs) (subst a v b) (subst_preserves_isprog_vars vs a v b x y).

Lemma substc_mkcv_function {o} :
  forall v (t : @CTerm o) (a : CVTerm [v]) x (b : CVTerm [x,v]),
    v <> x
    -> substc t v (mkcv_function [v] a x b)
       = mkc_function (substc t v a) x (substcv [x] t v b).
Proof.
  introv ni.
  apply cterm_eq; simpl.
  destruct_cterms; simpl.
  applydup @closed_if_isprog in i; unfold closed in i2.

  unfold subst, lsubst; simpl; allrw app_nil_r; rw i2; simpl; boolvar;
  allsimpl; try (complete (provefalse; tcsp)); tcsp; boolvar; allsimpl;
  tcsp; allrw not_over_or; repnd; tcsp; boolvar; allsimpl; tcsp.
Qed.

Lemma combine_map_r :
  forall (A B : tuniv) (f : A -> B) (l : list A),
    combine (map f l) l = map (fun a : A => (f a, a)) l.
Proof.
  induction l; simpl; auto.
  f_equal; auto.
Qed.

Lemma disjoint_swapbvars_if_remove_nvars :
  forall vs vs1 vs2 l,
    disjoint l (remove_nvars vs1 vs)
    -> disjoint vs2 vs
    -> disjoint vs2 vs1
    -> disjoint vs2 l
    -> length vs1 = length vs2
    -> no_repeats vs2
    -> disjoint l (swapbvars (mk_swapping vs1 vs2) vs).
Proof.
  induction vs; introv d1 d2 d3 d4 len norep; allsimpl; auto.
  allrw disjoint_cons_r; repnd.
  allrw remove_nvars_cons_r; boolvar; allrw disjoint_cons_r; repnd; dands; tcsp.
  - intro k.
    pose proof (swapvar_implies3 vs1 vs2 a) as h.
    repeat (autodimp h hyp); eauto with slow.
    apply d4 in h; sp.
  - rw swapvar_not_in; auto.
Qed.

Lemma allvars_swap {o} :
  forall (t : @NTerm o) vs1 vs2,
    no_repeats vs2
    -> disjoint vs1 vs2
    -> allvars (swap (mk_swapping vs1 vs2) t)
       = swapbvars (mk_swapping vs1 vs2) (allvars t).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv norep disj; allsimpl; auto.

  Case "oterm".
  rw flat_map_map; unfold compose.
  rw @swapbvars_flat_map.
  apply eq_flat_maps; introv i.
  destruct x as [l t]; simpl.
  allrw swapbvars_app; f_equal.
  erewrite ind; eauto.
Qed.

Lemma alphaeq_swap_cl {o} :
  forall (t : @NTerm o) vs1 vs2,
    disjoint vs1 (free_vars t)
    -> disjoint vs1 vs2
    -> disjoint vs2 (allvars t)
    -> length vs1 = length vs2
    -> no_repeats vs2
    -> alphaeq (swap (mk_swapping vs1 vs2) t) t.
Proof.
  nterm_ind1s t as [v|op bs ind] Case;
  introv d1 d2 d3 len norep; allsimpl; eauto 3 with slow.

  - Case "vterm".
    allrw disjoint_singleton_r.
    rw swapvar_not_in; eauto with slow.

  - Case "oterm".
    apply alphaeq_eq.
    apply alpha_eq_oterm_combine; allrw map_length; dands; auto.
    introv i.
    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].
    apply alphaeqbt_eq.
    rw combine_map_r in i.
    rw in_map_iff in i; exrepnd.
    destruct a as [l t]; allsimpl; ginv.
    disj_flat_map; allsimpl; allrw disjoint_app_r; repnd.

    pose proof (fresh_vars (length l)
                           (l
                              ++ vs1
                              ++ vs2
                              ++ swapbvars (mk_swapping vs1 vs2) l
                              ++ allvars (swap (mk_swapping vs1 vs2) t)
                              ++ allvars t
                              ++ free_vars t
                           )
               ) as h; exrepnd.
    allrw disjoint_app_r; repnd.

    apply (aeqbt _ lvn); allsimpl; auto.

    { rw length_swapbvars; auto. }

    { allrw disjoint_app_r; dands; auto. }

    { rw @swap_swap.
      rw mk_swapping_app; auto.
      rw <- @swap_app_swap; eauto with slow.
      rw <- mk_swapping_app; auto.
      rw <- @swap_swap.
      apply (ind t _ l); auto.

      - rw @size_swap; eauto 3 with slow.

      - rw @free_vars_swap; eauto 3 with slow.
        apply disjoint_swapbvars_if_remove_nvars; auto.

      - rw @allvars_swap; eauto 3 with slow.
        apply disjoint_swapbvars_if_remove_nvars; auto.
        eapply subvars_disjoint_r;[|exact i0].
        apply subvars_remove_nvars.
        apply subvars_app_weak_l; auto.
    }
Qed.

Definition range_sw (sw : swapping) : list NVar := map (fun x => snd x) sw.
Definition dom_sw (sw : swapping) : list NVar := map (fun x => fst x) sw.

Lemma length_range_sw :
  forall (sw : swapping), length (range_sw sw) = length sw.
Proof.
  introv.
  unfold range_sw.
  rw map_length; auto.
Qed.

Lemma length_dom_sw :
  forall (sw : swapping), length (dom_sw sw) = length sw.
Proof.
  introv.
  unfold dom_sw.
  rw map_length; auto.
Qed.

Lemma swapping_eta :
  forall sw, mk_swapping (dom_sw sw) (range_sw sw) = sw.
Proof.
  induction sw; simpl; auto.
  destruct a; simpl; f_equal; tcsp.
Qed.

Lemma alphaeq_add_swap2 {o} :
  forall (sw : swapping) (t1 t2 : @NTerm o),
    no_repeats (range_sw sw)
    -> disjoint (range_sw sw) (dom_sw sw ++ allvars t1 ++ allvars t2)
    -> alphaeq t1 t2
    -> alphaeq (swap sw t1) (swap sw t2).
Proof.
  introv norep disj aeq.
  pose proof (alphaeq_add_swap [] (dom_sw sw) (range_sw sw) t1 t2) as h.
  repeat (autodimp h hyp); allrw disjoint_app_r; repnd; dands; tcsp.
  - allrw length_dom_sw; allrw length_range_sw; auto.
  - apply alphaeq_implies_alphaeq_vs; auto.
  - rw @alphaeq_exists.
    allrw swapping_eta.
    eexists; eauto.
Qed.

Lemma alphaeq_swap_cl2 {o} :
  forall (t : @NTerm o) sw,
    disjoint (dom_sw sw) (free_vars t)
    -> disjoint (dom_sw sw) (range_sw sw)
    -> disjoint (range_sw sw) (allvars t)
    -> no_repeats (range_sw sw)
    -> alphaeq (swap sw t) t.
Proof.
  introv d1 d2 d3 norep.
  pose proof (alphaeq_swap_cl t (dom_sw sw) (range_sw sw)) as h.
  rw swapping_eta in h.
  rw length_dom_sw in h.
  rw length_range_sw in h.
  repeat (autodimp h hyp).
Qed.

Lemma substc_mkcv_fun {o} :
  forall v (t : @CTerm o) (a b : CVTerm [v]),
    alphaeqc
      (substc t v (mkcv_fun [v] a b))
      (mkc_fun (substc t v a) (substc t v b)).
Proof.
  introv.
  destruct_cterms.
  unfold alphaeqc; simpl.
  applydup @closed_if_isprog in i; unfold closed in i2.

  unfold subst, lsubst; simpl; allrw app_nil_r; rw i2; simpl; boolvar;
  allsimpl; try (complete (provefalse; tcsp)); tcsp; boolvar; allsimpl;
  tcsp; allrw not_over_or; repnd; tcsp; boolvar; allsimpl; tcsp;
  allrw @lsubst_aux_nil; repndors; tcsp; subst; GC.

  - apply alphaeq_eq; constructor; simpl; auto.
    introv k; destruct n;[|destruct n]; cpx; unfold selectbt; simpl.
    + apply alphaeqbt_eq; auto.
    + rw @lsubst_aux_trivial_cl_term; simpl;
      [apply alphaeqbt_eq; auto|].
      apply disjoint_singleton_r; intro j.
      apply newvar_prop in j; sp.

  - apply alphaeq_eq; constructor; simpl; auto.
    introv k; destruct n;[|destruct n]; cpx; unfold selectbt; simpl.
    + apply alphaeqbt_eq; auto.
    + rw @lsubst_aux_trivial_cl_term; simpl;
      [apply alphaeqbt_eq; auto|].
      apply disjoint_singleton_r; intro j.
      apply newvar_prop in j; sp.

  - apply alphaeq_eq; constructor; simpl; auto.
    introv k; destruct n;[|destruct n]; cpx; unfold selectbt; simpl.
    + apply alphaeqbt_eq; auto.
    + rw @lsubst_aux_trivial_cl_term; simpl;
      [apply alphaeqbt_eq; auto|].
      apply disjoint_singleton_r; intro j.
      pose proof (fresh_var_not_in (all_vars (change_bvars_alpha [] x0))) as h.
      destruct h.
      rw in_app_iff; left; rw @free_vars_change_bvars_alpha; auto.

  - apply alphaeq_eq; constructor; simpl; auto.
    introv k; destruct n;[|destruct n]; cpx; unfold selectbt; simpl.
    + apply alphaeqbt_eq; auto.
    + pose proof (ex_fresh_var ([newvar x0,newvar (lsubst_aux x0 [(v, x)])]
                                  ++ allvars (lsubst_aux x0 [(v, x)]))) as h; exrepnd.
      allsimpl; allrw not_over_or; repnd; GC.
      apply (aeqbt _ [v0]); simpl; auto.

      * apply disjoint_singleton_l; simpl; allrw in_app_iff; allrw not_over_or; dands; tcsp.

      * apply (alphaeq_trans _ (lsubst_aux x0 [(v,x)])).

        { apply alphaeq_swap_cl2; simpl; tcsp; apply disjoint_singleton_l; simpl; tcsp.
          rw @free_vars_lsubst_aux_cl; simpl.
          - rw in_remove_nvars; simpl; rw not_over_or; intro j; repnd.
            apply newvar_prop in j0; sp.
          - apply cl_sub_cons; dands; eauto with slow. }

        { apply alphaeq_sym.
          apply alphaeq_swap_cl2; simpl; tcsp; apply disjoint_singleton_l; simpl; tcsp.
          rw @free_vars_lsubst_aux_cl; simpl.
          - rw in_remove_nvars; simpl; rw not_over_or; intro j; repnd.
            rw @isprog_vars_eq in i0; repnd.
            rw subvars_prop in i3.
            apply i3 in j0; allsimpl; sp.
          - apply cl_sub_cons; dands; eauto with slow. }
Qed.

Lemma substc_mkcv_isect {o} :
  forall v (t : @CTerm o) (a : CVTerm [v]) x (b : CVTerm [x,v]),
    v <> x
    -> substc t v (mkcv_isect [v] a x b)
       = mkc_isect (substc t v a) x (substcv [x] t v b).
Proof.
  introv ni.
  apply cterm_eq; simpl.
  destruct_cterms; simpl.
  applydup @closed_if_isprog in i; unfold closed in i2.

  unfold subst, lsubst; simpl; allrw app_nil_r; rw i2; simpl; boolvar;
  allsimpl; try (complete (provefalse; tcsp)); tcsp; boolvar; allsimpl;
  tcsp; allrw not_over_or; repnd; tcsp; boolvar; allsimpl; tcsp.
Qed.

Lemma substc_mkcv_ufun {o} :
  forall v (t : @CTerm o) (a b : CVTerm [v]),
    alphaeqc
      (substc t v (mkcv_ufun [v] a b))
      (mkc_ufun (substc t v a) (substc t v b)).
Proof.
  introv.
  destruct_cterms.
  unfold alphaeqc; simpl.
  applydup @closed_if_isprog in i; unfold closed in i2.

  unfold subst, lsubst; simpl; allrw app_nil_r; rw i2; simpl; boolvar;
  allsimpl; try (complete (provefalse; tcsp)); tcsp; boolvar; allsimpl;
  tcsp; allrw not_over_or; repnd; tcsp; boolvar; allsimpl; tcsp;
  allrw @lsubst_aux_nil; repndors; tcsp; subst; GC.

  - apply alphaeq_eq; constructor; simpl; auto.
    introv k; destruct n;[|destruct n]; cpx; unfold selectbt; simpl.
    + apply alphaeqbt_eq; auto.
    + rw @lsubst_aux_trivial_cl_term; simpl;
      [apply alphaeqbt_eq; auto|].
      apply disjoint_singleton_r; intro j.
      apply newvar_prop in j; sp.

  - apply alphaeq_eq; constructor; simpl; auto.
    introv k; destruct n;[|destruct n]; cpx; unfold selectbt; simpl.
    + apply alphaeqbt_eq; auto.
    + rw @lsubst_aux_trivial_cl_term; simpl;
      [apply alphaeqbt_eq; auto|].
      apply disjoint_singleton_r; intro j.
      apply newvar_prop in j; sp.

  - apply alphaeq_eq; constructor; simpl; auto.
    introv k; destruct n;[|destruct n]; cpx; unfold selectbt; simpl.
    + apply alphaeqbt_eq; auto.
    + rw @lsubst_aux_trivial_cl_term; simpl;
      [apply alphaeqbt_eq; auto|].
      apply disjoint_singleton_r; intro j.
      pose proof (fresh_var_not_in (all_vars (change_bvars_alpha [] x0))) as h.
      destruct h.
      rw in_app_iff; left; rw @free_vars_change_bvars_alpha; auto.

  - apply alphaeq_eq; constructor; simpl; auto.
    introv k; destruct n;[|destruct n]; cpx; unfold selectbt; simpl.
    + apply alphaeqbt_eq; auto.
    + pose proof (ex_fresh_var ([newvar x0,newvar (lsubst_aux x0 [(v, x)])]
                                  ++ allvars (lsubst_aux x0 [(v, x)]))) as h; exrepnd.
      allsimpl; allrw not_over_or; repnd; GC.
      apply (aeqbt _ [v0]); simpl; auto.

      * apply disjoint_singleton_l; simpl; allrw in_app_iff; allrw not_over_or; dands; tcsp.

      * apply (alphaeq_trans _ (lsubst_aux x0 [(v,x)])).

        { apply alphaeq_swap_cl2; simpl; tcsp; apply disjoint_singleton_l; simpl; tcsp.
          rw @free_vars_lsubst_aux_cl; simpl.
          - rw in_remove_nvars; simpl; rw not_over_or; intro j; repnd.
            apply newvar_prop in j0; sp.
          - apply cl_sub_cons; dands; eauto with slow. }

        { apply alphaeq_sym.
          apply alphaeq_swap_cl2; simpl; tcsp; apply disjoint_singleton_l; simpl; tcsp.
          rw @free_vars_lsubst_aux_cl; simpl.
          - rw in_remove_nvars; simpl; rw not_over_or; intro j; repnd.
            rw @isprog_vars_eq in i0; repnd.
            rw subvars_prop in i3.
            apply i3 in j0; allsimpl; sp.
          - apply cl_sub_cons; dands; eauto with slow. }
Qed.

Lemma lsubstc_mkc_tnat {o} :
  forall (w : @wf_term o mk_tnat) s c,
    lsubstc mk_tnat w s c = mkc_tnat.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; auto.
Qed.
Hint Rewrite @lsubstc_mkc_tnat : slow.

Lemma csubst_mk_tnat {o} :
  forall sub, csubst mk_tnat sub = @mk_tnat o.
Proof.
  intro; unfold csubst; simpl; fold @mk_axiom.
  change_to_lsubst_aux4; simpl; sp.
  allrw @sub_filter_nil_r.
  repeat (rw @sub_find_sub_filter; simpl; tcsp).
Qed.
Hint Rewrite @csubst_mk_tnat : slow.

Lemma lsubstc_mk_tnat {o} :
  forall p sub c,
    lsubstc mk_tnat p sub c = @mkc_tnat o.
Proof.
  unfold lsubstc, mkc_tnat; sp.
  apply cterm_eq; simpl.
  apply csubst_mk_tnat; auto.
Qed.
Hint Rewrite @lsubstc_mk_tnat : slow.

Lemma lsubstc_mk_less {o} :
  forall (a b c d : @NTerm o) sub,
  forall wa : wf_term a,
  forall wb : wf_term b,
  forall wc : wf_term c,
  forall wd : wf_term d,
  forall w  : wf_term (mk_less a b c d),
  forall ca : cover_vars a sub,
  forall cb : cover_vars b sub,
  forall cc : cover_vars c sub,
  forall cd : cover_vars d sub,
  forall cv  : cover_vars (mk_less a b c d) sub,
    lsubstc (mk_less a b c d) w sub cv
    = mkc_less (lsubstc a wa sub ca)
               (lsubstc b wb sub cb)
               (lsubstc c wc sub cc)
               (lsubstc d wd sub cd).
Proof.
  introv.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; sp.
Qed.

Lemma lsubstc_mk_less_ex {o} :
  forall (a b c d : @NTerm o) sub,
  forall wf : wf_term (mk_less a b c d),
  forall cv : cover_vars (mk_less a b c d) sub,
  {wa : wf_term a
   & {wb : wf_term b
   & {wc : wf_term c
   & {wd : wf_term d
   & {ca : cover_vars a sub
   & {cb : cover_vars b sub
   & {cc : cover_vars c sub
   & {cd : cover_vars d sub
      & lsubstc (mk_less a b c d) wf sub cv
           = mkc_less (lsubstc a wa sub ca)
                      (lsubstc b wb sub cb)
                      (lsubstc c wc sub cc)
                      (lsubstc d wd sub cd)}}}}}}}}.
Proof.
  sp.

  assert (wf_term a) as wa.
  { allrw <- @wf_less_iff; sp. }

  assert (wf_term b) as wb.
  { allrw <- @wf_less_iff; sp. }

  assert (wf_term c) as wc.
  { allrw <- @wf_less_iff; sp. }

  assert (wf_term d) as wd.
  { allrw <- @wf_less_iff; sp. }

  exists wa wb wc wd.

  assert (cover_vars a sub) as ca.
  { unfold cover_vars in cv.
    simpl in cv.
    repeat (rw remove_nvars_nil_l in cv).
    rw app_nil_r in cv.
    repeat (rw @over_vars_app_l in cv); sp. }

  assert (cover_vars b sub) as cb.
  { unfold cover_vars in cv.
    simpl in cv.
    repeat (rw remove_nvars_nil_l in cv).
    rw app_nil_r in cv.
    repeat (rw @over_vars_app_l in cv); sp. }

  assert (cover_vars c sub) as cc.
  { unfold cover_vars in cv.
    simpl in cv.
    repeat (rw remove_nvars_nil_l in cv).
    rw app_nil_r in cv.
    repeat (rw @over_vars_app_l in cv); sp. }

  assert (cover_vars d sub) as cd.
  { unfold cover_vars in cv.
    simpl in cv.
    repeat (rw remove_nvars_nil_l in cv).
    rw app_nil_r in cv.
    repeat (rw @over_vars_app_l in cv); sp. }

  exists ca cb cc cd.
  apply lsubstc_mk_less.
Qed.

Lemma csubst_mk_true {o} :
  forall sub, csubst mk_true sub = @mk_true o.
Proof.
  intro; unfold csubst; simpl; fold @mk_axiom.
  change_to_lsubst_aux4; simpl; sp.
Qed.

Lemma lsubstc_mk_true {o} :
  forall p sub c,
    lsubstc mk_true p sub c = @mkc_true o.
Proof.
  unfold lsubstc, mkc_true; sp.
  apply cterm_eq; simpl.
  apply csubst_mk_true; auto.
Qed.

Lemma lsubstc_mk_less_than_ex {o} :
  forall (a b : @NTerm o) sub,
  forall wf : wf_term (mk_less_than a b),
  forall cv : cover_vars (mk_less_than a b) sub,
  {wa : wf_term a
   & {wb : wf_term b
   & {ca : cover_vars a sub
   & {cb : cover_vars b sub
      & lsubstc (mk_less_than a b) wf sub cv
           = mkc_less_than (lsubstc a wa sub ca)
                           (lsubstc b wb sub cb)}}}}.
Proof.
  introv.
  dup wf as w; apply wf_less_iff in w; repnd.

  dup cv as c.
  rw @cover_vars_eq in c; simpl in c.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  rw subvars_app_l in c; repnd.
  allrw <- @cover_vars_eq.

  assert (cover_vars mk_true sub) as ct.
  { rw @cover_vars_eq; simpl; sp. }

  assert (cover_vars mk_false sub) as cf.
  { rw @cover_vars_eq; simpl; sp. }

  pose proof (lsubstc_mk_less
                a b mk_true mk_false sub
                w0 w1 w2 w wf
                c0 c ct cf cv) as h.

  exists w0 w1 c0 c.
  unfold mk_less_than.
  rw h.
  rw @mkc_less_than_eq.
  rw @lsubstc_mk_false.
  rw @lsubstc_mk_true; auto.
Qed.

Lemma lsubstc_mk_le_ex {o} :
  forall (a b : @NTerm o) sub,
  forall wf : wf_term (mk_le a b),
  forall cv : cover_vars (mk_le a b) sub,
  {wa : wf_term a
   & {wb : wf_term b
   & {ca : cover_vars a sub
   & {cb : cover_vars b sub
      & lsubstc (mk_le a b) wf sub cv
           = mkc_le (lsubstc a wa sub ca)
                    (lsubstc b wb sub cb)}}}}.
Proof.
  introv.

  dup wf as w.
  unfold mk_le in w; rw @wf_not in w.
  dup w as w'.
  apply @wf_less_iff in w'; repnd.

  dup cv as c.
  rw @cover_vars_eq in c; simpl in c.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  rw subvars_app_l in c; repnd.
  allrw <- @cover_vars_eq.

  assert (cover_vars (mk_less_than b a) sub) as c'.
  { rw @cover_vars_eq; simpl; allrw remove_nvars_nil_l; allrw app_nil_r.
    rw subvars_app_l; sp. }

  exists w'1 w'0 c c0.
  pose proof (lsubstc_mk_less_than_ex
                b a sub w c') as h; exrepnd; clear_irr.

  allunfold @mk_le.
  pose proof (lsubstc_mk_not_ex (mk_less_than b a) sub wf cv) as k; exrepnd; clear_irr.
  rw k1; rw h1.
  rw @mkc_le_eq; auto.
Qed.

Lemma lsubstc_mk_minus {o} :
  forall (t : @NTerm o) sub,
  forall w  : wf_term t,
  forall w' : wf_term (mk_minus t),
  forall c  : cover_vars t sub,
  forall c' : cover_vars (mk_minus t) sub,
    lsubstc (mk_minus t) w' sub c'
    = mkc_minus (lsubstc t w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; sp.
Qed.

Lemma lsubstc_mk_minus_ex {o} :
  forall (t : @NTerm o) sub,
  forall w : wf_term (mk_minus t),
  forall c : cover_vars (mk_minus t) sub,
    {w1 : wf_term t
     & {c1 : cover_vars t sub
        & lsubstc (mk_minus t) w sub c
             = mkc_minus (lsubstc t w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term t) as w1.
  { allrw <- @wf_minus_iff; sp. }

  assert (cover_vars t sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_minus.
Qed.

Tactic Notation "one_lift_lsubst2" constr(T) ident(name) tactic(tac) :=
  match T with
    | context [lsubstc (mk_less ?a1 ?a2 ?a3 ?a4) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let w3 := fresh "w3" in
      let w4 := fresh "w4" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      let c3 := fresh "c3" in
      let c4 := fresh "c4" in
      pose proof (lsubstc_mk_less_ex a1 a2 a3 a4 s w c) as name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [w3 name];
        destruct name as [w4 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        destruct name as [c3 name];
        destruct name as [c4 name];
        clear_irr; tac
    | context [lsubstc (mk_less_than ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      pose proof (lsubstc_mk_less_than_ex a b s w c) as name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac
    | context [lsubstc (mk_le ?a ?b) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let w2 := fresh "w2" in
      let c1 := fresh "c1" in
      let c2 := fresh "c2" in
      pose proof (lsubstc_mk_le_ex a b s w c) as name;
        destruct name as [w1 name];
        destruct name as [w2 name];
        destruct name as [c1 name];
        destruct name as [c2 name];
        clear_irr; tac
    | context [lsubstc (mk_minus ?a) ?w ?s ?c] =>
      let w1 := fresh "w1" in
      let c1 := fresh "c1" in
      pose proof (lsubstc_mk_minus_ex a s w c) as name;
        destruct name as [w1 name];
        destruct name as [c1 name];
        clear_irr; tac
    | context [lsubstc mk_tnat ?w ?s ?c] =>
      pose proof (lsubstc_mk_tnat w s c) as name;
        clear_irr; tac
    | context [lsubstc mk_true ?w ?s ?c] =>
      pose proof (lsubstc_mk_true w s c) as name;
        clear_irr; tac
    | context [lsubstc mk_int ?w ?s ?c] =>
      pose proof (lsubstc_mk_int w s c) as name;
        clear_irr; tac
  end.

Lemma subst_mk_lam {o} :
  forall v b x u,
    @isprog o u
    -> v <> x
    -> subst (mk_lam v b) x u = mk_lam v (subst b x u).
Proof.
  introv isp d.
  unfold subst.
  change_to_lsubst_aux4; allsimpl; allrw app_nil_r; allrw disjoint_cons_l; sp.
  boolvar; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
Qed.

Lemma subst_mk_equality {o} :
  forall a b T x u,
    @isprog o u
    -> subst (mk_equality a b T) x u
       = mk_equality (subst a x u) (subst b x u) (subst T x u).
Proof.
  introv isp.
  unfold subst.
  change_to_lsubst_aux4; allsimpl; allrw app_nil_r;
  allrw disjoint_app_l; sp;
  allrw @isprog_eq; allunfold @isprogram; repnd;
  allrw isp0; sp.
Qed.

Lemma subst_mk_tequality {o} :
  forall a b x u,
    @isprog o u
    -> subst (mk_tequality a b) x u
       = mk_tequality (subst a x u) (subst b x u).
Proof.
  introv isp.
  unfold subst.
  change_to_lsubst_aux4; allsimpl; allrw app_nil_r;
  allrw disjoint_app_l; sp;
  allrw @isprog_eq; allunfold @isprogram; repnd;
  allrw isp0; sp.
Qed.

Lemma subst_mk_var1 {o} :
  forall x u, subst (@mk_var o x) x u = u.
Proof.
  introv.
  unfold subst.
  change_to_lsubst_aux4; allsimpl; sp.
  boolvar; sp.
Qed.

Lemma subst_mk_var2 {o} :
  forall v x u, v <> x -> subst (mk_var v) x u = @mk_var o v.
Proof.
  introv.
  unfold subst.
  change_to_lsubst_aux4; allsimpl; sp.
  boolvar; sp.
Qed.

Lemma subst_trivial {o} :
  forall t v u,
    @isprog o u
    -> isprog t
    -> subst t v u = t.
Proof.
  sp; apply lsubst_trivial2; allsimpl; sp; cpx;
  allrw @isprogram_eq; sp.
Qed.

Lemma subst_mk_function {o} :
  forall a v b x u,
    @isprog o u
    -> v <> x
    -> subst (mk_function a v b) x u = mk_function (subst a x u) v (subst b x u).
Proof.
  introv isp d.
  unfold subst.
  change_to_lsubst_aux4; allsimpl; allrw app_nil_r; allrw disjoint_cons_l; sp.
  boolvar; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
Qed.

Lemma subst_mk_function2 {o} :
  forall a v b u,
    @isprog o u
    -> subst (mk_function a v b) v u = mk_function (subst a v u) v b.
Proof.
  introv isp.
  unfold subst.
  change_to_lsubst_aux4; allsimpl; allrw app_nil_r; allrw disjoint_cons_l; sp.
  boolvar; sp; try (rw @lsubst_aux_nil); sp; allrw not_over_or; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
Qed.

Lemma subst_mk_isect {o} :
  forall a v b x u,
    @isprog o u
    -> v <> x
    -> subst (mk_isect a v b) x u = mk_isect (subst a x u) v (subst b x u).
Proof.
  introv isp d.
  unfold subst.
  change_to_lsubst_aux4; allsimpl; allrw app_nil_r; allrw disjoint_cons_l; sp.
  boolvar; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
Qed.

Lemma subst_mk_isect2 {o} :
  forall a v b u,
    @isprog o u
    -> subst (mk_isect a v b) v u = mk_isect (subst a v u) v b.
Proof.
  introv isp.
  unfold subst.
  change_to_lsubst_aux4; allsimpl; allrw app_nil_r; allrw disjoint_cons_l; sp.
  boolvar; sp; try (rw @lsubst_aux_nil); sp; allrw not_over_or; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
  allrw @isprog_eq; allunfold @isprogram; repnd.
  allrw isp0; sp.
Qed.
