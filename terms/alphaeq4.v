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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

 *)


Require Export alphaeq3.
Require Export alphaeq_sub.
Require Export approx_star_props1.
Require Export continuity_defs_ceq.


Lemma in_combine_no_repeats :
  forall (v1 v2 vn : NVar) l1 l2,
    no_repeats l2
    -> LIn (v1, vn) (combine l1 l2)
    -> LIn (v2, vn) (combine l1 l2)
    -> v1 = v2.
Proof.
  induction l1; introv norep i1 i2; allsimpl; tcsp.
  destruct l2; allsimpl; tcsp.
  allrw no_repeats_cons; repnd.
  repndors; ginv; tcsp.
  - apply in_combine in i1; tcsp.
  - apply in_combine in i2; tcsp.
  - eapply IHl1; eauto.
Qed.

Lemma all_vars_lsubst_aux_var_ren_subset {o} :
  forall (t : @NTerm o) vs1 vs2,
    disjoint vs2 (bound_vars t)
    -> length vs1 = length vs2
    -> subset (all_vars (lsubst_aux t (var_ren vs1 vs2)))
              (remove_nvars vs1 (free_vars t) ++ vs2 ++ bound_vars t).
Proof.
  introv disj len.
  unfold all_vars; apply subset_app; dands.
  - eapply subset_trans;[apply free_vars_lsubst_aux_subset|].
    rw @dom_sub_var_ren; auto.
    rw @sub_free_vars_var_ren; auto.
    apply subset_app; dands; eauto 3 with slow.
  - rw @boundvars_lsubst_aux_vars; eauto 3 with slow.
Qed.

Lemma alpha_eq_var_ren {o} :
  forall (t1 t2 : @NTerm o) l1 l2,
    no_repeats l2
    -> length l1 = length l2
    -> disjoint l2 (all_vars t1)
    -> disjoint l2 (all_vars t2)
    -> alpha_eq (lsubst_aux t1 (var_ren l1 l2)) (lsubst_aux t2 (var_ren l1 l2))
    -> alpha_eq t1 t2.
Proof.
  nterm_ind1s t1 as [v1|f1 ind|op1 bs1 ind] Case; introv norep len disj1 disj2 aeq; allsimpl.

  - Case "vterm".
    unfold all_vars in disj1; allsimpl.
    destruct t2 as [v2|f2|op2 bs2]; allsimpl.

    + unfold all_vars in disj2; allsimpl; allrw disjoint_singleton_r.
      remember (sub_find (var_ren l1 l2) v1) as sf1; symmetry in Heqsf1; destruct sf1;
      remember (sub_find (var_ren l1 l2) v2) as sf2; symmetry in Heqsf2; destruct sf2;
      allapply @sub_find_varsub; auto.

      * exrepnd; subst.
        inversion aeq; subst; clear aeq.
        apply (in_combine_no_repeats v1 v2 vn l1 l2) in Heqsf0; auto; subst; auto.

      * exrepnd; subst.
        inversion aeq; subst; clear aeq.
        apply in_combine in Heqsf0; tcsp.

      * exrepnd; subst.
        inversion aeq; subst; clear aeq.
        apply in_combine in Heqsf0; tcsp.

    + remember (sub_find (var_ren l1 l2) v1) as sf1; symmetry in Heqsf1; destruct sf1;
      allapply @sub_find_varsub; exrepnd; subst; auto; inversion aeq.

    + remember (sub_find (var_ren l1 l2) v1) as sf1; symmetry in Heqsf1; destruct sf1;
      allapply @sub_find_varsub; exrepnd; subst; auto; inversion aeq.

  - Case "sterm".
    destruct t2 as [v2|f2|op2 bs2]; allsimpl; try (complete (inversion aeq)); auto.

    remember (sub_find (var_ren l1 l2) v2) as sf1; symmetry in Heqsf1; destruct sf1;
    allapply @sub_find_varsub; exrepnd; subst; auto; inversion aeq.

  - Case "oterm".
    destruct t2 as [v2|f2|op2 bs2]; allsimpl; try (complete (inversion aeq)).

    + remember (sub_find (var_ren l1 l2) v2) as sf; symmetry in Heqsf; destruct sf;
      allapply @sub_find_varsub; exrepnd; subst; auto; inversion aeq.

    + rw @alpha_eq_oterm_combine2 in aeq; allrw map_length; repnd; subst.
      apply alpha_eq_oterm_combine; dands; auto.
      introv i.
      pose proof (aeq (lsubst_bterm_aux b1 (var_ren l1 l2))
                      (lsubst_bterm_aux b2 (var_ren l1 l2))) as h.
      rw <- @map_combine in h.
      rw in_map_iff in h.
      autodimp h hyp.
      { eexists; dands; eauto. }

      destruct b1 as [vs1 t1].
      destruct b2 as [vs2 t2].
      allsimpl.

      pose proof (fresh_vars
                    (length vs1)
                    ((all_vars (lsubst_aux t1 (sub_filter (var_ren l1 l2) vs1)))
                       ++ (all_vars (lsubst_aux t2 (sub_filter (var_ren l1 l2) vs2)))
                       ++ all_vars t1
                       ++ all_vars t2
                       ++ vs1
                       ++ vs2
                       ++ l1
                       ++ l2))
        as fvs.
      exrepnd.
      allrw disjoint_app_r; repnd.

      apply (alphabt_change_var_aux _ _ _ _ lvn) in h; auto;
      try (complete (allrw disjoint_app_r; dands; auto));[].
      repnd.

      apply (al_bterm_aux lvn);
        try (complete (allrw disjoint_app_r; dands; auto));[].

      pose proof (@sub_filter_var_ren_implies o l1 l2 vs1) as vr; exrepnd.
      pose proof (@sub_filter_var_ren_implies o l1 l2 vs2) as vq; exrepnd.
      rw vr0 in h0; rw vq0 in h0.
      autodimp vr1 hyp;[].
      autodimp vq1 hyp;[].
      apply eqvars_is_eqset in vr2.
      apply eqvars_is_eqset in vq2.
      rw subvars_eq in vr3.
      rw subvars_eq in vq3.

      allsimpl.
      applydup in_combine in i; repnd.
      disj_flat_map; allsimpl.
      allrw disjoint_app_r; repnd.

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    t1 (var_ren vs3 vs4) (var_ren vs1 lvn)) as e1.
      repeat (rw @sub_free_vars_var_ren in e1; auto;try lia;[]).
      rw @sub_bound_vars_var_ren in e1.
      rw @dom_sub_var_ren in e1; auto;[].
      repeat (autodimp e1 hyp); eauto 3 with slow.
      { eapply disjoint_eqset_l;[apply eqset_sym;exact vr2|].
        apply disjoint_remove_nvars2; eauto 3 with slow. }

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    t2 (var_ren vs0 vs5) (var_ren vs2 lvn)) as e2.
      repeat (rw @sub_free_vars_var_ren in e2; auto;try lia;[]).
      rw @sub_bound_vars_var_ren in e2.
      rw @dom_sub_var_ren in e2; auto;[].
      repeat (autodimp e2 hyp); eauto 3 with slow.
      { eapply disjoint_eqset_l;[apply eqset_sym;exact vq2|].
        apply disjoint_remove_nvars2; eauto 3 with slow. }

      rw <- e1 in h0; rw <- e2 in h0; clear e1 e2.
      rw @sub_filter_disjoint1 in h0;
        [|rw @dom_sub_var_ren; auto;
          eapply disjoint_eqset_r;[apply eqset_sym;exact vr2|];
          apply disjoint_remove_nvars_l; rw remove_nvars_eq; auto].
      rw @sub_filter_disjoint1 in h0;
        [|rw @dom_sub_var_ren; auto; try lia;
          eapply disjoint_eqset_r;[apply eqset_sym;exact vq2|];
          apply disjoint_remove_nvars_l; rw remove_nvars_eq; auto].

      rw @lsubst_aux_sub_disj_dom2 in h0;
        [|rw @sub_free_vars_var_ren;auto;try lia;[];
          rw @dom_sub_var_ren; auto; try lia;[];
          eapply subset_disjoint;[exact vr3|]; eauto 3 with slow].
      rw @lsubst_aux_sub_disj_dom2 in h0;
        [|rw @sub_free_vars_var_ren;auto;try lia;[];
          rw @dom_sub_var_ren; auto; try lia;[];
          eapply subset_disjoint;[exact vq3|]; eauto 3 with slow].

      pose proof (ind t1 (lsubst_aux t1 (var_ren vs1 lvn)) vs1) as r; clear ind.
      allrw @lsubst_aux_allvars_preserves_osize2.
      repeat (autodimp r hyp); eauto 3 with slow.
      pose proof (r (lsubst_aux t2 (var_ren vs2 lvn)) l1 l2) as ih; clear r.
      repeat (autodimp ih hyp).
      { eapply subset_disjoint_r;[|apply all_vars_lsubst_aux_var_ren_subset; auto];[].
        repeat (rw disjoint_app_r); dands; eauto 3 with slow. }
      { eapply subset_disjoint_r;[|apply all_vars_lsubst_aux_var_ren_subset; auto; try lia];[].
        repeat (rw disjoint_app_r); dands; eauto 3 with slow. }

      rw <- vr0 in h0.
      rw <- vq0 in h0.

      rw @lsubst_aux_sub_filter in h0; auto.
      rw @lsubst_aux_sub_filter in h0; auto.

      { eapply subset_disjoint;[apply free_vars_lsubst_aux_subset|].
        rewrite @dom_sub_var_ren; auto; try lia.
        rw @sub_free_vars_var_ren; auto; try lia.
        apply disjoint_app_l; dands; eauto 3 with slow. }

      { eapply subset_disjoint;[apply free_vars_lsubst_aux_subset|].
        rewrite @dom_sub_var_ren; auto; try lia.
        rw @sub_free_vars_var_ren; auto; try lia.
        apply disjoint_app_l; dands; eauto 3 with slow. }
Qed.

Fixpoint upd_sub {o} (s : @Sub o) v t :=
  match s with
    | [] => []
    | (x,u) :: s =>
      if deq_nvar v x
      then (x,t) :: upd_sub s v t
      else (x,u) :: upd_sub s v t
  end.

Lemma cl_sub_upd_sub {o} :
  forall (s : @Sub o) v t,
    cl_sub s
    -> closed t
    -> cl_sub (upd_sub s v t).
Proof.
  induction s; introv cls clt; allsimpl; eauto 3 with slow.
  destruct a as [x u]; allrw @cl_sub_cons; repnd.
  boolvar; eauto 3 with slow.
Qed.
Hint Resolve cl_sub_upd_sub : slow.

Lemma prog_sub_upd_sub {o} :
  forall (s : @Sub o) v t,
    prog_sub s
    -> isprog t
    -> prog_sub (upd_sub s v t).
Proof.
  induction s; introv cls clt; allsimpl; eauto 3 with slow.
  destruct a as [x u]; allrw @prog_sub_cons; repnd.
  boolvar; eauto 3 with slow.
  apply prog_sub_cons; dands; eauto 3 with slow.
Qed.
Hint Resolve prog_sub_upd_sub : slow.

Lemma dom_sub_upd_sub {o} :
  forall (s : @Sub o) v t,
    dom_sub (upd_sub s v t) = dom_sub s.
Proof.
  induction s; introv; allsimpl; eauto 3 with slow.
  destruct a as [x u]; boolvar; allsimpl; rw IHs; auto.
Qed.
Hint Rewrite @dom_sub_upd_sub : slow.

Lemma sub_find_upd_sub {o} :
  forall (s : @Sub o) v t z,
    sub_find (upd_sub s v t) z
    = if deq_nvar v z
      then if in_deq _ deq_nvar z (dom_sub s)
           then Some t
           else None
      else sub_find s z.
Proof.
  induction s; introv; allsimpl; boolvar; tcsp; destruct a as [x u]; allsimpl; boolvar;
  repndors; subst; GC; tcsp; allsimpl; boolvar; tcsp; GC; allrw not_over_or;
  repnd; tcsp; try (rw IHs); boolvar; tcsp.
Qed.

(* !! MOVE *)
Hint Resolve covered_sub_nil : slow.

Lemma covered_var_ren {o} :
  forall l1 l2 (sub : @Sub o),
    length l1 = length l2
    -> (covered_sub (var_ren l1 l2) sub <=> subset l2 (dom_sub sub)).
Proof.
  induction l1; introv len; allsimpl.
  - unfold var_ren; simpl; cpx.
    split; intro k; eauto 3 with slow.
  - destruct l2; allsimpl; ginv; cpx.
    rw @var_ren_cons.
    rw @covered_sub_cons.
    rw subset_cons_l.
    unfold covered; simpl.
    rw subvars_singleton_l.
    rw (IHl1 l2 sub len); sp.
Qed.

Lemma cl_lsubst_aux_app_weak_r {o} :
  forall (t : @NTerm o) sub1 sub2,
    cl_sub sub1
    -> cl_sub sub2
    -> disjoint (free_vars t) (dom_sub sub1)
    -> lsubst_aux t (sub1 ++ sub2) = lsubst_aux t sub2.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv cl1 cl2 disj; allsimpl; auto.

  - Case "vterm".
    rw @sub_find_app.
    allrw disjoint_singleton_l.
    rw (sub_find_none_if sub1); auto.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t]; allsimpl.
    f_equal.
    rw @sub_filter_app.
    eapply ind; eauto 3 with slow.
    rw <- @dom_sub_sub_filter.
    disj_flat_map; allsimpl.
    apply disjoint_remove_nvars_l; auto.
Qed.

Lemma cl_lsubst_aux_sub_cons_weak {o} :
  forall (s : @Sub o) v t sub,
    cl_sub sub
    -> closed t
    -> !LIn v (sub_free_vars s)
    -> lsubst_aux_sub s ((v, t) :: sub) = lsubst_aux_sub s sub.
Proof.
  induction s as [|p s]; introv cls clt ni; allsimpl; tcsp.
  destruct p as [x u]; allsimpl.
  allrw in_app_iff; allrw not_over_or; repnd.
  rw IHs; auto.
  f_equal; f_equal.
  rw cons_as_app.
  apply cl_lsubst_aux_app_weak_r; simpl; eauto 3 with slow.
  apply disjoint_singleton_r; auto.
Qed.

Lemma cl_lsubst_aux_sub_var_ren_eq_dom {o} :
  forall l1 l2 (sub : @Sub o),
    cl_sub sub
    -> length l1 = length l2
    -> no_repeats l2
    -> l2 = dom_sub sub
    -> lsubst_aux_sub (var_ren l1 l2) sub = combine l1 (range sub).
Proof.
  induction l1 as [|v1 l1 ind]; introv cl len norep e; allsimpl; cpx.
  destruct l2 as [|v2 l2]; allsimpl; cpx.
  destruct sub as [|p sub]; allsimpl; ginv.
  destruct p as [v t]; allsimpl.
  boolvar.
  f_equal.
  try (fold (@var_ren o l1 (dom_sub sub))).
  allrw @no_repeats_cons; repnd.
  allrw @cl_sub_cons; repnd.
  rw @cl_lsubst_aux_sub_cons_weak; eauto 3 with slow.
  rw @sub_free_vars_var_ren; auto.
Qed.

Lemma cl_alphaeq_sub_range_lsubst_aux_sub_var_ren {o} :
  forall l1 l2 lvn (sub1 sub2 : @Sub o),
    cl_sub sub1
    -> cl_sub sub2
    -> length lvn = length l1
    -> length lvn = length l2
    -> alphaeq_sub_range sub1 sub2
    -> lvn = dom_sub sub1
    -> lvn = dom_sub sub2
    -> no_repeats lvn
    -> alphaeq_sub_range (lsubst_aux_sub (var_ren l1 lvn) sub1)
                         (lsubst_aux_sub (var_ren l2 lvn) sub2).
Proof.
  induction l1 as [|v1 l1 ind]; introv cl1 cl2 len1 len2 aeq e1 e2 norep; allsimpl; cpx.

  - destruct sub1; allsimpl; ginv; cpx.

  - destruct lvn as [|v lvn]; allsimpl; ginv; cpx.
    destruct l2 as [|v2 l2]; allsimpl; ginv; cpx.
    destruct sub1 as [|p1 sub1]; allsimpl; ginv.
    destruct sub2 as [|p2 sub2]; allsimpl; ginv.
    destruct p1 as [x1 t1].
    destruct p2 as [x2 t2].
    allsimpl.
    apply cons_inj in e2; repnd; subst.
    inversion aeq as [|? ? ? ? ? ? aeq1 aeq2]; subst; clear aeq.
    boolvar; allsimpl.
    constructor; auto.
    try (fold (@var_ren o l1 (dom_sub sub1))).
    try (fold (@var_ren o l2 (dom_sub sub1))).
    allrw @no_repeats_cons; repnd.
    allrw @cl_sub_cons; repnd.
    repeat (rw @cl_lsubst_aux_sub_cons_weak; auto; try (rw @sub_free_vars_var_ren; auto)).
Qed.

Definition zero_sub {o} (l : list NVar) : @Sub o := map (fun v => (v,mk_zero)) l.

(* !!MOVE *)
Hint Rewrite @dom_sub_ax_sub : slow.

Lemma cl_sub_zero_sub {o} :
  forall l, @cl_sub o (zero_sub l).
Proof.
  induction l; simpl; eauto 3 with slow.
Qed.
Hint Resolve cl_sub_zero_sub : slow.

Lemma dom_sub_zero_sub {o} :
  forall l, @dom_sub o (zero_sub l) = l.
Proof.
  induction l; simpl; eauto 3 with slow.
  f_equal; auto.
Qed.
Hint Rewrite @dom_sub_zero_sub : slow.

Lemma sub_find_zero_sub {o} :
  forall (l : list NVar) (v : NVar),
    @sub_find o (zero_sub l) v =
    (if in_deq NVar deq_nvar v l then Some mk_zero else None).
Proof.
  induction l; introv; simpl; auto.
  boolvar; tcsp; allrw not_over_or; repnd; tcsp; repndors; subst; tcsp;
  rw IHl; boolvar; tcsp.
Qed.

Lemma lsubst_alpha_congr5_aux {o} :
  forall (t1 t2 : @NTerm o) l,
    (forall sub1 sub2,
       cl_sub sub1
       -> cl_sub sub2
       -> alphaeq_sub_range sub1 sub2
       -> l = dom_sub sub1
       -> l = dom_sub sub2
       -> alpha_eq (lsubst_aux t1 sub1) (lsubst_aux t2 sub2))
    -> alpha_eq t1 t2.
Proof.
  nterm_ind1s t1 as [v1|f1 ind|op1 bs1 ind] Case; introv imp; allsimpl; auto.

  - Case "vterm".
    destruct t2 as [v2|f2|op2 bs2].

    + destruct (deq_nvar v1 v2) as [i|i]; subst; eauto 3 with slow;[].
      allsimpl.

      pose proof (imp (upd_sub (ax_sub l) v2 mk_zero) (upd_sub (ax_sub l) v2 mk_zero)) as h.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto;[].

      repeat (rw @sub_find_upd_sub in h).
      repeat (autorewrite with slow in h).
      boolvar.

      * rw @sub_find_ax_sub in h; boolvar; tcsp; try (complete (inversion h)).

      * rw @sub_find_ax_sub in h; boolvar; tcsp; try (complete (inversion h)).

    + pose proof (imp (ax_sub l) (ax_sub l)) as h.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      rw @sub_find_ax_sub in h.
      boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

    + destruct (dec_op_eq_axiom op2) as [d|d].

      * subst.
        pose proof (imp (zero_sub l) (zero_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        rw @sub_find_zero_sub in h.
        boolvar; allsimpl; try (complete (inversion h)).

      * pose proof (imp (ax_sub l) (ax_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        rw @sub_find_ax_sub in h.
        boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

  - Case "sterm".
    pose proof (imp (ax_sub l) (ax_sub l)) as h; clear imp.
    repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.

    destruct t2 as [v2|f2|op2 bs2]; allsimpl; try (complete (inversion h)); auto.
    rw @sub_find_ax_sub in h.
    boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

  - Case "oterm".
    destruct t2 as [v2|f2|op2 bs2].

    + destruct (dec_op_eq_axiom op1) as [d|d].

      * subst.
        pose proof (imp (zero_sub l) (zero_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        allsimpl.
        rw @sub_find_zero_sub in h.
        boolvar; allsimpl; try (complete (inversion h)).

      * pose proof (imp (ax_sub l) (ax_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        allsimpl.
        rw @sub_find_ax_sub in h.
        boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

    + pose proof (imp (ax_sub l) (ax_sub l)) as h.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl; inversion h.

    + pose proof (imp (ax_sub l) (ax_sub l)) as h.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl.
      rw @alpha_eq_oterm_combine2 in h; repnd; subst.
      allrw map_length.
      allrw <- @map_combine.
      apply alpha_eq_oterm_combine; dands; auto.
      introv i.
      destruct b1 as [l1 t1].
      destruct b2 as [l2 t2].
      applydup in_combine in i; repnd.
      pose proof (fresh_vars (length l1) (l ++ all_vars t1 ++ all_vars t2)) as fv.
      exrepnd.
      allrw disjoint_app_r; repnd.
      apply (al_bterm_aux lvn); auto; try lia.
      { allrw disjoint_app_r; dands; auto. }
      { pose proof (h (lsubst_bterm_aux (bterm l1 t1) (ax_sub l))
                      (lsubst_bterm_aux (bterm l2 t2) (ax_sub l))) as q.
        allsimpl; allrw in_map_iff.
        autodimp q hyp.
        { eexists; dands; eauto. }
        inversion q; subst; auto. }

      pose proof (ind t1 (lsubst_aux t1 (var_ren l1 lvn)) l1) as r; clear ind.
      allrw @lsubst_aux_allvars_preserves_osize2.
      repeat (autodimp r hyp); eauto 3 with slow.
      pose proof (r (lsubst_aux t2 (var_ren l2 lvn)) l) as ih; clear r.
      repeat (autodimp ih hyp).

      introv cl1 cl2 aeqs ld1 ld2.
      pose proof (imp sub1 sub2 cl1 cl2 aeqs ld1 ld2) as r; clear imp.
      rw @alpha_eq_oterm_combine in r; repnd; subst.
      allrw map_length; GC.
      pose proof (r (lsubst_bterm_aux (bterm l1 t1) sub1)
                    (lsubst_bterm_aux (bterm l2 t2) sub2)) as q.
      autodimp q hyp.
      { rw <- @map_combine; rw in_map_iff.
        eexists; dands; eauto. }
      allsimpl.

      pose proof (fresh_vars (length l1)
                             ((all_vars (lsubst_aux t1 (sub_filter sub1 l1)))
                                ++ (all_vars (lsubst_aux t2 (sub_filter sub2 l2)))
                                ++ (all_vars (lsubst_aux (lsubst_aux t1 (var_ren l1 lvn)) sub1))
                                ++ (all_vars (lsubst_aux (lsubst_aux t2 (var_ren l2 lvn)) sub2))
                                ++ (dom_sub (sub_filter sub1 l1))
                                ++ (bound_vars t1)
                                ++ (sub_bound_vars (sub_filter sub1 l1))
                                ++ (dom_sub (sub_filter sub2 l2))
                                ++ (bound_vars t2)
                                ++ (sub_bound_vars (sub_filter sub2 l2))
                                ++ (bound_vars (lsubst_aux t1 (var_ren l1 lvn)))
                                ++ (bound_vars (lsubst_aux t2 (var_ren l2 lvn)))
                                ++ sub_bound_vars sub1
                                ++ sub_bound_vars sub2
                                ++ dom_sub sub1
                                ++ dom_sub sub2))
        as fvs; exrepnd.
      allrw disjoint_app_r; repnd.

      apply (alphabt_change_var_aux _ _ _ _ lvn0) in q; repnd; GC; auto;
      allrw disjoint_app_r; tcsp;[].

      apply (alpha_eq_var_ren _ _ lvn lvn0); auto; try lia;
      try (complete (allrw disjoint_app_r; tcsp)).

      assert (disjoint lvn (dom_sub sub2)) as dlvn2.
      { rw <- ld2; auto. }

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    (lsubst_aux t1 (var_ren l1 lvn))
                    sub1
                    (var_ren lvn lvn0)) as e1.
      rw @sub_free_vars_var_ren in e1; auto; try lia;[].
      rw @sub_free_vars_if_cl_sub in e1; auto;[].
      rw @cl_lsubst_aux_sub_trivial in e1; auto;[].
      rw @sub_filter_disjoint in e1; auto; try lia;[].
      rw @lsubst_aux_nest_vars_same in e1; auto; try lia;
      [|apply disjoint_app_l; dands; eauto 3 with slow];[].
      repeat (autodimp e1 hyp); eauto 2 with slow.

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    (lsubst_aux t2 (var_ren l2 lvn))
                    sub2
                    (var_ren lvn lvn0)) as e2.
      rw @sub_free_vars_var_ren in e2; auto; try lia;[].
      rw @sub_free_vars_if_cl_sub in e2; auto;[].
      rw @cl_lsubst_aux_sub_trivial in e2; auto;[].
      rw @sub_filter_disjoint in e2; auto; try lia;[].
      rw @lsubst_aux_nest_vars_same in e2; auto; try lia;
      [|apply disjoint_app_l; dands; eauto 3 with slow];[].
      repeat (autodimp e2 hyp); eauto 2 with slow.

      rw <- e1; rw <- e2; clear e1 e2.

      pose proof (simple_lsubst_aux_lsubst_aux_sub t1 (var_ren l1 lvn0) sub1) as e1.
      rw @sub_free_vars_var_ren in e1; auto;try lia;[].
      repeat (autodimp e1 hyp); eauto 2 with slow;[].

      pose proof (simple_lsubst_aux_lsubst_aux_sub t2 (var_ren l2 lvn0) sub2) as e2.
      rw @sub_free_vars_var_ren in e2; auto;try lia;[].
      repeat (autodimp e2 hyp); eauto 2 with slow;[].

      rw <- e1; rw <- e2; clear e1 e2.
      repeat (rw @dom_sub_var_ren; try lia;[]).

      rw @lsubst_aux_sub_disj_dom2;[|rw @sub_free_vars_var_ren; auto; try lia].
      rw @lsubst_aux_sub_disj_dom2;[|rw @sub_free_vars_var_ren; auto; try lia].
      auto.
Qed.

Lemma lsubst_alpha_congr5 {o} :
  forall (l1 l2 : list NVar) (t1 t2 : @NTerm o),
    length l1 = length l2
    -> (forall sub1 sub2,
          cl_sub sub1
          -> cl_sub sub2
          -> alphaeq_sub_range sub1 sub2
          -> l1 = dom_sub sub1
          -> l2 = dom_sub sub2
          -> alpha_eq (lsubst_aux t1 sub1) (lsubst_aux t2 sub2))
    -> alpha_eq_bterm (bterm l1 t1) (bterm l2 t2).
Proof.
  introv len imp.
  pose proof (fresh_vars (length l1) (l1 ++ l2 ++ all_vars t1 ++ all_vars t2)) as fv.
  exrepnd.
  allrw disjoint_app_r; repnd; auto.
  apply (al_bterm_aux lvn); auto.
  { allrw disjoint_app_r; dands; auto. }

  apply (lsubst_alpha_congr5_aux _ _ lvn).
  introv cl1 cl2 aeqs e1 e2.

  pose proof (simple_lsubst_aux_lsubst_aux_sub
                 t1 (var_ren l1 lvn) sub1) as x1.
  rw @sub_free_vars_var_ren in x1; auto.
  rw @dom_sub_var_ren in x1; auto.
  rw (lsubst_aux_trivial_cl t1 (sub_filter sub1 l1)) in x1; eauto 3 with slow;
  [|rw <- @dom_sub_sub_filter; apply disjoint_remove_nvars2; subst; auto];[].
  repeat (autodimp x1 hyp); eauto 3 with slow.

  pose proof (simple_lsubst_aux_lsubst_aux_sub
                 t2 (var_ren l2 lvn) sub2) as x2.
  rw @sub_free_vars_var_ren in x2; auto; try lia.
  rw @dom_sub_var_ren in x2; auto; try lia.
  rw (lsubst_aux_trivial_cl t2 (sub_filter sub2 l2)) in x2; eauto 3 with slow; try lia;
  [|rw <- @dom_sub_sub_filter; apply disjoint_remove_nvars2; subst; rw <- e2; auto].
  repeat (autodimp x2 hyp); eauto 3 with slow.

  rw <- x1; rw <- x2; clear x1 x2.

  apply imp; eauto 3 with slow.

  - apply implies_cl_sub_lsubst_aux_sub; auto.
    apply covered_var_ren; auto; try lia.
    rw e1; auto.

  - apply implies_cl_sub_lsubst_aux_sub; auto.
    apply covered_var_ren; auto; try lia.
    rw e2; auto.

  - apply cl_alphaeq_sub_range_lsubst_aux_sub_var_ren; eauto 3 with slow; try lia.

  - rw @dom_sub_lsubst_aux_sub.
    rw @dom_sub_var_ren; auto.

  - rw @dom_sub_lsubst_aux_sub.
    rw @dom_sub_var_ren; auto; try lia.
Qed.

Lemma lsubst_alpha_congr6_aux {o} :
  forall (t1 t2 : @NTerm o) l,
    (forall sub,
       cl_sub sub
       -> l = dom_sub sub
       -> alpha_eq (lsubst_aux t1 sub) (lsubst_aux t2 sub))
    -> alpha_eq t1 t2.
Proof.
  nterm_ind1s t1 as [v1|f1 ind|op1 bs1 ind] Case; introv imp; allsimpl.

  - Case "vterm".
    destruct t2 as [v2|f2|op2 bs2].

    + destruct (deq_nvar v1 v2) as [i|i]; subst; eauto 3 with slow;[].
      allsimpl.

      pose proof (imp (upd_sub (ax_sub l) v2 mk_zero)) as h.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto;[].

      repeat (rw @sub_find_upd_sub in h).
      repeat (autorewrite with slow in h).
      boolvar.

      * rw @sub_find_ax_sub in h; boolvar; tcsp; try (complete (inversion h)).

      * rw @sub_find_ax_sub in h; boolvar; tcsp; try (complete (inversion h)).

    + pose proof (imp (ax_sub l)) as h; clear imp.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl.
      allrw @sub_find_ax_sub.
      boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

    + destruct (dec_op_eq_axiom op2) as [d|d].

      * subst.
        pose proof (imp (zero_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        rw @sub_find_zero_sub in h.
        boolvar; allsimpl; try (complete (inversion h)).

      * pose proof (imp (ax_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        rw @sub_find_ax_sub in h.
        boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

  - Case "sterm".

    pose proof (imp (ax_sub l)) as h; clear imp.
    repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
    destruct t2 as [v2|f2|op2 bs2]; allsimpl; try (complete (inversion h)); auto.
    allrw @sub_find_ax_sub.
    boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

  - Case "oterm".
    destruct t2 as [v2|f2|op2 bs2].

    + destruct (dec_op_eq_axiom op1) as [d|d].

      * subst.
        pose proof (imp (zero_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        allsimpl.
        rw @sub_find_zero_sub in h.
        boolvar; allsimpl; try (complete (inversion h)).

      * pose proof (imp (ax_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        allsimpl.
        rw @sub_find_ax_sub in h.
        boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

    + pose proof (imp (ax_sub l)) as h; clear imp.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl; try (complete (inversion h; subst; tcsp)).

    + pose proof (imp (ax_sub l)) as h.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl.
      rw @alpha_eq_oterm_combine2 in h; repnd; subst.
      allrw map_length.
      allrw <- @map_combine.
      apply alpha_eq_oterm_combine; dands; auto.
      introv i.
      destruct b1 as [l1 t1].
      destruct b2 as [l2 t2].
      applydup in_combine in i; repnd.
      pose proof (fresh_vars (length l1) (l ++ all_vars t1 ++ all_vars t2)) as fv.
      exrepnd.
      allrw disjoint_app_r; repnd.
      apply (al_bterm_aux lvn); auto; try lia.
      { allrw disjoint_app_r; dands; auto. }
      { pose proof (h (lsubst_bterm_aux (bterm l1 t1) (ax_sub l))
                      (lsubst_bterm_aux (bterm l2 t2) (ax_sub l))) as q.
        allsimpl; allrw in_map_iff.
        autodimp q hyp.
        { eexists; dands; eauto. }
        inversion q; subst; auto. }

      pose proof (ind t1 (lsubst_aux t1 (var_ren l1 lvn)) l1) as r; clear ind.
      allrw @lsubst_aux_allvars_preserves_osize2.
      repeat (autodimp r hyp); eauto 3 with slow.
      pose proof (r (lsubst_aux t2 (var_ren l2 lvn)) l) as ih; clear r.
      repeat (autodimp ih hyp).

      introv cl ld.
      pose proof (imp sub cl ld) as r; clear imp.
      rw @alpha_eq_oterm_combine in r; repnd; subst.
      allrw map_length; GC.
      pose proof (r (lsubst_bterm_aux (bterm l1 t1) sub)
                    (lsubst_bterm_aux (bterm l2 t2) sub)) as q.
      autodimp q hyp.
      { rw <- @map_combine; rw in_map_iff.
        eexists; dands; eauto. }
      allsimpl.

      pose proof (fresh_vars (length l1)
                             ((all_vars (lsubst_aux t1 (sub_filter sub l1)))
                                ++ (all_vars (lsubst_aux t2 (sub_filter sub l2)))
                                ++ (all_vars (lsubst_aux (lsubst_aux t1 (var_ren l1 lvn)) sub))
                                ++ (all_vars (lsubst_aux (lsubst_aux t2 (var_ren l2 lvn)) sub))
                                ++ (dom_sub (sub_filter sub l1))
                                ++ (bound_vars t1)
                                ++ (sub_bound_vars (sub_filter sub l1))
                                ++ (dom_sub (sub_filter sub l2))
                                ++ (bound_vars t2)
                                ++ (sub_bound_vars (sub_filter sub l2))
                                ++ (bound_vars (lsubst_aux t1 (var_ren l1 lvn)))
                                ++ (bound_vars (lsubst_aux t2 (var_ren l2 lvn)))
                                ++ sub_bound_vars sub
                                ++ dom_sub sub))
        as fvs; exrepnd.
      allrw disjoint_app_r; repnd.

      apply (alphabt_change_var_aux _ _ _ _ lvn0) in q; repnd; GC; auto;
      allrw disjoint_app_r; tcsp;[].

      apply (alpha_eq_var_ren _ _ lvn lvn0); auto; try lia;
      try (complete (allrw disjoint_app_r; tcsp)).

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    (lsubst_aux t1 (var_ren l1 lvn))
                    sub
                    (var_ren lvn lvn0)) as e1.
      rw @sub_free_vars_var_ren in e1; auto; try lia;[].
      rw @sub_free_vars_if_cl_sub in e1; auto;[].
      rw @cl_lsubst_aux_sub_trivial in e1; auto;[].
      rw @sub_filter_disjoint in e1; auto; try lia;[].
      rw @lsubst_aux_nest_vars_same in e1; auto; try lia;
      [|apply disjoint_app_l; dands; eauto 3 with slow];[].
      repeat (autodimp e1 hyp); eauto 2 with slow.

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    (lsubst_aux t2 (var_ren l2 lvn))
                    sub
                    (var_ren lvn lvn0)) as e2.
      rw @sub_free_vars_var_ren in e2; auto; try lia;[].
      rw @sub_free_vars_if_cl_sub in e2; auto;[].
      rw @cl_lsubst_aux_sub_trivial in e2; auto;[].
      rw @sub_filter_disjoint in e2; auto; try lia;[].
      rw @lsubst_aux_nest_vars_same in e2; auto; try lia;
      [|apply disjoint_app_l; dands; eauto 3 with slow];[].
      repeat (autodimp e2 hyp); eauto 2 with slow.

      rw <- e1; rw <- e2; clear e1 e2.

      pose proof (simple_lsubst_aux_lsubst_aux_sub t1 (var_ren l1 lvn0) sub) as e1.
      rw @sub_free_vars_var_ren in e1; auto;try lia;[].
      repeat (autodimp e1 hyp); eauto 2 with slow;[].

      pose proof (simple_lsubst_aux_lsubst_aux_sub t2 (var_ren l2 lvn0) sub) as e2.
      rw @sub_free_vars_var_ren in e2; auto;try lia;[].
      repeat (autodimp e2 hyp); eauto 2 with slow;[].

      rw <- e1; rw <- e2; clear e1 e2.
      repeat (rw @dom_sub_var_ren; try lia;[]).

      rw @lsubst_aux_sub_disj_dom2;[|rw @sub_free_vars_var_ren; auto; try lia].
      rw @lsubst_aux_sub_disj_dom2;[|rw @sub_free_vars_var_ren; auto; try lia].
      auto.
Qed.

Lemma lsubst_alpha_congr7_aux {o} :
  forall (t1 t2 : @NTerm o) l,
    (forall sub1 sub2,
       cl_sub sub1
       -> cl_sub sub2
       -> range sub1 = range sub2
       -> l = dom_sub sub1
       -> l = dom_sub sub2
       -> alpha_eq (lsubst_aux t1 sub1) (lsubst_aux t2 sub2))
    -> alpha_eq t1 t2.
Proof.
  nterm_ind1s t1 as [v1|f1 ind|op1 bs1 ind] Case; introv imp; allsimpl.

  - Case "vterm".
    destruct t2 as [v2|f2|op2 bs2].

    + destruct (deq_nvar v1 v2) as [i|i]; subst; eauto 3 with slow;[].
      allsimpl.

      pose proof (imp (upd_sub (ax_sub l) v2 mk_zero) (upd_sub (ax_sub l) v2 mk_zero)) as h.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto;[].

      repeat (rw @sub_find_upd_sub in h).
      repeat (autorewrite with slow in h).
      boolvar.

      * rw @sub_find_ax_sub in h; boolvar; tcsp; try (complete (inversion h)).

      * rw @sub_find_ax_sub in h; boolvar; tcsp; try (complete (inversion h)).

    + pose proof (imp (ax_sub l) (ax_sub l)) as h; clear imp.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl.
      allrw @sub_find_ax_sub.
      boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

    + destruct (dec_op_eq_axiom op2) as [d|d].

      * subst.
        pose proof (imp (zero_sub l) (zero_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        rw @sub_find_zero_sub in h.
        boolvar; allsimpl; try (complete (inversion h)).

      * pose proof (imp (ax_sub l) (ax_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        rw @sub_find_ax_sub in h.
        boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

  - Case "sterm".
    pose proof (imp (ax_sub l) (ax_sub l)) as h; clear imp.
    repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
    allsimpl.
    destruct t2 as [v2|f2|op2 bs2]; try (complete (inversion h)); auto.
    allsimpl.
    allrw @sub_find_ax_sub.
    boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

  - Case "oterm".
    destruct t2 as [v2|f2|op2 bs2].

    + destruct (dec_op_eq_axiom op1) as [d|d].

      * subst.
        pose proof (imp (zero_sub l) (zero_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        allsimpl.
        rw @sub_find_zero_sub in h.
        boolvar; allsimpl; try (complete (inversion h)).

      * pose proof (imp (ax_sub l) (ax_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        allsimpl.
        rw @sub_find_ax_sub in h.
        boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

    + pose proof (imp (ax_sub l) (ax_sub l)) as h; clear imp.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl.
      allrw @sub_find_ax_sub.
      boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

    + pose proof (imp (ax_sub l) (ax_sub l)) as h.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl.
      rw @alpha_eq_oterm_combine2 in h; repnd; subst.
      allrw map_length.
      allrw <- @map_combine.
      apply alpha_eq_oterm_combine; dands; auto.
      introv i.
      destruct b1 as [l1 t1].
      destruct b2 as [l2 t2].
      applydup in_combine in i; repnd.
      pose proof (fresh_vars (length l1) (l ++ all_vars t1 ++ all_vars t2)) as fv.
      exrepnd.
      allrw disjoint_app_r; repnd.
      apply (al_bterm_aux lvn); auto; try lia.
      { allrw disjoint_app_r; dands; auto. }
      { pose proof (h (lsubst_bterm_aux (bterm l1 t1) (ax_sub l))
                      (lsubst_bterm_aux (bterm l2 t2) (ax_sub l))) as q.
        allsimpl; allrw in_map_iff.
        autodimp q hyp.
        { eexists; dands; eauto. }
        inversion q; subst; auto. }

      pose proof (ind t1 (lsubst_aux t1 (var_ren l1 lvn)) l1) as r; clear ind.
      allrw @lsubst_aux_allvars_preserves_osize2.
      repeat (autodimp r hyp); eauto 3 with slow.
      pose proof (r (lsubst_aux t2 (var_ren l2 lvn)) l) as ih; clear r.
      repeat (autodimp ih hyp).

      introv cl1 cl2 aeqs ld1 ld2.
      pose proof (imp sub1 sub2 cl1 cl2 aeqs ld1 ld2) as r; clear imp.
      rw @alpha_eq_oterm_combine in r; repnd; subst.
      allrw map_length; GC.
      pose proof (r (lsubst_bterm_aux (bterm l1 t1) sub1)
                    (lsubst_bterm_aux (bterm l2 t2) sub2)) as q.
      autodimp q hyp.
      { rw <- @map_combine; rw in_map_iff.
        eexists; dands; eauto. }
      allsimpl.

      pose proof (fresh_vars (length l1)
                             ((all_vars (lsubst_aux t1 (sub_filter sub1 l1)))
                                ++ (all_vars (lsubst_aux t2 (sub_filter sub2 l2)))
                                ++ (all_vars (lsubst_aux (lsubst_aux t1 (var_ren l1 lvn)) sub1))
                                ++ (all_vars (lsubst_aux (lsubst_aux t2 (var_ren l2 lvn)) sub2))
                                ++ (dom_sub (sub_filter sub1 l1))
                                ++ (bound_vars t1)
                                ++ (sub_bound_vars (sub_filter sub1 l1))
                                ++ (dom_sub (sub_filter sub2 l2))
                                ++ (bound_vars t2)
                                ++ (sub_bound_vars (sub_filter sub2 l2))
                                ++ (bound_vars (lsubst_aux t1 (var_ren l1 lvn)))
                                ++ (bound_vars (lsubst_aux t2 (var_ren l2 lvn)))
                                ++ sub_bound_vars sub1
                                ++ sub_bound_vars sub2
                                ++ dom_sub sub1
                                ++ dom_sub sub2))
        as fvs; exrepnd.
      allrw disjoint_app_r; repnd.

      apply (alphabt_change_var_aux _ _ _ _ lvn0) in q; repnd; GC; auto;
      allrw disjoint_app_r; tcsp;[].

      apply (alpha_eq_var_ren _ _ lvn lvn0); auto; try lia;
      try (complete (allrw disjoint_app_r; tcsp)).

      assert (disjoint lvn (dom_sub sub2)) as dlvn2.
      { rw <- ld2; auto. }

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    (lsubst_aux t1 (var_ren l1 lvn))
                    sub1
                    (var_ren lvn lvn0)) as e1.
      rw @sub_free_vars_var_ren in e1; auto; try lia;[].
      rw @sub_free_vars_if_cl_sub in e1; auto;[].
      rw @cl_lsubst_aux_sub_trivial in e1; auto;[].
      rw @sub_filter_disjoint in e1; auto; try lia;[].
      rw @lsubst_aux_nest_vars_same in e1; auto; try lia;
      [|apply disjoint_app_l; dands; eauto 3 with slow];[].
      repeat (autodimp e1 hyp); eauto 2 with slow.

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    (lsubst_aux t2 (var_ren l2 lvn))
                    sub2
                    (var_ren lvn lvn0)) as e2.
      rw @sub_free_vars_var_ren in e2; auto; try lia;[].
      rw @sub_free_vars_if_cl_sub in e2; auto;[].
      rw @cl_lsubst_aux_sub_trivial in e2; auto;[].
      rw @sub_filter_disjoint in e2; auto; try lia;[].
      rw @lsubst_aux_nest_vars_same in e2; auto; try lia;
      [|apply disjoint_app_l; dands; eauto 3 with slow];[].
      repeat (autodimp e2 hyp); eauto 2 with slow.

      rw <- e1; rw <- e2; clear e1 e2.

      pose proof (simple_lsubst_aux_lsubst_aux_sub t1 (var_ren l1 lvn0) sub1) as e1.
      rw @sub_free_vars_var_ren in e1; auto;try lia;[].
      repeat (autodimp e1 hyp); eauto 2 with slow;[].

      pose proof (simple_lsubst_aux_lsubst_aux_sub t2 (var_ren l2 lvn0) sub2) as e2.
      rw @sub_free_vars_var_ren in e2; auto;try lia;[].
      repeat (autodimp e2 hyp); eauto 2 with slow;[].

      rw <- e1; rw <- e2; clear e1 e2.
      repeat (rw @dom_sub_var_ren; try lia;[]).

      rw @lsubst_aux_sub_disj_dom2;[|rw @sub_free_vars_var_ren; auto; try lia].
      rw @lsubst_aux_sub_disj_dom2;[|rw @sub_free_vars_var_ren; auto; try lia].
      auto.
Qed.

Lemma lsubst_alpha_congr7 {o} :
  forall (l1 l2 : list NVar) (t1 t2 : @NTerm o),
    length l1 = length l2
    -> (forall sub1 sub2,
          cl_sub sub1
          -> cl_sub sub2
          -> range sub1 = range sub2
          -> l1 = dom_sub sub1
          -> l2 = dom_sub sub2
          -> alpha_eq (lsubst_aux t1 sub1) (lsubst_aux t2 sub2))
    -> alpha_eq_bterm (bterm l1 t1) (bterm l2 t2).
Proof.
  introv len imp.
  pose proof (fresh_vars (length l1) (l1 ++ l2 ++ all_vars t1 ++ all_vars t2)) as fv.
  exrepnd.
  allrw disjoint_app_r; repnd; auto.
  apply (al_bterm_aux lvn); auto.
  { allrw disjoint_app_r; dands; auto. }

  apply (lsubst_alpha_congr7_aux _ _ lvn).
  introv cl1 cl2 aeqs e1 e2.

  pose proof (simple_lsubst_aux_lsubst_aux_sub
                 t1 (var_ren l1 lvn) sub1) as x1.
  rw @sub_free_vars_var_ren in x1; auto.
  rw @dom_sub_var_ren in x1; auto.
  rw (lsubst_aux_trivial_cl t1 (sub_filter sub1 l1)) in x1; eauto 3 with slow;
  [|rw <- @dom_sub_sub_filter; apply disjoint_remove_nvars2; subst; auto];[].
  repeat (autodimp x1 hyp); eauto 3 with slow.

  pose proof (simple_lsubst_aux_lsubst_aux_sub
                 t2 (var_ren l2 lvn) sub2) as x2.
  rw @sub_free_vars_var_ren in x2; auto; try lia.
  rw @dom_sub_var_ren in x2; auto; try lia.
  rw (lsubst_aux_trivial_cl t2 (sub_filter sub2 l2)) in x2; eauto 3 with slow; try lia;
  [|rw <- @dom_sub_sub_filter; apply disjoint_remove_nvars2; subst; rw <- e2; auto].
  repeat (autodimp x2 hyp); eauto 3 with slow.

  rw <- x1; rw <- x2; clear x1 x2.

  apply imp; eauto 3 with slow.

  - apply implies_cl_sub_lsubst_aux_sub; auto.
    apply covered_var_ren; auto; try lia.
    rw e1; auto.

  - apply implies_cl_sub_lsubst_aux_sub; auto.
    apply covered_var_ren; auto; try lia.
    rw e2; auto.

  - repeat (rw @cl_lsubst_aux_sub_var_ren_eq_dom; auto; try lia).
    repeat (rw @range_combine); auto; rw @length_range; subst;
    allrw @length_dom; auto.
    rw <- @length_dom; rw <- e2; rw @length_dom; rw <- len; auto.

  - rw @dom_sub_lsubst_aux_sub.
    rw @dom_sub_var_ren; auto.

  - rw @dom_sub_lsubst_aux_sub.
    rw @dom_sub_var_ren; auto; try lia.
Qed.

Lemma prog_sub_zero_sub {o} :
  forall l, @prog_sub o (zero_sub l).
Proof.
  induction l; allsimpl; eauto 3 with slow.
Qed.
Hint Resolve prog_sub_zero_sub : slow.

Lemma lsubst_alpha_congr8_aux {o} :
  forall (t1 t2 : @NTerm o) l,
    (forall sub1 sub2,
       prog_sub sub1
       -> prog_sub sub2
       -> range sub1 = range sub2
       -> l = dom_sub sub1
       -> l = dom_sub sub2
       -> alpha_eq (lsubst_aux t1 sub1) (lsubst_aux t2 sub2))
    -> alpha_eq t1 t2.
Proof.
  nterm_ind1s t1 as [v1|f1 ind|op1 bs1 ind] Case; introv imp; allsimpl.

  - Case "vterm".
    destruct t2 as [v2|f2|op2 bs2].

    + destruct (deq_nvar v1 v2) as [i|i]; subst; eauto 3 with slow;[].
      allsimpl.

      pose proof (imp (upd_sub (ax_sub l) v2 mk_zero) (upd_sub (ax_sub l) v2 mk_zero)) as h.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.

      repeat (rw @sub_find_upd_sub in h).
      repeat (autorewrite with slow in h).
      boolvar.

      * rw @sub_find_ax_sub in h; boolvar; tcsp; try (complete (inversion h)).

      * rw @sub_find_ax_sub in h; boolvar; tcsp; try (complete (inversion h)).

    + pose proof (imp (ax_sub l) (ax_sub l)) as h; clear imp.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl.
      allrw @sub_find_ax_sub.
      boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

    + destruct (dec_op_eq_axiom op2) as [d|d].

      * subst.
        pose proof (imp (zero_sub l) (zero_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        rw @sub_find_zero_sub in h.
        boolvar; allsimpl; try (complete (inversion h)).

      * pose proof (imp (ax_sub l) (ax_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        rw @sub_find_ax_sub in h.
        boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

  - Case "sterm".
    pose proof (imp (ax_sub l) (ax_sub l)) as h; clear imp.
    repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
    allsimpl.
    destruct t2 as [v2|f2|op2 bs2]; try (complete (inversion h)); auto.
    allsimpl.
    allrw @sub_find_ax_sub.
    boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

  - Case "oterm".
    destruct t2 as [v2|f2|op2 bs2].

    + destruct (dec_op_eq_axiom op1) as [d|d].

      * subst.
        pose proof (imp (zero_sub l) (zero_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        allsimpl.
        rw @sub_find_zero_sub in h.
        boolvar; allsimpl; try (complete (inversion h)).

      * pose proof (imp (ax_sub l) (ax_sub l)) as h.
        repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
        allsimpl.
        rw @sub_find_ax_sub in h.
        boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

    + pose proof (imp (ax_sub l) (ax_sub l)) as h; clear imp.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl.
      allrw @sub_find_ax_sub.
      boolvar; allsimpl; try (complete (inversion h; subst; tcsp)).

    + pose proof (imp (ax_sub l) (ax_sub l)) as h.
      repeat (autodimp h hyp); eauto 3 with slow; autorewrite with slow; auto.
      allsimpl.
      rw @alpha_eq_oterm_combine2 in h; repnd; subst.
      allrw map_length.
      allrw <- @map_combine.
      apply alpha_eq_oterm_combine; dands; auto.
      introv i.
      destruct b1 as [l1 t1].
      destruct b2 as [l2 t2].
      applydup in_combine in i; repnd.
      pose proof (fresh_vars (length l1) (l ++ all_vars t1 ++ all_vars t2)) as fv.
      exrepnd.
      allrw disjoint_app_r; repnd.
      apply (al_bterm_aux lvn); auto; try lia.
      { allrw disjoint_app_r; dands; auto. }
      { pose proof (h (lsubst_bterm_aux (bterm l1 t1) (ax_sub l))
                      (lsubst_bterm_aux (bterm l2 t2) (ax_sub l))) as q.
        allsimpl; allrw in_map_iff.
        autodimp q hyp.
        { eexists; dands; eauto. }
        inversion q; subst; auto. }

      pose proof (ind t1 (lsubst_aux t1 (var_ren l1 lvn)) l1) as r; clear ind.
      allrw @lsubst_aux_allvars_preserves_osize2.
      repeat (autodimp r hyp); eauto 3 with slow.
      pose proof (r (lsubst_aux t2 (var_ren l2 lvn)) l) as ih; clear r.
      repeat (autodimp ih hyp).

      introv cl1 cl2 aeqs ld1 ld2.
      pose proof (imp sub1 sub2 cl1 cl2 aeqs ld1 ld2) as r; clear imp.
      rw @alpha_eq_oterm_combine in r; repnd; subst.
      allrw map_length; GC.
      pose proof (r (lsubst_bterm_aux (bterm l1 t1) sub1)
                    (lsubst_bterm_aux (bterm l2 t2) sub2)) as q.
      autodimp q hyp.
      { rw <- @map_combine; rw in_map_iff.
        eexists; dands; eauto. }
      allsimpl.

      pose proof (fresh_vars (length l1)
                             ((all_vars (lsubst_aux t1 (sub_filter sub1 l1)))
                                ++ (all_vars (lsubst_aux t2 (sub_filter sub2 l2)))
                                ++ (all_vars (lsubst_aux (lsubst_aux t1 (var_ren l1 lvn)) sub1))
                                ++ (all_vars (lsubst_aux (lsubst_aux t2 (var_ren l2 lvn)) sub2))
                                ++ (dom_sub (sub_filter sub1 l1))
                                ++ (bound_vars t1)
                                ++ (sub_bound_vars (sub_filter sub1 l1))
                                ++ (dom_sub (sub_filter sub2 l2))
                                ++ (bound_vars t2)
                                ++ (sub_bound_vars (sub_filter sub2 l2))
                                ++ (bound_vars (lsubst_aux t1 (var_ren l1 lvn)))
                                ++ (bound_vars (lsubst_aux t2 (var_ren l2 lvn)))
                                ++ sub_bound_vars sub1
                                ++ sub_bound_vars sub2
                                ++ dom_sub sub1
                                ++ dom_sub sub2))
        as fvs; exrepnd.
      allrw disjoint_app_r; repnd.

      apply (alphabt_change_var_aux _ _ _ _ lvn0) in q; repnd; GC; auto;
      allrw disjoint_app_r; tcsp;[].

      apply (alpha_eq_var_ren _ _ lvn lvn0); auto; try lia;
      try (complete (allrw disjoint_app_r; tcsp)).

      assert (disjoint lvn (dom_sub sub2)) as dlvn2.
      { rw <- ld2; auto. }

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    (lsubst_aux t1 (var_ren l1 lvn))
                    sub1
                    (var_ren lvn lvn0)) as e1.
      rw @sub_free_vars_var_ren in e1; auto; try lia;[].
      rw @sub_free_vars_if_cl_sub in e1; eauto 2 with slow;[].
      rw @cl_lsubst_aux_sub_trivial in e1; eauto 2 with slow;[].
      rw @sub_filter_disjoint in e1; auto; try lia;[].
      rw @lsubst_aux_nest_vars_same in e1; auto; try lia;
      [|apply disjoint_app_l; dands; eauto 3 with slow];[].
      repeat (autodimp e1 hyp); eauto 2 with slow.

      pose proof (simple_lsubst_aux_lsubst_aux_sub_disj
                    (lsubst_aux t2 (var_ren l2 lvn))
                    sub2
                    (var_ren lvn lvn0)) as e2.
      rw @sub_free_vars_var_ren in e2; auto; try lia;[].
      rw @sub_free_vars_if_cl_sub in e2; eauto 2 with slow;[].
      rw @cl_lsubst_aux_sub_trivial in e2; eauto 2 with slow;[].
      rw @sub_filter_disjoint in e2; auto; try lia;[].
      rw @lsubst_aux_nest_vars_same in e2; auto; try lia;
      [|apply disjoint_app_l; dands; eauto 3 with slow];[].
      repeat (autodimp e2 hyp); eauto 2 with slow.

      rw <- e1; rw <- e2; clear e1 e2.

      pose proof (simple_lsubst_aux_lsubst_aux_sub t1 (var_ren l1 lvn0) sub1) as e1.
      rw @sub_free_vars_var_ren in e1; auto;try lia;[].
      repeat (autodimp e1 hyp); eauto 2 with slow;[].

      pose proof (simple_lsubst_aux_lsubst_aux_sub t2 (var_ren l2 lvn0) sub2) as e2.
      rw @sub_free_vars_var_ren in e2; auto;try lia;[].
      repeat (autodimp e2 hyp); eauto 2 with slow;[].

      rw <- e1; rw <- e2; clear e1 e2.
      repeat (rw @dom_sub_var_ren; try lia;[]).

      rw @lsubst_aux_sub_disj_dom2;[|rw @sub_free_vars_var_ren; auto; try lia].
      rw @lsubst_aux_sub_disj_dom2;[|rw @sub_free_vars_var_ren; auto; try lia].
      auto.
Qed.

Lemma implies_prog_sub_lsubst_aux_sub {o} :
  forall (sub1 sub2 : @Sub o),
    prog_sub sub2
    -> wf_sub sub1
    -> covered_sub sub1 sub2
    -> prog_sub (lsubst_aux_sub sub1 sub2).
Proof.
  induction sub1; introv cl wf cov; allsimpl; eauto 3 with slow.
  destruct a as [v t].
  allrw @covered_sub_cons; repnd.
  allrw @wf_sub_cons_iff; repnd.
  apply prog_sub_cons; dands; auto.
  rw <- @cl_lsubst_lsubst_aux; eauto 2 with slow.
  apply isprogram_lsubst_if_isprog_sub; eauto 2 with slow.
  unfold covered in cov0.
  rw subvars_eq in cov0; auto.
Qed.

Lemma lsubst_alpha_congr8 {o} :
  forall (l1 l2 : list NVar) (t1 t2 : @NTerm o),
    length l1 = length l2
    -> (forall sub1 sub2,
          prog_sub sub1
          -> prog_sub sub2
          -> range sub1 = range sub2
          -> l1 = dom_sub sub1
          -> l2 = dom_sub sub2
          -> alpha_eq (lsubst_aux t1 sub1) (lsubst_aux t2 sub2))
    -> alpha_eq_bterm (bterm l1 t1) (bterm l2 t2).
Proof.
  introv len imp.
  pose proof (fresh_vars (length l1) (l1 ++ l2 ++ all_vars t1 ++ all_vars t2)) as fv.
  exrepnd.
  allrw disjoint_app_r; repnd; auto.
  apply (al_bterm_aux lvn); auto.
  { allrw disjoint_app_r; dands; auto. }

  apply (lsubst_alpha_congr8_aux _ _ lvn).
  introv cl1 cl2 aeqs e1 e2.

  pose proof (simple_lsubst_aux_lsubst_aux_sub
                 t1 (var_ren l1 lvn) sub1) as x1.
  rw @sub_free_vars_var_ren in x1; auto.
  rw @dom_sub_var_ren in x1; auto.
  rw (lsubst_aux_trivial_cl t1 (sub_filter sub1 l1)) in x1; eauto 3 with slow;
  [|rw <- @dom_sub_sub_filter; apply disjoint_remove_nvars2; subst; auto];[].
  repeat (autodimp x1 hyp); eauto 3 with slow.

  pose proof (simple_lsubst_aux_lsubst_aux_sub
                 t2 (var_ren l2 lvn) sub2) as x2.
  rw @sub_free_vars_var_ren in x2; auto; try lia.
  rw @dom_sub_var_ren in x2; auto; try lia.
  rw (lsubst_aux_trivial_cl t2 (sub_filter sub2 l2)) in x2; eauto 3 with slow; try lia;
  [|rw <- @dom_sub_sub_filter; apply disjoint_remove_nvars2; subst; rw <- e2; auto].
  repeat (autodimp x2 hyp); eauto 3 with slow.

  rw <- x1; rw <- x2; clear x1 x2.

  apply imp; eauto 3 with slow.

  - apply implies_prog_sub_lsubst_aux_sub; auto.
    apply covered_var_ren; auto; try lia.
    rw e1; auto.

  - apply implies_prog_sub_lsubst_aux_sub; auto.
    apply covered_var_ren; auto; try lia.
    rw e2; auto.

  - repeat (rw @cl_lsubst_aux_sub_var_ren_eq_dom; eauto 2 with slow; try lia).
    repeat (rw @range_combine); auto; rw @length_range; subst;
    allrw @length_dom; auto.
    rw <- @length_dom; rw <- e2; rw @length_dom; rw <- len; auto.

  - rw @dom_sub_lsubst_aux_sub.
    rw @dom_sub_var_ren; auto.

  - rw @dom_sub_lsubst_aux_sub.
    rw @dom_sub_var_ren; auto; try lia.
Qed.

Lemma implies_alphaeqc_mkc_function {o} :
  forall (t1 t2 : @CTerm o) v1 v2 u1 u2,
    alphaeqc t1 t2
    -> (forall t, alphaeqc (substc t v1 u1) (substc t v2 u2))
    -> alphaeqc (mkc_function t1 v1 u1) (mkc_function t2 v2 u2).
Proof.
  introv aeq1 aeq2; destruct_cterms; allunfold @alphaeqc; allsimpl.
  unfold mk_function, nobnd.
  prove_alpha_eq4.
  introv j; repeat (destruct n; allsimpl; tcsp).
  - apply alpha_eq_bterm_congr; auto.
  - apply lsubst_alpha_congr8; allsimpl; auto.
    introv cl1 cl2 aeq e1 e2.
    destruct sub1 as [|p1 sub1]; allsimpl; ginv.
    destruct sub2 as [|p2 sub2]; allsimpl; ginv.
    destruct sub1, sub2; allsimpl; ginv.
    destruct p1 as [v1 t1].
    destruct p2 as [v2 t2]; allsimpl.
    allrw @prog_sub_cons; repnd.
    allrw @isprogram_eq.
    ginv.
    repeat (rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow).
    allrw @fold_subst.
    pose proof (aeq2 (mk_ct t2 cl3)) as h; allsimpl; auto.
Qed.
