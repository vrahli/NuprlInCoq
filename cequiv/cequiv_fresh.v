(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Export csubst6.
Require Export approx_props3.
Require Export cequiv.
Require Export continuity_defs_ceq.

Lemma lblift_as_combine {o} :
  forall R (bs1 bs2 : list (@BTerm o)),
    lblift R bs1 bs2
    <=> (length bs1 = length bs2
         # forall b1 b2 : BTerm,
             LIn (b1,b2) (combine bs1 bs2) -> blift R b1 b2).
Proof.
  introv.
  unfold lblift; split; intro k; repnd; dands; auto; introv i.

  - allunfold @selectbt.
    apply (in_nth_combine_iff _ _ default_bt default_bt) in i.
    exrepnd; subst.
    apply k; auto.

  - allunfold @selectbt.
    pose proof (in_nth_combine _ _ bs1 bs2 n default_bt default_bt) as q.
    repeat (autodimp q hyp).
Qed.

Lemma isprogram_implies_nt_wf {o} :
  forall t : @NTerm o, isprogram t -> nt_wf t.
Proof.
  introv isp.
  inversion isp; auto.
Qed.
Hint Resolve isprogram_implies_nt_wf : slow.

Definition is_prog_refl {o} (R : bin_rel (@NTerm o)) :=
  forall a b, isprog a -> alpha_eq a b -> R a b.

Lemma is_prog_refl_or {o} :
  forall r1 r2 : @bin_rel (@NTerm o),
    (is_prog_refl r1 [+] is_prog_refl r2)
    -> is_prog_refl (r1 \2/ r2).
Proof.
  introv h isp aeq; simpl.
  repndors;[left|right]; auto.
Qed.
Hint Resolve is_prog_refl_or : slow.

Lemma is_prog_refl_or_left {o} :
  forall r1 r2 : @bin_rel (@NTerm o),
    is_prog_refl r1
    -> is_prog_refl (r1 \2/ r2).
Proof.
  introv h isp aeq; simpl; auto.
Qed.
Hint Resolve is_prog_refl_or_left : slow.

Lemma is_prog_refl_or_right {o} :
  forall r1 r2 : @bin_rel (@NTerm o),
    is_prog_refl r2
    -> is_prog_refl (r1 \2/ r2).
Proof.
  introv h isp aeq; simpl; auto.
Qed.
Hint Resolve is_prog_refl_or_right : slow.

Theorem approx_acc_resp_refl {p} :
  forall (lib : library)
         (l r0 : bin_rel (@NTerm p))
         (resp_l_l : respects_alpha_l l)
         (resp_r_l : respects_alpha_r l)
         (resp_l_r0 : respects_alpha_l r0)
         (resp_r_r0 : respects_alpha_r r0)
         (resp_refl_l : is_prog_refl l)
         (OBG : forall (r: bin_rel NTerm)
                       (INC: r0 =2> r)
                       (CIH: l =2> r)
                       (resp_r : respects_alpha_r r)
                       (resp_l : respects_alpha_l r)
                       (resp_refl : is_prog_refl r),
                  l =2> approx_aux lib r),
    l =2> approx_aux lib r0.
Proof.
  intros.
  assert (SIM: approx_aux lib (r0 \2/ l) x0 x1).
  { apply OBG; eauto 2 with slow. }
  clear PR; revert x0 x1 SIM; cofix CIH.
  intros; destruct SIM; econstructor; eauto.
  invertsna c Hcl. repnd.
  unfold close_comput.
  dands; eauto.

  - introv Hcomp.
    apply Hcl2 in Hcomp.
    exrepnd. exists tr_subterms. split; eauto.
    eapply le_lblift2; eauto.
    apply le_olift.

    unfold le_bin_rel.
    introv Hap.
    repndors; tcsp.
    left.
    apply CIH; apply OBG; eauto 3 with slow.

  - introv Hcomp.
    apply Hcl3 in Hcomp; exrepnd.
    exists a' e'; dands; auto; repndors; auto; tcsp;
    try (complete (left; apply CIH; apply OBG; tcsp; eauto 3 with slow)).

  - introv comp.
    apply Hcl4 in comp; exrepnd.
    eexists; dands; eauto.
    introv.
    pose proof (comp0 n) as h; clear comp0; repndors; tcsp.
    left.
    apply CIH; apply OBG; tcsp; eauto 3 with slow.
Qed.

Lemma approx_aux_refl {o} :
  forall lib r (t : @NTerm o),
    isprogram t
    -> approx_aux lib r t t.
Proof.
  unfold approx.
  intros lib r.
  pose proof (@approx_acc o lib (fun x y => isprogram x # y=x)) as HH.
  allsimpl.
  assert (forall x0 x1, isprogram x0 # x1 = x0 -> approx_aux lib r x0 x1);[| spcf;fail].
  eapply HH.
  intros.
  rename x0 into t.
  exrepnd. subst.
  constructor.
  unfold close_comput; dands; tcsp; introv comp; auto.

  - exists tl_subterms. split; auto.
    unfold lblift.  split; auto.
    intros ? Hlt. unfold blift.
    apply preserve_program in comp; auto.
    pose proof (selectbt_in2 _ tl_subterms Hlt) as Hbt.
    exrepnd.
    destruct bt as [lv nt].
    rw Hbt0.
    exists lv nt nt.
    split; eauto with slow.
    apply isprogram_ot_iff in comp. repnd.
    apply comp in Hbt1. repnud Hbt1.
    inverts Hbt1.
    unfold olift.
    dands; auto.

  - applydup @preserve_program_exc2 in comp; auto; repnd.
    exists a e; dands; auto.

  - eexists; dands; eauto.
    introv.
    applydup @reduces_to_preserves_program in comp as wf; auto.
    right; apply CIH; dands; eauto 3 with slow.
Qed.
Hint Resolve approx_aux_refl : slow.

Lemma approx_shadowed_fresh1 {o} :
  forall lib v (t : @NTerm o),
    isprogram t
    -> approx lib (mk_fresh v t) t.
Proof.
  intro lib.
  unfold approx.

  pose proof (approx_acc_resp
                lib
                (fun x y => {v : NVar & isprogram y # alpha_eq x (mk_fresh v y)})
                bot2) as HH.
  allsimpl.
  match goal with
    | [ HH : _ -> _ -> _ -> _ -> _ -> ?B |- _ ] =>
      assert B as xxx;[|introv isp;eapply xxx;eauto 3 with slow]
  end.
  apply HH; eauto 3 with slow.

  { introv aeq h; allsimpl; exrepnd.
    exists v; dands; eauto 3 with slow. }

  { introv aeq h; allsimpl; exrepnd.
    exists v; dands; eauto 3 with slow.
    eapply alpha_eq_trans;[exact h0|].
    apply implies_alpha_eq_mk_fresh; auto. }

  introv INC CIH rr rl h.
  exrepnd; subst.
  rename x1 into t.
  rename h1 into isp.
  rename x0 into u.
  rename h0 into aeq.

  eapply respects_alpha_l_approx_aux;
    [auto|apply alpha_eq_sym;exact aeq|].
  clear dependent u.

  pose proof (change_bvars_alpha_wspec [v] t) as aeq.
  exrepnd.
  allrw disjoint_singleton_l.
  rename ntcv into u.

  eapply respects_alpha_l_approx_aux;
    [auto|apply alpha_eq_sym;apply implies_alpha_eq_mk_fresh;exact aeq0|].
  eapply respects_alpha_r_approx_aux;
    [auto|apply alpha_eq_sym;exact aeq0|].
  apply alpha_prog_eauto in aeq0; auto.
  clear dependent t.
  rename u into t.
  rename aeq0 into isp.
  rename aeq1 into nivt.

  constructor.
  unfold close_comput; repnd; dands; auto.

  - apply isprogram_fresh.
    apply isprog_vars_if_isprog.
    apply isprog_eq; auto.

  - introv comp.
    allunfold @computes_to_value; repnd.
    pose proof (get_fresh_atom_prop t) as nia.
    remember (get_fresh_atom t) as a; clear Heqa.
    pose proof (fresh_reduces_to_implies lib v t (oterm (Can c) tl_subterms) a) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    exrepnd.

    unfold subst in q1.
    rw @cl_lsubst_trivial in q1; simpl;
    try (apply disjoint_singleton_l);
    eauto 3 with slow;
    [|apply closed_if_program in isp; rw isp; simpl; tcsp].

    applydup @reduces_to_preserves_program in q1 as ispu; auto.
    applydup @reduces_to_preserves_utokens in q1 as ss; eauto 3 with slow;[].
    assert (!LIn a (get_utokens u)) as niau.
    { intro i; apply ss in i; auto. }

    pose proof (trivial_subst_utokens u [(a,mk_var v)]) as aeq.
    allsimpl.
    allrw disjoint_singleton_r; autodimp aeq hyp.

    apply alpha_eq_sym in q0.
    eapply alpha_eq_trans in q0;
      [|apply alpha_eq_sym; apply implies_alpha_eq_pushdown_fresh_same; exact aeq].

    destruct u as [vu|f|op bs]; allsimpl; GC; try (complete (inversion q0)).
    apply alpha_eq_oterm_combine2 in q0; repnd; subst.
    allsimpl.

    exists bs; dands; auto.

    unfold mk_fresh_bterms in q3.
    allrw map_length.

    apply lblift_as_combine.
    dands; auto.

    introv i.
    pose proof (q0 (mk_fresh_bterm v b2) b1) as aeq1.
    autodimp aeq1 hyp.
    { unfold mk_fresh_bterms.
      rw <- map_combine_left.
      rw in_map_iff; simpl.
      exists (b2, b1); simpl; dands; auto.
      apply in_combine_swap; auto. }

    destruct b1 as [l1 t1].
    destruct b2 as [l2 t2].
    allsimpl.
    unfold blift.

    pose proof (fresh_vars (length l2)
                           ((maybe_new_var v l2 t2)
                              :: all_vars t1
                              ++ all_vars t2)) as fvs.
    exrepnd.
    allrw disjoint_cons_r.
    allrw disjoint_app_r.
    repnd.

    pose proof (alphabt_change_var_aux
                   (mk_fresh (maybe_new_var v l2 t2) t2)
                   t1 l2 l1 lvn) as aeq2.
    repeat (autodimp aeq2 hyp).
    { unfold all_vars; simpl; allrw app_nil_r.
      allrw disjoint_app_r; allrw disjoint_cons_r; dands; auto.
      apply implies_disjoint_remove_nvars; auto. }
    repnd.
    allsimpl; fold_terms.
    rw @lsubst_aux_sub_filter_aux in aeq0;
      [|simpl; introv i1 i2 i3; repndors; tcsp; subst;
        allunfold @maybe_new_var;
        rw @dom_sub_var_ren in i3; auto;
        boolvar; tcsp;
        apply newvar_prop in i1; sp].

    exists lvn (lsubst_aux t1 (var_ren l1 lvn)) (lsubst_aux t2 (var_ren l2 lvn)).
    dands;
      [|rw <- @lsubst_lsubst_aux;
         [apply btchange_alpha_aux;try lia;auto;
          allrw disjoint_app_l;dands;eauto 3 with slow|];
         rw @flat_map_free_var_vars_range; eauto 3 with slow; try lia;
         rw @range_var_ren; auto; try lia;
         rw flat_map_map; unfold compose; simpl
       |rw <- @lsubst_lsubst_aux;
         [apply btchange_alpha_aux;try lia;auto;
          allrw disjoint_app_l;dands;eauto 3 with slow|];
         rw @flat_map_free_var_vars_range; eauto 3 with slow; try lia;
         rw @range_var_ren; auto; try lia;
         rw flat_map_map; unfold compose; simpl];
      [].

    apply cl_olift_implies_olift; eauto 3 with slow.
    { apply respects_alpha_2; unfold respects2; dands; eauto 3 with slow. }

    applydup in_combine in i; repnd.
    apply isvalue_implies in comp; repnd.
    applydup @isprog_ntwf_eauto in comp.
    eapply nt_wf_ot_implies in comp2;[|exact i1];[].
    applydup @isprog_ntwf_eauto in ispu.
    eapply nt_wf_ot_implies in ispu0;[|exact i0];[].

    unfold cl_olift.
    dands; eauto 3 with slow;[].

    + introv ps ispl1 ispl2.
      apply (lsubst_alpha_congr2 _ _ sub) in aeq0.
      right.
      eapply rl;[exact aeq0|].
      repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
      simpl; fold_terms.

      rw @cl_lsubst_aux_swap_filter; eauto 3 with slow;
      [|apply disjoint_singleton_r;
         intro j; apply free_vars_lsubst_aux_subset in j;
         rw @dom_sub_var_ren in j;auto;[];
         rw @computation2.sub_free_vars_var_ren in j;auto;[];
         rw in_app_iff in j; repndors; tcsp;[];
         rw in_remove_nvars in j; repnd;
         applydup @maybe_new_var_in_implies in j0; repnd;
         allunfold @maybe_new_var; boolvar; tcsp;
         apply isprogram_ot_iff in ispu; repnd;
         apply ispu in i0;
         allrw <- @isprog_vars_iff_isprogram_bt;
         apply isprog_vars_eq in i0; repnd;
         allrw subvars_eq;
         apply i2 in j0; sp];[].

      apply CIH.
      exists (maybe_new_var v l2 t2); dands; auto.
      rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.

  - introv comp.
    allunfold @computes_to_exception; repnd.
    rename a into n.
    pose proof (get_fresh_atom_prop t) as nia.
    remember (get_fresh_atom t) as a; clear Heqa.
    pose proof (fresh_reduces_to_implies lib v t (mk_exception n e) a) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    exrepnd.

    unfold subst in q1.
    rw @cl_lsubst_trivial in q1; simpl;
    try (apply disjoint_singleton_l);
    eauto 3 with slow;
    [|apply closed_if_program in isp; rw isp; simpl; tcsp].

    applydup @reduces_to_preserves_program in q1 as ispu; auto.
    applydup @reduces_to_preserves_utokens in q1 as ss; eauto 3 with slow;[].
    assert (!LIn a (get_utokens u)) as niau.
    { intro i; apply ss in i; auto. }

    pose proof (trivial_subst_utokens u [(a,mk_var v)]) as aeq.
    allsimpl.
    allrw disjoint_singleton_r; autodimp aeq hyp.

    apply alpha_eq_sym in q0.
    eapply alpha_eq_trans in q0;
      [|apply alpha_eq_sym; apply implies_alpha_eq_pushdown_fresh_same; exact aeq].

    destruct u as [vu|f|op bs]; allsimpl; GC; try (complete (inversion q0));[].
    apply alpha_eq_oterm_combine2 in q0; repnd; subst.
    allsimpl.
    apply isprogram_exception_implies in ispu; exrepnd; subst; allsimpl; GC.
    fold_terms.
    allrw app_nil_r.
    allunfold @maybe_new_var; allsimpl.

    pose proof (q0 (nobnd (mk_fresh v a0)) (nobnd n)) as h1; autodimp h1 hyp.
    pose proof (q0 (nobnd (mk_fresh v t0)) (nobnd e)) as h2; autodimp h2 hyp.
    clear q0.
    allrw @alphaeqbt_nilv2.

    rename a0 into n'.
    rename t0 into e'.

    exists n' e'; dands; auto.

    + right.
      eapply rl;[exact h1|].
      apply CIH.
      exists v; dands; auto.

    + right.
      eapply rl;[exact h2|].
      apply CIH.
      exists v; dands; auto.

  - introv comp.
    pose proof (get_fresh_atom_prop t) as nia.
    remember (get_fresh_atom t) as a; clear Heqa.
    pose proof (fresh_reduces_to_implies lib v t (sterm f) a) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    exrepnd.

    unfold subst in q1.
    rw @cl_lsubst_trivial in q1; simpl;
    try (apply disjoint_singleton_l);
    eauto 3 with slow;
    [|apply closed_if_program in isp; rw isp; simpl; tcsp].

    applydup @reduces_to_preserves_program in q1 as ispu; auto.
    applydup @reduces_to_preserves_utokens in q1 as ss; eauto 3 with slow;[].
    assert (!LIn a (get_utokens u)) as niau.
    { intro i; apply ss in i; auto. }

    pose proof (trivial_subst_utokens u [(a,mk_var v)]) as aeq.
    allsimpl.
    allrw disjoint_singleton_r; autodimp aeq hyp.

    apply alpha_eq_sym in q0.
    eapply alpha_eq_trans in q0;
      [|apply alpha_eq_sym; apply implies_alpha_eq_pushdown_fresh_same; exact aeq].

    destruct u as [vu|f'|op bs]; allsimpl; GC; try (complete (inversion q0));[].

    apply alpha_eq_sym in q0; inversion q0; subst; auto.

    eexists; dands; eauto.
    introv.

    applydup @alphaeq_preserves_program in q0; auto.
    applydup q2 in ispu.
    left; eapply approxr_alpha_rw_r_aux;[|eauto|]; eauto 3 with slow.
Qed.

Lemma map_combine_right :
  forall (T1 T2 T3 : tuniv)
         (f : T2 -> T3) (l1 : list T1) (l2 : list T2),
    map (fun x => (fst x, f (snd x))) (combine l1 l2)
    = combine l1 (map f l2).
Proof.
  induction l1; introv; allsimpl; auto.
  destruct l2; allsimpl; auto.
  rw IHl1; auto.
Qed.

Lemma approx_shadowed_fresh2 {o} :
  forall lib v (t : @NTerm o),
    isprogram t
    -> approx lib t (mk_fresh v t).
Proof.
  intro lib.
  unfold approx.

  pose proof (approx_acc_resp
                lib
                (fun x y => {v : NVar & isprogram x # alpha_eq y (mk_fresh v x)})
                bot2) as HH.
  allsimpl.
  match goal with
    | [ HH : _ -> _ -> _ -> _ -> _ -> ?B |- _ ] =>
      assert B as xxx;[|introv isp;eapply xxx;eauto 3 with slow]
  end.
  apply HH; eauto 3 with slow.

  { introv aeq h; allsimpl; exrepnd.
    exists v; dands; eauto 3 with slow.
    eapply alpha_eq_trans;[exact h0|].
    apply implies_alpha_eq_mk_fresh; auto. }

  { introv aeq h; allsimpl; exrepnd.
    exists v; dands; eauto 3 with slow. }

  introv INC CIH rr rl h.
  exrepnd; subst.
  rename x1 into u.
  rename h1 into isp.
  rename x0 into t.
  rename h0 into aeq.

  eapply respects_alpha_r_approx_aux;
    [auto|apply alpha_eq_sym;exact aeq|].
  clear dependent u.

  pose proof (change_bvars_alpha_wspec [v] t) as aeq.
  exrepnd.
  allrw disjoint_singleton_l.
  rename ntcv into u.

  eapply respects_alpha_r_approx_aux;
    [auto|apply alpha_eq_sym;apply implies_alpha_eq_mk_fresh;exact aeq0|].
  eapply respects_alpha_l_approx_aux;
    [auto|apply alpha_eq_sym;exact aeq0|].
  apply alpha_prog_eauto in aeq0; auto.
  clear dependent t.
  rename u into t.
  rename aeq0 into isp.
  rename aeq1 into nivt.

  constructor.
  unfold close_comput; repnd; dands; auto.

  - apply isprogram_fresh.
    apply isprog_vars_if_isprog.
    apply isprog_eq; auto.

  - introv comp.
    allunfold @computes_to_value; repnd.
    pose proof (get_fresh_atom_prop t) as nia.
    remember (get_fresh_atom t) as a; clear Heqa.

    pose proof (reduces_to_fresh2 lib t (oterm (Can c) tl_subterms) v a) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    { unfold subst; rw @cl_lsubst_trivial; eauto 3 with slow;[].
      simpl; apply disjoint_singleton_l; auto.
      apply closed_if_program in isp; rw isp; simpl; tcsp. }
    exrepnd.

    applydup @reduces_to_preserves_program in q1 as ispu; auto;
    [|apply isprogram_fresh; apply isprog_vars_if_isprog; eauto 3 with slow].
    applydup @reduces_to_preserves_utokens in q1 as ss1;auto;
    [|apply nt_wf_fresh;eauto 3 with slow];[].
    applydup @reduces_to_preserves_utokens in comp0 as ss2; eauto 3 with slow;[].
    assert (!LIn a (get_utokens (oterm (Can c) tl_subterms))) as niau.
    { intro i; apply ss2 in i; auto. }

    pose proof (trivial_subst_utokens (oterm (Can c) tl_subterms) [(a,mk_var v)]) as aeq.
    allsimpl.
    allrw disjoint_singleton_r; autodimp aeq hyp;[].
    allrw app_nil_r.

    apply alpha_eq_sym in q0.
    eapply alpha_eq_trans in q0;[|apply alpha_eq_sym;exact aeq].
    clear aeq.
    apply alpha_eq_oterm_implies_combine2 in q0; exrepnd; subst.
    allsimpl.

    assert (reduces_to lib (mk_fresh v t) (oterm (Can c) (mk_fresh_bterms v bs'))) as rf.
    { eapply reduces_to_if_split1;[exact q1|].
      csunf; simpl; auto. }

    applydup @reduces_to_preserves_program in rf; auto;
    [|apply isprogram_fresh; apply isprog_vars_if_isprog; eauto 3 with slow].

    exists (mk_fresh_bterms v bs').
    dands; auto;[].

    unfold alpha_eq_bterms in q2; repnd.

    apply lblift_as_combine.
    unfold mk_fresh_bterms.
    allrw map_length.
    dands; auto; try lia.

    introv i.
    rw <- map_combine_right in i.
    allrw in_map_iff; exrepnd; allsimpl; ginv.
    applydup q2 in i1.

    destruct a1 as [l1 t1].
    destruct a0 as [l2 t2].
    allsimpl.
    unfold blift.

    pose proof (fresh_vars (length l2)
                           ((maybe_new_var v l2 t2)
                              :: all_vars t1
                              ++ all_vars t2)) as fvs.
    exrepnd.
    allrw disjoint_cons_r.
    allrw disjoint_app_r.
    repnd.

    applydup @alphaeqbt_numbvars in i0; allunfold @num_bvars; allsimpl.

    pose proof (alphabt_change_var_aux t1 t2 l1 l2 lvn) as aeq2.
    repeat (autodimp aeq2 hyp); try lia.
    { unfold all_vars; simpl; allrw app_nil_r.
      allrw disjoint_app_r; allrw disjoint_cons_r; dands; auto. }
    repnd; GC.

    exists
      lvn
      (lsubst_aux t1 (var_ren l1 lvn))
      (lsubst_aux (mk_fresh (maybe_new_var v l2 t2) t2) (var_ren l2 lvn)).
    dands;
      [|rw <- @lsubst_lsubst_aux;
         [apply btchange_alpha_aux;try lia;auto;
          allrw disjoint_app_l;dands;eauto 3 with slow|];
         rw @flat_map_free_var_vars_range; eauto 3 with slow; try lia;
         rw @range_var_ren; auto; try lia;
         rw flat_map_map; unfold compose; simpl
       |rw <- @lsubst_lsubst_aux;
         [apply btchange_alpha_aux;try lia;auto;
          allrw disjoint_app_l;simpl;dands;eauto 3 with slow;
          simpl;apply disjoint_singleton_l;auto
         |];[];
         rw @flat_map_free_var_vars_range; eauto 3 with slow; try lia;
         simpl;allrw app_nil_r; allrw disjoint_cons_l; dands; eauto 3 with slow];
      [].

    apply cl_olift_implies_olift; eauto 3 with slow.
    { apply respects_alpha_2; unfold respects2; dands; eauto 3 with slow. }

    applydup in_combine in i1; repnd.
    apply isvalue_implies in comp; repnd.
    applydup @isprog_ntwf_eauto in comp.
    eapply nt_wf_ot_implies in comp2;[|exact i4];[].
    applydup @isprog_ntwf_eauto in ispu.
    allrw @nt_wf_fresh.
    eapply nt_wf_ot_implies in ispu0;[|exact i3];[].

    simpl.
    rw @lsubst_aux_sub_filter_aux;
      [|simpl; introv x1 x2 x3; repndors; tcsp; subst;
        allunfold @maybe_new_var;
        rw @dom_sub_var_ren in x3; auto;
        boolvar; tcsp;
        apply newvar_prop in x1; sp].
    fold_terms.

    unfold cl_olift.
    dands.

    + apply implies_wf_lsubst_aux; eauto 3 with slow.

    + apply nt_wf_fresh; auto.
      apply implies_wf_lsubst_aux; eauto 3 with slow.

    + introv ps ispl1 ispl2.
      right.
      apply (lsubst_alpha_congr2 _ _ sub) in aeq0.
      eapply rl;[apply alpha_eq_sym;exact aeq0|].
      repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
      simpl; fold_terms.

      rw @cl_lsubst_aux_swap_filter; eauto 3 with slow.

      { apply CIH.
        exists (maybe_new_var v l2 t2); dands; auto.
        rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow. }

      apply disjoint_singleton_r.
      intro j; apply free_vars_lsubst_aux_subset in j.
      rw @dom_sub_var_ren in j;auto;[].
      rw @computation2.sub_free_vars_var_ren in j;auto;[].
      rw in_app_iff in j; repndors; tcsp;[].
      rw in_remove_nvars in j; repnd.
      applydup @maybe_new_var_in_implies in j0; repnd.
      allunfold @maybe_new_var; boolvar; tcsp.

      apply isprogram_ot_iff in comp; repnd.
      apply comp in i4.
      apply alphaeqbt_preserves_prog_r_eauto in i0; auto;[].
      allrw <- @isprog_vars_iff_isprogram_bt.
      apply isprog_vars_eq in i0; repnd.
      allrw subvars_eq.
      apply i5 in j0; sp.

  - introv comp.
    allunfold @computes_to_exception; repnd.
    rename a into n.
    pose proof (get_fresh_atom_prop t) as nia.
    remember (get_fresh_atom t) as a; clear Heqa.

    pose proof (reduces_to_fresh2 lib t (mk_exception n e) v a) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    { unfold subst; rw @cl_lsubst_trivial; eauto 3 with slow;[].
      simpl; apply disjoint_singleton_l; auto.
      apply closed_if_program in isp; rw isp; simpl; tcsp. }
    exrepnd.

    applydup @reduces_to_preserves_program in q1 as ispu; auto;
    [|apply isprogram_fresh; apply isprog_vars_if_isprog; eauto 3 with slow].
    applydup @reduces_to_preserves_utokens in q1 as ss1; auto;
    [|apply nt_wf_fresh; eauto 3 with slow];[].
    applydup @reduces_to_preserves_utokens in comp as ss2; eauto 2 with slow;[].
    assert (!LIn a (get_utokens (mk_exception n e))) as niau.
    { intro i; apply ss2 in i; auto. }

    pose proof (trivial_subst_utokens (mk_exception n e) [(a,mk_var v)]) as aeq.
    allsimpl.
    allrw disjoint_singleton_r; autodimp aeq hyp;[].
    allrw app_nil_r.

    apply alpha_eq_sym in q0.
    eapply alpha_eq_trans in q0;[|apply alpha_eq_sym;exact aeq].
    clear aeq.
    apply alpha_eq_exception in q0; exrepnd; subst.
    allsimpl.
    allrw app_nil_r.

    assert (reduces_to lib (mk_fresh v t) (mk_exception (mk_fresh v a') (mk_fresh v e'))) as rf.
    { eapply reduces_to_if_split1;[exact q1|].
      csunf; simpl; auto. }

    applydup @reduces_to_preserves_program in rf; auto;
    [|apply isprogram_fresh; apply isprog_vars_if_isprog; eauto 3 with slow].

    applydup @reduces_to_preserves_program in comp; auto.
    allrw @isprogram_exception_iff; repnd; GC.

    exists (mk_fresh v a') (mk_fresh v e').
    dands; auto.

    + right.
      eapply rl;[apply alpha_eq_sym;exact q3|].
      apply CIH.
      exists v; dands; eauto 3 with slow.

    + right.
      eapply rl;[apply alpha_eq_sym;exact q0|].
      apply CIH.
      exists v; dands; eauto 3 with slow.

  - introv comp.
    pose proof (get_fresh_atom_prop t) as nia.
    remember (get_fresh_atom t) as a; clear Heqa.

    pose proof (reduces_to_fresh2 lib t (sterm f) v a) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    { unfold subst; rw @cl_lsubst_trivial; eauto 3 with slow;[].
      simpl; apply disjoint_singleton_l; auto.
      apply closed_if_program in isp; rw isp; simpl; tcsp. }
    exrepnd.

    applydup @reduces_to_preserves_program in q1 as ispu; auto;
    [|apply isprogram_fresh; apply isprog_vars_if_isprog; eauto 3 with slow].
    applydup @reduces_to_preserves_utokens in q1 as ss1;auto;
    [|apply nt_wf_fresh;eauto 3 with slow];[].
    applydup @reduces_to_preserves_utokens in comp as ss2; eauto 3 with slow;[].
    assert (!LIn a (get_utokens (sterm f))) as niau.
    { intro i; apply ss2 in i; auto. }

    pose proof (trivial_subst_utokens (sterm f) [(a,mk_var v)]) as aeq.
    allsimpl.
    allrw disjoint_singleton_r; autodimp aeq hyp;[].
    allrw app_nil_r.

    apply alpha_eq_sym in q0.
    eapply alpha_eq_trans in q0;[|apply alpha_eq_sym;exact aeq].
    clear aeq.
    inversion q0 as [|? ? imp|]; clear q0; subst; GC.

    assert (reduces_to lib (mk_fresh v t) (sterm f2)) as rf.
    { eapply reduces_to_if_split1;[exact q1|].
      csunf; simpl; auto. }

    exists f2; dands; auto.
    applydup @reduces_to_preserves_program in comp; auto.

    introv; left.
    pose proof (imp n) as h.
    eapply respects_alpha_r_approx_aux;try (exact h); auto.
    eauto 3 with slow.
Qed.

Lemma cequiv_shadowed_fresh {o} :
  forall lib v (t : @NTerm o),
    isprogram t
    -> cequiv lib (mk_fresh v t) t.
Proof.
  introv niv.
  split.
  - apply approx_shadowed_fresh1; auto.
  - apply approx_shadowed_fresh2; auto.
Qed.
