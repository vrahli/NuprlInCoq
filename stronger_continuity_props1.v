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


Require Export list.
Require Export per_props.
Require Export continuity_defs.
Require Export stronger_continuity_defs0.
Require Export cequiv_fresh.


Lemma hasvalue_like_apply {o} :
  forall lib (t u : @NTerm o),
    wf_term t
    -> wf_term u
    -> hasvalue_like lib (mk_apply t u)
    -> ({v : NVar
         & {b : NTerm
         & reduces_to lib t (mk_lam v b)
         # hasvalue_like lib (subst b v u)}}
        [+] {s : nseq
             & reduces_to lib t (mk_nseq s)
             # hasvalue_like lib (mk_apseq s u) }
        [+] {s : ntseq
             & reduces_to lib t (mk_ntseq s)
             # hasvalue_like lib (mk_eapply (sterm s) u) }
        [+] {n : NTerm
             & {e : NTerm
             & computes_to_exception lib n t e }}).
Proof.
  introv wt wu hv.
  unfold hasvalue_like, reduces_to in hv; exrepnd.
  revert dependent t.
  induction k; introv wt comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allunfold @isvalue_like; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    destruct t as [v1|f1|op bs]; allsimpl; ginv.

    { right; right; left.
      exists f1; dands; eauto 3 with slow.
      exists v; dands; auto.
      exists k; auto. }

    dopid op as [can|ncan|exc|abs] Case; allsimpl; ginv.

    + Case "Can".
      clear IHk.
      apply compute_step_apply_success in comp1; repndors; exrepnd; subst; fold_terms; ginv.

      { left.
        exists v0 b; dands; eauto 3 with slow.
        exists v; dands; auto.
        exists k; auto. }

      { right; left.
        exists f; dands; eauto 3 with slow.
        exists v; dands; auto.
        exists k; auto. }

    + remember (compute_step lib (oterm (NCan ncan) bs)) as cs.
      symmetry in Heqcs; destruct cs; allsimpl; ginv; fold_terms.
      applydup @compute_step_preserves_wf in Heqcs; auto.
      apply IHk in comp0; auto; repndors; exrepnd.

      * left.
        exists v0 b; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right; left.
        exists s; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right; right; left.
        exists s; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right; right; right.
        exists n0 e.
        eapply reduces_to_if_split2; eauto.

    + apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; subst.
      allapply @wf_exception_implies; exrepnd; subst; fold_terms.
      right; right; right.
      exists a t.
      eapply reduces_to_symm.

    + remember (compute_step lib (oterm (Abs abs) bs)) as cs.
      symmetry in Heqcs; destruct cs; allsimpl; ginv; fold_terms.
      applydup @compute_step_preserves_wf in Heqcs; auto.
      apply IHk in comp0; auto; repndors; exrepnd.

      * left.
        exists v0 b; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right; left.
        exists s; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right; right; left.
        exists s; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right; right; right.
        exists n0 e.
        eapply reduces_to_if_split2; eauto.
Qed.

(* !!MOVE *)
Lemma alpha_eq_mk_nseq {o} :
  forall s (t : @NTerm o),
    alpha_eq (mk_nseq s) t
    -> t = mk_nseq s.
Proof.
  introv aeq.
  inversion aeq; allsimpl; cpx.
Qed.

(* !!MOVE *)
Lemma hasvalue_like_apseq {o} :
  forall lib s (t : @NTerm o),
    wf_term t
    -> hasvalue_like lib (mk_apseq s t)
    -> {n : nat & computes_to_value lib t (mk_nat n) }
       [+] raises_exception lib t.
Proof.
  introv wt hv.
  unfold hasvalue_like, reduces_to in hv; exrepnd.
  revert dependent t.
  induction k; introv wt comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    allunfold @isvalue_like; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    csunf comp1; allsimpl.
    destruct t as [v1|f1|op bs]; allsimpl; ginv;[].
    dopid op as [can|ncan|exc|abs] Case; allsimpl; ginv.

    + Case "Can".
      clear IHk.
      apply compute_step_apseq_success in comp1; repndors; exrepnd; subst; fold_terms; ginv.
      apply computation3.reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow.
      subst.
      left; exists n.
      eauto 3 with slow.

    + remember (compute_step lib (oterm (NCan ncan) bs)) as cs.
      symmetry in Heqcs; destruct cs; allsimpl; ginv; fold_terms.
      applydup @compute_step_preserves_wf in Heqcs; auto.
      apply IHk in comp0; auto; repndors; exrepnd.

      * left.
        exists n0; dands; auto.
        allunfold @computes_to_value; repnd; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right.
        allunfold @raises_exception; exrepnd.
        exists a e.
        eapply reduces_to_if_split2; eauto.

    + apply reduces_in_atmost_k_steps_if_isvalue_like in comp0; eauto 3 with slow; subst.
      right.
      unfold raises_exception.
      allapply @wf_exception_implies; exrepnd; subst; fold_terms.
      exists a t.
      eapply reduces_to_symm.

    + remember (compute_step lib (oterm (Abs abs) bs)) as cs.
      symmetry in Heqcs; destruct cs; allsimpl; ginv; fold_terms.
      applydup @compute_step_preserves_wf in Heqcs; auto.
      apply IHk in comp0; auto; repndors; exrepnd.

      * left.
        exists n0; dands; auto.
        allunfold @computes_to_value; repnd; dands; auto.
        eapply reduces_to_if_split2; eauto.

      * right.
        allunfold @raises_exception; exrepnd.
        exists a e.
        eapply reduces_to_if_split2; eauto.
Qed.

Lemma approx_apply_fresh1 {o} :
  forall lib v (t : @NTerm o) u,
    isprog u
    -> isprog_vars [v] t
    -> approx
         lib
         (mk_fresh v (mk_apply t u))
         (mk_apply (mk_fresh v t) u).
Proof.
  introv ispu ispt.

  pose proof (change_bvars_alpha_wspec [v] u) as hu.
  destruct hu as [u' hu]; repnd.
  allrw disjoint_singleton_l.
  applydup @alpha_eq_preserves_isprog in hu as ispu'; auto.
  eapply approx_alpha_rw_l_aux;
    [apply implies_alpha_eq_mk_fresh;
      apply implies_alpha_eq_mk_apply;
      [apply alpha_eq_refl|apply alpha_eq_sym;exact hu]
    |].
  eapply approx_alpha_rw_r_aux;
    [apply implies_alpha_eq_mk_apply;
      [apply alpha_eq_refl|apply alpha_eq_sym;exact hu]
    |].
  clear dependent u.
  rename ispu' into ispu.
  rename u' into u.

  pose proof (change_bvars_alpha_wspec [v] t) as ht.
  destruct ht as [t' ht]; repnd.
  allrw disjoint_singleton_l.
  applydup (alphaeq_preserves_isprog_vars t t' [v]) in ht as ispt'; auto.
  eapply approx_alpha_rw_l_aux;
    [apply implies_alpha_eq_mk_fresh;
      apply implies_alpha_eq_mk_apply;
      [apply alpha_eq_sym;exact ht|apply alpha_eq_refl]
    |].
  eapply approx_alpha_rw_r_aux;
    [apply implies_alpha_eq_mk_apply;
      [apply implies_alpha_eq_mk_fresh;
        apply alpha_eq_sym;exact ht
      |apply alpha_eq_refl]
    |].
  clear dependent t.
  rename ispt' into ispt.
  rename t' into t.

  apply approx_assume_hasvalue;
    try (apply isprogram_apply);
    try (apply isprogram_fresh);
    try (apply isprog_vars_apply_implies);
    eauto 3 with slow;[].

  introv hv.
  pose proof (fresh_atom o (get_utokens t ++ get_utokens u)) as fa.
  destruct fa as [a fa].
  allrw in_app_iff; allrw not_over_or; repnd.

  pose proof (hasvalue_like_fresh_implies lib a v (mk_apply t u)) as h.
  repeat (autodimp h hyp); simpl;
  try (apply wf_apply); eauto 3 with slow;
  allrw app_nil_r; allrw in_app_iff; tcsp.
  rw @cl_subst_subst_aux in h; eauto 2 with slow.
  unfold subst_aux in h; allsimpl; fold_terms.
  rw (lsubst_aux_trivial_cl_term2 u) in h; eauto 3 with slow.

  apply hasvalue_like_apply in h;
    try (apply lsubst_aux_preserves_wf_term2);
    eauto 3 with slow;[].

  repndors; exrepnd.

  - pose proof (reduces_to_fresh2 lib (mk_apply t u) (subst b v0 u) v a) as q.
    repeat (autodimp q hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms.
      rw (lsubst_aux_trivial_cl_term2 u); eauto 3 with slow.
      eapply reduces_to_if_split1;[apply reduces_to_prinarg; exact h0|].
      csunf; simpl; auto. }
    exrepnd.

    pose proof (reduces_to_fresh2 lib t (mk_lam v0 b) v a) as r.
    repeat (autodimp r hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms. }
    exrepnd.

    eapply approx_trans;
      [apply reduces_to_implies_approx2;
        [apply isprogram_fresh;
          apply isprog_vars_apply_implies;
          eauto 3 with slow
        |exact q1]
      |].
    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_apply;
           try (apply isprogram_fresh);
           eauto 3 with slow
         |apply reduces_to_prinarg;exact r1]
      ].
    fold_terms.

    eapply approx_alpha_rw_l_aux;
      [apply implies_alpha_eq_mk_fresh;
        apply alpha_eq_sym;exact q0
      |].

    eapply approx_alpha_rw_r_aux;
      [apply alpha_eq_sym;
        apply implies_alpha_eq_mk_apply;
        [apply implies_alpha_eq_mk_fresh;exact r0
        |apply alpha_eq_refl]
      |].

    pose proof (unfold_subst_utokens [(a,mk_var v)] (subst b v0 u)) as unfa.
    exrepnd.
    rw unfa0.

    pose proof (unfold_subst_utokens [(a,mk_var v)] (mk_lam v0 b)) as unfb.
    exrepnd.
    rw unfb0.
    apply alpha_eq_mk_lam in unfb1; exrepnd; subst.

    allsimpl; fold_terms.
    allrw app_nil_r.
    allrw disjoint_singleton_r; allsimpl.
    allrw in_app_iff; allrw not_over_or; repnd.

    rw <- @cl_lsubst_lsubst_aux in h0; eauto 2 with slow.
    applydup @reduces_to_preserves_isprog in h0;
      [|apply isprog_eq;
         apply isprogram_lsubst_if_isprog_sub;
         simpl; eauto 3 with slow;
         apply isprog_vars_eq in ispt;
         repnd; allrw subvars_eq;auto];[].

    apply isprog_lam_iff in h2.
    applydup @alpha_eq_bterm_preserves_isprog_vars in unfb1;auto.

    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_apply;
           try (apply isprogram_fresh);
           try (apply isprog_vars_lam);
           try (apply implies_isprog_vars_subst_utokens_aux);
           try (apply implies_isprog_vars_utok_sub_cons);
           eauto 3 with slow
         |apply reduces_to_prinarg;
           apply reduces_to_if_step;
           csunf; simpl;auto
         ]
      ];[]; fold_terms.

    unfold maybe_new_var; rw memvar_singleton; boolvar; tcsp;[].

    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_apply;
           try (apply isprogram_lam);
           try (apply isprog_vars_fresh_implies);
           try (apply implies_isprog_vars_subst_utokens_aux);
           try (apply implies_isprog_vars_utok_sub_cons);
           eauto 3 with slow
         |apply reduces_to_if_step;csunf;simpl;auto]
      ];[].
    unfold apply_bterm; simpl.

    rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[].
    simpl; rw memvar_singleton; boolvar; tcsp;[].
    fold_terms.

    assert (isprogram t') as ispt'.
    { apply alphaeq_preserves_program in unfa1; apply unfa1.
      apply isprogram_subst_if_bt; eauto 3 with slow. }
    apply isprogram_eq in ispt'.

    apply alpha_implies_approx3;
      try (apply isprogram_fresh);
      try (apply implies_isprog_vars_subst_utokens_aux);
      try (apply implies_isprog_vars_utok_sub_cons);
      eauto 3 with slow.
    apply implies_alpha_eq_mk_fresh.

    rw @lsubst_aux_subst_utokens_aux_disj;
      try (complete (unfold get_utokens_sub; simpl; allrw app_nil_r; allrw disjoint_singleton_r; auto));
      try (complete (unfold free_vars_utok_sub; simpl; apply disjoint_singleton_l; simpl; tcsp));
      [].

    pose proof (lsubst_alpha_congr4 [v0] [v'] b b' [(v0,u)] [(v',u)]) as aeq.
    allsimpl.
    repeat (autodimp aeq hyp); eauto 3 with slow;[].
    rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow;[].
    allrw @fold_subst.

    assert (alpha_eq t' (subst b' v' u)) as aeq' by eauto 3 with slow.

    apply alpha_eq_subst_utokens_aux; simpl; allrw disjoint_singleton_l;
    eauto 3 with slow.
    unfsubst; intro i.
    apply subset_bound_vars_lsubst_aux in i; allsimpl; allrw app_nil_r.
    allrw in_app_iff; sp.

  - pose proof (reduces_to_fresh2 lib (mk_apply t u) (mk_apseq s u) v a) as q.
    repeat (autodimp q hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms.
      rw (lsubst_aux_trivial_cl_term2 u); eauto 3 with slow.
      eapply reduces_to_if_split1;[apply reduces_to_prinarg; exact h1|].
      csunf; simpl; auto. }
    exrepnd.

    unfold subst_utokens in q0; allsimpl; allrw app_nil_r.
    boolvar; allrw disjoint_singleton_r; tcsp;[].
    fold_terms.
    rw @trivial_subst_utokens_aux in q0; simpl; allrw disjoint_singleton_r; auto.

    pose proof (reduces_to_fresh2 lib t (mk_nseq s) v a) as r.
    repeat (autodimp r hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms. }
    exrepnd.

    unfold subst_utokens in r0; allsimpl; fold_terms.
    apply alpha_eq_sym in r0.
    apply alpha_eq_mk_nseq in r0; subst.

    assert (reduces_to lib (mk_fresh v t) (mk_nseq s)) as r.
    { eapply reduces_to_if_split1;[exact r1|].
      csunf; simpl; auto. }
    clear r1.

    eapply approx_trans;
      [apply reduces_to_implies_approx2;
        [apply isprogram_fresh;
          apply isprog_vars_apply_implies;
          eauto 3 with slow
        |exact q1]
      |].
    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_apply;
           try (apply isprogram_fresh);
           eauto 3 with slow
         |apply reduces_to_prinarg;exact r]
      ].
    fold_terms.

    eapply approx_alpha_rw_l_aux;
      [apply implies_alpha_eq_mk_fresh;
        apply alpha_eq_sym;exact q0
      |].

    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_apply;
           try (apply isprogram_mk_nseq);
           eauto 3 with slow
         |apply reduces_to_if_step;
           csunf;simpl;reflexivity]
      ].

    eapply cequiv_le_approx.
    apply cequiv_shadowed_fresh.
    apply isprogram_apseq; eauto 3 with slow.

  - pose proof (reduces_to_fresh2 lib (mk_apply t u) (mk_eapply (sterm s) u) v a) as q.
    repeat (autodimp q hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms.
      rw (lsubst_aux_trivial_cl_term2 u); eauto 3 with slow.
      eapply reduces_to_if_split1;[apply reduces_to_prinarg; exact h1|].
      csunf; simpl; auto. }
    exrepnd.

    unfold subst_utokens in q0; allsimpl; allrw app_nil_r.
    boolvar; allrw disjoint_singleton_r; tcsp;[].
    fold_terms.
    rw @trivial_subst_utokens_aux in q0; simpl; allrw disjoint_singleton_r; auto.

    pose proof (reduces_to_fresh2 lib t (mk_ntseq s) v a) as r.
    repeat (autodimp r hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms. }
    exrepnd.

    unfold subst_utokens in r0; allsimpl; fold_terms.
    apply alpha_eq_sym in r0.
    apply alpha_eq_sterm in r0; exrepnd; subst.

    assert (reduces_to lib (mk_fresh v t) (sterm g)) as r.
    { eapply reduces_to_if_split1;[exact r1|].
      csunf; simpl; auto. }
    clear r1.

    eapply approx_trans;
      [apply reduces_to_implies_approx2;
        [apply isprogram_fresh;
          apply isprog_vars_apply_implies;
          eauto 3 with slow
        |exact q1]
      |].
    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_apply;
           try (apply isprogram_fresh);
           eauto 3 with slow
         |apply reduces_to_prinarg;exact r]
      ].
    fold_terms.

    eapply approx_alpha_rw_l_aux;
      [apply implies_alpha_eq_mk_fresh;
        apply alpha_eq_sym;exact q0
      |].

    applydup @reduces_to_preserves_program in r;
      try (apply isprogram_fresh; auto);[].

    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_apply;eauto 3 with slow
         |apply reduces_to_if_step; csunf;simpl;reflexivity]
      ].

    eapply cequiv_le_approx.
    eapply cequiv_rw_r_eauto;
      [apply implies_alpha_eq_mk_eapply;
        [constructor;exact r2|apply alpha_eq_refl]
      |].
    apply cequiv_shadowed_fresh.
    apply isprogram_eapply; eauto 2 with slow.
    eapply alpha_prog_eauto;[|exact r0].
    apply alpha_eq_sym; auto.

  - pose proof (reduces_to_fresh2 lib (mk_apply t u) (mk_exception n e) v a) as q.
    repeat (autodimp q hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms.
      rw (lsubst_aux_trivial_cl_term2 u); eauto 3 with slow.
      eapply reduces_to_if_split1;[apply reduces_to_prinarg; exact h1|].
      csunf; simpl; auto. }
    exrepnd.

    pose proof (reduces_to_fresh2 lib t (mk_exception n e) v a) as r.
    repeat (autodimp r hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms. }
    exrepnd.

    eapply approx_trans;
      [apply reduces_to_implies_approx2;
        [apply isprogram_fresh;
          apply isprog_vars_apply_implies;
          eauto 3 with slow
        |exact q1]
      |].
    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_apply;
           try (apply isprogram_fresh);
           eauto 3 with slow
         |apply reduces_to_prinarg;exact r1]
      ].
    fold_terms.

    eapply approx_alpha_rw_l_aux;
      [apply implies_alpha_eq_mk_fresh;
        apply alpha_eq_sym;exact q0
      |].

    eapply approx_alpha_rw_r_aux;
      [apply alpha_eq_sym;
        apply implies_alpha_eq_mk_apply;
        [apply implies_alpha_eq_mk_fresh;exact r0
        |apply alpha_eq_refl]
      |].

    pose proof (unfold_subst_utokens [(a,mk_var v)] (mk_exception n e)) as unf.
    exrepnd.
    rw unf0.
    apply alpha_eq_exception in unf1; exrepnd; subst.

    allsimpl; fold_terms.
    allrw app_nil_r.
    allrw disjoint_singleton_r; allsimpl.
    allrw in_app_iff; allrw not_over_or; repnd.

    rw <- @cl_lsubst_lsubst_aux in h1; eauto 2 with slow.
    applydup @reduces_to_preserves_isprog in h1;
      [|apply isprog_eq;
         apply isprogram_lsubst_if_isprog_sub;
         simpl; eauto 3 with slow;
         apply isprog_vars_eq in ispt;
         repnd; allrw subvars_eq;auto];[].

    apply isprog_exception_iff in h0; repnd.
    applydup @alpha_eq_preserves_isprog in unf1; auto.
    applydup @alpha_eq_preserves_isprog in unf4; auto.

    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_apply;
           try (apply isprogram_fresh);
           try (apply isprog_vars_exception);dands;
           try (apply implies_isprog_vars_subst_utokens_aux);
           try (apply implies_isprog_vars_utok_sub_cons);
           eauto 3 with slow
         |eapply reduces_to_if_split2;
           [csunf;simpl;auto|];fold_terms;
           eapply reduces_to_if_step;
           csunf;simpl;auto
         ]
      ];[]; fold_terms.

    unfold maybe_new_var; simpl.

    eapply approx_trans;
      [apply reduces_to_implies_approx2;
        [apply isprogram_fresh;
          try (apply isprog_vars_exception);dands;
          try (apply implies_isprog_vars_subst_utokens_aux);
          try (apply implies_isprog_vars_utok_sub_cons);
          eauto 3 with slow
        |apply reduces_to_if_step;csunf;simpl;auto]
      |];[];fold_terms.

    unfold maybe_new_var; simpl.
    apply approx_refl.
    apply isprogram_exception;
      apply isprogram_fresh;
      try (apply implies_isprog_vars_subst_utokens_aux);
      try (apply implies_isprog_vars_utok_sub_cons);
      eauto 3 with slow.
Qed.

Lemma approx_apply_fresh2 {o} :
  forall lib v (t : @NTerm o) u,
    isprog u
    -> isprog_vars [v] t
    -> approx
         lib
         (mk_apply (mk_fresh v t) u)
         (mk_fresh v (mk_apply t u)).
Proof.
  introv ispu ispt.

  pose proof (change_bvars_alpha_wspec [v] u) as hu.
  destruct hu as [u' hu]; repnd.
  allrw disjoint_singleton_l.
  applydup @alpha_eq_preserves_isprog in hu as ispu'; auto.
  eapply approx_alpha_rw_r_aux;
    [apply implies_alpha_eq_mk_fresh;
      apply implies_alpha_eq_mk_apply;
      [apply alpha_eq_refl|apply alpha_eq_sym;exact hu]
    |].
  eapply approx_alpha_rw_l_aux;
    [apply implies_alpha_eq_mk_apply;
      [apply alpha_eq_refl|apply alpha_eq_sym;exact hu]
    |].
  clear dependent u.
  rename ispu' into ispu.
  rename u' into u.

  pose proof (change_bvars_alpha_wspec [v] t) as ht.
  destruct ht as [t' ht]; repnd.
  allrw disjoint_singleton_l.
  applydup (alphaeq_preserves_isprog_vars t t' [v]) in ht as ispt'; auto.
  eapply approx_alpha_rw_r_aux;
    [apply implies_alpha_eq_mk_fresh;
      apply implies_alpha_eq_mk_apply;
      [apply alpha_eq_sym;exact ht|apply alpha_eq_refl]
    |].
  eapply approx_alpha_rw_l_aux;
    [apply implies_alpha_eq_mk_apply;
      [apply implies_alpha_eq_mk_fresh;
        apply alpha_eq_sym;exact ht
      |apply alpha_eq_refl]
    |].
  clear dependent t.
  rename ispt' into ispt.
  rename t' into t.

  apply approx_assume_hasvalue;
    try (apply isprogram_apply);
    try (apply isprogram_fresh);
    try (apply isprog_vars_apply_implies);
    eauto 3 with slow;[].

  introv hv.
  pose proof (fresh_atom o (get_utokens t ++ get_utokens u)) as fa.
  destruct fa as [a fa].
  allrw in_app_iff; allrw not_over_or; repnd.

  apply hasvalue_like_apply in hv;
    try (apply wf_fresh);
    eauto 3 with slow.

  repndors; exrepnd.

  - eapply approx_trans;
      [apply reduces_to_implies_approx2;
        [apply isprogram_apply;
          try (apply isprogram_fresh);
          eauto 3 with slow
        |eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact hv0|];
         apply reduces_to_if_step;csunf;simpl;auto]
      |].
    unfold apply_bterm; simpl; allrw @fold_subst.

    pose proof (fresh_reduces_to_implies lib v t (mk_lam v0 b) a) as h.
    repeat (autodimp h hyp); unfold isvalue_like; simpl; tcsp; eauto 3 with slow;[].
    exrepnd.

    pose proof (unfold_subst_utokens [(a,mk_var v)] u0) as unf.
    exrepnd.
    rw unf0 in h0.
    allsimpl; allrw disjoint_singleton_r.

    assert {v1 : NVar & {t1 : NTerm & t' = mk_lam v1 t1}} as e.
    { apply alpha_eq_mk_lam in h0; exrepnd.
      destruct t' as [v1|f1|op1 bs1]; ginv.
      dopid op1 as [can|ncan|exc|abs] Case; ginv.
      destruct can; ginv.
      - allsimpl.
        repeat (destruct bs1; allsimpl; ginv).
        destruct b0 as [l1 t1].
        repeat (destruct l1; allsimpl; ginv).
        fold_terms; ginv.
        eexists; eexists; eauto.
      - allsimpl.
        unfold subst_utok in h2; allsimpl; boolvar; ginv.
    }

    exrepnd; subst; allsimpl; fold_terms.
    allrw app_nil_r; allrw not_over_or; repnd.
    unfold maybe_new_var in h0; allrw memvar_singleton; boolvar; tcsp;[].
    apply alpha_eq_sym in unf1.
    apply alpha_eq_mk_lam in unf1; exrepnd; subst.
    apply alpha_eq_mk_lam in h0; exrepnd; subst; ginv.

    pose proof (reduces_to_fresh2 lib (mk_apply t u) (subst b' v' u) v a) as q.
    repeat (autodimp q hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms.
      rw (lsubst_aux_trivial_cl_term2 u); eauto 3 with slow.
      rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
      allrw @fold_subst.
      eapply reduces_to_if_split1;[apply reduces_to_prinarg; exact h1|].
      csunf; simpl; auto. }
    exrepnd.

    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_fresh;
           apply isprog_vars_apply;
           dands;eauto 3 with slow
         |exact q1]
      ].

    eapply approx_alpha_rw_r_aux;
      [apply alpha_eq_sym;
        apply implies_alpha_eq_mk_fresh;
        exact q0
      |].

    pose proof (lsubst_alpha_congr4 [v'0] [v'] t1 b' [(v'0,u)] [(v',u)]) as aeq.
    allsimpl.
    repeat (autodimp aeq hyp); eauto 3 with slow;[].
    allrw @fold_subst.

    eapply approx_alpha_rw_r_aux;
      [apply implies_alpha_eq_mk_fresh;
        apply alpha_eq_subst_utokens_same;
        exact aeq
      |].

    pose proof (lsubst_alpha_congr4
                  [v0] [v'0] b
                  (mk_fresh v (subst_utokens_aux t1 [(a,mk_var v)]))
                  [(v0,u)] [(v'0,u)]) as aeq'.
    allsimpl.
    repeat (autodimp aeq' hyp); eauto 3 with slow;[].
    allrw @fold_subst.

    eapply approx_alpha_rw_l_aux;
      [apply alpha_eq_sym;exact aeq'|].

    applydup @reduces_to_preserves_isprog in h1 as ispb';
      try (apply subst_preserves_isprog);
      eauto 3 with slow;[].
    apply isprog_lam_iff in ispb'.
    apply alpha_eq_bterm_sym in unf1.
    applydup @alpha_eq_bterm_preserves_isprog_vars in unf1; auto;[].

    apply alpha_implies_approx3;
      try (apply isprogram_subst_if_bt);
      try (apply isprog_vars_iff_isprogram_bt);
      try (apply isprog_vars_fresh_implies);
      try (apply implies_isprog_vars_subst_utokens_aux);
      eauto 3 with slow;[].

    rw @cl_subst_subst_aux; eauto 3 with slow;[].
    unfold subst_aux; simpl; rw memvar_singleton; boolvar; tcsp;[].
    fold_terms.
    apply implies_alpha_eq_mk_fresh.

    rw @lsubst_aux_subst_utokens_aux_disj;
      unfold get_utokens_sub;
      allsimpl; allrw app_nil_r; allrw disjoint_singleton_r;
      allsimpl; tcsp;
      eauto 3 with slow;[].

    rw @cl_subst_subst_aux; eauto 3 with slow;[].
    unfold subst_aux.

    unfold subst_utokens; simpl; boolvar; allrw disjoint_singleton_r; eauto 3 with slow.
    destruct n; intro i.
    apply subset_bound_vars_lsubst_aux in i; allsimpl; allrw app_nil_r.
    allrw in_app_iff; sp.

  - eapply approx_trans;
      [apply reduces_to_implies_approx2;
        [apply isprogram_apply;
          try (apply isprogram_fresh);
          eauto 3 with slow
        |eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact hv1|];
         apply reduces_to_if_step;csunf;simpl;auto]
      |].
    unfold apply_bterm; simpl; allrw @fold_subst.

    pose proof (fresh_reduces_to_implies lib v t (mk_nseq s) a) as h.
    repeat (autodimp h hyp); unfold isvalue_like; simpl; tcsp; eauto 3 with slow;[].
    exrepnd.

    pose proof (unfold_subst_utokens [(a,mk_var v)] u0) as unf.
    exrepnd.
    rw unf0 in h0.
    allsimpl; allrw disjoint_singleton_r.
    destruct t' as [x|f|op bs]; allsimpl; GC; try (complete (inversion h0));[].
    dopid op as [can|ncan|exc|abs] Case; try (complete (inversion h0));[].
    destruct can; allsimpl; try (complete (inversion h0));
    [|unfold subst_utok in h0; allsimpl; boolvar; allsimpl; inversion h0].
    apply alpha_eq_mk_nseq in h0.
    destruct bs; allsimpl; ginv; fold_terms; ginv; GC.
    apply alpha_eq_sym in unf1.
    apply alpha_eq_mk_nseq in unf1; subst.
    clear unf0.

    pose proof (reduces_to_fresh2 lib (mk_apply t u) (mk_apseq s u) v a) as q.
    repeat (autodimp q hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms.
      rw (lsubst_aux_trivial_cl_term2 u); eauto 3 with slow.
      rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
      allrw @fold_subst.
      eapply reduces_to_if_split1;[apply reduces_to_prinarg; exact h1|].
      csunf; simpl; auto. }
    exrepnd.

    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_fresh;
           apply isprog_vars_apply;
           dands;eauto 3 with slow
         |exact q1]
      ].

    eapply approx_alpha_rw_r_aux;
      [apply alpha_eq_sym;
        apply implies_alpha_eq_mk_fresh;
        exact q0
      |].
    unfold subst_utokens; simpl; allrw app_nil_r.
    boolvar; allrw disjoint_singleton_r; tcsp;[].
    fold_terms.
    rw @trivial_subst_utokens_aux; simpl; allrw disjoint_singleton_r; auto.

    eapply cequiv_le_approx.
    apply cequiv_sym.
    apply cequiv_shadowed_fresh.
    apply isprogram_apseq; eauto 3 with slow.

  - eapply approx_trans;
      [apply reduces_to_implies_approx2;
        [apply isprogram_apply;
          try (apply isprogram_fresh);
          eauto 3 with slow
        |eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact hv1|];
         apply reduces_to_if_step;csunf;simpl;auto]
      |].
    unfold apply_bterm; simpl; allrw @fold_subst.

    pose proof (fresh_reduces_to_implies lib v t (sterm s) a) as h.
    repeat (autodimp h hyp); unfold isvalue_like; simpl; tcsp; eauto 3 with slow;[].
    exrepnd.

    pose proof (unfold_subst_utokens [(a,mk_var v)] u0) as unf.
    exrepnd.
    rw unf0 in h0.
    allsimpl; allrw disjoint_singleton_r.

    destruct t' as [x|f|op bs]; allsimpl; GC; try (complete (inversion h0));
    [|destruct op; allsimpl; try (complete (inversion h0));[];
      destruct c; allsimpl; try (complete (inversion h0));[];
      allunfold @subst_utok; allsimpl; boolvar; allsimpl; try (complete (inversion h0))].

    inversion h0 as [|? ? aeq|]; subst; clear h0.
    apply alpha_eq_sym in unf1.
    apply alpha_eq_sterm in unf1; exrepnd; subst.
    unfold subst_utokens in unf0; allsimpl; ginv.
    clear unf2.

    pose proof (reduces_to_fresh2 lib (mk_apply t u) (mk_eapply (sterm f) u) v a) as q.
    repeat (autodimp q hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms.
      rw (lsubst_aux_trivial_cl_term2 u); eauto 3 with slow.
      rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
      allrw @fold_subst.
      eapply reduces_to_if_split1;[apply reduces_to_prinarg; exact h1|].
      csunf; simpl; auto. }
    exrepnd.

    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_fresh;
           apply isprog_vars_apply;
           dands;eauto 3 with slow
         |exact q1]
      ].

    eapply approx_alpha_rw_r_aux;
      [apply alpha_eq_sym;
        apply implies_alpha_eq_mk_fresh;
        exact q0
      |].
    unfold subst_utokens; simpl; allrw app_nil_r.
    boolvar; allrw disjoint_singleton_r; tcsp;[].
    fold_terms.
    rw @trivial_subst_utokens_aux; simpl; allrw disjoint_singleton_r; auto.

    applydup @reduces_to_preserves_program in hv1;
      try (apply isprogram_fresh; auto);[].

    eapply cequiv_le_approx.
    apply cequiv_sym.
    eapply cequiv_rw_r_eauto;
      [apply implies_alpha_eq_mk_eapply;
        [apply alpha_eq_sym;constructor;apply aeq|apply alpha_eq_refl]
      |].
    apply cequiv_shadowed_fresh.
    apply isprogram_eapply; eauto 2 with slow.
    eapply alpha_prog_eauto;[|exact hv2]; auto.

  - eapply approx_trans;
      [apply reduces_to_implies_approx2;
        [apply isprogram_apply;
          try (apply isprogram_fresh);
          eauto 3 with slow
        |eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact hv1|];
         apply reduces_to_if_step;csunf;simpl;auto]
      |].
    fold_terms.

    pose proof (fresh_reduces_to_implies lib v t (mk_exception n e) a) as h.
    repeat (autodimp h hyp); unfold isvalue_like; simpl; tcsp; eauto 3 with slow;[].
    exrepnd.

    pose proof (unfold_subst_utokens [(a,mk_var v)] u0) as unf.
    exrepnd.
    rw unf0 in h0; clear unf0.
    allsimpl; allrw disjoint_singleton_r.

    assert {n1 : NTerm & {e1 : NTerm & t' = mk_exception n1 e1}} as xx.
    { apply alpha_eq_exception in h0; exrepnd.
      destruct t' as [v1|f1|op1 bs1]; ginv.
      dopid op1 as [can|ncan|exc|abs] Case; ginv.
      - destruct can; ginv.
        allsimpl.
        unfold subst_utok in h2; allsimpl; boolvar; ginv.
      - allsimpl.
        repeat (destruct bs1; allsimpl; ginv).
        destruct b as [l1 t1].
        destruct b0 as [l2 t2].
        repeat (destruct l1; allsimpl; ginv).
        repeat (destruct l2; allsimpl; ginv).
        fold_terms; ginv.
        eexists; eexists; eauto. }

    exrepnd; subst; allsimpl; fold_terms.
    allrw app_nil_r; allrw not_over_or; repnd.
    unfold maybe_new_var in h0; allrw memvar_singleton; boolvar; tcsp; GC;[].
    apply alpha_eq_sym in unf1.
    apply alpha_eq_exception in unf1; exrepnd; subst.
    apply alpha_eq_exception in h0; exrepnd; subst; ginv.

    pose proof (reduces_to_fresh2 lib (mk_apply t u) (mk_exception a' e') v a) as q.
    repeat (autodimp q hyp); simpl;
    try (apply wf_apply); eauto 3 with slow;
    allrw app_nil_r; allrw in_app_iff; tcsp.
    { unfsubst; simpl; fold_terms.
      rw (lsubst_aux_trivial_cl_term2 u); eauto 3 with slow.
      rw <- @cl_lsubst_lsubst_aux; eauto 3 with slow.
      allrw @fold_subst.
      eapply reduces_to_if_split1;[apply reduces_to_prinarg; exact h1|].
      csunf; simpl; auto. }
    exrepnd.
    allrw not_over_or; repnd.

    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_fresh;
           apply isprog_vars_apply;
           dands;eauto 3 with slow
         |exact q1]
      ].

    eapply approx_alpha_rw_r_aux;
      [apply alpha_eq_sym;
        apply implies_alpha_eq_mk_fresh;
        exact q0
      |].

    eapply approx_alpha_rw_r_aux;
      [apply implies_alpha_eq_mk_fresh;
        apply alpha_eq_subst_utokens_same;
        apply implies_alphaeq_exception;
        [exact unf3|exact unf1]
      |].

    unfold subst_utokens; simpl; allrw app_nil_r; fold_terms.
    boolvar; allrw disjoint_singleton_r; allrw in_app_iff;
    allrw not_over_or; try (complete (destruct n0; sp));[].
    repnd; GC.

    applydup @reduces_to_preserves_isprog in h1 as ispb';
      try (apply subst_preserves_isprog);
      eauto 3 with slow;[].
    apply isprog_exception_iff in ispb'; repnd.
    apply alpha_eq_sym in unf1.
    apply alpha_eq_sym in unf3.
    applydup @alpha_eq_preserves_isprog in unf1;auto.
    applydup @alpha_eq_preserves_isprog in unf3;auto.

    eapply approx_trans;
      [|apply reduces_to_implies_approx1;
         [apply isprogram_fresh;
           apply isprog_vars_exception_implies;
           try (apply implies_isprog_vars_subst_utokens_aux);
           eauto 3 with slow
         |apply reduces_to_if_step;csunf;simpl;auto]
      ].
    fold_terms.
    unfold maybe_new_var; simpl.

    apply alpha_eq_sym in h0.
    apply alpha_eq_sym in h3.
    applydup @alpha_eq_preserves_isprog in h0;auto;
    try(apply isprog_fresh_implies;
        try (apply implies_isprog_vars_subst_utokens_aux);
        eauto 3 with slow).
    applydup @alpha_eq_preserves_isprog in h3;auto;
    try(apply isprog_fresh_implies;
        try (apply implies_isprog_vars_subst_utokens_aux);
        eauto 3 with slow).

    apply alpha_implies_approx3;
      try (apply isprogram_exception);
      eauto 3 with slow.

    apply implies_alphaeq_exception; eauto 3 with slow.
Qed.

Lemma cequiv_apply_fresh {o} :
  forall lib v (t : @NTerm o) a,
    isprog a
    -> isprog_vars [v] t
    -> cequiv
         lib
         (mk_fresh v (mk_apply t a))
         (mk_apply (mk_fresh v t) a).
Proof.
  introv ispa ispt.
  split.
  - apply approx_apply_fresh1; auto.
  - apply approx_apply_fresh2; auto.
Qed.

Lemma cequivc_apply_fresh {o} :
  forall lib v (t : @CVTerm o [v]) a,
    cequivc
      lib
      (mkc_fresh v (mkcv_apply [v] t (mk_cv [v] a)))
      (mkc_apply (mkc_fresh v t) a).
Proof.
  introv.
  destruct_cterms.
  unfold cequivc; simpl.
  apply cequiv_apply_fresh;auto.
Qed.

Lemma fresh_in_function {o} :
  forall lib v (t1 t2 : @CVTerm o [v]) A x B,
    type lib A
    -> (forall a1 a2,
          equality lib a1 a2 A
          -> tequality lib (substc a1 x B) (substc a2 x B))
    -> (forall a1 a2,
          equality lib a1 a2 A
          -> equality
               lib
               (mkc_fresh v (mkcv_apply [v] t1 (mk_cv [v] a1)))
               (mkc_fresh v (mkcv_apply [v] t2 (mk_cv [v] a2)))
               (substc a1 x B))
    -> equality lib (mkc_fresh v t1) (mkc_fresh v t2) (mkc_function A x B).
Proof.
  introv tA tB imp.
  apply equality_in_function.
  dands; auto.
  introv ea.
  applydup imp in ea.

  eapply equality_respects_cequivc_left in ea0;
    [|apply cequivc_apply_fresh].

  eapply equality_respects_cequivc_right in ea0;
    [|apply cequivc_apply_fresh].

  auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
