(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


Require Export cequiv.
Require Export csubst2.


Definition pv_olift {o} (R : NTrel) (x y : @NTerm o) vs : [univ] :=
  forall sub: Sub,
    prog_sub sub
    -> dom_sub sub = vs
    -> R (lsubst x sub) (lsubst y sub).

Definition sub_find_def {o} (sub : @Sub o) v d : NTerm :=
  match sub_find sub v with
    | Some t => t
    | None => d
  end.

Fixpoint sub_select {o} (sub : @Sub o) (vars : list NVar) (d : NTerm) : Sub :=
  match vars with
    | nil => nil
    | v :: vs => (v,sub_find_def sub v d) :: sub_select sub vs d
  end.

Lemma dom_sub_sub_select {o} :
  forall (s : @Sub o) d vs,
    dom_sub (sub_select s vs d) = vs.
Proof.
  induction vs; introv; allsimpl; tcsp.
  rw IHvs; auto.
Qed.

Definition eq_option {o} (op1 op2 : option (@NTerm o)) :=
  match op1, op2 with
    | Some t1, Some t2 => t1 = t2
    | None, None => True
    | _,_ => False
  end.

Definition ext_eq_subs {o} vs (sub1 sub2 : @Sub o) :=
  forall v,
    LIn v vs
    -> eq_option (sub_find sub1 v) (sub_find sub2 v).

Lemma eq_lsubst_aux_if_ext_eq {o} :
  forall (t : @NTerm o) sub1 sub2,
    ext_eq_subs (free_vars t) sub1 sub2
    -> disjoint (bound_vars t) (sub_free_vars sub1)
    -> disjoint (bound_vars t) (sub_free_vars sub2)
    -> lsubst_aux t sub1 = lsubst_aux t sub2.
Proof.
  nterm_ind1s t as [v|f|op bs ind] Case; introv ext d1 d2; allsimpl; auto.

  - Case "vterm".
    pose proof (ext v) as h.
    remember (sub_find sub1 v) as sf1; symmetry in Heqsf1; destruct sf1;
    remember (sub_find sub2 v) as sf2; symmetry in Heqsf2; destruct sf2;
    allsimpl; tcsp.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t].
    allsimpl.
    f_equal.

    pose proof (ind t t l i) as h; clear ind.
    autodimp h hyp; eauto 3 with slow.
    apply h.

    + introv j.
      allrw @sub_find_sub_filter_eq.
      destruct (in_deq _ deq_nvar v l) as [d|d]; boolvar; tcsp; GC.
      apply ext.
      rw lin_flat_map.
      eexists; dands; eauto.
      simpl.
      rw in_remove_nvars; sp.

    + introv j k.
      pose proof (d1 t0) as q.
      autodimp q hyp.
      { rw lin_flat_map.
        eexists; dands; eauto.
        simpl.
        rw in_app_iff; sp. }
      apply subset_sub_free_vars_sub_filter in k; sp.

    + introv j k.
      pose proof (d2 t0) as q.
      autodimp q hyp.
      { rw lin_flat_map.
        eexists; dands; eauto.
        simpl.
        rw in_app_iff; sp. }
      apply subset_sub_free_vars_sub_filter in k; sp.
Qed.

Lemma cl_eq_lsubst_if_ext_eq {o} :
  forall (t : @NTerm o) sub1 sub2,
    cl_sub sub1
    -> cl_sub sub2
    -> ext_eq_subs (free_vars t) sub1 sub2
    -> lsubst t sub1 = lsubst t sub2.
Proof.
  introv cl1 cl2 ext.
  repeat unflsubst.
  apply eq_lsubst_aux_if_ext_eq; eauto 3 with slow;
  rw @sub_free_vars_if_cl_sub; auto.
Qed.

Lemma implies_closed_sub_find_def {o} :
  forall (s : @Sub o) v d,
    closed d
    -> cl_sub s
    -> closed (sub_find_def s v d).
Proof.
  introv ispd isps.
  unfold sub_find_def.
  remember (sub_find s v) as sf; destruct sf; symmetry in Heqsf; auto.
  apply sub_find_some in Heqsf.
  rw @cl_sub_eq in isps.
  apply in_sub_eta in Heqsf; repnd.
  apply isps in Heqsf; eauto 3 with slow.
Qed.
Hint Resolve implies_closed_sub_find_def : slow.

Lemma prog_sub_sub_keep {o} :
  forall (s : @Sub o) vs, prog_sub s -> prog_sub (sub_keep s vs).
Proof.
  induction s; introv ps; allsimpl; auto.
  destruct a; boolvar; allsimpl; auto;
  allrw @prog_sub_cons; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve prog_sub_sub_keep : slow.

Lemma in_dom_sub_sub_keep_implies {o} :
  forall (sub : @Sub o) vs v,
    LIn v (dom_sub (sub_keep sub vs))
    <=> (LIn v vs # LIn v (dom_sub sub)).
Proof.
  induction sub; split; introv i; repnd; allsimpl; tcsp.
  - boolvar; allsimpl; repndors; subst; tcsp; apply IHsub in i; sp.
  - boolvar; allsimpl; repndors; subst; tcsp.
    + right; apply IHsub; sp.
    + apply IHsub; sp.
Qed.

Lemma implies_isprog_sub_find_def {o} :
  forall (s : @Sub o) v d,
    isprog d
    -> prog_sub s
    -> isprog (sub_find_def s v d).
Proof.
  introv ispd isps.
  unfold sub_find_def.
  remember (sub_find s v) as sf; destruct sf; symmetry in Heqsf; auto.
  apply sub_find_some in Heqsf.
  rw <- @prog_sub_eq in isps.
  apply in_sub_eta in Heqsf; repnd.
  apply isps in Heqsf; eauto 3 with slow.
Qed.
Hint Resolve implies_isprog_sub_find_def : slow.

Lemma prog_sub_sub_select {o} :
  forall (s : @Sub o) d vs,
    isprog d
    -> prog_sub s
    -> prog_sub (sub_select s vs d).
Proof.
  induction vs; introv pd ps; allsimpl; eauto 3 with slow.
  apply prog_sub_cons; dands; auto.
  destruct a; boolvar; allsimpl; auto;
  allrw @prog_sub_cons; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve prog_sub_sub_select : slow.

Lemma sub_find_sub_select {o} :
  forall (s : @Sub o) vs d v,
    sub_find (sub_select s vs d) v
    = if memvar v vs
      then Some (sub_find_def s v d)
      else None.
Proof.
  induction vs; introv; simpl; auto.
  allrw memvar_cons; boolvar; tcsp.
  - rw IHvs; boolvar; tcsp.
  - rw IHvs; boolvar; tcsp.
Qed.

Lemma cl_sub_sub_select {o} :
  forall (s : @Sub o) d vs,
    closed d
    -> cl_sub s
    -> cl_sub (sub_select s vs d).
Proof.
  induction vs; introv pd ps; allsimpl; eauto 3 with slow.
  apply cl_sub_cons; dands; auto.
  destruct a; boolvar; allsimpl; auto;
  allrw @cl_sub_cons; repnd; dands; eauto 3 with slow.
Qed.
Hint Resolve cl_sub_sub_select : slow.

Lemma cl_lsubst_trim_select {o} :
  forall t (sub : @Sub o) lv d,
    cl_sub sub
    -> closed d
    -> (forall v, LIn v (free_vars t) -> (LIn v lv <=> LIn v (dom_sub sub)))
    -> lsubst t sub = lsubst t (sub_select sub lv d).
Proof.
  introv cls cld sv.
  apply cl_eq_lsubst_if_ext_eq; eauto 3 with slow.
  introv i.
  applydup sv in i.
  rw @sub_find_sub_select.
  unfold sub_find_def.
  boolvar.
  - applydup i0 in Heqb.
    apply in_dom_sub_exists in Heqb0; exrepnd.
    rw Heqb1; simpl; auto.
  - rw @sub_find_none_if; simpl; auto.
    intro h.
    apply i0 in h; sp.
Qed.

Lemma isvalue_like_lam {o} :
  forall v (t : @NTerm o), isvalue_like (mk_lam v t).
Proof.
  introv.
  unfold isvalue_like; simpl; tcsp.
Qed.
Hint Resolve isvalue_like_lam : slow.

Lemma cl_olift_iff_pv_olift {o} :
  forall R (x y : @NTerm o) vs,
    isprog_vars vs x
    -> isprog_vars vs y
    -> (pv_olift R x y vs <=> cl_olift R x y).
Proof.
  introv ispx ispy.
  unfold pv_olift, cl_olift.
  split; intro h; repnd; dands; eauto 3 with slow.

  - introv ps isp1 isp2.
    applydup @lsubst_program_implies in isp1.
    applydup @lsubst_program_implies in isp2.
    applydup @isprog_vars_eq in ispx; repnd.
    applydup @isprog_vars_eq in ispy; repnd.
    allrw @subvars_eq.

    pose proof (h (sub_select sub vs mk_axiom)) as q; clear h.
    rw @dom_sub_sub_select in q.
    repeat (autodimp q hyp); eauto 2 with slow.

    rw <- @cl_lsubst_trim_select in q; eauto 2 with slow;
    [|introv i;applydup isp0 in i;apply ispx1 in i; sp].

    rw <- @cl_lsubst_trim_select in q; eauto 2 with slow.
    introv i;applydup isp3 in i;apply ispy1 in i; sp.

  - introv ps e.
    apply h; auto.

    + apply isprogram_lsubst_if_isprog_sub; eauto 2 with slow.
      introv i.
      apply isprog_vars_eq in ispx; repnd.
      allrw subvars_eq.
      apply ispx0 in i; subst; sp.

    + apply isprogram_lsubst_if_isprog_sub; eauto 2 with slow.
      introv i.
      apply isprog_vars_eq in ispy; repnd.
      allrw subvars_eq.
      apply ispy0 in i; subst; sp.
Qed.

Lemma implies_approxc_lam {o} :
  forall lib v (t1 t2 : @CVTerm o [v]),
    (forall u : CTerm, cequivc lib (substc u v t1) (substc u v t2))
    -> approxc lib (mkc_lam v t1) (mkc_lam v t2).
Proof.
  introv imp.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allunfold @approxc; allsimpl.

  constructor.
  unfold close_comput; dands;
  try (apply isprogram_lam);
  eauto 3 with slow.

  + introv comp.
    apply computes_to_value_isvalue_eq in comp;
      try (apply isvalue_mk_lam); eauto 3 with slow.
    unfold mk_lam in comp; ginv; fold_terms.
    exists [bterm [v] x]; fold_terms.
    dands.
    { apply computes_to_value_isvalue_refl;
      try (apply isvalue_mk_lam); eauto 3 with slow. }

    unfold lblift; simpl; dands; auto.
    introv ltn.
    destruct n; try omega; clear ltn.
    unfold selectbt; simpl.
    unfold blift.
    exists [v] x0 x; dands; eauto 3 with slow.
    apply clearbots_olift.
    apply cl_olift_implies_olift; eauto 3 with slow.

    pose proof (cl_olift_iff_pv_olift (approx lib) x0 x [v]) as xx.
    repeat (autodimp xx hyp).
    apply xx; clear xx.
    introv ps e.
    destruct sub as [|p s]; allsimpl; ginv.
    destruct s; ginv.
    destruct p as [z u]; allsimpl.
    allrw @fold_subst.
    allrw @prog_sub_cons; repnd.
    pose proof (imp (mk_cterm u ps0)) as h; clear imp; allsimpl.
    destruct h; sp.

  + introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.

  + introv comp.
    apply reduces_to_if_isvalue_like in comp; ginv; eauto 3 with slow.
Qed.

Lemma cequivc_iff_approxc {o} :
  forall lib (a b : @CTerm o),
    cequivc lib a b <=> (approxc lib a b # approxc lib b a).
Proof.
  introv; destruct_cterms; unfold cequivc, approxc; simpl; sp.
Qed.

Lemma implies_cequivc_lam {o} :
  forall lib v (t1 t2 : @CVTerm o [v]),
    (forall u : CTerm, cequivc lib (substc u v t1) (substc u v t2))
    -> cequivc lib (mkc_lam v t1) (mkc_lam v t2).
Proof.
  introv imp.
  apply cequivc_iff_approxc; dands.
  - apply implies_approxc_lam; auto.
  - apply implies_approxc_lam; auto.
    introv.
    apply cequivc_sym; auto.
Qed.

Lemma implies_approx_lam2 {o} :
  forall lib v1 v2 (t1 t2 : @NTerm o),
    isprog_vars [v1] t1
    -> isprog_vars [v2] t2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v1 u) (subst t2 v2 u))
    -> approx lib (mk_lam v1 t1) (mk_lam v2 t2).
Proof.
  introv isp1 isp2 imp.

  constructor.
  unfold close_comput; dands;
  try (apply isprogram_lam);
  eauto 3 with slow.

  - introv comp.
    apply computes_to_value_isvalue_eq in comp;
      try (apply isvalue_mk_lam); eauto 3 with slow.
    unfold mk_lam in comp; ginv; fold_terms.
    exists [bterm [v2] t2]; fold_terms.
    dands.
    { apply computes_to_value_isvalue_refl;
      try (apply isvalue_mk_lam); eauto 3 with slow. }

    unfold lblift; simpl; dands; auto.
    introv ltn.
    destruct n; try omega; clear ltn.
    unfold selectbt; simpl.
    unfold blift.
    exists [v1] t1 (subst t2 v2 (mk_var v1)); dands; eauto 3 with slow.

    + apply clearbots_olift.
      apply cl_olift_implies_olift; eauto 3 with slow.

      pose proof (cl_olift_iff_pv_olift (approx lib) t1 (subst t2 v2 (mk_var v1)) [v1]) as xx.
      repeat (autodimp xx hyp).
      { clear imp; allrw @isprog_vars_eq; repnd; dands.
        - eapply subvars_eqvars;
          [|apply eqvars_sym;apply eqvars_free_vars_disjoint].
          simpl.
          rw subvars_app_l; dands.
          + apply subvars_remove_nvars; simpl.
            eapply subvars_trans;eauto.
            rw subvars_prop; simpl; tcsp.
          + boolvar; simpl; eauto 3 with slow.
        - apply nt_wf_subst; eauto 3 with slow. }
      apply xx; clear xx.
      introv ps e.
      destruct sub as [|p s]; allsimpl; ginv.
      destruct s; ginv.
      destruct p as [z u]; allsimpl.
      allrw @fold_subst.
      allrw @prog_sub_cons; repnd.
      pose proof (imp u) as h; clear imp; allsimpl.
      autodimp h hyp; eauto 3 with slow.
      destruct h; sp.
      eapply approx_trans; eauto.

      eapply approx_alpha_rw_r_aux;
        [apply alpha_eq_sym;apply combine_sub_nest|].
      simpl.
      allrw @fold_subst.
      rw @subst_mk_var1.

      destruct (deq_nvar v2 z); subst.

      * pose proof (cl_lsubst_app_sub_filter t2 [(z,u)] [(z,u)]) as h; allsimpl.
        autodimp h hyp; eauto 3 with slow.
        allrw memvar_singleton; boolvar; rw h; eauto 3 with slow.

      * pose proof (lsubst_sub_filter_alpha t2 [(v2, u), (z, u)] [z]) as h.
        allrw disjoint_singleton_r; allsimpl.
        allrw memvar_singleton; boolvar; tcsp.
        autodimp h hyp.
        { allrw @isprog_vars_eq; repnd.
          allrw subvars_eq.
          introv h; apply isp0 in h; allsimpl; tcsp. }

        eapply approx_alpha_rw_r_aux;[exact h|].
        allrw @fold_subst; eauto 3 with slow.

    + pose proof (alpha_eq_bterm_single_change t2 v2) as h.
      allrw subset_singleton_r.
      autodimp h hyp.
      { introv ix.
        clear imp.
        allrw @isprog_vars_eq; repnd.
        allrw subvars_eq.
        apply isp3 in ix; allsimpl; tcsp. }
      apply h.

  - introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.

  - introv comp.
    apply reduces_to_if_isvalue_like in comp; ginv; eauto 3 with slow.
Qed.

Lemma implies_approxc_lam2 {o} :
  forall lib v1 v2 (t1 : @CVTerm o [v1]) t2,
    (forall u : CTerm, cequivc lib (substc u v1 t1) (substc u v2 t2))
    -> approxc lib (mkc_lam v1 t1) (mkc_lam v2 t2).
Proof.
  introv imp.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allunfold @approxc; allsimpl.

  apply implies_approx_lam2; auto.
  introv isp.
  apply isprogram_eq in isp.
  pose proof (imp (mk_cterm u isp)) as k; allsimpl; auto.
Qed.

Lemma implies_cequivc_lam2 {o} :
  forall lib v1 v2 (t1 : @CVTerm o [v1]) t2,
    (forall u : CTerm, cequivc lib (substc u v1 t1) (substc u v2 t2))
    -> cequivc lib (mkc_lam v1 t1) (mkc_lam v2 t2).
Proof.
  introv imp.
  apply cequivc_iff_approxc; dands.
  - apply implies_approxc_lam2; auto.
  - apply implies_approxc_lam2; auto.
    introv.
    apply cequivc_sym; auto.
Qed.

Lemma nt_wf_lambda_iff {p} :
  forall (bs : list (@BTerm p)),
    nt_wf (oterm (Can NLambda) bs)
    <=> {v : NVar
        $ {b : NTerm
        $ bs = [bterm [v] b]
        # nt_wf b}}.
Proof.
  introv; split; intro k.
  - inversion k as [|?|? ? imp e]; clear k; subst.
    allsimpl.
    repeat (destruct bs; allsimpl; ginv).
    destruct b as [l1 t1].
    allunfold @num_bvars; allsimpl.
    repeat (destruct l1; ginv).
    pose proof (imp (bterm [n] t1)) as h1.
    autodimp h1 hyp.
    clear imp.
    allrw @bt_wf_iff.
    exists n t1; dands; auto.
  - exrepnd; subst.
    repeat constructor.
    introv i; allsimpl; repndors; subst; tcsp.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/")
*** End:
*)
