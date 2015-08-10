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


Require Export terms_per.
Require Export csubst2.

(*
Lemma subst_mk_erase :
  forall a v u,
    isprog u
    -> subst (mk_erase a) v u = mk_erase (subst a v u).
Proof.
  introv isp.
  unfold subst, mk_erase, mk_ufun, newvar, fresh_var; simpl.
  fold nvarx.
  destruct (deq_nvar nvarx v); subst.
  apply subst_mk_isect2; auto.
  apply subst_mk_isect; auto.
Qed.
*)

Lemma cover_vars_erase_rel {o} :
  forall a s,
    cover_vars (@erase_rel o a) s
    <=> cover_vars a s.
Proof.
  introv.
  unfold erase_rel.
  remember (newvars2 [a]); repnd.
  apply newvars2_prop2 in Heqp; allsimpl; allrw app_nil_r; repnd.
  rw @cover_vars_lam.
  rw @cover_vars_upto_lam.
  rw <- @csub_filter_app_r; simpl.
  apply cover_vars_upto_csub_filter_disjoint; sp.
  rw eqvars_prop; simpl; sp; split; sp.
  repeat (rw disjoint_cons_r); sp.
Qed.

Lemma cover_vars_upto_erase_rel {o} :
  forall a s vs,
    cover_vars_upto (@erase_rel o a) s vs
    <=> cover_vars_upto a s vs.
Proof.
  introv.
  unfold erase_rel.
  remember (newvars2 [a]); repnd.
  apply newvars2_prop2 in Heqp; allsimpl; allrw app_nil_r; repnd.
  rw @cover_vars_upto_lam.
  rw @cover_vars_upto_lam.
  rw <- @csub_filter_app_r; simpl.
  assert (p :: p0 :: vs = [p,p0] ++ vs) as e by sp; rw e; clear e.
  apply cover_vars_upto_csub_filter_app.
  rw eqvars_prop; simpl; sp; split; sp.
  repeat (rw disjoint_cons_r); sp.
Qed.

Lemma covered_erase_rel {o} :
  forall a vs,
    covered (@erase_rel o a) vs
    <=> covered a vs.
Proof.
  introv.
  unfold erase_rel.
  remember (newvars2 [a]); repnd.
  apply newvars2_prop2 in Heqp; allsimpl; allrw app_nil_r; repnd.
  rw @covered_lam.
  rw @covered_lam.
  generalize (covered_cons_weak_iff a p Heqp1 (p0 :: vs)); intro e; rw e; clear e.
  apply covered_cons_weak_iff; sp.
Qed.

Lemma cover_vars_erase {o} :
  forall a s,
    cover_vars (@erase o a) s
    <=> cover_vars a s.
Proof.
  introv.
  unfold erase.
  rw @cover_vars_pertype.
  rw @cover_vars_erase_rel; sp.
Qed.

Lemma cover_vars_upto_erase {o} :
  forall a s vs,
    cover_vars_upto (@erase o a) s vs
    <=> cover_vars_upto a s vs.
Proof.
  introv.
  unfold erase.
  rw @cover_vars_upto_pertype.
  rw @cover_vars_upto_erase_rel; sp.
Qed.

Lemma covered_erase {o} :
  forall a vs,
    covered (@erase o a) vs
    <=> covered a vs.
Proof.
  introv.
  rw @covered_pertype.
  apply covered_erase_rel.
Qed.

Lemma cover_vars_uand {o} :
  forall A B s,
    cover_vars (@mk_uand o A B) s
    <=> (cover_vars A s # cover_vars B s).
Proof.
  introv.
  rw @cover_vars_eq.
  rw @free_vars_uand.
  rw subvars_app_l; sp.
Qed.

Lemma cover_vars_mk_per_function_rel {o} :
  forall A B s,
    cover_vars (@mk_per_function_rel o A B) s
    <=> (cover_vars A s # cover_vars B s).
Proof.
  introv.
  allrw @cover_vars_eq.
  rw @free_vars_per_function_rel_eq.
  allrw subvars_app_l; split; sp.
Qed.

Lemma covered_per_function_rel {o} :
  forall a b vs,
    covered (@mk_per_function_rel o a b) vs
    <=> covered a vs
        # covered b vs.
Proof.
  introv.
  unfold covered.
  rw @free_vars_per_function_rel_eq.
  allrw subvars_app_l; split; sp.
Qed.

Lemma cover_vars_per_function {o} :
  forall A B s,
    cover_vars (@mk_per_function o A B) s
    <=> (cover_vars A s # cover_vars B s).
Proof.
  introv.
  unfold mk_per_function.
  rw @cover_vars_pertype.
  rw @cover_vars_mk_per_function_rel; sp.
Qed.

Lemma unfold_mk_uand {o} :
  forall A B,
    {v1, v2 : NVar
     $ @mk_uand o A B
       = mk_isect mk_base v1
                  (mk_isect (mk_halts (mk_var v1)) v2
                            (mk_isaxiom (mk_var v1) A B))
     # (v1, v2) = newvars2 [A, B] }.
Proof.
  introv.
  remember (newvarlst [A,B]) as v1.
  exists v1.
  remember (newvarlst ([A,B] ++ [mk_var v1])) as v2.
  exists v2.
  subst; sp.
Qed.

Lemma unfold_mk_per_function_rel {o} :
  forall A B,
    {v1, v2, v3, v4, v5 : NVar
     $ mk_per_function_rel A B
       = mk_lam
           v3
           (mk_lam
              v4
              (erase
                 (mk_isect
                    mk_base
                    v1
                    (mk_isect
                       mk_base
                       v2
                       (mk_isect
                          (mk_equality (mk_var v1) (mk_var v2) A)
                          v5
                          (mk_uand
                             (mk_equality
                                (mk_apply (mk_var v3) (mk_var v1))
                                (mk_apply (mk_var v4) (mk_var v2))
                                (mk_apply B (mk_var v1)))
                             (mk_tequality
                                (mk_apply B (mk_var v1))
                                (mk_apply B (@mk_var o v2)))))))))
     # (v1, v2, v3, v4, v5) = newvars5 [A, B] }.
Proof.
  introv.
  remember (newvarlst [A,B]) as v1.
  exists v1.
  remember (newvarlst ([A,B] ++ [mk_var v1])) as v2.
  exists v2.
  remember (newvarlst ([A,B] ++ [mk_var v1, mk_var v2])) as v3.
  exists v3.
  remember (newvarlst ([A,B] ++ [mk_var v1, mk_var v2, mk_var v3])) as v4.
  exists v4.
  remember (newvarlst ([A,B] ++ [mk_var v1, mk_var v2, mk_var v3, mk_var v4])) as v5.
  exists v5.
  subst; sp.
Qed.

(*
Lemma lsubstc_mk_per_function_rel :
  forall A B sub,
  forall w1 : wf_term A,
  forall w2 : wf_term B,
  forall w  : wf_term (mk_per_function_rel A B),
  forall c1 : cover_vars A sub,
  forall c2 : cover_vars B sub,
  forall c  : cover_vars (mk_per_function_rel A B) sub,
    alphaeqc
      (lsubstc (mk_per_function_rel A B) w sub c)
      (mkc_per_function_rel
         (lsubstc A w1 sub c1)
         (lsubstc B w2 sub c2)).
Proof.
  sp; unfold lsubstc; simpl.
  remember (isprog_csubst (mk_per_function_rel A B) sub w c) as isp1; clear Heqisp1.
  remember (isprog_mk_per_function_rel
              (csubst A sub)
              (csubst B sub)
              (isprog_csubst A sub w1 c1)
              (isprog_csubst B sub w2 c2)) as isp2; clear Heqisp2.
  generalize (unfold_mk_per_function_rel A B); introv eq; exrepnd.
  generalize (unfold_mk_per_function_rel (csubst A sub) (csubst B sub)); introv eq; exrepnd.

  unfold alphaeqc; simpl.
  clear isp1 isp2.

  rewrite eq1; clear eq1.
  rewrite eq3; clear eq3.

  repeat (rewrite csubst_mk_lam);
    repeat (rewrite csubst_mk_isect);
    repeat (rewrite csubst_mk_base);
    repeat (rewrite csubst_mk_equality);
    repeat (rewrite csubst_mk_apply);
    repeat (rewrite <- csub_filter_app_r); simpl;
    repeat (rewrite csubst_mk_var_out2; [idtac | complete sp]).

(*
  apply alpha_eq_lam.
  apply isprogram_lam.
  apply isprog_vars_lam.
  apply isprog_vars_isect.
  apply isprog_vars_base.
  apply isprog_vars_isect.
  apply isprog_vars_base.
  apply isprog_vars_isect.
  apply isprog_vars_equality.
  apply isprog_vars_var_if; sp.
  apply isprog_vars_var_if; sp.
  apply isprog_vars_csubst; sp.
  apply nt_wf_eq; sp.
admit.
  apply isprog_vars_equality.
  apply isprog_vars_apply; sp.
  apply isprog_vars_var_if; sp.
  apply isprog_vars_var_if; sp.
  apply isprog_vars_apply; sp.
  apply isprog_vars_var_if; sp.
  apply isprog_vars_var_if; sp.
  apply isprog_vars_apply; sp.
  apply isprog_vars_csubst; sp.
  apply nt_wf_eq; sp.
admit.
  apply isprog_vars_var_if; sp.
*)

Abort.

Lemma lsubstc_mk_per_function_rel_ex :
  forall A B w s c,
     {wa : wf_term A
     & {wb : wf_term B
     & {ca : cover_vars A s
     & {cb : cover_vars B s
        & alphaeqc
            (lsubstc (mk_per_function_rel A B) w s c)
            (mkc_per_function_rel
               (lsubstc A wa s ca)
               (lsubstc B wb s cb))}}}}.
Proof.
  introv.
  duplicate w as w'.
  rw wf_term_mk_per_function_rel in w; repnd.
  exists w0 w.
  duplicate c as c'.
  rw cover_vars_mk_per_function_rel in c; repnd.
  exists c0 c.

  unfold alphaeqc; simpl.
  allrw csubst_as_lsubst_aux.

(*
  unfold mk_per_function_rel at 1.
  remember (newvars5 [A,B]); repnd.
  allrw lsubst_aux_lam_csub2sub; allrw <- csub_filter_app_r.
  allrw lsubst_aux_isect_csub2sub; allrw <- csub_filter_app_r.
  allrw lsubst_aux_base_csub2sub.
  allrw lsubst_aux_equality_csub2sub; allrw <- csub_filter_app_r.
  allrw lsubst_aux_apply_csub2sub; allrw <- csub_filter_app_r.
  allrw lsubst_aux_var_csub2sub_out;
    try (complete (rw dom_csub_csub_filter; rw in_remove_nvars; simpl; sp;
                   apply newvars5_prop2 in Heqp; repnd;
                   repeat (apply not_over_or in X; repnd); sp)).
  simpl.

  duplicate Heqp as nv5.
  apply newvars5_prop2 in Heqp; repnd; allsimpl; allrw app_nil_r; allrw in_app_iff.
  apply not_over_or in Heqp0; repnd.
  apply not_over_or in Heqp1; repnd.
  apply not_over_or in Heqp2; repnd.
  apply not_over_or in Heqp3; repnd.
  apply not_over_or in Heqp4; repnd.

  allrw <- sub_filter_csub2sub.
  allrw lsubst_aux_sub_filter;
    try (complete (sp; allapply in_csub2sub; sp));
    try (complete (unfold disjoint; simpl; sp; subst; sp)).

  unfold mk_per_function_rel.
  remember (newvars5 [lsubst_aux A (csub2sub s), lsubst_aux B (csub2sub s)]); repnd.

  constructor; simpl; sp; unfold selectbt; destruct n; sp; simpl.
  generalize (fresh_vars 5 (all_vars A ++ all_vars B ++ [p, p0, p1, p2, p3] ++ [p4, p5, p6, p7, p8]));
    intro nvs; exrepnd.
  repeat (destruct lvn; allsimpl; sp; try (complete omega)).
  apply al_bterm with (lv := [n]);
    try (complete (simpl; sp));
    try (complete (apply no_rep_cons; sp)).
*)

Abort.
*)

Lemma cover_vars_mk_iper_function_rel {o} :
  forall A B s,
    cover_vars (@mk_iper_function_rel o A B) s
    <=> (cover_vars A s # cover_vars B s).
Proof.
  introv.
  rw @cover_vars_eq.
  rw @free_vars_iper_function_rel_eq.
  allrw subvars_app_l; split; sp.
Qed.

Lemma covered_iper_function_rel {o} :
  forall a b vs,
    covered (@mk_iper_function_rel o a b) vs
    <=> covered a vs
        # covered b vs.
Proof.
  introv.
  unfold covered.
  rw @free_vars_iper_function_rel_eq.
  allrw subvars_app_l; split; sp.
Qed.

Lemma cover_vars_iper_function {o} :
  forall A B s,
    cover_vars (@mk_iper_function o A B) s
    <=> (cover_vars A s # cover_vars B s).
Proof.
  introv.
  unfold mk_iper_function.
  rw @cover_vars_ipertype.
  rw @cover_vars_mk_iper_function_rel; sp.
Qed.

Lemma cover_vars_sper_function {o} :
  forall A B s,
    cover_vars (@mk_sper_function o A B) s
    <=> (cover_vars A s # cover_vars B s).
Proof.
  introv.
  unfold mk_sper_function.
  rw @cover_vars_spertype.
  rw @cover_vars_mk_iper_function_rel; sp.
Qed.

Lemma unfold_mk_iper_function_rel {o} :
  forall A B,
    {v1, v2, v3, v4, v5 : NVar
     $ mk_iper_function_rel A B
       = mk_lam
           v3
           (mk_lam
              v4
              (mk_isect
                 mk_base
                 v1
                 (mk_isect
                    mk_base
                    v2
                    (mk_isect
                       (mk_equality (mk_var v1) (mk_var v2) A)
                       v5
                       (mk_uand
                          (mk_equality
                             (mk_apply (mk_var v3) (mk_var v1))
                             (mk_apply (mk_var v4) (mk_var v2))
                             (mk_apply B (mk_var v1)))
                          (mk_tequality
                             (mk_apply B (mk_var v1))
                             (mk_apply B (@mk_var o v2))))))))
     # (v1, v2, v3, v4, v5) = newvars5 [A, B] }.
Proof.
  introv.
  remember (newvarlst [A,B]) as v1.
  exists v1.
  remember (newvarlst ([A,B] ++ [mk_var v1])) as v2.
  exists v2.
  remember (newvarlst ([A,B] ++ [mk_var v1, mk_var v2])) as v3.
  exists v3.
  remember (newvarlst ([A,B] ++ [mk_var v1, mk_var v2, mk_var v3])) as v4.
  exists v4.
  remember (newvarlst ([A,B] ++ [mk_var v1, mk_var v2, mk_var v3, mk_var v4])) as v5.
  exists v5.
  subst; sp.
Qed.

Lemma alpha_eq_lam2 {o} :
  forall v1 v2 b1 b2 v,
    isprogram (mk_lam v1 b1)
    -> isprogram (mk_lam v2 b2)
    -> alpha_eq (lsubst b1 (var_ren [v1] [v])) (lsubst b2 (@var_ren o [v2] [v]))
    -> alpha_eq (mk_lam v1 b1) (mk_lam v2 b2).
Proof.
  introv isp1 isp2 aeq.
  apply alpha_eq_trans with (nt2 := mk_lam v (lsubst b1 (var_ren [v1] [v]))).
  unfold mk_lam.
  prove_alpha_eq3.
  apply alpha_eq_bterm_single_change2.
  apply implies_isprogram_bt_lam; auto.
  apply alpha_eq_trans with (nt2 := mk_lam v (lsubst b2 (var_ren [v2] [v]))).
  unfold mk_lam.
  prove_alpha_eq3.
  apply alpha_eq_bterm_congr; auto.
  unfold mk_lam.
  prove_alpha_eq3.
  apply alpha_eq_bterm_sym.
  apply alpha_eq_bterm_single_change2.
  apply implies_isprogram_bt_lam; auto.
Qed.

Lemma cover_vars_implies_cover_vars_upto {o} :
  forall t sub vs,
    @cover_vars o t sub
    -> cover_vars_upto t sub vs.
Proof.
  introv cv.
  allrw @cover_vars_eq.
  unfold cover_vars_upto.
  provesv.
  rw in_app_iff; sp.
Qed.

Lemma subst_mk_lam2 {o} :
  forall v b x u,
    disjoint (bound_vars b) (@free_vars o u)
    -> !LIn v (free_vars u)
    -> v <> x
    -> subst (mk_lam v b) x u = mk_lam v (subst b x u).
Proof.
  introv disj ni neq.
  unfold subst.
  change_to_lsubst_aux4; allsimpl; allrw app_nil_r; allrw disjoint_cons_l; sp.
  boolvar; sp.
Qed.

Lemma cover_vars_if_disjoint {o} :
  forall t sub vs,
    disjoint vs (@free_vars o t)
    -> (cover_vars t sub <=> cover_vars t (csub_filter sub vs)).
Proof.
  introv disj; split; intro k;
  allrw @cover_vars_eq; provesv;
  allrw @dom_csub_csub_filter; allrw in_remove_nvars;
  dands; auto; repnd; auto.
  intro j; apply disj in j; sp.
Qed.

Lemma lsubstc_erase_rel {o} :
  forall R sub,
  forall w  : @wf_term o R,
  forall w' : wf_term (erase_rel R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (erase_rel R) sub,
    alphaeqc (lsubstc (erase_rel R) w' sub c')
             (erasec_rel (lsubstc R w sub c)).
Proof.
  introv.
  destruct_cterms.
  unfold erasec_rel, erase_rel, alphaeqc; simpl.
  repeat (rw @csubst_mk_lam).
  remember (newvarlst [R]) as v1.
  remember (newvarlst [R, mk_var v1]) as v2.
  remember (newvarlst [csubst R sub]) as v3.
  remember (newvarlst [csubst R sub, mk_var v3]) as v4.
  allunfold @newvarlst; allsimpl; allrw app_nil_r.

  generalize (fresh_var_not_in (free_vars R)); intro k1.
  rw <- Heqv1 in k1; clear Heqv1.
  generalize (fresh_var_not_in (free_vars R ++ [v1])); intro k2.
  rw <- Heqv2 in k2; clear Heqv2.
  generalize (fresh_var_not_in (free_vars (csubst R sub))); intro k3.
  rw <- Heqv3 in k3; clear Heqv3.
  generalize (fresh_var_not_in (free_vars (csubst R sub) ++ [v3])); intro k4.
  rw <- Heqv4 in k4; clear Heqv4.
  allrw in_app_iff; allrw not_over_or; repnd.

  generalize (ex_fresh_var (v2
                              :: v4
                              :: (bound_vars (csubst R (csub_filter sub [v1, v2])))
                              ++ (bound_vars (csubst R sub))));
    intro f; exrepnd.
  simpl in f0; repeat (rw in_app_iff in f0); repeat (rw not_over_or in f0); repnd.

  apply @alpha_eq_lam2 with (v := v).

  { apply isprogram_lam.
    apply isprog_vars_lam.
    rw <- @csub_filter_app_r; simpl.
    apply csubst.isprog_vars_csubst; sp.
    allrw @dom_csub_csub_filter; allrw in_app_iff; allsimpl.
    allrw in_remove_nvars; allsimpl.
    apply cover_vars_upto_csub_filter_disjoint.
    rw eqvars_prop; simpl; sp; split; sp.
    repeat (rw disjoint_cons_r); sp.
    allrw @cover_vars_erase_rel; sp. }

  { apply isprogram_lam.
    apply isprog_vars_lam.
    apply csubst.isprog_vars_csubst; sp.
    allrw @cover_vars_erase_rel; sp.
    apply cover_vars_implies_cover_vars_upto; sp. }

  unfold var_ren; simpl.
  allrw @fold_subst.

  rw @subst_mk_lam2; simpl; sp; allrw disjoint_singleton_r;
  allrw <- @csub_filter_app_r; allsimpl; sp.

  rw @subst_mk_lam2; simpl; sp; allrw disjoint_singleton_r;
  allrw <- @csub_filter_app_r; allsimpl; sp.

  unfold subst.
  rw @lsubst_trivial3;
    try (simpl; introv h; repdors; cpx; simpl; rw disjoint_singleton_l; sp;
         allrw @free_vars_csubst; allrw in_remove_nvars; sp).
  rw @lsubst_trivial3;
    try (simpl; introv h; repdors; cpx; simpl; rw disjoint_singleton_l; sp;
         allrw @free_vars_csubst; allrw in_remove_nvars; sp).

  generalize (ex_fresh_var ((bound_vars (csubst R (csub_filter sub [v1, v2])))
                              ++ (bound_vars (csubst R sub))));
    intro g; exrepnd.
  simpl in g0; repeat (rw in_app_iff in g0); repeat (rw not_over_or in g0); repnd.

  apply @alpha_eq_lam2 with (v := v0);
    try (apply @isprogram_lam;
         allrw @cover_vars_erase_rel; sp;
         apply @csubst.isprog_vars_csubst; sp;
         try (apply @cover_vars_implies_cover_vars_upto); sp).
  apply @cover_vars_if_disjoint; sp.
  allrw disjoint_cons_l; sp.

  rw @lsubst_trivial3;
    try (simpl; introv h; repdors; cpx; simpl; rw disjoint_singleton_l; sp;
         allrw @free_vars_csubst; allrw in_remove_nvars; sp).
  rw @lsubst_trivial3;
    try (simpl; introv h; repdors; cpx; simpl; rw disjoint_singleton_l; sp;
         allrw @free_vars_csubst; allrw in_remove_nvars; sp).

  rw @csubst_csub_filter; sp.
  allrw disjoint_cons_r; sp.
Qed.

Lemma lsubstc_erase_rel_ex {o} :
  forall R sub,
  forall w : wf_term (@erase_rel o R),
  forall c : cover_vars (erase_rel R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & alphaeqc (lsubstc (erase_rel R) w sub c)
                   (erasec_rel (lsubstc R w1 sub c1))}}.
Proof.
  sp.

  assert (wf_term R) as w1.
  { allrw <- @wf_erase_rel_iff; sp. }

  assert (cover_vars R sub) as c1.
  { allrw @cover_vars_eq; allrw subvars_prop; introv i.
    apply c.
    unfold erase_rel.
    remember (newvars2 [R]); repnd; allsimpl; allrw app_nil_r.
    apply newvars2_prop2 in Heqp.
    allsimpl; allrw app_nil_r; repnd.
    allrw in_remove_nvars; allrw in_single_iff; dands; auto; intro k; subst; sp. }

  exists w1 c1.
  apply lsubstc_erase_rel.
Qed.

(* !! MOVE to alphaeq.v *)
Lemma alphaeqc_mkc_pertype {o} :
  forall R1 R2,
    @alphaeqc o R1 R2
    -> alphaeqc (mkc_pertype R1) (mkc_pertype R2).
Proof.
  introv aeq.
  destruct_cterms.
  allunfold @alphaeqc; allsimpl.
  unfold mk_pertype.
  prove_alpha_eq3.
Qed.

(* !! MOVE to alphaeq.v *)
Lemma alphaeqc_mkc_ipertype {o} :
  forall R1 R2,
    @alphaeqc o R1 R2
    -> alphaeqc (mkc_ipertype R1) (mkc_ipertype R2).
Proof.
  introv aeq.
  destruct_cterms.
  allunfold @alphaeqc; allsimpl.
  unfold mk_ipertype.
  prove_alpha_eq3.
Qed.

(* !! MOVE to alphaeq.v *)
Lemma alphaeqc_mkc_spertype {o} :
  forall R1 R2,
    @alphaeqc o R1 R2
    -> alphaeqc (mkc_spertype R1) (mkc_spertype R2).
Proof.
  introv aeq.
  destruct_cterms.
  allunfold @alphaeqc; allsimpl.
  unfold mk_spertype.
  prove_alpha_eq3.
Qed.

Lemma lsubstc_erase {o} :
  forall R sub,
  forall w  : @wf_term o R,
  forall w' : wf_term (erase R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (erase R) sub,
    alphaeqc (lsubstc (erase R) w' sub c')
             (erasec (lsubstc R w sub c)).
Proof.
  introv.
  rw @erasec_eq.
  unfold erase.
  generalize (lsubstc_mk_pertype_ex (erase_rel R) sub w' c'); intro k; exrepnd.
  rw k1.
  apply alphaeqc_mkc_pertype.
  apply lsubstc_erase_rel.
Qed.

Lemma lsubstc_erase_ex {o} :
  forall R sub,
  forall w : wf_term (@erase o R),
  forall c : cover_vars (erase R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & alphaeqc (lsubstc (erase R) w sub c)
                   (erasec (lsubstc R w1 sub c1))}}.
Proof.
  sp.

  assert (wf_term R) as w1.
  { allrw <- @wf_erase_iff; sp. }

  assert (cover_vars R sub) as c1.
  { rw @cover_vars_erase in c; sp. }

  exists w1 c1.
  apply lsubstc_erase.
Qed.

Lemma isprogram_isaxiom {o} :
  forall a b c,
    isprogram a
    -> isprogram b
    -> @isprogram o c
    -> isprogram (mk_isaxiom a b c).
Proof.
  repeat constructor.
  unfold closed; simpl.
  allrw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @isprogram; allunfold @closed.
  repeat (rewrite remove_nvars_nil_l); sp.
  simpl; sp; allunfold @isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_isaxiom_iff {p} :
  forall a b c, (isprogram a # isprogram b # @isprogram p c) <=> isprogram (mk_isaxiom a b c).
Proof.
  intros; split; intro i.
  apply isprogram_isaxiom; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| | o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Lemma isprog_isaxiom {p} :
  forall a b c,
    isprog a
    -> isprog b
    -> @isprog p c
    -> isprog (mk_isaxiom a b c).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_isaxiom; auto.
Qed.

Definition mkc_isaxiom {p} (t1 t2 t3 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
    exist isprog (mk_isaxiom a b c) (isprog_isaxiom a b c x y z).

Lemma mkc_isaxiom_eq {p} :
  forall a b c d e f,
    mkc_isaxiom a b c = @mkc_isaxiom p d e f
    -> a = d # b = e # c = f.
Proof.
  introv eq.
  destruct_cterms.
  allunfold @mkc_isaxiom.
  inversion eq; subst; dands; tcsp; eauto with pi.
Qed.

Lemma fold_isaxiom {p} :
  forall a b c,
    oterm (NCan (NCanTest CanIsaxiom)) [ nobnd a, nobnd b, @nobnd p c ]
    = mk_isaxiom a b c.
Proof.
  sp.
Qed.

Lemma lsubstc_mk_isaxiom {p} :
  forall t1 t2 t3 sub,
  forall w1 : wf_term t1,
  forall w2 : wf_term t2,
  forall w3 : @wf_term p t3,
  forall w  : wf_term (mk_isaxiom t1 t2 t3),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c3 : cover_vars t3 sub,
  forall c  : cover_vars (mk_isaxiom t1 t2 t3) sub,
    lsubstc (mk_isaxiom t1 t2 t3) w sub c
    = mkc_isaxiom (lsubstc t1 w1 sub c1)
                  (lsubstc t2 w2 sub c2)
                  (lsubstc t3 w3 sub c3).
Proof.
  introv; apply cterm_eq; simpl.
  unfold csubst; simpl;
  change_to_lsubst_aux4; simpl;
  rw @sub_filter_nil_r;
  allrw @fold_nobnd;
  rw @fold_isaxiom; sp.
Qed.

Lemma lsubstc_mk_isaxiom_ex {p} :
  forall t1 t2 t3 sub,
  forall w  : wf_term (@mk_isaxiom p t1 t2 t3),
  forall c  : cover_vars (mk_isaxiom t1 t2 t3) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {w3 : wf_term t3
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {c3 : cover_vars t3 sub
      & lsubstc (mk_isaxiom t1 t2 t3) w sub c
           = mkc_isaxiom (lsubstc t1 w1 sub c1)
                         (lsubstc t2 w2 sub c2)
                         (lsubstc t3 w3 sub c3)}}}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw @wf_isaxiom; sp. }

  assert (wf_term t2) as w2.
  { allrw @wf_isaxiom; sp. }

  assert (wf_term t3) as w3.
  { allrw @wf_isaxiom; sp. }

  assert (cover_vars t1 sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  assert (cover_vars t2 sub) as c2.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  assert (cover_vars t3 sub) as c3.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 w2 w3 c1 c2 c3.
  apply lsubstc_mk_isaxiom.
Qed.
