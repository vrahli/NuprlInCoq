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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export per_props_subtype_rel.
Require Export sterm.
Require Export sequents_tacs.
Require Export per_props_tequality.
Require Export subst_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export sequents2.
Require Export rules_useful.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export variables.
Require Export rules_typehood.



(* [23] ============ LAMBDA FORMATION ============ *)

(**

 The following rule is the alternate lambda formation rule.  It says
 that to prove that a function type is true, it is enough to prove
 that given a element [z] in its domain [A], we can prove that its
 codomain [B[x\z]] is true.  We also have to prove that its domain [A]
 is a well-formed type. In this rule we use the istype(A) form of that
 assertion. It does not require any universe level.
<<
   H |- x:A -> B ext \z.b

     By lambdaFormationAlt lvl(i) z ()

     H z : A |- B[x\z] ext b
     H |- istype(A)
>>

 *)

Definition rule_lambda_formation_alt {p}
           (A B b : NTerm)
           (x z  : NVar)
           (H    : @barehypotheses p) :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_function A x B) (mk_lam z b)))
    [ mk_baresequent (snoc H (mk_hyp z A))
                    (mk_concl (subst B x (mk_var z)) b),
      mk_baresequent H (mk_conclax (mk_istype A)) ]
    [sarg_var z].

Lemma rule_lambda_formation_alt_true {p} :
  forall lib (A B b : NTerm)
         (x z : NVar)
         (H   : @barehypotheses p)
         (bc1 : !LIn z (bound_vars B)),
    rule_true lib (rule_lambda_formation_alt A B b x z H).
Proof.
  intros.
  unfold rule_lambda_formation_alt, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent (snoc H (mk_hyp z A))
                                  (mk_concl (subst B x (mk_var z)) b))
                   (inl eq_refl))
             (hyps (mk_baresequent H (mk_conclax (mk_istype A)))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.
  duplicate wfct as wfi.
  rw <- @wf_function_iff in wfct.
  destruct wfct as [ wa wb ].
  duplicate ce0 as ce.
  allrw @nh_vars_hyps_snoc; allsimpl.

  assert (covered (mk_lam z b) (nh_vars_hyps H)) as cv.
  clear hyp1 hyp2.
  allunfold @covered; allsimpl; allrw app_nil_r.
  allrw subvars_remove_nvars.
  allrw <- snoc_as_append; sp.

  exists cv; GC.

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp;
  try (complete (generalize (cg z); sp;
                 allrw in_remove_nvars; allsimpl;
                 autodimp X0 h; sp));
  try (complete (apply_in_hyp p;
                 generalize (subvars_hs_vars_hyps H); intro sv;
                 rw subvars_prop in sv;
                 apply sv in p; sp)).

  destruct vhyps as [ nzB vhyps ].
  destruct vhyps as [ nzA nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  (* We prove our first subgoal *)
  assert (forall s2 pC2,
            similarity lib s1 s2 H
            -> tequality lib (lsubstc (mk_function A x B) wfi s1 pC1)
                         (lsubstc (mk_function A x B) wfi s2 pC2)) as tfb.
  clear s2 pC2 pt2 sim.
  intros s2 pC2 sim.
  lift_lsubst.
  rw @tequality_function.

  (* we have to prove that A is a type and B is a type family *)
  split.

  (* we use our 2nd hypothesis to prove that A is a type *)
  pose proof (@mk_istype_true2_implies p lib H A) as xx.
  autodimp xx G. unfold sequent_true2. exists (wfh, (wfct0, wfce0), (ct, ce)). auto.
  specialize (xx s1 s2 wa c1 c0 eqh sim) as xx.
  destruct xx. auto.
  
  (* we use our 1st hypothesis to prove that B is a type family *)
  intros.
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z, a)) (snoc s2 (z, a'))); clear hyp1; intro hyp1.
  autodimp hyp1 h.

  (* To use our 1st hyp, we first have to prove that the hypotheses are functional *)
  intros s3 sim3.
  inversion sim3; cpx; allsimpl; cpx; clear_irr.
  assert (cover_vars A s4) as c4
    by (apply similarity_cover_vars with (t := A) in sim0; auto).
  (* we use our hyp (coming from proving that our sequent is true) that says that H is functional *)
  rw @eq_hyps_snoc; simpl.

  exists s1 s4 a t2 wa c1 c4; sp.
  (* now to prove that functionality statement on A, we use our 2nd hyp *)
  pose proof (@mk_istype_true2_implies p lib H A) as xx.
  autodimp xx G. unfold sequent_true2. exists (wfh, (wfct0, wfce0), (ct, ce)). auto.
  specialize (xx s1 s4 wa c1 c4 eqh sim0) as xx.
  destruct xx. auto.
  (* and we're done proving that the hypotheses are functional *)

  (* now we can keep using our 1st hypothesis *)
  autodimp hyp1 hyp.

  (* For that we have to prove that the two terms we picked to be equal in A are actually equal in A *)
  rw @similarity_snoc; simpl.
  exists s1 s2 a a' wa c1; sp.
  (* easy enough *)

  (* and again, we keep on using our 1st hypothesis *)
  exrepd. (* we prove that from t *)

  assert (lsubstc (subst B x (mk_var z)) wfct1 (snoc s1 (z, a)) pC0
          = substc a x (lsubstc_vars B wb (csub_filter s1 [x]) [x] c2)) as eq1
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq1 in t.

  assert (lsubstc (subst B x (mk_var z)) wfct1 (snoc s2 (z, a')) pC3
          = substc a' x (lsubstc_vars B wb (csub_filter s2 [x]) [x] c3)) as eq2
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq2 in t.
  auto.
  (* and we're done proving our 1st subgoal (the tequality) *)


  (* We now prove our second subgoal *)
  sp; lift_lsubst.
  applydup @similarity_refl in sim.
  rw @equality_in_function.

  sp.
  (* We have to prove 3 goals *)

  (* 1) we have to prove that A is a type *)
  generalize (tfb s1 pC1 sim0); sp.
  lsubst_tac.
  allrw @tequality_function; sp.

  (* 2) we have to prove that B is a type family *)
  generalize (tfb s1 pC1 sim0); sp.
  lsubst_tac.
  allrw @tequality_function; sp.

  (* 3) we have to prove that b is a member B *)
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z, a)) (snoc s2 (z, a'))); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  (* first we have to prove that the hypotheses are functional *)
  intros s3 sim3.
  inversion sim3; cpx; allsimpl; cpx; clear_irr.
  assert (cover_vars A s4) as c4
    by (apply similarity_cover_vars with (t := A) in sim1; auto).
  (* we use our hyp (coming from proving that our sequent is true) that says that H is functional *)
  allapplydup eqh.
  rw @eq_hyps_snoc; simpl.
  exists s1 s4 a t2 wa c1 c4; sp.
  (* now to prove that functionality statement on A, we use our 2nd hyp (from tfb) *)
  assert (cover_vars (mk_isect A x B) s4) as c5
    by (apply cover_vars_isect; sp;
        allapplydup @similarity_dom; sp;
        apply @cover_vars_upto_eq_dom_csub with (s2 := s4) in c2; sp;
        allrw; sp).
  generalize (tfb s4 c5 sim1); sp.
  lsubst_tac.
  allrw @tequality_function; sp.
  (* and we're done proving that the hypotheses are functional *)

  (* now we can keep using our 1st hypothesis *)
  autodimp hyp1 hyp.

  (* For that we have to prove that the two terms we picked to be equal in A are actually equal in A *)
  rw @similarity_snoc; simpl.
  exists s1 s2 a a' wa c1; sp.
  (* easy enough *)

  (* and again, we keep on using our 1st hypothesis *)
  exrepd. (* we prove that from e *)
  clear t; clear_irr.

  assert (lsubstc (subst B x (mk_var z)) wfct1 (snoc s1 (z, a)) pC0
          = substc a x (lsubstc_vars B wb (csub_filter s1 [x]) [x] c2)) as eq1.
  rewrite substc_eq_lsubstc; simpl.
  apply lsubstc_eq_if_csubst.
  rewrite csubst_app.
  unfold subst, csubst.
  try (rw lsubstn_lsubst; try (complete (simpl; rw disjoint_singleton_r; sp))).
  rewrite simple_lsubst_lsubst;
    try (complete (sp; allapply @in_csub2sub; sp));
    try (complete (simpl; sp; cpx; simpl; apply disjoint_singleton_l; auto)).
  rewrite lsubst_sub_singleton.
  rewrite fold_csubst.
  rewrite csubst_snoc_var;
    try (complete (allapply @similarity_dom; exrepd; allrw; sp)).
  rewrite <- csub2sub_app; simpl.
  rewrite <- snoc_as_append.
  rewrite <- lsubst_swap;
    try (complete (sp; allapply @in_csub2sub; sp));
    try (complete (rewrite @dom_csub_eq; rewrite @dom_csub_csub_filter; rw in_remove_nvars; simpl; sp)).
  repeat (rewrite <- @csub2sub_cons).
  repeat (rewrite @fold_csubst).
  destruct (eq_var_dec z x); subst.
  (* if they're equal it's easy *)
  rewrite csubst_cons_trim.
  rewrite csub_filter_snoc1; sp.
  (* if they're not: *)
  rewrite <- csubst_csub_filter with (l := [z]);
    try (rw disjoint_singleton_r; sp).
  assert (x <> z) as d by auto; simpl.
  apply memvar_singleton_diff_r in d; rewrite d.
  rewrite csub_filter_snoc1; sp.
  rewrite csubst_cons_trim.
  rewrite <- csub_filter_app_r; simpl.
  symmetry.
  rewrite <- csubst_csub_filter with (l := [z]); simpl;
    try (rw disjoint_singleton_r; sp).
  rewrite d.
  rewrite csub_filter_swap.
  rewrite <- csub_filter_app_r; sp.

  rewrite eq1 in e; clear eq1.

  lsubst_tac; sp.

  assert (cequivc lib
            (lsubstc b wfce1 (snoc s1 (z, a)) pt0)
            (mkc_apply
               (mkc_lam z (lsubstc_vars b wfce1 (csub_filter s1 [z]) [z] c0))
               a)) as ceq1.
  apply cequivc_sym.
  revert c0; rw @csub_filter_trivial; introv;
  try (complete (simpl; sp; subst; allapply @similarity_dom; repnd; allrw sim1; sp)).
  destruct_cterms; unfold cequivc; simpl; unfold csubst; simpl.
  allrw @csub2sub_snoc; simpl.
  generalize (cequiv_beta lib z (lsubst b (csub2sub s1)) x1); introv ceq1.
  autodimp ceq1 hyp.
  apply csubst.isprog_vars_lsubst.
  introv k; allrw @in_range_iff; exrepnd; allapply @in_csub2sub; sp.
  simpl.
  rw @isprog_vars_eq; sp.
  allunfold @covered.
  rw @dom_csub_eq.
  allapply @similarity_dom; repnd; allrw.
  apply subvars_trans with (vs2 := snoc (nh_vars_hyps H) z); sp.
  rw subvars_prop; introv j; allsimpl; allrw in_snoc; sp.
  generalize (subset_hs_vars_hyps H); intro k.
  right; apply k; sp.
  rw @nt_wf_eq; sp.
  autodimp ceq1 hyp.
  allrw @isprogram_eq; sp.
  rw @simple_lsubst_snoc in ceq1; sp.
  rw @isprogram_eq; sp.
  allapply @in_csub2sub; sp.

  assert (cequivc lib
            (lsubstc b wfce1 (snoc s2 (z, a')) pt3)
            (mkc_apply
               (mkc_lam z (lsubstc_vars b wfce1 (csub_filter s2 [z]) [z] c3))
               a'))
         as ceq2.
  apply cequivc_sym.
  revert c3; rw @csub_filter_trivial; introv;
  try (complete (simpl; sp; subst; allapply @similarity_dom; repnd; allrw sim; sp)).
  destruct_cterms; unfold cequivc; simpl; unfold csubst; simpl.
  allrw @csub2sub_snoc; simpl.
  generalize (cequiv_beta lib z (lsubst b (csub2sub s2)) x0); introv ceq2.
  autodimp ceq2 hyp.
  apply csubst.isprog_vars_lsubst.
  introv k; allrw @in_range_iff; exrepnd; allapply @in_csub2sub; sp.
  simpl.
  rw @isprog_vars_eq; sp.
  allunfold @covered.
  rw @dom_csub_eq.
  allapply @similarity_dom; repnd; allrw.
  apply subvars_trans with (vs2 := snoc (nh_vars_hyps H) z); sp.
  rw subvars_prop; introv j; allsimpl; allrw in_snoc; sp.
  generalize (subset_hs_vars_hyps H); intro k.
  right; apply k; sp.
  rw @nt_wf_eq; sp.
  autodimp ceq2 hyp.
  allrw @isprogram_eq; sp.
  rw @simple_lsubst_snoc in ceq2; sp.
  rw @isprogram_eq; sp.
  allapply @in_csub2sub; sp.

  apply @equality_respects_cequivc_left with (t1 := lsubstc b wfce1 (snoc s1 (z, a)) pt0); sp.
  apply @equality_respects_cequivc_right with (t2 := lsubstc b wfce1 (snoc s2 (z, a')) pt3); sp.
Qed.

(* begin hide *)

Lemma rule_lambda_formation_alt_true_ex {p} :
  forall lib z A B b x H (bc1 : !LIn z (bound_vars B)),
    @rule_true_if p lib (rule_lambda_formation_alt A B b x z H).
Proof.
  intros.
  generalize (rule_lambda_formation_alt_true lib A B b x z H bc1); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.
