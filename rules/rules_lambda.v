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


Require Export rules_apply.
Require Export rules_function_elim.


(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)


Hint Rewrite @nh_vars_hyps_app : slow.
Hint Rewrite @nh_vars_hyps_snoc : slow.


(* end hide *)


(* [23] ============ LAMBDA FORMATION ============ *)

(**

 The following rule is called the lambda formation rules.  It says
 that to prove that a function type is true, it is enough to prove
 that given a element [z] in its domain [A], we can prove that its
 codomain [B[x\z]] is true.  We also have to prove that its domain [A}
 is a well-formed type.x
<<
   H |- x:A -> B ext \z.b

     By lambdaFormation lvl(i) z ()

     H z : A |- B[x\z] ext b
     H |- A = A in Type(i)
>>

 *)

Definition rule_lambda_formation {p}
           (A B b : NTerm)
           (x z  : NVar)
           (i    : nat)
           (H    : @barehypotheses p) :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_function A x B) (mk_lam z b)))
    [ mk_baresequent (snoc H (mk_hyp z A))
                    (mk_concl (subst B x (mk_var z)) b),
      mk_baresequent H (mk_conclax (mk_equality A A (mk_uni i))) ]
    [sarg_var z].

Lemma rule_lambda_formation_true {p} :
  forall lib (A B b : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses p)
         (bc1 : !LIn z (bound_vars B)),
    rule_true lib (rule_lambda_formation A B b x z i H).
Proof.
  intros.
  unfold rule_lambda_formation, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent (snoc H (mk_hyp z A))
                                  (mk_concl (subst B x (mk_var z)) b))
                   (inl eq_refl))
             (hyps (mk_baresequent H (mk_conclax (mk_equality A A (mk_uni i))))
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
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2); clear hyp2; intro hyp2.
  autodimp hyp2 h.
  autodimp hyp2 h; exrepd.
  lsubst_tac.
  rw @tequality_mkc_equality in t; repnd; GC.
  allrewrite @member_eq.
  rw <- @member_equality_iff in e.
  dimp t2. 
  apply @equality_in_uni in hyp. auto.
  
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
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s4); clear hyp2; intro hyp2.
  autodimp hyp2 hyp.
  autodimp hyp2 hyp; exrepd.
  lsubst_tac.
  rw @tequality_mkc_equality in t; repnd; GC.
  allrewrite @member_eq.
  allrw <- @member_equality_iff.
  dimp t3.
  apply @equality_in_uni in hyp.
  auto.
  
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

Lemma rule_lambda_formation_true_ex {p} :
  forall lib i z A B b x H (bc1 : !LIn z (bound_vars B)),
    @rule_true_if p lib (rule_lambda_formation A B b x z i H).
Proof.
  intros.
  generalize (rule_lambda_formation_true lib A B b x z i H bc1); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.



(* end hide *)


(* [24] ============ FUNCTION EQUALITY ============ *)

(**

  The following rule is called the function equality rule.  It says
  that to prove that a function type is well-formed, we have to prove
  that its domain is well-formed and that its co-domain is functional
  over its domain.
<<
   H |- x1:a1 -> b1 = x2:a2 -> b2 in Type(i)

     By functionEquality y ()

     H |- a1 = a2 in Type(i)
     H y : a1 |- subst b1 x1 y = subst b2 x2 y in Type(i)
>>
 *)

Definition rule_function_equality_concl {o} (H : @bhyps o) a1 x1 b1 a2 x2 b2 i :=
  mk_baresequent
    H
    (mk_conclax (mk_equality
                   (mk_function a1 x1 b1)
                   (mk_function a2 x2 b2)
                   (mk_uni i))).

Definition rule_function_equality_hyp1 {o} (H : @bhyps o) a1 a2 i e1 :=
  mk_baresequent
    H
    (mk_concl (mk_equality a1 a2 (mk_uni i)) e1).

Definition rule_function_equality_hyp2 {o} (H : @bhyps o) y a1 b1 x1 b2 x2 i e2 :=
  mk_baresequent
    (snoc H (mk_hyp y a1))
    (mk_concl (mk_equality
                 (subst b1 x1 (mk_var y))
                 (subst b2 x2 (mk_var y))
                 (mk_uni i)) e2).

Definition rule_function_equality {p}
           (a1 a2 b1 b2 e1 e2 : NTerm)
           (x1 x2 y : NVar)
           (i   : nat)
           (H   : @barehypotheses p) :=
  mk_rule
    (rule_function_equality_concl H a1 x1 b1 a2 x2 b2 i)
    [
      rule_function_equality_hyp1 H a1 a2 i e1,
      rule_function_equality_hyp2 H y a1 b1 x1 b2 x2 i e2
    ]
    [ sarg_var y ].

Lemma rule_function_equality_true {o} :
  forall lib (a1 a2 b1 b2 e1 e2 : NTerm) (x1 x2 y : NVar) (i : nat) (H : @barehypotheses o),
    rule_true lib (rule_function_equality
                     a1 a2 b1 b2 e1 e2
                     x1 x2 y
                     i
                     H).
Proof.
  intros.
  apply (rule_tyfam_equality_true _ _ mkc_function); auto.
  - introv; simpl; allrw remove_nvars_nil_l; allrw app_nil_r; auto.
  - introv; apply lsubstc_mk_function_ex.
  - introv; apply equality_function.
Qed.

Lemma rule_function_equality_true3 {o} :
  forall lib (a1 a2 b1 b2 e1 e2 : NTerm) (x1 x2 y : NVar) (i : nat) (H : @barehypotheses o),
    rule_true3 lib (rule_function_equality
                     a1 a2 b1 b2 e1 e2
                     x1 x2 y
                     i
                     H).
Proof.
  intros.
  apply (rule_tyfam_equality_true3 _ _ mkc_function); auto.
  - introv; simpl; allrw remove_nvars_nil_l; allrw app_nil_r; auto.
  - introv; apply lsubstc_mk_function_ex.
  - introv; apply equality_function.
Qed.

Lemma rule_function_equality_true_ext_lib {o} :
  forall lib (a1 a2 b1 b2 e1 e2 : NTerm) (x1 x2 y : NVar) (i : nat) (H : @barehypotheses o),
    rule_true_ext_lib lib (rule_function_equality
                             a1 a2 b1 b2 e1 e2
                             x1 x2 y
                             i
                             H).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_function_equality_true3.
Qed.

Lemma rule_function_equality_wf2 {o} :
  forall (a1 a2 b1 b2 e1 e2 : NTerm) (x1 x2 y : NVar) (i : nat) (H : @barehypotheses o),
    !LIn y (vars_hyps H)
    -> wf_rule2 (rule_function_equality
                   a1 a2 b1 b2 e1 e2
                   x1 x2 y
                   i
                   H).
Proof.
  introv niyH wf j.

  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq;
    allrw <- @wf_function_iff; repnd; auto;
      allrw @covered_function; repnd; auto; eauto 4 with slow.

  - apply vswf_hypotheses_snoc; dands; simpl; auto.
    apply isprog_vars_iff_covered; dands; auto.

  - apply covered_subst; eauto 2 with slow.
    eapply covered_subvars;[|eauto].
    rw subvars_eq; introv j; simpl in *; allrw in_snoc; tcsp.

  - apply covered_subst; eauto 2 with slow.
    eapply covered_subvars;[|eauto].
    rw subvars_eq; introv j; simpl in *; allrw in_snoc; tcsp.
Qed.


(* begin hide *)


Lemma rule_function_equality_true_ex {o} :
  forall lib y i a1 a2 b1 b2 e1 e2 x1 x2 H,
    @rule_true_if o lib (rule_function_equality a1 a2 b1 b2 e1 e2 x1 x2 y i H).
Proof.
  intros.
  generalize (rule_function_equality_true lib a1 a2 b1 b2 e1 e2 x1 x2 y i H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.



(* end hide *)


(* [25] ============ LAMBDA EQUALITY ============ *)

(**

  The following rule is called the lambda equality rule.  It allows
  one to prove that lambda-abstractions are well-typed.
<<

   H |- \x1.t1 = \x2.t2 in x:A->B

     By lambdaEquality lvl(i) z ()

     H z : A |- t1[x1\z] = t2[x2\z] in B[x\z]
     H |- A = A in Type(i)
>>
 *)

Definition rule_lambda_equality {o}
           (A B t1 t2 : NTerm)
           (x1 x2 x z : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_lam x1 t1)
                      (mk_lam x2 t2)
                      (mk_function A x B))))
    [ mk_baresequent
        (snoc H (mk_hyp z A))
        (mk_conclax (mk_equality
                       (subst t1 x1 (mk_var z))
                       (subst t2 x2 (mk_var z))
                       (subst B x (mk_var z)))),
      mk_baresequent
        H
        (mk_conclax (mk_equality A A (mk_uni i))) ]
    [sarg_var z].

Lemma rule_lambda_equality_true {o} :
  forall lib (A B t1 t2 : NTerm)
         (x1 x2 x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o)
         (bc1 : !LIn z (bound_vars B))
         (bc2 : !LIn z (bound_vars t1))
         (bc3 : !LIn z (bound_vars t2)),
    rule_true lib (rule_lambda_equality A B t1 t2 x1 x2 x z i H).
Proof.
  intros.
  unfold rule_lambda_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1; rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.
  duplicate wfct as wfi.
  rw <- @wf_equality_iff in wfct.
  destruct wfct as [ wl1 wfct ].
  destruct wfct as [ wl2 wfct ].
  rw <- @wf_function_iff in wfct.
  destruct wfct as [ wA wB ].
  duplicate ce0 as ce.
  allrw @nh_vars_hyps_snoc; allsimpl.

  exists (@covered_axiom o (nh_vars_hyps H)); GC.

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # (z <> x1 -> !LIn z (free_vars t1))
          # (z <> x2 -> !LIn z (free_vars t2))
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp;
  try (complete (generalize (cg z); sp;
                 allrw in_remove_nvars; allsimpl;
                 autodimp X0 h; sp));
  try (complete (generalize (cg0 z); sp;
                 allrw in_remove_nvars; allsimpl;
                 autodimp X0 h; sp));
  try (complete (generalize (cg1 z); sp;
                 allrw in_remove_nvars; allsimpl;
                 autodimp X0 h; sp));
  try (complete (apply_in_hyp p;
                 generalize (subvars_hs_vars_hyps H); intro sv;
                 rw subvars_prop in sv;
                 apply sv in p; sp)).

  destruct vhyps as [ nzB vhyps ].
  destruct vhyps as [ nzt1 vhyps ].
  destruct vhyps as [ nzt2 vhyps ].
  destruct vhyps as [ nzA nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.
  rw @member_eq.
  rw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality lib
                (mk_function A x B) (mk_lam x1 t1) (mk_lam x2 t2) s1 s2 H
                wT wl1 wl2 c1 c0 c2 c3 cT cT0 eqh sim);
    intro k.
  lsubst_tac.
  apply k; clear k.

  rw @tequality_function.

  split.

  (* First, we prove that the a's are types *)
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp2.
  rw <- @member_equality_iff in hyp2.
  apply @equality_commutes2 in hyp0; try (complete auto).
  apply @equality_in_uni in hyp0; auto.

  (* Then we prove that the b's are type families *)
  intros a a' ea.
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z, a)) (snoc s2 (z, a'))); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  (* we have to prove the functionality of our hypotheses *)
  apply hyps_functionality_snoc2; simpl; try (complete sp).
  introv eq s.
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s' eqh s); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1.
  apply @equality_commutes2 in hyp0; try (complete auto).
  apply @equality_in_uni in hyp0; auto.

  (* we have to prove the similarity of our hypotheses *)
  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s2 a a' wA c4; sp.

  (* we can now use hyp1 *)
  exrepnd; lsubst_tac.

  (* we use hyp0 *)
  rw @tequality_mkc_equality in hyp0; repnd.

  (* we use hyp3 *)
  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s1 (z, a)) cT1
          = substc a x (lsubstc_vars B wB (csub_filter s1 [x]) [x] c5)) as eq1
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq1 in hyp3.

  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s2 (z, a')) cT2
          = substc a' x (lsubstc_vars B wB (csub_filter s2 [x]) [x] c7)) as eq2
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq2 in hyp3.

  sp.


  (* we prove the membership *)
  clear dependent s1; clear dependent s2.
  introv hf sim.
  lsubst_tac.
  rw @equality_in_function3.

  dands.

  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp2.
  rw <- @member_equality_iff in hyp2.
  apply @equality_in_uni in hyp2; auto.

  introv ea.

  assert (cover_vars (mk_var z) (snoc s1 (z, a)))
    as cv1 by (apply @cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; sp).

  assert (cover_vars (mk_var z) (snoc s2 (z, a')))
    as cv2 by (apply @cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; sp).

  assert (disjoint (free_vars (@mk_var o z)) (bound_vars t1))
    as disj1 by (simpl; rw disjoint_singleton_l; sp).

  assert (disjoint (free_vars (@mk_var o z)) (bound_vars t2))
    as disj2 by (simpl; rw disjoint_singleton_l; sp).

  assert (disjoint (free_vars (@mk_var o z)) (bound_vars B))
    as disjB by (simpl; rw disjoint_singleton_l; sp).

  dands.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z, a)) (snoc s1 (z, a'))); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  (* we have to prove the functionality of our hypotheses *)
  apply hyps_functionality_snoc2; simpl; try (complete sp).
  introv eq sim'.
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s' hf sim'); clear hyp2; intro hyp2; exrepd.
  lsubst_tac.
  rw @member_eq in e.
  rw <- @member_equality_iff in e.
  apply @equality_commutes2 in t; try (complete auto).
  apply @equality_in_uni in t; auto.

  (* we have to prove the similarity of our hypotheses *)
  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s1 a a' wA c1; sp.
  apply @similarity_refl in sim; auto.

  exrepnd.
  lsubst_tac.
  rw @tequality_mkc_equality in hyp0; repnd.
  clear hyp1 hyp0.

  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s1 (z, a)) cT
          = substc a x (lsubstc_vars B wB (csub_filter s1 [x]) [x] c2)) as eq1
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq1 in hyp3; clear eq1.

  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s1 (z, a')) cT0
          = substc a' x (lsubstc_vars B wB (csub_filter s1 [x]) [x] c2)) as eq2
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq2 in hyp3; clear eq2.
  auto.

  repeat betared.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z, a)) (snoc s2 (z, a'))); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  (* we have to prove the functionality of our hypotheses *)
  apply hyps_functionality_snoc2; simpl; try (complete sp).
  introv eq sim'.
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s' hf sim'); clear hyp2; intro hyp2; exrepd.
  lsubst_tac.
  rw @member_eq in e.
  rw <- @member_equality_iff in e.
  apply @equality_commutes2 in t; try (complete auto).
  apply @equality_in_uni in t; auto.

  (* we have to prove the similarity of our hypotheses *)
  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s2 a a' wA c1; sp.

  exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1.

  apply @equality_commutes4 in hyp0; auto; clear hyp1.

  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s1 (z, a)) cT
          = substc a x (lsubstc_vars B wB (csub_filter s1 [x]) [x] c2)) as eq
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq in hyp0; clear eq.

  assert (lsubstc (subst t1 x1 (mk_var z)) w2 (snoc s1 (z, a)) c4
          = substc a x1 (lsubstc_vars t1 w1 (csub_filter s1 [x1]) [x1] c0)) as eq
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq in hyp0; clear eq.

  assert (lsubstc (subst t2 x2 (mk_var z)) w3 (snoc s2 (z, a')) c7
          = substc a' x2 (lsubstc_vars t2 w0 (csub_filter s2 [x2]) [x2] c3)) as eq
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq in hyp0; clear eq.
  auto.
Qed.

(* begin hide *)



(* end hide *)

