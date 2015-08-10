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


Require Export rules_useful.
Require Export subst_tacs.
Require Export cequiv_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export rules_tyfam.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)


(* end hide *)

(**

  The Nuprl manual%~\cite{Kreitz:02}% presents various useful rules to
  reason about function types.  This section prove the truth of
  several of these rules.

*)

(* [17] ============ FUNCTION ELIMINATION ============ *)

(**

 The following rule is called the function elimination rules.  It says
 that if we can prove that [a] is in the domain [A] then we can assume
 that [f a] is in [B[x\a]].  As for the other rules, first we show an
 informal statement of this rule, then we show its formal statement (a
 [Definition]), and finally we show the statement that the rule is
 true (a [Lemma]).  In such informal statements, we write ``C ext e''
 to indicate that e is the extract of the sequent, i.e., the evidence
 that C is true.  We omit the ``ext e'' part when e is [mk_axiom].

<<
   H, f : x:A->B[x], J |- C ext e[z\axiom]

     By perFunctionElimination s z

     H, f : x:A->B[x], J |- a in A
     H, f : x:A->B[x], J, z : (f a) in B[a] |- C ext e
>>

 *)

Definition rule_function_elimination {p}
           (A B C a e : NTerm)
           (f x z : NVar)
           (H J : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp f (mk_function A x B)) ++ J)
       (mk_concl C (subst e z mk_axiom)))
    [ mk_baresequent
        (snoc H (mk_hyp f (mk_function A x B)) ++ J)
        (mk_conclax (mk_member a A)),
      mk_baresequent
        (snoc (snoc H (mk_hyp f (mk_function A x B)) ++ J)
              (mk_hyp z (mk_member (mk_apply (mk_var f) a)
                                   (subst B x a))))
        (mk_concl C e)
    ]
    [sarg_term a, sarg_var z].

Lemma rule_function_elimination_true {p} :
  forall lib (A B C a e : NTerm),
  forall f x z : NVar,
  forall H J : @barehypotheses p,
  forall bc1 : x <> f,
  forall bc2 : disjoint (vars_hyps H) (bound_vars B),
  forall bc3 : disjoint (vars_hyps J) (bound_vars B),
  forall bc4 : !LIn f (bound_vars B),
    rule_true lib (rule_function_elimination
                 A B C a e
                 f x z
                 H J).
Proof.
  unfold rule_function_elimination, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent
                      (snoc H (mk_hyp f (mk_function A x B)) ++ J)
                      (mk_conclax (mk_member a A)))
                   (inl eq_refl))
             (hyps (mk_baresequent
                      (snoc (snoc H (mk_hyp f (mk_function A x B)) ++ J)
                            (mk_hyp z (mk_member (mk_apply (mk_var f) a) (subst B x a))))
                      (mk_concl C e))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2; clear hyps.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (covered
            (subst e z mk_axiom)
            (vars_hyps (filter is_nh (snoc H (mk_hyp f (mk_function A x B)) ++ J)))) as cv.
  clear hyp1 hyp2.
  dwfseq.
  intros.
  generalize (isprogram_lsubst2 e [(z,mk_axiom)]); simpl; intro k.
  autodimp k hyp; sp; cpx.
  unfold subst in X; rw k in X; clear k.
  rw in_remove_nvars in X; simpl in X; sp.
  apply not_over_or in X; sp.
  generalize (ce x0); sp.
  allrw in_app_iff; allrw in_snoc; sp.
  allrw in_app_iff; allrw in_snoc; sp.

  exists cv.

  (* We prove some simple facts on our sequents *)
  assert (disjoint (free_vars A) (vars_hyps J)
          # disjoint (remove_nvars [x] (free_vars B)) (vars_hyps J)
          # subvars (free_vars a) (snoc (vars_hyps H) f ++ vars_hyps J)
          # wf_term a
          # !LIn z (free_vars C)
          # !LIn z (vars_hyps H)
          # !LIn z (vars_hyps J)
          # (z <> f)
          # !LIn f (vars_hyps H)
          # !LIn f (vars_hyps J)
          # !LIn f (free_vars A)
          # !LIn f (free_vars B)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp;
    try (complete (introv i; discover; allunfold @disjoint; discover; auto));
    try (complete (assert (LIn f (remove_nvars [x] (free_vars B)))
                    by (rw in_remove_nvars; rw in_single_iff; sp);
                   discover; auto));
    try (complete (generalize (wg7 f);
                   rw in_remove_nvars; simpl; sp;
                   dest_imp X0 h));
    try (complete (unfold disjoint; introv i;
                   generalize (wfh10 t); sp;
                   apply wfh11 in X; sp));
    try (complete (apply wf_member_iff in wfct1; sp));
    try (complete (generalize (wfh10 z); rw in_app_iff; rw in_snoc; sp));
    try (complete (apply cg in X; allrw in_app_iff; allrw in_snoc; sp;
                   generalize (wfh10 f); rw in_remove_nvars; simpl; intro i;
                   dest_imp i hyp));
    try (complete (generalize (wfh10 f); rw in_remove_nvars; simpl; intro i;
                   dest_imp i hyp)).

  destruct vhyps as [ daj vhyps ].
  destruct vhyps as [ dbj vhyps ].
  destruct vhyps as [ sva vhyps ].
  destruct vhyps as [ wa vhyps ].
  destruct vhyps as [ nizc vhyps ].
  destruct vhyps as [ nizh vhyps ].
  destruct vhyps as [ nizj vhyps ].
  destruct vhyps as [ nzf vhyps ].
  destruct vhyps as [ nifh vhyps ].
  destruct vhyps as [ nifj vhyps ].
  destruct vhyps as [ nifa nifb ].
  (* done with proving these simple facts *)

  vr_seq_true.

  duplicate sim as simapp.

  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx.
  lsubst_tac.
  rw @equality_in_function in sim2; repnd.

  vr_seq_true in hyp2.
  generalize (hyp2 (snoc (snoc s1a0 (f, t1) ++ s1b) (z, mkc_axiom))
                   (snoc (snoc s2a0 (f, t2) ++ s2b) (z, mkc_axiom)));
    clear hyp2; intros hyp2.
  repeat (autodimp hyp2 h); exrepnd.

  (* hyps_functionality *)

  generalize (hyps_functionality_snoc lib
                (snoc H (mk_hyp f (mk_function A x B)) ++ J)
                (mk_hyp z (mk_member (mk_apply (mk_var f) a) (subst B x a)))
                (snoc s1a0 (f, t1) ++ s1b)
                mkc_axiom); simpl; intro k.
  apply k; try (complete auto); clear k.
  introv eq sim; GC; lsubst_tac.
  rw @tequality_mkc_member_sp.
  apply equality_refl in eq.
  rw <- @member_member_iff in eq.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1a0 (f, t1) ++ s1b) s'); clear hyp1; intros hyp1.
  repeat (autodimp hyp1 h); exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_member_iff in hyp1.
  rw @tequality_mkc_member_sp in hyp0; repnd.

  assert (equality lib (lsubstc a wa (snoc s1a0 (f, t1) ++ s1b) c3)
                   (lsubstc a wa s' c5)
                   (lsubstc A w1 s1a0 c1)) as eqa.
  sp.
  unfold member in hyp1.
  spcast; apply @equality_respects_cequivc_right with (t2 := lsubstc a wa (snoc s1a0 (f, t1) ++ s1b) c3); sp.

  applydup sim5 in eqa.

  duplicate sim as sim'.
  apply eqh in sim'.

  rw @eq_hyps_app in sim'; simpl in sim'; exrepnd; subst; cpx.
  apply app_split in sim'0; repnd; allrw length_snoc;
  try (complete (allrw; sp)); subst; cpx.

  rw @eq_hyps_snoc in sim'5; simpl in sim'5; exrepnd; subst; cpx.
  lsubst_tac.
  rw @tequality_function in sim'0; repnd.

  applydup sim'0 in eqa as teq.

  assert (substc (lsubstc a wa (snoc s1a (f, t0) ++ s1b0) c3) x
                 (lsubstc_vars B w2 (csub_filter s1a [x]) [x] c2)
          = lsubstc (subst B x a) wT (snoc s1a (f, t0) ++ s1b0) cT)
         as eq1
         by (apply substc_lsubstc_type_family_codom; sp; repeat insub).
  rw eq1 in teq.

  assert (substc (lsubstc a wa (snoc s2a1 (f, t3) ++ s2b0) c5) x
                 (lsubstc_vars B w2 (csub_filter s2a1 [x]) [x] c9)
          = lsubstc (subst B x a) wT (snoc s2a1 (f, t3) ++ s2b0) cT0)
         as eq2
         by (apply substc_lsubstc_type_family_codom; sp; repeat insub).
  rw eq2 in teq.

  split; try (complete auto).

  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  apply app_split in sim7; repnd; allrw length_snoc;
  try (complete (allrw; sp)); subst; cpx.
  apply app_split in sim9; repnd; allrw length_snoc;
  try (complete (allrw; sp)); subst; cpx.
  rw @similarity_snoc in sim12; simpl in sim12; exrepnd; subst; cpx.
  lsubst_tac.
  rw @equality_in_function in sim9; repnd.
  applydup sim9 in eqa as eqf.
  rw eq1 in eqf.

  left; sp.

  (* similarity *)

  assert (wf_term (mk_member (mk_apply (mk_var f) a) (subst B x a))) as wm.
  apply wf_member; sp; try (apply wf_apply; sp).
  apply subst_preserves_wf_term; sp.

  assert (cover_vars (mk_member (mk_apply (mk_var f) a) (subst B x a))
                     (snoc s1a0 (f, t1) ++ s1b)) as cm.
  apply cover_vars_member; sp.
  apply cover_vars_apply; sp.
  apply cover_vars_var.
  rw @dom_csub_app; rw @dom_csub_snoc; rw in_app_iff; rw in_snoc; simpl; sp.
  rw @cover_vars_eq; rw @dom_csub_app; rw @dom_csub_snoc; insub.
  (* begin proof of last cover_vars *)
  rw @cover_vars_eq; rw @cover_vars_covered; apply covered_subst; sp.
  rw @dom_csub_app; rw @dom_csub_snoc; simpl.
  rw cons_app; apply covered_app_weak_l.
  clear sim2 sim5; unfold cover_vars_upto in c2; unfold covered.
  prove_subvars c2; allsimpl; sp.
  rw @dom_csub_csub_filter in l; rw in_remove_nvars in l; rw in_single_iff in l.
  rw in_snoc; sp.
  clear hyp1; rw @covered_equality in ct0; repnd.
  unfold covered; unfold covered in ct1.
  rw @vars_hyps_app in ct1; rw @vars_hyps_snoc in ct1; simpl in ct1.
  rw @dom_csub_app; rw @dom_csub_snoc; simpl.
  allapply @similarity_dom; repnd; allrw; rw @vars_hyps_substitute_hyps; sp.
  (* end proof of last cover_vars *)

  rw @similarity_snoc; simpl.
  exists (snoc s1a0 (f, t1) ++ s1b)
         (snoc s2a0 (f, t2) ++ s2b)
         (@mkc_axiom p) (@mkc_axiom p)
         wm cm; sp.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_member_iff.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1a0 (f, t1) ++ s1b)
                   (snoc s2a0 (f, t2) ++ s2b));
    clear hyp1; intros hyp1.
  repeat (autodimp hyp1 h); exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_member_iff in hyp1.
  rw @tequality_mkc_member_sp in hyp0; repnd.
  unfold member in hyp1.
  apply sim2 in hyp1.

  assert (substc (lsubstc a wa (snoc s1a0 (f, t1) ++ s1b) c3) x
                 (lsubstc_vars B w2 (csub_filter s1a0 [x]) [x] c2)
          = lsubstc (subst B x a) wT (snoc s1a0 (f, t1) ++ s1b) cT)
         as eq1
         by (apply substc_lsubstc_type_family_codom; sp; repeat insub).
  rw eq1 in hyp1.
  apply equality_refl in hyp1; sp.

  (* conclusion *)

  lsubst_tac; sp.

  assert (lsubstc e wfce0 (snoc (snoc s1a0 (f, t1) ++ s1b) (z, mkc_axiom)) pt0
          = lsubstc (subst e z mk_axiom) wfce (snoc s1a0 (f, t1) ++ s1b) pt1) as eq1.
  apply lsubstc_eq_if_csubst.
  rw <- @csubst_swap.
  rw cons_as_app.
  rw <- @csubst_app.
  unfold csubst, subst; simpl; sp.
  rw @dom_csub_app; rw @dom_csub_snoc; simpl; rw in_app_iff; rw in_snoc.
  insub.

  assert (lsubstc e wfce0 (snoc (snoc s2a0 (f, t2) ++ s2b) (z, mkc_axiom)) pt3
          = lsubstc (subst e z mk_axiom) wfce (snoc s2a0 (f, t2) ++ s2b) pt2) as eq2.
  apply lsubstc_eq_if_csubst.
  rw <- @csubst_swap.
  rw cons_as_app.
  rw <- @csubst_app.
  unfold csubst, subst; simpl; sp.
  rw @dom_csub_app; rw @dom_csub_snoc; simpl; rw in_app_iff; rw in_snoc.
  insub.

  rw eq1 in hyp2; rw eq2 in hyp2; sp.
Qed.

(* begin hide *)


Lemma rule_function_elimination_true_ex {p} :
  forall lib (A B C a e : NTerm),
  forall f x z : NVar,
  forall H J : @barehypotheses p,
  forall bc1 : x <> f,
  forall bc2 : disjoint (vars_hyps H) (bound_vars B),
  forall bc3 : disjoint (vars_hyps J) (bound_vars B),
  forall bc4 : !LIn f (bound_vars B),
    rule_true_if lib (rule_function_elimination
                    A B C a e
                    f x z
                    H J).
Proof.
  intros.
  generalize (rule_function_elimination_true lib A B C a e f x z H J bc1 bc2 bc3 bc4); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.


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
  rw @tequality_mkc_equality_sp in t; repnd; GC.
  allrewrite @member_eq.
  rw <- @member_equality_iff in e.
  allapply @equality_in_uni.
  destruct t1 as [ s | s ].
  apply @equality_in_uni in s; auto.
  spcast; apply tequality_respects_cequivc_right with (T2 := lsubstc A wa s1 c1); auto.

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
  rw @tequality_mkc_equality_sp in t; repnd; GC.
  allrewrite @member_eq.
  allrw <- @member_equality_iff.
  allapply @equality_in_uni.
  destruct t1 as [ s | s ].
  apply @equality_in_uni in s; auto.
  spcast; apply tequality_respects_cequivc_right with (T2 := lsubstc A wa s1 c1); auto.
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

Definition rule_function_equality {p}
           (a1 a2 b1 b2 : NTerm)
           (x1 x2 y : NVar)
           (i   : nat)
           (H   : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_function a1 x1 b1)
                      (mk_function a2 x2 b2)
                      (mk_uni i))))
    [ mk_baresequent
        H
        (mk_conclax (mk_equality a1 a2 (mk_uni i))),
      mk_baresequent
        (snoc H (mk_hyp y a1))
        (mk_conclax (mk_equality
                       (subst b1 x1 (mk_var y))
                       (subst b2 x2 (mk_var y))
                       (mk_uni i)))
    ]
    [ sarg_var y ].

Lemma rule_function_equality_true {pp} :
  forall lib (a1 a2 b1 b2 : NTerm),
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses pp,
    rule_true lib (rule_function_equality
                     a1 a2 b1 b2
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


(* begin hide *)


Lemma rule_function_equality_true_ex {o} :
  forall lib y i a1 a2 b1 b2 x1 x2 H,
    @rule_true_if o lib (rule_function_equality a1 a2 b1 b2 x1 x2 y i H).
Proof.
  intros.
  generalize (rule_function_equality_true lib a1 a2 b1 b2 x1 x2 y i H); intro rt.
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
  rw @tequality_mkc_equality2_sp in hyp0; repnd.

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
  rw @tequality_mkc_equality2_sp in hyp0; repnd.
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

(* [26] ============ APPLY @EQUALITY ============ *)

(**

  We following rule called ``apply @equality`` allows one to prove that
  applications are well-typed.
<<
   H |- f1 t1 = f2 t2 in B[x\t1]

     By applyEquality ()

     H |- f1 = f2 in x:A->B
     H |- t1 = t2 in A
>>
 *)

Definition rule_apply_equality {o}
           (A B f1 f2 t1 t2 : NTerm)
           (x : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality
                                    (mk_apply f1 t1)
                                    (mk_apply f2 t2)
                                    (subst B x t1))))
    [ mk_baresequent H (mk_conclax (mk_equality f1 f2 (mk_function A x B))),
      mk_baresequent H (mk_conclax (mk_equality t1 t2 A))
    ]
    [].

Lemma rule_apply_equality_true {o} :
  forall lib (A B f1 f2 t1 t2 : NTerm)
         (x : NVar)
         (i   : nat)
         (H   : @barehypotheses o)
         (bc1 : disjoint (free_vars t1) (bound_vars B))
         (bc2 : disjoint (free_vars t2) (bound_vars B)),
    rule_true lib (rule_apply_equality A B f1 f2 t1 t2 x H).
Proof.
  intros.
  unfold rule_apply_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent H (mk_conclax (mk_equality f1 f2 (mk_function A x B))))
                   (inl eq_refl))
             (hyps (mk_baresequent H (mk_conclax (mk_equality t1 t2 A)))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.
  duplicate wfct as wfi.
  rw <- @wf_equality_iff in wfct.
  destruct wfct as [ wa1 wfct ].
  destruct wfct as [ wa2 wfct ].
  rw <- @wf_apply_iff in wa1.
  destruct wa1 as [ wf1 wt1 ].
  rw <- @wf_apply_iff in wa2.
  destruct wa2 as [ wf2 wt2 ].

  exists (@covered_axiom o (nh_vars_hyps H)); GC.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  rw @tequality_mkc_equality2_sp in hyp3.
  rw @tequality_mkc_equality2_sp in hyp0.
  rw @tequality_mkc_equality2_sp; repnd.
  repeat (rw prod_assoc).
  rw @tequality_function in hyp4; repnd.

  allunfold @equorsq2; repnd.

  (* a few assertions *)
  assert (equality lib (lsubstc t1 wt1 s1 c1)
                   (lsubstc t1 wt1 s2 c4)
                   (lsubstc A wT s1 cT))
         as eq1
         by (apply @cequorsq_equality_trans2 with (t2 := lsubstc t1 wt1 s1 c1); sp;
             allapply @equality_refl; sp).

  assert (equality lib (lsubstc f1 wf1 s1 c0)
                   (lsubstc f1 wf1 s2 c7)
                   (mkc_function (lsubstc A wT s1 cT) x
                                 (lsubstc_vars B w2 (csub_filter s1 [x]) [x] c5)))
         as eq3
         by (apply @cequorsq_equality_trans2 with (t2 := lsubstc f1 wf1 s1 c0); sp;
             allapply @equality_refl; sp).

  assert (equality lib (lsubstc t2 wt2 s1 c2)
                   (lsubstc t2 wt2 s2 c6)
                   (lsubstc A wT s1 cT))
         as eq5
         by (apply @cequorsq_equality_trans2 with (t2 := lsubstc t2 wt2 s1 c2); sp;
             apply @equality_sym in hyp2; apply @equality_refl in hyp2; sp).

  assert (equality lib (lsubstc f2 wf2 s1 c3)
                   (lsubstc f2 wf2 s2 c8)
                   (mkc_function (lsubstc A wT s1 cT) x
                                 (lsubstc_vars B w2 (csub_filter s1 [x]) [x] c5)))
         as eq6
         by (apply @cequorsq_equality_trans2 with (t2 := lsubstc f2 wf2 s1 c3); sp;
             apply @equality_sym in hyp1; apply @equality_refl in hyp1; sp).

  assert (equality lib (lsubstc t1 wt1 s1 c1)
                   (lsubstc t2 wt2 s2 c6)
                   (lsubstc A wT s1 cT))
         as eq7 by (apply @equality_trans with (t2 := lsubstc t2 wt2 s1 c2); sp).

  assert (wf_term (subst B x t2))
         as wfs2
         by (apply lsubst_preserves_wf_term; sp;
             unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp).

  assert (cover_vars (subst B x t2) s1)
         as cv2.
  (* begin proof of assert *)
  rw @cover_vars_eq.
  rw @cover_vars_eq in cT3.
  unfold subst.
  rw subvars_prop; introv k.
  generalize (eqvars_free_vars_disjoint B [(x,t1)]); intro u1.
  generalize (eqvars_free_vars_disjoint B [(x,t2)]); intro u2.
  rw eqvars_prop in u1.
  rw eqvars_prop in u2.
  rw u2 in k; simpl in k.
  rw in_app_iff in k; rw in_remove_nvars in k; rw in_single_iff in k; repdors; repnd.
  rw subvars_prop in cT3.
  apply cT3; unfold subst.
  rw u1.
  rw in_app_iff; rw in_remove_nvars; rw in_single_iff; sp.
  revert k.
  boolvar; simpl; allrw app_nil_r; intro k; sp.
  clear_dependents c2.
  rw @cover_vars_eq in c2.
  rw subvars_prop in c2.
  apply c2; sp.
  (* end proof of assert *)

  assert (cover_vars (subst B x t2) s2)
         as cv3
         by (rw @cover_vars_eq;
             rw @cover_vars_eq in cv2;
             allapply @similarity_dom; repnd; allrw;
             rw sim0 in cv2; sp).

  assert (tequality lib (lsubstc (subst B x t1) wfct s1 cT3)
                    (lsubstc (subst B x t2) wfs2 s1 cv2)) as teqB.
  (* begin proof of assert *)
  generalize (hyp4 (lsubstc t1 wt1 s1 c1) (lsubstc t2 wt2 s2 c6)); intro k1.
  autodimp k1 hyp; sp.
  generalize (hyp4 (lsubstc t2 wt2 s1 c2) (lsubstc t2 wt2 s2 c6)); intro k2.
  autodimp k2 hyp; sp.
  generalize (simple_lsubstc_subst t1 x B wfct s1 cT3 wt1 c1 w2 c5); intro e1.
  autodimp e1 hyp.
  rw <- e1 in k1; clear e1.
  generalize (simple_lsubstc_subst t2 x B wfs2 s1 cv2 wt2 c2 w2 c5); intro e1.
  autodimp e1 hyp.
  rw <- e1 in k2; clear e1.
  generalize (simple_lsubstc_subst t2 x B wfs2 s2 cv3 wt2 c6 w2 c10); intro e1.
  autodimp e1 hyp.
  rw <- e1 in k1; rw <- e1 in k2; clear e1.
  apply @tequality_trans with (t2 := lsubstc (subst B x t2) wfs2 s2 cv3); sp.
  apply @tequality_sym; sp.
  (* end proof of assert *)


  (* now we start proving our conclusion *)
  dands.

  (* from hyp 4 *)
  generalize (hyp4 (lsubstc t1 wt1 s1 c1) (lsubstc t1 wt1 s2 c4) eq1); intro teq.

  generalize (simple_lsubstc_subst t1 x B wfct s1 cT3 wt1 c1 w2 c5); intro e1.
  autodimp e1 hyp.
  rw <- e1 in teq.

  generalize (simple_lsubstc_subst t1 x B wfct s2 cT4 wt1 c4 w2 c10); intro e2.
  autodimp e2 hyp.
  rw <- e2 in teq; sp.

  (* from eq3 and eq1 *)
  rw @equality_in_function in eq3; repnd.
  generalize (eq3 (lsubstc t1 wt1 s1 c1) (lsubstc t1 wt1 s2 c4) eq1); intro e'.
  generalize (simple_lsubstc_subst t1 x B wfct s1 cT3 wt1 c1 w2 c5); intro e1.
  autodimp e1 hyp.
  rw <- e1 in e'; sp.

  (* from eq6 and eq5 *)
  rw @equality_in_function in eq6; repnd.
  generalize (eq6 (lsubstc t2 wt2 s1 c2) (lsubstc t2 wt2 s2 c6) eq5); intro e'.
  generalize (simple_lsubstc_subst t2 x B wfs2 s1 cv2 wt2 c2 w2 c5); intro e1.
  autodimp e1 hyp.
  rw <- e1 in e'; sp.
  left.
  eapply @tequality_preserving_equality.
  exact e'.
  apply @tequality_sym; sp.

  (* from hyp1 and hyp2 *)
  rw @equality_in_function in hyp1; repnd.
  generalize (hyp1 (lsubstc t1 wt1 s1 c1) (lsubstc t2 wt2 s1 c2) hyp2); intro e'.
  generalize (simple_lsubstc_subst t1 x B wfct s1 cT3 wt1 c1 w2 c5); intro e1.
  autodimp e1 hyp.
  rw <- e1 in e'; sp.
Qed.

(* begin hide *)



(* end hide *)


(* [27] ============ APPLY REDUCE ============ *)

(**

  The following rule called the ``apply reduce'' rule is the
  computation rule for applications.
<<
   H |- (\x.t)s = u in T

     By applyReduce ()

     H |- t[x\s] = u in T
>>
 *)

Definition rule_apply_reduce {o}
           (T t s u : NTerm)
           (x : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality (mk_apply (mk_lam x t) s) u T)))
    [ mk_baresequent
        H
        (mk_conclax (mk_equality (subst t x s) u T))
    ]
    [].

Lemma rule_apply_reduce_true {o} :
  forall lib (T t s u : NTerm)
         (x   : NVar)
         (H   : @barehypotheses o)
         (bc1 : disjoint (free_vars s) (bound_vars t)),
    rule_true lib (rule_apply_reduce T t s u x H).
Proof.
  intros.
  unfold rule_apply_reduce, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent H (mk_conclax (mk_equality (subst t x s) u T)))
                   (inl eq_refl));
    simpl; intros hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.
  duplicate wfct as wfi.
  rw <- @wf_equality_iff in wfct.
  destruct wfct as [ wa wfct ].
  destruct wfct as [ wu wT ].
  rw <- @wf_apply_iff in wa.
  destruct wa as [ wt ws ].
  rw <- @wf_lam_iff in wt.

  exists (@covered_axiom o (nh_vars_hyps H)); GC.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  rw @tequality_mkc_equality2_sp in hyp0; repnd.
  rw @tequality_mkc_equality2_sp.
  repeat (rw prod_assoc).
  allunfold @equorsq2; repnd.

  assert (cequivc lib
            (mkc_apply
               (mkc_lam x (lsubstc_vars t wt (csub_filter s1 [x]) [x] c10))
               (lsubstc s ws s1 c6))
            (lsubstc (subst t x s) w1 s1 c1))
         as ceq1.
  (* begin proof of assert *)
  destruct_cterms; unfold cequivc; simpl.
  generalize (cequiv_beta lib x (csubst t (csub_filter s1 [x])) (csubst s s1)); intro k.
  autodimp k hyp.
  rw <- @isprog_vars_csubst_iff.
  rw @isprog_vars_eq; sp.
  rw @nt_wf_eq; sp.
  autodimp k hyp.
  apply isprogram_csubst; sp.
  rw @nt_wf_eq; sp.
  eapply cequiv_trans.
  exact k.
  rw <- @simple_csubst_subst; sp.
  apply cequiv_refl.
  apply isprogram_csubst; sp.
  unfold subst; apply lsubst_wf_iff; try (rw @nt_wf_eq; sp).
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp.
  (* end proof of assert *)

  assert (cequivc lib
            (mkc_apply
               (mkc_lam x (lsubstc_vars t wt (csub_filter s2 [x]) [x] c11))
               (lsubstc s ws s2 c9))
            (lsubstc (subst t x s) w1 s2 c0))
         as ceq2.
  (* begin proof of assert *)
  destruct_cterms; unfold cequivc; simpl.
  generalize (cequiv_beta lib x (csubst t (csub_filter s2 [x])) (csubst s s2)); intro k.
  autodimp k hyp.
  rw <- @isprog_vars_csubst_iff.
  rw @isprog_vars_eq; sp.
  rw @nt_wf_eq; sp.
  autodimp k hyp.
  apply isprogram_csubst; sp.
  rw @nt_wf_eq; sp.
  eapply cequiv_trans.
  exact k.
  rw <- @simple_csubst_subst; sp.
  apply cequiv_refl.
  apply isprogram_csubst; sp.
  unfold subst; apply lsubst_wf_iff; try (rw @nt_wf_eq; sp).
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp.
  (* end proof of assert *)


  (* we start proving our conclusion *)
  dands; try (complete sp).

  left.
  eapply @equality_respects_cequivc_left.
  apply cequivc_sym.
  exact ceq1.
  apply @equality_sym.
  eapply @equality_respects_cequivc_left.
  apply cequivc_sym.
  exact ceq2.
  apply @equality_sym.
  unfold equorsq in hyp3; repdors; spcast; sp.
  apply @equality_respects_cequivc; sp.
  allapply @equality_refl; sp.

  eapply @equality_respects_cequivc_left.
  apply cequivc_sym.
  exact ceq1.
  sp.
Qed.

(* begin hide *)



(* end hide *)


(* [28] ============ FUNCTION EXTENSIONALITY ============ *)

(**

  The following rule called the ``function extensionality rule''
  states that the equality between functions in Nuprl is extensional.
<<
   H |- f1 = f2 in x:A->B

     By funcionExtensionality lvl(i) z ()

     H z : A |- f1 z = f2 z in B[x\z]
     H |- A = A in Type(i)
>>
 *)

Definition rule_function_extensionality {o}
           (A B f1 f2 : NTerm)
           (x z : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality f1 f2 (mk_function A x B))))
    [ mk_baresequent
        (snoc H (mk_hyp z A))
        (mk_conclax (mk_equality
                       (mk_apply f1 (mk_var z))
                       (mk_apply f2 (mk_var z))
                       (subst B x (mk_var z)))),
      mk_baresequent
        H
        (mk_conclax (mk_equality A A (mk_uni i))) ]
    [sarg_var z].

Lemma rule_function_extensionality_true {o} :
  forall lib (A B f1 f2 : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o)
         (bc1 : !LIn z (bound_vars B)),
    rule_true lib (rule_function_extensionality A B f1 f2 x z i H).
Proof.
  intros.
  unfold rule_function_extensionality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent (snoc H (mk_hyp z A))
                                  (mk_conclax (mk_equality
                                                 (mk_apply f1 (mk_var z))
                                                 (mk_apply f2 (mk_var z))
                                                 (subst B x (mk_var z)))))
                   (inl eq_refl))
             (hyps (mk_baresequent H (mk_conclax (mk_equality A A (mk_uni i))))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.
  duplicate wfct as wfi.
  rw <- @wf_equality_iff in wfct.
  destruct wfct as [ wf1 wfct ].
  destruct wfct as [ wf2 wfct ].
  rw <- @wf_function_iff in wfct.
  destruct wfct as [ wA wB ].

  exists (@covered_axiom o (nh_vars_hyps H)); GC.

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars f1)
          # !LIn z (free_vars f2)
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

  destruct vhyps as [ nzB  vhyps ].
  destruct vhyps as [ nzf1 vhyps ].
  destruct vhyps as [ nzf2 vhyps ].
  destruct vhyps as [ nzA  nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lift_lsubst.
  rw @member_eq.
  rw <- @member_equality_iff.

  assert (tequality lib
            (mkc_function (lsubstc A wA s1 c4) x
                          (lsubstc_vars B wB (csub_filter s1 [x]) [x] c5))
            (mkc_function (lsubstc A wA s2 c6) x
                          (lsubstc_vars B wB (csub_filter s2 [x]) [x] c7))) as eqfunc.

  rw @tequality_function.

  split.

  (* First, we prove that the a's are types *)
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2.
  exrepd.
  lift_lsubst in t.
  lift_lsubst in e.
  rw @member_eq in e.
  rw <- @member_equality_iff in e.
  applydup @equality_in_uni in e as e'.
  rw @fold_type in e'.
  apply @equality_commutes2 in t; try (complete auto).
  apply @equality_in_uni in t; sp.

  (* Then we prove that the b's are type families *)
  intros a a' eqaa'.
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z, a)) (snoc s2 (z, a'))); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  (* we have to prove the functionality of our hypotheses *)
  apply hyps_functionality_snoc2; simpl; try (complete sp).
  introv eq s.
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s' eqh s); clear hyp2; intro hyp2.
  exrepd.
  lift_lsubst in t.
  lift_lsubst in e.
  rw @member_eq in e.
  rw <- @member_equality_iff in e.
  applydup @equality_in_uni in e as e'.
  rw @fold_type in e'.
  apply @equality_commutes2 in t; try (complete auto).
  apply @equality_in_uni in t; sp.

  (* we have to prove the similarity of our hypotheses *)
  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s2 a a' wA c4; sp.

  (* we can now use hyp1 *)
  exrepnd; lsubst_tac.

  (* we use hyp0 *)
  rw @tequality_mkc_equality2_sp in hyp0; repnd.

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
  assert (forall a a' s1 s2,
            hyps_functionality lib s1 H
            -> similarity lib s1 s2 H
            -> {c1f : cover_vars f1 s1
                , {c2f : cover_vars f2 s2
                , {c1A : cover_vars A s1
                , {c1B : cover_vars_upto B (csub_filter s1 [x]) [x]
                , equality lib a a' (lsubstc A wA s1 c1A)
                  -> equality lib
                       (mkc_apply (lsubstc f1 wf1 s1 c1f) a)
                       (mkc_apply (lsubstc f2 wf2 s2 c2f) a')
                       (substc a x (lsubstc_vars B wB (csub_filter s1 [x]) [x] c1B))}}}}) as eqlam.
  introv eqh0 sim0.

  assert (cover_vars f1 s0) as c1f1.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allrw @cover_vars_eq.
  allrw.
  rw sim2 in c1; sp.

  assert (cover_vars f1 s3) as c2f1.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allrw @cover_vars_eq.
  allrw.
  rw sim2 in c1; sp.

  assert (cover_vars f2 s0) as c1f2.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allrw @cover_vars_eq.
  allrw.
  rw sim2 in c2; sp.

  assert (cover_vars f2 s3) as c2f2.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allrw @cover_vars_eq.
  allrw.
  rw sim2 in c2; sp.

  assert (cover_vars_upto B (csub_filter s0 [x]) [x]) as cB0.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allunfold @cover_vars_upto.
  allrw @dom_csub_csub_filter.
  allrw.
  rw sim in c7; sp.

  assert (cover_vars_upto B (csub_filter s3 [x]) [x]) as cB3.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allunfold @cover_vars_upto.
  allrw @dom_csub_csub_filter.
  allrw.
  rw sim in c7; sp.

  assert (cover_vars A s0) as cA0.
  clear eqfunc.
  allrw @cover_vars_eq.
  allapply @similarity_dom; repnd.
  allrw.
  rw sim in c6; sp.

  assert (cover_vars A s3) as cA3.
  clear eqfunc.
  allrw @cover_vars_eq.
  allapply @similarity_dom; repnd.
  allrw.
  rw sim in c6; sp.

  exists c1f1 c2f2 cA0 cB0.
  introv eqaa'.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s0 (z, a)) (snoc s3 (z, a'))); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  (* we have to prove the functionality of our hypotheses *)
  apply hyps_functionality_snoc2; simpl; try (complete sp).
  introv eq s.
  vr_seq_true in hyp2.
  generalize (hyp2 s0 s' eqh0 s); clear hyp2; intro hyp2.
  exrepd.
  lift_lsubst in t.
  lift_lsubst in e.
  rw @member_eq in e.
  rw <- @member_equality_iff in e.
  applydup @equality_in_uni in e as e'.
  rw @fold_type in e'.
  apply @equality_commutes2 in t; try (complete auto).
  apply @equality_in_uni in t; sp.

  (* we have to prove the similarity of our hypotheses *)
  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  exists s0 s3 a a' wA cA0; sp.

  (* we can now use hyp1 *)
  exrepnd; lsubst_tac.
  rw @tequality_mkc_equality2_sp in hyp0; repnd.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1.
  clear_irr; GC.

  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s0 (z, a)) cT1
          = substc a x (lsubstc_vars B wB (csub_filter s0 [x]) [x] cB0)) as eq1
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq1 in hyp0.
  rewrite eq1 in hyp1.
  rewrite eq1 in hyp3.
  clear eq1.

  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s3 (z, a')) cT2
          = substc a' x (lsubstc_vars B wB (csub_filter s3 [x]) [x] cB3)) as eq2
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq2 in hyp3.
  clear eq2.

  apply @cequorsq2_prop in hyp0; try (complete auto).

  (* a few useful assertions *)
  assert (similarity lib s1 s1 H)
         as sim1
         by (allapply @similarity_refl; sp).
  assert (similarity lib s2 s2 H)
         as sim2
         by (apply @similarity_sym in sim; allapplydup @similarity_refl; sp;
             apply eqh in sim; sp).
  assert (hyps_functionality lib s2 H)
         as eqh2
         by (apply @similarity_hyps_functionality_trans with (s1 := s1); sp).


  (* we start proving our conclusion *)
  rw @equality_in_function2.
  dands; try (complete sp).


  (* tequality *)
  rw @tequality_mkc_equality2_sp.
  dands; try (complete sp).

  (* we prove cequorsq2 *)
  split.

  (* application in B *)
  left.
  rw @equality_in_function2.
  split; try (complete (apply @tequality_refl in eqfunc; sp)).
  introv e.
  assert (equality lib a' a' (lsubstc A wA s2 c6))
         as e'
         by (apply @equality_sym in e; apply @equality_refl in e;
             rw @tequality_function in eqfunc; repnd;
             eapply @tequality_preserving_equality;
             try (exact e); sp).

  generalize (eqlam a a' s1 s2 eqh sim); intro k1; exrepnd; clear_irr; sp.
  generalize (eqlam a' a' s2 s2 eqh2 sim2); intro k2; exrepnd; clear_irr; sp.

  eapply @equality_trans; sp.
  exact k1.
  apply @equality_sym.
  eapply @tequality_preserving_equality.
  exact k2.
  apply @tequality_sym.
  rw @tequality_function in eqfunc; repnd; sp.

  (* application in B *)
  left.
  rw @equality_in_function2.
  split; try (complete (apply @tequality_refl in eqfunc; sp)).
  introv e.
  assert (equality lib a a (lsubstc A wA s1 c4)) as e' by (allapply @equality_refl; sp).

  generalize (eqlam a a' s1 s2 eqh sim); intro k1; exrepnd; clear_irr; sp.
  generalize (eqlam a a s1 s1 eqh sim1); intro k2; exrepnd; clear_irr; sp.

  eapply @equality_trans; sp.
  apply equality_sym.
  exact k2.
  auto.


  (* type *)
  apply @tequality_refl in eqfunc; sp.


  (* application in B *)
  introv e.
  generalize (eqlam a a' s1 s1 eqh sim1); intro k; exrepnd; clear_irr; sp.
Qed.

(* end hide *)


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
