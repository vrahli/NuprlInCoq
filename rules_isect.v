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


Require Export sequents_tacs.
Require Export per_props_equality.
Require Export rules_tyfam.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)



(* end hide *)

(**

  We now prove the truth of several rules about the intersection type.

*)

(* [3] ============ ISECT MEMBER FORMATION ============ *)

(**

  We can state the intersection member formation rule as follows:

<<
   H |- isect x:A. B ext b

     By isect_memberFormation lvl(i) z ()

     H [z : A] |- subst B x z ext b
     H |- A = A in Type(i)
>>

 *)

Definition rule_isect_member_formation {o}
           (A B b : NTerm)
           (x z  : NVar)
           (i    : nat)
           (H    : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_isect A x B) b))
    [ mk_baresequent
        (snoc H (mk_hhyp z A))
        (mk_concl (subst B x (mk_var z)) b),
      mk_baresequent H (mk_conclax (mk_equality A A (mk_uni i))) ]
    [sarg_var z].

Lemma rule_isect_member_formation_true {o} :
  forall lib (A B b : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o)
         (bc1 : !LIn z (bound_vars B)),
    rule_true lib (rule_isect_member_formation A B b x z i H).
Proof.
  intros.
  unfold rule_isect_member_formation, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent (snoc H (mk_hhyp z A))
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
  rw <- @wf_isect_iff in wfct.
  destruct wfct as [ wa wb ].
  duplicate ce0 as ce.
  allrw @nh_vars_hyps_snoc; allsimpl.

  exists ce0; GC.

  (* We prove some simple facts on our sequents *)
  assert (covered b (nh_vars_hyps H)
          # (z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars b)
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

  destruct vhyps as [ bcH vhyps ].
  destruct vhyps as [ nzB vhyps ].
  destruct vhyps as [ nzb vhyps ].
  destruct vhyps as [ nzA nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  (* We prove our first subgoal *)
  assert (forall s2 pC2,
            similarity lib s1 s2 H
            -> tequality lib (lsubstc (mk_isect A x B) wfi s1 pC1)
                         (lsubstc (mk_isect A x B) wfi s2 pC2)) as tfb.
  clear s2 pC2 pt2 sim.
  intros s2 pC2 sim.
  lift_lsubst.
  rw @tequality_isect.

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
  allapply @equality_in_uni.
  destruct t2 as [ s | s ].
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
  rw @tequality_mkc_equality in t; repnd; GC.
  allrewrite @member_eq.
  allrw <- @member_equality_iff.
  allapply @equality_in_uni.
  destruct t3 as [ s | s ].
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
  rw @equality_in_isect.

  sp.
  (* We have to prove 3 goals *)

  (* 1) we have to prove that A is a type *)
  generalize (tfb s1 pC1 sim0); sp.
  lsubst_tac.
  allrw @tequality_isect; sp.

  (* 2) we have to prove that B is a type family *)
  generalize (tfb s1 pC1 sim0); sp.
  lsubst_tac.
  allrw @tequality_isect; sp.

  (* 3) we have to prove that b is a member B *)
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z, a)) (snoc s2 (z, a'))); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  (* first we have to prove that the hypotheses are functional *)
  intros s3 sim3.
  inversion sim3; cpx; allsimpl; cpx; clear_irr.
  assert (cover_vars A s4) as c4
    by (apply @similarity_cover_vars with (t := A) in sim1; auto).
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
  allrw @tequality_isect; sp.
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
    try (complete (rewrite dom_csub_eq; rewrite dom_csub_csub_filter; rw in_remove_nvars; simpl; sp)).
  repeat (rewrite <- csub2sub_cons).
  repeat (rewrite fold_csubst).
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
Qed.

(* begin hide *)

Lemma rule_isect_member_formation_true_ex {o} :
  forall lib i z A B b x H (bc1 : !LIn z (bound_vars B)),
    @rule_true_if o lib (rule_isect_member_formation A B b x z i H).
Proof.
  intros.
  generalize (rule_isect_member_formation_true lib A B b x z i H bc1); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Lemma rule_isect_member_formation_true2 {o} :
  forall lib i z A B b x H (bc1 : !LIn z (bound_vars B)),
    @rule_true2 o lib (rule_isect_member_formation A B b x z i H).
Proof.
  intros.
  generalize (rule_isect_member_formation_true lib A B b x z i H bc1); intro rt.
  apply rule_true_iff_rule_true2; sp.
Qed.

Lemma rule_isect_member_formation_wf {o} :
  forall i z A B b x H (bc1 : !LIn z (bound_vars B)),
    !LIn z (vars_hyps H)
    -> @wf_rule o (rule_isect_member_formation A B b x z i H).
Proof.
  intros.

  introv pwf m; allsimpl; repdors; subst; sp;
  allunfold @pwf_sequent; wfseq; sp;
  allrw @covered_isect; repnd; auto;
  allrw <- @wf_isect_iff; repnd; auto.

  allrw @vswf_hypotheses_nil_eq.
  apply wf_hypotheses_snoc; simpl; sp.
  apply isprog_vars_eq; sp.
  apply nt_wf_eq; sp.

  apply subst_preserves_wf_term; sp.
  apply @covered_subst; sp;
  try (apply @covered_var; rw in_snoc; sp);
  try (complete (rw cons_snoc; apply @covered_snoc_weak; auto)).
Qed.




(* end hide *)

(* [8] ============ ISECT EQUALITY ============ *)

(**

  We can state the intersection equality rule as follows:
<<
   H |- isect x1:a1. b1 = isect x2:a2.b2 in Type(i)

     By isectEquality y ()

     H |- a1 = a2 in Type(i)
     H y : a1 |- subst b1 x1 y = subst b2 x2 y in Type(i)
>>
 *)

Definition rule_isect_equality {o}
           (a1 a2 b1 b2 : NTerm)
           (x1 x2 y : NVar)
           (i   : nat)
           (H   : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_isect a1 x1 b1)
                      (mk_isect a2 x2 b2)
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

Lemma rule_isect_equality_true {o} :
  forall lib (a1 a2 b1 b2 : NTerm),
  forall x1 x2 y : NVar,
  forall i   : nat,
  forall H   : @barehypotheses o,
    rule_true lib (rule_isect_equality
                 a1 a2 b1 b2
                 x1 x2 y
                 i
                 H).
Proof.
  intros.
  apply (rule_tyfam_equality_true _ _ mkc_isect); auto.

  - introv; simpl; allrw remove_nvars_nil_l; allrw app_nil_r; auto.

  - introv; apply lsubstc_mk_isect_ex.

  - introv; apply equality_isect.
Qed.

(* begin hide *)

Lemma rule_isect_equality_true_ex {o} :
  forall lib y i a1 a2 b1 b2 x1 x2 H,
    @rule_true_if o lib (rule_isect_equality a1 a2 b1 b2 x1 x2 y i H).
Proof.
  intros.
  generalize (rule_isect_equality_true lib a1 a2 b1 b2 x1 x2 y i H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Lemma rule_isect_equality_true2 {o} :
  forall lib (y : NVar),
  forall i : nat,
  forall a1 a2 b1 b2 : NTerm,
  forall x1 x2 : NVar,
  forall H   : @barehypotheses o,
    rule_true2 lib (rule_isect_equality
                  a1 a2 b1 b2
                  x1 x2 y
                  i
                  H).
Proof.
  introv.
  apply rule_true_iff_rule_true2; auto.
  apply rule_isect_equality_true; auto.
Qed.

Lemma rule_isect_equality_wf {o} :
  forall y : NVar,
  forall i : nat,
  forall a1 a2 b1 b2 : NTerm,
  forall x1 x2 : NVar,
  forall H   : @barehypotheses o,
  forall c1  : !LIn y (vars_hyps H),
    wf_rule (rule_isect_equality
               a1 a2 b1 b2
               x1 x2 y
               i
               H).
Proof.
  introv c1.
  introv pwf m.

  allsimpl; repdors; sp; subst; allunfold @pwf_sequent; wfseq;
  allapply @wf_isect_iff; repnd; auto;
  allrw @covered_isect; repnd; auto;
  try (apply subst_preserves_wf_term; auto);
  try (apply @covered_subst; try (apply @covered_var; rw in_snoc; sp));
  try (complete (rw cons_snoc; apply @covered_snoc_weak; auto)).

  allrw @vswf_hypotheses_nil_eq.
  apply wf_hypotheses_snoc; simpl; dands; auto.
  apply isprog_vars_eq; dands; auto.
  apply nt_wf_eq; auto.
Qed.

(* end hide *)


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
