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


Require Import rules_useful.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)



(* end hide *)


(**

  The following rule states that we can always replace an [a] for a
  [b] in the conclusion of a sequent if [a] and [b] are
  computationally equivalent:

<<
  H |- C[a] ext t

    By cequivSubstConcl

    H |- C[b] ext t
    H |- a ~ b
>>

*)

Definition rule_cequiv_subst_concl {o}
           (H : @barehypotheses o)
           (x : NVar)
           (C a b t  : NTerm) :=
  mk_rule
    (mk_baresequent H (mk_concl (subst C x a) t))
    [ mk_baresequent H (mk_concl (subst C x b) t),
      mk_baresequent H (mk_conclax (mk_cequiv a b))
    ]
    [].

Lemma rule_cequiv_subst_concl_true {o} :
  forall lib (H  : @barehypotheses o)
         (x : NVar)
         (C a b t  : NTerm)
         (bc1 : disjoint (free_vars a) (bound_vars C))
         (bc2 : disjoint (free_vars b) (bound_vars C)),
    rule_true lib (rule_cequiv_subst_concl H x C a b t).
Proof.
  intros.
  unfold rule_cequiv_subst_concl, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].

  unfold closed_extract; simpl.

  assert (covered t (nh_vars_hyps H))
    as cov by (clear hyp1 hyp2; dwfseq; intros; discover; sp).

  exists cov.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.

  destruct wf1 as [ws1 cl1].
  destruct cl1 as [ct1 ce1].
  destruct ws1 as [wh1 wc1].
  destruct wc1 as [wT1 we1].
  destruct wf2 as [ws2 cl2].
  destruct cl2 as [ct2 ce2].
  destruct ws2 as [wh2 wc2].
  destruct wc2 as [wT2 we2].
  allunfold @closed_type; allunfold @closed_extract; allsimpl.
  dup wT2 as w.
  rw <- @wf_cequiv_iff in w; destruct w as [wa wb].

  assert (cover_vars a s1) as cova1 by (clear hyp1 hyp2; rw @covered_cequiv in ct2; repnd; rw @cover_vars_eq; insub).
  assert (cover_vars a s2) as cova2 by (clear hyp1 hyp2; rw @covered_cequiv in ct2; repnd; rw @cover_vars_eq; insub).
  assert (cover_vars b s1) as covb1 by (clear hyp1 hyp2; rw @covered_cequiv in ct2; repnd; rw @cover_vars_eq; insub).
  assert (cover_vars b s2) as covb2 by (clear hyp1 hyp2; rw @covered_cequiv in ct2; repnd; rw @cover_vars_eq; insub).

  dup wfct as wC; unfold subst in wC; apply lsubst_wf_term in wC.

  assert (cover_vars_upto C (csub_filter s1 [x]) [x])
    as cuC1
      by (generalize (cover_vars_upto_if_cover_vars_lsubst C s1 [(x,a)]);
          rw @fold_subst; simpl; sp).
  assert (cover_vars_upto C (csub_filter s2 [x]) [x])
    as cuC2
      by (generalize (cover_vars_upto_if_cover_vars_lsubst C s2 [(x,a)]);
          rw @fold_subst; simpl; sp).

  generalize (simple_lsubstc_subst a x C wfct s1 pC1 wa cova1 wC cuC1);
    introv e1; autodimp e1 hyp.
  rw e1; clear e1.

  generalize (simple_lsubstc_subst a x C wfct s2 pC2 wa cova2 wC cuC2);
    introv e2; autodimp e2 hyp.
  rw e2; clear e2.

  generalize (hyp2 s1 s2 eqh sim); intro h2; exrepnd; proof_irr; GC.
  lsubst_tac.
  rw @member_eq in h1.
  rw <- @member_cequiv_iff in h1.

  generalize (similarity_hyps_functionality_trans lib s1 s2 H sim eqh); intro hf2.
  generalize (similarity_sym lib H s1 s2 (eqh s2 sim) sim); intro sim2.
  apply similarity_refl in sim2.

  generalize (hyp2 s2 s2 hf2 sim2); intro h3; exrepnd; proof_irr; GC.
  lsubst_tac.
  rw @member_eq in h3.
  rw <- @member_cequiv_iff in h3.

  clear hyp2.

  spcast.

  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd; proof_irr; GC.

  generalize (simple_lsubstc_subst b x C wT1 s1 pC4 wb covb1 wC cuC1);
    introv e3; autodimp e3 hyp.
  rw e3 in hyp0; rw e3 in hyp1; clear e3.

  generalize (simple_lsubstc_subst b x C wT1 s2 pC5 wb covb2 wC cuC2);
    introv e4; autodimp e4 hyp.
  rw e4 in hyp0; clear e4.

  dands.


  (* we prove the tequality part *)
  apply tequality_respects_cequivc_left
  with (T1 := substc (lsubstc b wb s1 covb1) x
                     (lsubstc_vars C wC (csub_filter s1 [x]) [x] cuC1));
    try (complete (apply cequivc_sym; eauto with cequivc)).

  apply tequality_respects_cequivc_right
  with (T2 := substc (lsubstc b wb s2 covb2) x
                     (lsubstc_vars C wC (csub_filter s2 [x]) [x] cuC2));
    auto;
    try (complete (apply cequivc_sym; eauto with cequivc)).


  (* we prove the equality part *)
  apply cequivc_preserving_equality
  with (A := substc (lsubstc b wb s1 covb1) x
                    (lsubstc_vars C wC (csub_filter s1 [x]) [x] cuC1));
    auto;
    try (complete (apply cequivc_sym; eauto with cequivc)).
Qed.


(* begin hide *)

(* end hide *)


(**

  The following rule states that we can always replace an [a] for a
  [b] in an hypothesis of a sequent if [a] and [b] are computationally
  equivalent:
<<
  H, z : T[a], J |- C ext t

    By cequivSubstHyp

    H, z : T[b], J |- C ext t
    H, z : T[a], J |- a ~ b
>>
*)

Definition rule_cequiv_subst_hyp {o}
           (H J : @barehypotheses o)
           (x z : NVar)
           (C T a b t  : NTerm) :=
  mk_rule
    (mk_baresequent (snoc H (mk_hyp z (subst T x a)) ++ J) (mk_concl C t))
    [ mk_baresequent (snoc H (mk_hyp z (subst T x b)) ++ J) (mk_concl C t),
      mk_baresequent (snoc H (mk_hyp z (subst T x a)) ++ J) (mk_conclax (mk_cequiv a b))
    ]
    [].

Lemma rule_cequiv_subst_hyp_true {o} :
  forall lib (H J : @barehypotheses o)
         (x z : NVar)
         (C T a b t  : NTerm)
         (bc1 : disjoint (free_vars a) (bound_vars T))
         (bc2 : disjoint (free_vars b) (bound_vars T)),
    rule_true lib (rule_cequiv_subst_hyp H J x z C T a b t).
Proof.
  intros.
  unfold rule_cequiv_subst_hyp, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].

  unfold closed_extract; simpl.

  assert (covered t (nh_vars_hyps (snoc H (mk_hyp z (subst T x a)) ++ J)))
    as cov by (clear hyp1 hyp2; dwfseq; intros; discover; sp).

  exists cov.

  (* We prove some simple facts on our sequents *)
  assert (!LIn z (vars_hyps H)
          # !LIn z (vars_hyps J)
          # disjoint (vars_hyps H) (vars_hyps J)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp.

  destruct vhyps as [ nizH vhyps].
  destruct vhyps as [ nizJ disjHJ ].
  (* done with proving these simple facts *)

  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.

  destruct wf1 as [ws1 cl1].
  destruct cl1 as [ct1 ce1].
  destruct ws1 as [wh1 wc1].
  destruct wc1 as [wT1 we1].
  destruct wf2 as [ws2 cl2].
  destruct cl2 as [ct2 ce2].
  destruct ws2 as [wh2 wc2].
  destruct wc2 as [wT2 we2].
  allunfold @closed_type; allunfold @closed_extract; allsimpl.
  dup wT2 as w.
  rw <- @wf_cequiv_iff in w; destruct w as [wa wb].

  assert (wf_term T)
    as wT
      by (clear hyp1 hyp2;
          allapply @vswf_hypotheses_nil_implies;
          rw @wf_hypotheses_app in wh1; repnd;
          rw @wf_hypotheses_snoc in wh0; repnd; allsimpl;
          allrw @isprog_vars_eq; repnd;
          allrw @nt_wf_eq;
          allapply @lsubst_wf_term; auto).


  (* first we check whether or not x is in the free variables of T
   * because to know that a and b only depend on H, we first have to
   * know that x is in T.  We don't get that a and b only depend on
   * H from hyp2 because hyp2 can use the other hypotheses too. *)
  generalize (in_deq NVar deq_nvar x (free_vars T)); introv i.
  destruct i as [i | i].

  (* First, we assume that x is in the free variables of T.
   * We can now prove that a and b depend on H only. *)

  assert (covered a (vars_hyps H))
         as cvah
         by (clear hyp1 hyp2;
             allapply @vswf_hypotheses_nil_implies;
             rw @wf_hypotheses_app in wh2; repnd;
             rw @wf_hypotheses_snoc in wh0; repnd; allsimpl;
             allrw @isprog_vars_eq; repnd;
             unfold covered;
             generalize (eqvars_free_vars_disjoint T [(x,a)]);
             introv e; rw @fold_subst in e; simpl in e;
             apply subvars_eqvars with (s2 := vars_hyps H) in e; auto;
             rw subvars_prop in e;
             rw subvars_prop; introv j;
             revert e; boolvar; try (complete sp); simpl; intro e;
             apply e; rw in_app_iff; rw app_nil_r; sp).

  assert (covered b (vars_hyps H))
         as cvbh
         by (clear hyp1 hyp2;
             allapply @vswf_hypotheses_nil_implies;
             rw @wf_hypotheses_app in wh1; repnd;
             rw @wf_hypotheses_snoc in wh0; repnd; allsimpl;
             allrw @isprog_vars_eq; repnd;
             unfold covered;
             generalize (eqvars_free_vars_disjoint T [(x,b)]);
             introv e; rw @fold_subst in e; simpl in e;
             apply subvars_eqvars with (s2 := vars_hyps H) in e; auto;
             rw subvars_prop in e;
             rw subvars_prop; introv j;
             revert e; boolvar; try (complete sp); simpl; intro e;
             apply e; rw in_app_iff; rw app_nil_r; sp).

  assert (covered T (snoc (vars_hyps H) x))
         as covT
         by (clear hyp1 hyp2;
             allapply @vswf_hypotheses_nil_implies;
             rw @wf_hypotheses_app in wh1; repnd;
             rw @wf_hypotheses_snoc in wh0; repnd; allsimpl;
             allrw @isprog_vars_eq; repnd;
             unfold covered;
             generalize (eqvars_free_vars_disjoint T [(x,b)]);
             introv e; rw @fold_subst in e; simpl in e;
             apply subvars_eqvars with (s2 := vars_hyps H) in e; auto;
             rw subvars_prop in e;
             rw subvars_prop; introv j;
             revert e; boolvar; try (complete sp); simpl; intro e;
             rw in_snoc;
             destruct (deq_nvar x0 x); subst; sp;
             left; apply e; rw in_app_iff; rw app_nil_r; rw in_remove_nvars; rw in_single_iff; sp).

  assert (!LIn z (free_vars a))
         as niza
         by (intro j; unfold covered in cvah;
             rw subvars_prop in cvah; apply cvah in j; sp).

  assert (!LIn z (free_vars b))
         as nizb
         by (intro j; unfold covered in cvbh;
             rw subvars_prop in cvbh; apply cvbh in j; sp).

  assert (disjoint (free_vars a) (vars_hyps J))
         as daj
         by (introv j k; unfold covered in cvah;
             rw subvars_prop in cvah; apply cvah in j; sp;
             apply disjHJ in j; sp).

  assert (disjoint (free_vars b) (vars_hyps J))
         as dbj
         by (introv j k; unfold covered in cvbh;
             rw subvars_prop in cvbh; apply cvbh in j; sp;
             apply disjHJ in j; sp).

  assert (subvars (free_vars (subst T x a)) (vars_hyps H))
         as svaH
         by (generalize (eqvars_free_vars_disjoint T [(x,a)]); intro e;
             apply eqvars_sym in e;
             apply subvars_eqvars with (s2 := vars_hyps H) in e; auto;
             rw subvars_prop; introv; simpl;
             rw in_app_iff; rw in_remove_nvars; rw in_single_iff;
             boolvar; simpl; try (complete sp);
             rw app_nil_r; intro j; repdors; repnd;
             try (complete (unfold covered in covT; rw subvars_prop in covT;
                            apply covT in j1; rw in_snoc in j1; allrw; sp));
             try (complete (unfold covered in cvah; rw subvars_prop in cvah;
                            apply cvah in j; sp))).

  assert (subvars (free_vars (subst T x b)) (vars_hyps H))
         as svbH
         by (generalize (eqvars_free_vars_disjoint T [(x,b)]); intro e;
             apply eqvars_sym in e;
             apply subvars_eqvars with (s2 := vars_hyps H) in e; auto;
             rw subvars_prop; introv; simpl;
             rw in_app_iff; rw in_remove_nvars; rw in_single_iff;
             boolvar; simpl; try (complete sp);
             rw app_nil_r; intro j; repdors; repnd;
             try (complete (unfold covered in covT; rw subvars_prop in covT;
                            apply covT in j1; rw in_snoc in j1; allrw; sp));
             try (complete (unfold covered in cvbh; rw subvars_prop in cvbh;
                            apply cvbh in j; sp))).

  assert (subvars (free_vars T) (x :: vars_hyps H))
         as svTH
         by (rw subvars_prop in covT; rw subvars_prop; introv j;
             apply covT in j; rw in_snoc in j; simpl; sp).

  generalize (hyp1 s1 s2); clear hyp1; intro hyp1.

  autodimp hyp1 hyp.


  (* First, we prove that the hypotheses of the first sequent are functional *)
  introv sim'.
  rw @similarity_app in sim'; simpl in sim'; exrepnd; subst; allrw length_snoc; cpx.
  rw @similarity_snoc in sim'5; simpl in sim'5; exrepnd; subst; allrw length_snoc; cpx.

  rw @eq_hyps_app.
  exists (snoc s1a0 (z, t1)) s1b (snoc s2a0 (z, t2)) s2b.
  allrw length_snoc; dands; try (complete sp).

  assert (cover_vars (subst T x b) s2a0)
    as cov2
      by (apply cover_vars_change_sub with (sub1 := s1a0); sp;
          allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists s1a0 s2a0 t1 t2 w p cov2.
  dands; try (complete sp).

  assert (wf_term (subst T x a))
    as wfsa
      by (apply @lsubst_preserves_wf_term; simpl;
          unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp).

  assert (cover_vars (subst T x a) s1a0)
    as cova1 by (rw @cover_vars_eq; allapply @similarity_dom; repnd; allrw; sp).

  dup eqh as hf.

  apply hyps_functionality_init_seg
  with (s3 := s2b) in eqh; auto.
  apply @hyps_functionality_init_seg_snoc2
  with (t' := t2) (w := wfsa) (c := cova1) in eqh.
  apply eqh in sim'6; auto.

  generalize (hyp2 (snoc s1a0 (z,t1) ++ s1b) s2 hf sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_cequiv_iff in hyp1.
  spcast.

  assert (cover_vars_upto T (csub_filter s1a0 [x]) [x])
         as covT1
         by (unfold cover_vars_upto; unfold covered in covT;
             rw @dom_csub_csub_filter;
             rw subvars_app_remove_nvars_r; simpl;
             allapply @similarity_dom; repnd; allrw; sp).

  generalize (simple_lsubstc_subst b x T w s1a0 p wb c6 wT covT1);
    introv e; autodimp e hyp.
  rw e in sim'2; clear e.

  generalize (simple_lsubstc_subst a x T wfsa s1a0 cova1 wa c4 wT covT1);
    introv e; autodimp e hyp.
  rw e; clear e.

  apply cequivc_preserving_equality
  with (A := substc (lsubstc b wb s1a0 c6) x
                    (lsubstc_vars T wT (csub_filter s1a0 [x]) [x] covT1));
    auto;
    try (complete (apply cequivc_sym; eauto with cequivc)).


  (* now we prove the tequality of T[x\b] *)
  assert (wf_term (subst T x a))
         as wfsa
         by (apply @lsubst_preserves_wf_term; sp;
             unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp).

  assert (cover_vars (subst T x a) s1a0)
         as covsa1 by (rw @cover_vars_eq; allapply @similarity_dom; repnd; allrw; sp).

  generalize (eqh (snoc s2a0 (z,t1) ++ s1b)); intro eqhy.
  autodimp eqhy hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a0 (z, t1)) s1b (snoc s2a0 (z, t1)) s1b; allrw length_snoc; sp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a0 t1 t1 wfsa covsa1; sp.

  rw @similarity_app in sim; simpl in sim; exrepnd.
  apply app_split in sim0; allrw length_snoc; repnd; subst;
  try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; cpx; proof_irr.
  apply equality_refl in sim2; sp.

  apply @similarity_refl in sim'1; sp.

  rw @eq_hyps_app in eqhy; simpl in eqhy; exrepnd.
  apply app_split in eqhy0; allrw length_snoc; repnd; subst; cpx;
  try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  apply app_split in eqhy2; allrw length_snoc; repnd; subst; cpx;
  try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  rw @eq_hyps_snoc in eqhy5; simpl in eqhy5; exrepnd; cpx.

  (* now we prove the tequality from eqhy0 *)

  generalize (hyp2 (snoc s1a (z,t0) ++ s2b0)
                   (snoc s2a (z,t0) ++ s2b0)
                   eqh); clear hyp2; intro hyp2.
  (* before using hyp2 we have to prove a few things *)
  autodimp hyp2 hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a (z,t0)) s2b0 (snoc s2a (z,t0)) s2b0; allrw length_snoc; sp.
  rw @similarity_snoc; simpl.
  exists s1a s2a t0 t0 w0 p1; sp.

  rw @similarity_app in sim; simpl in sim; exrepnd.
  apply app_split in sim0; allrw length_snoc; repnd; subst;
  try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; cpx; proof_irr.
  apply equality_refl in sim2; sp.

  apply @similarity_refl in sim'1; sp.
  (* now we start using hyp2 *)
  exrepnd.
  lsubst_tac.
  rw @tequality_mkc_cequiv in hyp0.
  rw @member_eq in hyp1.
  rw <- @member_cequiv_iff in hyp1.
  appdup hyp0 hyp1.
  spcast.

  assert (cover_vars_upto T (csub_filter s1a [x]) [x])
         as cvuT1
         by (unfold cover_vars_upto; unfold covered in covT;
             rw @dom_csub_csub_filter;
             rw subvars_app_remove_nvars_r; simpl;
             allapply @similarity_dom; repnd; allrw; sp).

  assert (cover_vars_upto T (csub_filter s2a [x]) [x])
         as cvuT2
         by (unfold cover_vars_upto; unfold covered in covT;
             rw @dom_csub_csub_filter;
             rw subvars_app_remove_nvars_r; simpl;
             allapply @similarity_dom; repnd; allrw; sp).

  generalize (simple_lsubstc_subst b x T w s1a p wb c6 wT cvuT1);
    intro e; autodimp e hyp.
  rw e; clear e.

  generalize (simple_lsubstc_subst b x T w s2a cov2 wb c10 wT cvuT2);
    intro e; autodimp e hyp.
  rw e; clear e.

  generalize (simple_lsubstc_subst a x T w0 s1a p1 wa c4 wT cvuT1);
    intro e; autodimp e hyp.
  rw e in eqhy0; clear e.

  generalize (simple_lsubstc_subst a x T w0 s2a p2 wa c8 wT cvuT2);
    intro e; autodimp e hyp.
  rw e in eqhy0; clear e.

  apply tequality_respects_cequivc_left
        with (T1 := substc (lsubstc a wa s1a c4) x
                           (lsubstc_vars T wT (csub_filter s1a [x]) [x] cvuT1));
    try (complete (eauto with cequivc)).

  apply tequality_respects_cequivc_right
  with (T2 := substc (lsubstc a wa s2a c8) x
                     (lsubstc_vars T wT (csub_filter s2a [x]) [x] cvuT2));
    auto;
    try (complete (eauto with cequivc)).


  (* Now we prove the sub_eq_hyps *)

  assert (wf_term (subst T x a))
         as wfsa
         by (apply @lsubst_preserves_wf_term; sp;
             unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp).

  assert (cover_vars (subst T x a) s1a0)
         as covsa1 by (rw @cover_vars_eq; allapply @similarity_dom; repnd; allrw; sp).

  generalize (hyp2 (snoc s1a0 (z,t1) ++ s1b)
                   (snoc s2a0 (z,t1) ++ s1b)
                   eqh); clear hyp2; intro hyp2.
  (* before using hyp2 we have to prove a few things *)
  autodimp hyp2 hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a0 (z,t1)) s1b (snoc s2a0 (z,t1)) s1b; allrw length_snoc; sp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a0 t1 t1 wfsa covsa1; sp.

  rw @similarity_app in sim; simpl in sim; exrepnd.
  apply app_split in sim0; allrw length_snoc; repnd; subst;
  try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; cpx; proof_irr.
  apply equality_refl in sim2; sp.

  apply @similarity_refl in sim'1; sp.
  (* now we start using hyp2 *)
  exrepnd.
  lsubst_tac.
  rw @tequality_mkc_cequiv in hyp0.
  rw @member_eq in hyp1.
  rw <- @member_cequiv_iff in hyp1.
  appdup hyp0 hyp1.
  spcast.

  generalize (eqh (snoc s2a0 (z,t2) ++ s2b)); intro eqhy.
  autodimp eqhy hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a0 (z,t1)) s1b (snoc s2a0 (z,t2)) s2b; allrw length_snoc; sp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a0 t1 t2 wfsa covsa1; sp.

  assert (cover_vars_upto T (csub_filter s1a0 [x]) [x])
         as cvuT1
         by (unfold cover_vars_upto; unfold covered in covT;
             rw @dom_csub_csub_filter;
             rw subvars_app_remove_nvars_r; simpl;
             allapply @similarity_dom; repnd; allrw; sp).

  generalize (simple_lsubstc_subst b x T w s1a0 p wb c6 wT cvuT1);
    intro e; autodimp e hyp.
  rw e in sim'2; clear e.

  generalize (simple_lsubstc_subst a x T wfsa s1a0 covsa1 wa c4 wT cvuT1);
    intro e; autodimp e hyp.
  rw e; clear e.

  apply cequivc_preserving_equality
        with (A := substc (lsubstc b wb s1a0 c6) x
                          (lsubstc_vars T wT (csub_filter s1a0 [x]) [x] cvuT1));
    auto;
    try (complete (apply cequivc_sym; eauto with cequivc)).

  rw @eq_hyps_app in eqhy; exrepnd.
  apply app_split in eqhy0; allrw length_snoc; repnd; subst; cpx;
  try (complete (allapply @similarity_dom; repnd; allrw; sp)).
  apply app_split in eqhy2; allrw length_snoc; repnd; subst; cpx;
  try (complete (allapply @similarity_dom; repnd; allrw; sp)).


  (* We're done proving the hyps_functionality part of hyp1.
   * We now prove the similarity part of hyp1 *)
  autodimp hyp1 hyp.
  rw @similarity_app in sim; exrepnd; subst; cpx.
  rw @similarity_snoc in sim5; simpl in sim5; exrepnd; subst; cpx.

  generalize (hyp2 (snoc s1a0 (z,t1) ++ s1b)
                   (snoc s2a0 (z,t1) ++ s1b)
                   eqh); clear hyp2; intro hyp2.
  (* before using hyp2 we have to prove a few things *)
  autodimp hyp2 hyp.
  rw @similarity_app; simpl.
  exists (snoc s1a0 (z,t1)) s1b (snoc s2a0 (z,t1)) s1b; allrw length_snoc; sp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a0 t1 t1 w p; sp.

  apply equality_refl in sim2; sp.

  apply @similarity_refl in sim1; sp.
  (* now we start using hyp2 *)
  exrepnd.
  lsubst_tac.
  rw @tequality_mkc_cequiv in hyp0.
  rw @member_eq in hyp1.
  rw <- @member_cequiv_iff in hyp1.
  appdup hyp0 hyp1.
  spcast.

  assert (wf_term (subst T x b))
         as wfsb
         by (apply @lsubst_preserves_wf_term; sp;
             unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp).

  assert (cover_vars (subst T x b) s1a0)
         as covb1 by (rw @cover_vars_eq; allapply @similarity_dom; repnd; allrw; sp).

  rw @similarity_app.
  exists (snoc s1a0 (z, t1)) s1b (snoc s2a0 (z, t2)) s2b; allrw length_snoc; sp.
  rw @similarity_snoc; simpl.
  exists s1a0 s2a0 t1 t2 wfsb covb1; sp.

  assert (cover_vars_upto T (csub_filter s1a0 [x]) [x])
         as cvuT1
         by (unfold cover_vars_upto; unfold covered in covT;
             rw @dom_csub_csub_filter;
             rw subvars_app_remove_nvars_r; simpl;
             allapply @similarity_dom; repnd; allrw; sp).

  generalize (simple_lsubstc_subst b x T wfsb s1a0 covb1 wb c6 wT cvuT1);
    intro e; autodimp e hyp.
  rw e; clear e.

  generalize (simple_lsubstc_subst a x T w s1a0 p wa c4 wT cvuT1);
    intro e; autodimp e hyp.
  rw e in sim2; clear e.

  apply cequivc_preserving_equality
        with (A := substc (lsubstc a wa s1a0 c4) x
                          (lsubstc_vars T wT (csub_filter s1a0 [x]) [x] cvuT1));
    auto;
    try (complete (eauto with cequivc)).


  (* now we use hyp1 *)
  exrepnd; proof_irr; GC; sp.



  (* now we're done to the case where x is not in the free_vars of t *)
  assert (subst T x a = T)
         as e1 by (apply @lsubst_trivial3; introv j; rw in_single_iff in j; cpx).
  allrw e1; clear e1.
  assert (subst T x b = T)
         as e2 by (apply @lsubst_trivial3; introv j; rw in_single_iff in j; cpx).
  allrw e2; clear e2.

  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd; proof_irr; sp.
Qed.

(* begin hide *)

(* end hide *)