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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export sequents_tacs.
Require Export sequents_useful.
Require Export per_props_equality.
Require Export per_props_pertype.
Require Export sequents_equality.
Require Export list. (* why *)




(* [21] ============ PERTYPE ELIMINATION 3 ============ *)

(**

  We state yet another pertype elimination rule.  This one is similar
  to the second one presented above but does not require us to provide
  a level for [R x x]:

<<
   H, x : pertype(R), J |- C ext e

     By pertypeElimination i z

     H, x : pertype(R), [z : R x x], J |- C ext e
     H, x : pertype(R) |- (R x x) is a type
>>
 *)

Definition rule_pertype_elimination3 {o}
           (R C e : NTerm)
           (x z : NVar)
           (H J : @barehypotheses o) :=
  mk_rule
    (mk_baresequent (snoc H (mk_hyp x (mk_pertype R)) ++ J)
                   (mk_concl C e))
    [ mk_baresequent (snoc (snoc H (mk_hyp x (mk_pertype R)))
                          (mk_hhyp z (mk_apply2 R (mk_var x) (mk_var x)))
                          ++ J)
                   (mk_concl C e),
      mk_baresequent (snoc H (mk_hyp x (mk_pertype R)))
                    (mk_concl_t (mk_apply2 R (mk_var x) (mk_var x)))
    ]
    [sarg_var z].

Lemma rule_pertype_elimination3_true {o} :
  forall lib (R C e : NTerm),
  forall x z : NVar,
  forall H J : @barehypotheses o,
    rule_true lib (rule_pertype_elimination3
                 R C e
                 x z
                 H J).
Proof.
  unfold rule_pertype_elimination3, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent
                      (snoc (snoc H (mk_hyp x (mk_pertype R)))
                            (mk_hhyp z (mk_apply2 R (mk_var x) (mk_var x))) ++ J)
                      (mk_concl C e))
                   (inl eq_refl))
             (hyps (mk_baresequent
                      (snoc H (mk_hyp x (mk_pertype R)))
                      (mk_concl_t (mk_apply2 R (mk_var x) (mk_var x))))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (covered e (nh_vars_hyps (snoc H (mk_hyp x (mk_pertype R)) ++ J))) as cs.
  clear hyp1 hyp2.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars R)
           # !LIn x (vars_hyps H)
           # !LIn z (free_vars C)
           # !LIn z (free_vars e)
           # !LIn z (hyps_free_vars J)
           # !LIn z (free_vars_hyps J)
           # !LIn z (vars_hyps J)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp;
    try (complete (discover; allrw in_snoc; sp));
    try (complete (generalize (wg9 x); allrw remove_nvars_nil_l; allrw app_nil_r; sp));
    try (complete (generalize (wfh6 z); allrw in_snoc; sp));
    try (complete (generalize (cg z); allrw in_app_iff; allrw in_snoc; sp));
    try (complete (generalize (wfh z); allrw in_app_iff; allrw in_snoc; sp));
    try (complete (generalize (ce0 z); allrw @nh_vars_hyps_app; allrw @nh_vars_hyps_snoc;
                   allsimpl; allrw in_app_iff; allrw in_snoc; sp;
                   generalize (subvars_hs_vars_hyps H); intros;
                   generalize (subvars_hs_vars_hyps J); intros;
                   allrw subvars_prop; apply_in_hyp p; sp)).

  destruct vhyps as [ nixr vhyps ].
  destruct vhyps as [ nixh vhyps ].
  destruct vhyps as [ nizc vhyps ].
  destruct vhyps as [ nize vhyps ].
  destruct vhyps as [ nizj1 vhyps ].
  destruct vhyps as [ nizj2 nizj3 ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  rw @similarity_app in sim; exrepnd; allsimpl; subst; cpx.
  duplicate sim5 as dup_sim_snoc.
  rw @similarity_snoc in sim5; exrepnd; allsimpl; subst; cpx.
  lsubst_tac.

  applydup @equality_refl in sim2 as simt1.
  rw @equality_in_mkc_pertype in sim2; repnd.
  rw @equality_in_mkc_pertype in simt1; repnd.

  vr_seq_true in hyp1.
  unfold inhabited_type in sim0; exrepnd.
  unfold inhabited_type in simt0; destruct simt0 as [t' simt0].
  generalize (hyp1 ((snoc (snoc s1a0 (x, t1)) (z, t')) ++ s1b)
                   ((snoc (snoc s2a0 (x, t2)) (z, t')) ++ s2b));
    clear hyp1; intro hyp1.
  repeat (autodimp hyp1 hyp); exrepnd.

  (* hyps_functionality *)
  introv sim.
  rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
  apply app_split in sim0; repnd; subst; repeat (rw length_snoc);
  try (complete (allrw; sp)).
  rw @similarity_snoc in sim12; simpl in sim12; exrepnd; subst; cpx.
  lsubst_tac.
  generalize (eqh (s2a1 ++ s2b0)); intro j.
  autodimp j hyp.

  rw @similarity_app; simpl.
  exists (snoc s1a0 (x, t1)) s1b0 s2a1 s2b0; repeat (rw length_snoc); sp.
  rewrite substitute_hyps_snoc_sub_weak in sim8; sp.

  rw @eq_hyps_app in j; simpl in j; exrepnd; allrw length_snoc.
  apply app_split in j0; repnd; subst; repeat (rw length_snoc);
  try (complete (allrw; sp)).
  apply app_split in j2; repnd; subst; repeat (rw length_snoc);
  try (complete (allrw; sp)).

  duplicate j5 as dup_eqhyps_snoc.
  rw @eq_hyps_snoc in j5; simpl in j5; exrepnd; subst; cpx.
  lsubst_tac.

  rw @eq_hyps_app; simpl.
  exists (snoc (snoc s1a (x, t4)) (z, t0))
         s1b
         (snoc (snoc s2a1 (x, t5)) (z, t3))
         s2b1; repeat (rw length_snoc); dands; try (complete sp).

  assert (cover_vars (mk_apply2 R (mk_var x) (mk_var x)) (snoc s2a1 (x, t5)))
         as cv
         by (apply cover_vars_apply2; sp;
             try (apply cover_vars_var);
             repeat (apply cover_vars_snoc_weak); sp;
             repeat (rw @dom_csub_snoc); simpl; repeat (rw in_snoc); sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc s1a (x, t4)) (snoc s2a1 (x, t5)) t0 t3 wfct0 p0 cv;
    dands; try (complete sp).

  lsubst_tac.

  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s1a (x,t4)) (snoc s2a1 (x,t5))); clear hyp2; intro hyp2.
  repeat (autodimp hyp2 hyp); exrepnd.

  apply hyps_functionality_init_seg with (s3 := s2b) in eqh; sp.

  lsubst_tac; sp.

  apply sub_eq_hyps_snoc_weak; sp.

  (* similarity *)
  rw @similarity_app; simpl.
  exists (snoc (snoc s1a0 (x, t1)) (z, t'))
         s1b
         (snoc (snoc s2a0 (x, t2)) (z, t'))
         s2b; repeat (rw length_snoc); sp.

  assert (wf_term (mk_apply2 R (mk_var x) (mk_var x)))
         as wfap by (apply wf_apply2; sp).

  assert (cover_vars (mk_apply2 R (mk_var x) (mk_var x)) (snoc s1a0 (x, t1)))
         as cvap
         by (rw @cover_vars_apply2; sp;
             try (complete (apply cover_vars_snoc_weak; sp));
             apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; sp).

  rw @similarity_snoc; simpl.
  exists (snoc s1a0 (x, t1)) (snoc s2a0 (x, t2)) t' t' wfap cvap; sp.

  lsubst_tac.
  rw @member_eq; sp.

  rewrite substitute_hyps_snoc_sub_weak; sp.
  (* similarity proved *)

  assert (lsubstc C wfct (snoc (snoc s1a0 (x, t1)) (z, t') ++ s1b) pC0
          = lsubstc C wfct (snoc s1a0 (x, t1) ++ s1b) pC1)
         as eq1
         by (apply lsubstc_eq_if_csubst; apply subset_free_vars_csub_snoc_app; sp).

  assert (lsubstc C wfct (snoc (snoc s2a0 (x, t2)) (z, t') ++ s2b) pC3
          = lsubstc C wfct (snoc s2a0 (x, t2) ++ s2b) pC2)
         as eq2
         by (apply lsubstc_eq_if_csubst; apply subset_free_vars_csub_snoc_app; sp).

  assert (lsubstc e wfce (snoc (snoc s1a0 (x, t1)) (z, t') ++ s1b) pt0
          = lsubstc e wfce (snoc s1a0 (x, t1) ++ s1b) pt1)
         as eq3
         by (apply lsubstc_eq_if_csubst; apply subset_free_vars_csub_snoc_app; sp).

  assert (lsubstc e wfce (snoc (snoc s2a0 (x, t2)) (z, t') ++ s2b) pt3
          = lsubstc e wfce (snoc s2a0 (x, t2) ++ s2b) pt2)
         as eq4
         by (apply lsubstc_eq_if_csubst; apply subset_free_vars_csub_snoc_app; sp).

  rw eq1 in hyp0.
  rw eq1 in hyp1.
  rw eq2 in hyp0.
  rw eq3 in hyp1.
  rw eq4 in hyp1.
  sp.
Qed.

Lemma rule_pertype_elimination3_true_ex {o} :
  forall lib z R C e x H J,
    rule_true_if lib (@rule_pertype_elimination3 o
                 R C e
                 x z
                 H J).
Proof.
  intros.
  generalize (rule_pertype_elimination3_true lib R C e x z H J); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.
