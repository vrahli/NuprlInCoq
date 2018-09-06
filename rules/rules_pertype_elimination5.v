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


Require Export sequents_tacs2.
Require Export sequents_useful.
Require Export per_props_equality.
Require Export per_props_pertype.
Require Export sequents_equality.
Require Export list. (* why *)


Lemma trivial_implies_equality_in_base {o} :
  forall lib (t : @CTerm o),
    equality lib t t mkc_base.
Proof.
  introv; apply equality_in_base_iff; spcast; eauto 3 with slow.
Qed.
Hint Resolve trivial_implies_equality_in_base : slow.




(*
  This is similar to [rule_pertype_elimination] but instead of the second
  well-formedness subgoal we have one that works for constant PERs.
*)



(* ============ PERTYPE ELIMINATION ============ *)

(**

  We can state the pertype elimination rule as follows:
<<
   H, x : t1 = t2 in pertype(R), J |- C ext e

     By pertypeElimination i z

     H, x : t1 = t2 in pertype(R), [z : R t1 t2], J |- C ext e
     H, x : Base, y : Base, z : Base, w : Base |- R x y ~ R z w
>>
 *)

Definition rule_pertype_elimination_sq {o}
           (R t1 t2 C e : NTerm)
           (x y z w : NVar)
           (H J : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x (mk_equality t1 t2 (mk_pertype R))) ++ J)
       (mk_concl C e))
    [ mk_baresequent
        (snoc (snoc H (mk_hyp x (mk_equality t1 t2 (mk_pertype R))))
              (mk_hhyp z (mk_apply2 R t1 t2))
              ++ J)
        (mk_concl C e),
      mk_baresequent
        (snoc (snoc (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base)) (mk_hyp z mk_base)) (mk_hyp w mk_base))
        (mk_conclax (mk_cequiv (mk_apply2 R (mk_var x) (mk_var y))
                               (mk_apply2 R (mk_var z) (mk_var w))))
    ]
    [sarg_var z].

Lemma rule_pertype_elimination_Sq_true {o} :
  forall lib (R t1 t2 C e : NTerm),
  forall x y z w : NVar,
  forall H J : @barehypotheses o,
    rule_true lib (rule_pertype_elimination_sq
                     R t1 t2 C e
                     x y z w
                     H J).
Proof.
  unfold rule_pertype_elimination_sq, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hypa.
  rename Hyp1 into hypb.
  destseq; allsimpl; proof_irr; GC.

  assert (covered e
                  (nh_vars_hyps
                     (snoc H (mk_hyp x (mk_equality t1 t2 (mk_pertype R))) ++ J))) as cs.
  { clear hypa hypb.
    dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp. }

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (x <> y
           # x <> z
           # x <> w
           # y <> z
           # y <> w
           # z <> w
           # !LIn x (free_vars R)
           # !LIn y (free_vars R)
           # !LIn z (free_vars R)
           # !LIn w (free_vars R)

           # !LIn x (free_vars t1)
           # !LIn y (free_vars t1)
           # !LIn z (free_vars t1)
           # !LIn w (free_vars t1)

           # !LIn x (free_vars t2)
           # !LIn y (free_vars t2)
           # !LIn z (free_vars t2)
           # !LIn w (free_vars t2)

           # !LIn x (vars_hyps H)
           # !LIn y (vars_hyps H)
           # !LIn z (vars_hyps H)
           # !LIn w (vars_hyps H)

           # !LIn z (free_vars C)
           # !LIn z (free_vars e)
           # !LIn z (hyps_free_vars J)
           # !LIn z (free_vars_hyps J)
           # !LIn z (vars_hyps J)) as vhyps.

  {
    clear hypa hypb.
    dwfseq.
    Time sp;
      try (complete (discover; allrw in_app_iff; allrw in_snoc; repndors; subst; tcsp));
      try (complete (discover; allrw in_app_iff; allrw in_snoc; repndors; subst; tcsp;
                       pose proof (subvars_hs_vars_hyps H) as q;
                       pose proof (subvars_hs_vars_hyps J) as r;
                       allrw subvars_prop; apply_in_hyp p; sp)).
  }

  destruct vhyps as [ nixr  vhyps ].
  destruct vhyps as [ niyr  vhyps ].
  destruct vhyps as [ nizr  vhyps ].
  destruct vhyps as [ niwr  vhyps ].

  destruct vhyps as [ nixt1 vhyps ].
  destruct vhyps as [ niyt1 vhyps ].
  destruct vhyps as [ nizt1 vhyps ].
  destruct vhyps as [ niwt1 vhyps ].

  destruct vhyps as [ nixt2 vhyps ].
  destruct vhyps as [ niyt2 vhyps ].
  destruct vhyps as [ nizt2 vhyps ].
  destruct vhyps as [ niwt2 vhyps ].

  destruct vhyps as [ nizc  vhyps ].
  destruct vhyps as [ nize  vhyps ].
  destruct vhyps as [ nizj1 vhyps ].
  destruct vhyps as [ nizj2 nizj3 ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  rw @similarity_app in sim; exrepnd; allsimpl; subst; cpx.
  duplicate sim5 as dup_sim_snoc.
  rw @similarity_snoc in sim5; exrepnd; allsimpl; subst; cpx.
  lsubst_tac.

  rw @equality_in_mkc_equality in sim2; repnd.
  rw @equality_in_mkc_pertype in sim0; repnd.

  vr_seq_true in hypa.
  unfold inhabited_type in sim7; exrepnd.
  pose proof (hypa ((snoc (snoc s1a0 (x, t0)) (z, t)) ++ s1b)
                   ((snoc (snoc s2a0 (x, t3)) (z, t)) ++ s2b)) as hypa.
  repeat (autodimp hypa hyp); exrepnd.

  {
    (* hyps_functionality *)
    introv sim.
    rw @similarity_app in sim; simpl in sim; exrepnd; subst; cpx.
    apply app_split in sim7; repnd; subst; repeat (rw length_snoc);
      try (complete (allrw; sp)).
    rw @similarity_snoc in sim14; simpl in sim14; exrepnd; subst; cpx.
    lsubst_tac.
    generalize (eqh (s2a1 ++ s2b0)); intro j.
    autodimp j hyp.

    rw @similarity_app; simpl.
    exists (snoc s1a0 (x, t0)) s1b0 s2a1 s2b0; repeat (rw length_snoc); sp.
    rewrite substitute_hyps_snoc_sub_weak in sim10; sp.

    rw @eq_hyps_app in j; simpl in j; exrepnd; allrw length_snoc.
    apply app_split in j0; repnd; subst; repeat (rw length_snoc);
      try (complete (allrw; sp)).
    apply app_split in j2; repnd; subst; repeat (rw length_snoc);
      try (complete (allrw; sp)).

    duplicate j5 as dup_eqhyps_snoc.
    rw @eq_hyps_snoc in j5; simpl in j5; exrepnd; subst; cpx.
    lsubst_tac.

    rw @eq_hyps_app; simpl.
    exists (snoc (snoc s1a (x, t6)) (z, t4))
           s1b
           (snoc (snoc s2a1 (x, t7)) (z, t5))
           s2b1;
      repeat (rw length_snoc); dands;
        try (complete sp);
        try (complete (apply sub_eq_hyps_snoc_weak; sp));[].

    assert (cover_vars (mk_apply2 R t1 t2) (snoc s2a1 (x, t7)))
      as cv
        by (apply cover_vars_apply2; sp;
            try (apply cover_vars_var);
            repeat (apply cover_vars_snoc_weak); sp;
            repeat (rw dom_csub_snoc); simpl; repeat (rw in_snoc); sp).

    rw @eq_hyps_snoc; simpl.
    exists (snoc s1a (x, t6)) (snoc s2a1 (x, t7)) t4 t5 w4 p0 cv;
      dands; try (complete sp).

    lsubst_tac.

    apply similarity_snoc in sim15; simpl in sim15; exrepnd; cpx.

    vr_seq_true in hypb.
    pose proof (hypb (snoc (snoc (snoc (snoc s1a0 (x,lsubstc t1 w1 s1a0 c1))
                                       (y,lsubstc t2 w2 s1a0 c2))
                                 (z,lsubstc t1 w1 s2a c6))
                           (w,lsubstc t2 w2 s2a c7))
                     (snoc (snoc (snoc (snoc s2a (x,lsubstc t1 w1 s1a0 c1))
                                       (y,lsubstc t2 w2 s1a0 c2))
                                 (z,lsubstc t1 w1 s2a c6))
                           (w,lsubstc t2 w2 s2a c7))) as hypb.
    repeat (autodimp hypb hyp); exrepnd.

    { eapply hyps_functionality_init_seg in eqh;[|eauto];[].

      pose proof (hyps_functionality_init_seg_snoc
                    lib
                    s1a0 t0 t8 H
                    (mk_hyp x (mk_equality t1 t2 (mk_pertype R)))
                    w0 p) as k.
      simpl in k.
      lsubst_tac.
      repeat (autodimp k hyp);[].

      apply hyps_functionality_snoc2; simpl; auto;[|].
      { introv equ sim'; lsubst_tac; eauto 3 with slow. }

      apply hyps_functionality_snoc2; simpl; auto;[|].
      { introv equ sim'; lsubst_tac; eauto 3 with slow. }

      apply hyps_functionality_snoc2; simpl; auto;[|].
      { introv equ sim'; lsubst_tac; eauto 3 with slow. }

      apply hyps_functionality_snoc2; simpl; auto;[].
      introv equ sim'; lsubst_tac; eauto 3 with slow. }

    { sim_snoc2; simpl; dands; auto;[|].
      { sim_snoc2; simpl; dands; auto;[|].
        { sim_snoc2; simpl; dands; auto;[|].
          { sim_snoc2; simpl; dands; auto;[].
            lsubst_tac; eauto 3 with slow. }
          lsubst_tac; eauto 3 with slow. }
        lsubst_tac; eauto 3 with slow. }
      lsubst_tac; eauto 3 with slow. }

    assert (!LIn x (dom_csub s1a0)) as nix1 by (apply similarity_dom in sim15; repnd; allrw; tcsp).
    assert (!LIn x (dom_csub s2a))  as nix2 by (apply similarity_dom in sim15; repnd; allrw; tcsp).
    assert (!LIn y (dom_csub s1a0)) as niy1 by (apply similarity_dom in sim15; repnd; allrw; tcsp).
    assert (!LIn y (dom_csub s2a))  as niy2 by (apply similarity_dom in sim15; repnd; allrw; tcsp).
    assert (!LIn z (dom_csub s1a0)) as niz1 by (apply similarity_dom in sim15; repnd; allrw; tcsp).
    assert (!LIn z (dom_csub s2a))  as niz2 by (apply similarity_dom in sim15; repnd; allrw; tcsp).
    assert (!LIn w (dom_csub s1a0)) as niw1 by (apply similarity_dom in sim15; repnd; allrw; tcsp).
    assert (!LIn w (dom_csub s2a))  as niw2 by (apply similarity_dom in sim15; repnd; allrw; tcsp).

    Time lsubst_tac.

    apply equality_in_mkc_cequiv in hypb1; repnd.
    apply tequality_mkc_cequiv in hypb0.
    clear hypb2 hypb3.
    applydup hypb0 in hypb1.
    clear hypb0.
    spcast.
    eapply tequality_respects_cequivc_right;[eauto|];[].
    repeat match goal with
           | [ H : cover_vars _ _ |- _ ] => clear H
           | [ H : wf_term _ |- _ ] => clear H
           end.
    apply tequality_mkc_equality2_sp in j0; repnd.
    clear j0.

    SearchAbout tequality mkc_pertype.

  }

  {
    (* similarity *)
    rw @similarity_app; simpl.
    exists (snoc (snoc s1a0 (x, t0)) (z, t))
           s1b
           (snoc (snoc s2a0 (x, t3)) (z, t))
           s2b; repeat (rw length_snoc); sp;
      try (complete (rewrite substitute_hyps_snoc_sub_weak; sp));[].

    assert (wf_term (mk_apply2 R t1 t2))
      as wfap by (apply wf_apply2; sp).

    assert (cover_vars (mk_apply2 R t1 t2) (snoc s1a0 (x, t0)))
      as cvap
        by (apply cover_vars_snoc_weak; rw @cover_vars_apply2; sp).

    rw @similarity_snoc; simpl.
    exists (snoc s1a0 (x, t0)) (snoc s2a0 (x, t3)) t t wfap cvap; sp;[].

    lsubst_tac.
    rw @member_eq; sp.
  }

  assert (lsubstc C wfct (snoc (snoc s1a0 (x, t0)) (z, t) ++ s1b) pC0
          = lsubstc C wfct (snoc s1a0 (x, t0) ++ s1b) pC1)
         as eq1
         by (apply lsubstc_eq_if_csubst; apply subset_free_vars_csub_snoc_app; sp).

  assert (lsubstc C wfct (snoc (snoc s2a0 (x, t3)) (z, t) ++ s2b) pC3
          = lsubstc C wfct (snoc s2a0 (x, t3) ++ s2b) pC2)
         as eq2
         by (apply lsubstc_eq_if_csubst; apply subset_free_vars_csub_snoc_app; sp).

  assert (lsubstc e wfce (snoc (snoc s1a0 (x, t0)) (z, t) ++ s1b) pt0
          = lsubstc e wfce (snoc s1a0 (x, t0) ++ s1b) pt1)
         as eq3
         by (apply lsubstc_eq_if_csubst; apply subset_free_vars_csub_snoc_app; sp).

  assert (lsubstc e wfce (snoc (snoc s2a0 (x, t3)) (z, t) ++ s2b) pt3
          = lsubstc e wfce (snoc s2a0 (x, t3) ++ s2b) pt2)
         as eq4
         by (apply lsubstc_eq_if_csubst; apply subset_free_vars_csub_snoc_app; sp).

  rw eq1 in hypa0.
  rw eq1 in hypa1.
  rw eq2 in hypa0.
  rw eq3 in hypa1.
  rw eq4 in hypa1.
  sp.
Qed.
