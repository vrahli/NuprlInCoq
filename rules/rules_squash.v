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

  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export sequents_equality.
Require Export sequents_tacs2.
Require Export per_can.
Require Export per_props_squash.
Require Export per_props_psquash.
Require Export per_props_usquash.
Require Export subst_tacs_aeq.
Require Export lsubst_hyps.
Require Export list. (* !!WTF *)


(*
   H |- x = y in psquash(t)

     By EqualityInPSquash

     H |- x in t
     H |- y in t

 *)
Definition rule_equality_in_psquash {o}
           (H : barehypotheses)
           (t x y : @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality x y (mk_psquash t))))
    [ mk_baresequent H (mk_conclax (mk_member x t)),
      mk_baresequent H (mk_conclax (mk_member y t))
    ]
    [].

Lemma rule_equality_in_psquash_true {o} :
  forall lib (H : barehypotheses)
         (t x y : @NTerm o),
    rule_true lib (rule_equality_in_psquash H t x y).
Proof.
  unfold rule_equality_in_psquash, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.
  teq_and_eq (mk_psquash t) x y s1 s2 H.

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1; exrepnd; clear_irr.
    lsubst_tac.
    apply tequality_mkc_member in hyp0; repnd.
    apply sp_implies_tequality_mkc_psquash; auto.

  - vr_seq_true in hyp1.
    vr_seq_true in hyp2.
    pose proof (hyp1 s1 s2 hf sim) as hyp; clear hyp1; exrepnd; clear_irr.
    pose proof (hyp2 s1 s2 hf sim) as hyp; clear hyp2; exrepnd; clear_irr.
    lsubst_tac.
    allrw <- @member_member_iff.
    apply implies_equality_in_mkc_psquash; auto.

    + repeat (rw <- @fold_mkc_member in hyp2).
      apply equality_commutes3 in hyp2; auto.
      apply equality_sym in hyp2; apply equality_refl in hyp2; auto.
Qed.


(*
   H |- x = y in squash(t)

     By EqualityInSquash

     H |- T
     H |- x ~ *
     H |- y ~ *

 *)
Definition rule_equality_in_squash {o}
           (H : barehypotheses)
           (t x y e : @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality x y (mk_squash t))))
    [ mk_baresequent H (mk_concl t e),
      mk_baresequent H (mk_conclax (mk_cequiv x mk_axiom)),
      mk_baresequent H (mk_conclax (mk_cequiv y mk_axiom))
    ]
    [].

Lemma rule_equality_in_squash_true {o} :
  forall lib (H : barehypotheses)
         (t x y e : @NTerm o),
    rule_true lib (rule_equality_in_squash H t x y e).
Proof.
  unfold rule_equality_in_squash, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.
  teq_and_eq (mk_squash t) x y s1 s2 H.

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1; exrepnd; clear_irr.
    lsubst_tac.
    apply tequality_mkc_squash; auto.

  - vr_seq_true in hyp1.
    vr_seq_true in hyp2.
    vr_seq_true in hyp3.
    pose proof (hyp1 s1 s2 hf sim) as hyp; clear hyp1; exrepnd; clear_irr.
    pose proof (hyp2 s1 s2 hf sim) as hyp; clear hyp2; exrepnd; clear_irr.
    pose proof (hyp3 s1 s2 hf sim) as hyp; clear hyp3; exrepnd; clear_irr.
    lsubst_tac.
    allrw <- @member_cequiv_iff.
    allrw @tequality_mkc_cequiv.
    applydup hyp3 in hyp5; clear hyp3.
    applydup hyp2 in hyp4; clear hyp2.
    spcast.

    apply cequivc_sym in hyp3; apply cequivc_axiom_implies in hyp3.
    apply cequivc_sym in hyp4; apply cequivc_axiom_implies in hyp4.
    apply cequivc_sym in hyp5; apply cequivc_axiom_implies in hyp5.
    apply cequivc_sym in hyp6; apply cequivc_axiom_implies in hyp6.
    apply equality_in_mkc_squash; dands; spcast; auto.

    apply equality_refl in hyp1.
    eexists; eauto.
Qed.


(*
   H |- psquash(t)

     By InhabitedPSquash

     H |- t

 *)
Definition rule_inhabited_psquash {o}
           (H : barehypotheses)
           (t e : @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_psquash t) e))
    [ mk_baresequent H (mk_concl t e)
    ]
    [].

Lemma rule_inhabited_psquash_true {o} :
  forall lib (H : barehypotheses)
         (t e : @NTerm o),
    rule_true lib (rule_inhabited_psquash H t e).
Proof.
  unfold rule_inhabited_psquash, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  exists ce.

  vr_seq_true.
  lsubst_tac.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1; exrepnd; clear_irr.
  dands.

  - apply sp_implies_tequality_mkc_psquash; auto.

  - apply implies_equality_in_mkc_psquash; auto.
    + apply equality_refl in hyp1; auto.
    + apply equality_sym in hyp1; apply equality_refl in hyp1; auto.
Qed.


(*
   H |- squash(t)

     By InhabitedSquash

     H |- t

 *)
Definition rule_inhabited_squash {o}
           (H : barehypotheses)
           (t e : @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_squash t)))
    [ mk_baresequent H (mk_concl t e)
    ]
    [].

Lemma rule_inhabited_squash_true {o} :
  forall lib (H : barehypotheses)
         (t e : @NTerm o),
    rule_true lib (rule_inhabited_squash H t e).
Proof.
  unfold rule_inhabited_squash, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  lsubst_tac.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1; exrepnd; clear_irr.
  dands.

  - apply tequality_mkc_squash; auto.

  - apply equality_in_mkc_squash; dands; spcast;
    try (apply computes_to_valc_refl; eauto 3 with slow).
    apply equality_refl in hyp1; auto.
    eexists; eauto.
Qed.


(* !!MOVE *)
Hint Rewrite @vars_hyps_substitute_hyps : slow.

(*
   H, x : squash(t), J |- C

     By SquashElim y

     H, x : squash(t), J, [y : t] |- C

 *)
Definition rule_squash_elim {o}
           (H J : barehypotheses)
           (t C e : @NTerm o)
           (x y : NVar)
  :=
    mk_rule
      (mk_baresequent (snoc H (mk_hyp x (mk_squash t)) ++ J) (mk_concl C e))
      [ mk_baresequent (snoc (snoc H (mk_hyp x (mk_squash t)) ++ J) (mk_hhyp y t)) (mk_concl C e)
      ]
      [].

Lemma rule_squash_elim_true {o} :
  forall lib (H J : barehypotheses)
         (t C e : @NTerm o) x y,
    rule_true lib (rule_squash_elim H J t C e x y).
Proof.
  unfold rule_squash_elim, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  assert (covered e (nh_vars_hyps (snoc H (mk_hyp x (mk_squash t)) ++ J))) as cov.
  { clear hyp1.
    rw @nh_vars_hyps_snoc in ce; allsimpl.
    allrw @nh_vars_hyps_app.
    allrw @nh_vars_hyps_snoc; allsimpl; auto. }
  exists cov.

  assert (x <> y
          # !LIn x (vars_hyps H)
          # !LIn y (vars_hyps H)
          # !LIn x (vars_hyps J)
          # !LIn y (vars_hyps J)
          # subset (free_vars t) (vars_hyps H)
          # disjoint (vars_hyps H) (vars_hyps J)
          # !LIn y (free_vars C)
          # !LIn y (free_vars e)
          # !LIn x (free_vars t)
          # !LIn y (free_vars t)) as vhyps.

  {
    clear hyp1.
    dwfseq.
    sp;
      try (complete (pose proof (cg y) as xx; autodimp xx hyp;
                     rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp));
      try (complete (pose proof (ce y) as xx; autodimp xx hyp;
                     rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp;
                     apply subset_hs_vars_hyps in xx; tcsp)).
  }

  destruct vhyps as [ nxy vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nyH vhyps ].
  destruct vhyps as [ nxJ vhyps ].
  destruct vhyps as [ nyJ vhyps ].
  destruct vhyps as [ stH vhyps ].
  destruct vhyps as [ dHJ vhyps ].
  destruct vhyps as [ nyC vhyps ].
  destruct vhyps as [ nye vhyps ].
  destruct vhyps as [ nxt nyt ].

  vr_seq_true.
  vr_seq_true in hyp1.

  dup sim as simbackup.

  apply similarity_app in sim; exrepnd; subst.
  allrw length_snoc.
  apply similarity_snoc in sim5; exrepnd; subst.
  allsimpl.
  allrw length_snoc; cpx.
  lsubst_tac.
  allrw @equality_in_mkc_squash; repnd; spcast.
  unfold inhabited_type in sim2; exrepnd.

  assert (disjoint (free_vars t) (dom_csub s1b)) as disjts1b.
  { introv i j.
    apply stH in i.
    apply dHJ in i.
    apply similarity_dom in sim1; repnd.
    autorewrite with slow in *.
    rw sim2 in j; tcsp. }

  pose proof (hyp1
                (snoc (snoc s1a0 (x,t1) ++ s1b) (y,t0))
                (snoc (snoc s2a0 (x,t2) ++ s2b) (y,t0))) as hyp;
    clear hyp1; exrepnd; clear_irr.
  repeat (autodimp hyp hh).

  { apply hyps_functionality_snoc2; simpl; auto.

    introv equ sim'.
    lsubst_tac.

    eapply hyps_functionality_init_seg in eqh;eauto.

    apply similarity_app in sim'; exrepnd; subst.
    allrw length_snoc.
    apply app_split in sim'0; repnd; subst; repeat (rw length_snoc);
    try (complete (allrw; sp)).
    apply similarity_snoc in sim'5; exrepnd; subst; allsimpl; cpx; ginv.

    assert (disjoint (free_vars t) (dom_csub s2b0)) as disjts2b0.
    { introv i j.
      apply stH in i.
      apply dHJ in i.
      apply similarity_dom in sim'1; repnd.
      autorewrite with slow in *.
      rw sim'1 in j; tcsp. }
    lsubst_tac.

    pose proof (eqh (snoc s2a1 (x,mkc_axiom))) as h.

    autodimp h hyp.
    { sim_snoc2; dands; auto.
      lsubst_tac.
      apply equality_in_mkc_squash; dands; spcast; auto;
      try (apply computes_to_valc_refl; eauto 3 with slow).
      exists t0.
      apply equality_refl in equ; auto. }

    apply eq_hyps_snoc in h; exrepnd; allsimpl; cpx; ginv.
    lsubst_tac.
    rw @tequality_mkc_squash in h0; auto.
  }

  { sim_snoc2; dands; lsubst_tac; auto.
    apply cover_vars_app_weak; apply cover_vars_snoc_weak; auto.
  }

  exrepnd.
  lsubst_tac.
  dands; auto.
Qed.


(*
   H |- x ~ *

     By MemberSquash y

     H |- x in squash(t)

 *)
Definition rule_member_squash {o}
           (H : barehypotheses)
           (t x : @NTerm o)
  :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_cequiv x mk_axiom)))
      [ mk_baresequent H (mk_conclax (mk_member x (mk_squash t)))
      ]
      [].

Lemma rule_member_squash_true {o} :
  forall lib (H : barehypotheses)
         (t x : @NTerm o),
    rule_true lib (rule_member_squash H t x).
Proof.
  unfold rule_member_squash, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  vr_seq_true in hyp1.

  pose proof (hyp1 s1 s2 eqh sim) as h; clear hyp1; exrepnd.
  lsubst_tac.
  allrw <- @member_cequiv_iff.
  allrw <- @member_member_iff.
  unfold member in h1.
  rw @equality_in_mkc_squash in h1; repnd; spcast.
  apply tequality_mkc_member in h0; repnd.
  rw @tequality_mkc_cequiv.
  apply computes_to_valc_implies_cequivc in h2.
  dands; split; try (intro xx);
  apply equality_in_mkc_squash in h0; repnd; spcast;
  try (apply computes_to_valc_implies_cequivc; auto);
  try (apply equality_in_mkc_squash; sp; spcast; auto).
 
Qed.


Lemma hyps_functionality_psquash_implies {o} :
  forall lib (s1 s2 : @CSub o) T (wT : wf_term T) (cT : cover_vars T s1) x t H J,
    length H = length s1
    -> (forall s3 (cT' : cover_vars T s3),
           similarity lib s1 s3 H
           -> tequality lib (lsubstc T wT s1 cT) (lsubstc T wT s3 cT'))
    -> hyps_functionality lib (snoc s1 (x, t) ++ s2) (snoc H (mk_hyp x (mk_psquash T)) ++ J)
    -> hyps_functionality lib (snoc s1 (x, t) ++ s2) (snoc H (mk_hyp x T) ++ J).
Proof.
  introv len imp hf sim.

  apply similarity_app in sim; exrepnd; subst.
  allrw length_snoc.
  apply app_split in sim0; repnd; subst; repeat (rw length_snoc); try (complete (allrw; sp)).
  allrw length_snoc; cpx.
  apply similarity_snoc in sim5; exrepnd; subst; allsimpl.
  allrw length_snoc; cpx.
  pose proof (hf (snoc s2a0 (x,t2) ++ s2b)) as xx; clear hf.
  autodimp xx hyp.

  - apply similarity_app.
    eexists; eexists; eexists; eexists; dands; eauto;
    allrw length_snoc; auto.

    sim_snoc2; eauto 3 with slow;
    try (apply wf_mk_psquash; auto);
    try (apply cover_vars_psquash; auto);
    dands; auto.

    lsubst_tac.
    apply implies_equality_in_mkc_psquash.

    + apply equality_refl in sim2; auto.
    + apply equality_sym in sim2; apply equality_refl in sim2; auto.

  - apply eq_hyps_app in xx; exrepnd.
    allrw length_snoc.

    apply app_split in xx0; repnd; subst;
    repeat (rw length_snoc); try (rw sim3; rw xx3; auto).

    apply app_split in xx2; repnd; subst;
    repeat (rw length_snoc); try (rw sim4; rw xx4; auto).

    apply eq_hyps_snoc in xx5; exrepnd; allsimpl; cpx.

    apply eq_hyps_app.
    eexists; eexists; eexists; eexists; dands; eauto;
    allrw length_snoc; auto.
    apply eq_hyps_snoc; simpl.

    assert (cover_vars T s2a) as c2.
    { clear xx0; rw @cover_vars_psquash in p2; auto. }

    exists s1a0 s2a t0 t3 w p c2; dands; auto.
    proof_irr.
    apply imp; auto.
Qed.


(*
   H, x : psquash(t), J |- a = b in C

     By PSquashElim i y z

     H, x : t, J, y : t |- a = b[x\y] in C
     H, x : psquash(t), J |- C in U{i}  // Required to prove that C is functional
     H |- t in U{i}                     // Required because psquash(t) is extensional

 *)
Definition rule_psquash_elim {o}
           (H J : barehypotheses)
           (t a b C : @NTerm o)
           (x y : NVar)
           (i : nat)
  :=
    mk_rule
      (mk_baresequent (snoc H (mk_hyp x (mk_psquash t)) ++ J) (mk_conclax (mk_equality a b C)))
      [ mk_baresequent
          (snoc (snoc H (mk_hyp x t) ++ J) (mk_hyp y t))
          (mk_conclax (mk_equality a (subst b x (mk_var y)) C)),
        mk_baresequent (snoc H (mk_hyp x (mk_psquash t)) ++ J) (mk_conclax (mk_member C (mk_uni i))),
        mk_baresequent H (mk_conclax (mk_member t (mk_uni i)))
      ]
      [].

Lemma rule_psquash_elim_true {o} :
  forall lib (H J : barehypotheses)
         (t a b C : @NTerm o) x y i,
    rule_true lib (rule_psquash_elim H J t a b C x y i).
Proof.
  unfold rule_psquash_elim, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps (snoc H (mk_hyp x (mk_psquash t)) ++ J))).

  assert (x <> y
          # !LIn x (vars_hyps H)
          # !LIn y (vars_hyps H)
          # !LIn x (vars_hyps J)
          # !LIn y (vars_hyps J)
          # subset (free_vars t) (vars_hyps H)
          # disjoint (vars_hyps H) (vars_hyps J)
          # !LIn y (free_vars a)
          # !LIn y (free_vars b)
          # !LIn y (free_vars C)
          # !LIn x (free_vars t)
          # !LIn y (free_vars t)) as vhyps.

  {
    clear hyp1.
    dwfseq.
    sp;
      try (complete (pose proof (cg y) as xx; autodimp xx hyp;
                     rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp));
      try (complete (pose proof (cg0 y) as xx; autodimp xx hyp;
                     rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp));
      try (complete (pose proof (cg1 y) as xx; autodimp xx hyp;
                     rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp)).
  }

  destruct vhyps as [ nxy vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nyH vhyps ].
  destruct vhyps as [ nxJ vhyps ].
  destruct vhyps as [ nyJ vhyps ].
  destruct vhyps as [ stH vhyps ].
  destruct vhyps as [ dHJ vhyps ].
  destruct vhyps as [ nya vhyps ].
  destruct vhyps as [ nyb vhyps ].
  destruct vhyps as [ nyC vhyps ].
  destruct vhyps as [ nxt nyt ].

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.
  teq_and_eq C a b s1 s2 (snoc H (mk_hyp x (mk_psquash t)) ++ J).

  - vr_seq_true in hyp2.
    pose proof (hyp2 s1 s2 eqh sim) as h; clear hyp2.
    exrepnd; lsubst_tac.
    apply tequality_in_uni_implies_tequality in h0; auto.
    rw <- @member_member_iff in h1.
    auto.

  - dup sim as simbackup.

    apply similarity_app in sim; exrepnd; subst.
    allrw length_snoc.
    apply similarity_snoc in sim5; exrepnd; subst.
    allsimpl.
    allrw length_snoc; cpx.
    lsubst_tac.
    allrw @equality_in_mkc_psquash; repnd.

    assert (disjoint (free_vars t) (dom_csub s1b)) as disjts1b.
    { introv k j.
      apply stH in k.
      apply dHJ in k.
      apply similarity_dom in sim1; repnd.
      autorewrite with slow in *.
      rw sim5 in j; tcsp. }

    vr_seq_true in hyp1.
    pose proof (hyp1
                  (snoc (snoc s1a0 (x,t1) ++ s1b) (y,t2))
                  (snoc (snoc s2a0 (x,t1) ++ s2b) (y,t2))) as hyp;
      clear hyp1; exrepnd; clear_irr.
    repeat (autodimp hyp hh).

    { apply hyps_functionality_snoc2; simpl; auto;[|].

      - introv equ sim'.
        lsubst_tac.
        apply similarity_app in sim'; exrepnd; subst.
        allrw length_snoc.
        apply app_split in sim'0; repnd; subst; repeat (rw length_snoc);
        try (complete (allrw; sp)).
        allrw length_snoc; cpx.
        apply similarity_snoc in sim'5; exrepnd; subst; allsimpl.
        allrw length_snoc; cpx.

        assert (disjoint (free_vars t) (dom_csub s2b0)) as disjts2b0.
        { introv k j.
          apply stH in k.
          apply dHJ in k.
          apply similarity_dom in sim'1; repnd.
          autorewrite with slow in *.
          rw sim'1 in j; tcsp. }

        lsubst_tac.

        eapply hyps_functionality_init_seg in hf;eauto.
        pose proof (hyps_functionality_init_seg_snoc2
                      lib s1a t0 t2 H x (mk_psquash t) w p hf) as h.
        autodimp h hh.
        { lsubst_tac.
          apply implies_equality_in_mkc_psquash; auto. }

        vr_seq_true in hyp3.
        pose proof (hyp3 s1a s2a1 h sim'5) as hh; clear hyp2; exrepnd.
        lsubst_tac.
        apply tequality_in_uni_implies_tequality in hh0; auto.
        rw @equality_in_member in hh1; sp.
        
      - apply (hyps_functionality_psquash_implies lib s1a0 s1b t w0 c1); auto.

        introv sim'.

        eapply hyps_functionality_init_seg in hf;eauto.
        pose proof (hyps_functionality_init_seg_snoc2
                      lib s1a0 t1 t2 H x (mk_psquash t) w p hf) as h.
        autodimp h hh.
        { lsubst_tac.
          apply implies_equality_in_mkc_psquash; auto. }

        vr_seq_true in hyp3.
        pose proof (hyp3 s1a0 s3 h sim') as hh; clear hyp2; exrepnd.
        lsubst_tac.
        apply tequality_in_uni_implies_tequality in hh0; auto.
         rw @equality_in_member in hh1; sp.
    }

    { sim_snoc2.

      { apply cover_vars_app_weak.
        apply cover_vars_snoc_weak; auto. }

      dands; lsubst_tac; auto;[].

      apply similarity_app.
      eexists; eexists; eexists; eexists; dands; eauto;
      allrw length_snoc; auto.

      sim_snoc2; dands; proof_irr; auto.
    }

    exrepnd.
    lsubst_tac.
    allrw <- @member_equality_iff.
    apply equality_commutes4 in hyp0; auto.
    eapply equality_respects_alphaeqc_right;[|exact hyp0].
    clear hyp0 hyp1.

    assert (cover_vars (mk_var y) (snoc (snoc s1a0 (x, t1) ++ s1b) (y, t2))) as covy1.
    { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

    assert (cover_vars (mk_var y) (snoc (snoc s2a0 (x, t1) ++ s2b) (y, t2))) as covy2.
    { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

    assert (!LIn y (dom_csub (snoc s2a0 (x, t1) ++ s2b))) as niy.
    { rw @dom_csub_app; rw @dom_csub_snoc; simpl; rw in_app_iff; rw in_snoc.
      apply similarity_dom in sim6; repnd; rw sim6.
      apply similarity_dom in sim1; repnd; rw sim1.
      autorewrite with slow.
      intro k; repndors; tcsp. }

    lsubstc_subst_aeq.
    substc_lsubstc_vars3.
    revert c6.
    lsubst_tac.
    introv.
    repeat (lsubstc_snoc2;[]).

    unfold alphaeqc; simpl.
    apply alpha_eq_lsubst_if_ext_eq; auto.
    introv k.
    simpl.
    repeat (rw <- @csub2sub_app).
    repeat (rw @csub2sub_snoc).
    repeat (rw @sub_find_app).
    repeat (rw @sub_find_snoc).
    boolvar; eauto 3 with slow.

    rw @sub_find_none_if; eauto 3 with slow.
    rw @dom_csub_eq.
    apply similarity_dom in sim6; repnd; rw sim6; auto.
Qed.


Hint Resolve tequality_mkc_uni : slow.


(*
   H |- psquash(t1) = psquash(t2) ∈ U(i)

     By EqualPSquash

     H |- t1 in U(i)
     H |- t2 in U(i)
     H , t : Base, z : t ∈ t1 |- t ∈ t2
     H , t : Base, z : t ∈ t2 |- t ∈ t1

 *)
Definition rule_equal_psquash {o}
           (H : barehypotheses)
           (i : nat)
           (t1 t2 : @NTerm o)
           (x z : NVar)
  :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_psquash t1) (mk_psquash t2) (mk_uni i))))
    [ mk_baresequent H (mk_conclax (mk_member t1 (mk_uni i))),
      mk_baresequent H (mk_conclax (mk_member t2 (mk_uni i))),
      mk_baresequent
        (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp z (mk_member (mk_var x) t1)))
        (mk_conclax (mk_member (mk_var x) t2)),
      mk_baresequent
        (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp z (mk_member (mk_var x) t2)))
        (mk_conclax (mk_member (mk_var x) t1))
    ]
    [].

Lemma rule_equal_psquash_true {o} :
  forall lib (H : barehypotheses) (i : nat)
         (t1 t2 : @NTerm o) (x z : NVar),
    rule_true lib (rule_equal_psquash H i t1 t2 x z).
Proof.
  unfold rule_equal_psquash, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  assert (x <> z
          # !LIn x (vars_hyps H)
          # !LIn z (vars_hyps H)
          # !LIn x (free_vars t1)
          # !LIn z (free_vars t1)
          # !LIn x (free_vars t2)
          # !LIn z (free_vars t2)) as vhyps.

  {
    clear hyp1 hyp2 hyp3 hyp4.
    dwfseq.
    sp.
  }

  destruct vhyps as [ nxz  vhyps ].
  destruct vhyps as [ nxH  vhyps ].
  destruct vhyps as [ nzH  vhyps ].
  destruct vhyps as [ nxt1 vhyps ].
  destruct vhyps as [ nzt1 vhyps ].
  destruct vhyps as [ nxt2 nzt2 ].

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.
  teq_and_eq (@mk_uni o i) (mk_psquash t1) (mk_psquash t2) s1 s2 H; eauto 3 with slow;[].

  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 hf sim) as hypa; exrepnd; clear_irr.
  pose proof (hyp2 s1 s2 hf sim) as hypb; exrepnd; clear_irr.

  hide_hyp hyp1.
  hide_hyp hyp2.

  lsubst_tac.
  allrw <- @member_member_iff.
  apply tequality_mkc_member_implies_sp in hypa0; auto;[].
  apply tequality_mkc_member_implies_sp in hypb0; auto;[].

  apply equality_mkc_psquash_in_uni; dands; eauto 3 with slow;[|].

  { apply equality_sym in hypb0; apply equality_refl in hypb0; auto. }

  introv.
  split; intro h.

  {
    vr_seq_true in hyp3.
    pose proof (hyp3 (snoc (snoc s1 (x,t)) (z,mkc_axiom))
                     (snoc (snoc s2 (x,t)) (z,mkc_axiom))) as hyp3.
    repeat (autodimp hyp3 hyp).

    { apply hyps_functionality_snoc2; simpl; auto;[|].

      { introv equ sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; cpx.
        lsubst_tac.
        apply equality_in_base in sim'1; spcast.

        pose proof (hyp1 s1a s2a) as hypc.
        repeat (autodimp hypc hyp);[].
        exrepnd.
        lsubst_tac.
        allrw <- @member_member_iff.
        apply tequality_mkc_member_implies_sp in hypc0; auto;[].
        apply equality_in_uni in hypc0.
        apply tequality_mkc_member_if_cequivc; dands; auto.
      }

      apply hyps_functionality_snoc2; simpl; auto;[].
      introv equ sim'.
      lsubst_tac; eauto 3 with slow. }

    { assert (cover_vars (mk_member (mk_var x) t1) (snoc s1 (x, t))) as cov2.
      { apply cover_vars_member; dands; eauto 3 with slow.
        - apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp.
        - apply cover_vars_snoc_weak; auto. }
      sim_snoc2;[].
      dands; auto;[|].

      { sim_snoc2;[].
        dands; auto;[].
        lsubst_tac; eauto 3 with slow.
        apply equality_in_base_iff; spcast; eauto 3 with slow. }

      lsubst_tac.
      rw <- @member_member_iff; auto. }

    exrepnd.
    lsubst_tac.
    allrw <- @member_member_iff.
    apply tequality_mkc_member in hyp0; repnd.
    apply hyp6; auto.
  }

  {
    vr_seq_true in hyp4.
    pose proof (hyp4 (snoc (snoc s1 (x,t)) (z,mkc_axiom))
                     (snoc (snoc s2 (x,t)) (z,mkc_axiom))) as hyp4.
    repeat (autodimp hyp4 hyp).

    { apply hyps_functionality_snoc2; simpl; auto;[|].

      { introv equ sim'.
        apply similarity_snoc in sim'; simpl in sim'.
        exrepnd; subst; cpx.
        lsubst_tac.
        apply equality_in_base in sim'1; spcast.

        pose proof (hyp2 s1a s2a) as hypc.
        repeat (autodimp hypc hyp);[].
        exrepnd.
        lsubst_tac.
        allrw <- @member_member_iff.
        apply tequality_mkc_member_implies_sp in hypc0; auto;[].
        apply equality_in_uni in hypc0.
        apply tequality_mkc_member_if_cequivc; dands; auto.
      }

      apply hyps_functionality_snoc2; simpl; auto;[].
      introv equ sim'.
      lsubst_tac; eauto 3 with slow. }

    { assert (cover_vars (mk_member (mk_var x) t2) (snoc s1 (x, t))) as cov2.
      { apply cover_vars_member; dands; eauto 3 with slow.
        - apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp.
        - apply cover_vars_snoc_weak; auto. }
      sim_snoc2;[].
      dands; auto;[|].

      { sim_snoc2;[].
        dands; auto;[].
        lsubst_tac; eauto 3 with slow.
        apply equality_in_base_iff; spcast; eauto 3 with slow. }

      lsubst_tac.
      rw <- @member_member_iff; auto.
      apply equality_in_uni in hypb0.
      eapply tequality_preserving_equality;[exact h|].
      apply tequality_sym;auto. }

    exrepnd.
    lsubst_tac.
    allrw <- @member_member_iff; auto.
  }
Qed.



(*
   H |- usquash(t1) = usquash(t2) ∈ U(i)

     By EqualUSquash

     H |- t1 in U(i)
     H |- t2 in U(i)
     H, z : t1 |- t2
     H, z : t2 |- t1

 *)
Definition rule_equal_usquash {o}
           (H : barehypotheses)
           (i : nat)
           (t1 t2 : @NTerm o)
           (z : NVar)
           (e1 e2 : NTerm)
  :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_usquash t1) (mk_usquash t2) (mk_uni i))))
    [ mk_baresequent H (mk_conclax (mk_member t1 (mk_uni i))),
      mk_baresequent H (mk_conclax (mk_member t2 (mk_uni i))),
      mk_baresequent (snoc H (mk_hyp z t1)) (mk_concl t2 e2),
      mk_baresequent (snoc H (mk_hyp z t2)) (mk_concl t1 e1)
    ]
    [].

Lemma rule_equal_usquash_true {o} :
  forall lib (H : barehypotheses) (i : nat)
         (t1 t2 : @NTerm o) (z : NVar) (e1 e2 : NTerm),
    rule_true lib (rule_equal_usquash H i t1 t2 z e1 e2).
Proof.
  unfold rule_equal_usquash, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  assert (!LIn z (vars_hyps H)
          # !LIn z (free_vars t1)
          # !LIn z (free_vars t2)) as vhyps.

  {
    clear hyp1 hyp2 hyp3 hyp4.
    dwfseq.
    sp.
  }

  destruct vhyps as [ nzH  vhyps ].
  destruct vhyps as [ nzt1 nzt2  ].

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.
  teq_and_eq (@mk_uni o i) (mk_usquash t1) (mk_usquash t2) s1 s2 H; eauto 3 with slow;[].

  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 hf sim) as hypa; exrepnd; clear_irr.
  pose proof (hyp2 s1 s2 hf sim) as hypb; exrepnd; clear_irr.

  hide_hyp hyp1.
  hide_hyp hyp2.

  lsubst_tac.
  allrw <- @member_member_iff.
  apply tequality_mkc_member_implies_sp in hypa0; auto;[].
  apply tequality_mkc_member_implies_sp in hypb0; auto;[].

  apply equality_mkc_usquash_in_uni; dands; eauto 3 with slow;[|].

  { apply equality_sym in hypb0; apply equality_refl in hypb0; auto. }

  introv.
  split; intro h.

  {
    unfold inhabited_type in h; exrepnd.
    vr_seq_true in hyp3.
    pose proof (hyp3 (snoc s1 (z,t)) (snoc s2 (z,t))) as hyp3.
    repeat (autodimp hyp3 hyp).

    { apply hyps_functionality_snoc2; simpl; auto;[].

      introv equ sim'.

      pose proof (hyp1 s1 s') as hypc.
      repeat (autodimp hypc hyp);[].
      exrepnd.
      lsubst_tac.
      allrw <- @member_member_iff.
      apply tequality_mkc_member_implies_sp in hypc0; auto;[].
      apply equality_in_uni in hypc0; auto. }

    { sim_snoc2;[].
      dands; auto;[].
      proof_irr; auto. }

    exrepnd.
    lsubst_tac.
    apply equality_refl in hyp3.
    eapply inhabited_type_tequality;[eauto|]; auto.
    eexists; eauto.
  }

  {
    unfold inhabited_type in h; exrepnd.
    vr_seq_true in hyp4.
    pose proof (hyp4 (snoc s1 (z,t)) (snoc s2 (z,t))) as hyp4.
    repeat (autodimp hyp4 hyp).

    { apply hyps_functionality_snoc2; simpl; auto;[].

      introv equ sim'.

      pose proof (hyp2 s1 s') as hypc.
      repeat (autodimp hypc hyp);[].
      exrepnd.
      lsubst_tac.
      allrw <- @member_member_iff.
      apply tequality_mkc_member_implies_sp in hypc0; auto;[].
      apply equality_in_uni in hypc0; auto. }

    { sim_snoc2;[].
      dands; auto;[].
      proof_irr; auto.
      apply equality_in_uni in hypb0.
      eapply tequality_preserving_equality;[|apply tequality_sym;eauto];auto. }

    exrepnd.
    lsubst_tac.
    apply equality_refl in hyp4.
    eexists; eauto.
  }
Qed.


(* MOVE *)
Lemma inhabited_type_implies_type {o} :
  forall lib (t : @CTerm o),
    inhabited_type lib t -> type lib t.
Proof.
  introv inh; unfold inhabited_type in inh; exrepnd.
  apply inhabited_implies_tequality in inh0; auto.
Qed.
Hint Resolve inhabited_type_implies_type : slow.

Hint Resolve inhabited_type_if_equality : slow.

Lemma hyps_functionality_usquash_implies {o} :
  forall lib (s1 s2 : @CSub o) T (wT : wf_term T) (cT : cover_vars T s1) x t H J,
    length H = length s1
    -> (forall s3 (cT' : cover_vars T s3),
           similarity lib s1 s3 H
           -> tequality lib (lsubstc T wT s1 cT) (lsubstc T wT s3 cT'))
    -> hyps_functionality lib (snoc s1 (x, t) ++ s2) (snoc H (mk_hyp x (mk_usquash T)) ++ J)
    -> hyps_functionality lib (snoc s1 (x, t) ++ s2) (snoc H (mk_hyp x T) ++ J).
Proof.
  introv len imp hf sim.

  apply similarity_app in sim; exrepnd; subst.
  allrw length_snoc.
  apply app_split in sim0; repnd; subst; repeat (rw length_snoc); try (complete (allrw; sp)).
  allrw length_snoc; cpx.
  apply similarity_snoc in sim5; exrepnd; subst; allsimpl.
  allrw length_snoc; cpx.
  pose proof (hf (snoc s2a0 (x,t2) ++ s2b)) as xx; clear hf.
  autodimp xx hyp.

  - apply similarity_app.
    eexists; eexists; eexists; eexists; dands; eauto;
    allrw length_snoc; auto.

    sim_snoc2; eauto 3 with slow;
    try (apply wf_mk_usquash; auto);
    try (apply cover_vars_usquash; auto);
    dands; auto.

    lsubst_tac.
    apply implies_equality_in_mkc_usquash; eauto 3 with slow.

  - apply eq_hyps_app in xx; exrepnd.
    allrw length_snoc.

    apply app_split in xx0; repnd; subst;
    repeat (rw length_snoc); try (rw sim3; rw xx3; auto).

    apply app_split in xx2; repnd; subst;
    repeat (rw length_snoc); try (rw sim4; rw xx4; auto).

    apply eq_hyps_snoc in xx5; exrepnd; allsimpl; cpx.

    apply eq_hyps_app.
    eexists; eexists; eexists; eexists; dands; eauto;
    allrw length_snoc; auto.
    apply eq_hyps_snoc; simpl.

    assert (cover_vars T s2a) as c2.
    { clear xx0; rw @cover_vars_usquash in p2; auto. }

    exists s1a0 s2a t0 t3 w p c2; dands; auto.
    proof_irr.
    apply imp; auto.
Qed.


(*
   H, x : usquash(t), J |- C

     By USquashElim i y z

     H, x : usquash(t), J, [y : t] |- C

 *)
Definition rule_usquash_elim {o}
           (H J : barehypotheses)
           (t C e : @NTerm o)
           (x y : NVar)
  :=
    mk_rule
      (mk_baresequent (snoc H (mk_hyp x (mk_usquash t)) ++ J) (mk_concl C e))
      [ mk_baresequent (snoc (snoc H (mk_hyp x (mk_usquash t)) ++ J) (mk_hhyp y t)) (mk_concl C e)
      ]
      [].

Lemma rule_usquash_elim_true {o} :
  forall lib (H J : barehypotheses)
         (t C e : @NTerm o) x y,
    rule_true lib (rule_usquash_elim H J t C e x y).
Proof.
  unfold rule_usquash_elim, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  assert (covered e (nh_vars_hyps (snoc H (mk_hyp x (mk_usquash t)) ++ J))) as cov.
  { clear hyp1.
    rw @nh_vars_hyps_snoc in ce; allsimpl.
    allrw @nh_vars_hyps_app.
    allrw @nh_vars_hyps_snoc; allsimpl; auto. }
  exists cov.

  assert (x <> y
          # !LIn x (vars_hyps H)
          # !LIn y (vars_hyps H)
          # !LIn x (vars_hyps J)
          # !LIn y (vars_hyps J)
          # subset (free_vars t) (vars_hyps H)
          # disjoint (vars_hyps H) (vars_hyps J)
          # !LIn y (free_vars C)
          # !LIn y (free_vars e)
          # !LIn x (free_vars t)
          # !LIn y (free_vars t)) as vhyps.

  {
    clear hyp1.
    dwfseq;
    sp;
      try (complete (pose proof (cg y) as xx; autodimp xx hyp;
                     rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp));
      try (complete (pose proof (ce y) as xx; autodimp xx hyp;
                     rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp;
                     apply subset_hs_vars_hyps in xx; tcsp));
      try (complete (introv i; apply wfh6; allrw in_remove_nvars; simpl; dands; tcsp;
                     intro xx; allrw not_over_or; repndors; subst; tcsp;
                     pose proof (newvarlst_prop [t]) as xx;
                     pose proof (newvarlst_prop [t,mk_var (newvarlst [t])]) as zz;
                     simpl in *; autorewrite with list in *; allrw in_app_iff; tcsp));
      try (complete (assert (LIn x (vars_hyps H)) as xx; tcsp;
                     apply wfh6; allrw in_remove_nvars; simpl; dands; tcsp;
                     intro xx; allrw not_over_or; repndors; subst; tcsp;
                     pose proof (newvarlst_prop [t]) as xx;
                     pose proof (newvarlst_prop [t,mk_var (newvarlst [t])]) as zz;
                     simpl in *; autorewrite with list in *; allrw in_app_iff; tcsp));
      try (complete (assert (LIn y (vars_hyps H)) as xx; tcsp;
                     apply wfh6; allrw in_remove_nvars; simpl; dands; tcsp;
                     intro xx; allrw not_over_or; repndors; subst; tcsp;
                     pose proof (newvarlst_prop [t]) as xx;
                     pose proof (newvarlst_prop [t,mk_var (newvarlst [t])]) as zz;
                     simpl in *; autorewrite with list in *; allrw in_app_iff; tcsp)).
  }

  destruct vhyps as [ nxy vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nyH vhyps ].
  destruct vhyps as [ nxJ vhyps ].
  destruct vhyps as [ nyJ vhyps ].
  destruct vhyps as [ stH vhyps ].
  destruct vhyps as [ dHJ vhyps ].
  destruct vhyps as [ nyC vhyps ].
  destruct vhyps as [ nye vhyps ].
  destruct vhyps as [ nxt nyt ].

  vr_seq_true.
  vr_seq_true in hyp1.

  dup sim as simbackup.

  apply similarity_app in sim; exrepnd; subst.
  allrw length_snoc.
  apply similarity_snoc in sim5; exrepnd; subst.
  allsimpl.
  allrw length_snoc; cpx.
  lsubst_tac.
  allrw @equality_in_mkc_usquash; repnd; spcast.
  unfold inhabited_type in sim2; exrepnd.

  assert (disjoint (free_vars t) (dom_csub s1b)) as disjts1b.
  { introv i j.
    apply stH in i.
    apply dHJ in i.
    apply similarity_dom in sim1; repnd.
    autorewrite with slow in *.
    rw sim2 in j; tcsp. }

  pose proof (hyp1
                (snoc (snoc s1a0 (x,t1) ++ s1b) (y,t0))
                (snoc (snoc s2a0 (x,t2) ++ s2b) (y,t0))) as hyp;
    clear hyp1; exrepnd; clear_irr.
  repeat (autodimp hyp hh).

  { apply hyps_functionality_snoc2; simpl; auto.

    introv equ sim'.
    lsubst_tac.

    eapply hyps_functionality_init_seg in eqh;eauto.

    apply similarity_app in sim'; exrepnd; subst.
    allrw length_snoc.
    apply app_split in sim'0; repnd; subst; repeat (rw length_snoc);
    try (complete (allrw; sp)).
    apply similarity_snoc in sim'5; exrepnd; subst; allsimpl; cpx; ginv.

    assert (disjoint (free_vars t) (dom_csub s2b0)) as disjts2b0.
    { introv i j.
      apply stH in i.
      apply dHJ in i.
      apply similarity_dom in sim'1; repnd.
      autorewrite with slow in *.
      rw sim'1 in j; tcsp. }
    lsubst_tac.

    pose proof (eqh (snoc s2a1 (x,mkc_axiom))) as h.

    autodimp h hyp.
    { sim_snoc2; dands; auto.
      lsubst_tac.
      apply equality_in_mkc_usquash.
      exists t0.
      apply equality_refl in equ; auto. }

    apply eq_hyps_snoc in h; exrepnd; allsimpl; cpx; ginv.
    lsubst_tac.
    rw @tequality_mkc_usquash in h0; auto.
(*  }

  { sim_snoc2; dands; lsubst_tac; auto.
    apply cover_vars_app_weak; apply cover_vars_snoc_weak; auto.
  }

  exrepnd.
  lsubst_tac.
  dands; auto.*)
Abort.


(*
Definition rule_usquash_elim {o}
           (H J : barehypotheses)
           (t a b C : @NTerm o)
           (x y : NVar)
           (i : nat)
  :=
    mk_rule
      (mk_baresequent (snoc H (mk_hyp x (mk_usquash t)) ++ J) (mk_conclax (mk_equality a b C)))
      [ mk_baresequent
          (snoc (snoc H (mk_hyp x t) ++ J) (mk_hyp y t))
          (mk_conclax (mk_equality a (subst b x (mk_var y)) C)),
        mk_baresequent (snoc H (mk_hyp x (mk_usquash t)) ++ J) (mk_conclax (mk_member C (mk_uni i))),
        mk_baresequent H (mk_conclax (mk_member t (mk_uni i)))
      ]
      [].

Lemma rule_usquash_elim_true {o} :
  forall lib (H J : barehypotheses)
         (t a b C : @NTerm o) x y i,
    rule_true lib (rule_usquash_elim H J t a b C x y i).
Proof.
  unfold rule_usquash_elim, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps (snoc H (mk_hyp x (mk_usquash t)) ++ J))).

  assert (x <> y
          # !LIn x (vars_hyps H)
          # !LIn y (vars_hyps H)
          # !LIn x (vars_hyps J)
          # !LIn y (vars_hyps J)
          # subset (free_vars t) (vars_hyps H)
          # disjoint (vars_hyps H) (vars_hyps J)
          # !LIn y (free_vars a)
          # !LIn y (free_vars b)
          # !LIn y (free_vars C)
          # !LIn x (free_vars t)
          # !LIn y (free_vars t)) as vhyps.

  {
    clear hyp1.
    dwfseq.
    sp;
      try (complete (pose proof (cg y) as xx; autodimp xx hyp;
                     rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp));
      try (complete (pose proof (cg0 y) as xx; autodimp xx hyp;
                     rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp));
      try (complete (pose proof (cg1 y) as xx; autodimp xx hyp;
                     rw in_app_iff in xx; rw in_snoc in xx; repndors; tcsp)).
  }

  destruct vhyps as [ nxy vhyps ].
  destruct vhyps as [ nxH vhyps ].
  destruct vhyps as [ nyH vhyps ].
  destruct vhyps as [ nxJ vhyps ].
  destruct vhyps as [ nyJ vhyps ].
  destruct vhyps as [ stH vhyps ].
  destruct vhyps as [ dHJ vhyps ].
  destruct vhyps as [ nya vhyps ].
  destruct vhyps as [ nyb vhyps ].
  destruct vhyps as [ nyC vhyps ].
  destruct vhyps as [ nxt nyt ].

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.
  teq_and_eq C a b s1 s2 (snoc H (mk_hyp x (mk_usquash t)) ++ J).

  - vr_seq_true in hyp2.
    pose proof (hyp2 s1 s2 eqh sim) as h; clear hyp2.
    exrepnd; lsubst_tac.
    apply tequality_in_uni_implies_tequality in h0; auto.
    rw <- @member_member_iff in h1.
    apply member_in_uni in h1; auto.

  - dup sim as simbackup.

    apply similarity_app in sim; exrepnd; subst.
    allrw length_snoc.
    apply similarity_snoc in sim5; exrepnd; subst.
    allsimpl.
    allrw length_snoc; cpx.
    lsubst_tac.
    allrw @equality_in_mkc_usquash; repnd.

    assert (disjoint (free_vars t) (dom_csub s1b)) as disjts1b.
    { introv k j.
      apply stH in k.
      apply dHJ in k.
      apply similarity_dom in sim1; repnd.
      autorewrite with slow in *.
      rw sim0 in j; tcsp. }

    vr_seq_true in hyp1.

    unfold inhabited_type in *; exrepnd.

    pose proof (hyp1
                  (snoc (snoc s1a0 (x,t0) ++ s1b) (y,t0))
                  (snoc (snoc s2a0 (x,t0) ++ s2b) (y,t0))) as hyp;
      clear hyp1; exrepnd; clear_irr.
    repeat (autodimp hyp hh).

    { apply hyps_functionality_snoc2; simpl; auto;[|].

      - introv equ sim'.
        lsubst_tac.
        apply similarity_app in sim'; exrepnd; subst.
        allrw length_snoc.
        apply app_split in sim'0; repnd; subst; repeat (rw length_snoc);
        try (complete (allrw; sp)).
        allrw length_snoc; cpx.
        apply similarity_snoc in sim'5; exrepnd; subst; allsimpl.
        allrw length_snoc; cpx.

        assert (disjoint (free_vars t) (dom_csub s2b0)) as disjts2b0.
        { introv k j.
          apply stH in k.
          apply dHJ in k.
          apply similarity_dom in sim'1; repnd.
          autorewrite with slow in *.
          rw sim'1 in j; tcsp. }

        lsubst_tac.

        eapply hyps_functionality_init_seg in hf;eauto.
        pose proof (hyps_functionality_init_seg_snoc2
                      lib s1a t1 t2 H x (mk_usquash t) w p hf) as h.
        autodimp h hh.
        { lsubst_tac.
          apply implies_equality_in_mkc_usquash; auto; eauto 3 with slow. }

        vr_seq_true in hyp3.
        pose proof (hyp3 s1a s2a1 h sim'5) as hh; clear hyp2; exrepnd.
        lsubst_tac.
        apply tequality_in_uni_implies_tequality in hh0; auto; eauto 3 with slow.

      -


Lemma hyps_functionality_usquash_implies2 {o} :
  forall lib (s1 s2 : @CSub o) T (wT : wf_term T) (cT : cover_vars T s1) x t t' H J,
    length H = length s1
    -> (forall s3 (cT' : cover_vars T s3),
           similarity lib s1 s3 H
           -> tequality lib (lsubstc T wT s1 cT) (lsubstc T wT s3 cT'))
    -> hyps_functionality lib (snoc s1 (x, t) ++ s2) (snoc H (mk_hyp x (mk_usquash T)) ++ J)
    -> hyps_functionality lib (snoc s1 (x, t' ) ++ s2) (snoc H (mk_hyp x T) ++ J).
Proof.
  introv len imp hf sim.

  apply similarity_app in sim; exrepnd; subst.
  allrw length_snoc.
  apply app_split in sim0; repnd; subst; repeat (rw length_snoc); try (complete (allrw; sp)).
  allrw length_snoc; cpx.
  apply similarity_snoc in sim5; exrepnd; subst; allsimpl.
  allrw length_snoc; cpx.
  pose proof (hf (snoc s2a0 (x,t2) ++ s2b)) as xx; clear hf.
  autodimp xx hyp.

  - apply similarity_app.
    eexists; eexists; eexists; eexists; dands; eauto;
    allrw length_snoc; auto.

    sim_snoc2; eauto 3 with slow;
    try (apply wf_mk_usquash; auto);
    try (apply cover_vars_usquash; auto);
    dands; auto.

    lsubst_tac.
    apply implies_equality_in_mkc_usquash; eauto 3 with slow.

  - apply eq_hyps_app in xx; exrepnd.
    allrw length_snoc.

    apply app_split in xx0; repnd; subst;
    repeat (rw length_snoc); try (rw sim3; rw xx3; auto).

    apply app_split in xx2; repnd; subst;
    repeat (rw length_snoc); try (rw sim4; rw xx4; auto).

    apply eq_hyps_snoc in xx5; exrepnd; allsimpl; cpx.

    apply eq_hyps_app.
    eexists; eexists; eexists; eexists; dands; eauto;
    allrw length_snoc; auto.
    apply eq_hyps_snoc; simpl.

    assert (cover_vars T s2a) as c2.
    { clear xx0; rw @cover_vars_usquash in p2; auto. }

    exists s1a0 s2a t0 t3 w p c2; dands; auto.
    proof_irr.
    apply imp; auto.
Qed.




        apply (hyps_functionality_usquash_implies lib s1a0 s1b t w0 c1); auto.
        introv sim'.

        eapply hyps_functionality_init_seg in hf;eauto.
        pose proof (hyps_functionality_init_seg_snoc2
                      lib s1a0 t1 t2 H x (mk_usquash t) w p hf) as h.
        autodimp h hh.
        { lsubst_tac.
          apply implies_equality_in_mkc_usquash; auto; eauto 3 with slow. }

        vr_seq_true in hyp3.
        pose proof (hyp3 s1a0 s3 h sim') as hh; clear hyp2; exrepnd.
        lsubst_tac.
        apply tequality_in_uni_implies_tequality in hh0; auto; eauto 3 with slow.
    }

    { sim_snoc2.

      { apply cover_vars_app_weak.
        apply cover_vars_snoc_weak; auto. }

      dands; lsubst_tac; auto.

      apply similarity_app.
      eexists; eexists; eexists; eexists; dands; eauto;
      allrw length_snoc; auto.

      sim_snoc2; dands; proof_irr; auto; eauto 3 with slow.
    }

    exrepnd.
    lsubst_tac.
    allrw <- @member_equality_iff.
    apply equality_commutes4 in hyp0; auto.
    eapply equality_respects_alphaeqc_right;[|exact hyp0].
    clear hyp0 hyp1.

    assert (cover_vars (mk_var y) (snoc (snoc s1a0 (x, t1) ++ s1b) (y, t2))) as covy1.
    { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

    assert (cover_vars (mk_var y) (snoc (snoc s2a0 (x, t1) ++ s2b) (y, t2))) as covy2.
    { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

    assert (!LIn y (dom_csub (snoc s2a0 (x, t1) ++ s2b))) as niy.
    { rw @dom_csub_app; rw @dom_csub_snoc; simpl; rw in_app_iff; rw in_snoc.
      apply similarity_dom in sim6; repnd; rw sim6.
      apply similarity_dom in sim1; repnd; rw sim1.
      autorewrite with slow.
      intro k; repndors; tcsp. }

    lsubstc_subst_aeq.
    substc_lsubstc_vars3.
    revert c6.
    lsubst_tac.
    introv.
    repeat (lsubstc_snoc2;[]).

    unfold alphaeqc; simpl.
    apply alpha_eq_lsubst_if_ext_eq; auto.
    introv k.
    simpl.
    repeat (rw <- @csub2sub_app).
    repeat (rw @csub2sub_snoc).
    repeat (rw @sub_find_app).
    repeat (rw @sub_find_snoc).
    boolvar; eauto 3 with slow.

    rw @sub_find_none_if; eauto 3 with slow.
    rw @dom_csub_eq.
    apply similarity_dom in sim6; repnd; rw sim6; auto.
Qed.
 *)
