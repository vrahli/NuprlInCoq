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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export sequents_equality.
Require Export per_props_psquash.
Require Export sequents_tacs2.
Require Export per_can.
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
    apply tequality_mkc_member_sp in hyp0; repnd.
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
  apply tequality_mkc_member_sp in h0; repnd.
  rw @tequality_mkc_cequiv.
  rw @tequality_mkc_squash in h4.
  dands; split; try (intro xx); spcast; auto;
  try (complete (apply computes_to_valc_implies_cequivc; auto)).
  apply cequiv_stable; repndors.

  - apply equality_in_mkc_squash in h0; repnd; spcast.
    apply computes_to_valc_implies_cequivc; auto.

  - spcast.
    eapply cequivc_trans;[apply cequivc_sym;eauto|]; auto.
Qed.


(*
   H, x : psquash(t), J |- a = b in C

     By PSquashElim i y z

     H, x : t, y : t, J |- a = b in C
     H |- t in U{i}  (* This is needed because psquash(t) is extensional *)

 *)
Definition rule_psquash_elim {o}
           (H J : barehypotheses)
           (t a b C : @NTerm o)
           (x : NVar)
           (i : nat)
  :=
    mk_rule
      (mk_baresequent (snoc H (mk_hyp x (mk_psquash t)) ++ J) (mk_conclax (mk_equality a b C)))
      [ mk_baresequent (snoc H (mk_hyp x t) ++ J) (mk_conclax (mk_equality a b C)),
        mk_baresequent H (mk_conclax (mk_member t (mk_uni i)))
      ]
      [].

Lemma rule_psquash_elim_true {o} :
  forall lib (H J : barehypotheses)
         (t a b C : @NTerm o) x i,
    rule_true lib (rule_psquash_elim H J t a b C x i).
Proof.
  unfold rule_psquash_elim, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps (snoc H (mk_hyp x (mk_psquash t)) ++ J))).

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.
  teq_and_eq C a b s1 s2 (snoc H (mk_hyp x (mk_psquash t)) ++ J).

  - vr_seq_true in hyp1.

    apply similarity_app in sim; exrepnd; subst.
    allrw length_snoc.
    apply similarity_snoc in sim5; exrepnd; subst.
    allsimpl.
    allrw length_snoc; cpx.
    lsubst_tac.
    allrw @equality_in_mkc_psquash; repnd.

    pose proof (hyp1
                  (snoc s1a0 (x,t1) ++ s1b)
                  (snoc s2a0 (x,t1) ++ s2b)) as hyp;
      clear hyp1; exrepnd; clear_irr.
    repeat (autodimp hyp hh).

    { introv sim'.
      apply similarity_app in sim'; exrepnd; subst.
      allrw length_snoc.
      apply app_split in sim'0; repnd; subst; repeat (rw length_snoc);
      try (complete (allrw; sp)).
      apply similarity_snoc in sim'5; exrepnd; subst; allsimpl.
      allrw length_snoc; cpx.

      assert (cover_vars t s2a1) as cov2.
      { allrw @cover_vars_eq.
        allapply @similarity_dom; repnd.
        rw sim'6; rw <- sim'3; auto. }

      apply eq_hyps_app.
      exists (snoc s1a (x,t0)) s1b0 (snoc s2a1 (x,t3)) s2b0;
        allrw length_snoc; dands; auto; proof_irr.

      - apply eq_hyps_snoc; simpl.
        exists s1a s2a1 t0 t3 w0 p0 cov2; dands; auto.

        + eapply hyps_functionality_init_seg in eqh;eauto.
          pose proof (hyps_functionality_init_seg_snoc2
                      lib s1a t0 t2 H x (mk_psquash t) w p eqh) as h.
          autodimp h hh.
          lsubst_tac.
          apply implies_equality_in_mkc_psquash; auto.

        + eapply hyps_functionality_init_seg in eqh;eauto.
          pose proof (eqh (snoc s2a1 (x,t2))) as h.
          autodimp h hyp.

          * sim_snoc2.
            dands; auto.
            lsubst_tac.
            apply implies_equality_in_mkc_psquash; auto.

          * pose proof (hyps_functionality_init_seg_snoc2
                          lib s1a t0 t2 H x (mk_psquash t) w p eqh) as q.
            autodimp q hyp.
            { lsubst_tac.
              apply implies_equality_in_mkc_psquash; auto. }

            vr_seq_true in hyp2.
            pose proof (hyp2 s1a s2a1 q sim'6) as hh; clear hyp2; exrepnd.
            lsubst_tac.
            apply tequality_in_uni_implies_tequality in hh0; auto.
            apply inhabited_implies_tequality in sim2; auto.

      - pose proof (eqh (snoc s2a1 (x,t3) ++ s2b0)) as h; clear eqh.
        autodimp h hh.

        + apply similarity_app.
          eexists; eexists; eexists; eexists; dands; eauto; allrw length_snoc; auto.
          sim_snoc2; dands; auto.
          lsubst_tac.
          apply implies_equality_in_mkc_psquash; auto.
          apply equality_sym in sim'2; apply equality_refl in sim'2; auto.

        + apply eq_hyps_app in h; exrepnd; allsimpl; allrw length_snoc.
          apply app_split in h0; repnd; subst; repeat (rw length_snoc);
          try (complete (allrw; sp)).
          apply app_split in h2; repnd; subst; repeat (rw length_snoc);
          try (complete (allrw; sp)).
    }

    { apply similarity_app.
      eexists; eexists; eexists; eexists; dands; eauto; allrw length_snoc; auto.
      sim_snoc2; dands; auto; proof_irr.
      rw @member_eq; auto. }

    exrepnd.
    lsubst_tac.
    apply tequality_mkc_equality_sp in hyp0; repnd.

    SearchAbout tequality mkc_equality.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
