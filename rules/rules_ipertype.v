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


Require Export sequents_tacs.
Require Export sequents_useful.
Require Export per_props_equality.
Require Export per_props_pertype.
Require Export sequents_equality.
Require Export list. (* why *)
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)



(* end hide *)

(**

  We now prove the truth of several rules about the intensional PER type.

*)

(* [14] ============ IPERTYPE MEMBER EQUALITY ============ *)

(**

  The following rule is called the ``ipertype member equality'' rule.
  It allows one to prove that terms are well-formed partial
  equivalence relations, i.e., members of a ``ipertype'' type.
<<
   H |- t1 = t2 in ipertype(R)

     By ipertypeMemberEquality i

     H |- ipertype(R) in Type(i)
     H |- R t1 t2
     H |- t1 in Base
>>
 *)


Definition rule_ipertype_member_equality {o}
           (t1 t2 R e : NTerm)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality t1 t2 (mk_ipertype R))))
    [ mk_baresequent H (mk_conclax (mk_member (mk_ipertype R) (mk_uni i))),
      mk_baresequent H (mk_concl (mk_apply2 R t1 t2) e),
      mk_baresequent H (mk_conclax (mk_member t1 mk_base))
    ]
    [].

Lemma rule_ipertype_member_equality_true {o} :
  forall lib (t1 t2 R e : NTerm),
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_ipertype_member_equality
                 t1 t2 R e
                 i
                 H).
Proof.
  unfold rule_ipertype_member_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lift_lsubst.
  rw @member_eq.
  rw <- @member_equality_iff.

  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2); intro h.
  repeat (autodimp h hyp); exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_member_iff.
  apply tequality_in_uni_implies_tequality in h0; auto.
  (* allapply @member_in_uni. *)

  generalize (teq_and_eq_if_equality
                lib (mk_ipertype R) t1 t2 s1 s2 H wT w1 w2 c1 c3 c2 c4 cT cT0
                eqh sim); intro k; lsubst_tac; apply k; clear k; auto.

  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.

  generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.

  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.

  vr_seq_true in hyp3.
  generalize (hyp3 s1 s2 hf sim); clear hyp3; intro hyp3; exrepnd.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_member_iff.
  allrw @tequality_mkc_member_base.
  assert (type lib (mkc_ipertype (lsubstc R w0 s1 c1))).
     { allapply @member_in_uni. auto. }
  apply tequality_in_uni_implies_tequality in hyp0; auto.
  
  allapply @inhabited_type_if_equality.
  rw @tequality_mkc_ipertype in hyp0; repnd.
  spcast.

  rw @equality_in_mkc_ipertype2; dands; auto.
  apply @inhabited_type_tequality with (a := mkc_apply2 (lsubstc R w0 s1 c1)
                                                       (lsubstc t1 w1 s1 ca1)
                                                       (lsubstc t2 w2 s1 c3)); auto.
  apply @tequality_trans with (t2 := mkc_apply2 (lsubstc R w0 s2 c0)
                                               (lsubstc t1 w1 s2 ct2)
                                               (lsubstc t2 w2 s2 cb2)); auto.
  apply @tequality_sym.
  apply @tequality_respects_cequivc_left with (T1 := mkc_apply2 (lsubstc R w0 s1 c1)
                                                                (lsubstc t1 w1 s2 ct2)
                                                                (lsubstc t2 w2 s2 cb2)); auto.
  apply implies_cequivc_apply2; sp.
  apply cequivc_sym; auto.
  
Qed.

(* begin hide *)




(* end hide *)

(* [15] ============ IPERTYPE ELIMINATION ============ *)

(**

  We can state the ipertype elimination rule as follows:
<<
   H, x : t1 = t2 in ipertype(R), J |- C ext e

     By ipertypeElimination i z

     H, x : t1 = t2 in ipertype(R), [z : R t1 t2], J |- C ext e
     H |- R t1 t2 in Type(i)
>>
 *)

Definition rule_ipertype_elimination {o}
           (R t1 t2 C e : NTerm)
           (x z : NVar)
           (i : nat)
           (H J : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x (mk_equality t1 t2 (mk_ipertype R))) ++ J)
       (mk_concl C e))
    [ mk_baresequent
        (snoc (snoc H (mk_hyp x (mk_equality t1 t2 (mk_ipertype R))))
              (mk_hhyp z (mk_apply2 R t1 t2))
              ++ J)
        (mk_concl C e),
      mk_baresequent
        H
        (mk_conclax (mk_member (mk_apply2 R t1 t2) (mk_uni i)))
    ]
    [sarg_var z].

Lemma rule_ipertype_elimination_true {o} :
  forall lib (R t1 t2 C e : NTerm),
  forall x z : NVar,
  forall i : nat,
  forall H J : @barehypotheses o,
    rule_true lib (rule_ipertype_elimination
                 R t1 t2 C e
                 x z
                 i
                 H J).
Proof.
  unfold rule_ipertype_elimination, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1; rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (covered e
                  (nh_vars_hyps
                     (snoc H (mk_hyp x (mk_equality t1 t2 (mk_ipertype R))) ++ J))) as cs.
  clear hyp1 hyp2.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars R)
           # !LIn x (free_vars t1)
           # !LIn x (free_vars t2)
           # !LIn z (free_vars C)
           # !LIn z (free_vars e)
           # !LIn z (hyps_free_vars J)
           # !LIn z (free_vars_hyps J)
           # !LIn z (vars_hyps J)) as vhyps.

  clear hyp1.
  dwfseq.
  sp;
    try (complete (discover; repeat(first[progress(allrw in_app_iff)|progress(allrw in_snoc)]); sp));
    try (complete (generalize (ce0 z); allrw @nh_vars_hyps_app; allrw @nh_vars_hyps_snoc;
                   allsimpl; allrw in_app_iff; allrw in_snoc; sp;
                   generalize (subvars_hs_vars_hyps H); intros;
                   generalize (subvars_hs_vars_hyps J); intros;
                   allrw subvars_prop; apply_in_hyp p; sp)).

  destruct vhyps as [ nixr vhyps ].
  destruct vhyps as [ nixt1 vhyps ].
  destruct vhyps as [ nixt2 vhyps ].
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
  rw @equality_in_mkc_ipertype in sim0; repnd.

  vr_seq_true in hyp1.
  unfold inhabited_type in sim7; exrepnd.
  generalize (hyp1 ((snoc (snoc s1a0 (x, t0)) (z, t)) ++ s1b)
                   ((snoc (snoc s2a0 (x, t3)) (z, t)) ++ s2b));
    clear hyp1; intro hyp1.
  repeat (autodimp hyp1 hyp); exrepnd.

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
         s2b1; repeat (rw length_snoc); dands; try (complete sp).

  assert (cover_vars (mk_apply2 R t1 t2) (snoc s2a1 (x, t7)))
         as cv
         by (apply cover_vars_apply2; sp;
             try (apply cover_vars_var);
             repeat (apply cover_vars_snoc_weak); sp;
             repeat (rw dom_csub_snoc); simpl; repeat (rw in_snoc); sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc s1a (x, t6)) (snoc s2a1 (x, t7)) t4 t5 w3 p0 cv;
    dands; try (complete sp).

  lsubst_tac.

(*
rw @tequality_mkc_equality in j0; repnd.
rw @tequality_mkc_ipertype in j2; repnd.
destruct j5 as [j5 | j5].
rw @equality_in_mkc_ipertype in j5; repnd.
*)

  vr_seq_true in hyp2.
  generalize (hyp2 s1a s2a1); clear hyp2; intro hyp2.
  repeat (autodimp hyp2 hyp); exrepnd.
  generalize (hyps_functionality_init_seg_snoc
                lib s1a t6 t7 H (mk_hyp x (mk_equality t1 t2 (mk_ipertype R))) w4 p1);
    simpl; intro k.
  apply k; sp.

  apply hyps_functionality_init_seg with (s3 := s2b1) in eqh; sp.
  rw @substitute_hyps_snoc_sub_weak in sim10; sp.

  rw @similarity_snoc in sim15; simpl in sim15; exrepnd; cpx.
  lsubst_tac; sp.

  rw @similarity_snoc in sim15; simpl in sim15; exrepnd; cpx.
  lsubst_tac.
  eapply tequality_in_uni_implies_tequality. exact hyp0. 
  eapply member_if_inhabited. exact hyp1.
  

  apply sub_eq_hyps_snoc_weak; sp.


  (* similarity *)
  rw @similarity_app; simpl.
  exists (snoc (snoc s1a0 (x, t0)) (z, t))
         s1b
         (snoc (snoc s2a0 (x, t3)) (z, t))
         s2b; repeat (rw length_snoc); sp.

  assert (wf_term (mk_apply2 R t1 t2))
         as wfap by (apply wf_apply2; sp).

  assert (cover_vars (mk_apply2 R t1 t2) (snoc s1a0 (x, t0)))
         as cvap
         by (apply cover_vars_snoc_weak;rw @cover_vars_apply2; sp).

  rw @similarity_snoc; simpl.
  exists (snoc s1a0 (x, t0)) (snoc s2a0 (x, t3)) t t wfap cvap; sp.

  lsubst_tac.
  rw @member_eq; sp.

  rewrite substitute_hyps_snoc_sub_weak; sp.
  (* similarity proved *)

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

  rw eq1 in hyp0.
  rw eq1 in hyp1.
  rw eq2 in hyp0.
  rw eq3 in hyp1.
  rw eq4 in hyp1.
  sp.
Qed.

(* begin hide *)

Lemma rule_ipertype_elimination_true_ex {o} :
  forall lib i z R t1 t2 C e x H J,
    rule_true_if lib (@rule_ipertype_elimination o
                 R t1 t2 C e
                 x z
                 i
                 H J).
Proof.
  intros.
  generalize (rule_ipertype_elimination_true lib R t1 t2 C e x z i H J); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.




(* end hide *)

(**

  This is a variant of [rule_ipertype_elimination] but where the
  well-formedness goal is stated using a ``type'' sequent.  Also it
  allows one to use all the hypotheses:
<<
   H, x : t1 = t2 in ipertype(R), J |- C ext e

     By ipertypeElimination i z

     H, x : t1 = t2 in ipertype(R), [z : R t1 t2], J |- C ext e
     H, x : t1 = t2 in ipertype(R), J |- R t1 t2 is a type
>>
 *)

Definition rule_ipertype_elimination_t {o}
           (R t1 t2 C e : NTerm)
           (x z : NVar)
           (i : nat)
           (H J : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x (mk_equality t1 t2 (mk_ipertype R))) ++ J)
       (mk_concl C e))
    [ mk_baresequent
        (snoc (snoc H (mk_hyp x (mk_equality t1 t2 (mk_ipertype R))))
              (mk_hhyp z (mk_apply2 R t1 t2))
              ++ J)
        (mk_concl C e),
      mk_baresequent
        (snoc H (mk_hyp x (mk_equality t1 t2 (mk_ipertype R))) ++ J)
        (mk_concl_t (mk_apply2 R t1 t2))
    ]
    [sarg_var z].

Lemma rule_ipertype_elimination_t_true {o} :
  forall lib (R t1 t2 C e : NTerm),
  forall x z : NVar,
  forall i : nat,
  forall H J : @barehypotheses o,
    rule_true lib (rule_ipertype_elimination_t
                 R t1 t2 C e
                 x z
                 i
                 H J).
Proof.
  unfold rule_ipertype_elimination_t, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (covered e
                  (nh_vars_hyps
                     (snoc H (mk_hyp x (mk_equality t1 t2 (mk_ipertype R))) ++ J))) as cs.
  clear hyp1 hyp2.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars R)
           # !LIn x (free_vars t1)
           # !LIn x (free_vars t2)
           # disjoint (free_vars R) (vars_hyps J)
           # disjoint (free_vars t1) (vars_hyps J)
           # disjoint (free_vars t2) (vars_hyps J)
           # !LIn z (free_vars C)
           # !LIn z (free_vars e)
           # !LIn z (hyps_free_vars J)
           # !LIn z (free_vars_hyps J)
           # !LIn z (vars_hyps J)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp;
    try (complete (allunfold @disjoint; introv p; discover; allrw in_app_iff; allrw in_snoc; sp));
    try (complete (discover; repeat (first [ progress (allrw in_app_iff) | progress (allrw in_snoc) ]); sp));
    try (complete (generalize (ce0 z); allrw @nh_vars_hyps_app; allrw @nh_vars_hyps_snoc;
                   allsimpl; allrw in_app_iff; allrw in_snoc; sp;
                   generalize (subvars_hs_vars_hyps H); intros;
                   generalize (subvars_hs_vars_hyps J); intros;
                   allrw subvars_prop; apply_in_hyp p; sp));
    try (complete (unfold disjoint; unfold disjoint in wfh13; introv k l; discover;
                   repeat (first [ progress (allrw in_app_iff) | progress (allrw in_snoc) ]); sp)).

  destruct vhyps as [ nixr vhyps ].
  destruct vhyps as [ nixt1 vhyps ].
  destruct vhyps as [ nixt2 vhyps ].
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
  rw @equality_in_mkc_ipertype in sim0; repnd.

  vr_seq_true in hyp1.
  unfold inhabited_type in sim7; exrepnd.
  generalize (hyp1 ((snoc (snoc s1a0 (x, t0)) (z, t)) ++ s1b)
                   ((snoc (snoc s2a0 (x, t3)) (z, t)) ++ s2b));
    clear hyp1; intro hyp1.
  repeat (autodimp hyp1 hyp); exrepnd.

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
         s2b1; repeat (rw length_snoc); dands; try (complete sp).

  assert (cover_vars (mk_apply2 R t1 t2) (snoc s2a1 (x, t7)))
         as cv
         by (apply cover_vars_apply2; sp;
             try (apply cover_vars_var);
             repeat (apply cover_vars_snoc_weak); sp;
             repeat (rw dom_csub_snoc); simpl; repeat (rw in_snoc); sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc s1a (x, t6)) (snoc s2a1 (x, t7)) t4 t5 wfct0 p0 cv;
    dands; try (complete sp).

  lsubst_tac.

  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s1a  (x, t6) ++ s1b)
                   (snoc s2a1 (x, t7) ++ s2b));
    clear hyp2; intro hyp2.
  repeat (autodimp hyp2 hyp); exrepnd.

  rw @similarity_app; simpl.
  exists (snoc s1a (x,t6)) s1b (snoc s2a1 (x,t7)) s2b; repeat (rw length_snoc); sp.
  lsubst_tac.
  auto.

  apply sub_eq_hyps_snoc_weak; sp.


  (* similarity *)
  rw @similarity_app; simpl.
  exists (snoc (snoc s1a0 (x, t0)) (z, t))
         s1b
         (snoc (snoc s2a0 (x, t3)) (z, t))
         s2b; repeat (rw length_snoc); sp.

  assert (wf_term (mk_apply2 R t1 t2))
         as wfap by (apply wf_apply2; sp).

  assert (cover_vars (mk_apply2 R t1 t2) (snoc s1a0 (x, t0)))
         as cvap
         by (apply cover_vars_snoc_weak;rw @cover_vars_apply2; sp).

  rw @similarity_snoc; simpl.
  exists (snoc s1a0 (x, t0)) (snoc s2a0 (x, t3)) t t wfap cvap; sp.

  lsubst_tac.
  rw @member_eq; sp.

  rewrite substitute_hyps_snoc_sub_weak; sp.
  (* similarity proved *)

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

  rw eq1 in hyp0.
  rw eq1 in hyp1.
  rw eq2 in hyp0.
  rw eq3 in hyp1.
  rw eq4 in hyp1.
  sp.
Qed.

(* begin hide *)

Lemma rule_ipertype_elimination_t_true_ex {o} :
  forall lib i z R t1 t2 C e x H J,
    rule_true_if lib (@rule_ipertype_elimination_t o
                 R t1 t2 C e
                 x z
                 i
                 H J).
Proof.
  intros.
  generalize (rule_ipertype_elimination_t_true lib R t1 t2 C e x z i H J); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.




(* end hide *)

(* [16] ============ IPERTYPE EQUALITY ============ *)

(**

  We can state the ipertype equality rule as follows:
<<
   H |- ipertype(R1) = ipertype(R2) in Type(i)

     By ipertypeMemberEquality x y z u v

     H, x : Base, y : Base |- R1 x y = R2 x y in Type(i)
     H, x : Base, y : Base, z : R1 x y |- R1 y x
     H, x : Base, y : Base, z : Base, u : R1 z y, v : R1 y z |- R1 x z
>>
 *)

Definition rule_ipertype_equality {o}
           (R1 R2 e1 e2 : NTerm)
           (x y z u v : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_ipertype R1) (mk_ipertype R2) (mk_uni i))))
    [ mk_baresequent
        (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))
        (mk_conclax (mk_equality
                       (mk_apply2 R1 (mk_var x) (mk_var y))
                       (mk_apply2 R2 (mk_var x) (mk_var y))
                       (mk_uni i))),
      mk_baresequent
        (snoc (snoc (snoc H (mk_hyp x mk_base))
                    (mk_hyp y mk_base))
              (mk_hyp z (mk_apply2 R1 (mk_var x) (mk_var y))))
        (mk_concl (mk_apply2 R1 (mk_var y) (mk_var x)) e1),
      mk_baresequent
        (snoc (snoc (snoc (snoc (snoc H (mk_hyp x mk_base))
                                (mk_hyp y mk_base))
                          (mk_hyp z mk_base))
                    (mk_hyp u (mk_apply2 R1 (mk_var x) (mk_var y))))
              (mk_hyp v (mk_apply2 R1 (mk_var y) (mk_var z))))
        (mk_concl (mk_apply2 R1 (mk_var x) (mk_var z)) e2)
    ]
    [].

Lemma rule_ipertype_equality_true {o} :
  forall lib (R1 R2 e1 e2 : NTerm),
  forall x y z u v : NVar,
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_ipertype_equality
                 R1 R2 e1 e2
                 x y z u v
                 i
                 H).
Proof.
  unfold rule_ipertype_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1; rename Hyp1 into hyp2; rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  dup hyp1 as hypmem.
  apply sequent_equality_implies_member in hypmem; exrepnd.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars R1)
           # !LIn y (free_vars R1)
           # !LIn z (free_vars R1)
           # !LIn u (free_vars R1)
           # !LIn v (free_vars R1)
           # !LIn x (free_vars R2)
           # !LIn y (free_vars R2)
           # !LIn z (free_vars R2)
           # !LIn u (free_vars R2)
           # !LIn v (free_vars R2)
           # !LIn x (vars_hyps H)
           # !LIn y (vars_hyps H)
           # !LIn z (vars_hyps H)
           # !x = y
           # !x = z
           # !y = z) as vhyps.

  clear hyp1 hyp2 hyp3 hypmem0.
  dwfseq.
  sp.

  destruct vhyps as [ nixr1 vhyps ].
  destruct vhyps as [ niyr1 vhyps ].
  destruct vhyps as [ nizr1 vhyps ].
  destruct vhyps as [ niur1 vhyps ].
  destruct vhyps as [ nivr1 vhyps ].
  destruct vhyps as [ nixr2 vhyps ].
  destruct vhyps as [ niyr2 vhyps ].
  destruct vhyps as [ nizr2 vhyps ].
  destruct vhyps as [ niur2 vhyps ].
  destruct vhyps as [ nivr2 vhyps ].
  destruct vhyps as [ nixh vhyps ].
  destruct vhyps as [ niyh vhyps ].
  destruct vhyps as [ nizh vhyps ].
  destruct vhyps as [ nxy vhyps ].
  destruct vhyps as [ nxz nyz ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality
                lib (mk_uni i) (mk_ipertype R1) (mk_ipertype R2) s1 s2 H
                wT w1 w2 c1 c4 c2 c5 cT cT0
                eqh sim);
    intro k; repeat (autodimp k hyp); lsubst_tac; auto; try (apply @tequality_mkc_uni).

  clear dependent s1; clear dependent s2.
  introv hf sim; lsubst_tac.

  assert (cover_vars R1 s2)
    as cvr12
      by (apply cover_vars_change_sub with (sub1 := s1); auto;
          allapply @similarity_dom; repnd; allrw; sp).

  assert (cover_vars R2 s1)
    as cvr21
      by (apply cover_vars_change_sub with (sub1 := s2); auto;
          allapply @similarity_dom; repnd; allrw; sp).

  generalize (membership_apply2_eq
                lib H R1 R2 x y i s1 s2 w0 w3
                c1 cvr12 cvr21 c0 (wfh2, (wfct2, wfce), (ct1, ce1))
                hyp1 hf sim);
    introv fty.
  repeat (autodimp fty hyp).

  repeat (rw @mkc_ipertype_equality_in_uni); dands.

  introv.
  generalize (fty x0 y0); intro k; repnd.
  apply equality_commutes in k0; auto.

  allunfold @is_per_type; repnd; dands.

  generalize (is_sym_type
                lib R1 H i x y z e1 s1 s2 w0 c1
                wc' (wfh1, (wfct1, wfce1), (ct0, ce0))).
  intro j; repeat (destimp j hyp).

  generalize (is_trans_type
                lib R1 H i x y z u v e2 s1 s2 w0 c1
                wc' (wfh0, (wfct0, wfce0), (ct, ce))).
  intro j; repeat (destimp j hyp).
Qed.

(* begin hide *)




(* end hide *)

(* [20] ============ IPERTYPE ELIMINATION 2 ============ *)

(**

  Let us now provide another ipertype elimination rule.  This version
  is stated in terms of a ipertype hypothesis and not an equality in a
  ipertype:

<<
   H, x : ipertype(R), J |- C ext e

     By ipertypeElimination i z

     H, x : ipertype(R), [z : R x x], J |- C ext e
     H, x : ipertype(R) |- R x x in Type(i)
>>
 *)

Definition rule_ipertype_elimination2 {o}
           (R C e : NTerm)
           (x z : NVar)
           (i : nat)
           (H J : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x (mk_ipertype R)) ++ J)
       (mk_concl C e))
    [ mk_baresequent
        (snoc (snoc H (mk_hyp x (mk_ipertype R)))
              (mk_hhyp z (mk_apply2 R (mk_var x) (mk_var x)))
              ++ J)
        (mk_concl C e),
      mk_baresequent
        (snoc H (mk_hyp x (mk_ipertype R)))
        (mk_conclax (mk_member
                       (mk_apply2 R (mk_var x) (mk_var x))
                       (mk_uni i)))
    ]
    [sarg_var z].

Lemma rule_ipertype_elimination2_true {o} :
  forall lib (R C e : NTerm),
  forall x z : NVar,
  forall i : nat,
  forall H J : @barehypotheses o,
    rule_true lib (rule_ipertype_elimination2
                 R C e
                 x z
                 i
                 H J).
Proof.
  unfold rule_ipertype_elimination2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1; rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (covered e (nh_vars_hyps (snoc H (mk_hyp x (mk_ipertype R)) ++ J))) as cs.
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
  rw @equality_in_mkc_ipertype in sim2; repnd.
  rw @equality_in_mkc_ipertype in simt1; repnd.

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
  exists (snoc s1a (x, t4)) (snoc s2a1 (x, t5)) t0 t3 w0 p0 cv;
    dands; try (complete sp).

  lsubst_tac.

  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s1a (x,t4)) (snoc s2a1 (x,t5))); clear hyp2; intro hyp2.
  repeat (autodimp hyp2 hyp); exrepnd.

  apply hyps_functionality_init_seg with (s3 := s2b) in eqh; sp.

  lsubst_tac.
  apply @tequality_in_uni_implies_tequality with (i := i); sp.
  eapply member_if_inhabited. exact hyp1.

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

(* begin hide *)

Lemma rule_ipertype_elimination2_true_ex {o} :
  forall lib i z R C e x H J,
    rule_true_if lib (@rule_ipertype_elimination2 o
                 R C e
                 x z
                 i
                 H J).
Proof.
  intros.
  generalize (rule_ipertype_elimination2_true lib R C e x z i H J); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.




(* end hide *)

(* [21] ============ IPERTYPE ELIMINATION 3 ============ *)

(**

  We state yet another ipertype elimination rule.  This one is similar
  to the second one presented above but does not require us to provide
  a level for [R x x]:

<<
   H, x : ipertype(R), J |- C ext e

     By ipertypeElimination i z

     H, x : ipertype(R), [z : R x x], J |- C ext e
     H, x : ipertype(R) |- (R x x) is a type
>>
 *)

Definition rule_ipertype_elimination3 {o}
           (R C e : NTerm)
           (x z : NVar)
           (H J : @barehypotheses o) :=
  mk_rule
    (mk_baresequent (snoc H (mk_hyp x (mk_ipertype R)) ++ J)
                   (mk_concl C e))
    [ mk_baresequent (snoc (snoc H (mk_hyp x (mk_ipertype R)))
                          (mk_hhyp z (mk_apply2 R (mk_var x) (mk_var x)))
                          ++ J)
                   (mk_concl C e),
      mk_baresequent (snoc H (mk_hyp x (mk_ipertype R)))
                    (mk_concl_t (mk_apply2 R (mk_var x) (mk_var x)))
    ]
    [sarg_var z].

Lemma rule_ipertype_elimination3_true {o} :
  forall lib (R C e : NTerm),
  forall x z : NVar,
  forall H J : @barehypotheses o,
    rule_true lib (rule_ipertype_elimination3
                 R C e
                 x z
                 H J).
Proof.
  unfold rule_ipertype_elimination3, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent
                      (snoc (snoc H (mk_hyp x (mk_ipertype R)))
                            (mk_hhyp z (mk_apply2 R (mk_var x) (mk_var x))) ++ J)
                      (mk_concl C e))
                   (inl eq_refl))
             (hyps (mk_baresequent
                      (snoc H (mk_hyp x (mk_ipertype R)))
                      (mk_concl_t (mk_apply2 R (mk_var x) (mk_var x))))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (covered e (nh_vars_hyps (snoc H (mk_hyp x (mk_ipertype R)) ++ J))) as cs.
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

  destruct vhyps as [ nixr  vhyps ].
  destruct vhyps as [ nixh  vhyps ].
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

  applydup @equality_refl in sim2 as simt1.
  rw @equality_in_mkc_ipertype in sim2; repnd.
  rw @equality_in_mkc_ipertype in simt1; repnd.

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

(* begin hide *)

Lemma rule_ipertype_elimination3_true_ex {o} :
  forall lib z R C e x H J,
    rule_true_if lib (@rule_ipertype_elimination3 o
                 R C e
                 x z
                 H J).
Proof.
  intros.
  generalize (rule_ipertype_elimination3_true lib R C e x z H J); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

(* end hide *)


(* [21] ============ IPERTYPE ELIMINATION 4 ============ *)

(**

  We state yet another ipertype elimination rule.  This one is similar
  to the third one presented above but [R x x] is now the last hypothesis
  in the first subgoal:

<<
   H, x : ipertype(R), J |- C ext e

     By ipertypeElimination i z

     H, x : ipertype(R), J, [z : R x x] |- C ext e
     H, x : ipertype(R) |- (R x x) is a type
>>
 *)

Definition rule_ipertype_elimination4 {o}
           (R C e : NTerm)
           (x z : NVar)
           (H J : @barehypotheses o) :=
  mk_rule
    (mk_baresequent (snoc H (mk_hyp x (mk_ipertype R)) ++ J)
                   (mk_concl C e))
    [ mk_baresequent (snoc ((snoc H (mk_hyp x (mk_ipertype R))) ++ J)
                           (mk_hhyp z (mk_apply2 R (mk_var x) (mk_var x))))
                   (mk_concl C e),
      mk_baresequent (snoc H (mk_hyp x (mk_ipertype R)))
                    (mk_concl_t (mk_apply2 R (mk_var x) (mk_var x)))
    ]
    [sarg_var z].

Lemma rule_ipertype_elimination4_true {o} :
  forall lib (R C e : NTerm),
  forall x z : NVar,
  forall H J : @barehypotheses o,
    rule_true lib (rule_ipertype_elimination4
                 R C e
                 x z
                 H J).
Proof.
  unfold rule_ipertype_elimination4, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (covered e (nh_vars_hyps (snoc H (mk_hyp x (mk_ipertype R)) ++ J))) as cs.
  clear hyp1 hyp2.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  assert (!LIn x (free_vars R)
           # disjoint (free_vars R) (vars_hyps J)
           # !LIn x (vars_hyps H)
           # !LIn x (vars_hyps J)
           # !LIn z (free_vars C)
           # !LIn z (free_vars e)
           # !LIn z (hyps_free_vars J)
           # !LIn z (free_vars_hyps J)
           # !LIn z (vars_hyps J)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp;
    try (complete (allunfold @disjoint; discover; allrw in_app_iff; allrw in_snoc; sp));
    try (complete (generalize (wg9 x); allrw remove_nvars_nil_l; allrw app_nil_r; sp));
    try (complete (generalize (wfh3 z); allrw in_snoc; sp));
    try (complete (generalize (wfh6 z); allrw in_snoc; sp));
    try (complete (generalize (cg z); allrw in_app_iff; allrw in_snoc; sp));
    try (complete (generalize (wfh z); allrw in_app_iff; allrw in_snoc; sp));
    try (complete (generalize (ce0 z); allrw @nh_vars_hyps_app; allrw @nh_vars_hyps_snoc;
                   allsimpl; allrw in_app_iff; allrw in_snoc; sp;
                   generalize (subvars_hs_vars_hyps H); intros;
                   generalize (subvars_hs_vars_hyps J); intros;
                   allrw subvars_prop; apply_in_hyp p; sp));
    try (complete (unfold disjoint; unfold disjoint in wfh11; introv k;
                   discover; auto)).

  destruct vhyps as [ nixr vhyps ].
  destruct vhyps as [ disjRJ vhyps ].
  destruct vhyps as [ nixh vhyps ].
  destruct vhyps as [ nixj vhyps ].
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
  rw @equality_in_mkc_ipertype in sim2; repnd.
  rw @equality_in_mkc_ipertype in simt1; repnd.

  vr_seq_true in hyp1.
  unfold inhabited_type in sim0; exrepnd.
  unfold inhabited_type in simt0; destruct simt0 as [t' simt0].
  generalize (hyp1 (snoc (snoc s1a0 (x, t1) ++ s1b) (z, t'))
                   (snoc (snoc s2a0 (x, t2) ++ s2b) (z, t')));
    clear hyp1; intro hyp1.
  repeat (autodimp hyp1 hyp); exrepnd.

  (* hyps_functionality *)
  introv sim.
  rw @similarity_snoc in sim; simpl in sim; exrepnd; subst; cpx.
  rw @similarity_app in sim10; simpl in sim10; exrepnd; subst; cpx.
  apply app_split in sim0; repnd; subst; repeat (rw length_snoc);
  try (complete (allrw; sp)).
  lsubst_tac.
  generalize (eqh (s2a1 ++ s2b0)); intro j.
  autodimp j hyp.

  rw @similarity_app; simpl.
  exists (snoc s1a0 (x, t1)) s1b0 s2a1 s2b0; repeat (rw length_snoc); sp.

  rw @eq_hyps_app in j; simpl in j; exrepnd; allrw length_snoc.
  apply app_split in j0; repnd; subst; repeat (rw length_snoc);
  try (complete (allrw; sp)).
  apply app_split in j2; repnd; subst; repeat (rw length_snoc);
  try (complete (allrw; sp)).

  duplicate j5 as dup_eqhyps_snoc.
  rw @eq_hyps_snoc in j5; simpl in j5; exrepnd; subst; cpx.
  lsubst_tac.

  assert (cover_vars (mk_apply2 R (mk_var x) (mk_var x))
                     (snoc s2a1 (x,t5) ++ s2b1))
    as cv
      by (apply cover_vars_apply2; sp;
          try (apply cover_vars_var);
          try (apply cover_vars_app_weak);
          repeat (apply cover_vars_snoc_weak); sp;
          repeat (rw @dom_csub_app); simpl;
          repeat (rw @dom_csub_snoc); simpl;
          repeat (rw in_app_iff);
          repeat (rw in_snoc); sp).

  rw @eq_hyps_snoc; simpl.
  exists (snoc s1a (x,t4) ++ s1b) (snoc s2a1 (x,t5) ++ s2b1) t0 t3
         wfct0 p0 cv; repeat (rw length_snoc); dands; try (complete sp).

  rw @eq_hyps_app; simpl.
  exists (snoc s1a (x, t4))
         s1b
         (snoc s2a1 (x, t5))
         s2b1; repeat (rw length_snoc); dands; try (complete sp).

  lsubst_tac.

rw @tequality_mkc_ipertype in j0; repnd.

  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s1a (x,t4)) (snoc s2a1 (x,t5))); clear hyp2; intro hyp2.
  repeat (autodimp hyp2 hyp); exrepnd.

  apply hyps_functionality_init_seg with (s3 := s2b) in eqh; sp.

  lsubst_tac; sp.

  (* similarity *)
  assert (cover_vars (mk_apply2 R (mk_var x) (mk_var x)) (snoc s1a0 (x,t1) ++s1b))
         as cvap
           by (rw @cover_vars_apply2; sp;
               try (complete (apply cover_vars_app_weak; apply cover_vars_snoc_weak; sp));
               apply cover_vars_var; rw @dom_csub_app; rw @dom_csub_snoc; simpl; rw in_app_iff; rw in_snoc; sp).

  rw @similarity_snoc; simpl.
  exists (snoc s1a0 (x,t1) ++ s1b) (snoc s2a0 (x,t2) ++ s2b) t' t'
         wfct0 cvap; sp.

  rw @similarity_app; simpl.
  exists (snoc s1a0 (x, t1))
         s1b
         (snoc s2a0 (x, t2))
         s2b; repeat (rw length_snoc); sp.

  lsubst_tac.
  rw @member_eq; sp.
  (* similarity proved *)

  lsubst_tac.
  sp.
Qed.

(* begin hide *)

Lemma rule_ipertype_elimination4_true_ex {o} :
  forall lib z R C e x H J,
    rule_true_if lib (@rule_ipertype_elimination4 o
                 R C e
                 x z
                 H J).
Proof.
  intros.
  generalize (rule_ipertype_elimination4_true lib R C e x z H J); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

(* end hide *)