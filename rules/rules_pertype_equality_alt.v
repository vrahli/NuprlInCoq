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


Require Export rules_pertype_equality.
Require Export rules_typehood.




(**

  We now prove the truth of several rules about the PER type.

*)

(* [14] ============ PERTYPE MEMBER EQUALITY (ALT) ============ *)

(**

  The following rule is called the ``pertype member equality'' rule.
  It allows one to prove that terms are well-formed partial
  equivalence relations, i.e., members of a ``pertype'' type.

  The 3rd subgoal is necessary because we have to prove [R[s1] t1[s1] t2[s2]]
  is inhabited, but from the 2nd subgoal we only know that [R[s1] t1[s1] t2[s1]]
  is inhabited and that [R[s1] t1[s1] t2[s1]] and [R[s2] t1[s2] t2[s2]] are
  equal types.  Therefore, we need to go from [R[s1] t1[s1] t2[s2]] to either
  [R[s1] t1[s1] t2[s1]] or [R[s2] t1[s2] t2[s2]].
  For that we use the 1st subgoal which says that [R[s1] x y] is inhabited iff
  [R[s2] x y] is inhabited.  We now get that [R[s2] t1[s1] t2[s2]] is inhabited.
  Finally because t1[s1] ~ t1[s2] we get that [R[s2] t1[s2] t2[s2]] is inhabited.

<<
   H |- t1 = t2 in pertype(R)

     By pertypeMemberEquality 

     H |- istype(pertype(R))
     H |- R t1 t2
     H |- t1 in Base
>>
 *)


Definition rule_pertype_member_equality_alt {o}
           (t1 t2 R e : NTerm)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality t1 t2 (mk_pertype R))))
    [ mk_baresequent H (mk_conclax (mk_istype (mk_pertype R))),
      mk_baresequent H (mk_concl (mk_apply2 R t1 t2) e),
      mk_baresequent H (mk_conclax (mk_member t1 mk_base))
    ]
    [].

Lemma rule_pertype_member_equality_alt_true {o} :
  forall lib (t1 t2 R e : NTerm),
  forall H : @barehypotheses o,
    rule_true lib (rule_pertype_member_equality_alt
                 t1 t2 R e
                 H).
Proof.
  unfold rule_pertype_member_equality_alt, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hypa.
  rename Hyp1 into hypb.
  rename Hyp2 into hypc.
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

  vr_seq_true in hypa.
  pose proof (hypa s1 s2) as hypa'.
  repeat (autodimp hypa' hyp); exrepnd.
  lsubst_tac.
  rw @tequality_mkc_istype in hypa'0.
  
  generalize (teq_and_eq_if_equality lib
                (mk_pertype R) t1 t2 s1 s2 H wT w1 w2 c1 c3 c2 c4 cT cT0
                eqh sim); intro k; lsubst_tac; apply k; clear k; auto.

  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.

  pose proof (hypa s1 s2 hf sim) as hypa; exrepnd.

  vr_seq_true in hypb.
  pose proof (hypb s1 s2 hf sim) as hypb; exrepnd.

  vr_seq_true in hypc.
  pose proof (hypc s1 s2 hf sim) as hypc; exrepnd.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_member_iff.
  allrw @tequality_mkc_member_base.
  allapply @member_in_uni.

  (* trivial hyp *)
  clear hypc1.

  rw @tequality_mkc_istype in hypa0; auto.
  duplicate hypa0 as xx.
  apply tequality_implies_type_left in xx.
  rw @tequality_mkc_pertype in hypa0; repnd.
  allapply @inhabited_type_if_equality.
  spcast.

  rw @equality_in_mkc_pertype2; dands; auto.
  apply hypa4.
  apply @inhabited_type_cequivc with (a := mkc_apply2 (lsubstc R w0 s2 c0)
                                                      (lsubstc t1 w1 s2 ct2)
                                                      (lsubstc t2 w2 s2 cb2)); auto;
    [apply implies_cequivc_apply2; sp;apply cequivc_sym; auto|];[].
  apply @inhabited_type_tequality in hypb0; auto.
Qed.


(**

  This is a variant of [rule_pertype_elimination] but where the
  well-formedness goal is stated using a ``type'' sequent.  Also it
  allows one to use all the hypotheses:
<<
   H, x : t1 = t2 in pertype(R), J |- C ext e

     By pertypeElimination i z

     H, x : t1 = t2 in pertype(R), [z : R t1 t2], J |- C ext e
     H, x : t1 = t2 in pertype(R), J |- istype(R t1 t2)
>>
 *)

Definition rule_pertype_elimination_alt {o}
           (R t1 t2 C e : NTerm)
           (x z : NVar)
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
      mk_baresequent (snoc H (mk_hyp x (mk_equality t1 t2 (mk_pertype R))) ++ J)
                      (mk_conclax (mk_istype (mk_apply2 R t1 t2)))
    ]
    [sarg_var z].

Lemma rule_pertype_elimination_alt_true {o} :
  forall lib (R t1 t2 C e : NTerm),
  forall x z : NVar,
  forall H J : @barehypotheses o,
    rule_true lib (rule_pertype_elimination_alt
                 R t1 t2 C e
                 x z
                 H J).
Proof.
  unfold rule_pertype_elimination_alt, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
                     (snoc H (mk_hyp x (mk_equality t1 t2 (mk_pertype R))) ++ J))) as cs.
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
    try (complete (discover; repeat (first [ progress (allrw in_app_iff) | progress (allrw in_snoc) ]); sp));
    try (complete (generalize (ce0 z); allrw @nh_vars_hyps_app; allrw @nh_vars_hyps_snoc;
                   allsimpl; allrw in_app_iff; allrw in_snoc; sp;
                   generalize (subvars_hs_vars_hyps H); intros;
                   generalize (subvars_hs_vars_hyps J); intros;
                   allrw subvars_prop; apply_in_hyp p; sp));
    try (complete (unfold disjoint; unfold disjoint in wfh13; introv k l; discover;
                   repeat (first [ progress (allrw in_app_iff) | progress (allrw in_snoc) ]); sp));
    try (complete (allunfold @disjoint; introv k;
                   discover; allrw in_app_iff; allrw in_snoc; sp)).

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
  rw @equality_in_mkc_pertype in sim0; repnd.

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

  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s1a  (x, t6) ++ s1b)
                   (snoc s2a1 (x, t7) ++ s2b));
    clear hyp2; intro hyp2.
  repeat (autodimp hyp2 hyp); exrepnd.

  rw @similarity_app; simpl.
  exists (snoc s1a (x,t6)) s1b (snoc s2a1 (x,t7)) s2b; repeat (rw length_snoc); sp.
  lsubst_tac.
  auto.
  apply tequality_mkc_istype. auto.

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

Lemma rule_pertype_elimination_alt_true_ex {o} :
  forall lib z R t1 t2 C e x H J,
    rule_true_if lib (@rule_pertype_elimination_alt
                    o
                    R t1 t2 C e
                    x z
                    H J).
Proof.
  intros.
  generalize (rule_pertype_elimination_alt_true lib R t1 t2 C e x z H J); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.




