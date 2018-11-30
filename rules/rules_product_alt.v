(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Export rules_product.
Require Export rules_typehood.


(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)

(* begin hide *)


(* end hide *)


(* [23] ============ PAIR FORMATION (ALT) ============ *)

(**

<<
   H |- x:A * B ext <a,b>

     By pairFormation_alt s z ()

     H |- a in A
     H |- B[x\a] ext b
     H, z : A |- istype(B[x\z])
>>

 *)

Definition rule_pair_formation_alt {p}
           (A B a b : NTerm)
           (x z  : NVar)
           (H    : @barehypotheses p) :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_product A x B) (mk_pair a b)))
    [ mk_baresequent H (mk_conclax (mk_member a A)),
      mk_baresequent H (mk_concl (subst B x a) b),
      mk_baresequent (snoc H (mk_hyp z A))
                     (mk_conclax (mk_istype (subst B x (mk_var z)))) ]
    [sarg_var z, sarg_term a].


Lemma rule_pair_formation_alt_true {p} :
  forall lib (A B a b : NTerm)
         (x z : NVar)
         (H   : @barehypotheses p),
    rule_true lib (rule_pair_formation_alt A B a b x z H).
Proof.
  intros.
  unfold rule_pair_formation_alt, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs; allsimpl.
  pose proof (cargs (sarg_var z)) as arg1; autodimp arg1 hyp.
  pose proof (cargs (sarg_term a)) as arg2; autodimp arg2 hyp.
  clear cargs.
  allunfold @arg_constraints; GC.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_concl (mk_product A x B) (mk_pair a b))) as cp.
  { clear hyp1 hyp2 hyp3.
    unfold closed_extract; simpl.
    allunfold @covered; allsimpl.
    autorewrite with slow core in *.
    allrw subvars_app_l; repnd; dands; auto. }

  exists cp; GC.

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)) as vhyps.

  { clear hyp1 hyp2 hyp3.
    dwfseq.
    autorewrite with slow core in *.
    sp;
      try (complete (assert (LIn z (remove_nvars [x] (free_vars B)))
                      as j by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; tcsp)). }

  destruct vhyps as [ nzB vhyps ].
  destruct vhyps as [ nzA nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.

  assert (forall s3,
            similarity lib s1 s3 H
            -> {ca3 : cover_vars A s3
                & {cb3 : cover_vars_upto B (csub_filter s3 [x]) [x]
                & tequality
                    lib
                    (mkc_product (lsubstc A w1 s1 c1) x
                                 (lsubstc_vars B w2 (csub_filter s1 [x]) [x] c2))
                    (mkc_product (lsubstc A w1 s3 ca3) x
                                 (lsubstc_vars B w2 (csub_filter s3 [x]) [x] cb3)) }}) as teq.

  { introv sim'.
    dup sim' as ca3.
    eapply similarity_cover_vars in ca3;[|exact c1].
    dup sim' as cb3.
    eapply similarity_cover_vars_upto in cb3;[|exact c2].

    exists ca3 cb3.

    apply tequality_product; dands.

    + vr_seq_true in hyp1.
      pose proof (hyp1 s1 s3 eqh sim') as h; clear hyp1; exrepnd.
      lsubst_tac; proof_irr.
      clear h1.
      apply tequality_mkc_member in h0; repnd; auto.

    + intros a1 a2 ea.
      repeat (substc_lsubstc_vars3;[]).

      vr_seq_true in hyp3.
      pose proof (hyp3 (snoc s1 (z,a1)) (snoc s3 (z,a2))) as h; clear hyp3.
      repeat (autodimp h hyp).

      * apply hyps_functionality_snoc2; simpl; auto;[].
        introv equ sim''.

        vr_seq_true in hyp1.
        pose proof (hyp1 s1 s' eqh sim'') as h; clear hyp1; exrepnd.
        lsubst_tac; proof_irr.
        clear h1.
        apply tequality_mkc_member in h0; repnd; auto.

      * sim_snoc; dands; auto.

      * exrepnd.
        lsubst_tac; proof_irr.
        rw @tequality_mkc_istype in h0.
        rw @equality_axiom_in_mkc_istype in h1.
        
        assert (cover_vars (mk_var z) (snoc s1 (z, a1))) as cov1.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }
        assert (cover_vars (mk_var z) (snoc s3 (z, a2))) as cov2.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

        repeat lsubstc_subst_aeq.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        repeat (lsubstc_snoc2;[]).
        proof_irr; auto. }

  dands.

  { apply teq in sim; clear teq; exrepnd; proof_irr; auto. }

  apply equality_in_product; dands.

  { apply teq in sim; clear teq; exrepnd; proof_irr; auto.
    apply tequality_product in sim1; repnd.
    apply tequality_refl in sim0; auto. }

  { intros a1 a2 ea.
    repeat (substc_lsubstc_vars3;[]).
    apply similarity_refl in sim.
    apply teq in sim; clear teq; exrepnd; proof_irr.
    apply tequality_product in sim1; repnd; proof_irr.
    apply sim1 in ea; clear sim1.
    repeat (substc_lsubstc_vars3;[]).
    proof_irr; auto. }

  eexists; eexists; eexists; eexists; dands; spcast;
  try (complete (apply computes_to_valc_refl; eauto 3 with slow));[|].

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 eqh sim) as h; clear hyp1; exrepnd.
    lsubst_tac; proof_irr.
    apply tequality_mkc_member in h0; repnd.
    apply member_if_inhabited in h1.
    eapply equality_trans. exact h1. apply h0.
    apply equality_sym in h1. apply equality_refl in h1. auto. 
    
  - repeat (substc_lsubstc_vars3;[]).
    vr_seq_true in hyp2.
    pose proof (hyp2 s1 s2 eqh sim) as h; clear hyp2; exrepnd.

    repeat lsubstc_subst_aeq.
    repeat (substc_lsubstc_vars3;[]).
    proof_irr; auto.
Qed.

(* begin hide *)

Lemma rule_pair_formation_alt_true_ex {p} :
  forall lib  z A B a b x H,
    @rule_true_if p lib (rule_pair_formation_alt A B a b x z H).
Proof.
  intros.
  generalize (rule_pair_formation_alt_true lib A B a b x z  H); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.




(* ============ PAIR EQUALITY (ALT) ============ *)

(**

<<

   H |- <a1,b1> = <a2,b2> in x:A*B

     By pairEquality_alt z ()

     H |- a1 = a2 in A
     H |- b1 = b2 in B[x\a1]
     H, z : A |- istype(B[x\z])
>>
 *)

Definition rule_pair_equality_alt {o}
           (A B a1 a2 b1 b2 : NTerm)
           (x z : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_pair a1 b1)
                      (mk_pair a2 b2)
                      (mk_product A x B))))
    [ mk_baresequent H (mk_conclax (mk_equality a1 a2 A)),
      mk_baresequent H (mk_conclax (mk_equality b1 b2 (subst B x a1))),
      mk_baresequent
        (snoc H (mk_hyp z A))
        (mk_conclax (mk_istype
                       (subst B x (mk_var z))
                     )) ]
    [sarg_var z].

Lemma rule_pair_equality_alt_true {o} :
  forall lib (A B a1 a2 b1 b2 : NTerm)
         (x z : NVar)
         (H   : @barehypotheses o),
    rule_true lib (rule_pair_equality_alt A B a1 a2 b1 b2 x z H).
Proof.
  intros.
  unfold rule_pair_equality_alt, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)) as vhyps.

  { clear hyp1 hyp2 hyp3.
    dwfseq.
    autorewrite with slow core in *.
    sp;
      try (complete (assert (LIn z (remove_nvars [x] (free_vars B)))
                      as j by (rw in_remove_nvars; rw in_single_iff; sp);
                     discover; tcsp)). }

  destruct vhyps as [ nzB vhyps ].
  destruct vhyps as [ nzA nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.
  rw <- @member_equality_iff.

  assert (forall s1 s2,
            hyps_functionality lib s1 H ->
            similarity lib s1 s2 H
            -> {ca1 : cover_vars A s1
                & {cb1 : cover_vars_upto B (csub_filter s1 [x]) [x]
                & {ca2 : cover_vars A s2
                & {cb2 : cover_vars_upto B (csub_filter s2 [x]) [x]
                & tequality
                    lib
                    (mkc_product (lsubstc A w0 s1 ca1) x
                                 (lsubstc_vars B w3 (csub_filter s1 [x]) [x] cb1))
                    (mkc_product (lsubstc A w0 s2 ca2) x
                                 (lsubstc_vars B w3 (csub_filter s2 [x]) [x] cb2)) }}}}) as teq.

  { introv eqh' sim'.
    dup sim' as ca.
    eapply similarity_cover_vars2 in ca;[|exact sim|exact c4]; repnd; GC;[].
    dup sim' as cb.
    eapply similarity_cover_vars_upto2 in cb;[|exact sim|exact c5]; repnd; GC;[].

    exists ca1 cb1 ca cb.

    apply tequality_product; dands.

    + vr_seq_true in hyp1.
      pose proof (hyp1 s0 s3 eqh' sim') as h; clear hyp1; exrepnd.
      lsubst_tac; proof_irr.
      clear h1.
      apply tequality_mkc_equality in h0; repnd; auto.

    + intros a a' ea.
      repeat (substc_lsubstc_vars3;[]).

      vr_seq_true in hyp3.
      pose proof (hyp3 (snoc s0 (z,a)) (snoc s3 (z,a'))) as h; clear hyp3.
      repeat (autodimp h hyp).

      * apply hyps_functionality_snoc2; simpl; auto;[].
        introv equ sim''.

        vr_seq_true in hyp1.
        pose proof (hyp1 s0 s' eqh' sim'') as h; clear hyp1; exrepnd.
        lsubst_tac; proof_irr.
        clear h1.
        apply tequality_mkc_equality in h0; repnd; auto.

      * sim_snoc; dands; auto.

      * exrepnd.
        lsubst_tac; proof_irr.
        rw @tequality_mkc_istype in h0.
        assert (cover_vars (mk_var z) (snoc s0 (z, a))) as cov1.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }
        assert (cover_vars (mk_var z) (snoc s3 (z, a'))) as cov2.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; rw in_snoc; tcsp. }

        repeat lsubstc_subst_aeq.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        repeat (lsubstc_snoc2;[]).
        proof_irr; auto. }

  pose proof (teq_and_eq_if_equality
                lib (mk_product A x B) (mk_pair a1 b1) (mk_pair a2 b2)
                s1 s2 H wT w1 w2 c1 c0 c2 c3 cT cT0
                eqh sim) as eqp.
  repeat (autodimp eqp hyp); auto;
  [| |lsubst_tac; clear_irr; auto];[|].

  { lsubst_tac; clear_irr.
    apply teq in sim; clear teq; exrepnd; proof_irr; auto. }

  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.
  apply equality_in_product; dands.

  { apply teq in sim; clear teq; exrepnd; proof_irr; auto.
    apply tequality_product in sim1; repnd.
    apply tequality_refl in sim0; auto. }

  { intros a a' ea.
    repeat (substc_lsubstc_vars3;[]).
    apply similarity_refl in sim.
    apply teq in sim; auto; clear teq; exrepnd; proof_irr.
    apply tequality_product in sim1; repnd; proof_irr.
    apply sim1 in ea; clear sim1.
    repeat (substc_lsubstc_vars3;[]).
    proof_irr; auto. }

  eexists; eexists; eexists; eexists; dands; spcast;
  try (complete (apply computes_to_valc_refl; eauto 3 with slow));[|].

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac; proof_irr.
    apply tequality_mkc_equality in h0; repnd.
    rw <- @member_equality_iff in h1.
    eapply equality_trans. exact h1. apply h0.
    apply equality_sym in h1. apply equality_refl in h1. auto. 
    
  - repeat (substc_lsubstc_vars3;[]).
    vr_seq_true in hyp2.
    pose proof (hyp2 s1 s2 hf sim) as h; clear hyp2; exrepnd.
    lsubst_tac; proof_irr.
    apply tequality_mkc_equality in h0; repnd.
    rw <- @member_equality_iff in h1.
    allrw @fold_equorsq.
    clear h2.

    assert (cover_vars a1 s2) as cov.
    { eapply similarity_cover_vars in sim; eauto. }

    assert (equality lib (lsubstc b1 w5 s1 c3) (lsubstc b2 w7 s2 c5) (lsubstc (subst B x a1) wT0 s1 cT)).
    { eapply equality_trans. exact h1. apply h0. 
     apply equality_sym in h1; apply equality_refl in h1. auto. 
    }

    repeat lsubstc_subst_aeq.
    repeat (substc_lsubstc_vars3;[]).
    proof_irr; auto.

Qed.



  
    
