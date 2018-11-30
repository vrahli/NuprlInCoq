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


Require Export sequents2.
Require Export sequents_lib.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export sequents_equality.
Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_isect.
Require Export rules_tyfam.
Require Export rules_tyfam2.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export lsubstc_weak.
Require Export rules_elimination.


Hint Rewrite @nh_vars_hyps_app : slow.
Hint Rewrite @nh_vars_hyps_snoc : slow.


(**

<<

   H |- t1 = t2 in isect(x:A;B)

     By isect_memberEquality lvl(i) z ()

     H z : A |- t1 = t2 in B[x\z]
     H |- A = A in Type(i)
>>
 *)

Definition rule_isect_member_equality_concl {o} (H : @bhyps o) t1 t2 A x B :=
  mk_baresequent H (mk_conclax (mk_equality t1 t2 (mk_isect A x B))).

Definition rule_isect_member_equality_hyp1 {o} (H : @bhyps o) z A t1 t2 B x e1 :=
  mk_baresequent
    (snoc H (mk_hyp z A))
    (mk_concl (mk_equality t1 t2 (subst B x (mk_var z))) e1).

Definition rule_isect_member_equality_hyp2 {o} (H : @bhyps o) A i e2 :=
  mk_baresequent H (mk_concl (mk_equality A A (mk_uni i)) e2).

Definition rule_isect_member_equality {o}
           (A B t1 t2 e1 e2 : NTerm)
           (x z : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (rule_isect_member_equality_concl H t1 t2 A x B)
    [ rule_isect_member_equality_hyp1 H z A t1 t2 B x e1,
      rule_isect_member_equality_hyp2 H A i e2 ]
    [].

Lemma rule_isect_member_equality_true3 {o} :
  forall lib (A B t1 t2 e1 e2 : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o),
    rule_true3 lib (rule_isect_member_equality A B t1 t2 e1 e2 x z i H).
Proof.
  intros.
  unfold rule_isect_member_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  rename Hyp0 into hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    prove_seq; eauto 3 with slow.
  }
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars t1)
          # !LIn z (free_vars t2)
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)) as vhyps.

  {
    clear hyp1 hyp2.
    dwfseq.
    sp;
      try (complete (pose proof (wfc1 z) as q; allrw in_remove_nvars;
                     allrw in_single_iff; autodimp q hyp)).
  }

  destruct vhyps as [ nzB  vhyps ].
  destruct vhyps as [ nzt1 vhyps ].
  destruct vhyps as [ nzt2 vhyps ].
  destruct vhyps as [ nzA nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.
  allrw <- @member_equality_iff.
  teq_and_eq (mk_isect A x B) t1 t2 s1 s2 H.

  - apply tequality_isect; dands.

    + vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 eqh sim) as hyp2; exrepnd.
      lsubst_tac.
      apply equality_in_mkc_equality in hyp2; repnd.
      apply equality_commutes2 in hyp0; auto.
      apply equality_in_uni in hyp0; auto.

    + introv eqa.

      vr_seq_true in hyp1.
      pose proof (hyp1 (snoc s1 (z,a)) (snoc s2 (z,a'))) as hyp1.
      repeat (autodimp hyp1 xxx).

      {
        apply hyps_functionality_snoc2; simpl; auto.
        introv equ sim'.

        vr_seq_true in hyp2.
        pose proof (hyp2 s1 s' eqh sim') as hyp2; exrepnd.
        lsubst_tac.
        apply equality_in_mkc_equality in hyp1; repnd.
        apply equality_commutes2 in hyp0; auto.
        apply equality_in_uni in hyp0; auto.
      }

      {
        sim_snoc; dands; auto.
      }

      exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality in hyp0; repnd.
      clear hyp0 hyp4.

      assert (cover_vars (mk_var z) (snoc s1 (z, a))) as covz1.
      { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

      assert (cover_vars (mk_var z) (snoc s2 (z, a'))) as covz2.
      { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

      repeat (lsubstc_subst_aeq2;[]).
      repeat (substc_lsubstc_vars3;[]).

      revert c13 c14 hyp3.
      lsubst_tac.
      introv t.
      repeat (lsubstc_snoc2;[]).
      clear_irr.
      auto.

  - apply equality_in_isect2; dands.

    + vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as hyp2; exrepnd.
      lsubst_tac.
      apply equality_in_mkc_equality in hyp2; repnd.
      apply equality_commutes2 in hyp0; auto.
      apply equality_in_uni in hyp0; auto.
      eapply tequality_trans;[eauto|]; apply tequality_sym; auto.

    + introv eqa.

      dands.

      * vr_seq_true in hyp1.
        pose proof (hyp1 (snoc s1 (z,a)) (snoc s2 (z,a'))) as hyp1.
        repeat (autodimp hyp1 xxx).

        {
          apply hyps_functionality_snoc2; simpl; auto.
          introv equ sim'.

          vr_seq_true in hyp2.
          pose proof (hyp2 s1 s' hf sim') as hyp2; exrepnd.
          lsubst_tac.
          apply equality_in_mkc_equality in hyp1; repnd.
          apply equality_commutes2 in hyp0; auto.
          apply equality_in_uni in hyp0; auto.
        }

        {
          sim_snoc; dands; auto.
        }

        exrepnd.
        lsubst_tac.

        apply equality_in_mkc_equality in hyp1; repnd.
        clear hyp1 hyp4.

        apply equality_commutes4 in hyp0; auto.
        clear hyp3.

        assert (cover_vars (mk_var z) (snoc s1 (z, a))) as covz1.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

        assert (cover_vars (mk_var z) (snoc s2 (z, a'))) as covz2.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

        repeat (lsubstc_subst_aeq2;[]).
        repeat (substc_lsubstc_vars3;[]).

        revert c8 hyp0.
        lsubst_tac.
        introv t.
        repeat (lsubstc_snoc2;[]).
        clear_irr.
        auto.

      * vr_seq_true in hyp1.
        pose proof (hyp1 (snoc s1 (z,a)) (snoc s1 (z,a'))) as hyp1.
        repeat (autodimp hyp1 xxx).

        {
          apply hyps_functionality_snoc2; simpl; auto.
          introv equ sim'.

          vr_seq_true in hyp2.
          pose proof (hyp2 s1 s' hf sim') as hyp2; exrepnd.
          lsubst_tac.
          apply equality_in_mkc_equality in hyp1; repnd.
          apply equality_commutes2 in hyp0; auto.
          apply equality_in_uni in hyp0; auto.
        }

        {
          sim_snoc; dands; auto.
          eapply similarity_refl; eauto.
        }

        exrepnd.
        lsubst_tac.

        apply tequality_mkc_equality in hyp0; repnd.
        clear hyp0 hyp4.

        assert (cover_vars (mk_var z) (snoc s1 (z, a))) as covz1.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

        assert (cover_vars (mk_var z) (snoc s1 (z, a'))) as covz2.
        { apply cover_vars_var; rw @dom_csub_snoc; simpl; apply in_snoc; tcsp. }

        repeat (lsubstc_subst_aeq2;[]).
        repeat (substc_lsubstc_vars3;[]).

        revert c8 c9 hyp3.
        lsubst_tac.
        introv t.
        repeat (lsubstc_snoc2;[]).
        clear_irr.
        auto.
Qed.

Lemma rule_isect_member_equality_true_ext_lib {o} :
  forall lib (A B t1 t2 e1 e2 : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o),
    rule_true_ext_lib lib (rule_isect_member_equality A B t1 t2 e1 e2 x z i H).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_isect_member_equality_true3.
Qed.

Lemma rule_isect_member_equality_wf2 {o} :
  forall (A B t1 t2 e1 e2 : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o),
    !LIn z (vars_hyps H)
    -> wf_rule2 (rule_isect_member_equality A B t1 t2 e1 e2 x z i H).
Proof.
  introv nizH  wf j; allsimpl; repndors; subst; tcsp;
    allunfold @wf_bseq; repnd; allsimpl; wfseq;
      allrw @covered_isect; repnd; auto;
        allrw <- @wf_isect_iff; repnd; auto.

  - allrw @vswf_hypotheses_nil_eq.
    allrw @wf_hypotheses_snoc.
    dands; auto; simpl.
    apply isprog_vars_iff_covered; dands; auto.

  - apply wf_term_subst; eauto 2 with slow.

  - apply covered_snoc_weak; auto.

  - apply covered_snoc_weak; auto.

  - apply covered_subst; auto.

    + rewrite cons_snoc.
      apply covered_snoc_weak; auto.

    + apply covered_var; rw in_snoc; tcsp.
Qed.
