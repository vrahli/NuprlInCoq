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

  Authors: Vincent Rahli

*)


Require Export sequents2.
Require Export sequents_tacs2.
Require Export sequents_equality.
Require Export sequents_util.
Require Export rules_useful.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export rules_tyfam.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.



(*
   H |- (\x1.b1)a1 = (\x2.b2)a2 in B[x\a1]

     By applyLambdaEquality z A

     H, z : A |- b1[x1\z] = b2[x2\z] in B[x\z]
     H |- a1 = a2 in A
 *)
Definition rule_apply_lambda_equality {o}
           (H : @bhyps o)
           (a1 a2 b1 b2 A B : NTerm)
           (x1 x2 x z : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality
                                     (mk_apply (mk_lam x1 b1) a1)
                                     (mk_apply (mk_lam x2 b2) a2)
                                     (subst B x a1))))
    [
      mk_baresequent (snoc H (mk_hyp z A)) (mk_conclax (mk_equality
                                                          (subst b1 x1 (mk_var z))
                                                          (subst b2 x2 (mk_var z))
                                                          (subst B x (mk_var z)))),
      mk_baresequent H (mk_conclax (mk_equality a1 a2 A))
    ]
    [].

Lemma rule_apply_lambda_equality_true3 {o} :
  forall lib (H : @bhyps o) a1 a2 b1 b2 A B x1 x2 x z,
    rule_true3 lib (rule_apply_lambda_equality H a1 a2 b1 b2 A B x1 x2 x z).
Proof.
  intros.
  unfold rule_apply_lambda_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  { clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    rw @vswf_hypotheses_nil_eq; dands; auto. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  assert
    (
      (wf_term A)
        # covered A (vars_hyps H)
        # !LIn z (vars_hyps H)
        # (z <> x -> !LIn z (free_vars B))
        # (z <> x1 -> !LIn z (free_vars b1))
        # (z <> x2 -> !LIn z (free_vars b2))
    ) as vhyps.
  {
    clear hyp1 hyp2.
    dwfseq.
    sp;
      try (complete (pose proof (wfc1 z) as xx; autodimp xx hyp;
                     apply eqset_free_vars_disjoint; simpl;
                     apply in_app_iff; rw in_remove_nvars; rw in_single_iff; tcsp));
      try (complete (pose proof (wfc3 z) as xx; autodimp xx hyp;
                     apply in_remove_nvars; rw in_single_iff; tcsp));
      try (complete (pose proof (wfc4 z) as xx; autodimp xx hyp;
                     apply in_remove_nvars; rw in_single_iff; tcsp)).
  }

  destruct vhyps as [ wfA vhyps ].
  destruct vhyps as [ covA nizH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw <- @member_equality_iff.

  pose proof (teq_and_eq_if_equality
                lib'
                (subst B x a1)
                (mk_apply (mk_lam x1 b1) a1)
                (mk_apply (mk_lam x2 b2) a2)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT0) as h.
  lsubst_tac.
  apply h; auto; clear h.

  {

    (* proving tequality *)

    repeat lsubstc_subst_aeq2.
    proof_irr.

    vr_seq_true in hyp1.
    pose proof (hyp1
                  _ ext
                  (snoc s1 (z,lsubstc a1 w3 s1 c3))
                  (snoc s2 (z,lsubstc a1 w3 s2 c9)))
      as h; clear hyp1.
    repeat (autodimp h hyp).

    {

      (* proving hyps_functionality *)

      apply hyps_functionality_ext_snoc2; simpl; auto; [].
      introv ext' equ sim'.

      vr_seq_true in hyp2.
      pose proof (hyp2 _ (lib_extends_trans ext' ext) s1 s') as q.
      repeat (autodimp q hyp); eauto 3 with slow.
      exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in q0; sp.
    }

    {

      (* proving similarity *)

      assert (cover_vars A s1) as covAs1.
      { eapply s_cover_typ1; eauto. }
      sim_snoc2; dands; auto;[].

      vr_seq_true in hyp2.
      pose proof (hyp2 _ ext s1 s2 eqh sim) as q; clear hyp2.
      exrepnd.
      lsubst_tac.
      rw <- @member_equality_iff in q1.
      apply equality_commutes3 in q0; auto.
    }

    exrepnd.
    lsubst_tac.
    apply tequality_mkc_equality_sp in h0; repnd.
    clear h0 h1 h3.

    assert (!LIn z (dom_csub s1)) as nizs1.
    { apply similarity_dom in sim; repnd; allrw; auto. }

    repeat (lsubstc_subst_aeq2;
            try (apply cover_vars_var; rw @dom_csub_snoc; apply in_snoc; simpl; tcsp);
            []).
    lsubst_tac.
    proof_irr.

    pose proof (lsubstc_vars_csub_filter_snoc_ex
                  B wb s1 z (lsubstc a1 w3 s1 c3) [x] cb1) as q.
    rw in_single_iff in q; autodimp q hyp;[].
    exrepnd.
    rw q0 in h2; clear q0.

    pose proof (lsubstc_vars_csub_filter_snoc_ex
                  B wb s2 z (lsubstc a1 w3 s2 c9) [x] cb2) as q.
    rw in_single_iff in q; autodimp q hyp;[].
    exrepnd.
    rw q0 in h2; clear q0.

    proof_irr; auto.
  }

  {

    (* proving equality *)

    clear dependent s1.
    clear dependent s2.
    introv eqh sim.
    lsubst_tac.

    repeat betared2.
    repeat lsubstc_subst_aeq2.
    proof_irr.

    vr_seq_true in hyp1.
    pose proof (hyp1
                  _ ext
                  (snoc s1 (z,lsubstc a1 w3 s1 c2))
                  (snoc s2 (z,lsubstc a2 w5 s2 c3)))
      as h; clear hyp1.
    repeat (autodimp h hyp).

    {

      (* proving hyps_functionality *)

      apply hyps_functionality_ext_snoc2; simpl; auto; [].
      introv ext' equ sim'.

      vr_seq_true in hyp2.
      pose proof (hyp2 _ (lib_extends_trans ext' ext) s1 s') as q.
      repeat (autodimp q hyp); eauto 3 with slow.
      exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in q0; sp.
    }

    {

      (* proving similarity *)

      assert (cover_vars A s1) as covAs1.
      { eapply s_cover_typ1; eauto. }
      sim_snoc2; dands; auto;[].

      vr_seq_true in hyp2.
      pose proof (hyp2 _ ext s1 s2 eqh sim) as q; clear hyp2.
      exrepnd.
      lsubst_tac.
      rw <- @member_equality_iff in q1.
      apply equality_commutes4 in q0; auto.
    }

    exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in h1.
    apply equality_commutes4 in h0; auto;[].
    clear h1.

    assert (!LIn z (dom_csub s1)) as nizs1.
    { apply similarity_dom in sim; repnd; allrw; auto. }

    repeat (lsubstc_subst_aeq2;
            try (apply cover_vars_var; rw @dom_csub_snoc; apply in_snoc; simpl; tcsp);
            []).
    lsubst_tac.
    proof_irr.

    pose proof (lsubstc_vars_csub_filter_snoc_ex
                  b1 w6 s1 z (lsubstc a1 w3 s1 c2) [x1] cb0) as q.
    rw in_single_iff in q; autodimp q hyp;[].
    exrepnd.
    rw q0 in h0; clear q0.

    pose proof (lsubstc_vars_csub_filter_snoc_ex
                  b2 w7 s2 z (lsubstc a2 w5 s2 c3) [x2] cb1) as q.
    rw in_single_iff in q; autodimp q hyp;[].
    exrepnd.
    rw q0 in h0; clear q0.

    pose proof (lsubstc_vars_csub_filter_snoc_ex
                  B wb s1 z (lsubstc a1 w3 s1 c2) [x] cb3) as q.
    rw in_single_iff in q; autodimp q hyp;[].
    exrepnd.
    rw q0 in h0; clear q0.

    proof_irr; auto; eauto 3 with slow.
  }
Qed.
