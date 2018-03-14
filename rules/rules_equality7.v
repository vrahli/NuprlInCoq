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

  Authors: Vincent Rahli

*)


Require Export sequents2.
Require Export sequents_tacs2.
Require Export sequents_equality.
Require Export per_props_uni.



(*
   H, x : A, J |- C ext t

     By hyp_replacement

     H, x : B, J |- C ext t
     H |- A = B in Type(i)
 *)
Definition rule_hyp_replacement {o}
           (H J : @bhyps o)
           (A B C t : NTerm)
           (x : NVar)
           (i : nat) :=
  mk_rule
    (mk_baresequent (snoc H (mk_hyp x A) ++ J) (mk_concl C t))
    [
      mk_baresequent (snoc H (mk_hyp x B) ++ J) (mk_concl C t),
      mk_baresequent H (mk_conclax (mk_equality A B (mk_uni i)))
    ]
    [].

Lemma rule_hyp_replacement_true3 {o} :
  forall lib (H J : @bhyps o) A B C t x i,
    rule_true3 lib (rule_hyp_replacement H J A B C t x i).
Proof.
  intros.
  unfold rule_hyp_replacement, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
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
    rw @vswf_hypotheses_nil_eq; dands; auto.
    dwfseq.
    dands; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  assert
    (
      (wf_term A)
        # wf_term B
        # covered A (vars_hyps H)
        # covered B (vars_hyps H)
    ) as vhyps.
  {
    clear hyp1 hyp2.
    dwfseq.
    sp.
  }

  destruct vhyps as [ wfA vhyps ].
  destruct vhyps as [ wfB vhyps ].
  destruct vhyps as [ covA covB ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2) as h; clear hyp1; exrepnd.

  apply similarity_app in sim; exrepnd; subst; allrw length_snoc.
  apply similarity_snoc in sim5; exrepnd; subst; cpx; allsimpl.
  ginv.

  repeat (autodimp h hyp);[| |exrepnd; clear_irr; auto];[|].

  {
    introv sim'.

    pose proof (eqh s') as eqh'.

    apply similarity_app in sim'; exrepnd; subst; allrw length_snoc.
    apply app_split in sim'0; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
    apply similarity_snoc in sim'5; exrepnd; subst; allrw length_snoc; cpx; allsimpl; GC.
    ginv.

    autodimp eqh' hyp.

    {
      apply similarity_app.
      eexists; eexists; eexists; eexists; dands;
        [eauto|eauto| | | |]; allrw length_snoc; auto.
      sim_snoc2; auto; dands; auto.

      vr_seq_true in hyp2.
      pose proof (hyp2 s1a s2a0) as h; clear hyp2.
      repeat (autodimp h hyp).
      { eapply hyps_functionality_init_seg in eqh;[|eauto].
        eapply hyps_functionality_init_seg_snoc2 in eqh;[auto|]; eauto. }
      exrepnd.
      lsubst_tac.
      apply member_equality_iff in h1.
      apply equality_in_uni in h1.
      eapply tequality_preserving_equality;try (apply tequality_sym); eauto.
    }

    rw @eq_hyps_app in eqh'; exrepnd; allrw length_snoc.
    apply app_split in eqh'0; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
    apply app_split in eqh'2; exrepd; allrw length_snoc; try (complete (allrw; sp)); subst; cpx.
    apply eq_hyps_snoc in eqh'5; exrepnd; cpx; allsimpl; GC; ginv.

    apply eq_hyps_app.
    eexists; eexists; eexists; eexists; dands;
      [eauto|eauto| | | |]; simpl; allrw length_snoc; auto.

    apply eq_hyps_snoc; simpl.
    assert (cover_vars B s2a) as cov2.
    { eapply similarity_cover_vars; eauto. }
    exists s1a0 s2a t1 t4 w0 p0 cov2; dands; auto.

    vr_seq_true in hyp2.
    pose proof (hyp2 s1a0 s2a) as h; clear hyp2.
    repeat (autodimp h hyp).
    { eapply hyps_functionality_init_seg in eqh;[|eauto].
      eapply hyps_functionality_init_seg_snoc2 in eqh;[auto|]; eauto. }
    exrepnd.
    lsubst_tac.
    apply member_equality_iff in h1.
    apply equality_in_universe in h0; auto.
    apply equality_in_uni in h1.
    eapply tequality_trans;[apply tequality_sym;eauto|].
    eapply tequality_trans;[exact eqh'0|];auto.
  }

  {
    apply similarity_app.
    eexists; eexists; eexists; eexists;dands;
      [eauto|eauto| | | |]; allrw length_snoc; auto.
    assert (cover_vars B s1a0) as cov2.
    { eapply s_cover_typ1;eauto. }
    sim_snoc2; dands; auto.

    vr_seq_true in hyp2.
    pose proof (hyp2 s1a0 s2a0) as h; clear hyp2.
    repeat (autodimp h hyp).
    { eapply hyps_functionality_init_seg in eqh;[|eauto].
      eapply hyps_functionality_init_seg_snoc2 in eqh;[auto|]; eauto. }
    exrepnd.
    lsubst_tac.
    apply member_equality_iff in h1.
    apply equality_in_uni in h1.
    eapply tequality_preserving_equality;eauto.
  }
Qed.
