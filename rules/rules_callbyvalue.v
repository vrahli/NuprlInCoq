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
Require Export per_props_cequiv3.
Require Export per_props_halts.


Lemma callbyvalue_reduce_c {o} :
  forall lib (a b t : @NTerm o) x ws s cs wt ct wa ca wb cb,
    cequivc lib (lsubstc (subst b x a) ws s cs) (lsubstc t wt s ct)
    -> hasvaluec lib (lsubstc a wa s ca)
    -> cequivc
         lib
         (mkc_cbv (lsubstc a wa s ca) x (lsubstc_vars b wb (csub_filter s [x]) [x] cb))
         (lsubstc t wt s ct).
Proof.
  introv ceq hv.
  unfold cequivc in ceq; simpl in ceq.
  unfold hasvaluec in hv; simpl in hv.
  unfold cequivc; simpl.

  eapply cequiv_trans;[|exact ceq]; clear ceq.
  unfold hasvalue in hv; exrepnd.
  rename t' into v.

  assert (reduces_to
            lib
            (mk_cbv (csubst a s) x (csubst b (csub_filter s [x])))
            (mk_cbv v x (csubst b (csub_filter s [x])))) as r.
  { apply reduces_to_prinarg; destruct hv0; auto. }

  eapply cequiv_trans;
    [apply reduces_to_implies_cequiv;
     [apply isprogram_cbv_iff2;dands;
      try (apply isprogram_csubst);eauto 3 with slow;
      apply isprog_vars_iff_isprogram_bt;
      apply isprog_vars_csubst; auto
     |exact r]
    |];
    clear r;[].

  destruct hv0 as [r isv].

  eapply cequiv_trans;
    [apply reduces_to_implies_cequiv;
     [apply isprogram_cbv_iff2;dands;
      try (apply isprogram_csubst);eauto 3 with slow;
      apply isvalue_implies in isv;tcsp;
      apply isprog_vars_iff_isprogram_bt;
      apply isprog_vars_csubst; auto
     |apply reduces_to_if_step;apply compute_step_cbv_iscan;eauto 3 with slow]
    |];[].

  pose proof (change_bvars_alpha_wspec (free_vars a) b) as q; exrepnd.
  rename ntcv into b'.

  eapply cequiv_rw_l_eauto;
    [apply alpha_eq_sym;apply lsubst_alpha_congr2;apply lsubst_alpha_congr2;exact q0|].
  eapply cequiv_rw_r_eauto;
    [apply alpha_eq_sym;apply lsubst_alpha_congr2;apply lsubst_alpha_congr2;exact q0|].

  allrw @fold_subst.
  allrw @fold_csubst.
  rewrite simple_csubst_subst; auto.

  apply cequiv_lsubst;
    allrw @fold_subst;
    allrw @fold_csubst.

  { apply isvalue_implies in isv; repnd.
    apply isprogram_subst_if_bt; eauto 3 with slow.
    apply isprog_vars_iff_isprogram_bt.
    apply isprog_vars_csubst; eauto 3 with slow.
    allunfold @cover_vars_upto.
    apply alphaeq_preserves_free_vars in q0; rewrite <- q0; auto. }

  { apply isvalue_implies in isv; repnd.
    apply isprogram_subst_if_bt; eauto 3 with slow;
      try (apply isprogram_csubst);eauto 3 with slow.
    apply isprog_vars_iff_isprogram_bt.
    apply isprog_vars_csubst; eauto 3 with slow.
    allunfold @cover_vars_upto.
    apply alphaeq_preserves_free_vars in q0; rewrite <- q0; auto. }

  constructor; auto.
  apply cequiv_sym.
  apply reduces_to_implies_cequiv; auto.
  apply isprogram_csubst;eauto 3 with slow.
Qed.


(*
   H |- let x = a in b ~ t

     By callbyvalueReduce

     H |- b[x\a] ~ t
     H |- halts(a)
 *)
Definition rule_callbyvalue_reduce {o}
           (H : @bhyps o)
           (a b t : NTerm)
           (x : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_cequiv (mk_cbv a x b) t)))
    [
      mk_baresequent H (mk_conclax (mk_cequiv (subst b x a) t)),
      mk_baresequent H (mk_conclax (mk_halts a))
    ]
    [].

Lemma rule_callbyvalue_reduce_true3 {o} :
  forall lib (H : @bhyps o) a b t x,
    rule_true3 lib (rule_callbyvalue_reduce H a b t x).
Proof.
  intros.
  unfold rule_callbyvalue_reduce, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw @equality_in_mkc_cequiv_ax.

  pose proof (teq_and_eq_if_cequiv lib (mk_cbv a x b) t s1 s2 H w1 w2 c1 c4 c2 c5) as h.
  lsubst_tac.
  apply h; auto; clear h.

  {
    vr_seq_true in hyp1.
    pose proof (hyp1 s1 s1) as h; clear hyp1.
    repeat (autodimp h hyp); auto.
    { eapply similarity_refl; eauto. }
    exrepnd; proof_irr.

    vr_seq_true in hyp2.
    pose proof (hyp2 s1 s1) as q; clear hyp2.
    repeat (autodimp q hyp); auto.
    { eapply similarity_refl; eauto. }
    exrepnd; proof_irr.

    clear q0 h0.

    lsubst_tac.
    apply equality_in_mkc_halts_ax in q1.
    apply equality_in_mkc_cequiv_ax in h1.
    spcast.

    eapply callbyvalue_reduce_c; eauto.
  }

  {
    vr_seq_true in hyp1.
    pose proof (hyp1 s2 s2) as h; clear hyp1.
    repeat (autodimp h hyp); auto.
    { eapply similarity_hyps_functionality_trans; eauto. }
    { apply similarity_sym in sim; auto; eapply similarity_refl; eauto. }
    exrepnd; proof_irr.

    vr_seq_true in hyp2.
    pose proof (hyp2 s2 s2) as q; clear hyp2.
    repeat (autodimp q hyp); auto.
    { eapply similarity_hyps_functionality_trans; eauto. }
    { apply similarity_sym in sim; auto; eapply similarity_refl; eauto. }
    exrepnd; proof_irr.

    clear q0 h0.

    lsubst_tac.
    apply equality_in_mkc_halts_ax in q1.
    apply equality_in_mkc_cequiv_ax in h1.
    spcast.

    eapply callbyvalue_reduce_c; eauto.
  }
Qed.
