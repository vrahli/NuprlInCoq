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
Require Import sequents_tacs.
Require Import subst_tacs_aeq.
Require Import cequiv_tacs.
Require Import cequiv_lsubst.
Require Import tactics2.
Require Import sequents_equality.
Require Import sequents_tacs2.
Require Import lsubst_hyps.
Require Import per_props_equality.
Require Import list.



(* This is meant to replace wfseq and prove_seq *)
Ltac dwfseq2_step :=
  match goal with
    (* unfold in hyp *)
    | [ H : wf_csequent _ |- _ ] => unfold wf_csequent in H; repnd; allsimpl
    | [ H : wf_sequent _ |- _ ] => unfold wf_sequent in H; repnd; allsimpl
    | [ H : wf_concl _ |- _ ] => unfold wf_concl in H; repnd; allsimpl
    | [ H : closed_type _ _ |- _ ] => unfold closed_type in H; repnd; allsimpl
    | [ H : closed_extract _ _ |- _ ] => unfold closed_extract in H; repnd; allsimpl
    | [ H : closed_type_baresequent _ |- _ ] => unfold closed_type_baresequent in H; repnd; allsimpl
    | [ H : closed_extract_baresequent _ |- _ ] => unfold closed_extract_baresequent in H; repnd; allsimpl
    | [ H : covered _ _ |- _ ] => unfold covered in H; repnd; allsimpl
    | [ H : args_constraints _ _ |- _ ] => unfold args_constraints in H; repnd; allsimpl
    | [ H : arg_constraints _ _ |- _ ] => unfold arg_constraints in H; repnd; allsimpl
    (* unfold in concl *)
    | [ |- context[covered _ _] ] => unfold covered; allsimpl
    (* rewrite in context in hyps *)
    | [ H : context[hyps_free_vars (_ ++ _)] |- _ ] => rewrite hyps_free_vars_app in H
    | [ H : context[hyps_free_vars (snoc _ _)] |- _ ] => rewrite hyps_free_vars_snoc in H
    | [ H : context[app _ nil] |- _ ] => rewrite app_nil_r in H; repnd; allsimpl
    | [ H : context[remove_nvars [] _] |- _ ] => rewrite remove_nvars_nil_l in H; repnd; allsimpl
    | [ H : context[vars_hyps (app _ _)] |- _ ] => rewrite vars_hyps_app in H; allsimpl
    | [ H : context[vars_hyps (snoc _ _)] |- _ ] => rewrite vars_hyps_snoc in H; allsimpl
    | [ H : context[nh_vars_hyps (app _ _)] |- _ ] => rewrite nh_vars_hyps_app in H; repnd; allsimpl
    | [ H : context[nh_vars_hyps (snoc _ _)] |- _ ] => rewrite nh_vars_hyps_snoc in H; repnd; allsimpl
    | [ H : context[hyp_free_vars (mk_hyp _ _)] |- _ ] => rewrite hyp_free_vars_mk_hyp in H; repnd; allsimpl
    | [ H : context[hyp_free_vars (mk_hhyp _ _)] |- _ ] => rewrite hyp_free_vars_mk_hhyp in H; repnd; allsimpl
    | [ H : context[filter _ (app _ _)] |- _ ] => rewrite filter_app in H; repnd; allsimpl
    | [ H : context[filter _ (snoc _ _)] |- _ ] => rewrite filter_snoc in H; repnd; allsimpl
    (* rewrite in context in concl *)
    | [ |- context[hyps_free_vars (_ ++ _)] ] => rewrite hyps_free_vars_app
    | [ |- context[hyps_free_vars (snoc _ _)] ] => rewrite hyps_free_vars_snoc
    | [ |- context[app _ nil] ] => rewrite app_nil_r; repnd; allsimpl
    | [ |- context[remove_nvars [] _] ] => rewrite remove_nvars_nil_l; repnd; allsimpl
    | [ |- context[vars_hyps (app _ _)] ] => rewrite vars_hyps_app; allsimpl
    | [ |- context[vars_hyps (snoc _ _)] ] => rewrite vars_hyps_snoc; allsimpl
    | [ |- context[nh_vars_hyps (app _ _)] ] => rewrite nh_vars_hyps_app; repnd; allsimpl
    | [ |- context[nh_vars_hyps (snoc _ _)] ] => rewrite nh_vars_hyps_snoc; repnd; allsimpl
    | [ |- context[hyp_free_vars (mk_hyp _ _)] ] => rewrite hyp_free_vars_mk_hyp; repnd; allsimpl
    | [ |- context[hyp_free_vars (mk_hhyp _ _)] ] => rewrite hyp_free_vars_mk_hhyp; repnd; allsimpl
    | [ |- context[filter _ (app _ _)] ] => rewrite filter_app; repnd; allsimpl
    | [ |- context[filter _ (snoc _ _)] ] => rewrite filter_snoc; repnd; allsimpl
    (* trw_h in context in hyps *)
    | [ H : context [LIn _ (snoc _ _)] |- _ ] => trw_h in_snoc H; repnd; allsimpl
    | [ H : context [LIn _ (app _ _)] |- _ ] => trw_h in_app_iff H; repnd; allsimpl
    (* trw_h in context in concl *)
    | [ |- context [LIn _ (snoc _ _)] ] => trw in_snoc; repnd; allsimpl
    | [ |- context [LIn _ (app _ _)] ] => trw in_app_iff; repnd; allsimpl
    (* trw_h *)
    | [ H : vs_wf_hypotheses _ (app _ _) |- _ ] => trw_h vs_wf_hypotheses_app H; repnd; allsimpl
    | [ H : vs_wf_hypotheses _ (snoc _ _) |- _ ] => trw_h vs_wf_hypotheses_snoc H; repnd; allsimpl
    | [ H : wf_hypotheses (app _ _) |- _ ] => trw_h wf_hypotheses_app H; repnd; allsimpl
    | [ H : wf_hypotheses (snoc _ _) |- _ ] => trw_h wf_hypotheses_snoc H; repnd; allsimpl
    | [ H : isprog_vars _ _ |- _ ] => trw_h isprog_vars_eq H; repnd; allsimpl
    | [ H : disjoint (snoc _ _) _ |- _ ] => trw_h disjoint_snoc_l H; repnd; allsimpl
    | [ H : disjoint _ (snoc _ _) |- _ ] => trw_h disjoint_snoc_r H; repnd; allsimpl
    | [ H : subvars nil _ |- _ ] => trw_h subvars_nil_l_iff H
    | [ H : subvars (app _ _) _ |- _ ] => trw_h subvars_app_l H; repnd; allsimpl
    | [ H : subvars (cons _ _) _ |- _ ] => trw_h subvars_cons_l H; repnd; allsimpl
    | [ H : subvars _ _ |- _ ] => trw_h subvars_prop H; repnd; allsimpl
    | [ H : nt_wf _ |- _ ] => trw_h nt_wf_eq H; repnd; allsimpl
    (* trw *)
    | [ |- context[subvars _ _] ] => trw subvars_prop; allsimpl
    (* apply *)
(*    | [ H : vs_wf_hypotheses _ _ |- _ ] => apply vs_wf_hypotheses_implies in H; repnd*)
    | [ H : vswf_hypotheses _ _ |- _ ] => apply vswf_hypotheses_nil_implies in H; repnd
    | [ H : ~ (_ \/ _) |- _ ] => apply not_or in H; repnd
    | [ H : !(_ [+] _) |- _ ] => apply not_over_or in H; repnd
  end; GC.

Ltac dwfseq2 := repeat dwfseq2_step.


(* MOVE *)
Lemma nh_vars_hyps_lsubst_hyps {o} :
  forall (J : @bhyps o) sub,
    nh_vars_hyps (lsubst_hyps sub J) = nh_vars_hyps J.
Proof.
  induction J; introv; simpl; auto.
  unfold nh_vars_hyps in *; simpl.
  destruct a; simpl.
  unfold is_nh in *; simpl.
  destruct (negb hidden); simpl; rewrite IHJ; auto.
Qed.
Hint Rewrite @nh_vars_hyps_lsubst_hyps : slow.

Lemma alpha_eq_hyps_subst_snoc {o} :
  forall (s : @CSub o) v t wf c J,
    !LIn v (dom_csub s)
    -> alpha_eq_hyps
         (substitute_hyps (snoc s (v, lsubstc t wf s c)) J)
         (substitute_hyps s (lsubst_hyps [(v, t)] J)).
Proof.
  induction J; introv ni; simpl; tcsp.
  constructor; auto;[].
  destruct a; simpl.
  unfold alpha_eq_hyp; simpl.

  rewrite <- csubst_swap; auto.
  apply alpha_eq_sym.
  eapply alpha_eq_trans;[apply combine_sub_nest|]; simpl; auto.
Qed.

Hint Rewrite @vars_hyps_substitute_hyps : slow.
Hint Rewrite @vars_hyps_lsubst_hyps : slow.



(*
  H, J[u/t] |-  C[u/t]  ext  z[u/t]
      By generalization  u t X
   H |- t \in X
  H, u:X, J |- C ext z
*)


Definition rule_generalization_concl {o}
           (H J : @bhyps o) (u : NVar) (t C z : NTerm) :=
  mk_baresequent
    (H ++ lsubst_hyps [(u,t)] J)
    (mk_concl (subst C u t) (subst z u t)).

Definition rule_generalization_hyp1 {o}
           (H : @bhyps o) (t X : NTerm) :=
  mk_baresequent H (mk_conclax (mk_member t X)).

Definition rule_generalization_hyp2 {o}
           (H J : @bhyps o) (u : NVar) (X C z : NTerm) :=
  mk_baresequent
    (snoc H (mk_hyp u X) ++ J)
    (mk_concl C z).


Definition rule_generalization {o}
           (H J : @bhyps o)
           (u : NVar)
           (t C z X : NTerm) : rule :=
  mk_rule
    (rule_generalization_concl H J u t C z)
    [
      rule_generalization_hyp1 H t X,
      rule_generalization_hyp2 H J u X C z
    ]
    [sarg_term t].

Lemma rule_generalization_true {o} :
  forall (lib : library)
         (H J : @bhyps o)
         (u : NVar)
         (t C z X : NTerm),
    rule_true3 lib (rule_generalization H J u t C z X).
Proof.
  unfold rule_generalization, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.

  pose proof (cargs (sarg_term t)) as cargs; simpl in cargs; autodimp cargs hyp.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfs
  end.
  { clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq2.
    rw @vswf_hypotheses_nil_eq.
    apply wf_member_iff2 in wfct0; repnd.
    dands; tcsp; eauto 3 with slow.
    { apply vs_wf_hypotheses_eq.
      apply vs_wf_hypotheses_app; dands; simpl; eauto 3 with slow;
        try (complete (apply vs_wf_hypotheses_eq; auto)). }
    { apply subst_preserves_wf_term; auto. }
    { introv i; apply eqset_free_vars_disjoint in i; simpl in *.
      allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff.
      autorewrite with slow in *.
      repndors; repnd; tcsp.
      { apply ce in i0.
        apply in_app_iff in i0; repndors; tcsp.
        apply in_snoc in i0; repndors; subst; tcsp. }
      boolvar; simpl in *; autorewrite with list in *; tcsp.
      apply cargs in i; allrw in_app_iff; tcsp. } }

  exists wfs.
  unfold wf_csequent, wf_sequent, wf_concl in wfs; allsimpl; repnd; proof_irr; GC.

  assert (! LIn u (vars_hyps H)) as niuH.
  {
    clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq2; auto.
  }

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.

  apply similarity_app in sim; exrepnd; subst.

  dup hyp1 as dhyp1.
  hide_hyp dhyp1.
  pose proof (hyp1 s1a s2a) as hyp1.
  repeat (autodimp hyp1 hyp); eauto 3 with slow.

  { eapply hyps_functionality_init_seg in eqh; eauto. }

  exrepnd.
  lsubst_tac.
  apply member_if_inhabited in hyp1.
  applydup @tequality_mkc_member_implies_sp in hyp0; auto.
  apply tequality_mkc_member_sp in hyp0; repnd.
  clear hyp0 hyp1.

  pose proof (hyp2 (snoc s1a (u,lsubstc t wt s1a ct1) ++ s1b)
                   (snoc s2a (u,lsubstc t wt s2a ct2) ++ s2b))as q.

  repeat (autodimp q hyp);[| |].

  {
    introv sim'.
    apply @similarity_app in sim'; exrepnd; subst; rewrite length_snoc in *; cpx.
    apply @similarity_snoc in sim'5; exrepnd; subst; cpx.
    apply app_split in sim'0; repeat (rewrite length_snoc in * ); auto; try omega;[].
    repnd; cpx; subst; simpl in *; GC.

    assert (! LIn u (dom_csub s1a1)) as niu1.
    { apply similarity_dom in sim5; repnd; allrw; auto. }

    apply eq_hyps_app.
    exists (snoc s1a1 (u, lsubstc t wt s1a1 ct1))
           s1b0
           (snoc s2a1 (u,t2))
           s2b0.
    repeat (rewrite length_snoc); dands; auto;[|].

    {
      apply eq_hyps_snoc.
      assert (cover_vars X s2a1) as cov2 by (eapply similarity_cover_vars; eauto).
      exists s1a1 s2a1 (lsubstc t wt s1a1 ct1) t2 w p cov2.
      dands; auto; simpl; [|].

      {
        pose proof (eqh (s2a1 ++ s2b0)) as eqh.
        autodimp eqh hyp.

        {
          apply similarity_app.
          exists s1a1 s1b0 s2a1 s2b0; dands; auto.

          eapply similarity_preserves_alpha_eq_hyps;[| |eauto];
            try (apply alpha_eq_hyps_subst_snoc); auto.
          autorewrite with slow; auto.
        }

        apply eq_hyps_app in eqh; exrepnd.
        apply app_split in eqh0; auto; try congruence;[].
        apply app_split in eqh2; auto; try congruence;[].
        repnd; subst; auto.
      }

      {
        pose proof (dhyp1 s1a1 s2a1) as dhyp1; repeat (autodimp dhyp1 hyp); eauto 3 with slow.
        { eapply hyps_functionality_init_seg in eqh; eauto. }
        exrepnd; clear_irr; auto.
        lsubst_tac.
        apply tequality_mkc_member_sp in dhyp0; repnd; auto.
      }
    }

    {
      pose proof (eqh (s2a1 ++ s2b0)) as eqh.
      autodimp eqh hyp.

      { apply similarity_app.
        exists s1a1 s1b0 s2a1 s2b0; dands; auto;[].
        eapply similarity_preserves_alpha_eq_hyps;[| |eauto];
          try (apply alpha_eq_hyps_subst_snoc); auto.
        autorewrite with slow; auto. }

      apply eq_hyps_app in eqh; exrepnd.
      apply app_split in eqh0; try omega;[].
      apply app_split in eqh2; try omega;[].
      repnd; subst.

      pose proof (sub_eq_hyps_snoc_subst lib J s1a s2a0 s1b s2b1 [(u,t)]) as q.

    }
  }

  {
  }
Qed.
