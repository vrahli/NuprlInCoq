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
           Mark Bickford

*)


Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_can.
(*Require Export per_props_top.*)
Require Export per_props_squash.
Require Export integer_type.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
(*Require Export seq_util.*)
Require Export per_props_cequiv2.
Require Export lsubstc_vars.
Require Export per_props_util.
Require Export per_props_cs.



(* MOVE to per_props_util *)
Lemma all_in_ex_bar_ccequivc_implies_ccequivc_ext {o} :
  forall lib (a b c d : @CTerm o),
    all_in_ex_bar lib (fun lib => (ccequivc lib a b <=> ccequivc lib c d))
    -> all_in_ex_bar lib (fun lib => (ccequivc_ext lib a b <=> ccequivc_ext lib c d)).
Proof.
  introv h.
  unfold all_in_ex_bar in *; exrepnd; exists bar; introv br ext; split; introv q xt.
  { eapply h0; eauto 3 with slow. }
  { eapply h0; eauto 3 with slow. }
Qed.

Lemma implies_ccequivc_ext_islambda {o} :
  forall lib (a1 b1 c1 a2 b2 c2 : @CTerm o),
    ccequivc_ext lib a1 a2
    -> ccequivc_ext lib b1 b2
    -> ccequivc_ext lib c1 c2
    -> ccequivc_ext lib (mkc_islambda a1 b1 c1) (mkc_islambda a2 b2 c2).
Proof.
  introv ceqa ceqb ceqc xt.
  pose proof (ceqa _ xt) as ceqa.
  pose proof (ceqb _ xt) as ceqb.
  pose proof (ceqc _ xt) as ceqc.
  simpl in *; spcast.
  apply implies_cequivc_islambda; auto.
Qed.

Lemma ccequivc_ext_mkc_islambda_mkc_lam {o} :
  forall lib v (b : @CVTerm o [v]) t1 t2,
    ccequivc_ext lib (mkc_islambda (mkc_lam v b) t1 t2) t1.
Proof.
  introv xt; spcast.
  apply cequivc_mkc_islambda_mkc_lam.
Qed.

Lemma implies_ccequivc_ext_lam2 {o} :
  forall lib v1 v2 (t1 : @CVTerm o [v1]) t2,
    (forall u : CTerm, ccequivc_ext lib (substc u v1 t1) (substc u v2 t2))
    -> ccequivc_ext lib (mkc_lam v1 t1) (mkc_lam v2 t2).
Proof.
  introv imp xt; spcast.
  apply implies_cequivc_lam2; introv.
  apply cequiv_stable; apply imp; auto.
Qed.

Lemma ccequivc_ext_mkc_islambda_mkc_choice_seq {o} :
  forall lib s (t1 t2 : @CTerm o),
    ccequivc_ext lib (mkc_islambda (mkc_choice_seq s) t1 t2) t2.
Proof.
  introv xt; spcast.
  apply cequivc_mkc_islambda_mkc_choice_seq.
Qed.

Lemma compatible_choice_sequence_name_2 :
  forall n, compatible_choice_sequence_name 2 n.
Proof.
  tcsp.
Qed.
Hint Resolve compatible_choice_sequence_name_2 : slow.


(*
   H |- f ~ λx.f(x) ∨ f ∈ Free(1)

     By CallbyvalueApplyCases a x

     H |- halts(f a)
     H |- f in Base

 *)
Definition rule_callbyvalue_apply_cases {o}
           (H : barehypotheses)
           (f a : @NTerm o)
           (x : NVar)
  :=
    mk_rule
      (mk_baresequent H (mk_concl
                           (mk_or
                              (mk_cequiv f (mk_lam x (mk_apply f (mk_var x))))
                              (mk_member f (mk_csname 2)))
                           (mk_islambda f mk_btrue mk_bfalse)))
      [mk_baresequent H (mk_conclax (mk_halts (mk_apply f a))),
       mk_baresequent H (mk_conclax (mk_member f mk_base))]
      [sarg_term f].

Lemma rule_callbyvalue_apply_cases_true {o} :
  forall lib (H : barehypotheses)
         (f a : @NTerm o)
         (x : NVar)
         (nixf : !LIn x (free_vars f)),
    rule_true lib (rule_callbyvalue_apply_cases H f a x).
Proof.
  unfold rule_callbyvalue_apply_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs; allsimpl.
  pose proof (cargs (sarg_term f)) as argf; clear cargs; autodimp argf hyp; allsimpl.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.
  assert (covered (mk_islambda f mk_btrue mk_bfalse) (nh_vars_hyps H)) as cov.
  { unfold covered; simpl; autorewrite with slow in *; auto. }
  exists cov.

  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.

  pose proof (hyp1 lib' ext s1 s2 eqh sim) as hyp; clear hyp1; exrepnd.
  pose proof (hyp2 lib' ext s1 s2 eqh sim) as ceq; clear hyp2; exrepnd.
  lsubst_tac.
  autorewrite with slow in *.

  apply tequality_mkc_member_base in ceq0; spcast.
  clear ceq1.

  apply equality_in_halts in hyp1; repnd.
  apply all_in_ex_bar_teq_and_eq_implies_teq_and_eq.

  apply ccequivc_ext_bar_iff_ccequivc_bar in ceq0.
  eapply all_in_ex_bar_modus_ponens2;[|exact hyp1|exact ceq0]; clear hyp1 ceq0; introv xt hyp1 ceq0; repnd.

  clear hyp3 hyp1.
  clear hyp0.
  spcast.

  dands.

  - apply tequality_mkc_or; dands; auto;[|].

    + apply tequality_mkc_cequiv.
      apply in_ext_implies_all_in_ex_bar; introv xt'; split; intro comp;[|].

      * pose proof (ceq0 lib'1) as ceq0; autodimp ceq0 hyp; eauto 3 with slow; simpl in ceq0.
        spcast.
        eapply cequivc_trans;[apply cequivc_sym;eauto|].
        eapply cequivc_trans;[exact comp|].
        apply implies_cequivc_lam; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        apply sp_implies_cequivc_apply; auto.

      * pose proof (ceq0 lib'1) as ceq0; autodimp ceq0 hyp; eauto 3 with slow; simpl in ceq0.
        spcast.
        eapply cequivc_trans;[exact ceq0|].
        eapply cequivc_trans;[exact comp|].
        apply implies_cequivc_lam; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        apply sp_implies_cequivc_apply; auto.
        apply cequivc_sym; auto.

    + autorewrite with slow.
      apply tequality_mkc_member_sp; dands; eauto 3 with slow;[].
      apply in_ext_implies_all_in_ex_bar; introv xt'; right; eauto 3 with slow.

  - eapply equality_respects_cequivc_right;
      [apply implies_ccequivc_ext_islambda;
       [exact ceq0
       |apply ccequivc_ext_refl
       |apply ccequivc_ext_refl]
      |].

    clear dependent s2.
    rw @member_eq.

    applydup @hasvaluec_mkc_apply_implies_hasvaluec in hyp2 as hv.
    apply hasvaluec_mkc_apply2 in hyp2.
    repndors; exrepnd; spcast.

    + eapply member_respects_cequivc;
        [apply implies_ccequivc_ext_islambda;
          [apply ccequivc_ext_sym;apply computes_to_valc_implies_ccequivc_ext;exact hyp1
          |apply ccequivc_ext_refl
          |apply ccequivc_ext_refl]
        |].
      eapply member_respects_cequivc;
        [apply ccequivc_ext_sym;apply ccequivc_ext_mkc_islambda_mkc_lam|].
      apply member_mkc_or_inl; dands; eauto 3 with slow.

      * apply tequality_mkc_member_sp; dands; eauto 3 with slow;[].
        apply in_ext_implies_all_in_ex_bar; introv xt'; right; eauto 3 with slow.

      * apply member_cequiv.
        eapply ccequivc_ext_trans;
          [apply computes_to_valc_implies_ccequivc_ext;eauto|].

        apply implies_ccequivc_ext_lam2; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        eapply ccequivc_ext_trans;
          [|apply sp_implies_ccequivc_ext_apply;
             apply ccequivc_ext_sym;
             apply computes_to_valc_implies_ccequivc_ext;eauto].
        eapply ccequivc_ext_trans;
          [|apply ccequivc_ext_sym;introv xt'; spcast; apply cequivc_beta]; auto; eauto 3 with slow.

    + eapply member_respects_cequivc;
        [apply implies_ccequivc_ext_islambda;
          [apply ccequivc_ext_sym;apply computes_to_valc_implies_ccequivc_ext;exact hyp0
          |apply ccequivc_ext_refl
          |apply ccequivc_ext_refl]
        |].
      eapply member_respects_cequivc;
        [apply ccequivc_ext_sym;apply ccequivc_ext_mkc_islambda_mkc_choice_seq|].
      apply member_mkc_or_inr; dands; eauto 3 with slow.

      * apply tequality_mkc_member_sp; dands; eauto 3 with slow;[].
        apply in_ext_implies_all_in_ex_bar; introv xt'; right; eauto 3 with slow.

      * rw <- @member_member_iff.
        apply equality_in_csname_iff.
        exists (trivial_bar lib'0).
        apply implies_all_in_bar_trivial_bar.
        introv xt'.
        exists n; dands; spcast; eauto 3 with slow.
Qed.
