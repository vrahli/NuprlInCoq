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


Require Export computation_apply.
Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_nat.
Require Export per_can.
Require Export per_props_top.
Require Export integer_type.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export seq_util.


(*
   H |- halts(t)

     By callbyvalueApply

     H |- halts (t a)

 *)
Definition rule_callbyvalue_apply {o}
           (H : barehypotheses)
           (t a: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_halts t) ))
    [ mk_baresequent H (mk_conclax 
       (mk_halts (mk_apply t a)))
    ]
    [].


Lemma rule_callbyvalue_apply_true {o} :
  forall lib (H : barehypotheses)
         (t a: @NTerm o),
    rule_true lib (rule_callbyvalue_apply H t a).
Proof.
  unfold rule_callbyvalue_apply, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
 
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd. 
  lsubst_tac.
  generalize_lsubstc_terms t1.
  generalize_lsubstc_terms t2.
  apply equality_in_halts in hyp1;exrepd.
  apply tequality_mkc_halts in hyp0; lsubst_tac.
  spcast.
  rename c into hasv.
  revert hyp0.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms a2.
  introv hyp.
  assert (chaltsc lib (mkc_apply t1 a1)) as ch1 by (spcast; auto).
  assert (chaltsc lib (mkc_apply t2 a2)) as ch2 by (apply hyp; auto).
  spcast.
  apply hasvaluec_mkc_apply_implies_hasvaluec in ch1.
  apply hasvaluec_mkc_apply_implies_hasvaluec in ch2.
  split.
  - (* tequality *)
    apply tequality_mkc_halts. split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_halts; sp; spcast; auto.
Qed.

(*
   H |- (<a,b> c) approx  bottom

     By applyPair

     NoSubgoals
    
 *)
Definition rule_apply_pair {o}
           (H : barehypotheses)
           (a b c: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx (mk_apply (mk_pair a b) c) mk_bottom)))
    []
    [].

Lemma apply_pair_not_valuelike {o} :
   forall lib (a b c : @NTerm o),
   !hasvalue_like lib (mk_apply (mk_pair a b) c).
Proof. introv hv. destruct hv as [v hv]. destruct hv as [red val]. destruct red as [k red].
       revert red. induction k; introv red.
       - apply reduces_in_atmost_k_steps_0 in red; subst. destruct val as [x | y].
        + inversion x.
        + inversion y.
      - apply reduces_in_atmost_k_steps_S in red; exrepnd.
        apply compute_step_apply_can_success in red1. repndors; exrepnd.
        + inversion red2.
        + inversion red1.
Qed.

Lemma rule_apply_pair_true {o} :
  forall lib (H : barehypotheses)
         (a b c: @NTerm o),
    rule_true lib (rule_apply_pair H a b c).
Proof.
  unfold rule_apply_pair, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
 
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  lsubst_tac.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms b1.
  generalize_lsubstc_terms x1.
  generalize_lsubstc_terms a2.
  generalize_lsubstc_terms b2.
  generalize_lsubstc_terms x2.
  assert (approxc lib (mkc_apply (mkc_pair a1 b1) x1) mkc_bottom) as appr1.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_pair; auto.
    - introv hvl. apply apply_pair_not_valuelike in hvl. inversion hvl. }
  assert( approxc lib (mkc_apply (mkc_pair a2 b2) x2) mkc_bottom) as appr2.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_pair; auto.
    - introv hvl. apply apply_pair_not_valuelike in hvl. inversion hvl. }
  
  split. 
  - (* tequality *)
    apply tequality_mkc_approx.
    split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_approx; sp; spcast; auto;
    apply computes_to_valc_refl;
    unfold iscvalue, mkc_axiom; simpl; eauto 3 with slow.
Qed.


(*
   H |- ((inl a) b) approx  bottom

     By applyInl

     NoSubgoals
    
 *)
Definition rule_apply_inl {o}
           (H : barehypotheses)
           (a b: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx (mk_apply (mk_inl a) b) mk_bottom)))
    []
    [].

Lemma apply_inl_not_valuelike {o} :
   forall lib (a b : @NTerm o),
   !hasvalue_like lib (mk_apply (mk_inl a) b).
Proof. introv hv. destruct hv as [v hv]. destruct hv as [red val]. destruct red as [k red].
       revert red. induction k; introv red.
       - apply reduces_in_atmost_k_steps_0 in red; subst. destruct val as [x | y].
        + inversion x.
        + inversion y.
      - apply reduces_in_atmost_k_steps_S in red; exrepnd.
        apply compute_step_apply_can_success in red1. repndors; exrepnd.
        + inversion red2.
        + inversion red1.
Qed.

Lemma rule_apply_inl_true {o} :
  forall lib (H : barehypotheses)
         (a b: @NTerm o),
    rule_true lib (rule_apply_inl H a b).
Proof.
  unfold rule_apply_inl, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
 
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  lsubst_tac.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms b1.
  generalize_lsubstc_terms a2.
  generalize_lsubstc_terms b2.
  assert (approxc lib (mkc_apply (mkc_inl a1) b1) mkc_bottom) as appr1.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_inl; auto.
    - introv hvl. apply apply_inl_not_valuelike in hvl. inversion hvl. }
  assert( approxc lib (mkc_apply (mkc_inl a2) b2) mkc_bottom) as appr2.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_inl; auto.
    - introv hvl. apply apply_inl_not_valuelike in hvl. inversion hvl. }
  
  split. 
  - (* tequality *)
    apply tequality_mkc_approx.
    split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_approx; sp; spcast; auto;
    apply computes_to_valc_refl;
    unfold iscvalue, mkc_axiom; simpl; eauto 3 with slow.
Qed.



(*
   H |- ((inr a) b) approx  bottom

     By applyInr

     NoSubgoals

 *)
Definition rule_apply_inr {o}
           (H : barehypotheses)
           (a b: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx (mk_apply (mk_inr a) b) mk_bottom)))
    []
    [].

Lemma apply_inr_not_valuelike {o} :
   forall lib (a b : @NTerm o),
   !hasvalue_like lib (mk_apply (mk_inr a) b).
Proof. introv hv. destruct hv as [v hv]. destruct hv as [red val]. destruct red as [k red].
       revert red. induction k; introv red.
       - apply reduces_in_atmost_k_steps_0 in red; subst. destruct val as [x | y].
        + inversion x.
        + inversion y.
      - apply reduces_in_atmost_k_steps_S in red; exrepnd.
        apply compute_step_apply_can_success in red1. repndors; exrepnd.
        + inversion red2.
        + inversion red1.
Qed.

Lemma rule_apply_inr_true {o} :
  forall lib (H : barehypotheses)
         (a b: @NTerm o),
    rule_true lib (rule_apply_inr H a b).
Proof.
  unfold rule_apply_inr, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
 
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  lsubst_tac.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms b1.
  generalize_lsubstc_terms a2.
  generalize_lsubstc_terms b2.
  assert (approxc lib (mkc_apply (mkc_inr a1) b1) mkc_bottom) as appr1.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_inr; auto.
    - introv hvl. apply apply_inr_not_valuelike in hvl. inversion hvl. }
  assert( approxc lib (mkc_apply (mkc_inr a2) b2) mkc_bottom) as appr2.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_inr; auto.
    - introv hvl. apply apply_inr_not_valuelike in hvl. inversion hvl. }
  
  split. 
  - (* tequality *)
    apply tequality_mkc_approx.
    split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_approx; sp; spcast; auto;
    apply computes_to_valc_refl;
    unfold iscvalue, mkc_axiom; simpl; eauto 3 with slow.
Qed.


(*
   H |- (z b) approx bottom

     By applyInt

     H |- z in Z

 *)
Definition rule_apply_int {o}
           (H : barehypotheses)
           (a b: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_approx (mk_apply a b) mk_bottom)))
    [mk_baresequent H (mk_conclax (mk_member a mk_int))]
    [].


Lemma apply_int_not_valuelike {o} :
  forall lib (a b : @NTerm o),
    isprogram a
    -> isprogram b
    -> {n : Z $ reduces_to lib a (mk_integer n)}
    -> !hasvalue_like lib (mk_apply a b).
Proof.
  introv ispa ispb red hv.
  destruct hv as [v c].
  destruct c as [red2 val].

  assert (isprogram v) as ispv.
  { eauto 3 with slow. }

  exrepnd.
  apply  @reduces_to_implies_cequiv in red0; auto.
  apply  @reduces_to_implies_cequiv in red2; try apply isprogram_apply; auto.

  assert (cequiv lib (mk_apply (mk_integer n) b) (mk_apply a b)) as ceq1.
  {repeat (prove_cequiv). apply cequiv_sym; auto. destruct ispb; auto. }

  assert (cequiv lib (mk_apply (mk_integer n) b) v) as ceq2.
  { eapply cequiv_trans; [exact ceq1 | auto]. }

  destruct val; destruct v as [v|f|op bs]; allsimpl; auto;
  try (destruct op; allsimpl; auto).

  - assert (cequiv lib mk_bottom (sterm f)) as ceq3.
    { eapply cequiv_trans;[|exact ceq2].
      split;[apply bottom_approx_any|]; eauto 3 with slow.
      apply approx_assume_hasvalue; eauto 3 with slow.
      introv hv; provefalse.
      unfold hasvalue_like in hv; exrepnd.
      apply reduces_to_split2 in hv1; repndors; exrepnd; subst; ginv.
      unfold isvalue_like in hv0; allsimpl; tcsp. }
    destruct ceq3 as [ap1 ap2].
    apply hasvalue_approx in ap2;
      [apply not_hasvalue_bot in ap2; tcsp|].
    apply hasvalue_sterm; auto.

  - pose proof (cequiv_canonical_form
                  lib
                  (oterm (Can c) bs)
                  (mk_apply (mk_integer n) b) c bs) as xx.
    repeat (autodimp xx hyp; eauto 3 with slow); exrepnd.
    destruct xx1 as [r v].
    destruct r as [k r].
    revert r.
    induction k; introv red.
    { rw @reduces_in_atmost_k_steps_0 in red. inversion red. }
    { apply @reduces_in_atmost_k_steps_S in red. exrepnd.
      apply compute_step_apply_can_success in red3. repndors; exrepnd. inversion red4.
      inversion red3.
    }

  - dup red2 as red3. apply cequiv_isprogram in red3. destruct red3. sp.
    apply isprogram_exception_implies in i1. exrepnd. subst.
    assert (oterm Exc [bterm [] a0, bterm [] t] =e>( a0, lib)t) as yy.
    + exists 0. apply reduces_in_atmost_k_steps_0. refl.
    + pose proof (cequiv_exception_weak
                    lib
                    (oterm Exc [bterm [] a0, bterm [] t]) a0 t
                    (mk_apply (mk_integer n) b) yy
                 ) as xx. dimp xx.
       { eapply @cequiv_trans; apply @cequiv_sym. exact red2. auto. }
       { exrepnd. destruct hyp1 as [k r]. revert r. induction k; introv red.
         { rw @reduces_in_atmost_k_steps_0 in red. inversion red. }
         { apply @reduces_in_atmost_k_steps_S in red. exrepnd.
           apply compute_step_apply_can_success in red3. repndors; exrepnd. inversion red4. 
           inversion red3.
         }
       }
Qed.

Lemma rule_apply_int_true {o} :
  forall lib (H : barehypotheses)
         (a b: @NTerm o),
    rule_true lib (rule_apply_int H a b).
Proof.
  unfold rule_apply_int, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  vr_seq_true  in Hyp0.
  pose proof (Hyp0 s1 s2 eqh sim) as hyp. clear Hyp0. exrepnd.
  lsubst_tac.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms b1.
  generalize_lsubstc_terms a2.
  generalize_lsubstc_terms b2.
  rw @equality_in_member in hyp1; exrepnd.
  apply tequality_member_int in hyp0; auto.
  dup hyp1 as aint.
  unfold equality_of_int in hyp0. exrepnd. allsimpl. spcast.

  assert (approxc lib (mkc_apply a1 b1) mkc_bottom) as appr1.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto.
    - introv hvl; apply apply_int_not_valuelike in hvl; try apply isprog_eq; tcsp.
      exists k. unfold computes_to_valc in hyp0. allsimpl. destruct hyp0. auto.
   }
  assert( approxc lib (mkc_apply a2 b2) mkc_bottom) as appr2.
  { destruct_cterms; allunfold @approxc; allsimpl.
     apply approx_assume_hasvalue; eauto 3 with slow.
    - apply isprogram_eq. apply isprog_apply; auto; apply isprog_inr; auto.
    - introv hvl; apply apply_int_not_valuelike in hvl; try apply isprog_eq; tcsp.
      exists k. unfold computes_to_valc in hyp4. allsimpl. destruct hyp4. auto.
  }

  split.
  - (* tequality *)
    apply tequality_mkc_approx.
    split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_approx; sp; spcast; auto;
    apply computes_to_valc_refl;
    unfold iscvalue, mkc_axiom; simpl; eauto 3 with slow.
Qed.

(* !!MOVE *)
Lemma type_mkc_cequiv {o} :
  forall lib (a b : @CTerm o),
    type lib (mkc_cequiv a b).
Proof.
  introv.
  apply tequality_mkc_cequiv; tcsp.
Qed.
Hint Resolve type_mkc_cequiv : slow.

(* !!MOVE *)
Lemma type_mkc_approx {o} :
  forall lib (a b : @CTerm o),
    type lib (mkc_approx a b).
Proof.
  introv.
  apply tequality_mkc_approx; tcsp.
Qed.
Hint Resolve type_mkc_approx : slow.

Lemma implies_tequality_equality_mkc_squash {o} :
  forall lib (t1 t2 : @CTerm o),
    tequality lib t1 t2
    -> inhabited_type lib t1
    -> (tequality lib (mkc_squash t1) (mkc_squash t2)
        # equality lib mkc_axiom mkc_axiom (mkc_squash t1)).
Proof.
  introv teq inh.
  rw @equality_in_mkc_squash.
  rw @tequality_mkc_squash.
  dands; auto; spcast;
  apply computes_to_valc_refl; eauto 3 with slow.
Qed.

(*
   H |- f ~ \x.f x \/ (isect x : Nat. f x <= bot) ext (islambda(f;btrue;bfalse)

     By CallbyvalueApplyCases a x

     H |- halts(f a)

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
                              (mk_isect
                                 mk_tnat
                                 x
                                 (mk_approx (mk_apply f (mk_var x)) mk_bottom)))
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
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1; exrepnd.
  pose proof (hyp2 s1 s2 eqh sim) as ceq; clear hyp2; exrepnd.
  lsubst_tac.
  autorewrite with slow in *.

  apply tequality_mkc_member_base in ceq0; spcast.
  clear ceq1.

  apply equality_in_halts in hyp1; repnd.
  clear hyp3 hyp1.
  clear hyp0.

  dands.

  - apply tequality_mkc_or; dands; auto;[|].

    + apply tequality_mkc_cequiv; split; intro comp; spcast;[|].

      * eapply cequivc_trans;[apply cequivc_sym;exact ceq0|].
        eapply cequivc_trans;[exact comp|].

        SearchAbout cequivc mkc_lam.

        (*
    + apply tequality_isect; dands; eauto 3 with slow; try (apply tnat_type);[].
      introv en.
      apply equality_in_tnat in en.
      unfold equality_of_nat in en; exrepnd; spcast.
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.

      eapply tequality_respects_cequivc_left;
        [apply cequivc_decomp_approx;dands;
         [apply implies_cequivc_apply;
           [apply cequivc_refl
           |apply cequivc_sym;
             apply computes_to_valc_implies_cequivc;eauto
           ]
         |apply cequivc_refl]
        |].

      eapply tequality_respects_cequivc_right;
        [apply cequivc_decomp_approx;dands;
         [apply implies_cequivc_apply;
           [apply cequivc_refl
           |apply cequivc_sym;
             apply computes_to_valc_implies_cequivc;eauto
           ]
         |apply cequivc_refl]
        |].

      rw @fold_type; eauto 3 with slow.

    +

      apply tequality_mkc_approx.

      SearchAbout tequality mkc_approx.

XXXXXXX

  apply hasvaluec_mkc_apply in hyp2.
  SearchAbout hasvaluec mkc_apply.
*)
Abort.



(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/" "../continuity/")
*** End:
*)
