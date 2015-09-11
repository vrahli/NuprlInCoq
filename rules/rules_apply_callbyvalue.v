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

(* !!MOVE *)
Lemma implies_approx_islambda {p} :
  forall lib a1 b1 c1 a2 b2 c2,
    @approx p lib a1 a2
    -> approx lib b1 b2
    -> approx lib c1 c2
    -> approx lib (mk_islambda a1 b1 c1) (mk_islambda a2 b2 c2).
Proof.
  introv apa apb apc.
  applydup @approx_relates_only_progs in apa.
  applydup @approx_relates_only_progs in apb.
  applydup @approx_relates_only_progs in apc.
  repnd.
  unfold mk_islambda, mk_can_test.
  repeat prove_approx; sp.
Qed.

(* !!MOVE *)
Lemma implies_cequivc_islambda {p} :
  forall lib a1 b1 c1 a2 b2 c2,
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> @cequivc p lib c1 c2
    -> cequivc lib (mkc_islambda a1 b1 c1) (mkc_islambda a2 b2 c2).
Proof.
  unfold cequivc.
  introv ceqa ceqb ceqc.
  destruct_cterms.
  allsimpl.
  allrw @isprog_eq.
  repnud ceqa.
  repnud ceqb.
  repnud ceqc.
  split; apply implies_approx_islambda; auto.
Qed.

(* !!MOVE *)
Definition mk_cnterm {o} (t : @NTerm o) (p : isprog_nout t) :=
  exist isprog_nout t p.

(* !!MOVE *)
Lemma hasvaluec_mkc_apply2 {q} :
  forall lib (t a : @CTerm q),
    hasvaluec lib (mkc_apply t a)
    -> {v : NVar $ {b : CVTerm [v] $ computes_to_valc lib t (mkc_lam v b)}}
       [+] {n : nseq $ computes_to_valc lib t (mkc_nseq n)}
       [+] {n : ntseqc $ computes_to_valc lib t (mkc_ntseq n)}.
Proof.
  introv hv.
  apply hasvaluec_mkc_apply in hv; repndors; exrepnd.

  - left.
    unfold computes_to_valuec in hv1.
    applydup @computes_to_value_preserves_program in hv1; auto.
    apply isprogram_eq in hv0; apply isprog_lam_iff in hv0.
    exists v (mk_cvterm [v] b hv0).
    unfold computes_to_valc; simpl; auto.

  - right; left.
    exists n; auto.

  - right; right.
    unfold computes_to_seqnc in hv0.
    unfold computes_to_seq in hv0.
    applydup @reduces_to_preserves_program in hv0; auto.
    rw @isprogram_mk_ntseq in hv1.
    assert (forall x, isprog_nout (n x)) as nout.
    { introv.
      pose proof (hv1 x) as h; clear hv1; repnd.
      destruct h0 as [cl wf].
      apply computation2.isprog_nout_iff; dands; auto. }

    exists (fun x => mk_cnterm (n x) (nout x)).
    unfold computes_to_valc, computes_to_value; simpl; auto.
    unfold ntseqc2seq; simpl; dands; auto.
    split; simpl; auto.
    apply nt_wf_sterm_implies_isprogram.
    apply nt_wf_sterm_iff; introv.
    pose proof (nout n0) as h.
    apply computation2.isprog_nout_iff in h; auto.
Qed.

Lemma cequivc_mkc_islambda_mkc_lam {o} :
  forall lib v (b : @CVTerm o [v]) t1 t2,
    cequivc lib (mkc_islambda (mkc_lam v b) t1 t2) t1.
Proof.
  introv.
  apply reduces_toc_implies_cequivc.
  destruct_cterms.
  unfold reduces_toc; simpl.
  apply reduces_to_if_step; csunf; simpl; auto.
Qed.

Lemma cequivc_mkc_islambda_mkc_nseq {o} :
  forall lib s (t1 t2 : @CTerm o),
    cequivc lib (mkc_islambda (mkc_nseq s) t1 t2) t2.
Proof.
  introv.
  apply reduces_toc_implies_cequivc.
  destruct_cterms.
  unfold reduces_toc; simpl.
  apply reduces_to_if_step; csunf; simpl; auto.
Qed.

Lemma cequivc_mkc_islambda_mkc_ntseq {o} :
  forall lib s (t1 t2 : @CTerm o),
    cequivc lib (mkc_islambda (mkc_ntseq s) t1 t2) t2.
Proof.
  introv.
  apply reduces_toc_implies_cequivc.
  destruct_cterms.
  unfold reduces_toc; simpl.
  apply reduces_to_if_step; csunf; simpl; auto.
Qed.

Lemma member_mkc_or_inl {p} :
  forall lib a (A B : @CTerm p),
    member lib (mkc_inl a) (mkc_or A B)
    <=> (type lib A
         # type lib B
         # member lib a A).
Proof.
  introv.
  rw @equality_mkc_or; split; intro h; repnd; repndors; exrepnd; spcast; dands; auto;
  computes_to_value_isvalue.
  left.
  exists a a; dands; spcast; auto;
  apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma member_mkc_or_inr {p} :
  forall lib b (A B : @CTerm p),
    member lib (mkc_inr b) (mkc_or A B)
    <=> (type lib A
         # type lib B
         # member lib b B).
Proof.
  introv.
  rw @equality_mkc_or; split; intro h; repnd; repndors; exrepnd; spcast; dands; auto;
  computes_to_value_isvalue.
  right.
  exists b b; dands; spcast; auto;
  apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma implies_approxc_lam2 {o} :
  forall lib v1 v2 (t1 : @CVTerm o [v1]) t2,
    (forall u : CTerm, cequivc lib (substc u v1 t1) (substc u v2 t2))
    -> approxc lib (mkc_lam v1 t1) (mkc_lam v2 t2).
Proof.
  introv imp.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allunfold @approxc; allsimpl.

  constructor.
  unfold close_comput; dands;
  try (apply isprogram_lam);
  eauto 3 with slow.

  - introv comp.
    apply computes_to_value_isvalue_eq in comp;
      try (apply isvalue_mk_lam); eauto 3 with slow.
    unfold mk_lam in comp; ginv; fold_terms.
    exists [bterm [v2] x]; fold_terms.
    dands.
    { apply computes_to_value_isvalue_refl;
      try (apply isvalue_mk_lam); eauto 3 with slow. }

    unfold lblift; simpl; dands; auto.
    introv ltn.
    destruct n; try omega; clear ltn.
    unfold selectbt; simpl.
    unfold blift.
    exists [v1] x0 (subst x v2 (mk_var v1)); dands; eauto 3 with slow.

    + apply clearbots_olift.
      apply cl_olift_implies_olift; eauto 3 with slow.

      pose proof (cl_olift_iff_pv_olift (approx lib) x0 (subst x v2 (mk_var v1)) [v1]) as xx.
      repeat (autodimp xx hyp).
      { clear imp; allrw @isprog_vars_eq; repnd; dands.
        - eapply subvars_eqvars;
          [|apply eqvars_sym;apply eqvars_free_vars_disjoint].
          simpl.
          rw subvars_app_l; dands.
          + apply subvars_remove_nvars; simpl.
            eapply subvars_trans;eauto.
            rw subvars_prop; simpl; tcsp.
          + boolvar; simpl; eauto 3 with slow.
        - apply nt_wf_subst; eauto 3 with slow. }
      apply xx; clear xx.
      introv ps e.
      destruct sub as [|p s]; allsimpl; ginv.
      destruct s; ginv.
      destruct p as [z u]; allsimpl.
      allrw @fold_subst.
      allrw @prog_sub_cons; repnd.
      pose proof (imp (mk_cterm u ps0)) as h; clear imp; allsimpl.
      destruct h; sp.
      eapply approx_trans; eauto.

      eapply approx_alpha_rw_r_aux;
        [apply alpha_eq_sym;apply combine_sub_nest|].
      simpl.
      allrw @fold_subst.
      rw @subst_mk_var1.

      destruct (deq_nvar v2 z); subst.

      * pose proof (cl_lsubst_app_sub_filter x [(z,u)] [(z,u)]) as h; allsimpl.
        autodimp h hyp; eauto 3 with slow.
        allrw memvar_singleton; boolvar; rw h; eauto 3 with slow.

      * pose proof (lsubst_sub_filter_alpha x [(v2, u), (z, u)] [z]) as h.
        allrw disjoint_singleton_r; allsimpl.
        allrw memvar_singleton; boolvar; tcsp.
        autodimp h hyp.
        { allrw @isprog_vars_eq; repnd.
          allrw subvars_eq.
          introv h; apply i1 in h; allsimpl; tcsp. }

        eapply approx_alpha_rw_r_aux;[exact h|].
        allrw @fold_subst; eauto 3 with slow.

    + pose proof (alpha_eq_bterm_single_change x v2) as h.
      allrw subset_singleton_r.
      autodimp h hyp.
      { introv ix.
        clear imp.
        allrw @isprog_vars_eq; repnd.
        allrw subvars_eq.
        apply i2 in ix; allsimpl; tcsp. }
      apply h.

  - introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.

  - introv comp.
    apply reduces_to_if_isvalue_like in comp; ginv; eauto 3 with slow.
Qed.

Lemma implies_cequivc_lam2 {o} :
  forall lib v1 v2 (t1 : @CVTerm o [v1]) t2,
    (forall u : CTerm, cequivc lib (substc u v1 t1) (substc u v2 t2))
    -> cequivc lib (mkc_lam v1 t1) (mkc_lam v2 t2).
Proof.
  introv imp.
  apply cequivc_iff_approxc; dands.
  - apply implies_approxc_lam2; auto.
  - apply implies_approxc_lam2; auto.
    introv.
    apply cequivc_sym; auto.
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
  spcast.

  dands.

  - apply tequality_mkc_or; dands; auto;[|].

    + apply tequality_mkc_cequiv; split; intro comp; spcast;[|].

      * eapply cequivc_trans;[apply cequivc_sym;exact ceq0|].
        eapply cequivc_trans;[exact comp|].
        apply implies_cequivc_lam; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        apply sp_implies_cequivc_apply; auto.

      * eapply cequivc_trans;[exact ceq0|].
        eapply cequivc_trans;[exact comp|].
        apply implies_cequivc_lam; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        apply sp_implies_cequivc_apply; auto.
        apply cequivc_sym; auto.

    + apply tequality_isect; dands; eauto 3 with slow; try (apply tnat_type);[].
      introv en.
      apply equality_in_tnat in en.
      unfold equality_of_nat in en; exrepnd; spcast.
      repeat (substc_lsubstc_vars3;[]).
      lsubst_tac.

      eapply tequality_respects_cequivc_left;
        [apply cequivc_decomp_approx;dands;
         [apply implies_cequivc_apply;
           [apply cequivc_sym;exact ceq0
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

  - eapply equality_respects_cequivc_right;
    [apply implies_cequivc_islambda;
      [exact ceq0
      |apply cequivc_refl
      |apply cequivc_refl]
    |].

    clear dependent s2.
    rw @member_eq.

    apply hasvaluec_mkc_apply2 in hyp2.
    repndors; exrepnd; spcast.

    + eapply member_respects_cequivc;
        [apply implies_cequivc_islambda;
          [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact hyp1
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
      eapply member_respects_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_islambda_mkc_lam|].
      apply member_mkc_or_inl; dands; eauto 3 with slow.

      * apply tequality_isect; dands; eauto 3 with slow; try (apply tnat_type);[].
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

      * apply member_cequiv.
        eapply cequivc_trans;
          [apply computes_to_valc_implies_cequivc;eauto|].

        apply implies_cequivc_lam2; introv.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.
        eapply cequivc_trans;
          [|apply sp_implies_cequivc_apply;
             apply cequivc_sym;
             apply computes_to_valc_implies_cequivc;eauto].
        eapply cequivc_trans;
          [|apply cequivc_sym;apply cequivc_beta]; auto.

    + eapply member_respects_cequivc;
        [apply implies_cequivc_islambda;
          [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact hyp0
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
      eapply member_respects_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_islambda_mkc_nseq|].
      apply member_mkc_or_inr; dands; eauto 3 with slow.

      * apply tequality_isect; dands; eauto 3 with slow; try (apply tnat_type);[].
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

      * apply member_in_isect; dands; eauto 3 with slow.
        introv en.
        apply equality_in_tnat in en.
        unfold equality_of_nat in en; exrepnd; spcast.
        repeat (substc_lsubstc_vars3;[]).
        lsubst_tac.

        dands.

        { apply member_approx.

Abort.



(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
