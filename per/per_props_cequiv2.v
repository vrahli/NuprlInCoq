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
           Mark Bickford

*)


Require Export csubst3.
Require Export computation_apply.
Require Export per_props_cequiv.
Require Export per_props_union.
Require Export continuity_defs_ceq.
Require Export per_props3.
Require Export per_props_nat.
Require Export cequiv_bind.


Lemma type_mkc_cequiv {o} :
  forall lib (a b : @CTerm o),
    type lib (mkc_cequiv a b).
Proof.
  introv.
  apply tequality_mkc_cequiv; tcsp.
Qed.
Hint Resolve type_mkc_cequiv : slow.

Lemma type_mkc_approx {o} :
  forall lib (a b : @CTerm o),
    type lib (mkc_approx a b).
Proof.
  introv.
  apply tequality_mkc_approx; tcsp.
Qed.
Hint Resolve type_mkc_approx : slow.

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

Lemma implies_approx_isint {p} :
  forall lib a1 b1 c1 a2 b2 c2,
    @approx p lib a1 a2
    -> approx lib b1 b2
    -> approx lib c1 c2
    -> approx lib (mk_isint a1 b1 c1) (mk_isint a2 b2 c2).
Proof.
  introv apa apb apc.
  applydup @approx_relates_only_progs in apa.
  applydup @approx_relates_only_progs in apb.
  applydup @approx_relates_only_progs in apc.
  repnd.
  unfold mk_isint, mk_can_test.
  repeat prove_approx; sp.
Qed.

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

Lemma implies_cequivc_isint {p} :
  forall lib a1 b1 c1 a2 b2 c2,
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> @cequivc p lib c1 c2
    -> cequivc lib (mkc_isint a1 b1 c1) (mkc_isint a2 b2 c2).
Proof.
  unfold cequivc.
  introv ceqa ceqb ceqc.
  destruct_cterms.
  allsimpl.
  allrw @isprog_eq.
  repnud ceqa.
  repnud ceqb.
  repnud ceqc.
  split; apply implies_approx_isint; auto.
Qed.

Lemma implies_cequiv_isint {p} :
  forall lib a1 b1 c1 a2 b2 c2,
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> @cequiv p lib c1 c2
    -> cequiv lib (mk_isint a1 b1 c1) (mk_isint a2 b2 c2).
Proof.
  introv ceqa ceqb ceqc.
  allrw @isprog_eq.
  repnud ceqa.
  repnud ceqb.
  repnud ceqc.
  split; apply implies_approx_isint; auto.
Qed.

Definition mk_cnterm {o} (t : @NTerm o) (p : isprog_nout t) :=
  exist isprog_nout t p.

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
      apply isprog_nout_iff; dands; auto. }

    exists (fun x => mk_cnterm (n x) (nout x)).
    unfold computes_to_valc, computes_to_value; simpl; auto.
    unfold ntseqc2seq; simpl; dands; auto.
    split; simpl; auto.
    apply nt_wf_sterm_implies_isprogram.
    apply nt_wf_sterm_iff; introv.
    pose proof (nout n0) as h.
    apply isprog_nout_iff in h; sp.
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

Lemma nt_wf_int_iff {p} :
  forall (bs : list (@BTerm p)) z,
    nt_wf (oterm (Can (Nint z)) bs)
    <=> bs = [].
Proof.
  introv; split; intro k.
  - inversion k as [|?|? ? imp e]; clear k; subst.
    allsimpl.
    repeat (destruct bs; allsimpl; ginv).
  - exrepnd; subst.
    repeat constructor.
    introv i; allsimpl; repndors; subst; tcsp.
Qed.

Lemma dec_can_int {o} :
  forall (op : @CanonicalOp o),
    decidable {z : Z & op = Nint z}.
Proof.
  introv; unfold decidable.
  destruct op; try (complete (right; sp; ginv)).
  left; exists z; auto.
Qed.

Lemma hasvaluec_implies_cequivc_mkc_isint {o} :
  forall lib (a b c : @CTerm o),
    hasvaluec lib a
    -> (cequivc lib (mkc_isint a b c) b [+] cequivc lib (mkc_isint a b c) c).
Proof.
  introv hv.
  destruct_cterms; allsimpl.
  unfold hasvaluec in hv; allsimpl.
  unfold cequivc; simpl.
  unfold hasvalue in hv; exrepnd.
  unfold computes_to_value in hv0; repnd.
  inversion hv0 as [v isp isc]; subst; clear hv0.
  destruct t' as [v|f|op bs]; allsimpl; tcsp; GC.
  - right.
    eapply cequiv_trans;
      [apply implies_cequiv_isint;
        [apply reduces_to_implies_cequiv; eauto 3 with slow
        |apply cequiv_refl;eauto 3 with slow
        |apply cequiv_refl;eauto 3 with slow]
      |].
    apply reduces_to_implies_cequiv; eauto 3 with slow.
    apply isprogram_isint; eauto 3 with slow.
  - dopid op as [can|ncan|exc|abs] Case; tcsp; GC;[].
    destruct (dec_can_int can) as [d|d]; exrepnd; subst.
    + left.
      eapply cequiv_trans;
        [apply implies_cequiv_isint;
          [apply reduces_to_implies_cequiv; eauto 3 with slow
          |apply cequiv_refl;eauto 3 with slow
          |apply cequiv_refl;eauto 3 with slow]
        |].
      inversion isp as [cl wf].
      apply nt_wf_int_iff in wf; subst; fold_terms.
      apply reduces_to_implies_cequiv; eauto 3 with slow.
      apply isprogram_isint; eauto 3 with slow.
    + right.
      eapply cequiv_trans;
        [apply implies_cequiv_isint;
          [apply reduces_to_implies_cequiv; eauto 3 with slow
          |apply cequiv_refl;eauto 3 with slow
          |apply cequiv_refl;eauto 3 with slow]
        |].
      apply reduces_to_implies_cequiv; eauto 3 with slow.
      { apply isprogram_isint; eauto 3 with slow. }
      apply reduces_to_if_step.
      csunf; simpl.
      destruct can; simpl; auto.
      destruct d; eexists; eauto.
Qed.

Definition isintegerc {o} (t : @CTerm o) := isinteger (get_cterm t).

Lemma hasvaluec_implies_cequivc_mkc_isint2 {o} :
  forall lib (a b c : @CTerm o),
    hasvaluec lib a
    -> {z : Z
        & computes_to_valc lib a (mkc_integer z)
        # cequivc lib (mkc_isint a b c) b}
       [+]
       {v : CTerm
        & computes_to_valc lib a v
        # !isintegerc v
        # cequivc lib (mkc_isint a b c) c}.
Proof.
  introv hv.
  destruct_cterms; allsimpl.
  unfold hasvaluec in hv; allsimpl.
  unfold cequivc, computes_to_valc, isintegerc; simpl.
  unfold hasvalue in hv; exrepnd.
  unfold computes_to_value in hv0; repnd.
  inversion hv0 as [v isp isc]; subst; clear hv0.
  destruct t' as [v|f|op bs]; allsimpl; tcsp; GC.

  - right.
    exists (mk_cterm (sterm f) isp); simpl.
    dands.

    + unfold computes_to_value; dands; eauto 3 with slow.

    + unfold isinteger; intro h; exrepnd; ginv.

    + eapply cequiv_trans;
      [apply implies_cequiv_isint;
        [apply reduces_to_implies_cequiv; eauto 3 with slow
        |apply cequiv_refl;eauto 3 with slow
        |apply cequiv_refl;eauto 3 with slow]
      |].
      apply reduces_to_implies_cequiv; eauto 3 with slow.
      apply isprogram_isint; eauto 3 with slow.

  - dopid op as [can|ncan|exc|abs] Case; tcsp; GC;[].
    destruct (dec_can_int can) as [d|d]; exrepnd; subst.

    + left.
      inversion isp as [cl wf].
      apply nt_wf_int_iff in wf; subst; fold_terms.
      exists z; dands; auto.

      * unfold computes_to_value; dands; eauto 3 with slow.

      * eapply cequiv_trans;
        [apply implies_cequiv_isint;
          [apply reduces_to_implies_cequiv; eauto 3 with slow
          |apply cequiv_refl;eauto 3 with slow
          |apply cequiv_refl;eauto 3 with slow]
        |].
        apply reduces_to_implies_cequiv; eauto 3 with slow.
        apply isprogram_isint; eauto 3 with slow.

    + right.
      exists (mk_cterm (oterm (Can can) bs) isp); simpl.
      dands; auto.

      * unfold computes_to_value; dands; eauto 3 with slow.

      * intro h; unfold isinteger, mk_integer in h; exrepnd; ginv.
        destruct d; eexists; eauto.

      * eapply cequiv_trans;
        [apply implies_cequiv_isint;
          [apply reduces_to_implies_cequiv; eauto 3 with slow
          |apply cequiv_refl;eauto 3 with slow
          |apply cequiv_refl;eauto 3 with slow]
        |].
      apply reduces_to_implies_cequiv; eauto 3 with slow.
      { apply isprogram_isint; eauto 3 with slow. }
      apply reduces_to_if_step.
      csunf; simpl.
      destruct can; simpl; auto.
      destruct d; eexists; eauto.
Qed.

Lemma implies_cequivc_halts {o} :
  forall lib (a b : @CTerm o),
    cequivc lib a b
    -> cequivc lib (mkc_halts a) (mkc_halts b).
Proof.
  introv imp.
  allrw <- @fold_mkc_halts.
  apply cequivc_decomp_approx; dands; eauto 3 with slow.
  apply simpl_cequivc_mkc_cbv; auto.
Qed.

Lemma hasvalue_likec_apply_nseq_implies_integer {o} :
  forall lib s (v : @CTerm o),
    iscvalue v
    -> hasvalue_likec lib (mkc_apply (mkc_nseq s) v)
    -> isintegerc v.
Proof.
  introv isv hv.
  destruct_cterms.
  unfold iscvalue in isv.
  unfold hasvalue_likec in hv.
  unfold isintegerc; allsimpl.
  unfold hasvalue_like in hv; exrepnd.
  apply isvalue_implies in isv; repnd.
  apply reduces_to_split2 in hv1; repndors; subst.
  - unfold isvalue_like in hv0; allsimpl; tcsp.
  - exrepnd.
    csunf hv1; allsimpl; ginv.
    apply reduces_to_split2 in hv2; repndors; subst.
    + unfold isvalue_like in hv0; allsimpl; tcsp.
    + exrepnd.
      csunf hv2; allsimpl; dcwf xx; allsimpl.
      apply iscan_implies in isv0; repndors; exrepnd; subst; ginv.
      destruct c; allsimpl; ginv.
      destruct bterms; allsimpl; ginv.
      boolvar; ginv; fold_terms; eauto 3 with slow.
Qed.

Lemma hasvalue_likec_apply_ntseq_implies_integer {o} :
  forall lib s (v : @CTerm o),
    iscvalue v
    -> hasvalue_likec lib (mkc_apply (mkc_ntseq s) v)
    -> isintegerc v.
Proof.
  introv isv hv.
  destruct_cterms.
  unfold iscvalue in isv.
  unfold hasvalue_likec in hv.
  unfold isintegerc; allsimpl.
  unfold hasvalue_like in hv; exrepnd.
  apply isvalue_implies in isv; repnd.
  apply reduces_to_split2 in hv1; repndors; subst.
  - unfold isvalue_like in hv0; allsimpl; tcsp.
  - exrepnd.
    csunf hv1; allsimpl; ginv.
    apply reduces_to_split2 in hv2; repndors; subst.
    + unfold isvalue_like in hv0; allsimpl; tcsp.
    + exrepnd.
      csunf hv2; allsimpl.
      apply iscan_implies in isv0; repndors; exrepnd; subst; ginv.
      apply compute_step_eapply_success in hv2; exrepnd.
      destruct l; allsimpl; ginv.
      repndors; exrepnd; subst; GC; allsimpl; tcsp.
      * destruct c; ginv.
        destruct bterms; allsimpl; ginv.
        exists z; auto.
      * unfold isnoncan_like in hv5; allsimpl; tcsp.
Qed.

Lemma type_base {o} : forall lib, @type o lib mkc_base.
Proof.
  introv; apply tequality_base.
Qed.
Hint Resolve type_base : slow.

Hint Rewrite @lsubstc_mk_true : slow.
Hint Resolve tnat_type : slow.
Hint Resolve type_mkc_true : slow.


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

Definition isNat {o} (t : @NTerm o) : NTerm := mk_le mk_zero t.
Definition diverges {o} (t: @NTerm o) : NTerm := mk_approx t mk_bot.

(*
    isect (x : Base) (z : halts(x)). isint(x;if x < 0 then diverges(f(x)) else isNat(f(x));diverges(f(x)))
 *)
Definition isChoiceSeq {o} (x z : NVar) (f : @NTerm o) : NTerm :=
  mk_isect
    mk_base
    x
    (mk_isect
       (mk_halts (mk_var x))
       z
       (mk_isint
          (mk_var x)
          (mk_less
             (mk_var x)
             mk_zero
             (diverges (mk_apply f (mk_var x)))
             (isNat (mk_apply f (mk_var x)))
          )
          (diverges (mk_apply f (mk_var x)))
       )
    ).


Lemma hasvaluec_approxc_lam_implies_cequivc {o} :
  forall lib (f : @CTerm o) x y a,
    approxc lib f (mkc_lam y a)
    -> hasvaluec lib f
    -> cequivc lib f (mkc_lam x (mkcv_apply [x] (mk_cv [x] f) (mkc_var x))).
Proof.
  introv apr hv.
  apply cequivc_iff_approxc; dands; auto; destruct_cterms;
  allunfold @approxc; allunfold @hasvaluec; allunfold @cequivc; allsimpl;
  rename x1 into a; rename x0 into f.

  - unfold hasvalue in hv; exrepnd.
    unfold computes_to_value in hv0; repnd.
    apply isvalue_iff in hv0; repnd.
    eapply approx_trans;
      [apply reduces_to_implies_approx2;eauto 3 with slow|].

    apply (approx_trans _ _ (mk_lam x (mk_apply t' (mk_var x)))).

    + inversion apr as [cl]; clear apr.
      unfold close_comput in cl; repnd; GC.
      apply iscan_implies in hv2; repndors; exrepnd; subst.

      * unfold close_compute_val in cl2.
        pose proof (cl2 c bterms) as h.
        clear cl2 cl3 cl4.
        autodimp h hyp.
        { unfold computes_to_value; dands; auto. }
        exrepnd.
        apply computes_to_value_isvalue_eq in h1; eauto 3 with slow;
        try (apply isvalue_iff; dands; simpl; auto).
        unfold mk_lam in h1; ginv.
        dup hv0 as isp.
        destruct hv0 as [c wf].
        apply nt_wf_lambda_iff in wf; exrepnd; subst; fold_terms.

        apply implies_approx_lam2.

        { apply implies_isprogram_bt_lam in isp.
          allrw <- @isprog_vars_iff_isprogram_bt; auto. }

        { apply isprog_vars_apply_implies; eauto 3 with slow. }

        introv ispu.
        applydup @closed_if_isprog in ispu.
        unfold subst.
        repeat (rw @cl_lsubst_lsubst_aux;[|eauto 3 with slow]); simpl; fold_terms.
        autorewrite with slow in *.
        apply cequiv_sym.
        eapply cequiv_trans.

        { apply reduces_to_implies_cequiv.

          - apply isprogram_apply; boolvar; eauto 2 with slow.
            { rw @lsubst_aux_nil; auto. }
            { apply isprogram_lam.
              rw <- @cl_lsubst_lsubst_aux;[|eauto 3 with slow].
              apply isprog_vars_lsubst_prog_sub; simpl; eauto 3 with slow.
              apply implies_isprogram_bt_lam in isp.
              apply isprog_vars_iff_isprogram_bt in isp.
              eapply isprog_vars_subvars;[|eauto].
              rw subvars_prop; simpl; tcsp. }

          - apply reduces_to_if_step; csunf; simpl; eauto. }

        unfold apply_bterm; simpl.
        boolvar; try (rw @lsubst_aux_nil).

        { rw <- @cl_lsubst_lsubst_aux;[|eauto 3 with slow].
          apply cequiv_refl.
          apply implies_isprogram_bt_lam in isp.
          apply isprog_vars_iff_isprogram_bt in isp.
          apply isprogram_lsubst_if_isprog_sub; simpl; eauto 3 with slow.
          apply isprog_vars_eq in isp; repnd.
          rw @subvars_eq in isp0; auto. }

        rw (lsubst_aux_trivial_cl b [(x,u)]); simpl; eauto 3 with slow.

        { rw <- @cl_lsubst_lsubst_aux;[|eauto 3 with slow].
          apply cequiv_refl.
          apply implies_isprogram_bt_lam in isp.
          apply isprog_vars_iff_isprogram_bt in isp.
          apply isprogram_lsubst_if_isprog_sub; simpl; eauto 3 with slow.
          apply isprog_vars_eq in isp; repnd.
          rw @subvars_eq in isp0; auto. }

        apply disjoint_singleton_l; intro xx.
        apply implies_isprogram_bt_lam in isp.
        apply isprog_vars_iff_isprogram_bt in isp.
        apply isprog_vars_eq in isp; repnd.
        rw @subvars_eq in isp0; auto.
        apply isp0 in xx; allsimpl; tcsp.

      * apply cl4 in hv1; clear cl2 cl3 cl4.
        exrepnd.
        apply reduces_to_if_value in hv1; ginv;
        try (apply isvalue_iff; dands; simpl; auto).

    + apply implies_approx_lam2; try (apply isprog_vars_apply_implies);
      eauto 3 with slow.

      introv ispu.
      unfold subst.
      repeat (rw @cl_lsubst_lsubst_aux;[|eauto 3 with slow]); simpl.
      boolvar; tcsp; fold_terms.
      repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow).
      apply sp_implies_cequiv_apply; eauto 2 with slow.
      apply cequiv_sym.
      apply reduces_to_implies_cequiv; eauto 2 with slow.

  - unfold hasvalue in hv; exrepnd.
    unfold computes_to_value in hv0; repnd.
    apply isvalue_iff in hv0; repnd.
    eapply approx_trans;
      [|apply reduces_to_implies_approx1;eauto 3 with slow].

    apply (approx_trans _ _ (mk_lam x (mk_apply t' (mk_var x)))).

    + apply implies_approx_lam2; try (apply isprog_vars_apply_implies);
      eauto 3 with slow.

      introv ispu.
      unfold subst.
      repeat (rw @cl_lsubst_lsubst_aux;[|eauto 3 with slow]); simpl.
      boolvar; tcsp; fold_terms.
      repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow).
      apply sp_implies_cequiv_apply; eauto 2 with slow.
      apply reduces_to_implies_cequiv; eauto 2 with slow.

    + inversion apr as [cl]; clear apr.
      unfold close_comput in cl; repnd; GC.
      apply iscan_implies in hv2; repndors; exrepnd; subst.

      * unfold close_compute_val in cl2.
        pose proof (cl2 c bterms) as h.
        clear cl2 cl3 cl4.
        autodimp h hyp.
        { unfold computes_to_value; dands; auto. }
        exrepnd.
        apply computes_to_value_isvalue_eq in h1; eauto 3 with slow;
        try (apply isvalue_iff; dands; simpl; auto).
        unfold mk_lam in h1; ginv.
        dup hv0 as isp.
        destruct hv0 as [c wf].
        apply nt_wf_lambda_iff in wf; exrepnd; subst; fold_terms.

        apply implies_approx_lam2.

        { apply isprog_vars_apply_implies; eauto 3 with slow. }

        { apply implies_isprogram_bt_lam in isp.
          allrw <- @isprog_vars_iff_isprogram_bt; auto. }

        introv ispu.
        applydup @closed_if_isprog in ispu.
        unfold subst.
        repeat (rw @cl_lsubst_lsubst_aux;[|eauto 3 with slow]); simpl; fold_terms.
        autorewrite with slow in *.
        eapply cequiv_trans.

        { apply reduces_to_implies_cequiv.

          - apply isprogram_apply; boolvar; eauto 2 with slow.
            { rw @lsubst_aux_nil; auto. }
            { apply isprogram_lam.
              rw <- @cl_lsubst_lsubst_aux;[|eauto 3 with slow].
              apply isprog_vars_lsubst_prog_sub; simpl; eauto 3 with slow.
              apply implies_isprogram_bt_lam in isp.
              apply isprog_vars_iff_isprogram_bt in isp.
              eapply isprog_vars_subvars;[|eauto].
              rw subvars_prop; simpl; tcsp. }

          - apply reduces_to_if_step; csunf; simpl; eauto. }

        unfold apply_bterm; simpl.
        boolvar; try (rw @lsubst_aux_nil).

        { rw <- @cl_lsubst_lsubst_aux;[|eauto 3 with slow].
          apply cequiv_refl.
          apply implies_isprogram_bt_lam in isp.
          apply isprog_vars_iff_isprogram_bt in isp.
          apply isprogram_lsubst_if_isprog_sub; simpl; eauto 3 with slow.
          apply isprog_vars_eq in isp; repnd.
          rw @subvars_eq in isp0; auto. }

        rw (lsubst_aux_trivial_cl b [(x,u)]); simpl; eauto 3 with slow.

        { rw <- @cl_lsubst_lsubst_aux;[|eauto 3 with slow].
          apply cequiv_refl.
          apply implies_isprogram_bt_lam in isp.
          apply isprog_vars_iff_isprogram_bt in isp.
          apply isprogram_lsubst_if_isprog_sub; simpl; eauto 3 with slow.
          apply isprog_vars_eq in isp; repnd.
          rw @subvars_eq in isp0; auto. }

        apply disjoint_singleton_l; intro xx.
        apply implies_isprogram_bt_lam in isp.
        apply isprog_vars_iff_isprogram_bt in isp.
        apply isprog_vars_eq in isp; repnd.
        rw @subvars_eq in isp0; auto.
        apply isp0 in xx; allsimpl; tcsp.

      * apply cl4 in hv1; clear cl2 cl3 cl4.
        exrepnd.
        apply reduces_to_if_value in hv1; ginv;
        try (apply isvalue_iff; dands; simpl; auto).
Qed.

Lemma mkc_cv_app_r_mkc_var {o} :
  forall x, mk_cv_app_r [] [x] (mkc_var x) = @mkc_var o x.
Proof.
  introv.
  apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @mkc_cv_app_r_mkc_var : slow.

Lemma if_raises_exceptionc_apply2 {o} :
  forall lib (t a: @CTerm o),
    raises_exceptionc lib (mkc_apply  t a)
    -> raises_exceptionc lib t
       [+] {v : NVar $ {b : CVTerm [v] $ computes_to_valc lib t (mkc_lam v b)}}
       [+] {n: nseq $ computes_to_valc lib t (mkc_nseq n)}
       [+] {n: ntseqc $ computes_to_valc lib t (mkc_ntseq n)}.
Proof.
  introv hv.
  apply if_raises_exceptionc_apply in hv; repndors; exrepnd; tcsp.

  - right; left.
    unfold computes_to_valuec in hv1.
    applydup @computes_to_value_preserves_program in hv1; auto.
    apply isprogram_eq in hv0; apply isprog_lam_iff in hv0.
    exists v (mk_cvterm [v] b hv0).
    unfold computes_to_valc; simpl; auto.

  - right; right; left.
    exists n; auto.

  - right; right; right.
    unfold computes_to_seqnc in hv0.
    unfold computes_to_seq in hv0.
    applydup @reduces_to_preserves_program in hv0; auto.
    rw @isprogram_mk_ntseq in hv1.
    assert (forall x, isprog_nout (n x)) as nout.
    { introv.
      pose proof (hv1 x) as h; clear hv1; repnd.
      destruct h0 as [cl wf].
      apply isprog_nout_iff; dands; auto. }

    exists (fun x => mk_cnterm (n x) (nout x)).
    unfold computes_to_valc, computes_to_value; simpl; auto.
    unfold ntseqc2seq; simpl; dands; auto.
    split; simpl; auto.
    apply nt_wf_sterm_implies_isprogram.
    apply nt_wf_sterm_iff; introv.
    pose proof (nout n0) as h.
    apply isprog_nout_iff in h; sp.
Qed.

Lemma inhabited_type_or {o} :
  forall lib (a b : @CTerm o),
    inhabited_type lib (mkc_or a b)
    <=> ((inhabited_type lib a # type lib b)
         {+} (inhabited_type lib b # type lib a)).
Proof.
  introv; split; intro h.
  - unfold inhabited_type in h; exrepnd.
    apply equality_mkc_or in h0; repnd; repndors; exrepnd.
    + left; dands; auto.
      exists a1.
      apply equality_refl in h0; auto.
    + right; dands; auto.
      exists b1.
      apply equality_refl in h0; auto.
  - repndors; unfold inhabited_type in h; exrepnd.
    + exists (mkc_inl t).
      apply member_mkc_or_inl; dands; auto.
      apply inhabited_implies_tequality in h1; auto.
    + exists (mkc_inr t).
      apply member_mkc_or_inr; dands; auto.
      apply inhabited_implies_tequality in h1; auto.
Qed.

Lemma base_in_uni {p} :
  forall lib i, @member p lib mkc_base (mkc_uni i).
Proof.
  introv.
  unfold member, equality.
  exists (fun A A' => {eqa : per , close lib (univi lib i) A A' eqa}).
  unfold nuprl.
  dands.

  { apply mkc_uni_in_nuprl. }

  { exists (fun t t' => t ~=~(lib) t').
    apply CL_base.
    unfold per_base; dands; spcast; auto;
      apply computes_to_valc_refl; eauto 3 with slow. }
Qed.
