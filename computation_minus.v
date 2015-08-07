(*

  Copyright 2014 Cornell University

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
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export computation_arith.
Require Export cvterm.

Lemma minus_reduces_to_0_sub {o} :
  forall lib t t2,
  isvalue_like t2 ->
  reduces_to lib (@mk_minus o t) t2 ->
   reduces_to lib (mk_arithop ArithOpSub (mk_integer 0) t) t2.
Proof.
  unfold reduces_to; introv val red; exrepnd. revert dependent t.
  induction k; introv red;
  [apply reduces_in_atmost_k_steps_0 in red | apply reduces_in_atmost_k_steps_S in red];
  exrepnd.

  - subst. unfold isvalue_like, mk_minus in val. allsimpl. repndors; inversion val.

  - destruct t as [v|f|op bs].

    + inversion red1.

    + csunf red1; allsimpl; ginv.

    + dopid op as [can|ncan|exc|abs] Case.

      * Case "Can".
        apply compute_step_minus_can_success in red1. exrepnd. subst.
        apply reduces_in_atmost_k_steps_if_isvalue_like in red0; subst;
        try (apply isvalue_like_integer).
        exists 1.
        apply reduces_in_atmost_k_steps_S.
        csunf; simpl; dcwf h; simpl.
        eexists; dands; eauto.
        apply reduces_in_atmost_k_steps_0; auto.

      * Case "NCan".
        rw @compute_step_minus_ncan in red1.
        remember (compute_step lib (oterm (NCan ncan) bs)) as res.
        destruct res; inversion red1; subst; apply IHk in red0.
        exrepnd. exists (S k0). apply reduces_in_atmost_k_steps_S.
        exists (mk_arithop ArithOpSub (mk_integer 0) n); split; auto.
        unfold mk_integer. rw @compute_step_arithop_can_ncan.
        rw<- Heqres; auto. simpl. auto.

      * Case "Exc".
        rw @compute_step_minus_exc in red1. inversion red1. subst.
        apply reduces_in_atmost_k_steps_exception in red0. subst. exists 1.
        apply reduces_in_atmost_k_steps_S.
        csunf; simpl; dcwf h; simpl.
        eexists; dands; eauto.

      * Case "Abs".
        rw @compute_step_minus_abs in red1.
        remember (compute_step lib (oterm (Abs abs) bs)) as res.
        destruct res; inversion red1; subst; apply IHk in red0.
        exrepnd. exists (S k0). apply reduces_in_atmost_k_steps_S.
        exists (mk_arithop ArithOpSub (mk_integer 0) n); split; auto.
        unfold mk_integer. rw @compute_step_arithop_can_abs.
        rw<- Heqres; auto. simpl. auto.
Qed.

(* !!MOVE *)
Lemma if_raises_exception_minus {o} :
  forall lib (t: @NTerm o),
    isprogram t
    -> raises_exception lib (mk_minus t)
    -> raises_exception lib t.
Proof.
  introv isp1 re.
  assert (isprogram (@mk_integer o 0)) as isp0 by eauto.
  assert (raises_exception lib (mk_arithop ArithOpSub (mk_integer 0) t)) as re'.
  - allunfold @raises_exception; exrepnd. exists a e. allunfold @computes_to_exception.
    remember (mk_exception a e) as t2. apply minus_reduces_to_0_sub in re1; auto. subst.
    apply isvalue_like_exc. eauto 3 with slow.
  - pose proof (if_raises_exception_arithop lib ArithOpSub (mk_integer 0) t isp0 isp1 re') as xxx.
    repndors; exrepnd; auto.
    apply raises_exception_can in xxx. inversion xxx. simpl. eauto 3 with slow.
Qed.

(* !!MOVE *)
Lemma if_raises_exceptionc_minus {o} :
  forall lib (t : @CTerm o),
    raises_exceptionc lib (mkc_minus t)
    -> raises_exceptionc lib t.
Proof.
  introv re.
  destruct_cterms.
  allunfold @raises_exceptionc.
  allunfold @computes_to_valc.
  allsimpl.
  pose proof (if_raises_exception_minus lib x ) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
Qed.


Lemma hasvaluec_mkc_minus {q} :
  forall lib t,
    hasvaluec lib (mkc_minus t)
    -> { n : Z $
          computes_to_valc lib t (@mkc_integer q n)
          }.
Proof. introv hv.
  assert (hasvaluec lib (mkc_arithop ArithOpSub (mkc_integer 0) t)) as hvsub.
  - destruct_cterms.
  unfold hasvaluec in hv; unfold hasvaluec; allsimpl.
  unfold hasvalue in hv. exrepnd. exists t'.
  allunfold @computes_to_value. sp.
  apply minus_reduces_to_0_sub in hv1. auto.
  apply isvalue_like_isvalue. auto.
  - apply hasvaluec_mkc_arithop in hvsub. exrepnd. eexists; eauto.
Qed.
