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

Require Export computation8.
Require Export computation_seq.


Lemma compute_step_cbv_ncan {o} :
  forall lib n l x b,
    @compute_step o lib (mk_cbv (oterm (NCan n) l) x b )
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess p => csuccess (mk_cbv p x b)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.

Lemma compute_step_cbv_abs {o} :
  forall lib n l x b,
    @compute_step o lib (mk_cbv (oterm (Abs n) l) x b )
    = match compute_step lib (oterm (Abs n) l) with
        | csuccess p => csuccess (mk_cbv p x b)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.


Lemma compute_step_cbv_exc {o} :
  forall lib l x b,
    @compute_step o lib (mk_cbv (oterm Exc l) x b )
    = csuccess (oterm Exc l).
Proof. introv; csunf; simpl; sp. Qed.


Lemma compute_step_cbv_can {o} :
  forall lib c l x b,
     @compute_step o lib (mk_cbv (oterm (Can c) l) x b ) =
       csuccess (apply_bterm (bterm [x] b) [oterm (Can c) l]).
Proof. introv; unfold mk_arithop; csunf; simpl; sp. 
Qed.

Lemma compute_step_cbv_can_success {o} :
  forall lib c l x b u,
    @compute_step o lib (mk_cbv (oterm (Can c) l) x b )
    = csuccess u ->
             u = (apply_bterm (bterm [x] b) [oterm (Can c) l]).
Proof. introv cs. csunf cs; allsimpl.  allsimpl. inversion cs. auto.
Qed.




Lemma if_computes_to_exc_cbv {q} :
  forall lib n x (t b : @NTerm q) e,
    isprogram t
    -> computes_to_exception lib n (mk_cbv t x b) e
    -> computes_to_exception lib n t e
       [+] hasvalue lib t.
Proof.
 unfold computes_to_exception, reduces_to.
  introv ispt  re; exrepnd.
  revert dependent b.
  revert dependent t.
  induction k; introv ispt  r.

  - apply reduces_in_atmost_k_steps_0 in r; inversion r.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    destruct t as [z|f|op1 bs]; try (complete (inversion r1)).

    { right; eauto 3 with slow. }

    dopid op1 as [can|ncan|exc|abs] Case; try (complete (inversion r1)).

    + Case "Can". right. exists (oterm (Can can) bs). unfold computes_to_value. sp.
       exists 0. apply reduces_in_atmost_k_steps_0. auto.

    + Case "NCan". rw @compute_step_cbv_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan) bs)) as c;
        destruct c; allsimpl; ginv; symmetry in Heqc.

      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in r0; auto.
      repndors; exrepnd.

      { left. exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n0; auto. }

      { right. allunfold @hasvalue. exrepnd.
        exists t'; sp.
       eapply computes_to_value_step; eauto.
     }

    + Case "Exc". rw @compute_step_cbv_exc in r1. inversion r1; subst.
       left. exists 0. apply reduces_in_atmost_k_steps_0.
        apply reduces_in_atmost_k_steps_exception in r0. auto.

    + Case "Abs".
       rw @compute_step_cbv_abs in r1.
      remember (compute_step lib (oterm (Abs abs) bs)) as c;
        destruct c; allsimpl; ginv; symmetry in Heqc.

      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in r0; auto.
      repndors; exrepnd.

      { left. exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n0; auto. }

      { right. allunfold @hasvalue. exrepnd.
        exists t'; sp.
       eapply computes_to_value_step; eauto.
     }
Qed.

(* !!MOVE *)
Lemma if_raises_exception_cbv {o} :
  forall lib x(t b: @NTerm o),
    isprogram t
    -> raises_exception lib (mk_cbv t x b)
    -> raises_exception lib t
       [+] hasvalue lib t.
Proof.
  introv ispt re.
  unfold raises_exception in re; exrepnd.
  pose proof (if_computes_to_exc_cbv lib a x t b e ispt re1 ) as h.
  repndors; exrepnd.
  - left; exists a e; auto.
  - right. auto.
Qed.


(* !!MOVE *)
Lemma if_raises_exceptionc_cbv {o} :
  forall lib x t (b: @CVTerm o [x]),
    raises_exceptionc lib (mkc_cbv t x b)
    -> raises_exceptionc lib t
       [+] hasvaluec lib t.
Proof.
  introv re.
  destruct_cterms. allsimpl.
  allunfold @raises_exceptionc.
  allunfold @computes_to_valc.
  allsimpl.
  pose proof (if_raises_exception_cbv lib x x0 x1 ) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
Qed. 
         

Lemma hasvaluec_mkc_cbv {q} :
  forall lib x t ( b : @CVTerm q [x]),
    hasvaluec lib (mkc_cbv t x b)
    -> hasvaluec lib t.
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv; allsimpl.
  rename x0 into t.
  rename x1 into b.
  destruct hv as [t' c].
  destruct c as [rt iv].
  destruct rt as [k comp].
  unfold hasvaluec. simpl.
  
  revert dependent x.
  revert dependent b.
  revert dependent t.
  revert dependent t'.
  induction k ; introv isv ispt ispb  comp.

  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    inversion isv; allsimpl; tcsp.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct t as [v|f|op bs].

    + inversion comp1.

    + eauto 3 with slow.

    +  dopid op as [can | ncan | ex | abs] Case.

       * Case "Can". exists (oterm (Can can) bs).
        apply computes_to_value_isvalue_refl; eauto 3 with slow.

      * Case "NCan".

        rw @compute_step_cbv_ncan in comp1.
        remember (compute_step lib (oterm (NCan ncan) bs)).
        destruct c; ginv.
        symmetry in Heqc.
        allrw @isprog_eq.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in comp0; auto; exrepnd; try (complete (apply isprog_eq; auto)).
        unfold hasvalue in comp0. exrepnd.
        exists t'0.
        eapply computes_to_value_step; eauto.

      * Case "Exc".
          rw @compute_step_cbv_exc in comp1.
          inversion comp1. subst.
          apply reduces_in_atmost_k_steps_exception in comp0. subst.
         inversion isv; allsimpl; tcsp.

      * Case "Abs".
        rw @compute_step_cbv_abs in comp1.
        remember (compute_step lib (oterm (Abs abs) bs)).
        destruct c; ginv.
        symmetry in Heqc.
        allrw @isprog_eq.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in comp0; auto; exrepnd; try (complete (apply isprog_eq; auto)).
        unfold hasvalue in comp0. exrepnd.
        exists t'0.
        eapply computes_to_value_step; eauto.
Qed.
