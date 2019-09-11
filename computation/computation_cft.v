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



Lemma isprogram_can_test {p} :
  forall test (a b c : @NTerm p),
    isprogram a
    -> isprogram b
    -> isprogram c
    -> isprogram (mk_can_test test a b c).
Proof.
  introv ipa ipb ipc.
  allunfold @isprogram; repnd; allunfold @closed; simpl; allrw; simpl; sp.
  constructor; sp; allsimpl; sp; subst; constructor; sp.
Qed.
Lemma isprogram_can_test_iff {p} :
  forall test (a b c : @NTerm p),
    (isprogram a # isprogram b # isprogram c) <=> isprogram (mk_can_test test a b c).
Proof.
  introv; split; intro i; repnd.
  apply isprogram_can_test; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| | o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Lemma compute_step_can_test_ncan {o} :
  forall lib n l test a b,
    @compute_step o lib (mk_can_test test (oterm (NCan n) l) a b )
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess p => csuccess (mk_can_test test p a b)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.

Lemma compute_step_can_test_abs {o} :
  forall lib n l test a b,
    @compute_step o lib (mk_can_test test (oterm (Abs n) l) a b )
    = match compute_step lib (oterm (Abs n) l) with
        | csuccess p => csuccess (mk_can_test test p a b)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.


Lemma compute_step_can_test_exc {o} :
  forall lib l test a b,
    @compute_step o lib (mk_can_test test (oterm Exc l) a b )
    = csuccess (oterm Exc l).
Proof. introv; csunf; simpl; sp. Qed.


Lemma compute_step_can_test_can {o} :
  forall lib c l test a b, 
     @compute_step o lib (mk_can_test test (oterm (Can c) l) a b ) =
       csuccess (if canonical_form_test_for test c then a else b).
Proof. introv; unfold mk_arithop; csunf; simpl; sp. 
Qed.

Lemma compute_step_can_test_can_success {o} :
  forall lib c l test a b u,
    @compute_step o lib (mk_can_test test (oterm (Can c) l) a b )
    = csuccess u ->
             u = (if canonical_form_test_for test c then a else b).
Proof. introv cs. csunf cs; allsimpl.  allsimpl. inversion cs. auto.
Qed.

Lemma if_computes_to_exc_can_test {q} :
  forall lib n test (t a b : @NTerm q) e,
    isprogram t
   -> isprogram a
   -> isprogram b
    -> computes_to_exception lib n (mk_can_test test t a b) e
    -> computes_to_exception lib n t e
       [+] hasvalue lib t.
Proof.
 unfold computes_to_exception, reduces_to.
  introv ispt ispa ispb re; exrepnd.
  revert dependent b.
  revert dependent a.
  revert dependent t.
  induction k; introv ispt ispa ispb r.

  - apply reduces_in_atmost_k_steps_0 in r; inversion r.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    destruct t as [z|f|op1 bs]; try (complete (inversion r1; allsimpl; tcsp));[|].

    { right; eauto 3 with slow. }

    dopid op1 as [can|ncan|exc|abs] Case; try (complete (inversion r1)).

    + Case "Can". right. exists (oterm (Can can) bs). unfold computes_to_value. sp.
       exists 0. apply reduces_in_atmost_k_steps_0. auto.

    + Case "NCan". rw @compute_step_can_test_ncan in r1.
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

    + Case "Exc". rw @compute_step_can_test_exc in r1. inversion r1; subst.
       left. exists 0. apply reduces_in_atmost_k_steps_0.
        apply reduces_in_atmost_k_steps_exception in r0. auto.

    + Case "Abs".
       rw @compute_step_can_test_abs in r1.
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
Lemma if_raises_exception_can_test {o} :
  forall lib test (t a b: @NTerm o),
    isprogram t
    -> isprogram a
    -> isprogram b
    -> raises_exception lib (mk_can_test test t a b)
    -> raises_exception lib t
       [+] hasvalue lib t.
Proof.
  introv ispt ispa ispb re.
  unfold raises_exception in re; exrepnd.
  pose proof (if_computes_to_exc_can_test lib a0 test t a b e ispt ispa ispb re1 ) as h.
  repndors; exrepnd.
  - left; exists a0 e; auto.
  - right. auto.
Qed.


(* !!MOVE *)
Lemma if_raises_exceptionc_can_test {o} :
  forall lib test (t a b: @CTerm o),
    raises_exceptionc lib (mkc_can_test test t a b)
    -> raises_exceptionc lib t
       [+] hasvaluec lib t.
Proof.
  introv re.
  destruct_cterms. allsimpl.
  allunfold @raises_exceptionc.
  allunfold @computes_to_valc.
  allsimpl.
  pose proof (if_raises_exception_can_test lib test x1 x0 x ) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
Qed.

Lemma hasvaluec_mkc_can_test {q} :
  forall lib test (t u v : @CTerm q),
    hasvaluec lib (mkc_can_test test t u v)
    -> hasvaluec lib t.
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv; allsimpl.
  rename x1 into t.
  rename x0 into u.
  rename x into v.
  destruct hv as [t' c].
  destruct c as [rt iv].
  destruct rt as [k comp].
  unfold hasvaluec. simpl.

  revert dependent v.
  revert dependent u.
  revert dependent test.
  revert dependent t.
  revert dependent t'.
  induction k; introv isv ispt ispu ispv comp.

  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    inversion isv; allsimpl; tcsp.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct t as [v1|f|op bs].

    + inversion comp1.

    + eauto 3 with slow.

    +  dopid op as [can | ncan | ex | abs] Case.

       * Case "Can". exists (oterm (Can can) bs).
         apply computes_to_value_isvalue_refl; eauto 3 with slow.

       * Case "NCan".
         rw @compute_step_can_test_ncan in comp1.
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
        rw @compute_step_can_test_exc in comp1.
        inversion comp1. subst.
        apply reduces_in_atmost_k_steps_exception in comp0. subst.
        inversion isv; allsimpl; tcsp.

      * Case "Abs".
        rw @compute_step_can_test_abs in comp1.
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
