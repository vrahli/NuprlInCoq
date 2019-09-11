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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)

Require Export computation8.
Require Export computation_seq.


Lemma compute_step_apply_ncan {o} :
  forall lib n l a ,
    @compute_step o lib (mk_apply (oterm (NCan n) l) a )
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess p => csuccess (mk_apply  p a )
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.

Lemma compute_step_apply_abs {o} :
  forall lib n l a,
    @compute_step o lib (mk_apply (oterm (Abs n) l) a )
    = match compute_step lib (oterm (Abs n) l) with
        | csuccess p => csuccess (mk_apply p a)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.


Lemma compute_step_apply_exc {o} :
  forall lib l a,
    @compute_step o lib (mk_apply (oterm Exc l) a)
    = csuccess (oterm Exc l).
Proof. introv; csunf; simpl; sp. Qed.


Lemma compute_step_apply_can {o} :
  forall lib c l a, 
     @compute_step o lib (mk_apply (oterm (Can c) l) a) =
       compute_step_apply c (mk_apply (oterm (Can c) l) a) l [nobnd a].
Proof. introv; unfold mk_arithop; csunf; simpl; sp. 
Qed.

Lemma compute_step_apply_can_success {o} :
  forall lib c l a u,
    @compute_step o lib (mk_apply (oterm (Can c) l) a) = csuccess u
    ->
    {v : NVar $ {b : NTerm $ c = NLambda
     # l =  [bterm [v] b]
     # u = (apply_bterm (bterm [v] b) [a])}}
    [+] {n : choice_sequence_name $ c = Ncseq n # l = [] # u = mk_eapply (mk_choice_seq n) a}.
Proof.
  introv cs. csunf cs; allsimpl.
  destruct c; inversion cs.

  - destruct l; inversion cs; destruct b; allsimpl; destruct l0; allsimpl; inversion cs.
    destruct l0; allsimpl; destruct l; allsimpl; inversion cs; subst.
    left; exists n0 n; auto.

  - destruct l; simpl in *; ginv; right; eexists; dands; eauto.
Qed.


Lemma if_computes_to_exc_apply {q} :
  forall lib n (t a : @NTerm q) e,
    isprogram t
   -> isprogram a
    -> computes_to_exception lib n (mk_apply t a) e
    -> computes_to_exception lib n t e
       [+] {v : NVar $ {b : NTerm $ computes_to_value lib t (mk_lam v b)}}
       [+] {n: choice_sequence_name $ computes_to_value lib t (mk_choice_seq n)}.
Proof.
 unfold computes_to_exception, reduces_to.
  introv ispt ispa re; exrepnd.
  revert dependent a.
  revert dependent t.
  induction k; introv ispt ispa r.

  - apply reduces_in_atmost_k_steps_0 in r; inversion r.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    destruct t as [z|op1 bs]; try (complete (inversion r1)).

    dopid op1 as [can|ncan|exc|abs] Case; try (complete (inversion r1)).

    + Case "Can".
      apply  @compute_step_apply_can_success in r1; repndors; exrepnd; subst.

      * right. left. exists v b. split; eauto 3 with slow.
        constructor; simpl; auto.

      * right; right; exists n0; eauto 3 with slow.

    + Case "NCan". rw @compute_step_apply_ncan in r1.
      remember (compute_step lib (oterm (NCan ncan) bs)) as c;
        destruct c; allsimpl; ginv; symmetry in Heqc.

      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in r0; auto.
      repndors; exrepnd.

      { left. exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n0; auto. }

      { right. left. allunfold @hasvalue. exrepnd. subst.
        exists v b; sp.
        eapply computes_to_value_step; eauto. }

      { right; right.
        exists n1; eauto 3 with slow. }

    + Case "Exc". rw @compute_step_apply_exc in r1. inversion r1; subst.
       left. exists 0. apply reduces_in_atmost_k_steps_0.
        apply reduces_in_atmost_k_steps_exception in r0. auto.

    + Case "Abs".
       rw @compute_step_apply_abs in r1.
      remember (compute_step lib (oterm (Abs abs) bs)) as c;
        destruct c; allsimpl; ginv; symmetry in Heqc.

      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in r0; auto.
      repndors; exrepnd.

      { left. exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n0; auto. }

      { right. left. allunfold @hasvalue. exrepnd.
        exists v b; sp.
        eapply computes_to_value_step; eauto. }

      { right; right.
        exists n1; eauto 3 with slow. }
Qed.

(* !!MOVE *)
Lemma if_raises_exception_apply {o} :
  forall lib (t a: @NTerm o),
    isprogram t
    -> isprogram a
    -> raises_exception lib (mk_apply t a)
    -> raises_exception lib t
       [+] {v : NVar $ {b : NTerm $ computes_to_value lib t (mk_lam v b)}}
       [+] {n: choice_sequence_name $ computes_to_value lib t (mk_choice_seq n)}.
Proof.
  introv ispt ispa re.
  unfold raises_exception in re; exrepnd.
  pose proof (if_computes_to_exc_apply lib a0 t a e ispt ispa re1 ) as h.
  repndors; exrepnd; eauto.
  - left; eexists; eauto.
Qed.

(* !!MOVE *)
Lemma if_raises_exceptionc_apply {o} :
  forall lib (t a: @CTerm o),
    raises_exceptionc lib (mkc_apply  t a)
    -> raises_exceptionc lib t
       [+] {v : NVar $ {b : NTerm $ computes_to_valuec lib t (mk_lam v b)}}
       [+] {n: choice_sequence_name $ computes_to_valuec lib t (mk_choice_seq n)}.
Proof.
  introv re.
  destruct_cterms. allsimpl.
  allunfold @raises_exceptionc.
  allunfold @computes_to_valuec.
  allsimpl.
  pose proof (if_raises_exception_apply lib x0 x) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
Qed.

Lemma apply_raises_exceptionc_two_cases {o} :
  forall lib  (t a: @CTerm o),
    raises_exceptionc lib (mkc_apply  t a)
    -> raises_exceptionc lib t
       [+] hasvaluec lib t.

Proof.
  introv ex.
  apply if_raises_exceptionc_apply in ex;
  repndors; exrepnd; [left | right | right]; auto;
  allunfold @computes_to_valuec;
  unfold hasvaluec; destruct_cterms; allsimpl;
  eapply @computes_to_value_hasvalue; eauto.
Qed.

Lemma hasvaluec_mkc_apply {q} :
  forall lib (t a : @CTerm q),
    hasvaluec lib (mkc_apply t a)
    -> {v : NVar $ {b : NTerm $ computes_to_valuec lib t (mk_lam v b)}}
       [+] {n: choice_sequence_name $ computes_to_valuec lib t (mk_choice_seq n)}.
Proof.
  introv hv.
  destruct_cterms.
  unfold computes_to_valuec.
  simpl.
  rename x0 into t.
  rename x into a.
  destruct hv as [t' c].
  destruct c as [rt iv].
  allsimpl.
  destruct rt as [k comp].
  revert dependent t.
  revert dependent t'.
  induction k; introv isv ispt comp.

  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    inversion isv; allsimpl; tcsp.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct t as [v|op bs].

    + inversion comp1.

    +  dopid op as [can | ncan | ex | abs] Case.

       * Case "Can".
         apply @compute_step_apply_can_success in comp1; repndors; exrepnd; subst.

         { left; exists v b.
           apply computes_to_value_isvalue_refl. constructor; simpl; auto.
           apply isprogram_eq. auto. }

         { right; exists n; eauto 3 with slow. }

      * Case "NCan".

        rw @compute_step_apply_ncan in comp1.
        remember (compute_step lib (oterm (NCan ncan) bs)).
        destruct c; ginv.
        symmetry in Heqc.

        applydup @preserve_compute_step in Heqc; auto;
        try rw<- @isprog_eq; auto.
        rw<- @isprog_eq in Heqc0.
        apply IHk in comp0; auto; try apply isprog_eq; auto.
        repndors; exrepnd; [left | right ].
        { exists v b.
          eapply computes_to_value_step; eauto. }
        { exists n0. eapply computes_to_value_step; eauto. }

      * Case "Exc".
          rw @compute_step_apply_exc in comp1.
          inversion comp1. subst.
          apply reduces_in_atmost_k_steps_exception in comp0. subst.
         inversion isv; allsimpl; tcsp.

      * Case "Abs".
         rw @compute_step_apply_abs in comp1.
        remember (compute_step lib (oterm (Abs abs) bs)).
        destruct c; ginv.
        symmetry in Heqc.

        applydup @preserve_compute_step in Heqc; auto;
        try rw<- @isprog_eq; auto.
        rw<- @isprog_eq in Heqc0.
        apply IHk in comp0; auto; try apply isprog_eq; auto.
        repndors; exrepnd; [left | right ].
        { exists v b.
          eapply computes_to_value_step; eauto. }
        { exists n0;  eapply computes_to_value_step; eauto. }
Qed.

Lemma hasvaluec_mkc_apply_implies_hasvaluec {q} :
  forall lib (t a : @CTerm q),
    hasvaluec lib (mkc_apply t a)
    -> hasvaluec lib t .
Proof.
  introv hv.
  apply hasvaluec_mkc_apply in  hv.
  repndors; exrepnd;
  allunfold @computes_to_valuec;
  unfold hasvaluec; destruct_cterms; allsimpl;
  eapply @computes_to_value_hasvalue; eauto.
Qed.
