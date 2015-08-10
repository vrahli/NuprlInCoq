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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)

Require Export computation4.

Lemma isprog_inl_iff {p} :
  forall a : @NTerm p, isprog (mk_inl a) <=> (isprog a).
Proof.
  introv; split; intro k.
  - allrw @isprog_eq.
    destruct k as [c w].
    inversion w as [| | o lnt j e ]; subst.
    generalize (j (nobnd a)); intros i1; allsimpl.
    repeat (autodimp i1 hyp).
    unfold isprogram.
    inversion c as [pp]. allrw remove_nvars_nil_l; allrw app_nil_r.
    inversion i1; subst. sp.
  - apply isprog_inl; sp.
Qed.

Lemma isprog_inr_iff {p} :
  forall a : @NTerm p, isprog (mk_inr a) <=> (isprog a).
Proof.
  introv; split; intro k.
  - allrw @isprog_eq.
    destruct k as [c w].
    inversion w as [| | o lnt j e ]; subst.
    generalize (j (nobnd a)); intros i1; allsimpl.
    repeat (autodimp i1 hyp).
    unfold isprogram.
    inversion c as [pp]. allrw remove_nvars_nil_l; allrw app_nil_r.
    inversion i1; subst. sp.
  - apply isprog_inr; sp.
Qed.

Lemma isvalue_inl {p} :
  forall (a : @NTerm p), isprogram a ->  isvalue (mk_inl a).
Proof.
 introv ispa.
 constructor; simpl; auto.
 apply isprogram_inl; auto.
Qed.

Lemma isvalue_inr {p} :
  forall (a : @NTerm p), isprogram a ->  isvalue (mk_inr a).
Proof.
 introv ispa.
 constructor; simpl; auto.
 apply isprogram_inr; auto.
Qed.
Hint Resolve isvalue_inr isvalue_inl : slow.

Lemma compute_step_decide_ncan {o} :
  forall lib n l x y b1 b2,
    @compute_step o lib (mk_decide (oterm (NCan n) l) x b1 y b2)
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess p => csuccess (mk_decide p x b1 y b2)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.

Lemma hasvaluec_mkc_decide {q} :
  forall lib p x y t1 t2,
    hasvaluec lib (mkc_decide p x t1 y t2)
    -> {a : @CTerm q $
          computes_to_valc lib p (mkc_inl a)
           [+]
          computes_to_valc lib p (mkc_inr a)
       }.
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv; allsimpl.
  rename x0 into p.
  rename x1 into t2.
  rename x2 into t1.
  unfold computes_to_valc; simpl.
  destruct hv as [t' c].
  destruct c as [rt iv].
  destruct rt as [k comp].
  revert dependent p.
  induction k; introv isp comp.

  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    inversion iv; allsimpl; tcsp.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct p as [v|f|op bs].

    + inversion comp1.

    + csunf comp1; allsimpl; ginv.

    +  dopid op as [can | ncan | ex | abs] Case.

       * Case "Can".
         csunf comp1. allsimpl. apply compute_step_decide_success in comp1; exrepnd.
         subst; cpx. repndors; exrepnd; subst; fold_terms.
         { rw @isprog_inl_iff in isp. exists (mk_ct d isp). simpl. left.
           apply computes_to_value_isvalue_refl; sp. eauto 3 with slow.
         }
         { rw @isprog_inr_iff in isp. exists (mk_ct d isp). simpl. right.
           apply computes_to_value_isvalue_refl; sp. eauto 3 with slow.
         }

      * Case "NCan".
        rw @compute_step_decide_ncan in comp1.
        remember (compute_step lib (oterm (NCan ncan) bs)).
        destruct c; ginv.

        symmetry in Heqc.
        allrw @isprog_eq.
        applydup @preserve_compute_step in Heqc; auto.
        apply IHk in comp0; auto; exrepnd; try (complete (apply isprog_eq; auto)).
        exists a. repndors; [left | right];
        eapply computes_to_value_step; eauto.

      * Case "Exc".
        simpl in comp1. csunf comp1; allsimpl; ginv.
        apply reduces_atmost_exc in comp0; subst.
        inversion iv; allsimpl; tcsp.

      * Case "Abs".
        csunf comp1; simpl in comp1; unfold on_success in comp1; csunf comp1; allsimpl.
        remember (compute_step_lib lib abs bs) as csl.
        destruct csl; inversion comp1; subst; GC.
        symmetry in Heqcsl.
        rw @isprog_eq in isp.
        applydup @isprogram_compute_step_lib in Heqcsl; auto.
        rw <- @isprog_eq in Heqcsl0.
        apply IHk in comp0; auto; exrepnd.
        exists a; repndors; [ left | right ]; eapply computes_to_value_step; eauto.
Qed.


Lemma if_computes_to_exception_decide0 {o} :
  forall lib n (t : @NTerm o) x y u v e,
    isprogram t
    -> computes_to_exception lib n (mk_decide t x u y v) e
    -> computes_to_exception lib n t e
       [+] {a : NTerm
            & computes_to_value lib t (mk_inl a)
            # computes_to_exception lib n (lsubst u [(x,a)]) e}

       [+] {a : NTerm
            & computes_to_value lib t (mk_inr a)
            # computes_to_exception lib n (lsubst v [(y,a)]) e}.
Proof.
  unfold computes_to_exception, reduces_to.
  introv ispt re; exrepnd.
  revert dependent t.
  revert x y u v.
  induction k; introv ispt r.

  - apply reduces_in_atmost_k_steps_0 in r; inversion r.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    csunf r1; allsimpl.
    destruct t as [z|f|op bs]; try (complete (inversion r1));[].
    dopid op as [can|ncan|exc|abs] Case; try (complete (inversion r1)).

    + Case "Can".
      apply compute_step_decide_success in r1; exrepnd; subst; ginv.
      right. repndors; [left | right]; repnd; subst; exists d; dands; eauto 3 with slow;
      allrw <- @isprogram_inl_iff; repnd;
      allrw <- @isprogram_inr_iff; repnd;
      apply computes_to_value_isvalue_refl; eauto 3 with slow.

    + Case "NCan".
      remember (compute_step lib (oterm (NCan ncan) bs)) as c;
        destruct c; allsimpl; ginv; symmetry in Heqc.

      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in r0; auto.
      repndors; exrepnd.

      { left.
        exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n0; auto. }

      { right. left.
        exists a; sp.
        { eapply computes_to_value_step; eauto. }
        exists k0; auto. }
      { right. right.
        exists a; sp.
        { eapply computes_to_value_step; eauto. }
        exists k0; auto. }

    + Case "Exc".
      ginv.
      left.
      exists k; auto.

    + Case "Abs".
      csunf r1; allsimpl.
      remember (compute_step_lib lib abs bs) as c;
        destruct c; allsimpl; symmetry in Heqc; ginv.

      applydup @isprogram_compute_step_lib in Heqc; auto.
      apply IHk in r0; auto.
      repndors; exrepnd.

      { left.
        exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n0; auto. }

      { right. left.
        exists a; sp.
        { eapply computes_to_value_step; eauto. }
        exists k0; auto. }
      { right. right.
        exists a; sp.
        { eapply computes_to_value_step; eauto. }
        exists k0; auto. }
  
Qed.

(* !!MOVE *)
Lemma if_raises_exception_decide0 {o} :
  forall lib (t : @NTerm o) x y u v,
    isprogram t
    -> raises_exception lib (mk_decide t x u y v)
    -> raises_exception lib t
       [+] {a : NTerm
            & computes_to_value lib t (mk_inl a)
            # raises_exception lib (lsubst u [(x,a)]) }
       [+] {a : NTerm
            & computes_to_value lib t (mk_inr a)
            # raises_exception lib (lsubst v [(y,a)])}.
Proof.
  introv isp re.
  unfold raises_exception in re; exrepnd.
  pose proof (if_computes_to_exception_decide0 lib a t x y u v e isp re1) as h.
  repndors; exrepnd.
  - left; exists a e; auto.
  - right. left.
    exists a0; dands; auto.
    exists a e; auto.
  - right. right.
    exists a0; dands; auto.
    exists a e; auto.
Qed.

(* !!MOVE *)
Lemma if_raises_exceptionc_decide0 {o} :
  forall lib (t : @CTerm o) x y u v,
    raises_exceptionc lib (mkc_decide t x u y v)
    -> raises_exceptionc lib t
       [+] {a : CTerm
            & computes_to_valc lib t (mkc_inl a)
            # raises_exceptionc lib (substc a x u) }
       [+] {a : CTerm
            & computes_to_valc lib t (mkc_inr a)
            # raises_exceptionc lib (substc a y v) }.
Proof.
  introv re.
  destruct_cterms.
  allunfold @raises_exceptionc.
  allunfold @computes_to_valc.
  allsimpl.
  pose proof (if_raises_exception_decide0 lib x0 x y x2 x1) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
  repndors; exrepnd; tcsp; right; [left | right].
  -
  applydup @preserve_program in h1; eauto 3 with slow.
  allrw <- @isprogram_inl_iff; repnd.
  exists (mk_cterm a h2); simpl.
  dands; auto.
 -applydup @preserve_program in h1; eauto 3 with slow.
  allrw <- @isprogram_inr_iff; repnd.
  exists (mk_cterm a h2); simpl.
  dands; auto.
Qed.
