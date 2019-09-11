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
Require Export cvterm.


Lemma compute_step_less_ncan {o} :
  forall lib n l b c d,
    @compute_step o lib (mk_less (oterm (NCan n) l) b c d )
    = match compute_step lib (oterm (NCan n) l) with
        | csuccess p => csuccess (mk_less p b c d)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.

Lemma compute_step_less_abs {o} :
  forall lib n l b c d,
    @compute_step o lib (mk_less (oterm (Abs n) l) b c d )
    = match compute_step lib (oterm (Abs n) l) with
        | csuccess p => csuccess (mk_less p b c d)
        | cfailure str ts => cfailure str ts
      end.
Proof. introv; csunf; simpl; sp. Qed.


Lemma compute_step_less_exc {o} :
  forall lib l b c d,
    @compute_step o lib (mk_less (oterm Exc l) b c d)
    = csuccess (oterm Exc l).
Proof. introv; csunf; simpl; sp. Qed.

Lemma compute_step_less_can_can {o} :
  forall lib c1 c2 l1 l2 c d , co_wf CompOpLess c1 l1 = true ->
     @compute_step o lib (mk_less (oterm (Can c1) l1) (oterm (Can c2) l2) c d ) =
     compute_step_comp CompOpLess c1 c2 l1 l2 [nobnd c, nobnd d]
       (oterm (NCan (NCompOp CompOpLess))
          [nobnd (oterm (Can c1) l1), nobnd (oterm (Can c2) l2), 
          nobnd c, nobnd d]) .
Proof. introv; unfold mk_less; csunf; simpl; sp. 
      unfold co. unfold co_aux. remember (co_wf CompOpLess c1 l1) as b; destruct b; [inversion H | sp].
      sp.
Qed.


Lemma compute_step_less_can_can_success {o} :
  forall lib c c2 l1 l2 t1 t2 u,
    @compute_step o lib (mk_less (oterm (Can c) l1) (oterm (Can c2) l2) t1 t2 )
    = csuccess u ->
 { z:Z $ { z0: Z $ u = (if Z_lt_le_dec z z0 then t1 else t2)
             # l1 = []  # l2 = []
             # c = Nint z # c2 = Nint z0
 }}.
Proof.
  introv cs.
  rw  @compute_step_less_can_can in cs.
  unfold compute_step_comp in cs. destruct l1; destruct l2; allsimpl; inversion cs.
  destruct c; allsimpl; inversion cs. destruct c2; allsimpl; inversion cs.
  exists z z0; sp; auto.
  csunf cs; allsimpl; dcwf h.
Qed.

Lemma compute_step_less_can_ncan {o} :
  forall lib c n l1 l2 t1 t2 , co_wf CompOpLess c l1 = true ->
    @compute_step o lib (mk_less (oterm (Can c) l1) (oterm (NCan n) l2) t1 t2 )
    = match compute_step lib (oterm (NCan n) l2) with
        | csuccess p => csuccess (mk_less (oterm (Can c)  l1) p t1 t2)
        | cfailure str ts => cfailure str ts
      end.
Proof.
  introv; unfold mk_arithop; csunf; simpl; dcwf h; tcsp.
Qed.

Lemma compute_step_less_can_ncan_success {o} :
  forall lib c n l1 l2 t1 t2 u,
    @compute_step o lib (mk_less (oterm (Can c) l1) (oterm (NCan n) l2) t1 t2 )
    = csuccess u ->
    { p: NTerm $ u = mk_less (oterm (Can c) l1) p t1 t2
                # compute_step lib (oterm (NCan n) l2) = csuccess p
    }.
Proof.
  introv comp.
  csunf comp; allsimpl; dcwf h; allsimpl.
  remember (compute_step lib (oterm (NCan n) l2)) as cs; destruct cs; ginv.
  eexists; dands; eauto; auto.
Qed.

Lemma compute_step_less_can_abs {o} :
  forall lib c n l1 l2 t1 t2 , co_wf CompOpLess c l1 = true ->
    @compute_step o lib (mk_less (oterm (Can c) l1) (oterm (Abs n) l2) t1 t2 )
    = match compute_step lib (oterm (Abs n) l2) with
        | csuccess p => csuccess (mk_less (oterm (Can c)  l1) p t1 t2)
        | cfailure str ts => cfailure str ts
      end.
Proof.
  introv h.
  csunf; simpl; dcwf q.
Qed.

Lemma compute_step_less_can_abs_success {o} :
  forall lib c n l1 l2 t1 t2 u,
    @compute_step o lib (mk_less (oterm (Can c) l1) (oterm (Abs n) l2) t1 t2 )
    = csuccess u ->
    { p: NTerm $ u = mk_less (oterm (Can c) l1) p t1 t2
                # compute_step lib (oterm (Abs n) l2) = csuccess p
    }.
Proof.
  introv comp.
  csunf comp; allsimpl; dcwf h; allsimpl.
  remember (compute_step lib (oterm (Abs n) l2)) as cs; destruct cs; ginv.
  eexists; dands; eauto; auto.
Qed.

Lemma compute_step_less_can_vterm {o} :
  forall lib c v l1 t1 t2 , co_wf CompOpLess c l1 = true ->
    @compute_step o lib (mk_less (oterm (Can c) l1) (vterm v) t1 t2 )
    =  cfailure compute_step_error_not_closed (oterm (NCan (NCompOp CompOpLess))
            [nobnd (oterm (Can c) l1), nobnd (vterm v), nobnd t1, nobnd t2]).
Proof.
  introv; unfold mk_less; csunf; simpl; dcwf h; tcsp.
Qed.


Lemma compute_step_less_can_vterm_success {o} :
  forall lib c v l1 t1 t2 u ,
    !@compute_step o lib (mk_less (oterm (Can c) l1) (vterm v) t1 t2 )
    = csuccess u .
Proof.
  introv comp.
  csunf comp; allsimpl; dcwf h.
Qed.

Lemma compute_step_less_can_exc {o} :
  forall lib c v l1 t1 t2 , co_wf CompOpLess c l1 = true ->
    @compute_step o lib (mk_less (oterm (Can c) l1) (oterm Exc v) t1 t2 )
    = csuccess (oterm Exc v).
Proof.
  introv q.
  csunf; simpl; dcwf h.
Qed.

Lemma compute_step_less_can_exc_success {o} :
  forall lib c v l1 t1 t2 u ,
    @compute_step o lib (mk_less (oterm (Can c) l1) (oterm Exc v) t1 t2 )
    = csuccess u -> {z: Z $  u = (oterm Exc v) # l1 = [] #  c = Nint z} .
Proof.
  introv comp.
  csunf comp; allsimpl; dcwf h; allsimpl; ginv.
  unfold co_wf_def in Heqh; exrepnd; subst.
  allrw @get_param_from_cop_some; subst.
  repndors; ginv.
  exrepnd; subst; GC; simpl.
  eexists; dands; eauto.
Qed.

Lemma hasvaluec_mkc_less {q} :
  forall lib a b t1 t2,
    hasvaluec lib (mkc_less a b t1 t2)
    -> {n1: Z $
       { n2 : Z $
          computes_to_valc lib a (mkc_integer n1)
           #
          computes_to_valc lib b (@mkc_integer q n2)
       }}.
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv; allsimpl.
  rename x2 into a.
  rename x1 into b.
  rename x0 into t1.
  rename x into  t2.
  unfold computes_to_valc; simpl.
  destruct hv as [t' c].
  destruct c as [rt iv].
  destruct rt as [k comp].
  revert dependent t2.
  revert dependent t1.
  revert dependent a.
  revert dependent b.
  induction k; introv isb isa is1 is2 comp.

  - rw @reduces_in_atmost_k_steps_0 in comp; subst.
    inversion iv; allsimpl; tcsp.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    destruct a as [v|f|op bs].

    + inversion comp1.

    + csunf comp1; allsimpl; ginv.

    +  dopid op as [can | ncan | ex | abs] Case.

       * Case "Can".
         destruct b as [v|f|op bs1].

         {apply (@compute_step_less_can_vterm_success q) in comp1. inversion comp1. }

         { csunf comp1; allsimpl; ginv; dcwf h. }

         { dopid op as [bcan | bncan | bex | babs] BCase.

           - (* BCase = "Can" *)
             apply compute_step_less_can_can_success in comp1; sp; subst.
             exists z z0. split; apply computes_to_value_isvalue_refl; eauto 3 with slow.

           - (* BCase = "NCan" *)
             apply (@compute_step_less_can_ncan_success q) in comp1. sp. subst.
             apply IHk in comp0; auto. sp.

             + exists n1 n2; split; auto.
               apply (@computes_to_value_step q lib (oterm (NCan bncan) bs1) p (mk_integer n2));auto.

             + apply (@isprogram_eq q).
               apply (@preserve_compute_step q lib (oterm (NCan bncan) bs1) p);
                 auto; apply (@isprogram_eq q); auto.

           - (* BCase = "Exc" *)
             apply (@compute_step_less_can_exc_success q) in comp1; exrepnd; subst.
             apply reduces_in_atmost_k_steps_exception in comp0. subst.
             inversion iv; allsimpl; tcsp.

           - (* BCase = "Abs" *)
             apply (@compute_step_less_can_abs_success q) in comp1. sp. subst.
             apply IHk in comp0; auto. sp.

             + exists n1 n2; split; auto.
               apply (@computes_to_value_step q lib (oterm (Abs babs) bs1) p (mk_integer n2));auto.

             + apply (isprogram_eq). eapply preserve_compute_step; eauto 3 with slow.
         }

       * Case "NCan".

         rw @compute_step_less_ncan in comp1.
         remember (compute_step lib (oterm (NCan ncan) bs)).
         destruct c; ginv.

         symmetry in Heqc.
         allrw @isprog_eq.
         applydup @preserve_compute_step in Heqc; auto.
         apply IHk in comp0; auto; exrepnd; try (complete (apply isprog_eq; auto)).
         exists n1 n2; split; auto.
         eapply computes_to_value_step; eauto.

       * Case "Exc".
         simpl in comp1. csunf comp1; allsimpl; ginv.
         apply reduces_atmost_exc in comp0; subst.
         inversion iv; allsimpl; tcsp.

       * Case "Abs".
         csunf comp1; simpl in comp1; unfold on_success in comp1; csunf comp1; allsimpl.
         remember (compute_step_lib lib abs bs) as csl.
         destruct csl; inversion comp1; subst.  GC.
         symmetry in Heqcsl.
         rw @isprog_eq in isb.
         applydup @isprogram_compute_step_lib in Heqcsl; auto.
         rw <- @isprog_eq in Heqcsl0.
         apply IHk in comp0; auto; exrepnd.
         exists n1 n2; split; auto. eapply computes_to_value_step; eauto.
         rw @isprog_eq; auto.
         rw<- @isprog_eq; auto.
Qed.

Lemma if_computes_to_exc_less {q} :
  forall lib n (a b t1 t2 : @NTerm q) e,
    isprogram a
    -> isprogram b
    -> isprogram t1
    -> isprogram t2
    -> computes_to_exception lib n (mk_less a b t1 t2) e
    -> computes_to_exception lib n a e
       [+] {z : Z
            & computes_to_value lib a (mk_integer z)
            # computes_to_exception lib n b e}
       [+] { z :Z
            & {z' :Z
            & computes_to_value lib a (mk_integer z)
            # computes_to_value lib b (mk_integer z')}}.
Proof.
 unfold computes_to_exception, reduces_to.
  introv ispa ispb ispt1 ispt2 re; exrepnd.
  revert dependent t2.
  revert dependent t1.
  revert dependent b.
  revert dependent a.
  induction k; introv ispa ispb ispt1 ispt2 r.

  - apply reduces_in_atmost_k_steps_0 in r; inversion r.

  - rw @reduces_in_atmost_k_steps_S in r; exrepnd.
    destruct a as [z|f|op1 bs]; try (complete (inversion r1));[].
    dopid op1 as [can|ncan|exc|abs] Case; try (complete (inversion r1)).

    + Case "Can".

      destruct b as [v|f|op bs1].

      { apply (@compute_step_less_can_vterm_success q) in r1. inversion r1. }

      { csunf r1; allsimpl; ginv; dcwf h. }

      { dopid op as [bcan | bncan | bex | babs] SCase.

        - SCase "Can".
          apply (@compute_step_less_can_can_success q) in r1; sp; subst.
          right. right. exists z z0. split.
          + fold (@mk_integer q z). eauto 3 with slow.
          + fold (@mk_integer q z0). eauto 3 with slow.

        - SCase "NCan".
          apply (@compute_step_less_can_ncan_success q) in r1. exrepnd. subst.
          assert (isprogram p) as ispp by
                (apply (@preserve_compute_step q lib (oterm (NCan bncan) bs1) p);
                 auto; apply (@isprogram_eq q); auto).
          apply IHk in r0; auto. repndors; exrepnd.
          + left. exists ( k0); auto.
          + right. left. exists z. split; auto. exists (S k0).
            rw @reduces_in_atmost_k_steps_S. exists p. auto.
          + right. right. exists z z'; split; auto.
            pose proof  (@computes_to_value_step q lib (oterm (NCan bncan) bs1) p (mk_integer z')) as xx.
            apply xx; auto.

        - SCase "Exc".
          apply (@compute_step_less_can_exc_success q) in r1; exrepnd; subst.
          right. left. exists z. dands. eauto 3 with slow. exists k; auto.

        - SCase "Abs".
          apply (@compute_step_less_can_abs_success q) in r1.
          exrepnd. subst.
          assert (isprogram p) as ispp by
                (apply (@preserve_compute_step q lib (oterm (Abs babs) bs1) p);
                 auto; apply (@isprogram_eq q); auto).
          apply IHk in r0; auto. repndors; exrepnd.
          + left. exists ( k0);  auto.
          + right. left. exists z. split; auto. exists (S k0).
            rw @reduces_in_atmost_k_steps_S. exists p. auto.
          + right. right. exists z z'; split; auto.
            pose proof  (@computes_to_value_step q lib (oterm (Abs babs) bs1) p (mk_integer z')) as xx.
            apply xx; auto.
      }

    + Case "NCan".
      csunf r1; allsimpl.
      remember (compute_step lib (oterm (NCan ncan) bs)) as c;
        destruct c; allsimpl; ginv; symmetry in Heqc.

      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in r0; auto.
      repndors; exrepnd.

      { left. exists (S k0).
        rw @reduces_in_atmost_k_steps_S.
        exists n0; auto. }

      { right. left.
        exists z; sp.
        { eapply computes_to_value_step; eauto. }
        exists k0; auto. }

      { right. right. exists z z'. split; auto.
         pose proof  (@computes_to_value_step q lib (oterm (NCan ncan) bs) n0 (mk_integer z)) as xx.
         apply xx; auto. }

    + Case "Exc".
      csunf r1; allsimpl.
      ginv.
      left.
      exists k; auto.

    + Case "Abs".
      csunf r1; allsimpl.
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
        exists z; sp.
        { eapply computes_to_value_step; eauto. }
        exists k0; auto. }

      { right. right. exists z z'; split; auto.
        pose proof  (@computes_to_value_step q lib (oterm (Abs abs) bs)  n0 (mk_integer z)) as xx.
        apply xx; auto. }
Qed.

(* !!MOVE *)
Lemma if_raises_exception_less {o} :
  forall lib (a b t1 t2: @NTerm o),
    isprogram a
    -> isprogram b
    -> isprogram t1
    -> isprogram t2
    -> raises_exception lib (mk_less a b t1 t2)
    -> raises_exception lib a
       [+] {z : Z
            & computes_to_value lib a (mk_integer z)
            # raises_exception lib b }
       [+] { z :Z 
           & {z' :Z
           & computes_to_value lib a (mk_integer z)
             # computes_to_value lib b (mk_integer z')}}.
Proof.
  introv ispa ispb isp1 isp2 re.
  unfold raises_exception in re; exrepnd.
  pose proof (if_computes_to_exc_less lib a0 a b t1 t2 e ispa ispb isp1 isp2  re1) as h.
  repndors; exrepnd.
  - left; exists a0 e; auto.
  - right. left. 
    exists z; dands; auto.
    exists a0 e; auto.
  - right. right. exists z z'. split; auto.
Qed.

(* !!MOVE *)
Lemma if_raises_exceptionc_less {o} :
  forall lib  (a b t1 t2 : @CTerm o),
    raises_exceptionc lib (mkc_less a b t1 t2)
    -> raises_exceptionc lib a
       [+] {z : Z 
            & computes_to_valc lib a (mkc_integer z)
            # raises_exceptionc lib b }  
       [+] { z :Z 
           & {z' :Z
           & computes_to_valc lib a (mkc_integer z)
             # computes_to_valc lib b (mkc_integer z')}}.

Proof.
  introv re.
  destruct_cterms.
  allunfold @raises_exceptionc.
  allunfold @computes_to_valc.
  allsimpl.
  pose proof (if_raises_exception_less lib x2 x1 x0 x ) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
Qed.
