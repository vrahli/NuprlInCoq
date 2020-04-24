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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export approx_star_swap.


Lemma isprogram_swap_cs0_implies {p} :
  forall (bterms : list (@BTerm p)),
    isprogram (oterm (NCan NSwapCs0) bterms)
    -> {a : NTerm
        $ {b : NTerm
        $ {c : NTerm
           $ bterms = [bterm [] a, bterm [] b, bterm [] c]
           # isprogram a
           # isprogram b
           # isprogram c }}}.
Proof.
  introv isp.
  apply isprogram_ot_iff in isp; simpl in isp; repnd.
  repeat (destruct bterms; allsimpl; cpx).
  allunfold @num_bvars.
  destruct b, b0, b1; simpl in *; ginv.
  destruct l, l0, l1; simpl in *; ginv.
  eexists; eexists; eexists; dands; eauto;
    dLin_hyp; allapply @isprogram_bt_nobnd; auto.
Qed.

Lemma computes_to_val_like_in_max_k_steps_swap_cs0_implies {p} :
  forall lib k n1 n2 n3 v,
    wf_term n1
    -> wf_term n2
    -> wf_term n3
    -> computes_to_val_like_in_max_k_steps lib
         (oterm (NCan NSwapCs0) [nobnd n1,nobnd n2,nobnd n3])
         v
         k
    -> {c1, c2 : choice_sequence_name
       $ { k1 , k2 : nat
       $ k1+k2+1 <= k
       # computes_to_can_in_max_k_steps lib k1 n1 (mk_choice_seq c1)
       # computes_to_can_in_max_k_steps lib k2 n2 (mk_choice_seq c2)
       # reduces_in_atmost_k_steps lib
           (oterm (NCan NSwapCs1) [nobnd n1,nobnd n2,nobnd n3])
           (oterm (NCan NSwapCs1)
                  [nobnd (mk_choice_seq c1),
                   nobnd (mk_choice_seq c2),
                   nobnd n3])
           (k1+k2)
       # computes_to_val_like_in_max_k_steps lib
           (push_swap_cs0 c1 c2 n3)
           v
           (k - (k1 + k2 + 1))
       }}
       [+]
       {en, e : NTerm
       $ {k1 : nat
       $ k1 + 1 <= k
       # v = mk_exception en e
       # computes_to_exception_in_max_k_steps lib en n1 e k1
       # reduces_in_atmost_k_steps lib
           (oterm (NCan NSwapCs1) [nobnd n1,nobnd n2,nobnd n3])
           (oterm (NCan NSwapCs1)
                  [nobnd v,
                   nobnd n2,
                   nobnd n3])
           k1
       }}
       [+]
       {en, e : @NTerm p
       $ {w : NTerm
       $ {k1 , k2 : nat
       $ k1+k2+1 <= k
       # v = mk_exception en e
       # computes_to_can_in_max_k_steps lib k1 n1 w
       # computes_to_exception_in_max_k_steps lib en n2 e k2
       # reduces_in_atmost_k_steps lib
           (oterm (NCan NSwapCs1) [nobnd n1,nobnd n2,nobnd n3])
           (oterm (NCan NSwapCs1)
                  [nobnd w,
                   nobnd v,
                   nobnd n3])
           (k1+k2)
       }}}.
Proof.
  induction k; introv wf1 wf2 wf3 comp.

  - destruct comp as [r is].
    inversion r; subst.
    allunfold @isvalue_like; allsimpl; sp.

  - apply computes_to_val_like_in_max_k_steps_S in comp; exrepnd.

    destruct n1; try (complete (inversion comp1));[].
    dopid o as [can1|ncan1|exc1|abs1] Case.

    + Case "Can".
      destruct n2; try (complete (csunf comp1; allsimpl; ginv));[].
      dopid o as [can2|ncan2|exc2|abs2] SCase.

      * SCase "Can".
        csunf comp1; simpl in *.
        apply compute_step_swap_cs0_aux_success_implies in comp1; exrepnd; subst; simpl in *; ginv.
        inversion comp6; subst; simpl in *; clear comp6.
        left.
        exists n1 n2 0 0; simpl; dands; auto; try omega;
          allrw @computes_to_can_in_max_k_steps_0;
          allrw @reduces_in_atmost_k_steps_0;
          autorewrite with slow; dands; eauto 3 with slow.

      * SCase "NCan".
        csunf comp1; simpl in comp1.
        apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
        apply IHk in comp0; eauto 3 with slow;[].
        repndors; exrepnd; subst; simpl in *.

        { left; exists c1 c2 k1 (S k2); simpl; dands; auto; try omega.
          { rw @computes_to_can_in_max_k_steps_S; eexists; eauto. }
          { rw  <- plus_n_Sm; rw @reduces_in_atmost_k_steps_S.
            unfold nobnd; rewrite compute_step_swap_cs1_if_isnoncan_like; allrw; eauto 2 with slow; tcsp;[].
            eexists; dands; eauto. }
          rw  <- plus_n_Sm; autorewrite with slow.
          assert (k1 + S k2 = k1 + k2 + 1) as e by omega; rewrite e; auto. }

        { apply computes_to_exception_in_max_k_steps_can in comp4; tcsp. }

        { right; right.
          exists en e w k1 (S k2); dands; auto; try omega.
          { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
          { rw  <- plus_n_Sm; rw @reduces_in_atmost_k_steps_S.
            unfold nobnd; rewrite compute_step_swap_cs1_if_isnoncan_like; allrw; eauto 2 with slow; tcsp;[].
            eexists; dands; eauto. } }

      * SCase "Exc".
        csunf comp1; simpl in comp1; ginv.
        right; right.
        apply wf_exception_implies in wf2; exrepnd; tcsp; subst; fold_terms.
        apply computes_to_val_like_in_max_k_steps_exc_iff in comp0; subst.
        exists a t (oterm (Can can1) l) 0 0; simpl; dands; auto; try omega;
          allrw @computes_to_can_in_max_k_steps_0;
          allrw @reduces_in_atmost_k_steps_0; tcsp.

      * SCase "Abs".
        csunf comp1; simpl in comp1.
        apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
        apply IHk in comp0; eauto 3 with slow;[].
        repndors; exrepnd; subst; simpl in *.

        { left; exists c1 c2 k1 (S k2); simpl; dands; auto; try omega.
          { rw @computes_to_can_in_max_k_steps_S; eexists; eauto. }
          { rw  <- plus_n_Sm; rw @reduces_in_atmost_k_steps_S.
            unfold nobnd; rewrite compute_step_swap_cs1_if_isnoncan_like; allrw; eauto 2 with slow; tcsp;[].
            eexists; dands; eauto. }
          rw  <- plus_n_Sm; autorewrite with slow.
          assert (k1 + S k2 = k1 + k2 + 1) as e by omega; rewrite e; auto. }

        { apply computes_to_exception_in_max_k_steps_can in comp4; tcsp. }

        { right; right.
          exists en e w k1 (S k2); dands; auto; try omega.
          { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
          { rw  <- plus_n_Sm; rw @reduces_in_atmost_k_steps_S.
            unfold nobnd; rewrite compute_step_swap_cs1_if_isnoncan_like; allrw; eauto 2 with slow; tcsp;[].
            eexists; dands; eauto. } }

    + Case "NCan".
      csunf comp1; simpl in *.
      apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
      apply IHk in comp0; repndors; exrepnd; subst; simpl in *; eauto 3 with slow.

      * left.
        exists c1 c2 (S k1) k2; dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

      * right; left.
        exists en e (S k1); simpl; dands; auto; try omega.
        { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; eauto.

      * right; right.
        exists en e w (S k1) k2; dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

    + Case "Exc".
      csunf comp1; simpl in comp1; ginv.
      apply wf_exception_implies in wf1; exrepnd; subst; simpl in *; fold_terms.
      apply computes_to_val_like_in_max_k_steps_exc in comp0; subst.
      right; left.
      exists a t 0; dands; auto; try omega.
      apply computes_to_exception_in_max_k_steps_exc; sp.
      unfold reduces_in_atmost_k_steps; simpl; sp.

    + Case "Abs".
      csunf comp1; simpl in *.
      apply on_success_csuccess in comp1; exrepnd; subst; simpl in *.
      apply IHk in comp0; repndors; exrepnd; subst; simpl in *; eauto 3 with slow.

      * left.
        exists c1 c2 (S k1) k2; dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.

      * right; left.
        exists en e (S k1); simpl; dands; auto; try omega.
        { rw @computes_to_exception_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; eauto.

      * right; right.
        exists en e w (S k1) k2; dands; simpl; auto; try omega.
        { rw @computes_to_can_in_max_k_steps_S; allrw; eexists; dands; eauto. }
        rw @reduces_in_atmost_k_steps_S.
        csunf; simpl; allrw; simpl; eexists; dands; eauto.
Qed.

Lemma isprogram_push_swap_cs0 {o} :
  forall a b (t : @NTerm o),
    isprogram t
    -> isprogram (push_swap_cs0 a b t).
Proof.
  introv isp.
  unfold push_swap_cs0.
  unfold isprogram, closed in *; repnd; autorewrite with slow in *; dands; eauto 3 with slow.
Qed.
Hint Resolve isprogram_push_swap_cs0 : slow.

Lemma swap_computes_to_val_like_in_max_k_steps {o} :
  forall {sw} {lib : @plibrary o} {a b : @NTerm o} {k},
    computes_to_val_like_in_max_k_steps lib a b k
    -> computes_to_val_like_in_max_k_steps (swap_cs_plib sw lib) (swap_cs_term sw a) (swap_cs_term sw b) k.
Proof.
  introv comp; unfold computes_to_val_like_in_max_k_steps in *; repnd.
  apply (@swap_reduces_in_atmost_k_steps o sw) in comp0; dands; eauto 3 with slow.
Qed.

Lemma extensional_swap_cs0 {o} : extensional_op (@NCan o NSwapCs0).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @isprogram_swap_cs0_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_swap_cs0_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.
  apply computes_to_val_like_in_max_k_steps_swap_cs0_implies in Hcv;
    try (complete (apply isprogram_implies_wf; auto));[].
  repndors; exrepnd; subst; GC.

  - unfold push_swap_cs0, push_swap_cs_sub_term in *.
    rewrite lsubst_aux_trivial_cl_term2 in Hcv1; try apply closed_swap_cs_term; eauto 2 with slow;[].

    unfold extensional_op_ind in Hi.
    unfold computes_to_can_in_max_k_steps in Hcv2; repnd.
    unfold computes_to_can_in_max_k_steps in Hcv3; repnd.
    applydup @reduces_atmost_preserves_program in Hcv5 as ispc1; auto.
    applydup @reduces_atmost_preserves_program in Hcv6 as ispc2; auto.
    apply @no_change_after_value_ra with (k2:=k) in Hcv5; auto; try omega; [].
    apply @no_change_after_value_ra with (k2:=k) in Hcv6; auto; try omega; [].
    applydup @reduces_atmost_preserves_program in Hcv5; auto.
    applydup @reduces_atmost_preserves_program in Hcv6; auto.
    make_red_val_like Hcv5 h1.
    eapply Hi in h1; try exact Has0bt; auto.
    make_red_val_like Hcv6 h2.
    eapply Hi in h2; try exact Has1bt; auto.
    apply howe_lemma2 in h1; auto; prove_isprogram.
    apply howe_lemma2 in h2; auto; prove_isprogram.
    exrepnd; fold_terms.
    allapply @approx_starbts_nil_left; subst.

    unfold computes_to_val_like_in_max_k_steps in Hcv1; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv9; auto; try omega; [].
    make_red_val_like Hcv9 g.
    apply (@swap_computes_to_val_like_in_max_k_steps o (c1,c2)) in g.
    autorewrite with slow in g.

    apply Hi with (v := c0) in g; auto;
      try (complete (destruct d1; auto)); eauto 2 with slow.

    eapply approx_star_open_trans.
SearchAbout approx_star approx_open.

2:{

Set Nested Proofs Allowed.

(*Lemma approx_open_swap_cs_term {o} :
  forall lib sw (t u : @NTerm o),
    approx_open lib t u
    -> approx_open lib (swap_cs_term sw t) (swap_cs_term sw u).
Proof.
  introv apo.
  unfold approx_open.

SearchAbout approx swap_cs_term.

Qed.
Hint Resolve approx_open_swap_cs_term : slow.*)

(*Lemma approx_star_swap_cs_term {o} :
  forall lib sw (t u : @NTerm o),
    approx_star lib t u
    -> approx_star lib (swap_cs_term sw t) (swap_cs_term sw u).
Proof.
  nterm_ind t as [v|op bs ind] Case; introv apx.

  { inversion apx as [? ? ? apo|]; repnd; clear apx; subst; simpl in *.
    constructor.


Qed.
Hint Resolve approx_star_swap_cs_term : slow.*)

Lemma approx_star_push_swap_cs0_swap_cs_term {o} :
  forall lib a b (t u : @NTerm o),
    isprogram t
    -> isprogram u
    -> approx_star lib t u
    -> approx_star lib (push_swap_cs0 a b t) (swap_cs_term (a,b) u).
Proof.
  introv ispa ispb apx; unfold push_swap_cs0, push_swap_cs_sub_term.
  rewrite lsubst_aux_trivial_cl_term2; eauto 3 with slow.

Qed.
Hint Resolve approx_star_push_swap_cs0_swap_cs_term : slow.

apply approx_star_push_swap_cs0_swap_cs_term.

XXx
    apply @approx_star_open_trans with (b := mk_swap_cs2 c1 c2 c0); auto.

    apply approx_implies_approx_open.
    apply @approx_trans with (b := mk_swap_cs1 (mk_choice_seq c1) (mk_choice_seq c2) c0).

    { apply reduces_to_implies_approx_eauto; prove_isprogram; eauto 2 with slow. }

    apply reduces_to_implies_approx_eauto; prove_isprogram.
    eapply implies_reduces_to_mk_swap_cs1_val; eauto.

  - unfold extensional_op_ind in Hi.
    unfold computes_to_exception_in_max_k_steps in Hcv3; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv3; auto;
      try omega; try (unfold isvalue_like; allsimpl; sp).
    make_red_val_like Hcv3 h1.
    apply Hi with (v := a1) in h1; auto.
    apply howe_lemma2_exc in h1; auto; prove_isprogram.
    exrepnd.
    applydup @preserve_program_exc2 in h1; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    { apply approx_star_exception; auto. }
    apply approx_implies_approx_open.
    apply @approx_trans with (b := mk_swap_cs1 (mk_exception a' e') b0 c0).
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      { apply implies_isprogram_mk_swap_cs1; eauto 3 with slow. }
      apply reduces_to_if_step; reflexivity. }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_prinarg.
      apply computes_to_exception_as_reduces_to; auto. }

  - unfold extensional_op_ind in Hi.
    unfold computes_to_can_in_max_k_steps in Hcv3; repnd.
    unfold computes_to_exception_in_max_k_steps in Hcv4; repnd.
    applydup @reduces_atmost_preserves_program in Hcv2 as ispx; auto.
    apply @no_change_after_value_ra with (k2:=k) in Hcv2; auto; try omega; [].
    apply @no_change_after_val_like with (k2:=k) in Hcv4; auto; try omega;
      try (unfold isvalue_like; allsimpl; tcsp);[].
    make_red_val_like Hcv2 h1.
    apply Hi with (v := a1) in h1; auto.
    make_red_val_like Hcv4 h2.
    apply Hi with (v := b0) in h2; auto.
    apply howe_lemma2_exc in h2; auto; prove_isprogram; exrepnd.
    applydup @iscan_implies in Hcv3; exrepnd; subst.
    apply howe_lemma2 in h1; auto; prove_isprogram; exrepnd.
    applydup @computes_to_value_preserves_program in h4; auto.
    applydup @preserve_program_exc2 in h2; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := mk_swap_cs1 (oterm (Can c1) lbt') (mk_exception a' e') c0).
    { apply reduces_to_implies_approx_eauto; prove_isprogram;[|].
      { apply implies_isprogram_mk_swap_cs1; eauto 3 with slow. }
      apply reduces_to_if_step.
      csunf; simpl; auto. }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      eapply implies_reduces_to_mk_swap_cs1; eauto. }
Qed.
