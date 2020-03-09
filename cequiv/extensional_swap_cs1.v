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


Lemma extensional_swap_cs1 {p} : extensional_op (@NCan p NSwapCs1).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @isprogram_swap_cs1_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_swap_cs1_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.
  apply computes_to_val_like_in_max_k_steps_swap_cs1_implies in Hcv;
    try (complete (apply isprogram_implies_wf; auto));[].
  repndors; exrepnd; subst; GC.

  - unfold extensional_op_ind in Hi.
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
    apply Hi with (v := mk_swap_cs2 c1 c2 c0) in g; auto;
      try (complete (destruct d1; auto)); eauto 2 with slow.

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
