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


Lemma extensional_swap_cs2 {o} : forall sw, extensional_op (@NSwapCs2 o sw).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @isprogram_swap_cs2_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_swap_cs2_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.
  apply computes_to_val_like_in_max_k_steps_swap_cs2_implies in Hcv;
    try (complete (apply isprogram_implies_wf; auto));[].
  repndors; exrepnd; subst; GC; fold_terms.

  - unfold extensional_op_ind in Hi.
    unfold computes_to_can_in_max_k_steps in Hcv2; repnd.
    applydup @reduces_atmost_preserves_program in Hcv4 as ispc1; auto; eauto 2 with slow.
    apply @no_change_after_value_ra with (k2:=k) in Hcv4; auto; try omega; [].
    applydup @reduces_atmost_preserves_program in Hcv4; auto; eauto 2 with slow.
    make_red_val_like Hcv4 h1.

    eapply Hi in h1; try apply implies_approx_star_swap_cs_term; try exact Has0bt; eauto 2 with slow.
    apply (implies_approx_star_swap_cs_term _ sw) in h1; simpl in *; autorewrite with slow in *.

    apply (implies_isprogram_swap_cs_term sw) in ispc1; simpl in *.
    apply howe_lemma2 in h1; auto; prove_isprogram.
    exrepnd; fold_terms.

    unfold computes_to_val_like_in_max_k_steps in Hcv0; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv6; auto; try (complete (destruct k1; simpl; try omega)).
    make_red_val_like Hcv6 g.

    apply Hi with (v := push_swap_cs_can sw (swap_cs_can sw can) lbt') in g; auto; eauto 2 with slow.

    { eapply approx_star_open_trans;[eauto|].
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; prove_isprogram.

      unfold computes_to_value in h0; repnd.
      apply (@swap_reduces_to o sw) in h2.
      apply implies_reduces_to_mk_swap_cs2 in h2.
      autorewrite with slow in *.
      eapply reduces_to_trans;[exact h2|].
      apply reduces_to_if_step.
      csunf; simpl; auto. }

    { apply implies_isprogram_push_swap_cs_can; eauto 3 with slow. }

    applydup @computes_to_value_wf4 in h0.
    apply approx_star_push_swap_cs_can; auto; eauto 2 with slow.

  - unfold extensional_op_ind in Hi.
    apply isprogram_exception_iff in Hpra; repnd.
    apply isprogram_mk_swap_cs2_implies in Hpra.
    apply isprogram_mk_swap_cs2_implies in Hpra0.
    apply isprogram_swap_cs_term_implies in Hpra.
    apply isprogram_swap_cs_term_implies in Hpra0.

    unfold computes_to_exception_in_max_k_steps in Hcv3; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv3; auto;
      try omega; try (unfold isvalue_like; allsimpl; sp);
      try (apply isprogram_exception; auto);[].
    make_red_val_like Hcv3 h1.
    apply Hi with (v := swap_cs_term sw a1) in h1; auto; eauto 2 with slow;
      try (apply isprogram_exception; auto);
      try (apply implies_approx_star_swap_cs_term); auto.
    apply (implies_approx_star_swap_cs_term _ sw) in h1; simpl in *;
      autorewrite with slow in *; fold_terms.

    apply howe_lemma2_exc in h1; auto; prove_isprogram;
      try (apply isprogram_exception; eauto 2 with slow);[].
    exrepnd.
    applydup @preserve_program_exc2 in h1; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception (mk_swap_cs2 sw a') (mk_swap_cs2 sw e')).
    { apply approx_star_exception; auto; apply implies_approx_star_mk_swap_cs2; auto. }
    apply approx_implies_approx_open.

    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply (@swap_reduces_to o sw) in h1.
    eapply reduces_to_trans;[apply implies_reduces_to_mk_swap_cs2; eauto|].
    autorewrite with slow.
    apply reduces_to_if_step; simpl.
    csunf; simpl; unfold push_swap_cs_exc; simpl; fold_terms; autorewrite with slow; auto.
Qed.
