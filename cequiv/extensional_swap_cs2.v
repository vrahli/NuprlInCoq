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


Lemma extensional_swap_cs2 {p} : forall nfo, extensional_op (@NCan p (NSwapCs2 nfo)).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @isprogram_swap_cs2_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_swap_cs2_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.
  apply computes_to_val_like_in_max_k_steps_swap_cs2_implies in Hcv;
    try (complete (apply isprogram_implies_wf; auto));[].
  repndors; exrepnd; subst; GC.

  - unfold extensional_op_ind in Hi.
    unfold computes_to_can_in_max_k_steps in Hcv2; repnd.
    applydup @reduces_atmost_preserves_program in Hcv4 as ispc1; auto.
    apply @no_change_after_value_ra with (k2:=k) in Hcv4; auto; try omega; [].
    applydup @reduces_atmost_preserves_program in Hcv4; auto.
    make_red_val_like Hcv4 h1.
    eapply Hi in h1; try exact Has0bt; auto.
    apply howe_lemma2 in h1; auto; prove_isprogram.
    exrepnd; fold_terms.
    allapply @approx_starbts_nil_left; subst.

    unfold computes_to_val_like_in_max_k_steps in Hcv0; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv6; auto; try omega; [].
    make_red_val_like Hcv6 g.
    assert (isprogram (oterm (Can can) lbt')) as isp' by eauto 3 with slow.
    apply Hi with (v := push_swap_cs_can (swap_cs_nfo_name1 nfo) (swap_cs_nfo_name2 nfo) can lbt') in g; auto;
      try (complete (destruct d1; auto)); eauto 2 with slow;
        try (apply approx_star_push_swap_cs_can; auto;
             apply implies_nt_wf_push_swap_cs_oterm; eauto 3 with slow);[].

    apply @approx_star_open_trans with (b := push_swap_cs_can (swap_cs_nfo_name1 nfo) (swap_cs_nfo_name2 nfo) can lbt'); auto.

    apply approx_implies_approx_open.
    apply @approx_trans with (b := mk_swap_cs2 (swap_cs_nfo_name1 nfo) (swap_cs_nfo_name2 nfo) (oterm (Can can) lbt')).

    { apply reduces_to_implies_approx_eauto; prove_isprogram; eauto 2 with slow. }

    apply reduces_to_implies_approx_eauto; prove_isprogram.
    destruct nfo as [n1 n2]; simpl in *.
    apply implies_reduces_to_mk_swap_cs2; auto.

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
    apply @approx_trans with (b := mk_swap_cs2 (swap_cs_nfo_name1 nfo) (swap_cs_nfo_name2 nfo) (mk_exception a' e')).
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      { apply implies_isprogram_mk_swap_cs2; eauto 3 with slow. }
      apply reduces_to_if_step; try reflexivity. }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      destruct nfo as [n1 n2]; simpl in *.
      apply reduces_to_prinarg.
      apply computes_to_exception_as_reduces_to; auto. }
Qed.
