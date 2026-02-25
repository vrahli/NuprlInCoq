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


Require Import approx_star0.


Lemma extensional_ncomp {p} : forall a, extensional_op (@NCan p (NCompOp a)).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  applydup @isprogram_compop_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_compop_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  apply computes_to_val_like_in_max_k_steps_comp_implies in Hcv;
    try (complete (apply isprogram_implies_wf; auto)).
  repndors; exrepnd; subst; GC.

  - unfold extensional_op_ind in Hi.
    unfold computes_to_can_in_max_k_steps in Hcv2; repnd.
    unfold computes_to_can_in_max_k_steps in Hcv3; repnd.
    applydup @reduces_atmost_preserves_program in Hcv6 as ispc1; auto.
    applydup @reduces_atmost_preserves_program in Hcv7 as ispc2; auto.
    assert (isvalue (pk2term pk1)) as isvc1 by (apply isvalue_iff; sp).
    assert (isvalue (pk2term pk2)) as isvc2 by (apply isvalue_iff; sp).
    apply @no_change_after_value_ra with (k2:=k) in Hcv6; auto; try lia; [].
    apply @no_change_after_value_ra with (k2:=k) in Hcv7; auto; try lia; [].
    applydup @reduces_atmost_preserves_program in Hcv6; auto.
    applydup @reduces_atmost_preserves_program in Hcv7; auto.
    make_red_val_like Hcv6 h1.
    apply Hi with (v := a2) in h1; auto.
    make_red_val_like Hcv7 h2.
    apply Hi with (v := b0) in h2; auto.
    allrw @pk2term_eq.
    apply howe_lemma2 in h1; auto; prove_isprogram.
    apply howe_lemma2 in h2; auto; prove_isprogram.
    allrw <- @pk2term_eq.
    exrepnd.
    unfold approx_starbts, lblift_sub in h1; simpl in h1; repnd; cpx.
    unfold approx_starbts, lblift_sub in h2; simpl in h2; repnd; cpx.

    unfold computes_to_val_like_in_max_k_steps in Hcv5; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv10; auto; try lia; [].
    make_red_val_like Hcv10 g.
    apply Hi with (v := if d1 then c0 else d0) in g; auto;
    try (complete (destruct d1; auto)).

    apply @approx_star_open_trans with (b := if d1 then c0 else d0); auto.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NCompOp a))
                                        [nobnd (pk2term pk1),
                                         nobnd (pk2term pk2),
                                         nobnd c0,
                                         nobnd d0]).

    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_if_step.
      repndors; exrepnd; subst;
      try (complete (csunf; simpl; dcwf h; simpl; unfold compute_step_comp; simpl; boolvar; tcsp));
      try (complete (csunf; simpl; allrw @pk2term_eq; dcwf h; simpl;
                     unfold compute_step_comp; simpl; allrw @get_param_from_cop_pk2can;
                     boolvar; tcsp;
                     allunfold @co_wf; allsimpl; allrw @get_param_from_cop_pk2can; ginv)).
    }

    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      allrw <- @pk2term_eq.
      apply reduce_to_prinargs_comp; auto.
      { repndors; exrepnd; subst; simpl; eauto 3 with slow. }
      unfold computes_to_value in h0; sp.
    }

  - unfold extensional_op_ind in Hi.
    unfold computes_to_exception_in_max_k_steps in Hcv3; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv3; auto;
    try lia; try (unfold isvalue_like; allsimpl; sp).
    make_red_val_like Hcv3 h1.
    apply Hi with (v := a2) in h1; auto.
    apply howe_lemma2_exc in h1; auto; prove_isprogram.
    exrepnd.
    applydup @preserve_program_exc2 in h1; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NCompOp a))
                                        [ nobnd (mk_exception a' e'),
                                          nobnd b0,
                                          nobnd c0,
                                          nobnd d0]).
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      { apply isprogram_compop_iff.
        eexists; eexists; eexists; eexists; dands; try reflexivity; auto;
        rw @isprogram_exception_iff; auto. }
      { apply reduces_to_if_step; reflexivity. }
    }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_prinarg.
      apply computes_to_exception_as_reduces_to; auto.
    }

  - unfold extensional_op_ind in Hi.
    unfold computes_to_can_in_max_k_steps in Hcv3; repnd.
    unfold computes_to_exception_in_max_k_steps in Hcv4; repnd.
    applydup @reduces_atmost_preserves_program in Hcv2 as ispx; auto.
    assert (isvalue (pk2term pk)) as isvx by (apply isvalue_iff; sp).
    apply @no_change_after_value_ra with (k2:=k) in Hcv2; auto; try lia; [].
    apply @no_change_after_val_like with (k2:=k) in Hcv5; auto; try lia;
    try (unfold isvalue_like; allsimpl; tcsp);[].
    make_red_val_like Hcv2 h1.
    apply Hi with (v := a2) in h1; auto.
    make_red_val_like Hcv5 h2.
    apply Hi with (v := b0) in h2; auto.
    apply howe_lemma2_exc in h2; auto; prove_isprogram; exrepnd.
    allrw @pk2term_eq.
    apply howe_lemma2 in h1; auto; prove_isprogram; exrepnd.
    applydup @computes_to_value_preserves_program in h4; auto.
    applydup @preserve_program_exc2 in h2; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NCompOp a))
                                        [ nobnd (oterm (Can (pk2can pk)) lbt'),
                                          nobnd (mk_exception a' e'),
                                          nobnd c0,
                                          nobnd d0]).
    { apply reduces_to_implies_approx_eauto; prove_isprogram;[|].
      { apply isprogram_compop_iff; eexists; eexists; eexists; eexists; dands; try reflexivity; auto.
        rw @isprogram_exception_iff; auto. }
      { apply reduces_to_if_step.
        csunf; simpl; dcwf h; simpl; auto;[].
        allrw @isprogram_pk2can; subst; GC.
        repndors; exrepnd; subst;
        allunfold @co_wf; allrw @get_param_from_cop_pk2can; ginv.
      }
    }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduce_to_prinargs_comp; auto.
      allrw @isprogram_pk2can; subst; GC.
      repndors; exrepnd; subst;
      allunfold @co_wf; allrw @get_param_from_cop_pk2can;
      allsimpl; ginv; fold_terms; allrw <- @pk2term_eq; eauto 3 with slow.
    }
Qed.

(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/")
*** End:
*)
