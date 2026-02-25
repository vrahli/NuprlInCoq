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



Lemma extensional_arith {p} : forall a, extensional_op (@NCan p (NArithOp a)).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  applydup @isprogram_arithop_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_arithop_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  apply computes_to_val_like_in_max_k_steps_arith_implies in Hcv;
    [|eauto with slow|eauto with slow].

  repndors; exrepnd; subst; GC.

  - unfold extensional_op_ind in Hi.
    unfold computes_to_value_in_max_k_steps in Hcv3; repnd.
    unfold computes_to_value_in_max_k_steps in Hcv4; repnd.
    apply @no_change_after_value_ra with (k2:=k) in Hcv0; auto; try lia; [].
    apply @no_change_after_value_ra with (k2:=k) in Hcv5; auto; try lia; [].
    make_red_val_like Hcv0 h1.
    apply Hi with (v := a2) in h1; auto.
    make_red_val_like Hcv5 h2.
    apply Hi with (v := b0) in h2; auto.
    apply howe_lemma2 in h1; auto; prove_isprogram.
    apply howe_lemma2 in h2; auto; prove_isprogram.
    exrepnd.
    unfold approx_starbts, lblift_sub in h1; simpl in h1; repnd; cpx.
    unfold approx_starbts, lblift_sub in h2; simpl in h2; repnd; cpx.
    allrw @fold_integer.
    apply approx_open_implies_approx_star.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NArithOp a))
                                        [ bterm [] (mk_integer nv1),
                                          bterm [] (mk_integer nv2)]).
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_if_step; reflexivity.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduce_to_prinargs_arith; eauto 3 with slow.

  - unfold extensional_op_ind in Hi.
    unfold computes_to_exception_in_max_k_steps in Hcv3; repnd.
    apply @no_change_after_val_like with (k2:=k) in Hcv3; auto;
    try lia; try (complete (unfold isvalue_like; simpl; sp)).
    make_red_val_like Hcv3 h1.
    apply Hi with (v := a2) in h1; auto.
    apply howe_lemma2_exc in h1; auto; prove_isprogram.
    exrepnd.
    applydup @preserve_program_exc2 in h1; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    { apply approx_star_exception; auto. }
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NArithOp a))
                                        [ bterm [] (mk_exception a' e'),
                                          bterm [] b0]).
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      { apply isprogram_arithop_iff.
        eexists; eexists; dands; try reflexivity; auto;
        rw @isprogram_exception_iff; tcsp.
      }
      apply reduces_to_if_step; reflexivity.
    }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_prinarg.
      apply computes_to_exception_as_reduces_to; auto.
    }

  - unfold extensional_op_ind in Hi.
    unfold computes_to_value_in_max_k_steps in Hcv3; repnd.
    unfold computes_to_exception_in_max_k_steps in Hcv4; repnd.
    applydup @reduces_atmost_preserves_program in Hcv2; auto.
    assert (@isvalue p (mk_integer z)) as isvx by (apply isvalue_iff; sp).
    apply @no_change_after_value_ra with (k2:=k) in Hcv2; auto; try lia; [].
    apply @no_change_after_val_like with (k2:=k) in Hcv4; auto; try lia;
    try (complete (unfold isvalue_like; simpl; sp)); [].
    make_red_val_like Hcv2 h1.
    apply Hi with (v := a2) in h1; auto.
    make_red_val_like Hcv4 h2.
    apply Hi with (v := b0) in h2; auto.
    apply howe_lemma2_exc in h2; auto; prove_isprogram; exrepnd.
    apply howe_lemma2 in h1; auto; prove_isprogram; exrepnd.
    applydup @computes_to_value_preserves_program in h4; auto.
    applydup @preserve_program_exc2 in h2; repnd; auto.
    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply @approx_trans with (b := oterm (NCan (NArithOp a))
                                         [ bterm [] (oterm (Can (Nint z)) lbt'),
                                           bterm [] (mk_exception a' e')]).
    { apply reduces_to_implies_approx_eauto; prove_isprogram;[|].
      { apply isprogram_arithop_iff; eexists; eexists; dands; try reflexivity; auto.
        rw @isprogram_exception_iff; auto. }
      { apply reduces_to_if_step.
        csunf; simpl; dcwf h; simpl; auto;[].
        allapply @isprogram_nat_implies; subst.
        allunfold @ca_wf; ginv.
      }
    }
    { apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduce_to_prinargs_arith; auto.
      allapply @isprogram_nat_implies; subst.
      fold_terms; eauto 3 with slow.
    }
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/")
*** End:
*)
