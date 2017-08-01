(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University

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


Require Import approx_ext_star0.


Lemma extensional_ext_minus {p} : extensional_op_ext (@NCan p NMinus).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.

  applydup @isprogram_minus_implies in Hprt; exrepnd; subst; cpx.
  applydup @isprogram_minus_implies in Hprt'; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_ext_star_bterm_nobnd2.
  fold_terms.
  allrw @fold_minus.

  apply computes_to_val_like_in_max_k_steps_minus_implies in Hcv; exrepnd; cpx.
  unfold extensional_op_ext_ind in Hi.
  applydup @computes_to_val_like_in_max_k_steps_preserves_program in Hcv2; auto.
  apply Hi with (v := t0) in Hcv2; auto; clear Hi.

  destruct Hcv1 as [Hcv1|Hcv1]; exrepnd; subst.

  - apply howe_lemma2 in Hcv2; auto; prove_isprogram; exrepnd.
    unfold approx_ext_starbts, lblift_sub in Hcv2; simpl in Hcv2; repnd; cpx.
    allrw @fold_integer.
    apply approx_ext_open_implies_approx_ext_star.
    apply approx_ext_implies_approx_ext_open.
    apply reduces_to_implies_approx_ext_eauto; prove_isprogram.
    apply reduces_to_trans with (b := mk_minus (mk_integer z)).
    apply reduces_to_prinarg; auto.
    destruct Hcv1; auto.
    apply reduces_to_if_step.
    simpl.
    unfold compute_step_minus; simpl; auto.

  - apply isexc_implies in Hcv3; auto; exrepnd; subst; GC.
    apply howe_lemma2_exc in Hcv2; auto; exrepnd.
    apply approx_ext_star_open_trans with (b := mk_exception a' e').
    apply approx_ext_star_exception; auto.
    apply approx_ext_implies_approx_ext_open.
    apply reduces_to_implies_approx_ext_eauto; prove_isprogram.
    apply reduces_to_trans with (b := mk_minus (mk_exception a' e')).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.
