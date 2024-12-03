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


Require Import approx_star0.


Lemma extensional_cbv {p} : extensional_op (@NCan p NCbv).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd;[|allsimpl; subst; repnd; complete ginv|subst;ginv];[].

  assert (m <= S k) as XX by lia.
  repnud Hcv.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [lia|].
  assert (skm <= k) by (subst; lia).
  apply reduces_atmost_S in XX; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv4; auto.
  allapply @isprogram_cbv_implies; exrepnd; subst; cpx.

  dorn Hcv0.

  - unfold lblift_sub in Has; repnd; allsimpl; GC.
    repeat(approxrelbtd); show_hyps.
    allapply @approx_star_bterm_nobnd2.
    apply no_change_after_value_ra with (k2:=k) in Hcv3; auto; [].
    make_red_val_like Hcv3 h.
    apply (Hi _ _ t2) in h; auto; prove_isprogram;[].
    applydup @howe_lemma2_implies_iscan in h; auto; exrepnd.

    apply apply_bterm_approx_star_congr
    with (lnt1:= [t1]) (lnt2:= [v1])
      in Has1bt;
      eauto 2 with slow;
      try (complete (intro xx; ginv)).
    allunfold @apply_bterm; allsimpl; allrw @fold_subst; fold_terms.
    rw @compute_step_cbv_iscan in XX1; auto;[]; ginv.

    apply no_change_after_val_like with (k2 := k) in XX0; auto.
    make_red_val_like XX0 hh.
    apply (Hi _ _ (subst b0 v0 v1)) in hh; auto; prove_isprogram;
    try (try (apply isprogram_subst_if_bt);
         try (apply isprogram_bt_implies);
         try (apply implies_isprogram_bt_lam);
         simpl; auto; prove_isprogram;
         introv i; repndors; subst; tcsp);[].
    allunfold @computes_to_value; repnd.

    eapply approx_star_open_trans;[eauto|].
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto;
      try (apply isprogram_cbv_iff2;dands;auto).
    eapply reduces_to_trans;[apply reduces_to_prinarg;eauto|]; fold_terms.
    apply reduces_to_if_step.
    rw @compute_step_cbv_iscan; auto.

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    clear Hcv.
    apply no_change_after_val_like with (k2:=k) in Hcv3; try splr.
    duplicate Has.
    unfold lblift_sub in Has; repnd; allsimpl.
    repeat(approxrelbtd). show_hyps.
    apply approx_star_bterm_nobnd2 in Has0bt.
    make_red_val_like Hcv3 h.
    unfold extensional_op_ind in Hi.
    apply Hi with (v := t2) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @fold_cbv.
    allrw @computes_to_exception_as_reduces_to.
    apply @reduces_to_trans with (b := mk_cbv (mk_exception a' e') v0 b0).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.
