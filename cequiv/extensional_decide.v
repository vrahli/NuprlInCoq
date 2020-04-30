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



Lemma extensional_decide {p} : extensional_op (@NCan p NDecide).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd;[|allsimpl; subst; repnd; complete ginv|subst;ginv];[].

  assert (m <= S k) as XX by omega.
  repnud Hcv.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [omega|].
  assert (skm <= k) by (subst; omega).
  apply reduces_atmost_S in XX; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv4; auto.
  allapply @isprogram_decide_implies; exrepnd; subst; cpx.
  allrw @fold_decide.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  apply no_change_after_val_like with (k2:=k) in Hcv3;auto;[].
  make_red_val_like Hcv3 hh.
  apply (Hi _ _ _ t2) in hh; auto; prove_isprogram.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst;
    csunf XX1; allsimpl; ginv;[].

    apply compute_step_decide_success in XX1; exrepnd; subst; cpx; GC.
    apply howe_lemma2 in hh; exrepnd; auto; prove_isprogram.
    unfold approx_starbts, lblift_sub in hh1; simpl in hh1; repnd; cpx.
    repeat(approxrelbtd); show_hyps.
    applydup @computes_to_value_preserves_program in hh0; auto.

    apply apply_bterm_approx_star_congr
    with (lnt1:= [d]) (lnt2:= [dr])
      in Has1bt;
      auto; try (complete (intro xxx; ginv));
      [|prove_bin_rel_nterm; prove_approx_star; auto; prove_isprogram].

    apply apply_bterm_approx_star_congr
    with (lnt1:= [d]) (lnt2:= [dr])
      in Has2bt;
      auto; try (complete (intro xxx; ginv));
      [|prove_bin_rel_nterm; prove_approx_star; auto; prove_isprogram].

    apply no_change_after_val_like with (k2 := k) in XX0; auto.
    make_red_val_like XX0 hh.

    destruct XX2 as [XX2|XX2]; repnd; subst.

    + applydup @isprogram_inl_iff in Hcv8; repnd.
      applydup @isprogram_inl_iff in hh1; repnd.

      apply (Hi _ _ _ (subst b0 v0 dr)) in hh; auto; prove_isprogram;
      try (eapply isprogram_bt_implies_isprogram_lsubst; simpl;[reflexivity|idtac|auto];[];
           introv i; repdors; cpx; auto).

      apply approx_star_open_trans with (b := subst b0 v0 dr); auto.
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_trans with (b := mk_decide (mk_inl dr) v0 b0 v3 b3).
      apply reduces_to_prinarg; auto; destruct hh0; auto.
      apply reduces_to_if_step; reflexivity.

    + applydup @isprogram_inr_iff in Hcv8; repnd.
      applydup @isprogram_inr_iff in hh1; repnd.

      apply (Hi _ _ _ (subst b3 v3 dr)) in hh; auto; prove_isprogram;
      try (eapply isprogram_bt_implies_isprogram_lsubst; simpl;[reflexivity|idtac|auto];[];
           introv i; repdors; cpx; auto).

      apply approx_star_open_trans with (b := subst b3 v3 dr); auto.
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_trans with (b := mk_decide (mk_inr dr) v0 b0 v3 b3).
      apply reduces_to_prinarg; auto; destruct hh0; auto.
      apply reduces_to_if_step; reflexivity.

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    apply howe_lemma2_exc in hh; exrepnd; auto; prove_isprogram.

    apply approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply reduces_to_trans with (b := mk_decide (mk_exception a' e') v0 b0 v3 b3).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.
