(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Lemma extensional_cantest {p} : forall a, extensional_op (@NCan p (NCanTest a)).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd; [|allsimpl; subst; repnd; complete ginv].

  assert (m <= S k) as XX by lia.
  repnud Hcv.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [lia|].
  assert (skm <= k) by (subst; lia).
  apply reduces_atmost_S in XX; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv4; auto.
  allapply @isprogram_cantest_implies; exrepnd; subst; cpx.

  unfold lblift_sub in Has; simpl in Has; repnd; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  apply no_change_after_val_like with (k2:=k) in Hcv3; auto; [].
  make_red_val_like Hcv3 h1.
  apply (Hi _ _ a2) in h1; auto; prove_isprogram;[].

  extensional_ind XX0 k hh.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst;
    csunf XX1; allsimpl; ginv.

    { apply (Hi _ _ (if canonical_form_test_for a c1 then b0 else c0)) in hh;
        auto; prove_isprogram;
        try (complete (destruct (canonical_form_test_for a c1); auto));
        eauto 2 with slow.
      apply howe_lemma2 in h1; exrepnd; auto; prove_isprogram.

      apply @approx_star_open_trans with (b := if canonical_form_test_for a c1 then b0 else c0); auto.
      apply approx_implies_approx_open.
      apply @approx_trans with (b := oterm (NCan (NCanTest a)) [nobnd (oterm (Can c1) lbt'),nobnd b0,nobnd c0]).
      apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_if_step; reflexivity.
      apply reduces_to_implies_approx_eauto; prove_isprogram.
      apply reduces_to_prinarg; auto; destruct h0; auto.
    }

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    apply howe_lemma2_exc in h1; exrepnd; auto; prove_isprogram.

    apply @approx_star_open_trans with (b := mk_exception a' e').
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply @reduces_to_trans with (b := oterm (NCan (NCanTest a)) [nobnd (mk_exception a' e'),nobnd b0,nobnd c0]).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.
