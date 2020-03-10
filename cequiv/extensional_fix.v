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


Lemma extensional_fix {p} : extensional_op (@NCan p NFix).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd;[|allsimpl; subst; repnd; complete ginv|subst;ginv];[].

  assert (m<= S k ) as XX by omega.
  repnud Hcv.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [omega|].
  assert (skm <= k) by (subst; omega).
  apply reduces_atmost_S in XX; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv4; auto.
  allapply @isprogram_fix_implies; exrepnd; subst; cpx.

  dorn Hcv0.

  - unfold lblift_sub in Has; repnd; allsimpl; GC.
    repeat(approxrelbtd). show_hyps.
    apply approx_star_bterm_nobnd2 in Has0bt.
    apply no_change_after_value_ra with (k2:=k) in Hcv3; auto.
    make_red_val_like Hcv3 h.

    apply iscan_implies in Hcv0; repndors; exrepnd; subst.

    { simpl in XX1; inversion XX1; subst; GC.
      apply (Hi _ _ f0) in h; auto.

      apply howe_lemma2 in h; exrepnd; auto.
      repnud h0.
      rename a into cc.
      apply reduces_to_prinarg with (lbt:= []) (op:=NFix) in h2.
      (* this will be used later in this proof *)
      assert (approx_star
                lib
                (mk_apply (oterm (Can c) bterms)
                          (oterm (NCan NFix) [bterm [] (oterm (Can c) bterms)]))
                (mk_apply (oterm (Can c) lbt')
                          (oterm (NCan NFix) [bterm [] (oterm (Can c) lbt')])))
        as XXX.
      { repeat (prove_approx_star; auto; prove_isprogram). }

      apply no_change_after_val_like with (k2:=k) in XX0; auto.
      make_red_val_like XX0 h.
      apply (Hi _ _ (mk_apply (oterm (Can c) lbt')
                              (oterm (NCan NFix) [bterm [] (oterm (Can c) lbt')])))
        in h; auto; prove_isprogram.

      match goal with
          [ H : approx_star ?lib ?cc ?t2 |- approx_star ?lib ?cc ?t1] =>
          apply (approx_star_open_trans lib) with (b:=t2) end; auto.

      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; try (rw <- @isprogram_fix_iff; auto).
      eapply reduces_to_if_split1; eauto.
    }

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
    apply Hi with (v := f0) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply approx_star_open_trans with (b := mk_exception a' e'); try (rw fold_fix).
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply reduces_to_trans with (b := mk_fix (mk_exception a' e')).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.
