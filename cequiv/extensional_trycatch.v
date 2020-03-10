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



Lemma extensional_trycatch {p} : extensional_op (@NCan p NTryCatch).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd;[|allsimpl; subst; repnd; complete ginv|subst;ginv];[].

  repnud Hcv.
  assert (m <= S k) as XX by omega.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [omega|].
  assert (skm <= k) by (subst; omega).
  apply reduces_atmost_S in XX; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv4; auto.
  allapply @isprogram_trycatch_implies; exrepnd; subst; cpx.
  allrw @fold_try.
  unfold lblift_sub in Has; repnd; simpl in Has0, Has; GC.
  repeat(approxrelbtd); show_hyps.
  allapply @approx_star_bterm_nobnd2.

  dorn Hcv0.

  - apply no_change_after_val_like with (k2:=k) in Hcv3; try splr.
    make_red_val_like Hcv3 h.
    apply (Hi _ _ t2) in h; auto.
    applydup @howe_lemma2_implies_iscan in h; auto; exrepnd.
    allunfold @computes_to_value; repnd.
    fold_terms.
    rw @compute_step_try_iscan in XX1; ginv.

    apply no_change_after_val_like with (k2 := k) in XX0; auto.
    make_red_val_like XX0 hh.
    apply (Hi _ _ (mk_atom_eq a1 a1 v1 mk_bot)) in hh;
      auto; prove_isprogram;
      try (apply isprogram_mk_atom_eq; dands; auto);
      eauto 2 with slow;
      try (complete (apply approx_star_mk_atom_eq; auto;
                     apply approx_star_refl; eauto 3 with slow)).

    eapply approx_star_open_trans;[eauto|].
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto;
      try (apply isprogram_try_iff2;dands;auto);[].
    eapply reduces_to_trans;[apply reduces_to_prinarg;eauto|]; fold_terms.
    apply reduces_to_if_step.
    rw @compute_step_try_iscan; auto.

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    applydup @isprogram_exception_iff in Hcv8.
    csunf XX1; simpl in XX1; ginv.

    apply no_change_after_val_like with (k2:=k) in Hcv3; try splr.
    apply no_change_after_val_like with (k2:=k) in XX0; try splr.
    unfold extensional_op_ind in Hi.
    make_red_val_like Hcv3 h.
    apply Hi with (v := t2) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.
    applydup @computes_to_exception_preserves_program in h1; auto.

    apply apply_bterm_approx_star_congr
    with (lnt1:=[e]) (lnt2:=[e']) in Has2bt;
      auto;
      try (complete (intro xx; ginv));
      [|prove_bin_rel_nterm; prove_approx_star; auto; prove_isprogram].
    unfold apply_bterm in Has1bt; simpl in Has1bt; repeat (rw fold_subst in Has1bt).

    make_red_val_like XX0 hh.
    apply Hi with (v := mk_atom_eq a1 a' (subst b0 v0 e') (mk_exception a' e')) in hh; auto; prove_isprogram;
    try (apply isprogram_subst_if_bt; auto).

    {
      eapply approx_star_open_trans; eauto.
      apply approx_implies_approx_open.
      apply reduces_to_implies_approx_eauto; prove_isprogram;
      try (apply isprogram_try_iff2; sp).
      apply (reduces_to_trans _ _ (mk_try (mk_exception a' e') a1 v0 b0)).
      * apply reduces_to_prinarg; auto.
      * apply reduces_to_if_step; csunf; simpl; boolvar; tcsp.
    }

    {
      apply isprogram_mk_atom_eq; dands; auto.
      apply isprogram_subst_if_bt; auto.
    }

    {
      apply isprogram_mk_atom_eq; dands; auto; prove_isprogram.
      - apply @preserve_program_exc2 in h1; sp.
      - apply isprogram_subst_if_bt; auto.
      - apply isprogram_exception; auto.
        apply @preserve_program_exc2 in h1; sp.
    }

    {
      apply approx_star_congruence3.
      - unfold approx_starbts, lblift_sub; allsimpl; dands; auto.
        introv i; repeat (destruct n; cpx); unfold selectbt; simpl;
        apply blift_sub_nobnd_congr; auto.
        apply approx_star_congruence3.
        + unfold approx_starbts, lblift_sub; allsimpl; dands; auto.
          introv j; repeat (destruct n; cpx); unfold selectbt; simpl;
          apply blift_sub_nobnd_congr; auto.
        + apply isprogram_exception; auto.
          apply @preserve_program_exc2 in h1; sp.
      - apply isprogram_mk_atom_eq; dands; auto; prove_isprogram.
        + apply @preserve_program_exc2 in h1; sp.
        + apply isprogram_subst_if_bt; auto.
        + apply isprogram_exception; auto.
          apply @preserve_program_exc2 in h1; sp.
    }
Qed.

(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/")
*** End:
*)
