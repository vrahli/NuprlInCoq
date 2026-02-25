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


Lemma extensional_eapply {p} : extensional_op (@NCan p NEApply).
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
  apply isprogram_eapply_implies in Hcv6; exrepnd; subst; cpx.

  dorn Hcv0.

  - apply no_change_after_value_ra with (k2:=k) in Hcv3; auto.
    unfold lblift_sub in Has; repnd; allsimpl; cpx.
    repeat(approxrelbtd); show_hyps.
    make_red_val_like Hcv3 h.
    pose proof (Hi la f lar) as q.
    repeat (autodimp q hyp); prove_isprogram.
    allrw <- @isprogram_eapply_iff; repnd.

    apply iscan_implies in Hcv0; repndors; exrepnd; subst.

    { csunf XX1; allsimpl.

      apply compute_step_eapply_success in XX1; exrepnd; allunfold @nobnd; ginv.
      apply eapply_wf_def_oterm_implies in XX3.
      destruct XX3 as [XX3|XX3]; exrepnd; subst; ginv.

      { apply howe_lemma2 in q; exrepnd; auto.
        unfold approx_starbts, lblift_sub in q1; repnd; allsimpl; cpx.
        repeat(approxrelbtd); show_hyps.
        fold_terms.
        applydup @preserve_program in q0; auto.

        repndors; exrepnd; subst; ginv.

        - applydup @howe_lemma2_implies_iscan in Has1bt; auto; exrepnd.
          applydup @preserve_program in Has1bt2; auto.

          eapply approx_star_open_trans in Has1bt;
            [|apply approx_implies_approx_open;
               apply computes_to_value_implies_approx2;[|exact Has1bt2];
               auto].

          apply apply_bterm_approx_star_congr with
          (lnt1:= [arg2]) (lnt2:= [v0]) in q10bt; simpl; tcsp; eauto 2 with slow;
          try (complete (intro xx; ginv)).

          apply no_change_after_val_like with (k2 := k) in XX0; auto.
          make_red_val_like XX0 w.
          pose proof (Hi
                        (apply_bterm (bterm [v] t) [arg2])
                        a
                        (apply_bterm (bterm [vr] tr) [v0])) as z.
          repeat (autodimp z hyp); prove_isprogram;
          try (apply isprogram_bt_implies; simpl; auto; prove_isprogram;
               try (apply implies_isprogram_bt_lam; auto);
               introv i; repndors; subst; tcsp);[].

          eapply approx_star_open_trans;[exact z|].
          apply approx_implies_approx_open.
          apply reduces_to_implies_approx_eauto; prove_isprogram.
          apply eapply_red_lam_val_implies; simpl; auto.

        - apply isexc_implies in XX2; auto; exrepnd; subst.
          apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; eauto 2 with slow; subst.
          apply howe_lemma2_exc in Has1bt; prove_isprogram; exrepnd.

          apply approx_star_open_trans with (b := mk_exception a' e').
          { apply approx_star_exception; auto. }

          apply approx_implies_approx_open.
          apply computes_to_exception_implies_approx; auto; prove_isprogram.
          eapply eapply_lam_exception_implies; eauto.

        - fold_terms.
          apply reduces_in_atmost_k_steps_eapply_lam_to_isvalue_like in XX0; auto.

          repndors; exrepnd.

          + apply no_change_after_val_like with (k2:=k) in XX2; eauto 2 with slow; try lia;[].
            make_red_val_like XX2 cak.

            applydup @preserve_compute_step in XX1; auto.
            applydup @reduces_atmost_preserves_program in XX5; auto.
            assert (reduces_in_atmost_k_steps lib arg2 c (S i)) as ra2.
            { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }
            apply no_change_after_val_like with (k2:=k) in ra2; eauto 2 with slow; try lia;[].
            make_red_val_like ra2 cck.
            pose proof (Hi arg2 c a0r) as z.
            repeat (autodimp z hyp); eauto 2 with slow;[].
            applydup @howe_lemma2_implies_iscan in z; auto; exrepnd.

            eapply approx_star_open_trans in z;
              [|apply approx_implies_approx_open;
                 apply computes_to_value_implies_approx2;[|exact z2];
                 auto];[].

            apply apply_bterm_approx_star_congr
            with (lnt1:= [c]) (lnt2:= [v0]) in q10bt;
              simpl; tcsp; eauto 2 with slow;
              try (complete (intro xx; ginv));[].
            allunfold @apply_bterm; allsimpl; allrw @fold_subst.

            pose proof (Hi (subst t v c) a (subst tr vr v0)) as w.
            repeat (autodimp w hyp); prove_isprogram;
            try (try (apply isprogram_subst_if_bt);
                 try (apply isprogram_bt_implies);
                 try (apply implies_isprogram_bt_lam);
                 simpl; auto; prove_isprogram;
                 introv i; repndors; subst; tcsp).

            eapply approx_star_open_trans;[exact w|].
            apply approx_implies_approx_open.
            apply reduces_to_implies_approx_eauto; prove_isprogram.
            apply eapply_red_lam_val_implies; simpl; auto.

          + apply isexc_implies in XX2; auto; exrepnd; subst.

            assert (reduces_in_atmost_k_steps lib arg2 (mk_exception a0 e) (S j)) as ra2.
            { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }

            apply no_change_after_val_like with (k2:=k) in ra2; try splr; try lia.
            make_red_val_like ra2 ca0.
            pose proof (Hi arg2 (mk_exception a0 e) a0r) as z.
            repeat (autodimp z hyp); eauto 2 with slow;[].
            apply howe_lemma2_exc in z; exrepnd; auto; prove_isprogram.

            apply approx_star_open_trans with (b := mk_exception a' e').
            { apply approx_star_exception; auto. }

            apply approx_implies_approx_open.
            apply computes_to_exception_implies_approx; auto; prove_isprogram.
            allrw @computes_to_exception_as_reduces_to.
            eapply eapply_lam_exception_implies; eauto.
      }

      { fold_terms.
        apply approx_star_nseq in q; auto;[].

        repndors; exrepnd; subst; ginv.

        - eapply compute_step_eapply2_success in XX1; repnd; GC.
          repndors; exrepnd; ginv;[].
          apply approx_star_nat in Has1bt; auto;[].
          apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; eauto 2 with slow; subst.
          apply approx_open_implies_approx_star.
          apply approx_implies_approx_open.
          apply reduces_to_implies_approx1;[apply isprogram_eapply;eauto 2 with slow|].
          allunfold @computes_to_value; repnd.
          eapply reduces_to_trans;
            [apply implies_eapply_red;
              [|eauto
               |eauto]
            |]; eauto 3 with slow.
          apply reduces_to_if_step; csunf; simpl.
          dcwf xx; simpl; boolvar; try lia.
          rw @Znat.Nat2Z.id; auto.

        - apply isexc_implies in XX2; auto; exrepnd; subst.
          apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; eauto 2 with slow; subst.
          apply howe_lemma2_exc in Has1bt; prove_isprogram; exrepnd.

          apply approx_star_open_trans with (b := mk_exception a' e').
          { apply approx_star_exception; auto. }

          apply approx_implies_approx_open.
          apply computes_to_exception_implies_approx; auto; prove_isprogram.
          eapply eapply_nseq_exception_implies; eauto.

        - fold_terms.
          apply reduces_in_atmost_k_steps_eapply_nseq_to_isvalue_like in XX0; auto.

          repndors; exrepnd; subst.

          + applydup @preserve_compute_step in XX1; auto.
            assert (reduces_in_atmost_k_steps lib arg2 (mk_nat n) (S i)) as ra2.
            { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }
            apply no_change_after_val_like with (k2:=k) in ra2; eauto 2 with slow; try lia;[].
            make_red_val_like ra2 cck.
            pose proof (Hi arg2 (mk_nat n) a0r) as z.
            repeat (autodimp z hyp); eauto 2 with slow;[].
            apply approx_star_nat in z; eauto 2 with slow;[].

            apply approx_open_implies_approx_star.
            apply approx_implies_approx_open.
            apply reduces_to_implies_approx1;[apply isprogram_eapply;eauto 2 with slow|].
            allunfold @computes_to_value; repnd.
            eapply reduces_to_trans;
              [apply implies_eapply_red;
                [|eauto
                 |eauto]
              |]; eauto 3 with slow.
            apply reduces_to_if_step; csunf; simpl.
            dcwf xx; simpl; boolvar; try lia.
            rw @Znat.Nat2Z.id; auto.

          + apply isexc_implies in XX2; auto; exrepnd; subst.

            assert (reduces_in_atmost_k_steps lib arg2 (mk_exception a0 e) (S j)) as ra2.
            { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }

            apply no_change_after_val_like with (k2:=k) in ra2; try splr; try lia.
            make_red_val_like ra2 ca0.
            pose proof (Hi arg2 (mk_exception a0 e) a0r) as z.
            repeat (autodimp z hyp); eauto 2 with slow;[].
            apply howe_lemma2_exc in z; exrepnd; auto; prove_isprogram.

            apply approx_star_open_trans with (b := mk_exception a' e').
            { apply approx_star_exception; auto. }

            apply approx_implies_approx_open.
            apply computes_to_exception_implies_approx; auto; prove_isprogram.
            allrw @computes_to_exception_as_reduces_to.
            eapply eapply_nseq_exception_implies; eauto.
      }

    }


    { allsimpl.
      csunf XX1; allsimpl; ginv.
      apply howe_lemma2_seq in q; exrepnd; auto; prove_isprogram.
      apply compute_step_eapply_success in XX1; exrepnd; allunfold @nobnd; ginv.
      applydup @reduces_to_preserves_program in q0; auto.
      fold_terms.

      repndors; exrepnd; subst.

      - apply compute_step_eapply2_success in XX1; repnd; GC.
        repndors; exrepnd; ginv.
        apply approx_star_nat in Has1bt; auto.

        apply no_change_after_val_like with (k2:=k) in XX0; eauto 2 with slow; try lia;[].
        make_red_val_like XX0 ca0.
        pose proof (Hi (f n) a (f' n)) as z.
        repeat (autodimp z hyp); eauto 2 with slow;[].

        eapply approx_star_open_trans;[eauto|].
        apply approx_implies_approx_open.
        apply reduces_to_implies_approx_eauto; prove_isprogram.
        apply eapply_red_sterm_nat_implies; auto.

      - apply isexc_implies in XX2; auto; exrepnd; subst.
        apply reduces_in_atmost_k_steps_if_isvalue_like in XX0; eauto 2 with slow; subst.
        apply howe_lemma2_exc in Has1bt; exrepnd; auto; prove_isprogram.

        apply approx_star_open_trans with (b := mk_exception a' e').
        { apply approx_star_exception; auto. }

        apply approx_implies_approx_open.
        apply computes_to_exception_implies_approx; auto; prove_isprogram.
        eapply eapply_red_sterm_exception_implies; eauto.

      - apply reduces_in_atmost_k_steps_eapply_sterm_to_isvalue_like in XX0; auto.
        repndors; exrepnd.

        + assert (reduces_in_atmost_k_steps lib arg2 (mk_nat n) (S i)) as ra2.
          { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }
          apply no_change_after_value_ra with (k2:=k) in ra2; eauto 2 with slow; try lia;[].
          pose proof (Hi arg2 (mk_nat n) a0r) as z.
          make_red_val_like ra2 ca0.
          repeat (autodimp z hyp); eauto 2 with slow;[].
          apply approx_star_nat in z; auto.

          apply no_change_after_val_like with (k2:=k) in XX2; eauto 2 with slow; try lia;[].
          make_red_val_like XX2 caf.
          pose proof (Hi (f0 n) a (f' n)) as w.
          repeat (autodimp w hyp); eauto 2 with slow;[].
          eapply approx_star_open_trans;[eauto|].

          apply approx_implies_approx_open.
          apply reduces_to_implies_approx_eauto; prove_isprogram.
          apply eapply_red_sterm_nat_implies; auto.

        + apply isexc_implies in XX2; auto; exrepnd; subst.
          assert (reduces_in_atmost_k_steps lib arg2 (mk_exception a0 e) (S j)) as ra2.
          { rw @reduces_in_atmost_k_steps_S; eexists; dands; eauto. }
          apply no_change_after_val_like with (k2:=k) in ra2; try splr; try lia.
          make_red_val_like ra2 ca0.
          pose proof (Hi arg2 (mk_exception a0 e) a0r) as z.
          repeat (autodimp z hyp); eauto 2 with slow;[].
          apply howe_lemma2_exc in z; exrepnd; auto; prove_isprogram.

          apply approx_star_open_trans with (b := mk_exception a' e').
          { apply approx_star_exception; auto. }

          apply approx_implies_approx_open.
          apply computes_to_exception_implies_approx; auto; prove_isprogram.
          eapply eapply_red_sterm_exception_implies; eauto.
    }

  - apply isexc_implies in Hcv0; auto; exrepnd; subst.
    csunf XX1; allsimpl; ginv.
    apply reduces_atmost_exc in XX0; subst.
    clear Hcv.
    allrw @fold_exception.
    apply no_change_after_val_like with (k2:=k) in Hcv3; try splr.
    duplicate Has.
    unfold lblift_sub in Has; repnd; allsimpl.
    repeat(approxrelbtd). show_hyps.
    make_red_val_like Hcv3 h.
    unfold extensional_op_ind in Hi.
    apply Hi with (v := lar) in h; auto; prove_isprogram.
    apply howe_lemma2_exc in h; exrepnd; auto; prove_isprogram.

    apply approx_star_open_trans with (b := mk_exception a' e').
    { apply approx_star_exception; auto. }
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply reduces_to_trans with (b := mk_eapply (mk_exception a' e') a0r).
    { apply reduces_to_prinarg; auto. }
    apply reduces_to_if_step; reflexivity.
Qed.

(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/")
*** End:
*)
