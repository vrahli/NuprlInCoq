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

Require Export approx_star0.


Lemma extensional_apply {p} : extensional_op (@NCan p NApply).
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
  apply isprogram_apply_implies in Hcv6; exrepnd; subst; cpx.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst.

    { csunf XX1; allsimpl.
      apply compute_step_apply_success in XX1; repndors; exrepnd; subst; ginv.

      + (* destruct lhs for a bit so that the args of lambda show up*)
        rename v into lamv.
        rename b into lamb.
        rename la into lamnt.
        apply no_change_after_value_ra with (k2:=k) in Hcv3; auto.
        duplicate Has.
        unfold lblift_sub in Has; repnd; allsimpl; cpx.
        repeat(approxrelbtd); show_hyps.
        make_red_val_like Hcv3 h.
        unfold extensional_op_ind in Hi.
        apply Hi with (v := lamntr) in h; eauto; prove_isprogram.
        apply howe_lemma2 in h; exrepnd; auto; prove_isprogram.
        duplicate h1.
        rename a into c.
        unfold approx_starbts, lblift_sub in h1; repnd; allsimpl; cpx.
        repeat(approxrelbtd); show_hyps.
        apply apply_bterm_approx_star_congr with
        (lnt1:= [arg]) (lnt2:= [argr]) in h10bt; tcsp;
        try (complete (intro xx; ginv));
        [|prove_bin_rel_nterm; fail].
        apply no_change_after_val_like with (k2 := k) in XX0; auto.
        repnud h0.

        match goal with
            [ |- approx_star _ _ (oterm (NCan ?no) _)] =>
            let T := type of Has0 in
            match T with
              | lblift_sub _ _ (approx_star _) _ (_::?tr) =>
                apply reduces_to_prinarg
                with (lbt:= tr) (op:=no) in h1
            end
        end. (* this will be used later in this proof *)
        pose proof (reduces_to_preserves_program _ _ _ h1 Hprt') as Hispr.
        apply reduces_atmost_preserves_program in Hcv4; auto; try lia.

        make_red_val_like XX0 hh.

        let T:= type of h10bt  in
        match T with
          | approx_star ?lib ?tl ?tr =>
            assert (isprogram tl) by (apply (preserve_compute_step lib) with (t2:=tl) in Hcv4;sp);
              assert(isprogram tr) by (apply (preserve_compute_step lib) with (t2:=tr) in Hispr;sp);
              apply Hi with (v:=tr) in hh; auto;
              apply approx_star_open_trans with (b:= tr); auto
        end.
        apply approx_implies_approx_open;
          apply reduces_to_implies_approx_eauto;auto;
          eapply reduces_to_if_split1; eauto.

      + apply no_change_after_value_ra with (k2:=k) in Hcv3; auto.
        duplicate Has.
        unfold lblift_sub in Has; repnd; allsimpl; cpx.
        repeat(approxrelbtd); show_hyps.
        make_red_val_like Hcv3 h.
        unfold extensional_op_ind in Hi.
        apply Hi with (v := lar) in h; eauto; prove_isprogram.
        apply howe_lemma2 in h; exrepnd; auto; prove_isprogram.
        unfold approx_starbts, lblift_sub in h1; repnd; allsimpl; cpx.
        clear h1.
        rename a into c.
        apply no_change_after_val_like with (k2 := k) in XX0; auto.
        repnud h0.

        match goal with
            [ |- approx_star _ _ (oterm (NCan ?no) _)] =>
            let T := type of Has0 in
            match T with
              | lblift_sub _ _ (approx_star _) _ (_::?tr) =>
                apply reduces_to_prinarg
                with (lbt:= tr) (op:=no) in h1
            end
        end. (* this will be used later in this proof *)
        pose proof (reduces_to_preserves_program _ _ _ h1 Hprt') as Hispr.
        apply reduces_atmost_preserves_program in Hcv4; auto; try lia.

        make_red_val_like XX0 hh.

        allrw <- @isprogram_apply_iff; repnd.

        pose proof (Hi (mk_eapply (mk_choice_seq n) arg) c (mk_eapply (mk_choice_seq n) argr)) as q.
        repeat (autodimp q hyp); try (apply isprogram_eapply); auto.
        { apply approx_star_congruence3; try (apply isprogram_eapply); auto.
          repeat (apply approx_starbts_cons; dands; eauto 3 with slow).
          { unfold nobnd; prove_approx_star; auto.
            apply approx_open_implies_approx_star.
            apply approx_implies_approx_open; eauto 3 with slow. }
          { unfold nobnd; prove_approx_star; auto. }
        }

        eapply approx_star_open_trans;[exact q|].
        apply approx_implies_approx_open.
        apply reduces_to_implies_approx_eauto;
          allrw <- @isprogram_apply_iff; auto.
        eapply reduces_to_if_split1; eauto.
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
    apply approx_star_exception; auto.
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply reduces_to_trans with (b := mk_apply (mk_exception a' e') a0r).
    apply reduces_to_prinarg; auto.
    apply reduces_to_if_step; reflexivity.
Qed.
