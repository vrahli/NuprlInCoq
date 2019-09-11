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


Lemma implies_isprogram_find_last_entry_default {o} :
  forall lib name (d : @NTerm o),
    isprogram d
    -> isprogram (find_last_entry_default lib name d).
Proof.
  introv isp.
  unfold find_last_entry_default.
  remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; auto.
  remember (last_cs_entry c) as lcs; symmetry in Heqlcs; destruct lcs; auto.
Qed.
Hint Resolve implies_isprogram_find_last_entry_default : slow.

Lemma implies_approx_star_find_last_entry_default {o} :
  forall lib name (a b : @NTerm o),
    approx_star lib a b
    -> approx_star
         lib
         (find_last_entry_default lib name a)
         (find_last_entry_default lib name b).
Proof.
  introv apr.
  unfold find_last_entry_default.
  remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs; auto.
  remember (last_cs_entry c) as lcs; symmetry in Heqlcs; destruct lcs; auto.
  apply approx_star_refl; eauto 3 with slow.
Qed.
Hint Resolve implies_approx_star_find_last_entry_default : slow.

Lemma extensional_last_cs {p} : extensional_op (@NCan p NLastCs).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  applydup @compute_decompose_aux in Hcv; auto; exrepnd.

  repndors; exrepnd; [|allsimpl; subst; repnd; complete ginv].

  assert (m <= S k) as XX by omega.
  repnud Hcv.
  eapply reduces_atmost_split in XX; eauto.
  remember (S k - m) as skm.
  destruct skm; [omega|].
  assert (skm <= k) by (subst; omega).
  apply reduces_atmost_S in XX; exrepnd.
  applydup @reduces_atmost_preserves_program in Hcv4; auto.
  apply isprogram_last_cs_implies_ex in Hcv6; unfold nobnd in *; exrepnd; subst; cpx.

  dorn Hcv0.

  - apply iscan_implies in Hcv0; repndors; exrepnd; subst.

    { csunf XX1; allsimpl.
      apply compute_step_last_cs_success in XX1; exrepnd; repndors;
        exrepnd; subst; unfold nobnd in *; ginv.

      apply no_change_after_value_ra with (k2:=k) in Hcv3; auto.
      duplicate Has.
      unfold lblift_sub in Has; repnd; allsimpl; cpx.
      repeat(approxrelbtd); show_hyps.
      make_red_val_like Hcv3 h.
      unfold extensional_op_ind in Hi.
      apply Hi with (v := lar) in h; eauto; prove_isprogram.
      apply howe_lemma2 in h; exrepnd; auto; prove_isprogram.
      duplicate h1.
      rename a into c.
      unfold approx_starbts, lblift_sub in h1; repnd; allsimpl; cpx.
      clear h1 h2.

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
      apply reduces_atmost_preserves_program in Hcv4; auto; try omega.

      make_red_val_like XX0 hh.
      applydup @isprogram_last_cs_implies in Hprt'; repnd.

      pose proof (Hi (find_last_entry_default lib name d)
                     c
                     (find_last_entry_default lib name dr)) as q.
      repeat (autodimp q hyp); eauto 2 with slow;[].

      eapply approx_star_open_trans;[eauto|].
      apply reduces_to_implies_approx_open1; eauto 2 with slow.
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
    { apply approx_star_exception; auto. }
    apply approx_implies_approx_open.
    apply computes_to_exception_implies_approx; auto; prove_isprogram.
    allrw @computes_to_exception_as_reduces_to.
    apply reduces_to_trans with (b := mk_last_cs (mk_exception a' e') ur).
    { apply reduces_to_prinarg; auto. }
    apply reduces_to_if_step; reflexivity.
Qed.
