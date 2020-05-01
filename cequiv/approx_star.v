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
Require Export approx_star_abs.
Require Export approx_star_fresh.
Require Export approx_star_swap.

Require Import extensional_apply.
Require Import extensional_eapply.
Require Import extensional_fix.
Require Import extensional_cbv.
Require Import extensional_trycatch.
Require Import extensional_spread.
Require Import extensional_dsup.
Require Import extensional_decide.
Require Import extensional_arith.
Require Import extensional_ncomp.
Require Import extensional_cantest.
Require Import extensional_sleep.
Require Import extensional_tuni.
Require Import extensional_minus.
Require Import extensional_abs.
Require Import extensional_fresh.
Require Import extensional_parallel.
Require Import extensional_lastcs.
Require Import extensional_compseq1.
Require Import extensional_compseq2.
Require Import extensional_swap_cs1.
Require Import extensional_swap_cs2.
Require Import extensional_ldepth.


Theorem nuprl_extensional {p} : forall op, @extensional_op p op.
  (* begin show *)
Proof.
  intro op. destruct op.
  - apply nuprl_extensional_can.
  - dopid_noncan n Case.
    + Case "NApply";    apply extensional_apply.
    + Case "NEApply";   apply extensional_eapply.
(*    + Case "NApseq";    apply extensional_apseq.*)
    + Case "NFix";      apply extensional_fix.
    + Case "NSpread";   apply extensional_spread.
    + Case "NDsup";     apply extensional_dsup.
    + Case "NDecide";   apply extensional_decide.
    + Case "NCbv";      apply extensional_cbv.
    + Case "NSleep";    apply extensional_sleep.
    + Case "NTUni";     apply extensional_tuni.
    + Case "NMinus";    apply extensional_minus.
    + Case "NFresh";    apply extensional_fresh.
    + Case "NTryCatch"; apply extensional_trycatch.
    + Case "NParallel"; apply extensional_parallel.
    + Case "NSwapCs1";  apply extensional_swap_cs1.
(*    + Case "NSwapCs2";  apply extensional_swap_cs2.*)
    + Case "NLDepth";   apply extensional_ldepth.
    + Case "NLastCs";   apply extensional_last_cs.
    + Case "NCompSeq1"; apply extensional_comp_seq1.
    + Case "NCompSeq2"; apply extensional_comp_seq2.
    + Case "NCompOp";   apply extensional_ncomp.
    + Case "NArithOp";  apply extensional_arith.
    + Case "NCanTest";  apply extensional_cantest.
  - apply extensional_swap_cs2.
  - apply nuprl_extensional_exc.
  - apply nuprl_extensional_abs.
Qed.

(* end show *)

(** %\noindent \\*% As we mentioned above, Howe
    abstracted the  extensionality condition above out
    of the proof of the following lemma.
    Hence its proof follows directly
    from the lemma [nuprl_extensional].

*)
Lemma howe_lemma3 {p} : forall lib (a a' b : @NTerm p),
  isprogram a
  -> isprogram a'
  -> isprogram b
  -> computes_to_val_like lib a a'
  -> approx_star lib a b
  -> approx_star lib a' b.
Proof.
  introv Hpra Hpra' Hprb Hc Hs.
  repnud Hc; exrepnd.
  revert lib a a' b Hpra Hpra' Hprb Hc0 Hs.
  induction k as [| k Hind]; introv Hpra Hpra' Hprb comp ap.

  - unfold computes_to_val_like_in_max_k_steps, reduces_in_atmost_k_steps in comp; repnd.
    simpl in comp0; inversion comp0; subst; auto.

  - destruct a as [|o lba]; [inversion Hpra as [c w]; inversion c|].

    + pose proof (@nuprl_extensional p) as Hex.
      applydup @approx_star_otd in ap; auto; []; exrepnd.
      unfold extensional_op in Hex.
      apply Hex with (lbt' := lbt') in comp; auto.
      eapply approx_star_open_trans; eauto.
Qed.

Lemma howe_lemma3_val {p} :
  forall lib (a a' b : @NTerm p),
    isprogram a
    -> isprogram a'
    -> isprogram b
    -> computes_to_value lib a a'
    -> approx_star lib a b
    -> approx_star lib a' b.
Proof.
  introv ispa ispa' ispb comp ap.
  apply @howe_lemma3 with (a := a); auto.
  apply computes_to_value_implies_val_like; auto.
Qed.

(*
(* !! MOVE to computation4 *)
Lemma computes_to_marker_implies_val_like {p} :
  forall lib (a : @NTerm p) m,
    computes_to_marker lib a m
    -> computes_to_val_like lib a (mk_marker m).
Proof.
  introv comp.
  unfold computes_to_val_like, computes_to_val_like_in_max_k_steps.
  unfold computes_to_marker, reduces_to in comp.
  exrepnd.
  exists k; dands; auto.
  right.
  constructor.
Qed.
*)

Lemma howe_lemma3_exc {p} :
  forall lib en (a a' b : @NTerm p),
    isprogram en
    -> isprogram a
    -> isprogram a'
    -> isprogram b
    -> computes_to_exception lib en a a'
    -> approx_star lib a b
    -> approx_star lib (mk_exception en a') b.
Proof.
  introv ispa ispa' ispb comp ap.
  apply @howe_lemma3 with (a := a); auto.
  apply isprogram_exception; auto.
  apply computes_to_exception_implies_val_like; auto.
Qed.

(*
Lemma howe_lemma3_mrk {p} :
  forall lib (a b : @NTerm p) m,
    isprogram a
    -> isprogram b
    -> computes_to_marker lib a m
    -> approx_star lib a b
    -> approx_star lib (mk_marker m) b.
Proof.
  introv ispa ispb comp ap.
  apply @howe_lemma3 with (a := a); auto; [apply isprogram_marker|].
  apply computes_to_marker_implies_val_like; auto.
Qed.
*)

(* begin hide *)

Lemma alphaeq_preserves_wf_r_eauto {p} :
  forall t1 t2 : @NTerm p, alpha_eq t1 t2 -> nt_wf t1 -> nt_wf t2.
Proof.
  introv Hal Hw. apply alphaeq_preserves_wf in Hal.
  destruct Hal.
  auto.
Qed.

Lemma alphaeqbt_preserves_prog_r_eauto {p} :
  forall t1 t2 : @BTerm p, alpha_eq_bterm t1 t2 -> isprogram_bt t1 -> isprogram_bt t2.
Proof.
  introv Hal Hw. allunfold @isprogram_bt. allunfold @closed_bt. exrepnd. dands.
  - apply alphaeqbt_preserves_fvars in Hal. rw Hw0 in Hal.
    apply eq_vars_nil in Hal; sp.
  - apply alphaeqbt_preserves_wf in Hal; destruct Hal.  sp.
Qed.

Hint Resolve alphaeqbt_preserves_prog_r_eauto : slow.

Lemma isprogam_bt_nt_wf_eauto {p} :
  forall (lv : list NVar) (nt : @NTerm p), isprogram_bt (bterm lv nt) -> nt_wf nt.
Proof.
  introv Hb.
  repnud Hb.
  apply bt_wf_iff in Hb; sp.
Qed.

Theorem howetheorem1_aux {p}:
  forall lib,
    (fun a b => @approx_star p lib a b # isprogram a # isprogram b)
    =2> (approx lib).
Proof.
  intro lib.
  apply approx_acc.
  introv Cb Cih. intros a b Has.
  exrepnd.
  constructor.
  unfold close_comput.
  dands; spcf.

  - introv hcv.
    applydup @preserve_program in hcv; sp;[].
    apply @howe_lemma3_val with (b:=b) in hcv; sp;[].
    apply howe_lemma2 in hcv;exrepnd; spc;[].
    exists lbt'; dands;sp.
    unfold approx_starbts in hcv2.
    allunfold @lblift_sub.
    exrepnd.
    split; spcf.
    introv Hlt.
    applydup hcv2 in Hlt.
    unfold blift.
    invertsna Hlt0 Hbas.
    exrepnd; repndors; exrepnd; ginv.
    exists x nt1 nt2.
    dands; sp.
    unfold olift.
    applydup @preserve_program in hcv1;spcf;[].
    applydup @isprogram_ot_iff in hcv4.
    applydup @isprogram_ot_iff in hcv0.
    exrepnd. clear hcv8 hcv7.
    Hint Resolve selectbt_in alphaeq_preserves_wf_r_eauto isprogam_bt_nt_wf_eauto : slow.
    assert (n < length lbt') as X99 by omega.
    dands; spcf; try (apply isprogam_bt_nt_wf_eauto with (lv:=x); eauto with slow);[].
    introv Hw Hpa Hpb.
    right.
    apply Cih;sp.
    apply lsubst_approx_star_congr3;sp.

  - introv comp.
    applydup @preserve_program_exc2 in comp; sp;[].
    apply @howe_lemma3_exc with (b:=b) in comp; sp;[].
    apply howe_lemma2_exc in comp; auto;
    try (apply isprogram_exception; auto); exrepnd;[].
    applydup @preserve_program_exc2 in comp3; auto; repnd.
    exists a' e'; dands; auto; tcsp.
Qed.

(* end hide *)

(** %\noindent \\*%
    Now Howe uses a simple coindiuctive argument to show that
    [approx_star] implies [approx] on closed terms.

 *)
Theorem howetheorem1 {p} :
  forall lib a b,
    @approx_star p lib a b
    -> isprogram a
    -> isprogram b
    -> approx lib a b.
Proof.
  intros. apply howetheorem1_aux;sp.
Qed.

(** %\noindent \\*%
    There are many useful Corollaries of the above theorem.

 *)
Corollary approx_star_implies_approx_open {p} :
  forall lib (t1 t2 : @NTerm p), approx_star lib t1 t2 -> approx_open lib t1 t2.
Proof.
  introv Has.
  applydup @approx_star_relates_only_wf in Has. repnd.
  unfold approx_open, olift. dands; spcf. introv Hw Hpa Hpb.
  apply howetheorem1;sp.
  apply lsubst_approx_star_congr3;sp.
Qed.

Corollary approx_star_iff_approx_open {p} :
  forall lib (t1 t2 : @NTerm p), approx_star lib t1 t2 <=> approx_open lib t1 t2.
Proof.
  split; introv hyp.
  - apply approx_star_implies_approx_open;sp.
  - apply approx_open_implies_approx_star;sp.
Qed.

Lemma le_blift_sub {p} :
  forall lib op (R1 R2 : @LNTrel p),
    le_bin_rel (R1 lib) (R2 lib) -> le_bin_rel (blift_sub op R1 lib) (blift_sub op R2 lib).
Proof.
  unfold le_bin_rel.
  intros R1 R2 Hle a b Hrel.
  allunfold @blift_sub.
  sp.
  - exists lv nt1 nt2; split; eauto.
  - exists lv nt1 nt2; split; eauto.
    subst; right; exists sub; subst; split; eauto.
Defined.
Hint Resolve le_blift_sub : slow.

Lemma le_blift_sub2 {p} :
  forall lib op (R1 R2 : @LNTrel p),
    le_bin_rel (R1 lib) (R2 lib)
    -> forall a b, (blift_sub op R1 lib a b) -> (blift_sub op R2 lib a b).
Proof.
  introv H.
  fold (@le_bin_rel (BTerm ) (blift_sub op R1 lib) (blift_sub op R2 lib)).
  apply le_blift_sub.
  auto.
Defined.
Hint Resolve le_blift_sub2 : slow.

Lemma le_lblift_sub {p} :
  forall lib op (R1 R2 : @LNTrel p),
    le_bin_rel (R1 lib) (R2 lib)
    -> le_bin_rel (lblift_sub op R1 lib) (lblift_sub op R2 lib).
Proof.
  unfold lblift_sub; sp.
  unfold le_bin_rel; sp.
  generalize (X0 n); sp.
  apply @le_blift_sub2 with (R1 := R1); sp.
Defined.

Lemma le_lblift_sub2 {p} :
  forall lib op (R1 R2 : @LNTrel p),
    le_bin_rel (R1 lib) (R2 lib)
    -> forall a b, (lblift_sub op R1 lib a b) -> (lblift_sub op R2 lib a b).
Proof.
  introv H.
  fold (@le_bin_rel (list BTerm) (lblift_sub op R1 lib) (lblift_sub op R2 lib)).
  apply le_lblift_sub. auto.
Defined.

Corollary approx_open_congruence_sub {p} :
  forall lib (o : Opid) (lbt1 lbt2 : list (@BTerm p)),
    lblift_sub o approx_open lib lbt1 lbt2
    -> nt_wf (oterm o lbt2)
    -> approx_open lib (oterm o lbt1) (oterm o lbt2).
Proof.
  introv Haps Hnt.
  apply (le_lblift_sub2 _ _ _ _ (approx_open_implies_approx_star lib)) in Haps.
  apply approx_star_implies_approx_open.
  apply approx_star_congruence2; sp.
Qed.

Corollary approx_open_congruence {p} :
  forall lib (o : Opid) (lbt1 lbt2 : list (@BTerm p)),
    lblift (approx_open lib) lbt1 lbt2
    -> nt_wf (oterm o lbt2)
    -> approx_open lib (oterm o lbt1) (oterm o lbt2).
Proof.
  introv Haps Hnt.
  apply (le_lblift2 _ _ (approx_open_implies_approx_star lib)) in Haps.
  apply approx_star_implies_approx_open.
  apply approx_star_congruence2; sp.

  unfold approx_starbts, lblift_sub.
  unfold lblift in Haps; repnd; dands; auto.
  introv i; applydup Haps in i as b.
  unfold blift in b; unfold blift_sub; exrepnd.
  exists lv nt1 nt2; dands; auto.
  destruct (dec_op_eq_fresh o) as [d|d]; tcsp.
  right.

  pose proof (exists_nrut_sub
                lv
                (get_utokens_lib lib nt1 ++ get_utokens_lib lib nt2))
    as exnrut; exrepnd.
  exists sub; dands; auto.
  apply lsubst_approx_star_congr3; eauto with slow.
Qed.

Corollary approx_congruence_sub {p} :
  forall lib o lbt1 lbt2,
    lblift_sub o approx_open lib lbt1 lbt2
    -> @isprogram p (oterm o lbt1)
    -> isprogram (oterm o lbt2)
    -> approx lib (oterm o lbt1) (oterm o lbt2).
Proof.
   introv Haps H1p H2p.
   apply approx_open_approx;sp.
   apply approx_open_congruence_sub;sp.
   eauto with slow.
Qed.

Corollary approx_congruence {p} : forall lib o lbt1 lbt2,
  lblift (approx_open lib) lbt1 lbt2
  -> @isprogram p (oterm o lbt1)
  -> isprogram (oterm o lbt2)
  -> approx lib (oterm o lbt1) (oterm o lbt2).
Proof.
   introv Haps H1p H2p.
   apply approx_open_approx;sp.
   apply approx_open_congruence;sp.
   eauto with slow.
Qed.

(* begin hide *)

Ltac prove_approx_lblift :=
  unfold lblift; simpl; dands;[spc|];
  let Hlt := fresh "XXHlt" in
  let n := fresh "XXn" in
  intros n Hlt;
    ( let rnum := (get_lt_rhs  Hlt) in
      fail_if_not_number rnum; (*fail if not a normal form*)
      repeat (destruct n; try omega); unfold selectbt; simpl; unfold nobnd
    ).

Ltac prove_approx_lblift_sub :=
  unfold lblift_sub; simpl; dands;[spc|];
  let Hlt := fresh "XXHlt" in
  let n := fresh "XXn" in
  intros n Hlt;
    ( let rnum := (get_lt_rhs  Hlt) in
      fail_if_not_number rnum; (*fail if not a normal form*)
      repeat (destruct n; try omega); unfold selectbt; simpl; unfold nobnd
    ).

Ltac prove_approx :=
  unfold_all_mk;
  match goal with
    | [ |- approx _ ?t ?t] => apply approx_refl
    | [ |- approx_open _ ?t ?t] => apply approx_open_refl
    | [ |- approx_open _ ?t1 ?t2] => apply approx_implies_approx_open
    | [ |- approx _ (oterm ?o _) (oterm ?o _)] => apply approx_congruence
    | [ |- isprogram _] => repeat(decomp_progh); show_hyps; repeat(decomp_progc); sp
    (* blift *)
    | [ |- lblift (olift approx) _ ] => prove_approx_lblift
    | [ |- lblift (olift approx) _ _ ] => prove_approx_lblift
    | [ |- lblift (approx_open _) _ _ ] => prove_approx_lblift
    | [ |- lblift (olift approx) _ _ _ ] => prove_approx_lblift
    | [ |- lblift (olift approx) _ _ _ _ ] => prove_approx_lblift
    | [ |- blift (olift approx) (bterm [] ?t1) (bterm [] ?t2)] => apply blift_nobnd_congr
    | [ |- blift (approx_open _) (bterm [] ?t1) (bterm [] ?t2)] => apply blift_nobnd_congr
    (* lblift *)
    | [ |- lblift_sub _ (olift approx) _ ] => prove_approx_lblift_sub
    | [ |- lblift_sub _ (olift approx) _ _ ] => prove_approx_lblift_sub
    | [ |- lblift_sub _ (approx_open _) _ _ ] => prove_approx_lblift_sub
    | [ |- lblift_sub _ (olift approx) _ _ _ ] => prove_approx_lblift_sub
    | [ |- lblift_sub _ (olift approx) _ _ _ _ ] => prove_approx_lblift_sub
    | [ |- blift_sub _ (olift approx) (bterm [] ?t1) (bterm [] ?t2)] => apply blift_nobnd_congr
    | [ |- blift_sub _ (approx_open _) (bterm [] ?t1) (bterm [] ?t2)] => apply blift_nobnd_congr
  end.

Lemma le_bin_rel_approx1_eauto {p} :
  forall lib, le_bin_rel (approx lib) (@approx_star p lib).
Proof.
  introv Has.
  eauto with slow.
  apply approx_star_iff_approx_open.
  apply approx_implies_approx_open.
  auto.
Qed.

Lemma le_bin_rel_approx2_eauto {p} :
  forall lib, le_bin_rel (@approx p lib) (indep_bin_rel isprogram isprogram).
Proof.
  introv Has. unfolds_base.
  apply approx_relates_only_progs in Has;sp.
Qed.

(* end hide *)

Corollary lsubst_approx_congr {p} : forall lib t1 t2 sub1 sub2,
  sub_range_rel (@approx p lib) sub1 sub2
  -> approx_open lib t1 t2
  -> isprogram (lsubst t1 sub1)
  -> isprogram (lsubst t2 sub2)
  -> approx lib (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv Hsr Hao H1p H2p.
  apply (le_sub_range_rel _ _  (le_bin_rel_approx1_eauto lib)) in Hsr.
  apply howetheorem1; auto.
  apply approx_open_implies_approx_star in Hao.
  apply lsubst_approx_star_congr2; auto.
Qed.

(* begin hide *)

Lemma approxbtd_change3 {p} : forall lib bt1 bt2 (lvn: list NVar),
  approx_open_bterm lib bt1 bt2
  -> no_repeats lvn
  -> length lvn = num_bvars bt1
  -> disjoint lvn (free_vars_bterm bt1  ++ free_vars_bterm bt2)
  -> approx_open lib (apply_bterm bt1 (map vterm lvn))
                 (apply_bterm bt2 (map (@vterm p) lvn)).
Proof.
  introv Hao Hnr Hlen Hdis.
  destruct bt1 as [lv1 nt1].
  destruct bt2 as [lv2 nt2].
  applydup @blift_numbvars in Hao.
  apply @approxbtd_change with (lvn:=lvn) in Hao; auto;[].
  exrepnd.
  unfold apply_bterm. allsimpl.
  allrw @fold_var_ren.
  allunfold @num_bvars. allsimpl.
  apply apply_bterm_alpha_congr2 with (lnt := map vterm lvn)  in Hao3; spcls; try congruence;[].
  apply apply_bterm_alpha_congr2 with (lnt := map vterm lvn)  in Hao4; spcls;
    unfold num_bvars; simpl;  try congruence;[].
  allunfold @apply_bterm.
  allsimpl.
  allrw (@fold_var_ren).
  pose proof (lsubst_trivial_alpha nt2' lvn)  as zz.
  pose proof (lsubst_trivial_alpha nt1' lvn)  as zzz.
  assert (alpha_eq nt1' (lsubst nt1 (var_ren lv1 lvn))) as r1 by eauto with slow.
  assert (alpha_eq nt2' (lsubst nt2 (var_ren lv2 lvn))) as r2 by eauto with slow.
  clear zzz zz Hao0 Hdis Hlen Hnr Hao2 Hao4 Hao3.
  eapply approx_open_alpha_rw_lr in Hao1; eauto with slow.
Qed.

Lemma implies_approx_fix {p} :
  forall lib a b,
    @approx p lib a b
    -> approx lib (mk_fix a) (mk_fix b).
Proof.
  introv ap.
  applydup @approx_relates_only_progs in ap.
  repnd.
  repeat (prove_approx);sp.
Qed.

(*
Lemma implies_approx_apseq {p} :
  forall lib f a b,
    @approx p lib a b
    -> approx lib (mk_apseq f a) (mk_apseq f b).
Proof.
  introv ap.
  applydup @approx_relates_only_progs in ap.
  repnd.
  repeat (prove_approx);sp.
Qed.
*)

Lemma implies_approx_apply {p} :
  forall lib f g a b,
    approx lib f g
    -> @approx p lib a b
    -> approx lib (mk_apply f a) (mk_apply g b).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  repeat (prove_approx);sp.
Qed.

(*
(* !! MOVE to computation4 *)
Lemma if_computes_to_marker_apply {p} :
  forall lib (f a : @NTerm p) m,
    isprogram f
    -> isprogram a
    -> computes_to_marker lib (mk_apply f a) m
    -> {v : NVar & {b : NTerm & reduces_to lib f (mk_lam v b)}}.
Proof.
  introv.
  unfold computes_to_marker, reduces_to.
  introv ispf ispa comp; exrepnd.
  revert f a ispf ispa comp0.
  induction k; simpl; introv ispf ispa comp.

  - inversion comp; subst; GC.

  - apply reduces_in_atmost_k_steps_S in comp; exrepnd.
    simpl in comp1.
    destruct f; try (complete (inversion comp1)).
    dopid o as [can|ncan|exc|abs] Case; try (complete (inversion comp1)).

    + Case "Can".
      csunf comp1; allsimpl.
      apply compute_step_apply_success in comp1; exrepnd; subst; cpx; GC.
      exists v b 0; sp.

    + Case "NCan".
      unfold mk_apply, nobnd in comp1; rw @compute_step_ncan_ncan in comp1.
      remember (compute_step lib (oterm (NCan ncan) l)); destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @preserve_compute_step in Heqc; auto.
      apply IHk in comp0; auto.
      exrepnd.

      exists v b (S k0).
      rw @reduces_in_atmost_k_steps_S.
      exists n; sp.

    + Case "Exc".
      csunf comp1; simpl in comp1; ginv.
      apply reduces_atmost_exc in comp0; ginv.

    + Case "Abs".
      unfold mk_apply, nobnd in comp1; rw @compute_step_ncan_abs in comp1.
      remember (compute_step_lib lib abs l); destruct c; inversion comp1; subst; GC.
      symmetry in Heqc.
      applydup @isprogram_compute_step_lib in Heqc; auto.
      apply IHk in comp0; auto; exrepnd.

      exists v b (S k0).
      rw @reduces_in_atmost_k_steps_S.
      exists n; sp.
Qed.
*)

Lemma hasvalue_like_implies_or {o} :
  forall lib (t : @NTerm o),
    isprogram t
    -> hasvalue_like lib t
    -> hasvalue lib t
       [+] raises_exception lib t.
Proof.
  introv isp hv.
  unfold hasvalue_like in hv; exrepnd.
  applydup @reduces_to_preserves_program in hv1; auto.
  dorn hv0.
  - left.
    exists v.
    unfold computes_to_value; dands; auto.
  - right.
    apply isexc_implies in hv0; exrepnd; subst; auto.
    exists a e; auto.
Qed.

Lemma fix_unfold_approx_fix {p} : forall lib f,
  @isprogram p f
  -> approx lib (mk_apply f (mk_fix f)) (mk_fix f).
Proof.
  introv Hpr.
  apply approx_assume_hasvalue;
  try match goal with [|- isprogram _] => eauto with slow; fail end.
  introv Hv.

  apply hasvalue_like_implies_or in Hv;
    [|apply isprogram_apply; auto; apply isprogram_fix; complete auto].

  dorn Hv.

  - unfold hasvalue in Hv; exrepnd.
    applydup @if_computes_to_value_apply in Hv0; auto;
    allrw @isprog_eq; auto; try (apply isprogram_fix; auto).
    repndors; exrepnd.

    { clear Hv1.
      applydup @computes_to_value_preserves_program in Hv2; auto.
      apply @approx_trans with (b := mk_fix (mk_lam v b)).

      + apply @approx_trans with (b := mk_apply (mk_lam v b) (mk_fix (mk_lam v b))); auto.

        * apply implies_approx_apply.
          apply reduces_to_implies_approx2; auto.
          destruct Hv2; auto.
          apply implies_approx_fix.
          apply reduces_to_implies_approx2; auto.
          destruct Hv2; auto.

        * apply reduces_to_implies_approx1; auto.
          apply isprogram_fix; auto.
          apply reduces_to_if_step; reflexivity.

      + apply implies_approx_fix; auto.
        apply reduces_to_implies_approx_eauto; prove_isprogram.
        destruct Hv2; auto.
    }

    { apply @approx_trans with (b := mk_fix (mk_choice_seq n)).

      + apply @approx_trans with (b := mk_apply (mk_choice_seq n) (mk_fix (mk_choice_seq n))); auto.

        * apply implies_approx_apply.
          { apply reduces_to_implies_approx2; auto.
            destruct Hv1; auto. }
          { apply implies_approx_fix.
            apply reduces_to_implies_approx2; auto.
            destruct Hv1; auto. }

        * apply reduces_to_implies_approx1; auto; prove_isprogram.
          apply reduces_to_if_step; reflexivity.

      + apply implies_approx_fix; auto.
        apply reduces_to_implies_approx_eauto; prove_isprogram.
        destruct Hv1; auto.
    }

  - repnud Hv; exrepnd.
    applydup @isprogram_fix in Hpr.
    apply if_computes_to_exception_apply in Hv1; auto.
    repndors; exrepnd.

    + applydup @reduces_to_preserves_program in Hv1; auto.
      apply @approx_trans with (b := mk_fix (mk_lam v b)).

      * apply @approx_trans with (b := mk_apply (mk_lam v b) (mk_fix (mk_lam v b))); auto.

        apply implies_approx_apply.
        apply reduces_to_implies_approx2; auto.
        apply implies_approx_fix.
        apply reduces_to_implies_approx2; auto.

        apply reduces_to_implies_approx1; auto.
        apply isprogram_fix; auto.
        apply reduces_to_if_step; reflexivity.

      * apply implies_approx_fix; auto.
        apply reduces_to_implies_approx_eauto; prove_isprogram; auto.

    + apply @approx_trans with (b := mk_fix (mk_choice_seq n)).

      * apply @approx_trans with (b := mk_apply (mk_choice_seq n) (mk_fix (mk_choice_seq n))); auto.

        { apply implies_approx_apply.
          { apply reduces_to_implies_approx2; auto. }
          { apply implies_approx_fix.
            apply reduces_to_implies_approx2; auto. }
        }

        { apply reduces_to_implies_approx1; auto.
          { apply isprogram_fix; eauto 3 with slow. }
          { apply reduces_to_if_step; reflexivity. }
        }

      * apply implies_approx_fix; auto.
        apply reduces_to_implies_approx_eauto; prove_isprogram; auto.

    + applydup @preserve_program_exc2 in Hv1; repnd; auto.
      apply approx_trans with (b := mk_apply (mk_exception a e) (mk_fix f)).

      * apply implies_approx_apply; auto; try (apply approx_refl; auto).
        apply computes_to_exception_implies_approx; auto.

      * applydup (isprogram_exception a)  in Hv0; auto.
        apply approx_trans with (b := mk_fix (mk_exception a e)).

        apply approx_trans with (b := mk_exception a e).
        apply reduces_to_implies_approx2; auto.
        apply isprogram_apply; auto.
        apply reduces_to_if_step; reflexivity.

        apply reduces_to_implies_approx1; auto.
        apply isprogram_fix; auto.
        apply reduces_to_if_step; reflexivity.

        apply implies_approx_fix.
        apply reduces_to_implies_approx1; auto.
        Grab Existential Variables.
Qed.
