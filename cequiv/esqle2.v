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


Require Export sqle.
Require Export eapprox2.


Inductive ex_sqle_n {o} (lib : @library o) (ex : @NTerm o)
  :  nat -> @NTerm o -> @NTerm o -> [univ] :=
| ex_sql0 : forall tl tr, isprogram tl -> isprogram tr -> ex_sqle_n lib ex 0 tl tr
| ex_sql_add1 : forall n tl tr,
    ex_close_comput lib ex (ex_sqle_n lib ex n) tl tr
    -> ex_sqle_n lib ex (S n) tl tr.


Lemma respects_alpha_ex_sqlen {o} :
  forall lib (ex : @NTerm o) n,
    respects_alpha (ex_sqle_n lib ex n).
Proof.
  induction n; split; introv Hal Hap;
  invertsn Hap;
  alpha_hyps Hal;
  constructor; auto;
  revert Hal Hap; apply respects_alpha_ex_closed_comput; auto.
Qed.
Hint Resolve respects_alpha_ex_sqlen : respects.

Definition respects_renaming {o} (R : bin_rel (@NTerm o)) :=
  forall t1 t2 l1 l2,
    R t1 t2
    -> R (lsubst t1 (var_ren l1 l2)) (lsubst t2 (var_ren l1 l2)).

Lemma blift_trans {o} :
  forall R (b1 b2 b3 : @BTerm o),
    trans_rel R
    -> respects_alpha R
    -> respects_renaming R
    -> blift R b1 b2
    -> blift R b2 b3
    -> blift R b1 b3.
Proof.
  introv tr ra rr h1 h2.
  unfold blift in *; exrepnd.

  pose proof (fresh_vars
                (length lv0)
                (all_vars nt0 ++ all_vars nt3 ++ all_vars nt1 ++ all_vars nt2)) as q.
  exrepnd.
  apply disjoint_app_r in q2; destruct q2 as [disj1 disj2].
  apply disjoint_app_r in disj2; destruct disj2 as [disj2 disj3].
  apply disjoint_app_r in disj3; destruct disj3 as [disj3 disj4].

  eapply alpha_eq_bterm_trans in h3;[|apply alpha_eq_bterm_sym; exact h4].
  applydup @alpha_eq_bterm_lenbvars in h3.

  pose proof (alpha_bterm_change b1 lv0 nt0 lvn) as z1.
  repeat (autodimp z1 hyp); eauto 2 with slow.

  pose proof (alpha_bterm_change b3 lv nt2 lvn) as z2.
  repeat (autodimp z2 hyp); eauto 2 with slow; try lia.

  exists lvn (lsubst nt0 (var_ren lv0 lvn)) (lsubst nt2 (var_ren lv lvn)).
  dands; auto.

  pose proof (alphabt_change_var nt3 nt1 lv0 lv lvn) as w.
  repeat (autodimp w hyp); try (complete (apply disjoint_app_r; dands; auto)).
  repnd.

  apply (rr _ _ lv0 lvn) in h1.
  apply (rr _ _ lv lvn) in h2.

  eapply tr;[|exact h2].
  eapply ra;[exact w0|]; auto.
Qed.

Lemma lblift_trans {o} :
  forall R (l1 l2 l3 : list (@BTerm o)),
    trans_rel R
    -> respects_alpha R
    -> respects_renaming R
    -> lblift R l1 l2
    -> lblift R l2 l3
    -> lblift R l1 l3.
Proof.
  introv tr ra rr  h1 h2.
  unfold lblift in *; repnd; dands; auto; try lia.
  introv ln.
  applydup h1 in ln.
  rewrite h3 in ln.
  applydup h2 in ln.
  eapply blift_trans;[| | |exact ln0|exact ln1]; auto.
Qed.

Definition respects_computes_to_same_name_l {o} lib (R : bin_rel (@NTerm o)) :=
  forall a b c,
    R a b
    -> computes_to_same_name lib b c
    -> computes_to_same_name lib a c.

Lemma trans_rel_ex_close_comput {o} :
  forall lib ex (R : @NTerm o -> @NTerm o -> [univ]),
  trans_rel R
  -> respects_alpha R
  -> respects_computes_to_same_name_l lib R
  -> trans_rel (ex_close_comput lib ex R).
Proof.
  intros lib ex R Ht Hra respSN a b c Hab Hbc.
  allunfold @ex_close_comput.
  repnd; dands; auto; GC.

  - introv Hcv.
    applydup_clear Hab2 in Hcv. exrepnd.
    rename Hcv0 into Hcb.
    applydup_clear Hbc2 in Hcb. exrepnd.
    exists tr_subterms0; sp.
    revert Hcv1 Hcb1.
    apply trans_lblift; auto; eauto with respects_alpha.

  - introv comp.
    applydup Hab3 in comp; repndors; exrepnd; tcsp.
    applydup @preserve_program_exc2 in comp1; auto; repnd.
    applydup Hbc3 in comp1; repndors; exrepnd; tcsp.

    {
      left.
      eapply respSN; eauto.
    }

    right.
    eexists; eexists; dands;[eauto| |]; eauto 3 with slow.

  - introv comp.
    apply Hab4 in comp; exrepnd.
    apply Hbc4 in comp1; exrepnd.
    eexists; dands; eauto.
Qed.

Definition ex_sqle {o} lib ex (tl tr : @NTerm o) :=
  forall n, ex_sqle_n lib ex n tl tr.

Theorem ex_sqlen_closed {o} :
  forall lib (ex : @NTerm o) n, is_rel_on_progs (ex_sqle_n lib ex n).
Proof.
  induction n as [| n Hind]; intros t1 t2 Hsq;
    invertsn Hsq; auto.
  rename Hsq into Hclose.
  unfold ex_close_comput in Hclose.
  sp; auto.
Qed.

Lemma respects_computes_to_same_name_l_ex_sqle_n {o} :
  forall lib (ex : @NTerm o) n,
    0 < n
    -> respects_computes_to_same_name_l lib (ex_sqle_n lib ex n).
Proof.
  introv lt0n sqle comp h.
  inversion sqle as [|? ? ? ecc]; subst; tcsp.
  unfold ex_close_comput in ecc; repnd.
  apply ecc2 in h; exrepnd.
  unfold lblift in *; simpl in *; repnd; cpx.
Qed.

Lemma ex_approx_ex_sqle {o} :
  forall lib (ex : @NTerm o) a b,
    ex_approx lib ex a b <=> ex_sqle lib ex a b.
Proof.
  intros; sp_iff Case.

  - Case "->"; intro Hap.
    unfold sqle; intro.
    revert a b Hap.
    induction n; constructor; invertsn Hap; unfold ex_close_comput in Hap; sp.
    unfold ex_close_comput. dands; auto.

    + introv Hcv.
      applydup Hap2 in Hcv. exrepnd.
      exists tr_subterms; sp.
      apply ex_clearbot_relbt in Hcv1.
      unfold lblift in Hcv1; exrepnd.
      split; auto. introv Hlt.
      apply Hcv1 in Hlt.
      eapply le_blift_olift; eauto.

    + introv comp.
      apply Hap3 in comp.
      repndors; tcsp.
      exrepnd.
      repndors; try (complete (unfold bot2 in *; tcsp)).
      right; eexists; eexists; dands;[eauto| |]; auto.

    + introv comp.
      apply Hap4 in comp; exrepnd.
      eexists; dands; eauto.
      introv.
      apply IHn; auto.
      pose proof (comp0 n0) as h; repndors; tcsp.
      unfold bot2 in h; tcsp.

  - Case "<-"; introv Hsq.
    revert a b Hsq.
    apply (ex_approx_acc).
    introv  Hb Hs.
    intros a b Hsq.
    constructor.
    repnud Hsq.
    pose proof (Hsq 2) as H1s.
    applydup @ex_sqlen_closed in H1s.
    repnd.
    split; auto.
    dands; auto.

    + introv Hcv.
      invertsn H1s.
      repnud H1s. duplicate Hcv as Hcvb.
      apply H1s4 in Hcv.
      exrepnd.
      exists tr_subterms.
      dands;auto.
      apply (le_lblift (olift (ex_sqle lib ex))).
      * apply le_olift. introv Hss. right. eauto.
      * repnud Hcv0.  clear H1s. unfolds_base. dands; auto.
        introv Hpt. unfolds_base. duplicate Hpt as Hptb. apply Hcv0 in Hpt.
        repnud Hpt. parallel lv Hpt. parallel  nt1 Hpt .
        parallel  nt2 Hpt. exrepnd.
        dands;sp. repnud Hpt0.
        split; auto. split;auto.
        introv Hwf H1p H2p.
        unfolds_base. intro nn.
        pose proof (Hsq (S nn)) as Hnn.
        invertsn Hnn.
        repnud Hnn.
        apply Hnn2 in Hcvb.
        exrepnd.
        eapply computes_to_value_eq in Hcv1; eauto.
        invertsn Hcv1.
        clear Hnn Hcv0.
        repnud Hcvb0.
        apply Hcvb0 in Hptb.
        apply (blift_alpha_fun_r _ _ _ _ Hptb) in Hpt.
        apply (blift_alpha_fun_l _ _ _ _ Hpt) in Hpt1.
        clear Hpt Hptb Hcvb0 Hcvb1.
        apply blift_selen_triv in Hpt1; eauto 1 with respects.
        apply Hpt1; auto.

    + introv ce.
      invertsn H1s.
      repnud H1s.
      applydup H1s5 in ce.
      repndors; exrepnd; tcsp.

      right.
      eexists; eexists; dands;[eauto| |].

      {
        assert (ex_sqle lib ex a0 a'); [|complete auto].
        intro n.
        generalize (Hsq (S n)); intro k.

        invertsn k; auto.
        repnud k.
        apply k3 in ce; repndors; exrepnd;
          [|eapply computes_to_exception_eq in ce3; eauto; repnd; subst; auto].
      }

    + introv comp.
      invertsn H1s.
      repnud H1s.
      applydup H1s6 in comp; exrepnd.
      eexists; dands; eauto.

      introv.
      right; apply Hs.
      intro k.
      pose proof (Hsq (S k)) as h.
      invertsn h.
      repnud h.
      apply h4 in comp; exrepnd.
      eapply reduces_to_eq_val_like in comp3;
        try (exact comp0); eauto 3 with slow; ginv; auto.
Qed.

Lemma ex_sqlen_n_trans {o} :
  forall lib (ex : @NTerm o) n, trans_rel (ex_sqle_n lib ex n).
Proof.
  induction n; intros a b c Hab Hbc;
    invertsn Hab; invertsn Hbc; constructor; auto;[].
  eapply trans_rel_ex_close_comput;[| | |eauto|eauto]; eauto 3 with slow.
  { apply respects_alpha_ex_sqlen. }

Qed.

Lemma trans_rel_olift_ex_sqlen {o} :
  forall lib (ex: @NTerm o) n,
    trans_rel (lblift (olift (ex_sqle_n lib ex n))).
Proof.
  intros.
  apply trans_lblift; eauto with respects;[].
  apply ex_sqlen_n_trans.
Qed.



Definition ex_sq_closure {o} lib ex :=
  fun (R : @NTerm o -> @NTerm o -> [univ]) =>
    is_rel_on_progs R
    # le_bin_rel R (ex_close_comput lib ex R).

Theorem ex_sqle_ge_postfixpoint {o} :
  forall lib (ex : @NTerm o),
    is_ge_any_rel_sat
      (ex_sqle lib ex)
      (ex_sq_closure lib ex).
Proof.
  unfold is_ge_any_rel_sat, le_bin_rel, ex_sq_closure.
  intros lib ex Rp Hsat a b Hrp n.
  gen a b.
  repnd.
  induction n; intros a b Hrp; constructor;
    try (apply Hsat0 in Hrp; sp; auto; fail).
  apply Hsat in Hrp. clear Hsat.
  allunfold @ex_close_comput; repnd.
  repeat(split;auto).

  - intros c tl_subterms Hcv.
    apply Hrp2 in Hcv. exrepnd.
    exists tr_subterms. sp; auto.
    clear Hcv1.
    gen tl_subterms tr_subterms.
    fold (@le_bin_rel  NTerm Rp (sqle_n lib n)) in IHn.
    fold (@le_bin_rel (list BTerm ) (lblift Rp) (lblift (sqle_n lib n)) ) .
    apply le_lblift. apply le_olift in IHn.
    auto.

  - introv comp.
    apply Hrp4 in comp; exrepnd.
    eexists; dands; eauto.
Qed.

Theorem ex_close_comput_mono {o} :
  forall lib (ex : @NTerm o) R1 R2,
    (le_bin_rel R1 R2)
    -> le_bin_rel (ex_close_comput lib ex R1) (ex_close_comput lib ex R2).
Proof.
  intros ? ? ? ? Hle.
  intros ? ? Hcr1.
  allunfold @ex_close_comput. repnd.
  repeat(split;auto).

  - intros ? ? Hcomp.
    apply Hcr3 in Hcomp. parallel tr_subterms Hrelbt.
    repnd. split;auto. allunfold @lblift.
    exrepnd.
    dands;sp.
    eapply le_blift_olift; eauto.

  - introv comp.
    apply Hcr5 in comp; exrepnd.
    eexists; dands; eauto.
Qed.
