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


Require Export sqle.
Require Export eapprox.

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

Lemma trans_rel_ex_close_comput {o} :
  forall lib ex (R : @NTerm o -> @NTerm o -> [univ]),
  trans_rel R
  -> respects_alpha R
  -> trans_rel (ex_close_comput lib ex R).
Proof.
  intros lib ex R Ht Hra a b c Hab Hbc.
  allunfold @ex_close_comput.
  repnd; dands; auto; GC.

  - introv Hcv.
    applydup_clear Hab2 in Hcv. exrepnd.
    rename Hcv0 into Hcb.
    applydup_clear Hbc2 in Hcb. exrepnd.
    exists tr_subterms0; sp.
    revert Hcv1 Hcb1.
    apply trans_lblift; auto; eauto with respects_alpha.

  - introv Hcv.
    applydup_clear Hab3 in Hcv.
    repndors; exrepnd; tcsp.
    rename Hcv1 into Hcb.
    applydup_clear Hbc3 in Hcb.
    repndors; exrepnd; tcsp.

    { left.
      eapply Ht; eauto. }

    right.
    exists a'0 e'0; sp.
    + revert Hcv2 Hcb2.
      apply Ht.
    + revert Hcv0 Hcb0.
      apply Ht.

  - introv comp.
    apply Hab4 in comp; exrepnd.
    apply Hbc4 in comp1; exrepnd.
    eexists; dands; eauto.
Qed.

Lemma ex_sqlen_n_trans {o} :
  forall lib (ex : @NTerm o) n, trans_rel (ex_sqle_n lib ex n).
Proof.
  induction n; intros a b c Hab Hbc;
  invertsn Hab; invertsn Hbc; constructor; auto;[].
  revert Hab Hbc.
  apply trans_rel_ex_close_comput; eauto with respects.
Qed.

Lemma trans_rel_olift_ex_sqlen {o} :
  forall lib (ex: @NTerm o) n,
    trans_rel (lblift (olift (ex_sqle_n lib ex n))).
Proof.
  intros.
  apply trans_lblift; eauto with respects;[].
  apply ex_sqlen_n_trans.
Qed.



Theorem ex_sqlen_closed {o} :
  forall lib (ex : @NTerm o) n, is_rel_on_progs (ex_sqle_n lib ex n).
Proof.
  induction n as [| n Hind]; intros t1 t2 Hsq;
    invertsn Hsq; auto.
  rename Hsq into Hclose.
  unfold ex_close_comput in Hclose.
  sp; auto.
Qed.

Definition ex_sqle {o} lib ex (tl tr : @NTerm o) :=
  forall n, ex_sqle_n lib ex n tl tr.

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

  - introv ce.
    apply Hrp3 in ce; repndors; exrepnd; tcsp.
    right.
    exists a' e'; auto.

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

  - introv ce.
    apply Hcr4 in ce; repndors; exrepnd; tcsp.
    right.
    exists a' e'; auto.

  - introv comp.
    apply Hcr5 in comp; exrepnd.
    eexists; dands; eauto.
Qed.

Lemma approx_ex_sqle {o} :
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

    + introv ce.
      applydup Hap3 in ce; repndors; exrepnd; tcsp.

      { inversion ce0. }

      right.
      exists a' e'; sp; inversion b0.

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
    introv  Hb Hs. intros a b Hsq.
    constructor. repnud Hsq. pose proof (Hsq 1) as H1s.
    applydup @ex_sqlen_closed in H1s. repnd.
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

      {
        (* WARNING: how can we ever hope to prove this? *)
        left.
        apply Hs; auto.
      }

      exists a' e'; sp.

      {
        assert (sqle lib a0 a'); [|complete auto].
        intro n.
        generalize (Hsq (S n)); intro k.

        invertsn k; auto.
        repnud k.
        apply k3 in ce; exrepnd.
        eapply computes_to_exception_eq in ce3; eauto; repnd; subst; auto.
      }

      {
        assert (sqle lib e e'); [|complete auto].
        intro n.
        generalize (Hsq (S n)); intro k.

        invertsn k; auto.
        repnud k.
        apply k3 in ce; exrepnd.
        eapply computes_to_exception_eq in ce3; eauto; repnd; subst; auto.
      }

(*
    + introv ce.
      invertsn H1s.
      repnud H1s.
      applydup H1s in ce; exrepnd; auto.
*)

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
