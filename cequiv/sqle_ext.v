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


Require Export approx_ext.
Require Export computation4.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)

(** For a deterministic computation system, [approx] is
    equivalent to [sqle].
    Since [sqle] is defined by induction on natural numbers,
    the proofs about approx that would otherwise need
    coinduction can be done more conveniently by
    induction on natural numbers.

 *)

Inductive sqle_ext_n {o} (lib : @library o) :  nat -> @NTerm o -> @NTerm o -> [univ] :=
| sql_ext0 :
    forall tl tr,
      isprogram tl
      -> isprogram tr
      -> sqle_ext_n lib 0 tl tr
 | sql_ext_add1 :
     forall n tl tr,
       close_compute_ext lib (sqle_ext_n lib n) tl tr
       -> sqle_ext_n lib (S n) tl tr.
Hint Constructors sqle_ext_n.

(* begin hide *)


(* does not even need induction *)
Lemma respects_alpha_sqle_ext_n {o} :
  forall lib n,
    respects_alpha (@sqle_ext_n o lib n).
Proof.
  induction n; split; introv Hal Hap;
    invertsn Hap;
    alpha_hyps Hal;
    constructor; auto;
      revert Hal Hap; apply respects_alpha_close_compute_ext; auto.
Qed.

Hint Resolve respects_alpha_sqle_ext_n : respects.
Hint Resolve alpha_eq_bterm_trans alpha_eq_bterm_sym: alphaeqbt.

Lemma trans_blift {o} : forall (R : @NTerm o -> @NTerm o -> [univ]),
  trans_rel R
  -> respects_alpha R
  -> trans_rel (blift (olift R)).
Proof.
  intros R Ht Hra a b c Hab Hbc.
  destruct a as [lva nta].
  destruct b as [lvb ntb].
  destruct c as [lvc ntc].
  allunfold @blift; exrepnd; try omega.
  pose proof (fresh_vars (length lv) (all_vars nt1 
      ++ all_vars nt2 ++ all_vars nt0 ++ all_vars nt3)) as Hfr.
  exrepnd.
  dimp (alpha_bterm_pair_change2 _ _ _ _ _ lvn Hbc0 Hbc2); 
    try(rename hyp into H1c); exrepnd; spc; [| disjoint_reasoningv].
  assert (alpha_eq_bterm (bterm lv nt1) (bterm lv0 nt3)) as Hbt by (eauto with slow).
  (** transitivity of alpha_eq_bterm*)
  apply alphaeqbt_numbvars in Hbt.
  allunfold @num_bvars.
  allsimpl.
  dimp (alpha_bterm_pair_change2 _ _ _ _ _ lvn Hab0 Hab2); try(rename hyp into H2c);
    exrepnd;spc;[| disjoint_reasoningv;fail].
  exists lvn.
  exists (lsubst nt2n0 (var_ren lv0 lvn)).
  exists (lsubst nt1n (var_ren lv lvn)).
  dands; spc;[].
  assert (alpha_eq_bterm 
    (bterm lvn (lsubst nt1n0 (var_ren lv0 lvn)))
    (bterm lvn (lsubst nt2n (var_ren lv lvn)))
  ) as Hlink by (eauto with alphaeqbt).
  apply alpha_eq_bterm_triv in Hlink.
  (repeat match goal with 
   | [ H : alpha_eq_bterm _ _ |- _ ] => thin H
   end).
 
  rwhg H2c0 Hab1.
  rwhg H2c2 Hab1.

  rwhg H1c0 Hbc1.
  rwhg H1c2 Hbc1.

  rename Hbc1 into H1ap.
  rename Hab1 into H2ap.

  clear H1c0 H1c2 H2c0 H2c2.
  
  apply olift_vars_lsubst with (lvi:=lv) (lvo:=lvn) in H1ap; auto.
  apply olift_vars_lsubst with (lvi:=lv0) (lvo:=lvn) in H2ap; auto.
  rwhg Hlink H2ap.
  apply olift_trans in Ht; auto.
  repnud Ht. eauto.
Qed.

Lemma trans_lblift {o} : forall (R : @NTerm o -> @NTerm o -> [univ]),
  trans_rel R
  -> respects_alpha R
  -> trans_rel (lblift (olift R)).
Proof.
  intros R Ht Hra a b c Hab Hbc.
  allunfold @lblift.
  repnd. dands; try congruence; eauto.
  intros n Hlt.
  dimp (Hbc n); try congruence.
  dimp (Hab n); try congruence.
  revert hyp0 hyp. apply trans_blift; auto.
Qed.




Lemma trans_rel_close_compute_ext {o} :
  forall lib (R : @NTerm o -> @NTerm o -> [univ]),
  trans_rel R
  -> respects_alpha R
  -> trans_rel (close_compute_ext lib R).
Proof.
  intros lib R Ht Hra a b c Hab Hbc.
  allunfold @close_compute_ext.
  repnd; dands; auto.

  - introv Hcv.
    applydup_clear Hab2 in Hcv. exrepnd.
    rename Hcv0 into Hcb.
    applydup_clear Hbc2 in Hcb. exrepnd.
    exists tr_subterms0; sp.
    revert Hcv1 Hcb1.
    apply trans_lblift; auto; eauto with respects_alpha.

  - introv Hcv.
    applydup_clear Hab3 in Hcv. exrepnd.
    rename Hcv1 into Hcb.
    applydup_clear Hbc3 in Hcb. exrepnd.
    exists a'0 e'0; sp.
    + revert Hcv2 Hcb2.
      apply Ht.
    + revert Hcv0 Hcb0.
      apply Ht.

(*
  - introv Hcv.
    applydup_clear Hab in Hcv. exrepnd.
    rename Hcv0 into Hcb.
    applydup_clear Hbc in Hcb.
    exrepnd; auto.
*)

  - introv comp.
    apply Hab4 in comp; exrepnd.
    apply Hbc4 in comp1; exrepnd.
    eexists; dands; eauto.
Qed.

Lemma sqle_ext_n_trans {o} : forall lib n, trans_rel (@sqle_ext_n o lib n).
Proof.
  induction n; intros a b c Hab Hbc;
  invertsn Hab; invertsn Hbc; constructor; auto;[].
  revert Hab Hbc.
  apply trans_rel_close_compute_ext; eauto with respects.
Qed.

Lemma trans_rel_olift_sqle_ext_n {o} : forall lib n,
  trans_rel (lblift (olift (@sqle_ext_n o lib n))).
Proof.
  intros. apply trans_lblift; eauto with respects;[].
  apply sqle_ext_n_trans.
Qed.



Theorem sqle_ext_n_closed {o} : forall lib n, is_rel_on_progs (@sqle_ext_n o lib n).
Proof. induction n as [| n Hind]; intros t1 t2 Hsq;
 invertsn Hsq; auto.
 rename Hsq into Hclose.
 unfold close_compute_ext in Hclose.
 sp; auto.
Qed.

(* end hide *)
(* This is Howe's specialized definition that works
 only for a deterministic computaion system*)
Definition sqle_ext {o} lib (tl tr : @NTerm o) :=
  forall n, sqle_ext_n lib n tl tr.
(* begin hide *)

Definition sq_ext_closure {o} lib :=
  fun (R : @NTerm o -> @NTerm o -> [univ]) =>
    is_rel_on_progs R
    # le_bin_rel R (close_compute_ext lib R).

Theorem sqle_ext_ge_postfixpoint {o} :
  forall lib,
  is_ge_any_rel_sat
    (sqle_ext lib)
    (@sq_ext_closure o lib).
Proof.
  unfold is_ge_any_rel_sat, le_bin_rel, sq_ext_closure. auto. intros lib Rp Hsat a b Hrp n.
  gen a b. repnd.
  induction n; intros a b Hrp; constructor;
  try (apply Hsat0 in Hrp; sp; auto; fail).
  apply Hsat in Hrp. clear Hsat.
  allunfold @close_compute_ext; repnd.
  repeat(split;auto).

  - intros c tl_subterms bar Hcv.
    apply Hrp2 in Hcv; exrepnd.
    exists tr_subterms; dands; tcsp.
    clear Hcv1.
    gen tl_subterms tr_subterms.
    fold (@le_bin_rel  NTerm Rp (sqle_ext_n lib n)) in IHn.
    fold (@le_bin_rel (list BTerm ) (lblift Rp) (lblift (sqle_ext_n lib n)) ) .
    apply le_lblift. apply le_olift in IHn.
    auto.

  - introv ce.
    apply Hrp3 in ce; exrepnd.
    exists a' e'; auto.

  - introv comp.
    apply Hrp4 in comp; exrepnd.
    eexists; dands; eauto.
Qed.

(*
Theorem sqle_closed : is_rel_on_progs sqle.
Proof.
  unfold is_rel_on_progs.  intros.
  allunfold sqle.
  apply sqle_ext_n_closed with 0; auto.
Qed.

Theorem sqle_closure :  sq_ext_closure sqle.
Proof.
 split; try apply sqle_closed.
 unfold le_bin_rel. intros a b Hsqle.
 duplicate Hsqle.
 apply sqle_closed in Hsqle0 as [Hproga  Hprogb].
 unfold close_comput. repnd.
 repeat(split; trivial).
 clear Hproga Hprogb.
 intros ? ? Hcv.
 unfold sqle_ext in Hsqle.
 assert (sqle_ext_n 1 a b ) as Hsqle1 by auto.
 inverts Hsqle1 as Hclose.
 duplicate Hcv.
 apply Hclose in Hcv0.
 parallel tr_subterms Hcrel.
 repnd ; sp; auto.
 rename Hcrel0 into Hcvb.
 clear Hcrel Hclose.
 unfold lblift, blift.
 applydup computes_to_value_wf2 in Hcv.
 applydup computes_to_value_wf2 in Hcvb.
 assert (length tl_subterms = length tr_subterms) by omega.
 split; trivial.
 clear Hcv0 Hcvb0.
  unfold sqle.
  intros.
  split.
  apply computes_to_value_wf3 with (n:=n) in Hcv; auto.
  apply computes_to_value_wf3 with (n:=n) in Hcvb; omega.
  intros lnt ? Hin m.
  assert (sqle_ext_n (S m) a b) as HsqleSm by auto.
  inverts HsqleSm as Hclose.
  duplicate Hcv.
  apply Hclose in Hcv0. exrepnd.
  assert ((oterm (Can c) tr_subterms)=(oterm (Can c) tr_subterms0))
    as Heqtr by (apply computes_to_value_eq with b; auto).
  inverts Heqtr.
  unfold lblift, blift in Hcv1. apply Hcv1; auto.
Qed.

Theorem sqle_greatest_postfixpoint: is_greatest_rel_sat 
                                   sqle
                                   sq_ext_closure.
Proof. unfold is_greatest_rel_sat. 
 split. 
  apply sqle_closure.
  apply sqle_ge_postfixpoint.
Qed.
*)


Theorem close_compute_ext_mono {o}: forall lib R1 R2, (le_bin_rel R1 R2)
  -> le_bin_rel (@close_compute_ext o lib R1) (close_compute_ext lib R2).
Proof.
  intros ? ? ? Hle. intros ? ? Hcr1.
  allunfold @close_compute_ext. repnd.
  repeat(split;auto).

  - intros ? ? ? Hcomp.
    apply Hcr3 in Hcomp. parallel tr_subterms Hrelbt.
    repnd. split;auto. allunfold @lblift.
    exrepnd.
    dands;sp.
    eapply le_blift_olift; eauto.

  - introv ce.
    apply Hcr4 in ce; exrepnd.
    exists a' e'; auto.

  - introv comp.
    apply Hcr5 in comp; exrepnd.
    eexists; dands; eauto.
Qed.

Definition nt_id_prog {o} :=
  fun x y : @NTerm o => isprogram x # isprogram y # x = y.

(*
Theorem  sqle_suff: le_bin_rel (close_comput sqle) (sqle).
Proof.
  apply sqle_ge_postfixpoint.
  split.
   unfold is_rel_on_progs. intros ? ? Hcomp. inverts Hcomp; sp; auto.
   unfold le_bin_rel.
   intros ? ? Hcomp.
   assert(le_bin_rel sqle_ext (close_comput sqle)) by apply sqle_closure.
   apply close_comput_mono in H.
   apply H; auto.
Qed.
(** this lemma should be all we need in most proofs about squiggle*)
Theorem  sqle_suff_necc: eq_bin_rel (close_comput sqle) (sqle).
Proof.
  intros. split.
   apply sqle_suff.
   apply sqle_closure.
Qed.


Theorem id_sq_ext_closure: sq_ext_closure nt_id_prog.
Proof.
 unfold nt_id_prog, sq_ext_closure, is_rel_on_progs, le_bin_rel.
 split; try(sp; intros; auto; fail).
 intros a b Hprogs. repnd.
 unfold close_comput.
 repeat(split;auto).
 intros ? ? Hcomp.
 rewrite  <- Hprogs.
 exists tl_subterms.
 (split;auto).
 unfold lblift, blift.
 split; auto.
 intros ? Hlt.
 split; auto.
 intros ? Hinprog Hlen.
 assert(isprogram (apply_bterm (selectbt tl_subterms n) lnt));
 sp;auto.
 apply preserve_program in Hcomp;auto.
 rewrite isprogram_ot_iff in Hcomp. repnd.
 instlemma (Hcomp (selectbt tl_subterms n)) as Hprogsel.
 assert (In (selectbt tl_subterms n) tl_subterms)
  as Htemp23   by (apply selectbt_in; auto).
 clear Hprogsel.
 assert (isprogram_bt (selectbt tl_subterms n)) as Hprogsel; auto.
 clear Htemp23.
 apply isprogram_bt_implies ; auto.
Qed.

Theorem id_le_sqle: le_bin_rel nt_id_prog sqle.
Proof.
 apply sqle_ge_postfixpoint.
 apply id_sq_ext_closure.
Qed.

Theorem sqle_id : forall (t1: NTerm) , (isprogram t1) -> (sqle_ext t1 t1).
Proof.
intros. apply id_le_sqle. unfold nt_id_prog.
sp;auto.
Qed.
*)

(* end hide *)


Lemma computes_to_value_bar_alpha {o} :
  forall {lib} (bar : NeBarLib lib) (t v1 v2 : @NTerm o),
    t =b=v>(bar) v1
    -> t =b=v>(bar) v2
    -> alpha_eq v1 v2.
Proof.
  introv comp1 comp2.
  apply computes_to_value_bar_implies_computes_to_value_alpha in comp1.
  exrepnd.
  pose proof (comp2 lib') as comp2; autodimp comp2 hyp.
  pose proof (comp2 lib') as comp2; autodimp comp2 hyp; eauto 2 with slow; simpl in comp2.
  unfold computes_to_value_alpha in *; exrepnd.
  eapply computes_to_value_eq in comp1;[|exact comp2]; subst.
  eauto 3 with slow.
Qed.

Lemma computes_to_exception_bar_alpha {o} :
  forall {lib} (bar : NeBarLib lib) (t a b c d : @NTerm o),
    t =b=e>(a,bar) b
    -> t =b=e>(c,bar) d
    -> alpha_eq a c # alpha_eq b d.
Proof.
  introv comp1 comp2.
  apply computes_to_exception_bar_implies_computes_to_exception_alpha in comp1.
  exrepnd.
  pose proof (comp2 lib') as comp2; autodimp comp2 hyp.
  pose proof (comp2 lib') as comp2; autodimp comp2 hyp; eauto 2 with slow; simpl in comp2.
  unfold computes_to_exception_alpha in *; exrepnd.
  eapply computes_to_exception_eq in comp3;[|exact comp5]; repnd; subst; dands; eauto 3 with slow.
Qed.

Lemma computes_to_seq_bar_alpha {o} :
  forall {lib} (bar : NeBarLib lib) (t : @NTerm o) f g,
    t =b=s>(bar) f
    -> t =b=s>(bar) g
    -> (forall n, alpha_eq (f n) (g n)).
Proof.
  introv comp1 comp2.
  apply computes_to_seq_bar_implies_computes_to_seq_alpha in comp1.
  exrepnd.
  pose proof (comp2 lib') as comp2; autodimp comp2 hyp.
  pose proof (comp2 lib') as comp2; autodimp comp2 hyp; eauto 2 with slow; simpl in comp2.
  unfold computes_to_seq_alpha in *; exrepnd.
  eapply reduces_to_eq_val_like in comp1;[|exact comp2| |]; eauto 2 with slow; ginv.
  introv; eauto 3 with slow.
Qed.

Lemma approx_ext_sqle_ext {o} :
  forall lib a b,
    @approx_ext o lib a b <=> sqle_ext lib a b.
Proof.
  intros; sp_iff Case.

  - Case "->"; intro Hap.
    unfold sqle_ext; intro.
    revert a b Hap.
    induction n; constructor; invertsn Hap; unfold close_compute_ext in Hap; sp.
    unfold close_compute_ext. dands; auto.

    + introv Hcv.
      applydup Hap2 in Hcv. exrepnd.
      exists tr_subterms; sp.
      apply clearbot_relbt in Hcv1.
      unfold lblift in Hcv1; exrepnd.
      split; auto. introv Hlt.
      apply Hcv1 in Hlt.
      eapply le_blift_olift; eauto.

    + introv ce.
      applydup Hap3 in ce; exrepnd.
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
    apply (approx_ext_acc).
    introv  Hb Hs. intros a b Hsq.
    constructor. repnud Hsq. pose proof (Hsq 1) as H1s.
    applydup @sqle_ext_n_closed in H1s. repnd.
    split; auto.
    dands; auto.

    + introv Hcv.
      invertsn H1s.
      repnud H1s.
      duplicate Hcv as Hcvb.
      apply H1s4 in Hcv.
      exrepnd.
      exists tr_subterms.
      dands;auto.
      apply (le_lblift (olift (sqle_ext lib))).

      * apply le_olift. introv Hss. right. eauto.

      * repnud Hcv0.
        clear H1s. unfolds_base. dands; auto.
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

        eapply computes_to_value_bar_alpha in Hcv1; try (exact Hcvb1).
        apply alpha_eq_oterm_combine in Hcv1; repnd.

        repnud Hcvb0.
        applydup Hcvb0 in Hptb.

        pose proof (Hcv1 (tr_subterms0 {[n]}) (tr_subterms {[n]})) as w.
        autodimp w hyp;[apply in_nth_combine; auto; try omega|];[].

        eapply blift_alpha_fun_r in w;[|eauto];[].
        eapply blift_alpha_fun_r in w;[|eauto];[].
        eapply blift_alpha_fun_l in w;[|eauto];[].

        apply blift_selen_triv in w; eauto 1 with respects.
        apply w; auto.

    + introv ce.
      invertsn H1s.
      repnud H1s.
      applydup H1s5 in ce; exrepnd.
      exists a' e'; sp.

      {
        assert (sqle_ext lib a0 a'); [|complete auto].
        intro n.
        generalize (Hsq (S n)); intro k.

        invertsn k; auto.
        repnud k.
        apply k3 in ce; exrepnd.
        eapply computes_to_exception_bar_alpha in ce3; eauto; repnd; subst; auto.
        eapply respects_alpha_sqle_ext_n;[apply alpha_eq_sym;eauto|];auto.
      }

      {
        assert (sqle_ext lib e e'); [|complete auto].
        intro n.
        generalize (Hsq (S n)); intro k.

        invertsn k; auto.
        repnud k.
        apply k3 in ce; exrepnd.
        eapply computes_to_exception_bar_alpha in ce3; eauto; repnd; subst; auto.
        eapply respects_alpha_sqle_ext_n;[apply alpha_eq_sym;eauto|];auto.
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
      eapply computes_to_seq_bar_alpha in comp3;[|exact comp0].
      eapply respects_alpha_sqle_ext_n;[apply alpha_eq_sym;eauto|];auto.
Qed.
(* begin hide *)
