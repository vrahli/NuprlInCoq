(*

  Copyright 2014 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Import rules_useful.
Require Export rules_partial.


(** This section is a work in progress. We plan to prove the
  rules that characterize the class of Mono types, i.e. types T such
  that the type [mkc_mono T] is inhabited. Crary proved monohood
  of many types (see %\cite[Sec. 5.3.2]{Crary:1998}%).
  Here is what we have proved so far:

  The class of Mono types include :
  - mkc_int (see [rule_mono_int] below)

  Monohood is closed under the following type constructors.
  - mkc_function (see [rule_mono_function] below)
  - mkc_product (see [rule_mono_product] below)

  We will keep updating this list as we prove more rules.
*)


(**
<<
   H |- Mono Z

     By int_mono
     no subgoals
>>
 *)
Definition rule_mono_int {o}
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_mono mk_int) ))
    []
    [].


Lemma rule_mono_int_true {o} : forall lib (H : @barehypotheses o),
  rule_true lib (rule_mono_int H).
Proof.
  unfold rule_mono_int, rule_true, closed_type_baresequent, closed_extract_baresequent. simpl.
  intros.
  clear cargs.
  destseq; allsimpl.
  dLin_hyp.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  allrw @lsubstc_mk_int.
  dands;[ apply tequality_mono; apply tequality_int |].
  apply equality_in_mkc_mono.
  exists (@equality_of_int o lib).
  dands; eauto with nequality;
  try(spcast;apply computes_to_valc_refl; eauto 3 with slow);
  [apply equality_of_int_xxx; fail|].
  introv Heq Hap.
  allunfold @equality_of_int.
  exrepnd. GC.
  exists k.
  dands; auto.
  spcast.
  clear pC2 pC1 cg wfct wfh sim eqh H.
  allunfold @computes_to_valc.
  allunfold @approxc.
  dest_ctermsn.
  allsimpl.
  repnud Hap.
  invertsn Hap.
  apply Hap in Heq1.
  exrepnd.
  match goal with
  [H : lblift _ _ ?bterms'  |- _ ] => unfold lblift in H; simpl in H;
    let Hlen := fresh H "len" in
      destruct H as [Hlen H];   dlist_len_name bterms' bt
  end;
  dforall_lt_hyp Hbt; auto.
Qed.
(**
<<
   H |- Mono ((x:A) -> B)

     By function_mono
     H |- Mono A
     H, x:A |- Mono B
>>
 *)
Definition rule_mono_function {o}
           (A B : @NTerm o)
           (x : NVar)
           (H : barehypotheses) :=
  mk_rule
    (mk_baresequent H (mk_conclax 
        (mk_mono (mk_function A x B)) ))
    [   (mk_baresequent H (mk_conclax  (mk_mono A) )), (* probably not necessary *)
        (mk_baresequent (snoc H (mk_hyp x A)) (mk_conclax (mk_mono B)))
    ]
    [].


Ltac abbrev_ls t s :=
let ts:= fresh t s in
match goal with
[H: context [lsubstc t ?w s ?c] |- _ ] =>
  remember (lsubstc t w s c) as ts
end.

Ltac abbrev_lsc t s :=
let ts:= fresh t s in
match goal with
[H: context [(lsubstc_vars t ?w (csub_filter s [?v1]) [?v2] ?c)] |- _ ] =>
  remember ((lsubstc_vars t w (csub_filter s [v1]) [v2] c)) as ts
end.

Lemma approxc_mkc_apply_congr {o} :
  forall lib (f g a b : @CTerm o),
    approxc lib f g
    -> approxc lib a b
    -> approxc lib (mkc_apply f a) (mkc_apply g b).
Proof.
  intros. dest_ctermsn.
  allunfold @approxc.
  allsimpl.
  apply implies_approx_apply; auto.
Qed.
Hint Resolve approxc_refl : slow.

Lemma rule_mono_function_true {o} :
  forall lib (H : @barehypotheses o)
         (A B : NTerm)
         (x: NVar),
    rule_true lib (rule_mono_function A B x H).
Proof.
  unfold rule_mono_function, rule_true, closed_type_baresequent,
       closed_extract_baresequent. simpl.
  intros.
  clear cargs.
  destseq; allsimpl.
  dLin_hyp.
  (* We prove the well-formedness of things *)
  destruct Hyp as [ wsa Hypa ].
  destruct Hyp0 as [ wsb Hypb ].
  destseq; allsimpl; proof_irr; GC.
  dup wfh0 as h; apply vswf_hypotheses_eq in h.
  inversion h as [XX |  Hsn HsH H2h H3h H4h H5h]; cpx; allsimpl.
  rename H4h into Hin.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  applydup @similarity_dom in sim. repnd.
  vr_seq_true in Hypa.
  generalize (Hypa s1 s2 eqh sim). rename Hypa into Hypab. intro Hypa. exrepnd.
  lsubst_tac. rw @tequality_mono in Hypa0.
  vr_seq_true in Hypb.
  match goal with
  [|- (tequality ?lib (mkc_mono ?A) (mkc_mono ?B))# _] =>
  assert (tequality lib A B) as Hteq
  end.
  - apply tequality_function.
    dands; auto;[]. introv Heq.
    specialize (Hypb (snoc s1 (x,a)) (snoc s2 (x,a'))). 
    (* why not cons? see defn of similarity *)
    autodimp Hypb Hypb';[ |autodimp Hypb Hypb'].
    + (* hyps_functionality *) 
      intros s3 sim2. inversion sim2; cpx; allsimpl; cpx.
      rw @eq_hyps_snoc; simpl.
      assert (cover_vars A s4) as cv4
          by (apply (similarity_cover_vars lib) with (hs := H) (s1 := s1); auto).
      exists s1 s4 a t2 w p cv4; sp.
      (* while proving that functionality result, we have to prove that
       * a1 is functional, which we prove using our 1st hyp *)
      specialize (Hypab s1 s4);
      autodimp Hypab hyp1';
      autodimp Hypab hyp1'; exrepnd; clear_irr.
      lsubst_tac.
      apply tequality_mono; auto.
    + (* similarity *)
      rw @similarity_snoc; simpl.
      exists s1 s2 a a' w0 c2; sp;
      complete (allapply similarity_refl; sp).
    + exrepnd.
      lsubst_tac.
      rw @tequality_mono in Hypb0.
      rewrite <- simple_substc2 with (c:=c6);
      [|rw sim1; auto; fail].
      rewrite <- simple_substc2 with (c:=c7);
      [|rw sim0; auto; fail]. trivial.
  - split;[apply tequality_mono; auto; fail |].
    apply equality_in_mkc_mono.
    applydup @tequality_refl in Hteq.
    repnud Hteq0. exrepnd.
    rename eq into eqfun.
    exists eqfun.
    dands; auto;
    try(spcast;apply computes_to_valc_refl; eauto 3 with slow); [].
    introv Heq Hap.
    abbrev_ls A s1.
    abbrev_lsc B s1.
    assert (equality lib t t (mkc_function As1 x Bs1)) as Heqf
      by (exists eqfun; dands; auto).
    clear Heq.
    assert (equality lib t t' (mkc_function As1 x Bs1)) as Heqf';
    [ | exrepnd; repnud Heqf';exrepnd;
        equality_unique; apply Huniq; auto].
    apply equality_in_function in Heqf.
    exrepnd.
    apply equality_in_function.
    dands;auto;[].
    introv Heqa. duplicate Heqa as Heqb.
    apply_clear Heqf in Heqa.
    dimp (approxc_mkc_apply_congr lib t t' a' a');
    eauto with slow;[].
    specialize (Hypb (snoc s1 (x,a)) (snoc s2 (x,a'))). (* why not cons? *)
    autodimp Hypb Hypb';[ |autodimp Hypb Hypb'].
    + (* hyps_functionality .. exactly same as the one above *) 
      intros s3 sim2. inversion sim2; cpx; allsimpl; cpx.
      rw @eq_hyps_snoc; simpl.
      assert (cover_vars A s4) as cv4
          by (apply (similarity_cover_vars lib) with (hs := H) (s1 := s1); auto).
      exists s1 s4 a t2 w p cv4; sp.
      (* while proving that functionality result, we have to prove that
       * a1 is functional, which we prove using our 1st hyp *)
      specialize (Hypab s1 s4);
      autodimp Hypab hyp1';
      autodimp Hypab hyp1'; exrepnd; clear_irr.
      lsubst_tac.
      apply tequality_mono; auto.
    + (* similarity *)
      rw @similarity_snoc; simpl.
      exists s1 s2 a a' w0 c2; sp;[].
      subst As1; auto.
    + exrepnd. 
      repeat match goal with
      [H: _ = _ |- _ ] => hide_hyp H
      end; lsubst_tac.
      show_hyps.
      rewrite  simple_substc2 with (cu:= c3) in Hypb1;
      [|rw sim1; auto; fail].
      rw <- HeqBs1 in Hypb1.
      apply equality_in_mkc_mono in Hypb1.
      exrepnd.
      clear Hypb1 Hypb3 pt3 pt0 Hypb0 c7 c6 pC5 pC4. 
      apply equality_sym in Heqa.
      applydup @equality_refl in Heqa.
      repnud Heqa0.
      repnud Heqa0.
      exrepnd.
      equality_unique.
      apply Huniq in Heqa1.
      repnud Hypb2.
      pose proof (Hypb2 _ _ Heqa1 hyp).
      repeat match goal with
      [H: eqa ?t1 ?t2 |- _ ] =>
        assert (equality lib t1 t2 ((Bs1) [[x \\ a]]))
         by (exists eqa; dands; auto); clear H
      end.
      eauto with nequality.
Qed.

(* 
Lemma resp_cequiv_sequent : forall H, respects1 cequiv
  (fun C: NTerm => let seq:= ((H) ||- (mk_conclax C)) in 
      forall  wg cg c, sequent_true (mk_wcseq seq (ext_wf_cseq seq wg cg c))).
Abort.
*)

(**
<<
   H |- Mono ((x:A) × B)

     By product_mono
     H |- Mono A
     H, x:A |- Mono B
>>
 *)
Definition rule_mono_product {o}
           (A B : @NTerm o)
           (x : NVar)
           (H : barehypotheses) :=
  mk_rule
    (mk_baresequent H (mk_conclax 
        (mk_mono (mk_product A x B)) ))
    [   (mk_baresequent H (mk_conclax  (mk_mono A) )),
        (mk_baresequent (snoc H (mk_hyp x A)) (mk_conclax (mk_mono B)))
    ]
    [].


(** The following lemma lifts [approx_mk_pair] of Sec. %\ref{sec:comp:approx}%
    to the [CTerm] type *)
Lemma approxc_mkc_pair {o} :
  forall lib (t t' a b : @CTerm o),
    computes_to_valc lib t (mkc_pair a b)
    -> approxc lib t t'
    -> {a', b' : CTerm $
         computes_to_valc lib t' (mkc_pair a' b')
         # approxc lib a a'
         # approxc lib b b'}.
Proof.
  introv Hcv Hap. dest_ctermsn.
  allunfold @approxc. allunfold @computes_to_valc.
  allsimpl.
  repeat match goal with 
  [H : isprog _ |- _] => clear H
  end.
  eapply approx_mk_pair in Hap; eauto;[].
  exrepnd.
  dest_ctermsn.
  applydup @approx_relates_only_progs in Hap1 as bp.
  applydup @approx_relates_only_progs in Hap2 as ap.
  repnd.
  exists (mk_cterm a' ap).
  exists (mk_cterm b' bp).
  dands; simpl; auto.
Qed.

Lemma rule_mono_product_true {o} :
  forall lib (H : @barehypotheses o)
         (A B : NTerm)
         (x: NVar),
    rule_true lib (rule_mono_product A B x H).
Proof.
  unfold rule_mono_product, rule_true, closed_type_baresequent,
       closed_extract_baresequent. simpl.
  intros.
  clear cargs.
  destseq; allsimpl.
  dLin_hyp.
  (* We prove the well-formedness of things *)
  destruct Hyp as [ wsa Hypa ].
  destruct Hyp0 as [ wsb Hypb ].
  destseq; allsimpl; proof_irr; GC.
  dup wfh0 as h; apply vswf_hypotheses_eq in h.
  inversion h as [XX |  Hsn HsH H2h H3h H4h H5h]; cpx; allsimpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  applydup @similarity_dom in sim. repnd.
  vr_seq_true in Hypa.
  generalize (Hypa s1 s2 eqh sim). rename Hypa into Hypab. intro Hypa. exrepnd.
  lsubst_tac. rw @tequality_mono in Hypa0.
  vr_seq_true in Hypb.
  match goal with
  [|- (tequality ?lib (mkc_mono ?A) (mkc_mono ?B))# _] =>
  assert (tequality lib A B) as Hteq
  end.
  - apply tequality_product.
    (* the of this subgal is exactly same as rule_function*)
    dands; auto;[]. introv Heq.
    specialize (Hypb (snoc s1 (x,a)) (snoc s2 (x,a'))). 
    (* why not cons? see defn of similarity *)
    autodimp Hypb Hypb';[ |autodimp Hypb Hypb'].
    + (* hyps_functionality *) 
      intros s3 sim2. inversion sim2; cpx; allsimpl; cpx.
      rw @eq_hyps_snoc; simpl.
      assert (cover_vars A s4) as cv4
          by (eapply @similarity_cover_vars with (hs := H) (s1 := s1); eauto).
      exists s1 s4 a t2 w p cv4; sp.
      (* while proving that functionality result, we have to prove that
       * a1 is functional, which we prove using our 1st hyp *)
      specialize (Hypab s1 s4);
      autodimp Hypab hyp1';
      autodimp Hypab hyp1'; exrepnd; clear_irr.
      lsubst_tac.
      apply tequality_mono; auto.
    + (* similarity *)
      rw @similarity_snoc; simpl.
      exists s1 s2 a a' w0 c2; sp;
      complete (allapply similarity_refl; sp).
    + exrepnd.
      lsubst_tac.
      rw @tequality_mono in Hypb0.
      rewrite <- simple_substc2 with (c:=c6);
      [|rw sim1; auto; fail].
      rewrite <- simple_substc2 with (c:=c7);
      [|rw sim0; auto; fail]. trivial.
  - split;[apply tequality_mono; auto; fail |].
    apply equality_in_mkc_mono.
    applydup @tequality_refl in Hteq.
    repnud Hteq0. exrepnd.
    rename eq into eqfun.
    exists eqfun.
    dands; auto;
    try(spcast;apply computes_to_valc_refl; eauto 3 with slow); [].
    introv Heq Hap.
    abbrev_ls A s1.
    abbrev_lsc B s1.
    assert (equality lib t t (mkc_product As1 x Bs1)) as Heqf
      by (exists eqfun; dands; auto).
    clear Heq.
    assert (equality lib t t' (mkc_product As1 x Bs1)) as Heqf';
    [ | exrepnd; repnud Heqf';exrepnd;
        equality_unique; apply Huniq; auto].
    apply equality_in_product in Heqf.
    exrepnd.
    apply equality_in_product.
    dands;auto;[].
    spcast.
    pose proof (computes_to_valc_eq _ _ _ _ Heqf4 Heqf2) as XX.
    apply mkc_pair_eq in XX. repnd.
    subst a2. subst b2.
    eapply approxc_mkc_pair in Hap; eauto.
    revert Hypa1. introv Hypa1. (* move to top for better visibility*)
    apply' @mono_inhabited_implies  Hypa1.
    exrepnd; auto. eapply Hypa1 in Hap2; eauto;[].
    clear Hypa1. exrepnd. exists a1 a' b1 b'. dands; spcast; auto;[].
    
    (* apply_clear Heqf in Heqa. *)
    specialize (Hypb (snoc s1 (x,a1)) (snoc s2 (x,a'))). (* why not cons? *)
    autodimp Hypb Hypb';[ |autodimp Hypb Hypb'].
    + (* hyps_functionality *) 
      intros s3 sim2. inversion sim2; cpx; allsimpl; cpx.
      rw @eq_hyps_snoc; simpl.
      assert (cover_vars A s4) as cv4
          by (eapply @similarity_cover_vars with (hs := H) (s1 := s1); eauto).
      exists s1 s4 a1 t2 w p cv4; sp.
      (* while proving that functionality result, we have to prove that
       * a1 is functional, which we prove using our 1st hyp *)
      specialize (Hypab s1 s4);
      autodimp Hypab hyp1';
      autodimp Hypab hyp1'; exrepnd; clear_irr.
      lsubst_tac.
      apply tequality_mono; auto.
    + (* similarity *)
      rw @similarity_snoc; simpl.
      exists s1 s2 a1 a' w0 c2; sp;[].
      subst As1; auto.
    + exrepnd. 
      repeat match goal with
      [H: _ = _ |- _ ] => hide_hyp H
      end; lsubst_tac.
      show_hyps.
      rewrite  simple_substc2 with (cu:= c3) in Hypb1;
      [|rw sim1; auto; fail].
      rw <- HeqBs1 in Hypb1.
      apply' @mono_inhabited_implies Hypb1.
      clear Hypb0.
      repeat match goal with
      [H:cover_vars _ _ |- _] => try clear H
      end.
      eapply Hypb1 in Hap1; eauto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
