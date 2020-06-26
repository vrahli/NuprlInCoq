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


Require Export sequents2.
(*Require Export sequents_lib.*)
Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_union.
Require Export per_props_cequiv.
Require Export per_props_squash.
Require Export subst_tacs.
Require Export sequents_equality.
Require Export sequents_tacs2.
Require Export sequents_useful.


Lemma inhabited_mkc_or {o} :
  forall uk lib (A B : @CTerm o),
    inhabited_type_bar uk lib (mkc_or A B)
    <=> (type uk lib A
         # type uk lib B
         # in_open_bar lib (fun lib => (inhabited_type uk lib A {+} inhabited_type uk lib B))).
Proof.
  introv.
  split; introv h; exrepnd; dands.

  - apply all_in_ex_bar_type_implies_type.
    eapply in_open_bar_pres; eauto; clear h; introv ext h.
    unfold inhabited_type in *; exrepnd.
    apply equality_mkc_or in h0; exrepnd; dands; auto.

  - apply all_in_ex_bar_type_implies_type.
    eapply in_open_bar_pres; eauto; clear h; introv ext h.
    unfold inhabited_type in *; exrepnd.
    apply equality_mkc_or in h0; exrepnd; dands; auto.

  - apply in_open_bar_ext_in_open_bar.
    eapply in_open_bar_ext_comb2;eauto; clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv ext h.
    unfold inhabited_type in *; exrepnd.
    apply equality_mkc_or in h0; exrepnd.
    eapply in_open_bar_pres; eauto; clear h0; introv xt h0.
    repndors; exrepnd; apply equality_refl in h0; eauto.

  - eapply in_open_bar_pres; eauto; clear h.
    introv ext h; unfold inhabited_type in *; repndors; exrepnd.

    + exists (mkc_inl t).
      apply equality_mkc_or; dands; auto; eauto 3 with slow.
      apply in_ext_implies_in_open_bar; introv xt; left.
      exists t t; dands; auto; spcast; eauto 3 with slow.

    + exists (mkc_inr t).
      apply equality_mkc_or; dands; auto; eauto 3 with slow.
      apply in_ext_implies_in_open_bar; introv xt; right.
      exists t t; dands; auto; spcast; eauto 3 with slow.
Qed.


(* MOVE *)
Lemma equality_respects_ccequivc_bar_left {o} :
  forall uk lib (t1 t2 t T : @CTerm o),
    ccequivc_bar lib t1 t
    -> equality uk lib t1 t2 T
    -> equality uk lib t t2 T.
Proof.
  introv ceq equ.
  apply ccequivc_ext_bar_iff_ccequivc_bar in ceq.
  apply all_in_ex_bar_equality_implies_equality.
  eapply in_open_bar_pres; eauto; clear ceq; introv ext ceq.
  eapply equality_respects_cequivc_left; eauto 3 with slow.
Qed.
Hint Resolve equality_respects_ccequivc_bar_left : nequality.

Lemma equality_respects_ccequivc_bar_right {o} :
  forall uk lib (t1 t2 t T : @CTerm o),
    ccequivc_bar lib t2 t
    -> equality uk lib t1 t2 T
    -> equality uk lib t1 t T.
Proof.
  introv ceq equ.
  apply ccequivc_ext_bar_iff_ccequivc_bar in ceq.
  apply all_in_ex_bar_equality_implies_equality.
  eapply in_open_bar_pres; eauto; clear ceq; introv ext ceq.
  eapply equality_respects_cequivc_right; eauto 3 with slow.
Qed.
Hint Resolve equality_respects_ccequivc_bar_right : nequality.

Lemma in_open_bar_collapse {o} :
  forall (lib : @library o) P,
    in_open_bar lib (fun lib' => in_open_bar lib' P) <=> in_open_bar lib P.
Proof.
  introv; split; intro h.
  { apply in_open_bar_ext_in_open_bar.
    eapply in_open_bar_ext_comb2; eauto; clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv xt h; auto. }
  { apply in_open_bar_ext_in_open_bar in h.
    eapply in_open_bar_comb2; eauto; clear h.
    apply in_ext_ext_implies_in_open_bar_ext; introv xt h; auto. }
Qed.


(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase

     H |- A = B in U(i)
     H |- squash(a1 = b1 in A \/ a1 ~ b1)
     H |- squash(a2 = b2 in A \/ a2 ~ b2)
>>
 *)
Definition rule_equality_equality_base_or {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 : NTerm)
           (u i : nat) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_equality a1 a2 A)
                      (mk_equality b1 b2 B)
                      (mk_uni u i))))
    [ mk_baresequent H (mk_conclax (mk_equality A B (mk_uni u i))),
      mk_baresequent H (mk_conclax (mk_squash (mk_or (mk_equality a1 b1 A) (mk_cequiv a1 b1)))),
      mk_baresequent H (mk_conclax (mk_squash (mk_or (mk_equality a2 b2 A) (mk_cequiv a2 b2))))
    ]
    [].

Lemma rule_equality_equality_base_or_true {o} :
  forall u lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 : NTerm)
         (i : nat),
    rule_true u lib (rule_equality_equality_base_or H A B a1 a2 b1 b2 u i).
Proof.
  unfold rule_equality_equality_base_or, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  rw <- @member_equality_iff.

  pose proof (teq_and_eq_if_equality
                u lib' (mk_uni u i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  repeat (autodimp eqp hyp);[apply tequality_mkc_uni|].

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.
  apply equality_mkc_equality2_sp_in_uni; dands.

  - vr_seq_true in hyp1.
    pose proof (hyp1 _ ext s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in h1.
    apply equality_commutes in h0; auto.

  - split.

    + vr_seq_true in hyp2.
      pose proof (hyp2 _ ext s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply equality_in_mkc_squash in h1; repnd.
      clear h2 h3.
      rw @tequality_mkc_squash in h0.
      apply tequality_mkc_or in h0; repnd.
      apply tequality_mkc_equality_sp in h2; repnd.
      allrw @fold_equorsq.
      apply inhabited_mkc_or in h1; repnd.

      apply in_open_bar_collapse.
      eapply in_open_bar_comb; try exact h1; clear h1.
      eapply in_open_bar_comb; try exact h2; clear h2.
      eapply in_open_bar_pres; try exact h4; clear h4.
      introv xt h4 h2 h1.

      repndors.
      { apply inhabited_mkc_equality in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply equality_monotone in h1; eauto.
        left.
        eapply equality_trans;[exact h1|]; eauto 3 with slow. }
      { apply inhabited_mkc_equality in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply equality_monotone in h1; eauto.
        left.
        eapply equality_trans;[exact h1|]; eauto 3 with slow. }
      { apply inhabited_mkc_equality in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply equality_monotone in h1; eauto.
        left.
        eapply equality_respects_cequivc_right;[|exact h1]; eauto 3 with slow. }
      { apply inhabited_mkc_equality in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply equality_monotone in h1; eauto.
        left.
        eapply equality_respects_cequivc_right;[|exact h1]; eauto 2 with slow. }
      { apply inhabited_cequiv in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply lib_extends_preserves_in_open_bar in h1; eauto.
        eapply equality_monotone in h2; eauto.
        left.
        eapply equality_respects_ccequivc_bar_left;[|exact h2]; eauto.
        apply ccequivc_bar_sym; auto. }
      { apply inhabited_cequiv in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply lib_extends_preserves_in_open_bar in h1; eauto.
        eapply equality_monotone in h2; eauto.
        left.
        eapply equality_respects_ccequivc_bar_left;[|exact h2]; eauto.
        apply ccequivc_bar_sym; auto. }
      { apply inhabited_cequiv in h1.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h1.
        eapply in_open_bar_pres; try exact h1; clear h1; introv xt' h1.
        right.
        eapply ccequivc_ext_trans;[eauto|]; eauto 3 with slow. }
      { apply inhabited_cequiv in h1.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h1.
        eapply in_open_bar_pres; try exact h1; clear h1; introv xt' h1.
        right.
        eapply ccequivc_ext_trans;[eauto|]; eauto 3 with slow. }

    + vr_seq_true in hyp3.
      pose proof (hyp3 _ ext s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply equality_in_mkc_squash in h1; repnd.
      clear h2 h3.
      rw @tequality_mkc_squash in h0.
      apply tequality_mkc_or in h0; repnd.
      apply tequality_mkc_equality_sp in h2; repnd.
      apply inhabited_mkc_or in h1; repnd.

      apply in_open_bar_collapse.
      eapply in_open_bar_comb; try exact h1; clear h1.
      eapply in_open_bar_comb; try exact h2; clear h2.
      eapply in_open_bar_pres; try exact h4; clear h4.
      introv xt h4 h2 h1.

      repndors.
      { apply inhabited_mkc_equality in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply equality_monotone in h1; eauto.
        left.
        eapply equality_trans;[exact h1|]; eauto 3 with slow. }
      { apply inhabited_mkc_equality in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply equality_monotone in h1; eauto.
        left.
        eapply equality_trans;[exact h1|]; eauto 3 with slow. }
      { apply inhabited_mkc_equality in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply equality_monotone in h1; eauto.
        left.
        eapply equality_respects_cequivc_right;[|exact h1]; eauto 3 with slow. }
      { apply inhabited_mkc_equality in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply equality_monotone in h1; eauto.
        left.
        eapply equality_respects_cequivc_right;[|exact h1]; eauto 2 with slow. }
      { apply inhabited_cequiv in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply lib_extends_preserves_in_open_bar in h1; eauto.
        eapply equality_monotone in h2; eauto.
        left.
        eapply equality_respects_ccequivc_bar_left;[|exact h2]; eauto.
        apply ccequivc_bar_sym; auto. }
      { apply inhabited_cequiv in h1.
        apply in_ext_implies_in_open_bar; introv xt'.
        eapply lib_extends_preserves_in_open_bar in h1; eauto.
        eapply equality_monotone in h2; eauto.
        left.
        eapply equality_respects_ccequivc_bar_left;[|exact h2]; eauto.
        apply ccequivc_bar_sym; auto. }
      { apply inhabited_cequiv in h1.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h1.
        eapply in_open_bar_pres; try exact h1; clear h1; introv xt' h1.
        right.
        eapply ccequivc_ext_trans;[eauto|]; eauto 3 with slow. }
      { apply inhabited_cequiv in h1.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h1.
        eapply in_open_bar_pres; try exact h1; clear h1; introv xt' h1.
        right.
        eapply ccequivc_ext_trans;[eauto|]; eauto 3 with slow. }
Qed.



Definition rule_equality_equality_concl {o} (H : @bhyps o) a1 a2 b1 b2 A B u i :=
  mk_baresequent
    H
    (mk_conclax (mk_equality
                   (mk_equality a1 a2 A)
                   (mk_equality b1 b2 B)
                   (mk_uni u i))).

Definition rule_equality_equality_hyp1 {o} (H : @bhyps o) A B u i e :=
  mk_baresequent H (mk_concl (mk_equality A B (mk_uni u i)) e).

Definition rule_equality_equality_hyp2 {o} (H : @bhyps o) a b A e :=
  mk_baresequent H (mk_concl (mk_equality a b A) e).

(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEquality

     H |- A = B in U(i)
     H |- a1 = b1 in A
     H |- a2 = b2 in A
>>
 *)
Definition rule_equality_equality {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (u i : nat) :=
  mk_rule
    (rule_equality_equality_concl H a1 a2 b1 b2 A B u i)
    [ rule_equality_equality_hyp1 H A B u i e1,
      rule_equality_equality_hyp2 H a1 b1 A e2,
      rule_equality_equality_hyp2 H a2 b2 A e3
    ]
    [].

Lemma rule_equality_equality_true3 {o} :
  forall u lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true3 u lib (rule_equality_equality H A B a1 a2 b1 b2 e1 e2 e3 u i).
Proof.
  unfold rule_equality_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2 hyp3.
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; auto.
    - apply wf_axiom.
    - unfold closed_extract; simpl; auto.
  }
  exists wfc.
  destseq; simpl in *.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  rw <- @member_equality_iff.

  pose proof (teq_and_eq_if_equality
                u lib' (mk_uni u i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  repeat (autodimp eqp hyp);[apply tequality_mkc_uni|].

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.
  apply equality_mkc_equality2_sp_in_uni; dands.

  - vr_seq_true in hyp1.
    pose proof (hyp1 _ ext s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; repnd.
    clear h1 h3.
    apply equality_commutes in h0; auto.

  - split; apply in_ext_implies_in_open_bar; left.

    + vr_seq_true in hyp2.
      pose proof (hyp2 _ ext s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in h0; repnd.
      apply equality_in_mkc_equality in h1; repnd.
      eapply lib_extends_preserves_in_open_bar in h0; eauto.
      eapply lib_extends_preserves_in_open_bar in h3; eauto.

      apply all_in_ex_bar_equality_implies_equality.
      eapply in_open_bar_comb; try exact h0; clear h0.
      eapply in_open_bar_pres; try exact h3; clear h3.
      introv xt h3 h0.

      repndors.
      { eapply equality_trans;[|exact h0]; eauto 3 with slow. }
      { eapply equality_trans;[|exact h0]; eauto 3 with slow. }
      { eapply equality_respects_cequivc_right; eauto; eauto 3 with slow. }
      { eapply equality_respects_cequivc_right; eauto; eauto 3 with slow. }

    + vr_seq_true in hyp3.
      pose proof (hyp3 _ ext s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in h0; repnd.
      apply equality_in_mkc_equality in h1; repnd.
      eapply lib_extends_preserves_in_open_bar in h0; eauto.
      eapply lib_extends_preserves_in_open_bar in h3; eauto.

      apply all_in_ex_bar_equality_implies_equality.
      eapply in_open_bar_comb; try exact h0; clear h0.
      eapply in_open_bar_pres; try exact h3; clear h3.
      introv xt h3 h0.

      repndors.
      { eapply equality_trans;[|exact h0]; eauto 3 with slow. }
      { eapply equality_trans;[|exact h0]; eauto 3 with slow. }
      { eapply equality_respects_cequivc_right; eauto; eauto 3 with slow. }
      { eapply equality_respects_cequivc_right; eauto; eauto 3 with slow. }
Qed.

(*Lemma rule_equality_equality_true_ext_lib {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true_ext_lib lib (rule_equality_equality H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_equality_equality_true3.
Qed.*)

Lemma rule_equality_equality_wf2 {o} :
  forall (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (u i : nat),
    wf_rule2 (rule_equality_equality H A B a1 a2 b1 b2 e1 e2 e3 u i).
Proof.
  introv wf m; allsimpl.
  repndors; subst; tcsp;
    allunfold @wf_bseq; allsimpl; repnd; dands; auto.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.
Qed.



Definition rule_equality_equality_hyp3 {o} (H : @bhyps o) a b e :=
  mk_baresequent H (mk_concl (mk_equality a b mk_base) e).

(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase

     H |- A = B in U(i)
     H |- a1 = b1 in Base
     H |- a2 = b2 in Base
>>
 *)
Definition rule_equality_equality_base {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (u i : nat) :=
  mk_rule
    (rule_equality_equality_concl H a1 a2 b1 b2 A B u i)
    [ rule_equality_equality_hyp1 H A B u i e1,
      rule_equality_equality_hyp3 H a1 b1 e2,
      rule_equality_equality_hyp3 H a2 b2 e3
    ]
    [].

Lemma rule_equality_equality_base_true3 {o} :
  forall u lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true3 u lib (rule_equality_equality_base H A B a1 a2 b1 b2 e1 e2 e3 u i).
Proof.
  unfold rule_equality_equality_base, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2 hyp3.
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; auto.
    - apply wf_axiom.
    - unfold closed_extract; simpl; auto.
  }
  exists wfc.
  destseq; simpl in *.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  rw <- @member_equality_iff.

  pose proof (teq_and_eq_if_equality
                u lib' (mk_uni u i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  repeat (autodimp eqp hyp);[apply tequality_mkc_uni|].

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.
  apply equality_mkc_equality2_sp_in_uni; dands.

  - vr_seq_true in hyp1.
    pose proof (hyp1 _ ext s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; repnd.
    clear h1 h3.
    apply equality_commutes in h0; auto.

  - split.

    + vr_seq_true in hyp2.
      pose proof (hyp2 _ ext s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in h0; repnd.
      apply equality_in_mkc_equality in h1; repnd.
      eapply lib_extends_preserves_in_open_bar in h0; eauto.
      eapply lib_extends_preserves_in_open_bar in h3; eauto.
      apply equality_in_base in h4; auto.
      apply ccequivc_ext_bar_iff_ccequivc_bar in h4.

      apply in_open_bar_collapse.
      eapply in_open_bar_comb; try exact h0; clear h0.
      eapply in_open_bar_comb; try exact h3; clear h3.
      eapply in_open_bar_pres; try exact h4; clear h4.
      introv xt h3 h0 h4.

      repndors.
      { apply equality_in_base in h0; auto.
        apply equality_in_base in h4; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h0.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h4.
        eapply in_open_bar_comb; try exact h0; clear h0.
        eapply in_open_bar_pres; try exact h4; clear h4.
        introv xt' h0 h4; right.
        eauto 3 with slow. }
      { apply equality_in_base in h4; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h4.
        eapply in_open_bar_pres; try exact h4; clear h4.
        introv xt' h4; right.
        eauto 3 with slow. }
      { apply equality_in_base in h0; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h0.
        eapply in_open_bar_pres; try exact h0; clear h0.
        introv xt' h0; right.
        eauto 3 with slow. }
      { eapply in_ext_implies_in_open_bar; introv xt'; right; eauto 3 with slow. }

    + vr_seq_true in hyp3.
      pose proof (hyp3 _ ext s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in h0; repnd.
      apply equality_in_mkc_equality in h1; repnd.
      eapply lib_extends_preserves_in_open_bar in h0; eauto.
      eapply lib_extends_preserves_in_open_bar in h3; eauto.
      apply equality_in_base in h4; auto.
      apply ccequivc_ext_bar_iff_ccequivc_bar in h4.

      apply in_open_bar_collapse.
      eapply in_open_bar_comb; try exact h0; clear h0.
      eapply in_open_bar_comb; try exact h3; clear h3.
      eapply in_open_bar_pres; try exact h4; clear h4.
      introv xt h3 h0 h4.

      repndors.
      { apply equality_in_base in h0; auto.
        apply equality_in_base in h4; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h0.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h4.
        eapply in_open_bar_comb; try exact h0; clear h0.
        eapply in_open_bar_pres; try exact h4; clear h4.
        introv xt' h0 h4; right.
        eauto 3 with slow. }
      { apply equality_in_base in h4; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h4.
        eapply in_open_bar_pres; try exact h4; clear h4.
        introv xt' h4; right.
        eauto 3 with slow. }
      { apply equality_in_base in h0; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h0.
        eapply in_open_bar_pres; try exact h0; clear h0.
        introv xt' h0; right.
        eauto 3 with slow. }
      { eapply in_ext_implies_in_open_bar; introv xt'; right; eauto 3 with slow. }
Qed.

(*Lemma rule_equality_equality_base_true_ext_lib {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true_ext_lib lib (rule_equality_equality_base H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_equality_equality_base_true3.
Qed.*)

Lemma rule_equality_equality_base_wf2 {o} :
  forall (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (u i : nat),
    wf_rule2 (rule_equality_equality_base H A B a1 a2 b1 b2 e1 e2 e3 u i).
Proof.
  introv wf m; allsimpl.
  repndors; subst; tcsp;
    allunfold @wf_bseq; allsimpl; repnd; dands; auto.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.
Qed.


(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase1

     H |- A = B in U(i)
     H |- a1 = b1 in Base
     H |- a2 = b2 in A
>>
 *)
Definition rule_equality_equality_base1 {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (u i : nat) :=
  mk_rule
    (rule_equality_equality_concl H a1 a2 b1 b2 A B u i)
    [ rule_equality_equality_hyp1 H A B u i e1,
      rule_equality_equality_hyp3 H a1 b1 e2,
      rule_equality_equality_hyp2 H a2 b2 A e3
    ]
    [].

Lemma rule_equality_equality_base1_true3 {o} :
  forall u lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true3 u lib (rule_equality_equality_base1 H A B a1 a2 b1 b2 e1 e2 e3 u i).
Proof.
  unfold rule_equality_equality_base1, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2 hyp3.
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; auto.
    - apply wf_axiom.
    - unfold closed_extract; simpl; auto.
  }
  exists wfc.
  destseq; simpl in *.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  rw <- @member_equality_iff.

  pose proof (teq_and_eq_if_equality
                u lib' (mk_uni u i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  repeat (autodimp eqp hyp);[apply tequality_mkc_uni|].

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.

  apply equality_mkc_equality2_sp_in_uni; dands.

  - vr_seq_true in hyp1.
    pose proof (hyp1 _ ext s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; repnd.
    clear h1 h3.
    apply equality_commutes in h0; auto.

  - split.

    + vr_seq_true in hyp2.
      pose proof (hyp2 _ ext s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in h0; repnd.
      apply equality_in_mkc_equality in h1; repnd.
      apply equality_in_base in h4; auto.
      apply ccequivc_ext_bar_iff_ccequivc_bar in h4.

      apply in_open_bar_collapse.
      eapply in_open_bar_comb; try exact h0; clear h0.
      eapply in_open_bar_comb; try exact h3; clear h3.
      eapply in_open_bar_pres; try exact h4; clear h4.
      introv xt h3 h0 h4.

      repndors.
      { apply equality_in_base in h0; auto.
        apply equality_in_base in h4; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h0.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h4.
        eapply in_open_bar_comb; try exact h0; clear h0.
        eapply in_open_bar_pres; try exact h4; clear h4.
        introv xt' h0 h4; right.
        eauto 3 with slow. }
      { apply equality_in_base in h4; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h4.
        eapply in_open_bar_pres; try exact h4; clear h4.
        introv xt' h4; right.
        eauto 3 with slow. }
      { apply equality_in_base in h0; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h0.
        eapply in_open_bar_pres; try exact h0; clear h0.
        introv xt' h0; right.
        eauto 3 with slow. }
      { eapply in_ext_implies_in_open_bar; introv xt'; right; eauto 3 with slow. }

    + vr_seq_true in hyp3.
      pose proof (hyp3 _ ext s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in h0; repnd.
      apply equality_in_mkc_equality in h1; repnd.

      eapply in_open_bar_comb; try exact h0; clear h0.
      eapply in_open_bar_pres; try exact h3; clear h3.
      introv xt h3 h0; left.

      repndors.
      { eapply equality_trans;[|exact h0]; eauto 3 with slow. }
      { eapply equality_trans;[|exact h0]; eauto 3 with slow. }
      { eapply equality_respects_cequivc_right; eauto; eauto 3 with slow. }
      { eapply equality_respects_cequivc_right; eauto; eauto 3 with slow. }
Qed.

(*Lemma rule_equality_equality_base1_true_ext_lib {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true_ext_lib lib (rule_equality_equality_base1 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_equality_equality_base1_true3.
Qed.*)

Lemma rule_equality_equality_base1_wf2 {o} :
  forall (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (u i : nat),
    wf_rule2 (rule_equality_equality_base1 H A B a1 a2 b1 b2 e1 e2 e3 u i).
Proof.
  introv wf m; allsimpl.
  repndors; subst; tcsp;
    allunfold @wf_bseq; allsimpl; repnd; dands; auto.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.
Qed.

(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase2

     H |- A = B in U(i)
     H |- a1 = b1 in A
     H |- a2 = b2 in Base
>>
 *)
Definition rule_equality_equality_base2 {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (u i : nat) :=
  mk_rule
    (rule_equality_equality_concl H a1 a2 b1 b2 A B u i)
    [ rule_equality_equality_hyp1 H A B u i e1,
      rule_equality_equality_hyp2 H a1 b1 A e2,
      rule_equality_equality_hyp3 H a2 b2 e3
    ]
    [].

Lemma rule_equality_equality_base2_true3 {o} :
  forall u lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true3 u lib (rule_equality_equality_base2 H A B a1 a2 b1 b2 e1 e2 e3 u i).
Proof.
  unfold rule_equality_equality_base2, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2 hyp3.
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; auto.
    - apply wf_axiom.
    - unfold closed_extract; simpl; auto.
  }
  exists wfc.
  destseq; simpl in *.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  rw <- @member_equality_iff.

  pose proof (teq_and_eq_if_equality
                u lib' (mk_uni u i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  repeat (autodimp eqp hyp);[apply tequality_mkc_uni|].

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.

  apply equality_mkc_equality2_sp_in_uni; dands.

  - vr_seq_true in hyp1.
    pose proof (hyp1 _ ext s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    apply equality_in_mkc_equality in h1; repnd.
    clear h1 h3.
    apply equality_commutes in h0; auto.

  - split.

    + vr_seq_true in hyp2.
      pose proof (hyp2 _ ext s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in h0; repnd.
      apply equality_in_mkc_equality in h1; repnd.

      eapply in_open_bar_comb; try exact h0; clear h0.
      eapply in_open_bar_pres; try exact h3; clear h3.
      introv xt h3 h0; left.

      repndors.
      { eapply equality_trans;[|exact h0]; eauto 3 with slow. }
      { eapply equality_trans;[|exact h0]; eauto 3 with slow. }
      { eapply equality_respects_cequivc_right; eauto; eauto 3 with slow. }
      { eapply equality_respects_cequivc_right; eauto; eauto 3 with slow. }

    + vr_seq_true in hyp3.
      pose proof (hyp3 _ ext s1 s2 hf sim) as h; clear hyp3; exrepnd.
      lsubst_tac.
      apply tequality_mkc_equality_sp in h0; repnd.
      apply equality_in_mkc_equality in h1; repnd.
      apply equality_in_base in h4; auto.
      apply ccequivc_ext_bar_iff_ccequivc_bar in h4.

      apply in_open_bar_collapse.
      eapply in_open_bar_comb; try exact h0; clear h0.
      eapply in_open_bar_comb; try exact h3; clear h3.
      eapply in_open_bar_pres; try exact h4; clear h4.
      introv xt h3 h0 h4.

      repndors.
      { apply equality_in_base in h0; auto.
        apply equality_in_base in h4; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h0.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h4.
        eapply in_open_bar_comb; try exact h0; clear h0.
        eapply in_open_bar_pres; try exact h4; clear h4.
        introv xt' h0 h4; right.
        eauto 3 with slow. }
      { apply equality_in_base in h4; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h4.
        eapply in_open_bar_pres; try exact h4; clear h4.
        introv xt' h4; right.
        eauto 3 with slow. }
      { apply equality_in_base in h0; auto.
        apply ccequivc_ext_bar_iff_ccequivc_bar in h0.
        eapply in_open_bar_pres; try exact h0; clear h0.
        introv xt' h0; right.
        eauto 3 with slow. }
      { eapply in_ext_implies_in_open_bar; introv xt'; right; eauto 3 with slow. }
Qed.

(*Lemma rule_equality_equality_base2_true_ext_lib {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true_ext_lib lib (rule_equality_equality_base2 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_equality_equality_base2_true3.
Qed.*)

Lemma rule_equality_equality_base2_wf2 {o} :
  forall (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (u i : nat),
    wf_rule2 (rule_equality_equality_base2 H A B a1 a2 b1 b2 e1 e2 e3 u i).
Proof.
  introv wf m; allsimpl.
  repndors; subst; tcsp;
    allunfold @wf_bseq; allsimpl; repnd; dands; auto.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.
Qed.
