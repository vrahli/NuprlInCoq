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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export rules_integer_ring.
Require Export rules_minus.
Require Export per_props_compute.
Require Export per_props_true.
Require Export cequiv_seq_util.


Lemma equality_of_int_mkc_integer {o} :
  forall lib n,
    @equality_of_int o lib (mkc_integer n) (mkc_integer n).
Proof.
  introv; exists n; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve equality_of_int_mkc_integer : slow.


Hint Rewrite @lsubstc_mk_true : slow.
Hint Rewrite @lsubstc_mk_false : slow.


(* Two rules about div and rem state equalities. They are div_rem_sum and rem_zero. *)

(*
   H |- a = (a div b) * b + (a rem b) in Z

     By divideRemainderSum

     H |- int_eq b 0 False True
     H |- a in Z
     H |- b in Z
 *)
Definition rule_div_rem_sum {o}
           (H : barehypotheses)
           (a b : @NTerm o) :=
  let d := mk_div a b in
  let r := mk_rem a b in
  let s := mk_add (mk_mul d b) r in
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a s  mk_int)))
    [ mk_baresequent H (mk_conclax (mk_not_eqint b (mk_integer 0))),
      mk_baresequent H (mk_conclax (mk_member a mk_int)),
      mk_baresequent H (mk_conclax (mk_member b mk_int))
    ]
    [].

(*
   H |- (0 rem b) = 0 in Z

     By remZero

     H |- int_eq b 0 False True
     H |- b in Z
 *)
Definition rule_rem_zero {o}
           (H : barehypotheses)
           (b : @NTerm o) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_rem (mk_integer 0) b) (mk_integer 0) mk_int)))
    [ mk_baresequent H (mk_conclax (mk_not_eqint b (mk_integer 0))),
      mk_baresequent H (mk_conclax (mk_member b mk_int))
    ]
    [].



Lemma rule_div_rem_sum_true {o} :
  forall lib (H : barehypotheses)
         (m n : @NTerm o),
    rule_true lib (rule_div_rem_sum H m n).
Proof.
  unfold rule_add_inverse, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  unfold mk_not_eqint.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.

  lsubst_tac.
  rw <- @member_equality_iff.
  teq_and_eq (@mk_int o) m (mk_add (mk_mul (mk_div m n) n) (mk_rem m n)) s1 s2 H;
    eauto 3 with slow;[].

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 hf sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 hf sim) as hyp1; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 hf sim) as hyp2; clear hyp3.
  exrepnd.
  fold_mk_arithop.
  lsubst_tac.
  autorewrite with slow in *.

  match goal with
  | [ H : cover_vars _ _ |- _ ] => clear H
  | [ H : wf_term _ |- _ ] => clear H
  end.

  allrw <- @member_member_iff.
  apply tequality_mkc_member_implies_sp in hyp3; auto;[].
  apply tequality_mkc_member_implies_sp in hyp0; auto;[].

  revert hyp0 hyp3.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms n2.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms m2.
  introv hyp0 hyp3.

  eapply equality_trans;[exact hyp3|].
  apply equality_sym in hyp0; apply equality_refl in hyp0.
  apply equality_sym in hyp3; apply equality_refl in hyp3.
  eapply tequality_preserving_equality in hyp5;[|eauto];[].
  clear dependent m1; clear dependent n1.

  allrw @member_int_iff; spcast; exrepnd.
  apply equality_in_int; exists z; dands; spcast; auto;[].

  assert (z0 <> 0%Z) as nz.
  {
    clear - hyp2 hyp5.
    (* from these two hyps we can prove z0 is not 0 *)
    introv xx; subst.
    rewrite <- mkc_not_eqint_eq in hyp5.
    eapply cequivc_preserving_equality in hyp5;
      [|apply computes_to_valc_implies_cequivc;
        eapply mkc_not_eqint_comp1;eauto 3 with slow].
    apply equality_in_false in hyp5; tcsp.
  }

  (* now we have z0 not eq 0 *)

  assert (mkc_integer z = @mkc_integer o (((Z.quot z z0)*z0)+(Z.rem z z0))) as eq.
  { apply mkc_integer_eq_iff.
    pose proof Z.quot_rem z z0.
    rw Z.mul_comm; auto. }

  rewrite mkc_add_is_mkc_arithop.
  rw eq; repeat (apply computes_to_valc_arithop;auto).
Qed.



Lemma rule_rem__zero_true {o} :
  forall lib (H : barehypotheses)
         (n : @NTerm o),
    rule_true lib (rule_rem_zero H n).
Proof.
  unfold rule_add_inverse, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  unfold mk_not_eqint.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hyp1; clear hyp2.
  
  exrepnd. 
  fold_mk_arithop. 
  lsubst_tac.
  repeat rw @lsubstc_mk_true in hyp2.
  repeat rw @lsubstc_mk_false in hyp2.
  repeat rw @lsubstc_mk_true in hyp3.
  repeat rw @lsubstc_mk_false in hyp3.
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms n2.
  assert (equality_of_int lib (mkc_integer 0) (mkc_integer 0)).
    apply equality_of_int_mkc_integer. 
  split.
  - (* tequality *) apply @tequality_mkc_equality_sp; split.
    + apply tequality_int.
    + split; left; apply equality_in_int; auto.
      repeat (apply @equality_of_int_arithop; auto). 
  - (* equality *)
     rw @member_eq. rw <- @member_equality_iff.
     rw @equality_in_int. 
     clear dependent n2.
    allrw @member_int_iff. spcast. exrepnd.
   unfold equality_of_int.
   exists 0%Z.
   sp; auto; spcast; auto.   
    assert (z <> 0%Z) as nz. clear - hyp0 hyp3.
    (* from these two hyps we can prove z is not 0 *)
    pose proof (Z.eq_dec z 0) as xx. destruct xx; auto. 
    assert (equality lib mkc_axiom mkc_axiom mkc_false).
    pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1. 
    specialize (r1 mkc_axiom mkc_axiom (mkc_inteq n1 (mkc_integer 0) mkc_false mkc_true) mkc_false).
    apply r1; auto.  rw e in hyp0. clear -hyp0.
    apply computes_to_valc_implies_cequivc.
    fold (@mkc_not_eqint o).
    pose proof (@mkc_not_eqint_comp1 o lib n1 (mkc_integer 0) 0 0) as xx.
     apply xx; auto.  
     apply computes_to_valc_refl. apply iscvalue_mkc_integer.  
   (* we have a member of False *)
    rw @equality_in_false in H; auto.  


   (* now we have z not eq 0 *)
    pose proof (@computes_to_valc_arithop o lib ArithOpRem (mkc_integer 0) n1 0 z) as xx.
    assert (get_arith_op ArithOpRem 0 z = 0%Z).
    simpl. apply Z.rem_0_l; auto.
    rw H1 in xx. apply xx; auto; apply computes_to_valc_refl; apply iscvalue_mkc_integer. 
    apply computes_to_valc_refl; apply iscvalue_mkc_integer.
Qed.

(* The next two rule give the sign of (a rem b) *)

(*
   H |- less (a rem b) 0 False True

     By remPositive

     H |- less 0 a True False
     H |- int_eq b 0 False True
     H |- a in Z
     H |- b in Z
 *)
Definition rule_rem_positive {o}
           (H : barehypotheses)
           (a b : @NTerm o) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_not_less_than (mk_rem a b) (mk_integer 0))))
    [ mk_baresequent H (mk_conclax (mk_less_than (mk_integer 0) a)),
      mk_baresequent H (mk_conclax (mk_not_eqint b (mk_integer 0))),
      mk_baresequent H (mk_conclax (mk_member a mk_int)),
      mk_baresequent H (mk_conclax (mk_member b mk_int))
    ]
    [].

(*
   H |- less 0 (a rem b) False True

     By remNegative

     H |- less a 0 True False
     H |- int_eq b 0 False True
     H |- a in Z
     H |- b in Z
 *)
Definition rule_rem_negative {o}
           (H : barehypotheses)
           (a b : @NTerm o) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_not_less_than (mk_integer 0) (mk_rem a b) )))
    [ mk_baresequent H (mk_conclax (mk_less_than a (mk_integer 0))),
      mk_baresequent H (mk_conclax (mk_not_eqint b (mk_integer 0))),
      mk_baresequent H (mk_conclax (mk_member a mk_int)),
      mk_baresequent H (mk_conclax (mk_member b mk_int))
    ]
    [].

Lemma rule_rem_positive_true {o} :
  forall lib (H : barehypotheses)
         (m n : @NTerm o),
    rule_true lib (rule_rem_positive H m n).
Proof.
  unfold rule_rem_positive, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  unfold mk_not_eqint.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hyp1; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as hyp2; clear hyp3.
  vr_seq_true in hyp4.
  pose proof (hyp4 s1 s2 eqh sim) as hyp3; clear hyp4.
  exrepnd. 
  unfold mk_less_than in hyp7.
  unfold mk_not_less_than. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw @lsubstc_mk_true .
  allrw @lsubstc_mk_false .
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp4; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  apply @equality_of_int_imp_tt in hyp4. destruct hyp4.
  apply @equality_of_int_imp_tt in hyp0. destruct hyp0.
  exrepnd.
  assert (x0 <> 0%Z) as nz. clear - hyp1 p1.
    (* from these two hyps we can prove x0 is not 0 *)
    pose proof (Z.eq_dec x0 0) as xx. destruct xx; auto. 
    assert (equality lib mkc_axiom mkc_axiom mkc_false).
    pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1. 
    specialize (r1 mkc_axiom mkc_axiom (mkc_inteq n1 (mkc_integer 0) mkc_false mkc_true) mkc_false).
    apply r1; auto.  rw e in p1. clear -p1.
    apply computes_to_valc_implies_cequivc.
    fold (@mkc_not_eqint o).
    pose proof (@mkc_not_eqint_comp1 o lib n1 (mkc_integer 0) 0 0) as xx.
     apply xx; auto.  
     apply computes_to_valc_refl. apply iscvalue_mkc_integer.  
   (* we have a member of False *)
    rw @equality_in_false in H; auto.
   (* now we have x0 not eq 0 *)
    assert (0 <= x)%Z.  clear - hyp7 p2.
    (* From these two hyps we can prove 0 <= x *) 
     pose proof (Z.le_decidable 0 x) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less (mkc_integer 0) m1 mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib (mkc_integer 0) m1 0 x) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have 0 <= x *)
   assert (0 <= Z.rem x x0)%Z. apply Z.rem_nonneg; auto.
  split.
  - (* tequality *) apply @tequality_mkc_less. 
    exists (Z.rem x x0). exists 0%Z. exists (Z.rem x x0). exists 0%Z.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m1 n1 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. apply computes_to_valc_refl. apply iscvalue_mkc_integer.
    split.
    unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m2 n2 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. apply computes_to_valc_refl. apply iscvalue_mkc_integer.
    assert (((0 <= Z.rem x x0)%Z # (0 <= Z.rem x x0)%Z # tequality lib mkc_true mkc_true)).
    split;auto; split;auto.
    auto.
  - (* equality *)

     rw @equality_in_less. exists (Z.rem x x0). exists 0%Z.
     split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m1 n1 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. apply computes_to_valc_refl. apply iscvalue_mkc_integer.
    assert ((0 <= Z.rem x x0)%Z # equality lib mkc_axiom mkc_axiom mkc_true).
    split; auto. 
    auto.
Qed.



Lemma rule_rem_negative_true {o} :
  forall lib (H : barehypotheses)
         (m n : @NTerm o),
    rule_true lib (rule_rem_negative H m n).
Proof.
  unfold rule_rem_negative, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  unfold mk_not_eqint.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hyp1; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as hyp2; clear hyp3.
  vr_seq_true in hyp4.
  pose proof (hyp4 s1 s2 eqh sim) as hyp3; clear hyp4.
  exrepnd. 
  unfold mk_less_than in hyp7.
  unfold mk_not_less_than. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw @lsubstc_mk_true .
  allrw @lsubstc_mk_false .
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp4; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  apply @equality_of_int_imp_tt in hyp4. destruct hyp4.
  apply @equality_of_int_imp_tt in hyp0. destruct hyp0.
  exrepnd.
  assert (x0 <> 0%Z) as nz. clear - hyp1 p1.
    (* from these two hyps we can prove x0 is not 0 *)
    pose proof (Z.eq_dec x0 0) as xx. destruct xx; auto. 
    assert (equality lib mkc_axiom mkc_axiom mkc_false).
    pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1. 
    specialize (r1 mkc_axiom mkc_axiom (mkc_inteq n1 (mkc_integer 0) mkc_false mkc_true) mkc_false).
    apply r1; auto.  rw e in p1. clear -p1.
    apply computes_to_valc_implies_cequivc.
    fold (@mkc_not_eqint o).
    pose proof (@mkc_not_eqint_comp1 o lib n1 (mkc_integer 0) 0 0) as xx.
     apply xx; auto.  
     apply computes_to_valc_refl. apply iscvalue_mkc_integer.  
   (* we have a member of False *)
    rw @equality_in_false in H; auto.
   (* now we have x0 not eq 0 *)
    assert (x <= 0)%Z.  clear - hyp7 p2.
    (* From these two hyps we can prove x <= 0 *) 
     pose proof (Z.le_decidable x 0) as xx. destruct xx; auto.
     assert ( 0 < x)%Z. omega. clear H.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less m1 (mkc_integer 0) mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib m1 (mkc_integer 0) x 0) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H0.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H. inversion H.
   (* Now we have x <= 0 *)
   assert (Z.rem x x0 <= 0)%Z. apply Z.rem_nonpos; auto.
  split.
  - (* tequality *) apply @tequality_mkc_less. 
    exists 0%Z. exists (Z.rem x x0). exists 0%Z. exists (Z.rem x x0).
    split. unfold ccomputes_to_valc. spcast. apply computes_to_valc_refl. apply iscvalue_mkc_integer.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m1 n1 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. apply computes_to_valc_refl. apply iscvalue_mkc_integer.
    split.
    unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m2 n2 x x0) as xx.
    apply xx; auto.
    assert  ((Z.rem x x0 <= 0)%Z # (Z.rem x x0 <= 0)%Z # tequality lib mkc_true mkc_true). 
    split;auto; split;auto.
    auto.
  - (* equality *)

     rw @equality_in_less. exists 0%Z. exists (Z.rem x x0). 
     split. unfold ccomputes_to_valc. spcast. apply computes_to_valc_refl. apply iscvalue_mkc_integer.
     split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m1 n1 x x0) as xx.
    apply xx; auto.
    
    assert ((Z.rem x x0 <= 0)%Z # equality lib mkc_axiom mkc_axiom mkc_true).
    split; auto. 
    auto.
Qed.

(* The four remaining rules specify the magnitude of (a rem b) *)

(*
   H |- less (a rem b) b True False

     By remainderBounds1

     H |- less 0 a True False
     H |- less 0 b True False
     H |- a in Z
     H |- b in Z
 *)
Definition rule_rem_bounds1 {o}
           (H : barehypotheses)
           (a b : @NTerm o) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_less_than (mk_rem a b) b)))
    [ mk_baresequent H (mk_conclax (mk_less_than (mk_integer 0) a)),
      mk_baresequent H (mk_conclax (mk_less_than (mk_integer 0) b)),
      mk_baresequent H (mk_conclax (mk_member a mk_int)),
      mk_baresequent H (mk_conclax (mk_member b mk_int))
    ]
    [].

(*
   H |- less (-b) (a rem b) True False

     By remainderBounds2

     H |- less a 0 True False
     H |- less 0 b True False
     H |- a in Z
     H |- b in Z
 *)
Definition rule_rem_bounds2 {o}
           (H : barehypotheses)
           (a b : @NTerm o) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_less_than (mk_minus b) (mk_rem a b) )))
    [ mk_baresequent H (mk_conclax (mk_less_than a (mk_integer 0))),
      mk_baresequent H (mk_conclax (mk_less_than (mk_integer 0) b)),
      mk_baresequent H (mk_conclax (mk_member a mk_int)),
      mk_baresequent H (mk_conclax (mk_member b mk_int))
    ]
    [].

(*
   H |- less b (a rem b) True False

     By remainderBounds3

     H |- less a 0 True False
     H |- less b 0 True False
     H |- a in Z
     H |- b in Z
 *)
Definition rule_rem_bounds3 {o}
           (H : barehypotheses)
           (a b : @NTerm o) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_less_than b (mk_rem a b) )))
    [ mk_baresequent H (mk_conclax (mk_less_than a (mk_integer 0))),
      mk_baresequent H (mk_conclax (mk_less_than b (mk_integer 0))),
      mk_baresequent H (mk_conclax (mk_member a mk_int)),
      mk_baresequent H (mk_conclax (mk_member b mk_int))
    ]
    [].

(*
   H |- less (a rem b) (-b) True False

     By remainderBounds4

     H |- less 0 a True False
     H |- less b 0 True False
     H |- a in Z
     H |- b in Z
 *)
Definition rule_rem_bounds4 {o}
           (H : barehypotheses)
           (a b : @NTerm o) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_less_than (mk_rem a b) (mk_minus b))))
    [ mk_baresequent H (mk_conclax (mk_less_than (mk_integer 0) a)),
      mk_baresequent H (mk_conclax (mk_less_than b (mk_integer 0))),
      mk_baresequent H (mk_conclax (mk_member a mk_int)),
      mk_baresequent H (mk_conclax (mk_member b mk_int))
    ]
    [].


Lemma rule_rem_bounds1_true {o} :
  forall lib (H : barehypotheses)
         (m n : @NTerm o),
    rule_true lib (rule_rem_bounds1 H m n).
Proof.
  unfold rule_rem_bounds1, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  unfold mk_not_eqint.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hyp1; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as hyp2; clear hyp3.
  vr_seq_true in hyp4.
  pose proof (hyp4 s1 s2 eqh sim) as hyp3; clear hyp4.
  exrepnd. 
  unfold mk_less_than in hyp7.
  unfold mk_less_than in hyp1.
  unfold mk_less_than. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw @lsubstc_mk_true .
  allrw @lsubstc_mk_false .
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp4; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  apply @equality_of_int_imp_tt in hyp4. destruct hyp4.
  apply @equality_of_int_imp_tt in hyp0. destruct hyp0.
  exrepnd.
  assert (0 < x)%Z.  clear - hyp7 p2.
    (* From these two hyps we can prove 0 < x *) 
     pose proof (Z.lt_decidable 0 x) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less (mkc_integer 0) m1 mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib (mkc_integer 0) m1 0 x) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have 0 < x *)
  assert (0 < x0)%Z.  clear - hyp1 p1.
    (* From these two hyps we can prove 0 < x0 *) 
     pose proof (Z.lt_decidable 0 x0) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less (mkc_integer 0) n1 mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib (mkc_integer 0) n1 0 x0) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have 0 < x0 *)
 
  assert (x0 <> 0%Z) as nz. omega.
  (* now we have x0 not eq 0 *)
    
   assert (Z.rem x x0 < x0)%Z. apply Z.rem_bound_pos. omega. auto.
  split.
  - (* tequality *) apply @tequality_mkc_less. 
    exists (Z.rem x x0). exists x0. exists (Z.rem x x0). exists x0. 
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m1 n1 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. auto. 
    split.
    unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m2 n2 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. auto. 
    assert  ((Z.rem x x0 < x0)%Z # (Z.rem x x0 < x0)%Z # tequality lib mkc_true mkc_true).
    split;auto; split;auto.
    auto.
  - (* equality *)

     rw @equality_in_less. exists (Z.rem x x0). exists x0.
     split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m1 n1 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. auto.
    
    assert ((Z.rem x x0 < x0)%Z # equality lib mkc_axiom mkc_axiom mkc_true).
    split; auto. 
    auto.
Qed.


Lemma rule_rem_bounds2_true {o} :
  forall lib (H : barehypotheses)
         (m n : @NTerm o),
    rule_true lib (rule_rem_bounds2 H m n).
Proof.
  unfold rule_rem_bounds2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  unfold mk_not_eqint.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hyp1; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as hyp2; clear hyp3.
  vr_seq_true in hyp4.
  pose proof (hyp4 s1 s2 eqh sim) as hyp3; clear hyp4.
  exrepnd. 
  unfold mk_less_than in hyp7.
  unfold mk_less_than in hyp1.
  unfold mk_less_than. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw @lsubstc_mk_true .
  allrw @lsubstc_mk_false .
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp4; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  apply @equality_of_int_imp_tt in hyp4. destruct hyp4.
  apply @equality_of_int_imp_tt in hyp0. destruct hyp0.
  exrepnd.
  assert (x < 0)%Z.  clear - hyp7 p2.
    (* From these two hyps we can prove  x< 0 *) 
     pose proof (Z.lt_decidable x 0) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less n1 (mkc_integer 0) mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib n1 (mkc_integer 0) x 0) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have x < 0 *)
  assert (0 < x0)%Z.  clear - hyp1 p1.
    (* From these two hyps we can prove 0 < x0 *) 
     pose proof (Z.lt_decidable 0 x0) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less (mkc_integer 0) m1 mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib (mkc_integer 0) m1 0 x0) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have 0 < x0 *)
 
  assert (x0 <> 0%Z) as nz. omega.
  (* now we have x0 not eq 0 *)
    
   assert ( -(x0) < Z.rem x x0 )%Z.  
    assert ( Z.abs (Z.rem x x0) < Z.abs x0)%Z. apply Z.rem_bound_abs; auto.
    rw Z.abs_lt in H2. rw Z.abs_eq in H2; auto. destruct H2; auto. omega.
   assert (computes_to_valc lib (mkc_minus m1) (mkc_integer (- x0))).
    pose proof (@implies_computes_to_valc_minus o lib) as xx. apply xx; auto.
  split.
  - (* tequality *) apply @tequality_mkc_less. 
     exists ((-x0)%Z). exists (Z.rem x x0). exists ((-x0)%Z). exists (Z.rem x x0).
    split. unfold ccomputes_to_valc. spcast. auto.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem n1 m1 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. 
    pose proof (@implies_computes_to_valc_minus o lib) as xx. apply xx; auto.
    split.
    unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem n2 m2 x x0) as xx.
    apply xx; auto. 
    assert ((- x0 < Z.rem x x0)%Z # (- x0 < Z.rem x x0)%Z # tequality lib mkc_true mkc_true). 
    split;auto; split;auto.
    auto.
  - (* equality *)

     rw @equality_in_less. exists ((-x0)%Z). exists (Z.rem x x0).
     split. unfold ccomputes_to_valc. spcast. auto.
     split. unfold ccomputes_to_valc. spcast. 
    pose proof (@computes_to_valc_arithop o lib ArithOpRem n1 m1 x x0) as xx.
    apply xx; auto.    
    assert ((- x0 < Z.rem x x0)%Z # equality lib mkc_axiom mkc_axiom mkc_true).
    split; auto. 
    auto.
Qed.


Lemma rule_rem_bounds3_true {o} :
  forall lib (H : barehypotheses)
         (m n : @NTerm o),
    rule_true lib (rule_rem_bounds3 H m n).
Proof.
  unfold rule_rem_bounds3, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  unfold mk_not_eqint.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hyp1; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as hyp2; clear hyp3.
  vr_seq_true in hyp4.
  pose proof (hyp4 s1 s2 eqh sim) as hyp3; clear hyp4.
  exrepnd. 
  unfold mk_less_than in hyp7.
  unfold mk_less_than in hyp1.
  unfold mk_less_than. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw @lsubstc_mk_true .
  allrw @lsubstc_mk_false .
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp4; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  apply @equality_of_int_imp_tt in hyp4. destruct hyp4.
  apply @equality_of_int_imp_tt in hyp0. destruct hyp0.
  exrepnd.
  assert (x < 0)%Z.  clear - hyp7 p2.
    (* From these two hyps we can prove x < 0*) 
     pose proof (Z.lt_decidable x 0) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less n1 (mkc_integer 0) mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib n1 (mkc_integer 0) x 0) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have x < 0 *)
  assert (x0 < 0 )%Z.  clear - hyp1 p1.
    (* From these two hyps we can prove x0 < 0 *) 
     pose proof (Z.lt_decidable x0 0) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less m1 (mkc_integer 0) mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib m1 (mkc_integer 0) x0 0) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have x0  < 0*)
 
  assert (x0 <> 0%Z) as nz. omega.
  (* now we have x0 not eq 0 *)
    
   assert (x0 < Z.rem x x0)%Z. 
    assert ( Z.abs (Z.rem x x0) < Z.abs x0)%Z. apply Z.rem_bound_abs; auto.
    rw Z.abs_lt in H2. destruct H2. rw Z.abs_neq in H2; omega.
  split.
  - (* tequality *) apply @tequality_mkc_less. 
    exists x0. exists (Z.rem x x0). exists x0. exists (Z.rem x x0).
    split. unfold ccomputes_to_valc. spcast. auto.  
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem n1 m1 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. auto. 
    split.
    unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem n2 m2 x x0) as xx.
    apply xx; auto.
    
    assert ((x0 < Z.rem x x0)%Z # (x0 < Z.rem x x0)%Z # tequality lib mkc_true mkc_true). 
    split;auto; split;auto.
    auto.
  - (* equality *)

     rw @equality_in_less. exists x0. exists (Z.rem x x0). 
     split. unfold ccomputes_to_valc. spcast. auto.
     split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem n1 m1 x x0) as xx.
    apply xx; auto.
    assert ((x0 < Z.rem x x0)%Z # equality lib mkc_axiom mkc_axiom mkc_true).
    split; auto. 
    auto.
Qed.


Lemma rule_rem_bounds4_true {o} :
  forall lib (H : barehypotheses)
         (m n : @NTerm o),
    rule_true lib (rule_rem_bounds4 H m n).
Proof.
  unfold rule_rem_bounds4, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  unfold mk_not_eqint.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  rename Hyp3 into hyp4.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hyp1; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as hyp2; clear hyp3.
  vr_seq_true in hyp4.
  pose proof (hyp4 s1 s2 eqh sim) as hyp3; clear hyp4.
  exrepnd. 
  unfold mk_less_than in hyp7.
  unfold mk_less_than in hyp1.
  unfold mk_less_than. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw @lsubstc_mk_true .
  allrw @lsubstc_mk_false .
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp4; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  apply @equality_of_int_imp_tt in hyp4. destruct hyp4.
  apply @equality_of_int_imp_tt in hyp0. destruct hyp0.
  exrepnd.
  assert (0 < x)%Z.  clear - hyp7 p2.
    (* From these two hyps we can prove 0 < x *) 
     pose proof (Z.lt_decidable 0 x) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less (mkc_integer 0) m1 mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib (mkc_integer 0) m1 0 x) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have 0 < x *)
   assert (x0 < 0)%Z.  clear - hyp1 p1.
    (* From these two hyps we can prove x0< 0 *) 
     pose proof (Z.lt_decidable x0 0) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less n1 (mkc_integer 0) mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib n1 (mkc_integer 0) x0 0 ) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have  x0 < 0 *)
 
  assert (x0 <> 0%Z) as nz. omega.
  (* now we have x0 not eq 0 *)
    
   assert ( Z.rem x x0  < -(x0))%Z.  
    assert ( Z.abs (Z.rem x x0) < Z.abs x0)%Z. apply Z.rem_bound_abs; auto.
    rw Z.abs_lt in H2. rw Z.abs_neq in H2; auto. destruct H2; auto. omega.
   assert (computes_to_valc lib (mkc_minus n1) (mkc_integer (- x0))).
    pose proof (@implies_computes_to_valc_minus o lib) as xx. apply xx; auto.
  split.
  - (* tequality *) apply @tequality_mkc_less. 
     exists (Z.rem x x0). exists ((-x0)%Z). exists (Z.rem x x0). exists ((-x0)%Z). 
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m1 n1 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. 
    pose proof (@implies_computes_to_valc_minus o lib) as xx. apply xx; auto.
    split.
    unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m2 n2 x x0) as xx.
    apply xx; auto. 
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@implies_computes_to_valc_minus o lib) as xx. apply xx; auto.
    assert  ((Z.rem x x0 < - x0)%Z # (Z.rem x x0 < - x0)%Z # tequality lib mkc_true mkc_true).
    split;auto; split;auto.
    auto.
  - (* equality *)

     rw @equality_in_less. exists (Z.rem x x0). exists ((-x0)%Z).
    split. unfold ccomputes_to_valc. spcast. 
    pose proof (@computes_to_valc_arithop o lib ArithOpRem m1 n1 x x0) as xx.
    apply xx; auto. 
    split. unfold ccomputes_to_valc. spcast. auto.   
    assert ((Z.rem x x0 < - x0)%Z # equality lib mkc_axiom mkc_axiom mkc_true).
    split; auto. 
    auto.
Qed.
