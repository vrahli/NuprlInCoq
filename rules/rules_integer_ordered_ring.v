(*
  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


Require Export rules_integer_division. 


(* To say that the integers form an ordered ring we need two rules that
   say that addition is monotonic and that the product of positive integers
   is positive.
   If we state a general form of the monotonicty of addition (that uses disjunction)
   then we can use it to prove the transitivity of (x < y).
   But it is easier to verify the rules
   if we state only a simple form of monotonicity of addition
   and add the transitivity of <  as an additional rule.
   So we have three rules for the ordered ring properies of the integers.
 *)


(*    H |- less (a + c) (b + c) True False 

     By addMonotonic

     H |- less a b True False
     H |- a in Z
     H |- b in Z
     H |- c in Z
 *)
Definition rule_add_monotonic {o}
           (H : barehypotheses)
           (a b c: @NTerm o) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_less_than (mk_add a c) (mk_add b c))))
    [ mk_baresequent H (mk_conclax (mk_less_than a b)),
      mk_baresequent H (mk_conclax (mk_member a mk_int)),
      mk_baresequent H (mk_conclax (mk_member b mk_int)),
      mk_baresequent H (mk_conclax (mk_member c mk_int))
    ]
    [].

(*
   H |- less a c True False

     By lessTransitive b

     H |- less a b True False
     H |- less b c True False
     H |- a in Z
     H |- b in Z
     H |- c in Z
 *)
Definition rule_less_transitive {o}
           (H : barehypotheses)
           (a b c: @NTerm o) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_less_than a c)))
    [ mk_baresequent H (mk_conclax (mk_less_than a b)),
      mk_baresequent H (mk_conclax (mk_less_than b c)),
      mk_baresequent H (mk_conclax (mk_member a mk_int)),
      mk_baresequent H (mk_conclax (mk_member b mk_int)),
      mk_baresequent H (mk_conclax (mk_member c mk_int))
    ]
    [].


(*    H |- less 0 (a * b) True False 

     By multiplyPositive

     H |- less 0 a True False
     H |- less 0 b True False
     H |- a in Z
     H |- b in Z
 *)
Definition rule_multiply_positive {o}
           (H : barehypotheses)
           (a b: @NTerm o) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_less_than (mk_integer 0) (mk_mul a b))))
    [ mk_baresequent H (mk_conclax (mk_less_than (mk_integer 0) a)),
      mk_baresequent H (mk_conclax (mk_less_than (mk_integer 0) b)),
      mk_baresequent H (mk_conclax (mk_member a mk_int)),
      mk_baresequent H (mk_conclax (mk_member b mk_int))
    ]
    [].

Lemma rule_add_monotonic_true {o} :
  forall lib (H : barehypotheses)
         (x y z: @NTerm o),
    rule_true lib (rule_add_monotonic H x y z).
Proof.
  unfold rule_add_monotonic, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  unfold mk_less_than. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw @lsubstc_mk_true .
  allrw @lsubstc_mk_false .
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp5; auto.
  apply (@tequality_member_int o) in hyp4; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms x1.
  generalize_lsubstc_terms z1.
  generalize_lsubstc_terms y1.
  generalize_lsubstc_terms x2.
  generalize_lsubstc_terms z2.
  generalize_lsubstc_terms y2.
  apply @equality_of_int_imp_tt in hyp5. destruct hyp5.
  apply @equality_of_int_imp_tt in hyp4. destruct hyp4.
  apply @equality_of_int_imp_tt in hyp0. destruct hyp0.
  exrepnd.
  assert (x0 < x3)%Z.  clear - hyp7 p4 p3.
    (* From these three hyps we can prove x0 < x3 *) 
     pose proof (Z.lt_decidable x0 x3) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less x1 y1 mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib x1 y1 x0 x3) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. 
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have x0 < x3 *)
  assert (x0+x4 < x3+x4)%Z. omega.
  split.
  - (* tequality *) apply @tequality_mkc_less. 
    exists (x0+x4)%Z. exists (x3+x4)%Z. exists (x0+x4)%Z. exists (x3+x4)%Z. 
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpAdd x1 z1 x0 x4) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpAdd y1 z1 x3 x4) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpAdd x2 z2 x0 x4) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpAdd y2 z2 x3 x4) as xx.
    apply xx; auto.
    assert ((x0 + x4 < x3 + x4)%Z # (x0 + x4 < x3 + x4)%Z # tequality lib mkc_true mkc_true).
    split;auto; split;auto.
    auto.
  - (* equality *)
     rw @equality_in_less. 
     exists (x0+x4)%Z. exists (x3+x4)%Z.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpAdd x1 z1 x0 x4) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpAdd y1 z1 x3 x4) as xx.
    apply xx; auto.
    assert ((x0 + x4 < x3 + x4)%Z # equality lib mkc_axiom mkc_axiom mkc_true).
    split;auto; split;auto.
    auto.
Qed.

Lemma rule_less_transitive_true {o} :
  forall lib (H : barehypotheses)
         (x y z: @NTerm o),
    rule_true lib (rule_less_transitive H x y z).
Proof.
  unfold rule_less_transitive, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  rename Hyp4 into hyp5.
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
  vr_seq_true in hyp5.
  pose proof (hyp5 s1 s2 eqh sim) as hyp4; clear hyp5.
  exrepnd. 
  unfold mk_less_than in hyp9.
  unfold mk_less_than in hyp1.
  unfold mk_less_than. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw @lsubstc_mk_true .
  allrw @lsubstc_mk_false .
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp6; auto.
  apply (@tequality_member_int o) in hyp5; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms x1.
  generalize_lsubstc_terms z1.
  generalize_lsubstc_terms x2.
  generalize_lsubstc_terms z2.
  revert hyp5.
  generalize_lsubstc_terms y1.
  generalize_lsubstc_terms y2.
  intro.
  apply @equality_of_int_imp_tt in hyp6. destruct hyp6.
  apply @equality_of_int_imp_tt in hyp5. destruct hyp5.
  apply @equality_of_int_imp_tt in hyp0. destruct hyp0.
  exrepnd.
  assert (x0 < x3)%Z.  clear - hyp9 p4 p2.
    (* From these three hyps we can prove x0 < x3 *) 
     pose proof (Z.lt_decidable x0 x3) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less x1 y1 mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib x1 y1 x0 x3) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. 
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have x0 < x3 *)
  assert (x3 < x4)%Z.  clear - hyp1 p3 p2.
    (* From these three hyps we can prove x3 < x4 *) 
     pose proof (Z.lt_decidable x3 x4) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less y1 z1 mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib y1 z1 x3 x4) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. 
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have x3 < x4 *)
  assert (x0 < x4)%Z. omega.
  split.
  - (* tequality *) apply @tequality_mkc_less. 
    exists x0%Z. exists (x4)%Z. exists (x0)%Z. exists (x4)%Z. 
    split. unfold ccomputes_to_valc. spcast. auto.
    split. unfold ccomputes_to_valc. spcast. auto.
    split. unfold ccomputes_to_valc. spcast. auto.
    split. unfold ccomputes_to_valc. spcast. auto.
    assert ((x0 < x4)%Z # (x0 < x4)%Z # tequality lib mkc_true mkc_true).
    split;auto; split;auto.
    auto.
  - (* equality *)
     rw @equality_in_less. 
     exists (x0)%Z. exists (x4)%Z.
    split. unfold ccomputes_to_valc. spcast. auto.
    split. unfold ccomputes_to_valc. spcast. auto.
    assert ((x0 < x4)%Z # equality lib mkc_axiom mkc_axiom mkc_true).
    split;auto; split;auto.
    auto.
Qed.

Lemma rule_multiply_positive_true {o} :
  forall lib (H : barehypotheses)
         (y z: @NTerm o),
    rule_true lib (rule_multiply_positive H y z).
Proof.
  unfold rule_multiply_positive, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  generalize_lsubstc_terms y1.
  generalize_lsubstc_terms z1.
  generalize_lsubstc_terms y2.
  generalize_lsubstc_terms z2.
  apply @equality_of_int_imp_tt in hyp4. destruct hyp4.
  apply @equality_of_int_imp_tt in hyp0. destruct hyp0.
  exrepnd.
  assert (0 < x)%Z.  clear - hyp7 p2.
    (* From these two hyps we can prove 0 < x *) 
     pose proof (Z.lt_decidable 0 x) as xx. destruct xx; auto.
     assert (equality lib mkc_axiom mkc_axiom mkc_false).
     pose proof (@respects_cequivc_equality o lib). destruct X. destruct p.
    unfold respects3_r in r1.
     specialize (r1 mkc_axiom mkc_axiom (mkc_less (mkc_integer 0) y1 mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib (mkc_integer 0) y1 0 x) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. 
     apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
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
     specialize (r1 mkc_axiom mkc_axiom (mkc_less (mkc_integer 0) z1 mkc_true mkc_false) mkc_false). 
     apply r1; auto. 
     apply computes_to_valc_implies_cequivc. 
     pose proof (@mkc_less_than_comp2 o lib (mkc_integer 0) z1 0 x0) as xx.
     rw @mkc_less_than_eq in xx.
     apply xx; auto. 
     apply computes_to_valc_refl. apply iscvalue_mkc_integer. clear - H.
     omega. 
    (* we have a member of False *)
    rw @equality_in_false in H0. inversion H0.
   (* Now we have 0 < x0 *)
  assert (0 < x*x0)%Z. apply Z.mul_pos_pos; auto.
  split.
  - (* tequality *) apply @tequality_mkc_less. 
    exists 0%Z. exists (x*x0)%Z. exists (0)%Z. exists (x*x0)%Z. 
    split. unfold ccomputes_to_valc. spcast. apply computes_to_valc_refl. apply iscvalue_mkc_integer.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpMul y1 z1 x x0) as xx.
    apply xx; auto.
    split. unfold ccomputes_to_valc. spcast. apply computes_to_valc_refl. apply iscvalue_mkc_integer.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpMul y2 z2 x x0) as xx.
    apply xx; auto.
    assert ((0 < x * x0)%Z # (0 < x * x0)%Z # tequality lib mkc_true mkc_true).
    split;auto; split;auto.
    auto.
  - (* equality *)
     rw @equality_in_less. 
     exists 0%Z. exists (x*x0)%Z. 
    split. unfold ccomputes_to_valc. spcast. apply computes_to_valc_refl. apply iscvalue_mkc_integer.
    split. unfold ccomputes_to_valc. spcast.
    pose proof (@computes_to_valc_arithop o lib ArithOpMul y1 z1 x x0) as xx.
    apply xx; auto.
    assert ((0 < x * x0)%Z # equality lib mkc_axiom mkc_axiom mkc_true).
    split;auto; split;auto.
    auto.
Qed.



