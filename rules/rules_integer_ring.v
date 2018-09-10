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


Require Export computation_arith.
Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_nat.
Require Export per_can.
Require Export per_props_top.
Require Export integer_type.
Require Export terms_arith.

Lemma mkc_integer_eq_iff {o} :
  forall a b, @mkc_integer o a = mkc_integer b <-> a = b.
Proof. intros; split; introv H.
   -  apply @mkc_integer_eq in H; auto. 
   - subst. auto.
Qed.

 

(*
   H |- (m+n)+k = m+(n+k) in Z

     By addAssociative 

     H |- m in Z
     H |- n in Z
     H |- k in Z
 *)
Definition rule_add_associative {o}
           (H : barehypotheses)
           (m n k: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_add (mk_add m n) k) (mk_add m (mk_add n k)) mk_int)))
    [ mk_baresequent H (mk_conclax (mk_member m mk_int)), 
      mk_baresequent H (mk_conclax (mk_member n mk_int)), 
      mk_baresequent H (mk_conclax (mk_member k mk_int))
    ]
    [].


(*
   H |- (m*n)*k = m*(n*k) in Z

     By mulAssociative 

     H |- m in Z
     H |- n in Z
     H |- k in Z
 *)
Definition rule_mul_associative {o}
           (H : barehypotheses)
           (m n k: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_mul (mk_mul m n) k) (mk_mul m (mk_mul n k)) mk_int)))
    [ mk_baresequent H (mk_conclax (mk_member m mk_int)), 
      mk_baresequent H (mk_conclax (mk_member n mk_int)), 
      mk_baresequent H (mk_conclax (mk_member k mk_int))
    ]
    [].


(*
   H |- m*(n+k) = (m*n) + (m*k) in Z

     By mulDistributive 

     H |- m in Z
     H |- n in Z
     H |- k in Z
 *)
Definition rule_mul_distributive {o}
           (H : barehypotheses)
           (m n k: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_mul m (mk_add n k)) 
                        (mk_add (mk_mul m n) (mk_mul m k)) mk_int)))
    [ mk_baresequent H (mk_conclax (mk_member m mk_int)), 
      mk_baresequent H (mk_conclax (mk_member n mk_int)), 
      mk_baresequent H (mk_conclax (mk_member k mk_int))
    ]
    [].


(*
   H |- m + (n - m) = n in Z

     By addInverse 
 
     H |- m in Z
     H |- n in Z
 *)
Definition rule_add_inverse {o}
           (H : barehypotheses)
           (m n: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax 
                       (mk_equality (mk_add m (mk_sub n m)) 
                                     n mk_int)))
    [ mk_baresequent H (mk_conclax (mk_member m mk_int)), 
      mk_baresequent H (mk_conclax (mk_member n mk_int))
    ]
    [].


(*
   H |- m op n = m op n in Z

     By arithopEquality 

     H |- m in Z
     H |- n in Z
    
 *)
Definition rule_arithop_equality {o}
           (H : barehypotheses)
           op
           (m n: @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_arithop op m n) (mk_arithop op m n) mk_int)))
    [ mk_baresequent H (mk_conclax (mk_member m mk_int)), 
      mk_baresequent H (mk_conclax (mk_member n mk_int))
    ]
    [].


(*
   H |- (m+n) = (n+m) in Z

     By addCommutative 

     H |- m in Z
     H |- n in Z
 *)
Definition rule_add_commutative {o}
           (H : barehypotheses)
           (m n : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_add m n) (mk_add n m ) mk_int)))
    [ mk_baresequent H (mk_conclax (mk_member m mk_int)), 
      mk_baresequent H (mk_conclax (mk_member n mk_int))
    ]
    [].


(*
   H |- (m*n) = (n*m) in Z

     By mullCommutative 

     H |- m in Z
     H |- n in Z
 *)
Definition rule_mul_commutative {o}
           (H : barehypotheses)
           (m n : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_mul m n) (mk_mul n m ) mk_int)))
    [ mk_baresequent H (mk_conclax (mk_member m mk_int)), 
      mk_baresequent H (mk_conclax (mk_member n mk_int))
    ]
    [].

(*
   H |- (0+n) = n in Z

     By addZero 

     H |- n in Z
 *)
Definition rule_add_zero {o}
           (H : barehypotheses)
           (n : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_add (mk_integer 0) n) n mk_int)))
    [ mk_baresequent H (mk_conclax (mk_member n mk_int)) ]
    [].


(*
   H |- (1*n) = n in Z

     By mulOne 

     H |- n in Z
 *)
Definition rule_mul_one {o}
           (H : barehypotheses)
           (n : @NTerm o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_mul (mk_integer 1) n) n  mk_int)))
    [ mk_baresequent H (mk_conclax (mk_member n mk_int)) ]
    [].


Lemma rule_arithop_equality_true {o} :
  forall lib (H : barehypotheses) op
         (m n : @NTerm o),
    rule_true lib (rule_arithop_equality H op m n).
Proof.
  unfold rule_arithop_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  lsubst_tac.
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp2; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
(*
 assert (equality_of_int lib (mkc_arithop op m1 n1)
          (mkc_arithop op m2 n2)) by (apply @equality_of_int_arithop; auto).
 *) split.

  - (* tequality *) apply @tequality_mkc_equality_sp; split.
    apply tequality_int. split; left; apply equality_in_int; 
    auto; apply equality_of_int_arithop; auto.
 
  - (* equality *)
     rw @member_eq. rw <- @member_equality_iff.
     rw @equality_in_int. 
      clear dependent n2. clear dependent m2.
      allrw @member_int_iff. spcast. exrepnd.
      exists (get_arith_op op z z0). sp; spcast; apply computes_to_valc_arithop; auto.
Qed.


Lemma rule_add_associative_true {o} :
  forall lib (H : barehypotheses)
         (m n k : @NTerm o),
    rule_true lib (rule_add_associative H m n k).
Proof.
  unfold rule_add_associative, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hyp1; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as hyp2; clear hyp3.
  exrepnd. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp4; auto.
  apply (@tequality_member_int o) in hyp3; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms k1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  generalize_lsubstc_terms k2.
  split.
  - (* tequality *) apply @tequality_mkc_equality_sp; split.
    + apply tequality_int.
    + split; left; apply equality_in_int; auto;
      repeat (apply @equality_of_int_arithop; auto).
 
  - (* equality *)
     rw @member_eq. rw <- @member_equality_iff.
     rw @equality_in_int. 
     clear dependent k2. clear dependent n2. clear dependent m2.
    allrw @member_int_iff. spcast. exrepnd.
   unfold equality_of_int.
   assert ((z + z0 + z1)%Z = (z + (z0 + z1))%Z) as eq by omega.
   exists (z + z0 + z1)%Z. sp; auto; spcast;
     [ | rw eq]; repeat (apply computes_to_valc_arithop;auto).
Qed.

Lemma rule_add_commutative_true {o} :
  forall lib (H : barehypotheses)
         (m n : @NTerm o),
    rule_true lib (rule_add_commutative H m n).
Proof.
  unfold rule_add_commutative, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp2; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  split.
  - (* tequality *) apply @tequality_mkc_equality_sp; split.
    + apply tequality_int.
    + split; left; apply equality_in_int; auto;
      repeat (apply @equality_of_int_arithop; auto).
 
  - (* equality *)
     rw @member_eq. rw <- @member_equality_iff.
     rw @equality_in_int. 
     clear dependent n2. clear dependent m2.
    allrw @member_int_iff. spcast. exrepnd.
   unfold equality_of_int.
   assert ((z + z0)%Z = (z0 + z)%Z) as eq by omega.
   exists (z + z0)%Z. sp; auto; spcast;
     [ | rw eq]; repeat (apply computes_to_valc_arithop;auto).
Qed.

Lemma rule_mul_associative_true {o} :
  forall lib (H : barehypotheses)
         (m n k : @NTerm o),
    rule_true lib (rule_mul_associative H m n k).
Proof.
  unfold rule_mul_associative, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hyp1; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as hyp2; clear hyp3.
  exrepnd. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp4; auto.
  apply (@tequality_member_int o) in hyp3; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms k1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  generalize_lsubstc_terms k2.
  split.
  - (* tequality *) apply @tequality_mkc_equality_sp; split.
    + apply tequality_int.
    + split; left; apply equality_in_int; auto;
      repeat (apply @equality_of_int_arithop; auto).
 
  - (* equality *)
     rw @member_eq. rw <- @member_equality_iff.
     rw @equality_in_int. 
     clear dependent k2. clear dependent n2. clear dependent m2.
    allrw @member_int_iff. spcast. exrepnd.
   unfold equality_of_int.
   assert ((z * z0 * z1)%Z = (z * (z0 * z1))%Z) as eq by (rw Z.mul_assoc;auto).
   exists (z * z0 * z1)%Z. sp; auto; spcast;
     [ | rw eq]; repeat (apply computes_to_valc_arithop;auto).
Qed.

Lemma rule_mul_distributive_true {o} :
  forall lib (H : barehypotheses)
         (m n k : @NTerm o),
    rule_true lib (rule_mul_distributive H m n k).
Proof.
  unfold rule_mul_distributive, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hyp1; clear hyp2.
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as hyp2; clear hyp3.
  exrepnd. 
  fold_mk_arithop. 
  lsubst_tac.
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp4; auto.
  apply (@tequality_member_int o) in hyp3; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms k1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  generalize_lsubstc_terms k2.
  split.
  - (* tequality *) apply @tequality_mkc_equality_sp; split.
    + apply tequality_int.
    + split; left; apply equality_in_int; auto;
      repeat (apply @equality_of_int_arithop; auto).
 
  - (* equality *)
     rw @member_eq. rw <- @member_equality_iff.
     rw @equality_in_int. 
     clear dependent k2. clear dependent n2. clear dependent m2.
    allrw @member_int_iff. spcast. exrepnd.
   unfold equality_of_int.
   assert ((z * (z0 + z1))%Z = ((z * z0) + (z * z1))%Z) as eq by (rw Z.mul_add_distr_l;auto).
   exists (z * (z0 + z1))%Z. sp; auto; spcast;
     [ | rw eq]; repeat (apply computes_to_valc_arithop;auto).
Qed.


Lemma rule_mul_commutative_true {o} :
  forall lib (H : barehypotheses)
         (m n : @NTerm o),
    rule_true lib (rule_mul_commutative H m n).
Proof.
  unfold rule_mul_commutative, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp2; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  split.
  - (* tequality *) apply @tequality_mkc_equality_sp; split.
    + apply tequality_int.
    + split; left; apply equality_in_int; auto;
      repeat (apply @equality_of_int_arithop; auto).
 
  - (* equality *)
     rw @member_eq. rw <- @member_equality_iff.
     rw @equality_in_int. 
     clear dependent n2. clear dependent m2.
    allrw @member_int_iff. spcast. exrepnd.
   unfold equality_of_int.
   assert ((z * z0)%Z = (z0 * z)%Z) as eq by(rw Z.mul_comm;auto).
   exists (z * z0)%Z. sp; auto; spcast;
     [ | rw eq]; repeat (apply computes_to_valc_arithop;auto).
Qed.

Lemma rule_add_inverse_true {o} :
  forall lib (H : barehypotheses)
         (m n : @NTerm o),
    rule_true lib (rule_add_inverse H m n).
Proof.
  unfold rule_add_inverse, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp2; auto.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms m1.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms m2.
  generalize_lsubstc_terms n2.
  split.
  - (* tequality *) apply @tequality_mkc_equality_sp; split.
    + apply tequality_int.
    + split; left; apply equality_in_int; auto;
      repeat (apply @equality_of_int_arithop; auto).
 
  - (* equality *)
     rw @member_eq. rw <- @member_equality_iff.
     rw @equality_in_int. 
     clear dependent n2. clear dependent m2.
    allrw @member_int_iff. spcast. exrepnd.
   unfold equality_of_int.
   exists z0.
   sp; auto; spcast; auto.
   assert ( (mkc_integer z0) = @mkc_integer o (z + (z0 - z))) as eq by 
     (apply mkc_integer_eq_iff; omega).
     rw eq; repeat (apply computes_to_valc_arithop;auto).
Qed.


Lemma rule_mul_one_true {o} :
  forall lib (H : barehypotheses)
         (n : @NTerm o),
    rule_true lib (rule_mul_one H n).
Proof.
  unfold rule_mul_one, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd. 
  fold_mk_arithop. 
  lsubst_tac. 

  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms n2.
  split.
  - (* tequality *) apply @tequality_mkc_equality_sp; split.
    + apply tequality_int.
    + split; left; apply equality_in_int; auto;
      repeat (apply @equality_of_int_arithop; auto).
     apply equality_of_int_mkc_integer; auto.
 
  - (* equality *)
     rw @member_eq. rw <- @member_equality_iff.
     rw @equality_in_int. 
     clear dependent n2.
    allrw @member_int_iff. spcast. exrepnd.
   unfold equality_of_int.
   assert (mkc_integer (1 * z) = @mkc_integer o z) as eq by
     (apply mkc_integer_eq_iff; omega).
    exists z; sp; spcast; auto.
    rw<- eq. apply @computes_to_valc_arithop; auto.
    apply computes_to_valc_refl.
    apply iscvalue_mkc_integer.

Qed.



Lemma rule_add_zero_true {o} :
  forall lib (H : barehypotheses)
         (n : @NTerm o),
    rule_true lib (rule_add_zero H n).
Proof.
  unfold rule_add_zero, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd. 
  fold_mk_arithop. 
  lsubst_tac. 

  allrw (@equality_in_member o).
  exrepnd.
  apply (@tequality_member_int o) in hyp0; auto.
  generalize_lsubstc_terms n1.
  generalize_lsubstc_terms n2.
  split.
  - (* tequality *) apply @tequality_mkc_equality_sp; split.
    + apply tequality_int.
    + split; left; apply equality_in_int; auto;
      repeat (apply @equality_of_int_arithop; auto).
     apply equality_of_int_mkc_integer; auto.
 
  - (* equality *)
     rw @member_eq. rw <- @member_equality_iff.
     rw @equality_in_int. 
     clear dependent n2.
    allrw @member_int_iff. spcast. exrepnd.
   unfold equality_of_int.
   assert (mkc_integer (0 + z) = @mkc_integer o z) as eq by
     (apply mkc_integer_eq_iff; omega).
    exists z; sp; spcast; auto.
    rw<- eq. apply @computes_to_valc_arithop; auto.
    apply computes_to_valc_refl. 
    apply iscvalue_mkc_integer.

Qed.
