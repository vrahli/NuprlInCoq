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


Require Export sequents_tacs.
Require Export per_props_tequality.
Require Export subst_tacs.
Require Export per_props_equality.
Require Export sequents_equality.

(* begin hide *)



(* end hide *)

(**

  The following rule is used to prove that [mkc_tequality] terms are
  types (equal types).
<<
   H |- (mkc_tequality T1 T2) = (mkc_tequality U1 U2) in Type(i)

     By tequalityEquality ()

     H |- T1 = U1 in Type(i)
     H |- T2 = U2 in Type(i)
     H |- T1 = T2 in Type(i)
>>
 *)

Definition rule_tequality_equality {o}
           (T1 T2 U1 U2 : @NTerm o)
           (i : nat)
           (H : barehypotheses) :=
  mk_rule
    (mk_bseq
       H
       (mk_conclax (mk_equality
                      (mk_tequality T1 T2)
                      (mk_tequality U1 U2)
                      (mk_uni i))))
    [ mk_bseq H (mk_conclax (mk_equality T1 U1 (mk_uni i))),
      mk_bseq H (mk_conclax (mk_equality T2 U2 (mk_uni i))),
      mk_bseq H (mk_conclax (mk_equality T1 T2 (mk_uni i)))
    ]
    [ ].

Lemma rule_tequality_equality_true {o} :
  forall lib (T1 T2 U1 U2 : NTerm),
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_tequality_equality
                 T1 T2 U1 U2
                 i
                 H).
Proof.
  unfold rule_tequality_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1; rename Hyp1 into hyp2; rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.

  allrw @member_eq.
  allrw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality lib
                (mk_uni i) (mk_tequality T1 T2) (mk_tequality U1 U2) s1 s2 H
                (wf_mk_uni i) w1 w2 c1 c0 c2 c3 cT cT0 eqh sim);
    intro k.
  lsubst_tac.
  apply k; clear k.

  apply tequality_mkc_uni.

  clear dependent s1.
  clear dependent s2.

  introv hf sim.

  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  vr_seq_true in hyp3.

  generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.
  generalize (hyp3 s1 s2 hf sim); clear hyp3; intro hyp3; exrepnd.
  lsubst_tac.
  proof_irr; GC.

  allrw @member_eq.
  allrw <- @member_equality_iff.
  apply mkc_tequality_equality_in_uni.
  dands; auto.

  apply equality_commutes4 in hyp0; auto.
  apply equality_commutes4 in hyp4; auto.
Qed.

(* begin hide *)



(* end hide *)

(**

This rule says that in an equality, a type can be replaced by an equal
types (this rule could be generalized):

<<
   H |- a = b in T

     By tequalitySubstEqual ()

     H |- (T = U)
     H |- a = b in U
>>

 *)

Definition rule_tequality_subst_equal {o}
           (a b T U : @NTerm o)
           (H : barehypotheses) :=
  mk_rule
    (mk_bseq H  (mk_conclax (mk_equality a b T)))
    [ mk_bseq H (mk_conclax (mk_tequality T U)),
      mk_bseq H (mk_conclax (mk_equality a b U))
    ]
    [ ].

Lemma rule_tequality_subst_equal_true {o} :
  forall lib (a b T U : NTerm),
  forall H : @barehypotheses o,
    rule_true lib (rule_tequality_subst_equal
                 a b T U
                 H).
Proof.
  unfold rule_tequality_subst_equal, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1; rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  exists ce0.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.

  allrw @member_eq.
  allrw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality
                lib T a b s1 s2 H
                wT w1 w2 c1 c0 c2 c3 cT cT0 eqh sim);
    intro k.
  lsubst_tac.
  apply k; clear k.

  - vr_seq_true in hyp1.
    generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
    lsubst_tac.
    clear hyp1.
    rw @tequality_mkc_tequality in hyp0; repnd; auto.

  - clear dependent s1.
    clear dependent s2.

    introv hf sim.

    vr_seq_true in hyp1.
    vr_seq_true in hyp2.

    generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.
    generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.

    clear hyp1.
    lsubst_tac.
    allrw @member_eq.
    allrw <- @member_equality_iff.
    rw @tequality_mkc_tequality in hyp0; repnd.

    apply equality_commutes4 in hyp3; auto.
    apply tequality_preserving_equality with (A := lsubstc U wT0 s1 cT); auto.
    apply tequality_sym; auto.
Qed.

(* begin hide *)




(* end hide *)

(**

The following rule says that tequality types do not have any
computational content:

<<
   H |- a = b in (T = U)

     By tequalityMember ()

     H |- (T = U)
>>

 *)

Definition rule_tequality_member {o}
           (a b T U : @NTerm o)
           (H : barehypotheses) :=
  mk_rule
    (mk_bseq H  (mk_conclax (mk_equality a b (mk_tequality T U))))
    [ mk_bseq H (mk_conclax (mk_tequality T U))
    ]
    [ ].

Lemma rule_tequality_member_true {o} :
  forall lib (a b T U : NTerm),
  forall H : @barehypotheses o,
    rule_true lib (rule_tequality_member
                 a b T U
                 H).
Proof.
  unfold rule_tequality_member, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  exists ce.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.

  allrw @member_eq.
  allrw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality
                lib (mk_tequality T U) a b s1 s2 H
                wfct0 w1 w2 c1 c0 c2 c3 cT cT0 eqh sim);
    intro k.
  lsubst_tac.
  apply k; clear k.

  - vr_seq_true in hyp1.
    generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
    lsubst_tac.
    clear hyp1; auto.

  - clear dependent s1.
    clear dependent s2.

    introv hf sim.

    vr_seq_true in hyp1.
    generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.

    clear hyp1.
    lsubst_tac.
    rw @tequality_mkc_tequality in hyp0; repnd.
    apply equality_in_mkc_tequality; auto.
Qed.

(* begin hide *)




(* end hide *)

(**

The following rule says that tequality types are well-formed only when
they're true:

<<
   H |- (T = U)

     By tequalityWf ()

     H |- (T = U) is a type
>>

 *)

Definition rule_tequality_type {o}
           (T U : @NTerm o)
           (H : barehypotheses) :=
  mk_rule
    (mk_bseq H (mk_conclax (mk_tequality T U)))
    [ mk_bseq H (mk_concl_t (mk_tequality T U))
    ]
    [ ].

Lemma rule_tequality_type_true {o} :
  forall lib (T U : NTerm),
  forall H : @barehypotheses o,
    rule_true lib (rule_tequality_type
                 T U
                 H).
Proof.
  unfold rule_tequality_type, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)); GC.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  clear hyp1.
  allrw @tequality_mkc_tequality; repnd.
  dands; auto.
  apply equality_in_mkc_tequality; auto.
Qed.

(* begin hide *)




(* end hide *)

(**

The following rule says that tequality types are symmetric:

<<
   H |- (T = U)

     By tequalitySym ()

     H |- (U = T)
>>

 *)

Definition rule_tequality_sym {o}
           (T U : @NTerm o)
           (H : barehypotheses) :=
  mk_rule
    (mk_bseq H (mk_conclax (mk_tequality T U)))
    [ mk_bseq H (mk_conclax (mk_tequality U T))
    ]
    [ ].

Lemma rule_tequality_sym_true {o} :
  forall lib (T U : NTerm),
  forall H : @barehypotheses o,
    rule_true lib (rule_tequality_sym
                 T U
                 H).
Proof.
  unfold rule_tequality_sym, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)); GC.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  clear hyp1.
  allrw @tequality_mkc_tequality; repnd.
  dands; auto.
  apply tequality_sym; auto.
  apply equality_in_mkc_tequality; auto.
  apply tequality_sym; auto.
Qed.

(* begin hide *)




Lemma tequality_member_uni {o} :
  forall lib A B i,
    @tequality o lib A B
    -> member lib A (mkc_uni i)
    -> member lib B (mkc_uni i)
    -> equality lib A B (mkc_uni i).
Proof.
  introv teq mem1 mem2.
  unfold member, equality in mem1; exrepnd.
  unfold member, equality in mem2; exrepnd.
  unfold tequality in teq; exrepnd.

Abort.


(**

The following rule allows one to weaken [mk_tequality] types to
[mk_equality] types in some universe.

<<
   H |- (T = U) in Type(i)

     By tequalityWeak ()

     H |- T in Type(i)
     H |- U in Type(i)
     H |- (T = U)
>>

 *)

Definition rule_tequality_weak {o}
           (T U : @NTerm o)
           (i : nat)
           (H : barehypotheses) :=
  mk_rule
    (mk_bseq H (mk_conclax (mk_equality T U (mk_uni i))))
    [ mk_bseq H (mk_conclax (mk_member T (mk_uni i))),
      mk_bseq H (mk_conclax (mk_member U (mk_uni i))),
      mk_bseq H (mk_conclax (mk_tequality T U))
    ]
    [ ].

Lemma rule_tequality_weak_true {o} :
  forall lib (T U : NTerm),
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_tequality_weak
                 T U
                 i
                 H).
Proof.
  unfold rule_tequality_weak, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1; rename Hyp1 into hyp2; rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)); GC.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  allrw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality
                lib (mk_uni i) T U s1 s2 H
                (wf_mk_uni i) w1 w2 c1 c0 c2 c3 cT cT0 eqh sim);
    intro k.
  lsubst_tac.
  apply k; clear k.

  apply tequality_mkc_uni.

  clear dependent s1.
  clear dependent s2.

  introv hf sim.

  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  vr_seq_true in hyp3.
  generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.
  generalize (hyp3 s1 s2 hf sim); clear hyp3; intro hyp3; exrepnd.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_member_iff.
  apply equality_in_mkc_tequality in hyp3.
  rw @tequality_mkc_tequality in hyp5; repnd.

Abort.
