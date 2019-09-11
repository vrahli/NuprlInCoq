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


Require Export computation_minus.
Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_nat.
Require Export per_can.
Require Export per_props_top.
Require Export integer_type.

Definition mk_conclax_pair {p} (typ1 typ2 : @NTerm p) : conclusion :=
   mk_concl (mk_prod typ1 typ2) (mk_pair mk_axiom mk_axiom).

Lemma covered_axiom_pair :
  forall (p : POpid) (vs : list NVar), covered (mk_pair (@mk_axiom p) mk_axiom) vs.
Proof. unfold covered; sp; simpl.
Qed.

(*
   H |- a in Z /\ b in Z

     By callbyvalueArith

     H |- halts (a op b)
     H |- a in Base
     H |- b in Base
 *)
Definition rule_callbyvalue_arith {o}
           (H : barehypotheses)
           (op: ArithOp )
           (a b: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax_pair (mk_member a mk_int) (mk_member b mk_int)))
    [ mk_baresequent H (mk_conclax 
       (mk_halts (mk_arithop op a b))),
     mk_baresequent H (mk_conclax 
       (mk_member  a mk_base)),
     mk_baresequent H (mk_conclax 
       (mk_member b mk_base))
    ]
    [].


Lemma rule_callbyvalue_arith_true {o} :
  forall lib (H : barehypotheses)
         op
         (a b: @NTerm o),
    rule_true lib (rule_callbyvalue_arith H op a b).
Proof.
  unfold rule_callbyvalue_arith, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom_pair o (nh_vars_hyps H)).
  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as abase; clear hyp2.
  exrepnd. 
  vr_seq_true in hyp3.
  pose proof (hyp3 s1 s2 eqh sim) as bbase; clear hyp3.
  exrepnd. 
  lsubst_tac.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms b1.
  generalize_lsubstc_terms a2.
  generalize_lsubstc_terms b2.
  apply equality_in_halts in hyp1;exrepd.
  apply tequality_mkc_halts in hyp0; lsubst_tac.
  spcast.
    rename c into hasv.
  apply hasvaluec_mkc_arithop in hasv; exrepnd.
  dup hasv0 as a1int.
  apply computes_to_integer_member_int in a1int.
  dup hasv1 as b1int. 
  apply computes_to_integer_member_int in b1int.
  apply @tequality_mkc_member_base in abase0.
  apply @tequality_mkc_member_base in bbase0.
  spcast.
  assert (equality lib a1 a2 mkc_int) as aeq by (apply equality_respects_cequivc; auto).
  assert (equality lib b1 b2 mkc_int) as beq by (apply equality_respects_cequivc; auto).
  dup aeq as a2int; apply equality_sym in a2int; apply equality_refl in a2int.
  dup beq as b2int; apply equality_sym in b2int; apply equality_refl in b2int.
  split.
  - (* tequality *)
    apply tequality_mkc_prod; split.
    + apply tequality_mkc_member; sp. apply tequality_int.
    + intro. apply tequality_mkc_member; sp. apply tequality_int.
  - (* equality *)
    apply equality_in_prod; sp;
   try apply tequality_mkc_member; sp;
   try apply tequality_int.
   eexists. eexists. eexists. eexists; sp;
   spcast; try apply computes_to_valc_refl;
   try  apply equality_in_member; sp; spcast; eauto 3 with slow.
Qed.

(*
   H |- a in Z

     By callbyvalueMinus

     H |- halts (-a)
     H |- a in Base
     
 *)
Definition rule_callbyvalue_minus {o}
           (H : barehypotheses)
           (op: ArithOp )
           (a: @NTerm o)  :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member a mk_int)))
    [ mk_baresequent H (mk_conclax 
       (mk_halts (mk_minus a))),
     mk_baresequent H (mk_conclax 
       (mk_member  a mk_base))
    ]
    [].


Lemma rule_callbyvalue_minus_true {o} :
  forall lib (H : barehypotheses)
         op
         (a: @NTerm o),
    rule_true lib (rule_callbyvalue_minus H op a).
Proof.
  unfold rule_callbyvalue_minus, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
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
  pose proof (hyp2 s1 s2 eqh sim) as abase; clear hyp2.
  exrepnd. 
  lsubst_tac.
  generalize_lsubstc_terms a1.
  generalize_lsubstc_terms a2.
  apply equality_in_halts in hyp1;exrepd.
  apply tequality_mkc_halts in hyp0; lsubst_tac.
  spcast.
    rename c into hasv.
  apply hasvaluec_mkc_minus in hasv; exrepnd.
  dup hasv0 as a1int.
  apply computes_to_integer_member_int in a1int.
  apply @tequality_mkc_member_base in abase0.
  spcast.
  assert (equality lib a1 a2 mkc_int) as aeq by (apply equality_respects_cequivc; auto).
  dup aeq as a2int; apply equality_sym in a2int; apply equality_refl in a2int.
  split.
  - (* tequality *)
   apply tequality_mkc_member; sp. apply tequality_int.
  - (* equality *)
   apply equality_in_member. sp; spcast; eauto 3 with slow.
Qed.
  
(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
