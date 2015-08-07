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


Require Export computation_cft.
Require Export computation_cbv.
Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_nat.
Require Export per_can.
Require Export per_props_top.
Require Export integer_type.


(*
   H |- halts(t)

     By callbyvalueCantest

     H |- halts (if t is ... then u else v)
    
 *)
Definition rule_callbyvalue_can_test {o}
           (H : barehypotheses)
           test
           (t u v: @NTerm o)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_halts t) ))
    [ mk_baresequent H (mk_conclax 
       (mk_halts (mk_can_test test t u v)))
    ]
    [].

(*
   H |- halts(t)

     By callbyvalueCallbyvalue

     H |- halts (eval x=t in b)
    
 *)
Definition rule_callbyvalue_cbv {o}
           (H : barehypotheses)
           (t b: @NTerm o)
           (x : NVar)
            :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_halts t) ))
    [ mk_baresequent H (mk_conclax 
       (mk_halts (mk_cbv  t x b)))
    ]
    [].



Lemma rule_callbyvalue_can_test_true {o} :
  forall lib (H : barehypotheses)
         test
         (t u v: @NTerm o),
    rule_true lib (rule_callbyvalue_can_test H test t u v).
Proof.
  unfold rule_callbyvalue_can_test, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
 
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd. 
  lsubst_tac.
  generalize_lsubstc_terms t1.
  generalize_lsubstc_terms t2.
  apply equality_in_halts in hyp1;exrepd.
  apply tequality_mkc_halts in hyp0; lsubst_tac.
  spcast.
  rename c into hasv.
  revert hyp0.
  generalize_lsubstc_terms u1.
  generalize_lsubstc_terms v1.
  generalize_lsubstc_terms u2.
  generalize_lsubstc_terms v2.
  introv hyp.
  assert (chaltsc lib (mkc_can_test test t1 u1 v1)) as ch1 by (spcast; auto).
  assert (chaltsc lib (mkc_can_test test t2 u2 v2)) as ch2 by (apply hyp; auto).
  spcast.
  apply hasvaluec_mkc_can_test in ch1.
  apply hasvaluec_mkc_can_test in ch2.
  split.
  - (* tequality *)
    apply tequality_mkc_halts. split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_halts; sp; spcast; auto.
Qed.


Lemma rule_callbyvalue_cbv_true {o} :
  forall lib (H : barehypotheses)
         (t b: @NTerm o)
         (x : NVar),
    rule_true lib (rule_callbyvalue_cbv H t b x).
Proof.
  unfold rule_callbyvalue_cbv, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
 
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom o (nh_vars_hyps H)).
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as hyp; clear hyp1.
  exrepnd. 
  lsubst_tac.
  generalize_lsubstc_terms t1.
  generalize_lsubstc_terms t2.
  apply equality_in_halts in hyp1;exrepd.
  apply tequality_mkc_halts in hyp0; lsubst_tac.
  spcast.
  rename c into hasv.
  assert (chaltsc lib (mkc_cbv t1 x (lsubstc_vars b w2 (csub_filter s1 [x]) [x] c2))) as ch1
           by (spcast; auto).
  assert (chaltsc lib ((mkc_cbv t2 x (lsubstc_vars b w2 (csub_filter s2 [x]) [x] c5)))) as ch2 
          by (apply hyp0; auto).
  spcast.
  apply hasvaluec_mkc_cbv in ch1.
  apply hasvaluec_mkc_cbv in ch2.
  split.
  - (* tequality *)
    apply tequality_mkc_halts. split; intro; spcast; auto.
  - (* equality *)
    apply equality_in_halts; sp; spcast; auto.
Qed.
  
(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
