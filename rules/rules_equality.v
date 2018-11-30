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


Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_equality_more.
Require Export per_props_union.
Require Export subst_tacs.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)

(* begin hide *)




(* end hide *)


(**

  The following rule tells us that if two equality types are equal
   then their types are equal.
  
<<
   H |- A = B in U(i)

     By equalityEqualityElim a1 a2 b1 b2

   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

    
>>
 *)
Definition rule_equality_equality_elim {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 : NTerm)
           (i : nat) :=
    mk_rule
    (mk_baresequent H (mk_conclax (mk_equality A B (mk_uni i))))
    [ mk_baresequent H (mk_conclax (mk_equality
                            (mk_equality a1 a2 A)
                            (mk_equality b1 b2 B)
                            (mk_uni i)))
    ]
    [].
 

Lemma rule_equality_equality_elim_true {o} :
  forall lib (H: @barehypotheses o)
         (A B a1 a2 b1 b2: NTerm)
         (i : nat),
    rule_true lib (rule_equality_equality_elim H A B a1 a2 b1 b2 i).
Proof.
  unfold rule_equality_equality_elim, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destseq; allsimpl; proof_irr; GC.
 

  assert (closed_extract H (mk_conclax (mk_equality A B (mk_uni i)))) as cex.
   clear hyp1.
  unfold closed_extract; allsimpl.
  allrw @nh_vars_hyps_app; allrw @nh_vars_hyps_snoc; allsimpl; auto.
  exists cex.
  vr_seq_true.
  lsubst_tac.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as h.
  clear hyp1; rename h into hyp1.
  exrepnd.
  lsubst_tac.
  
  apply tequality_mkc_equality in hyp0.
  repnd.

  rw <- @member_equality_iff in hyp1.
  dup hyp1 as hh. apply equality_sym in hh. apply equality_refl in hh. 
  apply hyp0 in hh. clear hyp0.
  apply equality_mkc_equality2_sp_in_uni in hh.
  dup hyp1 as h2.
  apply equality_refl in h2. 
  apply hyp4 in h2. clear hyp4.
  apply equality_mkc_equality2_sp_in_uni in h2.
  apply equality_mkc_equality2_sp_in_uni in hyp1.
  repnd.
  split.
  - apply tequality_mkc_equality_if_equal; auto.
  - rw <- @member_equality_iff; auto.
Qed.
