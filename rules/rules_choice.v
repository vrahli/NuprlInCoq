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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export rules_useful.
Require Export subst_tacs_aeq.
Require Export subst_tacs3.
Require Export cequiv_tacs.
Require Export cequiv_props3.
Require Export per_props_equality.
Require Export per_props_product.
Require Export per_props_nat.
Require Export sequents_equality.
Require Export sequents_tacs2.
Require Export rules_tyfam.
Require Export lsubst_hyps.
Require Export terms_pi.
Require Export per_props_natk2nat.
Require Export fresh_cs.


Definition entry_free_from_choice_seq_name {o} (e : @library_entry o) (name : choice_sequence_name) :=
  match e with
  | lib_cs n l =>
    if choice_sequence_name_deq n name then False
    else True
  | lib_abs _ _ _ _ => True
  end.

Fixpoint lib_free_from_choice_seq_name {o} (lib : @library o) (name : choice_sequence_name) :=
  match lib with
  | [] => True
  | e :: es =>
    (entry_free_from_choice_seq_name e name)
      # lib_free_from_choice_seq_name es name
  end.

Definition sequent_true_ex_ext {o} lib (s : @csequent o) :=
  {lib' : library & lib_extends lib' lib # sequent_true lib' s}.

Definition rule_true_ex_ext {o} lib (R : @rule o) : Type :=
  forall wg : wf_sequent (goal R),
  forall cg : closed_type_baresequent (goal R),
  forall cargs: args_constraints (sargs R) (hyps (goal R)),
  forall hyps : (forall s : baresequent,
                   LIn s (subgoals R)
                   -> {c : wf_csequent s & sequent_true lib (mk_wcseq s c)}),
    {c : closed_extract_baresequent (goal R)
     & sequent_true_ex_ext lib (mk_wcseq (goal R) (ext_wf_cseq (goal R) wg cg c))}.


(**

<<
   H |- ∃ (a:Free). f = a ∈ ℕn→ℕ

     By LS1

     H |- f ∈ ℕn→ℕ
     H |- n ∈ ℕ
>>

 *)

Definition ls1 {o} (n f a : NVar) : @NTerm o :=
  mk_exists
    mk_csname
    a
    (mk_equality
       (mk_var f)
       (mk_var a)
       (mk_natk2nat (mk_var n))).

Definition ls1_extract {o} (name : choice_sequence_name) (n f : NVar) : @NTerm o :=
  mk_pair (mk_choice_seq name) mk_axiom.

(* Write a proper extract instead of axiom *)
Definition rule_ls1 {o}
           (lib   : @library o)
           (name  : choice_sequence_name)
           (n f a : NVar)
           (e1 e2 : @NTerm o)
           (H     : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ls1 n f a) (ls1_extract name n f)))
    [ mk_baresequent H (mk_concl (mk_member (mk_var f) (mk_natk2nat (mk_var n))) e1),
      mk_baresequent H (mk_concl (mk_member (mk_var n) mk_tnat) e2) ]
    [].

Lemma rule_ls1_true {o} :
  forall lib (name : choice_sequence_name) (n f a : NVar) e1 e2 (H : @bhyps o),
    rule_true_ex_ext lib (rule_ls1 lib name n f a e1 e2 H).
Proof.
  unfold rule_ls1, rule_true_ex_ext, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (@covered o (ls1_extract name n f) (nh_vars_hyps H)) as cv.
  { clear hyp1 hyp2; dwfseq; tcsp. }
  exists cv.

  (* pick a fresh choice sequence name, and define a constraint based on [hyp1] and [hyp2] *)

Qed.