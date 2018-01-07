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


(**

<<
   H |- ∀ (f : ℕn→ℕ). ∃ (a:Free). f = a ∈ ℕn→ℕ

     By LS1
>>

 *)

Definition ls1 {o} (n f a : NVar) : @NTerm o :=
  mk_function
    mk_tnat
    n
    (mk_function
       (mk_natk2nat (mk_var n))
       f
       (mk_exists
          mk_csname
          a
          (mk_equality
             (mk_var f)
             (mk_var a)
             (mk_natk2nat (mk_var n))))).

Definition ls1_extract {o} (name : choice_sequence_name) (n f : NVar) : @NTerm o :=
  mk_lam n (mk_lam f (mk_pair (mk_choice_seq name) mk_axiom)).

(* Write a proper extract instead of axiom *)
Definition rule_ls1 {o}
           (lib   : @library o)
           (name  : choice_sequence_name)
           (n f a : NVar)
           (H     : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_concl (ls1 n f a) (ls1_extract name n f)))
    []
    [].

Lemma rule_ls1_true {o} :
  forall lib (name : choice_sequence_name) (n f a : NVar) (H : @bhyps o),
    lib_free_from_choice_seq_name lib name
    -> rule_true lib (rule_ls1 lib name n f a H).
Proof.
  unfold rule_ls1, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs hyps.
  destseq; allsimpl.

  assert (@covered o (ls1_extract name n f) (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp. }

  exists cv.

Qed.