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
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Import sequents.


Lemma pointwise_implies_pairwise {o} :
  forall lib (s : @csequent o),
    AN_sequent_true_pairwise lib s -> VR_sequent_true lib s.
Proof.
  introv seq.
  unfold VR_sequent_true.
  unfold AN_sequent_true_pairwise in seq.
  introv.
  generalize (seq s1 s2); clear seq; intro seq.
  destruct (destruct_csequent s); destruct ec; exrepnd; intros sim eqh; auto.
Qed.

Definition pairwise_sequent_true {o} lib (s : @baresequent o) :=
  {c : wf_csequent s & AN_sequent_true_pairwise lib (mk_wcseq s c)}.

Definition pairwise_rule_true2 {o} lib (R : @rule o) : Type :=
  forall pwf   : pwf_sequent (goal R),
  forall cargs : args_constraints (sargs R) (hyps (goal R)),
  forall hyps  : (forall s, LIn s (subgoals R) -> pairwise_sequent_true lib s),
    pairwise_sequent_true lib (goal R).
