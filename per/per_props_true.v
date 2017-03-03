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


Require Export per_props_not.


Lemma equality_in_true {o} :
  forall lib (u v : @CTerm o), equality lib u v mkc_true.
Proof.
  introv.
  rw @mkc_true_eq.
  apply equality_in_approx; spcast; eauto 2 with slow.
Qed.
Hint Resolve equality_in_true : slow.

Lemma tequality_mkc_true {o} :
  forall (lib : @library o), tequality lib mkc_true mkc_true.
Proof.
  introv; rw @mkc_true_eq.
  apply tequality_mkc_approx; sp.
Qed.
Hint Resolve tequality_mkc_true : slow.

Lemma type_mkc_true {o} :
  forall (lib : @library o), type lib mkc_true.
Proof.
  introv; rw @mkc_true_eq.
  apply fold_type.
  apply tequality_mkc_approx; sp.
Qed.
Hint Resolve type_mkc_true : slow.

Lemma true_not_equal_to_false {o} :
  forall (lib : @library o),
    !tequality lib mkc_true mkc_false.
Proof.
  introv teq.
  unfold tequality, nuprl in teq; exrepnd.
  destruct teq0 as [teq1 teq2].
  rw @mkc_true_eq in teq1.
  inversion teq1; subst; try not_univ; clear teq1.
  rw @mkc_false_eq in teq2.
  inversion teq2; subst; try not_univ; clear teq2.

  match goal with
  | [ H1 : per_approx _ _ _ _ , H2 : per_approx _ _ _ _ |- _ ] =>
    rename H1 into h; rename H2 into q
  end.

  unfold per_approx in *; exrepnd.
  computes_to_value_isvalue; GC.
  eapply eq_term_equals_trans in q1;[|apply eq_term_equals_sym;exact h1].
  pose proof (q1 (@mkc_axiom o) (@mkc_axiom o)) as w; simpl in w; auto.
  destruct w as [w w']; clear w'.
  autodimp w hyp; spcast; eauto 2 with slow.
  apply not_axiom_approxc_bot in w; sp.
Qed.
