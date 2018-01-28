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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export approx_props2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export per_props_nat.
Require Export per_can.
(*Require Export per_props_top.*)
Require Export computation_arith.


Lemma computes_to_integer_member_int {o} :
   forall lib (z : Z) (t : CTerm),
   computes_to_valc lib t (mkc_integer z) -> member lib t (@mkc_int o).
Proof.
  unfold member, equality; sp.
  exists (@equality_of_int_bar o lib);sp; eauto 3 with slow.
  exists (trivial_bar lib).
  apply implies_all_in_bar_trivial_bar.
  introv xt.
  exists z; dands; spcast; eauto 3 with slow.
Qed.

Lemma member_int_iff {o} :
   forall lib  (t : CTerm),
   member lib t (@mkc_int o) <-> all_in_ex_bar lib (fun lib => {z : Z ,  ccomputes_to_valc lib t (mkc_integer z)}).
Proof.
  intros; split; intro k.
  { apply equality_in_int in k.
    eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k; introv xt k.
    unfold equality_of_int in k; exrepnd.
    exists k0; dands; auto. }
  { apply equality_in_int.
    eapply all_in_ex_bar_modus_ponens1;[|exact k]; clear k; introv xt k; exrepnd.
    exists z; dands; auto. }
Qed.

Lemma  cequiv_member_int {o} :
  forall lib (z :Z) (a b : CTerm),
   cequivc lib a b ->
   computes_to_valc lib a (mkc_integer z) ->
   tequality lib (mkc_member a (@mkc_int o)) (mkc_member b (@mkc_int o)).
Proof.
  introv ceq compa.
  apply tequality_mkc_member_sp; dands; eauto 3 with slow.
  eapply cequivc_integer in ceq;[|eauto].
  apply in_ext_implies_all_in_ex_bar; introv xt; right.
  eapply ccequivc_ext_trans;[apply computes_to_valc_implies_ccequivc_ext; eauto 3 with slow|].
  apply ccequivc_ext_sym; eauto 3 with slow.
Qed.

Lemma tequality_member_int {o} :
  forall lib (t1 t2: CTerm),
    tequality lib (mkc_member t1 mkc_int) (mkc_member t2 (@mkc_int o))
    -> member lib t1 mkc_int
    -> equality_of_int_bar lib t1 t2.
Proof.
  introv teq mem.
  apply equality_in_int.
  apply tequality_mkc_member_sp in teq; repnd.
  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact teq]; clear teq; introv xt teq; exrepnd.
  repndors; auto.
  eapply equality_respects_cequivc_right;[eauto|].
  eauto 3 with slow.
Qed.


Lemma  computes_to_value_arithop {o} :
  forall lib op (a b : (@NTerm o)) i j,
   (a =v>(lib) (mk_integer i))->
   (b =v>(lib)  (mk_integer j))->
   ((mk_arithop op a b) =v>(lib) (mk_integer (get_arith_op op i j))).
Proof. introv ai bj. allunfold @computes_to_value; exrepnd; split; eauto 3 with slow.
    apply reduces_to_arithop; auto. 
Qed.

Lemma  computes_to_valc_arithop {o} :
  forall lib op (a b : (@CTerm o)) i j,
   computes_to_valc lib a (mkc_integer i)->
   computes_to_valc lib b (mkc_integer j)->
  computes_to_valc lib (mkc_arithop op a b) (mkc_integer (get_arith_op op i j)).
Proof. introv ai bj. allunfold @computes_to_valc.
       destruct a. destruct b. allsimpl.
       apply computes_to_value_arithop; auto. 
Qed.

Lemma  ccomputes_to_valc_arithop {o} :
  forall lib op (a b : (@CTerm o)) i j,
   a ===>( lib)(mkc_integer i)->
   b ===>( lib)(mkc_integer j)->
  (mkc_arithop op a b) ===>( lib)(mkc_integer (get_arith_op op i j)).
Proof.
  unfold ccomputes_to_valc; introv ai bj.
  destruct ai. destruct bj. constructor.
  apply computes_to_valc_arithop; auto.
Qed.

Lemma equality_of_int_arithop {o} :
  forall lib op (a b c d: (@CTerm o)),
   equality_of_int lib a b ->
   equality_of_int lib c d ->
   equality_of_int lib (mkc_arithop op a c) (mkc_arithop op b d).
Proof.
    introv ab cd. allunfold @equality_of_int. exrepnd.
    exists (get_arith_op op k0 k); split; apply ccomputes_to_valc_arithop; auto.
Qed.

Lemma equality_of_int_mkc_integer {o} :
  forall lib  i j,
  equality_of_int lib (mkc_integer i) (@mkc_integer o j) <-> i = j.
Proof.  intros; split; introv H.
  - unfold equality_of_int in H; exrepnd; spcast.
    allunfold @computes_to_valc. allunfold @get_cterm. allunfold @mkc_integer.
    allunfold @computes_to_value. sp. allapply @integer_reduces_to; subst; auto.
  - subst. unfold equality_of_int. exists j; split; spcast; apply computes_to_valc_refl;
    apply iscvalue_mkc_integer.
Qed.
