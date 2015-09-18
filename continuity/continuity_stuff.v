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
  Authors: Abhishek Anand & Vincent Rahli

*)


(**

  In continuity_rule we prove that Brouwer's weak Continuity Principle
  is true using diverging terms as computational effects:
  see lemma [rule_continuity_true] which is a proof that the rule
  [rule_continuity] is true.

  The proof of this rule uses the following meta-result: [continuity_axiom]
  which is in continuity_axiom2.  We go in several steps.  The first and
  final steps use typing in order to add constraints to our terms so that
  we can do the rest of the proof purely computationally.

  The second step is [comp_force_int_app_F_c], which is also in continuity_axiom2,
  and which is the closed version of [comp_force_int_app_F], which is in continuity.

  The third step is [comp_force_int_app_F3_c], which is also in continuity_axiom2,
  and which is the closed version of [comp_force_int_app_F3], which is in continuity3_2.

  The fourth step is [comp_force_int_app_F2_c], which is also in continuity_axiom2,
  and which is the closed version of [comp_force_int_app_F2], which is in continuity2_2.

  These three computational steps use a non-strict lock-step simulation method:

*)

Require Export continuity_rule.


(**

   stronger_continuity_rule4_v3 contains our proof that Brouwer's strong
   Continuity Principle is true: see lemma [rule_strong_continuity_true2_v3_2]
   that proves that rule [rule_strong_continuity2_v3_2] is true.
   In that rule, the existential quantifier that asserts the existence of
   a modulus of continuity function [M] is truncated using [mk_psquash]
   The other (inner) existential is squashed using our regular squash operator
   [mk_squash].

   In stronger_continuity_rule4_v2, we proved the same thing but where
   both existential quantifiers are squashed using [mk_squash].

   Both of these are for sequences from nat to subtypes of nat.
   We have a prove in stronger_continuity_rule4 for functions from nat to nat.

   This strong continuity principle consists of a well-formedness lemma, and
   two conditions.
   The well-formedness lemma is [spM_in_modulus_fun_type_u] in
   stronger_continuity_defs4.
   The first condition is [spM_cond] in stronger_continuity_defs4.
   The second condition is [spM_cond2] in stronger_continuity_rule3.

 *)

Require Export stronger_continuity_rule4_v3.


(**

  In stronger_continuity_props1, we show how to prove that [mk_fresh] is
  a member of a function type: [fresh_in_function].

*)

Require Export stronger_continuity_props1.


(*Require Import continuity_axiom.*) (* !TO FIX---don't need anymore, we've got the strong version *)
(*Require Import continuity_rule2. (* Can't prove that, right? *) *)
(*
Require Import stronger_continuity_rule4.
Require Import stronger_continuity_rule4_v2. (* slightly more general than rule4, uses a meta-hypothesis *)
Require Import stronger_continuity_rule4_v2_2. (* slightly more general than rule4, uses an object-hypothesis (subtype of nat) *)
*)



(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
