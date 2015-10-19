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


(* contains an alternate definition of alphaeq in terms of variable swapping: *)
Require Import swap.


(* contains a proof that n:Nat->Univ(n) is a Nuprl type: *)
Require Import function_all_types.
(* contains a proof that U(n:Nat;Univ(n)) is a Nuprl type: *)
Require Import union_all_types.


(* Rules(structural): *)
Require Import rules_struct.
Require Import rules_move.


(* Bar Induction on nats: *)
Require Import bar_induction3.
(* Bar Induction on sequences of closed terms without atoms: *)
Require Import bar_induction_cterm2.

(* Require Import rules_barind. *)


(* Axiom of Choice: *)
Require Import axiom_choice.
(*Require Import axiom_choice2.*)


(* Rules(squiggle): *)
Require Import rules_squiggle.
Require Import rules_squiggle2.
Require Import rules_squiggle3.
Require Import rules_squiggle4.
Require Import rules_squiggle5.


(* Rules(exception): *)
Require Import rules_exception.
Require Import rules_exception2.
Require Import rules_decide_exception.
Require Import rules_arith_exception.
Require Import rules_cft_exception.
Require Import rules_apply_exception.
Require Import rules_cbv_exception.
Require Import rules_less_exception.


(* Rules(callbyvalue): *)
Require Import rules_arith_callbyvalue.
Require Import rules_apply_callbyvalue.
Require Import rules_cft_callbyvalue.
Require Import rules_halts_spread.


(* Cases rules for canonical form tests *)
Require Import rules_cft.
Require Import rules_inl_inr_cases.
Require Import rules_axiom_cases.


(* Arithmetic Rules *)
Require Import rules_integer_ring.


(* Continuity axiom and rule: *)
Require Import continuity_roadmap.


(* Functionality rules *)
Require Import rules_functionality.


(* Set type *)
Require Import rules_set.


(* Equality type *)
Require Import rules_equality.
Require Import rules_equality2.
Require Import rules_equality3.


(* Type equality type *)
Require Import rules_tequality.


(* Intersection type *)
Require Import rules_isect.
Require Import rules_isect2.


(* A few lemmas using our verified rules *)
Require Import nuprl_lemmas1.
Require Import nuprl_lemmas2.


(* Function/pi type *)
Require Import rules_function.


(* Product/sum type *)
Require Import rules_product.


(* Image type *)
Require Import rules_image.


(* PER types *)
Require Import rules_pertype.
Require Import rules_ipertype.
Require Import rules_spertype.
Require Import rules_iper_function.


(* W type *)
Require Import rules_w.
Require Import rules_pw3.


(* classical rules *)
Require Import rules_classical.


(* Domain theory *)
Require Import rules_partial.
Require Import rules_mono.


(* Nominal rules *)
Require Import rules_fresh.


(* Squash rules (derivable) *)
Require Import rules_squash.


(* Rules(atoms): *)
Require Import rules_atom_atom.
Require Import rules_atom_struct.


(* Require Import rules_per_function. *)


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
