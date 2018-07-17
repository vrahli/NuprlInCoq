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


  Websites: http://nuprl.org/html/verification
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli
           Abhishek Anand
           Mark Bickford

*)


(* contains an alternate definition of sosub: *)
Require Import sosub_variant.


(* contains an alternate definition of alphaeq in terms of variable swapping: *)
Require Import swap.


Require Import rules_all.


(* contains a proof that n:Nat->Univ(n) is a Nuprl type: *)
Require Import function_all_types.
(*
(* contains a proof that U(n:Nat;Univ(n)) is a Nuprl type: *)
 Require Import union_all_types.
 *)


(* weak consistency *)
Require Import weak_consistency.


(*
(* Rules(structural): *)
 Require Import rules_struct.
 Require Import rules_struct2.
 Require Import rules_move.


(* Bar Induction on nats: *)
 Require Import bar_induction3.
(* Bar Induction on nats with constraint on the spread: *)
 Require Import bar_induction3_con.
(* A more useful version than the one proved in bar_induction3_con
   (the inductive case is inductive over R too): *)
 Require Import bar_induction5_con.
(* Bar Induction on sequences of closed terms without atoms: *)
 Require Import bar_induction_cterm2.
(* Same as bar_induction_cterm2 but a simpler 0-sequence: *)
 Require Import bar_induction_cterm3.
(* Same as bar_induction_cterm3 but squashed bar in base hyp: *)
 Require Import bar_induction_cterm4.

(* Require Import rules_barind. *)


(* Kripke's Schema *)
 Require Import kripkes_schema.
 Require Import kripkes_schema2.


(* Choice sequences: *)
 Require Import choice_sequence_ind.
 Require Import choice_sequence_ind2.


(* Axiom of Choice: *)
 Require Import axiom_choice.
 Require Import axiom_choice_gen.
(*Require Import axiom_choice2.*)
*)


(* Rules(squiggle): *)
(* Require Import rules_squiggle.
 Require Import rules_squiggle2.
 Require Import rules_squiggle3.
 Require Import rules_squiggle4.
 Require Import rules_squiggle5.
 Require Import rules_squiggle6.*)
Require Import rules_squiggle7.
(* Require Import rules_squiggle8.*)
Require Import rules_base.


(*
(* Rules(exception): *)
 Require Import rules_exception.
 Require Import rules_exception2.
 Require Import rules_decide_exception.
 Require Import rules_arith_exception.
 Require Import rules_cft_exception.
 Require Import rules_apply_exception.
 Require Import rules_cbv_exception.
 Require Import rules_less_exception.


(* Rules(try): *)
 Require Import rules_try.


(* Rules(callbyvalue): *)
 Require Import rules_arith_callbyvalue.
 Require Import rules_apply_callbyvalue.
 Require Import rules_cft_callbyvalue.
 Require Import rules_halts_spread.
 Require Import rules_halts_decide.
 Require Import rules_callbyvalue.


(* Cases rules for canonical form tests *)
 Require Import rules_cft.
 Require Import rules_inl_inr_cases.
 Require Import rules_axiom_cases.
 Require Import rules_isint.


(* Arithmetic Rules *)
 Require Import rules_arith.
 Require Import rules_integer.
 Require Import rules_integer_ring.
 Require Import rules_minus.
 Require Import rules_number.


(* Continuity axiom and rule: *)
 Require Import continuity_roadmap.
(* Some results related to continuity and bar induction *)
 Require Import unsquashed_continuity.


(* Functionality rules *)
 Require Import rules_functionality.


(* Set type *)
 Require Import rules_set.


(* Equality type *)
 Require Import rules_equality.*)
Require Import rules_equality2.
(* Require Import rules_equality3.
 Require Import rules_equality4.
 Require Import rules_equality5.
 Require Import rules_equality6.
 Require Import rules_equality7.


(* Type equality type *)
 Require Import rules_tequality.


(* Intersection type *)
 Require Import rules_isect.
 Require Import rules_isect2.


(* Derivation of False from false hypotheses *)
 Require Import rules_false.


(* A few lemmas using our verified rules *)
 Require Import nuprl_lemmas1.
 Require Import nuprl_lemmas2.
 Require Import proof1.
 Require Import proof_with_lib.
 Require Import proof_with_lib_example1.
 Require Import proof_with_lib_non_dep.
 Require Import proof_with_lib_non_dep_example1.
 Require Import sterm.
*)


(* Function/pi type *)
Require Import rules_function.
Require Import rules_function2.


(* Product/sum type *)
Require Import rules_product.


(*
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
*)


(* classical rules *)
(* Require Import rules_classical.*)
Require Import rules_not_classical.
Require Import rules_not_MP.
Require Import rules_not_IP.


(*
(* Domain theory *)
 Require Import rules_partial.
 Require Import rules_mono.


(* Nominal rules *)
 Require Import rules_fresh.


(* Universe type *)
 Require Import rules_uni.


(* Void type: *)
 Require Import rules_void.
*)


(* Union type: *)
Require Import rules_union.


(*
(* Squash rules (derivable) *)
 Require Import rules_squash.


(* Rules(atoms): *)
 Require Import rules_atom_atom.
 Require Import rules_atom_struct.
 Require Import rules_free_from_atom.


(* Require Import rules_per_function. *)
 *)
