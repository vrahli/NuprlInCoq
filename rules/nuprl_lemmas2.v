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


Require Import sequents_tacs.
Require Import rules_isect.
Require Import rules_squiggle.
Require Import rules_struct.
Require Import tactics2.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)

Lemma in_lst_1_out_of_1 {o} :
  forall s1,
    (forall s : @baresequent o, (s1 = s) [+] False -> pwf_sequent s)
    -> pwf_sequent s1.
Proof. sp. Qed.

Lemma in_lst_1_out_of_2 {o} :
  forall s1 s2,
    (forall s : @baresequent o, (s1 = s) [+] (s2 = s) [+] False -> pwf_sequent s)
    -> pwf_sequent s1.
Proof. sp. Qed.

Lemma in_lst_2_out_of_2 {o} :
  forall s1 s2,
    (forall s : @baresequent o, (s1 = s) [+] (s2 = s) [+] False -> pwf_sequent s)
    -> pwf_sequent s2.
Proof. sp. Qed.

(* end hide *)

(**

  Let us now illustrate how we can use the proofs of the validity of
  Nuprl's rules and the meaning of rules to build a simple refiner of
  Nuprl proofs directly in Coq using Ltac.

  We first define the [rule] inductive type that contains the list of
  rules that we allow ourselves to use.  This list does not contain
  yet all the rules we have proved to be valid.

*)

Notation lvl := nat.

Inductive rule :=
| isect_equality : NVar -> lvl -> rule
| isect_member_formation : lvl -> NVar -> rule
| approx_intensional_equality_simple : lvl -> rule
| cequiv_refl : rule
| thin_hyps : rule.

(**

  A lemma will be stated as follows: [nuprove statement].

  We now define a few useful rules to simulate a proof environment.
  First, the [start_proof] tactic is used when starting a proof.  It
  uses [eexists] in order to build extracts bottom-up while doing a
  proof top-down.  Then we prove the well-formedness of the given goal
  and the remaining subgoal is a statement that says that the goal is
  true in an empty environment.

*)

(* begin show *)

Ltac start_proof :=
  let pwf := fresh "pwf" in
    eexists;
  prove_and pwf;
  [ unfold pwf_sequent; wfseq
  | idtac
  ].

(* end show *)

(**

  When using [start_proof] we are also left with a subgoal where we
  have to prove that the extract is well-formed.  However, we cannot
  prove that just yet because we do not know yet what the extract is.
  Extracts are built bottom-up, therefore, the extract will be fully
  built only once the proof is finished.  Therefore, we use
  [end_proof] at the end of a proof to prove the well-formedness of
  the extract.

*)

(* begin show *)

Ltac end_proof := sp.

(* end show *)

(**

  We use [use_lemma] to use a Nuprl lemma already proven and get its
  extract.

*)

(* begin show *)

Ltac use_lemma lem :=
  let l  := fresh "l"  in
  let hl := fresh "hl" in
  let r  := fresh "r"  in
  let hr := fresh "hr" in
  let e  := fresh "e"  in
  let t  := fresh "t"  in
  let w  := fresh "w"  in
    remember lem as l eqn:hl;
  remember (projT1 l) as r eqn:hr;
  dup hr as e;
  rewrite hl in e;
  rewrite hr in e;
  simpl in e;
  clear hl hr;
  unfold nuprove in l;
  destruct l as [t l];
  destruct l as [w l];
  simpl in e;
  subst;
  try (apply l).

(* end show *)

(**

  The following few tactics are used to prove simple side-conditions
  of rules.

*)

(* begin show *)

Ltac inveq :=
  match goal with
    | [ H : _ = _ |- _ ] => complete inversion H
  end.

Ltac prove_side_condition := simpl; sp; try inveq; try wfseq.
Ltac tc_prove_side_condition := try (complete prove_side_condition).

(* end show *)

(**

  The next tactic is our most important tactic, which refines a goal
  using a [rule].  It applies the corresponding lemmas that states
  that the rule is valid.  It also uses the facts that most of our
  rules satisfy the [wf_rule] predicate to prove the well-formedness
  of sequents.

*)

(* begin show *)

Ltac nuprl_refine_o o R :=
  let r := fresh "r" in
    match R with
      | isect_equality ?v ?n =>
        pose proof (@rule_isect_equality_true2 o emlib v n) as r;
          apply r;
          clear r;
          [ tc_prove_side_condition
          | tc_prove_side_condition
          | let w := fresh "w" in
            let i := fresh "i" in
              pose proof (@rule_isect_equality_wf o v n) as w;
              unfold wf_rule in w;
              simpl in w;
              match goal with
                [ H : pwf_sequent _ |- _ ] =>
                apply w in H;
                  clear w;
                  [ introv i; simpl in i; repdors; subst;
                    unfold wf_subgoals in H; simpl in H;
                    try ( unfold rule_isect_equality_hyp1 in * );
                    try ( unfold rule_isect_equality_hyp2 in * );
                    [ apply in_lst_1_out_of_2 in H
                    | apply in_lst_2_out_of_2 in H
                    | complete sp
                    ]
                  | tc_prove_side_condition
                  ]
              end
          ]

      | isect_member_formation ?l ?v =>
          pose proof (@rule_isect_member_formation_true2 o emlib l v mk_axiom) as r;
          apply r;
          clear r;
          [ tc_prove_side_condition
          | tc_prove_side_condition
          | let w := fresh "w" in
            let i := fresh "i" in
              pose proof (@rule_isect_member_formation_wf o l v mk_axiom) as w;
              unfold wf_rule in w;
              simpl in w;
              match goal with
                  [ H : pwf_sequent _ |- _ ] =>
                    apply w in H;
                  clear w;
                  [ introv i; simpl in i; repdors; subst;
                    unfold wf_subgoals in H; simpl in H;
                    [ apply in_lst_1_out_of_2 in H
                    | apply in_lst_2_out_of_2 in H
                    | complete sp
                    ]
                  | tc_prove_side_condition
                  | tc_prove_side_condition
                  ]
              end
          ]

      | approx_intensional_equality_simple ?n =>
          pose proof (@rule_approx_intensional_equality_simple_true2 o emlib n) as r;
          apply r;
          clear r;
          [ tc_prove_side_condition
          | tc_prove_side_condition
          | complete (simpl; sp) (* no subgoals *)
          ]

      | cequiv_refl =>
          pose proof (@rule_cequiv_refl_true2 o emlib) as r;
          apply r;
          clear r;
          [ tc_prove_side_condition
          | tc_prove_side_condition
          | complete (simpl; sp) (* no subgoals *)
          ]

      | thin_hyps =>
          pose proof (@rule_thin_hyps_true2 o emlib) as r;
          apply r;
          clear r;
          [ tc_prove_side_condition
          | tc_prove_side_condition
          | let w := fresh "w" in
            let i := fresh "i" in
              pose proof (@rule_thin_hyps_wf o) as w;
              unfold wf_rule in w;
              simpl in w;
              match goal with
                  [ H : pwf_sequent _ |- _ ] =>
                    apply w in H;
                  clear w;
                  [ introv i; simpl in i; repdors; subst;
                    unfold wf_subgoals in H; simpl in H;
                    [ apply in_lst_1_out_of_1 in H
                    | complete sp
                    ]
                  | tc_prove_side_condition
                  ]
              end
          ]
    end.

Ltac nuprl_refine R :=
  match goal with
    | [ o : POpid |- _ ] => nuprl_refine_o o R
  end.

(* end show *)

Ltac nuprl_tree := idtac.

(**

  Let us now prove a few simple lemmas.  First, we prove that
  [mk_false] is a type, where [mk_false] is defined as [mk_approx
  mk_axiom mk_bot], where [mk_bot] is defined as [mk_fix mk_id].

*)

(* begin show *)

Lemma false_in_type {o} :
  @nuprove o emlib (mk_member mk_false (mk_uni 0)).
Proof.
  start_proof.
  Focus 2.

  nuprl_tree;
    [ nuprl_refine (approx_intensional_equality_simple 0)
    ].

  end_proof.
Defined.

(* end show *)

(**

  Next, we prove that [mk_top] is a type, where [mk_top] is defined as
  [mk_isect mk_false nvarx mk_false].  This proof contains a few extra
  steps, which eventually will disappear once we have built enough
  tactics.

*)

(* begin show *)

Lemma top_in_type {o} :
  @nuprove o emlib (mk_member mk_top (mk_uni 0)).
Proof.
  start_proof.
  Focus 2.

  nuprl_tree;
    [ nuprl_refine (isect_equality nvary 0);
      [ use_lemma (@false_in_type o)

      | rw @subst_mk_false; try prove_side_condition;
        rw @subst_mk_false in pwf; try prove_side_condition;
        assert ([mk_hyp nvary mk_false] = [] ++ [mk_hyp nvary (@mk_false o)]) as eq by (simpl; sp);
        rw eq; rw eq in pwf; clear eq;

        nuprl_refine thin_hyps;
        [ use_lemma (@false_in_type o)
        ]
      ]
    ].

  end_proof.
Defined.

(* end show *)

(**

  The following lemma proves that for all [x] in [mk_top], [x] is
  computationally equivalent to [x].  Once again this proof contains a
  few extra steps which eventually will disappear once we have built
  enough tactics.

*)

(* begin show *)

(* prove: [uall x : Top], x ~ x. *)
Lemma cequiv_refl_top {o} :
  @nuprove o emlib (mk_uall mk_top nvarx (mk_cequiv (mk_var nvarx) (mk_var nvarx))).
Proof.
  start_proof.
  Focus 2.

  nuprl_tree;
    [ nuprl_refine (isect_member_formation 0 nvary);
      [ unfold rule_isect_member_formation_hyp1 in *;
        unfold subst, lsubst; simpl; rw @fold_nobnd; rw @fold_cequiv;
        unfold subst, lsubst in pwf; simpl in pwf; rw @fold_nobnd in pwf; rw @fold_cequiv in pwf;
        nuprl_refine cequiv_refl
      |   use_lemma (@top_in_type o)
      ]
    ].
  end_proof.
Defined.

(* end show *)

(* end hide *)
