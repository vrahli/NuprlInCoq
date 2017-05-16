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

  Authors: Vincent Rahli

*)


Require Export terms_deq_op.
Require Export compute_atmost_k_steps.

Require Export rules_isect.
Require Export rules_squiggle.
Require Export rules_squiggle2.
Require Export rules_squiggle3.
Require Export rules_squiggle5.
Require Export rules_squiggle6.
Require Export rules_squiggle7.
Require Export rules_false.
Require Export rules_struct.
Require Export rules_function.
Require Export rules_uni.
Require Export rules_equality3.
Require Export rules_integer.



(* ===========================================================

  A pre-sequent is a sequent without the extract, which we can
  only build once a proof is finished

  ============================================================ *)

(* a pre-conclusion is a conclusion without the extract *)
Inductive pre_conclusion {o} :=
| pre_concl_ext : forall (ctype : @NTerm o), pre_conclusion
| pre_concl_typ : forall (ctype : @NTerm o), pre_conclusion.

Definition mk_pre_concl {o} (t : @NTerm o) : pre_conclusion :=
  pre_concl_ext t.

Definition mk_pre_concleq {o} (t1 t2 T : @NTerm o) : pre_conclusion :=
  mk_pre_concl (mk_equality t1 t2 T).

Record pre_baresequent {o} :=
  MkPreBaresequent
    {
      pre_hyps  : @barehypotheses o;
      pre_concl : @pre_conclusion o;
    }.

Arguments MkPreBaresequent [o] _ _.

Definition mk_pre_bseq {o} H (c : @pre_conclusion o) : pre_baresequent :=
  MkPreBaresequent H c.

Definition concl2pre {o} (c : @conclusion o) : pre_conclusion :=
  match c with
  | concl_ext t _ => pre_concl_ext t
  | concl_typ t => pre_concl_typ t
  end.

Definition concl2pre_baresequent {o} (c : @conclusion o) : pre_baresequent :=
  mk_pre_bseq [] (concl2pre c).

Definition baresequent2pre {o} (s : @baresequent o) : pre_baresequent :=
  mk_pre_bseq (hyps s) (concl2pre (concl s)).

Definition PreStatement {o} (T : @NTerm o) : pre_baresequent :=
  mk_pre_bseq [] (mk_pre_concl T).

Definition Statement {o} (T : @NTerm o) (e : NTerm) : baresequent :=
  mk_baresequent [] (mk_concl T e).



(* ===========================================================

  Some pre-sequents corresponding to the hypotheses and conclusions
  of some of our rules

  ============================================================ *)

Definition pre_rule_isect_equality_concl {o} a1 a2 x1 x2 b1 b2 i (H : @bhyps o) :=
  mk_pre_bseq
    H
    (mk_pre_concleq
       (mk_isect a1 x1 b1)
       (mk_isect a2 x2 b2)
       (mk_uni i)).

Definition pre_rule_isect_equality_hyp1 {o} a1 a2 i (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concleq a1 a2 (mk_uni i)).

Definition pre_rule_isect_equality_hyp2 {o} a1 b1 b2 x1 x2 y i (H : @bhyps o) :=
  mk_pre_bseq
    (snoc H (mk_hyp y a1))
    (mk_pre_concleq
       (subst b1 x1 (mk_var y))
       (subst b2 x2 (mk_var y))
       (mk_uni i)).

Definition pre_rule_cequiv_computation_concl {o} a b (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concl (mk_cequiv a b)).

Definition pre_rule_function_elimination_concl {o}
           (A : @NTerm o) B C f x H J :=
  mk_pre_bseq
    (snoc H (mk_hyp f (mk_function A x B)) ++ J)
    (mk_pre_concl C).

Definition pre_rule_function_elimination_hyp1 {o}
           (A : @NTerm o) B a f x H J :=
  mk_pre_bseq
    (snoc H (mk_hyp f (mk_function A x B)) ++ J)
    (mk_pre_concl (mk_member a A)).

Definition pre_rule_function_elimination_hyp2 {o}
           (A : @NTerm o) B C a f x z H J :=
  mk_pre_bseq
    (snoc (snoc H (mk_hyp f (mk_function A x B)) ++ J)
          (mk_hyp z (mk_member (mk_apply (mk_var f) a)
                               (subst B x a))))
    (mk_pre_concl C).

Definition pre_rule_approx_refl_concl {o} a (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concl (mk_approx a a)).

Definition pre_rule_cequiv_approx_concl {o} (a b : @NTerm o) H :=
  mk_pre_bseq H (mk_pre_concl (mk_cequiv a b)).

Definition pre_rule_cequiv_approx_hyp {o} (a b : @NTerm o) H :=
  mk_pre_bseq H (mk_pre_concl (mk_approx a b)).

Definition pre_rule_approx_eq_concl {o} a1 a2 b1 b2 i (H : @bhyps o) :=
  mk_pre_bseq
    H
    (mk_pre_concleq
       (mk_approx a1 b1)
       (mk_approx a2 b2)
       (mk_uni i)).

Definition pre_rule_eq_base_hyp {o} a1 a2 (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concleq a1 a2 mk_base).

Definition pre_rule_cequiv_eq_concl {o} a1 a2 b1 b2 i (H : @bhyps o) :=
  mk_pre_bseq
    H
    (mk_pre_concleq
       (mk_cequiv a1 b1)
       (mk_cequiv a2 b2)
       (mk_uni i)).

Definition pre_rule_bottom_diverges_concl {o} x (H J : @bhyps o) :=
  mk_pre_bseq
    (snoc H (mk_hyp x (mk_halts mk_bottom)) ++ J)
    (mk_pre_concl mk_false).

Definition pre_rule_cut_concl {o} (H : @bhyps o) C :=
  mk_pre_bseq H (mk_pre_concl C).

Definition pre_rule_cut_hyp1 {o} (H : @bhyps o) B :=
  mk_pre_bseq H (mk_pre_concl B).

Definition pre_rule_cut_hyp2 {o} (H : @bhyps o) x B C :=
  mk_pre_bseq (snoc H (mk_hyp x B)) (mk_pre_concl C).

Definition pre_rule_equal_in_base_concl {o} (a b : @NTerm o) H :=
  mk_pre_bseq H (mk_pre_concl (mk_equality a b mk_base)).

Definition pre_rule_equal_in_base_hyp1 {o} (a b : @NTerm o) H :=
  mk_pre_bseq H (mk_pre_concl (mk_cequiv a b)).

Definition pre_rule_equal_in_base_hyp2 {o} (v : NVar) (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concl (mk_member (mk_var v) mk_base)).

Definition pre_rule_equal_in_base_rest {o} (a : @NTerm o) (H : @bhyps o) :=
  map (fun v => pre_rule_equal_in_base_hyp2 v H)
      (free_vars a).

Definition pre_rule_cequiv_subst_hyp1 {o} (H : @bhyps o) x C a :=
  mk_pre_bseq H (mk_pre_concl (subst C x a)).

Definition pre_rule_cequiv_subst_hyp2 {o} (H : @bhyps o) a b :=
  mk_pre_bseq H (mk_pre_concl (mk_cequiv a b)).

Definition pre_rule_hypothesis_concl {o} (G J : @bhyps o) A x :=
  mk_pre_bseq (snoc G (mk_hyp x A) ++ J) (mk_pre_concl A).

Definition pre_rule_approx_member_eq_concl {o} a b (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concleq mk_axiom mk_axiom (mk_approx a b)).

Definition pre_rule_approx_member_eq_hyp {o} a b (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concl (mk_approx a b)).

Definition pre_rule_isect_member_formation_concl {o} A x B (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concl (mk_isect A x B)).

Definition pre_rule_isect_member_formation_hyp1 {o} z A x B (H : @bhyps o) :=
  mk_pre_bseq
    (snoc H (mk_hhyp z A))
    (mk_pre_concl (subst B x (mk_var z))).

Definition pre_rule_isect_member_formation_hyp2 {o} A i (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concl (mk_equality A A (mk_uni i))).

Definition pre_rule_universe_equality_concl {o} (H : @bhyps o) i j :=
  mk_pre_bseq H (mk_pre_concl (mk_member (mk_uni i) (mk_uni j))).

Definition pre_rule_hypothesis_equality_concl {o} (G J : @bhyps o) A x :=
  mk_pre_bseq
    (snoc G (mk_hyp x A) ++ J)
    (mk_pre_concl (mk_equality (mk_var x) (mk_var x) A)).

Definition pre_rule_integer_equality_concl {o} (H : @bhyps o) n :=
  mk_pre_bseq H (mk_pre_concl (mk_member (mk_integer n) mk_int)).

Definition pre_rule_unhide_equality_concl {o} (H J : @bhyps o) x A t1 t2 C :=
  mk_pre_bseq
    (snoc H (mk_hhyp x A) ++ J)
    (mk_pre_concl (mk_equality t1 t2 C)).

Definition pre_rule_unhide_equality_hyp {o} (H J : @bhyps o) x A t1 t2 C :=
  mk_pre_bseq
    (snoc H (mk_hyp x A) ++ J)
    (mk_pre_concl (mk_equality t1 t2 C)).

Definition pre_rule_equality_equality_concl {o} (H : @bhyps o) a1 a2 b1 b2 A B i :=
  mk_pre_bseq
    H
    (mk_pre_concl (mk_equality
                     (mk_equality a1 a2 A)
                     (mk_equality b1 b2 B)
                     (mk_uni i))).

Definition pre_rule_equality_equality_hyp1 {o} (H : @bhyps o) A B i :=
  mk_pre_bseq H (mk_pre_concl (mk_equality A B (mk_uni i))).

Definition pre_rule_equality_equality_hyp2 {o} (H : @bhyps o) a b A :=
  mk_pre_bseq H (mk_pre_concl (mk_equality a b A)).

Definition pre_rule_introduction_concl {o} (H : @bhyps o) C :=
  mk_pre_bseq H (mk_pre_concl C).

Definition pre_rule_introduction_hyp {o} (H : @bhyps o) C t :=
  mk_pre_bseq H (mk_pre_concl (mk_member t C)).



(* ===========================================================

  Side-checks

  ============================================================ *)

Definition NVin v (vs : list NVar) := memvar v vs = false.

Definition Vin v (vs : list NVar) := memvar v vs = true.

Lemma NVin_iff :
  forall v vs, NVin v vs <=> !LIn v vs.
Proof.
  introv.
  unfold NVin.
  rw <- (@assert_memberb NVar eq_var_dec).
  rw <- not_of_assert; sp.
Qed.

Lemma Vin_iff :
  forall v vs, Vin v vs <=> LIn v vs.
Proof.
  introv.
  unfold Vin.
  rw <- (@assert_memberb NVar eq_var_dec); auto.
Qed.

Definition NVin_dec : forall v vs, decidable (NVin v vs).
Proof.
  introv.
  unfold NVin.
  destruct (memvar v vs); tcsp.
  right; intro xx; tcsp.
Defined.



(* ===========================================================

  A proof context is a list of abstractions and a list of proved
  formulas.

  ============================================================ *)

Definition extract_ax {o} (c : @conclusion o) : NTerm :=
  match extract c with
  | Some e => e
  | None => mk_axiom
  end.

Definition valid_extract {o} (t : @NTerm o) : Prop :=
  wf_term t # closed t # noutokens t.

Definition LemmaName := opname.

Lemma LemmaNameDeq : Deq LemmaName.
Proof.
  introv.
  destruct (String.string_dec x y); auto.
Defined.

Record named_concl {o} :=
  MkNamedConcl
    {
      nm_conclusion_name : LemmaName;
      nm_conclusion_type : @NTerm o;
    }.
Arguments MkNamedConcl [o] _ _.

Definition opname2opabs (op : opname) : opabs :=
  mk_opabs op [] [].

Definition named_concl2concl {o} (n : @named_concl o) : conclusion :=
  mk_concl (nm_conclusion_type n) (mk_abs (opname2opabs (nm_conclusion_name n)) []).

Definition named_concl2bseq {o} H (n : @named_concl o) : baresequent :=
  mk_bseq H (named_concl2concl n).

Definition named_concl2pre_concl {o} (n : @named_concl o) : pre_conclusion :=
  mk_pre_concl (nm_conclusion_type n).

Definition named_concl2pre_bseq {o} H (n : @named_concl o) : pre_baresequent :=
  mk_pre_bseq H (named_concl2pre_concl n).

(*Record wf_conclusion {o} :=
  MkWfConcl
    {
      wf_conclusion_concl :> @named_concl o;
      wf_conclusion_wf    : valid_extract (extract_ax wf_conclusion_concl);
    }.
Arguments MkWfConcl [o] _ _.

Definition wf_conclusions {o} := list (@wf_conclusion o).

Definition in_wf_conclusions {o} (c : @named_concl o) (l : wf_conclusions) :=
  LIn c (map wf_conclusion_concl l).*)

Record ProofContext {o} :=
  MkProofContext
    {
      PC_lib :> @library o;
      PC_conclusions : list (@named_concl o);
    }.

Definition EMPC {o} : @ProofContext o := MkProofContext o [] [].

Definition updLibProofContext {o} (pc : @ProofContext o) (e : library_entry) :=
  MkProofContext
    o
    (e :: PC_lib pc)
    (PC_conclusions pc).

Definition updConclProofContext {o} (pc : @ProofContext o) (c : named_concl) :=
  MkProofContext
    o
    (PC_lib pc)
    (c :: PC_conclusions pc).



(* ===========================================================

  A pre-proof is a tree of proof-steps without the extracts,
  which we can only build once the proof is finished

  ============================================================ *)

(* We have the library here so that we can unfold abstractions *)
Inductive pre_proof {o} (ctxt : @ProofContext o) : @pre_baresequent o -> Type :=
| pre_proof_from_ctxt :
    forall (c : named_concl) H,
      LIn c (@PC_conclusions o ctxt)
      -> pre_proof ctxt (named_concl2pre_bseq H c)
| pre_proof_hole : forall (s : pre_baresequent), pre_proof ctxt s
| pre_proof_isect_eq :
    forall a1 a2 b1 b2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> pre_proof ctxt (pre_rule_isect_equality_hyp1 a1 a2 i H)
      -> pre_proof ctxt (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H)
      -> pre_proof ctxt (pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
| pre_proof_isect_member_formation :
    forall A x B z i H,
      NVin z (vars_hyps H)
      -> pre_proof ctxt (pre_rule_isect_member_formation_hyp1 z A x B H)
      -> pre_proof ctxt (pre_rule_isect_member_formation_hyp2 A i H)
      -> pre_proof ctxt (pre_rule_isect_member_formation_concl A x B H)
| pre_proof_approx_refl :
    forall a H,
      pre_proof ctxt (pre_rule_approx_refl_concl a H)
| pre_proof_cequiv_approx :
    forall a b H,
      pre_proof ctxt (pre_rule_cequiv_approx_hyp a b H)
      -> pre_proof ctxt (pre_rule_cequiv_approx_hyp b a H)
      -> pre_proof ctxt (pre_rule_cequiv_approx_concl a b H)
| pre_proof_approx_eq :
    forall a1 a2 b1 b2 i H,
      pre_proof ctxt (pre_rule_eq_base_hyp a1 a2 H)
      -> pre_proof ctxt (pre_rule_eq_base_hyp b1 b2 H)
      -> pre_proof ctxt (pre_rule_approx_eq_concl a1 a2 b1 b2 i H)
| pre_proof_cequiv_eq :
    forall a1 a2 b1 b2 i H,
      pre_proof ctxt (pre_rule_eq_base_hyp a1 a2 H)
      -> pre_proof ctxt (pre_rule_eq_base_hyp b1 b2 H)
      -> pre_proof ctxt (pre_rule_cequiv_eq_concl a1 a2 b1 b2 i H)
(*| pre_proof_bottom_diverges :
    forall x H J,
      pre_proof hole ctxt (pre_rule_bottom_diverges_concl x H J)*)
| pre_proof_cut :
    forall B C x H,
      wf_term B
      -> covered B (vars_hyps H)
      -> NVin x (vars_hyps H)
      -> pre_proof ctxt (pre_rule_cut_hyp1 H B)
      -> pre_proof ctxt (pre_rule_cut_hyp2 H x B C)
      -> pre_proof ctxt (pre_rule_cut_concl H C)
(*| pre_proof_equal_in_base :
    forall a b H,
      pre_proof hole ctxt (pre_rule_equal_in_base_hyp1 a b H)
      -> (forall v, LIn v (free_vars a) -> pre_proof hole ctxt (pre_rule_equal_in_base_hyp2 v H))
      -> pre_proof hole ctxt (pre_rule_equal_in_base_concl a b H)*)
| pre_proof_hypothesis :
    forall x A G J,
      pre_proof ctxt (pre_rule_hypothesis_concl G J A x)
| pre_proof_cequiv_subst_concl :
    forall C x a b H,
      wf_term a
      -> wf_term b
      -> covered a (vars_hyps H)
      -> covered b (vars_hyps H)
      -> pre_proof ctxt (pre_rule_cequiv_subst_hyp1 H x C b)
      -> pre_proof ctxt (pre_rule_cequiv_subst_hyp2 H a b)
      -> pre_proof ctxt (pre_rule_cequiv_subst_hyp1 H x C a)
(*| pre_proof_approx_member_eq :
    forall a b H,
      pre_proof hole ctxt (pre_rule_approx_member_eq_hyp a b H)
      -> pre_proof hole ctxt (pre_rule_approx_member_eq_concl a b H)*)
| pre_proof_cequiv_computation :
    forall a b H,
      reduces_to ctxt a b
      -> pre_proof ctxt (pre_rule_cequiv_computation_concl a b H)
| pre_proof_cequiv_computation_atmost :
    forall a b n H,
      reduces_in_atmost_k_steps ctxt a b n
      -> pre_proof ctxt (pre_rule_cequiv_computation_concl a b H)
(*| pre_proof_function_elimination :
    forall A B C a f x z H J,
      wf_term a
      -> covered a (snoc (vars_hyps H) f ++ vars_hyps J)
      -> !LIn z (vars_hyps H)
      -> !LIn z (vars_hyps J)
      -> z <> f
      -> pre_proof hole ctxt (pre_rule_function_elimination_hyp1 A B a f x H J)
      -> pre_proof hole ctxt (pre_rule_function_elimination_hyp2 A B C a f x z H J)
      -> pre_proof hole ctxt (pre_rule_function_elimination_concl A B C f x H J)*)
| pre_proof_universe_equality :
    forall i j H,
      i < j
      -> pre_proof ctxt (pre_rule_universe_equality_concl H i j)
| pre_proof_hypothesis_equality :
    forall x A G J,
      pre_proof ctxt (pre_rule_hypothesis_equality_concl G J A x)
| pre_proof_unhide_equality :
    forall x A t1 t2 C G J,
      pre_proof ctxt (pre_rule_unhide_equality_hyp G J x A t1 t2 C)
      -> pre_proof ctxt (pre_rule_unhide_equality_concl G J x A t1 t2 C)
| pre_proof_equality_equality :
    forall A B a1 a2 b1 b2 i H,
      pre_proof ctxt (pre_rule_equality_equality_hyp1 H A B i)
      -> pre_proof ctxt (pre_rule_equality_equality_hyp2 H a1 b1 A)
      -> pre_proof ctxt (pre_rule_equality_equality_hyp2 H a2 b2 A)
      -> pre_proof ctxt (pre_rule_equality_equality_concl H a1 a2 b1 b2 A B i)
| pre_proof_integer_equality :
    forall n H,
      pre_proof ctxt (pre_rule_integer_equality_concl H n)
| pre_proof_introduction :
    forall t C H,
      wf_term t
      -> covered t (nh_vars_hyps H)
      -> noutokens t
      -> pre_proof ctxt (pre_rule_introduction_hyp H C t)
      -> pre_proof ctxt (pre_rule_introduction_concl H C).

Inductive proof {o} (ctxt : @ProofContext o) : @baresequent o -> Type :=
| proof_from_ctxt :
    forall (c : named_concl) H,
      LIn c (@PC_conclusions o ctxt)
      -> proof ctxt (named_concl2bseq H c)
| proof_isect_eq :
    forall a1 a2 b1 b2 e1 e2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> proof ctxt (rule_isect_equality2_hyp1 a1 a2 e1 i H)
      -> proof ctxt (rule_isect_equality2_hyp2 a1 b1 b2 e2 x1 x2 y i H)
      -> proof ctxt (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
| proof_isect_member_formation :
    forall A x B z i b e H,
      NVin z (vars_hyps H)
      -> proof ctxt (rule_isect_member_formation_hyp1 z A x B b H)
      -> proof ctxt (rule_isect_member_formation_hyp2 A e i H)
      -> proof ctxt (rule_isect_member_formation_concl A x B b H)
| proof_approx_refl :
    forall a H,
      proof ctxt (rule_approx_refl_concl a H)
| proof_cequiv_approx :
    forall a b e1 e2 H,
      proof ctxt (rule_cequiv_approx2_hyp a b e1 H)
      -> proof ctxt (rule_cequiv_approx2_hyp b a e2 H)
      -> proof ctxt (rule_cequiv_approx_concl a b H)
| proof_approx_eq :
    forall a1 a2 b1 b2 e1 e2 i H,
      proof ctxt (rule_eq_base2_hyp a1 a2 e1 H)
      -> proof ctxt (rule_eq_base2_hyp b1 b2 e2 H)
      -> proof ctxt (rule_approx_eq_concl a1 a2 b1 b2 i H)
| proof_cequiv_eq :
    forall a1 a2 b1 b2 e1 e2 i H,
      proof ctxt (rule_eq_base2_hyp a1 a2 e1 H)
      -> proof ctxt (rule_eq_base2_hyp b1 b2 e2 H)
      -> proof ctxt (rule_cequiv_eq_concl a1 a2 b1 b2 i H)
(*| proof_bottom_diverges :
    forall x H J,
      proof ctxt (rule_bottom_diverges_concl x H J)*)
| proof_cut :
    forall B C t u x H,
      wf_term B
      -> covered B (vars_hyps H)
      -> NVin x (vars_hyps H)
      -> proof ctxt (rule_cut_hyp1 H B u)
      -> proof ctxt (rule_cut_hyp2 H x B C t)
      -> proof ctxt (rule_cut_concl H C t x u)
(*| proof_equal_in_base :
    forall a b e F H,
      proof ctxt (rule_equal_in_base2_hyp1 a b e H)
      -> (forall v (i : LIn v (free_vars a)),
             proof ctxt (rule_equal_in_base2_hyp2 v (F v i) H))
      -> proof ctxt (rule_equal_in_base_concl a b H)*)
| proof_hypothesis :
    forall x A G J,
      proof ctxt (rule_hypothesis_concl G J A x)
| proof_cequiv_subst_concl :
    forall C x a b t e H,
      wf_term a
      -> wf_term b
      -> covered a (vars_hyps H)
      -> covered b (vars_hyps H)
      -> proof ctxt (rule_cequiv_subst_hyp1 H x C b t)
      -> proof ctxt (rule_cequiv_subst2_hyp2 H a b e)
      -> proof ctxt (rule_cequiv_subst_hyp1 H x C a t)
(*| proof_approx_member_eq :
    forall a b e H,
      proof ctxt (rule_approx_member_eq2_hyp a b e H)
      -> proof ctxt (rule_approx_member_eq_concl a b H)*)
| proof_cequiv_computation :
    forall a b H,
      reduces_to ctxt a b
      -> proof ctxt (rule_cequiv_computation_concl a b H)
| proof_cequiv_computation_atmost :
    forall a b n H,
      reduces_in_atmost_k_steps ctxt a b n
      -> proof ctxt (rule_cequiv_computation_concl a b H)
(*| proof_function_elimination :
    (* When deriving a sequent, e is not supposed to be given but inferred
     * from the second sequent.  That's the case in a pre_proof
     *)
    forall A B C a e ea f x z H J,
      wf_term a
      -> covered a (snoc (vars_hyps H) f ++ vars_hyps J)
      -> !LIn z (vars_hyps H)
      -> !LIn z (vars_hyps J)
      -> z <> f
      -> proof ctxt (rule_function_elimination_hyp1 A B a ea f x H J)
      -> proof ctxt (rule_function_elimination_hyp2 A B C a e f x z H J)
      -> proof ctxt (rule_function_elimination_concl A B C e f x z H J)*)
| proof_universe_equality :
    forall i j H,
      i < j
      -> proof ctxt (rule_universe_equality_concl H i j)
| proof_hypothesis_equality :
    forall x A G J,
      proof ctxt (rule_hypothesis_equality_concl G J A x)
| proof_unhide_equality :
    forall x A t1 t2 C e G J,
      proof ctxt (rule_unhide_equality_hyp G J x A t1 t2 C e)
      -> proof ctxt (rule_unhide_equality_concl G J x A t1 t2 C)
| proof_equality_equality :
    forall A B a1 a2 b1 b2 e1 e2 e3 i H,
      proof ctxt (rule_equality_equality_hyp1 H A B i e1)
      -> proof ctxt (rule_equality_equality_hyp2 H a1 b1 A e2)
      -> proof ctxt (rule_equality_equality_hyp2 H a2 b2 A e3)
      -> proof ctxt (rule_equality_equality_concl H a1 a2 b1 b2 A B i)
| proof_integer_equality :
    forall n H,
      proof ctxt (rule_integer_equality_concl H n)
| proof_introduction :
    forall t e C H,
      wf_term t
      -> covered t (nh_vars_hyps H)
      -> noutokens t
      -> proof ctxt (rule_introduction_hyp H C t e)
      -> proof ctxt (rule_introduction_concl H C t).



(* ===========================================================

  The library consists of a list of abstractions and proved lemmas.
  The difference with ProofContext is that we include the proofs of
  lemmas.  [Library2ProofContext] shows how to extract a proof context
  from a Library.

  ============================================================ *)

Definition name_not_in_lib {o} (name : LemmaName) (l : @library o) :=
  !in_lib (opname2opabs name) l.

(* !!MOVE *)
Lemma soterm2nterm_nterm2soterm {o} :
  forall (t : @NTerm o), soterm2nterm (nterm2soterm t) = t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; simpl; auto.
  Case "oterm".
  f_equal.
  rewrite map_map; unfold compose.
  apply eq_map_l; introv i.
  destruct x as [vs t]; simpl.
  f_equal.
  eapply ind; eauto.
Qed.
Hint Rewrite @soterm2nterm_nterm2soterm : slow.

(* !!MOVE *)
Lemma injective_fun_var2sovar : injective_fun var2sovar.
Proof.
  introv e.
  destruct a1, a2.
  unfold var2sovar in e; ginv; auto.
Qed.
Hint Resolve injective_fun_var2sovar : slow.

(* !!MOVE *)
Lemma so_free_vars_nterm2soterm {o} :
  forall (t : @NTerm o),
    so_free_vars (nterm2soterm t)
    = vars2sovars (free_vars t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; simpl; auto.
  rewrite flat_map_map; unfold compose.
  unfold vars2sovars.
  rewrite map_flat_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x as [vs t]; simpl.
  rewrite (ind t vs); auto.
  unfold remove_so_vars.
  unfold vars2sovars.
  rewrite <- (map_diff_commute deq_nvar); eauto 2 with slow.
Qed.
Hint Rewrite @so_free_vars_nterm2soterm : slow.

(* !!MOVE *)
Lemma get_utokens_so_nterm2soterm {o} :
  forall (t : @NTerm o),
    get_utokens_so (nterm2soterm t) = get_utokens t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; simpl; auto.
  f_equal.
  rewrite flat_map_map; unfold compose.
  apply eq_flat_maps; introv i.
  destruct x as [vs t]; simpl.
  eapply ind; eauto.
Qed.
Hint Rewrite @get_utokens_so_nterm2soterm : slow.

Lemma extract2correct {o} :
  forall (name : opname)
         (t    : @NTerm o)
         (v    : valid_extract t),
    correct_abs (opname2opabs name) [] (nterm2soterm t).
Proof.
  introv valid.
  destruct valid as [w v]; destruct v as [c n].
  unfold correct_abs; simpl.
  dands.
  - unfold wf_soterm.
    rewrite soterm2nterm_nterm2soterm; auto.
  - unfold socovered; simpl.
    rewrite so_free_vars_nterm2soterm.
    rewrite c; simpl; auto.
  - constructor.
  - constructor.
  - unfold no_utokens.
    rewrite get_utokens_so_nterm2soterm.
    rewrite n; auto.
Qed.

Definition extract2def {o}
           (name  : LemmaName)
           (ext   : @NTerm o)
           (valid : valid_extract ext) : library_entry :=
  lib_abs
    (opname2opabs name)
    []
    (nterm2soterm ext)
    (extract2correct name ext valid).

(*Inductive DepLibrary {o} : @ProofContext o -> Type :=
| DepLibrary_Empty :
    DepLibrary (MkProofContext o [] [])
| DepLibrary_Abs :
    forall {ctxt}
           (c : DepLibrary ctxt)
           (e : @library_entry o)
           (n : entry_not_in_lib e ctxt),
      DepLibrary (updLibProofContext ctxt e)
| DepLibrary_Proof :
    forall {ctxt}
           (c     : DepLibrary ctxt)
           (name  : LemmaName)
           (stmt  : @NTerm o)
           (ext   : NTerm)
           (valid : valid_extract ext)
           (p     : proof ctxt (Statement stmt ext))
           (n     : name_not_in_lib name ctxt),
      DepLibrary (updLibProofContext
                    (updConclProofContext ctxt (MkWfConcl (mk_concl stmt ext) valid))
                    (extract2def name ext valid)).*)

Inductive LibraryEntry {o} :=
| LibraryEntry_abs (e : @library_entry o)
| LibraryEntry_proof
    (ctxt  : @ProofContext o)
    (name  : LemmaName)
    (stmt  : NTerm)
    (ext   : NTerm)
    (isp   : isprog stmt)
    (valid : valid_extract ext)
    (prf   : proof ctxt (Statement stmt ext)).

(* A library is just a list of entries such that we store the most recent
   entry at the front of the list
 *)
Definition Library {o} := list (@LibraryEntry o).

Definition extend_proof_context {o} (ctxt : @ProofContext o) (e : LibraryEntry) : ProofContext :=
  match e with
  | LibraryEntry_abs e => updLibProofContext ctxt e
  | LibraryEntry_proof c name stmt ext isp valid prf =>
    updLibProofContext
      (updConclProofContext ctxt (MkNamedConcl name stmt))
      (extract2def name ext valid)
  end.

Definition ValidLibraryEntry {o} (ctxt : @ProofContext o) (e : LibraryEntry) : Type :=
  match e with
  | LibraryEntry_abs e => entry_not_in_lib e ctxt
  | LibraryEntry_proof c name stmt ext isp valid prf =>
    c = ctxt # name_not_in_lib name ctxt
  end.

Fixpoint Library2ProofContext {o} (L : @Library o) : ProofContext :=
  match L with
  | [] => EMPC
  | entry :: entries =>
    let ctxt := Library2ProofContext entries in
    extend_proof_context ctxt entry
  end.

Definition Library2lib {o} (L : @Library o) : library := Library2ProofContext L.

Fixpoint ValidLibrary {o} (L : @Library o) : Type :=
  match L with
  | [] => True
  | entry :: entries =>
    ValidLibraryEntry (Library2ProofContext entries) entry
    # ValidLibrary entries
  end.

Definition lemma_in_LibraryEntry {o}
           (s : @baresequent o)
           (e : LibraryEntry) : Type :=
  match e with
  | LibraryEntry_abs e => False
  | LibraryEntry_proof c name stmt ext isp valid prf =>
    s = mk_baresequent [] (mk_concl stmt ext)
  end.

Fixpoint lemma_in_Library {o}
         (s : @baresequent o)
         (l : Library) : Type :=
  match l with
  | [] => False
  | entry :: entries =>
    lemma_in_LibraryEntry s entry
    [+]
    lemma_in_Library s entries
  end.



(* ===========================================================

  We'll now prove that proofs are valid and that the sequents
  in the library are true.

  ============================================================ *)

(* By assuming [wf_bseq seq], when we start with a sequent with no hypotheses,
   it means that we have to prove that the conclusion is well-formed and closed.
 *)
Lemma valid_proof {o} :
  forall (ctxt : @ProofContext o) s (wf : wf_bseq s),
    (forall c H,
        LIn c (PC_conclusions ctxt)
        -> sequent_true_ext_lib_wf ctxt (named_concl2bseq H c))
    -> proof ctxt s
    -> sequent_true_ext_lib_wf ctxt s.
Proof.
  introv wf imp prf.

  induction prf
    as [ (* proved sequent            *) seq p
       | (* isect_eq                  *) a1 a2 b1 b2 e1 e2 x1 x2 y i hs niy p1 ih1 p2 ih2
       | (* isect_member_formation    *) A x B z i b e H nizH p1 ih1 p2 ih2
       | (* approx_refl               *) a hs
       | (* cequiv_approx             *) a b e1 e2 hs p1 ih1 p2 ih2
       | (* approx_eq                 *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       | (* cequiv_eq                 *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       (*| (* bottom_diverges         *) x hs js*)
       | (* cut                       *) B C t u x hs wB covB nixH p1 ih1 p2 ih2
       (*| (* equal_in_base           *) a b e F H p1 ih1 ps ihs*)
       | (* hypothesis                *) x A G J
       | (* cequiv_subst_concl        *) C x a b t e H wfa wfb cova covb p1 ih1 p2 ih2
       (*| (* approx_member_eq        *) a b e H p ih*)
       | (* cequiv_computation        *) a b H p ih
       | (* cequiv_computation_atmost *) a b n H p ih
       (*| (* function elimination    *) A B C a e ea f x z H J wa cova nizH nizJ dzf p1 ih1 p2 ih2*)
       | (* universe_equality         *) i j H
       | (* hypothesis_equality       *) x A G J
       | (* unhide_equality           *) x A t1 t2 C e G J ih1 p1
       | (* equality_equality         *) A B a1 a2 b1 b2 e1 e2 e3 i H p1 ih1 p2 ih2 p3 ih3
       | (* integer_equality          *) n H
       | (* introduction              *) t e C H wft covt nout p ih
       ];
    allsimpl;
    allrw NVin_iff; tcsp.

  - apply (rule_isect_equality2_true_ext_lib ctxt a1 a2 b1 b2 e1 e2 x1 x2 y i hs); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply ih1; auto.
        apply (rule_isect_equality2_wf2 y i a1 a2 b1 b2 e1 e2 x1 x2 hs); simpl; tcsp.

      * apply ih2; auto.
        apply (rule_isect_equality2_wf2 y i a1 a2 b1 b2 e1 e2 x1 x2 hs); simpl; tcsp.

  - apply (rule_isect_member_formation_true_ext_lib ctxt A B b e x z i H); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv xx; repndors; subst; tcsp.

      * apply ih1; auto.
        apply (rule_isect_member_formation_wf2 i z A B b e x H); simpl; tcsp.

      * apply ih2; auto.
        apply (rule_isect_member_formation_wf2 i z A B b e x H); simpl; tcsp.

  - apply (rule_approx_refl_true_ext_lib ctxt hs a); simpl; tcsp.

  - apply (rule_cequiv_approx2_true_ext_lib ctxt hs a b e1 e2); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    apply ih2; auto.
    apply (rule_cequiv_approx2_wf2 a b e1 e2 hs); simpl; tcsp.

  - apply (rule_approx_eq2_true_ext_lib ctxt a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_approx_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_approx_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

  - apply (rule_cequiv_eq2_true_ext_lib ctxt a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_cequiv_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_cequiv_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

  (*
  - apply (rule_bottom_diverges_true3 lib x hs js); simpl; tcsp.
*)

  - apply (rule_cut_true_ext_lib ctxt hs B C t u x); simpl; tcsp.

    + unfold args_constraints; simpl; introv xx; repndors; subst; tcsp.

    + introv xx; repndors; subst; tcsp.

      * apply ih1.
        apply (rule_cut_wf2 hs B C t u x); simpl; tcsp.

      * apply ih2.
        apply (rule_cut_wf2 hs B C t u x); simpl; tcsp.

(*  - apply (rule_equal_in_base2_true3 lib H a b e F); simpl; tcsp.

    introv xx; repndors; subst; tcsp.
    unfold rule_equal_in_base2_rest in xx; apply in_mapin in xx; exrepnd; subst.
    pose proof (ihs a0 i) as hh; clear ihs.
    repeat (autodimp hh hyp).
    pose proof (rule_equal_in_base2_wf2 H a b e F) as w.
    apply w; simpl; tcsp.
    right.
    apply in_mapin; eauto.*)

  - apply (rule_hypothesis_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_cequiv_subst_concl2_true_ext_lib ctxt H x C a b t e); allsimpl; tcsp.

    introv i; repndors; subst; allsimpl; tcsp.

    + apply ih1.
      apply (rule_cequiv_subst_concl2_wf2 H x C a b t e); simpl; tcsp.

    + apply ih2.
      apply (rule_cequiv_subst_concl2_wf2 H x C a b t e); simpl; tcsp.

(*  - apply (rule_approx_member_eq2_true3 lib a b e); simpl; tcsp.
    introv xx; repndors; subst; tcsp.
    apply ih.
    apply (rule_approx_member_eq2_wf2 a b e H); simpl; tcsp.*)

  - apply (rule_cequiv_computation_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_cequiv_computation_atmost_true_ext_lib ctxt a b n); simpl; tcsp.

(*  - apply (rule_function_elimination_true3 lib A B C a e ea f x z); simpl; tcsp.

    introv ih; repndors; subst; tcsp.

    + apply ih1.
      pose proof (rule_function_elimination_wf2 A B C a e ea f x z H J) as h.
      unfold wf_rule2, wf_subgoals2 in h; simpl in h.
      repeat (autodimp h hyp).

    + apply ih2.
      pose proof (rule_function_elimination_wf2 A B C a e ea f x z H J) as h.
      unfold wf_rule2, wf_subgoals2 in h; simpl in h.
      repeat (autodimp h hyp).
*)

  - apply (rule_universe_equality_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_hypothesis_equality_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_unhide_equality_true_ext_lib ctxt G J A C t1 t2 e x); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    apply p1; auto.
    apply (rule_unhide_equality_wf2 G J A C t1 t2 e x); simpl; tcsp.

  - apply (rule_equality_equality_true_ext_lib ctxt H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

    introv e; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_equality_equality_wf2 H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_equality_equality_wf2 H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

    + apply ih3; auto.
      apply (rule_equality_equality_wf2 H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

  - apply (rule_integer_equality_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_introduction_true_ext_lib ctxt H C t e); simpl; tcsp.

    { unfold args_constraints; simpl; introv i; repndors; tcsp; subst; simpl; auto. }

    introv xx; repndors; subst; tcsp.

    apply ih; auto.
    apply (rule_introduction_wf2 H C t e); simpl; tcsp; auto.
    eapply subvars_trans;[eauto|].
    apply subvars_hs_vars_hyps.
Qed.

Definition wf_ext {o} (H : @bhyps o) (c : @conclusion o) :=
  match c with
  | concl_ext C e => wf_term e # covered e (vars_hyps H) # noutokens e
  | concl_typ C => True
  end.

Lemma noutokens_var {o} : forall x, @noutokens o (mk_var x).
Proof.
  introv; compute; auto.
Qed.
Hint Resolve noutokens_var : slow.

(*Lemma wf_proof {o} :
  forall (ctxt : @ProofContext o) s,
    wf_hypotheses (hyps s)
    -> (forall c,
           in_wf_conclusions c (PC_conclusions ctxt)
           -> wf_ext [] c)
    -> proof ctxt s
    -> wf_ext (hyps s) (concl s).
Proof.
  introv wf imp prf.

  induction prf
    as [ (* proved sequent         *) seq p
       | (* isect_eq               *) a1 a2 b1 b2 e1 e2 x1 x2 y i hs niy p1 ih1 p2 ih2
       | (* isect_member_formation *) A x B z i b H nizH p1 ih1 p2 ih2
       | (* approx_refl            *) a hs
       | (* cequiv_approx          *) a b e1 e2 hs p1 ih1 p2 ih2
       | (* approx_eq              *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       | (* cequiv_eq              *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       (*| (* bottom_diverges      *) x hs js
       | (* cut                    *) B C t u x hs wB covB nixH p1 ih1 p2 ih2
       | (* equal_in_base          *) a b e F H p1 ih1 ps ihs*)
       | (* hypothesis             *) x A G J
       (*| (* cequiv_subst_concl   *) C x a b t e H wfa wfb cova covb p1 ih1 p2 ih2
       | (* approx_member_eq       *) a b e H p ih
       | (* cequiv_computation     *) a b H p ih
       | (* function elimination   *) A B C a e ea f x z H J wa cova nizH nizJ dzf p1 ih1 p2 ih2*)
       ];
    allsimpl;
    allrw NVin_iff; tcsp;
      try (complete (dands; eauto 2 with slow; apply covered_var;
                     rw @vars_hyps_app; rw @vars_hyps_snoc; simpl;
                     rw in_app_iff; rw in_snoc; tcsp)).
  autodimp ih1 hyp.
  apply wf_hypotheses_snoc; simpl; dands; auto.
Qed.*)

Hint Resolve isprogram_implies_wf : slow.

Lemma implies_wf_bseq_no_hyps {o} :
  forall (C e : @NTerm o),
    isprogram C
    -> valid_extract e
    -> wf_bseq (mk_bseq [] (mk_concl C e)).
Proof.
  introv isp valid.
  unfold wf_bseq; dands; simpl; tcsp; eauto 2 with slow.
  unfold closed_type_baresequent; simpl.
  unfold closed_type; simpl.
  unfold covered.
  apply closed_if_program in isp; rewrite isp; auto.
Qed.

(*Lemma lemma_in_Library_named_concl2bseq_iff {o} :
  forall (c : @named_concl o) L,
    lemma_in_Library (named_concl2bseq c) L
    <=> LIn c (PC_conclusions (Library2ProofContext L)).
Proof.
  induction L; simpl; split; introv h; tcsp.

  - repndors.

    + destruct a; simpl in *; tcsp.
      unfold named_concl2bseq, named_concl2concl in *; simpl in *.
      inversion h; subst; clear h.
      left.
      destruct c; simpl in *; ginv.
      ginv.
      subst; simpl in *.
      exists (MkNamedConcl name stmt); simpl.
      dands;[reflexivity|]; tcsp.

    + apply IHL in h; exrepnd; subst; clear IHL.
      eexists; dands;[reflexivity|]; tcsp.
      destruct a; simpl; tcsp.

  - exrepnd; subst.
    destruct a; simpl in *; tcsp.

    + right; apply IHL; clear IHL.
      eexists; dands;[reflexivity|]; tcsp.

    + unfold in_wf_conclusions in *; simpl in *; tcsp.
      repndors; subst; tcsp.
      right; apply IHL; clear IHL.
      eexists; dands;[reflexivity|]; tcsp.
Qed.*)

(*Lemma correct_library {o} :
  forall (L : Library) (s : @baresequent o),
    ValidLibrary L
    -> lemma_in_Library s L
    -> sequent_true_ext_lib_wf (Library2ProofContext L) s.
Proof.
  induction L; introv valid i; simpl in *; tcsp.
  repnd; repndors.

  - destruct a; simpl in *; tcsp.
    repnd; subst; simpl in *.

    assert (forall s,
               lemma_in_Library s L
               -> sequent_true_ext_lib_wf (Library2ProofContext L) s) as imp.
    { introv i; apply IHL; auto. }
    clear IHL.

    assert (forall c,
               LIn c (PC_conclusions (Library2ProofContext L))
               -> sequent_true_ext_lib_wf (Library2ProofContext L) (named_concl2bseq c)) as w.
    { introv i; apply imp; auto; clear imp.
      apply lemma_in_Library_iff.
      exists c; dands; auto. }
    clear imp.

    remember (Library2ProofContext L) as ctxt.

    apply sequent_true_mono_lib; auto.

    apply valid_proof; auto.
    apply implies_wf_bseq_no_hyps; eauto 3 with slow.

  - apply IHL in i; auto.
    destruct a; simpl in *; repnd; tcsp;
      apply sequent_true_mono_lib; auto.
Qed.*)



(* ===========================================================

  Nuprl state, i.e., a Library and a list of lemmas currently being proved.

  ============================================================ *)

Definition term2pre_baresequent {o} (t : @NTerm o) : pre_baresequent :=
  mk_pre_bseq [] (pre_concl_ext t).

Record pre_proof_seq {o} (ctxt : @ProofContext o) :=
  MkPreProofSeq
    {
      pre_proof_seq_name  : LemmaName;
      pre_proof_seq_term  : NTerm;
      pre_proof_seq_prog  : isprog pre_proof_seq_term;
      pre_proof_seq_proof : pre_proof ctxt (term2pre_baresequent pre_proof_seq_term)
    }.

Arguments MkPreProofSeq [o] [ctxt] _ _ _ _.

Arguments pre_proof_seq_name  [o] [ctxt] _.
Arguments pre_proof_seq_term  [o] [ctxt] _.
Arguments pre_proof_seq_proof [o] [ctxt] _.


Definition pre_proofs {o} (ctxt : @ProofContext o) :=
  list (pre_proof_seq ctxt).

Record NuprlState {o} :=
  MkNuprlState
    {
      NuprlState_lib        :> @Library o;
      NuprlState_unfinished : pre_proofs (Library2ProofContext NuprlState_lib);
    }.

Arguments MkNuprlState [o] _ _.



(* ===========================================================

  Commands to manipulate the state

  ============================================================ *)

Definition address := list nat.

Inductive proof_step {o} :=
| proof_step_isect_equality         (y : NVar)
| proof_step_isect_member_formation (z : NVar) (i : nat)
| proof_step_hypothesis             (x : NVar)
| proof_step_cut                    (x : NVar) (B : @NTerm o)
| proof_step_cequiv_computation     (n : nat)
| proof_step_cequiv_subst_concl     (x : NVar) (C a b : @NTerm o)
| proof_step_universe_equality
| proof_step_hypothesis_equality
| proof_step_unhide_equality        (x : NVar)
| proof_step_equality_equality
| proof_step_integer_equality
| proof_step_introduction           (t : @NTerm o)
| proof_step_lemma                  (name : LemmaName).

Inductive command {o} :=
(* add a definition at the head *)
| COM_add_def
    (opabs   : opabs)
    (vars    : list sovar_sig)
    (rhs     : @SOTerm o)
    (correct : correct_abs opabs vars rhs)
(* tries to complete a proof if it has no holes *)
| COM_finish_proof (name : LemmaName)
(* do a proof step *)
| COM_update_proof (name : LemmaName) (addr : address) (step : @proof_step o)
(* start a new proof *)
| COM_start_proof (name : LemmaName) (C : @NTerm o) (isp : isprog C)
(* print holes *)
| COM_find_holes (name : LemmaName).

(*(* focuses to a node in a proof *)
| COM_focus_proof (name : LemmaName) (addr : address)*)

Definition commands {o} := list (@command o).

Lemma in_conclusions_extend_proof_context {o} :
  forall (ctxt  : @ProofContext o)
         (entry : LibraryEntry)
         (c     : named_concl)
         (i     : LIn c (PC_conclusions ctxt)),
    LIn c (PC_conclusions (extend_proof_context ctxt entry)).
Proof.
  introv i.
  destruct entry; simpl in *; auto.
Qed.

Definition LibraryEntry2opabs {o} (e : @LibraryEntry o) : opabs :=
  match e with
  | LibraryEntry_abs e => opabs_of_lib_entry e
  | LibraryEntry_proof c name stmt ext isp valid prf => opname2opabs name
  end.

Definition entry_in_lib {o} (e : @LibraryEntry o) (l : @library o) :=
  in_lib (LibraryEntry2opabs e) l.

Lemma entry_in_library_implies_in_lib {o} :
  forall (entry e : @library_entry o) l,
    entry_in_library entry l
    -> matching_entries entry e
    -> in_lib (opabs_of_lib_entry e) l.
Proof.
  induction l; introv i m; simpl in *; tcsp.
  repndors; repnd; subst; tcsp.

  - exists a; simpl; dands; tcsp.
    apply matching_entry_sign_sym; auto.

  - repeat (autodimp IHl hyp).
    unfold in_lib in IHl; exrepnd.
    exists e0; simpl; dands; tcsp.
Qed.

Lemma lib_extends_if_not_in_lib {o} :
  forall (e : @library_entry o) l,
    !in_lib (opabs_of_lib_entry e) l
    -> lib_extends (e :: l) l.
Proof.
  introv ni i; simpl.
  right; dands; auto.
  intro h.
  destruct ni.
  eapply entry_in_library_implies_in_lib; eauto.
Qed.

Lemma extend_proof_context_preserves_reduces_to {o} :
  forall (ctxt : @ProofContext o) (e : LibraryEntry) a b,
    !entry_in_lib e ctxt
    -> reduces_to ctxt a b
    -> reduces_to (extend_proof_context ctxt e) a b.
Proof.
  introv ni r.
  destruct e; simpl in *.

  - unfold entry_in_lib in ni; simpl in ni.
    eapply reduces_to_preserves_lib_extends;[|exact r].
    apply lib_extends_if_not_in_lib; auto.

  - unfold entry_in_lib in ni; simpl in ni.
    eapply reduces_to_preserves_lib_extends;[|exact r].
    apply lib_extends_if_not_in_lib; simpl; auto.
Qed.

Lemma extend_proof_context_preserves_reduces_in_atmost_k_steps {o} :
  forall (ctxt : @ProofContext o) (e : LibraryEntry) a b n,
    !entry_in_lib e ctxt
    -> reduces_in_atmost_k_steps ctxt a b n
    -> reduces_in_atmost_k_steps (extend_proof_context ctxt e) a b n.
Proof.
  introv ni r.
  destruct e; simpl in *.

  - unfold entry_in_lib in ni; simpl in ni.
    eapply reduces_in_atmost_k_steps_preserves_lib_extends;[|exact r].
    apply lib_extends_if_not_in_lib; auto.

  - unfold entry_in_lib in ni; simpl in ni.
    eapply reduces_in_atmost_k_steps_preserves_lib_extends;[|exact r].
    apply lib_extends_if_not_in_lib; simpl; auto.
Qed.

Fixpoint pre_proof_cons {o}
         {ctxt  : @ProofContext o}
         (entry : LibraryEntry)
         (ni    : !entry_in_lib entry ctxt)
         {s     : pre_baresequent}
         (p     : pre_proof ctxt s)
  : pre_proof (extend_proof_context ctxt entry) s :=
  match p with
  | pre_proof_from_ctxt _ c H i =>
    pre_proof_from_ctxt _ c H (in_conclusions_extend_proof_context ctxt entry c i)

  | pre_proof_hole _ s => pre_proof_hole _ s

  | pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1' prf2'

  | pre_proof_isect_member_formation _ A x B z i H nizH prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_isect_member_formation _ A x B z i H nizH prf1' prf2'

  | pre_proof_approx_refl _ a H => pre_proof_approx_refl _ a H

  | pre_proof_cequiv_approx _ a b H prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_cequiv_approx _ a b H prf1' prf2'

  | pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1' prf2'

  | pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1' prf2'

  | pre_proof_cut _ B C x H wfB covB nixH prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_cut _ B C x H wfB covB nixH prf1' prf2'

  | pre_proof_hypothesis _ x A G J => pre_proof_hypothesis _ x A G J

  | pre_proof_cequiv_subst_concl _ C x a b H wfa wfb cova covb prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_cequiv_subst_concl _ C x a b H wfa wfb cova covb prf1' prf2'

  | pre_proof_cequiv_computation _ a b H r =>
    pre_proof_cequiv_computation
      _ a b H
      (extend_proof_context_preserves_reduces_to ctxt entry a b ni r)

  | pre_proof_cequiv_computation_atmost _ a b n H r =>
    pre_proof_cequiv_computation_atmost
      _ a b n H
      (extend_proof_context_preserves_reduces_in_atmost_k_steps ctxt entry a b n ni r)

  | pre_proof_universe_equality _ i j H ltij => pre_proof_universe_equality _ i j H ltij

  | pre_proof_hypothesis_equality _ x A G J => pre_proof_hypothesis_equality _ x A G J

  | pre_proof_unhide_equality _ x A t1 t2 C G J prf =>
    let prf' := pre_proof_cons entry ni prf in
    pre_proof_unhide_equality _ x A t1 t2 C G J prf'

  | pre_proof_equality_equality _ A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    let prf3' := pre_proof_cons entry ni prf3 in
    pre_proof_equality_equality _ A B a1 a2 b1 b2 i H prf1' prf2' prf3'

  | pre_proof_integer_equality _ n H => pre_proof_integer_equality _ n H

  | pre_proof_introduction _ t C H wft covt nout prf =>
    let prf' := pre_proof_cons entry ni prf in
    pre_proof_introduction _ t C H wft covt nout prf'
  end.

Definition pre_proof_seq_cons {o}
           {ctxt  : @ProofContext o}
           (entry : LibraryEntry)
           (ni    : !entry_in_lib entry ctxt)
           (pps   : pre_proof_seq ctxt)
  : pre_proof_seq (extend_proof_context ctxt entry) :=
  match pps with
  | MkPreProofSeq name C isp prf => MkPreProofSeq name C isp (pre_proof_cons entry ni prf)
  end.

Definition pre_proofs_cons {o}
           {ctxt  : @ProofContext o}
           (entry : LibraryEntry)
           (ni    : !entry_in_lib entry ctxt)
           (l     : pre_proofs ctxt)
  : pre_proofs (extend_proof_context ctxt entry) :=
  map (pre_proof_seq_cons entry ni) l.

Lemma in_lib_dec {o} :
  forall (opabs : opabs)
         (lib   : @library o),
    decidable (in_lib opabs lib).
Proof.
  unfold in_lib; induction lib; simpl.
  - right; intro xx; exrepnd; auto.
  - destruct a.
    destruct (same_opabs_dec opabs opabs0) as [d|d]; ginv.
    + left; eexists; eexists; eauto.
    + destruct IHlib as [k|k]; exrepnd.
      * left.
        exrepnd.
        eexists; eexists; eauto.
      * right; intro xx; exrepnd; repndors; subst; allsimpl; tcsp.
        destruct k; eexists; eexists; eauto.
Defined.

Lemma entry_in_lib_dec {o} :
  forall (entry : @LibraryEntry o)
         (lib   : @library o),
    decidable (entry_in_lib entry lib).
Proof.
  unfold entry_in_lib; introv.
  apply in_lib_dec.
Defined.

Record Hole {o} :=
  MkHole
    {
      hole_seq  : @pre_baresequent o;
      hole_addr : address;
    }.

Arguments MkHole [o] _ _.
Arguments hole_seq [o] _.
Arguments hole_addr [o] _.

Definition Holes {o} := list (@Hole o).

Inductive DEBUG_MSG {o} :=
| could_not_add_definition_because_definition_already_in_library
| added_definition

| started_proof

| could_not_apply_isect_eq_rule_not_isects
| could_not_apply_isect_eq_rule_type_not_universe
| could_not_apply_isect_eq_rule_not_equality
| could_not_apply_isect_eq_rule
| applied_isect_eq_rule

| could_not_apply_universe_eq_rule_not_universes
| could_not_apply_universe_eq_rule_type_not_universe
| could_not_apply_universe_eq_rule_not_equality
| could_not_apply_universe_eq_rule
| applied_universe_eq_rule

| could_not_apply_isect_member_formation_rule_not_isect
| could_not_apply_isect_member_formation_rule
| applied_isect_member_formation_rule

| could_not_apply_cequiv_computation_atmost_rule_not_cequiv
| could_not_apply_cequiv_computation_atmost_rule
| applied_cequiv_computation_atmost_rule

| could_not_apply_cequiv_computation_rule_not_cequiv
| could_not_apply_cequiv_computation_rule
| applied_cequiv_computation_rule

| could_not_apply_cequiv_subst_concl_rule_not_subst
| could_not_apply_cequiv_subst_concl_rule
| applied_cequiv_subst_concl_rule

| could_not_apply_hypothesis_rule_because_different_types (A B : @NTerm o)
| could_not_apply_hypothesis_rule_because_couldnt_find_hypothesis
| could_not_apply_hypothesis_rule
| applied_hypothesis_rule

| could_not_apply_hypothesis_equality_rule
| applied_hypothesis_equality_rule

| could_not_apply_lemma_rule
| applied_lemma_rule

| could_not_apply_unhide_equality_rule
| applied_unhide_equality_rule

| could_not_apply_equality_equality_rule
| applied_equality_equality_rule

| could_not_apply_introduction_rule
| applied_introduction_rule

| could_not_apply_integer_equality_rule
| applied_integer_equality_rule

| could_not_apply_cut_rule
| applied_cut_rule

| could_not_apply_update_because_wrong_address
| could_not_apply_update_because_no_hole_at_address
| could_not_apply_update_because_could_not_find_lemma

| found_holes (holes : @Holes o)
| could_not_find_holes_because_could_not_find_lemma

| finished_proof
| could_not_finish_proof
| could_not_finish_proof_because_entry_exists_in_lib
| could_not_finish_proof_because_could_not_find_lemma.

Definition NuprlState_add_def {o}
           (state   : @NuprlState o)
           (opabs   : opabs)
           (vars    : list sovar_sig)
           (rhs     : SOTerm)
           (correct : correct_abs opabs vars rhs) : NuprlState * @DEBUG_MSG o :=
  match state with
  | MkNuprlState L unfinished =>
    let entry := LibraryEntry_abs (lib_abs opabs vars rhs correct) in

    match entry_in_lib_dec entry (Library2lib L) with
    | inl p => (state, could_not_add_definition_because_definition_already_in_library)
    | inr p =>
      (MkNuprlState
         (entry :: L)
         (pre_proofs_cons entry p unfinished),
       added_definition)
    end
  end.

Fixpoint find_unfinished_in_pre_proofs {o} {ctxt}
         (l : @pre_proofs o ctxt)
         (n : LemmaName)
  : option (pre_proof_seq ctxt) * pre_proofs ctxt :=
  match l with
  | [] => (None, [])
  | pp :: pps =>
    if LemmaNameDeq n (pre_proof_seq_name pp) then
      (Some pp, pps)
    else
      let (ppop, pps') := find_unfinished_in_pre_proofs pps n in
      (ppop, pp :: pps')
  end.

Lemma name_of_find_unfinished_in_pre_proofs {o} :
  forall {ctxt}
         (l  : @pre_proofs o ctxt)
         (n  : LemmaName)
         (p  : pre_proof_seq ctxt)
         (ps : pre_proofs ctxt),
    find_unfinished_in_pre_proofs l n = (Some p, ps)
    -> pre_proof_seq_name p = n.
Proof.
  induction l; introv h; simpl in *; ginv.
  boolvar; ginv; cpx.
  remember (find_unfinished_in_pre_proofs l n) as f; symmetry in Heqf; destruct f; cpx.
  apply IHl in Heqf; auto.
Qed.

Definition pre2conclusion {o} (c : @pre_conclusion o) (e : @NTerm o) :=
  match c with
  | pre_concl_ext T => concl_ext T e
  | pre_concl_typ T => concl_typ T
  end.

Definition pre2baresequent {o} (s : @pre_baresequent o) (e : @NTerm o) :=
  mk_baresequent
    (pre_hyps s)
    (pre2conclusion (pre_concl s) e).

Definition valid_pre_extract {o} (H : @bhyps o) (t : @NTerm o) : Prop :=
  wf_term t # covered t (nh_vars_hyps H) # noutokens t.

Record ExtractProof {o} ctxt (seq : @pre_baresequent o) :=
  MkExtractProof
    {
      extract_proof_extract : NTerm;
      extract_proof_valid   : valid_pre_extract (pre_hyps seq) extract_proof_extract;
      extract_proof_proof   : proof ctxt (pre2baresequent seq extract_proof_extract);
    }.

Arguments MkExtractProof [o] [ctxt] [seq] _ _ _.

Lemma valid_extract_axiom {o} : @valid_extract o mk_axiom.
Proof.
  unfold valid_extract; dands; eauto 2 with slow.
  compute; auto.
Qed.

Lemma valid_extract_implies_valid_pre_extract_nil {o} :
  forall (t : @NTerm o),
    valid_extract t -> valid_pre_extract [] t.
Proof.
  introv v.
  unfold valid_extract in v; repnd.
  unfold valid_pre_extract; simpl; dands; auto.
  unfold nh_vars_hyps; simpl; auto.
  unfold covered; allrw; auto.
Qed.
Hint Resolve valid_extract_implies_valid_pre_extract_nil : slow.

Lemma valid_pre_extract_axiom {o} : forall H, @valid_pre_extract o H mk_axiom.
Proof.
  introv; unfold valid_pre_extract; dands; eauto 2 with slow.
  compute; auto.
Qed.

Lemma valid_pre_extract_mk_abs_opname2opabs {o} :
  forall name (H : @bhyps o), valid_pre_extract H (mk_abs (opname2opabs name) []).
Proof.
  introv; unfold valid_pre_extract; dands; eauto 2 with slow;
    try (complete (compute;auto));
    try (complete (unfold covered; simpl; auto)).
Qed.

(* Why can't I define these? *)
Definition finish_proof_from_context {o}
           (ctxt : ProofContext)
           (c    : @named_concl o)
           (H    : bhyps)
           (i    : LIn c (PC_conclusions ctxt))
  : ExtractProof ctxt (named_concl2pre_bseq H c).
Proof.
  destruct c as [name T]; simpl in *.

  exists (@mk_abs o (opname2opabs name) []).

  { simpl in *; apply valid_pre_extract_mk_abs_opname2opabs. }

  unfold pre2baresequent; simpl.
  exact (proof_from_ctxt _ (MkNamedConcl name T) H i).
Defined.

Definition finish_proof_isect_eq {o}
           (ctxt : @ProofContext o)
           (a1 a2 b1 b2 : NTerm)
           (x1 x2 y : NVar)
           (i : nat)
           (H : bhyps)
           (ni : NVin y (vars_hyps H))
           (p1 : ExtractProof ctxt (pre_rule_isect_equality_hyp1 a1 a2 i H))
           (p2 : ExtractProof ctxt (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H))
  : ExtractProof ctxt (pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_isect_eq _ a1 a2 b1 b2 e1 e2 x1 x2 y i H ni q1 q2).
Defined.

Lemma valid_pre_extract_snoc_mk_hhyp_implies {o} :
  forall (H : @bhyps o) (z : NVar) (A e : NTerm),
    valid_pre_extract (snoc H (mk_hhyp z A)) e
    -> valid_pre_extract H e.
Proof.
  introv val.
  unfold valid_pre_extract in *; simpl in *.
  allrw @nh_vars_hyps_snoc; simpl in *; auto.
Qed.

Definition finish_proof_isect_member_formation {o}
           (ctxt : @ProofContext o)
           (A : NTerm)
           (x : NVar)
           (B : NTerm)
           (z : NVar)
           (i : nat)
           (H : bhyps)
           (ni : NVin z (vars_hyps H))
           (p1 : ExtractProof ctxt (pre_rule_isect_member_formation_hyp1 z A x B H))
           (p2 : ExtractProof ctxt (pre_rule_isect_member_formation_hyp2 A i H))
  : ExtractProof ctxt (pre_rule_isect_member_formation_concl A x B H).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  exists e1.
  { simpl; eapply valid_pre_extract_snoc_mk_hhyp_implies; eauto. }
  unfold pre2baresequent; simpl.
  exact (proof_isect_member_formation _ A x B z i e1 e2 H ni q1 q2).
Defined.

Definition finish_proof_approx_refl {o}
           (ctxt : @ProofContext o)
           (a : NTerm)
           (H : bhyps)
  : ExtractProof ctxt (pre_rule_approx_refl_concl a H).
Proof.
  introv.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_approx_refl _ a H).
Defined.

Definition finish_proof_cequiv_approx {o}
           (ctxt : @ProofContext o)
           (a b : NTerm)
           (H : bhyps)
           (p1 : ExtractProof ctxt (pre_rule_cequiv_approx_hyp a b H))
           (p2 : ExtractProof ctxt (pre_rule_cequiv_approx_hyp b a H))
  : ExtractProof ctxt (pre_rule_cequiv_approx_concl a b H).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_cequiv_approx _ a b e1 e2 H q1 q2).
Defined.

Definition finish_proof_approx_eq {o}
           (ctxt : @ProofContext o)
           (a1 a2 b1 b2 : NTerm)
           (i : nat)
           (H : bhyps)
           (p1 : ExtractProof ctxt (pre_rule_eq_base_hyp a1 a2 H))
           (p2 : ExtractProof ctxt (pre_rule_eq_base_hyp b1 b2 H))
  : ExtractProof ctxt (pre_rule_approx_eq_concl a1 a2 b1 b2 i H).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_approx_eq _ a1 a2 b1 b2 e1 e2 i H q1 q2).
Defined.

Definition finish_proof_cequiv_eq {o}
           (ctxt : @ProofContext o)
           (a1 a2 b1 b2 : NTerm)
           (i : nat)
           (H : bhyps)
           (p1 : ExtractProof ctxt (pre_rule_eq_base_hyp a1 a2 H))
           (p2 : ExtractProof ctxt (pre_rule_eq_base_hyp b1 b2 H))
  : ExtractProof ctxt (pre_rule_cequiv_eq_concl a1 a2 b1 b2 i H).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_cequiv_eq _ a1 a2 b1 b2 e1 e2 i H q1 q2).
Defined.

Lemma implies_valid_pre_extract_subst {o} :
  forall (H : @bhyps o) x C e1 e2,
    valid_pre_extract H e1
    -> valid_pre_extract (snoc H (mk_hyp x C)) e2
    -> valid_pre_extract H (subst e2 x e1).
Proof.
  introv v1 v2.
  unfold valid_pre_extract in *.
  allrw @nh_vars_hyps_snoc; simpl in *.
  repnd.
  dands; auto.

  - apply wf_term_subst; auto.

  - apply covered_subst; auto.
    unfold covered in *.
    allrw subvars_prop; introv i; simpl.
    discover; allrw in_snoc; tcsp.

  - unfold noutokens in *.
    apply null_iff_nil.
    introv i.
    apply get_utokens_subst in i.
    rewrite v1 in i.
    rewrite v2 in i.
    simpl in i; boolvar; simpl in *; tcsp.
Qed.

Definition finish_proof_cut {o}
           (ctxt : @ProofContext o)
           (B C : NTerm)
           (x : NVar)
           (H : bhyps)
           (wfB : wf_term B)
           (covB : covered B (vars_hyps H))
           (nixH : NVin x (vars_hyps H))
           (p1 : ExtractProof ctxt (pre_rule_cut_hyp1 H B))
           (p2 : ExtractProof ctxt (pre_rule_cut_hyp2 H x B C))
  : ExtractProof ctxt (pre_rule_cut_concl H C).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  exists (subst e2 x e1).
  { simpl; eapply implies_valid_pre_extract_subst; eauto. }
  unfold pre2baresequent; simpl.
  exact (proof_cut _ B C e2 e1 x H wfB covB nixH q1 q2).
Defined.

Definition finish_proof_hypothesis {o}
           (ctxt : @ProofContext o)
           (x : NVar)
           (A : NTerm)
           (G J : bhyps)
  : ExtractProof ctxt (pre_rule_hypothesis_concl G J A x).
Proof.
  introv.
  exists (@mk_var o x).
  { unfold valid_pre_extract; dands; simpl; eauto 2 with slow.
    apply covered_var; rw @nh_vars_hyps_app; rw @nh_vars_hyps_snoc; simpl.
    rw in_app_iff; rw in_snoc; tcsp. }
  unfold pre2baresequent; simpl.
  exact (proof_hypothesis _ x A G J).
Defined.

Definition finish_proof_cequiv_subst_concl {o}
           (ctxt : @ProofContext o)
           (C : NTerm)
           (x : NVar)
           (a b : NTerm)
           (H : bhyps)
           (wfa : wf_term a)
           (wfb : wf_term b)
           (cova : covered a (vars_hyps H))
           (covb : covered b (vars_hyps H))
           (p1 : ExtractProof ctxt (pre_rule_cequiv_subst_hyp1 H x C b))
           (p2 : ExtractProof ctxt (pre_rule_cequiv_subst_hyp2 H a b))
  : ExtractProof ctxt (pre_rule_cequiv_subst_hyp1 H x C a).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  exists e1; auto;[].
  unfold pre2baresequent; simpl.
  exact (proof_cequiv_subst_concl _ C x a b e1 e2 H wfa wfb cova covb q1 q2).
Defined.

Definition finish_proof_cequiv_computation {o}
           (ctxt : @ProofContext o)
           (a b : NTerm)
           (H : bhyps)
           (r : reduces_to ctxt a b)
  : ExtractProof ctxt (pre_rule_cequiv_computation_concl a b H).
Proof.
  introv.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_cequiv_computation _ a b H r).
Defined.

Definition finish_proof_cequiv_computation_atmost {o}
           (ctxt : @ProofContext o)
           (a b : NTerm)
           (n : nat)
           (H : bhyps)
           (r : reduces_in_atmost_k_steps ctxt a b n)
  : ExtractProof ctxt (pre_rule_cequiv_computation_concl a b H).
Proof.
  introv.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_cequiv_computation_atmost _ a b n H r).
Defined.

Definition finish_proof_universe_equality {o}
           (ctxt : @ProofContext o)
           (i j : nat)
           (H : bhyps)
           (ltij : i < j)
  : ExtractProof ctxt (pre_rule_universe_equality_concl H i j).
Proof.
  introv.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_universe_equality _ i j H ltij).
Defined.

Definition finish_proof_hypothesis_equality {o}
           (ctxt : @ProofContext o)
           (x : NVar)
           (A : NTerm)
           (G J : bhyps)
  : ExtractProof ctxt (pre_rule_hypothesis_equality_concl G J A x).
Proof.
  introv.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_hypothesis_equality _ x A G J).
Defined.

Definition finish_proof_unhide_equality {o}
           (ctxt : @ProofContext o)
           (x : NVar)
           (A t1 t2 C : NTerm)
           (G J : bhyps)
           (p : ExtractProof ctxt (pre_rule_unhide_equality_hyp G J x A t1 t2 C))
  : ExtractProof ctxt (pre_rule_unhide_equality_concl G J x A t1 t2 C).
Proof.
  introv.
  destruct p as [e v q].
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_unhide_equality _ x A t1 t2 C e G J q).
Defined.

Definition finish_proof_equality_equality {o}
           (ctxt : @ProofContext o)
           (A B a1 a2 b1 b2 : NTerm)
           (i : nat)
           (H : bhyps)
           (p1 : ExtractProof ctxt (pre_rule_equality_equality_hyp1 H A B i))
           (p2 : ExtractProof ctxt (pre_rule_equality_equality_hyp2 H a1 b1 A))
           (p3 : ExtractProof ctxt (pre_rule_equality_equality_hyp2 H a2 b2 A))
  : ExtractProof ctxt (pre_rule_equality_equality_concl H a1 a2 b1 b2 A B i).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  destruct p3 as [e3 v3 q3].
  unfold pre2baresequent in *; simpl in *.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_equality_equality _ A B a1 a2 b1 b2 e1 e2 e3 i H q1 q2 q3).
Defined.

Definition finish_proof_integer_equality {o}
           (ctxt : @ProofContext o)
           (n : Z)
           (H : bhyps)
  : ExtractProof ctxt (pre_rule_integer_equality_concl H n).
Proof.
  introv.
  exists (@mk_axiom o).
  { apply valid_pre_extract_axiom. }
  unfold pre2baresequent; simpl.
  exact (proof_integer_equality _ n H).
Defined.

Definition finish_proof_introduction {o}
           (ctxt : @ProofContext o)
           (t C : NTerm)
           (H : bhyps)
           (wft : wf_term t)
           (covt : covered t (nh_vars_hyps H))
           (nout : noutokens t)
           (p : ExtractProof ctxt (pre_rule_introduction_hyp H C t))
  : ExtractProof ctxt (pre_rule_introduction_concl H C).
Proof.
  introv.
  destruct p as [e v q].
  exists t.
  { simpl; unfold valid_pre_extract; dands; auto. }
  unfold pre2baresequent; simpl.
  exact (proof_introduction _ t e C H wft covt nout q).
Defined.

Fixpoint finish_pre_proof {o}
         {ctxt  : @ProofContext o}
         {s     : pre_baresequent}
         (p     : pre_proof ctxt s)
  : option (ExtractProof ctxt s) :=
  match p with
  | pre_proof_from_ctxt _ c H i => Some (finish_proof_from_context ctxt c H i)

  | pre_proof_hole _ s => None

  | pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_isect_eq ctxt a1 a2 b1 b2 x1 x2 y i H niyH p1 p2)
    | _, _ => None
    end

  | pre_proof_isect_member_formation _ A x B z i H nizH prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_isect_member_formation ctxt A x B z i H nizH p1 p2)
    | _, _ => None
    end

  | pre_proof_approx_refl _ a H => Some (finish_proof_approx_refl ctxt a H)

  | pre_proof_cequiv_approx _ a b H prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_cequiv_approx ctxt a b H p1 p2)
    | _, _ => None
    end

  | pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_approx_eq ctxt a1 a2 b1 b2 i H p1 p2)
    | _, _ => None
    end

  | pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_cequiv_eq ctxt a1 a2 b1 b2 i H p1 p2)
    | _, _ => None
    end

  | pre_proof_cut _ B C x H wfB covB nixH prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_cut ctxt B C x H wfB covB nixH p1 p2)
    | _, _ => None
    end

  | pre_proof_hypothesis _ x A G J => Some (finish_proof_hypothesis ctxt x A G J)

  | pre_proof_cequiv_subst_concl _ C x a b H wfa wfb cova covb prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_cequiv_subst_concl ctxt C x a b H wfa wfb cova covb p1 p2)
    | _, _ => None
    end

  | pre_proof_cequiv_computation _ a b H r =>
    Some (finish_proof_cequiv_computation ctxt a b H r)

  | pre_proof_cequiv_computation_atmost _ a b n H r =>
    Some (finish_proof_cequiv_computation_atmost ctxt a b n H r)

  | pre_proof_universe_equality _ i j H ltij =>
    Some (finish_proof_universe_equality ctxt i j H ltij)

  | pre_proof_hypothesis_equality _ x A G J =>
    Some (finish_proof_hypothesis_equality ctxt x A G J)

  | pre_proof_unhide_equality _ x A t1 t2 C G J prf =>
    match finish_pre_proof prf with
    | Some p => Some (finish_proof_unhide_equality ctxt x A t1 t2 C G J p)
    | _ => None
    end

  | pre_proof_equality_equality _ A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
    match finish_pre_proof prf1,
          finish_pre_proof prf2,
          finish_pre_proof prf3 with
    | Some p1, Some p2, Some p3 =>
      Some (finish_proof_equality_equality ctxt A B a1 a2 b1 b2 i H p1 p2 p3)
    | _, _, _ => None
    end

  | pre_proof_integer_equality _ n H =>
    Some (finish_proof_integer_equality ctxt n H)

  | pre_proof_introduction _ t C H wft covt nout prf =>
    match finish_pre_proof prf with
    | Some p => Some (finish_proof_introduction ctxt t C H wft covt nout p)
    | _ => None
    end
  end.

Lemma valid_pre_extract_nil_implies_valid_extract {o} :
  forall {t : @NTerm o}, valid_pre_extract [] t -> valid_extract t.
Proof.
  introv v.
  unfold valid_pre_extract in v; repnd.
  unfold valid_extract; simpl; dands; auto.
  unfold nh_vars_hyps in *; simpl in *; auto.
  unfold covered in *.
  allrw @subvars_nil_r; auto.
Qed.
Hint Resolve valid_pre_extract_nil_implies_valid_extract : slow.

Definition finish_pre_proof_seq {o}
           {ctxt : @ProofContext o}
           (pps  : pre_proof_seq ctxt)
  : option LibraryEntry :=
  match pps with
  | MkPreProofSeq name C isp pre_prf =>
    match finish_pre_proof pre_prf with
    | Some (MkExtractProof ext valid prf) =>

      Some (LibraryEntry_proof
              ctxt
              name
              C
              ext
              isp
              (valid_pre_extract_nil_implies_valid_extract valid)
              prf)

    | None => None
    end
  end.

Lemma name_of_finish_pre_proof_seq {o} :
  forall {ctxt}
         (p     : @pre_proof_seq o ctxt)
         (name  : LemmaName)
         (stmt  : NTerm)
         (ext   : NTerm)
         (isp   : isprog stmt)
         (valid : valid_extract ext)
         (prf   : proof ctxt (Statement stmt ext)),
    finish_pre_proof_seq p = Some (LibraryEntry_proof ctxt name stmt ext isp valid prf)
    -> pre_proof_seq_name p = name.
Proof.
  introv h.
  unfold finish_pre_proof_seq in h.
  destruct p; simpl in *.
  remember (finish_pre_proof pre_proof_seq_proof0) as fin; symmetry in Heqfin;
    destruct fin; ginv.
  destruct e; ginv; cpx.
  inversion h; auto.
Qed.

Definition NuprlState_add_entry {o}
           (state : @NuprlState o)
           (entry : LibraryEntry)
  : !entry_in_lib entry (Library2ProofContext state)
    -> pre_proofs (Library2ProofContext state)
    -> NuprlState :=
  match state with
  | MkNuprlState L _ =>
    fun ni pps => MkNuprlState (entry :: L)
                               (pre_proofs_cons entry ni pps)
  end.

Definition NuprlState_finish_proof {o}
           (state : @NuprlState o)
           (name  : LemmaName) : NuprlState * @DEBUG_MSG o :=
  match find_unfinished_in_pre_proofs (NuprlState_unfinished state) name with
  | (Some pp, pps) =>

    match finish_pre_proof_seq pp with
    | Some entry =>

      match entry_in_lib_dec entry (Library2lib state) with
      | inl p => (state, could_not_finish_proof_because_entry_exists_in_lib)
      | inr p => (NuprlState_add_entry state entry p pps, finished_proof)
      end

    | None => (state, could_not_finish_proof)
    end

  | (None, pps) => (state, could_not_finish_proof_because_could_not_find_lemma)
  end.

Definition NuprlState_change_unfinished {o}
           (state : @NuprlState o)
  : pre_proofs (Library2ProofContext state) -> NuprlState :=
  match state with
  | MkNuprlState L _ => fun l => MkNuprlState L l
  end.

Definition pre_concl2type {o} (c : @pre_conclusion o) : option NTerm :=
  match c with
  | pre_concl_ext t => Some t
  | pre_concl_typ t => None
  end.

Definition destruct_equality {o} (t : @NTerm o) : option (NTerm * NTerm * NTerm) :=
  match t with
  | oterm (Can NEquality) [bterm [] a, bterm [] b, bterm [] c] => Some (a, b, c)
  | _ => None
  end.

Definition destruct_universe {o} (t : @NTerm o) : option nat :=
  match t with
  | oterm (Can (NUni i)) [] => Some i
  | _ => None
  end.

Definition destruct_intersection {o} (t : @NTerm o) : option (NTerm * NVar * NTerm) :=
  match t with
  | oterm (Can NIsect) [bterm [] a, bterm [v] b] => Some (a, v, b)
  | _ => None
  end.

Definition destruct_isect_eq {o}
           (H : @barehypotheses o)
           (C : @pre_conclusion o)
           (y : NVar)
  : option (NTerm * NTerm * NVar * NVar * NTerm * NTerm * nat * NVin y (vars_hyps H)) :=
  match NVin_dec y (vars_hyps H) with
  | inl p =>

    match pre_concl2type C with
    | Some T =>

      match destruct_equality T with
      | Some (T1, T2, U) =>

        match destruct_universe U with
        | Some i =>

          match destruct_intersection T1, destruct_intersection T2 with
          | Some (a1, x1, b1), Some (a2, x2, b2) =>
            Some (a1, a1, x1, x2, b1, b2, i, p)

          | _, _ => None
          end

        | None => None
        end

      | None => None
      end

    | None => None
    end

  | _ => None
  end.

Ltac use_hole :=
  match goal with
  | [ |- pre_proof _ ?s ] => exact (pre_proof_hole _ s)
  end.

(*
(* This doesn't work because the returned type is not for the sequent [s] but for the
   isect one, which is computationally equivalent.  Can we do something about it?
   I define it more directly below.
   What will we do when we'll have to find an hypothesis in a list of hypotheses?
*)
Definition apply_proof_step {o} {ctxt}
           (s    : @pre_baresequent o)
           (step : proof_step) : pre_proof ctxt s :=
  match step with
  | proof_set_isect_eq y =>
    let H := pre_hyps  s in
    let C := pre_concl s in
    match destruct_isect_eq H C y with
    | Some (a1, a2, x1, x2, b1, b2, i, niyH) =>

      let prf1 := pre_proof_hole ctxt (pre_rule_isect_equality_hyp1 a1 a2 i H) in
      let prf2 := pre_proof_hole ctxt (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H) in
      pre_proof_isect_eq ctxt a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2

    | None => pre_proof_hole _ s
    end
  end.
 *)

Definition apply_proof_step_isect_eq {o} {ctxt}
           (s : @pre_baresequent o)
           (y : NVar) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match NVin_dec y (vars_hyps H) with
    | inl p =>

      match C return pre_proof ctxt (MkPreBaresequent H C) * DEBUG_MSG with
      | pre_concl_ext
          (oterm (Can NEquality)
                 [bterm [] (oterm (Can NIsect) [bterm [] a1, bterm [x1] b1]),
                  bterm [] (oterm (Can NIsect) [bterm [] a2, bterm [x2] b2]),
                  bterm [] (oterm (Can (NUni i)) [])]) =>

        let prf1 := pre_proof_hole ctxt (pre_rule_isect_equality_hyp1 a1 a2 i H) in
        let prf2 := pre_proof_hole ctxt (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H) in
        (pre_proof_isect_eq ctxt a1 a2 b1 b2 x1 x2 y i H p prf1 prf2,
         applied_isect_eq_rule)

      | c => (pre_proof_hole _ (MkPreBaresequent H c),
              could_not_apply_isect_eq_rule)
      end

    | _ => (pre_proof_hole _ (MkPreBaresequent H C),
            could_not_apply_isect_eq_rule)
    end
  end.

Definition apply_proof_step_isect_member_formation {o} {ctxt}
           (s : @pre_baresequent o)
           (z : NVar)
           (i : nat) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match NVin_dec z (vars_hyps H) with
    | inl p =>

      match C with
      | pre_concl_ext (oterm (Can NIsect) [bterm [] A, bterm [x] B]) =>

        let prf1 := pre_proof_hole ctxt (pre_rule_isect_member_formation_hyp1 z A x B H) in
        let prf2 := pre_proof_hole ctxt (pre_rule_isect_member_formation_hyp2 A i H) in
        (pre_proof_isect_member_formation ctxt A x B z i H p prf1 prf2,
         applied_isect_member_formation_rule)

      | c => (pre_proof_hole _ (MkPreBaresequent H c),
              could_not_apply_isect_member_formation_rule)
      end

    | _ => (pre_proof_hole _ (MkPreBaresequent H C),
            could_not_apply_isect_member_formation_rule)
    end
  end.

Fixpoint find_hypothesis {o} (H : @bhyps o) (x : NVar)
  : option (bhyps * NTerm * bhyps) :=
  match H with
  | [] => None
  | h :: hs =>
    if deq_nvar (hvar h) x then Some ([], htyp h, hs)
    else match find_hypothesis hs x with
         | Some (G, T, J) => Some (h :: G, T, J)
         | None => None
         end
  end.

Inductive decomp_hyps {o} (H : @bhyps o) (v : NVar) :=
| dhyps (G : bhyps)
        (A : NTerm)
        (J : bhyps)
        (p : H = snoc G (mk_hyp v A) ++ J).

Arguments dhyps [o] [H] [v] _ _ _ _.

Lemma extend_decomp_hyps {o} :
  forall {H : @bhyps o} {G x J h},
    H = snoc G x ++ J
    -> h :: H = snoc (h :: G) x ++ J.
Proof.
  introv z; subst; reflexivity.
Defined.

Definition add_hyp2decomp_hyps {o}
           (h : @hypothesis o)
           {H : barehypotheses}
           {v : NVar}
           (d : decomp_hyps H v) : decomp_hyps (h :: H) v :=
  match d with
  | dhyps G A J p => dhyps (h :: G) A J (extend_decomp_hyps p)
  end.

Lemma init_decomp_hyps {o} :
  forall (v : NVar) (A : @NTerm o) x H (p : v = x),
    mk_hyp v A :: H = snoc [] (mk_hyp x A) ++ H.
Proof.
  introv z; subst; reflexivity.
Defined.

Definition mk_init_decomp_hyps {o}
           (v : NVar)
           (A : @NTerm o)
           (x : NVar)
           (H : barehypotheses)
           (p : v = x) : decomp_hyps (mk_hyp v A :: H) x :=
  dhyps [] A H (init_decomp_hyps v A x H p).

Fixpoint find_hypothesis_eq {o} (H : @bhyps o) (x : NVar)
  : option (decomp_hyps H x) :=
  match H with
  | [] => None
  | Build_hypothesis _ v hid A lvl as h :: hs =>
    match deq_nvar v x with
    | left p =>
      match lvl, hid with
      | nolvl, false => Some (mk_init_decomp_hyps v A x hs p)
      | _, _ => None
      end
    | _ =>
      match find_hypothesis_eq hs x with
      | Some x => Some (add_hyp2decomp_hyps h x)
      | None => None
      end
    end
  end.

Inductive decomp_hhyps {o} (H : @bhyps o) (v : NVar) :=
| dhhyps (G : bhyps)
         (A : NTerm)
         (J : bhyps)
         (p : H = snoc G (mk_hhyp v A) ++ J).

Arguments dhhyps [o] [H] [v] _ _ _ _.

Definition add_hyp2decomp_hhyps {o}
           (h : @hypothesis o)
           {H : barehypotheses}
           {v : NVar}
           (d : decomp_hhyps H v) : decomp_hhyps (h :: H) v :=
  match d with
  | dhhyps G A J p => dhhyps (h :: G) A J (extend_decomp_hyps p)
  end.

Lemma init_decomp_hhyps {o} :
  forall (v : NVar) (A : @NTerm o) x H (p : v = x),
    mk_hhyp v A :: H = snoc [] (mk_hhyp x A) ++ H.
Proof.
  introv z; subst; reflexivity.
Defined.

Definition mk_init_decomp_hhyps {o}
           (v : NVar)
           (A : @NTerm o)
           (x : NVar)
           (H : barehypotheses)
           (p : v = x) : decomp_hhyps (mk_hhyp v A :: H) x :=
  dhhyps [] A H (init_decomp_hhyps v A x H p).

Fixpoint find_hhypothesis_eq {o} (H : @bhyps o) (x : NVar)
  : option (decomp_hhyps H x) :=
  match H with
  | [] => None
  | Build_hypothesis _ v hid A lvl as h :: hs =>
    match deq_nvar v x with
    | left p =>
      match lvl, hid with
      | nolvl, true => Some (mk_init_decomp_hhyps v A x hs p)
      | _, _ => None
      end
    | _ =>
      match find_hhypothesis_eq hs x with
      | Some x => Some (add_hyp2decomp_hhyps h x)
      | None => None
      end
    end
  end.

Lemma pre_rule_hypothesis_concl_as_pre_baresequent {o} :
  forall (H : @bhyps o) G x A J T
         (q : H = snoc G (mk_hyp x A) ++ J)
         (p : A = T),
    pre_rule_hypothesis_concl G J A x
    = mk_pre_bseq H (pre_concl_ext T).
Proof.
  introv e1 e2; subst; reflexivity.
Defined.

Definition apply_proof_step_hypothesis {o} {ctxt}
           (s : @pre_baresequent o)
           (x : NVar) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match find_hypothesis_eq H x with
      | Some (dhyps G A J q) =>

        match term_dec_op A T with
        | Some p =>

          (* NOTE: This coercion is not so great.  Is that going to compute well? *)
          (eq_rect
             _
             _
             (pre_proof_hypothesis ctxt x A G J)
             _
             (pre_rule_hypothesis_concl_as_pre_baresequent H G x A J T q p),
           applied_hypothesis_rule)

        | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                   could_not_apply_hypothesis_rule_because_different_types A T)
        end

      | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                 could_not_apply_hypothesis_rule_because_couldnt_find_hypothesis)
      end

    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_hypothesis_rule)
    end
  end.

(* MOVE to terms_deq_op *)
Lemma wf_term_dec_op {o} :
  forall (t : @NTerm o), option (wf_term t).
Proof.
  sp_nterm_ind1 t as [v|f|op bs ind] Case; introv.

  - Case "vterm".
    left; constructor.

  - Case "sterm".
    right.

  - Case "oterm".

    remember (beq_list deq_nat (map num_bvars bs) (OpBindings op)) as b.
    symmetry in Heqb; destruct b;[|right].
    unfold wf_term; simpl.
    rewrite Heqb; simpl.
    clear Heqb op.

    induction bs; simpl in *.

    { left; auto. }

    destruct a as [l t]; simpl in *.

    autodimp IHbs hyp.

    { introv i; eapply ind; eauto. }

    destruct IHbs as [IHbs|];[|right].
    rewrite IHbs.

    pose proof (ind t l) as q; clear ind; autodimp q hyp.
    destruct q as [q|];[|right].
    rewrite q.

    left; auto.
Defined.

Lemma dec_bool :
  forall (a b : bool),
    decidable (a = b).
Proof.
  introv.
  destruct a, b; tcsp; right; intro xx; ginv.
Defined.

Lemma covered_decidable {o} :
  forall (t : @NTerm o) vs, decidable (covered t vs).
Proof.
  introv.
  apply dec_bool.
Defined.

(* we need semi-deciders for wf_term B, covered B (var_hyps H), and NVin x (vars_hyps H) *)

Definition apply_proof_step_cut {o} {ctxt}
           (s : @pre_baresequent o)
           (x : NVar)
           (B : NTerm) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match wf_term_dec_op B with
      | Some wfB =>

        match covered_decidable B (vars_hyps H) with
        | inl covB =>

          match NVin_dec x (vars_hyps H) with
          | inl nixH =>

            let prf1 := pre_proof_hole ctxt (pre_rule_cut_hyp1 H B) in
            let prf2 := pre_proof_hole ctxt (pre_rule_cut_hyp2 H x B T) in
            (pre_proof_cut ctxt B T x H wfB covB nixH prf1 prf2,
             applied_cut_rule)

          | inr _ => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                      could_not_apply_cut_rule)
          end

        | inr _ => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                    could_not_apply_cut_rule)
        end

      | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                 could_not_apply_cut_rule)
      end

    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_cut_rule)
    end
  end.

Definition apply_proof_step_cequiv_computation {o} {ctxt}
           (s : @pre_baresequent o)
           (n : nat) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match T with
      | oterm (Can NCequiv) [bterm [] a, bterm [] b] =>

        let x := compute_atmost_k_steps ctxt n a in
        match term_dec_op x b with
        | Some p =>

          (pre_proof_cequiv_computation
             ctxt a b H
             (eq_rect
                _
                _
                (reduces_to_of_compute_atmost_k_steps ctxt n a)
                _
                p),
           applied_cequiv_computation_rule)

        | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext (mk_cequiv a b))),
                   could_not_apply_cequiv_computation_rule_not_cequiv)
        end

      | t => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext t)),
              could_not_apply_cequiv_computation_rule_not_cequiv)
      end


    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_cequiv_computation_rule)
    end
  end.

Lemma pre_rule_cequiv_subst_hyp1_as_pre_baresequent {o} :
  forall (H : @bhyps o) T x C a
         (p : (subst C x a) = T),
    pre_rule_cequiv_subst_hyp1 H x C a
    = mk_pre_bseq H (pre_concl_ext T).
Proof.
  introv e; subst; reflexivity.
Defined.

Definition apply_proof_step_cequiv_subst_concl {o} {ctxt}
           (s : @pre_baresequent o)
           (x : NVar)
           (X a b : NTerm) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match term_dec_op (subst X x a) T with
      | Some p =>

        match wf_term_dec_op a with
        | Some wfa =>

          match wf_term_dec_op b with
          | Some wfb =>

            match covered_decidable a (vars_hyps H) with
            | inl cova =>

              match covered_decidable b (vars_hyps H) with
              | inl covb =>

                let prf1 := pre_proof_hole ctxt (pre_rule_cequiv_subst_hyp1 H x X b) in
                let prf2 := pre_proof_hole ctxt (pre_rule_cequiv_subst_hyp2 H a b) in
                (eq_rect
                   _
                   _
                   (pre_proof_cequiv_subst_concl ctxt X x a b H wfa wfb cova covb prf1 prf2)
                   _
                   (pre_rule_cequiv_subst_hyp1_as_pre_baresequent H T x X a p),
                 applied_cequiv_subst_concl_rule)

              | inr _ => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                          could_not_apply_cequiv_subst_concl_rule)
              end

            | inr _ => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                        could_not_apply_cequiv_subst_concl_rule)
            end

          | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                     could_not_apply_cequiv_subst_concl_rule)
          end

        | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                   could_not_apply_cequiv_subst_concl_rule)
        end

      | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                 could_not_apply_cequiv_subst_concl_rule_not_subst)
      end

    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_cequiv_subst_concl_rule)
    end
  end.

Lemma pre_rule_universe_equality_concl_as_pre_baresequent {o} :
  forall (H : @bhyps o) i j1 j2
         (p : j2 = j1),
    pre_rule_universe_equality_concl H j1 i
    = mk_pre_bseq H (mk_pre_concl (mk_equality (mk_uni j1) (mk_uni j2) (mk_uni i))).
Proof.
  introv e; subst; reflexivity.
Defined.

Definition apply_proof_step_universe_eq {o} {ctxt}
           (s : @pre_baresequent o) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality)
               [bterm [] (oterm (Can (NUni j1)) []),
                bterm [] (oterm (Can (NUni j2)) []),
                bterm [] (oterm (Can (NUni i)) [])])=>

      match eq_nat_dec j2 j1 with
      | left e =>

        match lt_dec j1 i with
        | left p =>

          (eq_rect
             _
             _
             (pre_proof_universe_equality ctxt j1 i H p)
             _
             (pre_rule_universe_equality_concl_as_pre_baresequent H i j1 j2 e),
           applied_universe_eq_rule)

        | right _ => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext (mk_equality (mk_uni j1) (mk_uni j2) (mk_uni i)))),
                      could_not_apply_universe_eq_rule_not_universes)
        end

      | right _ => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext (mk_equality (mk_uni j1) (mk_uni j2) (mk_uni i)))),
                    could_not_apply_universe_eq_rule_not_universes)
      end

    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_universe_eq_rule)
    end
  end.

Lemma pre_rule_hypothesis_equality_concl_as_pre_baresequent {o} :
  forall (H : @bhyps o) G J x1 x2 A B
         (q : H = snoc G (mk_hyp x1 B) ++ J)
         (e : x2 = x1)
         (p : B = A),
    pre_rule_hypothesis_equality_concl G J A x1
    = mk_pre_bseq H (pre_concl_ext (mk_equality (mk_var x1) (mk_var x2) A)).
Proof.
  introv e1 e2 e3; subst; reflexivity.
Defined.

Definition apply_proof_step_hypothesis_eq {o} {ctxt}
           (s : @pre_baresequent o) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (vterm v1),
                                bterm [] (vterm v2),
                                bterm [] A]) =>

      match deq_nvar v2 v1 with
      | left e =>

        match find_hypothesis_eq H v1 with
        | Some (dhyps G B J q) =>

          match term_dec_op B A with
          | Some p =>

            (* NOTE: This coercion is not so great.  Is that going to compute well? *)
            (eq_rect
               _
               _
               (pre_proof_hypothesis_equality ctxt v1 A G J)
               _
               (pre_rule_hypothesis_equality_concl_as_pre_baresequent H G J v1 v2 A B q e p),
             applied_hypothesis_equality_rule)

          | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext (mk_equality (mk_var v1) (mk_var v2) A))),
                     could_not_apply_hypothesis_equality_rule)
          end

        | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext (mk_equality (mk_var v1) (mk_var v2) A))),
                   could_not_apply_hypothesis_equality_rule)
        end

      | right _ => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext (mk_equality (mk_var v1) (mk_var v2) A))),
                    could_not_apply_hypothesis_equality_rule)
      end

    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_hypothesis_equality_rule)
    end
  end.

Lemma pre_rule_unhide_equality_concl_as_pre_baresequent {o} :
  forall (H : @bhyps o) G J x A t1 t2 T
         (q : H = snoc G (mk_hhyp x A) ++ J),
    pre_rule_unhide_equality_concl G J x A t1 t2 T
    = mk_pre_bseq H (pre_concl_ext (mk_equality t1 t2 T)).
Proof.
  introv e; subst; reflexivity.
Defined.

Definition apply_proof_step_unhide_equality {o} {ctxt}
           (s : @pre_baresequent o)
           (x : NVar) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] t1,
                                bterm [] t2,
                                bterm [] T]) =>

      match find_hhypothesis_eq H x with
      | Some (dhhyps G A J q) =>

        let prf := pre_proof_hole ctxt (pre_rule_unhide_equality_hyp G J x A t1 t2 T) in
        (eq_rect
           _
           _
           (pre_proof_unhide_equality ctxt x A t1 t2 T G J prf)
           _
           (pre_rule_unhide_equality_concl_as_pre_baresequent H G J x A t1 t2 T q),
         applied_unhide_equality_rule)

      | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext (mk_equality t1 t2 T))),
                 could_not_apply_unhide_equality_rule)
      end

    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_unhide_equality_rule)
    end
  end.

Definition apply_proof_step_equality_equality {o} {ctxt}
           (s : @pre_baresequent o) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (oterm (Can NEquality) [bterm [] a1, bterm [] a2, bterm [] A]),
                                bterm [] (oterm (Can NEquality) [bterm [] b1, bterm [] b2, bterm [] B]),
                                bterm [] (oterm (Can (NUni i)) [])]) =>

        let prf1 := pre_proof_hole ctxt (pre_rule_equality_equality_hyp1 H A B i) in
        let prf2 := pre_proof_hole ctxt (pre_rule_equality_equality_hyp2 H a1 b1 A) in
        let prf3 := pre_proof_hole ctxt (pre_rule_equality_equality_hyp2 H a2 b2 A) in
        (pre_proof_equality_equality ctxt A B a1 a2 b1 b2 i H prf1 prf2 prf3,
         applied_equality_equality_rule)

    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_equality_equality_rule)
    end
  end.

Lemma pre_rule_integer_equality_concl_as_pre_baresequent {o} :
  forall (H : @bhyps o) n1 n2
         (p : n2 = n1),
    pre_rule_integer_equality_concl H n1
    = mk_pre_bseq H (pre_concl_ext (mk_equality (mk_integer n1) (mk_integer n2) mk_int)).
Proof.
  introv e; subst; reflexivity.
Defined.

Definition apply_proof_step_integer_equality {o} {ctxt}
           (s : @pre_baresequent o) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (oterm (Can (Nint n1)) []),
                                bterm [] (oterm (Can (Nint n2)) []),
                                bterm [] (oterm (Can NInt) [])]) =>

      match Z.eq_dec n2 n1 with
      | left p =>

        (eq_rect
           _
           _
           (pre_proof_integer_equality ctxt n1 H)
           _
           (pre_rule_integer_equality_concl_as_pre_baresequent H n1 n2 p),
         applied_integer_equality_rule)

      | right _ => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext (mk_equality (mk_integer n1) (mk_integer n2) mk_int))),
                    could_not_apply_integer_equality_rule)
      end

    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_integer_equality_rule)
    end
  end.

Lemma noutokens_decidable {o} :
  forall (t : @NTerm o), decidable (noutokens t).
Proof.
  introv.
  unfold noutokens.
  remember (get_utokens t) as l.
  destruct l;[left|right]; auto.
  intro xx; inversion xx.
Defined.

Definition apply_proof_step_introduction {o} {ctxt}
           (s : @pre_baresequent o)
           (t : @NTerm o) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match wf_term_dec_op t with
      | Some wft =>

        match covered_decidable t (nh_vars_hyps H) with
        | inl covt =>

          match noutokens_decidable t with
          | inl nout =>

            let prf1 := pre_proof_hole ctxt (pre_rule_introduction_hyp H T t) in
            (pre_proof_introduction ctxt t T H wft covt nout prf1,
             applied_introduction_rule)

          | inr _ => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                      could_not_apply_introduction_rule)
          end

        | inr _ => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                    could_not_apply_introduction_rule)
        end

      | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                  could_not_apply_introduction_rule)
      end

    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_introduction_rule)
    end
  end.

Lemma find_named_concl {o}
      (c : @named_concl o)
      (l : list named_concl) : option (LIn c l).
Proof.
  induction l; simpl;[right;auto|].
  destruct c as [n1 t1], a as [n2 t2]; simpl in *.
  destruct (LemmaNameDeq n1 n2) as [d|d]; subst.
  { destruct (term_dec_op t1 t2) as [d|d]; subst;[left;auto|].
    destruct IHl as [IHl|];[|right].
    left; right; auto. }
  { destruct IHl as [IHl|];[|right].
    left; right; auto. }
Defined.

Definition apply_proof_step_lemma {o} {ctxt}
           (s : @pre_baresequent o)
           (name : LemmaName) : pre_proof ctxt s * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      let nc := MkNamedConcl name T in

      match find_named_concl nc (PC_conclusions ctxt) with
      | Some i =>

        (pre_proof_from_ctxt ctxt nc H i,
         applied_lemma_rule)

      | None => (pre_proof_hole _ (MkPreBaresequent H (pre_concl_ext T)),
                 could_not_apply_lemma_rule)
      end

    | c => (pre_proof_hole _ (MkPreBaresequent H c),
            could_not_apply_lemma_rule)
    end
  end.

Definition apply_proof_step {o} {ctxt}
           (s    : @pre_baresequent o)
           (step : proof_step) : pre_proof ctxt s * DEBUG_MSG :=
  match step with
  | proof_step_isect_equality y           => apply_proof_step_isect_eq s y
  | proof_step_isect_member_formation z i => apply_proof_step_isect_member_formation s z i
  | proof_step_hypothesis x               => apply_proof_step_hypothesis s x
  | proof_step_cut x B                    => apply_proof_step_cut s x B
  | proof_step_cequiv_computation n       => apply_proof_step_cequiv_computation s n
  | proof_step_cequiv_subst_concl x C a b => apply_proof_step_cequiv_subst_concl s x C a b
  | proof_step_universe_equality          => apply_proof_step_universe_eq s
  | proof_step_hypothesis_equality        => apply_proof_step_hypothesis_eq s
  | proof_step_unhide_equality x          => apply_proof_step_unhide_equality s x
  | proof_step_equality_equality          => apply_proof_step_equality_equality s
  | proof_step_integer_equality           => apply_proof_step_integer_equality s
  | proof_step_introduction t             => apply_proof_step_introduction s t
  | proof_step_lemma name                 => apply_proof_step_lemma s name
  end.

Fixpoint update_pre_proof {o}
         {ctxt : @ProofContext o}
         {s    : pre_baresequent}
         (p    : pre_proof ctxt s)
         (addr : address)
         (step : proof_step) : pre_proof ctxt s * DEBUG_MSG :=
  match p with
  | pre_proof_from_ctxt _ c H i =>
    (pre_proof_from_ctxt _ c H i,
     could_not_apply_update_because_no_hole_at_address)

  | pre_proof_hole _ s => apply_proof_step s step

  | pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let (prf1', msg) := update_pre_proof prf1 addr step in
      (pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1' prf2, msg)
    | 2 :: addr =>
      let (prf2', msg) := update_pre_proof prf2 addr step in
      (pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2', msg)
    | _ => (pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2,
            could_not_apply_update_because_wrong_address)
    end

  | pre_proof_isect_member_formation _ A x B z i H nizH prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let (prf1', msg) := update_pre_proof prf1 addr step in
      (pre_proof_isect_member_formation _ A x B z i H nizH prf1' prf2, msg)
    | 2 :: addr =>
      let (prf2', msg) := update_pre_proof prf2 addr step in
      (pre_proof_isect_member_formation _ A x B z i H nizH prf1 prf2', msg)
    | _ => (pre_proof_isect_member_formation _ A x B z i H nizH prf1 prf2,
            could_not_apply_update_because_wrong_address)
    end

  | pre_proof_approx_refl _ a H =>
    (pre_proof_approx_refl _ a H,
     could_not_apply_update_because_no_hole_at_address)

  | pre_proof_cequiv_approx _ a b H prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let (prf1', msg) := update_pre_proof prf1 addr step in
      (pre_proof_cequiv_approx _ a b H prf1' prf2, msg)
    | 2 :: addr =>
      let (prf2', msg) := update_pre_proof prf2 addr step in
      (pre_proof_cequiv_approx _ a b H prf1 prf2', msg)
    | _ => (pre_proof_cequiv_approx _ a b H prf1 prf2,
            could_not_apply_update_because_wrong_address)
    end

  | pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let (prf1', msg) := update_pre_proof prf1 addr step in
      (pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1' prf2, msg)
    | 2 :: addr =>
      let (prf2', msg) := update_pre_proof prf2 addr step in
      (pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2', msg)
    | _ => (pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2,
            could_not_apply_update_because_wrong_address)
    end

  | pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let (prf1', msg) := update_pre_proof prf1 addr step in
      (pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1' prf2, msg)
    | 2 :: addr =>
      let (prf2', msg) := update_pre_proof prf2 addr step in
      (pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2', msg)
    | _ => (pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2,
            could_not_apply_update_because_wrong_address)
    end

  | pre_proof_cut _ B C x H wfB covB nixH prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let (prf1', msg) := update_pre_proof prf1 addr step in
      (pre_proof_cut _ B C x H wfB covB nixH prf1' prf2, msg)
    | 2 :: addr =>
      let (prf2', msg) := update_pre_proof prf2 addr step in
      (pre_proof_cut _ B C x H wfB covB nixH prf1 prf2', msg)
    | _ => (pre_proof_cut _ B C x H wfB covB nixH prf1 prf2,
            could_not_apply_update_because_wrong_address)
    end

  | pre_proof_hypothesis _ x A G J =>
    (pre_proof_hypothesis _ x A G J,
     could_not_apply_update_because_no_hole_at_address)

  | pre_proof_cequiv_subst_concl _ C x a b H wfa wfb cova covb prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let (prf1', msg) := update_pre_proof prf1 addr step in
      (pre_proof_cequiv_subst_concl _ C x a b H wfa wfb cova covb prf1' prf2, msg)
    | 2 :: addr =>
      let (prf2', msg) := update_pre_proof prf2 addr step in
      (pre_proof_cequiv_subst_concl _ C x a b H wfa wfb cova covb prf1 prf2', msg)
    | _ => (pre_proof_cequiv_subst_concl _ C x a b H wfa wfb cova covb prf1 prf2,
            could_not_apply_update_because_wrong_address)
    end

  | pre_proof_cequiv_computation _ a b H r =>
    (pre_proof_cequiv_computation _ a b H r,
     could_not_apply_update_because_no_hole_at_address)

  | pre_proof_cequiv_computation_atmost _ a b n H r =>
    (pre_proof_cequiv_computation_atmost _ a b n H r,
     could_not_apply_update_because_no_hole_at_address)

  | pre_proof_universe_equality _ i j H ltij =>
    (pre_proof_universe_equality _ i j H ltij,
     could_not_apply_update_because_no_hole_at_address)

  | pre_proof_hypothesis_equality _ x A G J =>
    (pre_proof_hypothesis_equality _ x A G J,
     could_not_apply_update_because_no_hole_at_address)

  | pre_proof_unhide_equality _ x A t1 t2 C G J prf =>
    match addr with
    | 1 :: addr =>
      let (prf', msg) := update_pre_proof prf addr step in
      (pre_proof_unhide_equality _ x A t1 t2 C G J prf', msg)
    | _ => (pre_proof_unhide_equality _ x A t1 t2 C G J prf,
            could_not_apply_update_because_wrong_address)
    end

  | pre_proof_equality_equality _ A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
    match addr with
    | 1 :: addr =>
      let (prf1', msg) := update_pre_proof prf1 addr step in
      (pre_proof_equality_equality _ A B a1 a2 b1 b2 i H prf1' prf2 prf3, msg)
    | 2 :: addr =>
      let (prf2', msg) := update_pre_proof prf2 addr step in
      (pre_proof_equality_equality _ A B a1 a2 b1 b2 i H prf1 prf2' prf3, msg)
    | 3 :: addr =>
      let (prf3', msg) := update_pre_proof prf3 addr step in
      (pre_proof_equality_equality _ A B a1 a2 b1 b2 i H prf1 prf2 prf3', msg)
    | _ => (pre_proof_equality_equality _ A B a1 a2 b1 b2 i H prf1 prf2 prf3,
            could_not_apply_update_because_wrong_address)
    end

  | pre_proof_integer_equality _ n H =>
    (pre_proof_integer_equality _ n H,
     could_not_apply_update_because_no_hole_at_address)

  | pre_proof_introduction _ t C H wft covt nout prf =>
    match addr with
    | 1 :: addr =>
      let (prf', msg) := update_pre_proof prf addr step in
      (pre_proof_introduction _ t C H wft covt nout prf', msg)
    | _ => (pre_proof_introduction _ t C H wft covt nout prf,
            could_not_apply_update_because_wrong_address)
    end
  end.

Definition update_pre_proof_seq {o} {ctxt}
           (pps  : @pre_proof_seq o ctxt)
           (addr : address)
           (step : proof_step) : pre_proof_seq ctxt * DEBUG_MSG :=
  match pps with
  | MkPreProofSeq name C isp pre_prf =>
    let (pre_prf', msg) := update_pre_proof pre_prf addr step in
    (MkPreProofSeq name C isp pre_prf', msg)
  end.

Definition NuprlState_update_proof {o}
           (state : @NuprlState o)
           (name  : LemmaName)
           (addr  : address)
           (step  : proof_step) : NuprlState * DEBUG_MSG :=
  match find_unfinished_in_pre_proofs (NuprlState_unfinished state) name with
  | (Some pp, pps) =>

    let (pp', msg) := update_pre_proof_seq pp addr step in
    (NuprlState_change_unfinished state (pp' :: pps), msg)

  | (None, pps) => (state, could_not_apply_update_because_could_not_find_lemma)
  end.

Definition NuprlState_start_proof {o}
           (state : @NuprlState o)
           (name  : LemmaName)
           (C     : NTerm)
           (isp   : isprog C) : NuprlState * @DEBUG_MSG o :=
  let pps : pre_proof_seq (Library2ProofContext (NuprlState_lib state)) :=
      MkPreProofSeq name C isp (pre_proof_hole _ (term2pre_baresequent C))
  in
  (MkNuprlState
     (NuprlState_lib state)
     (pps :: NuprlState_unfinished state),
   started_proof).

Fixpoint find_holes_in_pre_proof {o}
         {ctxt : @ProofContext o}
         {s    : pre_baresequent}
         (p    : pre_proof ctxt s)
         (addr : address) : Holes :=
  match p with
  | pre_proof_from_ctxt _ c H i => []

  | pre_proof_hole _ s => [MkHole s addr]

  | pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_isect_member_formation _ A x B z i H nizH prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_approx_refl _ a H => []

  | pre_proof_cequiv_approx _ a b H prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_cut _ B C x H wfB covB nixH prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_hypothesis _ x A G J => []

  | pre_proof_cequiv_subst_concl _ C x a b H wfa wfb cova covb prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_cequiv_computation _ a b H r => []

  | pre_proof_cequiv_computation_atmost _ a b n H r => []

  | pre_proof_universe_equality _ i j H ltij => []

  | pre_proof_hypothesis_equality _ x A G J => []

  | pre_proof_unhide_equality _ x A t1 t2 C G J prf =>
    find_holes_in_pre_proof prf (snoc addr 1)

  | pre_proof_equality_equality _ A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    let holes3 := find_holes_in_pre_proof prf3 (snoc addr 3) in
    holes1 ++ holes2 ++ holes3

  | pre_proof_integer_equality _ n H => []

  | pre_proof_introduction _ t C H wft covt nout prf =>
    find_holes_in_pre_proof prf (snoc addr 1)
  end.

Definition find_holes_in_pre_proof_seq {o} {ctxt}
           (pps : @pre_proof_seq o ctxt) : Holes :=
  match pps with
  | MkPreProofSeq name C isp pre_prf => find_holes_in_pre_proof pre_prf []
  end.

Definition NuprlState_find_holes {o}
           (state : @NuprlState o)
           (name  : LemmaName) : NuprlState * DEBUG_MSG :=
  match find_unfinished_in_pre_proofs (NuprlState_unfinished state) name with
  | (Some pp, _) =>

    let holes := find_holes_in_pre_proof_seq pp in
    (state, found_holes holes)

  | (None, pps) => (state, could_not_find_holes_because_could_not_find_lemma)
  end.

Definition update {o}
           (state : @NuprlState o)
           (cmd   : command) : NuprlState * DEBUG_MSG :=
  match cmd with
  | COM_add_def opabs vars rhs correct =>
    NuprlState_add_def state opabs vars rhs correct

  | COM_finish_proof name =>
    NuprlState_finish_proof state name

  | COM_update_proof name addr step =>
    NuprlState_update_proof state name addr step

  | COM_start_proof name C isp =>
    NuprlState_start_proof state name C isp

  | COM_find_holes name =>
    NuprlState_find_holes state name
  end.

Definition DEBUG_MSGS {o} := list (@DEBUG_MSG o).

Record UpdRes {o} :=
  MkUpdRes
    {
      upd_res_state : @NuprlState o;
      upd_res_trace : @DEBUG_MSGS o;
    }.

Arguments MkUpdRes [o] _ _.

Fixpoint update_list {o}
         (state : @NuprlState o)
         (cmds  : commands) : UpdRes :=
  match cmds with
  | [] => MkUpdRes state []
  | cmd :: cmds =>
    let (s1,m) := update state cmd in
    match update_list s1 cmds with
    | MkUpdRes s2 ms => MkUpdRes s2 (snoc ms m)
    end
  end.

Definition initLibrary {o} : @Library o := [].

Definition initUnfinished {o} : @pre_proofs o (Library2ProofContext initLibrary) := [].

Definition initNuprlState {o} : @NuprlState o :=
  MkNuprlState initLibrary initUnfinished.

Definition update_list_from_init {o} (cmds : commands) : @UpdRes o :=
  update_list initNuprlState cmds.

(* Should we add this to NuprlState *)
Definition ValidNuprlState {o} (state : @NuprlState o) := ValidLibrary state.

Lemma update_preserves_validity {o} :
  forall (state : @NuprlState o) (cmd : command),
    ValidNuprlState state -> ValidNuprlState (fst (update state cmd)).
Proof.
  introv valid.
  destruct cmd; simpl; auto.

  - (* addition of a definition *)
    destruct state as [L pre_prfs]; simpl in *.
    unfold ValidNuprlState in *; simpl in *.

    destruct (entry_in_lib_dec
                (LibraryEntry_abs (lib_abs opabs vars rhs correct))
                (Library2lib L)) as [d|d]; simpl; auto.

  - (* finalizing a proof *)
    destruct state as [L pre_prfs]; simpl in *.
    unfold ValidNuprlState in *; simpl in *.
    unfold NuprlState_finish_proof; simpl.

    remember (find_unfinished_in_pre_proofs pre_prfs name) as f; symmetry in Heqf; repnd.
    destruct f0; simpl in *; auto;[].

    remember (finish_pre_proof_seq p) as eop; symmetry in Heqeop.
    destruct eop; simpl in *; dands; auto;[].

    destruct (entry_in_lib_dec l (Library2lib L)) as [d|d]; simpl; auto;[].

    destruct l; simpl in *.

    + unfold finish_pre_proof_seq in Heqeop.
      destruct p; simpl in *.
      remember (finish_pre_proof pre_proof_seq_proof0) as fin; symmetry in Heqfin;
        destruct fin; ginv.

    + assert (ctxt = Library2ProofContext L) as xx.

      { unfold finish_pre_proof_seq in Heqeop.
        destruct p; simpl in *.
        remember (finish_pre_proof pre_proof_seq_proof0) as fin; symmetry in Heqfin;
          destruct fin; ginv;[].
        destruct e; ginv; cpx.
        inversion Heqeop; auto. }

      dands; auto.

  - (* update an unfinished proof *)
    destruct state; simpl in *.
    unfold ValidNuprlState in *; simpl in *.
    unfold NuprlState_update_proof; simpl.

    remember (find_unfinished_in_pre_proofs NuprlState_unfinished0 name) as f; symmetry in Heqf; repnd.
    destruct f0; simpl in *; auto.
    remember (update_pre_proof_seq p addr step) as upd; destruct upd; simpl; auto.

  - unfold NuprlState_find_holes.
    remember (find_unfinished_in_pre_proofs (NuprlState_unfinished state) name) as f; symmetry in Heqf; repnd.
    destruct f0; simpl in *; auto.
Qed.

Lemma update_list_preserves_validity {o} :
  forall (cmds : commands) (state : @NuprlState o),
    ValidNuprlState state -> ValidNuprlState (upd_res_state (update_list state cmds)).
Proof.
  induction cmds; introv v; simpl in *; auto.

  remember (update state a) as p; symmetry in Heqp; repnd.
  pose proof (update_preserves_validity state a) as q; autodimp q hyp.
  rewrite Heqp in q; simpl in q.

  apply IHcmds in q.
  remember (update_list p0 cmds) as w; symmetry in Heqw; repnd; simpl in *; auto.
  destruct w; auto.
Qed.

Lemma ValidInitNuprlState {o} : @ValidNuprlState o initNuprlState.
Proof.
  introv.
  compute; auto.
Qed.

Lemma valid_update_list_from_init {o} :
  forall (cmds : commands),
    @ValidNuprlState o (upd_res_state (update_list_from_init cmds)).
Proof.
  introv.
  apply update_list_preserves_validity.
  apply ValidInitNuprlState.
Qed.

Record ValidUpdRes {o} :=
  MkValidUpdRes
    {
      valid_upd_res_state : @NuprlState o;
      valid_upd_res_trace : list (@DEBUG_MSG o);
      valid_upd_res_valid : ValidNuprlState valid_upd_res_state;
    }.
Arguments MkValidUpdRes [o] _ _ _.

Lemma eq_upd_res_state {o} :
  forall {a b}, a = b -> @upd_res_state o a = upd_res_state b.
Proof.
  introv h; subst; auto.
Defined.

Definition update_list_from_init_with_validity {o}
           (cmds : @commands o) : @ValidUpdRes o :=
  MkValidUpdRes
    (upd_res_state (update_list_from_init cmds))
    (upd_res_trace (update_list_from_init cmds))
    (eq_rect
       _
       _
       (valid_update_list_from_init cmds)
       _
       (eq_upd_res_state eq_refl)).

Notation "𝕌( i )" := (oterm (Can (NUni i)) []).
Notation "𝕍( v )" := (vterm (nvar v)) (at level 0).
Notation "𝕎( v )" := (sovar (nvar v) []) (at level 0).
Notation "𝔸( name , t1 , t2 )" := (oterm (Abs {| opabs_name := name; opabs_params := []; opabs_sign := [0, 0] |}) [ bterm [] t1, bterm [] t2]).
Notation " ( a ≡ b ∈ T ) " := (oterm  (Can NEquality) [ bterm [] a, bterm [] b, bterm [] T]) (at level 0).
Notation "⋂ v : T . U" := (oterm (Can NIsect) [ bterm [] T, bterm [nvar v] U ]) (at level 0).
Notation " ( a ≣ b ∈ T ) " := (soterm (Can NEquality) [ sobterm [] a, sobterm [] b, sobterm [] T ]).
Notation "★" := (oterm (Can NAxiom) []).
Notation "𝔸( name , v1 , v2 ) ≜ t" := (lib_abs {| opabs_name := name; opabs_params := []; opabs_sign := [0, 0] |} [ (nvar v1, 0), (nvar v2, 0) ] t _) (at level 0).
Notation "⎧ v ∷ t ⎫" := {| hvar := nvar v; hidden := false; htyp := t; lvl := nolvl |}.
Notation "⎡ v ∷ t ⎤" := {| hvar := nvar v; hidden := true; htyp := t; lvl := nolvl |}.
Notation "( a ≈ b )" := (oterm (Can NCequiv) [ bterm [] a, bterm [] b]).
Notation "LibraryEntry_proof( name , stmt , exp )" := (LibraryEntry_proof _ name stmt exp _ _ _).
Notation "CUT( B , C , t , u , x , H , prf1 , prf2 )" := (proof_cut _ B C t u x H _ _ _ prf1 prf2).
Notation "'ℤ'" := (oterm (Can NInt) []).

Arguments pre_proof_isect_member_formation [o] [ctxt] _ _ _ _ _ _ _ _ _.
Arguments pre_proof_hole [o] [ctxt] _.

Definition mk_simple_so_abs {o} (abs : opabs) := @soterm o (Abs abs) [].
