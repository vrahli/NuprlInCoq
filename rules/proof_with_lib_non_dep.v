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

Require Export name_invariance.

Require Export rules_mon.



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

Definition NLemma {o} (T : @NTerm o) (e : NTerm) : baresequent :=
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

Definition pre_rule_cequiv_refl_concl {o} a (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concl (mk_cequiv a a)).

Definition pre_rule_cequiv_alpha_eq_concl {o} a b (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concl (mk_cequiv a b)).

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

Definition pre_rule_maybe_hidden_hypothesis_equality_concl {o} (G J : @bhyps o) A x b :=
  mk_pre_bseq
    (snoc G (mk_nlhyp b x A) ++ J)
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

Definition pre_rule_equality_equality_hyp3 {o} (H : @bhyps o) a b :=
  mk_pre_bseq H (mk_pre_concl (mk_equality a b mk_base)).

Definition pre_rule_introduction_concl {o} (H : @bhyps o) C :=
  mk_pre_bseq H (mk_pre_concl C).

Definition pre_rule_introduction_hyp {o} (H : @bhyps o) C t :=
  mk_pre_bseq H (mk_pre_concl (mk_member t C)).

Definition pre_rule_unfold_abstractions_concl {o} a (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concl a).

Definition pre_rule_unfold_abstractions_hyp {o} lib abs a (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concl (unfold_abstractions lib abs a)).

Definition pre_rule_axiom_equality_concl {o} (a b T : @NTerm o) H :=
  mk_pre_bseq H (mk_pre_concl (mk_member mk_axiom (mk_equality a b T))).

Definition pre_rule_axiom_equality_hyp {o} (a b T : @NTerm o) H :=
  mk_pre_bseq H (mk_pre_concl (mk_equality a b T)).

Definition pre_rule_thin_concl {o} G  x (A : @NTerm o) J C :=
  mk_pre_bseq (snoc G (mk_hyp x A) ++ J) (mk_pre_concl C).

Definition pre_rule_thin_hyp {o} G J (C : @NTerm o) :=
  mk_pre_bseq (G ++ J) (mk_pre_concl C).

Definition pre_rule_function_equality_concl {o} (H : @bhyps o) a1 x1 b1 a2 x2 b2 i :=
  mk_pre_bseq
    H
    (mk_pre_concl (mk_equality
                     (mk_function a1 x1 b1)
                     (mk_function a2 x2 b2)
                     (mk_uni i))).

Definition pre_rule_function_equality_hyp1 {o} (H : @bhyps o) a1 a2 i :=
  mk_pre_bseq
    H
    (mk_pre_concl (mk_equality a1 a2 (mk_uni i))).

Definition pre_rule_function_equality_hyp2 {o} (H : @bhyps o) y a1 b1 x1 b2 x2 i :=
  mk_pre_bseq
    (snoc H (mk_hyp y a1))
    (mk_pre_concl (mk_equality
                     (subst b1 x1 (mk_var y))
                     (subst b2 x2 (mk_var y))
                     (mk_uni i))).

Definition pre_rule_apply_equality_concl {o} (H : @bhyps o) f1 t1 f2 t2 B x :=
  mk_pre_bseq H (mk_pre_concl (mk_equality
                                 (mk_apply f1 t1)
                                 (mk_apply f2 t2)
                                 (subst B x t1))).

Definition pre_rule_apply_equality_hyp1 {o} (H : @bhyps o) f1 f2 A x B :=
  mk_pre_bseq H (mk_pre_concl (mk_equality f1 f2 (mk_function A x B))).

Definition pre_rule_apply_equality_hyp2 {o} (H : @bhyps o) t1 t2 A :=
  mk_pre_bseq H (mk_pre_concl (mk_equality t1 t2 A)).

Definition pre_rule_isect_elimination_concl {o}
           (A : @NTerm o) B C f x H J :=
  mk_pre_bseq
    (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
    (mk_pre_concl C).

Definition pre_rule_isect_elimination_hyp1 {o}
           (A : @NTerm o) B a f x H J :=
  mk_pre_bseq
    (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
    (mk_pre_concl (mk_member a A)).

Definition pre_rule_isect_elimination_hyp2 {o}
           (A : @NTerm o) B C a f x z H J :=
  mk_pre_bseq
    (snoc (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
          (mk_hyp z (mk_member (mk_var f) (subst B x a))))
    (mk_pre_concl C).

Definition pre_rule_isect_elimination2_hyp2 {o}
           (A : @NTerm o) B C a f x y z H J :=
  mk_pre_bseq
    (snoc (snoc (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
                (mk_hyp y (subst B x a)))
          (mk_hyp z (mk_equality (mk_var y) (mk_var f) (subst B x a))))
    (mk_pre_concl C).

Definition pre_rule_isect_elimination2_concl {o}
           (A : @NTerm o) B C f x H J :=
  mk_pre_bseq
    (snoc H (mk_hyp f (mk_isect A x B)) ++ J)
    (mk_pre_concl C).

Definition pre_rule_isect_member_equality_concl {o} (H : @bhyps o) t1 t2 A x B :=
  mk_pre_bseq H (mk_pre_concl (mk_equality t1 t2 (mk_isect A x B))).

Definition pre_rule_isect_member_equality_hyp1 {o} (H : @bhyps o) z A t1 t2 B x :=
  mk_pre_bseq
    (snoc H (mk_hyp z A))
    (mk_pre_concl (mk_equality t1 t2 (subst B x (mk_var z)))).

Definition pre_rule_isect_member_equality_hyp2 {o} (H : @bhyps o) A i :=
  mk_pre_bseq H (mk_pre_concl (mk_equality A A (mk_uni i))).

Definition pre_rule_cumulativity_concl {o} (H : @bhyps o) T j :=
  mk_pre_bseq H (mk_pre_concl (mk_member T (mk_uni j))).

Definition pre_rule_cumulativity_hyp {o} (H : @bhyps o) T i :=
  mk_pre_bseq H (mk_pre_concl (mk_member T (mk_uni i))).

Definition pre_rule_equality_seq {o} (H : @bhyps o) a b T :=
  mk_pre_bseq H (mk_pre_concl (mk_equality a b T)).

Definition pre_rule_cequiv_seq {o} (H : @bhyps o) a b :=
  mk_pre_bseq H (mk_pre_concl (mk_cequiv a b)).

Definition pre_rule_cequiv_subst_hyp_concl {o} (H : @bhyps o) z T x a J C :=
  mk_pre_bseq (snoc H (mk_hyp z (subst T x a)) ++ J) (mk_pre_concl C).

Definition pre_rule_cequiv_subst_hyp_hyp1 {o} (H : @bhyps o) z T x b J C :=
  mk_pre_bseq (snoc H (mk_hyp z (subst T x b)) ++ J) (mk_pre_concl C).

Definition pre_rule_cequiv_subst_hyp_hyp2 {o} (H : @bhyps o) z T x a J b :=
  mk_pre_bseq (snoc H (mk_hyp z (subst T x a)) ++ J) (mk_pre_concl (mk_cequiv a b)).

Definition pre_rule_base_equality_concl {o} (H : @bhyps o) i :=
  mk_pre_bseq H (mk_pre_concl (mk_member mk_base (mk_uni i))).

Definition pre_rule_int_equality_concl {o} (H : @bhyps o) i :=
  mk_pre_bseq H (mk_pre_concl (mk_equality mk_int mk_int (mk_uni i))).

Definition pre_rule_base_closed_concl {o} (t : @NTerm o) :=
  mk_pre_bseq [] (mk_pre_concl (mk_member t mk_base)).




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
  rw <- (@assert_memberb NVar eq_var_dec); tcsp.
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
Definition LemmaNames := list LemmaName.

Lemma LemmaNameDeq : Deq LemmaName.
Proof.
  introv.
  destruct (String.string_dec x y); auto.
Defined.

Record named_concl {o} :=
  MkNamedConcl
    {
      nm_conclusion_name    : LemmaName;
      nm_conclusion_type    : @NTerm o;
    }.
Arguments MkNamedConcl [o] _ _.

Definition opname2opabs (op : opname) : opabs :=
  mk_opabs op [] [].

Definition LemmaName2extract {o} (n : LemmaName) : @NTerm o :=
  mk_abs (opname2opabs n) [].

Definition named_concl2concl {o} (n : @named_concl o) : conclusion :=
  mk_concl (nm_conclusion_type n) (LemmaName2extract (nm_conclusion_name n)).

Definition named_concl2bseq {o} H (n : @named_concl o) : baresequent :=
  mk_bseq H (named_concl2concl n).

Definition named_concl2pre_concl {o} (n : @named_concl o) : pre_conclusion :=
  mk_pre_concl (nm_conclusion_type n).

Definition named_concl2pre_bseq {o} H (n : @named_concl o) : pre_baresequent :=
  mk_pre_bseq H (named_concl2pre_concl n).

Definition named_concl2concl_with_extract {o} (n : @named_concl o) t : conclusion :=
  mk_concl (mk_equality t t (nm_conclusion_type n)) mk_axiom.

Definition named_concl2bseq_with_extract {o} H (n : @named_concl o) t : baresequent :=
  mk_bseq H (named_concl2concl_with_extract n t).

Definition named_concl2pre_concl_with_extract {o} (n : @named_concl o) t : pre_conclusion :=
  mk_pre_concl (mk_equality t t (nm_conclusion_type n)).

Definition named_concl2pre_bseq_with_extract {o} H (n : @named_concl o) t : pre_baresequent :=
  mk_pre_bseq H (named_concl2pre_concl_with_extract n t).

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

  Unfolding of abstractions

  ============================================================ *)

Definition unfoldable {o} lib abstractions (t : @NTerm o) : bool :=
  match get_abstraction_name t with
  | Some name =>
    if in_deq _ String.string_dec name abstractions then
      match unfold lib t with
      | Some u => true
      | None => false
      end
    else true
  | None => true
  end.

Fixpoint abstractions_can_be_unfolded {o} lib abstractions (t : @NTerm o) : bool :=
  match t with
  | vterm v => true
  | sterm f => true
  | oterm op bs =>
    (forallb (abstractions_can_be_unfolded_b lib abstractions) bs)
      &&
    unfoldable lib abstractions t
  end
with abstractions_can_be_unfolded_b {o} lib abstractions (b : @BTerm o) : bool :=
       match b with
       | bterm vs t => abstractions_can_be_unfolded lib abstractions t
       end.

Definition all_abstractions_can_be_unfolded {o} lib abstractions (t : @NTerm o) :=
  abstractions_can_be_unfolded lib abstractions t = true.


(* ===========================================================

  Decidable alpha_eq

  ============================================================ *)

Lemma map_map2 :
  forall {A B C} (f : B -> C) (g : A -> B) (l : list A),
    map f (map g l) = map (compose f g) l.
Proof.
  induction l; simpl; auto.
  f_equal; auto.
Defined.

Lemma eq_maps2 :
  forall {A B} (f g : A -> B) (l : list A),
    (forall x,  LIn x l -> f x = g x)
    -> map f l = map g l.
Proof.
  induction l; simpl; auto; introv imp.
  f_equal.
  { apply imp; auto. }
  apply IHl; introv i; apply imp; auto.
Defined.


Definition term_is_var {o} (t : @NTerm o) : bool :=
  match t with
  | vterm _ => true
  | _ => false
  end.

Definition all_vars_sub {o} (s : @Sub o) : bool :=
  forallb (fun x => term_is_var (snd x)) s.

Lemma size_sub_find_var_ren {o} :
  forall s v,
    all_vars_sub s = true
    -> size match sub_find s v with
            | Some t => t
            | None => @vterm o v
            end = 1.
Proof.
  induction s; introv allvs; simpl in *; auto.
  destruct a; simpl in *.
  destruct (beq_var n v) as [d|d]; simpl; auto.
  - destruct n0; simpl in *; auto.
    inversion allvs.
  - apply IHs.
    destruct n0; simpl in *; auto.
Defined.

Lemma implies_all_vars_sub_sub_filter {o} :
  forall (s : @Sub o) l,
    all_vars_sub s = true
    -> all_vars_sub (sub_filter s l) = true.
Proof.
  induction s; introv allvs; simpl in *; auto.
  destruct a.
  simpl in *.
  destruct (memvar n l) as [d|d]; simpl in *.
  - apply IHs.
    destruct n0; simpl in *; auto.
  - destruct n0; simpl in *; auto.
Defined.

Lemma size_lsubst_aux_vars_ren_eq {o} :
  forall (t : @NTerm o) s,
    all_vars_sub s = true
    -> size (lsubst_aux t s) = size t.
Proof.
  sp_nterm_ind1 t as [v|f|op bs ind] Case; introv allvs; simpl; auto.

  - Case "vterm".
    apply size_sub_find_var_ren; auto.

  - Case "oterm".
    f_equal.
    f_equal.
    rewrite map_map2.
    unfold compose.
    apply eq_maps2.
    introv i.
    destruct x as [l t]; simpl.
    apply (ind t l); auto.
    apply implies_all_vars_sub_sub_filter; auto.
Defined.

Lemma all_vars_sub_var_ren {o} :
  forall l1 l2, @all_vars_sub o (var_ren l1 l2) = true.
Proof.
  induction l1; introv; simpl; auto.
  destruct l2; simpl; auto.
  apply IHl1.
Defined.

Lemma size_change_bvars_alpha {o} :
  forall (t : @NTerm o) l,
    size (change_bvars_alpha l t) = size t.
Proof.
  sp_nterm_ind1 t as [v|f|op bs ind] Case; introv; simpl; auto.
  f_equal.
  f_equal.
  rewrite map_map2; unfold compose.
  apply eq_maps2.
  introv i.
  destruct x as [vs t]; simpl.
  rewrite size_lsubst_aux_vars_ren_eq;[|apply all_vars_sub_var_ren].
  eapply ind; exact i.
Defined.

Lemma size_lsubst_vars_ren_eq {o} :
  forall (t : @NTerm o) l1 l2, size (lsubst t (var_ren l1 l2)) = size t.
Proof.
  introv.
  unfold lsubst; simpl.
  destruct (dec_disjointv (bound_vars t) (flat_map free_vars (range (var_ren l1 l2)))) as [d|d].

  - apply size_lsubst_aux_vars_ren_eq.
    apply all_vars_sub_var_ren.

  - rewrite size_lsubst_aux_vars_ren_eq;[|apply all_vars_sub_var_ren].
    apply size_change_bvars_alpha.
Defined.

Lemma alpha_eq_dec_op {o} :
  forall (x y : @NTerm o), option (alpha_eq x y).
Proof.
  induction x as [v1|f1|op1 bs1 ind] using NTerm_simple_better_ind2; introv.

  - destruct y as [v2|f1|op bs2];[|exact None|exact None].
    destruct (deq_nvar v1 v2); subst;[|exact None].
    left.
    apply alpha_eq_refl.

  - right.

  - destruct y as [v2|f2|op2 bs2];[right|right|].
    destruct (opid_dec_op op1 op2); subst;[|right].

    assert (option (alpha_eq_bterms bs1 bs2)) as opbs.
    {
      revert bs2.
      induction bs1; introv.

      - destruct bs2;[left|right].
        apply alpha_eq_bterms_refl.

      - destruct bs2;[right|].
        destruct a as [l1 t1], b as [l2 t2].
        simpl in *.
        autodimp IHbs1 hyp.
        { introv i; introv; eapply ind; eauto. }
        pose proof (IHbs1 bs2) as h; clear IHbs1.
        destruct h as [aeqs|];[|right].

        destruct (deq_nat (length l1) (length l2)) as [d|d];[|right].

        remember (fresh_distinct_vars (length l1) (all_vars t1 ++ all_vars t2)) as l.

        pose proof (ind t1 (lsubst t1 (var_ren l1 l)) l1) as q; clear ind.
        repeat (autodimp q hyp).

        { rewrite size_lsubst_vars_ren_eq; auto. }

        pose proof (q (lsubst t2 (var_ren l2 l))) as w; clear q.
        destruct w as [aeq|];[|right].
        left; auto.
        unfold alpha_eq_bterms in *; simpl; repnd.
        dands; auto.
        introv i; destruct i as [i|i].

        + inversion i; clear i.
          subst b1 b2.

          pose proof (fresh_distinct_vars_spec (length l1) (all_vars t1 ++ all_vars t2)) as q.
          rewrite <- Heql in q; clear Heql; simpl in q; repnd.

          apply (al_bterm _ _ l); auto.

        + apply aeqs; auto.
    }

    destruct opbs as [d|d]; subst;[left|right];auto.

    unfold alpha_eq_bterms in *; repnd.
    constructor; auto.
    introv i.
    apply d.

    pose proof (select2bts bs1 bs2 n) as q.
    repeat (autodimp q hyp).
    exrepnd; subst; auto.
Defined.



(* ===========================================================

  A proof step is essentially a rule name

  ============================================================ *)

Inductive proof_step {o} :=
| proof_step_lemma                     (name : LemmaName)
| proof_step_lemma_with_extract        (name : LemmaName)
| proof_step_base_closed
| proof_step_base_closed2
| proof_step_int_equality
| proof_step_base_equality
| proof_step_isect_equality            (y : NVar)
| proof_step_function_equality         (y : NVar)
| proof_step_isect_member_formation    (z : NVar) (i : nat)
| proof_step_hypothesis                (x : NVar)
| proof_step_hypothesis_num            (n : nat)
| proof_step_cut                       (x : NVar) (B : @NTerm o)
| proof_step_cequiv_computation        (n : nat)
| proof_step_cequiv_computation_aeq    (n : nat)
| proof_step_cequiv_computation_atmost (n : nat)
| proof_step_unfold_abstractions       (names : list opname)
| proof_step_rev_unfold_abstractions   (names : list opname) (a : @NTerm o)
| proof_step_cequiv_subst_concl        (x : NVar) (C a b : @NTerm o)
| proof_step_cequiv_subst_hyp          (z x : NVar) (T a b : @NTerm o)
| proof_step_cequiv_subst_hyp_num      (n : nat) (x : NVar) (T a b : @NTerm o)
| proof_step_universe_equality
| proof_step_hypothesis_equality
| proof_step_maybe_hidden_hypothesis_equality
| proof_step_unhide_equality           (x : NVar)
| proof_step_equality_equality
| proof_step_equality_equality_base
| proof_step_integer_equality
| proof_step_introduction              (t : @NTerm o)
| proof_step_axiom_equality
| proof_step_thin                      (x : NVar)
| proof_step_thin_num                  (n : nat)
| proof_step_apply_equality            (x : NVar) (A B : @NTerm o)
| proof_step_isect_elimination         (n : nat) (a : @NTerm o) (x : NVar)
| proof_step_isect_elimination2        (n : nat) (a : @NTerm o) (x y : NVar)
| proof_step_isect_member_equality     (x : NVar) (i : nat)
| proof_step_cumulativity              (i : nat)
| proof_step_equality_symmetry
| proof_step_equality_transitivity     (c : @NTerm o)
| proof_step_cequiv_transitivity       (c : @NTerm o)
| proof_step_approx_refl
| proof_step_cequiv_refl
| proof_step_cequiv_alpha_eq
| proof_step_cequiv_approx
| proof_step_approx_eq
| proof_step_cequiv_eq.



(* ===========================================================

  A pre-proof is a tree of proof-steps without the extracts,
  which we can only build once the proof is finished

  ============================================================ *)

Inductive pre_proof {o} :=
| pre_proof_hole
    (concl : @pre_baresequent o)
| pre_proof_node
    (name  : @proof_step o)
    (concl : @pre_baresequent o)
    (hyps  : list pre_proof).

Inductive proof {o} :=
| proof_node
    (name  : @proof_step o)
    (concl : @baresequent o)
    (hyps  : list proof).


(*(* We have the library here so that we can unfold abstractions *)
Inductive pre_proof {o} : @pre_baresequent o -> Type :=
| pre_proof_from_ctxt :
    forall (c : named_concl) H,
      pre_proof (named_concl2pre_bseq H c)
| pre_proof_hole : forall (s : pre_baresequent), pre_proof s
| pre_proof_isect_eq :
    forall a1 a2 b1 b2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> pre_proof (pre_rule_isect_equality_hyp1 a1 a2 i H)
      -> pre_proof (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H)
      -> pre_proof (pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
| pre_proof_isect_member_formation :
    forall A x B z i H,
      NVin z (vars_hyps H)
      -> pre_proof (pre_rule_isect_member_formation_hyp1 z A x B H)
      -> pre_proof (pre_rule_isect_member_formation_hyp2 A i H)
      -> pre_proof (pre_rule_isect_member_formation_concl A x B H)
| pre_proof_approx_refl :
    forall a (H : bhyps),
      pre_proof (pre_rule_approx_refl_concl a H)
| pre_proof_cequiv_refl :
    forall a (H : bhyps),
      pre_proof (pre_rule_cequiv_refl_concl a H)
| pre_proof_cequiv_alpha_eq :
    forall a b H,
      alpha_eq a b
      -> pre_proof (pre_rule_cequiv_alpha_eq_concl a b H)
| pre_proof_cequiv_approx :
    forall a b H,
      pre_proof (pre_rule_cequiv_approx_hyp a b H)
      -> pre_proof (pre_rule_cequiv_approx_hyp b a H)
      -> pre_proof (pre_rule_cequiv_approx_concl a b H)
| pre_proof_approx_eq :
    forall a1 a2 b1 b2 i H,
      pre_proof (pre_rule_eq_base_hyp a1 a2 H)
      -> pre_proof (pre_rule_eq_base_hyp b1 b2 H)
      -> pre_proof (pre_rule_approx_eq_concl a1 a2 b1 b2 i H)
| pre_proof_cequiv_eq :
    forall a1 a2 b1 b2 i H,
      pre_proof (pre_rule_eq_base_hyp a1 a2 H)
      -> pre_proof (pre_rule_eq_base_hyp b1 b2 H)
      -> pre_proof (pre_rule_cequiv_eq_concl a1 a2 b1 b2 i H)
(*| pre_proof_bottom_diverges :
    forall x H J,
      pre_proof hole ctxt (pre_rule_bottom_diverges_concl x H J)*)
| pre_proof_cut :
    forall B C x H,
      wf_term B
      -> covered B (vars_hyps H)
      -> NVin x (vars_hyps H)
      -> pre_proof (pre_rule_cut_hyp1 H B)
      -> pre_proof (pre_rule_cut_hyp2 H x B C)
      -> pre_proof (pre_rule_cut_concl H C)
(*| pre_proof_equal_in_base :
    forall a b H,
      pre_proof hole ctxt (pre_rule_equal_in_base_hyp1 a b H)
      -> (forall v, LIn v (free_vars a) -> pre_proof hole ctxt (pre_rule_equal_in_base_hyp2 v H))
      -> pre_proof hole ctxt (pre_rule_equal_in_base_concl a b H)*)
| pre_proof_hypothesis :
    forall x A G J,
      pre_proof (pre_rule_hypothesis_concl G J A x)
| pre_proof_cequiv_subst_concl :
    forall C x a b H,
      wf_term a
      -> wf_term b
      -> covered a (vars_hyps H)
      -> covered b (vars_hyps H)
      -> pre_proof (pre_rule_cequiv_subst_hyp2 H a b)
      -> pre_proof (pre_rule_cequiv_subst_hyp1 H x C b)
      -> pre_proof (pre_rule_cequiv_subst_hyp1 H x C a)
| pre_proof_cequiv_subst_hyp :
    forall H z T x a b J C,
      wf_term a
      -> wf_term b
      -> covered a (vars_hyps H)
      -> covered b (vars_hyps H)
      -> pre_proof (pre_rule_cequiv_subst_hyp_hyp2 H z T x a J b)
      -> pre_proof (pre_rule_cequiv_subst_hyp_hyp1 H z T x b J C)
      -> pre_proof (pre_rule_cequiv_subst_hyp_concl H z T x a J C)
(*| pre_proof_approx_member_eq :
    forall a b H,
      pre_proof hole ctxt (pre_rule_approx_member_eq_hyp a b H)
      -> pre_proof hole ctxt (pre_rule_approx_member_eq_concl a b H)*)
| pre_proof_cequiv_computation :
    forall lib a b H,
      reduces_to lib a b
      -> pre_proof (pre_rule_cequiv_computation_concl a b H)
| pre_proof_cequiv_computation_aeq :
    forall lib a b c H,
      reduces_to lib a b
      -> alpha_eq b c
      -> pre_proof (pre_rule_cequiv_computation_concl a c H)
| pre_proof_cequiv_computation_atmost :
    forall lib a b n H,
      reduces_in_atmost_k_steps lib a b n
      -> pre_proof (pre_rule_cequiv_computation_concl a b H)
| pre_proof_unfold_abstractions :
    forall lib abs a H,
      all_abstractions_can_be_unfolded lib abs a
      -> pre_proof (pre_rule_unfold_abstractions_hyp lib abs a H)
      -> pre_proof (pre_rule_unfold_abstractions_concl a H)
| pre_proof_rev_unfold_abstractions :
    forall lib abs a H,
      wf_term a
      -> covered a (vars_hyps H)
      -> all_abstractions_can_be_unfolded lib abs a
      -> pre_proof (pre_rule_unfold_abstractions_concl a H)
      -> pre_proof (pre_rule_unfold_abstractions_hyp lib abs a H)
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
      -> pre_proof (pre_rule_universe_equality_concl H i j)
| pre_proof_hypothesis_equality :
    forall x A G J,
      pre_proof (pre_rule_hypothesis_equality_concl G J A x)
| pre_proof_maybe_hidden_hypothesis_equality :
    forall x A G J b,
      pre_proof (pre_rule_maybe_hidden_hypothesis_equality_concl G J A x b)
| pre_proof_unhide_equality :
    forall x A t1 t2 C G J,
      pre_proof (pre_rule_unhide_equality_hyp G J x A t1 t2 C)
      -> pre_proof (pre_rule_unhide_equality_concl G J x A t1 t2 C)
| pre_proof_equality_equality :
    forall A B a1 a2 b1 b2 i H,
      pre_proof (pre_rule_equality_equality_hyp1 H A B i)
      -> pre_proof (pre_rule_equality_equality_hyp2 H a1 b1 A)
      -> pre_proof (pre_rule_equality_equality_hyp2 H a2 b2 A)
      -> pre_proof (pre_rule_equality_equality_concl H a1 a2 b1 b2 A B i)
| pre_proof_integer_equality :
    forall n H,
      pre_proof (pre_rule_integer_equality_concl H n)
| pre_proof_introduction :
    forall t C H,
      wf_term t
      -> covered t (nh_vars_hyps H)
      -> noutokens t
      -> pre_proof (pre_rule_introduction_hyp H C t)
      -> pre_proof (pre_rule_introduction_concl H C)
| pre_proof_axiom_equality :
    forall a b T H,
      pre_proof (pre_rule_axiom_equality_hyp a b T H)
      -> pre_proof (pre_rule_axiom_equality_concl a b T H)
| pre_proof_thin :
    forall G J A C x,
      NVin x (free_vars_hyps J)
      -> NVin x (free_vars C)
      -> pre_proof (pre_rule_thin_hyp G J C)
      -> pre_proof (pre_rule_thin_concl G x A J C)
| pre_proof_function_equality :
    forall a1 a2 b1 b2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> pre_proof (pre_rule_function_equality_hyp1 H a1 a2 i)
      -> pre_proof (pre_rule_function_equality_hyp2 H y a1 b1 x1 b2 x2 i)
      -> pre_proof (pre_rule_function_equality_concl H a1 x1 b1 a2 x2 b2 i)
| pre_proof_apply_equality :
    forall A B f1 f2 t1 t2 x H,
      wf_term A
      -> covered A (vars_hyps H)
      -> pre_proof (pre_rule_apply_equality_hyp1 H f1 f2 A x B)
      -> pre_proof (pre_rule_apply_equality_hyp2 H t1 t2 A)
      -> pre_proof (pre_rule_apply_equality_concl H f1 t1 f2 t2 B x)
| pre_proof_isect_elimination :
    forall A B C a f x z H J,
      wf_term a
      -> covered a (snoc (vars_hyps H) f ++ vars_hyps J)
      -> NVin z (vars_hyps H)
      -> NVin z (vars_hyps J)
      -> z <> f
      -> pre_proof (pre_rule_isect_elimination_hyp1 A B a f x H J)
      -> pre_proof (pre_rule_isect_elimination_hyp2 A B C a f x z H J)
      -> pre_proof (pre_rule_isect_elimination_concl A B C f x H J)
| pre_proof_isect_elimination2 :
    forall A B C a f x y z H J,
      wf_term a
      -> covered a (snoc (vars_hyps H) f ++ vars_hyps J)
      -> NVin z (vars_hyps H)
      -> NVin z (vars_hyps J)
      -> NVin y (vars_hyps H)
      -> NVin y (vars_hyps J)
      -> z <> f
      -> z <> y
      -> y <> f
      -> pre_proof (pre_rule_isect_elimination_hyp1 A B a f x H J)
      -> pre_proof (pre_rule_isect_elimination2_hyp2 A B C a f x y z H J)
      -> pre_proof (pre_rule_isect_elimination2_concl A B C f x H J)
| pre_proof_isect_member_equality :
    forall H t1 t2 A x B z i,
      NVin z (vars_hyps H)
      -> pre_proof (pre_rule_isect_member_equality_hyp1 H z A t1 t2 B x)
      -> pre_proof (pre_rule_isect_member_equality_hyp2 H A i)
      -> pre_proof (pre_rule_isect_member_equality_concl H t1 t2 A x B)
| pre_proof_cumulativity :
    forall H T i j,
      i <=? j = true
      -> pre_proof (pre_rule_cumulativity_hyp H T i)
      -> pre_proof (pre_rule_cumulativity_concl H T j)
| pre_proof_equality_symmetry :
    forall H a b T,
      pre_proof (pre_rule_equality_seq H b a T)
      -> pre_proof (pre_rule_equality_seq H a b T)
| pre_proof_equality_transitivity :
    forall H a b c T,
      wf_term c
      -> covered c (vars_hyps H)
      -> pre_proof (pre_rule_equality_seq H a c T)
      -> pre_proof (pre_rule_equality_seq H c b T)
      -> pre_proof (pre_rule_equality_seq H a b T)
| pre_proof_cequiv_transitivity :
    forall H a b c,
      wf_term c
      -> covered c (vars_hyps H)
      -> pre_proof (pre_rule_cequiv_seq H a c)
      -> pre_proof (pre_rule_cequiv_seq H c b)
      -> pre_proof (pre_rule_cequiv_seq H a b).*)


(*Inductive proof {o} : @baresequent o -> Type :=
| proof_from_ctxt :
    forall (c : named_concl) H,
      proof (named_concl2bseq H c)
| proof_isect_eq :
    forall a1 a2 b1 b2 e1 e2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> proof (rule_isect_equality2_hyp1 a1 a2 e1 i H)
      -> proof (rule_isect_equality2_hyp2 a1 b1 b2 e2 x1 x2 y i H)
      -> proof (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
| proof_isect_member_formation :
    forall A x B z i b e H,
      NVin z (vars_hyps H)
      -> proof (rule_isect_member_formation_hyp1 z A x B b H)
      -> proof (rule_isect_member_formation_hyp2 A e i H)
      -> proof (rule_isect_member_formation_concl A x B b H)
| proof_approx_refl :
    forall a (H : bhyps),
      proof (rule_approx_refl_concl a H)
| proof_cequiv_refl :
    forall a (H : bhyps),
      proof (rule_cequiv_refl_concl H a)
| proof_cequiv_alpha_eq :
    forall a b H,
      alpha_eq a b
      -> proof (rule_cequiv_alpha_eq_concl H a b)
| proof_cequiv_approx :
    forall a b e1 e2 H,
      proof (rule_cequiv_approx2_hyp a b e1 H)
      -> proof (rule_cequiv_approx2_hyp b a e2 H)
      -> proof (rule_cequiv_approx_concl a b H)
| proof_approx_eq :
    forall a1 a2 b1 b2 e1 e2 i H,
      proof (rule_eq_base2_hyp a1 a2 e1 H)
      -> proof (rule_eq_base2_hyp b1 b2 e2 H)
      -> proof (rule_approx_eq_concl a1 a2 b1 b2 i H)
| proof_cequiv_eq :
    forall a1 a2 b1 b2 e1 e2 i H,
      proof (rule_eq_base2_hyp a1 a2 e1 H)
      -> proof (rule_eq_base2_hyp b1 b2 e2 H)
      -> proof (rule_cequiv_eq_concl a1 a2 b1 b2 i H)
(*| proof_bottom_diverges :
    forall x H J,
      proof (rule_bottom_diverges_concl x H J)*)
| proof_cut :
    forall B C t u x H,
      wf_term B
      -> covered B (vars_hyps H)
      -> NVin x (vars_hyps H)
      -> proof (rule_cut_hyp1 H B u)
      -> proof (rule_cut_hyp2 H x B C t)
      -> proof (rule_cut_concl H C t x u)
(*| proof_equal_in_base :
    forall a b e F H,
      proof (rule_equal_in_base2_hyp1 a b e H)
      -> (forall v (i : LIn v (free_vars a)),
             proof (rule_equal_in_base2_hyp2 v (F v i) H))
      -> proof (rule_equal_in_base_concl a b H)*)
| proof_hypothesis :
    forall x A G J,
      proof (rule_hypothesis_concl G J A x)
| proof_cequiv_subst_concl :
    forall C x a b t e H,
      wf_term a
      -> wf_term b
      -> covered a (vars_hyps H)
      -> covered b (vars_hyps H)
      -> proof (rule_cequiv_subst2_hyp2 H a b e)
      -> proof (rule_cequiv_subst_hyp1 H x C b t)
      -> proof (rule_cequiv_subst_hyp1 H x C a t)
| proof_cequiv_subst_hyp :
    forall H z T x a b J C t e,
      wf_term a
      -> wf_term b
      -> covered a (vars_hyps H)
      -> covered b (vars_hyps H)
      -> proof (rule_cequiv_subst_hyp_hyp2 H z T x a J b e)
      -> proof (rule_cequiv_subst_hyp_hyp1 H z T x b J C t)
      -> proof (rule_cequiv_subst_hyp_concl H z T x a J C t)
(*| proof_approx_member_eq :
    forall a b e H,
      proof (rule_approx_member_eq2_hyp a b e H)
      -> proof (rule_approx_member_eq_concl a b H)*)
| proof_cequiv_computation :
    forall lib a b H,
      reduces_to lib a b
      -> proof (rule_cequiv_computation_concl a b H)
| proof_cequiv_computation_aeq :
    forall lib a b c H,
      reduces_to lib a b
      -> alpha_eq b c
      -> proof (rule_cequiv_computation_concl a c H)
| proof_cequiv_computation_atmost :
    forall lib a b n H,
      reduces_in_atmost_k_steps lib a b n
      -> proof (rule_cequiv_computation_concl a b H)
| proof_unfold_abstractions :
    forall lib abs a e H,
      all_abstractions_can_be_unfolded lib abs a
      -> proof (rule_unfold_abstractions_hyp lib abs a e H)
      -> proof (rule_unfold_abstractions_concl a e H)
| proof_rev_unfold_abstractions :
    forall lib abs a e H,
      wf_term a
      -> covered a (vars_hyps H)
      -> all_abstractions_can_be_unfolded lib abs a
      -> proof (rule_unfold_abstractions_concl a e H)
      -> proof (rule_unfold_abstractions_hyp lib abs a e H)
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
      -> proof (rule_function_elimination_hyp1 A B a ea f x H J)
      -> proof (rule_function_elimination_hyp2 A B C a e f x z H J)
      -> proof (rule_function_elimination_concl A B C e f x z H J)*)
| proof_universe_equality :
    forall i j H,
      i < j
      -> proof (rule_universe_equality_concl H i j)
| proof_hypothesis_equality :
    forall x A G J,
      proof (rule_hypothesis_equality_concl G J A x)
| proof_maybe_hidden_hypothesis_equality :
    forall x A G J b,
      proof (rule_maybe_hidden_hypothesis_equality_concl G J A x b)
| proof_unhide_equality :
    forall x A t1 t2 C e G J,
      proof (rule_unhide_equality_hyp G J x A t1 t2 C e)
      -> proof (rule_unhide_equality_concl G J x A t1 t2 C)
| proof_equality_equality :
    forall A B a1 a2 b1 b2 e1 e2 e3 i H,
      proof (rule_equality_equality_hyp1 H A B i e1)
      -> proof (rule_equality_equality_hyp2 H a1 b1 A e2)
      -> proof (rule_equality_equality_hyp2 H a2 b2 A e3)
      -> proof (rule_equality_equality_concl H a1 a2 b1 b2 A B i)
| proof_integer_equality :
    forall n H,
      proof (rule_integer_equality_concl H n)
| proof_introduction :
    forall t e C H,
      wf_term t
      -> covered t (nh_vars_hyps H)
      -> noutokens t
      -> proof (rule_introduction_hyp H C t e)
      -> proof (rule_introduction_concl H C t)
| proof_axiom_equality :
    forall e a b T H,
      proof (rule_axiom_equality_hyp e a b T H)
      -> proof (rule_axiom_equality_concl a b T H)
| proof_thin :
    forall G J A C t x,
      NVin x (free_vars_hyps J)
      -> NVin x (free_vars C)
      -> proof (rule_thin_hyp G J C t)
      -> proof (rule_thin_concl G x A J C t)
| proof_function_equality :
    forall a1 a2 b1 b2 e1 e2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> proof (rule_function_equality_hyp1 H a1 a2 i e1)
      -> proof (rule_function_equality_hyp2 H y a1 b1 x1 b2 x2 i e2)
      -> proof (rule_function_equality_concl H a1 x1 b1 a2 x2 b2 i)
| proof_apply_equality :
    forall A B f1 f2 t1 t2 e1 e2 x H,
      wf_term A
      -> covered A (vars_hyps H)
      -> proof (rule_apply_equality_hyp1 H f1 f2 A x B e1)
      -> proof (rule_apply_equality_hyp2 H t1 t2 A e2)
      -> proof (rule_apply_equality_concl H f1 t1 f2 t2 B x)
| proof_isect_elimination :
    forall A B C a e ea f x z H J,
      wf_term a
      -> covered a (snoc (vars_hyps H) f ++ vars_hyps J)
      -> NVin z (vars_hyps H)
      -> NVin z (vars_hyps J)
      -> z <> f
      -> proof (rule_isect_elimination_hyp1 A B a ea f x H J)
      -> proof (rule_isect_elimination_hyp2 A B C a e f x z H J)
      -> proof (rule_isect_elimination_concl A B C e f x z H J)
| proof_isect_elimination2 :
    forall A B C a e ea f x y z H J,
      wf_term a
      -> covered a (snoc (vars_hyps H) f ++ vars_hyps J)
      -> NVin z (vars_hyps H)
      -> NVin z (vars_hyps J)
      -> NVin y (vars_hyps H)
      -> NVin y (vars_hyps J)
      -> z <> f
      -> z <> y
      -> y <> f
      -> proof (rule_isect_elimination_hyp1 A B a ea f x H J)
      -> proof (rule_isect_elimination2_hyp2 A B C a e f x y z H J)
      -> proof (rule_isect_elimination2_concl A B C e f x y z H J)
| proof_isect_member_equality :
    forall H t1 t2 A x B e1 e2 z i,
      NVin z (vars_hyps H)
      -> proof (rule_isect_member_equality_hyp1 H z A t1 t2 B x e1)
      -> proof (rule_isect_member_equality_hyp2 H A i e2)
      -> proof (rule_isect_member_equality_concl H t1 t2 A x B)
| proof_cumulativity :
    forall H T e i j,
      i <=? j = true
      -> proof (rule_cumulativity_hyp H T i e)
      -> proof (rule_cumulativity_concl H T j)
| proof_equality_symmetry :
    forall H a b T e,
      proof (rule_equality_hyp H b a T e)
      -> proof (rule_equality_concl H a b T)
| proof_equality_transitivity :
    forall H a b c T e1 e2,
      wf_term c
      -> covered c (vars_hyps H)
      -> proof (rule_equality_hyp H a c T e1)
      -> proof (rule_equality_hyp H c b T e2)
      -> proof (rule_equality_concl H a b T)
| proof_cequiv_transitivity :
    forall H a b c e1 e2,
      wf_term c
      -> covered c (vars_hyps H)
      -> proof (rule_cequiv_trans_hyp H a c e1)
      -> proof (rule_cequiv_trans_hyp H c b e2)
      -> proof (rule_cequiv_trans_concl H a b).*)



(* ===========================================================

  The library consists of a list of abstractions and proved lemmas.
  The difference with ProofContext is that we include the proofs of
  lemmas.  [RigidLibrary2ProofContext] shows how to extract a proof context
  from a RigidLibrary.

  ============================================================ *)

Definition name_not_in_lib {o} (name : LemmaName) (l : @library o) :=
  !in_lib (opname2opabs name) l.

(* !!MOVE *)
Lemma soterm2nterm_nterm2soterm {o} :
  forall (t : @NTerm o), soterm2nterm (nterm2soterm t) = t.
Proof.
  sp_nterm_ind1 t as [v|f ind|op bs ind] Case; simpl; auto.
  Case "oterm".
  f_equal.
  induction bs; simpl in *; auto.
  rewrite IHbs;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
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

Lemma rename_valid_extract {o} :
  forall r {e : @NTerm o},
    valid_extract e -> valid_extract (rename_term r e).
Proof.
  introv valid.
  unfold valid_extract in *; repnd; dands; eauto 3 with slow.
Qed.


(*Lemma rename_correct {o} :
  forall {opabs vars rhs} (r : renaming) (correct : @correct_abs o opabs vars rhs),
    correct_abs (rename_opabs r opabs) vars (rename_soterm r rhs).
Proof.
  introv cor.
  unfold correct_abs in *; simpl in *; repnd; dands; eauto 3 with slow;
    autorewrite with slow in *; auto.
Defined.
Hint Resolve rename_correct : slow.

Lemma foo {o} :
  forall r name (ext : @NTerm o) valid,
    lib_abs
      (opname2opabs (rename_opname r name))
      []
      (rename_soterm r (nterm2soterm ext))
      (rename_correct r (extract2correct name ext valid))
    = lib_abs
        (opname2opabs (rename_opname r name))
        []
        (nterm2soterm (rename_term r ext))
        (extract2correct
           (rename_opname r name)
           (rename_term r ext)
           (rename_valid_extract r valid)).
Proof.
  introv.
  unfold valid_extract in *; repnd; simpl.
  unfold extract2correct.

Qed.*)


Definition proof2type {o} (p : @proof o) : NTerm :=
  match p with
  | proof_node n c H => ctype (concl c)
  end.

Definition proof2hyps {o} (p : @proof o) : barehypotheses :=
  match p with
  | proof_node n c H => hyps c
  end.

Definition proof2bseq {o} (p : @proof o) : baresequent :=
  match p with
  | proof_node n c H => c
  end.

Definition proof_of_bseq {o} (p : @proof o) (s : baresequent) : Prop :=
  s = proof2bseq p.

Definition pre_proof2bseq {o} (p : @pre_proof o) : pre_baresequent :=
  match p with
  | pre_proof_hole s => s
  | pre_proof_node n c H => c
  end.

Definition pre_proof_of_bseq {o} (p : @pre_proof o) (s : pre_baresequent) : Prop :=
  s = pre_proof2bseq p.

Definition proof2extract {o} (p : @proof o) : NTerm :=
  match p with
  | proof_node n c H => extract_ax (concl c)
  end.

Definition proof2extract_op {o} (p : @proof o) : option NTerm :=
  match p with
  | proof_node n c H => extract (concl c)
  end.

Definition valid_extract_of_proof {o} (p : @proof o) :=
  match proof2hyps p with
  | [] =>
    match proof2extract_op p with
    | Some e => valid_extract e
    | None => False
    end
  | _ => False
  end.

Definition type_of_proof_is_prog {o} (p : @proof o) := isprog (proof2type p).

Record wf_proof {o} (p : @proof o) :=
  MkWfProof {
      wf_proof_type : type_of_proof_is_prog p;
      wf_proof_ext  : valid_extract_of_proof p
    }.

Arguments MkWfProof [o] [p] _ _.
Arguments wf_proof_type [o] [p] _.
Arguments wf_proof_ext  [o] [p] _.

Inductive RigidLibraryEntry {o} :=
| RigidLibraryEntry_abs (e : @library_entry o)
| RigidLibraryEntry_proof
    (name  : LemmaName)
    (prf   : @proof o)
    (wf    : wf_proof prf).

(* A library is just a list of entries such that we store the most recent
   entry at the front of the list
 *)
Definition RigidLibrary {o} := list (@RigidLibraryEntry o).

Definition extract2def {o}
           (name  : LemmaName)
           (ext   : @NTerm o)
           (valid : valid_extract ext) : library_entry :=
  lib_abs
    (opname2opabs name)
    []
    (nterm2soterm ext)
    (extract2correct name ext valid).

Lemma valid_extract_if_valid_extract_of_proof {o} :
  forall {prf : @proof o},
    valid_extract_of_proof prf
    -> valid_extract (proof2extract prf).
Proof.
  introv valid.
  unfold valid_extract_of_proof in valid.
  destruct (proof2hyps prf); tcsp.
  unfold proof2extract.
  destruct prf; simpl in *.
  unfold extract_ax.
  remember (extract (sequents.concl concl)) as e; destruct e; auto; tcsp.
Qed.

Definition proof2def {o}
           (name  : LemmaName)
           {prf   : @proof o}
           (valid : valid_extract_of_proof prf) : @library_entry o :=
  extract2def
    name
    (proof2extract prf)
    (valid_extract_if_valid_extract_of_proof valid).

Definition extend_proof_context {o}
           (ctxt : @ProofContext o)
           (e    : RigidLibraryEntry) : ProofContext :=
  match e with
  | RigidLibraryEntry_abs e => updLibProofContext ctxt e
  | RigidLibraryEntry_proof name prf wf =>
    updLibProofContext
      (updConclProofContext ctxt (MkNamedConcl name (proof2type prf)))
      (proof2def name (wf_proof_ext wf))
  end.

Fixpoint RigidLibrary2ProofContext {o} (L : @RigidLibrary o) : ProofContext :=
  match L with
  | [] => EMPC
  | entry :: entries =>
    let ctxt := RigidLibrary2ProofContext entries in
    extend_proof_context ctxt entry
  end.

Definition RigidLibrary2lib {o} (L : @RigidLibrary o) : library := RigidLibrary2ProofContext L.

Fixpoint find_hypothesis_name_from_nat {o} (H : @bhyps o) (n : nat) : option NVar :=
  match H with
  | [] => None
  | h :: hs =>
    match n with
    | 0 => None
    | 1 =>  Some (hvar h)
    | S m => find_hypothesis_name_from_nat hs m
    end
  end.

Definition valid_proof_node_context {o}
           (ctxt : @ProofContext o)
           (n    : @proof_step o)
           (c    : @baresequent o)
           (hs   : list (@baresequent o)) : Type :=
  match n with
  | proof_step_lemma name =>
    {T : NTerm $ {H : bhyps $
      LIn (MkNamedConcl name T) (PC_conclusions ctxt)
      # c = named_concl2bseq H (MkNamedConcl name T)
      # hs = [] }}

  | proof_step_lemma_with_extract name =>
    {T : NTerm $ {t : NTerm $ {r : NTerm $ {H : bhyps $
      LIn (MkNamedConcl name T) (PC_conclusions ctxt)
      # c = named_concl2bseq_with_extract H (MkNamedConcl name T) t
      # reduces_to ctxt (LemmaName2extract name) r
      # alpha_eq r t
      # hs = [] }}}}

  | proof_step_base_closed =>
    {t : NTerm $
      c = rule_base_closed_concl t
      # hs = [] }

  | proof_step_base_closed2 =>
    {x : NTerm $ {t : NTerm $
      c = mk_bseq [] (mk_concl x mk_axiom)
      # reduces_in_atmost_k_steps ctxt x (mk_equality t t mk_base) 1
      # hs = [] }}

  | proof_step_int_equality =>
    {H : bhyps $ {i : nat $
      c = rule_int_equality_concl H i
      # hs = [] }}

  | proof_step_base_equality =>
    {H : bhyps $ {i : nat $
      c = rule_base_equality_concl H i
      # hs = [] }}

  | proof_step_isect_equality y =>
    {a1 , a2 , b1 , b2 , e1 , e2 : NTerm $ {x1 , x2 : NVar $ {i : nat $ {H : bhyps $
      ! LIn y (vars_hyps H)
      # c = rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H
      # hs = [rule_isect_equality2_hyp1 a1 a2 e1 i H,
              rule_isect_equality2_hyp2 a1 b1 b2 e2 x1 x2 y i H] }}}}

  | proof_step_isect_member_formation z i =>
    {A : NTerm $ {x : NVar $ {B , b , e : NTerm $ {H : bhyps $
    ! LIn z (vars_hyps H)
    # c = rule_isect_member_formation_concl A x B b H
    # hs = [rule_isect_member_formation_hyp1 z A x B b H,
	     rule_isect_member_formation_hyp2 A e i H] }}}}

  | proof_step_approx_refl =>
    {a : NTerm $ {H : bhyps $
    c = rule_approx_refl_concl a H
    # hs = [] }}

  | proof_step_cequiv_refl =>
    {a : NTerm $ {H : bhyps $
      c = rule_cequiv_refl_concl H a
      # hs = [] }}

  | proof_step_cequiv_alpha_eq =>
    {a , b : NTerm $ {H : bhyps $
    alpha_eq a b
    # c = rule_cequiv_alpha_eq_concl H a b
    # hs = [] }}

  | proof_step_cequiv_approx =>
    {a , b , e1 , e2 : NTerm $ {H : bhyps $
    c = rule_cequiv_approx_concl a b H
    # hs = [rule_cequiv_approx2_hyp a b e1 H,
             rule_cequiv_approx2_hyp b a e2 H] }}

  | proof_step_approx_eq =>
    {a1 , a2 , b1 , b2 , e1 , e2 : NTerm $ {i : nat $ {H : bhyps $
    c = rule_approx_eq_concl a1 a2 b1 b2 i H
    # hs = [rule_eq_base2_hyp a1 a2 e1 H,
             rule_eq_base2_hyp b1 b2 e2 H] }}}

  | proof_step_cequiv_eq =>
    {a1 , a2 , b1 , b2 , e1 , e2 : NTerm $ {i : nat $ {H : bhyps $
    c = rule_cequiv_eq_concl a1 a2 b1 b2 i H
    # hs = [rule_eq_base2_hyp a1 a2 e1 H,
             rule_eq_base2_hyp b1 b2 e2 H] }}}

  | proof_step_cut x B =>
    {C , t , u : NTerm $ {H : bhyps $
    wf_term B
    # covered B (vars_hyps H)
    # ! LIn x (vars_hyps H)
    # c = rule_cut_concl H C t x u
    # hs = [rule_cut_hyp1 H B u,
             rule_cut_hyp2 H x B C t] }}

  | proof_step_hypothesis x =>
    {A : NTerm $ {G , J : bhyps $
    c = rule_hypothesis_concl G J A x
    # hs = [] }}

  | proof_step_hypothesis_num n =>
    {A : NTerm $ {x : NVar $ {G , J : bhyps $
    find_hypothesis_name_from_nat (snoc G (mk_hyp x A) ++ J) n = Some x
    # c = rule_hypothesis_concl G J A x
    # hs = [] }}}

  | proof_step_cequiv_subst_concl x C a b =>
    {t , e : NTerm $ {H : bhyps $
    wf_term a
    # wf_term b
    # covered a (vars_hyps H)
    # covered b (vars_hyps H)
    # c = rule_cequiv_subst_hyp1 H x C a t
    # hs = [rule_cequiv_subst2_hyp2 H a b e,
             rule_cequiv_subst_hyp1 H x C b t] }}

  | proof_step_cequiv_subst_hyp z x T a b =>
    {H , J : bhyps $ {C , t , e : NTerm $
    wf_term a
    # wf_term b
    # covered a (vars_hyps H)
    # covered b (vars_hyps H)
    # c = rule_cequiv_subst_hyp_concl H z T x a J C t
    # hs = [rule_cequiv_subst_hyp_hyp2 H z T x a J b e,
             rule_cequiv_subst_hyp_hyp1 H z T x b J C t] }}

  | proof_step_cequiv_subst_hyp_num n x T a b =>
    {H , J : bhyps $ {z : NVar $ {C , t , e : NTerm $
    find_hypothesis_name_from_nat (snoc H (mk_hyp z (subst T x a)) ++ J) n = Some z
    # wf_term a
    # wf_term b
    # covered a (vars_hyps H)
    # covered b (vars_hyps H)
    # c = rule_cequiv_subst_hyp_concl H z T x a J C t
    # hs = [rule_cequiv_subst_hyp_hyp2 H z T x a J b e,
             rule_cequiv_subst_hyp_hyp1 H z T x b J C t] }}}

  | proof_step_cequiv_computation n =>
    {a , b : NTerm $ {H : bhyps $
    reduces_to ctxt a b
    # c = rule_cequiv_computation_concl a b H
    # hs = [] }}

  | proof_step_cequiv_computation_aeq n =>
    {a , b , d : NTerm $ {H : bhyps $
    reduces_to ctxt a b
    # alpha_eq b d
    # c = rule_cequiv_computation_concl a d H
    # hs = [] }}

  | proof_step_cequiv_computation_atmost n =>
    {a , b : NTerm $ {H : bhyps $ {k : nat $
    k <= n
    # reduces_in_atmost_k_steps ctxt a b k
    # c = rule_cequiv_computation_concl a b H
    # hs = [] }}}

  | proof_step_unfold_abstractions abs =>
    {a , e : NTerm $ {H : bhyps $
    all_abstractions_can_be_unfolded ctxt abs a
    # c = rule_unfold_abstractions_concl a e H
    # hs = [rule_unfold_abstractions_hyp ctxt abs a e H] }}

  | proof_step_rev_unfold_abstractions abs a =>
    {e : NTerm $ {H : bhyps $
    wf_term a
    # covered a (vars_hyps H)
    # all_abstractions_can_be_unfolded ctxt abs a
    # c = rule_unfold_abstractions_hyp ctxt abs a e H
    # hs = [rule_unfold_abstractions_concl a e H] }}

  | proof_step_universe_equality =>
    {i , j : nat $ {H : bhyps $
    i < j
    # c = rule_universe_equality_concl H i j
    # hs = [] }}

  | proof_step_hypothesis_equality =>
    {x : NVar $ {A : NTerm $ {G , J : bhyps $
    c = rule_hypothesis_equality_concl G J A x
    # hs = [] }}}

  | proof_step_maybe_hidden_hypothesis_equality =>
    {x : NVar $ {A : NTerm $ {G , J : bhyps $ {b : bool $
    c = rule_maybe_hidden_hypothesis_equality_concl G J A x b
    # hs = [] }}}}

  | proof_step_unhide_equality x =>
    {A , t1 , t2 , C , e : NTerm $ {G , J : bhyps $
    c = rule_unhide_equality_concl G J x A t1 t2 C
    # hs = [rule_unhide_equality_hyp G J x A t1 t2 C e] }}

  | proof_step_equality_equality =>
    {A , B , a1 , a2 , b1 , b2 : NTerm $ {e1 , e2 , e3 : NTerm $ {i : nat $ {H : bhyps $
    c = rule_equality_equality_concl H a1 a2 b1 b2 A B i
    # hs = [rule_equality_equality_hyp1 H A B i e1,
             rule_equality_equality_hyp2 H a1 b1 A e2,
             rule_equality_equality_hyp2 H a2 b2 A e3] }}}}

  | proof_step_equality_equality_base =>
    {A , B , a1 , a2 , b1 , b2 : NTerm $ {e1 , e2 , e3 : NTerm $ {i : nat $ {H : bhyps $
    c = rule_equality_equality_concl H a1 a2 b1 b2 A B i
    # hs = [rule_equality_equality_hyp1 H A B i e1,
             rule_equality_equality_hyp3 H a1 b1 e2,
             rule_equality_equality_hyp3 H a2 b2 e3] }}}}

  | proof_step_integer_equality =>
    {n : Z $ {H : bhyps $
    c = rule_integer_equality_concl H n
    # hs = [] }}

  | proof_step_introduction t =>
    {e , C : NTerm $ {H : bhyps $
    wf_term t
    # covered t (nh_vars_hyps H)
    # noutokens t
    # c = rule_introduction_concl H C t
    # hs = [rule_introduction_hyp H C t e] }}

  | proof_step_axiom_equality =>
    {e , a , b , T : NTerm $ {H : bhyps $
    c = rule_axiom_equality_concl a b T H
    # hs = [rule_axiom_equality_hyp e a b T H] }}

  | proof_step_thin x =>
    {G , J : bhyps $ {A , C , t : NTerm $
      ! LIn x (free_vars_hyps J)
      # ! LIn x (free_vars C)
      # c = rule_thin_concl G x A J C t
      # hs = [rule_thin_hyp G J C t] }}

  | proof_step_thin_num n =>
    {G , J : bhyps $ {x : NVar $ {A , C , t : NTerm $
      find_hypothesis_name_from_nat (snoc G (mk_hyp x A) ++ J) n = Some x
      # ! LIn x (free_vars_hyps J)
      # ! LIn x (free_vars C)
      # c = rule_thin_concl G x A J C t
      # hs = [rule_thin_hyp G J C t] }}}

  | proof_step_function_equality y =>
    {a1 , a2 , b1 , b2 , e1 , e2 : NTerm $ {x1 , x2 : NVar $ {i : nat $ {H : bhyps $
      !LIn y (vars_hyps H)
      # c = rule_function_equality_concl H a1 x1 b1 a2 x2 b2 i
      # hs = [rule_function_equality_hyp1 H a1 a2 i e1,
               rule_function_equality_hyp2 H y a1 b1 x1 b2 x2 i e2] }}}}

  | proof_step_apply_equality x A B =>
    {f1 , f2 , t1 , t2 , e1 , e2 : NTerm $ {H : bhyps $
    wf_term A
    # covered A (vars_hyps H)
    # c = rule_apply_equality_concl H f1 t1 f2 t2 B x
    # hs = [rule_apply_equality_hyp1 H f1 f2 A x B e1,
             rule_apply_equality_hyp2 H t1 t2 A e2] }}

  | proof_step_isect_elimination n a z =>
    {A , B , C , e , ea : NTerm $ {f , x : NVar $ {H , J : bhyps $
    find_hypothesis_name_from_nat (snoc H (mk_hyp f (mk_isect A x B)) ++ J) n = Some f
    # wf_term a
    # covered a (snoc (vars_hyps H) f ++ vars_hyps J)
    # ! LIn z (vars_hyps H)
    # ! LIn z (vars_hyps J)
    # z <> f
    # c = rule_isect_elimination_concl A B C e f x z H J
    # hs = [rule_isect_elimination_hyp1 A B a ea f x H J,
             rule_isect_elimination_hyp2 A B C a e f x z H J] }}}

  | proof_step_isect_elimination2 n a z y =>
    {A , B , C , e , ea : NTerm $ {f , x : NVar $ {H , J : bhyps $
    find_hypothesis_name_from_nat (snoc H (mk_hyp f (mk_isect A x B)) ++ J) n = Some f
    # wf_term a
    # covered a (snoc (vars_hyps H) f ++ vars_hyps J)
    # ! LIn z (vars_hyps H)
    # ! LIn z (vars_hyps J)
    # ! LIn y (vars_hyps H)
    # ! LIn y (vars_hyps J)
    # z <> f
    # z <> y
    # y <> f
    # c = rule_isect_elimination2_concl A B C e f x y z H J
    # hs = [rule_isect_elimination_hyp1 A B a ea f x H J,
             rule_isect_elimination2_hyp2 A B C a e f x y z H J] }}}

  | proof_step_isect_member_equality z i =>
    {H : bhyps $ {t1 , t2 , A : NTerm $ {x : NVar $ {B , e1 , e2 : NTerm $
    ! LIn z (vars_hyps H)
    # c = rule_isect_member_equality_concl H t1 t2 A x B
    # hs = [rule_isect_member_equality_hyp1 H z A t1 t2 B x e1,
             rule_isect_member_equality_hyp2 H A i e2] }}}}

  | proof_step_cumulativity i =>
    {H : bhyps $ {T , e : NTerm $ {j : nat $
    i <= j
    # c = rule_cumulativity_concl H T j
    # hs = [rule_cumulativity_hyp H T i e] }}}

  | proof_step_equality_symmetry =>
    {H : bhyps $ {a , b , T , e : NTerm $
    c = rule_equality_concl H a b T
    # hs = [rule_equality_hyp H b a T e] }}

  | proof_step_equality_transitivity d =>
    {H : bhyps $ {a , b , T , e1 , e2 : NTerm $
    wf_term d
    # covered d (vars_hyps H)
    # c = rule_equality_concl H a b T
    # hs = [rule_equality_hyp H a d T e1,
             rule_equality_hyp H d b T e2] }}

  | proof_step_cequiv_transitivity d =>
    {H : bhyps $ {a , b , e1 , e2 : NTerm $
    wf_term d
    # covered d (vars_hyps H)
    # c = rule_cequiv_trans_concl H a b
    # hs = [rule_cequiv_trans_hyp H a d e1,
             rule_cequiv_trans_hyp H d b e2] }}
  end.

Inductive valid_proof_context {o} (ctxt : @ProofContext o) : @proof o -> Type :=
| valid_proof_node :
    forall n c hs,
      valid_proof_node_context ctxt n c (map proof2bseq hs)
      -> (forall h, LIn h hs -> valid_proof_context ctxt h)
      -> valid_proof_context ctxt (proof_node n c hs).

Definition mon_true_sequent_wf {o} l (s : @baresequent o) :=
  sequent_true_ext_lib_wf l s.

Definition concl_has_extract {o} (c : @conclusion o) : bool :=
  match extract c with
  | Some e => true
  | None => false
  end.

Definition proof_has_extract {o} (p : @proof o) : bool :=
  match p with
  | proof_node n c H => concl_has_extract (concl c)
  end.

Definition ValidRigidLibraryEntry {o}
           (ctxt : @ProofContext o)
           (e    : RigidLibraryEntry) : Type :=
  match e with
  | RigidLibraryEntry_abs e => entry_not_in_lib e ctxt
  | RigidLibraryEntry_proof name prf wf =>
    (valid_proof_context ctxt prf)
    # proof_has_extract prf = true
    # name_not_in_lib name ctxt
    # mon_true_sequent_wf ctxt (NLemma (proof2type prf) (proof2extract prf))
  end.

Fixpoint ValidRigidLibrary {o} (L : @RigidLibrary o) : Type :=
  match L with
  | [] => True
  | entry :: entries =>
    ValidRigidLibraryEntry (RigidLibrary2ProofContext entries) entry
    # ValidRigidLibrary entries
  end.

Lemma wf_bseq_implies_wf_hypotheses {o} :
  forall (H : @bhyps o) s,
    wf_bseq (named_concl2bseq H s)
    -> wf_hypotheses H.
Proof.
  introv wf; unfold wf_bseq in *; repnd; auto.
Qed.
Hint Resolve wf_bseq_implies_wf_hypotheses : slow.

Lemma wf_bseq_with_extract_implies_wf_hypotheses {o} :
  forall (H : @bhyps o) s t,
    wf_bseq (named_concl2bseq_with_extract H s t)
    -> wf_hypotheses H.
Proof.
  introv wf; unfold wf_bseq in *; repnd; auto.
Qed.
Hint Resolve wf_bseq_with_extract_implies_wf_hypotheses : slow.


(* ===========================================================

  We'll now prove that proofs are valid and that the sequents
  in the library are true.

  ============================================================ *)

Lemma wf_term_unfold_abstractions {o} :
  forall lib abs (t : @NTerm o),
    wf_term t
    -> wf_term (unfold_abstractions lib abs t).
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv wf; simpl in *; auto.
  Case "oterm".

  unfold maybe_unfold; simpl.
  remember (get_abstraction_name_op op) as gop; destruct gop; symmetry in Heqgop.

  - boolvar.

    + destruct op; simpl.

      * allrw @wf_oterm_iff; repnd.
        allrw map_map; unfold compose.
        dands.

        { rw <- wf0; apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto. }

        introv i; allrw in_map_iff; exrepnd; subst.
        destruct a; simpl in *.
        applydup wf in i1.
        allrw @wf_bterm_iff.
        eapply ind; eauto.

      * allrw @wf_oterm_iff; repnd.
        allrw map_map; unfold compose.
        dands.

        { rw <- wf0; apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto. }

        introv i; allrw in_map_iff; exrepnd; subst.
        destruct a; simpl in *.
        applydup wf in i1.
        allrw @wf_bterm_iff.
        eapply ind; eauto.

      * allrw @wf_oterm_iff; repnd.
        allrw map_map; unfold compose.
        dands.

        { rw <- wf0; apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto. }

        introv i; allrw in_map_iff; exrepnd; subst.
        destruct a; simpl in *.
        applydup wf in i1.
        allrw @wf_bterm_iff.
        eapply ind; eauto.

      * remember (unfold_abs lib o1 (map (unfold_abstractions_b lib abs) bs)) as unf.
        destruct unf; symmetry in Hequnf.

        {
          apply unfold_abs_implies_find_entry in Hequnf; exrepnd; subst.
          eapply wf_mk_instance;[unfold found_entry;eauto|].
          introv i; allrw in_map_iff; exrepnd; subst.
          destruct a; simpl in *.
          allrw @wf_oterm_iff; repnd.
          applydup wf in i1.
          allrw @wf_bterm_iff.
          eapply ind; eauto.
        }

        {
          allrw @wf_oterm_iff; repnd.
          allrw map_map; unfold compose.
          dands.

          { rw <- wf0; apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto. }

          introv i; allrw in_map_iff; exrepnd; subst.
          destruct a; simpl in *.
          applydup wf in i1.
          allrw @wf_bterm_iff.
          eapply ind; eauto.
        }

    + allrw @wf_oterm_iff; repnd.
      allrw map_map; unfold compose.
      dands.

      { rw <- wf0; apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto. }

      introv i; allrw in_map_iff; exrepnd; subst.
      destruct a; simpl in *.
      applydup wf in i1.
      allrw @wf_bterm_iff.
      eapply ind; eauto.

  - allrw @wf_oterm_iff; repnd.
    allrw map_map; unfold compose.
    dands.

    { rw <- wf0; apply eq_maps; introv i; destruct x; unfold num_bvars; simpl; auto. }

    introv i; allrw in_map_iff; exrepnd; subst.
    destruct a; simpl in *.
    applydup wf in i1.
    allrw @wf_bterm_iff.
    eapply ind; eauto.
Qed.
Hint Resolve wf_term_unfold_abstractions : slow.

Lemma cequivc_lsubstc_unfold_abstractions_ext {o} :
  forall lib2 lib1 abs (t : @NTerm o) s w' c' w c,
    lib_extends lib2 lib1
    -> cequivc lib2 (lsubstc (unfold_abstractions lib1 abs t) w' s c') (lsubstc t w s c).
Proof.
  introv ext.
  unfold cequivc; simpl.
  apply lsubst_cequiv_congr; eauto 2 with slow.

  - apply olift_approx_cequiv; apply approx_star_implies_approx_open.

    + eapply approx_star_unfold_abstractions_left_ext; eauto 2 with slow.

    + eapply approx_star_unfold_abstractions_right_ext; eauto 2 with slow.

  - apply isprogram_csubst; eauto 2 with slow.

  - apply isprogram_csubst; eauto 2 with slow.
Qed.
Hint Resolve cequivc_lsubstc_unfold_abstractions_ext : slow.

Lemma mon_true_sequent_wf_preserves_lib_extends {o} :
  forall lib1 lib2 (a e : @NTerm o) H abs,
    wf_term a
    -> covered a (vars_hyps H)
    -> lib_extends lib2 lib1
    -> mon_true_sequent_wf lib2 (rule_unfold_abstractions_hyp lib1 abs a e H)
    -> mon_true_sequent_wf lib2 (rule_unfold_abstractions_hyp lib2 abs a e H).
Proof.
  introv wfa cova ext mon.
  unfold mon_true_sequent_wf, sequent_true_ext_lib_wf in *; exrepnd.
  unfold rule_unfold_abstractions_hyp in *; simpl in *.

  assert (wf_csequent (rule_unfold_abstractions_hyp lib2 abs a e H)) as wfc.
  {
    clear mon0.
    unfold rule_unfold_abstractions_hyp in *; simpl in *.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl in *; simpl in *.
    repnd; dands; auto; eauto 3 with slow.
  }

  exists wfc.
  introv ext'.
  applydup mon0 in ext'.

  rw @VR_sequent_true_ex in ext'0; simpl in *.
  apply VR_sequent_true_all; simpl.
  introv sim hf.
  pose proof (ext'0 s1 s2) as h; clear ext'0; repeat (autodimp h hyp).
  exrepnd.
  introv.

  assert (cover_vars a s1) as cov1.
  { eapply s_cover_typ1; eauto. }

  assert (cover_vars a s2) as cov2.
  { eapply s_cover_typ2; eauto. }

  dands.

  - eapply tequality_respects_cequivc_left;
      [apply cequivc_sym;apply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov1);eauto 3 with slow|].
    eapply tequality_respects_cequivc_right;
      [apply cequivc_sym;apply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov2);eauto 3 with slow|].
    eapply tequality_respects_cequivc_left in h0;
      [|eapply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov1); eauto 3 with slow].
    eapply tequality_respects_cequivc_right in h0;
      [|eapply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov2); eauto 3 with slow].
    auto.

  - eapply cequivc_preserving_equality;
      [|apply cequivc_sym;apply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov1);eauto 3 with slow].
    eapply cequivc_preserving_equality in h1;
      [|apply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov1);eauto 3 with slow].
    destruct c, wfc, w, w0, w, w0; simpl in *; proof_irr; auto.
Qed.

Lemma mon_true_sequent_wf_preserves_lib_extends2 {o} :
  forall lib1 lib2 (a e : @NTerm o) H abs,
    wf_term a
    -> covered a (vars_hyps H)
    -> lib_extends lib2 lib1
    -> mon_true_sequent_wf lib2 (rule_unfold_abstractions_hyp lib2 abs a e H)
    -> mon_true_sequent_wf lib2 (rule_unfold_abstractions_hyp lib1 abs a e H).
Proof.
  introv wfa cova ext mon.
  unfold mon_true_sequent_wf, sequent_true_ext_lib_wf in *; exrepnd.
  unfold rule_unfold_abstractions_hyp in *; simpl in *.

  assert (wf_csequent (rule_unfold_abstractions_hyp lib1 abs a e H)) as wfc.
  {
    clear mon0.
    unfold rule_unfold_abstractions_hyp in *; simpl in *.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl in *; simpl in *.
    repnd; dands; auto; eauto 3 with slow.
  }

  exists wfc.
  introv ext'.
  applydup mon0 in ext'.

  rw @VR_sequent_true_ex in ext'0; simpl in *.
  apply VR_sequent_true_all; simpl.
  introv sim hf.
  pose proof (ext'0 s1 s2) as h; clear ext'0; repeat (autodimp h hyp).
  exrepnd.
  introv.

  assert (cover_vars a s1) as cov1.
  { eapply s_cover_typ1; eauto. }

  assert (cover_vars a s2) as cov2.
  { eapply s_cover_typ2; eauto. }

  dands.

  - eapply tequality_respects_cequivc_left;
      [apply cequivc_sym;apply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov1);eauto 3 with slow|].
    eapply tequality_respects_cequivc_right;
      [apply cequivc_sym;apply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov2);eauto 3 with slow|].
    eapply tequality_respects_cequivc_left in h0;
      [|eapply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov1); eauto 3 with slow].
    eapply tequality_respects_cequivc_right in h0;
      [|eapply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov2); eauto 3 with slow].
    auto.

  - eapply cequivc_preserving_equality;
      [|apply cequivc_sym;apply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov1);eauto 3 with slow].
    eapply cequivc_preserving_equality in h1;
      [|apply (cequivc_lsubstc_unfold_abstractions_ext _ _ _ _ _ _ _ wfa cov1);eauto 3 with slow].
    destruct c, wfc, w, w0, w, w0; simpl in *; proof_irr; auto.
Qed.

Lemma wf_bseq_rule_unfold_abstractions_concl_implies_wf_term {o} :
  forall (a e : @NTerm o) H,
    wf_bseq (rule_unfold_abstractions_concl a e H)
    -> wf_term a.
Proof.
  introv wf.
  unfold rule_unfold_abstractions_concl in wf.
  unfold wf_bseq in wf; simpl in *; tcsp.
Qed.
Hint Resolve wf_bseq_rule_unfold_abstractions_concl_implies_wf_term : slow.

Lemma wf_bseq_rule_unfold_abstractions_concl_implies_covered {o} :
  forall (a e : @NTerm o) H,
    wf_bseq (rule_unfold_abstractions_concl a e H)
    -> covered a (vars_hyps H).
Proof.
  introv wf.
  unfold rule_unfold_abstractions_concl in wf.
  unfold wf_bseq in wf; simpl in *; tcsp.
Qed.
Hint Resolve wf_bseq_rule_unfold_abstractions_concl_implies_covered : slow.

Lemma lib_extends_preserves_wf_bseq_rule_unfold_abstractions_hyp {o} :
  forall lib2 lib1 (a e : @NTerm o) H abs,
    wf_term a
    -> covered a (vars_hyps H)
    -> lib_extends lib2 lib1
    -> wf_bseq (rule_unfold_abstractions_hyp lib1 abs a e H)
    -> wf_bseq (rule_unfold_abstractions_hyp lib2 abs a e H).
Proof.
  introv wfa cova ext wf.
  unfold wf_bseq, rule_unfold_abstractions_hyp in *; simpl in *; repnd.
  dands; eauto 3 with slow.
  unfold closed_type_baresequent, closed_type in *; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_wf_bseq_rule_unfold_abstractions_hyp : slow.

Hint Resolve reduces_to_preserves_lib_extends : slow.
Hint Resolve reduces_in_atmost_k_steps_preserves_lib_extends : slow.

Definition wf_proof_context {o} (ctxt : @ProofContext o) :=
  forall c H,
    wf_hypotheses H
    -> LIn c (PC_conclusions ctxt)
    -> mon_true_sequent_wf ctxt (named_concl2bseq H c).

Definition wf_proof_context_with_extract {o} (ctxt : @ProofContext o) :=
  forall c a t H,
    wf_hypotheses H
    -> LIn c (PC_conclusions ctxt)
    -> reduces_to ctxt (LemmaName2extract (nm_conclusion_name c)) a
    -> alpha_eq a t
    -> mon_true_sequent_wf ctxt (named_concl2bseq_with_extract H c t).

Fixpoint proof_size {o} (p : @proof o) : nat :=
  match p with
  | proof_node n c ps => S (addl (map proof_size ps))
  end.

Lemma le_addl :
  forall {T} (f : T -> nat) (t : T) ts,
    LIn t ts -> f t <= addl (map f ts).
Proof.
  induction ts; introv i; allsimpl; tcsp.
  repndors; subst; tcsp; try lia.
  apply IHts in i; try lia.
Qed.

Lemma proof_better_ind {o} :
  forall (P : @proof o -> Type),
    (forall n c ps (ind : forall p, LIn p ps -> P p), P (proof_node n c ps))
    -> forall p : proof, P p.
Proof.
  introv hn; introv.
  remember (proof_size p) as n.
  revert p Heqn.
  induction n as [? imp] using comp_ind_type; introv h; subst.

  destruct p; simpl; auto.
  apply hn; introv i.
  clear hn.

  pose proof (imp (proof_size p)) as q; clear imp; apply q; auto.
  simpl.
  apply (le_addl proof_size) in i; try lia.
Defined.

Lemma isprogram_implies_covered {o} :
  forall (a : @NTerm o) l,
    isprogram a
    -> covered a l.
Proof.
  introv isp.
  destruct isp as [cl wf].
  unfold covered; allrw; auto.
Qed.
Hint Resolve isprogram_implies_covered : slow.

Lemma isprogram_implies_disjoint_free_vars {o} :
  forall (a : @NTerm o) l,
    isprogram a
    -> disjoint l (free_vars a).
Proof.
  introv isp.
  destruct isp as [cl wf]; rewrite cl; auto.
Qed.
Hint Resolve isprogram_implies_disjoint_free_vars : slow.

Lemma covered_implies_closed {o} :
  forall (t : @NTerm o),
    covered t []
    -> closed t.
Proof.
  introv cov.
  unfold closed.
  unfold covered in cov.
  apply subvars_nil_r in cov; auto.
Qed.
Hint Resolve covered_implies_closed : slow.

Lemma cequiv_preserves_mon_true_sequent_wf {o} :
  forall lib H (a b e : @NTerm o),
    (forall lib', lib_extends lib' lib -> cequiv lib' a b)
    -> mon_true_sequent_wf lib (mk_bseq H (mk_concl a e))
    -> mon_true_sequent_wf lib (mk_bseq H (mk_concl b e)).
Proof.
  introv ceq mon.
  unfold mon_true_sequent_wf, sequent_true_ext_lib_wf in *; exrepnd.
  pose proof (ceq lib (lib_extends_refl lib)) as isp.
  applydup @cequiv_isprogram in isp; repnd.

  assert (wf_csequent (mk_bseq H (mk_concl b e))) as wf.
  {
    clear mon0.
    unfold wf_csequent, wf_sequent, wf_concl, closed_type in *; simpl in *; repnd.
    dands; eauto 3 with slow.
  }
  exists wf.
  rw @sequent_true_ext_lib_ex in mon0; simpl in *.
  apply sequent_true_ext_lib_all; simpl in *; introv ext sim hf; introv.
  pose proof (mon0 lib0 s1 s2 ext hf sim) as mon0; exrepnd.

  unfold wf_csequent, wf_sequent, wf_concl in *; simpl in *; repnd; simpl in *.
  proof_irr.

  dands.

  - eapply tequality_respects_cequivc_left;
      [|eapply tequality_respects_cequivc_right];[| |eauto];
        unfold cequivc; simpl;
          repeat (rewrite csubst_trivial; eauto 3 with slow).

  - eapply cequivc_preserving_equality;[eauto|].
    unfold cequivc; simpl.
    repeat (rewrite csubst_trivial; eauto 3 with slow).
Qed.

Lemma reduces_to_preserves_mon_true_sequent_wf {o} :
  forall lib H (a b e : @NTerm o),
    isprogram b
    -> reduces_to lib b a
    -> mon_true_sequent_wf lib (mk_bseq H (mk_concl a e))
    -> mon_true_sequent_wf lib (mk_bseq H (mk_concl b e)).
Proof.
  introv isp r mon.
  eapply cequiv_preserves_mon_true_sequent_wf;[|eauto].
  introv ext.
  eapply reduces_to_preserves_lib_extends in r;[|eauto].
  apply cequiv_sym.
  apply reduces_to_implies_cequiv; auto.
Qed.

Lemma wf_bseq_nil_implies_isprogram {o} :
  forall (t : @NTerm o) e,
    wf_bseq (mk_bseq [] (mk_concl t e)) -> isprogram t.
Proof.
  introv wf.
  unfold wf_bseq, closed_type_baresequent, closed_type in *; simpl in *; repnd.
  split; eauto 3 with slow.
Qed.
Hint Resolve wf_bseq_nil_implies_isprogram : slow.

Lemma reduces_in_1_step_implies_wf_bseq_rule_base_closed_concl {o} :
  forall lib (x t : @NTerm o),
    reduces_in_atmost_k_steps lib x (mk_equality t t mk_base) 1
    -> wf_bseq (mk_bseq [] (mk_concl x mk_axiom))
    -> wf_bseq (rule_base_closed_concl t).
Proof.
  introv r wf.
  unfold wf_bseq, closed_type_baresequent, closed_type in *; simpl in *; repnd.
  rw @wf_member_iff2.
  rw @covered_member.
  apply reduces_in_atmost_k_steps_implies_reduces_to in r.
  applydup @reduces_to_free_vars in r; eauto 3 with slow.
  apply reduces_to_preserves_wf in r; auto.
  rw @wf_member_iff2 in r; repnd.
  simpl in *; autorewrite with slow in *.
  apply app_subset in r0; repnd.
  dands; eauto 2 with slow.
  unfold covered in *.
  allrw subvars_eq.
  introv i; apply r2 in i; apply wf in i; auto.
Qed.
Hint Resolve reduces_in_1_step_implies_wf_bseq_rule_base_closed_concl : slow.


(* By assuming [wf_bseq seq], when we start with a sequent with no hypotheses,
   it means that we have to prove that the conclusion is well-formed and closed.
 *)
Lemma valid_proof {o} :
  forall (ctxt : @ProofContext o) s (prf : proof),
    wf_bseq s
    -> wf_proof_context ctxt
    -> wf_proof_context_with_extract ctxt
    -> proof_of_bseq prf s
    -> valid_proof_context ctxt prf
    -> mon_true_sequent_wf ctxt s.
Proof.
  introv wfs wfc wfce pob valid.
  revert dependent s.

  induction prf using proof_better_ind; introv wfs pob;[].

  inversion valid as [? ? ? val imp]; clear valid; subst; auto.
  unfold proof_of_bseq in pob; subst; simpl in *.

  destruct n; simpl in *; exrepnd; subst;
    repeat (destruct ps; simpl in *; ginv);
    repeat (apply cons_inj in val1; repnd; GC);
    repeat (apply cons_inj in val0; repnd; GC).

  - apply wfc; eauto 3 with slow.

  - eapply wfce; eauto 3 with slow.

  - apply rule_base_closed_true_ext_lib; simpl in *; tcsp.

  - eapply reduces_to_preserves_mon_true_sequent_wf;[|exists 1;eauto|];
      [|apply rule_base_closed_true_ext_lib; simpl in *; tcsp]; eauto 3 with slow.

  - apply rule_int_equality_true_ext_lib; simpl in *; tcsp.

  - apply rule_base_equality_true_ext_lib; simpl in *; tcsp.

  - apply (rule_isect_equality2_true_ext_lib ctxt a1 a2 b1 b2 e1 e2 x1 x2 y i H); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply (ind p); auto; try (unfold proof_of_bseq; auto).
        apply (rule_isect_equality2_wf2 y i a1 a2 b1 b2 e1 e2 x1 x2 H); simpl; tcsp.

      * apply (ind p0); auto; try (unfold proof_of_bseq; auto).
        apply (rule_isect_equality2_wf2 y i a1 a2 b1 b2 e1 e2 x1 x2 H); simpl; tcsp.

  - apply (rule_function_equality_true_ext_lib ctxt a1 a2 b1 b2 e1 e2 x1 x2 y i H); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply (ind p); auto; try (unfold proof_of_bseq; auto).
        apply (rule_function_equality_wf2 a1 a2 b1 b2 e1 e2 x1 x2 y i H); simpl; tcsp.

      * apply (ind p0); auto; try (unfold proof_of_bseq; auto).
        apply (rule_function_equality_wf2 a1 a2 b1 b2 e1 e2 x1 x2 y i H); simpl; tcsp.

  - apply (rule_isect_member_formation_true_ext_lib ctxt A B b e x z i H); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv xx; repndors; subst; tcsp.

      * apply (ind p); auto; try (unfold proof_of_bseq; auto).
        apply (rule_isect_member_formation_wf2 i z A B b e x H); simpl; tcsp.

      * apply (ind p0); auto; try (unfold proof_of_bseq; auto).
        apply (rule_isect_member_formation_wf2 i z A B b e x H); simpl; tcsp.

  - apply (rule_hypothesis_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_hypothesis_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_cut_true_ext_lib ctxt H B C t u x); simpl; tcsp.

    + unfold args_constraints; simpl; introv xx; repndors; subst; tcsp.

    + introv xx; repndors; subst; tcsp.

      * apply (ind p); auto; try (unfold proof_of_bseq; auto).
        apply (rule_cut_wf2 H B C t u x); simpl; tcsp.

      * apply (ind p0); auto; try (unfold proof_of_bseq; auto).
        apply (rule_cut_wf2 H B C t u x); simpl; tcsp.

  - apply (rule_cequiv_computation_true_ext_lib ctxt); simpl; tcsp; eauto 3 with slow.

  - apply (rule_cequiv_computation_aeq_true_ext_lib ctxt a b); simpl; tcsp; eauto 3 with slow.

  - apply (rule_cequiv_computation_atmost_true_ext_lib ctxt a b k); simpl; tcsp; eauto 3 with slow.

  - apply (rule_unfold_abstractions_true_ext_lib ctxt names a e H); simpl; tcsp.
    introv xx; repndors; subst; tcsp.
    apply (ind p); tcsp;
      try (unfold proof_of_bseq; auto);
      try (apply (rule_unfold_abstractions_wf2 ctxt names a e H); simpl; tcsp).

  - apply (rule_rev_unfold_abstractions_true_ext_lib ctxt names a e H); simpl; tcsp.
    introv xx; repndors; subst; tcsp.
    apply (ind p); tcsp;
      try (unfold proof_of_bseq; auto).
    apply (rule_rev_unfold_abstractions_wf2 ctxt names a e H); simpl; tcsp.

  - apply (rule_cequiv_subst_concl2_true_ext_lib ctxt H x C a b t e); allsimpl; tcsp.

    introv i; repndors; subst; allsimpl; tcsp.

    + apply (ind p0); auto; try (unfold proof_of_bseq; auto).
      apply (rule_cequiv_subst_concl2_wf2 H x C a b t e); simpl; tcsp.

    + apply (ind p); auto; try (unfold proof_of_bseq; auto).
      apply (rule_cequiv_subst_concl2_wf2 H x C a b t e); simpl; tcsp.

  - apply (rule_cequiv_subst_hyp_true_ext_lib ctxt H J x z C T a b t e); allsimpl; tcsp.

    introv i; repndors; subst; allsimpl; tcsp.

    + apply (ind p0); auto; try (unfold proof_of_bseq; auto).
      apply (rule_cequiv_subst_hyp_wf2 H J x z C T a b t e); simpl; tcsp.

    + apply (ind p); auto; try (unfold proof_of_bseq; auto).
      apply (rule_cequiv_subst_hyp_wf2 H J x z C T a b t e); simpl; tcsp.

  - apply (rule_cequiv_subst_hyp_true_ext_lib ctxt H J x z C T a b t e); allsimpl; tcsp.

    introv i; repndors; subst; allsimpl; tcsp.

    + apply (ind p0); auto; try (unfold proof_of_bseq; auto).
      apply (rule_cequiv_subst_hyp_wf2 H J x z C T a b t e); simpl; tcsp.

    + apply (ind p); auto; try (unfold proof_of_bseq; auto).
      apply (rule_cequiv_subst_hyp_wf2 H J x z C T a b t e); simpl; tcsp.

  - apply (rule_universe_equality_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_hypothesis_equality_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_maybe_hidden_hypothesis_equality_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_unhide_equality_true_ext_lib ctxt G J A C t1 t2 e x); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    apply (ind p); auto; try (unfold proof_of_bseq; auto).
    apply (rule_unhide_equality_wf2 G J A C t1 t2 e x); simpl; tcsp.

  - apply (rule_equality_equality_true_ext_lib ctxt H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

    introv e; repndors; subst; tcsp.

    + apply (ind p); auto; try (unfold proof_of_bseq; auto).
      apply (rule_equality_equality_wf2 H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

    + apply (ind p0); auto; try (unfold proof_of_bseq; auto).
      apply (rule_equality_equality_wf2 H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

    + apply (ind p1); auto; try (unfold proof_of_bseq; auto).
      apply (rule_equality_equality_wf2 H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

  - apply (rule_equality_equality_base_true_ext_lib ctxt H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

    introv e; repndors; subst; tcsp.

    + apply (ind p); auto; try (unfold proof_of_bseq; auto).
      apply (rule_equality_equality_base_wf2 H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

    + apply (ind p0); auto; try (unfold proof_of_bseq; auto).
      apply (rule_equality_equality_base_wf2 H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

    + apply (ind p1); auto; try (unfold proof_of_bseq; auto).
      apply (rule_equality_equality_base_wf2 H A B a1 a2 b1 b2 e1 e2 e3 i); simpl; tcsp.

  - apply (rule_integer_equality_true_ext_lib ctxt); simpl; tcsp.

  - apply (rule_introduction_true_ext_lib ctxt H C t e); simpl; tcsp.

    { unfold args_constraints; simpl; introv i; repndors; tcsp; subst; simpl; auto. }

    introv xx; repndors; subst; tcsp.

    apply (ind p); auto; try (unfold proof_of_bseq; auto).
    apply (rule_introduction_wf2 H C t e); simpl; tcsp; auto.
    eapply subvars_trans;[eauto|].
    apply subvars_hs_vars_hyps.

  - apply (rule_axiom_equality_true_ext_lib ctxt H e a b T); simpl; tcsp.

    introv xx; repndors; subst; tcsp.
    apply (ind p); auto; try (unfold proof_of_bseq; auto).

    apply (rule_axiom_equality_wf2 H e a b T); simpl; tcsp; auto.

  - apply (rule_thin_true_ext_lib ctxt G J A C t x); simpl; tcsp.

    introv xx; repndors; subst; tcsp.
    apply (ind p); auto; try (unfold proof_of_bseq; auto).

    apply (rule_thin_wf2 G J A C t x); simpl; tcsp; auto.

  - apply (rule_thin_true_ext_lib ctxt G J A C t x); simpl; tcsp.

    introv xx; repndors; subst; tcsp.
    apply (ind p); auto; try (unfold proof_of_bseq; auto).

    apply (rule_thin_wf2 G J A C t x); simpl; tcsp; auto.

  - apply (rule_apply_equality_true_ext_lib ctxt A B f1 f2 t1 t2 e1 e2 x H); simpl; tcsp.

    introv e; repndors; subst; tcsp.

      * apply (ind p); auto; try (unfold proof_of_bseq; auto).
        apply (rule_apply_equality_wf2 A B f1 f2 t1 t2 e1 e2 x H); simpl; tcsp.

      * apply (ind p0); auto; try (unfold proof_of_bseq; auto).
        apply (rule_apply_equality_wf2 A B f1 f2 t1 t2 e1 e2 x H); simpl; tcsp.

  - apply (rule_isect_elimination_true_ext_lib ctxt A B C a e ea f x0 x H J); simpl; tcsp.

    introv xx; repndors; subst; tcsp.

      * apply (ind p); auto; try (unfold proof_of_bseq; auto).
        apply (rule_isect_elimination_wf2 A B C a e ea f x0 x H J); simpl; tcsp.

      * apply (ind p0); auto; try (unfold proof_of_bseq; auto).
        apply (rule_isect_elimination_wf2 A B C a e ea f x0 x H J); simpl; tcsp.

  - apply (rule_isect_elimination2_true_ext_lib ctxt A B C a e ea f x0 y x H J); simpl; tcsp.

    introv xx; repndors; subst; tcsp.

      * apply (ind p); auto; try (unfold proof_of_bseq; auto).
        apply (rule_isect_elimination2_wf2 A B C a e ea f x0 y x H J); simpl; tcsp.

      * apply (ind p0); auto; try (unfold proof_of_bseq; auto).
        apply (rule_isect_elimination2_wf2 A B C a e ea f x0 y x H J); simpl; tcsp.

  - apply (rule_isect_member_equality_true_ext_lib ctxt A B t1 t2 e1 e2 x0 x i H); simpl; tcsp.

    introv xx; repndors; subst; tcsp.

      * apply (ind p); auto; try (unfold proof_of_bseq; auto).
        apply (rule_isect_member_equality_wf2 A B t1 t2 e1 e2 x0 x i H); simpl; tcsp.

      * apply (ind p0); auto; try (unfold proof_of_bseq; auto).
        apply (rule_isect_member_equality_wf2 A B t1 t2 e1 e2 x0 x i H); simpl; tcsp.

  - apply (rule_cumulativity_true_ext_lib ctxt H T e i j); simpl; tcsp.

    introv xx; repndors; subst; tcsp.

    apply (ind p); tcsp; try (unfold proof_of_bseq; auto).

  - apply (rule_equality_symmetry_true_ext_lib ctxt H a b T e); simpl; tcsp.

    introv xx; repndors; subst; tcsp.

    apply (ind p); auto; try (unfold proof_of_bseq; auto).
    apply (rule_equality_symmetry_wf2 H a b T e); simpl; tcsp.

  - apply (rule_equality_transitivity_true_ext_lib ctxt H a b c0 T e1 e2); simpl; tcsp.

    introv xx; repndors; subst; tcsp.

      * apply (ind p); auto; try (unfold proof_of_bseq; auto).
        apply (rule_equality_transitivity_wf2 H a b c0 T e1 e2); simpl; tcsp.

      * apply (ind p0); auto; try (unfold proof_of_bseq; auto).
        apply (rule_equality_transitivity_wf2 H a b c0 T e1 e2); simpl; tcsp.

  - apply (rule_cequiv_trans_true_ext_lib ctxt H a b c0 e1 e2); simpl; tcsp.

    introv xx; repndors; subst; tcsp.

      * apply (ind p); auto; try (unfold proof_of_bseq; auto).
        apply (rule_cequiv_trans_wf2 H a b c0 e1 e2); simpl; tcsp.

      * apply (ind p0); auto; try (unfold proof_of_bseq; auto).
        apply (rule_cequiv_trans_wf2 H a b c0 e1 e2); simpl; tcsp.

  - apply (rule_approx_refl_true_ext_lib ctxt H a); simpl; tcsp.

  - apply (rule_cequiv_refl_true_ext_lib ctxt H a); simpl; tcsp.

  - apply (rule_cequiv_alpha_eq_true_ext_lib ctxt H a b); simpl; tcsp.

  - apply (rule_cequiv_approx2_true_ext_lib ctxt H a b e1 e2); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply (ind p); auto; try (unfold proof_of_bseq; auto).

    + apply (ind p0); auto; try (unfold proof_of_bseq; auto).
      apply (rule_cequiv_approx2_wf2 a b e1 e2 H); simpl; tcsp.

  - apply (rule_approx_eq2_true_ext_lib ctxt a1 a2 b1 b2 e1 e2 i H); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply (ind p); auto; try (unfold proof_of_bseq; auto).
      apply (rule_approx_eq2_wf2 a1 a2 b1 b2 e1 e2 i H); simpl; tcsp.

    + apply (ind p0); auto; try (unfold proof_of_bseq; auto).
      apply (rule_approx_eq2_wf2 a1 a2 b1 b2 e1 e2 i H); simpl; tcsp.

  - apply (rule_cequiv_eq2_true_ext_lib ctxt a1 a2 b1 b2 e1 e2 i H); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply (ind p); auto; try (unfold proof_of_bseq; auto).
      apply (rule_cequiv_eq2_wf2 a1 a2 b1 b2 e1 e2 i H); simpl; tcsp.

    + apply (ind p0); auto; try (unfold proof_of_bseq; auto).
      apply (rule_cequiv_eq2_wf2 a1 a2 b1 b2 e1 e2 i H); simpl; tcsp.

  (*
  - apply (rule_bottom_diverges_true3 lib x hs js); simpl; tcsp.
*)

(*  - apply (rule_equal_in_base2_true3 lib H a b e F); simpl; tcsp.

    introv xx; repndors; subst; tcsp.
    unfold rule_equal_in_base2_rest in xx; apply in_mapin in xx; exrepnd; subst.
    pose proof (ihs a0 i) as hh; clear ihs.
    repeat (autodimp hh hyp).
    pose proof (rule_equal_in_base2_wf2 H a b e F) as w.
    apply w; simpl; tcsp.
    right.
    apply in_mapin; eauto.*)

(*  - apply (rule_approx_member_eq2_true3 lib a b e); simpl; tcsp.
    introv xx; repndors; subst; tcsp.
    apply ih.
    apply (rule_approx_member_eq2_wf2 a b e H); simpl; tcsp.*)

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



(* ===========================================================

  Nuprl state, i.e., a RigidLibrary and a list of lemmas currently being proved.

  ============================================================ *)

Definition term2pre_baresequent {o} (t : @NTerm o) : pre_baresequent :=
  mk_pre_bseq [] (pre_concl_ext t).

Definition pre_proof2hyps {o} (p : @pre_proof o) : barehypotheses :=
  pre_hyps (pre_proof2bseq p).

Definition pre_concl2some_type {o} (c : @pre_conclusion o) : NTerm :=
  match c with
  | pre_concl_ext t => t
  | pre_concl_typ t => t
  end.

Definition pre_proof2type {o} (p : @pre_proof o) : NTerm :=
  pre_concl2some_type (pre_concl (pre_proof2bseq p)).

Record pre_proof_seq {o} :=
  MkPreProofSeq
    {
      pre_proof_seq_name  : LemmaName;
      pre_proof_seq_proof : @pre_proof o;
      (*pre_proof_seq_nhyps : null (pre_proof2hyps pre_proof_seq_proof);*)
      (*pre_proof_seq_prog  : isprog (pre_proof2type pre_proof_seq_proof);*)
    }.

Arguments MkPreProofSeq [o] _ _ (*_*) (*_*).

Arguments pre_proof_seq_name  [o] _.
Arguments pre_proof_seq_proof [o] _.


Definition pre_proofs {o} := list (@pre_proof_seq o).

Record SoftLibrary {o} :=
  MkSoftLibrary
    {
      SoftLibrary_lib        :> @RigidLibrary o;
      SoftLibrary_unfinished : @pre_proofs o;
    }.

Arguments MkSoftLibrary [o] _ _.



(* ===========================================================

  Commands to manipulate the state

  ============================================================ *)

Definition address := list nat.

Record Abstraction {o} :=
  MkAbstraction
    {
      abs_opabs   : opabs;
      abs_vars    : list sovar_sig;
      abs_rhs     : @SOTerm o;
      abs_correct : correct_abs abs_opabs abs_vars abs_rhs;
    }.
Arguments MkAbstraction [o] _ _ _ _.

Inductive command {o} :=
(* add a definition at the head *)
| COM_add_def (abs : @Abstraction o)
(* tries to complete a proof if it has no holes *)
| COM_finish_proof (name : LemmaName)
(* do a proof step *)
| COM_update_proof (name : LemmaName) (addr : address) (step : @proof_step o)
(* start a new proof *)
| COM_start_proof (name : LemmaName) (C : @NTerm o) (*(isp : isprog C)*)
(* print holes *)
| COM_find_holes (name : LemmaName)
(* print a specific hole *)
| COM_find_sequent_at_address (name : LemmaName) (addr : address)
(* rename an abstraction *)
| COM_rename (o1 o2 : opname).

(*(* focuses to a node in a proof *)
| COM_focus_proof (name : LemmaName) (addr : address)*)

Definition commands {o} := list (@command o).

Lemma in_conclusions_extend_proof_context {o} :
  forall (ctxt  : @ProofContext o)
         (entry : RigidLibraryEntry)
         (c     : named_concl)
         (i     : LIn c (PC_conclusions ctxt)),
    LIn c (PC_conclusions (extend_proof_context ctxt entry)).
Proof.
  introv i.
  destruct entry; simpl in *; auto.
Qed.

Definition RigidLibraryEntry2opabs {o} (e : @RigidLibraryEntry o) : opabs :=
  match e with
  | RigidLibraryEntry_abs e => opabs_of_lib_entry e
  | RigidLibraryEntry_proof name prf wf => opname2opabs name
  end.

Definition entry_in_lib {o} (e : @RigidLibraryEntry o) (l : @library o) :=
  in_lib (RigidLibraryEntry2opabs e) l.

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
  forall (ctxt : @ProofContext o) (e : RigidLibraryEntry) a b,
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
  forall (ctxt : @ProofContext o) (e : RigidLibraryEntry) a b n,
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

Lemma forallb_forall_lin :
  forall {A}(f : A -> bool) (l : list A),
    forallb f l = true <-> (forall x, LIn x l -> f x = true).
Proof.
  induction l; introv; simpl in *; split; intro h; tcsp.

  - allrw andb_true; repnd.
    rewrite IHl in h.
    introv i; repndors; subst; tcsp.

  - rewrite andb_true; rewrite IHl.
    dands; tcsp.
Qed.

Lemma unfold_abs_implies_in_lib {o} :
  forall lib a bs (u : @NTerm o),
    unfold_abs lib a bs = Some u
    -> in_lib a lib.
Proof.
  induction lib; introv h; simpl in *; ginv.
  remember (unfold_abs_entry a a0 bs) as ua; symmetry in Hequa; destruct ua; ginv.

  - unfold unfold_abs_entry in Hequa.
    destruct a; boolvar; ginv.

    unfold in_lib; simpl.
    eexists; dands; eauto; simpl; eauto 3 with slow.

  - apply IHlib in h.
    unfold in_lib in *; exrepnd; simpl.
    exists e; dands; tcsp.
Qed.

Lemma implies_abstraction_can_be_unfold_extend_proof_context_true {o} :
  forall (ctxt : @ProofContext o) entry abs (t : @NTerm o),
    abstractions_can_be_unfolded ctxt abs t = true
    -> abstractions_can_be_unfolded (extend_proof_context ctxt entry) abs t = true.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv h; simpl in *; auto.

  Case "oterm".

  allrw andb_true_iff; repnd.
  allrw @forallb_forall_lin.
  dands.

  - introv i.
    destruct x as [l t]; simpl in *.
    applydup h0 in i; simpl in *.
    eapply ind;eauto.

  - unfold unfoldable in *; simpl in *.
    dopid op as [can|ncan|exc|a] SCase; simpl in *; auto.
    boolvar; auto.

    remember (unfold_abs ctxt a bs) as ua; symmetry in Hequa; destruct ua; ginv.

    destruct entry; simpl in *.

    + remember (unfold_abs_entry e a bs) as q; symmetry in Heqq; destruct q; auto.
      allrw; auto.

    + boolvar; auto; allrw; auto.
Qed.

Lemma implies_lib_extends_extend_proof_context {o} :
  forall (ctxt : @ProofContext o) e,
    !entry_in_lib e ctxt
    -> lib_extends (extend_proof_context ctxt e) ctxt.
Proof.
  introv ni i.
  unfold entry_in_lib in ni; simpl in ni.
  destruct e; simpl in *.

  - right; dands; auto.
    intro m; destruct ni; eapply entry_in_library_implies_in_lib; eauto.

  - right; dands; auto.
    intro m; destruct ni.
    eapply entry_in_library_implies_in_lib in m;[|eauto]; tcsp.
Qed.
Hint Resolve implies_lib_extends_extend_proof_context : slow.

Lemma eq_unfold_abstractions_extend_proof_context {o} :
  forall (ctxt : @ProofContext o) entry abs a,
    !entry_in_lib entry ctxt
    -> abstractions_can_be_unfolded ctxt abs a = true
    -> unfold_abstractions ctxt abs a
       = unfold_abstractions (extend_proof_context ctxt entry) abs a.
Proof.
  nterm_ind a as [v|f|op bs ind] Case; introv ni unf; simpl in *; tcsp.

  Case "oterm".

  allrw andb_true; repnd.
  allrw @forallb_forall_lin.

  match goal with
  | [ |- maybe_unfold _ _ ?x = maybe_unfold _ _ ?y ] => assert (x = y) as q
  end.

  {
    f_equal.
    apply eq_maps.
    introv i.
    applydup unf0 in i.
    destruct x as [l t]; simpl in *.
    f_equal.
    eapply ind; eauto.
  }

  rewrite <- q; clear q.

  unfold unfoldable in unf; simpl in unf.
  unfold maybe_unfold; simpl.
  dopid op as [can|ncan|exc|a] SCase; simpl in *; auto.
  boolvar; auto.

  remember (unfold_abs ctxt a bs) as ua; symmetry in Hequa; destruct ua; ginv.
  apply unfold_abs_implies_find_entry in Hequa; exrepnd; subst.

  erewrite find_entry_implies_unfold_abs;
    [|rewrite find_entry_map_unfold_abstractions_b_eq; eauto].

  erewrite find_entry_implies_unfold_abs;
    [|rewrite find_entry_map_unfold_abstractions_b_eq];
    [reflexivity|].

  eapply lib_extends_preserves_find_entry;[|eauto].
  apply implies_lib_extends_extend_proof_context; auto.
Defined.

Lemma eq_pre_rule_unfold_abstractions_hyp_extend_proof_context {o} :
  forall (ctxt : @ProofContext o) entry abs a H,
    !entry_in_lib entry ctxt
    -> all_abstractions_can_be_unfolded ctxt abs a
    -> pre_rule_unfold_abstractions_hyp ctxt abs a H
       = pre_rule_unfold_abstractions_hyp (extend_proof_context ctxt entry) abs a H.
Proof.
  introv bi unf.
  unfold pre_rule_unfold_abstractions_hyp.
  f_equal; f_equal.
  apply eq_unfold_abstractions_extend_proof_context; auto.
Defined.

Lemma eq_pre_rule_rev_unfold_abstractions_hyp_extend_proof_context {o} :
  forall (ctxt : @ProofContext o) entry abs a H,
    !entry_in_lib entry ctxt
    -> all_abstractions_can_be_unfolded ctxt abs a
    -> pre_rule_unfold_abstractions_hyp (extend_proof_context ctxt entry) abs a H
       = pre_rule_unfold_abstractions_hyp ctxt abs a H.
Proof.
  introv bi unf.
  unfold pre_rule_unfold_abstractions_hyp.
  f_equal; f_equal.
  symmetry.
  apply eq_unfold_abstractions_extend_proof_context; auto.
Defined.

(*Fixpoint pre_proof_cons {o}
         {ctxt  : @ProofContext o}
         (entry : RigidLibraryEntry)
         (ni    : !entry_in_lib entry ctxt)
         {s     : pre_baresequent}
         (p     : pre_proof s)
  : pre_proof s :=
  match p with
  | pre_proof_from_ctxt c H => pre_proof_from_ctxt c H

  | pre_proof_hole s => pre_proof_hole s

  | pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH prf1' prf2'

  | pre_proof_isect_member_formation A x B z i H nizH prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_isect_member_formation A x B z i H nizH prf1' prf2'

  | pre_proof_approx_refl a H => pre_proof_approx_refl a H

  | pre_proof_cequiv_refl a H => pre_proof_cequiv_refl a H

  | pre_proof_cequiv_alpha_eq a b aeq H => pre_proof_cequiv_alpha_eq a b aeq H

  | pre_proof_cequiv_approx a b H prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_cequiv_approx a b H prf1' prf2'

  | pre_proof_approx_eq a1 a2 b1 b2 i H prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_approx_eq a1 a2 b1 b2 i H prf1' prf2'

  | pre_proof_cequiv_eq a1 a2 b1 b2 i H prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_cequiv_eq a1 a2 b1 b2 i H prf1' prf2'

  | pre_proof_cut B C x H wfB covB nixH prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_cut B C x H wfB covB nixH prf1' prf2'

  | pre_proof_hypothesis x A G J => pre_proof_hypothesis x A G J

  | pre_proof_cequiv_subst_concl C x a b H wfa wfb cova covb prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_cequiv_subst_concl C x a b H wfa wfb cova covb prf1' prf2'

  | pre_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb prf1' prf2'

  | pre_proof_cequiv_computation lib a b H r =>
    pre_proof_cequiv_computation
      lib a b H
      (extend_proof_context_preserves_reduces_to lib entry a b ni r)

  | pre_proof_cequiv_computation_aeq _ a b c H r aeq =>
    pre_proof_cequiv_computation_aeq
      _ a b c H
      (extend_proof_context_preserves_reduces_to ctxt entry a b ni r)
      aeq

  | pre_proof_cequiv_computation_atmost _ a b n H r =>
    pre_proof_cequiv_computation_atmost
      _ a b n H
      (extend_proof_context_preserves_reduces_in_atmost_k_steps ctxt entry a b n ni r)

  | pre_proof_unfold_abstractions _ abs a H unf prf =>
    let prf' := pre_proof_cons entry ni prf in
    pre_proof_unfold_abstractions
      _ abs a H
      (implies_abstraction_can_be_unfold_extend_proof_context_true ctxt entry abs a unf)
      (eq_rect (* -- QUESTION: IS THIS [eq_rect] GOING TO BE A PROBLEM?? -- *)
         _
         _
         prf'
         _
         (eq_pre_rule_unfold_abstractions_hyp_extend_proof_context
            ctxt entry abs a H ni unf))

  | pre_proof_rev_unfold_abstractions _ abs a H wfa cova unf prf =>
    let prf' := pre_proof_cons entry ni prf in
    (eq_rect (* -- QUESTION: IS THIS [eq_rect] GOING TO BE A PROBLEM?? -- *)
         _
         _
         (pre_proof_rev_unfold_abstractions
            _ abs a H wfa cova
            (implies_abstraction_can_be_unfold_extend_proof_context_true ctxt entry abs a unf)
            prf')
         _
         (eq_pre_rule_rev_unfold_abstractions_hyp_extend_proof_context
            ctxt entry abs a H ni unf))

  | pre_proof_universe_equality i j H ltij => pre_proof_universe_equality i j H ltij

  | pre_proof_hypothesis_equality x A G J => pre_proof_hypothesis_equality x A G J

  | pre_proof_maybe_hidden_hypothesis_equality x A G J b => pre_proof_maybe_hidden_hypothesis_equality x A G J b

  | pre_proof_unhide_equality x A t1 t2 C G J prf =>
    let prf' := pre_proof_cons entry ni prf in
    pre_proof_unhide_equality x A t1 t2 C G J prf'

  | pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    let prf3' := pre_proof_cons entry ni prf3 in
    pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1' prf2' prf3'

  | pre_proof_integer_equality n H => pre_proof_integer_equality n H

  | pre_proof_introduction t C H wft covt nout prf =>
    let prf' := pre_proof_cons entry ni prf in
    pre_proof_introduction t C H wft covt nout prf'

  | pre_proof_axiom_equality a b T H prf =>
    let prf' := pre_proof_cons entry ni prf in
    pre_proof_axiom_equality a b T H prf'

  | pre_proof_thin G J A C x nixJ nixC prf =>
    let prf' := pre_proof_cons entry ni prf in
    pre_proof_thin G J A C x nixJ nixC prf'

  | pre_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH prf1' prf2'

  | pre_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA prf1' prf2'

  | pre_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf prf1' prf2'

  | pre_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1' prf2'

  | pre_proof_isect_member_equality H t1 t2 A x B z i nizH prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_isect_member_equality H t1 t2 A x B z i nizH prf1' prf2'

  | pre_proof_cumulativity H T i j lij prf1 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    pre_proof_cumulativity H T i j lij prf1'

  | pre_proof_equality_symmetry H a b T prf1 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    pre_proof_equality_symmetry H a b T prf1'

  | pre_proof_equality_transitivity H a b c T wfc covc prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_equality_transitivity H a b c T wfc covc prf1' prf2'

  | pre_proof_cequiv_transitivity H a b c wfc covc prf1 prf2 =>
    let prf1' := pre_proof_cons entry ni prf1 in
    let prf2' := pre_proof_cons entry ni prf2 in
    pre_proof_cequiv_transitivity H a b c wfc covc prf1' prf2'
  end.*)

(*Definition pre_proof_seq_cons {o}
           {ctxt  : @ProofContext o}
           (entry : RigidLibraryEntry)
           (ni    : !entry_in_lib entry ctxt)
           (pps   : pre_proof_seq ctxt)
  : pre_proof_seq (extend_proof_context ctxt entry) :=
  match pps with
  | MkPreProofSeq name C isp prf => MkPreProofSeq name C isp (pre_proof_cons entry ni prf)
  end.*)

(*Definition pre_proofs_cons {o}
           {ctxt  : @ProofContext o}
           (entry : RigidLibraryEntry)
           (ni    : !entry_in_lib entry ctxt)
           (l     : pre_proofs ctxt)
  : pre_proofs (extend_proof_context ctxt entry) :=
  map (pre_proof_seq_cons entry ni) l.*)

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
        { destruct k; eexists; eexists; eauto. }
Defined.

Lemma entry_in_lib_dec {o} :
  forall (entry : @RigidLibraryEntry o)
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
| added_definition (op : opabs)

| started_proof (name : LemmaName)

| renamed

| could_not_apply_base_equality_rule
| applied_base_equality_rule

| could_not_apply_base_closed_rule_terms_differ (a b : @NTerm o)
| could_not_apply_base_closed_rule_not_an_equality (c : @pre_conclusion o)
| could_not_apply_base_closed_rule_non_empty_hypotheses (H : @bhyps o)
| applied_base_closed_rule

| could_not_apply_base_closed2_rule_terms_differ (a b : @NTerm o)
| could_not_apply_base_closed2_rule_not_an_equality (c : @pre_conclusion o)
| could_not_apply_base_closed2_rule_non_empty_hypotheses (H : @bhyps o)
| applied_base_closed2_rule

| could_not_apply_int_equality_rule
| applied_int_equality_rule

| could_not_apply_isect_eq_rule_not_isects
| could_not_apply_isect_eq_rule_type_not_universe
| could_not_apply_isect_eq_rule_not_equality
| could_not_apply_isect_eq_rule
| applied_isect_eq_rule

| could_not_apply_function_equality_rule_not_functions
| could_not_apply_function_equality_rule_type_not_universe
| could_not_apply_function_equality_rule_not_equality
| could_not_apply_function_equality_rule
| applied_function_equality_rule

| could_not_apply_universe_eq_rule_not_equal_universes (i j : nat)
| could_not_apply_universe_eq_rule_not_less_than_universe (i j : nat)
| could_not_apply_universe_eq_rule
| applied_universe_eq_rule

| could_not_apply_isect_member_formation_rule_not_isect
| could_not_apply_isect_member_formation_rule
| applied_isect_member_formation_rule

| could_not_apply_cequiv_computation_atmost_rule_not_cequiv
| could_not_apply_cequiv_computation_atmost_rule
| applied_cequiv_computation_atmost_rule

| could_not_apply_cequiv_computation_rule_terms_not_equal (a x b : @NTerm o)
| could_not_apply_cequiv_computation_rule_not_cequiv
| could_not_apply_cequiv_computation_rule
| applied_cequiv_computation_rule

| could_not_apply_cequiv_computation_aeq_rule_terms_not_equal (a x b : @NTerm o)
| could_not_apply_cequiv_computation_aeq_rule_not_cequiv
| could_not_apply_cequiv_computation_aeq_rule
| applied_cequiv_computation_aeq_rule

| could_not_apply_unfold_abstractions_rule_not_all_unfoldable
| could_not_apply_unfold_abstractions_rule
| applied_unfold_abstractions_rule

| could_not_apply_rev_unfold_abstractions_rule_not_all_unfoldable
| could_not_apply_rev_unfold_abstractions_rule
| applied_rev_unfold_abstractions_rule

| could_not_apply_cequiv_subst_concl_rule_not_subst (x : NVar) (a b c d e : @NTerm o)
| could_not_apply_cequiv_subst_concl_rule
| applied_cequiv_subst_concl_rule

| could_not_apply_cequiv_subst_hyp_rule_not_subst
| could_not_apply_cequiv_subst_hyp_rule
| applied_cequiv_subst_hyp_rule

| could_not_apply_hypothesis_rule_because_different_types (A B : @NTerm o)
| could_not_apply_hypothesis_rule_because_couldnt_find_hypothesis
| could_not_apply_hypothesis_rule
| applied_hypothesis_rule

| could_not_apply_hypothesis_equality_rule_terms_dont_match (a b : @NTerm o)
| could_not_apply_hypothesis_equality_rule_not_an_equality (c : @pre_conclusion o)
| could_not_apply_hypothesis_equality_rule_couldnt_find_hypothesis (s : @pre_baresequent o)
| could_not_apply_hypothesis_equality_rule_variables_dont_match (v1 v2 : NVar)
| could_not_apply_hypothesis_equality_rule
| applied_hypothesis_equality_rule

| could_not_apply_maybe_hidden_hypothesis_equality_rule_terms_dont_match (a b : @NTerm o)
| could_not_apply_maybe_hidden_hypothesis_equality_rule_not_an_equality (c : @pre_conclusion o)
| could_not_apply_maybe_hidden_hypothesis_equality_rule_couldnt_find_hypothesis (s : @pre_baresequent o)
| could_not_apply_maybe_hidden_hypothesis_equality_rule_variables_dont_match (v1 v2 : NVar)
| could_not_apply_maybe_hidden_hypothesis_equality_rule
| applied_maybe_hidden_hypothesis_equality_rule

| could_not_apply_lemma_rule
| applied_lemma_rule

| could_not_apply_lemma_with_extract_rule_named_concl_not_found
| could_not_apply_lemma_with_extract_rule_not_alpha_eq (a b : @NTerm o)
| could_not_apply_lemma_with_extract_rule_members_not_equal (a b : @NTerm o)
| could_not_apply_lemma_with_extract_rule
| applied_lemma_with_extract_rule

| could_not_apply_apply_equality_rule
| applied_apply_equality_rule

| could_not_apply_isect_elimination_rule
| applied_isect_elimination_rule

| could_not_apply_isect_elimination2_rule_variables_not_different1 (a b : NVar)
| could_not_apply_isect_elimination2_rule_variables_not_different2 (a b : NVar)
| could_not_apply_isect_elimination2_rule_variables_not_different3 (a b : NVar)
| could_not_apply_isect_elimination2_rule_variable_in_hypotheses1 (a : NVar) (l : list NVar)
| could_not_apply_isect_elimination2_rule_variable_in_hypotheses2 (a : NVar) (l : list NVar)
| could_not_apply_isect_elimination2_rule_variable_in_hypotheses3 (a : NVar) (l : list NVar)
| could_not_apply_isect_elimination2_rule_variable_in_hypotheses4 (a : NVar) (l : list NVar)
| could_not_apply_isect_elimination2_rule_not_covered (a : @NTerm o) (l : list NVar)
| could_not_apply_isect_elimination2_rule_not_well_formed (a : @NTerm o)
| could_not_apply_isect_elimination2_rule_hypothesis_not_found (a : NVar) (l : list NVar)
| could_not_apply_isect_elimination2_rule
| applied_isect_elimination2_rule

| could_not_apply_isect_member_equality_rule
| applied_isect_member_equality_rule

| could_not_apply_cumulativity_rule
| applied_cumulativity_rule

| could_not_apply_unhide_equality_rule
| applied_unhide_equality_rule

| could_not_apply_equality_equality_rule
| applied_equality_equality_rule

| could_not_apply_equality_equality_base_rule
| applied_equality_equality_base_rule

| could_not_apply_introduction_rule
| applied_introduction_rule

| could_not_apply_integer_equality_rule
| applied_integer_equality_rule

| could_not_apply_cut_rule
| applied_cut_rule

| could_not_apply_axiom_equality_rule
| applied_axiom_equality_rule

| could_not_apply_thin_rule
| applied_thin_rule

| could_not_apply_equality_symmetry_rule
| applied_equality_symmetry_rule

| could_not_apply_equality_transitivity_rule
| applied_equality_transitivity_rule

| could_not_apply_cequiv_transitivity_rule
| applied_cequiv_transitivity_rule

| could_not_apply_approx_refl_rule
| applied_approx_refl_rule

| could_not_apply_cequiv_refl_rule_terms_dont_match (a b : @NTerm o)
| could_not_apply_cequiv_refl_rule_not_a_cequiv (c : @pre_conclusion o)
| applied_cequiv_refl_rule

| could_not_apply_cequiv_alpha_eq_rule_terms_dont_match (a b : @NTerm o)
| could_not_apply_cequiv_alpha_eq_rule_not_a_cequiv (c : @pre_conclusion o)
| applied_cequiv_alpha_eq_rule

| could_not_apply_cequiv_approx_rule
| applied_cequiv_approx_rule

| could_not_apply_approx_eq_rule
| applied_approx_eq_rule

| could_not_apply_cequiv_eq_rule
| applied_cequiv_eq_rule

| could_not_apply_update_because_wrong_address
| could_not_apply_update_because_bad_address (oaddr addr : address)
| could_not_apply_update_because_no_hole_at_address
| could_not_apply_update_because_could_not_find_lemma

| found_holes (holes : @Holes o)
| could_not_find_holes_because_could_not_find_lemma (name : LemmaName) (names : LemmaNames)

| found_sequent_at_address (addr : address) (s : @pre_baresequent o)
| could_not_find_sequent_at_address (addr : address)
| could_not_find_sequent_because_could_not_find_lemma

| finished_proof (name : LemmaName)
| could_not_finish_proof
| could_not_finish_proof_because_entry_exists_in_lib
| could_not_finish_proof_because_could_not_find_lemma.

Definition DEBUG_MSGS {o} := list (@DEBUG_MSG o).

Record UpdRes {o} :=
  MkUpdRes
    {
      upd_res_state :> @SoftLibrary o;
      upd_res_trace : @DEBUG_MSGS o;
    }.
Arguments MkUpdRes [o] _ _.


Definition SoftLibrary_add_def {o}
           (state   : @SoftLibrary o)
           (opabs   : opabs)
           (vars    : list sovar_sig)
           (rhs     : SOTerm)
           (correct : correct_abs opabs vars rhs) : UpdRes :=
  match state with
  | MkSoftLibrary L unfinished =>
    let entry := RigidLibraryEntry_abs (lib_abs opabs vars rhs correct) in

    match entry_in_lib_dec entry (RigidLibrary2lib L) with
    | inl p => MkUpdRes state [could_not_add_definition_because_definition_already_in_library]
    | inr p =>
      MkUpdRes
        (MkSoftLibrary
           (entry :: L)
           ((*pre_proofs_cons entry p*) unfinished))
        [added_definition opabs]
    end
  end.

Fixpoint find_unfinished_in_pre_proofs {o}
         (l : @pre_proofs o)
         (n : LemmaName)
  : option (pre_proof_seq) * pre_proofs :=
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
  forall (l  : @pre_proofs o)
         (n  : LemmaName)
         (p  : pre_proof_seq)
         (ps : pre_proofs),
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

Record ExtractProof {o} :=
  MkExtractProof
    {
      extract_proof_extract : @NTerm o;
      extract_proof_proof   : proof;
      extract_proof_valid   : valid_pre_extract (proof2hyps extract_proof_proof) extract_proof_extract;
      extract_proof_seq     : extract_proof_extract = proof2extract extract_proof_proof
    }.

Arguments MkExtractProof [o] _ _ _ _.

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

Lemma valid_pre_extract_mk_abs_opname2opabs2 {o} :
  forall name (s : @pre_baresequent o), valid_pre_extract (pre_hyps s) (mk_abs (opname2opabs name) []).
Proof.
  introv; unfold valid_pre_extract; dands; eauto 2 with slow;
    try (complete (compute;auto));
    try (complete (unfold covered; simpl; auto)).
Qed.

(*(* Why can't I define these? *)
Definition finish_proof_from_context {o}
           (c : @named_concl o)
           (H : bhyps)
  : ExtractProof (named_concl2pre_bseq H c).
Proof.
  destruct c as [name T]; simpl in *.
  eexists (@mk_abs o (opname2opabs name) [])
          (proof_node (proof_step_lemma name) (named_concl2bseq H (MkNamedConcl name T)) []).
  { apply valid_pre_extract_mk_abs_opname2opabs. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_isect_eq {o}
           (a1 a2 b1 b2 : @NTerm o)
           (x1 x2 y : NVar)
           (i : nat)
           (H : bhyps)
           (ni : NVin y (vars_hyps H))
           (p1 : ExtractProof (pre_rule_isect_equality_hyp1 a1 a2 i H))
           (p2 : ExtractProof (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H))
  : ExtractProof (pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_isect_equality y)
                      (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
                      [v1, v2]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

Lemma valid_pre_extract_snoc_mk_hhyp_implies {o} :
  forall (H : @bhyps o) (z : NVar) (A e : NTerm),
    valid_pre_extract (snoc H (mk_hhyp z A)) e
    -> valid_pre_extract H e.
Proof.
  introv val.
  unfold valid_pre_extract in *; simpl in *.
  allrw @nh_vars_hyps_snoc; simpl in *; auto.
Qed.

(*Definition finish_proof_isect_member_formation {o}
           (A : NTerm)
           (x : NVar)
           (B : @NTerm o)
           (z : NVar)
           (i : nat)
           (H : bhyps)
           (ni : NVin z (vars_hyps H))
           (p1 : ExtractProof (pre_rule_isect_member_formation_hyp1 z A x B H))
           (p2 : ExtractProof (pre_rule_isect_member_formation_hyp2 A i H))
  : ExtractProof (pre_rule_isect_member_formation_concl A x B H).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists e1
          (proof_node (proof_step_isect_member_formation z i)
                      (rule_isect_member_formation_concl A x B e1 H)
                      [v1, v2]).
  { eapply valid_pre_extract_snoc_mk_hhyp_implies; eauto. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_approx_refl {o}
           (a : @NTerm o)
           (H : bhyps)
  : ExtractProof (pre_rule_approx_refl_concl a H).
Proof.
  introv.
  eexists (@mk_axiom o)
          (proof_node (proof_step_approx_refl)
                      (rule_approx_refl_concl a H)
                      []).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cequiv_refl {o}
           (a : @NTerm o)
           (H : bhyps)
  : ExtractProof (pre_rule_cequiv_refl_concl a H).
Proof.
  introv.
  eexists (@mk_axiom o)
          (proof_node (proof_step_cequiv_refl)
                      (rule_cequiv_refl_concl H a)
                      []).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cequiv_alpha_eq {o}
           (a b : @NTerm o)
           (H : bhyps)
           (aeq : alpha_eq a b)
  : ExtractProof (pre_rule_cequiv_alpha_eq_concl a b H).
Proof.
  introv.
  eexists (@mk_axiom o)
          (proof_node (proof_step_cequiv_alpha_eq)
                      (rule_cequiv_alpha_eq_concl H a b)
                      []).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cequiv_approx {o}
           (a b : @NTerm o)
           (H : bhyps)
           (p1 : ExtractProof (pre_rule_cequiv_approx_hyp a b H))
           (p2 : ExtractProof (pre_rule_cequiv_approx_hyp b a H))
  : ExtractProof (pre_rule_cequiv_approx_concl a b H).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_cequiv_approx)
                      (rule_cequiv_approx_concl a b H)
                      [v1, v2]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_approx_eq {o}
           (a1 a2 b1 b2 : @NTerm o)
           (i : nat)
           (H : bhyps)
           (p1 : ExtractProof (pre_rule_eq_base_hyp a1 a2 H))
           (p2 : ExtractProof (pre_rule_eq_base_hyp b1 b2 H))
  : ExtractProof (pre_rule_approx_eq_concl a1 a2 b1 b2 i H).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_approx_eq)
                      (rule_approx_eq_concl a1 a2 b1 b2 i H)
                      [v1, v2]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cequiv_eq {o}
           (a1 a2 b1 b2 : @NTerm o)
           (i : nat)
           (H : bhyps)
           (p1 : ExtractProof (pre_rule_eq_base_hyp a1 a2 H))
           (p2 : ExtractProof (pre_rule_eq_base_hyp b1 b2 H))
  : ExtractProof (pre_rule_cequiv_eq_concl a1 a2 b1 b2 i H).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_cequiv_eq)
                      (rule_cequiv_eq_concl a1 a2 b1 b2 i H)
                      [v1, v2]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

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

(*Definition finish_proof_cut {o}
           (B C : @NTerm o)
           (x : NVar)
           (H : bhyps)
           (wfB : wf_term B)
           (covB : covered B (vars_hyps H))
           (nixH : NVin x (vars_hyps H))
           (p1 : ExtractProof (pre_rule_cut_hyp1 H B))
           (p2 : ExtractProof (pre_rule_cut_hyp2 H x B C))
  : ExtractProof (pre_rule_cut_concl H C).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists (subst e2 x e1)
          (proof_node (proof_step_cut x B)
                      (rule_cut_concl H C e2 x e1)
                      [v1, v2]).
  { simpl; eapply implies_valid_pre_extract_subst; eauto. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_hypothesis {o}
           (x : NVar)
           (A : @NTerm o)
           (G J : bhyps)
  : ExtractProof (pre_rule_hypothesis_concl G J A x).
Proof.
  introv.
  eexists (@mk_var o x)
          (proof_node (proof_step_hypothesis x)
                      (rule_hypothesis_concl G J A x)
                      []).
  { unfold valid_pre_extract; dands; simpl; eauto 2 with slow.
    apply covered_var; rw @nh_vars_hyps_app; rw @nh_vars_hyps_snoc; simpl.
    rw in_app_iff; rw in_snoc; tcsp. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cequiv_subst_concl {o}
           (C : NTerm)
           (x : NVar)
           (a b : @NTerm o)
           (H : bhyps)
           (wfa : wf_term a)
           (wfb : wf_term b)
           (cova : covered a (vars_hyps H))
           (covb : covered b (vars_hyps H))
           (p1 : ExtractProof (pre_rule_cequiv_subst_hyp2 H a b))
           (p2 : ExtractProof (pre_rule_cequiv_subst_hyp1 H x C b))
  : ExtractProof (pre_rule_cequiv_subst_hyp1 H x C a).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists e2
          (proof_node (proof_step_cequiv_subst_concl x C a b)
                      (rule_cequiv_subst_hyp1 H x C a e2)
                      [v1,v2]); auto.
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cequiv_subst_hyp {o}
           (H : bhyps)
           (z : NVar)
           (T : @NTerm o)
           (x : NVar)
           (a b : NTerm)
           (J : bhyps)
           (C : NTerm)
           (wfa : wf_term a)
           (wfb : wf_term b)
           (cova : covered a (vars_hyps H))
           (covb : covered b (vars_hyps H))
           (p1 : ExtractProof (pre_rule_cequiv_subst_hyp_hyp2 H z T x a J b))
           (p2 : ExtractProof (pre_rule_cequiv_subst_hyp_hyp1 H z T x b J C))
  : ExtractProof (pre_rule_cequiv_subst_hyp_concl H z T x a J C).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists e2
          (proof_node (proof_step_cequiv_subst_hyp z x T a b)
                      (rule_cequiv_subst_hyp_concl H z T x a J C e2)
                      [v1,v2]).
  { unfold valid_pre_extract in *; simpl in *.
    allrw @nh_vars_hyps_app.
    allrw @nh_vars_hyps_snoc.
    simpl in *; tcsp. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cequiv_computation {o}
           (lib : library)
           (a b : @NTerm o)
           (H : bhyps)
           (r : reduces_to lib a b)
  : ExtractProof (pre_rule_cequiv_computation_concl a b H).
Proof.
  introv.
  unfold reduces_to in r; exrepnd.
  eexists (@mk_axiom o)
          (proof_node (proof_step_cequiv_computation k)
                      (rule_cequiv_computation_concl a b H)
                      []).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cequiv_computation_aeq {o}
           (lib : library)
           (a b c : @NTerm o)
           (H : bhyps)
           (r : reduces_to lib a b)
           (aeq : alpha_eq b c)
  : ExtractProof (pre_rule_cequiv_computation_concl a c H).
Proof.
  introv.
  unfold reduces_to in r; exrepnd.
  eexists (@mk_axiom o)
          (proof_node (proof_step_cequiv_computation_aeq k)
                      (rule_cequiv_computation_concl a c H)
                      []).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cequiv_computation_atmost {o}
           (lib : library)
           (a b : @NTerm o)
           (n : nat)
           (H : bhyps)
           (r : reduces_in_atmost_k_steps lib a b n)
  : ExtractProof (pre_rule_cequiv_computation_concl a b H).
Proof.
  introv.
  eexists (@mk_axiom o)
          (proof_node (proof_step_cequiv_computation_atmost n)
                      (rule_cequiv_computation_concl a b H)
                      []).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_universe_equality {o}
           (i j : nat)
           (H : @bhyps o)
           (ltij : i < j)
  : ExtractProof (pre_rule_universe_equality_concl H i j).
Proof.
  introv.
  eexists (@mk_axiom o)
          (proof_node (proof_step_universe_equality)
                      (rule_universe_equality_concl H i j)
                      []).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_hypothesis_equality {o}
           (x : NVar)
           (A : @NTerm o)
           (G J : bhyps)
  : ExtractProof (pre_rule_hypothesis_equality_concl G J A x).
Proof.
  introv.
  eexists (@mk_axiom o)
          (proof_node (proof_step_hypothesis_equality)
                      (rule_hypothesis_equality_concl G J A x)
                      []).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_maybe_hidden_hypothesis_equality {o}
           (x : NVar)
           (A : NTerm)
           (G J : @bhyps o)
           (b : bool)
  : ExtractProof (pre_rule_maybe_hidden_hypothesis_equality_concl G J A x b).
Proof.
  introv.
  eexists (@mk_axiom o)
          (proof_node (proof_step_maybe_hidden_hypothesis_equality)
                      (rule_maybe_hidden_hypothesis_equality_concl G J A x b)
                      []).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_unhide_equality {o}
           (x : NVar)
           (A t1 t2 C : NTerm)
           (G J : @bhyps o)
           (p : ExtractProof (pre_rule_unhide_equality_hyp G J x A t1 t2 C))
  : ExtractProof (pre_rule_unhide_equality_concl G J x A t1 t2 C).
Proof.
  introv.
  destruct p as [e v q].
  eexists (@mk_axiom o)
          (proof_node (proof_step_unhide_equality x)
                      (rule_unhide_equality_concl G J x A t1 t2 C)
                      [v]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_equality_equality {o}
           (A B a1 a2 b1 b2 : @NTerm o)
           (i : nat)
           (H : bhyps)
           (p1 : ExtractProof (pre_rule_equality_equality_hyp1 H A B i))
           (p2 : ExtractProof (pre_rule_equality_equality_hyp2 H a1 b1 A))
           (p3 : ExtractProof (pre_rule_equality_equality_hyp2 H a2 b2 A))
  : ExtractProof (pre_rule_equality_equality_concl H a1 a2 b1 b2 A B i).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  destruct p3 as [e3 v3 q3].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_equality_equality)
                      (rule_equality_equality_concl H a1 a2 b1 b2 A B i)
                      [v1,v2,v3]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_integer_equality {o}
           (n : Z)
           (H : @bhyps o)
  : ExtractProof (pre_rule_integer_equality_concl H n).
Proof.
  introv.
  eexists (@mk_axiom o)
          (proof_node (proof_step_integer_equality)
                      (rule_integer_equality_concl H n)
                      []).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_introduction {o}
           (t C : @NTerm o)
           (H : bhyps)
           (wft : wf_term t)
           (covt : covered t (nh_vars_hyps H))
           (nout : noutokens t)
           (p : ExtractProof (pre_rule_introduction_hyp H C t))
  : ExtractProof (pre_rule_introduction_concl H C).
Proof.
  introv.
  destruct p as [e v q].
  eexists t
          (proof_node (proof_step_introduction t)
                      (rule_introduction_concl H C t)
                      [v]).
  { simpl; unfold valid_pre_extract; dands; auto. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_unfold_abstractions {o}
           (lib : library)
           (abs  : list opname)
           (a : @NTerm o)
           (H : bhyps)
           (unf : all_abstractions_can_be_unfolded lib abs a)
           (p : ExtractProof (pre_rule_unfold_abstractions_hyp lib abs a H))
  : ExtractProof (pre_rule_unfold_abstractions_concl a H).
Proof.
  introv.
  destruct p as [e v q].
  eexists e
          (proof_node (proof_step_unfold_abstractions abs)
                      (rule_unfold_abstractions_concl a e H)
                      [v]).
  { simpl in *; auto. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_rev_unfold_abstractions {o}
           (lib : library)
           (abs  : list opname)
           (a : @NTerm o)
           (H : bhyps)
           (wfa : wf_term a)
           (cova : covered a (vars_hyps H))
           (unf : all_abstractions_can_be_unfolded lib abs a)
           (p : ExtractProof (pre_rule_unfold_abstractions_concl a H))
  : ExtractProof (pre_rule_unfold_abstractions_hyp lib abs a H).
Proof.
  introv.
  destruct p as [e v q].
  eexists e
          (proof_node (proof_step_rev_unfold_abstractions abs a)
                      (rule_unfold_abstractions_hyp lib abs a e H)
                      [v]).
  { simpl in *; auto. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_axiom_equality {o}
           (a b T : @NTerm o)
           (H : bhyps)
           (p : ExtractProof (pre_rule_axiom_equality_hyp a b T H))
  : ExtractProof (pre_rule_axiom_equality_concl a b T H).
Proof.
  introv.
  destruct p as [e v q].
  eexists (@mk_axiom o)
          (proof_node (proof_step_axiom_equality)
                      (rule_axiom_equality_concl a b T H)
                      [v]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_thin {o}
           (G J : @bhyps o)
           (A C : NTerm)
           (x : NVar)
           (nixJ : NVin x (free_vars_hyps J))
           (nixC : NVin x (free_vars C))
           (p : ExtractProof (pre_rule_thin_hyp G J C))
  : ExtractProof (pre_rule_thin_concl G x A J C).
Proof.
  introv.
  destruct p as [e v q].

  eexists e
          (proof_node (proof_step_thin x)
                      (rule_thin_concl G x A J C e)
                      [v]).
  {
    simpl in *; auto.
    unfold valid_pre_extract in *; repnd; dands; auto.
    allrw @nh_vars_hyps_app.
    allrw @nh_vars_hyps_snoc; simpl in *.
    eapply covered_subvars;[|eauto].
    rw subvars_eq; introv i.
    allrw in_app_iff; allrw in_snoc; tcsp.
  }

  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_function_equality {o}
           (a1 a2 b1 b2 : @NTerm o)
           (x1 x2 y : NVar)
           (i : nat)
           (H : bhyps)
           (ni : NVin y (vars_hyps H))
           (p1 : ExtractProof (pre_rule_function_equality_hyp1 H a1 a2 i))
           (p2 : ExtractProof (pre_rule_function_equality_hyp2 H y a1 b1 x1 b2 x2 i))
  : ExtractProof (pre_rule_function_equality_concl H a1 x1 b1 a2 x2 b2 i).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_function_equality y)
                      (rule_function_equality_concl H a1 x1 b1 a2 x2 b2 i)
                      [v1,v2]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_apply_equality {o}
           (A B f1 f2 t1 t2 : @NTerm o)
           (x : NVar)
           (H : bhyps)
           (wfA : wf_term A)
           (covA : covered A (vars_hyps H))
           (p1 : ExtractProof (pre_rule_apply_equality_hyp1 H f1 f2 A x B))
           (p2 : ExtractProof (pre_rule_apply_equality_hyp2 H t1 t2 A))
  : ExtractProof (pre_rule_apply_equality_concl H f1 t1 f2 t2 B x).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_apply_equality x A B)
                      (rule_apply_equality_concl H f1 t1 f2 t2 B x)
                      [v1,v2]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_isect_elimination {o}
           (n : nat)
           (A B C a : @NTerm o)
           (f x z : NVar)
           (H J : bhyps)
           (wfa : wf_term a)
           (cova : covered a (snoc (vars_hyps H) f ++ vars_hyps J))
           (nizH : NVin z (vars_hyps H))
           (nizJ : NVin z (vars_hyps J))
           (dzf : z <> f)
           (p1 : ExtractProof (pre_rule_isect_elimination_hyp1 A B a f x H J))
           (p2 : ExtractProof (pre_rule_isect_elimination_hyp2 A B C a f x z H J))
  : ExtractProof (pre_rule_isect_elimination_concl A B C f x H J).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.

  eexists (subst e2 z mk_axiom)
          (proof_node (proof_step_isect_elimination n a x)
                      (rule_isect_elimination_concl A B C e2 f x z H J)
                      [v1,v2]).

  {
    unfold valid_pre_extract in *; simpl in *; repnd.
    dands; eauto 3 with slow.

    - apply covered_subst; simpl; auto.
      eapply covered_subvars;[|eauto].
      allrw @nh_vars_hyps_snoc; simpl.
      allrw @nh_vars_hyps_app; simpl.
      allrw @nh_vars_hyps_snoc; simpl.
      rw subvars_eq.
      introv i; simpl in *.
      allrw in_app_iff.
      allrw in_snoc.
      allrw in_app_iff.
      allrw in_snoc.
      tcsp.

    - unfold noutokens in *.
      allrw <- null_iff_nil.
      introv i.
      apply get_utokens_subst in i; simpl in i.
      apply in_app_iff in i; boolvar; simpl in *; repndors; tcsp;
        try (apply q2 in i; tcsp).
  }

  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_isect_elimination2 {o}
           (n : nat)
           (A B C a : @NTerm o)
           (f x y z : NVar)
           (H J : bhyps)
           (wfa : wf_term a)
           (cova : covered a (snoc (vars_hyps H) f ++ vars_hyps J))
           (nizH : NVin z (vars_hyps H))
           (nizJ : NVin z (vars_hyps J))
           (niyH : NVin y (vars_hyps H))
           (niyJ : NVin y (vars_hyps J))
           (dzf : z <> f)
           (dzy : z <> y)
           (dyf : y <> f)
           (p1 : ExtractProof (pre_rule_isect_elimination_hyp1 A B a f x H J))
           (p2 : ExtractProof (pre_rule_isect_elimination2_hyp2 A B C a f x y z H J))
  : ExtractProof (pre_rule_isect_elimination2_concl A B C f x H J).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.

  eexists (subst (subst e2 y (mk_var f)) z mk_axiom)
          (proof_node (proof_step_isect_elimination2 n a x y)
                      (rule_isect_elimination2_concl A B C e2 f x y z H J)
                      [v1,v2]).

  {
    unfold valid_pre_extract in *; simpl in *; repnd.
    dands; eauto 3 with slow.

    - apply wf_term_subst; eauto 2 with slow.
      apply wf_term_subst; eauto 2 with slow.

    - apply covered_subst; simpl; auto.
      allrw @nh_vars_hyps_snoc; simpl in *.
      allrw @nh_vars_hyps_app; simpl in *.
      allrw @nh_vars_hyps_snoc; simpl in *.
      apply covered_subst; simpl; auto;
        [|apply covered_var; simpl; rw in_app_iff; rw in_snoc; tcsp].

      eapply covered_subvars;[|eauto].
      rw subvars_eq.
      introv i; simpl in *.
      allrw in_app_iff.
      allrw in_snoc.
      allrw in_app_iff.
      allrw in_snoc.
      tcsp.

    - unfold noutokens in *.
      allrw <- null_iff_nil.
      introv i.
      apply get_utokens_subst in i; simpl in i.
      apply in_app_iff in i; boolvar; simpl in *; repndors; tcsp;
        apply get_utokens_subst in i; simpl in i;
          apply in_app_iff in i; boolvar; simpl in *; repndors; tcsp;
            try (apply q2 in i; tcsp).
  }

  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_isect_member_equality {o}
           (H : @bhyps o)
           (t1 t2 A : NTerm)
           (x : NVar)
           (B : NTerm)
           (z : NVar)
           (i : nat)
           (nizH : NVin z (vars_hyps H))
           (p1 : ExtractProof (pre_rule_isect_member_equality_hyp1 H z A t1 t2 B x))
           (p2 : ExtractProof (pre_rule_isect_member_equality_hyp2 H A i))
  : ExtractProof (pre_rule_isect_member_equality_concl H t1 t2 A x B).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_isect_member_equality x i)
                      (rule_isect_member_equality_concl H t1 t2 A x B)
                      [v1,v2]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cumulativity {o}
           (H : @bhyps o)
           (T : NTerm)
           (i j : nat)
           (lij : i <=? j = true)
           (p1 : ExtractProof (pre_rule_cumulativity_hyp H T i))
  : ExtractProof (pre_rule_cumulativity_concl H T j).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_cumulativity i)
                      (rule_cumulativity_concl H T j)
                      [v1]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_equality_symmetry {o}
           (H : @bhyps o)
           (a b T : NTerm)
           (p1 : ExtractProof (pre_rule_equality_seq H b a T))
  : ExtractProof (pre_rule_equality_seq H a b T).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_equality_symmetry)
                      (rule_equality_concl H a b T)
                      [v1]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_equality_transitivity {o}
           (H : @bhyps o)
           (a b c T : NTerm)
           (wfc : wf_term c)
           (covc : covered c (vars_hyps H))
           (p1 : ExtractProof (pre_rule_equality_seq H a c T))
           (p2 : ExtractProof (pre_rule_equality_seq H c b T))
  : ExtractProof (pre_rule_equality_seq H a b T).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_equality_transitivity c)
                      (rule_equality_concl H a b T)
                      [v1,v2]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

(*Definition finish_proof_cequiv_transitivity {o}
           (H : @bhyps o)
           (a b c : NTerm)
           (wfc : wf_term c)
           (covc : covered c (vars_hyps H))
           (p1 : ExtractProof (pre_rule_cequiv_seq H a c))
           (p2 : ExtractProof (pre_rule_cequiv_seq H c b))
  : ExtractProof (pre_rule_cequiv_seq H a b).
Proof.
  introv.
  destruct p1 as [e1 v1 q1].
  destruct p2 as [e2 v2 q2].
  unfold pre2baresequent in *; simpl in *.
  eexists (@mk_axiom o)
          (proof_node (proof_step_cequiv_transitivity c)
                      (rule_cequiv_trans_concl H a b)
                      [v1,v2]).
  { apply valid_pre_extract_axiom. }
  { exact eq_refl. }
Defined.*)

Fixpoint list_option2option_list {A} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | Some a :: l =>
    match list_option2option_list l with
    | Some k => Some (a :: k)
    | None => None
    end
  | None :: _ => None
  end.

Definition pre_concl2type {o} (c : @pre_conclusion o) : option NTerm :=
  match c with
  | pre_concl_ext t => Some t
  | pre_concl_typ t => None
  end.

Definition finish_pre_proof_node {o} (n : @proof_step o) (c : @pre_baresequent o) (l : list (@proof o)) : option NTerm :=
  match n with
  | proof_step_lemma name => Some (LemmaName2extract name)

  | proof_step_lemma_with_extract name => Some mk_axiom

  | proof_step_base_closed => Some mk_axiom
  | proof_step_base_closed2 => Some mk_axiom
  | proof_step_int_equality => Some mk_axiom
  | proof_step_base_equality => Some mk_axiom
  | proof_step_isect_equality y => Some mk_axiom
  | proof_step_function_equality z => Some mk_axiom

  | proof_step_isect_member_formation z i =>
    match l with
    | [p1,p2] => Some (proof2extract p1)
    | _ => None
    end

  | proof_step_hypothesis x => Some (mk_var x)
  | proof_step_hypothesis_num n =>
    match find_hypothesis_name_from_nat (pre_hyps c) n with
    | Some x => Some (mk_var x)
    | None => None
    end

  | proof_step_cut x B =>
    match l with
    | [p1,p2] => Some (subst (proof2extract p2) x (proof2extract p1))
    | _ => None
    end

  | proof_step_cequiv_computation n => Some mk_axiom
  | proof_step_cequiv_computation_aeq n => Some mk_axiom
  | proof_step_cequiv_computation_atmost n => Some mk_axiom

  | proof_step_unfold_abstractions names =>
    match l with
    | [p1] => Some (proof2extract p1)
    | _ => None
    end

  | proof_step_rev_unfold_abstractions names a =>
    match l with
    | [p1] => Some (proof2extract p1)
    | _ => None
    end

  | proof_step_cequiv_subst_concl x C a b =>
    match l with
    | [p1,p2] => Some (proof2extract p2)
    | _ => None
    end

  | proof_step_cequiv_subst_hyp z x C a b =>
    match l with
    | [p1,p2] => Some (proof2extract p2)
    | _ => None
    end

  | proof_step_cequiv_subst_hyp_num n x C a b =>
    match l with
    | [p1,p2] => Some (proof2extract p2)
    | _ => None
    end

  | proof_step_universe_equality => Some mk_axiom
  | proof_step_hypothesis_equality => Some mk_axiom
  | proof_step_maybe_hidden_hypothesis_equality => Some mk_axiom
  | proof_step_unhide_equality x => Some mk_axiom
  | proof_step_equality_equality => Some mk_axiom
  | proof_step_equality_equality_base => Some mk_axiom
  | proof_step_integer_equality => Some mk_axiom

  | proof_step_introduction t => Some t

  | proof_step_axiom_equality => Some mk_axiom

  | proof_step_thin x =>
    match l with
    | [p1] => Some (proof2extract p1)
    | _ => None
    end

  | proof_step_thin_num n =>
    match l with
    | [p1] => Some (proof2extract p1)
    | _ => None
    end

  | proof_step_apply_equality x A B => Some mk_axiom

  | proof_step_isect_elimination n a z =>
    match l with
    | [p1,p2] => Some (subst (proof2extract p2) z mk_axiom)
    | _ => None
    end

  | proof_step_isect_elimination2 n a z y =>
    match l with
    | [p1,p2] =>
      match find_hypothesis_name_from_nat (proof2hyps p1) n with
      | Some f => Some (subst (subst (proof2extract p2) y (mk_var f)) z mk_axiom)
      | None => None
      end
    | _ => None
    end

  | proof_step_isect_member_equality x i => Some mk_axiom
  | proof_step_cumulativity i => Some mk_axiom
  | proof_step_equality_symmetry => Some mk_axiom
  | proof_step_equality_transitivity _ => Some mk_axiom
  | proof_step_cequiv_transitivity _ => Some mk_axiom
  | proof_step_approx_refl => Some mk_axiom
  | proof_step_cequiv_refl => Some mk_axiom
  | proof_step_cequiv_alpha_eq => Some mk_axiom
  | proof_step_cequiv_approx => Some mk_axiom
  | proof_step_approx_eq => Some mk_axiom
  | proof_step_cequiv_eq => Some mk_axiom
  end.

Fixpoint finish_pre_proof {o} (p : @pre_proof o) : option proof :=
  match p with
  | pre_proof_hole _ => None
  | pre_proof_node n c ps =>
    match list_option2option_list (map finish_pre_proof ps) with
    | Some l =>
      match finish_pre_proof_node n c l with
      | Some e => Some (proof_node n (pre2baresequent c e) l)
      | None => None
      end
    | None => None
    end
  end.


(*Fixpoint finish_pre_proof {o}
         {s : @pre_baresequent o}
         (p : pre_proof)
  : option (ExtractProof s) :=
  match p with
  | pre_proof_from_ctxt c H => Some (finish_proof_from_context c H)

  | pre_proof_hole s => None

  | pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH p1 p2)
    | _, _ => None
    end

  | pre_proof_isect_member_formation A x B z i H nizH prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_isect_member_formation A x B z i H nizH p1 p2)
    | _, _ => None
    end

  | pre_proof_approx_refl a H => Some (finish_proof_approx_refl a H)

  | pre_proof_cequiv_refl a H => Some (finish_proof_cequiv_refl a H)

  | pre_proof_cequiv_alpha_eq a b H aeq => Some (finish_proof_cequiv_alpha_eq a b H aeq)

  | pre_proof_cequiv_approx a b H prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_cequiv_approx a b H p1 p2)
    | _, _ => None
    end

  | pre_proof_approx_eq a1 a2 b1 b2 i H prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_approx_eq a1 a2 b1 b2 i H p1 p2)
    | _, _ => None
    end

  | pre_proof_cequiv_eq a1 a2 b1 b2 i H prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_cequiv_eq a1 a2 b1 b2 i H p1 p2)
    | _, _ => None
    end

  | pre_proof_cut B C x H wfB covB nixH prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_cut B C x H wfB covB nixH p1 p2)
    | _, _ => None
    end

  | pre_proof_hypothesis x A G J => Some (finish_proof_hypothesis x A G J)

  | pre_proof_cequiv_subst_concl C x a b H wfa wfb cova covb prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_cequiv_subst_concl C x a b H wfa wfb cova covb p1 p2)
    | _, _ => None
    end

  | pre_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 => Some (finish_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb p1 p2)
    | _, _ => None
    end

  | pre_proof_cequiv_computation lib a b H r =>
    Some (finish_proof_cequiv_computation lib a b H r)

  | pre_proof_cequiv_computation_aeq lib a b c H r aeq =>
    Some (finish_proof_cequiv_computation_aeq lib a b c H r aeq)

  | pre_proof_cequiv_computation_atmost lib a b n H r =>
    Some (finish_proof_cequiv_computation_atmost lib a b n H r)

  | pre_proof_unfold_abstractions lib abs a H unf prf =>
    match finish_pre_proof prf with
    | Some p => Some (finish_proof_unfold_abstractions lib abs a H unf p)
    | _ => None
    end

  | pre_proof_rev_unfold_abstractions lib abs a H wfa cova unf prf =>
    match finish_pre_proof prf with
    | Some p => Some (finish_proof_rev_unfold_abstractions lib abs a H wfa cova unf p)
    | _ => None
    end

  | pre_proof_universe_equality i j H ltij =>
    Some (finish_proof_universe_equality i j H ltij)

  | pre_proof_hypothesis_equality x A G J =>
    Some (finish_proof_hypothesis_equality x A G J)

  | pre_proof_maybe_hidden_hypothesis_equality x A G J b =>
    Some (finish_proof_maybe_hidden_hypothesis_equality x A G J b)

  | pre_proof_unhide_equality x A t1 t2 C G J prf =>
    match finish_pre_proof prf with
    | Some p => Some (finish_proof_unhide_equality x A t1 t2 C G J p)
    | _ => None
    end

  | pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
    match finish_pre_proof prf1,
          finish_pre_proof prf2,
          finish_pre_proof prf3 with
    | Some p1, Some p2, Some p3 =>
      Some (finish_proof_equality_equality A B a1 a2 b1 b2 i H p1 p2 p3)
    | _, _, _ => None
    end

  | pre_proof_integer_equality n H =>
    Some (finish_proof_integer_equality n H)

  | pre_proof_introduction t C H wft covt nout prf =>
    match finish_pre_proof prf with
    | Some p => Some (finish_proof_introduction t C H wft covt nout p)
    | _ => None
    end

  | pre_proof_axiom_equality a b T H prf =>
    match finish_pre_proof prf with
    | Some p => Some (finish_proof_axiom_equality a b T H p)
    | _ => None
    end

  | pre_proof_thin G J A C x nixJ nixC prf =>
    match finish_pre_proof prf with
    | Some p => Some (finish_proof_thin G J A C x nixJ nixC p)
    | _ => None
    end

  | pre_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH p1 p2)
    | _, _ => None
    end

  | pre_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA p1 p2)
    | _, _ => None
    end

  | pre_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf p1 p2)
    | _, _ => None
    end

  | pre_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf p1 p2)
    | _, _ => None
    end

  | pre_proof_isect_member_equality H t1 t2 A x B z i nizH prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_isect_member_equality H t1 t2 A x B z i nizH p1 p2)
    | _, _ => None
    end

  | pre_proof_cumulativity H T i j lij prf1 =>
    match finish_pre_proof prf1 with
    | Some p1 =>
      Some (finish_proof_cumulativity H T i j lij p1)
    | _ => None
    end

  | pre_proof_equality_symmetry H a b T prf1 =>
    match finish_pre_proof prf1 with
    | Some p1 =>
      Some (finish_proof_equality_symmetry H a b T p1)
    | _ => None
    end

  | pre_proof_equality_transitivity H a b c T wfc covc prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_equality_transitivity H a b c T wfc covc p1 p2)
    | _, _ => None
    end

  | pre_proof_cequiv_transitivity H a b c wfc covc prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_cequiv_transitivity H a b c wfc covc p1 p2)
    | _, _ => None
    end
  end.*)

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

Lemma finish_pre_proof_preserves_isprog {o} :
  forall {pre_prf : @pre_proof o} {prf},
    finish_pre_proof pre_prf = Some prf
    -> isprog (pre_proof2type pre_prf)
    -> isprog (proof2type prf).
Proof.
  introv fin isp.
  destruct pre_prf; simpl in *; ginv.
  remember (list_option2option_list (map finish_pre_proof hyps)) as ol.
  destruct ol; ginv.
  remember (finish_pre_proof_node name concl l) as oe.
  destruct oe; ginv.
  simpl in *.
  unfold pre_proof2type in isp; simpl in isp.
  destruct concl; simpl in *; auto.
  destruct pre_concl0; simpl in *; auto.
Qed.

Fixpoint pre_proof_size {o} (p : @pre_proof o) : nat :=
  match p with
  | pre_proof_hole c => 1
  | pre_proof_node n c ps => S (addl (map pre_proof_size ps))
  end.

Lemma pre_proof_better_ind {o} :
  forall (P : @pre_proof o -> Type),
    (forall c, P (pre_proof_hole c))
    -> (forall n c ps (ind : forall p, LIn p ps -> P p), P (pre_proof_node n c ps))
    -> forall p : pre_proof, P p.
Proof.
  introv hh hn; introv.
  remember (pre_proof_size p) as n.
  revert p Heqn.
  induction n as [? imp] using comp_ind_type; introv h; subst.

  destruct p; simpl; auto.
  apply hn; introv i.
  clear hn.

  pose proof (imp (pre_proof_size p)) as q; clear imp; apply q; auto.
  simpl.
  apply (le_addl pre_proof_size) in i; try lia.
Defined.

Lemma in_list_option2option_list_implies :
  forall {A} (l : list (option A)) k a,
    list_option2option_list l = Some k
    -> LIn a k -> LIn (Some a) l.
Proof.
  induction l; introv h i; simpl in *; ginv; simpl in *; tcsp.
  destruct a; simpl in *; tcsp.
  remember (list_option2option_list l) as j; destruct j; ginv.
  simpl in *; repndors; subst; tcsp.
  apply IHl in i; tcsp.
Qed.

Definition valid_pre_proof_node_context {o}
           (ctxt : @ProofContext o)
           (n    : @proof_step o)
           (c    : @pre_baresequent o)
           (hs   : list (@pre_baresequent o)) : Type :=
  match n with
  | proof_step_lemma name =>
    {T : NTerm $ {H : bhyps $
      LIn (MkNamedConcl name T) (PC_conclusions ctxt)
      # c = named_concl2pre_bseq H (MkNamedConcl name T)
      # hs = [] }}

  | proof_step_lemma_with_extract name =>
    {T : NTerm $ {t : NTerm $ {r : NTerm $ {H : bhyps $
      LIn (MkNamedConcl name T) (PC_conclusions ctxt)
      # c = named_concl2pre_bseq_with_extract H (MkNamedConcl name T) t
      # reduces_to ctxt (LemmaName2extract name) r
      # alpha_eq r t
      # hs = [] }}}}

  | proof_step_base_closed =>
    {t : NTerm $
      c = pre_rule_base_closed_concl t
      # hs = [] }

  | proof_step_base_closed2 =>
    {x : NTerm $ {t : NTerm $
      c = mk_pre_bseq [] (mk_pre_concl x)
      # reduces_in_atmost_k_steps ctxt x (mk_equality t t mk_base) 1
      # hs = [] }}

  | proof_step_int_equality =>
    {H : bhyps $ {i : nat $
      c = pre_rule_int_equality_concl H i
      # hs = [] }}

  | proof_step_base_equality =>
    {H : bhyps $ {i : nat $
      c = pre_rule_base_equality_concl H i
      # hs = [] }}

  | proof_step_isect_equality y =>
    {a1 , a2 , b1 , b2 : NTerm $ {x1 , x2 : NVar $ {i : nat $ {H : bhyps $
      ! LIn y (vars_hyps H)
      # c = pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H
      # hs = [pre_rule_isect_equality_hyp1 a1 a2 i H,
              pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H] }}}}

  | proof_step_isect_member_formation z i =>
    {A : NTerm $ {x : NVar $ {B : NTerm $ {H : bhyps $
    ! LIn z (vars_hyps H)
    # c = pre_rule_isect_member_formation_concl A x B H
    # hs = [pre_rule_isect_member_formation_hyp1 z A x B H,
	     pre_rule_isect_member_formation_hyp2 A i H] }}}}

  | proof_step_approx_refl =>
    {a : NTerm $ {H : bhyps $
    c = pre_rule_approx_refl_concl a H
    # hs = [] }}

  | proof_step_cequiv_refl =>
    {a : NTerm $ {H : bhyps $
      c = pre_rule_cequiv_refl_concl a H
      # hs = [] }}

  | proof_step_cequiv_alpha_eq =>
    {a , b : NTerm $ {H : bhyps $
    alpha_eq a b
    # c = pre_rule_cequiv_alpha_eq_concl a b H
    # hs = [] }}

  | proof_step_cequiv_approx =>
    {a , b : NTerm $ {H : bhyps $
    c = pre_rule_cequiv_approx_concl a b H
    # hs = [pre_rule_cequiv_approx_hyp a b H,
             pre_rule_cequiv_approx_hyp b a H] }}

  | proof_step_approx_eq =>
    {a1 , a2 , b1 , b2 : NTerm $ {i : nat $ {H : bhyps $
    c = pre_rule_approx_eq_concl a1 a2 b1 b2 i H
    # hs = [pre_rule_eq_base_hyp a1 a2 H,
             pre_rule_eq_base_hyp b1 b2 H] }}}

  | proof_step_cequiv_eq =>
    {a1 , a2 , b1 , b2 : NTerm $ {i : nat $ {H : bhyps $
    c = pre_rule_cequiv_eq_concl a1 a2 b1 b2 i H
    # hs = [pre_rule_eq_base_hyp a1 a2 H,
             pre_rule_eq_base_hyp b1 b2 H] }}}

  | proof_step_cut x B =>
    {C : NTerm $ {H : bhyps $
    wf_term B
    # covered B (vars_hyps H)
    # ! LIn x (vars_hyps H)
    # c = pre_rule_cut_concl H C
    # hs = [pre_rule_cut_hyp1 H B,
             pre_rule_cut_hyp2 H x B C] }}

  | proof_step_hypothesis x =>
    {A : NTerm $ {G , J : bhyps $
    c = pre_rule_hypothesis_concl G J A x
    # hs = [] }}

  | proof_step_hypothesis_num n =>
    {A : NTerm $ {x : NVar $ {G , J : bhyps $
    find_hypothesis_name_from_nat (snoc G (mk_hyp x A) ++ J) n = Some x
    # c = pre_rule_hypothesis_concl G J A x
    # hs = [] }}}

  | proof_step_cequiv_subst_concl x C a b =>
    {H : bhyps $
    wf_term a
    # wf_term b
    # covered a (vars_hyps H)
    # covered b (vars_hyps H)
    # c = pre_rule_cequiv_subst_hyp1 H x C a
    # hs = [pre_rule_cequiv_subst_hyp2 H a b,
             pre_rule_cequiv_subst_hyp1 H x C b] }

  | proof_step_cequiv_subst_hyp z x T a b =>
    {H , J : bhyps $ {C : NTerm $
    wf_term a
    # wf_term b
    # covered a (vars_hyps H)
    # covered b (vars_hyps H)
    # c = pre_rule_cequiv_subst_hyp_concl H z T x a J C
    # hs = [pre_rule_cequiv_subst_hyp_hyp2 H z T x a J b,
             pre_rule_cequiv_subst_hyp_hyp1 H z T x b J C] }}

  | proof_step_cequiv_subst_hyp_num n x T a b =>
    {H , J : bhyps $ {z : NVar $ {C : NTerm $
    find_hypothesis_name_from_nat (snoc H (mk_hyp z (subst T x a)) ++ J) n = Some z
    # wf_term a
    # wf_term b
    # covered a (vars_hyps H)
    # covered b (vars_hyps H)
    # c = pre_rule_cequiv_subst_hyp_concl H z T x a J C
    # hs = [pre_rule_cequiv_subst_hyp_hyp2 H z T x a J b,
             pre_rule_cequiv_subst_hyp_hyp1 H z T x b J C] }}}

  | proof_step_cequiv_computation n =>
    {a , b : NTerm $ {H : bhyps $
    reduces_to ctxt a b
    # c = pre_rule_cequiv_computation_concl a b H
    # hs = [] }}

  | proof_step_cequiv_computation_aeq n =>
    {a , b , d : NTerm $ {H : bhyps $
    reduces_to ctxt a b
    # alpha_eq b d
    # c = pre_rule_cequiv_computation_concl a d H
    # hs = [] }}

  | proof_step_cequiv_computation_atmost n =>
    {a , b : NTerm $ {H : bhyps $ {k : nat $
    k <= n
    # reduces_in_atmost_k_steps ctxt a b k
    # c = pre_rule_cequiv_computation_concl a b H
    # hs = [] }}}

  | proof_step_unfold_abstractions abs =>
    {a : NTerm $ {H : bhyps $
    all_abstractions_can_be_unfolded ctxt abs a
    # c = pre_rule_unfold_abstractions_concl a H
    # hs = [pre_rule_unfold_abstractions_hyp ctxt abs a H] }}

  | proof_step_rev_unfold_abstractions abs a =>
    {H : bhyps $
    wf_term a
    # covered a (vars_hyps H)
    # all_abstractions_can_be_unfolded ctxt abs a
    # c = pre_rule_unfold_abstractions_hyp ctxt abs a H
    # hs = [pre_rule_unfold_abstractions_concl a H] }

  | proof_step_universe_equality =>
    {i , j : nat $ {H : bhyps $
    i < j
    # c = pre_rule_universe_equality_concl H i j
    # hs = [] }}

  | proof_step_hypothesis_equality =>
    {x : NVar $ {A : NTerm $ {G , J : bhyps $
    c = pre_rule_hypothesis_equality_concl G J A x
    # hs = [] }}}

  | proof_step_maybe_hidden_hypothesis_equality =>
    {x : NVar $ {A : NTerm $ {G , J : bhyps $ {b : bool $
    c = pre_rule_maybe_hidden_hypothesis_equality_concl G J A x b
    # hs = [] }}}}

  | proof_step_unhide_equality x =>
    {A , t1 , t2 , C : NTerm $ {G , J : bhyps $
    c = pre_rule_unhide_equality_concl G J x A t1 t2 C
    # hs = [pre_rule_unhide_equality_hyp G J x A t1 t2 C] }}

  | proof_step_equality_equality =>
    {A , B , a1 , a2 , b1 , b2 : NTerm $ {i : nat $ {H : bhyps $
    c = pre_rule_equality_equality_concl H a1 a2 b1 b2 A B i
    # hs = [pre_rule_equality_equality_hyp1 H A B i,
             pre_rule_equality_equality_hyp2 H a1 b1 A,
             pre_rule_equality_equality_hyp2 H a2 b2 A] }}}

  | proof_step_equality_equality_base =>
    {A , B , a1 , a2 , b1 , b2 : NTerm $ {i : nat $ {H : bhyps $
    c = pre_rule_equality_equality_concl H a1 a2 b1 b2 A B i
    # hs = [pre_rule_equality_equality_hyp1 H A B i,
             pre_rule_equality_equality_hyp3 H a1 b1,
             pre_rule_equality_equality_hyp3 H a2 b2] }}}

  | proof_step_integer_equality =>
    {n : Z $ {H : bhyps $
    c = pre_rule_integer_equality_concl H n
    # hs = [] }}

  | proof_step_introduction t =>
    {C : NTerm $ {H : bhyps $
    wf_term t
    # covered t (nh_vars_hyps H)
    # noutokens t
    # c = pre_rule_introduction_concl H C
    # hs = [pre_rule_introduction_hyp H C t] }}

  | proof_step_axiom_equality =>
    {a , b , T : NTerm $ {H : bhyps $
    c = pre_rule_axiom_equality_concl a b T H
    # hs = [pre_rule_axiom_equality_hyp a b T H] }}

  | proof_step_thin x =>
    {G , J : bhyps $ {A , C : NTerm $
      ! LIn x (free_vars_hyps J)
      # ! LIn x (free_vars C)
      # c = pre_rule_thin_concl G x A J C
      # hs = [pre_rule_thin_hyp G J C] }}

  | proof_step_thin_num n =>
    {G , J : bhyps $ {x : NVar $ {A , C : NTerm $
      find_hypothesis_name_from_nat (snoc G (mk_hyp x A) ++ J) n = Some x
      # ! LIn x (free_vars_hyps J)
      # ! LIn x (free_vars C)
      # c = pre_rule_thin_concl G x A J C
      # hs = [pre_rule_thin_hyp G J C] }}}

  | proof_step_function_equality y =>
    {a1 , a2 , b1 , b2 : NTerm $ {x1 , x2 : NVar $ {i : nat $ {H : bhyps $
      !LIn y (vars_hyps H)
      # c = pre_rule_function_equality_concl H a1 x1 b1 a2 x2 b2 i
      # hs = [pre_rule_function_equality_hyp1 H a1 a2 i,
               pre_rule_function_equality_hyp2 H y a1 b1 x1 b2 x2 i] }}}}

  | proof_step_apply_equality x A B =>
    {f1 , f2 , t1 , t2 : NTerm $ {H : bhyps $
    wf_term A
    # covered A (vars_hyps H)
    # c = pre_rule_apply_equality_concl H f1 t1 f2 t2 B x
    # hs = [pre_rule_apply_equality_hyp1 H f1 f2 A x B,
             pre_rule_apply_equality_hyp2 H t1 t2 A] }}

  | proof_step_isect_elimination n a z =>
    {A , B , C : NTerm $ {f , x : NVar $ {H , J : bhyps $
    find_hypothesis_name_from_nat (snoc H (mk_hyp f (mk_isect A x B)) ++ J) n = Some f
    # wf_term a
    # covered a (snoc (vars_hyps H) f ++ vars_hyps J)
    # ! LIn z (vars_hyps H)
    # ! LIn z (vars_hyps J)
    # z <> f
    # c = pre_rule_isect_elimination_concl A B C f x H J
    # hs = [pre_rule_isect_elimination_hyp1 A B a f x H J,
             pre_rule_isect_elimination_hyp2 A B C a f x z H J] }}}

  | proof_step_isect_elimination2 n a z y =>
    {A , B , C : NTerm $ {f , x : NVar $ {H , J : bhyps $
    find_hypothesis_name_from_nat (snoc H (mk_hyp f (mk_isect A x B)) ++ J) n = Some f
    # wf_term a
    # covered a (snoc (vars_hyps H) f ++ vars_hyps J)
    # ! LIn z (vars_hyps H)
    # ! LIn z (vars_hyps J)
    # ! LIn y (vars_hyps H)
    # ! LIn y (vars_hyps J)
    # z <> f
    # z <> y
    # y <> f
    # c = pre_rule_isect_elimination2_concl A B C f x H J
    # hs = [pre_rule_isect_elimination_hyp1 A B a f x H J,
             pre_rule_isect_elimination2_hyp2 A B C a f x y z H J] }}}

  | proof_step_isect_member_equality z i =>
    {H : bhyps $ {t1 , t2 , A : NTerm $ {x : NVar $ {B : NTerm $
    ! LIn z (vars_hyps H)
    # c = pre_rule_isect_member_equality_concl H t1 t2 A x B
    # hs = [pre_rule_isect_member_equality_hyp1 H z A t1 t2 B x,
             pre_rule_isect_member_equality_hyp2 H A i] }}}}

  | proof_step_cumulativity i =>
    {H : bhyps $ {T : NTerm $ {j : nat $
    i <= j
    # c = pre_rule_cumulativity_concl H T j
    # hs = [pre_rule_cumulativity_hyp H T i] }}}

  | proof_step_equality_symmetry =>
    {H : bhyps $ {a , b , T : NTerm $
    c = pre_rule_equality_seq H a b T
    # hs = [pre_rule_equality_seq H b a T] }}

  | proof_step_equality_transitivity d =>
    {H : bhyps $ {a , b , T : NTerm $
    wf_term d
    # covered d (vars_hyps H)
    # c = pre_rule_equality_seq H a b T
    # hs = [pre_rule_equality_seq H a d T,
             pre_rule_equality_seq H d b T] }}

  | proof_step_cequiv_transitivity d =>
    {H : bhyps $ {a , b : NTerm $
    wf_term d
    # covered d (vars_hyps H)
    # c = pre_rule_cequiv_seq H a b
    # hs = [pre_rule_cequiv_seq H a d,
             pre_rule_cequiv_seq H d b] }}
  end.

Inductive valid_pre_proof_context {o} (ctxt : @ProofContext o) : @pre_proof o -> Type :=
| valid_pre_proof_hole : forall s, valid_pre_proof_context ctxt (pre_proof_hole s)
| valid_pre_proof_node :
    forall n c hs,
      valid_pre_proof_node_context ctxt n c (map pre_proof2bseq hs)
      -> (forall h, LIn h hs -> valid_pre_proof_context ctxt h)
      -> valid_pre_proof_context ctxt (pre_proof_node n c hs).
Hint Constructors valid_pre_proof_context.

Lemma length_list_option2option_list :
  forall {A} (l : list (option A)) k,
    list_option2option_list l = Some k
    -> length l = length k.
Proof.
  induction l; introv h; simpl in *; ginv; simpl in *; tcsp.
  destruct a; simpl in *; ginv.
  remember (list_option2option_list l) as j; symmetry in Heqj.
  destruct j; ginv; simpl in *; tcsp.
Qed.

Lemma in_combine_list_option2option_list_implies :
  forall {A} (l : list (option A)) k a b,
    list_option2option_list l = Some k
    -> LIn (a,b) (combine k l) -> b = Some a.
Proof.
  induction l; introv h i; simpl in *; ginv; simpl in *; tcsp.
  destruct a; simpl in *; tcsp.
  remember (list_option2option_list l) as j; destruct j; ginv.
  simpl in *; repndors; subst; tcsp; ginv.
  apply IHl in i; tcsp.
Qed.

Lemma in_combine_sym :
  forall {A B} (l : list A) (k : list B) a b,
    LIn (a,b) (combine k l) -> LIn (b, a) (combine l k).
Proof.
  induction l; introv i; simpl in *; ginv; simpl in *; tcsp;
    destruct k; simpl in *; tcsp.
  repndors; ginv; tcsp.
Qed.

Definition proof2pre_bseq {o} (p : @proof o) := baresequent2pre (proof2bseq p).

Lemma finish_pre_proof_implies_pre_proof2bseq_eq {o} :
  forall (pp : @pre_proof o) p,
    finish_pre_proof pp = Some p
    -> pre_proof2bseq pp = proof2pre_bseq p.
Proof.
  introv fin.
  destruct pp; simpl in *; ginv.
  remember (list_option2option_list (map finish_pre_proof hyps)) as ol.
  destruct ol; simpl in *; ginv.
  remember (finish_pre_proof_node name concl l) as on.
  destruct on; simpl in *; ginv; tcsp.
  destruct concl, pre_concl0; simpl; tcsp.
Qed.

Lemma list_option2option_list_map_finish_pre_proof_implies_eq_proof2bseq {o} :
  forall (ps : list (@pre_proof o)) l,
    list_option2option_list (map finish_pre_proof ps) = Some l
    -> map pre_proof2bseq ps = map proof2pre_bseq l.
Proof.
  introv h.
  applydup @length_list_option2option_list in h as len.
  allrw map_length.
  apply eq_maps3; auto.
  introv i.

  assert (LIn (finish_pre_proof a, c) (combine (map finish_pre_proof ps) l)) as j.
  {
    rewrite <- map_combine_left.
    apply in_map_iff; eexists; dands; eauto.
  }
  clear i.

  apply in_combine_sym in j.
  apply in_combine_list_option2option_list_implies in j; auto.
  clear h len.
  apply finish_pre_proof_implies_pre_proof2bseq_eq; auto.
Qed.

Lemma proof2hyps_as_pre_hyps_proof2pre_bseq {o} :
  forall (p : @proof o),
    proof2hyps p = pre_hyps (proof2pre_bseq p).
Proof.
  introv; destruct p; simpl; auto.
Qed.

Lemma find_hypothesis_name_from_nat_middle {o} :
  forall (H : @bhyps o) x t J,
    find_hypothesis_name_from_nat (snoc H (mk_hyp x t) ++ J) (S (length H)) = Some x.
Proof.
  induction H; introv; simpl; auto.
Qed.

Lemma find_hypothesis_name_from_nat_in {o} :
  forall (H : @bhyps o) n x,
    find_hypothesis_name_from_nat H n = Some x
    -> LIn x (vars_hyps H).
Proof.
  induction H; introv h; simpl in *; tcsp.
  destruct n; ginv; tcsp.
  destruct n; ginv; tcsp.
  apply IHlist in h; tcsp.
Qed.

Lemma finish_pre_proof_node_valid_pre_extract {o} :
  forall ctxt n (c : @pre_baresequent o) l e,
    valid_pre_proof_node_context ctxt n c (map proof2pre_bseq l)
    -> (forall p, LIn p l -> valid_pre_extract (proof2hyps p) (proof2extract p))
    -> finish_pre_proof_node n c l = Some e
    -> valid_pre_extract (pre_hyps c) e.
Proof.
  introv val imp fin.
  destruct n; simpl in *; ginv;
    try (apply valid_pre_extract_axiom).

(*  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val1; repnd; GC).
    admit.
 *)

(*  - destruct c; simpl in *; ginv.
    destruct pre_concl0; simpl in *; ginv.
    unfold named_concl2extract; simpl.
    apply valid_pre_extract_mk_abs_opname2opabs.*)

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val1; repnd; GC).

    pose proof (imp p) as q; autodimp q hyp; clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in q.
    rewrite val2 in q; simpl in *.
    apply valid_pre_extract_snoc_mk_hhyp_implies in q; auto.

  - exrepnd; subst.
    repeat (destruct l; simpl in *; ginv).
    clear imp.

    unfold valid_pre_extract; dands; simpl; eauto 2 with slow.
    apply covered_var; rw @nh_vars_hyps_app; rw @nh_vars_hyps_snoc; simpl.
    rw in_app_iff; rw in_snoc; tcsp.

  - exrepnd; subst.
    repeat (destruct l; simpl in *; ginv).

    clear imp.

    rewrite val0 in fin; ginv.

    unfold valid_pre_extract; dands; simpl; eauto 2 with slow.
    apply covered_var; rw @nh_vars_hyps_app; rw @nh_vars_hyps_snoc; simpl.
    rw in_app_iff; rw in_snoc; tcsp.

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val1; repnd; GC).

    pose proof (imp p0) as q; autodimp q hyp.
    pose proof (imp p) as h; autodimp h hyp.
    clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in q, h.
    rewrite val5 in q; rewrite val4 in h; simpl in *.

    eapply implies_valid_pre_extract_subst; eauto.

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val1; repnd; GC).

    pose proof (imp p) as h; autodimp h hyp.
    clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in h.
    rewrite val2 in h; simpl in *; auto.

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val0; repnd; GC).

    pose proof (imp p) as h; autodimp h hyp.
    clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in h.
    rewrite val4 in h; simpl in *; auto.

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val0; repnd; GC).

    pose proof (imp p0) as h; autodimp h hyp.
    clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in h.
    rewrite val6 in h; simpl in *; auto.

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val0; repnd; GC).

    pose proof (imp p0) as h; autodimp h hyp.
    clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in h.
    rewrite val6 in h; simpl in *; auto.

    unfold valid_pre_extract in *; simpl in *.
    allrw @nh_vars_hyps_app.
    allrw @nh_vars_hyps_snoc.
    simpl in *; tcsp.

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val1; repnd; GC).

    pose proof (imp p0) as h; autodimp h hyp.
    clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in h.
    rewrite val7 in h; simpl in *; auto.

    unfold valid_pre_extract in *; simpl in *.
    allrw @nh_vars_hyps_app.
    allrw @nh_vars_hyps_snoc.
    simpl in *; tcsp.

  - exrepnd.
    repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val1; repnd; GC).

    simpl; unfold valid_pre_extract; dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val1; repnd; GC).

    pose proof (imp p) as h; autodimp h hyp.
    clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in h.
    rewrite val3 in h; simpl in *; auto.

    simpl in *; auto.
    unfold valid_pre_extract in *; repnd; dands; auto.
    allrw @nh_vars_hyps_app.
    allrw @nh_vars_hyps_snoc; simpl in *.
    eapply covered_subvars;[|eauto].
    rw subvars_eq; introv i.
    allrw in_app_iff; allrw in_snoc; tcsp.

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val0; repnd; GC).

    pose proof (imp p) as h; autodimp h hyp.
    clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in h.
    rewrite val4 in h; simpl in *; auto.

    simpl in *; auto.
    unfold valid_pre_extract in *; repnd; dands; auto.
    allrw @nh_vars_hyps_app.
    allrw @nh_vars_hyps_snoc; simpl in *.
    eapply covered_subvars;[|eauto].
    rw subvars_eq; introv i.
    allrw in_app_iff; allrw in_snoc; tcsp.

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val0; repnd; GC).

    pose proof (imp p) as h; autodimp h hyp.
    pose proof (imp p0) as q; autodimp q hyp.
    clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in h, q.
    rewrite val7 in h; rewrite val8 in q; simpl in *; auto.

    unfold valid_pre_extract in *; simpl in *; repnd.
    dands; eauto 3 with slow;[|].

    + apply covered_subst; simpl; auto.
      eapply covered_subvars;[|eauto].
      allrw @nh_vars_hyps_snoc; simpl.
      allrw @nh_vars_hyps_app; simpl.
      allrw @nh_vars_hyps_snoc; simpl.
      rw subvars_eq.
      introv i; simpl in *.
      allrw in_app_iff.
      allrw in_snoc.
      allrw in_app_iff.
      allrw in_snoc.
      repndors; subst; tcsp.

    + unfold noutokens in *.
      allrw <- null_iff_nil.
      introv i.
      apply get_utokens_subst in i; simpl in i.
      apply in_app_iff in i; boolvar; simpl in *; repndors; tcsp;
        try (apply q in i; tcsp).

  - repeat (destruct l; simpl in *; ginv).
    exrepnd; subst; simpl in *.
    repeat (apply cons_inj in val0; repnd; GC).

    pose proof (imp p) as h; autodimp h hyp.
    pose proof (imp p0) as q; autodimp q hyp.
    clear imp.
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in h, q, fin.
    rewrite val11 in fin; simpl in fin.
    rewrite val1 in fin; ginv.
    rewrite val11 in h; rewrite val12 in q; simpl in *; auto.

    unfold valid_pre_extract in *; simpl in *; repnd.
    dands; eauto 3 with slow;[| |].

    + apply wf_term_subst; eauto 2 with slow.
      apply wf_term_subst; eauto 2 with slow.

    + apply covered_subst; simpl; auto.
      allrw @nh_vars_hyps_snoc; simpl in *.
      allrw @nh_vars_hyps_app; simpl in *.
      allrw @nh_vars_hyps_snoc; simpl in *.
      apply covered_subst; simpl; auto;
        [|apply covered_var; simpl; rw in_app_iff; rw in_snoc; tcsp].

      eapply covered_subvars;[|eauto].
      rw subvars_eq.
      introv i; simpl in *.
      allrw in_app_iff.
      allrw in_snoc.
      allrw in_app_iff.
      allrw in_snoc.
      tcsp.

    + unfold noutokens in *.
      allrw <- null_iff_nil.
      introv i.
      apply get_utokens_subst in i; simpl in i.
      apply in_app_iff in i; boolvar; simpl in *; repndors; tcsp;
        apply get_utokens_subst in i; simpl in i;
          apply in_app_iff in i; boolvar; simpl in *; repndors; tcsp;
            try (apply q in i; tcsp).
Qed.

Lemma finish_implies_valid_pre_extract {o} :
  forall {ctxt} {pre_prf : @pre_proof o} {prf : @proof o},
    valid_pre_proof_context ctxt pre_prf
    -> finish_pre_proof pre_prf = Some prf
    -> valid_pre_extract (proof2hyps prf) (proof2extract prf).
Proof.
  induction pre_prf using pre_proof_better_ind; introv valid fin; simpl in *; ginv.

  remember (list_option2option_list (map finish_pre_proof ps)) as ol.
  destruct ol; ginv.
  symmetry in Heqol.

  remember (finish_pre_proof_node n c l) as oe.
  destruct oe; ginv.
  symmetry in Heqoe.

  simpl in *.
  unfold extract_ax; simpl.

  remember (extract (pre2conclusion (pre_concl c) n0)) as oe.
  destruct oe; symmetry in Heqoe0;[|apply valid_pre_extract_axiom].

  inversion valid as [|? ? ? valid_node valid_imp]; subst; clear valid.

  assert (forall p, LIn p l -> valid_pre_extract (proof2hyps p) (proof2extract p)) as imp.
  { introv h.
    eapply in_list_option2option_list_implies in h;[|eauto].
    allrw in_map_iff; exrepnd.
    pose proof (ind a) as q; autodimp q hyp. }
  clear ind valid_imp.

  pose proof (list_option2option_list_map_finish_pre_proof_implies_eq_proof2bseq ps l) as q.
  repeat (autodimp q hyp).
  rewrite q in valid_node.
  clear Heqol q.

  remember (pre_concl c) as w; symmetry in Heqw.
  destruct w; simpl in *; ginv.
  clear Heqw.

  eapply finish_pre_proof_node_valid_pre_extract; eauto.
Qed.

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

Lemma noutokens_decidable {o} :
  forall (t : @NTerm o), decidable (noutokens t).
Proof.
  introv.
  unfold noutokens.
  remember (get_utokens t) as l.
  destruct l;[left|right]; auto.
  intro xx; inversion xx.
Defined.

Lemma closed_decidable {o} :
  forall (t : @NTerm o), decidable (closed t).
Proof.
  introv.
  unfold closed.
  remember (free_vars t) as l.
  destruct l;[left|right]; auto.
  intro xx; inversion xx.
Defined.

Lemma valid_extract_dec_op {o} :
  forall (t : @NTerm o), option (valid_extract t).
Proof.
  introv; unfold valid_extract.
  destruct (wf_term_dec_op t);[|right].
  destruct (closed_decidable t);[|right].
  destruct (noutokens_decidable t);[|right].
  left; dands; auto.
Defined.

Lemma valid_extract_of_proof_dec_op {o} :
  forall (p : @proof o), option (valid_extract_of_proof p).
Proof.
  introv; unfold valid_extract_of_proof.
  destruct (proof2hyps p);[|right].
  destruct (proof2extract_op p);[|right].
  apply valid_extract_dec_op.
Defined.

Lemma isprog_dec_op {o} :
  forall (t : @NTerm o), option (isprog t).
Proof.
  introv.
  unfold isprog.
  remember (nullb (free_vars t)) as b.
  destruct b; unfold assert; simpl;[|right].
  destruct (wf_term_dec_op t);[|right].
  left; dands; auto.
Defined.

Definition finish_pre_proof_seq {o} (pps : @pre_proof_seq o) : option (@RigidLibraryEntry o).
Proof.
  destruct pps as [name pre_prf (*nhyps*) isp].

  remember (finish_pre_proof pre_prf) as q; symmetry in Heqq.
  destruct q;[|right].
  destruct (isprog_dec_op (proof2type p));[|right].
  destruct (valid_extract_of_proof_dec_op p);[|right].

  exact (Some (RigidLibraryEntry_proof name p (MkWfProof i v))).
Defined.

(*Lemma name_of_finish_pre_proof_seq {o} :
  forall (p     : @pre_proof_seq o)
         (name  : LemmaName)
         (stmt  : NTerm)
         (ext   : NTerm)
         (isp   : isprog stmt)
         (valid : valid_extract ext)
         (prf   : proof (NLemma stmt ext)),
    finish_pre_proof_seq p = Some (RigidLibraryEntry_proof name stmt ext isp valid prf)
    -> pre_proof_seq_name p = name.
Proof.
  introv h.
  unfold finish_pre_proof_seq in h.
  destruct p; simpl in *.
  remember (finish_pre_proof pre_proof_seq_proof0) as fin; symmetry in Heqfin;
    destruct fin; ginv.
  destruct e; ginv; cpx.
  inversion h; auto.
Qed.*)

Definition SoftLibrary_add_entry {o}
           (state : @SoftLibrary o)
           (entry : RigidLibraryEntry)
           (pps   : pre_proofs) : SoftLibrary :=
  match state with
  | MkSoftLibrary L _ => MkSoftLibrary (entry :: L) pps
  end.

Definition SoftLibrary_finish_proof {o}
           (state : @SoftLibrary o)
           (name  : LemmaName) : UpdRes :=
  match find_unfinished_in_pre_proofs (SoftLibrary_unfinished state) name with
  | (Some pp, pps) =>

    match finish_pre_proof_seq pp with
    | Some entry =>

      match entry_in_lib_dec entry (RigidLibrary2lib state) with
      | inl p => MkUpdRes state [could_not_finish_proof_because_entry_exists_in_lib]
      | inr p => MkUpdRes (SoftLibrary_add_entry state entry pps) [finished_proof name]
      end

    | None => MkUpdRes state [could_not_finish_proof]
    end

  | (None, pps) => MkUpdRes state [could_not_finish_proof_because_could_not_find_lemma]
  end.

Definition SoftLibrary_change_unfinished {o}
           (state : @SoftLibrary o)
  : pre_proofs -> SoftLibrary :=
  match state with
  | MkSoftLibrary L _ => fun l => MkSoftLibrary L l
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

Definition apply_proof_step_isect_eq {o}
           (s : @pre_baresequent o)
           (y : NVar) : option (list pre_baresequent) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match NVin_dec y (vars_hyps H) with
    | inl p =>

      match C with
      | pre_concl_ext
          (oterm (Can NEquality)
                 [bterm [] (oterm (Can NIsect) [bterm [] a1, bterm [x1] b1]),
                  bterm [] (oterm (Can NIsect) [bterm [] a2, bterm [x2] b2]),
                  bterm [] (oterm (Can (NUni i)) [])]) =>

        let prf1 := pre_rule_isect_equality_hyp1 a1 a2 i H in
        let prf2 := pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H in
        (Some [prf1, prf2],
         applied_isect_eq_rule)

      | c => (None,
              could_not_apply_isect_eq_rule)
      end

    | _ => (None,
            could_not_apply_isect_eq_rule)
    end
  end.

Definition apply_proof_step_isect_member_formation {o}
           (s : @pre_baresequent o)
           (z : NVar)
           (i : nat) : option (list pre_baresequent) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match NVin_dec z (vars_hyps H) with
    | inl p =>

      match C with
      | pre_concl_ext (oterm (Can NIsect) [bterm [] A, bterm [x] B]) =>

        let prf1 := pre_rule_isect_member_formation_hyp1 z A x B H in
        let prf2 := pre_rule_isect_member_formation_hyp2 A i H in
        (Some [prf1, prf2],
         applied_isect_member_formation_rule)

      | c => (None,
              could_not_apply_isect_member_formation_rule)
      end

    | _ => (None,
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
        (p : H = snoc G (mk_hyp v A) ++ J)
        (q : NVin v (vars_hyps G)).

Arguments dhyps [o] [H] [v] _ _ _ _ _.

Lemma extend_decomp_hyps {o} :
  forall {H : @bhyps o} {G x J h},
    H = snoc G x ++ J
    -> h :: H = snoc (h :: G) x ++ J.
Proof.
  introv z; subst; reflexivity.
Defined.

Lemma extend_nvin_vars_hyps {o} :
  forall {v} {h} {H : @bhyps o},
    hvar h <> v
    -> NVin v (vars_hyps H)
    -> NVin v (vars_hyps (h :: H)).
Proof.
  introv d ni; simpl in *.
  unfold NVin, memvar in *; simpl in *.
  boolvar; auto.
  apply d in e; destruct e.
Defined.

Definition add_hyp2decomp_hyps {o}
           (h : @hypothesis o)
           {H : barehypotheses}
           {v : NVar}
           (w : hvar h <> v)
           (d : decomp_hyps H v) : decomp_hyps (h :: H) v :=
  match d with
  | dhyps G A J p q => dhyps (h :: G) A J (extend_decomp_hyps p) (extend_nvin_vars_hyps w q)
  end.

Lemma init_decomp_hyps {o} :
  forall (v : NVar) (A : @NTerm o) x H (p : v = x),
    mk_hyp v A :: H = snoc [] (mk_hyp x A) ++ H.
Proof.
  introv z; subst; reflexivity.
Defined.

Lemma init_nvin_vars_hyps {o} :
  forall (v : NVar), NVin v (@vars_hyps o []).
Proof.
  introv; simpl; reflexivity.
Defined.

Definition mk_init_decomp_hyps {o}
           (v : NVar)
           (A : @NTerm o)
           (x : NVar)
           (H : barehypotheses)
           (p : v = x) : decomp_hyps (mk_hyp v A :: H) x :=
  dhyps [] A H (init_decomp_hyps v A x H p) (@init_nvin_vars_hyps o v).

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
    | right p =>
      match find_hypothesis_eq hs x with
      | Some x => Some (add_hyp2decomp_hyps h p x)
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

Definition apply_proof_step_hypothesis {o}
           (s : @pre_baresequent o)
           (x : NVar) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match find_hypothesis_eq H x with
      | Some (dhyps G A J q w) =>

        match term_dec_op A T with
        | Some p =>

          (Some [],
           applied_hypothesis_rule)

        | None => (None,
                   could_not_apply_hypothesis_rule_because_different_types A T)
        end

      | None => (None,
                 could_not_apply_hypothesis_rule_because_couldnt_find_hypothesis)
      end

    | c => (None,
            could_not_apply_hypothesis_rule)
    end
  end.

Definition apply_proof_step_hypothesis_num {o}
           (s : @pre_baresequent o)
           (n : nat) : option (list pre_baresequent) * @DEBUG_MSG o :=
  match find_hypothesis_name_from_nat (pre_hyps s) n with
  | Some name => apply_proof_step_hypothesis s name
  | None => (None, could_not_apply_hypothesis_rule)
  end.

Definition apply_proof_step_cut {o}
           (s : @pre_baresequent o)
           (x : NVar)
           (B : NTerm) : option (list pre_baresequent) * @DEBUG_MSG o :=
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

            let prf1 := pre_rule_cut_hyp1 H B in
            let prf2 := pre_rule_cut_hyp2 H x B T in
            (Some [prf1, prf2],
             applied_cut_rule)

          | inr _ => (None,
                      could_not_apply_cut_rule)
          end

        | inr _ => (None,
                    could_not_apply_cut_rule)
        end

      | None => (None,
                 could_not_apply_cut_rule)
      end

    | c => (None,
            could_not_apply_cut_rule)
    end
  end.

Definition apply_proof_step_cequiv_computation {o}
           (lib : library)
           (s : @pre_baresequent o)
           (n : nat) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match T with
      | oterm (Can NCequiv) [bterm [] a, bterm [] b] =>

        let x := compute_atmost_k_steps lib n a in
        match term_dec_op x b with
        | Some p =>

          (Some [],
           applied_cequiv_computation_rule)

        | None => (None,
                   could_not_apply_cequiv_computation_rule_terms_not_equal a x b)
        end

      | t => (None,
              could_not_apply_cequiv_computation_rule_not_cequiv)
      end


    | c => (None,
            could_not_apply_cequiv_computation_rule)
    end
  end.

Definition apply_proof_step_cequiv_computation_aeq {o}
           (lib : library)
           (s : @pre_baresequent o)
           (n : nat) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match T with
      | oterm (Can NCequiv) [bterm [] a, bterm [] b] =>

        let x := compute_atmost_k_steps lib n a in
        match alpha_eq_dec_op x b with
        | Some p =>

          (Some [],
           applied_cequiv_computation_aeq_rule)

        | None => (None,
                   could_not_apply_cequiv_computation_aeq_rule_terms_not_equal a x b)
        end

      | t => (None,
              could_not_apply_cequiv_computation_aeq_rule_not_cequiv)
      end


    | c => (None,
            could_not_apply_cequiv_computation_aeq_rule)
    end
  end.

Definition apply_proof_step_cequiv_computation_atmost {o}
           (lib : library)
           (s : @pre_baresequent o)
           (n : nat) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match T with
      | oterm (Can NCequiv) [bterm [] a, bterm [] b] =>

        let x := compute_atmost_k_steps lib n a in
        match term_dec_op x b with
        | Some p =>

          (Some [],
           applied_cequiv_computation_atmost_rule)

        | None => (None,
                   could_not_apply_cequiv_computation_rule_terms_not_equal a x b)
        end

      | t => (None,
              could_not_apply_cequiv_computation_atmost_rule_not_cequiv)
      end


    | c => (None,
            could_not_apply_cequiv_computation_aeq_rule)
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

Definition apply_proof_step_cequiv_subst_concl {o}
           (s : @pre_baresequent o)
           (x : NVar)
           (X a b : NTerm) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
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

                let prf1 := pre_rule_cequiv_subst_hyp2 H a b in
                let prf2 := pre_rule_cequiv_subst_hyp1 H x X b in
                (Some [prf1,prf2],
                 applied_cequiv_subst_concl_rule)

              | inr _ => (None,
                          could_not_apply_cequiv_subst_concl_rule)
              end

            | inr _ => (None,
                        could_not_apply_cequiv_subst_concl_rule)
            end

          | None => (None,
                     could_not_apply_cequiv_subst_concl_rule)
          end

        | None => (None,
                   could_not_apply_cequiv_subst_concl_rule)
        end

      | None => (None,
                 could_not_apply_cequiv_subst_concl_rule_not_subst x X a b (subst X x a) T)
      end

    | c => (None,
            could_not_apply_cequiv_subst_concl_rule)
    end
  end.

Lemma pre_rule_cequiv_subst_hyp_concl_as_pre_baresequent {o} :
  forall (H : @bhyps o) G z X x a J T U
         (q : H = snoc G (mk_hyp z U) ++ J)
         (p : (subst X x a) = U),
    pre_rule_cequiv_subst_hyp_concl G z X x a J T
    = mk_pre_bseq H (pre_concl_ext T).
Proof.
  introv i j; subst; reflexivity.
Defined.

Definition apply_proof_step_cequiv_subst_hyp {o}
           (s : @pre_baresequent o)
           (z x : NVar)
           (X a b : NTerm) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match find_hypothesis_eq H z with
      | Some (dhyps G U J q w) =>

        match term_dec_op (subst X x a) U with
        | Some p =>

          match wf_term_dec_op a with
          | Some wfa =>

            match wf_term_dec_op b with
            | Some wfb =>

              match covered_decidable a (vars_hyps G) with
              | inl cova =>

                match covered_decidable b (vars_hyps G) with
                | inl covb =>

                  let prf1 := pre_rule_cequiv_subst_hyp_hyp2 G z X x a J b in
                  let prf2 := pre_rule_cequiv_subst_hyp_hyp1 G z X x b J T in
                  (Some [prf1,prf2],
                   applied_cequiv_subst_hyp_rule)

                | inr _ => (None,
                            could_not_apply_cequiv_subst_hyp_rule)
                end

              | inr _ => (None,
                          could_not_apply_cequiv_subst_hyp_rule)
              end

            | None => (None,
                       could_not_apply_cequiv_subst_hyp_rule)
            end

          | None => (None,
                     could_not_apply_cequiv_subst_hyp_rule)
          end

        | None => (None,
                   could_not_apply_cequiv_subst_hyp_rule)
        end

      | None => (None,
                 could_not_apply_cequiv_subst_hyp_rule_not_subst)
      end

    | c => (None,
            could_not_apply_cequiv_subst_hyp_rule)
    end
  end.

Definition apply_proof_step_cequiv_subst_hyp_num {o}
           (s : @pre_baresequent o)
           (n : nat)
           (x : NVar)
           (X a b : NTerm) : option (list pre_baresequent) * @DEBUG_MSG o :=
  match find_hypothesis_name_from_nat (pre_hyps s) n with
  | Some name => apply_proof_step_cequiv_subst_hyp s name x X a b
  | None => (None, could_not_apply_hypothesis_rule)
  end.

Lemma pre_rule_universe_equality_concl_as_pre_baresequent {o} :
  forall (H : @bhyps o) i j1 j2
         (p : j2 = j1),
    pre_rule_universe_equality_concl H j1 i
    = mk_pre_bseq H (mk_pre_concl (mk_equality (mk_uni j1) (mk_uni j2) (mk_uni i))).
Proof.
  introv e; subst; reflexivity.
Defined.

Definition apply_proof_step_universe_eq {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
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

          (Some [],
           applied_universe_eq_rule)

        | right _ => (None,
                      could_not_apply_universe_eq_rule_not_less_than_universe j1 i)
        end

      | right _ => (None,
                    could_not_apply_universe_eq_rule_not_equal_universes j2 j1)
      end

    | c => (None,
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

Definition apply_proof_step_hypothesis_eq {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
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
        | Some (dhyps G B J q w) =>

          match term_dec_op B A with
          | Some p =>

            (Some [],
             applied_hypothesis_equality_rule)

          | None => (None,
                     could_not_apply_hypothesis_equality_rule_terms_dont_match B A)
          end

        | None => (None,
                   could_not_apply_hypothesis_equality_rule_couldnt_find_hypothesis s)
        end

      | right _ => (None,
                    could_not_apply_hypothesis_equality_rule_variables_dont_match v2 v1)
      end

    | c => (None,
            could_not_apply_hypothesis_equality_rule_not_an_equality c)
    end
  end.

Inductive decomp_maybe_hidden_hyps {o} (H : @bhyps o) (v : NVar) :=
| dmhhyps (G : bhyps)
          (b : bool)
          (A : NTerm)
          (J : bhyps)
          (p : H = snoc G (mk_nlhyp b v A) ++ J).

Arguments dmhhyps [o] [H] [v] _ _ _ _ _.

Lemma init_decomp_maybe_hidden_hyps {o} :
  forall b (v : NVar) (A : @NTerm o) x H (p : v = x),
    mk_nlhyp b v A :: H = snoc [] (mk_nlhyp b x A) ++ H.
Proof.
  introv z; subst; reflexivity.
Defined.

Definition mk_init_decomp_maybe_hidden_hyps {o}
           (b : bool)
           (v : NVar)
           (A : @NTerm o)
           (x : NVar)
           (H : barehypotheses)
           (p : v = x) : decomp_maybe_hidden_hyps (mk_nlhyp b v A :: H) x :=
  dmhhyps [] b A H (init_decomp_maybe_hidden_hyps b v A x H p).

Definition add_hyp2decomp_maybe_hidden_hyps {o}
           (h : @hypothesis o)
           {H : barehypotheses}
           {v : NVar}
           (d : decomp_maybe_hidden_hyps H v) : decomp_maybe_hidden_hyps (h :: H) v :=
  match d with
  | dmhhyps G b A J p => dmhhyps (h :: G) b A J (extend_decomp_hyps p)
  end.

Fixpoint find_maybe_hidden_hypothesis_eq {o} (H : @bhyps o) (x : NVar)
  : option (decomp_maybe_hidden_hyps H x) :=
  match H with
  | [] => None
  | Build_hypothesis _ v hid A lvl as h :: hs =>
    match deq_nvar v x with
    | left p =>
      match lvl with
      | nolvl => Some (mk_init_decomp_maybe_hidden_hyps hid v A x hs p)
      | _ => None
      end
    | _ =>
      match find_maybe_hidden_hypothesis_eq hs x with
      | Some x => Some (add_hyp2decomp_maybe_hidden_hyps h x)
      | None => None
      end
    end
  end.

Lemma pre_rule_maybe_hidden_hypothesis_equality_concl_as_pre_baresequent {o} :
  forall (H : @bhyps o) G J x1 x2 A B b
         (q : H = snoc G (mk_nlhyp b x1 B) ++ J)
         (e : x2 = x1)
         (p : B = A),
    pre_rule_maybe_hidden_hypothesis_equality_concl G J A x1 b
    = mk_pre_bseq H (pre_concl_ext (mk_equality (mk_var x1) (mk_var x2) A)).
Proof.
  introv e1 e2 e3; subst; reflexivity.
Defined.

Definition apply_proof_step_maybe_hidden_hypothesis_eq {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (vterm v1),
                                bterm [] (vterm v2),
                                bterm [] A]) =>

      match deq_nvar v2 v1 with
      | left e =>

        match find_maybe_hidden_hypothesis_eq H v1 with
        | Some (dmhhyps G b B J q) =>

          match term_dec_op B A with
          | Some p =>

            (Some [],
             applied_maybe_hidden_hypothesis_equality_rule)

          | None => (None,
                     could_not_apply_maybe_hidden_hypothesis_equality_rule_terms_dont_match B A)
          end

        | None => (None,
                   could_not_apply_maybe_hidden_hypothesis_equality_rule_couldnt_find_hypothesis s)
        end

      | right _ => (None,
                    could_not_apply_maybe_hidden_hypothesis_equality_rule_variables_dont_match v2 v1)
      end

    | c => (None,
            could_not_apply_maybe_hidden_hypothesis_equality_rule_not_an_equality c)
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

Definition apply_proof_step_unhide_equality {o}
           (s : @pre_baresequent o)
           (x : NVar) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] t1,
                                bterm [] t2,
                                bterm [] T]) =>

      match find_hhypothesis_eq H x with
      | Some (dhhyps G A J q) =>

        let prf := pre_rule_unhide_equality_hyp G J x A t1 t2 T in
        (Some [prf],
         applied_unhide_equality_rule)

      | None => (None,
                 could_not_apply_unhide_equality_rule)
      end

    | c => (None,
            could_not_apply_unhide_equality_rule)
    end
  end.

Definition apply_proof_step_equality_equality {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (oterm (Can NEquality) [bterm [] a1, bterm [] a2, bterm [] A]),
                                bterm [] (oterm (Can NEquality) [bterm [] b1, bterm [] b2, bterm [] B]),
                                bterm [] (oterm (Can (NUni i)) [])]) =>

        let prf1 := pre_rule_equality_equality_hyp1 H A B i in
        let prf2 := pre_rule_equality_equality_hyp2 H a1 b1 A in
        let prf3 := pre_rule_equality_equality_hyp2 H a2 b2 A in
        (Some [prf1, prf2, prf3],
         applied_equality_equality_rule)

    | c => (None,
            could_not_apply_equality_equality_rule)
    end
  end.

Definition apply_proof_step_equality_equality_base {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (oterm (Can NEquality) [bterm [] a1, bterm [] a2, bterm [] A]),
                                bterm [] (oterm (Can NEquality) [bterm [] b1, bterm [] b2, bterm [] B]),
                                bterm [] (oterm (Can (NUni i)) [])]) =>

        let prf1 := pre_rule_equality_equality_hyp1 H A B i in
        let prf2 := pre_rule_equality_equality_hyp3 H a1 b1 in
        let prf3 := pre_rule_equality_equality_hyp3 H a2 b2 in
        (Some [prf1, prf2, prf3],
         applied_equality_equality_base_rule)

    | c => (None,
            could_not_apply_equality_equality_base_rule)
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

Definition apply_proof_step_integer_equality {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (oterm (Can (Nint n1)) []),
                                bterm [] (oterm (Can (Nint n2)) []),
                                bterm [] (oterm (Can NInt) [])]) =>

      match Z.eq_dec n2 n1 with
      | left p =>

        (Some [],
         applied_integer_equality_rule)

      | right _ => (None,
                    could_not_apply_integer_equality_rule)
      end

    | c => (None,
            could_not_apply_integer_equality_rule)
    end
  end.

Definition apply_proof_step_introduction {o}
           (s : @pre_baresequent o)
           (t : @NTerm o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
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

            let prf1 := pre_rule_introduction_hyp H T t in
            (Some [prf1],
             applied_introduction_rule)

          | inr _ => (None,
                      could_not_apply_introduction_rule)
          end

        | inr _ => (None,
                    could_not_apply_introduction_rule)
        end

      | None => (None,
                  could_not_apply_introduction_rule)
      end

    | c => (None,
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

Definition apply_proof_step_lemma {o}
           (ctxt : ProofContext)
           (s    : @pre_baresequent o)
           (name : LemmaName) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      let nc := MkNamedConcl name T in

      match find_named_concl nc (PC_conclusions ctxt) with
      | Some i =>

        (Some [],
         applied_lemma_rule)

      | None => (None,
                 could_not_apply_lemma_rule)
      end

    | c => (None,
            could_not_apply_lemma_rule)
    end
  end.

Definition decidable_bool_true :
  forall (b : bool), decidable (b = true).
Proof.
  introv; destruct b;[left|right]; auto.
  intro xx; inversion xx.
Defined.

Definition all_abstractions_can_be_unfolded_dec {o} :
  forall lib abs (t : @NTerm o),
    decidable (all_abstractions_can_be_unfolded lib abs t).
Proof.
  introv; apply decidable_bool_true.
Defined.

Definition apply_proof_step_unfold_abstractions {o}
           (lib : library)
           (s : @pre_baresequent o)
           (names : list opname) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match all_abstractions_can_be_unfolded_dec lib names T with
      | inl unf =>

        let prf := pre_rule_unfold_abstractions_hyp lib names T H in
        (Some [prf],
         applied_unfold_abstractions_rule)

      | inr _ => (None,
                  could_not_apply_unfold_abstractions_rule_not_all_unfoldable)
      end

    | c => (None,
            could_not_apply_unfold_abstractions_rule)
    end
  end.

Lemma pre_rule_rev_unfold_abstractions_as_pre_baresequent {o} :
  forall {lib} {names}
         (H : @bhyps o) a b
         (p : a = unfold_abstractions lib names b),
    pre_rule_unfold_abstractions_hyp lib names b H
    = mk_pre_bseq H (pre_concl_ext a).
Proof.
  introv p; subst; reflexivity.
Defined.

Definition apply_proof_step_rev_unfold_abstractions {o}
           (lib : library)
           (s : @pre_baresequent o)
           (names : list opname)
           (b : NTerm) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext a =>

      match term_dec_op a (unfold_abstractions lib names b) with
      | Some p =>

        match wf_term_dec_op b with
        | Some wfb =>

          match covered_decidable b (vars_hyps H) with
          | inl covb =>

            match all_abstractions_can_be_unfolded_dec lib names b with
            | inl unf =>

              let prf := pre_rule_unfold_abstractions_concl b H in
              (Some [prf],
               applied_rev_unfold_abstractions_rule)

            | inr _ => (None,
                        could_not_apply_rev_unfold_abstractions_rule_not_all_unfoldable)
            end

          | inr _ => (None,
                      could_not_apply_rev_unfold_abstractions_rule_not_all_unfoldable)
          end

        | None => (None,
                   could_not_apply_rev_unfold_abstractions_rule_not_all_unfoldable)
        end

      | None => (None,
                 could_not_apply_rev_unfold_abstractions_rule_not_all_unfoldable)
      end

    | c => (None,
            could_not_apply_rev_unfold_abstractions_rule)
    end
  end.

Definition apply_proof_step_axiom_equality {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (oterm (Can NAxiom) []),
                                bterm [] (oterm (Can NAxiom) []),
                                bterm [] (oterm (Can NEquality) [bterm [] a,
                                                                 bterm [] b,
                                                                 bterm [] T])]) =>

      let prf := pre_rule_axiom_equality_hyp a b T H in
      (Some [prf],
       applied_axiom_equality_rule)

    | c => (None,
            could_not_apply_axiom_equality_rule)
    end
  end.

Lemma pre_rule_thin_concl_as_pre_baresequent {o} :
  forall (H : @bhyps o) G x A J C
         (q : H = snoc G (mk_hyp x A) ++ J),
    pre_rule_thin_concl G x A J C
    = mk_pre_bseq H (pre_concl_ext C).
Proof.
  introv e1; subst; reflexivity.
Defined.

Definition apply_proof_step_thin {o}
           (s : @pre_baresequent o)
           (x : NVar) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match find_hypothesis_eq H x with
      | Some (dhyps G A J q w) =>

        match NVin_dec x (free_vars_hyps J) with
        | inl nixJ =>

          match NVin_dec x (free_vars T) with
          | inl nixC =>

            let prf := pre_rule_thin_hyp G J T in
            (Some [prf],
             applied_thin_rule)

          | inr _ => (None,
                      could_not_apply_thin_rule)
          end

        | inr _ => (None,
                    could_not_apply_thin_rule)
        end

      | None => (None,
                 could_not_apply_thin_rule)
      end

    | c => (None,
            could_not_apply_thin_rule)
    end
  end.

Definition apply_proof_step_thin_num {o}
           (s : @pre_baresequent o)
           (n : nat) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match find_hypothesis_name_from_nat (pre_hyps s) n with
  | Some name => apply_proof_step_thin s name
  | None => (None, could_not_apply_thin_rule)
  end.

Definition apply_proof_step_function_equality {o}
           (s : @pre_baresequent o)
           (y : NVar) : option (list pre_baresequent) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match NVin_dec y (vars_hyps H) with
    | inl p =>

      match C with
      | pre_concl_ext
          (oterm (Can NEquality)
                 [bterm [] (oterm (Can NFunction) [bterm [] a1, bterm [x1] b1]),
                  bterm [] (oterm (Can NFunction) [bterm [] a2, bterm [x2] b2]),
                  bterm [] (oterm (Can (NUni i)) [])]) =>

        let prf1 := pre_rule_function_equality_hyp1 H a1 a2 i in
        let prf2 := pre_rule_function_equality_hyp2 H y a1 b1 x1 b2 x2 i in
        (Some [prf1,prf2],
         applied_function_equality_rule)

      | c => (None,
              could_not_apply_function_equality_rule)
      end

    | _ => (None,
            could_not_apply_function_equality_rule)
    end
  end.

Lemma pre_rule_apply_equality_as_pre_baresequent {o} :
  forall (H : @bhyps o) B f1 f2 t1 t2 x U
         (p : subst B x t1 = U),
    pre_rule_apply_equality_concl H f1 t1 f2 t2 B x
    = mk_pre_bseq H (pre_concl_ext (mk_equality (mk_apply f1 t1) (mk_apply f2 t2) U)).
Proof.
  introv p; subst; reflexivity.
Defined.

Definition apply_proof_step_apply_equality {o}
           (s : @pre_baresequent o)
           (x : NVar)
           (A B : NTerm) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
          (oterm (Can NEquality)
                 [bterm [] (oterm (NCan NApply) [bterm [] f1, bterm [] t1]),
                  bterm [] (oterm (NCan NApply) [bterm [] f2, bterm [] t2]),
                  bterm [] U]) =>

      match term_dec_op (subst B x t1) U with
      | Some p =>

        match wf_term_dec_op A with
        | Some wfA =>

          match covered_decidable A (vars_hyps H) with
          | inl covA =>

            let prf1 := pre_rule_apply_equality_hyp1 H f1 f2 A x B in
            let prf2 := pre_rule_apply_equality_hyp2 H t1 t2 A in
            (Some [prf1,prf2],
             applied_apply_equality_rule)

          | inr _ => (None,
                      could_not_apply_apply_equality_rule)
          end

        | None => (None,
                   could_not_apply_apply_equality_rule)
        end

      | None => (None,
                 could_not_apply_apply_equality_rule)
      end

    | c => (None,
            could_not_apply_apply_equality_rule)
    end
  end.

Lemma pre_rule_isect_elimination_as_pre_baresequent {o} :
  forall (H : @bhyps o) A B C f x G J
         (q : H = snoc G (mk_hyp f (mk_isect A x B)) ++ J),
    pre_rule_isect_elimination_concl A B C f x G J
    = mk_pre_bseq H (pre_concl_ext C).
Proof.
  introv p; subst; reflexivity.
Defined.

Definition apply_proof_step_isect_elimination {o}
           (s : @pre_baresequent o)
           (n : nat)
           (a : NTerm)
           (f z : NVar) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match find_hypothesis_eq H f with
      | Some (dhyps G (oterm (Can NIsect) [bterm [] A, bterm [x] B]) J q w) =>

        match wf_term_dec_op a with
        | Some wfa =>

          match covered_decidable a (snoc (vars_hyps G) f ++ vars_hyps J) with
          | inl cova =>

            match NVin_dec z (vars_hyps G) with
            | inl nizG =>

              match NVin_dec z (vars_hyps J) with
              | inl nizJ =>

                match deq_nvar z f with
                | right dzf =>

                  let prf1 := pre_rule_isect_elimination_hyp1 A B a f x G J in
                  let prf2 := pre_rule_isect_elimination_hyp2 A B T a f x z G J in
                  (Some [prf1,prf2],
                   applied_isect_elimination_rule)

                | left _ => (None,
                              could_not_apply_isect_elimination_rule)
                end

              | inr _ => (None,
                          could_not_apply_isect_elimination_rule)
              end

            | inr _ => (None,
                        could_not_apply_isect_elimination_rule)
            end

          | inr _ => (None,
                      could_not_apply_isect_elimination_rule)
          end

        | None => (None,
                   could_not_apply_isect_elimination_rule)
        end

      | _ => (None,
              could_not_apply_isect_elimination_rule)
      end

    | c => (None,
            could_not_apply_isect_elimination_rule)
    end
  end.

Definition apply_proof_step_isect_elimination_num {o}
           (s : @pre_baresequent o)
           (n : nat)
           (a : NTerm)
           (z : NVar) : option (list pre_baresequent) * @DEBUG_MSG o :=
  match find_hypothesis_name_from_nat (pre_hyps s) n with
  | Some f => apply_proof_step_isect_elimination s n a f z
  | None => (None, could_not_apply_isect_elimination_rule)
  end.

Lemma pre_rule_isect_elimination2_as_pre_baresequent {o} :
  forall (H : @bhyps o) A B C f x G J
         (q : H = snoc G (mk_hyp f (mk_isect A x B)) ++ J),
    pre_rule_isect_elimination2_concl A B C f x G J
    = mk_pre_bseq H (pre_concl_ext C).
Proof.
  introv p; subst; reflexivity.
Defined.

Definition apply_proof_step_isect_elimination2 {o}
           (s : @pre_baresequent o)
           (n : nat)
           (a : NTerm)
           (f z y : NVar) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext T =>

      match find_hypothesis_eq H f with
      | Some (dhyps G (oterm (Can NIsect) [bterm [] A, bterm [x] B]) J q w) =>

        match wf_term_dec_op a with
        | Some wfa =>

          match covered_decidable a (snoc (vars_hyps G) f ++ vars_hyps J) with
          | inl cova =>

            match NVin_dec z (vars_hyps G) with
            | inl nizG =>

              match NVin_dec z (vars_hyps J) with
              | inl nizJ =>

                match NVin_dec y (vars_hyps G) with
                | inl niyG =>

                  match NVin_dec y (vars_hyps J) with
                  | inl niyJ =>

                    match deq_nvar z f with
                    | right dzf =>

                      match deq_nvar z y with
                      | right dzy =>

                        match deq_nvar y f with
                        | right dyf =>

                          let prf1 := pre_rule_isect_elimination_hyp1 A B a f x G J in
                          let prf2 := pre_rule_isect_elimination2_hyp2 A B T a f x y z G J in
                          (Some [prf1,prf2],
                           applied_isect_elimination2_rule)

                        | left _ => (None,
                                     could_not_apply_isect_elimination2_rule_variables_not_different3 y f)
                        end

                      | left _ => (None,
                                   could_not_apply_isect_elimination2_rule_variables_not_different2 z y)
                      end

                    | left _ => (None,
                                 could_not_apply_isect_elimination2_rule_variables_not_different1 z f )
                    end

                  | inr _ => (None,
                              could_not_apply_isect_elimination2_rule_variable_in_hypotheses4 y (vars_hyps J))
                  end

                | inr _ => (None,
                            could_not_apply_isect_elimination2_rule_variable_in_hypotheses3 y (vars_hyps G))
                end

              | inr _ => (None,
                          could_not_apply_isect_elimination2_rule_variable_in_hypotheses2 z (vars_hyps J))
              end

            | inr _ => (None,
                        could_not_apply_isect_elimination2_rule_variable_in_hypotheses1 z (vars_hyps G))
            end

          | inr _ => (None,
                      could_not_apply_isect_elimination2_rule_not_covered a (snoc (vars_hyps G) f ++ vars_hyps J))
          end

        | None => (None,
                   could_not_apply_isect_elimination2_rule_not_well_formed a)
        end

      | _ => (None,
              could_not_apply_isect_elimination2_rule_hypothesis_not_found f (vars_hyps H))
      end

    | c => (None,
            could_not_apply_isect_elimination2_rule)
    end
  end.

Definition apply_proof_step_isect_elimination2_num {o}
           (s : @pre_baresequent o)
           (n : nat)
           (a : NTerm)
           (z y : NVar) : option (list pre_baresequent) * @DEBUG_MSG o :=
  match find_hypothesis_name_from_nat (pre_hyps s) n with
  | Some f => apply_proof_step_isect_elimination2 s n a f z y
  | None => (None, could_not_apply_isect_elimination2_rule)
  end.

Definition apply_proof_step_isect_member_equality {o}
           (s : @pre_baresequent o)
           (z : NVar)
           (i : nat) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] t1,
                                bterm [] t2,
                                bterm [] (oterm (Can NIsect) [bterm [] A,
                                                              bterm [x] B])]) =>

      match NVin_dec z (vars_hyps H) with
      | inl nizH =>

        let prf1 := pre_rule_isect_member_equality_hyp1 H z A t1 t2 B x in
        let prf2 := pre_rule_isect_member_equality_hyp2 H A i in
        (Some [prf1,prf2],
         applied_isect_member_equality_rule)

      | inr _ => (None,
                  could_not_apply_isect_member_equality_rule)
      end

    | c => (None,
            could_not_apply_isect_member_equality_rule)
    end
  end.

Definition decidable_le_true :
  forall (i j : nat), decidable (i <=? j = true).
Proof.
  introv; apply decidable_bool_true.
Defined.

Lemma pre_rule_cumulativity_as_pre_baresequent {o} :
  forall (H : @bhyps o) T T' j
         (eqts : T' = T),
    pre_rule_cumulativity_concl H T j
    = mk_pre_bseq H (pre_concl_ext (mk_equality T T' (mk_uni j))).
Proof.
  introv p; subst; reflexivity.
Defined.

Definition apply_proof_step_cumulativity {o}
           (s : @pre_baresequent o)
           (i : nat) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] T,
                                bterm [] T',
                                bterm [] (oterm (Can (NUni j)) [])]) =>

      match term_dec_op T' T with
      | Some eqts =>

        match decidable_le_true i j with
        | inl leij =>

          let prf1 := pre_rule_cumulativity_hyp H T i in
          (Some [prf1],
           applied_cumulativity_rule)

        | inr _ => (None,
                    could_not_apply_cumulativity_rule)
        end

      | None => (None,
                 could_not_apply_cumulativity_rule)
      end

    | c => (None,
            could_not_apply_cumulativity_rule)
    end
  end.

Definition apply_proof_step_equality_symmetry {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext (oterm (Can NEquality) [bterm [] a, bterm [] b, bterm [] T]) =>

      let prf1 := pre_rule_equality_seq H b a T in
      (Some [prf1],
       applied_isect_member_equality_rule)

    | c => (None,
            could_not_apply_equality_symmetry_rule)
    end
  end.

Definition apply_proof_step_equality_transitivity {o}
           (s : @pre_baresequent o)
           (c : NTerm): option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext (oterm (Can NEquality) [bterm [] a, bterm [] b, bterm [] T]) =>

      match wf_term_dec_op c with
      | Some wfc =>

        match covered_decidable c (vars_hyps H) with
        | inl covc =>

          let prf1 := pre_rule_equality_seq H a c T in
          let prf2 := pre_rule_equality_seq H c b T in
          (Some [prf1,prf2],
           applied_equality_transitivity_rule)

        | inr _ => (None,
                    could_not_apply_equality_transitivity_rule)
        end

      | None => (None,
                 could_not_apply_equality_transitivity_rule)
      end

    | c => (None,
            could_not_apply_equality_transitivity_rule)
    end
  end.

Definition apply_proof_step_cequiv_transitivity {o}
           (s : @pre_baresequent o)
           (c : NTerm): option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext (oterm (Can NCequiv) [bterm [] a, bterm [] b]) =>

      match wf_term_dec_op c with
      | Some wfc =>

        match covered_decidable c (vars_hyps H) with
        | inl covc =>

          let prf1 := pre_rule_cequiv_seq H a c in
          let prf2 := pre_rule_cequiv_seq H c b in
          (Some [prf1,prf2],
           applied_cequiv_transitivity_rule)

        | inr _ => (None,
                    could_not_apply_cequiv_transitivity_rule)
        end

      | None => (None,
                 could_not_apply_cequiv_transitivity_rule)
      end

    | c => (None,
            could_not_apply_cequiv_transitivity_rule)
    end
  end.

Lemma pre_rule_approx_refl_as_pre_baresequent {o} :
  forall (H : @bhyps o) a a'
         (eqts : a' = a),
    pre_rule_approx_refl_concl a H
    = mk_pre_bseq H (pre_concl_ext (mk_approx a a')).
Proof.
  introv p; subst; reflexivity.
Defined.

Definition apply_proof_step_approx_refl {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext (oterm (Can NApprox) [bterm [] a, bterm [] a']) =>

      match term_dec_op a' a with
      | Some eqas =>

        (Some [],
         applied_approx_refl_rule)

      | None => (None,
                 could_not_apply_approx_refl_rule)
      end

    | c => (None,
            could_not_apply_approx_refl_rule)
    end
  end.

Lemma pre_rule_cequiv_refl_as_pre_baresequent {o} :
  forall (H : @bhyps o) a a'
         (eqts : a' = a),
    pre_rule_cequiv_refl_concl a H
    = mk_pre_bseq H (pre_concl_ext (mk_cequiv a a')).
Proof.
  introv p; subst; reflexivity.
Defined.

Definition apply_proof_step_cequiv_refl {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext (oterm (Can NCequiv) [bterm [] a, bterm [] a']) =>

      match term_dec_op a' a with
      | Some eqas =>

        (Some [],
         applied_cequiv_refl_rule)

      | None => (None,
                 could_not_apply_cequiv_refl_rule_terms_dont_match a a')
      end

    | c => (None,
            could_not_apply_cequiv_refl_rule_not_a_cequiv C)
    end
  end.

Definition apply_proof_step_cequiv_alpha_eq {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext (oterm (Can NCequiv) [bterm [] a, bterm [] b]) =>

      match alpha_eq_dec_op a b with
      | Some aeq =>

        (Some [],
         applied_cequiv_alpha_eq_rule)

      | None => (None,
                 could_not_apply_cequiv_alpha_eq_rule_terms_dont_match a b)
      end

    | c => (None,
            could_not_apply_cequiv_alpha_eq_rule_not_a_cequiv C)
    end
  end.

Definition apply_proof_step_cequiv_approx {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext (oterm (Can NCequiv) [bterm [] a, bterm [] b]) =>

      let prf1 := pre_rule_cequiv_approx_hyp a b H in
      let prf2 := pre_rule_cequiv_approx_hyp b a H in
      (Some [prf1, prf2],
       applied_cequiv_approx_rule)

    | c => (None,
            could_not_apply_cequiv_approx_rule)
    end
  end.

Definition apply_proof_step_approx_eq {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (oterm (Can NApprox) [bterm [] a1, bterm [] a2]),
                                bterm [] (oterm (Can NApprox) [bterm [] b1, bterm [] b2]),
                                bterm [] (oterm (Can (NUni i)) [])]) =>

        let prf1 := pre_rule_eq_base_hyp a1 b1 H in
        let prf2 := pre_rule_eq_base_hyp a2 b2 H in
        (Some [prf1, prf2],
         applied_approx_eq_rule)

    | c => (None,
            could_not_apply_approx_eq_rule)
    end
  end.

Definition apply_proof_step_cequiv_eq {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (oterm (Can NCequiv) [bterm [] a1, bterm [] a2]),
                                bterm [] (oterm (Can NCequiv) [bterm [] b1, bterm [] b2]),
                                bterm [] (oterm (Can (NUni i)) [])]) =>

        let prf1 := pre_rule_eq_base_hyp a1 b1 H in
        let prf2 := pre_rule_eq_base_hyp a2 b2 H in
        (Some [prf1, prf2],
         applied_cequiv_eq_rule)

    | c => (None,
            could_not_apply_cequiv_eq_rule)
    end
  end.

Definition apply_proof_step_base_equality {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (oterm (Can NBase) []),
                                bterm [] (oterm (Can NBase) []),
                                bterm [] (oterm (Can (NUni i)) [])]) =>

        (Some [],
         applied_base_equality_rule)

    | c => (None,
            could_not_apply_base_equality_rule)
    end
  end.

Definition apply_proof_step_int_equality {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] (oterm (Can NInt) []),
                                bterm [] (oterm (Can NInt) []),
                                bterm [] (oterm (Can (NUni i)) [])]) =>

        (Some [],
         applied_int_equality_rule)

    | c => (None,
            could_not_apply_int_equality_rule)
    end
  end.

Definition apply_proof_step_base_closed {o}
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match H with
    | [] =>

      match C with
      | pre_concl_ext
          (oterm (Can NEquality) [bterm [] a,
                                  bterm [] b,
                                  bterm [] (oterm (Can NBase) [])]) =>

        match term_dec_op a b with
        | Some eqas =>

          (Some [],
           applied_base_closed_rule)

        | None => (None,
                   could_not_apply_base_closed_rule_terms_differ a b)
        end

      | c => (None,
              could_not_apply_base_closed_rule_not_an_equality C)
      end

    | _ => (None,
            could_not_apply_base_closed_rule_non_empty_hypotheses H)
    end
  end.

Definition apply_proof_step_base_closed2 {o}
           (ctxt : ProofContext)
           (s : @pre_baresequent o) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match H with
    | [] =>

      match C with
      | pre_concl_ext ((oterm (Abs _) _) as t) =>

        let x := compute_atmost_k_steps ctxt 1 t in

        match x with
        | oterm (Can NEquality) [bterm [] a,
                                 bterm [] b,
                                 bterm [] (oterm (Can NBase) [])] =>

          match term_dec_op a b with
          | Some eqas =>

            (Some [],
             applied_base_closed2_rule)

          | None => (None,
                     could_not_apply_base_closed2_rule_terms_differ a b)
          end

        | _ => (None,
                could_not_apply_base_closed2_rule_not_an_equality C)
        end

      | c => (None,
              could_not_apply_base_closed2_rule_not_an_equality C)
      end

    | _ => (None,
            could_not_apply_base_closed2_rule_non_empty_hypotheses H)
    end
  end.

Definition apply_proof_step_lemma_with_extract {o}
           (ctxt : ProofContext)
           (s    : @pre_baresequent o)
           (name : LemmaName) : option (list (@pre_baresequent o)) * @DEBUG_MSG o :=
  match s with
  | MkPreBaresequent H C =>

    match C with
    | pre_concl_ext
        (oterm (Can NEquality) [bterm [] a, bterm [] b, bterm [] T]) =>

      match term_dec_op a b with
      | Some eqas =>

        let nc := MkNamedConcl name T in
        let x := (*compute_atmost_k_steps ctxt 1*) (LemmaName2extract name) in

        match alpha_eq_dec_op x a with
        | Some aeq =>

          match find_named_concl nc (PC_conclusions ctxt) with
          | Some i =>

            (Some [],
             applied_lemma_with_extract_rule)

          | None => (None,
                     could_not_apply_lemma_with_extract_rule_named_concl_not_found)
          end

        | None => (None,
                   could_not_apply_lemma_with_extract_rule_not_alpha_eq x a)
        end

      | None => (None,
                 could_not_apply_lemma_with_extract_rule_members_not_equal a b)
      end

    | c => (None,
            could_not_apply_lemma_with_extract_rule)
    end
  end.

Definition apply_proof_step {o}
           (ctxt : ProofContext)
           (s    : @pre_baresequent o)
           (step : proof_step) : option (list pre_baresequent) * DEBUG_MSG :=
  match step with
  | proof_step_base_closed                      => apply_proof_step_base_closed s
  | proof_step_base_closed2                     => apply_proof_step_base_closed2 ctxt s
  | proof_step_base_equality                    => apply_proof_step_base_equality s
  | proof_step_int_equality                     => apply_proof_step_int_equality s
  | proof_step_isect_equality y                 => apply_proof_step_isect_eq s y
  | proof_step_isect_member_formation z i       => apply_proof_step_isect_member_formation s z i
  | proof_step_hypothesis x                     => apply_proof_step_hypothesis s x
  | proof_step_hypothesis_num x                 => apply_proof_step_hypothesis_num s x
  | proof_step_cut x B                          => apply_proof_step_cut s x B
  | proof_step_cequiv_computation n             => apply_proof_step_cequiv_computation ctxt s n
  | proof_step_cequiv_computation_aeq n         => apply_proof_step_cequiv_computation_aeq ctxt s n
  | proof_step_cequiv_computation_atmost n      => apply_proof_step_cequiv_computation_atmost ctxt s n
  | proof_step_unfold_abstractions names        => apply_proof_step_unfold_abstractions ctxt s names
  | proof_step_rev_unfold_abstractions names a  => apply_proof_step_rev_unfold_abstractions ctxt s names a
  | proof_step_cequiv_subst_concl x C a b       => apply_proof_step_cequiv_subst_concl s x C a b
  | proof_step_cequiv_subst_hyp z x C a b       => apply_proof_step_cequiv_subst_hyp s z x C a b
  | proof_step_cequiv_subst_hyp_num n x C a b   => apply_proof_step_cequiv_subst_hyp_num s n x C a b
  | proof_step_universe_equality                => apply_proof_step_universe_eq s
  | proof_step_hypothesis_equality              => apply_proof_step_hypothesis_eq s
  | proof_step_maybe_hidden_hypothesis_equality => apply_proof_step_maybe_hidden_hypothesis_eq s
  | proof_step_unhide_equality x                => apply_proof_step_unhide_equality s x
  | proof_step_equality_equality                => apply_proof_step_equality_equality s
  | proof_step_equality_equality_base           => apply_proof_step_equality_equality_base s
  | proof_step_integer_equality                 => apply_proof_step_integer_equality s
  | proof_step_introduction t                   => apply_proof_step_introduction s t
  | proof_step_lemma name                       => apply_proof_step_lemma ctxt s name
  | proof_step_lemma_with_extract name          => apply_proof_step_lemma_with_extract ctxt s name
  | proof_step_axiom_equality                   => apply_proof_step_axiom_equality s
  | proof_step_thin x                           => apply_proof_step_thin s x
  | proof_step_thin_num n                       => apply_proof_step_thin_num s n
  | proof_step_function_equality y              => apply_proof_step_function_equality s y
  | proof_step_apply_equality x A B             => apply_proof_step_apply_equality s x A B
  | proof_step_isect_elimination n a z          => apply_proof_step_isect_elimination_num s n a z
  | proof_step_isect_elimination2 n a z y       => apply_proof_step_isect_elimination2_num s n a z y
  | proof_step_isect_member_equality x i        => apply_proof_step_isect_member_equality s x i
  | proof_step_cumulativity j                   => apply_proof_step_cumulativity s j
  | proof_step_equality_symmetry                => apply_proof_step_equality_symmetry s
  | proof_step_equality_transitivity c          => apply_proof_step_equality_transitivity s c
  | proof_step_cequiv_transitivity c            => apply_proof_step_cequiv_transitivity s c
  | proof_step_approx_refl                      => apply_proof_step_approx_refl s
  | proof_step_cequiv_refl                      => apply_proof_step_cequiv_refl s
  | proof_step_cequiv_alpha_eq                  => apply_proof_step_cequiv_alpha_eq s
  | proof_step_cequiv_approx                    => apply_proof_step_cequiv_approx s
  | proof_step_approx_eq                        => apply_proof_step_approx_eq s
  | proof_step_cequiv_eq                        => apply_proof_step_cequiv_eq s
  end.

(* FIX *)
Fixpoint update_pre_proof {o}
         (ctxt  : @ProofContext o)
         (p     : @pre_proof o)
         (oaddr : address)
         (addr  : address)
         (step  : proof_step) : pre_proof * DEBUG_MSG :=
  match addr with
  | [] =>
    let s := pre_proof2bseq p in
    match apply_proof_step ctxt s step with
    | (Some l, msg) => (pre_proof_node step s (map pre_proof_hole l), msg)
    | (None, msg) => (p, msg)
    end
  | k :: addr =>
    match p with
    | pre_proof_hole _ => (p, could_not_apply_update_because_no_hole_at_address)
    | pre_proof_node n c ps =>
      match k, ps with
      | 1, p1 :: ps =>
        let (p1',msg) := update_pre_proof ctxt p1 oaddr addr step in
        (pre_proof_node n c (p1' :: ps), msg)
      | 2, p1 :: p2 :: ps =>
        let (p2',msg) := update_pre_proof ctxt p2 oaddr addr step in
        (pre_proof_node n c (p1 :: p2' :: ps), msg)
      | 3, p1 :: p2 :: p3 :: ps =>
        let (p3',msg) := update_pre_proof ctxt p3 oaddr addr step in
        (pre_proof_node n c (p1 :: p2 :: p3' :: ps), msg)
      | _, _ => (p, could_not_apply_update_because_bad_address oaddr addr)
      end
    end
  end.

(*Fixpoint update_pre_proof {o}
         (lib  : library)
         {s    : @pre_baresequent o}
         (p    : pre_proof s)
         (addr : address)
         (step : proof_step) : pre_proof s * DEBUG_MSG :=
  match addr with
  | [] => apply_proof_step lib s step
  | _ =>
    match p with
    | pre_proof_from_ctxt c H =>
      (pre_proof_from_ctxt c H,
       could_not_apply_update_because_no_hole_at_address)

    | pre_proof_hole s => apply_proof_step lib s step

    | pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2', msg)
      | _ => (pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_isect_member_formation A x B z i H nizH prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_isect_member_formation A x B z i H nizH prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_isect_member_formation A x B z i H nizH prf1 prf2', msg)
      | _ => (pre_proof_isect_member_formation A x B z i H nizH prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_approx_refl a H =>
      (pre_proof_approx_refl a H, could_not_apply_update_because_no_hole_at_address)

    | pre_proof_cequiv_refl a H =>
      (pre_proof_cequiv_refl a H, could_not_apply_update_because_no_hole_at_address)

    | pre_proof_cequiv_alpha_eq a b H aeq =>
      (pre_proof_cequiv_alpha_eq a b H aeq, could_not_apply_update_because_no_hole_at_address)

    | pre_proof_cequiv_approx a b H prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_cequiv_approx a b H prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_cequiv_approx a b H prf1 prf2', msg)
      | _ => (pre_proof_cequiv_approx a b H prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_approx_eq a1 a2 b1 b2 i H prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_approx_eq a1 a2 b1 b2 i H prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_approx_eq a1 a2 b1 b2 i H prf1 prf2', msg)
      | _ => (pre_proof_approx_eq a1 a2 b1 b2 i H prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_cequiv_eq a1 a2 b1 b2 i H prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_cequiv_eq a1 a2 b1 b2 i H prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_cequiv_eq a1 a2 b1 b2 i H prf1 prf2', msg)
      | _ => (pre_proof_cequiv_eq a1 a2 b1 b2 i H prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_cut B C x H wfB covB nixH prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_cut B C x H wfB covB nixH prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_cut B C x H wfB covB nixH prf1 prf2', msg)
      | _ => (pre_proof_cut B C x H wfB covB nixH prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_hypothesis x A G J =>
      (pre_proof_hypothesis x A G J,
       could_not_apply_update_because_no_hole_at_address)

    | pre_proof_cequiv_subst_concl C x a b H wfa wfb cova covb prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_cequiv_subst_concl C x a b H wfa wfb cova covb prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_cequiv_subst_concl C x a b H wfa wfb cova covb prf1 prf2', msg)
      | _ => (pre_proof_cequiv_subst_concl C x a b H wfa wfb cova covb prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb prf1 prf2', msg)
      | _ => (pre_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_cequiv_computation _ a b H r =>
      (pre_proof_cequiv_computation _ a b H r,
       could_not_apply_update_because_no_hole_at_address)

    | pre_proof_cequiv_computation_aeq _ a b c H r aeq =>
      (pre_proof_cequiv_computation_aeq _ a b c H r aeq,
       could_not_apply_update_because_no_hole_at_address)

    | pre_proof_cequiv_computation_atmost _ a b n H r =>
      (pre_proof_cequiv_computation_atmost _ a b n H r,
       could_not_apply_update_because_no_hole_at_address)

    | pre_proof_unfold_abstractions _ abs a H unf prf =>
      match addr with
      | 1 :: addr =>
        let (prf', msg) := update_pre_proof lib prf addr step in
        (pre_proof_unfold_abstractions _ abs a H unf prf', msg)
      | _ => (pre_proof_unfold_abstractions _ abs a H unf prf,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_rev_unfold_abstractions _ abs a H wfa cova unf prf =>
      match addr with
      | 1 :: addr =>
        let (prf', msg) := update_pre_proof lib prf addr step in
        (pre_proof_rev_unfold_abstractions _ abs a H wfa cova unf prf', msg)
      | _ => (pre_proof_rev_unfold_abstractions _ abs a H wfa cova unf prf,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_universe_equality i j H ltij =>
      (pre_proof_universe_equality i j H ltij,
       could_not_apply_update_because_no_hole_at_address)

    | pre_proof_hypothesis_equality x A G J =>
      (pre_proof_hypothesis_equality x A G J,
       could_not_apply_update_because_no_hole_at_address)

    | pre_proof_maybe_hidden_hypothesis_equality x A G J b =>
      (pre_proof_maybe_hidden_hypothesis_equality x A G J b,
       could_not_apply_update_because_no_hole_at_address)

    | pre_proof_unhide_equality x A t1 t2 C G J prf =>
      match addr with
      | 1 :: addr =>
        let (prf', msg) := update_pre_proof lib prf addr step in
        (pre_proof_unhide_equality x A t1 t2 C G J prf', msg)
      | _ => (pre_proof_unhide_equality x A t1 t2 C G J prf,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1' prf2 prf3, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1 prf2' prf3, msg)
      | 3 :: addr =>
        let (prf3', msg) := update_pre_proof lib prf3 addr step in
        (pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1 prf2 prf3', msg)
      | _ => (pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1 prf2 prf3,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_integer_equality n H =>
      (pre_proof_integer_equality n H,
       could_not_apply_update_because_no_hole_at_address)

    | pre_proof_introduction t C H wft covt nout prf =>
      match addr with
      | 1 :: addr =>
        let (prf', msg) := update_pre_proof lib prf addr step in
        (pre_proof_introduction t C H wft covt nout prf', msg)
      | _ => (pre_proof_introduction t C H wft covt nout prf,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_axiom_equality a b T H prf =>
      match addr with
      | 1 :: addr =>
        let (prf', msg) := update_pre_proof lib prf addr step in
        (pre_proof_axiom_equality a b T H prf', msg)
      | _ => (pre_proof_axiom_equality a b T H prf,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_thin G J A C x nixJ nixC prf =>
      match addr with
      | 1 :: addr =>
        let (prf', msg) := update_pre_proof lib prf addr step in
        (pre_proof_thin G J A C x nixJ nixC prf', msg)
      | _ => (pre_proof_thin G J A C x nixJ nixC prf,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2', msg)
      | _ => (pre_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA prf1 prf2', msg)
      | _ => (pre_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf prf1 prf2', msg)
      | _ => (pre_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1 prf2', msg)
      | _ => (pre_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_isect_member_equality H t1 t2 A x B z i nizH prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_isect_member_equality H t1 t2 A x B z i nizH prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_isect_member_equality H t1 t2 A x B z i nizH prf1 prf2', msg)
      | _ => (pre_proof_isect_member_equality H t1 t2 A x B z i nizH prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_cumulativity H T i j leij prf1 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_cumulativity H T i j leij prf1', msg)
      | _ => (pre_proof_cumulativity H T i j leij prf1,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_equality_symmetry H a b T prf1 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_equality_symmetry H a b T prf1', msg)
      | _ => (pre_proof_equality_symmetry H a b T prf1,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_equality_transitivity H a b c T wfc covc prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_equality_transitivity H a b c T wfc covc prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_equality_transitivity H a b c T wfc covc prf1 prf2', msg)
      | _ => (pre_proof_equality_transitivity H a b c T wfc covc prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end

    | pre_proof_cequiv_transitivity H a b c wfc covc prf1 prf2 =>
      match addr with
      | 1 :: addr =>
        let (prf1', msg) := update_pre_proof lib prf1 addr step in
        (pre_proof_cequiv_transitivity H a b c wfc covc prf1' prf2, msg)
      | 2 :: addr =>
        let (prf2', msg) := update_pre_proof lib prf2 addr step in
        (pre_proof_cequiv_transitivity H a b c wfc covc prf1 prf2', msg)
      | _ => (pre_proof_cequiv_transitivity H a b c wfc covc prf1 prf2,
              could_not_apply_update_because_wrong_address)
      end
    end
  end.*)

Lemma pre_proof2bseq_update_pre_proof {o} :
  forall lib (pre_prf : @pre_proof o) oaddr addr step,
    pre_proof2bseq (fst (update_pre_proof lib pre_prf oaddr addr step))
    = pre_proof2bseq pre_prf.
Proof.
  destruct addr; simpl; introv.

  { destruct pre_prf; simpl.

    + remember (apply_proof_step lib concl step) as w; destruct w.
      symmetry in Heqw.
      destruct o0; simpl; auto.

    + remember (apply_proof_step lib concl step) as w; destruct w.
      symmetry in Heqw.
      destruct o0; simpl; auto. }

  { destruct pre_prf; simpl; tcsp.
    destruct n; simpl; tcsp.
    destruct n; simpl; tcsp.
    { destruct hyps; simpl in *; tcsp.
      remember (update_pre_proof lib p oaddr addr step) as w; destruct w; simpl; tcsp. }
    destruct n; simpl; tcsp.
    { destruct hyps; simpl in *; tcsp.
      destruct hyps; simpl in *; tcsp.
      remember (update_pre_proof lib p0 oaddr addr step) as w; destruct w; simpl; tcsp. }
    destruct n; simpl; tcsp.
    { destruct hyps; simpl in *; tcsp.
      destruct hyps; simpl in *; tcsp.
      destruct hyps; simpl in *; tcsp.
      remember (update_pre_proof lib p1 oaddr addr step) as w; destruct w; simpl; tcsp. } }
Qed.

Lemma pre_proof2type_update_pre_proof {o} :
  forall lib (pre_prf : @pre_proof o) oaddr addr step,
    pre_proof2type (fst (update_pre_proof lib pre_prf oaddr addr step))
    = pre_proof2type pre_prf.
Proof.
  introv; unfold pre_proof2type.
  rewrite pre_proof2bseq_update_pre_proof; auto.
Qed.

Definition update_pre_proof_seq {o}
           (ctxt : @ProofContext o)
           (pps  : @pre_proof_seq o)
           (addr : address)
           (step : @proof_step o) : @pre_proof_seq o * @DEBUG_MSG o :=
  match pps with
  | MkPreProofSeq name pre_prf =>
    let (pre_prf', msg) := update_pre_proof ctxt pre_prf addr addr step in
    (MkPreProofSeq name pre_prf', msg)
  end.

(*Definition update_pre_proof_seq {o}
           (ctxt : @ProofContext o)
           (pps  : @pre_proof_seq o)
           (addr : address)
           (step : @proof_step o) : @pre_proof_seq o * @DEBUG_MSG o.
Proof.
  destruct pps as [name pre_prf (*nhyps*) isp].

  remember (update_pre_proof ctxt pre_prf addr addr step) as w; symmetry in Heqw.
  destruct w as [pre_prf' msg].

  assert (isprog (pre_proof2type pre_prf')) as isp'.
  { assert (pre_prf' = fst (update_pre_proof ctxt pre_prf addr addr step)) as xx by (rewrite Heqw; simpl; auto).
    rewrite xx; clear xx.
    rewrite pre_proof2type_update_pre_proof; auto. }

  exact (MkPreProofSeq name pre_prf' (*nhyps*) isp', msg).
Defined.*)

Definition SoftLibrary_update_proof {o}
           (state : @SoftLibrary o)
           (name  : LemmaName)
           (addr  : address)
           (step  : proof_step) : UpdRes :=
  match find_unfinished_in_pre_proofs (SoftLibrary_unfinished state) name with
  | (Some pp, pps) =>

    let (pp', msg) := update_pre_proof_seq (RigidLibrary2ProofContext state) pp addr step in
    MkUpdRes (SoftLibrary_change_unfinished state (pp' :: pps)) [msg]

  | (None, pps) => MkUpdRes state [could_not_apply_update_because_could_not_find_lemma]
  end.

Definition SoftLibrary_start_proof {o}
           (state : @SoftLibrary o)
           (name  : LemmaName)
           (C     : NTerm)
           (*(isp   : isprog C)*) : UpdRes :=
  let pps : pre_proof_seq :=
      MkPreProofSeq name (pre_proof_hole (term2pre_baresequent C)) (*isp*)
  in
  MkUpdRes
    (MkSoftLibrary
       (SoftLibrary_lib state)
       (pps :: SoftLibrary_unfinished state))
    [started_proof name].

(* FIX *)
Fixpoint find_holes_in_pre_proof {o}
         (addr : address)
         (p    : @pre_proof o) : Holes :=
  match p with
  | pre_proof_hole s => [MkHole s addr]
  | pre_proof_node n c [] => []
  | pre_proof_node n c [p1] => find_holes_in_pre_proof (snoc addr 1) p1
  | pre_proof_node n c [p1, p2] => find_holes_in_pre_proof (snoc addr 1) p1 ++ find_holes_in_pre_proof (snoc addr 2) p2
  | pre_proof_node n c [p1, p2, p3] => find_holes_in_pre_proof (snoc addr 1) p1 ++ find_holes_in_pre_proof (snoc addr 2) p2 ++ find_holes_in_pre_proof (snoc addr 3) p3
  | pre_proof_node n c _ => []
  end.

(*Fixpoint find_holes_in_pre_proof {o}
         (p    : pre_proof)
         (addr : address) : Holes :=
  match p with
  | pre_proof_from_ctxt c H => []

  | pre_proof_hole s => [MkHole s addr]

  | pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_isect_member_formation A x B z i H nizH prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_approx_refl a H => []

  | pre_proof_cequiv_refl a H => []

  | pre_proof_cequiv_alpha_eq a b H aeq => []

  | pre_proof_cequiv_approx a b H prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_approx_eq a1 a2 b1 b2 i H prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_cequiv_eq a1 a2 b1 b2 i H prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_cut B C x H wfB covB nixH prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_hypothesis x A G J => []

  | pre_proof_cequiv_subst_concl C x a b H wfa wfb cova covb prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_cequiv_computation _ a b H r => []

  | pre_proof_cequiv_computation_aeq _ a b c H r aeq => []

  | pre_proof_cequiv_computation_atmost _ a b n H r => []

  | pre_proof_unfold_abstractions _ abs a H unf prf =>
    find_holes_in_pre_proof prf (snoc addr 1)

  | pre_proof_rev_unfold_abstractions _ abs a H wfa cova unf prf =>
    find_holes_in_pre_proof prf (snoc addr 1)

  | pre_proof_universe_equality i j H ltij => []

  | pre_proof_hypothesis_equality x A G J => []

  | pre_proof_maybe_hidden_hypothesis_equality x A G J b => []

  | pre_proof_unhide_equality x A t1 t2 C G J prf =>
    find_holes_in_pre_proof prf (snoc addr 1)

  | pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    let holes3 := find_holes_in_pre_proof prf3 (snoc addr 3) in
    holes1 ++ holes2 ++ holes3

  | pre_proof_integer_equality n H => []

  | pre_proof_introduction t C H wft covt nout prf =>
    find_holes_in_pre_proof prf (snoc addr 1)

  | pre_proof_axiom_equality a b T H prf =>
    find_holes_in_pre_proof prf (snoc addr 1)

  | pre_proof_thin G J A C x nixJ nixC prf =>
    find_holes_in_pre_proof prf (snoc addr 1)

  | pre_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_isect_member_equality H t1 t2 A x B z i nizH prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_cumulativity H T i j leij prf1 =>
    find_holes_in_pre_proof prf1 (snoc addr 1)

  | pre_proof_equality_symmetry H a b T prf1 =>
    find_holes_in_pre_proof prf1 (snoc addr 1)

  | pre_proof_equality_transitivity H a b c T wfc covc prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2

  | pre_proof_cequiv_transitivity H a b c wfc covc prf1 prf2 =>
    let holes1 := find_holes_in_pre_proof prf1 (snoc addr 1) in
    let holes2 := find_holes_in_pre_proof prf2 (snoc addr 2) in
    holes1 ++ holes2
  end.*)

Definition find_holes_in_pre_proof_seq {o}
           (pps : @pre_proof_seq o) : Holes :=
  match pps with
  | MkPreProofSeq name pre_prf (*isp*) => find_holes_in_pre_proof [] pre_prf
  end.

Definition pre_proofs2names {o} (ps : @pre_proofs o) : LemmaNames :=
  map (@pre_proof_seq_name o) ps.

Definition SoftLibrary_unfinished_names {o} (state : @SoftLibrary o) : LemmaNames :=
  pre_proofs2names (SoftLibrary_unfinished state).

Definition SoftLibrary_find_holes {o}
           (state : @SoftLibrary o)
           (name  : LemmaName) : UpdRes :=
  match find_unfinished_in_pre_proofs (SoftLibrary_unfinished state) name with
  | (Some pp, _) =>

    let holes := find_holes_in_pre_proof_seq pp in
    MkUpdRes state [found_holes holes]

  | (None, pps) =>
    let names := SoftLibrary_unfinished_names state in
    MkUpdRes state [could_not_find_holes_because_could_not_find_lemma name names]
  end.

(* FIX *)
Fixpoint find_sequent_in_pre_proof {o}
         (addr : address)
         (p    : @pre_proof o) : option pre_baresequent :=
  match addr, p with
  | [], _ => Some (pre_proof2bseq p)
  | _ :: _, pre_proof_hole _ => None
  | 1 :: addr, pre_proof_node n c (p1 :: _) => find_sequent_in_pre_proof addr p1
  | 2 :: addr, pre_proof_node n c (_ :: p2 :: _) => find_sequent_in_pre_proof addr p2
  | 3 :: addr, pre_proof_node n c (_ :: _ :: p3 :: _) => find_sequent_in_pre_proof addr p3
  | _, _ => None
  end.

(*Fixpoint find_sequent_in_pre_proof {o}
         {s    : @pre_baresequent o}
         (p    : pre_proof s)
         (addr : address) : option pre_baresequent :=
  match addr with
  | [] => Some s
  | n :: addr =>
    match p with
    | pre_proof_from_ctxt c H => None

    | pre_proof_hole s => None

    | pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_isect_member_formation A x B z i H nizH prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_approx_refl a H => None

    | pre_proof_cequiv_refl a H => None

    | pre_proof_cequiv_alpha_eq a b H aeq => None

    | pre_proof_cequiv_approx a b H prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_approx_eq a1 a2 b1 b2 i H prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_cequiv_eq a1 a2 b1 b2 i H prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_cut B C x H wfB covB nixH prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_hypothesis x A G J => None

    | pre_proof_cequiv_subst_concl C x a b H wfa wfb cova covb prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_cequiv_computation _ a b H r => None

    | pre_proof_cequiv_computation_aeq _ a b c H r aeq => None

    | pre_proof_cequiv_computation_atmost _ a b n H r => None

    | pre_proof_unfold_abstractions _ abs a H unf prf =>
      match n with
      | 1 => find_sequent_in_pre_proof prf addr
      | _ => None
      end

    | pre_proof_rev_unfold_abstractions _ abs a H wfa cova unf prf =>
      match n with
      | 1 => find_sequent_in_pre_proof prf addr
      | _ => None
      end

    | pre_proof_universe_equality i j H ltij => None

    | pre_proof_hypothesis_equality x A G J => None

    | pre_proof_maybe_hidden_hypothesis_equality x A G J b => None

    | pre_proof_unhide_equality x A t1 t2 C G J prf =>
      match n with
      | 1 => find_sequent_in_pre_proof prf addr
      | _ => None
      end

    | pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | 3 => find_sequent_in_pre_proof prf3 addr
      | _ => None
      end

    | pre_proof_integer_equality n H => None

    | pre_proof_introduction t C H wft covt nout prf =>
      match n with
      | 1 => find_sequent_in_pre_proof prf addr
      | _ => None
      end

    | pre_proof_axiom_equality a b T H prf =>
      match n with
      | 1 => find_sequent_in_pre_proof prf addr
      | _ => None
      end

    | pre_proof_thin G J A C x nixJ nixC prf =>
      match n with
      | 1 => find_sequent_in_pre_proof prf addr
      | _ => None
      end

    | pre_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_isect_member_equality H t1 t2 A x B z i nizH prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_cumulativity H T i j leij prf1 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | _ => None
      end

    | pre_proof_equality_symmetry H a b T prf1 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | _ => None
      end

    | pre_proof_equality_transitivity H a b c T wfc covc prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end

    | pre_proof_cequiv_transitivity H a b c wfc covc prf1 prf2 =>
      match n with
      | 1 => find_sequent_in_pre_proof prf1 addr
      | 2 => find_sequent_in_pre_proof prf2 addr
      | _ => None
      end
    end
  end.*)

Definition find_sequent_in_pre_proof_seq {o}
           (pps  : @pre_proof_seq o)
           (addr : address) : option pre_baresequent :=
  match pps with
  | MkPreProofSeq name pre_prf (*isp*) => find_sequent_in_pre_proof addr pre_prf
  end.

Definition SoftLibrary_find_hole {o}
           (state : @SoftLibrary o)
           (name  : LemmaName)
           (addr  : address) : UpdRes :=
  match find_unfinished_in_pre_proofs (SoftLibrary_unfinished state) name with
  | (Some pp, _) =>

    match find_sequent_in_pre_proof_seq pp addr with
    | Some s => MkUpdRes state [found_sequent_at_address addr s]
    | None => MkUpdRes state [could_not_find_sequent_at_address addr]
    end

  | (None, pps) => MkUpdRes state [could_not_find_sequent_because_could_not_find_lemma]
  end.

Definition rename_LemmaName r (n : LemmaName) : LemmaName :=
  rename_opname r n.

Definition rename_named_concl {o} r (nc : @named_concl o) : named_concl :=
  MkNamedConcl
    (rename_LemmaName r (nm_conclusion_name nc))
    (rename_term r (nm_conclusion_type nc)).

Definition rename_named_concls {o} r (l : list (@named_concl o)) : list named_concl :=
  map (rename_named_concl r) l.

Definition rename_ProofContext {o} r (pc : @ProofContext o) : ProofContext :=
  MkProofContext
    o
    (rename_lib r (PC_lib pc))
    (rename_named_concls r (PC_conclusions pc)).

Lemma rename_in_PC_conclusions {o} :
  forall r {c : @named_concl o} {l} (i : LIn c l),
    LIn (rename_named_concl r c) (rename_named_concls r l).
Proof.
  induction l; introv i; simpl in *; repndors; subst; tcsp.
Qed.

Lemma rename_NVin_vars_hyps {o} :
  forall r {y} {H : @barehypotheses o},
    NVin y (vars_hyps H)
    -> NVin y (vars_hyps (rename_barehypotheses r H)).
Proof.
  introv i.
  allrw @NVin_iff.
  introv j; destruct i.
  unfold vars_hyps in *.
  allrw in_map_iff; exrepnd; subst.
  exists (rename_hypothesis r a); simpl; dands; auto;
    [|destruct a; simpl; auto].
  induction H; simpl in *; tcsp.
  repndors; subst; tcsp; autorewrite with slow; tcsp.
Qed.

Lemma rename_NVin_free_vars_hyps {o} :
  forall r {y} {H : @barehypotheses o},
    NVin y (free_vars_hyps H)
    -> NVin y (free_vars_hyps (rename_barehypotheses r H)).
Proof.
  introv i.
  allrw @NVin_iff.
  introv j; destruct i.
  induction H; simpl in *; tcsp.
  allrw in_app_iff; allrw in_remove_nvars; simpl in *.
  destruct a; simpl in *.
  unfold hyp_free_vars in *; simpl in *.
  repndors; autorewrite with slow in *; tcsp.
Qed.

Lemma rename_NVin_free_vars {o} :
  forall r {y} {t : @NTerm o},
    NVin y (free_vars t)
    -> NVin y (free_vars (rename_term r t)).
Proof.
  introv i.
  allrw @NVin_iff.
  autorewrite with slow in *; auto.
Qed.

Lemma reduces_in_atmost_k_steps_rename {o} :
  forall r {lib} {n} {a b : @NTerm o},
    reduces_in_atmost_k_steps lib a b n
    -> reduces_in_atmost_k_steps (rename_lib r lib) (rename_term r a) (rename_term r b) n.
Proof.
  induction n; introv h.

  - allrw @reduces_in_atmost_k_steps_0; subst; auto.

  - allrw @reduces_in_atmost_k_steps_S; exrepnd.
    apply (compute_step_rename r) in h1.
    apply IHn in h0.
    allrw.
    eexists; dands; eauto.
Qed.
Hint Resolve reduces_in_atmost_k_steps_rename : slow.

Definition rename_abs r abs := map (rename_opname r) abs.

Lemma get_abstraction_name_rename {o} :
  forall r (t : @NTerm o),
    get_abstraction_name (rename_term r t)
    = option_map (rename_opname r) (get_abstraction_name t).
Proof.
  introv; destruct t; simpl; auto.
  destruct o0; simpl; tcsp.
  destruct o0; simpl; tcsp.
Qed.

Lemma unfold_rename {o} :
  forall r lib (t : @NTerm o),
    unfold (rename_lib r lib) (rename_term r t)
    = option_map (rename_term r) (unfold lib t).
Proof.
  introv; destruct t as [| |op bs]; simpl; auto.
  destruct op as [| | |abs]; simpl; tcsp.
  induction lib; simpl; tcsp.
  destruct a; simpl in *.

  boolvar; ginv; simpl; tcsp.

  - unfold mk_instance; simpl.
    rewrite rename_term_sosub.
    rewrite rename_sosub_mk_abs_subst; auto.

  - apply (implies_matching_entry_rename r) in m.
    autorewrite with slow in *.
    apply not_matching_entry_iff in n; destruct n.
    allrw map_map; unfold compose in *.
    assert (map (fun x => rename_bterm r (rename_bterm r x)) bs = bs) as xx; try congruence.
    apply eq_map_l; introv i; destruct x; simpl; autorewrite with slow; auto.

  - apply (implies_matching_entry_rename r) in m.
    apply not_matching_entry_iff in n; destruct n; auto.
Qed.

Lemma rename_unfoldable {o} :
  forall r lib abs (t : @NTerm o),
    unfoldable (rename_lib r lib) (rename_abs r abs) (rename_term r t)
    = unfoldable lib abs t.
Proof.
  introv; unfold unfoldable.
  rewrite get_abstraction_name_rename.
  remember (get_abstraction_name t) as gan; symmetry in Heqgan.
  destruct gan; simpl; auto.
  rewrite unfold_rename.
  boolvar; tcsp.

  - remember (unfold lib t) as unf; symmetry in Hequnf; destruct unf; simpl; tcsp.

  - unfold rename_abs in *; allrw in_map_iff; exrepnd.
    apply eq_rename_opname_implies in l0; subst; tcsp.

  - destruct n.
    unfold rename_abs in *; allrw in_map_iff; exrepnd.
    eexists; dands; eauto.
Qed.

Lemma rename_all_abstractions_can_be_unfolded {o} :
  forall r {lib} {abs} {t : @NTerm o},
    all_abstractions_can_be_unfolded lib abs t
    -> all_abstractions_can_be_unfolded (rename_lib r lib) (rename_abs r abs) (rename_term r t).
Proof.
  introv alla.
  unfold all_abstractions_can_be_unfolded in *.
  nterm_ind t as [v|f|op bs ind] Case; simpl in *; tcsp.
  allrw andb_true; repnd.
  dands; auto.

  - rewrite forallb_forall_lin.
    rewrite forallb_forall_lin in alla0.
    introv i.
    allrw in_map_iff; exrepnd; subst.
    destruct a.
    applydup alla0 in i1.
    applydup ind in i1; auto.

  - rw <- (@rename_unfoldable o r) in alla; simpl in *; tcsp.
Qed.

Definition rename_pre_conclusion {o} r (c : @pre_conclusion o) : pre_conclusion :=
  match c with
  | pre_concl_ext t => pre_concl_ext (rename_term r t)
  | pre_concl_typ t => pre_concl_typ (rename_term r t)
  end.

Definition rename_pre_baresequent {o} (r : renaming) (s : @pre_baresequent o) : pre_baresequent :=
  match s with
  | MkPreBaresequent hyps concl =>
    MkPreBaresequent (rename_barehypotheses r hyps) (rename_pre_conclusion r concl)
  end.

Lemma named_concl2bseq_rename_eq {o} :
  forall {r} {H : @bhyps o} {c},
    named_concl2bseq (rename_barehypotheses r H) (rename_named_concl r c)
    = rename_baresequent r (named_concl2bseq H c).
Proof.
  introv; simpl; auto.
Defined.

Lemma rename_barehypotheses_app {o} :
  forall r (H G : @bhyps o),
    rename_barehypotheses r (H ++ G)
    = rename_barehypotheses r H ++ rename_barehypotheses r G.
Proof.
  induction H; introv; simpl; auto.
  rewrite IHlist; auto.
Defined.

Lemma get_abstraction_name_op_rename_op {o} :
  forall r (op : @Opid o),
    get_abstraction_name_op (rename_op r op)
    = match get_abstraction_name_op op with
      | Some x => Some (rename_opname r x)
      | None => None
      end.
Proof.
  introv; destruct op as [| | |abs]; simpl; auto.
  destruct abs; simpl; auto.
Defined.

Definition rename_bterms {o} r (bs : list (@BTerm o)) := map (rename_bterm r) bs.

Lemma unfold_abs_rename {o} :
  forall r lib abs (bs : list (@BTerm o)),
    unfold_abs (rename_lib r lib) (rename_opabs r abs) (rename_bterms r bs)
    = option_map (rename_term r) (unfold_abs lib abs bs).
Proof.
  induction lib; introv; simpl; tcsp.
  destruct a; simpl in *.

  boolvar; ginv; simpl; tcsp.

  - unfold mk_instance; simpl.
    rewrite rename_term_sosub.
    rewrite rename_sosub_mk_abs_subst; auto.

  - apply (implies_matching_entry_rename r) in m.
    autorewrite with slow in *.
    apply not_matching_entry_iff in n; destruct n.
    unfold rename_bterms in *.
    allrw map_map; unfold compose in *.
    assert (map (fun x => rename_bterm r (rename_bterm r x)) bs = bs) as xx; try congruence.
    apply eq_map_l; introv i; destruct x; simpl; autorewrite with slow; auto.

  - apply (implies_matching_entry_rename r) in m.
    apply not_matching_entry_iff in n; destruct n; auto.
Defined.

Lemma rename_maybe_unfold {o} :
  forall r lib abs (t : @NTerm o),
    rename_term r (maybe_unfold lib abs t)
    = maybe_unfold (rename_lib r lib) (rename_abs r abs) (rename_term r t).
Proof.
  introv.
  unfold maybe_unfold; simpl.
  rewrite get_abstraction_name_rename.
  remember (get_abstraction_name t) as gan; symmetry in Heqgan; destruct gan; simpl; auto.
  boolvar; auto.

  - rewrite unfold_rename.
    remember (unfold lib t) as u; symmetry in Hequ; destruct u; simpl; auto.

  - destruct n.
    unfold rename_abs; apply in_map_iff; eexists; dands; eauto.

  - unfold rename_abs in *; allrw in_map_iff; exrepnd.
    apply eq_rename_opname_implies in l0; subst; tcsp.
Defined.

Lemma rename_term_unfold_abstractions {o} :
  forall r lib abs (t : @NTerm o),
    rename_term r (unfold_abstractions lib abs t)
    = unfold_abstractions (rename_lib r lib) (rename_abs r abs) (rename_term r t).
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; simpl in *; tcsp.
  Case "oterm".
  rewrite rename_maybe_unfold.
  f_equal; simpl; f_equal.
  allrw map_map; unfold compose.
  apply eq_maps; introv i; destruct x; simpl; f_equal.
  eapply ind; eauto.
Defined.

(*Lemma proof_named_concl2bseq_rename_implies {o} :
  forall {r} {H : @bhyps o} {c},
    proof (named_concl2bseq (rename_barehypotheses r H) (rename_named_concl r c))
    -> proof (rename_baresequent r (named_concl2bseq H c)).
Proof.
  introv prf; simpl in *; auto.
Defined.

Lemma pre_proof_named_concl2pre_bseq_rename_implies {o} :
  forall {r} {H : @bhyps o} {c},
    pre_proof (named_concl2pre_bseq (rename_barehypotheses r H) (rename_named_concl r c))
    -> pre_proof (rename_pre_baresequent r (named_concl2pre_bseq H c)).
Proof.
  introv prf; simpl in *; auto.
Defined.

Lemma proof_mk_bseq_rename_implies {o} :
  forall {r} {H : @bhyps o} {c},
    proof (mk_bseq (rename_barehypotheses r H) (rename_conclusion r c))
    -> proof (rename_baresequent r (mk_bseq H c)).
Proof.
  introv prf; simpl in *; auto.
Defined.

Lemma implies_proof_rename_named_concl2bseq {o} :
  forall {r} {H : @bhyps o} {c},
    proof (rename_baresequent r (named_concl2bseq H c))
    -> proof (named_concl2bseq (rename_barehypotheses r H) (rename_named_concl r c)).
Proof.
  introv prf; simpl in *; auto.
Defined.

Lemma implies_proof_rename_mk_bseq {o} :
  forall {r} {H : @bhyps o} {c},
    proof (rename_baresequent r (mk_bseq H c))
    -> proof (mk_bseq (rename_barehypotheses r H) (rename_conclusion r c)).
Proof.
  introv prf; simpl in *; auto.
Defined.

Lemma proof_rename_rule_isect_equality2_hyp2_implies {o} :
  forall {r} {a1 b1 b2 e2 : @NTerm o} {x1} {x2} {y} {i} {H},
    proof (rename_baresequent r (rule_isect_equality2_hyp2 a1 b1 b2 e2 x1 x2 y i H))
    -> proof (rule_isect_equality2_hyp2 (rename_term r a1) (rename_term r b1) (rename_term r b2) (rename_term r e2) x1 x2 y i  (rename_barehypotheses r H)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma pre_proof_rename_pre_rule_isect_equality_hyp2_implies {o} :
  forall {r} {a1 b1 b2 : @NTerm o} {x1} {x2} {y} {i} {H},
    pre_proof (rename_pre_baresequent r (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H))
    -> pre_proof (pre_rule_isect_equality_hyp2 (rename_term r a1) (rename_term r b1) (rename_term r b2) x1 x2 y i (rename_barehypotheses r H)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma proof_rename_rule_isect_member_formation_hyp1 {o} :
  forall {r} {z} {A : @NTerm o} {x} {B} {b} {H},
    proof (rename_baresequent r (rule_isect_member_formation_hyp1 z A x B b H))
    -> proof (rule_isect_member_formation_hyp1 z (rename_term r A) x (rename_term r B) (rename_term r b) (rename_barehypotheses r H)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma pre_proof_rename_pre_rule_isect_member_formation_hyp1 {o} :
  forall {r} {z} {A : @NTerm o} {x} {B} {H},
    pre_proof (rename_pre_baresequent r (pre_rule_isect_member_formation_hyp1 z A x B H))
    -> pre_proof (pre_rule_isect_member_formation_hyp1 z (rename_term r A) x (rename_term r B) (rename_barehypotheses r H)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma proof_rename_rule_cut_hyp2 {o} :
  forall {r} {H : @bhyps o} {x} {B} {C} {t},
    proof (rename_baresequent r (rule_cut_hyp2 H x B C t))
    -> proof (rule_cut_hyp2 (rename_barehypotheses r H) x (rename_term r B) (rename_term r C) (rename_term r t)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
Defined.

Lemma pre_proof_rename_pre_rule_cut_hyp2 {o} :
  forall {r} {H : @bhyps o} {x} {B} {C},
    pre_proof (rename_pre_baresequent r (pre_rule_cut_hyp2 H x B C))
    -> pre_proof (pre_rule_cut_hyp2 (rename_barehypotheses r H) x (rename_term r B) (rename_term r C)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
Defined.

Lemma proof_rename_rule_cut_concl {o} :
  forall {r} {H : @bhyps o} {C} {t} {x} {u},
    proof (rule_cut_concl (rename_barehypotheses r H) (rename_term r C) (rename_term r t) x (rename_term r u))
    -> proof (rename_baresequent r (rule_cut_concl H C t x u)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_term_subst); auto.
Defined.

Lemma pre_proof_rename_pre_rule_cut_concl {o} :
  forall {r} {H : @bhyps o} {C},
    pre_proof (pre_rule_cut_concl (rename_barehypotheses r H) (rename_term r C))
    -> pre_proof (rename_pre_baresequent r (pre_rule_cut_concl H C)).
Proof.
  introv prf; simpl in *; auto.
Defined.

Lemma proof_rename_rule_hypothesis_concl {o} :
  forall {r} {G : @bhyps o} {J} {A} {x},
    proof (rule_hypothesis_concl (rename_barehypotheses r G)  (rename_barehypotheses r J) (rename_term r A) x)
    -> proof (rename_baresequent r (rule_hypothesis_concl G J A x)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma pre_proof_rename_pre_rule_hypothesis_concl {o} :
  forall {r} {G : @bhyps o} {J} {A} {x},
    pre_proof (pre_rule_hypothesis_concl (rename_barehypotheses r G)  (rename_barehypotheses r J) (rename_term r A) x)
    -> pre_proof (rename_pre_baresequent r (pre_rule_hypothesis_concl G J A x)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma proof_rename_rule_cequiv_subst_hyp1 {o} :
  forall {r} {H : @bhyps o} {x} {C} {b} {t},
    proof (rename_baresequent r (rule_cequiv_subst_hyp1 H x C b t))
    -> proof (rule_cequiv_subst_hyp1 (rename_barehypotheses r H) x (rename_term r C) (rename_term r b) (rename_term r t)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma pre_proof_rename_pre_rule_cequiv_subst_hyp1 {o} :
  forall {r} {H : @bhyps o} {x} {C} {b},
    pre_proof (rename_pre_baresequent r (pre_rule_cequiv_subst_hyp1 H x C b))
    -> pre_proof (pre_rule_cequiv_subst_hyp1 (rename_barehypotheses r H) x (rename_term r C) (rename_term r b)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma implies_proof_rename_rule_cequiv_subst_hyp1 {o} :
  forall {r} {H : @bhyps o} {x} {C} {a} {t},
    proof (rule_cequiv_subst_hyp1 (rename_barehypotheses r H) x (rename_term r C) (rename_term r a) (rename_term r t))
    -> proof (rename_baresequent r (rule_cequiv_subst_hyp1 H x C a t)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_term_subst); auto.
Defined.

Lemma implies_pre_proof_rename_pre_rule_cequiv_subst_hyp1 {o} :
  forall {r} {H : @bhyps o} {x} {C} {a},
    pre_proof (pre_rule_cequiv_subst_hyp1 (rename_barehypotheses r H) x (rename_term r C) (rename_term r a))
    -> pre_proof (rename_pre_baresequent r (pre_rule_cequiv_subst_hyp1 H x C a)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_term_subst); auto.
Defined.

Lemma proof_rename_rule_cequiv_subst_hyp_hyp2 {o} :
  forall {r} {H : @bhyps o} {z} {T} {x} {a} {J} {b} {e},
    proof (rename_baresequent r (rule_cequiv_subst_hyp_hyp2 H z T x a J b e))
    -> proof (rule_cequiv_subst_hyp_hyp2 (rename_barehypotheses r H) z (rename_term r T) x (rename_term r a) (rename_barehypotheses r J) (rename_term r b) (rename_term r e)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma pre_proof_rename_pre_rule_cequiv_subst_hyp_hyp2 {o} :
  forall {r} {H : @bhyps o} {z} {T} {x} {a} {J} {b},
    pre_proof (rename_pre_baresequent r (pre_rule_cequiv_subst_hyp_hyp2 H z T x a J b))
    -> pre_proof (pre_rule_cequiv_subst_hyp_hyp2 (rename_barehypotheses r H) z (rename_term r T) x (rename_term r a) (rename_barehypotheses r J) (rename_term r b)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma proof_rename_rule_cequiv_subst_hyp_hyp1 {o} :
  forall {r} {H : @bhyps o} {z} {T} {x} {b} {J} {C} {t},
    proof (rename_baresequent r (rule_cequiv_subst_hyp_hyp1 H z T x b J C t))
    -> proof (rule_cequiv_subst_hyp_hyp1 (rename_barehypotheses r H) z (rename_term r T) x (rename_term r b) (rename_barehypotheses r J) (rename_term r C) (rename_term r t)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma pre_proof_rename_pre_rule_cequiv_subst_hyp_hyp1 {o} :
  forall {r} {H : @bhyps o} {z} {T} {x} {b} {J} {C},
    pre_proof (rename_pre_baresequent r (pre_rule_cequiv_subst_hyp_hyp1 H z T x b J C))
    -> pre_proof (pre_rule_cequiv_subst_hyp_hyp1 (rename_barehypotheses r H) z (rename_term r T) x (rename_term r b) (rename_barehypotheses r J) (rename_term r C)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma proof_rename_rule_cequiv_subst_hyp_concl {o} :
  forall {r} {H : @bhyps o} {z} {T} {x} {a} {J} {C} {t},
    proof (rule_cequiv_subst_hyp_concl (rename_barehypotheses r H) z (rename_term r T) x (rename_term r a) (rename_barehypotheses r J) (rename_term r C) (rename_term r t))
    -> proof (rename_baresequent r (rule_cequiv_subst_hyp_concl H z T x a J C t)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
  repeat (rewrite rename_term_subst); auto.
Defined.

Lemma pre_proof_rename_pre_rule_cequiv_subst_hyp_concl {o} :
  forall {r} {H : @bhyps o} {z} {T} {x} {a} {J} {C},
    pre_proof (pre_rule_cequiv_subst_hyp_concl (rename_barehypotheses r H) z (rename_term r T) x (rename_term r a) (rename_barehypotheses r J) (rename_term r C))
    -> pre_proof (rename_pre_baresequent r (pre_rule_cequiv_subst_hyp_concl H z T x a J C)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
  repeat (rewrite rename_term_subst); auto.
Defined.

Lemma proof_rename_rule_unfold_abstraction_hyp {o} :
  forall {r} {lib} {abs} {a} {e} {H : @bhyps o},
    proof (rename_baresequent r (rule_unfold_abstractions_hyp lib abs a e H))
    -> proof (rule_unfold_abstractions_hyp (rename_lib r lib) (rename_abs r abs) (rename_term r a) (rename_term r e) (rename_barehypotheses r H)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_term_unfold_abstractions in prf; auto.
Defined.

Lemma pre_proof_rename_pre_rule_unfold_abstraction_hyp {o} :
  forall {r} {lib} {abs} {a} {H : @bhyps o},
    pre_proof (rename_pre_baresequent r (pre_rule_unfold_abstractions_hyp lib abs a H))
    -> pre_proof (pre_rule_unfold_abstractions_hyp (rename_lib r lib) (rename_abs r abs) (rename_term r a) (rename_barehypotheses r H)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_term_unfold_abstractions in prf; auto.
Defined.

Lemma proof_rename_rule_unfold_abstractions_hyp {o} :
  forall {r} {lib} {abs} {a} {e} {H : @bhyps o},
    proof (rule_unfold_abstractions_hyp (rename_lib r lib) (rename_abs r abs) (rename_term r a) (rename_term r e) (rename_barehypotheses r H))
    -> proof (rename_baresequent r (rule_unfold_abstractions_hyp lib abs a e H)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_term_unfold_abstractions; auto.
Defined.

Lemma pre_proof_rename_pre_rule_unfold_abstractions_hyp {o} :
  forall {r} {lib} {abs} {a} {H : @bhyps o},
    pre_proof (pre_rule_unfold_abstractions_hyp (rename_lib r lib) (rename_abs r abs) (rename_term r a) (rename_barehypotheses r H))
    -> pre_proof (rename_pre_baresequent r (pre_rule_unfold_abstractions_hyp lib abs a H)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_term_unfold_abstractions; auto.
Defined.

Lemma proof_rename_rule_hypothesis_equality_concl {o} :
  forall {r} {G : @bhyps o} {J} {A} {x},
    proof (rule_hypothesis_equality_concl (rename_barehypotheses r G) (rename_barehypotheses r J) (rename_term r A) x)
    -> proof (rename_baresequent r (rule_hypothesis_equality_concl G J A x)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma pre_proof_rename_pre_rule_hypothesis_equality_concl {o} :
  forall {r} {G : @bhyps o} {J} {A} {x},
    pre_proof (pre_rule_hypothesis_equality_concl (rename_barehypotheses r G) (rename_barehypotheses r J) (rename_term r A) x)
    -> pre_proof (rename_pre_baresequent r (pre_rule_hypothesis_equality_concl G J A x)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma proof_rename_rule_maybe_hidden_hypothesis_equality_concl {o} :
  forall {r} {G : @bhyps o} {J} {A} {x} {b},
    proof (rule_maybe_hidden_hypothesis_equality_concl (rename_barehypotheses r G) (rename_barehypotheses r J) (rename_term r A) x b)
    -> proof (rename_baresequent r (rule_maybe_hidden_hypothesis_equality_concl G J A x b)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma pre_proof_rename_pre_rule_maybe_hidden_hypothesis_equality_concl {o} :
  forall {r} {G : @bhyps o} {J} {A} {x} {b},
    pre_proof (pre_rule_maybe_hidden_hypothesis_equality_concl (rename_barehypotheses r G) (rename_barehypotheses r J) (rename_term r A) x b)
    -> pre_proof (rename_pre_baresequent r (pre_rule_maybe_hidden_hypothesis_equality_concl G J A x b)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma proof_rename_rule_unhide_equality_hyp {o} :
  forall {r} {G : @bhyps o} {J} {x} {A} {t1} {t2} {C} {e},
    proof (rename_baresequent r (rule_unhide_equality_hyp G J x A t1 t2 C e))
    -> proof (rule_unhide_equality_hyp (rename_barehypotheses r G) (rename_barehypotheses r J) x (rename_term r A) (rename_term r t1) (rename_term r t2) (rename_term r C) (rename_term r e)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
Defined.

Lemma pre_proof_rename_pre_rule_unhide_equality_hyp {o} :
  forall {r} {G : @bhyps o} {J} {x} {A} {t1} {t2} {C},
    pre_proof (rename_pre_baresequent r (pre_rule_unhide_equality_hyp G J x A t1 t2 C))
    -> pre_proof (pre_rule_unhide_equality_hyp (rename_barehypotheses r G) (rename_barehypotheses r J) x (rename_term r A) (rename_term r t1) (rename_term r t2) (rename_term r C)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
Defined.

Lemma proof_rename_rule_unhide_equality_concl {o} :
  forall {r} {G : @bhyps o} {J} {x} {A} {t1} {t2} {C},
    proof (rule_unhide_equality_concl (rename_barehypotheses r G) (rename_barehypotheses r J) x (rename_term r A) (rename_term r t1) (rename_term r t2) (rename_term r C))
    -> proof (rename_baresequent r (rule_unhide_equality_concl G J x A t1 t2 C)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma pre_proof_rename_pre_rule_unhide_equality_concl {o} :
  forall {r} {G : @bhyps o} {J} {x} {A} {t1} {t2} {C},
    pre_proof (pre_rule_unhide_equality_concl (rename_barehypotheses r G) (rename_barehypotheses r J) x (rename_term r A) (rename_term r t1) (rename_term r t2) (rename_term r C))
    -> pre_proof (rename_pre_baresequent r (pre_rule_unhide_equality_concl G J x A t1 t2 C)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma proof_rename_rule_thin_hyp {o} :
  forall {r} {G : @bhyps o} {J} {C} {t},
    proof (rename_baresequent r (rule_thin_hyp G J C t))
    -> proof (rule_thin_hyp (rename_barehypotheses r G) (rename_barehypotheses r J) (rename_term r C) (rename_term r t)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
Defined.

Lemma pre_proof_rename_pre_rule_thin_hyp {o} :
  forall {r} {G : @bhyps o} {J} {C},
    pre_proof (rename_pre_baresequent r (pre_rule_thin_hyp G J C))
    -> pre_proof (pre_rule_thin_hyp (rename_barehypotheses r G) (rename_barehypotheses r J) (rename_term r C)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
Defined.

Lemma rule_rename_rule_thin_concl {o} :
  forall {r} {G : @bhyps o} {x} {A} {J} {C} {t},
    proof (rule_thin_concl (rename_barehypotheses r G) x (rename_term r A) (rename_barehypotheses r J) (rename_term r C) (rename_term r t))
    -> proof (rename_baresequent r (rule_thin_concl G x A J C t)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma pre_rule_rename_pre_rule_thin_concl {o} :
  forall {r} {G : @bhyps o} {x} {A} {J} {C},
    pre_proof (pre_rule_thin_concl (rename_barehypotheses r G) x (rename_term r A) (rename_barehypotheses r J) (rename_term r C))
    -> pre_proof (rename_pre_baresequent r (pre_rule_thin_concl G x A J C)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma proof_rename_rule_function_equality_hyp2 {o} :
  forall {r} {H : @bhyps o} {y} {a1} {b1} {x1} {b2} {x2} {i} {e2},
    proof (rename_baresequent r (rule_function_equality_hyp2 H y a1 b1 x1 b2 x2 i e2))
    -> proof (rule_function_equality_hyp2 (rename_barehypotheses r H) y (rename_term r a1) (rename_term r b1) x1 (rename_term r b2) x2 i (rename_term r e2)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma pre_proof_rename_pre_rule_function_equality_hyp2 {o} :
  forall {r} {H : @bhyps o} {y} {a1} {b1} {x1} {b2} {x2} {i},
    pre_proof (rename_pre_baresequent r (pre_rule_function_equality_hyp2 H y a1 b1 x1 b2 x2 i))
    -> pre_proof (pre_rule_function_equality_hyp2 (rename_barehypotheses r H) y (rename_term r a1) (rename_term r b1) x1 (rename_term r b2) x2 i).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma proof_rename_rule_apply_equality_concl {o} :
  forall {r} {H : @bhyps o} {f1} {t1} {f2} {t2} {B} {x},
    proof (rule_apply_equality_concl (rename_barehypotheses r H) (rename_term r f1) (rename_term r t1) (rename_term r f2) (rename_term r t2) (rename_term r B) x)
    -> proof (rename_baresequent r (rule_apply_equality_concl H f1 t1 f2 t2 B x)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_term_subst); auto.
Defined.

Lemma pre_proof_rename_pre_rule_apply_equality_concl {o} :
  forall {r} {H : @bhyps o} {f1} {t1} {f2} {t2} {B} {x},
    pre_proof (pre_rule_apply_equality_concl (rename_barehypotheses r H) (rename_term r f1) (rename_term r t1) (rename_term r f2) (rename_term r t2) (rename_term r B) x)
    -> pre_proof (rename_pre_baresequent r (pre_rule_apply_equality_concl H f1 t1 f2 t2 B x)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_term_subst); auto.
Defined.

Lemma proof_rename_rule_isect_elimination_hyp1 {o} :
  forall {r} {A} {B} {a} {ea} {f} {x} {H : @bhyps o} {J},
    proof (rename_baresequent r (rule_isect_elimination_hyp1 A B a ea f x H J))
    -> proof (rule_isect_elimination_hyp1 (rename_term r A) (rename_term r B) (rename_term r a) (rename_term r ea) f x (rename_barehypotheses r H) (rename_barehypotheses r J)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
Defined.

Lemma pre_proof_rename_pre_rule_isect_elimination_hyp1 {o} :
  forall {r} {A} {B} {a} {f} {x} {H : @bhyps o} {J},
    pre_proof (rename_pre_baresequent r (pre_rule_isect_elimination_hyp1 A B a f x H J))
    -> pre_proof (pre_rule_isect_elimination_hyp1 (rename_term r A) (rename_term r B) (rename_term r a) f x (rename_barehypotheses r H) (rename_barehypotheses r J)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
Defined.

Lemma proof_rename_rule_isect_elimination_hyp2 {o} :
  forall {r} {A} {B} {C} {a} {e} {f} {x} {z} {H : @bhyps o} {J},
    proof (rename_baresequent r (rule_isect_elimination_hyp2 A B C a e f x z H J))
    -> proof (rule_isect_elimination_hyp2 (rename_term r A) (rename_term r B) (rename_term r C) (rename_term r a) (rename_term r e) f x z (rename_barehypotheses r H) (rename_barehypotheses r J)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma pre_proof_rename_pre_rule_isect_elimination_hyp2 {o} :
  forall {r} {A} {B} {C} {a} {f} {x} {z} {H : @bhyps o} {J},
    pre_proof (rename_pre_baresequent r (pre_rule_isect_elimination_hyp2 A B C a f x z H J))
    -> pre_proof (pre_rule_isect_elimination_hyp2 (rename_term r A) (rename_term r B) (rename_term r C) (rename_term r a) f x z (rename_barehypotheses r H) (rename_barehypotheses r J)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma proof_rename_rule_isect_elimination_concl {o} :
  forall {r} {A} {B} {C} {e} {f} {x} {z} {H : @bhyps o} {J},
    proof (rule_isect_elimination_concl (rename_term r A) (rename_term r B) (rename_term r C) (rename_term r e) f x z (rename_barehypotheses r H) (rename_barehypotheses r J))
    -> proof (rename_baresequent r (rule_isect_elimination_concl A B C e f x z H J)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
  repeat (rewrite rename_term_subst); auto.
Defined.

Lemma pre_proof_rename_pre_rule_isect_elimination_concl {o} :
  forall {r} {A} {B} {C} {f} {x} {H : @bhyps o} {J},
    pre_proof (pre_rule_isect_elimination_concl (rename_term r A) (rename_term r B) (rename_term r C) f x (rename_barehypotheses r H) (rename_barehypotheses r J))
    -> pre_proof (rename_pre_baresequent r (pre_rule_isect_elimination_concl A B C f x H J)).
Proof.
  introv prf; simpl in *; auto.
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma proof_rename_rule_isect_elimination2_hyp2 {o} :
  forall {r} {A} {B} {C} {a} {e} {f} {x} {y} {z} {H : @bhyps o} {J},
    proof (rename_baresequent r (rule_isect_elimination2_hyp2 A B C a e f x y z H J))
    -> proof (rule_isect_elimination2_hyp2 (rename_term r A) (rename_term r B) (rename_term r C) (rename_term r a) (rename_term r e) f x y z (rename_barehypotheses r H) (rename_barehypotheses r J)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_barehypotheses_snoc in prf; simpl in *; auto).
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma pre_proof_rename_pre_rule_isect_elimination2_hyp2 {o} :
  forall {r} {A} {B} {C} {a} {f} {x} {y} {z} {H : @bhyps o} {J},
    pre_proof (rename_pre_baresequent r (pre_rule_isect_elimination2_hyp2 A B C a f x y z H J))
    -> pre_proof (pre_rule_isect_elimination2_hyp2 (rename_term r A) (rename_term r B) (rename_term r C) (rename_term r a) f x y z (rename_barehypotheses r H) (rename_barehypotheses r J)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_barehypotheses_snoc in prf; simpl in *; auto).
  rewrite rename_barehypotheses_app in prf; simpl in *; auto.
  rewrite rename_barehypotheses_snoc in prf; simpl in *; auto.
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma proof_rename_rule_isect_elimination2_concl {o} :
  forall {r} {A} {B} {C} {e} {f} {x} {y} {z} {H : @bhyps o} {J},
    proof (rule_isect_elimination2_concl (rename_term r A) (rename_term r B) (rename_term r C) (rename_term r e) f x y z (rename_barehypotheses r H) (rename_barehypotheses r J))
    -> proof (rename_baresequent r (rule_isect_elimination2_concl A B C e f x y z H J)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_barehypotheses_snoc; simpl in *; auto).
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
  repeat (rewrite rename_term_subst); auto.
Defined.

Lemma pre_proof_rename_pre_rule_isect_elimination2_concl {o} :
  forall {r} {A} {B} {C} {f} {x} {H : @bhyps o} {J},
    pre_proof (pre_rule_isect_elimination2_concl (rename_term r A) (rename_term r B) (rename_term r C) f x (rename_barehypotheses r H) (rename_barehypotheses r J))
    -> pre_proof (rename_pre_baresequent r (pre_rule_isect_elimination2_concl A B C f x H J)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_barehypotheses_snoc; simpl in *; auto).
  rewrite rename_barehypotheses_app; simpl in *; auto.
  rewrite rename_barehypotheses_snoc; simpl in *; auto.
Defined.

Lemma proof_rename_rule_isect_member_equality_hyp1 {o} :
  forall {r} {H : @bhyps o} {z} {A} {t1} {t2} {B} {x} {e1},
    proof (rename_baresequent r (rule_isect_member_equality_hyp1 H z A t1 t2 B x e1))
    -> proof (rule_isect_member_equality_hyp1 (rename_barehypotheses r H) z (rename_term r A) (rename_term r t1) (rename_term r t2) (rename_term r B) x (rename_term r e1)).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_barehypotheses_snoc in prf; simpl in *; auto).
  repeat (rewrite rename_term_subst in prf); auto.
Defined.

Lemma pre_proof_rename_pre_rule_isect_member_equality_hyp1 {o} :
  forall {r} {H : @bhyps o} {z} {A} {t1} {t2} {B} {x},
    pre_proof (rename_pre_baresequent r (pre_rule_isect_member_equality_hyp1 H z A t1 t2 B x))
    -> pre_proof (pre_rule_isect_member_equality_hyp1 (rename_barehypotheses r H) z (rename_term r A) (rename_term r t1) (rename_term r t2) (rename_term r B) x).
Proof.
  introv prf; simpl in *; auto.
  repeat (rewrite rename_barehypotheses_snoc in prf; simpl in *; auto).
  repeat (rewrite rename_term_subst in prf); auto.
Defined.*)

Lemma implies_covered_rename_vars_hyps {o} :
  forall r {t : @NTerm o} {H : @bhyps o},
    covered t (vars_hyps H)
    -> covered (rename_term r t) (vars_hyps (rename_barehypotheses r H)).
Proof.
  introv cov.
  unfold covered in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_covered_rename_vars_hyps : slow.

Lemma implies_covered_rename_snoc_app_vars_hyps {o} :
  forall r {t : @NTerm o} {H : @bhyps o} {x} {J : @bhyps o},
    covered t (snoc (vars_hyps H) x ++ vars_hyps J)
    -> covered (rename_term r t) (snoc (vars_hyps (rename_barehypotheses r H)) x ++ vars_hyps (rename_barehypotheses r J)).
Proof.
  introv cov.
  unfold covered in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_covered_rename_snoc_app_vars_hyps : slow.

Lemma implies_covered_rename_nh_vars_hyps {o} :
  forall r {t : @NTerm o} {H : @bhyps o},
    covered t (nh_vars_hyps H)
    -> covered (rename_term r t) (nh_vars_hyps (rename_barehypotheses r H)).
Proof.
  introv cov.
  unfold covered in *; autorewrite with slow in *; auto.
Qed.
Hint Resolve implies_covered_rename_nh_vars_hyps : slow.

Definition rename_opnames r names := map (rename_opname r) names.

Definition rename_proof_step {o} (r : renaming) (s : @proof_step o) : proof_step :=
  match s with
  | proof_step_lemma n                          => proof_step_lemma (rename_LemmaName r n)
  | proof_step_lemma_with_extract n             => proof_step_lemma_with_extract (rename_LemmaName r n)
  | proof_step_base_closed                      => proof_step_base_closed
  | proof_step_base_closed2                     => proof_step_base_closed2
  | proof_step_int_equality                     => proof_step_int_equality
  | proof_step_base_equality                    => proof_step_base_equality
  | proof_step_isect_equality y                 => proof_step_isect_equality y
  | proof_step_function_equality y              => proof_step_function_equality y
  | proof_step_isect_member_formation z i       => proof_step_isect_member_formation z i
  | proof_step_hypothesis x                     => proof_step_hypothesis x
  | proof_step_hypothesis_num n                 => proof_step_hypothesis_num n
  | proof_step_cut x B                          => proof_step_cut x (rename_term r B)
  | proof_step_cequiv_computation n             => proof_step_cequiv_computation n
  | proof_step_cequiv_computation_aeq n         => proof_step_cequiv_computation_aeq n
  | proof_step_cequiv_computation_atmost n      => proof_step_cequiv_computation_atmost n
  | proof_step_unfold_abstractions names        => proof_step_unfold_abstractions (rename_opnames r names)
  | proof_step_rev_unfold_abstractions names a  => proof_step_rev_unfold_abstractions (rename_opnames r names) (rename_term r a)
  | proof_step_cequiv_subst_concl x C a b       => proof_step_cequiv_subst_concl x (rename_term r C) (rename_term r a) (rename_term r b)
  | proof_step_cequiv_subst_hyp z x T a b       => proof_step_cequiv_subst_hyp z x (rename_term r T) (rename_term r a) (rename_term r b)
  | proof_step_cequiv_subst_hyp_num n x T a b   => proof_step_cequiv_subst_hyp_num n x (rename_term r T) (rename_term r a) (rename_term r b)
  | proof_step_universe_equality                => proof_step_universe_equality
  | proof_step_hypothesis_equality              => proof_step_hypothesis_equality
  | proof_step_maybe_hidden_hypothesis_equality => proof_step_maybe_hidden_hypothesis_equality
  | proof_step_unhide_equality x                => proof_step_unhide_equality x
  | proof_step_equality_equality                => proof_step_equality_equality
  | proof_step_equality_equality_base           => proof_step_equality_equality_base
  | proof_step_integer_equality                 => proof_step_integer_equality
  | proof_step_introduction t                   => proof_step_introduction (rename_term r t)
  | proof_step_axiom_equality                   => proof_step_axiom_equality
  | proof_step_thin x                           => proof_step_thin x
  | proof_step_thin_num n                       => proof_step_thin_num n
  | proof_step_apply_equality x A B             => proof_step_apply_equality x (rename_term r A) (rename_term r B)
  | proof_step_isect_elimination n a x          => proof_step_isect_elimination n (rename_term r a) x
  | proof_step_isect_elimination2 n a x y       => proof_step_isect_elimination2 n (rename_term r a) x y
  | proof_step_isect_member_equality x i        => proof_step_isect_member_equality x i
  | proof_step_cumulativity i                   => proof_step_cumulativity i
  | proof_step_equality_symmetry                => proof_step_equality_symmetry
  | proof_step_equality_transitivity c          => proof_step_equality_transitivity (rename_term r c)
  | proof_step_cequiv_transitivity c            => proof_step_cequiv_transitivity (rename_term r c)
  | proof_step_approx_refl                      => proof_step_approx_refl
  | proof_step_cequiv_refl                      => proof_step_cequiv_refl
  | proof_step_cequiv_alpha_eq                  => proof_step_cequiv_alpha_eq
  | proof_step_cequiv_approx                    => proof_step_cequiv_approx
  | proof_step_approx_eq                        => proof_step_approx_eq
  | proof_step_cequiv_eq                        => proof_step_cequiv_eq
  end.

Fixpoint rename_proof {o}
         (r : renaming)
         (p : @proof o) : proof :=
  match p with
  | proof_node n c ps => proof_node (rename_proof_step r n) (rename_baresequent r c) (map (rename_proof r) ps)
  end.

(*Fixpoint rename_proof {o}
         (r    : renaming)
         {s    : @baresequent o}
         (prf  : proof s) : proof (rename_baresequent r s) :=
  match prf with
  | proof_from_ctxt c H =>
    proof_named_concl2bseq_rename_implies
      (proof_from_ctxt
         (rename_named_concl r c)
         (rename_barehypotheses r H))
  | proof_isect_eq a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH prf1 prf2 =>
    proof_isect_eq
      (rename_term r a1)
      (rename_term r a2)
      (rename_term r b1)
      (rename_term r b2)
      (rename_term r e1)
      (rename_term r e2)
      x1 x2 y i
      (rename_barehypotheses r H)
      (rename_NVin_vars_hyps r niyH)
      (rename_proof r prf1)
      (proof_rename_rule_isect_equality2_hyp2_implies (rename_proof r prf2))
  | proof_isect_member_formation A x B z i b e H nizH prf1 prf2 =>
    proof_isect_member_formation
      (rename_term r A)
      x
      (rename_term r B)
      z i
      (rename_term r b)
      (rename_term r e)
      (rename_barehypotheses r H)
      (rename_NVin_vars_hyps r nizH)
      (proof_rename_rule_isect_member_formation_hyp1 (rename_proof r prf1))
      (rename_proof r prf2)
  | proof_approx_refl a H =>
    proof_approx_refl
      (rename_term r a)
      (rename_barehypotheses r H)
  | proof_cequiv_refl a H =>
    proof_cequiv_refl
      (rename_term r a)
      (rename_barehypotheses r H)
  | proof_cequiv_alpha_eq a b H aeq =>
    proof_cequiv_alpha_eq
      (rename_term r a)
      (rename_term r b)
      (rename_barehypotheses r H)
      (implies_alpha_eq_term_rename r a b aeq)
  | proof_cequiv_approx a b e1 e2 H prf1 prf2 =>
    proof_cequiv_approx
      (rename_term r a)
      (rename_term r b)
      (rename_term r e1)
      (rename_term r e2)
      (rename_barehypotheses r H)
      (rename_proof r prf1)
      (rename_proof r prf2)
  | proof_approx_eq a1 a2 b1 b2 e1 e2 i H prf1 prf2 =>
    proof_approx_eq
      (rename_term r a1)
      (rename_term r a2)
      (rename_term r b1)
      (rename_term r b2)
      (rename_term r e1)
      (rename_term r e2)
      i
      (rename_barehypotheses r H)
      (rename_proof r prf1)
      (rename_proof r prf2)
  | proof_cequiv_eq a1 a2 b1 b2 e1 e2 i H prf1 prf2 =>
    proof_cequiv_eq
      (rename_term r a1)
      (rename_term r a2)
      (rename_term r b1)
      (rename_term r b2)
      (rename_term r e1)
      (rename_term r e2)
      i
      (rename_barehypotheses r H)
      (rename_proof r prf1)
      (rename_proof r prf2)
  | proof_cut B C t u x H wfB covB nixH prf1 prf2 =>
    proof_rename_rule_cut_concl
      (proof_cut
         (rename_term r B)
         (rename_term r C)
         (rename_term r t)
         (rename_term r u)
         x
         (rename_barehypotheses r H)
         (implies_wf_term_rename_term r B wfB)
         (implies_covered_rename_vars_hyps r covB)
         (rename_NVin_vars_hyps r nixH)
         (rename_proof r prf1)
         (proof_rename_rule_cut_hyp2 (rename_proof r prf2)))
  | proof_hypothesis x A G J =>
    proof_rename_rule_hypothesis_concl
      (proof_hypothesis
         x
         (rename_term r A)
         (rename_barehypotheses r G)
         (rename_barehypotheses r J))
  | proof_cequiv_subst_concl C x a b t e H wfa wfb cova covb prf1 prf2 =>
    implies_proof_rename_rule_cequiv_subst_hyp1
      (proof_cequiv_subst_concl
         (rename_term r C)
         x
         (rename_term r a)
         (rename_term r b)
         (rename_term r t)
         (rename_term r e)
         (rename_barehypotheses r H)
         (implies_wf_term_rename_term r a wfa)
         (implies_wf_term_rename_term r b wfb)
         (implies_covered_rename_vars_hyps r cova)
         (implies_covered_rename_vars_hyps r covb)
         (rename_proof r prf1)
         (proof_rename_rule_cequiv_subst_hyp1 (rename_proof r prf2)))
  | proof_cequiv_subst_hyp H z T x a b J C t e wfa wfb cova covb prf1 prf2 =>
    proof_rename_rule_cequiv_subst_hyp_concl
      (proof_cequiv_subst_hyp
         (rename_barehypotheses r H)
         z
         (rename_term r T)
         x
         (rename_term r a)
         (rename_term r b)
         (rename_barehypotheses r J)
         (rename_term r C)
         (rename_term r t)
         (rename_term r e)
         (implies_wf_term_rename_term r a wfa)
         (implies_wf_term_rename_term r b wfb)
         (implies_covered_rename_vars_hyps r cova)
         (implies_covered_rename_vars_hyps r covb)
         (proof_rename_rule_cequiv_subst_hyp_hyp2 (rename_proof r prf1))
         (proof_rename_rule_cequiv_subst_hyp_hyp1 (rename_proof r prf2)))
  | proof_cequiv_computation lib a b H rd =>
    proof_cequiv_computation
      (rename_lib r lib)
      (rename_term r a)
      (rename_term r b)
      (rename_barehypotheses r H)
      (reduces_to_rename r lib a b rd)
  | proof_cequiv_computation_aeq lib a b c H rd aeq =>
    proof_cequiv_computation_aeq
      (rename_lib r lib)
      (rename_term r a)
      (rename_term r b)
      (rename_term r c)
      (rename_barehypotheses r H)
      (reduces_to_rename r lib a b rd)
      (implies_alpha_eq_term_rename r b c aeq)
  | proof_cequiv_computation_atmost lib a b n H rd =>
    proof_cequiv_computation_atmost
      (rename_lib r lib)
      (rename_term r a)
      (rename_term r b)
      n
      (rename_barehypotheses r H)
      (reduces_in_atmost_k_steps_rename r rd)
  | proof_unfold_abstractions lib abs a e H alla prf1 =>
    proof_unfold_abstractions
      (rename_lib r lib)
      (rename_abs r abs)
      (rename_term r a)
      (rename_term r e)
      (rename_barehypotheses r H)
      (rename_all_abstractions_can_be_unfolded r alla)
      (proof_rename_rule_unfold_abstraction_hyp (rename_proof r prf1))
  | proof_rev_unfold_abstractions lib abs a e H wfa cova alla prf1 =>
    proof_rename_rule_unfold_abstractions_hyp
      (proof_rev_unfold_abstractions
         (rename_lib r lib)
         (rename_abs r abs)
         (rename_term r a)
         (rename_term r e)
         (rename_barehypotheses r H)
         (implies_wf_term_rename_term r a wfa)
         (implies_covered_rename_vars_hyps r cova)
         (rename_all_abstractions_can_be_unfolded r alla)
         (rename_proof r prf1))
  | proof_universe_equality i j H ltij =>
    proof_universe_equality i j (rename_barehypotheses r H) ltij
  | proof_hypothesis_equality x A G J =>
    proof_rename_rule_hypothesis_equality_concl
      (proof_hypothesis_equality
         x
         (rename_term r A)
         (rename_barehypotheses r G)
         (rename_barehypotheses r J))
  | proof_maybe_hidden_hypothesis_equality x A G J b =>
    proof_rename_rule_maybe_hidden_hypothesis_equality_concl
      (proof_maybe_hidden_hypothesis_equality
         x
         (rename_term r A)
         (rename_barehypotheses r G)
         (rename_barehypotheses r J)
         b)
  | proof_unhide_equality x A t1 t2 C e G J prf1 =>
    proof_rename_rule_unhide_equality_concl
      (proof_unhide_equality
         x
         (rename_term r A)
         (rename_term r t1)
         (rename_term r t2)
         (rename_term r C)
         (rename_term r e)
         (rename_barehypotheses r G)
         (rename_barehypotheses r J)
         (proof_rename_rule_unhide_equality_hyp (rename_proof r prf1)))
  | proof_equality_equality A B a1 a2 b1 b2 e1 e2 e3 i H prf1 prf2 prf3 =>
    proof_equality_equality
      (rename_term r A)
      (rename_term r B)
      (rename_term r a1)
      (rename_term r a2)
      (rename_term r b1)
      (rename_term r b2)
      (rename_term r e1)
      (rename_term r e2)
      (rename_term r e3)
      i
      (rename_barehypotheses r H)
      (rename_proof r prf1)
      (rename_proof r prf2)
      (rename_proof r prf3)
  | proof_integer_equality n H =>
    proof_integer_equality
      n
      (rename_barehypotheses r H)
  | proof_introduction t e C H wft covt noutt prf1 =>
    proof_introduction
      (rename_term r t)
      (rename_term r e)
      (rename_term r C)
      (rename_barehypotheses r H)
      (implies_wf_term_rename_term r t wft)
      (implies_covered_rename_nh_vars_hyps r covt)
      (implies_noutokens_rename_term r t noutt)
      (rename_proof r prf1)
  | proof_axiom_equality e a b T H prf1 =>
    proof_axiom_equality
      (rename_term r e)
      (rename_term r a)
      (rename_term r b)
      (rename_term r T)
      (rename_barehypotheses r H)
      (rename_proof r prf1)
  | proof_thin G J A C t x nixJ nixC prf1 =>
    rule_rename_rule_thin_concl
      (proof_thin
         (rename_barehypotheses r G)
         (rename_barehypotheses r J)
         (rename_term r A)
         (rename_term r C)
         (rename_term r t)
         x
         (rename_NVin_free_vars_hyps r nixJ)
         (rename_NVin_free_vars r nixC)
         (proof_rename_rule_thin_hyp (rename_proof r prf1)))
  | proof_function_equality a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH prf1 prf2 =>
    proof_function_equality
      (rename_term r a1)
      (rename_term r a2)
      (rename_term r b1)
      (rename_term r b2)
      (rename_term r e1)
      (rename_term r e2)
      x1 x2 y i
      (rename_barehypotheses r H)
      (rename_NVin_vars_hyps r niyH)
      (rename_proof r prf1)
      (proof_rename_rule_function_equality_hyp2 (rename_proof r prf2))
  | proof_apply_equality A B f1 f2 t1 t2 e1 e2 x H wfA covA prf1 prf2 =>
    proof_rename_rule_apply_equality_concl
      (proof_apply_equality
         (rename_term r A)
         (rename_term r B)
         (rename_term r f1)
         (rename_term r f2)
         (rename_term r t1)
         (rename_term r t2)
         (rename_term r e1)
         (rename_term r e2)
         x
         (rename_barehypotheses r H)
         (implies_wf_term_rename_term r A wfA)
         (implies_covered_rename_vars_hyps r covA)
         (rename_proof r prf1)
         (rename_proof r prf2))
  | proof_isect_elimination A B C a e ea f x z H J wfa cova nizH nizJ dzf prf1 prf2 =>
    proof_rename_rule_isect_elimination_concl
      (proof_isect_elimination
         (rename_term r A)
         (rename_term r B)
         (rename_term r C)
         (rename_term r a)
         (rename_term r e)
         (rename_term r ea)
         f x z
         (rename_barehypotheses r H)
         (rename_barehypotheses r J)
         (implies_wf_term_rename_term r a wfa)
         (implies_covered_rename_snoc_app_vars_hyps r cova)
         (rename_NVin_vars_hyps r nizH)
         (rename_NVin_vars_hyps r nizJ)
         dzf
         (proof_rename_rule_isect_elimination_hyp1 (rename_proof r prf1))
         (proof_rename_rule_isect_elimination_hyp2 (rename_proof r prf2)))
  | proof_isect_elimination2 A B C a e ea f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1 prf2 =>
    proof_rename_rule_isect_elimination2_concl
      (proof_isect_elimination2
         (rename_term r A)
         (rename_term r B)
         (rename_term r C)
         (rename_term r a)
         (rename_term r e)
         (rename_term r ea)
         f x y z
         (rename_barehypotheses r H)
         (rename_barehypotheses r J)
         (implies_wf_term_rename_term r a wfa)
         (implies_covered_rename_snoc_app_vars_hyps r cova)
         (rename_NVin_vars_hyps r nizH)
         (rename_NVin_vars_hyps r nizJ)
         (rename_NVin_vars_hyps r niyH)
         (rename_NVin_vars_hyps r niyJ)
         dzf dzy dyf
         (proof_rename_rule_isect_elimination_hyp1 (rename_proof r prf1))
         (proof_rename_rule_isect_elimination2_hyp2 (rename_proof r prf2)))
  | proof_isect_member_equality H t1 t2 A x B e1 e2 z i nizH prf1 prf2 =>
    proof_isect_member_equality
      (rename_barehypotheses r H)
      (rename_term r t1)
      (rename_term r t2)
      (rename_term r A)
      x
      (rename_term r B)
      (rename_term r e1)
      (rename_term r e2)
      z i
      (rename_NVin_vars_hyps r nizH)
      (proof_rename_rule_isect_member_equality_hyp1 (rename_proof r prf1))
      (rename_proof r prf2)
  | proof_cumulativity H T e i j leij prf1 =>
    proof_cumulativity
      (rename_barehypotheses r H)
      (rename_term r T)
      (rename_term r e)
      i j leij
      (rename_proof r prf1)
  | proof_equality_symmetry H a b T e prf1 =>
    proof_equality_symmetry
      (rename_barehypotheses r H)
      (rename_term r a)
      (rename_term r b)
      (rename_term r T)
      (rename_term r e)
      (rename_proof r prf1)
  | proof_equality_transitivity H a b c T e1 e2 wfc covc prf1 prf2 =>
    proof_equality_transitivity
      (rename_barehypotheses r H)
      (rename_term r a)
      (rename_term r b)
      (rename_term r c)
      (rename_term r T)
      (rename_term r e1)
      (rename_term r e2)
      (implies_wf_term_rename_term r c wfc)
      (implies_covered_rename_vars_hyps r covc)
      (rename_proof r prf1)
      (rename_proof r prf2)
  | proof_cequiv_transitivity H a b c e1 e2 wfc covc prf1 prf2 =>
    proof_cequiv_transitivity
      (rename_barehypotheses r H)
      (rename_term r a)
      (rename_term r b)
      (rename_term r c)
      (rename_term r e1)
      (rename_term r e2)
      (implies_wf_term_rename_term r c wfc)
      (implies_covered_rename_vars_hyps r covc)
      (rename_proof r prf1)
      (rename_proof r prf2)
  end.*)

Fixpoint rename_pre_proof {o}
         (r : renaming)
         (p : @pre_proof o) : pre_proof :=
  match p with
  | pre_proof_hole s => pre_proof_hole (rename_pre_baresequent r s)
  | pre_proof_node n c ps => pre_proof_node (rename_proof_step r n) (rename_pre_baresequent r c) (map (rename_pre_proof r) ps)
  end.

(*Fixpoint rename_pre_proof {o}
         (r    : renaming)
         {s    : @pre_baresequent o}
         (prf  : pre_proof s) : pre_proof (rename_pre_baresequent r s) :=
  match prf with
  | pre_proof_from_ctxt c H =>
    pre_proof_named_concl2pre_bseq_rename_implies
      (pre_proof_from_ctxt
         (rename_named_concl r c)
         (rename_barehypotheses r H))
  | pre_proof_hole s =>
    pre_proof_hole
      (rename_pre_baresequent r s)
  | pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    pre_proof_isect_eq
      (rename_term r a1)
      (rename_term r a2)
      (rename_term r b1)
      (rename_term r b2)
      x1 x2 y i
      (rename_barehypotheses r H)
      (rename_NVin_vars_hyps r niyH)
      (rename_pre_proof r prf1)
      (pre_proof_rename_pre_rule_isect_equality_hyp2_implies (rename_pre_proof r prf2))
  | pre_proof_isect_member_formation A x B z i H nizH prf1 prf2 =>
    pre_proof_isect_member_formation
      (rename_term r A)
      x
      (rename_term r B)
      z i
      (rename_barehypotheses r H)
      (rename_NVin_vars_hyps r nizH)
      (pre_proof_rename_pre_rule_isect_member_formation_hyp1 (rename_pre_proof r prf1))
      (rename_pre_proof r prf2)
  | pre_proof_approx_refl a H =>
    pre_proof_approx_refl
      (rename_term r a)
      (rename_barehypotheses r H)
  | pre_proof_cequiv_refl a H =>
    pre_proof_cequiv_refl
      (rename_term r a)
      (rename_barehypotheses r H)
  | pre_proof_cequiv_alpha_eq a b H aeq =>
    pre_proof_cequiv_alpha_eq
      (rename_term r a)
      (rename_term r b)
      (rename_barehypotheses r H)
      (implies_alpha_eq_term_rename r a b aeq)
  | pre_proof_cequiv_approx a b H prf1 prf2 =>
    pre_proof_cequiv_approx
      (rename_term r a)
      (rename_term r b)
      (rename_barehypotheses r H)
      (rename_pre_proof r prf1)
      (rename_pre_proof r prf2)
  | pre_proof_approx_eq a1 a2 b1 b2 i H prf1 prf2 =>
    pre_proof_approx_eq
      (rename_term r a1)
      (rename_term r a2)
      (rename_term r b1)
      (rename_term r b2)
      i
      (rename_barehypotheses r H)
      (rename_pre_proof r prf1)
      (rename_pre_proof r prf2)
  | pre_proof_cequiv_eq a1 a2 b1 b2 i H prf1 prf2 =>
    pre_proof_cequiv_eq
      (rename_term r a1)
      (rename_term r a2)
      (rename_term r b1)
      (rename_term r b2)
      i
      (rename_barehypotheses r H)
      (rename_pre_proof r prf1)
      (rename_pre_proof r prf2)
  | pre_proof_cut B C x H wfB covB nixH prf1 prf2 =>
    pre_proof_rename_pre_rule_cut_concl
      (pre_proof_cut
         (rename_term r B)
         (rename_term r C)
         x
         (rename_barehypotheses r H)
         (implies_wf_term_rename_term r B wfB)
         (implies_covered_rename_vars_hyps r covB)
         (rename_NVin_vars_hyps r nixH)
         (rename_pre_proof r prf1)
         (pre_proof_rename_pre_rule_cut_hyp2 (rename_pre_proof r prf2)))
  | pre_proof_hypothesis x A G J =>
    pre_proof_rename_pre_rule_hypothesis_concl
      (pre_proof_hypothesis
         x
         (rename_term r A)
         (rename_barehypotheses r G)
         (rename_barehypotheses r J))
  | pre_proof_cequiv_subst_concl C x a b H wfa wfb cova covb prf1 prf2 =>
    implies_pre_proof_rename_pre_rule_cequiv_subst_hyp1
      (pre_proof_cequiv_subst_concl
         (rename_term r C)
         x
         (rename_term r a)
         (rename_term r b)
         (rename_barehypotheses r H)
         (implies_wf_term_rename_term r a wfa)
         (implies_wf_term_rename_term r b wfb)
         (implies_covered_rename_vars_hyps r cova)
         (implies_covered_rename_vars_hyps r covb)
         (rename_pre_proof r prf1)
         (pre_proof_rename_pre_rule_cequiv_subst_hyp1 (rename_pre_proof r prf2)))
  | pre_proof_cequiv_subst_hyp H z T x a b J C wfa wfb cova covb prf1 prf2 =>
    pre_proof_rename_pre_rule_cequiv_subst_hyp_concl
      (pre_proof_cequiv_subst_hyp
         (rename_barehypotheses r H)
         z
         (rename_term r T)
         x
         (rename_term r a)
         (rename_term r b)
         (rename_barehypotheses r J)
         (rename_term r C)
         (implies_wf_term_rename_term r a wfa)
         (implies_wf_term_rename_term r b wfb)
         (implies_covered_rename_vars_hyps r cova)
         (implies_covered_rename_vars_hyps r covb)
         (pre_proof_rename_pre_rule_cequiv_subst_hyp_hyp2 (rename_pre_proof r prf1))
         (pre_proof_rename_pre_rule_cequiv_subst_hyp_hyp1 (rename_pre_proof r prf2)))
  | pre_proof_cequiv_computation lib a b H rd =>
    pre_proof_cequiv_computation
      (rename_lib r lib)
      (rename_term r a)
      (rename_term r b)
      (rename_barehypotheses r H)
      (reduces_to_rename r lib a b rd)
  | pre_proof_cequiv_computation_aeq lib a b c H rd aeq =>
    pre_proof_cequiv_computation_aeq
      (rename_lib r lib)
      (rename_term r a)
      (rename_term r b)
      (rename_term r c)
      (rename_barehypotheses r H)
      (reduces_to_rename r lib a b rd)
      (implies_alpha_eq_term_rename r b c aeq)
  | pre_proof_cequiv_computation_atmost lib a b n H rd =>
    pre_proof_cequiv_computation_atmost
      (rename_lib r lib)
      (rename_term r a)
      (rename_term r b)
      n
      (rename_barehypotheses r H)
      (reduces_in_atmost_k_steps_rename r rd)
  | pre_proof_unfold_abstractions lib abs a H alla prf1 =>
    pre_proof_unfold_abstractions
      (rename_lib r lib)
      (rename_abs r abs)
      (rename_term r a)
      (rename_barehypotheses r H)
      (rename_all_abstractions_can_be_unfolded r alla)
      (pre_proof_rename_pre_rule_unfold_abstraction_hyp (rename_pre_proof r prf1))
  | pre_proof_rev_unfold_abstractions lib abs a H wfa cova alla prf1 =>
    pre_proof_rename_pre_rule_unfold_abstractions_hyp
      (pre_proof_rev_unfold_abstractions
         (rename_lib r lib)
         (rename_abs r abs)
         (rename_term r a)
         (rename_barehypotheses r H)
         (implies_wf_term_rename_term r a wfa)
         (implies_covered_rename_vars_hyps r cova)
         (rename_all_abstractions_can_be_unfolded r alla)
         (rename_pre_proof r prf1))
  | pre_proof_universe_equality i j H ltij =>
    pre_proof_universe_equality i j (rename_barehypotheses r H) ltij
  | pre_proof_hypothesis_equality x A G J =>
    pre_proof_rename_pre_rule_hypothesis_equality_concl
      (pre_proof_hypothesis_equality
         x
         (rename_term r A)
         (rename_barehypotheses r G)
         (rename_barehypotheses r J))
  | pre_proof_maybe_hidden_hypothesis_equality x A G J b =>
    pre_proof_rename_pre_rule_maybe_hidden_hypothesis_equality_concl
      (pre_proof_maybe_hidden_hypothesis_equality
         x
         (rename_term r A)
         (rename_barehypotheses r G)
         (rename_barehypotheses r J)
         b)
  | pre_proof_unhide_equality x A t1 t2 C G J prf1 =>
    pre_proof_rename_pre_rule_unhide_equality_concl
      (pre_proof_unhide_equality
         x
         (rename_term r A)
         (rename_term r t1)
         (rename_term r t2)
         (rename_term r C)
         (rename_barehypotheses r G)
         (rename_barehypotheses r J)
         (pre_proof_rename_pre_rule_unhide_equality_hyp (rename_pre_proof r prf1)))
  | pre_proof_equality_equality A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
    pre_proof_equality_equality
      (rename_term r A)
      (rename_term r B)
      (rename_term r a1)
      (rename_term r a2)
      (rename_term r b1)
      (rename_term r b2)
      i
      (rename_barehypotheses r H)
      (rename_pre_proof r prf1)
      (rename_pre_proof r prf2)
      (rename_pre_proof r prf3)
  | pre_proof_integer_equality n H =>
    pre_proof_integer_equality
      n
      (rename_barehypotheses r H)
  | pre_proof_introduction t C H wft covt noutt prf1 =>
    pre_proof_introduction
      (rename_term r t)
      (rename_term r C)
      (rename_barehypotheses r H)
      (implies_wf_term_rename_term r t wft)
      (implies_covered_rename_nh_vars_hyps r covt)
      (implies_noutokens_rename_term r t noutt)
      (rename_pre_proof r prf1)
  | pre_proof_axiom_equality a b T H prf1 =>
    pre_proof_axiom_equality
      (rename_term r a)
      (rename_term r b)
      (rename_term r T)
      (rename_barehypotheses r H)
      (rename_pre_proof r prf1)
  | pre_proof_thin G J A C x nixJ nixC prf1 =>
    pre_rule_rename_pre_rule_thin_concl
      (pre_proof_thin
         (rename_barehypotheses r G)
         (rename_barehypotheses r J)
         (rename_term r A)
         (rename_term r C)
         x
         (rename_NVin_free_vars_hyps r nixJ)
         (rename_NVin_free_vars r nixC)
         (pre_proof_rename_pre_rule_thin_hyp (rename_pre_proof r prf1)))
  | pre_proof_function_equality a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    pre_proof_function_equality
      (rename_term r a1)
      (rename_term r a2)
      (rename_term r b1)
      (rename_term r b2)
      x1 x2 y i
      (rename_barehypotheses r H)
      (rename_NVin_vars_hyps r niyH)
      (rename_pre_proof r prf1)
      (pre_proof_rename_pre_rule_function_equality_hyp2 (rename_pre_proof r prf2))
  | pre_proof_apply_equality A B f1 f2 t1 t2 x H wfA covA prf1 prf2 =>
    pre_proof_rename_pre_rule_apply_equality_concl
      (pre_proof_apply_equality
         (rename_term r A)
         (rename_term r B)
         (rename_term r f1)
         (rename_term r f2)
         (rename_term r t1)
         (rename_term r t2)
         x
         (rename_barehypotheses r H)
         (implies_wf_term_rename_term r A wfA)
         (implies_covered_rename_vars_hyps r covA)
         (rename_pre_proof r prf1)
         (rename_pre_proof r prf2))
  | pre_proof_isect_elimination A B C a f x z H J wfa cova nizH nizJ dzf prf1 prf2 =>
    pre_proof_rename_pre_rule_isect_elimination_concl
      (pre_proof_isect_elimination
         (rename_term r A)
         (rename_term r B)
         (rename_term r C)
         (rename_term r a)
         f x z
         (rename_barehypotheses r H)
         (rename_barehypotheses r J)
         (implies_wf_term_rename_term r a wfa)
         (implies_covered_rename_snoc_app_vars_hyps r cova)
         (rename_NVin_vars_hyps r nizH)
         (rename_NVin_vars_hyps r nizJ)
         dzf
         (pre_proof_rename_pre_rule_isect_elimination_hyp1 (rename_pre_proof r prf1))
         (pre_proof_rename_pre_rule_isect_elimination_hyp2 (rename_pre_proof r prf2)))
  | pre_proof_isect_elimination2 A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1 prf2 =>
    pre_proof_rename_pre_rule_isect_elimination2_concl
      (pre_proof_isect_elimination2
         (rename_term r A)
         (rename_term r B)
         (rename_term r C)
         (rename_term r a)
         f x y z
         (rename_barehypotheses r H)
         (rename_barehypotheses r J)
         (implies_wf_term_rename_term r a wfa)
         (implies_covered_rename_snoc_app_vars_hyps r cova)
         (rename_NVin_vars_hyps r nizH)
         (rename_NVin_vars_hyps r nizJ)
         (rename_NVin_vars_hyps r niyH)
         (rename_NVin_vars_hyps r niyJ)
         dzf dzy dyf
         (pre_proof_rename_pre_rule_isect_elimination_hyp1 (rename_pre_proof r prf1))
         (pre_proof_rename_pre_rule_isect_elimination2_hyp2 (rename_pre_proof r prf2)))
  | pre_proof_isect_member_equality H t1 t2 A x B z i nizH prf1 prf2 =>
    pre_proof_isect_member_equality
      (rename_barehypotheses r H)
      (rename_term r t1)
      (rename_term r t2)
      (rename_term r A)
      x
      (rename_term r B)
      z i
      (rename_NVin_vars_hyps r nizH)
      (pre_proof_rename_pre_rule_isect_member_equality_hyp1 (rename_pre_proof r prf1))
      (rename_pre_proof r prf2)
  | pre_proof_cumulativity H T i j leij prf1 =>
    pre_proof_cumulativity
      (rename_barehypotheses r H)
      (rename_term r T)
      i j leij
      (rename_pre_proof r prf1)
  | pre_proof_equality_symmetry H a b T prf1 =>
    pre_proof_equality_symmetry
      (rename_barehypotheses r H)
      (rename_term r a)
      (rename_term r b)
      (rename_term r T)
      (rename_pre_proof r prf1)
  | pre_proof_equality_transitivity H a b c T wfc covc prf1 prf2 =>
    pre_proof_equality_transitivity
      (rename_barehypotheses r H)
      (rename_term r a)
      (rename_term r b)
      (rename_term r c)
      (rename_term r T)
      (implies_wf_term_rename_term r c wfc)
      (implies_covered_rename_vars_hyps r covc)
      (rename_pre_proof r prf1)
      (rename_pre_proof r prf2)
  | pre_proof_cequiv_transitivity H a b c wfc covc prf1 prf2 =>
    pre_proof_cequiv_transitivity
      (rename_barehypotheses r H)
      (rename_term r a)
      (rename_term r b)
      (rename_term r c)
      (implies_wf_term_rename_term r c wfc)
      (implies_covered_rename_vars_hyps r covc)
      (rename_pre_proof r prf1)
      (rename_pre_proof r prf2)
  end.*)

Lemma implies_isprog_proof2type_rename_proof {o} :
  forall r {p : @proof o},
    isprog (proof2type p) -> isprog (proof2type (rename_proof r p)).
Proof.
  introv isp.
  destruct p; simpl.
  destruct concl; simpl.
  unfold proof2type in *; simpl in *.
  destruct concl; simpl in *; apply implies_isprog_rename_term; auto.
Qed.

Lemma implies_valid_extract_proof2extract_rename_proof {o} :
  forall r {p : @proof o},
    valid_extract (proof2extract p)
    -> valid_extract (proof2extract (rename_proof r p)).
Proof.
  introv valid.
  destruct p; simpl in *.
  destruct concl; simpl in *.
  destruct concl; simpl in *.

  - unfold extract_ax in *; simpl in *.
    apply rename_valid_extract; auto.

  - unfold extract_ax in *; simpl in *; auto.
Qed.

Lemma implies_proof2extract_op_rename_proof {o} :
  forall r (p : @proof o) t,
    proof2extract_op p = Some t
    -> proof2extract_op (rename_proof r p) = Some (rename_term r t).
Proof.
  introv e.
  destruct p, concl; simpl in *.
  destruct concl; simpl in *; ginv; auto.
Qed.

Lemma proof2hyps_rename_proof {o} :
  forall r (p : @proof o),
    proof2hyps (rename_proof r p)
    = rename_barehypotheses r (proof2hyps p).
Proof.
  introv; destruct p, concl; simpl; auto.
Qed.

Lemma implies_valid_extract_of_proof_proof2extract_rename_proof {o} :
  forall r {p : @proof o},
    valid_extract_of_proof p
    -> valid_extract_of_proof (rename_proof r p).
Proof.
  introv valid.
  unfold valid_extract_of_proof in *.

  rewrite proof2hyps_rename_proof.
  destruct (proof2hyps p); simpl in *; auto.

  remember (proof2extract_op p) as e; symmetry in Heqe.
  destruct e; tcsp.
  rewrite (implies_proof2extract_op_rename_proof r p n); auto.
  apply rename_valid_extract; auto.
Qed.

Definition rename_RigidLibraryEntry {o} r (e : @RigidLibraryEntry o) : RigidLibraryEntry :=
  match e with
  | RigidLibraryEntry_abs e => RigidLibraryEntry_abs (rename_library_entry r e)
  | RigidLibraryEntry_proof name prf wf =>
    RigidLibraryEntry_proof
      (rename_LemmaName r name)
      (rename_proof r prf)
      (MkWfProof
         (implies_isprog_proof2type_rename_proof r (wf_proof_type wf))
         (implies_valid_extract_of_proof_proof2extract_rename_proof r (wf_proof_ext wf)))
  end.

Definition rename_RigidLibrary {o} r (lib : @RigidLibrary o) : RigidLibrary :=
  map (rename_RigidLibraryEntry r) lib.

Lemma implies_isprog_pre_proof2type_rename_pre_proof {o} :
  forall r {p : @pre_proof o},
    isprog (pre_proof2type p) -> isprog (pre_proof2type (rename_pre_proof r p)).
Proof.
  introv isp.
  destruct p; simpl; tcsp.

  - destruct concl; simpl.
    unfold pre_proof2type in *; simpl in *.
    destruct pre_concl0; simpl in *; apply implies_isprog_rename_term; auto.

  - destruct concl; simpl.
    unfold pre_proof2type in *; simpl in *.
    destruct pre_concl0; simpl in *; apply implies_isprog_rename_term; auto.
Qed.

Definition rename_pre_proof_seq {o} r (p : @pre_proof_seq o) : pre_proof_seq :=
  match p with
  | MkPreProofSeq name prf (*isp*) =>
    MkPreProofSeq
      (rename_LemmaName r name)
      (rename_pre_proof r prf)
      (*(implies_isprog_pre_proof2type_rename_pre_proof r isp)*)
  end.

Definition rename_pre_proofs {o} r (l : @pre_proofs o) : pre_proofs :=
  map (rename_pre_proof_seq r) l.

Lemma rename_soterm_nterm2soterm {o} :
  forall r (t : @NTerm o),
    rename_soterm r (nterm2soterm t) = nterm2soterm (rename_term r t).
Proof.
  sp_nterm_ind1 t as [v|f|op bs ind] Case; introv; auto.
  simpl; f_equal.
  induction bs; simpl in *; auto.
  rewrite IHbs;[|introv i; eapply ind; eauto].
  destruct a; simpl.
  erewrite ind; eauto.
Qed.

Lemma equal_lib_abs {o} :
  forall o1 o2 vs1 vs2 (t1 t2 : @SOTerm o) c1 c2,
    o1 = o2
    -> vs1 = vs2
    -> t1 = t2
    -> lib_abs o1 vs1 t1 c1 = lib_abs o2 vs2 t2 c2.
Proof.
  introv h1 h2 h3; subst; f_equal; eauto 3 with pi.
Qed.

Lemma rename_term_proof2type {o} :
  forall r (p : @proof o),
    rename_term r (proof2type p) = proof2type (rename_proof r p).
Proof.
  introv.
  destruct p; simpl.
  destruct concl; simpl.
  destruct concl; simpl; auto.
Defined.

Lemma rename_term_proof2extract {o} :
  forall r (p : @proof o),
    rename_term r (proof2extract p)
    = proof2extract (rename_proof r p).
Proof.
  introv.
  destruct p; simpl.
  destruct concl; simpl.
  destruct concl; simpl; auto.
Defined.

Lemma rename_ProofContext_RigidLibrary2ProofContext {o} :
  forall r (l : @RigidLibrary o),
    rename_ProofContext r (RigidLibrary2ProofContext l)
    = RigidLibrary2ProofContext (rename_RigidLibrary r l).
Proof.
  induction l; introv; simpl; auto.
  rewrite <- IHl; clear IHl.
  unfold rename_ProofContext; simpl.
  unfold extend_proof_context; simpl.
  destruct a; simpl; tcsp.

  unfold updLibProofContext; simpl; auto.
  unfold rename_named_concl; simpl.
  rewrite rename_term_proof2type.
  f_equal; f_equal;[].

  unfold extract2def; simpl.

  apply equal_lib_abs; auto.
  rewrite rename_soterm_nterm2soterm.
  rewrite rename_term_proof2extract; auto.
Qed.

Lemma in_PC_conclusion_rename_ProofContext_RigidLibrary2ProofContext_implies {o} :
  forall {c} {r} {l : @RigidLibrary o},
    LIn c (PC_conclusions (rename_ProofContext r (RigidLibrary2ProofContext l)))
    -> LIn c (PC_conclusions (RigidLibrary2ProofContext (rename_RigidLibrary r l))).
Proof.
  introv i.
  rewrite <- rename_ProofContext_RigidLibrary2ProofContext; auto.
Qed.

Lemma reduces_to_rename_ProofContext_RigidLibrary2ProofContext {o} :
  forall {r} {l} {a b : @NTerm o},
    reduces_to (rename_ProofContext r (RigidLibrary2ProofContext l)) a b
    -> reduces_to (RigidLibrary2ProofContext (rename_RigidLibrary r l)) a b.
Proof.
  introv rd.
  rewrite <- rename_ProofContext_RigidLibrary2ProofContext; auto.
Qed.

Lemma reduces_in_atmost_k_steps_rename_ProofContext_RigidLibrary2ProofContext {o} :
  forall {r} {l} {a b : @NTerm o} {k},
    reduces_in_atmost_k_steps (rename_ProofContext r (RigidLibrary2ProofContext l)) a b k
    -> reduces_in_atmost_k_steps (RigidLibrary2ProofContext (rename_RigidLibrary r l)) a b k.
Proof.
  introv rd.
  rewrite <- rename_ProofContext_RigidLibrary2ProofContext; auto.
Qed.

Lemma all_abstraction_can_be_unfolded_rename_ProofContext_RigidLibrary2ProofContext {o} :
  forall {r} {l} {abs} {a : @NTerm o},
    all_abstractions_can_be_unfolded (rename_ProofContext r (RigidLibrary2ProofContext l)) abs a
    -> all_abstractions_can_be_unfolded (RigidLibrary2ProofContext (rename_RigidLibrary r l)) abs a.
Proof.
  introv h.
  rewrite <- rename_ProofContext_RigidLibrary2ProofContext; auto.
Qed.

(*Lemma pre_proof_RigidLibrary2ProofContext_rename_RigidLibrary_pre_rule_unfold_abstractions_hyp_implies {o} :
  forall {r} {l} {abs} {a} {H : @bhyps o},
    pre_proof (pre_rule_unfold_abstractions_hyp (rename_ProofContext r (RigidLibrary2ProofContext l)) abs a H) ->
    pre_proof (pre_rule_unfold_abstractions_hyp (RigidLibrary2ProofContext (rename_RigidLibrary r l)) abs a H).
Proof.
  introv h.
  rewrite rename_ProofContext_RigidLibrary2ProofContext in h; auto.
Qed.

Lemma implies_pre_proof_RigidLibrary2ProofContext_rename_RigidLibrary_pre_rule_unfold_abstractions_hyp {o} :
  forall {r} {l} {abs} {a} {H : @bhyps o},
    pre_proof (pre_rule_unfold_abstractions_hyp (RigidLibrary2ProofContext (rename_RigidLibrary r l)) abs a H) ->
    pre_proof (pre_rule_unfold_abstractions_hyp (rename_ProofContext r (RigidLibrary2ProofContext l)) abs a H).
Proof.
  introv h.
  rewrite rename_ProofContext_RigidLibrary2ProofContext; auto.
Qed.*)

(*Fixpoint rename_ctxt_pre_proof {o}
         (r    : renaming)
         {l    : @RigidLibrary o}
         {s    : pre_baresequent}
         (prf  : pre_proof s)
  : pre_proof s :=
  match prf with
  | pre_proof_from_ctxt _ c H i =>
    pre_proof_from_ctxt
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      c H
      (in_PC_conclusion_rename_ProofContext_RigidLibrary2ProofContext_implies i)
  | pre_proof_hole _ s =>
    pre_proof_hole
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      s
  | pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    pre_proof_isect_eq
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a1 a2 b1 b2 x1 x2 y i H niyH
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_isect_member_formation _ A x B z i H nizH prf1 prf2 =>
    pre_proof_isect_member_formation
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      A x B z i H nizH
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_approx_refl _ a H =>
    pre_proof_approx_refl
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a H
  | pre_proof_cequiv_refl _ a H =>
    pre_proof_cequiv_refl
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a H
  | pre_proof_cequiv_alpha_eq _ a b H aeq =>
    pre_proof_cequiv_alpha_eq
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a b H aeq
  | pre_proof_cequiv_approx _ a b H prf1 prf2 =>
    pre_proof_cequiv_approx
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a b H
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    pre_proof_approx_eq
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a1 a2 b1 b2 i H
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    pre_proof_cequiv_eq
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a1 a2 b1 b2 i H
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_cut _ B C x H wfB covB nixH prf1 prf2 =>
    pre_proof_cut
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      B C x H wfB covB nixH
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_hypothesis _ x A G J =>
    pre_proof_hypothesis
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      x A G J
  | pre_proof_cequiv_subst_concl _ C x a b H wfa wfb cova covb prf1 prf2 =>
    pre_proof_cequiv_subst_concl
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      C x a b H wfa wfb cova covb
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_cequiv_subst_hyp _ H z T x a b J C wfa wfb cova covb prf1 prf2 =>
    pre_proof_cequiv_subst_hyp
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      H z T x a b J C wfa wfb cova covb
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_cequiv_computation _ a b H rd =>
    pre_proof_cequiv_computation
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a b H (reduces_to_rename_ProofContext_RigidLibrary2ProofContext rd)
  | pre_proof_cequiv_computation_aeq _ a b c H rd aeq =>
    pre_proof_cequiv_computation_aeq
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a b c H (reduces_to_rename_ProofContext_RigidLibrary2ProofContext rd) aeq
  | pre_proof_cequiv_computation_atmost _ a b n H rd =>
    pre_proof_cequiv_computation_atmost
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a b n H (reduces_in_atmost_k_steps_rename_ProofContext_RigidLibrary2ProofContext rd)
  | pre_proof_unfold_abstractions _ abs a H alla prf1 =>
    pre_proof_unfold_abstractions
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      abs a H
      (all_abstraction_can_be_unfolded_rename_ProofContext_RigidLibrary2ProofContext alla)
      (pre_proof_RigidLibrary2ProofContext_rename_RigidLibrary_pre_rule_unfold_abstractions_hyp_implies (rename_ctxt_pre_proof r prf1))
  | pre_proof_rev_unfold_abstractions _ abs a H wfa cova alla prf1 =>
    implies_pre_proof_RigidLibrary2ProofContext_rename_RigidLibrary_pre_rule_unfold_abstractions_hyp
      (pre_proof_rev_unfold_abstractions
         (RigidLibrary2ProofContext (rename_RigidLibrary r l))
         abs a H wfa cova
         (all_abstraction_can_be_unfolded_rename_ProofContext_RigidLibrary2ProofContext alla)
         (rename_ctxt_pre_proof r prf1))
  | pre_proof_universe_equality _ i j H ltij =>
    pre_proof_universe_equality
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      i j H ltij
  | pre_proof_hypothesis_equality _ x A G J =>
    pre_proof_hypothesis_equality
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      x A G J
  | pre_proof_maybe_hidden_hypothesis_equality _ x A G J b =>
    pre_proof_maybe_hidden_hypothesis_equality
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      x A G J b
  | pre_proof_unhide_equality _ x A t1 t2 C G J prf1 =>
    pre_proof_unhide_equality
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      x A t1 t2 C G J
      (rename_ctxt_pre_proof r prf1)
  | pre_proof_equality_equality _ A B a1 a2 b1 b2 i H prf1 prf2 prf3 =>
    pre_proof_equality_equality
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      A B a1 a2 b1 b2 i H
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
      (rename_ctxt_pre_proof r prf3)
  | pre_proof_integer_equality _ n H =>
    pre_proof_integer_equality
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      n H
  | pre_proof_introduction _ t C H wft covt noutt prf1 =>
    pre_proof_introduction
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      t C H wft covt noutt
      (rename_ctxt_pre_proof r prf1)
  | pre_proof_axiom_equality _ a b T H prf1 =>
    pre_proof_axiom_equality
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a b T H
      (rename_ctxt_pre_proof r prf1)
  | pre_proof_thin _ G J A C x nixJ nixC prf1 =>
    pre_proof_thin
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      G J A C x nixJ nixC
      (rename_ctxt_pre_proof r prf1)
  | pre_proof_function_equality _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    pre_proof_function_equality
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      a1 a2 b1 b2 x1 x2 y i H niyH
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_apply_equality _ A B f1 f2 t1 t2 x H wfA covA prf1 prf2 =>
    pre_proof_apply_equality
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      A B f1 f2 t1 t2 x H wfA covA
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_isect_elimination _ A B C a f x z H J wfa cova nizH nizJ dzf prf1 prf2 =>
    pre_proof_isect_elimination
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      A B C a f x z H J wfa cova nizH nizJ dzf
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_isect_elimination2 _ A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf prf1 prf2 =>
    pre_proof_isect_elimination2
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      A B C a f x y z H J wfa cova nizH nizJ niyH niyJ dzf dzy dyf
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_isect_member_equality _ H t1 t2 A x B z i nizH prf1 prf2 =>
    pre_proof_isect_member_equality
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      H t1 t2 A x B z i nizH
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_cumulativity _ H T i j leij prf1 =>
    pre_proof_cumulativity
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      H T i j leij
      (rename_ctxt_pre_proof r prf1)
  | pre_proof_equality_symmetry _ H a b T prf1 =>
    pre_proof_equality_symmetry
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      H a b T
      (rename_ctxt_pre_proof r prf1)
  | pre_proof_equality_transitivity _ H a b c T wfc covc prf1 prf2 =>
    pre_proof_equality_transitivity
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      H a b c T wfc covc
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  | pre_proof_cequiv_transitivity _ H a b c wfc covc prf1 prf2 =>
    pre_proof_cequiv_transitivity
      (RigidLibrary2ProofContext (rename_RigidLibrary r l))
      H a b c wfc covc
      (rename_ctxt_pre_proof r prf1)
      (rename_ctxt_pre_proof r prf2)
  end.*)

(*Lemma pre_proofs_rename_ProofContext_implies {o} :
  forall {r} {state : @SoftLibrary o},
    pre_proofs (rename_ProofContext r (RigidLibrary2ProofContext state))
    -> pre_proofs (RigidLibrary2ProofContext (rename_RigidLibrary r (SoftLibrary_lib state))).
Proof.
  introv pp.
  destruct state as [l unf]; simpl in *.
  clear unf.
  unfold pre_proofs in *.
  induction pp.

  - exact [].

  - assert (pre_proof_seq (RigidLibrary2ProofContext (rename_RigidLibrary r l))) as p;[|exact (p :: IHpp)].
    clear pp IHpp.
    destruct a as [n t isp pp].
    apply rename_ctxt_pre_proof in pp.
    exact (MkPreProofSeq n t isp pp).
Defined.*)

Definition SoftLibrary_rename {o}
           (state : @SoftLibrary o)
           (r     : renaming) : UpdRes :=
  let lib := rename_RigidLibrary r (SoftLibrary_lib state) in
  let unf := rename_pre_proofs r (SoftLibrary_unfinished state) in
  MkUpdRes
    (MkSoftLibrary lib unf)
    [renamed].

Definition SoftLibrary_add_abs {o} state (abs : @Abstraction o) :=
  match abs with
  | MkAbstraction opabs vars rhs correct =>
    SoftLibrary_add_def state opabs vars rhs correct
  end.

Definition update {o}
           (state : @SoftLibrary o)
           (cmd   : command) : UpdRes :=
  match cmd with
  | COM_add_def abs =>
    SoftLibrary_add_abs state abs

  | COM_finish_proof name =>
    SoftLibrary_finish_proof state name

  | COM_update_proof name addr step =>
    SoftLibrary_update_proof state name addr step

  | COM_start_proof name C (*isp*) =>
    SoftLibrary_start_proof state name C (*isp*)

  | COM_find_holes name =>
    SoftLibrary_find_holes state name

  | COM_find_sequent_at_address name addr =>
    SoftLibrary_find_hole state name addr

  | COM_rename o1 o2 =>
    SoftLibrary_rename state (o1, o2)
  end.

Fixpoint update_list {o}
         (state : @SoftLibrary o)
         (cmds  : commands) : UpdRes :=
  match cmds with
  | [] => MkUpdRes state []
  | cmd :: cmds =>
    let (s1,ms1) := update state cmd in
    match update_list s1 cmds with
    | MkUpdRes s2 ms2 => MkUpdRes s2 (ms2 ++ ms1)
    end
  end.

Definition initRigidLibrary {o} : @RigidLibrary o := [].

Definition initUnfinished {o} : @pre_proofs o := [].

Definition initSoftLibrary {o} : @SoftLibrary o :=
  MkSoftLibrary initRigidLibrary initUnfinished.

Definition update_list_from_init {o} (cmds : commands) : @UpdRes o :=
  update_list initSoftLibrary cmds.

Definition valid_pre_proof_seq_context {o} (ctxt : ProofContext) (p : @pre_proof_seq o) :=
  valid_pre_proof_context ctxt (pre_proof_seq_proof p).

Definition valid_pre_proofs_context {o} (ctxt : ProofContext) (ps : @pre_proofs o) :=
  forall p, LIn p ps -> valid_pre_proof_seq_context ctxt p.

(* Should we add this to SoftLibrary *)
Definition ValidSoftLibrary {o} (state : @SoftLibrary o) :=
  (ValidRigidLibrary state)
    # valid_pre_proofs_context (RigidLibrary2ProofContext state) (SoftLibrary_unfinished state).

Lemma matching_entry_sign_rename_opabs :
  forall r o1 o2,
    matching_entry_sign (rename_opabs r o1) (rename_opabs r o2)
    <=> matching_entry_sign o1 o2.
Proof.
  introv.
  unfold matching_entry_sign.
  destruct o1, o2; simpl.
  split; intro h; repnd; dands; subst; auto.
  apply eq_rename_opname_implies in h0; auto.
Qed.

Lemma opname2opabs_rename_opname :
  forall r name,
    opname2opabs (rename_opname r name)
    = rename_opabs r (opname2opabs name).
Proof.
  introv.
  unfold opname2opabs; simpl; auto.
Qed.

Lemma wf_csequent_rename {o} :
  forall r {s : @baresequent o},
    wf_csequent s -> wf_csequent (rename_baresequent r s).
Proof.
  introv wf.
  unfold wf_csequent in *; simpl in *; repnd.
  dands; eauto 3 with slow.

  - unfold closed_type in *; destruct s, concl; simpl in *; eauto 3 with slow.

  - unfold closed_extract in *; destruct s, concl; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve wf_csequent_rename : slow.

Lemma implies_mon_true_sequent_wf {o} :
  forall r l (stmt ext : @NTerm o),
    mon_true_sequent_wf (RigidLibrary2ProofContext l) (NLemma stmt ext)
    -> mon_true_sequent_wf
         (rename_ProofContext r (RigidLibrary2ProofContext l))
         (NLemma (rename_term r stmt) (rename_term r ext)).
Proof.
  introv strue.
  unfold mon_true_sequent_wf, sequent_true_ext_lib_wf in *; exrepnd.
  exists (wf_csequent_rename r c).
  apply (renaming_preserves_sequent_true_ext_lib r) in strue0.
  unfold rename_ProofContext; simpl.

  match goal with
  | [ H : sequent_true_ext_lib _ ?s1 |- sequent_true_ext_lib _ ?s2] =>
    assert (s2 = s1) as xx;[|rewrite xx; auto];[]
  end.
  apply eq_csequent; simpl.
  apply eq_ctsequent; simpl.
  apply eq_sequent; simpl; auto.
Qed.

Lemma map_proof2bseq_rename_proof_swap {o} :
  forall r (ps : list (@proof o)),
    map proof2bseq (map (rename_proof r) ps)
    = map (rename_baresequent r) (map proof2bseq ps).
Proof.
  induction ps; introv; simpl; auto.
  rewrite IHps; f_equal; clear IHps.
  destruct a; simpl; auto.
Qed.

Lemma free_vars_hyps_rename_barehypotheses {o} :
  forall r (H : @bhyps o),
    free_vars_hyps (rename_barehypotheses r H)
    = free_vars_hyps H.
Proof.
  unfold rename_barehypotheses; introv; autorewrite with slow; auto.
  induction H; simpl; tcsp.
  rewrite IHlist; clear IHlist.
  destruct a; simpl; f_equal.
  unfold hyp_free_vars; simpl; autorewrite with slow; auto.
Qed.
Hint Rewrite @free_vars_hyps_rename_barehypotheses : slow.

Lemma length_rename_barehypotheses {o} :
  forall r (H : @bhyps o),
    length (rename_barehypotheses r H) = length H.
Proof.
  unfold rename_barehypotheses; introv; autorewrite with slow; auto.
Qed.
Hint Rewrite @length_rename_barehypotheses : slow.

Hint Rewrite @rename_barehypotheses_snoc : ren.
Hint Rewrite @rename_barehypotheses_app : ren.
Hint Rewrite @rename_term_subst : ren.
Hint Rewrite @rename_term_unfold_abstractions : ren.

Hint Resolve rename_all_abstractions_can_be_unfolded : slow.

Lemma rename_find_hypotheses_name_from_nat {o} :
  forall r (H : @bhyps o) n,
    find_hypothesis_name_from_nat (rename_barehypotheses r H) n
    = find_hypothesis_name_from_nat H n.
Proof.
  induction H; introv; simpl; tcsp.
  destruct n; tcsp.
  destruct n; tcsp.
  destruct a; simpl; tcsp.
Qed.

Lemma LemmaName2extract_rename_LemmaName {o} :
  forall r name,
    @LemmaName2extract o (rename_LemmaName r name)
    = rename_term r (LemmaName2extract name).
Proof.
  tcsp.
Qed.

Lemma implies_rename_valid_proof_node_context {o} :
  forall r ctxt n (c : @baresequent o) l,
    valid_proof_node_context ctxt n c l
    -> valid_proof_node_context
         (rename_ProofContext r ctxt)
         (rename_proof_step r n)
         (rename_baresequent r c)
         (map (rename_baresequent r) l).
Proof.
  introv valid.
  destruct n; simpl in *; exrepnd; subst.

  - exists (rename_term r T) (rename_barehypotheses r H); simpl; dands; auto.
    apply (rename_in_PC_conclusions r) in valid0; simpl in *; auto.

  - exists (rename_term r T) (rename_term r t) (rename_term r r0) (rename_barehypotheses r H);
      simpl; dands; auto; try rewrite LemmaName2extract_rename_LemmaName; eauto 3 with slow.
    apply (rename_in_PC_conclusions r) in valid0; simpl in *; auto.

  - exists (rename_term r t).
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r x) (rename_term r t).
    repeat (autorewrite with slow ren; simpl; dands; auto).
    apply (reduces_in_atmost_k_steps_rename r) in valid2; simpl in *; auto.

  - exists (rename_barehypotheses r H) i.
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_barehypotheses r H) i.
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2) (rename_term r e1) (rename_term r e2) x1 x2 i; exists (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2) (rename_term r e1) (rename_term r e2) x1 x2 i; exists (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r A) x (rename_term r B) (rename_term r b) (rename_term r e) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r A) (rename_barehypotheses r G) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r A) x (rename_barehypotheses r G) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto).

    rewrite <- (rename_find_hypotheses_name_from_nat r) in valid0.
    autorewrite with slow ren in *; auto.

  - exists (rename_term r C) (rename_term r t) (rename_term r u) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_term r d) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_barehypotheses r H) k.
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r e) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r e) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r t) (rename_term r e) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_barehypotheses r J) (rename_term r C) (rename_term r t) (rename_term r e).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_barehypotheses r J) z (rename_term r C) (rename_term r t) (rename_term r e).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

    rewrite <- (rename_find_hypotheses_name_from_nat r) in valid0.
    repeat (autorewrite with slow ren in *; simpl in *; auto).

  - exists i j (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists x (rename_term r A) (rename_barehypotheses r G) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists x (rename_term r A) (rename_barehypotheses r G) (rename_barehypotheses r J) b.
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r A) (rename_term r t1) (rename_term r t2) (rename_term r C) (rename_term r e) (rename_barehypotheses r G) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r A) (rename_term r B) (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2) (rename_term r e1) (rename_term r e2) (rename_term r e3); exists i (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r A) (rename_term r B) (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2) (rename_term r e1) (rename_term r e2) (rename_term r e3); exists i (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists n (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r e) (rename_term r C) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r e) (rename_term r a) (rename_term r b) (rename_term r T) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r G) (rename_barehypotheses r J) (rename_term r A) (rename_term r C) (rename_term r t).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r G) (rename_barehypotheses r J) x (rename_term r A) (rename_term r C) (rename_term r t).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

    rewrite <- (rename_find_hypotheses_name_from_nat r) in valid0.
    repeat (autorewrite with slow ren in *; simpl in *; auto).

  - exists (rename_term r f1) (rename_term r f2) (rename_term r t1) (rename_term r t2) (rename_term r e1) (rename_term r e2) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r A) (rename_term r B) (rename_term r C) (rename_term r e) (rename_term r ea) f x0 (rename_barehypotheses r H) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

    rewrite <- (rename_find_hypotheses_name_from_nat r) in valid1.
    repeat (autorewrite with slow ren in *; simpl in *; auto).

  - exists (rename_term r A) (rename_term r B) (rename_term r C) (rename_term r e) (rename_term r ea) f x0 (rename_barehypotheses r H) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

    rewrite <- (rename_find_hypotheses_name_from_nat r) in valid1.
    repeat (autorewrite with slow ren in *; simpl in *; auto).

  - exists (rename_barehypotheses r H) (rename_term r t1) (rename_term r t2) (rename_term r A) x0 (rename_term r B) (rename_term r e1) (rename_term r e2).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_term r T) (rename_term r e) j.
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_term r a) (rename_term r b) (rename_term r T) (rename_term r e).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_term r a) (rename_term r b) (rename_term r T) (rename_term r e1) (rename_term r e2).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_term r a) (rename_term r b) (rename_term r e1) (rename_term r e2).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_term r e1) (rename_term r e2) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2) (rename_term r e1) (rename_term r e2) i (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2) (rename_term r e1) (rename_term r e2) i (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).
Qed.

Lemma implies_rename_valid_pre_proof_node_context {o} :
  forall r ctxt n (c : @pre_baresequent o) l,
    valid_pre_proof_node_context ctxt n c l
    -> valid_pre_proof_node_context
         (rename_ProofContext r ctxt)
         (rename_proof_step r n)
         (rename_pre_baresequent r c)
         (map (rename_pre_baresequent r) l).
Proof.
  introv valid.
  destruct n; simpl in *; exrepnd; subst.

  - exists (rename_term r T) (rename_barehypotheses r H); simpl; dands; auto.
    apply (rename_in_PC_conclusions r) in valid0; simpl in *; auto.

  - exists (rename_term r T) (rename_term r t) (rename_term r r0) (rename_barehypotheses r H);
      simpl; dands; auto; try rewrite LemmaName2extract_rename_LemmaName; eauto 3 with slow.
    apply (rename_in_PC_conclusions r) in valid0; simpl in *; auto.

  - exists (rename_term r t).
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r x) (rename_term r t).
    repeat (autorewrite with slow ren; simpl; dands; auto).
    apply (reduces_in_atmost_k_steps_rename r) in valid2; simpl in *; auto.

  - exists (rename_barehypotheses r H) i.
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_barehypotheses r H) i.
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2) x1 x2 i; exists (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2) x1 x2 i; exists (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r A) x (rename_term r B) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r A) (rename_barehypotheses r G) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto).

  - exists (rename_term r A) x (rename_barehypotheses r G) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto).

    rewrite <- (rename_find_hypotheses_name_from_nat r) in valid0.
    repeat (autorewrite with slow ren in *; simpl in *; auto).

  - exists (rename_term r C) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_term r d) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_barehypotheses r H) k.
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_barehypotheses r J) (rename_term r C).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_barehypotheses r J) z (rename_term r C).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

    rewrite <- (rename_find_hypotheses_name_from_nat r) in valid0.
    repeat (autorewrite with slow ren in *; simpl in *; auto).

  - exists i j (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists x (rename_term r A) (rename_barehypotheses r G) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists x (rename_term r A) (rename_barehypotheses r G) (rename_barehypotheses r J) b.
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r A) (rename_term r t1) (rename_term r t2) (rename_term r C) (rename_barehypotheses r G) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r A) (rename_term r B) (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2); exists i (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r A) (rename_term r B) (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2); exists i (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists n (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r C) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_term r T) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r G) (rename_barehypotheses r J) (rename_term r A) (rename_term r C).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r G) (rename_barehypotheses r J) x (rename_term r A) (rename_term r C).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

    rewrite <- (rename_find_hypotheses_name_from_nat r) in valid1.
    repeat (autorewrite with slow ren in *; simpl in *; auto).

  - exists (rename_term r f1) (rename_term r f2) (rename_term r t1) (rename_term r t2) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r A) (rename_term r B) (rename_term r C) f x0 (rename_barehypotheses r H) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

    rewrite <- (rename_find_hypotheses_name_from_nat r) in valid1.
    repeat (autorewrite with slow ren in *; simpl in *; auto).

  - exists (rename_term r A) (rename_term r B) (rename_term r C) f x0 (rename_barehypotheses r H) (rename_barehypotheses r J).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

    rewrite <- (rename_find_hypotheses_name_from_nat r) in valid1.
    repeat (autorewrite with slow ren in *; simpl in *; auto).

  - exists (rename_barehypotheses r H) (rename_term r t1) (rename_term r t2) (rename_term r A) x0 (rename_term r B).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_term r T) j.
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_term r a) (rename_term r b) (rename_term r T).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_term r a) (rename_term r b) (rename_term r T).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_barehypotheses r H) (rename_term r a) (rename_term r b).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a) (rename_term r b) (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2) i (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).

  - exists (rename_term r a1) (rename_term r a2) (rename_term r b1) (rename_term r b2) i (rename_barehypotheses r H).
    repeat (autorewrite with slow ren; simpl; dands; auto; eauto 2 with slow).
Qed.

Lemma implies_rename_valid_proof_context {o} :
  forall r ctxt (prf : @proof o),
    valid_proof_context ctxt prf
    -> valid_proof_context (rename_ProofContext r ctxt) (rename_proof r prf).
Proof.
  induction prf using proof_better_ind; introv valid; simpl in *; auto.

  inversion valid as [? ? ? valnode imp]; subst; clear valid.
  constructor; auto;
    [|introv i;allrw in_map_iff; exrepnd; subst;apply ind; auto].

  rewrite map_proof2bseq_rename_proof_swap.
  apply implies_rename_valid_proof_node_context; auto.
Qed.

Lemma map_pre_proof2bseq_rename_pre_proof_swap {o} :
  forall r (ps : list (@pre_proof o)),
    map pre_proof2bseq (map (rename_pre_proof r) ps)
    = map (rename_pre_baresequent r) (map pre_proof2bseq ps).
Proof.
  induction ps; introv; simpl; auto.
  rewrite IHps; f_equal; clear IHps.
  destruct a; simpl; auto.
Qed.

Lemma implies_rename_valid_pre_proof_context {o} :
  forall r ctxt (prf : @pre_proof o),
    valid_pre_proof_context ctxt prf
    -> valid_pre_proof_context (rename_ProofContext r ctxt) (rename_pre_proof r prf).
Proof.
  induction prf using pre_proof_better_ind; introv valid; simpl in *; auto.

  inversion valid as [|? ? ? valnode imp]; subst; clear valid.
  constructor; auto;
    [|introv i;allrw in_map_iff; exrepnd; subst;apply ind; auto].

  rewrite map_pre_proof2bseq_rename_pre_proof_swap.
  apply implies_rename_valid_pre_proof_node_context; auto.
Qed.

Lemma proof_has_extract_rename_proof {o} :
  forall r (p : @proof o),
    proof_has_extract (rename_proof r p) = proof_has_extract p.
Proof.
  introv; unfold proof_has_extract.
  destruct p; simpl; simpl.
  destruct concl; simpl.
  destruct concl; simpl; auto.
Qed.
Hint Rewrite @proof_has_extract_rename_proof : slow.

Lemma implies_ValidRigidLibrary_rename {o} :
  forall r (l : @RigidLibrary o),
    ValidRigidLibrary l
    -> ValidRigidLibrary (rename_RigidLibrary r l).
Proof.
  induction l; introv val; simpl in *; auto.
  repnd; dands; tcsp.
  destruct a; simpl in *.

  - unfold entry_not_in_lib in *.
    introv xx; destruct val0.
    unfold in_lib in *; simpl in *; exrepnd.

    rewrite <- rename_ProofContext_RigidLibrary2ProofContext in xx1.
    unfold rename_ProofContext in xx1; simpl in *.
    unfold rename_lib in *.
    allrw List.in_map_iff; exrepnd; subst.
    eexists; dands; eauto.
    destruct e, x; simpl in *.
    allrw matching_entry_sign_rename_opabs; auto.

  - repnd; subst; simpl in *.
    autodimp IHl hyp.
    autorewrite with slow.
    rewrite <- rename_ProofContext_RigidLibrary2ProofContext.
    dands; auto;[| |].

    + apply implies_rename_valid_proof_context; auto.

    + unfold name_not_in_lib in *.
      introv xx; destruct val3.
      unfold in_lib in *; simpl in *; exrepnd.

      unfold rename_lib in *.
      allrw List.in_map_iff; exrepnd; subst.
      eexists; dands; eauto.
      destruct x; simpl in *.
      unfold rename_LemmaName in *; simpl in *.
      rewrite opname2opabs_rename_opname in xx0.
      allrw matching_entry_sign_rename_opabs; auto.

    + apply (implies_mon_true_sequent_wf r) in val0; auto.
      rewrite rename_term_proof2type in val0.
      rewrite rename_term_proof2extract in val0; auto.
Qed.

Definition lemma_in_RigidLibraryEntry {o}
           (s : @baresequent o)
           (e : RigidLibraryEntry) : Type :=
  match e with
  | RigidLibraryEntry_abs e => False
  | RigidLibraryEntry_proof name prf wf =>
    s = named_concl2bseq [] (MkNamedConcl name (proof2type prf)) (*mk_baresequent [] (mk_concl stmt ext)*)
  end.

Fixpoint lemma_in_RigidLibrary {o}
         (s : @baresequent o)
         (l : RigidLibrary) : Type :=
  match l with
  | [] => False
  | entry :: entries =>
    lemma_in_RigidLibraryEntry s entry
    [+]
    lemma_in_RigidLibrary s entries
  end.

Lemma lemma_in_RigidLibrary_named_concl2bseq_iff {o} :
  forall (c : @named_concl o) L,
    lemma_in_RigidLibrary (named_concl2bseq [] c) L
    <=> LIn c (PC_conclusions (RigidLibrary2ProofContext L)).
Proof.
  induction L; simpl; split; introv h; tcsp.

  - repndors.

    + destruct a; simpl in *; tcsp.
      unfold named_concl2bseq, named_concl2concl in *; simpl in *; ginv.
      left.
      destruct c; simpl in *; tcsp.
      unfold mk_bseq in h; ginv; tcsp.

    + apply IHL in h; exrepnd; subst; clear IHL.
      destruct a; simpl; tcsp.

  - destruct a; simpl in *; tcsp.

    + right; apply IHL; clear IHL; auto.

    + repndors; subst; tcsp.
      right; apply IHL; clear IHL; auto.
Qed.

Lemma implies_lemma_in_RigidLibrary_named_concl2bseq {o} :
  forall (c : @named_concl o) L,
    LIn c (PC_conclusions (RigidLibrary2ProofContext L))
    -> lemma_in_RigidLibrary (named_concl2bseq [] c) L.
Proof.
  introv i.
  apply lemma_in_RigidLibrary_named_concl2bseq_iff; auto.
Qed.
Hint Resolve implies_lemma_in_RigidLibrary_named_concl2bseq : slow.

Lemma wf_term_simple_mk_abs {o} :
  forall n, @wf_term o (mk_abs (opname2opabs n) []).
Proof.
  introv; apply wf_term_eq.
  constructor; simpl; tcsp.
Qed.
Hint Resolve wf_term_simple_mk_abs : slow.

Lemma closed_simple_mk_abs {o} :
  forall n, @closed o (mk_abs (opname2opabs n) []).
Proof.
  introv; unfold closed, mk_abs; simpl; auto.
Qed.
Hint Resolve closed_simple_mk_abs : slow.

Lemma noutokens_simple_mk_abs {o} :
  forall n, @noutokens o (mk_abs (opname2opabs n) []).
Proof.
  introv; unfold noutokens, mk_abs; simpl; auto.
Qed.
Hint Resolve noutokens_simple_mk_abs : slow.

Lemma valid_extract_simple_mk_abs {o} :
  forall n, @valid_extract o (mk_abs (opname2opabs n) []).
Proof.
  introv; unfold valid_extract; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve valid_extract_simple_mk_abs : slow.

Lemma wf_sequent_named_concl_no_hyps_implies {o} :
  forall (H : @bhyps o) c,
    wf_hypotheses H
    -> wf_sequent (named_concl2bseq [] c)
    -> wf_sequent (named_concl2bseq H c).
Proof.
  introv wfh wfs.
  unfold wf_sequent in *; simpl in *; repnd; dands; eauto 3 with slow.
  apply vswf_hypotheses_nil_eq; auto.
Qed.
Hint Resolve wf_sequent_named_concl_no_hyps_implies : slow.

Lemma closed_type_named_concl_no_hyps_implies {o} :
  forall (H : @bhyps o) c,
    closed_type [] (named_concl2concl c)
    -> closed_type H (named_concl2concl c).
Proof.
  introv cl; unfold closed_type, covered in *; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve closed_type_named_concl_no_hyps_implies : slow.

Lemma closed_extract_named_concl_no_hyps_implies {o} :
  forall (H : @bhyps o) c,
    closed_extract [] (named_concl2concl c)
    -> closed_extract H (named_concl2concl c).
Proof.
  introv cl; unfold closed_extract, covered in *; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve closed_extract_named_concl_no_hyps_implies : slow.

Lemma wf_csequent_named_concl2bseq_no_hyps_implies {o} :
  forall {H : @bhyps o} {c},
    wf_hypotheses H
    -> wf_csequent (named_concl2bseq [] c)
    -> wf_csequent (named_concl2bseq H c).
Proof.
  introv wfh wfc.
  unfold wf_csequent in *; repnd; simpl in *.
  dands; auto; eauto 3 with slow.
Qed.
Hint Resolve wf_csequent_named_concl2bseq_no_hyps_implies : slow.

Hint Resolve sim_nil : slow.

Lemma equal_lsubstc_nil {o} :
  forall (t : @NTerm o) w s c (c' : cover_vars t []),
    lsubstc t w s c = lsubstc t w [] c'.
Proof.
  introv.
  apply cterm_eq; simpl.
  rewrite csubst_nil.
  rewrite csubst_trivial; auto.
  unfold cover_vars, over_vars in *; simpl in *.
  introv i j.
  allrw subvars_eq.
  apply c' in j; simpl in *; tcsp.
Qed.

Lemma sequent_true_ext_lib_no_hyps_implies {o} :
  forall l H (c : @conclusion o) wf1 wf2 wc ct1 ct2 ce1 ce2,
    sequent_true_ext_lib l (mk_csequent [] c wf1 wc ct1 ce1)
    -> sequent_true_ext_lib l (mk_csequent H c wf2 wc ct2 ce2).
Proof.
  introv strue ext.
  apply strue in ext; clear strue.

  rw @VR_sequent_true_ex in ext; simpl in ext.
  rw @VR_sequent_true_all; simpl.

  introv sim eqh.
  pose proof (ext [] []) as h; clear ext.
  repeat (autodimp h hyp); eauto 3 with slow.
  exrepnd; simpl in *.

  destruct c; simpl in *; exrepnd.

  - introv.
    rewrite (equal_lsubstc_nil _ _ s1 _ pt1).
    rewrite (equal_lsubstc_nil _ _ s2 _ pt2).
    rewrite (equal_lsubstc_nil _ _ s1 _ pC0).
    rewrite (equal_lsubstc_nil _ _ s2 _ pC3).
    auto.

  - rewrite (equal_lsubstc_nil _ _ s1 _ pC0).
    rewrite (equal_lsubstc_nil _ _ s2 _ pC3).
    auto.
Qed.
Hint Resolve sequent_true_ext_lib_no_hyps_implies : slow.

Lemma mon_true_sequent_wf_no_hyps_implies {o} :
  forall l H (c : @named_concl o),
    wf_hypotheses H
    -> mon_true_sequent_wf l (named_concl2bseq [] c)
    -> mon_true_sequent_wf l (named_concl2bseq H c).
Proof.
  introv wf strue.
  unfold mon_true_sequent_wf, sequent_true_ext_lib_wf in *; exrepnd.
  assert (wf_csequent (named_concl2bseq H c)) as w by eauto 2 with slow.
  exists w.

  unfold mk_wcseq in *; simpl in *.
  destruct c; simpl in *.
  unfold named_concl2concl in *; simpl in *.
  destruct c0, w, w, w0; repnd; simpl in *.
  proof_irr; eauto 3 with slow.
Qed.
Hint Resolve mon_true_sequent_wf_no_hyps_implies : slow.

Lemma implies_wf_sequent_simple_mk_abs {o} :
  forall (H : @bhyps o) t e name,
    wf_sequent (mk_baresequent H (mk_concl t e))
    -> wf_sequent (mk_baresequent H (mk_concl t (mk_abs (opname2opabs name) []))).
Proof.
  introv wf; unfold wf_sequent in *; simpl in *; repnd; dands; auto.
  unfold wf_concl in *; simpl in *; repnd; dands; auto; eauto 3 with slow.
Qed.
Hint Resolve implies_wf_sequent_simple_mk_abs : slow.

Lemma implies_closed_type_simple_mk_abs {o} :
  forall (H : @bhyps o) t e name,
    closed_type H (mk_concl t e)
    -> closed_type H (mk_concl t (mk_abs (opname2opabs name) [])).
Proof.
  introv cl.
  unfold closed_type in *; simpl in *; auto.
Qed.
Hint Resolve implies_closed_type_simple_mk_abs : slow.

Lemma implies_closed_extract_simple_mk_abs {o} :
  forall (H : @bhyps o) t e name,
    closed_extract H (mk_concl t e)
    -> closed_extract H (mk_concl t (mk_abs (opname2opabs name) [])).
Proof.
  introv cl.
  unfold closed_extract in *; simpl in *.
  unfold covered in *; simpl in *; auto.
Qed.
Hint Resolve implies_closed_extract_simple_mk_abs : slow.

Lemma matching_entry_opname2opname_same_nil {o} :
  forall n, @matching_entry o (opname2opabs n) (opname2opabs n) [] [].
Proof.
  introv.
  unfold matching_entry; simpl; dands; auto; tcsp.
Qed.
Hint Resolve matching_entry_opname2opname_same_nil : slow.

Lemma sosub_aux_nil_nterm2soterm {o} :
  forall (t : @NTerm o), sosub_aux [] (nterm2soterm t) = t.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv; simpl; tcsp.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_map_l; introv i; destruct x; simpl; f_equal; eapply ind; eauto.
Qed.
Hint Rewrite @sosub_aux_nil_nterm2soterm : slow.

Lemma sosub_nil_nterm2soterm {o} :
  forall (t : @NTerm o), sosub [] (nterm2soterm t) = t.
Proof.
  introv; unfold sosub; simpl; boolvar; tcsp; autorewrite with slow; auto;
    try (complete (destruct n; tcsp)).
Qed.
Hint Rewrite @sosub_nil_nterm2soterm : slow.

Lemma reduces_to_extract2def_cons_simple_mk_abs {o} :
  forall name (e : @NTerm o) valid l,
    reduces_to (extract2def name e valid :: l) (mk_abs (opname2opabs name) []) e.
Proof.
  introv.
  apply reduces_to_if_step.
  csunf.
  unfold compute_step_unfold; simpl.
  unfold compute_step_lib; simpl; boolvar; auto;
    [|apply not_matching_entry_iff in n; destruct n; eauto 3 with slow];[].
  unfold mk_instance; simpl; autorewrite with slow; auto.
Qed.

Lemma implies_sequent_true_ext_lib_simple_mk_abs {o} :
  forall lib (H : @bhyps o) t a b c1 c2,
    reduces_to lib a b
    -> sequent_true_ext_lib lib (mk_wcseq (mk_baresequent H (mk_concl t b)) c1)
    -> sequent_true_ext_lib lib (mk_wcseq (mk_baresequent H (mk_concl t a)) c2).
Proof.
  introv rd strue ext.
  applydup strue in ext; clear strue.
  eapply reduces_to_preserves_lib_extends in rd;[|eauto].

  clear lib ext.
  rename lib0 into lib.

  rw @VR_sequent_true_ex in ext0; simpl in ext0.
  rw @VR_sequent_true_all; simpl.

  introv sim eqh.
  pose proof (ext0 s1 s2) as h; clear ext0.
  repeat (autodimp h hyp); eauto 3 with slow.
  exrepnd; simpl in *.

  introv.
  destruct c1, c2, w0, w, w0, w; repnd; simpl in *.
  proof_irr.

  dands; auto.
  clear h0.

  match goal with
  | [ H : equality _ ?a ?b _ |- equality _ ?c ?d _ ] =>
    assert (cequivc lib a c) as ceq1;
      [|assert (cequivc lib b d) as ceq2;
        [
        |eapply equality_respects_cequivc_left;eauto;
         eapply equality_respects_cequivc_right;eauto]
      ]
  end.

  {
    apply cequivc_sym.
    apply reduces_to_implies_cequiv_lsubst; auto.
  }

  {
    apply cequivc_sym.
    apply reduces_to_implies_cequiv_lsubst; auto.
  }
Qed.

Lemma implies_mon_true_sequent_wf_named {o} :
  forall name (ext : @NTerm o) valid ctxt stmt,
    mon_true_sequent_wf
      (extract2def name ext valid :: ctxt)
      (NLemma stmt ext)
    -> mon_true_sequent_wf
         (extract2def name ext valid :: ctxt)
         (mk_bseq [] (mk_concl stmt (mk_abs (opname2opabs name) []))).
Proof.
  introv strue.
  unfold NLemma, mk_bseq, mon_true_sequent_wf, sequent_true_ext_lib_wf in *; exrepnd.

  assert (wf_csequent ([]) ||- (mk_concl stmt (mk_abs (opname2opabs name) []))) as w.
  { clear strue0; unfold wf_csequent in *; simpl in *; repnd; dands; eauto 3 with slow. }
  exists w.

  eapply implies_sequent_true_ext_lib_simple_mk_abs;[|eauto].
  apply reduces_to_extract2def_cons_simple_mk_abs.
Qed.

Lemma correct_library {o} :
  forall (L : RigidLibrary) (s : @baresequent o),
    ValidRigidLibrary L
    -> lemma_in_RigidLibrary s L
    -> mon_true_sequent_wf (RigidLibrary2ProofContext L) s.
Proof.
  induction L; introv valid i; simpl in *; tcsp.
  repnd; repndors;
    [|apply IHL in i; auto; destruct a; simpl in *; repnd; tcsp;
      apply sequent_true_mono_lib; auto];[].

  destruct a; simpl in *; tcsp;[].
  repnd; subst; simpl in *.
  unfold named_concl2bseq, named_concl2concl; simpl.

  assert (forall s,
             lemma_in_RigidLibrary s L
             -> mon_true_sequent_wf (RigidLibrary2ProofContext L) s) as imp.
  { introv i; apply IHL; auto. }
  clear IHL.

  assert (forall c,
             LIn c (PC_conclusions (RigidLibrary2ProofContext L))
             -> mon_true_sequent_wf (RigidLibrary2ProofContext L) (named_concl2bseq [] c)) as w.
  { introv i; apply imp; auto; clear imp.
    apply lemma_in_RigidLibrary_named_concl2bseq_iff; auto. }
  clear imp.

  remember (RigidLibrary2ProofContext L) as ctxt.
  apply implies_mon_true_sequent_wf_named.

  apply sequent_true_mono_lib; auto.
Qed.

Lemma valid_pre_proofs_context_cons {o} :
  forall ctxt (p : @pre_proof_seq o) ps,
    valid_pre_proof_seq_context ctxt p
    -> valid_pre_proofs_context ctxt ps
    -> valid_pre_proofs_context ctxt (p :: ps).
Proof.
  introv val1 val2 i; simpl in *; repndors; subst; tcsp.
Qed.

Lemma implies_rename_valid_pre_proof_seq_context {o} :
  forall r ctxt (p : @pre_proof_seq o),
    valid_pre_proof_seq_context ctxt p
    -> valid_pre_proof_seq_context (rename_ProofContext r ctxt) (rename_pre_proof_seq r p).
Proof.
  introv valid.
  destruct p; simpl in *.
  unfold valid_pre_proof_seq_context in *; simpl in *.
  apply implies_rename_valid_pre_proof_context; auto.
Qed.

Lemma implies_rename_valid_pre_proofs_context {o} :
  forall r ctxt (ps : @pre_proofs o),
    valid_pre_proofs_context ctxt ps
    -> valid_pre_proofs_context (rename_ProofContext r ctxt) (rename_pre_proofs r ps).
Proof.
  introv valid i.
  unfold rename_pre_proofs in i; allrw in_map_iff; exrepnd; subst.
  apply valid in i1.
  apply implies_rename_valid_pre_proof_seq_context; auto.
Qed.

Lemma implies_valid_pre_proof_node_context_extend_proof_context {o} :
  forall (ctxt : ProofContext) entry n (c : @pre_baresequent o) l,
    !entry_in_lib entry ctxt
    -> valid_pre_proof_node_context ctxt n c l
    -> valid_pre_proof_node_context (extend_proof_context ctxt entry) n c l.
Proof.
  introv ni valid.
  destruct n; simpl in *; exrepnd; subst;
    try (complete (repeat eexists; auto)).

  - exists T H.
    dands; auto.
    apply in_conclusions_extend_proof_context; auto.

  - exists T t r H.
    dands; auto.
    { apply in_conclusions_extend_proof_context; auto. }
    { apply extend_proof_context_preserves_reduces_to; auto. }

  - exists x t.
    dands; auto.
    apply extend_proof_context_preserves_reduces_in_atmost_k_steps; auto.

  - exists a b H.
    dands; auto.
    apply extend_proof_context_preserves_reduces_to; auto.

  - exists a b d H.
    dands; auto.
    apply extend_proof_context_preserves_reduces_to; auto.

  - exists a b H k.
    dands; auto.
    apply extend_proof_context_preserves_reduces_in_atmost_k_steps; auto.

  - exists a H.
    rewrite eq_pre_rule_rev_unfold_abstractions_hyp_extend_proof_context; auto.
    dands; auto.
    apply implies_abstraction_can_be_unfold_extend_proof_context_true; auto.

  - exists H.
    rewrite eq_pre_rule_rev_unfold_abstractions_hyp_extend_proof_context; auto.
    dands; auto.
    apply implies_abstraction_can_be_unfold_extend_proof_context_true; auto.
Qed.

Lemma implies_valid_pre_proof_context_extend_proof_context {o} :
  forall (ctxt : ProofContext) entry (p : @pre_proof o),
    !entry_in_lib entry ctxt
    -> valid_pre_proof_context ctxt p
    -> valid_pre_proof_context (extend_proof_context ctxt entry) p.
Proof.
  induction p using pre_proof_better_ind; introv ni valid; simpl in *; auto.
  inversion valid as [|? ? ? valnode imp]; subst; clear valid.
  constructor;[|introv i; apply ind; tcsp];[].
  apply implies_valid_pre_proof_node_context_extend_proof_context; auto.
Qed.

Lemma implies_valid_pre_proof_seq_context_extend_proof_context {o} :
  forall (ctxt : ProofContext) entry (p : @pre_proof_seq o),
    !entry_in_lib entry ctxt
    -> valid_pre_proof_seq_context ctxt p
    -> valid_pre_proof_seq_context (extend_proof_context ctxt entry) p.
Proof.
  introv ni valid.
  destruct p; simpl in *.
  unfold valid_pre_proof_seq_context in *; simpl in *.
  apply implies_valid_pre_proof_context_extend_proof_context; auto.
Qed.

Lemma implies_valid_pre_proofs_context_extend_proof_context {o} :
  forall (ctxt : ProofContext) entry (ps : @pre_proofs o),
    !entry_in_lib entry ctxt
    -> valid_pre_proofs_context ctxt ps
    -> valid_pre_proofs_context (extend_proof_context ctxt entry) ps.
Proof.
  introv ni valid i.
  apply valid in i; clear valid.
  apply implies_valid_pre_proof_seq_context_extend_proof_context; auto.
Qed.

Lemma find_unfinished_in_pre_proofs_implies_in {o} :
  forall (ps : @pre_proofs o) name p f,
    find_unfinished_in_pre_proofs ps name = (Some p, f)
    -> LIn p ps.
Proof.
  induction ps; introv find; simpl in *; tcsp; ginv.
  boolvar; subst; ginv.

  - inversion find; subst; tcsp.

  - remember (find_unfinished_in_pre_proofs ps name) as w; symmetry in Heqw.
    destruct w.
    inversion find; subst.
    apply IHps in Heqw; tcsp.
Qed.

Lemma in_valid_pre_proofs_context_implies {o} :
  forall ctxt (ps : @pre_proofs o) name p f,
    valid_pre_proofs_context ctxt ps
    -> find_unfinished_in_pre_proofs ps name = (Some p, f)
    -> valid_pre_proof_seq_context ctxt p.
Proof.
  introv valid find.
  apply find_unfinished_in_pre_proofs_implies_in in find.
  apply valid in find; auto.
Qed.
Hint Resolve in_valid_pre_proofs_context_implies : slow.

Lemma proof2bseq_as_proof2pre_bseq {o} :
  forall (p : @proof o),
    proof2bseq p = pre2baresequent (proof2pre_bseq p) (proof2extract p).
Proof.
  introv.
  destruct p; simpl.
  destruct concl; simpl.
  destruct concl; simpl; auto.
Qed.

Lemma finish_pre_proof_node_implies_valid {o} :
  forall ctxt n (c : @pre_baresequent o) l t,
    finish_pre_proof_node n c l = Some t
    -> valid_pre_proof_node_context ctxt n c (map proof2pre_bseq l)
    -> valid_proof_node_context ctxt n (pre2baresequent c t) (map proof2bseq l).
Proof.
  introv fin valnode.
  destruct n; simpl in *; exrepnd; subst; simpl in *.

  - exists T H; simpl; dands; auto; ginv.
    destruct l; ginv.

  - exists T t0 r H; simpl; dands; auto; ginv.
    destruct l; ginv.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists t0.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists x t0.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists H i.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists H i.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists a1 a2 b1 b2 (proof2extract p) (proof2extract p0) x1 x2 i; exists H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists a1 a2 b1 b2 (proof2extract p) (proof2extract p0) x1 x2 i; exists H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists A x B (proof2extract p) (proof2extract p0) H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists A G J.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    rewrite valnode0 in fin; ginv.
    exists A x G J.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists C (proof2extract p0) (proof2extract p) H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    exists a b H; dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    exists a b d H; dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    exists a b H k; dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists a (proof2extract p) H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode0; repnd; GC).
    exists (proof2extract p) H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode0; repnd; GC).
    exists (proof2extract p0) (proof2extract p) H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode0; repnd; GC).
    exists H J C (proof2extract p0) (proof2extract p).
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists H J z C (proof2extract p0) (proof2extract p).
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    exists i j H.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    exists x A G J.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    exists x A G J b.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists A t1 t2 C (proof2extract p) G J.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists A B a1 a2 b1 b2 (proof2extract p) (proof2extract p0) (proof2extract p1); exists i H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists A B a1 a2 b1 b2 (proof2extract p) (proof2extract p0) (proof2extract p1); exists i H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    exists n H.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists (proof2extract p) C H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists (proof2extract p) a b T H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists G J A C (proof2extract p).
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode0; repnd; GC).
    exists G J x A C (proof2extract p).
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode0; repnd; GC).
    exists f1 f2 t1 t2 (proof2extract p) (proof2extract p0) H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode0; repnd; GC).
    exists A B C (proof2extract p0) (proof2extract p) f x0 H J.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    rewrite valnode7, valnode8; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode0; repnd; GC).
    rewrite proof2hyps_as_pre_hyps_proof2pre_bseq in fin.
    rewrite valnode11 in fin; simpl in fin.
    rewrite valnode1 in fin; ginv.
    exists A B C (proof2extract p0) (proof2extract p) f x0 H J.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    rewrite valnode11, valnode12; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists H t1 t2 A x0 B (proof2extract p) (proof2extract p0).
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode0; repnd; GC).
    exists H T (proof2extract p) j.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    rewrite valnode2; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists H a b T (proof2extract p).
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists H a b T (proof2extract p) (proof2extract p0).
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode0; repnd; GC).
    exists H a b (proof2extract p) (proof2extract p0).
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists a H.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists a H.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists a b H.
    dands; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode0; repnd; GC).
    exists a b (proof2extract p) (proof2extract p0) H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists a1 a2 b1 b2 (proof2extract p) (proof2extract p0) i H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.

  - repeat (destruct l; simpl in *; ginv).
    repeat (apply cons_inj in valnode1; repnd; GC).
    exists a1 a2 b1 b2 (proof2extract p) (proof2extract p0) i H.
    dands; auto.
    repeat (rewrite proof2bseq_as_proof2pre_bseq).
    allrw; simpl; auto.
Qed.

Lemma finish_pre_proof_implies_valid {o} :
  forall ctxt (pp : @pre_proof o) p,
    valid_pre_proof_context ctxt pp
    -> finish_pre_proof pp = Some p
    -> valid_proof_context ctxt p.
Proof.
  induction pp using pre_proof_better_ind; introv valid fin; simpl in *; ginv.

  remember (list_option2option_list (map finish_pre_proof ps)) as k; symmetry in Heqk.
  destruct k; ginv;[].

  remember (finish_pre_proof_node n c l) as f; symmetry in Heqf.
  destruct f; ginv.

  inversion valid as [|? ? ? valnode imp]; subst; clear valid.

  constructor; auto.

  {
    apply list_option2option_list_map_finish_pre_proof_implies_eq_proof2bseq in Heqk.
    rewrite Heqk in valnode; clear Heqk.
    apply finish_pre_proof_node_implies_valid; auto.
  }


  {
    introv i.
    eapply in_list_option2option_list_implies in i;[|eauto].
    allrw in_map_iff; exrepnd; subst.
    eapply ind; try exact i1; auto.
  }
Qed.
Hint Resolve finish_pre_proof_implies_valid : slow.

Lemma finish_pre_proof_seq_implies_valid {o} :
  forall ctxt (pp : @pre_proof_seq o) name p wf,
    finish_pre_proof_seq pp = Some (RigidLibraryEntry_proof name p wf)
    -> valid_pre_proof_seq_context ctxt pp
    -> valid_proof_context ctxt p.
Proof.
  introv fin valp.
  destruct pp; simpl in *.
  unfold valid_pre_proof_seq_context in *; simpl in *.
  remember (finish_pre_proof pre_proof_seq_proof0) as w; symmetry in Heqw.
  destruct w; tcsp;[].
  destruct (isprog_dec_op (proof2type p0)); ginv;[].
  destruct (valid_extract_of_proof_dec_op p0); ginv;[].
  inversion fin; subst; eauto 3 with slow.
Qed.
Hint Resolve finish_pre_proof_seq_implies_valid : slow.

Lemma valid_extract_of_proof_implies_proof_has_extract {o} :
  forall (p : @proof o),
    valid_extract_of_proof p
    -> proof_has_extract p = true.
Proof.
  introv valid.
  unfold valid_extract_of_proof in valid.
  destruct (proof2hyps p); simpl in *; tcsp.
  destruct p, concl; simpl in *.
  destruct concl; simpl in *; tcsp.
Qed.
Hint Resolve valid_extract_of_proof_implies_proof_has_extract : slow.

Lemma implies_wf_bseq_proof {o} :
  forall (p : @proof o),
    isprogram (proof2type p)
    -> valid_extract_of_proof p
    -> wf_bseq (NLemma (proof2type p) (proof2extract p)).
Proof.
  introv isp valid.
  unfold wf_bseq; dands; simpl; tcsp; eauto 2 with slow.
  unfold closed_type_baresequent; simpl.
  unfold closed_type; simpl.
  unfold covered.
  apply closed_if_program in isp; rewrite isp; auto.
Qed.
Hint Resolve implies_wf_bseq_proof : slow.

Lemma proof_of_bseq_NLemma {o} :
  forall (p : @proof o),
    valid_extract_of_proof p
    -> proof_of_bseq p (NLemma (proof2type p) (proof2extract p)).
Proof.
  introv valid.
  unfold proof_of_bseq.
  unfold valid_extract_of_proof in valid.
  destruct p, concl; simpl in *.
  destruct hyps0; simpl in *; tcsp.
  unfold NLemma.
  destruct concl; simpl in *; unfold mk_concl; simpl in *; tcsp.
Qed.
Hint Resolve proof_of_bseq_NLemma : slow.

Lemma find_unfinished_in_pre_proofs_implies_subset {o} :
  forall (ps : @pre_proofs o) name x f,
    find_unfinished_in_pre_proofs ps name = (x, f)
    -> subset f ps.
Proof.
  induction ps; introv find; simpl in *; tcsp; ginv.

  { inversion find; subst; tcsp. }

  boolvar; subst; ginv.

  - inversion find; subst; tcsp.

  - remember (find_unfinished_in_pre_proofs ps name) as w; symmetry in Heqw.
    destruct w.
    inversion find; subst; clear find.
    apply IHps in Heqw; tcsp.
    eauto 3 with slow.
Qed.

Lemma find_unfinished_preserves_valid_pre_proofs_context {o} :
  forall ctxt (ps : @pre_proofs o) name x l,
    valid_pre_proofs_context ctxt ps
    -> find_unfinished_in_pre_proofs ps name = (x, l)
    -> valid_pre_proofs_context ctxt l.
Proof.
  introv valid find i.
  apply valid.
  eapply find_unfinished_in_pre_proofs_implies_subset in i;eauto.
Qed.
Hint Resolve find_unfinished_preserves_valid_pre_proofs_context : slow.

Lemma reduces_atmost_k_steps_of_compute_atmost_k_steps2 {o} :
  forall lib k (t : @NTerm o),
    {n : nat
     & n <= k
     # reduces_in_atmost_k_steps lib t (compute_atmost_k_steps lib n t) n}.
Proof.
  induction k; introv; simpl.

  - exists 0; dands; auto.
    rw @reduces_in_atmost_k_steps_0; auto.

  - remember (compute_step lib t) as comp; symmetry in Heqcomp.
    destruct comp as [u|].

    + pose proof (IHk u) as h; clear IHk; exrepnd.
      exists (S n); dands; auto; try lia.
      simpl.
      rw @reduces_in_atmost_k_steps_S; allrw.
      exists u; dands; auto.

    + exists 0; dands; try lia.
      rw @reduces_in_atmost_k_steps_0; auto.
Qed.

Ltac dest_match :=
  match goal with
  | [ H : context[match compute_atmost_k_steps ?l ?n ?t with _ => _ end] |- _ ] =>
    let x := fresh "x" in
    remember (compute_atmost_k_steps l n t) as x; destruct x; simpl in *; ginv;[]
  | [ H : context[match compute_step ?l ?t with _ => _ end] |- _ ] =>
    let x := fresh "x" in
    remember (compute_step l t) as x; destruct x; simpl in *; ginv;[]
  | [ H : context[match ?x with _ => _ end] |- _ ] =>
    destruct x; simpl in *; ginv;[]
  end.

Lemma apply_proof_step_implies_valid_node {o} :
  forall ctxt (c : @pre_baresequent o) step l d,
    apply_proof_step ctxt c step = (Some l, d)
    -> valid_pre_proof_node_context ctxt step c l.
Proof.
  introv appstep.
  destruct step; simpl in *.

  - unfold apply_proof_step_lemma in appstep.
    repeat dest_match.
    exists ctype pre_hyps0; dands; auto.

  - unfold apply_proof_step_lemma_with_extract in appstep.
    repeat dest_match.
    exists n1 n0 (@LemmaName2extract o name) pre_hyps0; dands; auto; eauto 3 with slow.

    (*
    remember (compute_step ctxt (LemmaName2extract name)) as comp; symmetry in Heqcomp; destruct comp.
    { exists n1 n0 n pre_hyps0; dands; auto; eauto 3 with slow. }
    { exists n1 n0 (@LemmaName2extract o name) pre_hyps0; dands; auto; eauto 3 with slow. }
*)

  - unfold apply_proof_step_base_closed in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_base_closed2 in appstep.
    repeat dest_match.

    pose proof (reduces_atmost_k_steps_of_compute_atmost_k_steps ctxt 1 (mk_abs o0 l0)) as h; exrepnd.
    simpl in *; unfold mk_abs in *.
    rw <- Heqx in h0; fold_terms.
    destruct n; simpl in *; try lia;
      [allrw @reduces_in_atmost_k_steps_0; ginv|].
    destruct n; simpl in *; try lia;[].
    repeat eexists; eauto.

  - unfold apply_proof_step_int_equality in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_base_equality in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_isect_eq in appstep.
    repeat dest_match.
    repeat eexists; auto.
    allrw NVin_iff; auto.

  - unfold apply_proof_step_function_equality in appstep.
    repeat dest_match.
    repeat eexists; auto.
    allrw NVin_iff; auto.

  - unfold apply_proof_step_isect_member_formation in appstep.
    repeat dest_match.
    repeat eexists; auto.
    allrw NVin_iff; auto.

  - unfold apply_proof_step_hypothesis in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_hypothesis_num in appstep.
    remember (find_hypothesis_name_from_nat (pre_hyps c) n) as f; symmetry in Heqf.
    destruct f; ginv;[].

    unfold apply_proof_step_hypothesis in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_cut in appstep.
    repeat dest_match.
    repeat eexists; auto.
    allrw NVin_iff; auto.

  - unfold apply_proof_step_cequiv_computation in appstep.
    repeat dest_match.
    pose proof (reduces_atmost_k_steps_of_compute_atmost_k_steps ctxt n n0) as h; exrepnd.
    repeat eexists; auto; eauto.

  - unfold apply_proof_step_cequiv_computation_aeq in appstep.
    repeat dest_match.
    pose proof (reduces_atmost_k_steps_of_compute_atmost_k_steps ctxt n n0) as h; exrepnd.
    repeat eexists;[|eauto]; eauto.

  - unfold apply_proof_step_cequiv_computation_atmost in appstep.
    repeat dest_match.
    pose proof (reduces_atmost_k_steps_of_compute_atmost_k_steps ctxt n n0) as h; exrepnd.
    repeat eexists; eauto.

  - unfold apply_proof_step_unfold_abstractions in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_rev_unfold_abstractions in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_cequiv_subst_concl in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_cequiv_subst_hyp in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_cequiv_subst_hyp_num in appstep.
    remember (find_hypothesis_name_from_nat (pre_hyps c) n) as f; symmetry in Heqf.
    destruct f; ginv;[].

    unfold apply_proof_step_cequiv_subst_hyp in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_universe_eq in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_hypothesis_eq in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_maybe_hidden_hypothesis_eq in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_unhide_equality in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_equality_equality in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_equality_equality_base in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_integer_equality in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_introduction in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_axiom_equality in appstep.
    repeat dest_match.
    repeat eexists; auto.

  - unfold apply_proof_step_thin in appstep.
    repeat dest_match.
    repeat eexists; auto; allrw NVin_iff; auto.

  - unfold apply_proof_step_thin_num in appstep.
    remember (find_hypothesis_name_from_nat (pre_hyps c) n) as f; symmetry in Heqf.
    destruct f; ginv;[].

    unfold apply_proof_step_thin in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_apply_equality in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_isect_elimination_num in appstep.
    remember (find_hypothesis_name_from_nat (pre_hyps c) n) as f; symmetry in Heqf.
    destruct f; ginv;[].

    unfold apply_proof_step_isect_elimination in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_isect_elimination2_num in appstep.
    remember (find_hypothesis_name_from_nat (pre_hyps c) n) as f; symmetry in Heqf.
    destruct f; ginv;[].

    unfold apply_proof_step_isect_elimination2 in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_isect_member_equality in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_cumulativity in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).
    allrw Nat.leb_le; auto.

  - unfold apply_proof_step_equality_symmetry in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_equality_transitivity in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_cequiv_transitivity in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_approx_refl in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_cequiv_refl in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_cequiv_alpha_eq in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_cequiv_approx in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).

  - unfold apply_proof_step_approx_eq in appstep.
    repeat dest_match.
    repeat eexists.

  - unfold apply_proof_step_cequiv_eq in appstep.
    repeat dest_match.
    repeat eexists; auto; try (apply NVin_iff; auto).
Qed.

Lemma apply_proof_step_implies_valid {o} :
  forall ctxt (c : @pre_baresequent o) step l d,
    apply_proof_step ctxt c step = (Some l, d)
    -> valid_pre_proof_context ctxt (pre_proof_node step c (map pre_proof_hole l)).
Proof.
  introv app.
  constructor;[|introv i; allrw in_map_iff; exrepnd; subst; auto];[].
  allrw map_map; unfold compose; simpl.
  rewrite map_id.
  eapply apply_proof_step_implies_valid_node; eauto.
Qed.

Lemma update_pre_proof_preserves_valid_pre_proof {o} :
  forall ctxt (p : @pre_proof o) oaddr addr step p' d,
    valid_pre_proof_context ctxt p
    -> update_pre_proof ctxt p oaddr addr step = (p', d)
    -> valid_pre_proof_context ctxt p'.
Proof.
  induction p using pre_proof_better_ind; introv valid upd; simpl in *.

  - destruct addr; simpl in *; ginv; tcsp.

    remember (apply_proof_step ctxt c step) as w; symmetry in Heqw.
    destruct w as [op msg].
    destruct op; simpl in *; ginv.

    eapply apply_proof_step_implies_valid; eauto.

  - destruct addr.

    remember (apply_proof_step ctxt c step) as w; symmetry in Heqw.
    destruct w as [op msg].
    destruct op; simpl in *; ginv.

    + eapply apply_proof_step_implies_valid; eauto.

    + destruct n0; ginv; tcsp.
      destruct n0; ginv; tcsp.

      * destruct ps; simpl in *; ginv; tcsp.

        remember (update_pre_proof ctxt p oaddr addr step) as u; symmetry in Hequ.
        destruct u; ginv.

        inversion valid as [|? ? ? valnode imp]; subst; clear valid.
        constructor; auto.

        {
          simpl in *.
          pose proof (pre_proof2bseq_update_pre_proof ctxt p oaddr addr step) as q.
          rewrite Hequ in q; simpl in q.
          rewrite q; auto.
        }

        {
          introv i; simpl in *; repndors; subst; tcsp.
          pose proof (imp p) as q; autodimp q hyp.
          eapply ind; eauto.
        }

      * destruct n0; ginv; tcsp.

        {
          destruct ps; simpl in *; ginv; tcsp.
          destruct ps; simpl in *; ginv; tcsp.

          remember (update_pre_proof ctxt p0 oaddr addr step) as u; symmetry in Hequ.
          destruct u; ginv.

          inversion valid as [|? ? ? valnode imp]; subst; clear valid.
          constructor; auto.

          {
            simpl in *.
            pose proof (pre_proof2bseq_update_pre_proof ctxt p0 oaddr addr step) as q.
            rewrite Hequ in q; simpl in q.
            rewrite q; auto.
          }

          {
            introv i; simpl in *; repndors; subst; tcsp.
            pose proof (imp p) as q; autodimp q hyp.
            eapply ind; eauto.
          }
        }

        {
          destruct n0; ginv; tcsp.
          destruct ps; ginv; tcsp.
          destruct ps; ginv; tcsp.
          destruct ps; ginv; tcsp.

          remember (update_pre_proof ctxt p1 oaddr addr step) as u; symmetry in Hequ.
          destruct u; ginv.

          inversion valid as [|? ? ? valnode imp]; subst; clear valid.
          constructor; auto.

          {
            simpl in *.
            pose proof (pre_proof2bseq_update_pre_proof ctxt p1 oaddr addr step) as q.
            rewrite Hequ in q; simpl in q.
            rewrite q; auto.
          }

          {
            introv i; simpl in *; repndors; subst; tcsp.
            pose proof (imp p) as q; autodimp q hyp.
            eapply ind; eauto.
          }
        }
Qed.
Hint Resolve update_pre_proof_preserves_valid_pre_proof : slow.

Lemma update_pre_proof_seq_preserves_valid_pre_proof_seq {o} :
  forall ctxt (p : @pre_proof_seq o) addr step p' d,
    update_pre_proof_seq ctxt p addr step = (p', d)
    -> valid_pre_proof_seq_context ctxt p
    -> valid_pre_proof_seq_context ctxt p'.
Proof.
  introv upd valid.
  unfold valid_pre_proof_seq_context in *.
  destruct p; simpl in *.

  remember (update_pre_proof ctxt pre_proof_seq_proof0 addr addr step) as w.
  symmetry in Heqw.
  destruct w; ginv; simpl in *; eauto 3 with slow.
Qed.
Hint Resolve update_pre_proof_seq_preserves_valid_pre_proof_seq : slow.

Lemma update_pre_proof_seq_preserves_valid_pre_proofs {o} :
  forall ctxt (ps : @pre_proofs o) name p l addr step p' d,
    valid_pre_proofs_context ctxt ps
    -> find_unfinished_in_pre_proofs ps name = (Some p, l)
    -> update_pre_proof_seq ctxt p addr step = (p', d)
    -> valid_pre_proofs_context ctxt (p' :: l).
Proof.
  introv valid find upd i; simpl in *; repndors; subst; tcsp;
    [|apply valid; eauto 3 with slow;
      eapply find_unfinished_in_pre_proofs_implies_subset; eauto];[].
  eapply in_valid_pre_proofs_context_implies in find;[|eauto]; eauto 3 with slow.
Qed.
Hint Resolve update_pre_proof_seq_preserves_valid_pre_proofs : slow.

Lemma mon_true_sequent_wf_named_concl2bseq_implies_isprogram {o} :
  forall lib (c : @named_concl o),
    mon_true_sequent_wf lib (named_concl2bseq [] c)
    -> isprogram (nm_conclusion_type c).
Proof.
  introv mon.
  unfold mon_true_sequent_wf, sequent_true_ext_lib_wf in *; exrepnd.
  clear mon0.
  unfold wf_csequent, wf_sequent in *; simpl in *; repnd.
  unfold named_concl2concl in *; destruct c; simpl in *.
  unfold wf_concl, closed_type in *; simpl in *; repnd.
  split; eauto 3 with slow.
Qed.
Hint Resolve mon_true_sequent_wf_named_concl2bseq_implies_isprogram : slow.

Lemma implies_mon_true_sequent_wf_named_with_extract {o} :
  forall name (ext : @NTerm o) valid ctxt stmt,
    mon_true_sequent_wf
      (extract2def name ext valid :: ctxt)
      (NLemma stmt ext)
    -> mon_true_sequent_wf
         (extract2def name ext valid :: ctxt)
         (mk_bseq [] (mk_concl
                        (mk_equality
                           (LemmaName2extract name)
                           (LemmaName2extract name)
                           stmt)
                        mk_axiom)).
Proof.
  introv strue.
  apply implies_mon_true_sequent_wf_named in strue.
  fold (@LemmaName2extract o name) in *.

  unfold mon_true_sequent_wf in *; exrepnd.
  apply rule_equality_to_extract_true_ext_lib; simpl; auto.

  {
    unfold sequent_true_ext_lib_wf in strue; exrepnd.
    clear strue0.
    unfold wf_csequent, wf_sequent in *.
    unfold wf_bseq; simpl in *.
    unfold wf_concl in *; simpl in *.
    repnd; dands; auto; eauto 2 with slow.
    { apply wf_member; auto. }
    unfold closed_type_baresequent; simpl.
    unfold closed_type in *; simpl in *.
    apply covered_member; dands; auto.
  }

  introv h; repndors; subst; tcsp.
Qed.

Lemma correct_library_with_extract {o} :
  forall (L : RigidLibrary) (c : @named_concl o),
    ValidRigidLibrary L
    -> lemma_in_RigidLibrary (named_concl2bseq [] c) L
    -> mon_true_sequent_wf
         (RigidLibrary2ProofContext L)
         (mk_bseq []
                  (mk_concl
                     (mk_equality
                        (LemmaName2extract (nm_conclusion_name c))
                        (LemmaName2extract (nm_conclusion_name c))
                        (nm_conclusion_type c))
                     mk_axiom)).
Proof.
  induction L; introv valid i; simpl in *; tcsp.
  repnd; repndors;
    [|apply IHL in i; auto; destruct a; simpl in *; repnd; tcsp;
      apply sequent_true_mono_lib; auto].

  destruct a; simpl in *; tcsp;[].
  destruct c as [nm T]; simpl in *; ginv.
  repnd; subst; simpl in *.
  unfold named_concl2bseq, named_concl2concl; simpl.

  assert (forall c,
             lemma_in_RigidLibrary (named_concl2bseq [] c) L
             -> mon_true_sequent_wf
                  (RigidLibrary2ProofContext L)
                  (mk_bseq []
                           (mk_concl
                              (mk_equality
                                 (LemmaName2extract (nm_conclusion_name c))
                                 (LemmaName2extract (nm_conclusion_name c))
                                 (nm_conclusion_type c)) mk_axiom))) as imp.
  { introv i; apply IHL; auto. }
  clear IHL.

  assert (forall c,
             LIn c (PC_conclusions (RigidLibrary2ProofContext L))
             -> mon_true_sequent_wf
                  (RigidLibrary2ProofContext L)
                  (mk_bseq []
                           (mk_concl
                              (mk_equality
                                 (LemmaName2extract (nm_conclusion_name c))
                                 (LemmaName2extract (nm_conclusion_name c))
                                 (nm_conclusion_type c)) mk_axiom))) as w.
  { introv i; apply imp; auto; clear imp.
    apply lemma_in_RigidLibrary_named_concl2bseq_iff; auto. }
  clear imp.

  remember (RigidLibrary2ProofContext L) as ctxt.

  apply implies_mon_true_sequent_wf_named_with_extract.

  apply sequent_true_mono_lib; auto.
Qed.

Hint Resolve vswf_hypotheses_nil_if : slow.

Lemma covered_nil_implies_covered_not_nil {o} :
  forall (t : @NTerm o) l,
    covered t []
    -> covered t l.
Proof.
  introv cov.
  apply covered_implies_closed in cov.
  unfold covered in *; allrw; auto.
Qed.
Hint Resolve covered_nil_implies_covered_not_nil : slow.

Lemma nh_vars_hyps_nil_eq {o} :
  @nh_vars_hyps o [] = [].
Proof.
  unfold nh_vars_hyps; simpl; auto.
Qed.
Hint Rewrite @nh_vars_hyps_nil_eq : slow.

Lemma covered_op_nil_implies_covered_not_nil {o} :
  forall (t : option (@NTerm o)) l,
    covered_op t []
    -> covered_op t l.
Proof.
  introv cov.
  destruct t; simpl in *; auto; eauto 3 with slow.
Qed.
Hint Resolve covered_op_nil_implies_covered_not_nil : slow.

Lemma mon_true_sequent_wf_nil_hyps_implies {o} :
  forall lib (H : @bhyps o) C,
    wf_hypotheses H
    -> mon_true_sequent_wf lib (mk_bseq [] C)
    -> mon_true_sequent_wf lib (mk_bseq H C).
Proof.
  introv wfh mon.
  unfold mon_true_sequent_wf, sequent_true_ext_lib_wf in *; exrepnd.

  assert (wf_csequent (mk_bseq H C)) as wf.
  {
    clear mon0.
    unfold wf_csequent, wf_sequent, closed_type, closed_extract in *; repnd; simpl in *.
    dands; auto; autorewrite with slow in *; eauto 3 with slow.
  }

  exists wf.
  unfold wf_csequent, wf_sequent, mk_wcseq in *; repnd; simpl in *.
  autorewrite with slow in *.
  proof_irr.
  eapply sequent_true_ext_lib_no_hyps_implies; eauto.
Qed.

Lemma update_preserves_validity {o} :
  forall (state : @SoftLibrary o) (cmd : command),
    ValidSoftLibrary state -> ValidSoftLibrary (update state cmd).
Proof.
  introv valid.
  destruct cmd; simpl; auto.

  - (* addition of a definition *)
    destruct state as [L pre_prfs]; simpl in *.
    unfold ValidSoftLibrary in *; simpl in *; repnd.
    destruct abs as [opabs vars rhs correct]; simpl in *.

    destruct (entry_in_lib_dec
                (RigidLibraryEntry_abs (lib_abs opabs vars rhs correct))
                (RigidLibrary2lib L)) as [d|d]; simpl; dands; auto.

    apply (implies_valid_pre_proofs_context_extend_proof_context
             _ (RigidLibraryEntry_abs (lib_abs opabs vars rhs correct))); auto.

  - (* finalizing a proof *)
    destruct state as [L pre_prfs]; simpl in *.
    unfold ValidSoftLibrary in *; simpl in *.
    unfold SoftLibrary_finish_proof; simpl.

    remember (find_unfinished_in_pre_proofs pre_prfs name) as f; symmetry in Heqf; repnd.
    destruct f0; simpl in *; auto;[].

    remember (finish_pre_proof_seq p) as eop; symmetry in Heqeop.
    destruct eop; simpl in *; dands; auto;[|].

    {
      destruct (entry_in_lib_dec r (RigidLibrary2lib L)) as [d|d]; simpl; auto;[].

      destruct r; simpl in *.

      + unfold finish_pre_proof_seq in Heqeop.
        destruct p; simpl in *.
        revert Heqeop.
        remember (finish_pre_proof pre_proof_seq_proof0) as fin; symmetry in Heqfin;
          destruct fin; ginv.

      + destruct wf as [valt vale].
        dands; auto; eauto 3 with slow;[].
        apply (valid_proof _ _ prf); eauto 3 with slow;[|].

        {
          introv wf i; apply implies_lemma_in_RigidLibrary_named_concl2bseq in i.
          apply correct_library in i; auto; eauto 3 with slow.
        }

        {
          introv wf i redto aeq.
          applydup @implies_lemma_in_RigidLibrary_named_concl2bseq in i.

          assert (forall lib',
                     lib_extends lib' (RigidLibrary2ProofContext L)
                     -> cequiv lib' t (LemmaName2extract (nm_conclusion_name c))) as ceq.
          {
            introv ext.
            eapply cequiv_rw_l_eauto;[eauto|].
            apply cequiv_sym.
            apply reduces_to_implies_cequiv;eauto 2 with slow.
          }

          eapply cequiv_preserves_mon_true_sequent_wf.

          {
            introv ext.

            apply cequiv_decomp_equality; dands;
              [apply cequiv_sym; apply ceq; auto
              |apply cequiv_sym; apply ceq; auto
              |apply cequiv_refl].

            applydup @correct_library in i0; auto; eauto 3 with slow.
          }

          apply mon_true_sequent_wf_nil_hyps_implies; auto.
          apply correct_library_with_extract; auto.
        }
    }

    {
      destruct (entry_in_lib_dec r (RigidLibrary2lib L)) as [d|d]; simpl; auto;[].
      apply implies_valid_pre_proofs_context_extend_proof_context; eauto 3 with slow.
    }

  - (* update an unfinished proof *)
    destruct state; simpl in *.
    unfold ValidSoftLibrary in *; simpl in *.
    unfold SoftLibrary_update_proof; simpl.

    remember (find_unfinished_in_pre_proofs SoftLibrary_unfinished0 name) as f; symmetry in Heqf; repnd.
    destruct f0; simpl in *; auto.

    remember (update_pre_proof_seq (RigidLibrary2ProofContext SoftLibrary_lib0) p addr step) as upd.
    symmetry in Hequpd.
    destruct upd; simpl; auto.
    dands; auto; eauto 3 with slow.

  - unfold ValidSoftLibrary in *; simpl in *; repnd; dands; auto.
    apply valid_pre_proofs_context_cons; auto.
    unfold valid_pre_proof_seq_context; simpl; eauto.

  - unfold SoftLibrary_find_holes.
    remember (find_unfinished_in_pre_proofs (SoftLibrary_unfinished state) name) as f; symmetry in Heqf; repnd.
    destruct f0; simpl in *; auto;
      unfold ValidSoftLibrary in *; repnd; simpl in *; dands; auto.

  - unfold SoftLibrary_find_hole.
    remember (find_unfinished_in_pre_proofs (SoftLibrary_unfinished state) name) as f; symmetry in Heqf; repnd.
    destruct f0; simpl in *; auto.
    remember (find_sequent_in_pre_proof_seq p addr) as fh; symmetry in Heqfh.
    destruct fh; simpl; auto.

  - destruct state; simpl in *.
    unfold ValidSoftLibrary in *; simpl in *; repnd; dands; auto.
    { apply implies_ValidRigidLibrary_rename; auto. }
    { rewrite <- rename_ProofContext_RigidLibrary2ProofContext.
      apply implies_rename_valid_pre_proofs_context; auto. }
Qed.

Lemma update_list_preserves_validity {o} :
  forall (cmds : commands) (state : @SoftLibrary o),
    ValidSoftLibrary state -> ValidSoftLibrary (upd_res_state (update_list state cmds)).
Proof.
  induction cmds; introv v; simpl in *; auto.

  remember (update state a) as p; symmetry in Heqp; repnd.
  destruct p; simpl in *.
  pose proof (update_preserves_validity state a) as q; autodimp q hyp.
  rewrite Heqp in q; simpl in q.

  apply IHcmds in q.
  remember (update_list upd_res_state0 cmds) as w; symmetry in Heqw; repnd; simpl in *; auto.
  destruct w; auto.
Qed.

Lemma ValidInitSoftLibrary {o} : @ValidSoftLibrary o initSoftLibrary.
Proof.
  introv; compute; dands; auto; tcsp.
Qed.

Lemma valid_update_list_from_init {o} :
  forall (cmds : commands),
    @ValidSoftLibrary o (update_list_from_init cmds).
Proof.
  introv.
  apply update_list_preserves_validity.
  apply ValidInitSoftLibrary.
Qed.

Record ValidUpdRes {o} :=
  MkValidUpdRes
    {
      valid_upd_res_state :> @UpdRes o;
      valid_upd_res_valid : ValidSoftLibrary valid_upd_res_state;
    }.
Arguments MkValidUpdRes [o] _ _.

Definition initValidUpdRes {o} : @ValidUpdRes o :=
  MkValidUpdRes
    (MkUpdRes initSoftLibrary [])
    (@ValidInitSoftLibrary o).

Definition update_list_with_validity {o} (s : @ValidUpdRes o) (cmds : commands) : ValidUpdRes :=
  MkValidUpdRes
    (update_list s cmds)
    (update_list_preserves_validity cmds s (valid_upd_res_valid s)).

Definition update_list_from_init_with_validity {o}
           (cmds : @commands o) : @ValidUpdRes o :=
  MkValidUpdRes
    (update_list_from_init cmds)
    (valid_update_list_from_init cmds).

(*Arguments pre_proof_isect_member_formation [o] [ctxt] _ _ _ _ _ _ _ _ _.*)
(*Arguments pre_proof_hole [o] [ctxt] _.*)

Definition mk_simple_so_abs {o} (abs : opabs) := @soterm o (Abs abs) [].

(* simple POpid *)
Definition spo : POpid := Build_POpid dset_string True unit.
