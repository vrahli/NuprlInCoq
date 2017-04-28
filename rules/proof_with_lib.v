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

Record pre_baresequent {p} :=
  MkPreBaresequent
    {
      pre_hyps  : @barehypotheses p;
      pre_concl : @pre_conclusion p
    }.

Definition mk_pre_bseq {o} H (c : @pre_conclusion o) : pre_baresequent :=
  MkPreBaresequent o H c.

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

Definition pre_rule_cequiv_concl {o} a b (H : @bhyps o) :=
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

Record wf_conclusion {o} :=
  MkWfConcl
    {
      wf_conclusion_concl : @conclusion o;
      wf_conclusion_wf    : valid_extract (extract_ax wf_conclusion_concl);
    }.

Arguments MkWfConcl [o] _ _.

Definition wf_conclusions {o} := list (@wf_conclusion o).

Definition in_wf_conclusions {o} (c : @conclusion o) (l : wf_conclusions) :=
  LIn c (map wf_conclusion_concl l).

Record ProofContext {o} :=
  MkProofContext
    {
      PC_lib :> @library o;
      PC_conclusions : list (@wf_conclusion o);
    }.

Definition EMPC {o} : @ProofContext o := MkProofContext o [] [].

Definition updLibProofContext {o} (pc : @ProofContext o) (e : library_entry) :=
  MkProofContext
    o
    (e :: PC_lib pc)
    (PC_conclusions pc).

Definition updConclProofContext {o} (pc : @ProofContext o) (c : wf_conclusion) :=
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
    forall c,
      in_wf_conclusions c (@PC_conclusions o ctxt)
      -> pre_proof ctxt (concl2pre_baresequent c)
| pre_proof_hole : forall s, pre_proof ctxt s
| pre_proof_isect_eq :
    forall a1 a2 b1 b2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> pre_proof ctxt (pre_rule_isect_equality_hyp1 a1 a2 i H)
      -> pre_proof ctxt (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H)
      -> pre_proof ctxt (pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
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
      pre_proof hole ctxt (pre_rule_bottom_diverges_concl x H J)
| pre_proof_cut :
    forall B C x H,
      wf_term B
      -> covered B (vars_hyps H)
      -> NVin x (vars_hyps H)
      -> pre_proof hole ctxt (pre_rule_cut_hyp1 H B)
      -> pre_proof hole ctxt (pre_rule_cut_hyp2 H x B C)
      -> pre_proof hole ctxt (pre_rule_cut_concl H C)
| pre_proof_equal_in_base :
    forall a b H,
      pre_proof hole ctxt (pre_rule_equal_in_base_hyp1 a b H)
      -> (forall v, LIn v (free_vars a) -> pre_proof hole ctxt (pre_rule_equal_in_base_hyp2 v H))
      -> pre_proof hole ctxt (pre_rule_equal_in_base_concl a b H)*)
| pre_proof_hypothesis :
    forall x A G J,
      pre_proof ctxt (pre_rule_hypothesis_concl G J A x)
(*| pre_proof_cequiv_subst_concl :
    forall C x a b H,
      wf_term a
      -> wf_term b
      -> covered a (vars_hyps H)
      -> covered b (vars_hyps H)
      -> pre_proof hole ctxt (pre_rule_cequiv_subst_hyp1 H x C b)
      -> pre_proof hole ctxt (pre_rule_cequiv_subst_hyp2 H a b)
      -> pre_proof hole ctxt (pre_rule_cequiv_subst_hyp1 H x C a)
| pre_proof_approx_member_eq :
    forall a b H,
      pre_proof hole ctxt (pre_rule_approx_member_eq_hyp a b H)
      -> pre_proof hole ctxt (pre_rule_approx_member_eq_concl a b H)
| pre_proof_cequiv_computation :
    forall a b H,
      reduces_to ctxt a b
      -> pre_proof hole ctxt (pre_rule_cequiv_concl a b H)
| pre_proof_function_elimination :
    forall A B C a f x z H J,
      wf_term a
      -> covered a (snoc (vars_hyps H) f ++ vars_hyps J)
      -> !LIn z (vars_hyps H)
      -> !LIn z (vars_hyps J)
      -> z <> f
      -> pre_proof hole ctxt (pre_rule_function_elimination_hyp1 A B a f x H J)
      -> pre_proof hole ctxt (pre_rule_function_elimination_hyp2 A B C a f x z H J)
      -> pre_proof hole ctxt (pre_rule_function_elimination_concl A B C f x H J)*).

Inductive proof {o} (ctxt : @ProofContext o) : @baresequent o -> Type :=
| proof_from_ctxt :
    forall c,
      in_wf_conclusions c (@PC_conclusions o ctxt)
      -> proof ctxt (mk_baresequent [] c)
| proof_isect_eq :
    forall a1 a2 b1 b2 e1 e2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> proof ctxt (rule_isect_equality2_hyp1 a1 a2 e1 i H)
      -> proof ctxt (rule_isect_equality2_hyp2 a1 b1 b2 e2 x1 x2 y i H)
      -> proof ctxt (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
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
      proof ctxt (rule_bottom_diverges_concl x H J)
| proof_cut :
    forall B C t u x H,
      wf_term B
      -> covered B (vars_hyps H)
      -> NVin x (vars_hyps H)
      -> proof ctxt (rule_cut_hyp1 H B u)
      -> proof ctxt (rule_cut_hyp2 H x B C t)
      -> proof ctxt (rule_cut_concl H C t x u)
| proof_equal_in_base :
    forall a b e F H,
      proof ctxt (rule_equal_in_base2_hyp1 a b e H)
      -> (forall v (i : LIn v (free_vars a)),
             proof ctxt (rule_equal_in_base2_hyp2 v (F v i) H))
      -> proof ctxt (rule_equal_in_base_concl a b H)*)
| proof_hypothesis :
    forall x A G J,
      proof ctxt (rule_hypothesis_concl G J A x)
(*| proof_cequiv_subst_concl :
    forall C x a b t e H,
      wf_term a
      -> wf_term b
      -> covered a (vars_hyps H)
      -> covered b (vars_hyps H)
      -> proof ctxt (rule_cequiv_subst_hyp1 H x C b t)
      -> proof ctxt (rule_cequiv_subst2_hyp2 H a b e)
      -> proof ctxt (rule_cequiv_subst_hyp1 H x C a t)
| proof_approx_member_eq :
    forall a b e H,
      proof ctxt (rule_approx_member_eq2_hyp a b e H)
      -> proof ctxt (rule_approx_member_eq_concl a b H)
| proof_cequiv_computation :
    forall a b H,
      reduces_to ctxt a b
      -> proof ctxt (rule_cequiv_concl a b H)
| proof_function_elimination :
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
      -> proof ctxt (rule_function_elimination_concl A B C e f x z H J)*).



(* ===========================================================

  The library consists of a list of abstractions and proved lemmas.
  The difference with ProofContext is that we include the proofs of
  lemmas.  [Library2ProofContext] shows how to extract a proof context
  from a Library.

  ============================================================ *)

Definition LemmaName := opname.

Lemma LemmaNameDeq : Deq LemmaName.
Proof.
  introv.
  destruct (String.string_dec x y); auto.
Defined.

Definition opname2opabs (op : opname) : opabs :=
  mk_opabs op [] [].

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

Inductive DepLibrary {o} : @ProofContext o -> Type :=
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
                    (extract2def name ext valid)).

Inductive LibraryEntry {o} :=
| LibraryEntry_abs (e : @library_entry o)
| LibraryEntry_proof
    (ctxt  : @ProofContext o)
    (name  : LemmaName)
    (stmt  : NTerm)
    (ext   : NTerm)
    (isp   : isprogram stmt)
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
      (updConclProofContext ctxt (MkWfConcl (mk_concl stmt ext) valid))
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

Lemma lemma_in_Library_iff {o} :
  forall (s : @baresequent o) L,
    lemma_in_Library s L
    <=> {c : conclusion
         & s = mk_bseq [] c
         # in_wf_conclusions c (PC_conclusions (Library2ProofContext L))}.
Proof.
  induction L; simpl; split; introv h; tcsp.

  - repndors.

    + destruct a; simpl in *; tcsp.
      subst; simpl in *.
      eexists; dands;[reflexivity|]; tcsp.

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
Qed.

(* By assuming [wf_bseq seq], when we start with a sequent with no hypotheses,
   it means that we have to prove that the conclusion is well-formed and closed.
 *)
Lemma valid_proof {o} :
  forall (ctxt : @ProofContext o) s (wf : wf_bseq s),
    (forall c,
        in_wf_conclusions c (PC_conclusions ctxt)
        -> sequent_true_ext_lib_wf ctxt (mk_bseq [] c))
    -> proof ctxt s
    -> sequent_true_ext_lib_wf ctxt s.
Proof.
  introv wf imp prf.

  induction prf
    as [ (* proved sequent       *) seq p
       | (* isect_eq             *) a1 a2 b1 b2 e1 e2 x1 x2 y i hs niy p1 ih1 p2 ih2
       | (* approx_refl          *) a hs
       | (* cequiv_approx        *) a b e1 e2 hs p1 ih1 p2 ih2
       | (* approx_eq            *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       | (* cequiv_eq            *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       (*| (* bottom_diverges      *) x hs js
       | (* cut                  *) B C t u x hs wB covB nixH p1 ih1 p2 ih2
       | (* equal_in_base        *) a b e F H p1 ih1 ps ihs*)
       | (* hypothesis           *) x A G J
       (*| (* cequiv_subst_concl   *) C x a b t e H wfa wfb cova covb p1 ih1 p2 ih2
       | (* approx_member_eq     *) a b e H p ih
       | (* cequiv_computation   *) a b H p ih
       | (* function elimination *) A B C a e ea f x z H J wa cova nizH nizJ dzf p1 ih1 p2 ih2*)
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

  - apply (rule_cut_true3 lib hs B C t u x); simpl; tcsp.

    + unfold args_constraints; simpl; introv xx; repndors; subst; tcsp.

    + introv xx; repndors; subst; tcsp.

      * apply ih1.
        apply (rule_cut_wf2 hs B C t u x); simpl; tcsp.

      * apply ih2.
        apply (rule_cut_wf2 hs B C t u x); simpl; tcsp.

  - apply (rule_equal_in_base2_true3 lib H a b e F); simpl; tcsp.

    introv xx; repndors; subst; tcsp.
    unfold rule_equal_in_base2_rest in xx; apply in_mapin in xx; exrepnd; subst.
    pose proof (ihs a0 i) as hh; clear ihs.
    repeat (autodimp hh hyp).
    pose proof (rule_equal_in_base2_wf2 H a b e F) as w.
    apply w; simpl; tcsp.
    right.
    apply in_mapin; eauto.*)

  - apply (rule_hypothesis_true_ext_lib ctxt); simpl; tcsp.

(*  - apply (rule_cequiv_subst_concl2_true3 lib H x C a b t e); allsimpl; tcsp.

    introv i; repndors; subst; allsimpl; tcsp.

    + apply ih1.
      apply (rule_cequiv_subst_concl2_wf2 H x C a b t e); simpl; tcsp.

    + apply ih2.
      apply (rule_cequiv_subst_concl2_wf2 H x C a b t e); simpl; tcsp.

  - apply (rule_approx_member_eq2_true3 lib a b e); simpl; tcsp.
    introv xx; repndors; subst; tcsp.
    apply ih.
    apply (rule_approx_member_eq2_wf2 a b e H); simpl; tcsp.

  - apply (rule_cequiv_computation_true3 lib); simpl; tcsp.

  - apply (rule_function_elimination_true3 lib A B C a e ea f x z); simpl; tcsp.

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

Lemma wf_proof {o} :
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
    as [ (* proved sequent       *) seq p
       | (* isect_eq             *) a1 a2 b1 b2 e1 e2 x1 x2 y i hs niy p1 ih1 p2 ih2
       | (* approx_refl          *) a hs
       | (* cequiv_approx        *) a b e1 e2 hs p1 ih1 p2 ih2
       | (* approx_eq            *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       | (* cequiv_eq            *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       (*| (* bottom_diverges      *) x hs js
       | (* cut                  *) B C t u x hs wB covB nixH p1 ih1 p2 ih2
       | (* equal_in_base        *) a b e F H p1 ih1 ps ihs*)
       | (* hypothesis           *) x A G J
       (*| (* cequiv_subst_concl   *) C x a b t e H wfa wfb cova covb p1 ih1 p2 ih2
       | (* approx_member_eq     *) a b e H p ih
       | (* cequiv_computation   *) a b H p ih
       | (* function elimination *) A B C a e ea f x z H J wa cova nizH nizJ dzf p1 ih1 p2 ih2*)
       ];
    allsimpl;
    allrw NVin_iff; tcsp;
      try (complete (dands; eauto 2 with slow; apply covered_var;
                     rw @vars_hyps_app; rw @vars_hyps_snoc; simpl;
                     rw in_app_iff; rw in_snoc; tcsp)).
Qed.

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

Lemma correct_library {o} :
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
               in_wf_conclusions c (PC_conclusions (Library2ProofContext L))
               -> sequent_true_ext_lib_wf (Library2ProofContext L) (mk_bseq [] c)) as w.
    { introv i; apply imp; auto.
      apply lemma_in_Library_iff.
      exists c; dands; auto. }
    clear imp.

    remember (Library2ProofContext L) as ctxt.

    apply sequent_true_mono_lib; auto.

    apply valid_proof; auto.
    apply implies_wf_bseq_no_hyps; auto.

  - apply IHL in i; auto.
    destruct a; simpl in *; repnd; tcsp;
      apply sequent_true_mono_lib; auto.
Qed.



(* ===========================================================

  Nuprl state, i.e., a Library and a list of lemmas currently being proved.

  ============================================================ *)

Definition term2pre_baresequent {o} (t : @NTerm o) : pre_baresequent :=
  MkPreBaresequent _ [] (pre_concl_ext t).

Record pre_proof_seq {o} (ctxt : @ProofContext o) :=
  MkPreProofSeq
    {
      pre_proof_seq_name  : LemmaName;
      pre_proof_seq_term  : NTerm;
      pre_proof_seq_prog  : isprogram pre_proof_seq_term;
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

Inductive proof_step :=
| proof_set_isect_eq (y : NVar).

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
| COM_update_proof (name : LemmaName) (addr : address) (step : proof_step)
(*(* focuses to a node in a proof *)
| COM_focus_proof (name : LemmaName) (addr : address)*).

Lemma in_conclusions_extend_proof_context {o} :
  forall (ctxt  : @ProofContext o)
         (entry : LibraryEntry)
         (c     : conclusion)
         (i     : in_wf_conclusions c (PC_conclusions ctxt)),
    in_wf_conclusions c (PC_conclusions (extend_proof_context ctxt entry)).
Proof.
  introv i.
  destruct entry; simpl in *; auto.
  unfold in_wf_conclusions; simpl in *; tcsp.
Qed.

Fixpoint pre_proof_cons {o}
         {ctxt  : @ProofContext o}
         (entry : LibraryEntry)
         {s     : pre_baresequent}
         (p     : pre_proof ctxt s)
  : pre_proof (extend_proof_context ctxt entry) s :=
  match p with
  | pre_proof_from_ctxt _ c i =>
    pre_proof_from_ctxt _ c (in_conclusions_extend_proof_context ctxt entry c i)

  | pre_proof_hole _ s => pre_proof_hole _ s

  | pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    let prf1' := pre_proof_cons entry prf1 in
    let prf2' := pre_proof_cons entry prf2 in
    pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1' prf2'

  | pre_proof_approx_refl _ a H => pre_proof_approx_refl _ a H

  | pre_proof_cequiv_approx _ a b H prf1 prf2 =>
    let prf1' := pre_proof_cons entry prf1 in
    let prf2' := pre_proof_cons entry prf2 in
    pre_proof_cequiv_approx _ a b H prf1' prf2'

  | pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    let prf1' := pre_proof_cons entry prf1 in
    let prf2' := pre_proof_cons entry prf2 in
    pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1' prf2'

  | pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    let prf1' := pre_proof_cons entry prf1 in
    let prf2' := pre_proof_cons entry prf2 in
    pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1' prf2'

  | pre_proof_hypothesis _ x A G J => pre_proof_hypothesis _ x A G J
  end.

Definition pre_proof_seq_cons {o}
           {ctxt  : @ProofContext o}
           (entry : LibraryEntry)
           (pps   : pre_proof_seq ctxt)
  : pre_proof_seq (extend_proof_context ctxt entry) :=
  match pps with
  | MkPreProofSeq name C isp prf => MkPreProofSeq name C isp (pre_proof_cons entry prf)
  end.

Definition pre_proofs_cons {o}
           {ctxt  : @ProofContext o}
           (entry : LibraryEntry)
           (l     : pre_proofs ctxt)
  : pre_proofs (extend_proof_context ctxt entry) :=
  map (pre_proof_seq_cons entry) l.

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
      * left; eexists; eexists; eauto.
      * right; intro xx; exrepnd; repndors; subst; allsimpl; tcsp.
        destruct k; eexists; eexists; eauto.
Qed.

Definition NuprlState_add_def {o}
           (state   : @NuprlState o)
           (opabs   : opabs)
           (vars    : list sovar_sig)
           (rhs     : SOTerm)
           (correct : correct_abs opabs vars rhs) : NuprlState :=
  match state with
  | MkNuprlState L unfinished =>
    if in_lib_dec opabs (Library2lib L) then state
    else
      let entry := LibraryEntry_abs (lib_abs opabs vars rhs correct) in
      MkNuprlState
        (entry :: L)
        (pre_proofs_cons entry unfinished)
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

(* Why can't I define these? *)
Definition finish_proof_from_context {o}
           (ctxt : ProofContext)
           (c    : @conclusion o)
           (i    : in_wf_conclusions c (PC_conclusions ctxt))
  : ExtractProof ctxt (concl2pre_baresequent c).
Proof.
  unfold concl2pre_baresequent; simpl.
  destruct c; simpl in *.

  - exists extract; simpl.

    { unfold in_wf_conclusions in i; simpl in i.
      rw in_map_iff in i; exrepnd.
      destruct a; simpl in *; ginv; subst.
      unfold extract_ax in *; simpl in *; eauto 2 with slow. }

    unfold pre2baresequent; simpl.
    exact (proof_from_ctxt _ (concl_ext ctype extract) i).

  - exists (@mk_axiom o); simpl.

    { apply valid_pre_extract_axiom. }

    unfold pre2baresequent; simpl.
    exact (proof_from_ctxt _ (concl_typ ctype) i).
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

Fixpoint finish_pre_proof {o}
         {ctxt  : @ProofContext o}
         {s     : pre_baresequent}
         (p     : pre_proof ctxt s)
  : option (ExtractProof ctxt s) :=
  match p with
  | pre_proof_from_ctxt _ c i => Some (finish_proof_from_context ctxt c i)

  | pre_proof_hole _ s => None

  | pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    match finish_pre_proof prf1, finish_pre_proof prf2 with
    | Some p1, Some p2 =>
      Some (finish_proof_isect_eq ctxt a1 a2 b1 b2 x1 x2 y i H niyH p1 p2)
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

  | pre_proof_hypothesis _ x A G J => Some (finish_proof_hypothesis ctxt x A G J)
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
         (isp   : isprogram stmt)
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
  : pre_proofs (Library2ProofContext state) -> NuprlState :=
  match state with
  | MkNuprlState L _ => fun pps => MkNuprlState (entry :: L) (pre_proofs_cons entry pps)
  end.

Definition NuprlState_finish_proof {o}
           (state : @NuprlState o)
           (name  : LemmaName) : NuprlState :=
  if in_lib_dec (opname2opabs name) (Library2lib state) then state
  else
    match find_unfinished_in_pre_proofs (NuprlState_unfinished state) name with
    | (Some pp, pps) =>

      match finish_pre_proof_seq pp with
      | Some entry => NuprlState_add_entry state entry pps
      | None => state
      end

    | (None, pps) => state
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

Definition apply_proof_step {o} {ctxt}
           (s    : @pre_baresequent o)
           (step : proof_step) : pre_proof ctxt s :=
  match step, s with
  | proof_set_isect_eq y, MkPreBaresequent _ H C =>

    match NVin_dec y (vars_hyps H) with
    | inl p =>

      match C return pre_proof ctxt (MkPreBaresequent _ H C) with
      | pre_concl_ext T =>

        match T with
        | oterm (Can NEquality) [bterm [] T1, bterm [] T2, bterm [] U] =>

          match U with
          | oterm (Can (NUni i)) [] =>

            match T1, T2 with
            | oterm (Can NIsect) [bterm [] a1, bterm [x1] b1], oterm (Can NIsect) [bterm [] a2, bterm [x2] b2] =>

              let prf1 := pre_proof_hole ctxt (pre_rule_isect_equality_hyp1 a1 a2 i H) in
              let prf2 := pre_proof_hole ctxt (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H) in
              pre_proof_isect_eq ctxt a1 a2 b1 b2 x1 x2 y i H p prf1 prf2

            | a, b => pre_proof_hole _ (MkPreBaresequent _ H (pre_concl_ext (mk_equality a b (mk_uni i))))
            end

          | u => pre_proof_hole _ (MkPreBaresequent _ H (pre_concl_ext (mk_equality T1 T2 u)))
          end

        | t => pre_proof_hole _ (MkPreBaresequent _ H (pre_concl_ext t))
        end

      | c => pre_proof_hole _ (MkPreBaresequent _ H c)
      end

    | _ => pre_proof_hole _ (MkPreBaresequent _ H C)
    end
  end.

Fixpoint update_pre_proof {o}
         {ctxt : @ProofContext o}
         {s    : pre_baresequent}
         (p    : pre_proof ctxt s)
         (addr : address)
         (step : proof_step) : pre_proof ctxt s :=
  match p with
  | pre_proof_from_ctxt _ c i => pre_proof_from_ctxt _ c i

  | pre_proof_hole _ s => apply_proof_step s step

  | pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let prf1' := update_pre_proof prf1 addr step in
      pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1' prf2
    | 2 :: addr =>
      let prf2' := update_pre_proof prf2 addr step in
      pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2'
    | _ => pre_proof_isect_eq _ a1 a2 b1 b2 x1 x2 y i H niyH prf1 prf2
    end

  | pre_proof_approx_refl _ a H => pre_proof_approx_refl _ a H

  | pre_proof_cequiv_approx _ a b H prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let prf1' := update_pre_proof prf1 addr step in
      pre_proof_cequiv_approx _ a b H prf1' prf2
    | 2 :: addr =>
      let prf2' := update_pre_proof prf2 addr step in
      pre_proof_cequiv_approx _ a b H prf1 prf2'
    | _ => pre_proof_cequiv_approx _ a b H prf1 prf2
    end

  | pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let prf1' := update_pre_proof prf1 addr step in
      pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1' prf2
    | 2 :: addr =>
      let prf2' := update_pre_proof prf2 addr step in
      pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2'
    | _ => pre_proof_approx_eq _ a1 a2 b1 b2 i H prf1 prf2
    end

  | pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2 =>
    match addr with
    | 1 :: addr =>
      let prf1' := update_pre_proof prf1 addr step in
      pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1' prf2
    | 2 :: addr =>
      let prf2' := update_pre_proof prf2 addr step in
      pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2'
    | _ => pre_proof_cequiv_eq _ a1 a2 b1 b2 i H prf1 prf2
    end

  | pre_proof_hypothesis _ x A G J => pre_proof_hypothesis _ x A G J
  end.

Definition update_pre_proof_seq {o} {ctxt}
           (pps  : @pre_proof_seq o ctxt)
           (addr : address)
           (step : proof_step) : pre_proof_seq ctxt :=
  match pps with
  | MkPreProofSeq name C isp pre_prf =>
    MkPreProofSeq name C isp (update_pre_proof pre_prf addr step)
  end.

Definition NuprlState_update_proof {o}
           (state : @NuprlState o)
           (name  : LemmaName)
           (addr  : address)
           (step  : proof_step) : NuprlState :=
  match find_unfinished_in_pre_proofs (NuprlState_unfinished state) name with
  | (Some pp, pps) =>

    let pp' := update_pre_proof_seq pp addr step in
    NuprlState_change_unfinished state (pp' :: pps)

  | (None, pps) => state
  end.

Definition update {o}
           (state : @NuprlState o)
           (cmd   : command) : NuprlState :=
  match cmd with
  | COM_add_def opabs vars rhs correct =>
    NuprlState_add_def state opabs vars rhs correct

  | COM_finish_proof name =>
    NuprlState_finish_proof state name

  | COM_update_proof name addr step =>
    NuprlState_update_proof state name addr step
(*    let lib := NuprlState_proof_library state in
    NuprlState_upd_focus state (focus_proof_in_library lib name addr)*)
  end.

(* Should we add this to NuprlState *)
Definition ValidNuprlState {o} (state : @NuprlState o) := ValidLibrary state.

Lemma update_preserves_validity {o} :
  forall (state : @NuprlState o) (cmd : command),
    ValidNuprlState state -> ValidNuprlState (update state cmd).
Proof.
  introv valid.
  destruct cmd; simpl; auto.

  - (* addition of a definition *)
    destruct state as [L pre_prfs]; simpl in *.
    unfold ValidNuprlState in *; simpl in *.

    destruct (in_lib_dec opabs (Library2lib L)) as [d|d]; simpl; auto.

  - (* finalizing a proof *)
    destruct state as [L pre_prfs]; simpl in *.
    unfold ValidNuprlState in *; simpl in *.
    unfold NuprlState_finish_proof; simpl.

    destruct (in_lib_dec (opname2opabs name) (Library2lib L)) as [d|d]; simpl; auto;[].

    remember (find_unfinished_in_pre_proofs pre_prfs name) as f; symmetry in Heqf; repnd.
    destruct f0; simpl in *; auto;[].

    remember (finish_pre_proof_seq p) as eop; symmetry in Heqeop.
    destruct eop; simpl in *; dands; auto;[].

    destruct l; simpl in *.

    + unfold finish_pre_proof_seq in Heqeop.
      destruct p; simpl in *.
      remember (finish_pre_proof pre_proof_seq_proof0) as fin; symmetry in Heqfin;
        destruct fin; ginv.
      destruct e0; ginv.

    + assert (ctxt = Library2ProofContext L) as xx.

      { unfold finish_pre_proof_seq in Heqeop.
        destruct p; simpl in *.
        remember (finish_pre_proof pre_proof_seq_proof0) as fin; symmetry in Heqfin;
          destruct fin; ginv;[].
        destruct e; ginv; cpx.
        inversion Heqeop; auto. }

      dands; auto.
      subst.

      unfold name_not_in_lib; auto.
      apply name_of_find_unfinished_in_pre_proofs in Heqf.
      apply name_of_finish_pre_proof_seq in Heqeop.
      subst; auto.

  - (* update an unfinished proof *)
    destruct state; simpl in *.
    unfold ValidNuprlState in *; simpl in *.
    unfold NuprlState_update_proof; simpl.

    remember (find_unfinished_in_pre_proofs NuprlState_unfinished0 name) as f; symmetry in Heqf; repnd.
    destruct f0; simpl in *; auto.
Qed.
