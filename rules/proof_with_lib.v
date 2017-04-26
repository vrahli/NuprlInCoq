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



(* ===========================================================

  A proof context is a list of abstractions and a list of proved
  formulas.

  ============================================================ *)

Record ProofContext {o} :=
  MkProofContext
    {
      PC_lib :> @library o;
      PC_conclusions : list (@conclusion o);
    }.

Definition EMPC {o} : @ProofContext o := MkProofContext o [] [].

Definition updLibProofContext {o} (pc : @ProofContext o) (e : library_entry) :=
  MkProofContext
    o
    (e :: PC_lib pc)
    (PC_conclusions pc).

Definition updConclProofContext {o} (pc : @ProofContext o) (c : conclusion) :=
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
      LIn c (@PC_conclusions o ctxt)
      -> pre_proof ctxt (concl2pre_baresequent c)
| pre_proof_hole : forall s, pre_proof ctxt s
| pre_proof_isect_eq :
    forall a1 a2 b1 b2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> pre_proof ctxt (pre_rule_isect_equality_hyp1 a1 a2 i H)
      -> pre_proof ctxt (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H)
      -> pre_proof ctxt (pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H).

Inductive proof {o} (ctxt : @ProofContext o) : @baresequent o -> Type :=
| proof_from_ctxt :
    forall c,
      LIn c (@PC_conclusions o ctxt)
      -> proof ctxt (mk_baresequent [] c)
| proof_isect_eq :
    forall a1 a2 b1 b2 e1 e2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> proof ctxt (rule_isect_equality2_hyp1 a1 a2 e1 i H)
      -> proof ctxt (rule_isect_equality2_hyp2 a1 b1 b2 e2 x1 x2 y i H)
      -> proof ctxt (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H).



(* ===========================================================

  State, i.e.:
    (1) the list of defined abstractions,
    (2) the list of proved lemmas,
    (3) the list of lemmas currently being proved

  ============================================================ *)

Definition LemmaName := opname.

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

Definition valid_extract {o} (t : @NTerm o) : Prop :=
  wf_term t # closed t # noutokens t.

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
                    (updConclProofContext ctxt (mk_concl stmt ext))
                    (extract2def name ext valid)).

Inductive LibraryEntry {o} :=
| LibraryEntry_abs (e : @library_entry o)
| LibraryEntry_proof
    (ctxt  : @ProofContext o)
    (name  : LemmaName)
    (stmt  : NTerm)
    (ext   : NTerm)
    (valid : valid_extract ext)
    (prf   : proof ctxt (Statement stmt ext)).

(* A library is just a list of entries such that we store the most recent
   entry at the front of the list
 *)
Definition Library {o} := list (@LibraryEntry o).

Definition extend_proof_context {o} (ctxt : @ProofContext o) (e : LibraryEntry) : ProofContext :=
  match e with
  | LibraryEntry_abs e => updLibProofContext ctxt e
  | LibraryEntry_proof c name stmt ext valid prf =>
    updLibProofContext
      (updConclProofContext ctxt (mk_concl stmt ext))
      (extract2def name ext valid)
  end.

Definition ValidLibraryEntry {o} (ctxt : @ProofContext o) (e : LibraryEntry) : Type :=
  match e with
  | LibraryEntry_abs e => entry_not_in_lib e ctxt
  | LibraryEntry_proof c name stmt ext valid prf =>
    c = ctxt # name_not_in_lib name ctxt
  end.

Fixpoint Library2ProofContext {o} (L : @Library o) : ProofContext :=
  match L with
  | [] => EMPC
  | entry :: entries =>
    let ctxt := Library2ProofContext entries in
    extend_proof_context ctxt entry
  end.

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
  | LibraryEntry_proof c name stmt ext valid prf =>
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

Definition seq_in_context {o}
           (s  : @baresequent o)
           (pc : ProofContext) : Type :=
  {c : conclusion & s = mk_bseq [] c # LIn c (PC_conclusions pc)}.

(*Lemma correct_library {o} :
  forall {c : ProofContext} (l : Library c) (s : @baresequent o),
    lemma_in_Library s l
    -> sequent_true_ext_lib_wf c s.
Proof.
  induction l; simpl; introv i; tcsp.

  - apply IHl in i; clear IHl.
    apply sequent_true_mono_lib; auto.

  - repndors.

    + apply IHl in i; clear IHl.
      apply sequent_true_mono_lib; auto.

    + subst.

      assert (forall c,
                 LIn c (PC_conclusions ctxt)
                 -> sequent_true_ext_lib_wf ctxt (mk_bseq [] c)) as imp.
      {
        introv i.
        apply IHl.
      }
Qed.*)


Lemma correct_library {o} :
  forall (pc : ProofContext) (L : Library) (s : @baresequent o),
    ValidLibrary pc L
    -> lemma_in_Library s L
    -> sequent_true_ext_lib_wf pc s.
Proof.
  induction L; introv valid i; simpl in *; tcsp.
  repnd; repndors.

  - destruct a; simpl in *; tcsp.
    repnd; subst; simpl in *.



    Focus 2.
  apply (IHL _ s) in valid; auto.

  XXXXXXXXXX

  - apply IHL in i.
    apply sequent_true_mono_lib; auto.

  - repndors; subst.

    +

Qed.

Definition pre_proofs {o} (ctxt : @ProofContext o) :=
  list {s : pre_baresequent & pre_proof ctxt s}.

Record NuprlState {o} :=
  MkNuprlState
    {
      NuprlState_context    : @ProofContext o;
      NuprlState_lib        : Library NuprlState_context;
      NuprlState_unfinished : pre_proofs NuprlState_context;
    }.



(* ===========================================================

  Commands to manipulate the state

  ============================================================ *)

Definition address := list nat.

Inductive command {o} :=
(* add a definition at the head *)
| COM_add_def
    (opabs   : opabs)
    (vars    : list sovar_sig)
    (rhs     : @SOTerm o)
    (correct : correct_abs opabs vars rhs)
(* tries to complete a proof if it has no holes *)
| COM_finish_proof (name : LemmaName)
(* focuses to a node in a proof *)
| COM_focus_proof (name : LemmaName) (adr : address).

Definition update {o}
           (state : @NuprlState o)
           (com   : command) : NuprlState :=
  match com with
  | COM_add_def opabs vars rhs correct =>
    NuprlState_add_def_lib state opabs vars rhs correct
  | COM_finish_proof name =>
    let lib := NuprlState_proof_library state in
    NuprlState_upd_proof_lib state (finish_proof_in_library lib name)
  | COM_focus_proof name addr =>
    let lib := NuprlState_proof_library state in
    NuprlState_upd_focus state (focus_proof_in_library lib name addr)
  end.
