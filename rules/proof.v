(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


  Websites: http://nuprl.org/html/Nuprl2Coq
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

Require Export computation_preserves_lib.


Inductive valid_rule {o} : @rule o -> Type :=
| valid_rule_isect_equality :
    forall a1 a2 b1 b2 x1 x2 y i H,
      !LIn y (vars_hyps H)
      -> valid_rule (rule_isect_equality a1 a2 b1 b2 x1 x2 y i H).

Inductive gen_proof {o} (G : @baresequent o) : Type :=
| gen_proof_cons :
    forall hyps args,
      valid_rule (mk_rule G hyps args)
      -> (forall h, LIn h hyps -> gen_proof h)
      -> gen_proof G.

(* [pwf_sequent] says that the hypotheses and conclusion are well-formed and
   the type is closed w.r.t. the hypotheses.
 *)
Lemma valid_gen_proof {o} :
  forall lib (seq : @baresequent o) (wf : pwf_sequent seq),
    gen_proof seq -> sequent_true2 lib seq.
Proof.
  introv wf p.
  induction p as [? ? ? vr imp ih].
  inversion vr as [a1 a2 b1 b2 x1 x2 y i hs niy]; subst; allsimpl; clear vr.

  - apply (rule_isect_equality_true2 lib y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply ih; auto.
        apply (rule_isect_equality_wf y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.

      * apply ih; auto.
        apply (rule_isect_equality_wf y i a1 a2 b1 b2 x1 x2 hs); simpl; tcsp.
Qed.

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

Inductive Llist {A} (f : A -> Type) : list A -> Type :=
| lnil : Llist f []
| lcons : forall {h t}, (f h) -> Llist f t -> Llist f (h :: t).

Lemma in_Llist {A} :
  forall f (a : A) l,
    LIn a l -> Llist f l -> f a.
Proof.
  induction l; introv i h; allsimpl; tcsp.
  repndors; subst; auto.
  - inversion h; subst; auto.
  - apply IHl; auto.
    inversion h; subst; auto.
Qed.

Lemma Llist_implies_forall {A f} {l : list A} :
  Llist f l -> (forall v, LIn v l -> f v).
Proof.
  introv h i.
  eapply in_Llist in h;eauto.
Qed.

Definition ProofName := opname.
Definition ProofNames := list ProofName.

(*
Record ProofLibSig {o} lib :=
  {
    ProofLib_type : Type;
    ProofLib_access :
      ProofLib_type
      -> ProofName
      -> option {seq : @baresequent o &  sequent_true2 lib seq}
  }.
*)

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

Definition option2list {T} (x : option T) : list T :=
  match x with
  | Some t => [t]
  | None => []
  end.

Definition opname2opabs (op : opname) : opabs :=
  mk_opabs op [] [].

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
  forall (t  : @NTerm o)
         (w  : wf_term t)
         (c  : closed t)
         (n  : noutokens t)
         (op : opname),
    correct_abs (opname2opabs op) [] (nterm2soterm t).
Proof.
  introv w c n; introv.
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
           (name : ProofName)
           (ext  : @NTerm o)
           (wf   : wf_term ext)
           (cl   : closed ext)
           (nout : noutokens ext) : library_entry :=
  lib_abs
    (opname2opabs name)
    []
    (nterm2soterm ext)
    (extract2correct ext wf cl nout name).

Record ProofContext {o} :=
  MkProofContext
    {
      PC_lib :> @library o;
      PC_proof_names : ProofNames;
      PC_conclusions : list (@conclusion o)
    }.

Definition not_in_lib_entry {o} (e : @library_entry o) ctxt :=
  !@in_lib o (opabs_of_lib_entry e) (PC_lib ctxt).

Definition not_in_lib_name {o} (name : ProofName) ctxt :=
  !@in_lib o (opname2opabs name) (PC_lib ctxt).

Definition not_in_names {o} (e : @library_entry o) (ctxt : @ProofContext o) :=
  forall opabs,
    LIn opabs (map opname2opabs (PC_proof_names ctxt))
    -> !same_opabs (opabs_of_lib_entry e) opabs.

Definition updLibProofContext {o} (pc : @ProofContext o) e :=
  MkProofContext
    o
    (e :: PC_lib pc)
    (PC_proof_names pc)
    (PC_conclusions pc).

Definition updNameProofContext {o} (pc : @ProofContext o) name :=
  MkProofContext
    o
    (PC_lib pc)
    (name :: PC_proof_names pc)
    (PC_conclusions pc).

Definition updSeqProofContext {o} (pc : @ProofContext o) seq :=
  MkProofContext
    o
    (PC_lib pc)
    (PC_proof_names pc)
    (seq :: PC_conclusions pc).

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

(* A pre-proof is a proof without the extracts, which we can build a posteriori *)
Inductive pre_proof {o} (hole : bool) (ctxt : @ProofContext o) : @pre_baresequent o -> Type :=
| pre_proof_from_lib :
    forall c,
      LIn c (@PC_conclusions o ctxt)
      -> pre_proof hole ctxt (concl2pre_baresequent c)
| pre_proof_hole : forall s, hole = true -> pre_proof hole ctxt s
| pre_proof_isect_eq :
    forall a1 a2 b1 b2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> pre_proof hole ctxt (pre_rule_isect_equality_hyp1 a1 a2 i H)
      -> pre_proof hole ctxt (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H)
      -> pre_proof hole ctxt (pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
| pre_proof_approx_refl :
    forall a H,
      pre_proof hole ctxt (pre_rule_approx_refl_concl a H)
| pre_proof_cequiv_approx :
    forall a b H,
      pre_proof hole ctxt (pre_rule_cequiv_approx_hyp a b H)
      -> pre_proof hole ctxt (pre_rule_cequiv_approx_hyp b a H)
      -> pre_proof hole ctxt (pre_rule_cequiv_approx_concl a b H)
| pre_proof_approx_eq :
    forall a1 a2 b1 b2 i H,
      pre_proof hole ctxt (pre_rule_eq_base_hyp a1 a2 H)
      -> pre_proof hole ctxt (pre_rule_eq_base_hyp b1 b2 H)
      -> pre_proof hole ctxt (pre_rule_approx_eq_concl a1 a2 b1 b2 i H)
| pre_proof_cequiv_eq :
    forall a1 a2 b1 b2 i H,
      pre_proof hole ctxt (pre_rule_eq_base_hyp a1 a2 H)
      -> pre_proof hole ctxt (pre_rule_eq_base_hyp b1 b2 H)
      -> pre_proof hole ctxt (pre_rule_cequiv_eq_concl a1 a2 b1 b2 i H)
| pre_proof_bottom_diverges :
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
      -> pre_proof hole ctxt (pre_rule_equal_in_base_concl a b H)
| pre_proof_hypothesis :
    forall x A G J,
      pre_proof hole ctxt (pre_rule_hypothesis_concl G J A x)
| pre_proof_cequiv_subst_concl :
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
      -> pre_proof hole ctxt (pre_rule_function_elimination_concl A B C f x H J).

Inductive proof {o} (ctxt : @ProofContext o) : @baresequent o -> Type :=
| proof_from_lib :
    forall c,
      LIn c (@PC_conclusions o ctxt)
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
| proof_bottom_diverges :
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
      -> proof ctxt (rule_equal_in_base_concl a b H)
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
      -> proof ctxt (rule_function_elimination_concl A B C e f x z H J).

Inductive Library {o} : @ProofContext o -> Type :=
| Library_Empty :
    Library (MkProofContext o [] [] [])
| Library_Abs :
    forall {pc}
           (c  : Library pc)
           (e  : @library_entry o)
           (n1 : not_in_lib_entry e pc)
           (n2 : not_in_names e pc),
      Library (updLibProofContext pc e)
| Library_Proof_tmp :
    forall {pc}
           (c    : Library pc)
           (name : ProofName)
           (stmt : @NTerm o)
           (hole : bool)
           (p    : pre_proof hole pc (PreStatement stmt))
           (n1   : !LIn name (PC_proof_names pc))
           (n2   : not_in_lib_name name pc),
      Library (updNameProofContext pc name)
| Library_Proof_final :
    forall {pc}
           (c    : Library pc)
           (name : ProofName)
           (stmt : @NTerm o)
           (ext  : NTerm)
           (wf   : wf_term ext)
           (cl   : closed ext)
           (nout : noutokens ext)
           (p    : proof pc (Statement stmt ext))
           (n1   : !LIn name (PC_proof_names pc))
           (n2   : not_in_lib_name name pc),
      Library (updLibProofContext
                 (updSeqProofContext
                    (updNameProofContext pc name)
                    (mk_concl stmt ext))
                 (extract2def name ext wf cl nout)).

Lemma similarity_nil_implies {o} :
  forall lib (s1 s2 : @CSub o),
    similarity lib s1 s2 [] -> (s1 = [] # s2 = []).
Proof.
  introv sim; inversion sim; cpx.
Qed.

Ltac clear_eq1 x :=
  match goal with
    | [ H : x = _ |- _ ] => clear H
  end.

Lemma computes_to_valc_consistent_with_new_definition {o} {lib} :
  forall (a b : @CTerm o)
         (r   : computes_to_valc lib a b)
         (e   : library_entry)
         (p   : !in_lib (opabs_of_lib_entry e) lib),
    computes_to_valc (e :: lib) a b.
Proof.
  introv r p.
  allunfold @computes_to_valc.
  allunfold @computes_to_value; repnd; dands; auto.
  eapply reduces_to_consistent_with_new_definition; auto.
Qed.

Lemma approx_stable_iff {o} :
  forall lib (a b : @CTerm o),
    (a) ~<~( lib)(b) <=> approxc lib a b.
Proof.
  introv; split; intro h; try (apply approx_stable; auto).
  spcast; auto.
Qed.

Lemma cequiv_stable_iff {o} :
  forall lib (a b : @CTerm o),
    (a) ~=~( lib)(b) <=> cequivc lib a b.
Proof.
  introv; split; intro h; try (apply cequiv_stable; auto).
  spcast; auto.
Qed.

Lemma simpleCorrectAbs {o}
           (op : opname)
           (t  : @NTerm o)
           (wf : wf_term t)
           (cl : closed t)
           (nu : noutokens t)
  : correct_abs (opname2opabs op) [] (nterm2soterm t).
Proof.
  unfold correct_abs; simpl; dands; auto.
  - unfold wf_soterm.
    autorewrite with slow; auto.
  - unfold socovered.
    autorewrite with slow; auto.
    rw cl; simpl; auto.
  - unfold correct_abs_params, correct_abs_params_b; simpl; auto.
  - unfold no_utokens; simpl; auto.
    autorewrite with slow; auto.
Qed.

Definition simpleDef {o}
           (op : opname)
           (t  : @NTerm o)
           (wf : wf_term t)
           (cl : closed t)
           (nu : noutokens t)
  : @library_entry o :=
  lib_abs (opname2opabs op)
          []
          (nterm2soterm t)
          (simpleCorrectAbs op t wf cl nu).

Definition simpleAbs {o} (op : opname) : @NTerm o :=
  oterm (Abs (opname2opabs op)) [].

Lemma isprogram_simpleAbs {o} :
  forall op, @isprogram o (simpleAbs op).
Proof.
  introv.
  unfold isprogram, closed; simpl; dands; tcsp.
  constructor; simpl; tcsp.
Qed.
Hint Resolve isprogram_simpleAbs : slow.

Lemma approx_abs_in_empty_lib {o} :
  forall op (u : @NTerm o),
    isprogram u
    -> approx emlib (simpleAbs op) u.
Proof.
  introv ispu.
  apply approx_assume_hasvalue; eauto 2 with slow.
  introv hv.
  unfold hasvalue_like in hv; exrepnd.
  apply reduces_to_split2 in hv1; repndors; exrepnd; subst; allsimpl; tcsp.

  - unfold isvalue_like in hv0; allsimpl; tcsp.

  - csunf hv1; allsimpl.
    apply compute_step_lib_success in hv1; exrepnd; subst.
    unfold found_entry in hv3; allsimpl; ginv.
Qed.

Lemma wf_zero {o} : @wf_term o mk_zero.
Proof.
  eauto 3 with slow.
Qed.

Lemma closed_zero {o} : @closed o mk_zero.
Proof.
  eauto 3 with slow.
Qed.

Lemma noutokens_zero {o} : @noutokens o mk_zero.
Proof.
  unfold noutokens; simpl; auto.
Qed.

Definition simpleDef0 {o} (op : opname) : @library_entry o :=
  simpleDef op mk_zero wf_zero closed_zero noutokens_zero.

Lemma not_approx_abs_in_single_lib {o} :
  forall op, !(@approx o [simpleDef0 op] (simpleAbs op) mk_bot).
Proof.
  introv apr.
  destruct apr as [c].
  unfold close_comput in c; repnd; allsimpl.
  pose proof (c2 (Nint 0) []) as h.
  fold_terms.
  autodimp h hyp.
  {
    unfold computes_to_value; simpl; dands; eauto 3 with slow.
    apply reduces_to_if_step.
    csunf; simpl.
    unfold compute_step_lib; simpl; boolvar; tcsp.
    unfold not_matching_entry in n; allsimpl; repndors; tcsp.
    - unfold matching_parameters, assert in *; allsimpl; tcsp.
    - unfold matching_bterms, assert in *; allsimpl; tcsp.
  }

  exrepnd.
  apply bottom_diverges in h1; auto.
Qed.

Lemma not_approx_cons_library_entry {o} :
  !(forall lib e (t1 t2 : @NTerm o),
       !in_lib (opabs_of_lib_entry e) lib
       -> approx lib t1 t2
       -> approx (e :: lib) t1 t2).
Proof.
  introv h.

  pose proof (h emlib
                (simpleDef0 "foo")
                (simpleAbs "foo")
                mk_bot) as q;
    clear h.

  repeat (autodimp q hyp).
  { unfold in_lib; simpl; intro h; exrepnd; tcsp. }
  { apply approx_abs_in_empty_lib; auto. }

  apply not_approx_abs_in_single_lib in q; auto.
Qed.

Lemma not_cequiv_cons_library_entry {o} :
  !(forall lib e (t1 t2 : @NTerm o),
       !in_lib (opabs_of_lib_entry e) lib
       -> cequiv lib t1 t2
       -> cequiv (e :: lib) t1 t2).
Proof.
  introv h.

  pose proof (h emlib
                (simpleDef0 "foo")
                (simpleAbs "foo")
                mk_bot) as q;
    clear h.

  repeat (autodimp q hyp).
  { unfold in_lib; simpl; intro h; exrepnd; tcsp. }
  { split; try (apply approx_abs_in_empty_lib; auto).
    unfold mk_bot.
    apply bottom_approx_any; eauto 3 with slow. }

  destruct q as [c1 c2].
  apply not_approx_abs_in_single_lib in c1; auto.
Qed.

Lemma not_cequivc_cons_library_entry {o} :
  !(forall lib e (t1 t2 : @CTerm o),
       !in_lib (opabs_of_lib_entry e) lib
       -> cequivc lib t1 t2
       -> cequivc (e :: lib) t1 t2).
Proof.
  introv h.
  allunfold @cequivc; destruct_cterms; allsimpl.
  pose proof (h emlib
                (simpleDef0 "foo")
                (mk_cterm (simpleAbs "foo") (isprogram_simpleAbs "foo"))
                mkc_bot) as q; clear h; allsimpl.

  repeat (autodimp q hyp).
  { unfold in_lib; simpl; intro h; exrepnd; tcsp. }
  { split; try (apply approx_abs_in_empty_lib; auto).
    unfold mk_bot.
    apply bottom_approx_any; eauto 3 with slow. }

  destruct q as [c1 c2].
  apply not_approx_abs_in_single_lib in c1; auto.
Qed.

Lemma not_eqorceq_cons_library_entry_sp {o} :
  forall eq,
    !(forall lib e (t1 t2 : @CTerm o),
       !in_lib (opabs_of_lib_entry e) lib
       -> eqorceq lib eq t1 t2
       -> eqorceq (e :: lib) (ccequivc (e :: lib)) t1 t2).
Proof.
  introv h.
  pose proof (@not_cequivc_cons_library_entry o) as q; destruct q; introv ni ceq.
  pose proof (h lib e t1 t2) as z; clear h.
  repeat (autodimp z hyp; auto).
  - right; spcast; auto.
  - unfold eqorceq in z.
    apply cequiv_stable; repndors; auto.
Qed.

Lemma not_eqorceq_cons_library_entry_sp2 {o} :
  !(forall lib e (t1 t2 : @CTerm o),
       !in_lib (opabs_of_lib_entry e) lib
       -> eqorceq lib (ccequivc (e :: lib)) t1 t2
       -> eqorceq (e :: lib) (ccequivc (e :: lib)) t1 t2).
Proof.
  introv h.
  pose proof (@not_cequivc_cons_library_entry o) as q; destruct q; introv ni ceq.
  pose proof (h lib e t1 t2) as z; clear h.
  repeat (autodimp z hyp; auto).
  - right; spcast; auto.
  - unfold eqorceq in z.
    apply cequiv_stable; repndors; auto.
Qed.

Lemma not_eqorceq_cons_library_entry_sp3 {o} :
  !(forall lib e (t1 t2 : @CTerm o),
       !in_lib (opabs_of_lib_entry e) lib
       -> eqorceq lib (ccequivc lib) t1 t2
       -> eqorceq (e :: lib) (ccequivc (e :: lib)) t1 t2).
Proof.
  introv h.
  pose proof (@not_cequivc_cons_library_entry o) as q; destruct q; introv ni ceq.
  pose proof (h lib e t1 t2) as z; clear h.
  repeat (autodimp z hyp; auto).
  - right; spcast; auto.
  - unfold eqorceq in z.
    apply cequiv_stable; repndors; auto.
Qed.

Lemma not_eqorceq_cons_library_entry {o} :
  !(forall lib e eq (t1 t2 : @CTerm o),
       !in_lib (opabs_of_lib_entry e) lib
       -> eqorceq lib eq t1 t2
       -> eqorceq (e :: lib) eq t1 t2).
Proof.
  introv h.
  pose proof (@not_eqorceq_cons_library_entry_sp2 o) as q; destruct q; introv ni ceq.
  apply h; auto.
Qed.

Lemma not_tequality_cons_library_entry {o} :
  !(forall lib e (t1 t2 : @CTerm o),
       !in_lib (opabs_of_lib_entry e) lib
       -> tequality lib t1 t2
       -> tequality (e :: lib) t1 t2).
Proof.
  introv h.
  pose proof (@not_cequivc_cons_library_entry o) as q; destruct q; introv ni eor.
  pose proof (h lib e (mkc_equality t1 t1 mkc_base) (mkc_equality t2 t2 mkc_base) ni) as z; clear h.
  repeat (rw @tequality_mkc_equality_base_iff in z).
  autodimp z hyp; repnd; dands; spcast; auto.
  apply cequiv_stable; auto.
Qed.

(* !!MOVE to choice.v*)
Lemma choice_teq0 {o} :
  forall lib v1 B1 v2 B2 eqa,
    (forall a1 a2 : @CTerm o,
       eqa a1 a2
       -> exists eqb, nuprl lib (B1 [[v1 \\ a1]]) (B2 [[v2 \\ a2]]) eqb)
    ->
    exists f,
    forall (a1 a2 : CTerm) (e : eqa a1 a2),
      nuprl lib (substc a1 v1 B1) (substc a2 v2 B2) (f a1 a2 e).
Proof.
  introv F.
  pose proof (FunctionalChoice_on
                {a1 : CTerm & {a2 : CTerm & eqa a1 a2}}
                per
                (fun a b => nuprl lib (substc (projT1 a) v1 B1) (substc (projT1 (projT2 a)) v2 B2) b))
    as C.
  autodimp C hyp.
  { introv; exrepnd; simpl; apply F; auto. }

  exrepnd.

  exists (fun a1 a2 e => f (existT (fun a1 => {a2 : CTerm & eqa a1 a2})
                                   a1
                                   (existT (fun a2 => eqa a1 a2)
                                           a2
                                           e))).
  introv.
  pose proof (C0 (existT (fun a1 => {a2 : CTerm & eqa a1 a2})
                         a1
                         (existT (fun a2 => eqa a1 a2)
                                 a2
                                 e))); sp.
Qed.

Lemma matching_entry_sign_deq :
  forall oa1 oa2, decidable (matching_entry_sign oa1 oa2).
Proof.
  introv.
  unfold matching_entry_sign.
  destruct (String.string_dec (opabs_name oa1) (opabs_name oa2));
  try (complete (right; auto));
  destruct (opsign_dec (opabs_sign oa1) (opabs_sign oa2));
  try (complete (right; auto));
  remember (matching_parametersb (opabs_params oa1) (opabs_params oa2)) as m;
  destruct m;
  try (complete (right; intro k; repnd; tcsp;
                 unfold matching_parameters in k;
                 rw <- Heqm in k; inversion k));
  try (complete (right; auto)).
  left; dands; auto.
  unfold matching_parameters.
  rewrite <- Heqm; sp.
Qed.

Fixpoint found_entry_b {o} (lib : @library o) opabs (bs : list (@BTerm o)) : bool :=
  match lib with
  | [] => false
  | lib_abs oa vars rhs correct :: l =>
    if matching_entry_deq opabs oa vars bs
    then true
    else found_entry_b l opabs bs
  end.

Fixpoint found_entry_sign {o} (lib : @library o) opabs : bool :=
  match lib with
  | [] => false
  | lib_abs oa vars rhs correct :: l =>
    if matching_entry_sign_deq opabs oa
    then true
    else found_entry_sign l opabs
  end.

Fixpoint get_all_abs {o} (t : @NTerm o) : OList opabs :=
  match t with
  | vterm _ => onil
  | sterm f => OLS (fun n => get_all_abs (f n))
  | oterm op bs =>
    match op with
    | Abs abs => OLL (OLO abs :: map get_all_abs_b bs)
    | _ => OLL (map get_all_abs_b bs)
    end
  end
with get_all_abs_b {o} (b : @BTerm o) : OList opabs :=
       match b with
       | bterm vs t => get_all_abs t
       end.

Definition all_abs_are_defined {o} (lib : @library o) (t : @NTerm o) : Prop :=
  forall opabs,
    in_olist opabs (get_all_abs t)
    -> found_entry_sign lib opabs = true.

Definition all_abs_are_defined_cterm {o} lib (t : @CTerm o) : Prop :=
  all_abs_are_defined lib (get_cterm t).

(*
Inductive all_abstractions_are_defined {o} lib : @NTerm o -> Type :=
| all_abs_vterm : forall v, all_abstractions_are_defined lib (vterm v)
| all_abs_sterm :
    forall f,
      (forall n, all_abstractions_are_defined lib (f n))
      -> all_abstractions_are_defined lib (sterm f)
| all_abs_oterm :
    forall op bs,
      found_opid_in_library lib op bs = true
      -> (forall b, LIn b bs -> all_abstractions_are_defined_b lib b)
      -> all_abstractions_are_defined lib (oterm op bs)
with all_abstractions_are_defined_b {o} lib : @BTerm o -> Type :=
| all_abs_bterm :
    forall vs t,
      all_abstractions_are_defined lib t
      -> all_abstractions_are_defined_b lib (bterm vs t).
*)

Definition found_opid_in_library_sign {o} (lib : @library o) (op : @Opid o) : bool :=
  match op with
  | Abs abs => found_entry_sign lib abs
  | _ => true
  end.

Fixpoint all_abstractions_are_defined {o} lib (t : @NTerm o) : obool :=
  match t with
  | vterm _ => otrue
  | sterm f => obseq (fun n => all_abstractions_are_defined lib (f n))
  | oterm op bs =>
    oband
      (bool2obool (found_opid_in_library_sign lib op))
      (oball (map (all_abstractions_are_defined_b lib) bs))
  end
with all_abstractions_are_defined_b {o} lib (b : @BTerm o) : obool :=
       match b with
       | bterm vs t => all_abstractions_are_defined lib t
       end.

Lemma all_abs_are_defined_eq {o} :
  forall lib (t : @NTerm o),
    all_abs_are_defined lib t
    <=> isotrue (all_abstractions_are_defined lib t).
Proof.
  nterm_ind t as [|f ind|op bs ind] Case; unfold all_abs_are_defined; simpl;
  split; introv h; auto.

  - Case "vterm".
    introv i.
    inversion i; subst; exrepnd; allsimpl; tcsp.

  - Case "sterm".
    introv.
    pose proof (ind n) as q; clear ind.
    apply q; auto.
    unfold all_abs_are_defined; introv i.
    apply h.
    constructor; eexists; eauto.

  - Case "sterm".
    introv i.
    inversion i as [| |F j]; subst; clear i; exrepnd.
    pose proof (h n) as q; clear h.
    apply ind in q; apply q; auto.

  - Case "oterm".
    apply isotrue_oband; dands.

    + apply isotrue_bool2obool_iff.
      dopid op as [can|ncan|exc|abs] SCase; allsimpl; auto.
      SCase "Abs".
      apply h.
      constructor; simpl; eexists; dands;[left;eauto|]; auto.

    + apply isotrue_oball_map; introv i.
      destruct x as [vs t]; allsimpl.
      pose proof (ind t vs) as q; clear ind.
      apply q; auto.
      introv j.
      apply h.
      destruct op;
        try (apply in_olist_OLL_cons; right);
        try apply in_olist_OLL_map;
        try (complete (eexists; dands; eauto)).

  - Case "oterm".
    introv i.
    allrw isotrue_oband; repnd.
    allrw isotrue_oball_map.
    allrw isotrue_bool2obool_iff.

    destruct op; allsimpl; auto;
    allrw @in_olist_OLL_map; exrepnd;
    try (destruct a as [l t]);
    try (pose proof (h (bterm l t)) as q; autodimp q hyp);
    try (pose proof (ind t l) as z; autodimp z hyp);
    allsimpl; try (apply z in q; apply q; auto).

    apply in_olist_OLL_cons in i; repndors.

    + inversion i; subst; clear i; auto.

    + apply in_olist_OLL_map in i; exrepnd.
      applydup h in i1.
      destruct a as [l t]; allsimpl.
      pose proof (ind t l) as q; autodimp q hyp.
      apply q in i2; apply i2; auto.
Qed.

Definition all_abstractions_are_defined_cterm {o} lib (t : @CTerm o) : obool :=
  all_abstractions_are_defined lib (get_cterm t).

Definition all_abstractions_are_defined_sub {o} lib (sub : @Sub o) : obool :=
  oball (map (all_abstractions_are_defined lib) (range sub)).

Lemma isotrue_all_abstractions_are_defined_sub_iff {o} :
  forall lib (sub : @Sub o),
    isotrue (all_abstractions_are_defined_sub lib sub)
    <=> (forall v t, LIn (v,t) sub -> isotrue (all_abstractions_are_defined lib t)).
Proof.
  introv.
  unfold all_abstractions_are_defined_sub.
  rw isotrue_oball_map; split; introv h; introv i.
  - apply h.
    apply in_sub_eta in i; tcsp.
  - apply in_range in i; exrepnd; eauto.
Qed.

Lemma implies_isotrue_all_abstractions_are_defined_sub_sub_filter {o} :
  forall lib (sub : @Sub o) l,
    isotrue (all_abstractions_are_defined_sub lib sub)
    -> isotrue (all_abstractions_are_defined_sub lib (sub_filter sub l)).
Proof.
  introv i.
  allrw @isotrue_all_abstractions_are_defined_sub_iff.
  introv j.
  apply in_sub_filter in j; repnd.
  eapply i; eauto.
Qed.
Hint Resolve implies_isotrue_all_abstractions_are_defined_sub_sub_filter : slow.

Lemma implies_isotrue_all_abstraction_are_defined_lsubst_aux {o} :
  forall lib (t : @NTerm o) sub,
    isotrue (all_abstractions_are_defined lib t)
    -> isotrue (all_abstractions_are_defined_sub lib sub)
    -> isotrue (all_abstractions_are_defined lib (lsubst_aux t sub)).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv isot isos; allsimpl; tcsp.

  - Case "vterm".
    remember (sub_find sub v) as p; destruct p; symmetry in Heqp; simpl; auto.

    apply sub_find_some in Heqp.
    rw @isotrue_all_abstractions_are_defined_sub_iff in isos.
    eapply isos; eauto.

  - Case "oterm".
    allrw isotrue_oband.
    rw isotrue_oball_map in isot; repnd.
    rw isotrue_oball_map.
    dands; auto.
    introv i.
    allrw in_map_iff; exrepnd; subst.
    destruct a as [l t]; allsimpl.
    pose proof (ind t t l) as q; clear ind.
    repeat (autodimp q hyp); eauto 3 with slow;[].
    pose proof (q (sub_filter sub l)) as h; clear q.
    repeat (autodimp h hyp); eauto 3 with slow;[].
    apply isot in i1; allsimpl; auto.
Qed.

Hint Rewrite @osize_cswap : slow.

Lemma isotrue_all_abstraction_are_defined_lsubst_preserves_cswap {o} :
  forall lib (t : @NTerm o) sw,
    all_abstractions_are_defined lib (cswap sw t)
    = all_abstractions_are_defined lib t.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; allsimpl; introv; tcsp.

  Case "oterm".
  f_equal.
  f_equal.
  rewrite map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x as [l t]; allsimpl.
  eapply ind; eauto 3 with slow.
Qed.
Hint Rewrite @isotrue_all_abstraction_are_defined_lsubst_preserves_cswap : slow.

Lemma isotrue_all_abstraction_are_defined_lsubst_preserves_alphaeq {o} :
  forall lib (t u : @NTerm o),
    alphaeq t u
    -> all_abstractions_are_defined lib t = all_abstractions_are_defined lib u.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; allsimpl; introv aeq.

  - Case "vterm".
    inversion aeq; subst; simpl; auto.

  - Case "sterm".
    inversion aeq as [|? g q|]; subst; simpl.
    f_equal.
    apply functional_extensionality; introv.
    apply ind; auto; clear ind.
    apply q.

  - Case "oterm".
    apply alphaeq_oterm_implies_combine in aeq; exrepnd; subst; allsimpl.
    f_equal.
    f_equal.
    apply eq_maps3; auto.
    introv i.
    applydup aeq0 in i.
    destruct a as [l1 t1].
    destruct c as [l2 t2].
    allsimpl.
    inversion i0 as [? ? ? ? ? len1 len2 disj norep aeq]; allsimpl; subst; clear i0.
    applydup in_combine in i; repnd.
    pose proof (ind t1 (cswap (mk_swapping l1 vs) t1) l1) as h; clear ind.
    autorewrite with slow in *.
    repeat (autodimp h hyp); eauto 3 with slow.
    apply h in aeq.
    autorewrite with slow in *; auto.
Qed.

Lemma implies_isotrue_all_abstraction_are_defined_lsubst {o} :
  forall lib (t : @NTerm o) sub,
    isotrue (all_abstractions_are_defined lib t)
    -> isotrue (all_abstractions_are_defined_sub lib sub)
    -> isotrue (all_abstractions_are_defined lib (lsubst t sub)).
Proof.
  introv isot isos.
  pose proof (unfold_lsubst sub t) as q; exrepnd.
  rewrite q0.
  apply implies_isotrue_all_abstraction_are_defined_lsubst_aux; auto.
  erewrite isotrue_all_abstraction_are_defined_lsubst_preserves_alphaeq; eauto.
  apply alphaeq_sym; auto.
  apply alphaeq_eq; auto.
Qed.

Lemma implies_isotrue_all_abstraction_are_defined_subst {o} :
  forall lib (t : @NTerm o) x u,
    isotrue (all_abstractions_are_defined lib t)
    -> isotrue (all_abstractions_are_defined lib u)
    -> isotrue (all_abstractions_are_defined lib (subst t x u)).
Proof.
  introv isot isou.
  apply implies_isotrue_all_abstraction_are_defined_lsubst; auto.
  apply isotrue_all_abstractions_are_defined_sub_iff; simpl; introv i.
  repndors; ginv; tcsp.
Qed.

Lemma isotrue_all_abstractions_are_defined_oterm {o} :
  forall lib op (bs : list (@BTerm o)),
    isotrue (all_abstractions_are_defined lib (oterm op bs))
    <=> (found_opid_in_library_sign lib op = true
         # forall b, LIn b bs -> isotrue (all_abstractions_are_defined_b lib b)).
Proof.
  introv; simpl.
  rw isotrue_oband.
  rw isotrue_oball_map.
  remember (found_opid_in_library_sign lib op) as b; destruct b; simpl; split; tcsp.
Qed.

Lemma compute_step_preseves_all_abstractions_are_defined {o} :
  forall lib (t : @NTerm o) u,
    compute_step lib t = csuccess u
    -> isotrue (all_abstractions_are_defined lib t)
    -> isotrue (all_abstractions_are_defined lib u).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv comp allabs.

  - Case "vterm".
    csunf comp; allsimpl; ginv.

  - Case "sterm".
    csunf comp; allsimpl; ginv; auto.

  - Case "oterm".
    apply isotrue_all_abstractions_are_defined_oterm in allabs; repnd.
    dopid op as [can|ncan|exc|abs] SCase.

    + SCase "Can".
      csunf comp; allsimpl; ginv; auto.
      apply isotrue_all_abstractions_are_defined_oterm; auto.

    + SCase "NCan".
      destruct bs as [|b1 bs]; try (complete (allsimpl; ginv)).
      destruct b1 as [l t]; try (complete (allsimpl; ginv)).
      destruct l; try (complete (allsimpl; ginv)).

      {
        destruct t as [x|f|op bts]; try (complete (allsimpl; ginv));[|].

        - csunf comp; allsimpl.
          dopid_noncan ncan SSCase; allsimpl; ginv; auto.

          {
            SSCase "NApply".
            apply compute_step_seq_apply_success in comp; exrepnd; subst.
            apply isotrue_all_abstractions_are_defined_oterm; auto.
          }

          {
            SSCase "NEApply".

            apply compute_step_eapply_success in comp; exrepnd; subst.
            repndors; exrepnd; allsimpl; subst; auto.

            + apply compute_step_eapply2_success in comp1; repnd; subst.
              repndors; exrepnd; subst; ginv; auto.
              apply (allabs (nobnd (sterm f0))); tcsp.

            + apply (allabs (nobnd arg2)); tcsp.

            + fold_terms.
              apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
              introv i; repndors; subst; try (complete (apply allabs; tcsp)).
              allsimpl.
              pose proof (ind arg2 arg2 []) as h; clear ind.
              repeat (autodimp h hyp); eauto 3 with slow.
              apply h in comp1; auto; try (complete (apply (allabs (nobnd arg2)); tcsp)).
          }

          {
            SSCase "NFix".
            apply compute_step_fix_success in comp; exrepnd; subst.
            apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
            introv i; repndors; subst; try (complete (apply allabs; tcsp)).
            apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
          }

          {
            SSCase "NCbv".
            apply compute_step_cbv_success in comp; exrepnd; subst; allsimpl; auto.
            apply implies_isotrue_all_abstraction_are_defined_subst.
            - apply (allabs (bterm [v] x)); tcsp.
            - apply (allabs (nobnd (sterm f))); tcsp.
          }

          {
            SSCase "NTryCatch".
            apply compute_step_try_success in comp; exrepnd; subst.
            apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
            introv i; repndors; subst; tcsp; try (complete (apply allabs; tcsp)).
          }

          {
            SSCase "NCanTest".
            apply compute_step_seq_can_test_success in comp; exrepnd; subst.
            apply (allabs (nobnd b)); tcsp.
          }

        - dopid op as [can2|ncan2|exc2|abs2] SSCase.

          + SSCase "Can".
            dopid_noncan ncan SSSCase.

            {
              SSSCase "NApply".

              csunf comp; allsimpl.
              apply compute_step_apply_success in comp.
              repndors; exrepnd; subst; auto.

              - apply implies_isotrue_all_abstraction_are_defined_subst;
                try (apply (allabs (nobnd arg)); tcsp).
                pose proof (allabs (nobnd (mk_lam v b))) as q.
                autodimp q hyp.
                allsimpl; autorewrite with slow in *; auto.

              - apply isotrue_all_abstractions_are_defined_oterm; simpl; dands; auto.
            }

            {
              SSSCase "NEApply".

              csunf comp; allsimpl.
              apply compute_step_eapply_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; allsimpl; auto.

              - apply compute_step_eapply2_success in comp1; repnd; subst.
                repndors; exrepnd; subst; auto; ginv.

                + unfold mk_lam in *; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  apply iscan_implies in comp0; repndors; exrepnd; subst; simpl; auto.

                + unfold mk_nseq in *; allsimpl; ginv.
                  csunf; simpl.
                  dcwf h; simpl.
                  boolvar; simpl; auto; try omega.
                  rewrite Znat.Nat2Z.id; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isexc; auto.

              - fold_terms; rewrite compute_step_eapply_iscan_isnoncan_like; auto.

                pose proof (ind arg2 arg2 []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp1; clear q.
                rewrite comp1; auto.
            }

            {
              SSSCase "NFix".

              csunf comp; allsimpl.
              apply compute_step_fix_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NSpread".

              csunf comp; allsimpl.
              apply compute_step_spread_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NDsup".

              csunf comp; allsimpl.
              apply compute_step_dsup_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NDecide".

              csunf comp; allsimpl.
              apply compute_step_decide_success in comp.
              repndors; exrepnd; subst; auto.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NCbv".

              csunf comp; allsimpl.
              apply compute_step_cbv_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NSleep".

              csunf comp; allsimpl.
              apply compute_step_sleep_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NTUni".

              csunf comp; allsimpl.
              apply compute_step_tuni_success in comp.
              repndors; exrepnd; subst; auto.
              csunf; simpl.
              unfold compute_step_tuni; simpl.
              boolvar; try omega.
              rewrite Znat.Nat2Z.id; auto.
            }

            {
              SSSCase "NMinus".

              csunf comp; allsimpl.
              apply compute_step_minus_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NFresh".

              csunf comp; allsimpl; ginv.
            }

            {
              SSSCase "NTryCatch".

              csunf comp; allsimpl.
              apply compute_step_try_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NParallel".

              csunf comp; allsimpl.
              apply compute_step_parallel_success in comp.
              repndors; exrepnd; subst; auto.
            }

            {
              SSSCase "NCompOp".

              apply compute_step_ncompop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.

              - rewrite compute_step_ncompop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q.
                rewrite comp4; auto.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
            }

            {
              SSSCase "NArithOp".

              apply compute_step_narithop_can1_success in comp; repnd.
              repndors; exrepnd; allsimpl; subst; tcsp.

              - csunf; simpl.
                dcwf h.

              - rewrite compute_step_narithop_ncanlike2; auto.
                dcwf h.
                pose proof (ind t t []) as q; clear ind.
                repeat (autodimp q hyp); eauto 2 with slow.
                apply q in comp4; clear q.
                rewrite comp4; auto.

              - csunf; simpl.
                apply isexc_implies2 in comp1; exrepnd; subst.
                dcwf h; simpl; auto.
            }

            {
              SSSCase "NCanTest".

              csunf comp; allsimpl.
              apply compute_step_can_test_success in comp.
              repndors; exrepnd; subst; auto.
            }

          + SSCase "NCan".

            csunf comp; allsimpl.
            remember (compute_step lib (oterm (NCan ncan2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (NCan ncan2) bts) (oterm (NCan ncan2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q.
            csunf; simpl.
            rewrite Heqc; auto.

          + SSCase "Exc".

            csunf comp; allsimpl.
            apply compute_step_catch_success in comp.
            repndors; exrepnd; subst; allsimpl; ginv.

            * csunf; simpl; auto.

            * csunf; simpl; auto.
              rewrite compute_step_catch_if_diff; auto.

          + SSCase "Abs".

            csunf comp; allsimpl.
            remember (compute_step lib (oterm (Abs abs2) bts)) as c.
            destruct c; allsimpl; ginv.
            symmetry in Heqc.

            pose proof (ind (oterm (Abs abs2) bts) (oterm (Abs abs2) bts) []) as q; clear ind.
            repeat (autodimp q hyp); eauto 2 with slow.
            apply q in Heqc; clear q.
            csunf; simpl.
            rewrite Heqc; auto.
      }

      {
        csunf comp; allsimpl.
        apply compute_step_fresh_success in comp; exrepnd; subst.
        repndors; exrepnd; subst; ginv.

        - csunf; simpl; boolvar; auto.

        - rewrite compute_step_fresh_if_isvalue_like2; auto.

        - rewrite compute_step_fresh_if_isnoncan_like; auto.

          pose proof (ind t (subst t n (mk_utoken (get_fresh_atom t))) [n]) as q; clear ind.
          repeat (autodimp q hyp); eauto 2 with slow.
          { rewrite simple_osize_subst; eauto 2 with slow. }
          apply q in comp2; clear q.
          rewrite comp2; simpl; auto.
      }

    + SCase "Exc".

      csunf comp; allsimpl; ginv.

    + SCase "Abs".

      csunf comp; allsimpl.
      apply compute_step_lib_success in comp.
      exrepnd; subst.

      csunf; simpl.
      destruct e.
      apply (found_entry_implies_compute_step_lib_success _ _ _ _ _ _ correct).

      apply found_entry_add_new_abs; auto.

Qed.

Lemma tequality_cons_library_entry {o} :
  forall lib1 lib2 (t1 t2 : @CTerm o) eq,
    all_abstractions_are_defined_cterm lib1 t1
    -> all_abstractions_are_defined_cterm lib1 t2
    -> all_abstractions_are_defined_cterm lib2 t1
    -> all_abstractions_are_defined_cterm lib2 t2
    -> nuprl lib1 t1 t2 eq
    -> nuprl lib2 t1 t2 eq.
Proof.
  introv all11 all12 all21 all22 n.
  allunfold @nuprl.

  remember (univ lib1) as ts.
  close_cases (induction n using @close_ind') Case; subst.

  Focus 11.

  - Case "CL_func".
    clear per; spcast.
    repeat (autodimp IHn hyp); exrepnd.

XXXXXXXXXXXXXXXXXXX

    rename eq0 into eqa0.

    assert (forall a a' : CTerm,
               eqa a a' ->
               exists eq0,
                 close (e :: lib)
                       (univ (e :: lib))
                       (B) [[v \\ a]]
                       (B') [[v' \\ a']]
                       eq0) as recbb.
    { introv h; apply recb; auto. }
    clear recb.

    apply choice_teq0 in recbb; exrepnd.
    rename f into eqb0.

    exists (fun t t' =>
              forall a a' (e : eqa0 a a'),
                (eqb0 a a' e) (mkc_apply t a) (mkc_apply t' a')).

  - Case "CL_init".
    duniv i h.

    induction i; allsimpl; tcsp.
    repndors; exrepnd; spcast.

    + exists (fun A A' => exists eqa, close (e :: lib) (univi (e :: lib) i) A A' eqa).
      apply CL_init.
      exists (S i); simpl.
      left; dands; auto; spcast;
      try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

    + autodimp IHi hyp.

  - Case "CL_int".
    exists (equality_of_int (e :: lib)).
    apply CL_int.
    allunfold @per_int; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_atom".
    unfold per_atom in per; repnd; spcast.
    eexists.
    apply CL_atom.
    unfold per_atom; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_uatom".
    unfold per_uatom in per; repnd; spcast.
    eexists.
    apply CL_uatom.
    unfold per_uatom; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_base".
    unfold per_base in per; repnd; spcast.
    eexists.
    apply CL_base.
    unfold per_base; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_approx".
    unfold per_approx in per; exrepnd; spcast.
    eexists.
    apply CL_approx.
    unfold per_approx.
    eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)).
    allrw @approx_stable_iff; auto.

  - Case "CL_cequiv".
    unfold per_cequiv in per; exrepnd; spcast.
    eexists.
    apply CL_cequiv.
    unfold per_cequiv.
    eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)).
    allrw @cequiv_stable_iff; auto.

  - Case "CL_eq".
    clear per.
    autodimp IHteq0 hyp; exrepnd.
    eexists.
    apply CL_eq.
    unfold per_eq.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)); eauto.
    allrw @cequiv_stable_iff; auto.
Qed.

Lemma tequality_cons_library_entry {o} :
  forall lib e (t1 t2 : @CTerm o),
    !in_lib (opabs_of_lib_entry e) lib
    -> tequality lib t1 t2
    -> tequality (e :: lib) t1 t2.
Proof.
  introv p teq.
  allunfold @tequality; exrepnd.
  allunfold @nuprl.

  remember (univ lib) as ts.
  close_cases (induction teq0 using @close_ind') Case; subst.

  Focus 11.

  - Case "CL_func".
    clear per; spcast.
    autodimp IHteq0 hyp; exrepnd.
    rename eq0 into eqa0.

    assert (forall a a' : CTerm,
               eqa a a' ->
               exists eq0,
                 close (e :: lib)
                       (univ (e :: lib))
                       (B) [[v \\ a]]
                       (B') [[v' \\ a']]
                       eq0) as recbb.
    { introv h; apply recb; auto. }
    clear recb.

    apply choice_teq0 in recbb; exrepnd.
    rename f into eqb0.

    exists (fun t t' =>
              forall a a' (e : eqa0 a a'),
                (eqb0 a a' e) (mkc_apply t a) (mkc_apply t' a')).

  - Case "CL_init".
    duniv i h.

    induction i; allsimpl; tcsp.
    repndors; exrepnd; spcast.

    + exists (fun A A' => exists eqa, close (e :: lib) (univi (e :: lib) i) A A' eqa).
      apply CL_init.
      exists (S i); simpl.
      left; dands; auto; spcast;
      try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

    + autodimp IHi hyp.

  - Case "CL_int".
    exists (equality_of_int (e :: lib)).
    apply CL_int.
    allunfold @per_int; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_atom".
    unfold per_atom in per; repnd; spcast.
    eexists.
    apply CL_atom.
    unfold per_atom; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_uatom".
    unfold per_uatom in per; repnd; spcast.
    eexists.
    apply CL_uatom.
    unfold per_uatom; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_base".
    unfold per_base in per; repnd; spcast.
    eexists.
    apply CL_base.
    unfold per_base; repnd; dands; auto; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; auto)).

  - Case "CL_approx".
    unfold per_approx in per; exrepnd; spcast.
    eexists.
    apply CL_approx.
    unfold per_approx.
    eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)).
    allrw @approx_stable_iff; auto.

  - Case "CL_cequiv".
    unfold per_cequiv in per; exrepnd; spcast.
    eexists.
    apply CL_cequiv.
    unfold per_cequiv.
    eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)).
    allrw @cequiv_stable_iff; auto.

  - Case "CL_eq".
    clear per.
    autodimp IHteq0 hyp; exrepnd.
    eexists.
    apply CL_eq.
    unfold per_eq.
    eexists; eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast;
    try (complete (apply computes_to_valc_consistent_with_new_definition; eauto));
    try (complete (introv; apply t_iff_refl)); eauto.
    allrw @cequiv_stable_iff; auto.
Qed.

Lemma cover_vars_nil_iff_closed {o} :
  forall (t : @NTerm o), cover_vars t [] <=> closed t.
Proof.
  introv.
  rw @cover_vars_eq; simpl.
  unfold closed.
  rw subvars_eq; split; intro h; try (rewrite h); auto.
  remember (free_vars t) as l; clear Heql; destruct l; auto.
  apply subset_cons_nil in h; tcsp.
Qed.

Lemma cover_vars_nil2closed {o} :
  forall {t : @NTerm o}, cover_vars t [] -> closed t.
Proof.
  introv cov.
  apply cover_vars_nil_iff_closed; auto.
Qed.

Lemma wfClosed2isprogram {o} :
  forall {t : @NTerm o},
    wf_term t
    -> closed t
    -> isprogram t.
Proof.
  introv w c.
  constructor; eauto 3 with slow.
Qed.

Definition mk_cterm_wc {o}
           (t : @NTerm o)
           (w : wf_term t)
           (c : cover_vars t []) : CTerm :=
  mk_cterm t (wfClosed2isprogram w (cover_vars_nil2closed c)).

Lemma lsubstc_sub_nil {o} :
  forall (t : @NTerm o) w c,
    lsubstc t w [] c = mk_cterm_wc t w c.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_nil.
Qed.

Lemma sequent_true2_cons_library_entry {o} :
  forall lib e (c : @conclusion o),
    sequent_true2 lib (mk_baresequent [] c)
    -> sequent_true2 (e :: lib) (mk_baresequent [] c).
Proof.
  introv h.
  allunfold @sequent_true2; exrepnd.
  exists c0.
  allrw @sequent_true_eq_VR.
  allunfold @VR_sequent_true; introv.
  pose proof (h0 s1 s2) as q; clear h0; simpl in *.
  intros sim hf.
  dup sim as sim'.
  apply similarity_nil_implies in sim'; repnd; subst; allsimpl.
  pose proof (q (sim_nil lib) (hyps_functionality_nil lib)) as h; clear q; repnd.

  dands.

  - clear h.

    match goal with [ |- tequality _ (lsubstc _ _ _ ?c) _ ] => let c := fresh "c" in remember c; clear_eq1 c end.
    match goal with [ |- tequality _ _ (lsubstc _ _ _ ?c) ] => let c := fresh "c" in remember c; clear_eq1 c end.
    match goal with [ H : tequality _ (lsubstc _ _ _ ?c) _ |- _ ] => let c := fresh "c" in remember c; clear_eq1 c end.
    match goal with [ H : tequality _ _ (lsubstc _ _ _ ?c) |- _ ] => let c := fresh "c" in remember c; clear_eq1 c end.
    proof_irr.
    allrw @lsubstc_sub_nil.

Qed.

(* By assuming [wf_bseq seq], when we start with a sequent with no hypotheses,
   it means that we have to prove that the conclusion is well-formed and closed.
 *)
Lemma valid_proof {o} :
  forall ctxt (seq : @baresequent o) (wf : wf_bseq seq),
    Library ctxt
    -> proof ctxt seq
    -> sequent_true2 ctxt seq.
Proof.
  introv wf Lib p.
  induction p
    as [ (* proved sequent       *) seq p
       | (* isect_eq             *) a1 a2 b1 b2 e1 e2 x1 x2 y i hs niy p1 ih1 p2 ih2
       | (* approx_refl          *) a hs
       | (* cequiv_approx        *) a b e1 e2 hs p1 ih1 p2 ih2
       | (* approx_eq            *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       | (* cequiv_eq            *) a1 a2 b1 b2 e1 e2 i hs p1 ih1 p2 ih2
       | (* bottom_diverges      *) x hs js
       | (* cut                  *) B C t u x hs wB covB nixH p1 ih1 p2 ih2
       | (* equal_in_base        *) a b e F H p1 ih1 ps ihs
       | (* hypothesis           *) x A G J
       | (* cequiv_subst_concl   *) C x a b t e H wfa wfb cova covb p1 ih1 p2 ih2
       | (* approx_member_eq     *) a b e H p ih
       | (* cequiv_computation   *) a b H p ih
       | (* function elimination *) A B C a e ea f x z H J wa cova nizH nizJ dzf p1 ih1 p2 ih2
       ];
    allsimpl;
    allrw NVin_iff.

  -

Lemma seq_in_library_is_true {o} :
  forall (ctxt : @ProofContext o) c,
    Library ctxt
    -> LIn c (PC_conclusions ctxt)
    -> sequent_true2 ctxt (mk_baresequent [] c).
Proof.
  introv Lib.
  induction Lib; simpl; introv i; tcsp.
  - autodimp IHLib hyp.

Qed.

  - apply (rule_isect_equality2_true3 lib a1 a2 b1 b2 e1 e2 x1 x2 y i hs); simpl; tcsp.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply ih1; auto.
        apply (rule_isect_equality2_wf2 y i a1 a2 b1 b2 e1 e2 x1 x2 hs); simpl; tcsp.

      * apply ih2; auto.
        apply (rule_isect_equality2_wf2 y i a1 a2 b1 b2 e1 e2 x1 x2 hs); simpl; tcsp.

  - apply (rule_approx_refl_true3 lib hs a); simpl; tcsp.

  - apply (rule_cequiv_approx2_true3 lib hs a b e1 e2); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    apply ih2; auto.
    apply (rule_cequiv_approx2_wf2 a b e1 e2 hs); simpl; tcsp.

  - apply (rule_approx_eq2_true3 lib a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_approx_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_approx_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

  - apply (rule_cequiv_eq2_true3 lib a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.
    introv xx; repndors; subst; tcsp.

    + apply ih1; auto.
      apply (rule_cequiv_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

    + apply ih2; auto.
      apply (rule_cequiv_eq2_wf2 a1 a2 b1 b2 e1 e2 i hs); simpl; tcsp.

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
    apply in_mapin; eauto.

  - apply (rule_hypothesis_true3 lib); simpl; tcsp.

  - apply (rule_cequiv_subst_concl2_true3 lib H x C a b t e); allsimpl; tcsp.

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
Qed.

Fixpoint map_option
         {T U : Type}
         (f : T -> option U)
         (l : list T) : option (list U) :=
  match l with
  | [] => Some []
  | t :: ts =>
    match f t, map_option f ts with
    | Some u, Some us => Some (u :: us)
    | _, _ => None
    end
  end.

Fixpoint map_option_in
         {T U : Type}
         (l : list T)
  : forall (f : forall (t : T) (i : LIn t l), option U), option (list U) :=
  match l with
  | [] => fun f => Some []
  | t :: ts =>
    fun f =>
      match f t (@inl (t = t) (LIn t ts) eq_refl), map_option_in ts (fun x i => f x (inr i)) with
      | Some u, Some us => Some (u :: us)
      | _, _ => None
      end
  end.

Fixpoint map_option_in_fun
         {T U}
         (l : list T)
  : (forall t, LIn t l -> option (U t)) -> option (forall t, LIn t l -> U t) :=
  match l with
  | [] => fun f => Some (fun t (i : LIn t []) => match i with end)
  | t :: ts =>
    fun (f : forall x, LIn x (t :: ts) -> option (U x)) =>
      match f t (@inl (t = t) (LIn t ts) eq_refl),
            map_option_in_fun ts (fun x i => f x (inr i)) with
      | Some u, Some g => Some (fun x (i : LIn x (t :: ts)) =>
                                   match i with
                                   | inl e => transport e u
                                   | inr j => g x j
                                   end)
      | _, _ => None
      end
  end.

Lemma map_option_in_fun2_lem :
  forall {T : Type }
         (l : list T)
         (U : forall (t : T) (i : LIn t l), Type)
         (f : forall (t : T) (i : LIn t l), option (U t i)),
    option (forall t (i : LIn t l), U t i).
Proof.
  induction l; introv f; simpl in *.
  - left; introv; destruct i.
  - pose proof (f a (inl eq_refl)) as opt1.
    destruct opt1 as [u|];[|right].
    pose proof (IHl (fun x i => U x (inr i)) (fun x i => f x (inr i))) as opt2.
    destruct opt2 as [g|];[|right].
    left.
    introv.
    destruct i as [i|i].
    + rewrite <- i.
      exact u.
    + apply g.
Defined.

Fixpoint map_option_in_fun2
         {T : Type }
         (l : list T)
  : forall (U : forall (t : T) (i : LIn t l), Type),
    (forall (t : T) (i : LIn t l), option (U t i))
    -> option (forall t (i : LIn t l), U t i) :=
  match l with
  | [] => fun U f => Some (fun t (i : LIn t []) => match i with end)
  | t :: ts =>
    fun (U : forall (x : T) (i : LIn x (t :: ts)), Type)
        (f : forall x (i : LIn x (t :: ts)), option (U x i)) =>
      match f t (@inl (t = t) (LIn t ts) eq_refl),
            @map_option_in_fun2 T ts (fun x i => U x (inr i)) (fun x i => f x (inr i))
            return option (forall x (i : LIn x (t :: ts)), U x i)
      with
      | Some u, Some g => Some (fun x (i : LIn x (t :: ts)) =>
                                  match i as s return U x s with
                                  | inl e =>
                                    internal_eq_rew_dep
                                      T t
                                      (fun (x : T) (i : t = x) => U x injL(i))
                                      u x e
                                  | inr j => g x j
                                  end)
      | _, _ => None
      end
  end.

Fixpoint finish_pre_proof
         {o} {seq : @pre_baresequent o} {h : bool} {lib}
         (prf: pre_proof h lib seq) : option (pre_proof false lib seq) :=
  match prf with
  | pre_proof_hole s e => None
  | pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH pa pb =>
    match finish_pre_proof pa, finish_pre_proof pb with
    | Some p1, Some p2 => Some (pre_proof_isect_eq _ _ a1 a2 b1 b2 x1 x2 y i H niyH p1 p2)
    | _, _ => None
    end
  | pre_proof_approx_refl a H => Some (pre_proof_approx_refl _ _ a H)
  | pre_proof_cequiv_approx a b H p1 p2 =>
    match finish_pre_proof p1, finish_pre_proof p2 with
    | Some p1, Some p2 => Some (pre_proof_cequiv_approx _ _ a b H p1 p2)
    | _, _ => None
    end
  | pre_proof_approx_eq a1 a2 b1 b2 i H p1 p2 =>
    match finish_pre_proof p1, finish_pre_proof p2 with
    | Some p1, Some p2 => Some (pre_proof_approx_eq _ _ a1 a2 b1 b2 i H p1 p2)
    | _, _ => None
    end
  | pre_proof_cequiv_eq a1 a2 b1 b2 i H p1 p2 =>
    match finish_pre_proof p1, finish_pre_proof p2 with
    | Some p1, Some p2 => Some (pre_proof_cequiv_eq _ _ a1 a2 b1 b2 i H p1 p2)
    | _, _ => None
    end
  | pre_proof_bottom_diverges x H J => Some (pre_proof_bottom_diverges _ _ x H J)
  | pre_proof_cut B C x H wB cBH nixH pu pt =>
    match finish_pre_proof pu, finish_pre_proof pt with
    | Some p1, Some p2 => Some (pre_proof_cut _ _ B C x H wB cBH nixH p1 p2)
    | _, _ => None
    end
  | pre_proof_equal_in_base a b H p1 pl =>
    let op := map_option_in_fun (free_vars a) (fun v i => finish_pre_proof (pl v i)) in
    match finish_pre_proof p1, op with
    | Some p1, Some g => Some (pre_proof_equal_in_base _ _ a b H p1 g)
    | _, _ => None
    end
  | pre_proof_hypothesis x A G J => Some (pre_proof_hypothesis _ _ x A G J)
  | pre_proof_cequiv_subst_concl C x a b H wa wb ca cb p1 p2 =>
    match finish_pre_proof p1, finish_pre_proof p2 with
    | Some p1, Some p2 => Some (pre_proof_cequiv_subst_concl _ _ C x a b H wa wb ca cb p1 p2)
    | _, _ => None
    end
  | pre_proof_approx_member_eq a b H p1 =>
    match finish_pre_proof p1 with
    | Some p1 => Some (pre_proof_approx_member_eq _ _ a b H p1)
    | _ => None
    end
  | pre_proof_cequiv_computation a b H r => Some (pre_proof_cequiv_computation _ _ a b H r)
  | pre_proof_function_elimination A B C a f x z H J wa cova nizH nizJ dzf p1 p2 =>
    match finish_pre_proof p1, finish_pre_proof p2 with
    | Some p1, Some p2 => Some (pre_proof_function_elimination _ _ A B C a f x z H J wa cova nizH nizJ dzf p1 p2)
    | _, _ => None
    end
  end.

Definition pre2conclusion {o} (c : @pre_conclusion o) (e : @NTerm o) :=
  match c with
  | pre_concl_ext T => concl_ext T e
  | pre_concl_typ T => concl_typ T
  end.

Definition pre2baresequent {o} (s : @pre_baresequent o) (e : @NTerm o) :=
  mk_baresequent
    (pre_hyps s)
    (pre2conclusion (pre_concl s) e).

Definition ExtractProof {o} (seq : @pre_baresequent o) lib :=
  {e : NTerm & proof lib (pre2baresequent seq e)}.

Definition mkExtractProof {o} {lib}
           (seq : @pre_baresequent o)
           (e : @NTerm o)
           (p : proof lib (pre2baresequent seq e))
  : ExtractProof seq lib :=
  existT _ e p.

(* converts a pre-proof without holes to a proof without holes by
 * generating the extract
 *)
Fixpoint pre_proof2iproof
         {o} {seq : @pre_baresequent o} {lib}
         (prf : pre_proof false lib seq)
  : ExtractProof seq lib  :=
  match prf with
  | pre_proof_hole s e => match e with end
  | pre_proof_isect_eq a1 a2 b1 b2 x1 x2 y i H niyH pa pb =>
    match pre_proof2iproof pa, pre_proof2iproof pb with
    | existT e1 p1, existT e2 p2 =>
      mkExtractProof
        (pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
        mk_axiom
        (proof_isect_eq _ a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH p1 p2)
 (* I need to generalize the rule a bit to allow any extract in subgoals *)
    end
  | pre_proof_approx_refl a H =>
    mkExtractProof
      (pre_rule_approx_refl_concl a H)
      mk_axiom
      (proof_approx_refl _ a H)
  | pre_proof_cequiv_approx a b H p1 p2 =>
    match pre_proof2iproof p1, pre_proof2iproof p2 with
    | existT e1 p1, existT e2 p2 =>
      mkExtractProof
        (pre_rule_cequiv_approx_concl a b H)
        mk_axiom
        (proof_cequiv_approx _ a b e1 e2 H p1 p2)
    end
  | pre_proof_approx_eq a1 a2 b1 b2 i H p1 p2 =>
    match pre_proof2iproof p1, pre_proof2iproof p2 with
    | existT e1 p1, existT e2 p2 =>
      mkExtractProof
        (pre_rule_approx_eq_concl a1 a2 b1 b2 i H)
        mk_axiom
        (proof_approx_eq _ a1 a2 b1 b2 e1 e2 i H p1 p2)
    end
  | pre_proof_cequiv_eq a1 a2 b1 b2 i H p1 p2 =>
    match pre_proof2iproof p1, pre_proof2iproof p2 with
    | existT e1 p1, existT e2 p2 =>
      mkExtractProof
        (pre_rule_cequiv_eq_concl a1 a2 b1 b2 i H)
        mk_axiom
        (proof_cequiv_eq _ a1 a2 b1 b2 e1 e2 i H p1 p2)
    end
  | pre_proof_bottom_diverges x H J =>
    mkExtractProof
      (pre_rule_bottom_diverges_concl x H J)
      mk_bottom
      (proof_bottom_diverges _ x H J)
  | pre_proof_cut B C x H wB cBH nixH pu pt =>
    match pre_proof2iproof pu, pre_proof2iproof pt with
    | existT u p1, existT t p2 =>
      mkExtractProof
        (pre_rule_cut_concl H C)
        (subst t x u)
        (proof_cut _ B C t u x H wB cBH nixH p1 p2)
    end
  | pre_proof_equal_in_base a b H p1 pl =>
    let F := fun v (i : LIn v (free_vars a)) => pre_proof2iproof (pl v i) in
    let E := fun v i => projT1 (F v i) in
    let P := fun v i => projT2 (F v i) in
    match pre_proof2iproof p1 with
    | existT e p1 =>
      mkExtractProof
        (pre_rule_equal_in_base_concl a b H)
        mk_axiom
        (proof_equal_in_base _ a b e E H p1 P)
    end
  | pre_proof_hypothesis x A G J =>
    mkExtractProof
      (pre_rule_hypothesis_concl G J A x)
      (mk_var x)
      (proof_hypothesis _ x A G J)
  | pre_proof_cequiv_subst_concl C x a b H wa wb ca cb p1 p2 =>
    match pre_proof2iproof p1, pre_proof2iproof p2 with
    | existT t p1, existT e p2 =>
      mkExtractProof
        (pre_rule_cequiv_subst_hyp1 H x C a)
        t
        (proof_cequiv_subst_concl _ C x a b t e H wa wb ca cb p1 p2)
    end
  | pre_proof_approx_member_eq a b H p1 =>
    match pre_proof2iproof p1 with
    | existT e1 p1 =>
      mkExtractProof
        (pre_rule_approx_member_eq_concl a b H)
        mk_axiom
        (proof_approx_member_eq _ a b e1 H p1)
    end
  | pre_proof_cequiv_computation a b H r =>
    mkExtractProof
      (pre_rule_cequiv_concl a b H)
      mk_axiom
      (proof_cequiv_computation _ a b H r)
  | pre_proof_function_elimination A B C a f x z H J wa cova nizH nizJ dzf p1 p2 =>
    match pre_proof2iproof p1, pre_proof2iproof p2 with
    | existT ea p1, existT e p2 =>
      mkExtractProof
        (pre_rule_function_elimination_concl A B C f x H J)
        (subst e z mk_axiom)
        (proof_function_elimination _ A B C a e ea f x z H J wa cova nizH nizJ dzf p1 p2)
    end
  end.

Lemma test {o} :
  @sequent_true2 o emlib (mk_baresequent [] (mk_conclax ((mk_member mk_axiom mk_unit)))).
Proof.
  apply valid_proof;
  [ exact (eq_refl, (eq_refl, eq_refl))
  | exact (proof_approx_member_eq emlib (mk_axiom) (mk_axiom) (mk_axiom) (nil) (proof_approx_refl emlib (mk_axiom) (nil)))
          (* This last bit was generated by JonPRL; I've got to generate the whole thing now *)
  ].
Qed.


(*
Inductive test : nat -> Type :=
| Foo : test 1
| Bar : test 0.

(* works *)
Definition xxx {n : nat} (t : test n) : test n :=
  match t with
  | Foo => Foo
  | Bar => Bar
  end.

(* works *)
Definition yyy {n : nat} (t : test n) : test n :=
  match t with
  | Foo => Foo
  | x => x
  end.

(* works *)
Definition www {n : nat} (t : test n) : option (test n) :=
  match t with
  | Foo => Some Foo
  | Bar => None
  end.

(* doesn't work *)
Definition zzz {n : nat} (t : test n) : test n :=
  match t with
  | Foo => Foo
  | Bar => t
  end.
*)

Definition proof_update_fun {o} lib (s seq : @baresequent o) :=
  proof lib s -> proof lib seq.

Definition proof_update {o} lib (seq : @baresequent o) :=
  {s : @baresequent o & proof_update_fun lib s seq}.

Definition ProofUpdate {o} lib (seq : @baresequent o) :=
  option (proof_update lib seq).

Definition retProofUpd
           {o} {lib} {seq : @baresequent o}
           (s : @baresequent o)
           (f : proof lib s -> proof lib seq)
  : ProofUpdate lib seq :=
  Some (existT _ s f).

Definition idProofUpd
           {o} {lib}
           (seq : @baresequent o)
  : ProofUpdate lib seq :=
  retProofUpd seq (fun p => p).

Definition noProofUpd {o} {lib} {seq : @baresequent o}
  : ProofUpdate lib seq :=
  None.

Definition bindProofUpd
           {o} {lib} {seq1 seq2 : @baresequent o}
           (pu  : ProofUpdate lib seq1)
           (puf : proof lib seq1 -> proof lib seq2)
  : ProofUpdate lib seq2 :=
  match pu with
  | Some (existT s f) => retProofUpd s (fun p => puf (f p))
  | None => None
  end.

Definition address := list nat.

Fixpoint get_sequent_fun_at_address {o}
         {lib}
         {seq  : @baresequent o}
         (prf  : proof lib seq)
         (addr : address) : ProofUpdate lib seq :=
  match prf with
  | proof_isect_eq a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH pa pb =>
    match addr with
    | [] => idProofUpd (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pa addr)
        (fun x => proof_isect_eq _ a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH x pb)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pb addr)
        (fun x => proof_isect_eq _ a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH pa x)
    | _ => noProofUpd
    end
  | proof_approx_refl a H =>
    match addr with
    | [] => idProofUpd (rule_approx_refl_concl a H)
    | _ => noProofUpd
    end
  | proof_cequiv_approx a b e1 e2 H p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_cequiv_approx_concl a b H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun x => proof_cequiv_approx _ a b e1 e2 H x p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun x => proof_cequiv_approx _ a b e1 e2 H p1 x)
    | _ => noProofUpd
    end
  | proof_approx_eq a1 a2 b1 b2 e1 e2 i H p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_approx_eq_concl a1 a2 b1 b2 i H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun x => proof_approx_eq _ a1 a2 b1 b2 e1 e2 i H x p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun x => proof_approx_eq _ a1 a2 b1 b2 e1 e2 i H p1 x)
    | _ => noProofUpd
    end
  | proof_cequiv_eq a1 a2 b1 b2 e1 e2 i H p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_cequiv_eq_concl a1 a2 b1 b2 i H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun x => proof_cequiv_eq _ a1 a2 b1 b2 e1 e2 i H x p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun x => proof_cequiv_eq _ a1 a2 b1 b2 e1 e2 i H p1 x)
    | _ => noProofUpd
    end
  | proof_bottom_diverges x H J =>
    match addr with
    | [] => idProofUpd (rule_bottom_diverges_concl x H J)
    | _ => noProofUpd
    end
  | proof_cut B C t u x H wB cBH nixH pu pt =>
    match addr with
    | [] => idProofUpd (rule_cut_concl H C t x u)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pu addr)
        (fun z => proof_cut _ B C t u x H wB cBH nixH z pt)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address pt addr)
        (fun z => proof_cut _ B C t u x H wB cBH nixH pu z)
    | _ => noProofUpd
    end
  | proof_equal_in_base a b e F H p1 pl =>
    match addr with
    | [] => idProofUpd (rule_equal_in_base_concl a b H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun z => proof_equal_in_base _ a b e F H z pl)
    | _ => noProofUpd (* TODO *)
    end
  | proof_hypothesis x A G J =>
    match addr with
    | [] => idProofUpd (rule_hypothesis_concl G J A x)
    | _ => noProofUpd
    end
  | proof_cequiv_subst_concl C x a b t e H wa wb ca cb p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_cequiv_subst_hyp1 H x C a t)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun z => proof_cequiv_subst_concl _ C x a b t e H wa wb ca cb z p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun z => proof_cequiv_subst_concl _ C x a b t e H wa wb ca cb p1 z)
    | _ => noProofUpd
    end
  | proof_approx_member_eq a b e H p1 =>
    match addr with
    | [] => idProofUpd (rule_approx_member_eq_concl a b H)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun z => proof_approx_member_eq _ a b e H z)
    | _ => noProofUpd
    end
  | proof_cequiv_computation a b H r =>
    match addr with
    | [] => idProofUpd (rule_cequiv_concl a b H)
    | _ => noProofUpd
    end
  | proof_function_elimination A B C a e ea f x z H J wa cova nizH nizJ dzf p1 p2 =>
    match addr with
    | [] => idProofUpd (rule_function_elimination_concl A B C e f x z H J)
    | 1 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p1 addr)
        (fun p => proof_function_elimination _ A B C a e ea f x z H J wa cova nizH nizJ dzf p p2)
    | 2 :: addr =>
      bindProofUpd
        (get_sequent_fun_at_address p2 addr)
        (fun p => proof_function_elimination _ A B C a e ea f x z H J wa cova nizH nizJ dzf p1 p)
    | _ => noProofUpd
    end
  end.

Fixpoint get_sequent_at_address {o}
           {seq  : @baresequent o}
           {lib}
           (prf  : proof lib seq)
           (addr : address) : option baresequent :=
  match get_sequent_fun_at_address prf addr with
  | Some (existT s _) => Some s
  | _ => None
  end.

Definition list1 {T} : forall a : T, LIn a [a].
Proof.
  tcsp.
Qed.


(* Looking at how we can define a Nuprl process *)

Inductive command {o} :=
(* add a definition at the head *)
| COM_add_def :
    forall (opabs   : opabs)
           (vars    : list sovar_sig)
           (rhs     : @SOTerm o)
           (correct : correct_abs opabs vars rhs),
      command
(* tries to complete a proof if it has no holes *)
| COM_finish_proof :
    ProofName -> command
(* focuses to a node in a proof *)
| COM_focus_proof :
    ProofName -> address -> command.

Definition proof_library {o} lib := list (@proof_library_entry o lib).

Record proof_update_seq {o} lib :=
  MkProofUpdateSeq
    {
      PUS_name  : ProofName;
      PUS_seq   : @baresequent o;
      PUS_focus : baresequent;
      PUS_upd   : proof_update_fun lib PUS_focus PUS_seq
    }.

Definition ProofUpdateSeq {o} lib :=
  option (@proof_update_seq o lib).

Record NuprlState {o} :=
  MkNuprlState
    {
      NuprlState_def_library   : @library o;
      NuprlState_proof_library : @proof_library o NuprlState_def_library;
      NuprlState_focus         : @ProofUpdateSeq o NuprlState_def_library
    }.

Fixpoint proof_consistent_with_new_definition
         {o} {seq : @baresequent o} {lib}
         (prf : proof lib seq)
         (e   : library_entry)
         (p   : !in_lib (opabs_of_lib_entry e) lib)
  : proof (e :: lib) seq :=
  match prf with
  | proof_isect_eq a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH pa pb =>
    let p1 := proof_consistent_with_new_definition pa e p in
    let p2 := proof_consistent_with_new_definition pb e p in
    proof_isect_eq _ a1 a2 b1 b2 e1 e2 x1 x2 y i H niyH p1 p2
  | proof_approx_refl a H => proof_approx_refl _ a H
  | proof_cequiv_approx a b e1 e2 H p1 p2 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let p2 := proof_consistent_with_new_definition p2 e p in
    proof_cequiv_approx _ a b e1 e2 H p1 p2
  | proof_approx_eq a1 a2 b1 b2 e1 e2 i H p1 p2 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let p2 := proof_consistent_with_new_definition p2 e p in
    proof_approx_eq _ a1 a2 b1 b2 e1 e2 i H p1 p2
  | proof_cequiv_eq a1 a2 b1 b2 e1 e2 i H p1 p2 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let p2 := proof_consistent_with_new_definition p2 e p in
    proof_cequiv_eq _ a1 a2 b1 b2 e1 e2 i H p1 p2
  | proof_bottom_diverges x H J => proof_bottom_diverges _ x H J
  | proof_cut B C t u x H wB cBH nixH pu pt =>
    let p1 := proof_consistent_with_new_definition pu e p in
    let p2 := proof_consistent_with_new_definition pt e p in
    proof_cut _ B C t u x H wB cBH nixH p1 p2
  | proof_equal_in_base a b ee F H p1 pl =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let g := fun v (i : LIn v (free_vars a)) => proof_consistent_with_new_definition (pl v i) e p in
    proof_equal_in_base _ a b ee F H p1 g
  | proof_hypothesis x A G J => proof_hypothesis _ x A G J
  | proof_cequiv_subst_concl C x a b t ee H wa wb ca cb p1 p2 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let p2 := proof_consistent_with_new_definition p2 e p in
    proof_cequiv_subst_concl _ C x a b t ee H wa wb ca cb p1 p2
  | proof_approx_member_eq a b ee H p1 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    proof_approx_member_eq _ a b ee H p1
  | proof_cequiv_computation a b H r =>
    proof_cequiv_computation
      _ a b H
      (reduces_to_consistent_with_new_definition a b r e p)
  | proof_function_elimination A B C a ee ea f x z H J wa cova nizH nizJ dzf p1 p2 =>
    let p1 := proof_consistent_with_new_definition p1 e p in
    let p2 := proof_consistent_with_new_definition p2 e p in
    proof_function_elimination _ A B C a ee ea f x z H J wa cova nizH nizJ dzf p1 p2
  end.

Definition NuprlState_add_def_lib {o}
           (state   : @NuprlState o)
           (opabs   : opabs)
           (vars    : list sovar_sig)
           (rhs     : SOTerm)
           (correct : correct_abs opabs vars rhs) : NuprlState :=
  let lib := NuprlState_def_library state in
  match in_lib_dec opabs lib with
  | inl _ => state
  | inr p =>
    @MkNuprlState
      o
      (lib_abs opabs vars rhs correct :: lib)
      (NuprlState_proof_library state)
      (NuprlState_focus state)
  end.

Definition NuprlState_upd_proof_lib {o}
           (state : @NuprlState o)
           (lib   : @proof_library o) : NuprlState :=
  @MkNuprlState
    o
    (NuprlState_def_library state)
    lib
    (NuprlState_focus state).

Definition NuprlState_upd_focus {o}
           (state : @NuprlState o)
           (upd   : @ProofUpdateSeq o) : NuprlState :=
  @MkNuprlState
    o
    (NuprlState_def_library state)
    (NuprlState_proof_library state)
    upd.

Definition proof_library_entry_upd_proof {o} {lib}
           (e : @proof_library_entry o lib)
           (p : proof lib (proof_library_entry_seq lib e))
  : proof_library_entry lib :=
  MkProofLibEntry
    _
    _
    (proof_library_entry_name _ e)
    (proof_library_entry_seq _ e)
    h
    p.

Fixpoint finish_proof_in_library {o}
           (lib : @proof_library o)
           (name : ProofName) : proof_library :=
  match lib with
  | [] => []
  | p :: ps =>
    if String.string_dec (proof_library_entry_name p) name
    then if proof_library_entry_hole p (* no need to finish the proof if it is already finished *)
         then let p' := option_with_default
                          (option_map (fun p' => proof_library_entry_upd_proof p p')
                                      (finish_proof (proof_library_entry_proof p)))
                          p
              in p' :: ps
         else p :: ps
    else p :: finish_proof_in_library ps name
  end.

Fixpoint focus_proof_in_library {o}
           (lib : @proof_library o)
           (name : ProofName)
           (addr : address) : ProofUpdateSeq :=
  match lib with
  | [] => None
  | p :: ps =>
    if String.string_dec (proof_library_entry_name p) name
    then match get_sequent_fun_at_address (proof_library_entry_proof p) addr with
         | Some (existT s f) =>
           Some (MkProofUpdateSeq
                   o
                   name
                   (proof_library_entry_hole p)
                   (proof_library_entry_seq p)
                   s
                   f)
         | None => None
         end
    else focus_proof_in_library ps name addr
  end.

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

CoInductive Loop {o} : Type :=
| proc : (@command o -> Loop) -> Loop.

CoFixpoint loop {o} (state : @NuprlState o) : Loop :=
  proc (fun c => loop (update state c)).


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/" "../per/")
*** End:
*)
