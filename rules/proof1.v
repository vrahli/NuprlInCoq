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

Require Export computation10.
Require Export computation_preserves_lib.
Require Export computation_preserves_abs2bot.
Require Export computation_preserves_diff_abs_bot.
Require Export cequiv_lsubst.


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
      -> proof ctxt (rule_cequiv_computation_concl a b H)
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
  - constructor.
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

Hint Resolve computes_to_valc_implies_cequivc : slow.

(*
Definition unfold_entry_abs {o}
           (e  : library_entry)
           (op : @Opid o)
           (bs : list (@BTerm o)) : NTerm :=
  match op with
  | Abs abs =>
    match unfold_abs_entry e abs bs with
    | Some u => u
    | None => mk_bottom
    end
  | _ => oterm op bs
  end.

Fixpoint unfold_entry {o} (e : library_entry) (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => vterm v
  | sterm f => sterm (fun n => unfold_entry e (f n))
  | oterm op bs => unfold_entry_abs e op (map (unfold_entry_bterm e) bs)
  end
with unfold_entry_bterm {o} (e : library_entry) (b : @BTerm o) : BTerm :=
       match b with
       | bterm l t => bterm l (unfold_entry e t)
       end.

Fixpoint unfold_lib {o} (lib : @library o) (t : @NTerm o) : NTerm :=
  match lib with
  | [] => t
  | entry :: entries => unfold_lib entries (unfold_entry entry t)
  end.
 *)

Record LibTerm {o} :=
  MkLibTerm
    {
      LT_lib  : @library o;
      LT_term : @NTerm o
    }.

Definition size_lib_term {o} (LT : @LibTerm o) : (nat * ord) :=
  (length (LT_lib LT), osize (LT_term LT)).

Inductive lt_lib_term {o} (lt1 lt2 : @LibTerm o) : Prop :=
| lt_lib_term_lib :
    length (LT_lib lt1) < length (LT_lib lt2)
    -> lt_lib_term lt1 lt2
| lt_lib_term_term :
    length (LT_lib lt1) = length (LT_lib lt2)
    -> ord_lt (osize (LT_term lt1)) (osize (LT_term lt2))
    -> lt_lib_term lt1 lt2.

Lemma lt_lib_term_wf {o} :
  well_founded (@lt_lib_term o).
Proof.
  introv.
  destruct a as [l t].
  remember (length l) as n.
  revert dependent l.
  revert t.
  induction n as [n ind1] using comp_ind.
  intro t.
  remember (osize t) as s.
  revert dependent t.
  induction s as [s ind2] using comp_ind_ord.
  introv es en; subst.

  constructor.
  destruct l; allsimpl; ginv; introv ltlt.

  - inversion ltlt as [ltl|]; allsimpl; clear ltlt.

    + destruct y as [l1 t1]; allsimpl.
      destruct l1; allsimpl; ginv; try omega.

    + destruct y as [l1 t1]; allsimpl.
      destruct l1; allsimpl; ginv.
      pose proof (ind2 (osize t1)) as h; autodimp h hyp.

  - inversion ltlt as [ltl|ltl ltt]; allsimpl; clear ltlt.

    + destruct y as [l1 t1]; allsimpl.
      eapply ind1;[exact ltl|]; auto.

    + destruct y as [l1 t1]; allsimpl.
      destruct l1 as [|e1 l1]; allsimpl; ginv; inj.
      eapply ind2;[exact ltt| |]; simpl; auto.
Qed.

Definition unfold_entry_op {o}
           (entry : library_entry)
           (op : @Opid o)
           (bs : list BTerm) : NTerm :=
  match op with
  | Abs abs =>
    match unfold_abs_entry entry abs bs with
    | Some u => u
    | None => oterm op bs
    end
  | _ => oterm op bs
  end.

Fixpoint unfold_entry {o} (e : library_entry) (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => vterm v
  | sterm f => sterm (fun n => unfold_entry e (f n))
  | oterm op bs =>
    unfold_entry_op e op (map (unfold_entry_bterm e) bs)
  end
with unfold_entry_bterm {o} (e : library_entry) (b : @BTerm o) : BTerm :=
       match b with
       | bterm vs t => bterm vs (unfold_entry e t)
       end.

Fixpoint unfold_library {o} (l : library) (t : @NTerm o) : NTerm :=
  match l with
  | [] => t
  | entry :: entries =>
    unfold_library entries (unfold_entry entry t)
  end.

Definition unfold_lib {o} lib (t : @NTerm o) : NTerm :=
  abs2bot (unfold_library lib t).

(* then replace non-unfolded abs by bottom.
   then what? *)

(*
Definition unfold_library {o} (LT : @LibTerm o) : NTerm :=
  @Fix LibTerm
       (fun a b => lt_lib_term a b)
       lt_lib_term_wf
       (fun _ => NTerm)
       (fun LT =>
          match LT with
          | MkLibTerm l t =>
            match t with
            | vterm v => vterm v
            | sterm f => sterm (fun n => unfold_library (l,f n))
            | oterm (Abs abs) bs =>
              match l with
              | [] => mk_bottom
              | entry :: entries =>
                match unfold_abs_entry entry abs bs with
                | Some u => unfold_library (entries, u)
                | None => unfold_library (entries,oterm (Abs abs) bs)
                end
              end
            | oterm op bs => oterm op (map (fun b => unfold_library_bterm (l,b)) bs)
            end
          end
with unfold_library_bterm {o} (a : library * @BTerm o) : BTerm :=
       match a with
       | (l,b) =>
         match b with
         | bterm vs t => bterm vs (unfold_library (l,t))
         end
       end.

Fixpoint unfold_library {o} (l : library) (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => vterm v
  | sterm f => sterm (fun n => unfold_library l (f n))
  | oterm op bs => unfold_library_abs l op (map (unfold_library_bterm l) bs)
  end
with unfold_library_bterm {o} (l : library) (b : @BTerm o) : BTerm :=
       match b with
       | bterm vs t => bterm vs (unfold_library l t)
       end
with unfold_library_abs {o} (l : library) (op : @Opid o) (bs : list (@BTerm o)) : NTerm :=
       match op with
       | Abs abs =>
         match l with
         | [] => mk_bottom
         | entry :: entries =>
           match unfold_abs_entry entry abs bs with
           | Some u => unfold_library entries u
           | None => unfold_library_abs entries op bs
           end
         end
       | _ => oterm op bs
       end.
 *)

Lemma implies_approx_sterm {o} :
  forall lib (f1 f2 : @ntseq o),
    isprog (sterm f1)
    -> isprog (sterm f2)
    -> (forall n, approx lib (f1 n) (f2 n))
    -> approx lib (sterm f1) (sterm f2).
Proof.
  introv isp1 isp2 h.
  constructor; unfold close_comput; dands; eauto 3 with slow.

  - introv comp.
    apply computes_to_value_isvalue_eq in comp; eauto 3 with slow; ginv.

  - introv comp.
    eapply computes_to_value_and_exception_false in comp;
      [|apply computes_to_value_isvalue_refl]; eauto 2 with slow.
    tcsp.

  - introv comp.
    apply reduces_to_if_isvalue_like in comp; eauto 3 with slow.
    inversion comp; subst; clear comp.
    exists f2; dands; eauto 3 with slow; auto.
    apply reduces_to_symm.
    introv; left; apply h.
Qed.

Lemma reduces_to_abs2bot {o} :
  forall (t : @NTerm o) u,
    wf_term t
    -> reduces_to [] t u
    -> {w : NTerm
        & reduces_to [] (abs2bot t) w
        # alpha_eq w (abs2bot u)}.
Proof.
  introv wf comp.
  allunfold @reduces_to; exrepnd.
  revert dependent t.
  induction k; introv wf comp.

  - allrw @reduces_in_atmost_k_steps_0; subst.
    exists (abs2bot u).
    dands; auto.
    exists 0.
    apply reduces_in_atmost_k_steps_0; auto.

  - rw @reduces_in_atmost_k_steps_S in comp; exrepnd.
    pose proof (compute_step_abs2bot t u0 wf comp1) as h; exrepnd.

    applydup @preserve_nt_wf_compute_step in comp1; eauto 3 with slow.

    pose proof (IHk u0) as q; clear IHk.
    repeat (autodimp q hyp); eauto 3 with slow.
    exrepnd.

    pose proof (reduces_in_atmost_k_steps_alpha [] (abs2bot u0) w) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    apply q in q2; clear q; exrepnd.

    exists t2'; dands; eauto 3 with slow.
    exists (S k0).
    rw @reduces_in_atmost_k_steps_S.
    eexists; dands; eauto.
Qed.

Lemma implies_isvalue_abs2bot {o} :
  forall (t : @NTerm o),
    isvalue t
    -> isvalue (abs2bot t).
Proof.
  introv isv.
  destruct isv as [wf cl isc].
  constructor; eauto 4 with slow.
  apply iscan_implies in isc.
  repndors; exrepnd; subst; simpl; auto.
Qed.
Hint Resolve implies_isvalue_abs2bot : slow.

Lemma compute_to_value_abs2bot {o} :
  forall (t : @NTerm o) u,
    wf_term t
    -> computes_to_value [] t u
    -> {w : NTerm
        & computes_to_value [] (abs2bot t) w
        # alpha_eq w (abs2bot u)}.
Proof.
  introv wf comp; allunfold @computes_to_value; repnd.
  pose proof (reduces_to_abs2bot t u wf comp0) as h; exrepnd.
  exists w; dands; auto.
  eapply alpha_preserves_value;[apply alpha_eq_sym;exact h0|].
  eauto 3 with slow.
Qed.

Lemma lblift_as_combine {o} :
  forall R (bs1 bs2 : list (@BTerm o)),
    lblift R bs1 bs2
    <=> (length bs1 = length bs2
         # forall b1 b2,
             LIn (b1,b2) (combine bs1 bs2)
             -> blift R b1 b2).
Proof.
  introv.
  unfold lblift; split; intro h; repnd; dands; auto; introv i.
  - apply (in_nth_combine_iff _ _ default_bt default_bt) in i.
    exrepnd; subst.
    apply h; auto.
  - apply h.
    apply (in_nth_combine_iff _ _ default_bt default_bt).
    eexists; dands; eauto; auto; try omega.
Qed.

Lemma implies_alpha_eq_abs2bot {o} :
  forall (t1 t2 : @NTerm o),
    alpha_eq t1 t2
    -> alpha_eq (abs2bot t1) (abs2bot t2).
Proof.
  introv aeq.
  allrw @abs2bot_as_abs2vbot; eauto 3 with slow.
Qed.
Hint Resolve implies_alpha_eq_abs2bot : slow.

Hint Resolve alpha_eq_bterms_sym : slow.
Hint Resolve alpha_eq_bterms_trans : slow.

Lemma in_combine_trans {T} :
  forall a c (l1 l2 l3 : list T),
    length l1 = length l2
    -> LIn (a, c) (combine l1 l3)
    -> {b : T & LIn (a,b) (combine l1 l2) # LIn (b,c) (combine l2 l3)}.
Proof.
  induction l1; introv len i; allsimpl; tcsp.
  destruct l3 as [|x3 l3]; allsimpl; tcsp.
  destruct l2 as [|x2 l2]; allsimpl; tcsp; cpx.
  repndors; ginv; cpx.
  - exists x2; dands; auto.
  - pose proof (IHl1 l2 l3 len i) as h; clear IHl1; exrepnd.
    exists b; dands; auto.
Qed.

Lemma diff_abs_bot_b_alpha_l {o} :
  forall (b1 b2 b3 : @BTerm o),
    alpha_eq_bterm b1 b2
    -> diff_abs_bot_b_alpha b2 b3
    -> diff_abs_bot_b_alpha b1 b3.
Proof.
  introv aeq diff.
  destruct b1, b2, b3.
  unfold diff_abs_bot_b_alpha in diff; exrepnd.
  exists u1 u2; dands; eauto 3 with slow.
Qed.
Hint Resolve diff_abs_bot_b_alpha_l : slow.

Lemma diff_abs_bot_b_alpha_r {o} :
  forall (b1 b2 b3 : @BTerm o),
    diff_abs_bot_b_alpha b1 b2
    -> alpha_eq_bterm b2 b3
    -> diff_abs_bot_b_alpha b1 b3.
Proof.
  introv diff aeq.
  destruct b1, b2, b3.
  unfold diff_abs_bot_b_alpha in diff; exrepnd.
  exists u1 u2; dands; eauto 3 with slow.
Qed.
Hint Resolve diff_abs_bot_b_alpha_r : slow.

Lemma diff_abs_bot_bs_alpha_l {o} :
  forall bs1 bs2 bs3 : list (@BTerm o),
    alpha_eq_bterms bs1 bs2
    -> diff_abs_bot_bs_alpha bs2 bs3
    -> diff_abs_bot_bs_alpha bs1 bs3.
Proof.
  introv aeq diff.
  unfold alpha_eq_bterms in aeq; repnd.
  allunfold @diff_abs_bot_bs_alpha.
  allunfold @br_bterms.
  allunfold @br_list; repnd.
  dands; auto; try omega.
  introv i.
  apply (in_combine_trans _ _ _ bs2) in i; auto.
  exrepnd.
  apply aeq in i1.
  apply diff in i0.
  eauto 3 with slow.
Qed.
Hint Resolve diff_abs_bot_bs_alpha_l : slow.

Lemma diff_abs_bot_bs_alpha_r {o} :
  forall bs1 bs2 bs3 : list (@BTerm o),
    diff_abs_bot_bs_alpha bs1 bs2
    -> alpha_eq_bterms bs2 bs3
    -> diff_abs_bot_bs_alpha bs1 bs3.
Proof.
  introv diff aeq.
  unfold alpha_eq_bterms in aeq; repnd.
  allunfold @diff_abs_bot_bs_alpha.
  allunfold @br_bterms.
  allunfold @br_list; repnd.
  dands; auto; try omega.
  introv i.
  apply (in_combine_trans _ _ _ bs2) in i; auto.
  exrepnd.
  apply aeq in i0.
  apply diff in i1.
  eauto 3 with slow.
Qed.
Hint Resolve diff_abs_bot_bs_alpha_r : slow.

Lemma diff_abs_bot_alpha_oterm_can_implies {o} :
  forall c (bs : list (@BTerm o)) t,
    diff_abs_bot_alpha (oterm (Can c) bs) t
    -> {bs' : list BTerm
        & t = oterm (Can c) bs'
        # diff_abs_bot_bs_alpha bs bs'}.
Proof.
  introv diff.
  unfold diff_abs_bot_alpha in diff; exrepnd.
  apply alpha_eq_oterm_implies_combine2 in diff0; exrepnd; subst.
  invdiff.
  assert (diff_abs_bot_bterms bs' bs2) as d.
  { unfold diff_abs_bot_bterms, br_bterms, br_list; auto. }
  apply alpha_eq_sym in diff2.
  apply alpha_eq_oterm_implies_combine2 in diff2; exrepnd; subst.
  eexists; dands; eauto 4 with slow.
Qed.

Lemma diff_abs_bot_bs_alpha_implies_eq_len {o} :
  forall (bs1 bs2 : list (@BTerm o)),
    diff_abs_bot_bs_alpha bs1 bs2 -> length bs1 = length bs2.
Proof.
  introv diff.
  unfold diff_abs_bot_bs_alpha, br_bterms, br_list in diff; sp.
Qed.

Lemma diff_abs_bot_b_alpha_implies {o} :
  forall (b1 b2 : @BTerm o),
    diff_abs_bot_b_alpha b1 b2
    -> {l : list NVar
        & {t1 : NTerm
        & {t2 : NTerm
        & alpha_eq_bterm b1 (bterm l t1)
        # alpha_eq_bterm b2 (bterm l t2)
        # diff_abs_bot t1 t2 }}}.
Proof.
  introv diff.
  unfold diff_abs_bot_b_alpha in diff; exrepnd.
  inversion diff1; subst; clear diff1.
  exists l t1 t2; dands; auto.
Qed.

Lemma isprogram_bt_implies_isprog_bt {o} :
  forall (b : @BTerm o),
    isprogram_bt b -> isprog_bt b.
Proof.
  introv isp.
  apply isprogram_bt_eq; auto.
Qed.
Hint Resolve isprogram_bt_implies_isprog_bt : slow.

Lemma isprog_bt_implies_isprogram_bt {o} :
  forall (b : @BTerm o),
    isprog_bt b -> isprogram_bt b.
Proof.
  introv isp.
  apply isprogram_bt_eq; auto.
Qed.
Hint Resolve isprog_bt_implies_isprogram_bt : slow.

Lemma alpha_eq_bterm_preserves_isprog_bt {o} :
  forall (b1 b2 : @BTerm o),
    alpha_eq_bterm b1 b2
    -> isprog_bt b1
    -> isprog_bt b2.
Proof.
  introv aeq isp.
  apply alphaeqbt_preserves_prog_r_eauto in aeq; eauto 3 with slow.
Qed.
Hint Resolve alpha_eq_bterm_preserves_isprog_bt : slow.

Lemma diff_abs_bot_alpha_sterm_implies {o} :
  forall f (t : @NTerm o),
    diff_abs_bot_alpha (sterm f) t
    -> {g : ntseq
        & t = sterm g
        # forall n, diff_abs_bot_alpha (f n) (g n)}.
Proof.
  introv d.
  unfold diff_abs_bot_alpha in d; exrepnd.
  apply alpha_eq_sterm in d0; exrepnd; subst.
  invdiff.
  apply alpha_eq_sym in d2.
  apply alpha_eq_sterm in d2; exrepnd; subst.
  eexists; dands; eauto 4 with slow.
Qed.

Lemma diff_abs_bot_alpha_vterm_implies {o} :
  forall v (t : @NTerm o),
    diff_abs_bot_alpha (vterm v) t
    -> t = vterm v.
Proof.
  introv d.
  unfold diff_abs_bot_alpha in d; exrepnd.
  inversion d0; subst; clear d0.
  invdiff.
  inversion  d2; subst; clear d2.
  auto.
Qed.

Lemma implies_approx_open_sterm {o} :
  forall lib (f g : @ntseq o),
    wf_term (sterm f)
    -> wf_term (sterm g)
    -> (forall n, approx_open lib (f n) (g n))
    -> approx_open lib (sterm f) (sterm g).
Proof.
  introv wf1 wf2 imp.
  apply approx_open_simpler_equiv.
  unfold simpl_olift; dands; eauto 3 with slow.
  introv ps isp1 isp2.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 2 with slow;[]).
  simpl.
  apply implies_approx_sterm; eauto 3 with slow.
  introv.
  apply approx_open_approx; try (apply imp); eauto 3 with slow.
Qed.

Lemma implies_cequiv_open_sterm {o} :
  forall lib (f g : @ntseq o),
    wf_term (sterm f)
    -> wf_term (sterm g)
    -> (forall n, cequiv_open lib (f n) (g n))
    -> cequiv_open lib (sterm f) (sterm g).
Proof.
  introv wf1 wf2 imp.
  apply olift_approx_cequiv; apply implies_approx_open_sterm; auto;
  introv; pose proof (imp n) as h; clear imp; apply olift_cequiv_approx in h; sp.
Qed.

Lemma wf_sterm_implies_wf_app {o} :
  forall (f : @ntseq o) (n : nat),
    wf_term (sterm f) -> wf_term (f n).
Proof.
  introv wf.
  allrw @wf_term_eq.
  eauto 3 with slow.
Qed.
Hint Resolve wf_sterm_implies_wf_app : slow.

Lemma alpha_eq_mk_vid_implies {o} :
  forall v (t : @NTerm o),
    alpha_eq (mk_vid v) t -> {z : NVar & t = mk_vid z}.
Proof.
  introv aeq.
  apply alpha_eq_mk_lam in aeq; exrepnd; subst.
  apply alphaeqbt_1v in aeq1; exrepnd; ginv.
  allrw disjoint_singleton_l.
  allrw in_app_iff; allrw not_over_or; repnd; GC.

  unfold lsubst in aeq0; allsimpl.
  boolvar; allrw disjoint_singleton_r; tcsp.
  inversion aeq0; clear aeq0; subst; GC.
  destruct nt2; allsimpl; ginv; GC.
  allrw not_over_or; repnd; GC.
  boolvar; ginv; tcsp.
  unfold mk_vid, mk_var.
  eexists; eauto.
Qed.

Lemma diff_abs_bot_alpha_oterm_implies {o} :
  forall op (bs : list (@BTerm o)) t,
    diff_abs_bot_alpha (oterm op bs) t
    -> {bs' : list BTerm
        & t = oterm op bs'
        # diff_abs_bot_bs_alpha bs bs'}
       [+]
       {v : NVar
        & {abs : opabs
        & t = mk_vbot v
        # op = Abs abs}}
       [+]
       {v : NVar
        & {abs : opabs
        & {bs' : list BTerm
        & t = oterm (Abs abs) bs'
        # op = NCan NFix
        # bs = [nobnd (mk_vid v)] }}}.
Proof.
  introv diff.
  unfold diff_abs_bot_alpha in diff; exrepnd.
  apply alpha_eq_oterm_implies_combine2 in diff0; exrepnd; subst.
  invdiff.

  - assert (diff_abs_bot_bterms bs' bs2) as d.
    { unfold diff_abs_bot_bterms, br_bterms, br_list; auto. }
    clear imp.
    apply alpha_eq_sym in diff2.
    apply alpha_eq_oterm_implies_combine2 in diff2; exrepnd; subst.
    left; eexists; dands; eauto 4 with slow.

  - apply alpha_eq_sym in diff2; apply alpha_eq_mk_vbot_implies in diff2; exrepnd; subst.
    right; left.
    eexists; eexists; dands; eauto.

  - apply alpha_eq_sym in diff2.
    apply alpha_eq_oterm_implies_combine2 in diff2; exrepnd; subst.
    unfold alpha_eq_bterms in diff3; allsimpl; repnd; cpx.
    allsimpl.
    pose proof (diff3 x (nobnd (mk_vid v))) as h; clear diff3.
    autodimp h hyp.
    apply alpha_eq_bterm_sym in h; apply alpha_eq_bterm_nobnd in h; exrepnd; subst.
    apply alpha_eq_mk_vid_implies in h0; exrepnd; subst.
    right; right.
    eexists; eexists; eexists; dands; eauto.
Qed.

Hint Resolve diff_abs_bot_bs_alpha_implies_eq_len : slow.

Lemma abs_not_hasvalue_like {o} :
  forall lib abs (bs : list (@BTerm o)),
    find_entry lib abs bs = None
    -> !hasvalue_like lib (oterm (Abs abs) bs).
Proof.
  introv f comp.
  unfold hasvalue_like in comp; exrepnd.
  apply reduces_to_split2 in comp1; repndors; subst; tcsp.
  { unfold isvalue_like in comp0; allsimpl; tcsp. }
  exrepnd.
  csunf comp1; allsimpl.
  apply compute_step_lib_success in comp1; exrepnd; subst.
  unfold found_entry in comp3.
  rewrite f in comp3; ginv.
Qed.

(* can be generalized to libraries that are disjoint from the terms *)
Lemma approx_open_nil_diff_abs_bot {o} :
  forall (t u : @NTerm o),
    wf_term t
    -> wf_term u
    -> diff_abs_bot_alpha t u
    -> approx_open [] t u.
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv wf1 wf2 diff.

  - Case "vterm".
    apply diff_abs_bot_alpha_vterm_implies in diff; subst; eauto 3 with slow.

  - Case "sterm".
    apply diff_abs_bot_alpha_sterm_implies in diff; exrepnd; subst.
    apply implies_approx_open_sterm; auto.
    introv.
    apply ind; eauto 3 with slow.

  - Case "oterm".
    apply diff_abs_bot_alpha_oterm_implies in diff.
    repndors; exrepnd; subst; allsimpl; auto.

    + apply approx_open_congruence; eauto 3 with slow.
      apply lblift_as_combine; dands; eauto 3 with slow.
      introv i.
      unfold diff_abs_bot_bs_alpha, br_bterms, br_list in diff0; repnd.
      applydup diff0 in i.

      apply diff_abs_bot_b_alpha_implies in i0; exrepnd.
      exists l t1 t2; dands; auto.

      applydup in_combine in i; repnd.

      destruct b1 as [l1 u1].
      applydup @alpha_eq_bterm_preserves_osize in i0.
      pose proof (ind u1 t1 l1) as h; clear ind.
      repeat (autodimp h hyp);[allrw; eauto 3 with slow|].

      allrw @wf_oterm_iff; repnd.
      applydup wf2 in i3 as w2.
      applydup wf1 in i4 as w1.
      applydup @alpha_eq_bterm_preserves_wf_bterm in i0; auto.
      applydup @alpha_eq_bterm_preserves_wf_bterm in i2; auto.
      allrw @wf_bterm_iff.
      apply h; eauto 3 with slow.

    + apply approx_open_simpler_equiv.
      unfold simpl_olift; dands; eauto 3 with slow.
      introv ps isp1 isp2.
      apply approx_assume_hasvalue; eauto 2 with slow.
      repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[]).
      simpl; autorewrite with slow; fold_terms.
      introv hv.
      apply abs_not_hasvalue_like in hv; tcsp.

    + apply approx_open_simpler_equiv.
      unfold simpl_olift; dands; eauto 3 with slow.
      introv ps isp1 isp2.
      apply approx_assume_hasvalue; eauto 2 with slow.
      repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[]).
      simpl; autorewrite with slow; fold_terms.
      introv hv.
      apply not_hasvalue_like_vbot in hv; tcsp.
Qed.

Lemma approx_nil_diff_abs_bot {o} :
  forall (t u : @NTerm o),
    isprog t
    -> isprog u
    -> diff_abs_bot_alpha t u
    -> approx [] t u.
Proof.
  introv isp1 isp2 diff.
  apply approx_open_nil_diff_abs_bot in diff; eauto 3 with slow.
  apply approx_open_approx; eauto 3 with slow.
Qed.

Lemma diff_abs_bot_abs2bot_r {o} :
  forall (t : @NTerm o),
    diff_abs_bot t (abs2bot t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; auto.
  Case "oterm".
  rewrite abs2bot_op_eq; boolvar; exrepnd; subst;
  constructor; autorewrite with slow in *; auto.
  introv i.
  rewrite combine_map_l in i.
  apply in_map_iff in i; exrepnd; ginv.
  destruct a as [l t]; allsimpl.
  constructor.
  eapply ind; eauto.
Qed.
Hint Resolve diff_abs_bot_abs2bot_r : slow.

Lemma diff_abs_bot_abs2bot_l {o} :
  forall (t : @NTerm o),
    diff_abs_bot (abs2bot t) t.
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv; simpl; auto.
  Case "oterm".
  rewrite abs2bot_op_eq; boolvar; exrepnd; subst;
  constructor; autorewrite with slow in *; auto.
  introv i.
  rewrite combine_map_r in i.
  apply in_map_iff in i; exrepnd; ginv.
  destruct a as [l t]; allsimpl.
  constructor.
  eapply ind; eauto.
Qed.
Hint Resolve diff_abs_bot_abs2bot_l : slow.

Lemma approx_nil_abs2bot_r {o} :
  forall (t : @NTerm o), isprog t -> approx [] t (abs2bot t).
Proof.
  introv isp.
  apply approx_nil_diff_abs_bot; eauto 3 with slow.
Qed.

Lemma approx_nil_abs2bot_l {o} :
  forall (t : @NTerm o), isprog t -> approx [] (abs2bot t) t.
Proof.
  introv isp.
  apply approx_nil_diff_abs_bot; eauto 3 with slow.
Qed.

Lemma cequiv_nil_abs2bot {o} :
  forall (t : @NTerm o), isprog t -> cequiv [] t (abs2bot t).
Proof.
  introv isp.
  split.
  - apply approx_nil_abs2bot_r; auto.
  - apply approx_nil_abs2bot_l; auto.
Qed.

Lemma isotrue_all_abstractions_are_defined_nil_abs2bot {o} :
  forall (t : @NTerm o), isotrue (all_abstractions_are_defined [] (abs2bot t)).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv; allsimpl; auto.
  rewrite abs2bot_op_eq; boolvar; simpl; auto.
  apply isotrue_oband.
  rw isotrue_bool2obool_iff.
  dands.
  - destruct op; simpl; auto.
    destruct n; eexists; eauto.
  - rewrite map_map.
    apply isotrue_oball_map; introv i.
    destruct x as [l t]; simpl.
    unfold compose; simpl.
    eapply ind; eauto 3 with slow.
Qed.

Lemma isprogram_sterm_iff {o} :
  forall (f : @ntseq o),
    isprogram (sterm f) <=> forall n, isprogram (f n) # noutokens (f n).
Proof.
  introv; split; intro h.

  - inversion h as [cl wf]; clear h.
    introv.
    allrw @nt_wf_sterm_iff.
    pose proof (wf n) as h; clear wf; repnd; dands; auto.
    constructor; auto.

  - constructor; tcsp.
    constructor; introv.
    pose proof (h n) as q; clear h; repnd.
    inversion q0.
    dands; auto.
Qed.

Lemma isprog_sterm_iff {o} :
  forall (f : @ntseq o),
    isprog (sterm f) <=> forall n, isprog (f n) # noutokens (f n).
Proof.
  introv; rw @isprog_eq.
  rw @isprogram_sterm_iff.
  split; introv h; introv; pose proof (h n) as q; clear h;
  repnd; dands; eauto 3 with slow.
Qed.

Lemma unfold_entry_op_eq {o} :
  forall entry op (bs : list (@BTerm o)),
    unfold_entry_op entry op bs
    = match dec_op_abs op with
      | inl (existT _ abs _) =>
        match unfold_abs_entry entry abs bs with
        | Some u => u
        | None => oterm op bs
        end
      | _  => oterm op bs
      end.
Proof.
  introv.
  destruct (dec_op_abs op); exrepnd; subst; simpl; auto.
  destruct op; simpl; auto.
  destruct n; eexists; eauto.
Qed.

Lemma matching_entry_implies_matching_bterms {o} :
  forall abs opabs vars (bs : list (@BTerm o)),
    matching_entry abs opabs vars bs
    -> matching_bterms vars bs.
Proof.
  introv m.
  destruct m; tcsp.
Qed.
Hint Resolve matching_entry_implies_matching_bterms : slow.

Lemma correct_abs_implies_get_utokens_so_nil {o} :
  forall opabs vars (t : @SOTerm o),
    correct_abs opabs vars t
    -> get_utokens_so t = [].
Proof.
  introv c.
  destruct c; tcsp.
Qed.

Lemma get_utokens_unfold_entry {o} :
  forall entry (t : @NTerm o),
    subset (get_utokens (unfold_entry entry t)) (get_utokens t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; simpl; auto.
  Case "oterm".
  rewrite unfold_entry_op_eq.
  destruct (dec_op_abs op); exrepnd; subst; simpl.

  - unfold unfold_abs_entry.
    destruct entry.
    boolvar; simpl.

    + eapply subset_trans;[apply get_utokens_mk_instance|]; eauto 3 with slow.
      dup correct as e.
      apply correct_abs_implies_get_utokens_so_nil in e; rewrite e; simpl.

      unfold get_utokens_bs.
      rewrite flat_map_map; unfold compose; simpl.
      apply subset_flat_map2; introv i.
      destruct x as [l t]; simpl.
      eapply ind; eauto.

    + rewrite flat_map_map; unfold compose; simpl.
      apply subset_flat_map2; introv i.
      destruct x as [l t]; simpl.
      eapply ind; eauto.

  - apply subset_app_lr; auto.
    rewrite flat_map_map; unfold compose; simpl.
    apply subset_flat_map2; introv i.
    destruct x as [l t]; simpl.
    eapply ind; eauto.
Qed.

Lemma correct_abs_implies_wf {o} :
  forall opabs vars (rhs : @SOTerm o),
    correct_abs opabs vars rhs
    -> wf_soterm rhs.
Proof.
  introv c; destruct c; tcsp.
Qed.
Hint Resolve correct_abs_implies_wf : slow.

Lemma correct_abs_implies_covered {o} :
  forall opabs vars (rhs : @SOTerm o),
    correct_abs opabs vars rhs
    -> socovered rhs vars.
Proof.
  introv c; destruct c; tcsp.
Qed.
Hint Resolve correct_abs_implies_covered : slow.

Lemma isprogram_mk_instance {o} :
  forall opabs vars rhs (bs : list (@BTerm o)),
    correct_abs opabs vars rhs
    -> matching_bterms vars bs
    -> (forall b, LIn b bs -> isprogram_bt b)
    -> isprogram (mk_instance vars bs rhs).
Proof.
  introv correct m i.
  apply isprogram_sosub; eauto 3 with slow.
  - rw <- @mk_abs_subst_some_prop2; auto.
    eapply correct_abs_implies_covered; eauto.
  - apply sosub_prog_prop1.
    introv k.
    rw @sorange_mk_abs_subst in k; auto.
Qed.

Lemma wf_term_mk_instance {o} :
  forall opabs vars rhs (bs : list (@BTerm o)),
    correct_abs opabs vars rhs
    -> matching_bterms vars bs
    -> (forall b, LIn b bs -> wf_bterm b)
    -> wf_term (mk_instance vars bs rhs).
Proof.
  introv correct m i.
  apply wf_sosub; auto; eauto 3 with slow.
  apply sosub_wf_mk_abs_subst; auto.
Qed.

Lemma free_vars_unfold_entry {o} :
  forall entry (t : @NTerm o),
    subset (free_vars (unfold_entry entry t)) (free_vars t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; simpl; auto.

  Case "oterm".
  rewrite unfold_entry_op_eq.
  destruct (dec_op_abs op); exrepnd; subst; simpl.

  - unfold unfold_abs_entry; destruct entry; simpl.
    boolvar.

    + apply subvars_eq.
      eapply subvars_trans;[apply subvars_free_vars_mk_instance|]; eauto 3 with slow.
      apply subvars_eq.
      rewrite flat_map_map; unfold compose.
      apply subset_flat_map2; introv i.
      destruct x as [l t]; simpl.
      applydup ind in i.
      introv j.
      allrw in_remove_nvars; repnd; dands; auto.

    + simpl.
      rewrite flat_map_map; unfold compose.
      apply subset_flat_map2; introv i.
      destruct x as [l t]; simpl.
      applydup ind in i.
      introv j.
      allrw in_remove_nvars; repnd; dands; auto.

  - rewrite flat_map_map; unfold compose.
    apply subset_flat_map2; introv i.
    destruct x as [l t]; simpl.
    applydup ind in i.
    introv j.
    allrw in_remove_nvars; repnd; dands; auto.
Qed.

Lemma wf_unfold_entry {o} :
  forall entry (t : @NTerm o),
    wf_term t
    -> wf_term (unfold_entry entry t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv wf; simpl; auto.

  - Case "sterm".
    allrw @wf_sterm_iff; introv.
    pose proof (wf n) as h; clear wf; repnd.
    pose proof (ind n) as q; clear ind.
    allrw @isprog_nout_iff; repnd.
    autodimp q hyp; eauto 3 with slow.
    dands; eauto 3 with slow.

    + pose proof (free_vars_unfold_entry entry (f n)) as s.
      rewrite h1 in s.
      apply subset_nil_implies_nil in s; auto.

    + pose proof (get_utokens_unfold_entry entry (f n)) as s.
      rewrite h in s.
      apply subset_nil_implies_nil in s; auto.

  - Case "oterm".
    rewrite unfold_entry_op_eq.
    destruct (dec_op_abs op); exrepnd; subst; simpl.

    + unfold unfold_abs_entry; destruct entry; simpl.
      boolvar.

      * eapply wf_term_mk_instance; eauto 3 with slow.
        introv i.
        apply in_map_iff in i; exrepnd; subst.
        apply wf_oterm_iff in wf; repnd.
        applydup wf in i1.
        destruct a as [l t]; allsimpl.
        allrw @wf_bterm_iff.
        eapply ind; eauto.

      * allrw @wf_oterm_iff; repnd.
        rewrite <- wf0.
        rewrite map_map; unfold compose; simpl.
        dands.

        {
          apply eq_maps; introv i.
          destruct x; unfold num_bvars; simpl; auto.
        }

        {
          introv i.
          apply in_map_iff in i; exrepnd; subst.
          destruct a as [l t]; allsimpl.
          applydup wf in i1.
          allrw @wf_bterm_iff.
          eapply ind; eauto.
        }

    + allrw @wf_oterm_iff; repnd.
      rewrite <- wf0.
      rewrite map_map; unfold compose; simpl.
      dands.

      {
        apply eq_maps; introv i.
        destruct x; unfold num_bvars; simpl; auto.
      }

      {
        introv i.
        apply in_map_iff in i; exrepnd; subst.
        destruct a as [l t]; allsimpl.
        applydup wf in i1.
        allrw @wf_bterm_iff.
        eapply ind; eauto.
      }
Qed.
Hint Resolve wf_unfold_entry : slow.

Lemma implies_isprog_unfold_entry {o} :
  forall entry (t : @NTerm o),
    isprog t
    -> isprog (unfold_entry entry t).
Proof.
  introv isp.
  allrw @isprog_eq.
  inversion isp as [cl wf]; clear isp.
  constructor; allrw @nt_wf_eq; try (apply wf_unfold_entry); auto.
  pose proof (free_vars_unfold_entry entry t) as s.
  rewrite cl in s.
  apply subset_nil_implies_nil in s; auto.
Qed.
Hint Resolve implies_isprog_unfold_entry : slow.

Lemma implies_isprog_nout_unfold_entry {o} :
  forall entry (t : @NTerm o),
    isprog_nout t
    -> isprog_nout (unfold_entry entry t).
Proof.
  introv isp.
  allrw @isprog_nout_iff; repnd.
  allrw @nt_wf_eq; dands; eauto 2 with slow.
  - pose proof (free_vars_unfold_entry entry t) as s.
    rewrite isp1 in s.
    apply subset_nil_implies_nil in s; auto.
  - pose proof (get_utokens_unfold_entry entry t) as s.
    rewrite isp in s.
    apply subset_nil_implies_nil in s; auto.
Qed.
Hint Resolve implies_isprog_nout_unfold_entry : slow.

Lemma isotrue_all_abs_are_defined_abs2bot {o} :
  forall lib (t : @NTerm o),
    isotrue (all_abstractions_are_defined lib (abs2bot t)).
Proof.
  nterm_ind1s t as [v|f ind|op bs ind] Case; introv; allsimpl; auto;[].

  Case "oterm".
  rewrite abs2bot_op_eq.
  boolvar; exrepnd; subst; simpl; auto;[].
  apply isotrue_oband.
  rw @isotrue_bool2obool_iff.
  dands; auto.

  {
    destruct op; simpl; auto.
    destruct n; eexists; eauto.
  }

  apply isotrue_oball_map.
  introv i.
  apply in_map_iff in i; exrepnd; subst.
  destruct a as [l t]; allsimpl.
  eapply ind; eauto 3 with slow.
Qed.
Hint Resolve isotrue_all_abs_are_defined_abs2bot : slow.

Hint Resolve olift_approx_cequiv : slow.

Lemma le_bin_rel_cequiv_open_approx_open {o} :
  forall (lib : @library o), le_bin_rel (cequiv_open lib) (approx_open lib).
Proof.
  introv h.
  apply olift_cequiv_approx in h; sp.
Qed.
Hint Resolve le_bin_rel_cequiv_open_approx_open : slow.

Lemma olift_symm {o} :
  forall (R : bin_rel (@NTerm o)),
    symm_rel R
    -> respects_alpha R
    -> symm_rel (olift R).
Proof.
  introv sym resp h.
  apply olift_iff_oliftp in h; auto.
  apply olift_iff_oliftp; auto.
  allunfold @oliftp; repnd; dands; auto.
Qed.
Hint Resolve olift_symm : slow.

Lemma symm_blift {o} :
  forall (R : bin_rel (@NTerm o)),
    symm_rel R
    -> respects_alpha R
    -> symm_rel (blift R).
Proof.
  introv sym resp h.
  allunfold @blift; exrepnd.
  eexists; eexists; eexists; eauto.
Qed.
Hint Resolve symm_blift : slow.

Lemma sym_lblift {o} :
  forall (R : bin_rel (@NTerm o)),
    symm_rel R
    -> respects_alpha R
    -> symm_rel (lblift R).
Proof.
  introv sym res h.
  allrw @lblift_as_combine; repnd; dands; auto.
  introv i.
  applydup @in_combine_swap in i; auto.
  apply h in i0; auto.
  apply symm_blift; auto.
Qed.
Hint Resolve sym_lblift : slow.

Lemma cequiv_open_sym {o} :
   forall lib (t1 t2 : (@NTerm o)),
     cequiv_open lib t1 t2
     -> cequiv_open lib t2 t1.
Proof.
  introv e.
  apply olift_symm; eauto 3 with slow;
  try (apply respects_alpha_cequiv).
  introv h; apply cequiv_sym; auto.
Qed.
Hint Resolve cequiv_open_sym : slow.

Lemma symm_rel_cequiv_open {o} :
  forall (lib : @library o), symm_rel (cequiv_open lib).
Proof.
  introv h; eauto 3 with slow.
Qed.
Hint Resolve symm_rel_cequiv_open : slow.

Lemma respects_alpha_cequiv_open {o} :
  forall (lib : @library o), respects_alpha (cequiv_open lib).
Proof.
  introv.
  split; introv aeq ceq; eauto 3 with slow.
Qed.
Hint Resolve respects_alpha_cequiv_open : slow.

Lemma cequiv_open_congruence {o} :
  forall lib op (bs1 bs2 : list (@BTerm o)),
    lblift (cequiv_open lib) bs1 bs2
    -> nt_wf (oterm op bs1)
    -> nt_wf (oterm op bs2)
    -> cequiv_open lib (oterm op bs1) (oterm op bs2).
Proof.
  introv h wf1 wf2.
  apply olift_approx_cequiv; apply approx_open_congruence; eauto 3 with slow;
  apply (le_lblift (cequiv_open lib) (approx_open lib)); eauto 3 with slow.
  apply sym_lblift; eauto 3 with slow.
Qed.

Lemma cequiv_open_unfold_entry {o} :
  forall entry lib (t : @NTerm o),
    wf_term t
    -> cequiv_open (entry :: lib) t (unfold_entry entry t).
Proof.
  nterm_ind t as [v|f ind|op bs ind] Case; introv wf; simpl; eauto 3 with slow.

  - Case "sterm".
    apply implies_cequiv_open_sterm; eauto 3 with slow.
    allrw @wf_sterm_iff; introv; eauto 3 with slow.

  - Case "oterm".
    rewrite unfold_entry_op_eq.
    destruct (dec_op_abs op) as [d|d]; exrepd; subst; allsimpl.

    + destruct entry; simpl; boolvar.

      * apply (cequiv_open_trans _ _ (oterm (Abs abs) (map (unfold_entry_bterm (lib_abs opabs vars rhs correct)) bs)));
        [|apply reduces_to_implies_cequiv_open;eauto 3 with slow].

        {
          apply cequiv_open_congruence; eauto 2 with slow.

          - apply lblift_as_combine.
            allrw map_length; dands; auto.
            introv i.
            rewrite combine_map_l in i.
            apply in_map_iff in i; exrepnd; ginv.
            destruct a as [l t]; allsimpl.
            exists l t (unfold_entry (lib_abs opabs vars rhs correct) t); dands; eauto 3 with slow.
            eapply ind; eauto.

            allrw @wf_oterm_iff; repnd.
            applydup wf in i1 as w1.
            allrw @wf_bterm_iff; auto.

          - allrw @nt_wf_eq.
            allrw @wf_oterm_iff; repnd.
            rewrite <- wf0.
            dands.

            + rewrite map_map; unfold compose, num_bvars.
              apply eq_maps; introv i.
              destruct x; simpl; auto.

            + introv i.
              apply in_map_iff in i; exrepnd; subst.
              apply wf in i1.
              destruct a as [l t]; simpl.
              allrw @wf_bterm_iff; eauto 3 with slow.
        }

        {
          allrw @nt_wf_eq.
          allrw @wf_oterm_iff; repnd.
          rewrite <- wf0.
          dands.

          + rewrite map_map; unfold compose, num_bvars.
            apply eq_maps; introv i.
            destruct x; simpl; auto.

          + introv i.
            apply in_map_iff in i; exrepnd; subst.
            apply wf in i1.
            destruct a as [l t]; simpl.
            allrw @wf_bterm_iff; eauto 3 with slow.
        }

        {
          eapply wf_term_mk_instance; eauto 3 with slow.
          introv i.
          apply in_map_iff in i; exrepnd; subst.
          allrw @wf_oterm_iff; repnd.
          apply wf in i1.
          destruct a as [l t]; simpl.
          allrw @wf_bterm_iff; eauto 3 with slow.
        }

        {
          apply reduces_to_if_step; csunf; simpl.
          eapply found_entry_implies_compute_step_lib_success.
          unfold found_entry; simpl; boolvar; tcsp.
          apply @not_matching_entry_iff in m; tcsp.
        }

      * apply cequiv_open_congruence; eauto 2 with slow.

        {
          apply lblift_as_combine.
          allrw map_length; dands; auto.
          introv i.
          rewrite combine_map_l in i.
          apply in_map_iff in i; exrepnd; ginv.
          destruct a as [l t]; allsimpl.
          exists l t (unfold_entry (lib_abs opabs vars rhs correct) t); dands; eauto 3 with slow.
          eapply ind; eauto.

          allrw @wf_oterm_iff; repnd.
          applydup wf in i1 as w1.
          allrw @wf_bterm_iff; auto.
        }

        {
          allrw @nt_wf_eq.
          allrw @wf_oterm_iff; repnd.
          rewrite <- wf0.
          dands.

          - rewrite map_map; unfold compose, num_bvars.
            apply eq_maps; introv i.
            destruct x; simpl; auto.

          - introv i.
            apply in_map_iff in i; exrepnd; subst.
            apply wf in i1.
            destruct a as [l t]; simpl.
            allrw @wf_bterm_iff; eauto 3 with slow.
        }

    + apply cequiv_open_congruence; eauto 2 with slow.

      {
        apply lblift_as_combine.
        allrw map_length; dands; auto.
        introv i.
        rewrite combine_map_l in i.
        apply in_map_iff in i; exrepnd; ginv.
        destruct a as [l t]; allsimpl.
        exists l t (unfold_entry entry t); dands; eauto 3 with slow.
        eapply ind; eauto.

        allrw @wf_oterm_iff; repnd.
        applydup wf in i1 as w1.
        allrw @wf_bterm_iff; auto.
      }

      {
        allrw @nt_wf_eq.
        allrw @wf_oterm_iff; repnd.
        rewrite <- wf0.
        dands.

        - rewrite map_map; unfold compose, num_bvars.
          apply eq_maps; introv i.
          destruct x; simpl; auto.

        - introv i.
          apply in_map_iff in i; exrepnd; subst.
          apply wf in i1.
          destruct a as [l t]; simpl.
          allrw @wf_bterm_iff; eauto 3 with slow.
      }
Qed.

Lemma cequiv_unfold_entry {o} :
  forall entry lib (t : @NTerm o),
    isprog t
    -> cequiv (entry :: lib) t (unfold_entry entry t).
Proof.
  introv isp.
  apply cequiv_open_cequiv; eauto 3 with slow.
  apply cequiv_open_unfold_entry; eauto 3 with slow.
Qed.

Lemma unfold_library_vterm {o} :
  forall (lib : @library o) v,
    unfold_library lib (vterm v) = vterm v.
Proof.
  induction lib; introv; simpl; auto.
Qed.

Lemma unfold_lib_vterm {o} :
  forall (lib : @library o) v,
    unfold_lib lib (vterm v) = vterm v.
Proof.
  introv.
  unfold unfold_lib in *.
  rewrite unfold_library_vterm; simpl; auto.
Qed.

Lemma unfold_library_sterm {o} :
  forall lib (f : @ntseq o),
    unfold_library lib (sterm f)
    = sterm (fun n => unfold_library lib (f n)).
Proof.
  induction lib; simpl; introv; auto.
Qed.

Lemma unfold_lib_sterm {o} :
  forall lib (f : @ntseq o),
    unfold_lib lib (sterm f)
    = sterm (fun n => unfold_lib lib (f n)).
Proof.
  introv.
  unfold unfold_lib in *.
  rewrite unfold_library_sterm; simpl; auto.
Qed.

Definition unfold_library_bterm {o} lib (b : @BTerm o) :=
  match b with
  | bterm l t => bterm l (unfold_library lib t)
  end.

Definition unfold_library_bterms {o} lib (bs : list (@BTerm o)) :=
  map (unfold_library_bterm lib) bs.

Lemma unfold_library_bterm_nil_lib {o} :
  forall (bs : list (@BTerm o)),
    unfold_library_bterms [] bs = bs.
Proof.
  introv; unfold unfold_library_bterms.
  apply eq_map_l; introv i.
  destruct x as [l t]; simpl; auto.
Qed.
Hint Rewrite @unfold_library_bterm_nil_lib : slow.

Lemma unfold_library_bterms_cons_lib {o} :
  forall e lib (bs : list (@BTerm o)),
    unfold_library_bterms (e :: lib) bs
    = unfold_library_bterms lib (map (unfold_entry_bterm e) bs).
Proof.
  introv.
  unfold unfold_library_bterms.
  rewrite map_map; unfold compose.
  apply eq_maps; introv i.
  destruct x as [l t]; simpl; auto.
Qed.
Hint Rewrite @unfold_library_bterms_cons_lib : slow.

Lemma wf_unfold_library {o} :
  forall lib (t : @NTerm o),
    wf_term t
    -> wf_term (unfold_library lib t).
Proof.
  induction lib; introv wf; simpl; auto.
  apply IHlib; eauto 3 with slow.
Qed.
Hint Resolve wf_unfold_library : slow.

Lemma wf_abs2bot {o} :
  forall (t : @NTerm o), wf_term t -> wf_term (abs2bot t).
Proof.
  introv wf.
  pose proof (implies_props_abs2bot t) as h; repnd.
  allrw @wf_term_eq; auto.
Qed.
Hint Resolve wf_abs2bot : slow.

Lemma wf_unfold_lib {o} :
  forall lib (t : @NTerm o),
    wf_term t
    -> wf_term (unfold_lib lib t).
Proof.
  introv wf; unfold unfold_lib.
  eauto 3 with slow.
Qed.
Hint Resolve wf_unfold_lib : slow.

(*
Definition unf_oterm {o} (lib : library) op (bs : list (@BTerm o)) : NTerm :=
  match unfold lib (oterm op bs) with
  | Some t => t
  | None => oterm op bs
  end.

Fixpoint unf_term {o} (lib : library) (t : @NTerm o) : NTerm :=
  match t with
  | vterm v => vterm v
  | sterm f => sterm (fun n => unf_term lib (f n))
  | oterm op bs => unf_oterm lib op (map (unf_bterm lib) bs)
  end
with unf_bterm {o} (lib : library) (b : @BTerm o) : BTerm :=
       match b with
       | bterm vs t => bterm vs (unf_term lib t)
       end.

Definition unf_sooterm {o} (lib : library) op (bs : list (@SOBTerm o)) : SOTerm :=
  match unfold lib (oterm op bs) with
  | Some t => t
  | None => oterm op bs
  end.

Fixpoint unf_soterm {o} (lib : library) (t : @SOTerm o) : SOTerm :=
  match t with
  | sovar v ts => sovar v (map (unf_soterm lib) ts)
  | soseq f => soseq (fun n => unf_term lib (f n))
  | soterm op bs => unfold_entry_op lib op (map (unf_sobterm lib) bs)
  end
with unf_sobterm {o} (lib : library) (b : @SOBTerm o) : SOBTerm :=
       match b with
       | sobterm vs t => sobterm vs (unf_soterm lib t)
       end.

Definition unf_entry {o} lib (e : @library_entry) : library_entry :=
  match e with
  | lib_abs opabs vars rhs correct =>
    lib_abs opabs vars (unf_soterm lib rhs) correct
  end.

Fixpoint unf_lib {o} (lib : @library o) : library :=
  match lib with
  | [] => []
  | entry :: entries => unf_entry (unf_lib entries) entry
  end
 *)

Definition reduces_to_al {o} lib (t1 t2 : @NTerm o) :=
  {t : NTerm & reduces_to lib t1 t # alpha_eq t t2}.

Lemma reduces_to_al_refl {o} :
  forall lib (t : @NTerm o), reduces_to_al lib t t.
Proof.
  introv.
  exists t; dands; eauto 3 with slow.
Qed.
Hint Resolve reduces_to_al_refl : slow.

Lemma reduces_to_al_if_split2 {o} :
  forall lib (t u v : @NTerm o),
    compute_step lib t = csuccess u
    -> reduces_to_al lib u v
    -> reduces_to_al lib t v.
Proof.
  introv comp r.
  allunfold @reduces_to_al; exrepnd.
  exists t0; dands; auto.
  eapply reduces_to_if_split2; eauto.
Qed.

Lemma reduces_to_al_implies_cequiv_open {o} :
  forall lib (t x : @NTerm o),
    wf_term t
    -> wf_term x
    -> reduces_to_al lib t x
    -> cequiv_open lib t x.
Proof.
  introv w1 w2 r.
  unfold reduces_to_al in r; exrepnd.
  eapply olift_cequiv_rw_r_eauto;[exact r0|].
  eapply reduces_to_implies_cequiv_open; eauto 3 with slow.
Qed.

Lemma disjoint_bound_vars_prop4 {o} :
  forall (sub : @SOSub o) v vs t ts,
    disjoint (bound_vars_sosub sub) (free_vars_sosub sub)
    -> disjoint (bound_vars_sosub sub) (flat_map all_fo_vars ts)
    -> LIn (v, sosk vs t) sub
    -> disjoint (bound_vars t) (flat_map (fun x => free_vars (sosub_aux sub x)) ts).
Proof.
  introv disj1 disj2 insub cov.
  eapply disjoint_bound_vars_prop1; eauto;
  eapply subvars_disjoint_l;[|eauto|idtac|eauto];
  apply subvars_bound_vars_in_sosub_bound_vars_sosub.
Qed.

Lemma implies_alphaeq_sub_range_combine {o} :
  forall l1 l2 (ts1 ts2 : list (@NTerm o)),
    length l1 = length l2
    -> length l1 = length ts1
    -> length l2 = length ts2
    -> (forall t1 t2, LIn (t1, t2) (combine ts1 ts2) -> alpha_eq t1 t2)
    -> alphaeq_sub_range (combine l1 ts1) (combine l2 ts2).
Proof.
  induction l1; simpl; introv len1 len2 len3 imp; cpx.
  destruct l2; allsimpl; cpx.
  destruct ts1; allsimpl; cpx.
  destruct ts2; allsimpl; cpx.
  constructor; auto.
  apply alphaeq_eq.
  apply imp; auto.
Qed.
