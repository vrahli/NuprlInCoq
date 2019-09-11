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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export rules_isect.


(* simple terms --- without choice sequences *)
Inductive Term {o} :=
| vTerm: NVar -> Term
| oTerm: @Opid o -> list Bterm -> Term
with Bterm {o} :=
| bTerm: (list NVar) -> Term -> Bterm.

Fixpoint Term2NTerm {o} (t : @Term o) : NTerm :=
  match t with
  | vTerm v => vterm v
  | oTerm op bs => oterm op (map Bterm2BTerm bs)
  end
with Bterm2BTerm {o} (b : Bterm) : BTerm :=
  match b with
  | bTerm l t => bterm l (Term2NTerm t)
  end.
Coercion Term2NTerm : Term >-> NTerm.
Coercion Bterm2BTerm : Bterm >-> BTerm.

Definition mk__axiom {p} : @Term p := oTerm (Can NAxiom) [].

Fixpoint NTerm2Term {o} (t : @NTerm o) : Term :=
  match t with
  | vterm v => vTerm v
  | sterm _ => mk__axiom
  | oterm op bs => oTerm op (map BTerm2Bterm bs)
  end
with BTerm2Bterm {o} (b : BTerm) : Bterm :=
  match b with
  | bterm l t => bTerm l (NTerm2Term t)
  end.
Coercion NTerm2Term : NTerm >-> Term.
Coercion BTerm2Bterm : BTerm >-> Bterm.

Coercion BTerms2Bterms {o} (bs : list (@BTerm o)) : list Bterm :=
  map BTerm2Bterm bs.

Coercion Bterms2BTerms {o} (bs : list (@Bterm o)) : list BTerm :=
  map Bterm2BTerm bs.

Fixpoint size {p} (t : @Term p) : nat :=
  match t with
  | vTerm _ => 1
  | oTerm op bterms => S (addl (map size_bterm bterms))
  end
 with size_bterm {p} (bt: Bterm) :=
  match bt with
  | bTerm lv nt => size nt
  end.

Lemma size_subterm2 {p} :
  forall (o : @Opid p) (lb : list Bterm) (b : Bterm) ,
    LIn b lb
    -> size_bterm b <  size (oTerm o lb).
Proof.
  simpl. induction lb; intros ? Hin; inverts Hin as; simpl.
  - unfold lt. apply le_n_S.
    apply le_plus_l.
  - intros Hin. apply IHlb in Hin. clear IHlb.
    eapply lt_le_trans; eauto.
    apply le_n_S. apply le_plus_r.
Defined.

Lemma size_subterm3 {p} :
  forall (o : @Opid p) (lb : list Bterm) (nt : Term) (lv : list NVar) ,
    LIn (bTerm lv nt) lb
    -> size nt <  size (oTerm o lb).
Proof.
 introv X.
 apply (@size_subterm2 p) with (o:=o) in X; auto.
Defined.

Lemma Term_better_ind2 {p} :
  forall P : (@Term p) -> Type,
    (forall n : NVar, P (vTerm n))
    -> (forall (o : Opid) (lbt : list Bterm),
          (forall (nt nt': Term) (lv: list NVar),
             (LIn (bTerm lv nt) lbt)
              -> size nt' <= size nt
              -> P nt'
          )
          -> P (oTerm o lbt)
       )
    -> forall t : Term, P t.
Proof.
 intros P Hvar Hbt.

 assert (forall n (t : Term), (size t) = n -> P t) as Hass;
   [|introv; apply Hass with (n := size t);auto].

 induction n as [n Hind] using comp_ind_type.
 intros t Hsz.
 destruct t as [v|op bs]; auto.

 apply Hbt; clear Hbt.
 introv Hin Hs; allsimpl.
 apply (Hind (size nt')); auto; clear Hind.
 subst.
 eapply le_trans;[|apply (size_subterm3 op bs nt lv Hin)].
 omega.
Defined.

Lemma Term_better_ind {p} :
  forall P : @Term p -> Type,
    (forall n : NVar, P (vTerm n))
    -> (forall (o : Opid) (lbt : list Bterm),
          (forall (nt : Term) (lv: list NVar),
             (LIn (bTerm lv nt) lbt) -> P nt
          )
          -> P (oTerm o lbt)
       )
    -> forall t : Term, P t.
Proof.
 introv Hv Hind.
 apply Term_better_ind2; auto.
 introv Hx.
 apply Hind.
 introv Hin.
 eapply Hx in Hin; eauto.
Defined.

Tactic Notation "term_ind" ident(h) ident(c) :=
  induction h using Term_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "term_ind" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using Term_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "term_ind1" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using Term_better_ind;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Tactic Notation "term_ind1s" ident(h) "as" simple_intropattern(I)  ident(c) :=
  induction h as I using Term_better_ind2;
  [ Case_aux c "vterm"
  | Case_aux c "oterm"
  ].

Lemma NTerm2Term_Term2NTerm {o} :
  forall (t : @Term o),
    NTerm2Term (Term2NTerm t) = t.
Proof.
  term_ind t as [v|op bs ind] Case; simpl; auto.
  f_equal.
  allrw map_map; unfold compose.
  apply eq_map_l; introv i; auto.
  destruct x; simpl; f_equal.
  eapply ind; eauto.
Qed.
Hint Rewrite @NTerm2Term_Term2NTerm : slow.

Definition no_bnd {o} (t : @Term o) := bTerm [] t.

Definition mk__equality {o} (t1 t2 T : @Term o) : Term :=
  oTerm (Can NEquality) [no_bnd t1, no_bnd t2, no_bnd T].

Definition mk__isect {o} (T1 : @Term o) (v : NVar) (T2 : Term) :=
  oTerm (Can NIsect) [no_bnd T1, bTerm [v] T2].

Definition mk__uni {o} n : @Term o := oTerm (Can (NUni n)) [].

Inductive pre_conclusion {o} :=
| pre_concl_ext : forall (ctype : @Term o), pre_conclusion
| pre_concl_typ : forall (ctype : @Term o), pre_conclusion.

Definition mk_pre_concl {o} (t : @Term o) : pre_conclusion :=
  pre_concl_ext t.

Definition mk_pre_concleq {o} (t1 t2 T : @Term o) : pre_conclusion :=
  mk_pre_concl (mk__equality t1 t2 T).

Record pre_baresequent {p} :=
  MkPreBaresequent
    {
      pre_hyps  : @barehypotheses p;
      pre_concl : @pre_conclusion p
    }.

Definition mk_pre_bseq {o} H (c : @pre_conclusion o) : pre_baresequent :=
  MkPreBaresequent o H c.

Definition pre_rule_isect_equality_concl {o} a1 a2 x1 x2 b1 b2 i (H : @bhyps o) :=
  mk_pre_bseq
    H
    (mk_pre_concleq
       (mk__isect a1 x1 b1)
       (mk__isect a2 x2 b2)
       (mk__uni i)).

Definition pre_rule_isect_equality_hyp1 {o} a1 a2 i (H : @bhyps o) :=
  mk_pre_bseq H (mk_pre_concleq a1 a2 (mk__uni i)).

Definition pre_rule_isect_equality_hyp2 {o} a1 b1 b2 x1 x2 y i (H : @bhyps o) :=
  mk_pre_bseq
    (snoc H (mk_hyp y a1))
    (mk_pre_concleq
       (subst b1 x1 (mk_var y))
       (subst b2 x2 (mk_var y))
       (mk_uni i)).

Definition NVin v (vs : list NVar) := memvar v vs = false.

(* A pre-proof is a proof without the extracts, which we can build a posteriori *)
Inductive pre_proof {o} (hole : bool) : @pre_baresequent o -> Type :=
(*| pre_proof_from_lib :
    forall c,
      LIn c (@PC_conclusions o ctxt)
      -> pre_proof hole ctxt (concl2pre_baresequent c)*)
| pre_proof_hole : forall s, hole = true -> pre_proof hole s
| pre_proof_isect_eq :
    forall a1 a2 b1 b2 x1 x2 y i H,
      NVin y (vars_hyps H)
      -> pre_proof hole (pre_rule_isect_equality_hyp1 a1 a2 i H)
      -> pre_proof hole (pre_rule_isect_equality_hyp2 a1 b1 b2 x1 x2 y i H)
      -> pre_proof hole (pre_rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H).
(*
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
 *)

Record SP_hypothesis {o} :=
  {
    SP_hvar   : NVar;
    SP_hidden : bool;
    SP_htyp   : @Term o;
    SP_lvl    : lvlop
  }.

Definition SP_hypothesis2hypothesis {o} (b : @SP_hypothesis o) : hypothesis :=
  {|
    hvar   := SP_hvar b;
    hidden := SP_hidden b;
    htyp   := SP_htyp b;
    lvl    := SP_lvl b
  |}.
Coercion SP_hypothesis2hypothesis : SP_hypothesis >-> hypothesis.

Definition hypothesis2SP_hypothesis {o} (b : @hypothesis o) : SP_hypothesis :=
  {|
    SP_hvar   := hvar b;
    SP_hidden := hidden b;
    SP_htyp   := htyp b;
    SP_lvl    := lvl b
  |}.
Coercion hypothesis2SP_hypothesis : hypothesis >-> SP_hypothesis.

Definition mk__hyp {p} v t : @SP_hypothesis p :=
  {|
    SP_hvar   := v;
    SP_hidden := false;
    SP_htyp   := t;
    SP_lvl    := nolvl
  |}.

Definition SP_barehypotheses {p} := list (@SP_hypothesis p).
Definition SP_bhyps {p} := @SP_barehypotheses p.

Coercion SP_barehypotheses2barehypotheses {o} (H : @SP_barehypotheses o) : barehypotheses :=
  map SP_hypothesis2hypothesis H.

Coercion SP_barehypotheses2bhyps {o} (H : @SP_barehypotheses o) : bhyps :=
  map SP_hypothesis2hypothesis H.

Coercion barehypotheses2SP_barehypotheses {o} (H : @barehypotheses o) : SP_barehypotheses :=
  map hypothesis2SP_hypothesis H.

Lemma hypothesis2SP_hypothesis_SP_hypothesis2hypothesis {o} :
  forall (h : @SP_hypothesis o),
    hypothesis2SP_hypothesis (SP_hypothesis2hypothesis h) = h.
Proof.
  introv.
  unfold hypothesis2SP_hypothesis, SP_hypothesis2hypothesis; simpl.
  destruct h; simpl; f_equal.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @hypothesis2SP_hypothesis_SP_hypothesis2hypothesis : slow.

Lemma barehypotheses2SP_barehypotheses_SP_barehypotheses2bhyps {o} :
  forall (H : @SP_barehypotheses o),
    barehypotheses2SP_barehypotheses (SP_barehypotheses2bhyps H) = H.
Proof.
  introv.
  unfold barehypotheses2SP_barehypotheses, SP_barehypotheses2bhyps.
  allrw map_map; unfold compose.
  apply eq_map_l.
  introv i.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @barehypotheses2SP_barehypotheses_SP_barehypotheses2bhyps : slow.

Inductive SP_conclusion {o} :=
| SP_concl_ext : forall (ctype : @Term o) (extract : @Term o), SP_conclusion
| SP_concl_typ : forall (ctype : @Term o), SP_conclusion.

Coercion SP_conclusion2conclusion {o} (c : @SP_conclusion o) : conclusion :=
  match c with
  | SP_concl_ext t e => concl_ext t e
  | SP_concl_typ t => concl_typ t
  end.

Coercion conclusion2SP_conclusion {o} (c : @conclusion o) : SP_conclusion :=
  match c with
  | concl_ext t e => SP_concl_ext t e
  | concl_typ t => SP_concl_typ t
  end.

Record SP_baresequent {o} :=
  mk__baresequent
    {
      SP_hyps  : @SP_barehypotheses o;
      SP_concl : @SP_conclusion o
    }.

Coercion SP_baresequent2baresequent {o} (b : @SP_baresequent o) : baresequent :=
  mk_baresequent (SP_hyps b) (SP_concl b).

Coercion baresequent2SP_baresequent {o} (b : @baresequent o) : SP_baresequent :=
  mk__baresequent o (hyps b) (concl b).

Hint Rewrite @lsubst_aux_nil : slow.

Lemma Term2NTerm_NTerm2Term_lsubst_aux_Term2NTerm_var_ren {o} :
  forall (t : @Term o) s,
    allvars_sub s
    -> Term2NTerm (NTerm2Term (lsubst_aux (Term2NTerm t) s))
       = lsubst_aux (Term2NTerm t) s.
Proof.
  term_ind t as [z|op bs ind] Case; introv allv; simpl; boolvar; simpl; auto.

  - Case "vterm".
    remember (sub_find s z) as sf; destruct sf; simpl; auto.
    symmetry in Heqsf; apply sub_find_allvars in Heqsf; auto.
    exrepnd; subst; simpl; auto.

  - f_equal.
    allrw map_map; unfold compose; simpl.
    apply eq_maps; introv i; destruct x as [l t]; simpl; f_equal; boolvar; simpl;
      autorewrite with slow; auto;[].
    eapply ind; eauto 3 with slow.
Qed.

Lemma change_bvars_alpha_Term2NTerm_eq {o} :
  forall vs (t : @Term o),
    {u : Term
     & change_bvars_alpha vs (Term2NTerm t)
       = Term2NTerm u # disjoint vs (bound_vars u)}.
Proof.
  term_ind1s t as [v|op bs ind] Case; simpl; introv.

  - exists (@vTerm o v); simpl; auto.

  - assert {bs' : list Bterm
            & map (change_bvars_alphabt vs) (map Bterm2BTerm bs)
              = map Bterm2BTerm bs'
            /\ disjoint (flat_map bound_vars_bterm (Bterms2BTerms bs')) vs} as h.
    {
      induction bs; simpl.
      - exists ([] : list (@Bterm o)); simpl; auto.
      - repeat (autodimp IHbs hyp).
        { introv i; introv; eapply ind; simpl; eauto. }
        exrepnd.
        rewrite IHbs1.
        destruct a as [l t].
        simpl in *.

        pose proof (ind t t l) as h; clear ind.
        repeat (autodimp h hyp); exrepnd.
        rewrite h1.

        exists ((bTerm (fresh_distinct_vars (length l) (vs ++ all_vars u))
                       (lsubst_aux u (var_ren l (fresh_distinct_vars (length l) (vs ++ all_vars u)))))
                  :: bs').
        simpl.
        dands; auto.

        + f_equal.
          f_equal.
          rewrite Term2NTerm_NTerm2Term_lsubst_aux_Term2NTerm_var_ren; eauto 3 with slow.

        + repeat (rw disjoint_app_l); dands; auto.

          * pose proof (fresh_distinct_vars_spec (length l) (vs ++ all_vars u)) as q.
            remember (fresh_distinct_vars (length l) (vs ++ all_vars u)) as fd; simpl in *; repnd.
            allrw disjoint_app_r; sp.

          * rewrite Term2NTerm_NTerm2Term_lsubst_aux_Term2NTerm_var_ren; eauto 3 with slow.
            eapply subset_disjoint;[apply subset_bound_vars_lsubst_aux|].
            rewrite sub_bound_vars_var_ren; autorewrite with slow.
            eauto 2 with slow.
    }

    exrepnd.
    exists (oTerm op bs'); simpl.
    rewrite h1.
    rewrite flat_map_map; unfold compose.
    dands; auto.
    match goal with
    | [ H : disjoint ?x _ |- disjoint _ ?y ] =>
      assert (x = y) as xx;[|rewrite <- xx; apply disjoint_sym; auto]
    end.
    unfold Bterms2BTerms; rw flat_map_map; unfold compose; auto.
Qed.

Lemma Term2NTerm_NTerm2Term_subst_Term2NTerm_var {o} :
  forall (t : @Term o) x v,
    Term2NTerm (NTerm2Term (subst (Term2NTerm t) x (mk_var v)))
    = subst (Term2NTerm t) x (mk_var v).
Proof.
  introv.
  unfold subst, lsubst; simpl.
  boolvar.

  - apply Term2NTerm_NTerm2Term_lsubst_aux_Term2NTerm_var_ren; eauto 3 with slow.

  - pose proof (change_bvars_alpha_Term2NTerm_eq [v] t) as h; exrepnd.
    rewrite h1.
    apply Term2NTerm_NTerm2Term_lsubst_aux_Term2NTerm_var_ren; eauto 3 with slow.
Qed.
Hint Rewrite @Term2NTerm_NTerm2Term_subst_Term2NTerm_var : slow.

Lemma SP_barehypotheses2barehypotheses_snoc {o} :
  forall (hs : @SP_barehypotheses o) h,
    SP_barehypotheses2barehypotheses (snoc hs h)
    = snoc (SP_barehypotheses2barehypotheses hs) (SP_hypothesis2hypothesis h).
Proof.
  introv; unfold SP_barehypotheses2barehypotheses.
  rw map_snoc; auto.
Qed.
Hint Rewrite @SP_barehypotheses2barehypotheses_snoc : slow.

Lemma barehypotheses2SP_barehypotheses_snoc {o} :
  forall (hs : @barehypotheses o) h,
    barehypotheses2SP_barehypotheses (snoc hs h)
    = snoc (barehypotheses2SP_barehypotheses hs) (hypothesis2SP_hypothesis h).
Proof.
  introv; unfold barehypotheses2SP_barehypotheses.
  rw map_snoc; auto.
Qed.
Hint Rewrite @barehypotheses2SP_barehypotheses_snoc : slow.

Lemma SP_hypothesis2hypothesis_hypothesis2SP_hypothesis_mk_hyp_Term2NTerm {o} :
  forall v (t : @Term o),
    SP_hypothesis2hypothesis (hypothesis2SP_hypothesis (mk_hyp v (Term2NTerm t)))
    = mk_hyp v (Term2NTerm t).
Proof.
  introv; unfold mk_hyp, hypothesis2SP_hypothesis, SP_hypothesis2hypothesis; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @SP_hypothesis2hypothesis_hypothesis2SP_hypothesis_mk_hyp_Term2NTerm : slow.

Inductive proof {o} : @SP_baresequent o -> Type :=
(*| proof_from_lib :
    forall c,
      LIn c (@PC_conclusions o ctxt)
      -> proof ctxt (mk_baresequent [] c)*)
| proof_isect_eq :
    forall (a1 a2 b1 b2 e1 e2 : Term) x1 x2 y i (H : SP_barehypotheses),
      NVin y (vars_hyps H)
      -> proof (rule_isect_equality2_hyp1 a1 a2 e1 i H)
      -> proof (rule_isect_equality2_hyp2 a1 b1 b2 e2 x1 x2 y i H)
      -> proof (rule_isect_equality_concl a1 a2 x1 x2 b1 b2 i H).
(*| proof_approx_refl :
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
*)

Lemma NVin_iff :
  forall v vs, NVin v vs <=> !LIn v vs.
Proof.
  introv.
  unfold NVin.
  rw <- (@assert_memberb NVar eq_var_dec).
  rw <- not_of_assert; sp.
Qed.

Lemma valid_proof {o} :
  forall lib (seq : @SP_baresequent o) (wf : wf_bseq seq),
    proof seq
    -> sequent_true2 lib seq.
Proof.
  introv wf p.
  induction p
    as [(* (* proved sequent       *) seq p
       |*) (* isect_eq             *) a1 a2 b1 b2 e1 e2 x1 x2 y i hs niy p1 ih1 p2 ih2
                                                                  (*
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
*)
       ];
    allsimpl;
    allrw NVin_iff.

  - unfold SP_baresequent2baresequent in *; simpl; fold_terms.
    autorewrite with slow in *.
    apply (rule_isect_equality2_true3 lib a1 a2 b1 b2 e1 e2 x1 x2 y i hs);
      simpl in *; autorewrite with slow in *; auto.

    + unfold args_constraints; simpl; introv h; repndors; subst; tcsp.

    + introv e; repndors; subst; tcsp.

      * apply ih1; auto.
        apply (rule_isect_equality2_wf2 y i a1 a2 b1 b2 e1 e2 x1 x2 hs); simpl; tcsp.

      * apply ih2; auto.
        apply (rule_isect_equality2_wf2 y i a1 a2 b1 b2 e1 e2 x1 x2 hs); simpl; tcsp.
Qed.