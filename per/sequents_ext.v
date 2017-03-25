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


Require Export sequents.
Require Export csubst6.


Inductive per_intensional {o} lib (T1 T2 : @CTerm o) : Prop :=
| PER_INT_FUN :
    forall A1 v1 B1 A2 v2 B2,
      T1 ===>(lib) (mkc_function A1 v1 B1)
      -> T2 ===>(lib) (mkc_function A2 v2 B2)
      -> tequality lib A1 A2
      -> (forall a1 a2,
             equality lib a1 a2 A1
             -> tequality lib (substc a1 v1 B1) (substc a2 v2 B2))
      -> (forall a1 a2,
             equality lib a1 a2 A1
             -> per_intensional lib (substc a1 v1 B1) (substc a2 v2 B2))
      -> per_intensional lib T1 T2
(* This is required by the lambdaFormation rule for example to prove that
   the domain is per_intensional --- should we say
       (per_intensional lib a1 a2 \/ a1 ~ a2)?
 *)
| PER_INT_EQ :
    forall a1 a2 A b1 b2 B i,
      T1 ===>(lib) (mkc_equality a1 a2 A)
      -> T2 ===>(lib) (mkc_equality b1 b2 B)
      -> A ===>(lib) (mkc_uni i)
      -> B ===>(lib) (mkc_uni i)
      -> per_intensional lib a1 b1
      -> per_intensional lib a2 b2
      -> per_intensional lib T1 T2
.

(*
   Adapted from [eq_hyps].
   We added the per_intensional constraint which is supposed to enforce that
   types such as function types are intensional enough
 *)
Inductive ext_eq_hyps {o} (lib : @library o) : @CSub o -> @CSub o -> @bhyps o -> [U] :=
  | ext_eq_hyps_nil : ext_eq_hyps lib [] [] []
  | ext_eq_hyps_cons :
      forall (t1 t2 : CTerm)
             (s1 s2 : CSub)
             (h  : hypothesis)
             (hs : barehypotheses)
             (w  : wf_term (htyp h))
             (p1 : cover_vars (htyp h) s1)
             (p2 : cover_vars (htyp h) s2)
             (eqt : eqtypes
                      lib
                      (lvl h)
                      (lsubstc (htyp h) w s1 p1)
                      (lsubstc (htyp h) w s2 p2))
             (int : per_intensional
                      lib
                      (lsubstc (htyp h) w s1 p1)
                      (lsubstc (htyp h) w s2 p2))
             (eqh : ext_eq_hyps lib s1 s2 hs),
        ext_eq_hyps lib (snoc s1 (hvar h, t1)) (snoc s2 (hvar h, t2)) (snoc hs h).
Hint Constructors ext_eq_hyps.

(* Adapted from [hyps_functionality] *)
Definition ext_hyps_functionality {o} lib (s : @CSub o) (H : @bhyps o) :=
  forall s', similarity lib s s' H -> ext_eq_hyps lib s s' H.

(* Adapted from [VR_sequent_true] *)
Definition ext_sequent_true {o} lib (S : @csequent o) : Type :=
  forall s1 s2,
    match destruct_csequent S with
    | cseq_comps H T wh wt ct ec =>
      forall p : similarity lib s1 s2 H,
        ext_hyps_functionality lib s1 H
        -> tequality
             lib
             (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
             (lsubstc T wt s2 (s_cover_typ2 lib T s1 s2 H ct p))
           /\ per_intensional
                lib
                (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                (lsubstc T wt s2 (s_cover_typ2 lib T s1 s2 H ct p))
           /\ match ec with
              | Some (existT _ ext (we, ce)) =>
                equality
                  lib
                  (lsubstc ext we s1 (s_cover_ex1 lib ext s1 s2 H ce p))
                  (lsubstc ext we s2 (s_cover_ex2 lib ext s1 s2 H ce p))
                  (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
              | None => True
              end
    end.

(* Adapted from [rule_true] *)
Definition ext_rule_true {o} lib (R : @rule o) : Type :=
  forall (wg : wf_sequent (goal R))
         (cg : closed_type_baresequent (goal R))
         (cargs: args_constraints (sargs R) (hyps (goal R)))
         (hyps :
            forall s : baresequent,
              LIn s (subgoals R)
              -> {c : wf_csequent s & ext_sequent_true lib (mk_wcseq s c)}),
    {c : closed_extract_baresequent (goal R)
     & ext_sequent_true lib (mk_wcseq (goal R) (ext_wf_cseq (goal R) wg cg c))}.
Hint Unfold ext_rule_true.

Lemma ext_sequent_true_all {o} :
  forall lib (S : @csequent o),
    ext_sequent_true lib S
    <=>
    forall s1 s2,
      match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
        forall (pC1 : cover_vars T s1) (pC2 : cover_vars T s2),
          similarity lib s1 s2 H
          -> ext_hyps_functionality lib s1 H
          -> match ec with
             | Some (existT _ ext (we, ce)) =>
               forall (pt1 : cover_vars ext s1) (pt2 : cover_vars ext s2),
                 tequality
                   lib
                   (lsubstc T wt s1 pC1)
                   (lsubstc T wt s2 pC2)
                 /\
                 per_intensional
                   lib
                   (lsubstc T wt s1 pC1)
                   (lsubstc T wt s2 pC2)
                 /\
                 equality
                   lib
                   (lsubstc ext we s1 pt1)
                   (lsubstc ext we s2 pt2)
                   (lsubstc T wt s1 pC1)
             | None =>
               tequality
                 lib
                 (lsubstc T wt s1 pC1)
                 (lsubstc T wt s2 pC2)
               /\
               per_intensional
                 lib
                 (lsubstc T wt s1 pC1)
                 (lsubstc T wt s2 pC2)
             end
      end.
Proof.
  unfold ext_sequent_true; split; intro h;
    destruct (destruct_csequent S); destruct ec; exrepnd; tcsp; introv;
      try (complete (apply h; auto)).

  {
    introv sim hf; introv.
    pose proof (h s2 s3 sim hf) as hyp.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in hyp; auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in hyp; auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in hyp; auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in hyp; auto.
  }

  {
    introv sim hf; introv.
    pose proof (h s1 s2 sim hf) as hyp.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in hyp; auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in hyp; auto.
    tcsp.
  }

  {
    introv hf.
    remember (s_cover_typ1 lib T s2 s3 hs ct p) as pC1.
    remember (s_cover_typ2 lib T s2 s3 hs ct p) as pC2.
    remember (s_cover_ex1 lib t s2 s3 hs s0 p) as pt1.
    remember (s_cover_ex2 lib t s2 s3 hs s0 p) as pt2.
    pose proof (h s2 s3 pC1 pC2 p hf pt1 pt2) as hyp.
    auto.
  }

  {
    introv hf.
    remember (s_cover_typ1 lib T s1 s2 hs ct p) as pC1.
    remember (s_cover_typ2 lib T s1 s2 hs ct p) as pC2.
    pose proof (h s1 s2 pC1 pC2 p hf) as hyp.
    tcsp.
  }
Qed.


Lemma ext_sequent_true_ex {o} :
  forall lib (S : @csequent o),
    ext_sequent_true lib S
    <=>
    forall s1 s2,
      match destruct_csequent S with
        | cseq_comps H T wh wt ct ec =>
          similarity lib s1 s2 H
          -> ext_hyps_functionality lib s1 H
          -> {pC1 : cover_vars T s1
              & {pC2 : cover_vars T s2
              & match ec with
                | Some (existT _ ext (we, ce)) =>
                  {pt1 : cover_vars ext s1
                   & {pt2 : cover_vars ext s2
                   & tequality
                       lib
                       (lsubstc T wt s1 pC1)
                       (lsubstc T wt s2 pC2)
                   # per_intensional
                       lib
                       (lsubstc T wt s1 pC1)
                       (lsubstc T wt s2 pC2)
                   # equality
                       lib
                       (lsubstc ext we s1 pt1)
                       (lsubstc ext we s2 pt2)
                       (lsubstc T wt s1 pC1)
                  }}
                | None =>
                  tequality
                       lib
                       (lsubstc T wt s1 pC1)
                       (lsubstc T wt s2 pC2)
                   # per_intensional
                       lib
                       (lsubstc T wt s1 pC1)
                       (lsubstc T wt s2 pC2)
                end
             }}
      end.
Proof.
  unfold ext_sequent_true; split; intro h; introv;
    destruct (destruct_csequent S); destruct ec; exrepnd; tcsp; intros sim hf; auto.

  {
    pose proof (h s1 s2 sim hf) as q.

    exists (s_cover_typ1 lib T s1 s2 hs ct sim)
           (s_cover_typ2 lib T s1 s2 hs ct sim)
           (s_cover_ex1 lib t s1 s2 hs s0 sim)
           (s_cover_ex2 lib t s1 s2 hs s0 sim); sp.
  }

  {
    pose proof (h s1 s2 sim hf) as q; repnd.
    exists (s_cover_typ1 lib T s1 s2 hs ct sim)
           (s_cover_typ2 lib T s1 s2 hs ct sim); sp.
  }

  {
    pose proof (h s1 s2 sim hf) as q; exrepnd.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
    rewrite lsubstc_replace with (w2 := s3) (p2 := pt1); auto.
    rewrite lsubstc_replace with (w2 := s3) (p2 := pt2); auto.
  }

  {
    pose proof (h s1 s2 sim hf) as q; exrepnd.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
  }
Qed.

Tactic Notation "ext_seq_true" :=
  rw @ext_sequent_true_all;
  simpl;
  introv sim hf;
  introv;
  proof_irr;
  GC.

 Ltac ext_seq_true_ltac H :=
  trw_h ext_sequent_true_ex  H;
  simpl in H.

Tactic Notation "ext_seq_true" "in" ident(H) :=
  ext_seq_true_ltac H.

Lemma ext_eq_hyps_snoc {o} :
  forall lib (hs : @bhyps o) h s1 s2,
    ext_eq_hyps lib s1 s2 (snoc hs h)
    <=>
    {s1a, s2a : CSub
     , {t1, t2 : CTerm
     , {w : wf_term (htyp h)
     , {p1 : cover_vars (htyp h) s1a
     , {p2 : cover_vars (htyp h) s2a
     , s1 = snoc s1a (hvar h, t1)
     # s2 = snoc s2a (hvar h, t2)
     # ext_eq_hyps lib s1a s2a hs
     # eqtypes lib (lvl h) (lsubstc (htyp h) w s1a p1) (lsubstc (htyp h) w s2a p2)
     # per_intensional lib (lsubstc (htyp h) w s1a p1) (lsubstc (htyp h) w s2a p2)
    }}}}}.
Proof.
  introv; split; intro k; exrepnd; subst.

  - inversion k; subst; cpx.
    exists s0 s3 t1 t2 w.
    exists p1 p2; sp.

  - apply @ext_eq_hyps_cons with (w := w) (p1 := p1) (p2 := p2); sp.
Qed.

Lemma per_intensional_mkc_equality_implies {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o) i,
    per_intensional
      lib
      (mkc_equality a1 a2 (mkc_uni i))
      (mkc_equality b1 b2 (mkc_uni i))
    -> (per_intensional lib a1 b1
        # per_intensional lib a2 b2).
Proof.
  introv per.
  inversion per; computes_to_value_isvalue.
Qed.

Lemma per_intensional_mkc_member_implies {o} :
  forall lib (a b : @CTerm o) i,
    per_intensional
      lib
      (mkc_member a (mkc_uni i))
      (mkc_member b (mkc_uni i))
    -> per_intensional lib a b.
Proof.
  introv per.
  allrw <- @fold_mkc_member.
  apply per_intensional_mkc_equality_implies in per; tcsp.
Qed.

Lemma per_intensional_respects_cequivc {o} :
  forall lib (A1 A2 B1 B2 : @CTerm o),
    cequivc lib A1 A2
    -> cequivc lib B1 B2
    -> per_intensional lib A1 B1
    -> per_intensional lib A2 B2.
Proof.
  introv ceq1 ceq2 per.
  revert A2 B2 ceq1 ceq2.

  induction per; introv ceq1 ceq2; spcast.

  - eapply cequivc_mkc_function in ceq1;[|eauto]; exrepnd.
    eapply cequivc_mkc_function in ceq2;[|eauto]; exrepnd.

    eapply PER_INT_FUN; spcast; eauto;
      eauto 3 with nequality.

    + introv eqa.
      match goal with
      | [ H : context[equality _ _ _ _ -> tequality _ _ _ ] |- _ ] =>
        rename H into h
      end.
      assert (equality lib a1 a2 A1) as q.
      { eapply cequivc_preserving_equality;[eauto|]; apply cequivc_sym; auto. }
      applydup h in q.

      eapply tequality_respects_cequivc_left;[apply bcequivc1;eauto|].
      eapply tequality_respects_cequivc_right;[apply bcequivc1;eauto|].
      auto.

    + introv eqa.
      match goal with
      | [ H : context[cequivc _ _ _ -> per_intensional _ _ _ ] |- _ ] =>
        rename H into h
      end.
      assert (equality lib a1 a2 A1) as q.
      { eapply cequivc_preserving_equality;[eauto|]; apply cequivc_sym; auto. }

      apply (h a1 a2 q); apply bcequivc1; auto.

  - eapply cequivc_mkc_equality in ceq1;[|eauto]; exrepnd.
    eapply cequivc_mkc_equality in ceq2;[|eauto]; exrepnd.
    eapply cequivc_uni in ceq0;[|eauto].
    eapply cequivc_uni in ceq5;[|eauto].

    eapply PER_INT_EQ; spcast; eauto.
Qed.

Lemma per_intensional_respects_alphaeqc {o} :
  forall lib (A1 A2 B1 B2 : @CTerm o),
    alphaeqc A1 A2
    -> alphaeqc B1 B2
    -> per_intensional lib A1 B1
    -> per_intensional lib A2 B2.
Proof.
  introv aeqa aeqb peri.
  eapply per_intensional_respects_cequivc;[| |eauto]; eauto 3 with slow.
Qed.

Lemma respects_cequivc_per_intensional {o} :
  forall (lib : @library o), respects2 (cequivc lib) (per_intensional lib).
Proof.
  introv; split; introv ceq per.
  - eapply per_intensional_respects_cequivc;[| |eauto]; eauto 3 with slow.
  - eapply per_intensional_respects_cequivc;[| |eauto]; eauto 3 with slow.
Qed.
Hint Resolve respects_cequivc_per_intensional : respects.

Lemma respects_alphaeqc_per_intensional {o} :
  forall (lib : @library o), respects2 alphaeqc (per_intensional lib).
Proof.
  introv; split; introv ceq per.
  - eapply per_intensional_respects_alphaeqc;[| |eauto]; eauto 3 with slow.
  - eapply per_intensional_respects_alphaeqc;[| |eauto]; eauto 3 with slow.
Qed.
Hint Resolve respects_alphaeqc_per_intensional : respects.

Lemma ext_hyps_functionality_snoc {o} :
  forall lib (H : @bhyps o) h s t,
    (forall t' s' w c c',
       equality lib t t' (lsubstc (htyp h) w s c)
       -> similarity lib s s' H
       -> eqtypes lib (lvl h) (lsubstc (htyp h) w s c) (lsubstc (htyp h) w s' c')
          /\ per_intensional lib (lsubstc (htyp h) w s c) (lsubstc (htyp h) w s' c'))
    -> ext_hyps_functionality lib s H
    -> ext_hyps_functionality lib (snoc s (hvar h, t)) (snoc H h).
Proof.
  introv imp hf sim.
  rw @similarity_snoc in sim; exrepnd; subst; cpx.
  rw @ext_eq_hyps_snoc; simpl.

  assert (cover_vars (htyp h) s2a)
    as c
      by (clear sim1;
          allrw @cover_vars_covered; allapply @similarity_dom; exrepnd; allrw; sp;
          rw <- sim0; sp).

  exists s1a s2a t1 t2 w p c; sp; apply imp with (t' := t2); sp.
Qed.

Lemma ext_hyps_functionality_snoc2 {o} :
  forall lib (H : @bhyps o) h s t v,
    (forall t' s' w c c',
       equality lib t t' (lsubstc (htyp h) w s c)
       -> similarity lib s s' H
       -> eqtypes lib (lvl h) (lsubstc (htyp h) w s c) (lsubstc (htyp h) w s' c')
          /\ per_intensional lib (lsubstc (htyp h) w s c) (lsubstc (htyp h) w s' c'))
    -> ext_hyps_functionality lib s H
    -> v = hvar h
    -> ext_hyps_functionality lib (snoc s (v, t)) (snoc H h).
Proof.
  intros; subst.
  apply ext_hyps_functionality_snoc; sp.
Qed.

(** We now generalize Aleksey's definition to handle extra substitutions.
 * This is needed to state eq_hyps_app. *)
Inductive ext_sub_eq_hyps {o} (lib : @library o) :
  @CSub o -> @CSub o
  -> @CSub o -> @CSub o
  -> @bhyps o
  -> [U] :=
| ext_sub_eq_hyps_nil : forall s1 s2, ext_sub_eq_hyps lib s1 s2 [] [] []
| ext_sub_eq_hyps_cons :
    forall (t1 t2 : CTerm)
           (s1 s2 s3 s4 : CSub)
           (h  : hypothesis)
           (hs : barehypotheses)
           (w  : wf_term (htyp h))
           (p1 : cover_vars (htyp h) (s3 ++ s1))
           (p2 : cover_vars (htyp h) (s4 ++ s2))
           (eqt : eqtypes
                    lib
                    (lvl h)
                    (lsubstc (htyp h) w (s3 ++ s1) p1)
                    (lsubstc (htyp h) w (s4 ++ s2) p2))
           (per : per_intensional
                    lib
                    (lsubstc (htyp h) w (s3 ++ s1) p1)
                    (lsubstc (htyp h) w (s4 ++ s2) p2))
           (seh : ext_sub_eq_hyps lib s3 s4 s1 s2 hs),
      ext_sub_eq_hyps lib s3 s4 (snoc s1 (hvar h, t1)) (snoc s2 (hvar h, t2)) (snoc hs h).
Hint Constructors ext_sub_eq_hyps.

Lemma ext_eq_hyps_length {o} :
  forall lib (hs : @bhyps o) s1 s2,
    ext_eq_hyps lib s1 s2 hs
    -> (length s1 = length hs # length s2 = length hs).
Proof.
  induction hs using rev_list_indT; simpl; introv eh;
  inversion eh; subst; simpl; cpx.

  repeat (rewrite length_snoc).
  discover; sp.
Qed.

Lemma ext_eq_hyps_app {o} :
  forall lib (hs1 hs2 : @bhyps o) s1 s2,
    ext_eq_hyps lib s1 s2 (hs1 ++ hs2)
    <=>
    {s1a, s1b, s2a, s2b : CSub
      , s1 = s1a ++ s1b
      # s2 = s2a ++ s2b
      # length s1a = length hs1
      # length s2a = length hs1
      # ext_eq_hyps lib s1a s2a hs1
      # ext_sub_eq_hyps lib s1a s2a s1b s2b hs2}.
Proof.
  induction hs2 using rev_list_indT; simpl; sp.

  - rewrite app_nil_r; split; intro k; exrepnd; subst.
    applydup @ext_eq_hyps_length in k; sp.
    exists s1 (nil : (@CSub o)) s2 (nil : (@CSub o)); simpl; sp;
      allrewrite app_nil_r; auto.
    inversion k1; subst; allrewrite app_nil_r; auto; cpx.

  - rewrite snoc_append_l; split; intro k; exrepnd; subst.

    + inversion k; cpx.

      rw IHhs2 in eqh; sp; subst.
      exists s1a (snoc s1b (hvar a, t1)) s2a (snoc s2b (hvar a, t2)).
      repeat (rewrite snoc_append_l); sp.

      apply @ext_sub_eq_hyps_cons with (w := w) (p1 := p1) (p2 := p2); sp.

    + inversion k1; cpx.
      repeat (rewrite snoc_append_l).
      apply @ext_eq_hyps_cons with (w := w) (p1 := p1) (p2 := p2); sp.
      rw IHhs2.
      exists s1a s1 s2a s2; sp.
Qed.

Lemma per_intensional_function {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2,
    per_intensional lib (mkc_function A1 v1 B1) (mkc_function A2 v2 B2)
    <=> (tequality lib A1 A2
         # (forall a1 a2,
               equality lib a1 a2 A1
               -> tequality lib (substc a1 v1 B1) (substc a2 v2 B2))
         # (forall a1 a2,
               equality lib a1 a2 A1
               -> per_intensional lib (substc a1 v1 B1) (substc a2 v2 B2))).
Proof.
  introv; split; intro h.

  - inversion h; spcast; computes_to_value_isvalue.

  - repnd.
    eapply PER_INT_FUN; spcast; eauto 3 with slow.
Qed.

Lemma ext_sub_eq_hyps_dom {o} :
  forall lib (hs : @bhyps o) s1 s2 s3 s4,
    ext_sub_eq_hyps lib s3 s4 s1 s2 hs
    -> dom_csub s1 = vars_hyps hs
       # dom_csub s2 = vars_hyps hs.
Proof.
  induction hs using rev_list_indT; simpl; introv seh; inversion seh; subst; allsimpl; cpx.
  repeat (rewrite dom_csub_snoc); simpl.
  rewrite vars_hyps_snoc.
  discover; repnd.
  allrw; sp.
Qed.
