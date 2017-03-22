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


Inductive per_intensional {o} lib (T1 T2 : @CTerm o) : Prop :=
| PER_EXT :
    forall A1 v1 B1 A2 v2 B2,
      T1 ===>(lib) (mkc_function A1 v1 B1)
      -> T2 ===>(lib) (mkc_function A2 v2 B2)
      -> tequality lib A1 A2
      -> (forall a1 a2,
             equality lib a1 a2 A1
             -> per_intensional lib (substc a1 v1 B1) (substc a2 v2 B2)
                /\ tequality lib (substc a1 v1 B1) (substc a2 v2 B2))
      -> per_intensional lib T1 T2.

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

(*
Definition ext_sequent_true {o} lib (S : @csequent o) : Type :=
  forall s1 s2,
    match destruct_csequent S with
    | cseq_comps H T wh wt ct ec =>
      forall p : similarity lib s1 s2 H,
        match ec with
        | Some (existT _ ext (we, ce)) =>
          equality
            lib
            (lsubstc ext we s1 (s_cover_ex1 lib ext s1 s2 H ce p))
            (lsubstc ext we s2 (s_cover_ex2 lib ext s1 s2 H ce p))
            (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
          /\
          equality
            lib
            (lsubstc ext we s1 (s_cover_ex1 lib ext s1 s2 H ce p))
            (lsubstc ext we s2 (s_cover_ex2 lib ext s1 s2 H ce p))
            (lsubstc T wt s2 (s_cover_typ2 lib T s1 s2 H ct p))
        | None => True
        end
    end.

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
              -> match ec with
                   | Some (existT _ ext (we, ce)) =>
                       forall (pt1 : cover_vars ext s1) (pt2 : cover_vars ext s2),
                         equality
                           lib
                           (lsubstc ext we s1 pt1)
                           (lsubstc ext we s2 pt2)
                           (lsubstc T wt s1 pC1)
                         /\
                         equality
                           lib
                           (lsubstc ext we s1 pt1)
                           (lsubstc ext we s2 pt2)
                           (lsubstc T wt s2 pC2)
                   | None => True
                 end
      end.
Proof.
  unfold ext_sequent_true; split; intro h;
    destruct (destruct_csequent S); destruct ec; exrepnd; tcsp; introv;
      try (complete (apply h; auto)).

  introv sim; introv.
  pose proof (h s2 s3 sim) as h; repnd.

  rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in h0; auto.
  rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in h; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in h0; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in h; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in h0; auto.
  rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in h; auto.
Qed.


XXXXXXXXXXXXXXXX


Lemma ext_sequent_true_ex {o} :
  forall lib (S : @csequent o),
    ext_sequent_true lib S
    <=>
    forall s1 s2,
      match destruct_csequent S with
        | cseq_comps H T wh wt ct ec =>
          similarity lib s1 s2 H
          -> {pC1 : cover_vars T s1
              & {pC2 : cover_vars T s2
              & match ec with
                | Some (existT _ ext (we, ce)) =>
                  {pt1 : cover_vars ext s1
                   & {pt2 : cover_vars ext s2
                   & equality
                       lib
                       (lsubstc ext we s1 pt1)
                       (lsubstc ext we s2 pt2)
                       (lsubstc T wt s1 pC1)
                   # equality
                       lib
                       (lsubstc ext we s1 pt1)
                       (lsubstc ext we s2 pt2)
                       (lsubstc T wt s2 pC2)
                  }}
                | None => True
                end
             }}
      end.
Proof.
  unfold ext_sequent_true; split; intro h; introv;
    destruct (destruct_csequent S); destruct ec; exrepnd; tcsp; intro sim; auto.

  {
    pose proof (h s1 s2 sim) as q.

    exists (s_cover_typ1 lib T s1 s2 hs ct sim)
           (s_cover_typ2 lib T s1 s2 hs ct sim)
           (s_cover_ex1 lib t s1 s2 hs s0 sim)
           (s_cover_ex2 lib t s1 s2 hs s0 sim); sp.
  }

  {
    exists (s_cover_typ1 lib T s1 s2 hs ct sim)
           (s_cover_typ2 lib T s1 s2 hs ct sim); sp.
  }

  {
    pose proof (h s1 s2 sim) as q; exrepnd.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
    rewrite lsubstc_replace with (w2 := s3) (p2 := pt1); auto.
    rewrite lsubstc_replace with (w2 := s3) (p2 := pt2); auto.
  }
Qed.

Tactic Notation "ext_seq_true" :=
  rw @ext_sequent_true_all;
  simpl;
  introv sim;
  introv;
  proof_irr;
  GC.

 Ltac ext_seq_true_ltac H :=
  trw_h ext_sequent_true_ex  H;
  simpl in H.

Tactic Notation "ext_seq_true" "in" ident(H) :=
  ext_seq_true_ltac H.


Definition sp_ext_sequent_true {o} lib (S : @csequent o) : Type :=
  forall s1 s2,
    match destruct_csequent S with
    | cseq_comps H T wh wt ct ec =>
      forall p : similarity lib s1 s2 H,
        match ec with
        | Some (existT _ ext (we, ce)) =>
          equality
            lib
            (lsubstc ext we s1 (s_cover_ex1 lib ext s1 s2 H ce p))
            (lsubstc ext we s2 (s_cover_ex2 lib ext s1 s2 H ce p))
            (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
        | None => True
        end
    end.

Lemma ext_sequent_true_iff_sp {o} :
  forall lib (s : @csequent o), ext_sequent_true lib s <=> sp_ext_sequent_true lib s.
Proof.
  introv; split; introv h; introv.

  - pose proof (h s1 s2) as q.
    destruct (destruct_csequent s); introv; destruct ec; auto.
    pose proof (q p) as w; clear q.
    destruct s0; destruct p0; tcsp.

  - pose proof (h s1 s2) as q.
    destruct (destruct_csequent s); introv; destruct ec; auto.
    pose proof (q p) as w; clear q.
    destruct s0; destruct p0; dands; auto.
Abort.
*)