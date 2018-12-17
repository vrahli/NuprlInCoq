(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Import sequents2.


Lemma pointwise_implies_pairwise {o} :
  forall lib (s : @csequent o),
    AN_sequent_true_pairwise lib s -> VR_sequent_true lib s.
Proof.
  introv seq.
  unfold VR_sequent_true.
  unfold AN_sequent_true_pairwise in seq.
  introv.
  generalize (seq s1 s2); clear seq; intro seq.
  destruct (destruct_csequent s); destruct ec; exrepnd; intros sim eqh; auto.
Qed.

Definition pairwise_sequent_true {o} lib (s : @baresequent o) :=
  {c : wf_csequent s & AN_sequent_true_pairwise lib (mk_wcseq s c)}.

Definition pairwise_rule_true2 {o} lib (R : @rule o) : Type :=
  forall pwf   : pwf_sequent (goal R),
  forall cargs : args_constraints (sargs R) (hyps (goal R)),
  forall hyps  : (forall s, LIn s (subgoals R) -> pairwise_sequent_true lib s),
    pairwise_sequent_true lib (goal R).

Definition pairwise_rule_true3 {o} lib (R : @rule o) : Type :=
  forall pwf   : wf_bseq (goal R),
  forall cargs : args_constraints (sargs R) (hyps (goal R)),
  forall hyps  : (forall s, LIn s (subgoals R) -> pairwise_sequent_true lib s),
    pairwise_sequent_true lib (goal R).

Lemma pairwise_rule_true3_implies_pairwise_rule_true2 {o} :
  forall lib (R : @rule o), pairwise_rule_true3 lib R -> pairwise_rule_true2 lib R.
Proof.
  introv rt wf args imp.
  unfold pairwise_rule_true3 in rt.
  repeat (autodimp rt hyp); eauto 3 with slow.
Qed.
Hint Resolve pairwise_rule_true3_implies_pairwise_rule_true2 : slow.

Lemma AN_sequent_true_pairwise_all {o} :
  forall lib (S : @csequent o),
    AN_sequent_true_pairwise lib S
    <=>
    forall s1 s2,
      match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
        forall pC1 : cover_vars T s1,
        forall pC2 : cover_vars T s2,
          similarity lib s1 s2 H
          -> eq_hyps lib s1 s2 H
          -> match ec with
             | Some (existT _ ext (we, ce)) =>
               forall pt1 : cover_vars ext s1,
               forall pt2 : cover_vars ext s2,
                 tequality lib (lsubstc T wt s1 pC1)
                           (lsubstc T wt s2 pC2)
                           # equality lib (lsubstc ext we s1 pt1)
                           (lsubstc ext we s2 pt2)
                           (lsubstc T wt s1 pC1)
             | None => tequality lib (lsubstc T wt s1 pC1)
                                 (lsubstc T wt s2 pC2)
             end
      end.
Proof.
  unfold AN_sequent_true_pairwise; split; intro h;
    destruct (destruct_csequent S); destruct ec; exrepnd; introv.

  { introv sim eqh; introv.
    pose proof (h s2 s3 sim eqh) as h.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in h; auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in h; auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in h; auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in h; auto. }

  { introv sim eqh.
    pose proof (h s1 s2 sim eqh) as h.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in h; auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in h; tcsp. }

  { introv eqh; eapply h; auto. }

  { introv eqh; dands; auto. }
Qed.

Lemma AN_sequent_true_pairwise_ex {o} :
  forall lib (S : @csequent o),
    AN_sequent_true_pairwise lib S
    <=>
    forall s1 s2,
      match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
        similarity lib s1 s2 H
        -> eq_hyps lib s1 s2 H
        -> {pC1 : cover_vars T s1
            & {pC2 : cover_vars T s2
            & tequality lib (lsubstc T wt s1 pC1)
                        (lsubstc T wt s2 pC2)
              #
              match ec with
              | Some (existT _ ext (we, ce)) =>
                {pt1 : cover_vars ext s1
                 & {pt2 : cover_vars ext s2
                 & equality lib (lsubstc ext we s1 pt1)
                            (lsubstc ext we s2 pt2)
                            (lsubstc T wt s1 pC1)}}
              | None => True
              end}}
      end.
Proof.
  unfold AN_sequent_true_pairwise; split; intro h;
    destruct (destruct_csequent S); destruct ec; exrepnd; introv; auto.

  { introv sim eqh.
    pose proof (h s2 s3 sim eqh) as h; repnd.
    exists (s_cover_typ1 lib T s2 s3 hs ct sim)
           (s_cover_typ2 lib T s2 s3 hs ct sim); sp.
    exists (s_cover_ex1 lib t s2 s3 hs s0 sim)
           (s_cover_ex2 lib t s2 s3 hs s0 sim); sp. }

  { introv sim eqh.
    pose proof (h s1 s2 sim eqh) as h; repnd.
    exists (s_cover_typ1 lib T s1 s2 hs ct sim)
           (s_cover_typ2 lib T s1 s2 hs ct sim); sp. }

  { introv eqh.
    pose proof (h s2 s3 p eqh) as h; exrepnd.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt1); auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt2); auto. }

  { introv eqh.
    pose proof (h s1 s2 p eqh ) as h; exrepnd.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto. }
Qed.

Tactic Notation "seq_true_pairwise" :=
  rw @AN_sequent_true_pairwise_all;
  simpl;
  introv sim eqh;
  introv;
  proof_irr;
  GC.

Ltac seq_true_pairwise_ltac H :=
  trw_h AN_sequent_true_pairwise_ex  H;
  simpl in H.

Tactic Notation "seq_true_pairwise" "in" ident(H) :=
  seq_true_pairwise_ltac H.

Ltac prove_eq_hyps_snoc :=
  match goal with
  | [ |- eq_hyps _ (snoc ?s1 (?x1,?t1)) (snoc ?s2 (?x2,?t2)) (snoc ?hs ?h) ] =>
    let wf := fresh "wf" in
    let cov1 := fresh "cov1" in
    let cov2 := fresh "cov2" in
    assert (wf_term (htyp h)) as wf;
    [simpl;auto
    |assert (cover_vars (htyp h) s1) as cov1;
     [simpl;auto
     |assert (cover_vars (htyp h) s2) as cov2;
      [simpl;auto
      |apply eq_hyps_snoc;
       exists s1 s2 t1 t2 wf cov1 cov2;
       simpl;dands;auto
      ]
     ]
    ]
  end.
