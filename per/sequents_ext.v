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
