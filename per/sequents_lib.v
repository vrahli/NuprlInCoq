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


Require Export sequents2.
Require Export computation_lib_extends.


Definition sequent_true_ext_lib {o} uk lib0 (s : @csequent o) : Type :=
  forall lib,
    lib_extends lib lib0
    -> VR_sequent_true uk lib s.

Definition sequent_true_ext_lib_wf {o} uk lib (s : @baresequent o) :=
  {c : wf_csequent s & sequent_true_ext_lib uk lib (mk_wcseq s c)}.

Definition rule_true_ext_lib {o} uk lib (R : @rule o) : Type :=
  forall (wf    : wf_bseq (goal R))
         (cargs : args_constraints (sargs R) (hyps (goal R)))
         (hyps  : forall s, LIn s (subgoals R) -> sequent_true_ext_lib_wf uk lib s),
    sequent_true_ext_lib_wf uk lib (goal R).

Lemma sequent_true_mono_lib {o} :
  forall (e : @library_entry o) uk (l : library) (s : baresequent),
    entry_not_in_lib e l
    -> sequent_true_ext_lib_wf uk l s
    -> sequent_true_ext_lib_wf uk (e :: l) s.
Proof.
  introv ni st.
  unfold sequent_true_ext_lib_wf in *; exrepnd.
  exists c.
  introv libext.
  apply st0.
  apply lib_extends_cons_implies in libext; auto.
Qed.

Lemma sequent_true_ext_lib_wf_implies_sequent_true2_if_lib_extends {o} :
  forall lib lib0 (s : @baresequent o),
    lib_extends lib0 lib
    -> sequent_true_ext_lib_wf lib s
    -> sequent_true2 lib0 s.
Proof.
  introv libext st.
  unfold sequent_true_ext_lib_wf in st; exrepnd.
  exists c.
  unfold sequent_true_ext_lib in st0.
  apply sequent_true_eq_VR.
  apply st0; clear st0; eauto 2 with slow.
Qed.
Hint Resolve sequent_true_ext_lib_wf_implies_sequent_true2_if_lib_extends : slow.

Lemma sequent_true_ext_lib_wf_implies_sequent_true2 {o} :
  forall lib (s : @baresequent o),
    sequent_true_ext_lib_wf lib s
    -> sequent_true2 lib s.
Proof.
  introv st.
  eapply sequent_true_ext_lib_wf_implies_sequent_true2_if_lib_extends; eauto 2 with slow.
Qed.
Hint Resolve sequent_true_ext_lib_wf_implies_sequent_true2 : slow.

Definition wf_extract_seq {o} (s : @baresequent o) :=
  wf_term_op (extract (concl s)).

Definition wf_extract_goal {o} (R : @rule o) :=
  wf_extract_seq (goal R).

Definition wf_extract_sub {o} (R : @rule o) :=
  forall s : baresequent, LIn s (subgoals R) -> wf_extract_seq s.

Definition wf_extract {o} (R : @rule o) :=
  wf_extract_sub R -> wf_extract_goal R.

Lemma wf_sequent_implies_wf_extract_seq {o} :
  forall (s : @baresequent o),
    wf_sequent s
    -> wf_extract_seq s.
Proof.
  introv wf.
  unfold wf_sequent in wf; repnd.
  unfold wf_extract_seq.
  destruct s; simpl in *.
  unfold wf_concl in wf; tcsp.
Qed.
Hint Resolve wf_sequent_implies_wf_extract_seq : slow.

Lemma wf_csequent_implies_wf_extract_seq {o} :
  forall (s : @baresequent o),
    wf_csequent s
    -> wf_extract_seq s.
Proof.
  introv wf.
  unfold wf_csequent in wf; repnd; eauto 2 with slow.
Qed.
Hint Resolve wf_csequent_implies_wf_extract_seq : slow.

(* MOVE to sequents2.v *)
Lemma rule_true2_implies_rule_true3 {o} :
  forall lib (R : @rule o),
    wf_extract R
    -> rule_true2 lib R
    -> rule_true3 lib R.
Proof.
  introv wfe rt wf args imp.
  unfold rule_true2 in rt; repeat (autodimp rt hyp).
  unfold pwf_sequent.
  unfold wf_bseq in wf; repnd; dands; auto.
  unfold wf_sequent; dands; auto.
  unfold wf_concl; dands; auto.
  apply wfe; introv i; apply imp in i.
  unfold sequent_true2 in i; exrepnd; eauto 2 with slow.
Qed.

(* MOVE to sequents2.v *)
Lemma rule_true_implies_rule_true3 {o} :
  forall lib (R : @rule o),
    wf_extract R
    -> rule_true lib R
    -> rule_true3 lib R.
Proof.
  introv wfe rt.
  apply rule_true_iff_rule_true2 in rt.
  apply rule_true2_implies_rule_true3; auto.
Qed.

Lemma rule_true3_implies_rule_true_ext_lib {o} :
  forall (R : @rule o),
    (forall lib, rule_true3 lib R)
    -> forall lib, rule_true_ext_lib lib R.
Proof.
  introv rt wf args imp.
  pose proof (rt lib wf args) as q.
  autodimp q hyp.

  { introv i; apply imp in i; eauto 2 with slow. }

  unfold sequent_true2 in q; exrepnd.
  exists c.
  introv i.

  pose proof (rt lib0 wf args) as h.
  repeat (autodimp h hyp).

  { introv j; apply imp in j; eauto 2 with slow. }

  unfold sequent_true2 in h; exrepnd.
  apply sequent_true_eq_VR.
  pose proof (wf_csequent_proof_irrelevance _ c c0) as xx; subst; auto.
Qed.

Lemma rule_true2_implies_rule_true_ext_lib {o} :
  forall (R : @rule o),
    wf_extract R
    -> (forall lib, rule_true2 lib R)
    -> forall lib, rule_true_ext_lib lib R.
Proof.
  introv wfe rt; introv.
  apply rule_true3_implies_rule_true_ext_lib; introv.
  apply rule_true2_implies_rule_true3; auto.
Qed.

Lemma rule_true_implies_rule_true_ext_lib {o} :
  forall (R : @rule o),
    wf_extract R
    -> (forall lib, rule_true lib R)
    -> forall lib, rule_true_ext_lib lib R.
Proof.
  introv wfe rt; introv.
  apply rule_true3_implies_rule_true_ext_lib; introv.
  apply rule_true_implies_rule_true3; auto.
Qed.

Lemma sequent_true_ext_lib_all {o} :
  forall lib0 (S : @csequent o),
    sequent_true_ext_lib lib0 S
    <=>
    forall lib s1 s2,
      match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
        forall (pC1 : cover_vars T s1)
               (pC2 : cover_vars T s2),
          lib_extends lib lib0
          -> similarity lib s1 s2 H
          -> hyps_functionality lib s1 H
          -> match ec with
             | Some (existT _ ext (we, ce)) =>
               forall pt1 : cover_vars ext s1,
               forall pt2 : cover_vars ext s2,
                 tequality
                   lib
                   (lsubstc T wt s1 pC1)
                   (lsubstc T wt s2 pC2)
                 #
                 equality
                   lib
                   (lsubstc ext we s1 pt1)
                   (lsubstc ext we s2 pt2)
                   (lsubstc T wt s1 pC1)
             | None => tequality lib (lsubstc T wt s1 pC1)
                                 (lsubstc T wt s2 pC2)
             end
      end.
Proof.
  unfold sequent_true_ext_lib, VR_sequent_true; split; intro h;
    destruct (destruct_csequent S); destruct ec; exrepnd;
      introv libext sim; auto; introv hf.

  { introv.
    pose proof (h lib libext s2 s3 sim hf) as h.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in h; auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in h; auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in h; auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in h; auto. }

  { pose proof (h lib libext s1 s2 sim hf) as h.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in h; auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in h; tcsp. }
Qed.

Lemma sequent_true_ext_lib_ex {o} :
  forall lib0 (S : @csequent o),
    sequent_true_ext_lib lib0 S
    <=>
    forall lib s1 s2,
      match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
        lib_extends lib lib0
        -> hyps_functionality lib s1 H
        -> similarity lib s1 s2 H
        -> {pC1 : cover_vars T s1
            & {pC2 : cover_vars T s2
            & tequality
                lib
                (lsubstc T wt s1 pC1)
                (lsubstc T wt s2 pC2)
              #
              match ec with
              | Some (existT _ ext (we, ce)) =>
                {pt1 : cover_vars ext s1
                 & {pt2 : cover_vars ext s2
                 & equality
                     lib
                     (lsubstc ext we s1 pt1)
                     (lsubstc ext we s2 pt2)
                     (lsubstc T wt s1 pC1)}}
              | None => True
              end}}
      end.
Proof.
  unfold sequent_true_ext_lib, VR_sequent_true; split; intro h;
    destruct (destruct_csequent S); introv extlib hf;
      destruct ec; exrepnd; auto; try intro sim.

  { pose proof (h lib extlib s1 s2 sim hf) as h.

    exists (s_cover_typ1 lib T s1 s2 hs ct sim)
           (s_cover_typ2 lib T s1 s2 hs ct sim); sp.
    exists (s_cover_ex1 lib t s1 s2 hs s0 sim)
           (s_cover_ex2 lib t s1 s2 hs s0 sim); sp. }

  { pose proof (h lib extlib s1 s2 sim hf) as h.

    exists (s_cover_typ1 lib T s1 s2 hs ct sim)
           (s_cover_typ2 lib T s1 s2 hs ct sim); sp. }

  { pose proof (h lib s1 s2 extlib hf p) as h; exrepnd.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
    rewrite lsubstc_replace with (w2 := s3) (p2 := pt1); auto.
    rewrite lsubstc_replace with (w2 := s3) (p2 := pt2); auto. }

  { pose proof (h lib s1 s2 extlib hf p) as h; exrepnd.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto. }
Qed.

Tactic Notation "seq_true_ext_lib" :=
  rw @sequent_true_ext_lib_all;
  simpl;
  introv extlib sim eqh;
  introv;
  proof_irr;
  GC.

Ltac seq_true_ext_lib_ltac H :=
  trw_h sequent_true_ext_lib_ex H;
  simpl in H.

Tactic Notation "seq_true_ext_lib" "in" ident(H) :=
  seq_true_ext_lib_ltac H.
