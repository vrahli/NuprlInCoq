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


Definition matching_sovar_sigs (vars1 vars2 : list sovar_sig) : Prop :=
  map snd vars1 = map snd vars2.

Definition matching_entries {o} (entry1 entry2 : @library_entry o) : Prop :=
  match entry1, entry2 with
  | lib_abs oa1 vars1 rhs1 correct1, lib_abs oa2 vars2 rhs2 correct2 =>
    matching_entry_sign oa1 oa2
    /\ matching_sovar_sigs vars1 vars2
  end.

Inductive entry_in_library {o} : @library_entry o -> library -> Prop :=
| entry_in_library_hd :
    forall entry lib,
      entry_in_library entry (entry :: lib)
| entry_in_library_tl :
    forall entry1 entry2 lib,
      ~ matching_entries entry1 entry2
      -> entry_in_library entry1 lib
      -> entry_in_library entry1 (entry2 :: lib).

(* [lib1] extends [lib0] *)
Definition lib_extends {o} (lib1 lib0 : @library o) : Prop :=
  forall entry, entry_in_library entry lib0 -> entry_in_library entry lib1.

Definition sequent_true_ext_lib {o} lib0 (S : @csequent o) : Type :=
  forall lib s1 s2,
    lib_extends lib lib0
    ->
    match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
          forall (p : similarity lib s1 s2 H),
            hyps_functionality lib s1 H
            -> tequality lib
                 (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                 (lsubstc T wt s2 (s_cover_typ2 lib T s1 s2 H ct p))
               # match ec with
                   | Some (existT _ ext (we, ce)) =>
                       equality lib
                         (lsubstc ext we s1 (s_cover_ex1 lib ext s1 s2 H ce p))
                         (lsubstc ext we s2 (s_cover_ex2 lib ext s1 s2 H ce p))
                         (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                   | None => True
                 end
    end.

Definition sequent_true_ext_lib_wf {o} lib (s : @baresequent o) :=
  {c : wf_csequent s & sequent_true_ext_lib lib (mk_wcseq s c)}.

Definition rule_true_ext_lib {o} lib (R : @rule o) : Type :=
  forall (wf    : wf_bseq (goal R))
         (cargs : args_constraints (sargs R) (hyps (goal R)))
         (hyps  : forall s, LIn s (subgoals R) -> sequent_true_ext_lib_wf lib s),
    sequent_true_ext_lib_wf lib (goal R).

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
  unfold sequent_true_ext_lib; split; intro h;
    destruct (destruct_csequent S); destruct ec; exrepnd;
      introv libext sim; auto; introv hf.

  { introv.
    pose proof (h lib s2 s3 libext sim hf) as h.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in h; auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in h; auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in h; auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in h; auto. }

  { pose proof (h lib s1 s2 libext sim hf) as h.

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
  unfold sequent_true_ext_lib; split; intro h;
    destruct (destruct_csequent S); introv extlib hf;
      destruct ec; exrepnd; auto; try intro sim.

  { pose proof (h lib s1 s2 extlib sim hf) as h.

    exists (s_cover_typ1 lib T s1 s2 hs ct sim)
           (s_cover_typ2 lib T s1 s2 hs ct sim); sp.
    exists (s_cover_ex1 lib t s1 s2 hs s0 sim)
           (s_cover_ex2 lib t s1 s2 hs s0 sim); sp. }

  { pose proof (h lib s1 s2 extlib sim hf) as h.

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
