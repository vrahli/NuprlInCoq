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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)



Require Export sequents2.


(* The goal is that lib1 does not extend the sequences in [names] *)
Definition lib_extends_upto {o}
           (lib1 lib0 : @library o)
           (names : list choice_sequence_name) : Prop :=
  lib_extends lib1 lib0
  /\ forall n, LIn n names -> find_cs lib1 n = find_cs lib0 n.

Definition sequent_true_ext_wf_names {o} lib names (S : @csequent o) : Prop :=
  forall lib' (x : lib_extends_upto lib' lib names) s1 s2,
    match destruct_csequent S with
    | cseq_comps H T wh wt ct ec =>
      forall (p : similarity lib' s1 s2 H),
        hyps_functionality_ext lib' s1 H
        -> {lib'' : library , {xt : lib_extends lib'' lib' ,
            (tequality
               lib''
               (lsubstc T wt s1 (s_cover_typ1 lib' T s1 s2 H ct p))
               (lsubstc T wt s2 (s_cover_typ2 lib' T s1 s2 H ct p)))
              /\ match ec with
                | Some (existT _ ext (we, ce)) =>
                  equality
                    lib''
                    (lsubstc ext we s1 (s_cover_ex1 lib' ext s1 s2 H ce p))
                    (lsubstc ext we s2 (s_cover_ex2 lib' ext s1 s2 H ce p))
                    (lsubstc T wt s1 (s_cover_typ1 lib' T s1 s2 H ct p))
                | None => True
                end}}
    end.

(*
Definition sequent_true_ext_wf {o} lib (S : @csequent o) : Type :=
  {names : list choice_sequence_name & sequent_true_ext_wf_names lib names S}.
*)

Definition sequent_true_ext {o} lib names (s : @baresequent o) :=
  {c : wf_csequent s , sequent_true_ext_wf_names lib names (mk_wcseq s c)}.

Record rule_ext {o} :=
  mk_rule_ext
    {
      re_goal     : @baresequent o;
      re_names    : list choice_sequence_name;
      re_subgoals : list (@baresequent o * list choice_sequence_name);
      re_sargs    : list (@sarg o)
    }.
Arguments mk_rule_ext [o] _ _ _ _.

Fixpoint disjointb
         {A}
         (deq : Deq A)
         (l k : list A) : bool :=
  match l with
  | [] => true
  | a :: l => if in_dec deq a k then false else disjointb deq l k
  end.

Fixpoint disjoint_from_list
         {A}
         (deq : Deq A)
         (l : list A)
         (L : list (list A)) : bool :=
  match L with
  | [] => true
  | k :: K => disjointb deq l k && disjoint_from_list deq l K
  end.

Fixpoint all_disjoint {A} (deq : Deq A) (L : list (list A)) : bool :=
  match L with
  | [] => true
  | l :: K => disjoint_from_list deq l K && all_disjoint deq K
  end.

Definition all_disjoint_names {o} (L : list (@baresequent o * list choice_sequence_name)) :=
  all_disjoint choice_sequence_name_deq (map snd L) = true.

(* We have to enforce at the top that the names used in the subgoals are disjoint
   from each others *)
Definition rule_true_ext {o} lib (R : @rule_ext o) : Type :=
  forall (wf    : wf_bseq (re_goal R))
         (cargs : args_constraints (re_sargs R) (hyps (re_goal R)))
         (hyps  : (forall s, LIn s (re_subgoals R) -> sequent_true_ext lib (snd s) (fst s))),
    (*(all_disjoint_names (re_subgoals R)) #*)
    sequent_true_ext lib (re_names R) (re_goal R).

Lemma sequent_true_ext_wf_names_all {o} :
  forall lib names (S : @csequent o),
    sequent_true_ext_wf_names lib names S
    <=>
    forall lib' (ext : lib_extends_upto lib' lib names) s1 s2,
      match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
        forall pC1 : cover_vars T s1,
        forall pC2 : cover_vars T s2,
          similarity lib' s1 s2 H
          -> hyps_functionality_ext lib' s1 H
          -> {lib'' : library , lib_extends lib'' lib' /\
             match ec with
             | Some (existT _ ext (we, ce)) =>
               forall pt1 : cover_vars ext s1,
               forall pt2 : cover_vars ext s2,
                 (tequality
                    lib''
                    (lsubstc T wt s1 pC1)
                    (lsubstc T wt s2 pC2))
                   /\ (equality
                        lib''
                        (lsubstc ext we s1 pt1)
                        (lsubstc ext we s2 pt2)
                        (lsubstc T wt s1 pC1))
             | None => tequality
                         lib''
                         (lsubstc T wt s1 pC1)
                         (lsubstc T wt s2 pC2)
             end}
      end.
Proof.
  unfold sequent_true_ext_wf_names; split; intro h;
    destruct (destruct_csequent S); destruct ec; exrepnd; introv ext sim; introv.

  {
    introv hf.
    pose proof (h _ ext s2 s3 sim hf) as h; exrepnd; exists lib''; dands; auto; introv.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in h0, h1; auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in h0; auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt1) in h1; auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt2) in h1; auto.
  }

  {
    introv hf.
    pose proof (h _ ext s1 s2 sim hf) as h; exrepnd; exists lib''; dands; auto.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1) in h0; auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2) in h0; auto; tcsp.
  }

  { pose proof (h _ ext s2 s3 (s_cover_typ1 lib' T s2 s3 hs ct p) (s_cover_typ2 lib' T s2 s3 hs ct p) p sim) as h; exrepnd.
    exists lib'' h1; apply h0. }

  { pose proof (h _ ext s1 s2 (s_cover_typ1 lib' T s1 s2 hs ct p) (s_cover_typ2 lib' T s1 s2 hs ct p) p sim) as h; exrepnd.
    exists lib'' h1; auto. }
Qed.

Lemma sequent_true_ext_wf_names_ex {o} :
  forall lib names (S : @csequent o),
    sequent_true_ext_wf_names lib names S
    <=>
    forall lib' (x : lib_extends_upto lib' lib names) s1 s2,
      match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
        hyps_functionality_ext lib' s1 H
        -> similarity lib' s1 s2 H
        -> {pC1 : cover_vars T s1
            , {pC2 : cover_vars T s2
            , {lib'' : library , lib_extends lib'' lib' /\
            (tequality
               lib''
               (lsubstc T wt s1 pC1)
               (lsubstc T wt s2 pC2))
            /\
            match ec with
            | Some (existT _ ext (we, ce)) =>
              {pt1 : cover_vars ext s1
               , {pt2 : cover_vars ext s2
               , equality
                   lib''
                   (lsubstc ext we s1 pt1)
                   (lsubstc ext we s2 pt2)
                   (lsubstc T wt s1 pC1)}}
            | None => True
            end}}}
      end.
Proof.
  unfold sequent_true_ext_wf_names; split; intro h;
    destruct (destruct_csequent S); destruct ec; exrepnd; introv ext hf; introv.

  {
    introv sim.
    pose proof (h _ ext s2 s3 sim hf) as h; exrepnd.
    eexists; eexists; eexists; dands; eauto.
  }

  {
    introv sim.
    pose proof (h _ ext s1 s2 sim hf) as h; exrepnd.
    eexists; eexists; eexists; dands; eauto.
  }

  {
    pose proof (h _ ext s2 s3 hf p) as h; exrepnd; exists lib''; dands; auto.
    exists h1.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt1); auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt2); auto.
  }

  {
    pose proof (h _ ext s1 s2 hf p) as h; exrepnd; exists lib''; dands; auto.
    exists h1.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
  }
Qed.



Tactic Notation "vr_seq_ext_true" :=
  rw @sequent_true_ext_wf_names_all;
  simpl;
  introv ext sim eqh;
  introv;
  proof_irr;
  GC.

 Ltac vr_seq_ext_true_ltac H :=
  trw_h sequent_true_ext_wf_names_ex  H;
  simpl in H.

Tactic Notation "vr_seq_ext_true" "in" ident(H) :=
  vr_seq_ext_true_ltac H.


Lemma lib_extends_upto_app_implies_left {o} :
  forall (lib' lib : @library o) names1 names2,
    lib_extends_upto lib' lib (names1 ++ names2)
    -> lib_extends_upto lib' lib names1.
Proof.
  introv ext.
  unfold lib_extends_upto in *; repnd; dands; auto.
  introv i.
  apply ext; apply in_app_iff; tcsp.
Qed.
Hint Resolve lib_extends_upto_app_implies_left : slow.

Lemma lib_extends_upto_app_implies_right {o} :
  forall (lib' lib : @library o) names1 names2,
    lib_extends_upto lib' lib (names1 ++ names2)
    -> lib_extends_upto lib' lib names2.
Proof.
  introv ext.
  unfold lib_extends_upto in *; repnd; dands; auto.
  introv i.
  apply ext; apply in_app_iff; tcsp.
Qed.
Hint Resolve lib_extends_upto_app_implies_right : slow.
