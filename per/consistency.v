(*

  Copyright 2014 Cornell University

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


Require Export sequents.
Require Export sequents_tacs.
Require Export per_props_union.
Require Export per_props_equality.


Definition csequent_not_not_true {o} lib (S : @csequent o) : Type :=
  forall s1 s2,
    match destruct_csequent S with
      | cseq_comps H T wh wt ct ec =>
          forall p : similarity lib s1 s2 H,
            hyps_functionality lib s1 H
            -> !!tequality lib
                   (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                   (lsubstc T wt s2 (s_cover_typ2 lib T s1 s2 H ct p))
               # match ec with
                   | Some (existT ext (we, ce)) =>
                       !!equality lib
                          (lsubstc ext we s1 (s_cover_ex1 lib ext s1 s2 H ce p))
                          (lsubstc ext we s2 (s_cover_ex2 lib ext s1 s2 H ce p))
                          (lsubstc T wt s1 (s_cover_typ1 lib T s1 s2 H ct p))
                   | None => True
                 end
    end.

Definition sequent_not_not_true {o} lib (s : @baresequent o) :=
  {c : wf_csequent s & csequent_not_not_true lib (mk_wcseq s c)}.

Definition rule_not_not_true {o} lib (R : @rule o) : Type :=
  forall pwf   : pwf_sequent (goal R),
  forall cargs : args_constraints (sargs R) (hyps (goal R)),
  forall hyps  : (forall s, LIn s (subgoals R) -> sequent_not_not_true lib s),
    sequent_not_not_true lib (goal R).

Lemma covered_mk_not {o} :
  forall (t : @NTerm o) vs,
    covered (mk_not t) vs <=> covered t vs.
Proof.
  introv.
  unfold mk_not.
  rw @covered_fun; split; intro k; repnd; auto.
Qed.

Lemma covered_mk_squash {o} :
  forall (t : @NTerm o) vs,
    covered (mk_squash t) vs <=> covered t vs.
Proof.
  introv.
  unfold mk_squash.
  unfold covered; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r; sp.
Qed.

(* !!MOVE *)
Hint Resolve vswf_hypotheses_nil_if : slow.
Hint Resolve sim_nil : slow.

Lemma csequent_not_not_true_ex {o} :
  forall lib (S : @csequent o),
    csequent_not_not_true lib S
    <=>
    forall s1 s2,
      match destruct_csequent S with
        | cseq_comps H T wh wt ct ec =>
              hyps_functionality lib s1 H
              -> similarity lib s1 s2 H
              -> {pC1 : cover_vars T s1
                  & {pC2 : cover_vars T s2
                     & !!tequality lib (lsubstc T wt s1 pC1) (lsubstc T wt s2 pC2)
                       #
                       match ec with
                         | Some (existT ext (we, ce)) =>
                             {pt1 : cover_vars ext s1
                               & {pt2 : cover_vars ext s2
                                  & !!equality lib (lsubstc ext we s1 pt1)
                                               (lsubstc ext we s2 pt2)
                                               (lsubstc T wt s1 pC1)}}
                         | None => True
                       end}}
      end.
Proof.
  introv; unfold csequent_not_not_true; split; intro h;
  destruct (destruct_csequent S) as [? ? ? ? ? opt]; destruct opt;
  exrepnd; introv hf.

  - intro sim.
    pose proof (h s2 s3 sim hf) as hyp.

    exists (s_cover_typ1 lib T s2 s3 hs ct sim)
           (s_cover_typ2 lib T s2 s3 hs ct sim); sp.
    exists (s_cover_ex1 lib t s2 s3 hs s0 sim)
           (s_cover_ex2 lib t s2 s3 hs s0 sim); sp.

  - intro sim.
    pose proof (h s1 s2 sim hf) as hyp.

    exists (s_cover_typ1 lib T s1 s2 hs ct sim)
           (s_cover_typ2 lib T s1 s2 hs ct sim); sp.

  - pose proof (h s2 s3 hf p) as hyp; exrepnd.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt1); auto.
    rewrite lsubstc_replace with (w2 := s1) (p2 := pt2); auto.

  - generalize (h s1 s2 hf p); intro hyp; exrepnd.

    rewrite lsubstc_replace with (w2 := wt) (p2 := pC1); auto.
    rewrite lsubstc_replace with (w2 := wt) (p2 := pC2); auto.
Qed.

Lemma weak_consistency2 {o} :
  forall lib (t : @NTerm o),
    wf_term t
    -> !rule_not_not_true lib (mk_rule (mk_baresequent [] (mk_concl mk_false t)) [] []).
Proof.
  introv wft rt; unfold rule_not_not_true in rt; allsimpl.

  repeat (autodimp rt hyp); tcsp.
  { unfold pwf_sequent, wf_sequent, closed_type_baresequent, closed_type, wf_concl; simpl.
    dands; eauto 3 with slow. }

  unfold sequent_not_not_true in rt; exrepnd.
  rw @csequent_not_not_true_ex in rt0.
  pose proof (rt0 [] []) as h; clear rt0; allsimpl.
  repeat (autodimp h hyp); eauto 3 with slow.
  exrepnd; allsimpl.
  allrewrite @lsubstc_mk_false.
  proof_irr.
  destruct h1; intro e.
  allapply @equality_refl.
  allapply @false_not_inhabited; sp.
Qed.

(* !!MOVE *)
Lemma inhabited_type_not {o} :
  forall lib (T : @CTerm o),
    inhabited_type lib (mkc_not T) <=> (!inhabited_type lib T # type lib T).
Proof.
  introv.
  unfold inhabited_type; split; introv h; exrepnd.
  - allrw @equality_in_not; repnd; dands; auto.
  - exists (@mkc_lam o nvarx (mkc_var nvarx)).
    allrw @equality_in_not; dands; auto.
Qed.

Definition rule_squash_if_not_not {o}
           (T e : NTerm)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_squash T)))
    [ mk_baresequent H (mk_concl (mk_not (mk_not T)) e)
    ]
    [].

Lemma rule_squash_if_not_not_not_not_true {o} :
  forall lib
         (T e : @NTerm o)
         (H : barehypotheses),
  rule_not_not_true lib (rule_squash_if_not_not T e H).
Proof.
  unfold rule_squash_if_not_not, rule_not_not_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [wf1 hyp1].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.

  assert (wf_term T) as wfT.
  { clear hyp1; allrw @wf_not; auto. }

  assert (wf_sequent (mk_baresequent H (mk_conclax (mk_squash T)))) as wfs.
  { split; simpl; auto.
    split; simpl; eauto 3 with slow.
    apply wf_squash; auto. }

  assert (closed_type H (mk_conclax (mk_squash T))) as clt.
  { unfold closed_type; simpl.
    clear hyp1.
    allrw @covered_mk_not; auto. }

  assert (closed_extract H (mk_conclax (mk_squash T))) as cle.
  { unfold closed_extract; simpl; auto. }

  exists (wfs,(clt,cle)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  unfold csequent_not_not_true; simpl; intros s1 s2 sim hf.

  lsubst_tac.
  rw @tequality_mkc_squash.
  rw @equality_in_mkc_squash.

  rw @csequent_not_not_true_ex in hyp1; simpl in hyp1.
  pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
  lsubst_tac.
  allrw @tequality_not.
  dands; auto.

  allrw @equality_in_not.
  allrw @inhabited_type_not.
  intro k.
  destruct h1; intro q; repnd.
  destruct h0; intro j.
  applydup @tequality_refl in j.
  destruct q; dands; auto; intro q.
  destruct k; dands; auto; spcast; apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma rule_true_implies_rule_not_not_true {o} :
  forall lib (R : @rule o),
    rule_true lib R -> rule_not_not_true lib R.
Proof.
  introv rt pwf args imp.
  apply rule_true_iff_rule_true2 in rt.
  unfold rule_true2 in rt.
  repeat (autodimp rt hyp).
  - introv i; apply imp in i.
(* No way we can prove that constructively *)
Abort.

Definition rule_choice {o}
           (A B : NTerm)
           (x : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_squash (mk_function A x B))))
    [ mk_baresequent (snoc H (mk_hyp x A)) (mk_conclax (mk_squash B)),
      mk_baresequent H (mk_conclax (mk_member A (mk_uni i)))
    ]
    [].

Lemma rule_choice_not_not_true {o} :
  forall lib
         (A B : @NTerm o)
         (x : NVar)
         (i : nat)
         (H : barehypotheses),
  rule_not_not_true lib (rule_choice A B x i H).
Proof.
  unfold rule_choice, rule_not_not_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destseq; allsimpl; proof_irr; GC.

(*
  assert (wf_term T) as wfT.
  { clear hyp1; allrw @wf_not; auto. }
*)

  assert (wf_sequent (mk_baresequent H (mk_conclax (mk_squash (mk_function A x B))))) as wfs.
  { clear hyp1 hyp2.
    allrw @vswf_hypotheses_snoc; repnd.
    split; simpl; auto.
    split; simpl; eauto 3 with slow.
    allrw @wf_squash.
    allrw @wf_member_iff2; repnd.
    apply wf_function; auto. }

  assert (closed_type H (mk_conclax (mk_squash (mk_function A x B)))) as clt.
  { clear hyp1 hyp2.
    unfold closed_type; simpl.
    allrw @covered_mk_squash.
    allrw @covered_equality; repnd.
    allrw @vars_hyps_snoc; allsimpl.
    apply covered_function; dands; auto.
    eapply covered_subvars;[|exact ct0].
    rw subvars_prop; introv k; simpl; allrw in_snoc; sp. }

  assert (closed_extract H (mk_conclax (mk_squash (mk_function A x B)))) as cle.
  { unfold closed_extract; simpl; auto. }

  exists (wfs,(clt,cle)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  unfold csequent_not_not_true; simpl; intros s1 s2 sim hf.

  lsubst_tac.
  rw @tequality_mkc_squash.
  rw @equality_in_mkc_squash.

  rw @csequent_not_not_true_ex in hyp1; simpl in hyp1.

(*
  pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
  lsubst_tac.
  allrw @tequality_not.
  dands; auto.

  allrw @equality_in_not.
  allrw @inhabited_type_not.
  intro k.
  destruct h1; intro q; repnd.
  destruct h0; intro j.
  applydup @tequality_refl in j.
  destruct q; dands; auto; intro q.
  destruct k; dands; auto; spcast; apply computes_to_valc_refl; eauto 3 with slow.
*)

Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
