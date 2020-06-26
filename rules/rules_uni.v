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
(*Require Export sequents_lib.*)
Require Export sequents_tacs.
Require Export sequents_equality.
Require Export per_props_uni.
(*Require Export per_props_halts.*)


Definition rule_universe_equality_concl {o} (H : @bhyps o) u i j : baresequent :=
  mk_baresequent H (mk_conclax (mk_member (mk_uni u i) (mk_uni u j))).

(*
   H |- Type(i) = Type(i) in Type(j)

     By universeEquality (i < j)
 *)
Definition rule_universe_equality {o}
           (H : @bhyps o)
           (u i j : nat) :=
  mk_rule
    (rule_universe_equality_concl H u i j)
    []
    [].

Lemma rule_universe_equality_true3 {o} :
  forall u lib (H : @bhyps o) (i j : nat),
    i < j -> rule_true3 u lib (rule_universe_equality H u i j).
Proof.
  intros.
  unfold rule_universe_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs hyps.

  (* We prove the well-formedness of things *)
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (H) ||- (mk_conclax (mk_member (mk_uni u i) (mk_uni u j)))) as wfc.
  { unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  pose proof (teq_and_member_if_member u lib' (mk_uni u j) (mk_uni u i) s1 s2 H wT wt ct ct0 cT cT0) as q.
  rw <- @member_member_iff.
  lsubst_tac.
  apply q; eauto 3 with slow.
  clear dependent s1; clear dependent s2.
  introv hf sim.
  lsubst_tac.
  apply uni_in_uni; auto.
Qed.

(*Lemma rule_universe_equality_true_ext_lib {o} :
  forall lib (H : @bhyps o) (i j : nat),
    i < j -> rule_true_ext_lib lib (rule_universe_equality H i j).
Proof.
  introv ltij.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_universe_equality_true3; auto.
Qed.*)


Definition rule_cumulativity_concl {o} (H : @bhyps o) T u j :=
  mk_baresequent H (mk_conclax (mk_member T (mk_uni u j))).

Definition rule_cumulativity_hyp {o} (H : @bhyps o) T u i e :=
  mk_baresequent H (mk_concl (mk_member T (mk_uni u i)) e).

(*
   H |- T in Type(j)

     By cumulativity (i < j)

     H |- T in Type(i)
 *)
Definition rule_cumulativity {o}
           (H : @bhyps o)
           (T e : NTerm)
           (u i j : nat) :=
  mk_rule
    (rule_cumulativity_concl H T u j)
    [ rule_cumulativity_hyp H T u i e ]
    [].

Lemma rule_cumulativity_true3 {o} :
  forall u lib (H : @bhyps o) T e (i j : nat),
    i <= j -> rule_true3 u lib (rule_cumulativity H T e u i j).
Proof.
  intros.
  unfold rule_cumulativity, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (H) ||- (mk_conclax (mk_member T (mk_uni u j)))) as wfc.
  { clear hyp1.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp.
    introv xx; allrw in_app_iff; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw <- @member_member_iff.
  pose proof (teq_and_member_if_member u lib' (mk_uni u j) T s1 s2 H wT wt ct0 ct1 cT cT0) as q.
  lsubst_tac.
  apply q; auto.
  { apply tequality_mkc_uni. }
  clear dependent s1; clear dependent s2.

  introv hf sim.
  vr_seq_true in hyp1.
  pose proof (hyp1 _ ext s1 s2 hf sim) as q; clear hyp1; exrepnd.
  lsubst_tac.
  apply member_if_inhabited in q1.

  apply tequality_mkc_member_sp in q0; repnd; clear q2.
  apply all_in_ex_bar_equality_implies_equality.
  eapply in_open_bar_pres; try exact q0; clear q0; introv xt q0.
  repndors; spcast;
    [|eapply equality_respects_cequivc_right;[exact q0|] ];
    eapply cumulativity; eauto 3 with slow.
Qed.

(*Lemma rule_cumulativity_true_ext_lib {o} :
  forall lib (H : @bhyps o) T e (i j : nat),
    i <= j -> rule_true_ext_lib lib (rule_cumulativity H T e i j).
Proof.
  introv ltij.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_cumulativity_true3; auto.
Qed.*)

Lemma rule_cumulativity_wf2 {o} :
  forall u (H : @bhyps o) T e (i j : nat),
    wf_rule2 (rule_cumulativity H T e u i j).
Proof.
  introv wf k.
  allsimpl; repndors; subst; tcsp;
    allunfold @wf_bseq; repnd; allsimpl; wfseq.
Qed.
