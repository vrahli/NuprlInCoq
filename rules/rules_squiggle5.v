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


  Websites: http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export sequents2.
Require Export sequents_tacs.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export lsubst_hyps.
Require Export per_can.
Require Export per_props_atom.
Require Export per_props_nat.
Require Export cequiv_util.


(*
   H |- a = b in Base

     By EqualInBase

     H |- a ~ b
     forall v in (free_vars a), H |- v in Base

 *)

Definition rule_equal_in_base_concl {o} (a b : @NTerm o) H :=
  mk_baresequent H (mk_conclax (mk_equality a b mk_base)).

Definition rule_equal_in_base_hyp1 {o} (a b : @NTerm o) H :=
  mk_baresequent H (mk_conclax (mk_cequiv a b)).

Definition rule_equal_in_base_hyp2 {o} (v : NVar) (H : @bhyps o) :=
  mk_baresequent H (mk_conclax (mk_member (mk_var v) mk_base)).

Definition rule_equal_in_base_rest {o} (a : @NTerm o) (H : @bhyps o) :=
  map (fun v => rule_equal_in_base_hyp2 v H)
      (free_vars a).

Definition rule_equal_in_base {o}
           (H : barehypotheses)
           (a b : @NTerm o)
  :=
    mk_rule
      (rule_equal_in_base_concl a b H)
      (rule_equal_in_base_hyp1 a b H :: rule_equal_in_base_rest a H)
      [].

Lemma rule_equal_in_base_true3 {o} :
  forall lib (H : barehypotheses)
         (a b : @NTerm o),
    rule_true3 lib (rule_equal_in_base H a b).
Proof.
  unfold rule_equal_in_base, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (rule_equal_in_base_concl a b H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.

  teq_and_eq (@mk_base o) a b s1 s2 H; eauto 3 with slow.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 hf sim) as hyp; clear hyp1; exrepnd.
  lsubst_tac.
  allrw <- @member_equality_iff.
  allrw <- @member_cequiv_iff.
  apply tequality_mkc_cequiv in hyp0.
  applydup hyp0 in hyp1; clear hyp0; spcast.
  spcast.
  apply equality_in_base_iff; spcast.
  eapply cequivc_trans;[|eauto].

  clear dependent b.

  pose proof (lsubstc_csub_filter_free_vars a w1 s1 ca1) as e1; exrepnd; rw e0; clear e0.
  pose proof (lsubstc_csub_filter_free_vars a w1 s2 c1) as e2; exrepnd; rw e0; clear e0.

  apply cequivc_lsubstc; try (apply isprogram_csubst; eauto 3 with slow).
  apply implies_cequiv_csub_if_eq_doms; auto.

  { rw @dom_csub_csub_keep.
    apply implies_no_repeats_lkeep.
    apply similarity_dom in sim; repnd.
    rw sim0.
    eapply vswf_hypotheses_implies_no_repeats; eauto. }

  { allrw @dom_csub_csub_keep.
    apply similarity_dom in sim; repnd.
    rw sim0; rw sim; auto. }

  { introv e1 e2.
    rw @csub_find_csub_keep in e1.
    rw @csub_find_csub_keep in e2.
    boolvar; ginv.
    pose proof (hyps (mk_baresequent H (mk_conclax (mk_member (mk_var v) mk_base)))) as hyp.
    autodimp hyp h.

    { rw in_map_iff; eexists; dands; eauto. }

    destruct hyp as [ws hyp].
    destseq; allsimpl; proof_irr; GC.
    vr_seq_true in hyp.
    pose proof (hyp s1 s2 hf sim) as hyp0; clear hyp; exrepnd.
    lsubst_tac.
    clear hyp0.
    apply tequality_mkc_member_base in hyp1; spcast.
    apply cequiv_stable in hyp1.
    repeat (erewrite lsubstc_mk_var_if_csub_find in hyp1;[|eauto]).
    auto. }
Qed.

Lemma rule_equal_in_base_true {o} :
  forall lib (H : barehypotheses)
         (a b : @NTerm o),
    rule_true lib (rule_equal_in_base H a b).
Proof.
  introv.
  apply rule_true3_implies_rule_true; auto.
  apply rule_equal_in_base_true3; auto.
Qed.

Lemma rule_equal_in_base_true2 {o} :
  forall lib (H : barehypotheses)
         (a b : @NTerm o),
    rule_true2 lib (rule_equal_in_base H a b).
Proof.
  introv.
  apply rule_true_iff_rule_true2; auto.
  apply rule_equal_in_base_true; auto.
Qed.

Lemma rule_equal_in_base_wf2 {o} :
  forall (H : barehypotheses) (a b : @NTerm o),
    wf_rule2 (rule_equal_in_base H a b).
Proof.
  introv wf i.

  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq; auto;
  unfold rule_equal_in_base_rest in i; rw in_map_iff in i; exrepnd; subst; allsimpl; auto.
  unfold covered; simpl.
  allunfold @covered.
  allrw subvars_eq.
  repeat (rw subset_cons_l); dands; auto.
Qed.



(* same as above but we don't force the subgoals to have given extracts *)

Definition rule_equal_in_base2_hyp1 {o} (a b : @NTerm o) e H :=
  mk_baresequent H (mk_concl (mk_cequiv a b) e).

Definition rule_equal_in_base2_hyp2 {o} (v : NVar) e (H : @bhyps o) :=
  mk_baresequent H (mk_concl (mk_member (mk_var v) mk_base) e).

Definition rule_equal_in_base2_rest {o}
           (a : @NTerm o)
           (F : forall v (i : LIn v (free_vars a)), @NTerm o)
           (H : @bhyps o) :=
  mapin
    (free_vars a)
    (fun v i => rule_equal_in_base2_hyp2 v (F v i) H).

Definition rule_equal_in_base2 {o}
           (H : barehypotheses)
           (a b : @NTerm o)
           (e : NTerm)
           (F : forall v (i : LIn v (free_vars a)), @NTerm o)
  :=
    mk_rule
      (rule_equal_in_base_concl a b H)
      (rule_equal_in_base2_hyp1 a b e H :: rule_equal_in_base2_rest a F H)
      [].

Lemma rule_equal_in_base2_true3 {o} :
  forall lib (H : barehypotheses)
         (a b : @NTerm o) e F,
    rule_true3 lib (rule_equal_in_base2 H a b e F).
Proof.
  unfold rule_equal_in_base2, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (rule_equal_in_base_concl a b H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.

  teq_and_eq (@mk_base o) a b s1 s2 H; eauto 3 with slow.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 hf sim) as hyp; clear hyp1; exrepnd.
  lsubst_tac.
  allrw <- @member_equality_iff.
  allrw @equality_in_mkc_cequiv; repnd.
  apply tequality_mkc_cequiv in hyp0.
  applydup hyp0 in hyp1; clear hyp0; spcast.
  spcast.
  apply equality_in_base_iff; spcast.
  eapply cequivc_trans;[|eauto].

  clear dependent b.

  pose proof (lsubstc_csub_filter_free_vars a w1 s1 ca1) as e1; exrepnd; rw e0; clear e0.
  pose proof (lsubstc_csub_filter_free_vars a w1 s2 c1) as e2; exrepnd; rw e0; clear e0.

  apply cequivc_lsubstc; try (apply isprogram_csubst; eauto 3 with slow).
  apply implies_cequiv_csub_if_eq_doms; auto.

  { rw @dom_csub_csub_keep.
    apply implies_no_repeats_lkeep.
    apply similarity_dom in sim; repnd.
    rw sim0.
    eapply vswf_hypotheses_implies_no_repeats; eauto. }

  { allrw @dom_csub_csub_keep.
    apply similarity_dom in sim; repnd.
    rw sim0; rw sim; auto. }

  { introv e1 e2.
    rw @csub_find_csub_keep in e1.
    rw @csub_find_csub_keep in e2.
    boolvar; ginv.
    pose proof (hyps (mk_baresequent H (mk_concl (mk_member (mk_var v) mk_base) (F v Heqb)))) as hyp.
    autodimp hyp h.

    { unfold rule_equal_in_base2_rest.
      apply in_mapin.
      eexists; eexists.
      unfold rule_equal_in_base2_hyp2; eauto. }

    destruct hyp as [ws hyp].
    destseq; allsimpl; proof_irr; GC.
    vr_seq_true in hyp.
    pose proof (hyp s1 s2 hf sim) as hyp0; clear hyp; exrepnd.
    lsubst_tac.
    clear hyp0.
    apply tequality_mkc_member_base in hyp1; spcast.
    apply cequiv_stable in hyp1.
    repeat (erewrite lsubstc_mk_var_if_csub_find in hyp1;[|eauto]).
    auto. }
Qed.

Lemma rule_equal_in_base2_true {o} :
  forall lib (H : barehypotheses)
         (a b : @NTerm o) e F,
    rule_true lib (rule_equal_in_base2 H a b e F).
Proof.
  introv.
  apply rule_true3_implies_rule_true; auto.
  apply rule_equal_in_base2_true3; auto.
Qed.

Lemma rule_equal_in_base2_true2 {o} :
  forall lib (H : barehypotheses)
         (a b : @NTerm o) e F,
    rule_true2 lib (rule_equal_in_base2 H a b e F).
Proof.
  introv.
  apply rule_true_iff_rule_true2; auto.
  apply rule_equal_in_base2_true; auto.
Qed.

Lemma rule_equal_in_base2_wf2 {o} :
  forall (H : barehypotheses) (a b : @NTerm o) e F,
    wf_rule2 (rule_equal_in_base2 H a b e F).
Proof.
  introv wf i.

  allsimpl; repdors; sp; subst; allunfold @wf_bseq; wfseq; auto;
  unfold rule_equal_in_base_rest in i; apply in_mapin in i; exrepnd; subst; allsimpl; auto.
  unfold covered; simpl.
  allunfold @covered.
  allrw subvars_eq.
  repeat (rw subset_cons_l); dands; auto.
Qed.




(*
   H |- a = b in Base

     By AtomSubtypeBase

     H |- a = b in Atom

 *)
Definition rule_atom_subtype_base {o}
           (H : barehypotheses)
           (a b : @NTerm o)
  :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_equality a b mk_base)))
      [mk_baresequent H (mk_conclax (mk_equality a b mk_atom))]
      [].

Lemma rule_atom_subtype_base_true {o} :
  forall lib (H : barehypotheses)
         (a b : @NTerm o),
    rule_true lib (rule_atom_subtype_base H a b).
Proof.
  unfold rule_atom_subtype_base, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.

  teq_and_eq (@mk_base o) a b s1 s2 H; eauto 3 with slow.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 hf sim) as hyp; clear hyp1; exrepnd.
  lsubst_tac.
  allrw <- @member_equality_iff.
  apply equality_commutes in hyp0; auto; clear hyp1.
  apply equality_in_atom_iff in hyp0; exrepnd; spcast.
  apply equality_in_base_iff; spcast.
  eapply cequivc_trans;
    [apply computes_to_valc_implies_cequivc;eauto|].
  eapply cequivc_trans;
    [|apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto].
  apply cequivc_refl.
Qed.


(*
   H |- a = b in Base

     By UAtomSubtypeBase

     H |- a = b in UAtom

 *)
Definition rule_uatom_subtype_base {o}
           (H : barehypotheses)
           (a b : @NTerm o)
  :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_equality a b mk_base)))
      [mk_baresequent H (mk_conclax (mk_equality a b mk_uatom))]
      [].

Lemma rule_uatom_subtype_base_true {o} :
  forall lib (H : barehypotheses)
         (a b : @NTerm o),
    rule_true lib (rule_uatom_subtype_base H a b).
Proof.
  unfold rule_uatom_subtype_base, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.

  teq_and_eq (@mk_base o) a b s1 s2 H; eauto 3 with slow.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 hf sim) as hyp; clear hyp1; exrepnd.
  lsubst_tac.
  allrw <- @member_equality_iff.
  apply equality_commutes in hyp0; auto; clear hyp1.
  apply equality_in_uatom_iff in hyp0; exrepnd; spcast.
  apply equality_in_base_iff; spcast.
  eapply cequivc_trans;
    [apply computes_to_valc_implies_cequivc;eauto|].
  eapply cequivc_trans;
    [|apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto].
  apply cequivc_refl.
Qed.

(*
   H |- a = b in Base

     By IntSubtypeBase

     H |- a = b in Int

 *)
Definition rule_int_subtype_base {o}
           (H : barehypotheses)
           (a b : @NTerm o)
  :=
    mk_rule
      (mk_baresequent H (mk_conclax (mk_equality a b mk_base)))
      [mk_baresequent H (mk_conclax (mk_equality a b mk_int))]
      [].

Lemma rule_int_subtype_base_true {o} :
  forall lib (H : barehypotheses)
         (a b : @NTerm o),
    rule_true lib (rule_int_subtype_base H a b).
Proof.
  unfold rule_int_subtype_base, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  clear cargs.

  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.
  lsubst_tac.
  allrw <- @member_equality_iff.

  teq_and_eq (@mk_base o) a b s1 s2 H; eauto 3 with slow.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 hf sim) as hyp; clear hyp1; exrepnd.
  lsubst_tac.
  allrw <- @member_equality_iff.
  apply equality_commutes in hyp0; auto; clear hyp1.
  apply equality_in_int_implies_cequiv in hyp0.
  apply equality_in_base_iff; spcast; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
