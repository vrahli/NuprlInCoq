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


Require Export rules_useful.
Require Export subst_tacs_aeq.
Require Export subst_tacs3.
Require Export cequiv_tacs.
Require Export cequiv_props3.
Require Export per_props_qnat.
Require Export per_props_nat2.
Require Export per_props_cs.
Require Export fresh_cs.
Require Export sequents_equality.
Require Export sequents_tacs2.
Require Export rules_tyfam.
Require Export lsubst_hyps.
Require Export terms_pi.



Lemma implies_cequivc_last_cs {o} :
  forall lib (a b u v : @CTerm o),
    cequivc lib a b
    -> cequivc lib u v
    -> cequivc lib (mkc_last_cs a u) (mkc_last_cs b v).
Proof.
  unfold cequivc; introv ceqa ceqb; destruct_cterms; simpl in *.
  repnud ceqa.
  repnud ceqb.
  split; apply approx_congruence; fold_terms;
    try (apply implies_isprogram_last_cs; apply isprog_implies; auto).

  { unfold lblift; simpl; dands; auto; introv w.
    repeat (destruct n; try omega); unfold selectbt; simpl;
      apply blift_approx_open_nobnd2; eauto 2 with slow. }

  { unfold lblift; simpl; dands; auto; introv w.
    repeat (destruct n; try omega); unfold selectbt; simpl;
      apply blift_approx_open_nobnd2; eauto 2 with slow. }
Qed.

Lemma implies_ccequivc_ext_last_cs {o} :
  forall lib (a b u v : @CTerm o),
    ccequivc_ext lib a b
    -> ccequivc_ext lib u v
    -> ccequivc_ext lib (mkc_last_cs a u) (mkc_last_cs b v).
Proof.
  introv ceqa ceqb ext; applydup ceqa in ext; applydup ceqb in ext; spcast.
  apply implies_cequivc_last_cs; auto.
Qed.

Lemma last_cs_entry_implies_in {o} :
  forall vals (v : @ChoiceSeqVal o),
    last_cs_entry vals = Some v -> LIn v vals.
Proof.
  induction vals; introv h; simpl in *; tcsp.
  destruct vals; ginv; tcsp.
Qed.

Lemma in_implies_select :
  forall {A} (a : A) l,
    LIn a l -> {n : nat & select n l = Some a}.
Proof.
  induction l; introv i; simpl in *; tcsp.
  repndors; subst; tcsp.
  { exists 0; simpl; tcsp. }
  { apply IHl in i; exrepnd.
    exists (S n); simpl; tcsp. }
Qed.

Lemma is_nat_mkc_nat {o} :
  forall n i, @is_nat o n (mkc_nat i).
Proof.
  introv; unfold is_nat; eexists; eauto.
Qed.
Hint Resolve is_nat_mkc_nat : slow.

Lemma compatible_cs_kind_0_implies_is_nat_restriction {o} :
  forall name (restr : @ChoiceSeqRestriction o) vals v,
    compatible_cs_kind 0 (csn_kind name)
    -> correct_restriction name restr
    -> LIn v vals
    -> choice_sequence_satisfies_restriction vals restr
    -> {n : nat & is_nat n v}.
Proof.
  introv comp cor iv sat.
  unfold correct_restriction in *.
  unfold compatible_cs_kind in *; boolvar; tcsp; GC.
  destruct name as [nm kd]; simpl in *.
  destruct kd; subst; boolvar; tcsp; GC.

  {
    unfold is_nat_restriction in *.
    unfold choice_sequence_satisfies_restriction in *.
    destruct restr; repnd; dands; tcsp.
    apply in_implies_select in iv; exrepnd.
    apply sat in iv0; apply cor in iv0; exists n; auto.
  }

  {
    unfold is_nat_seq_restriction in *.
    unfold choice_sequence_satisfies_restriction in *.
    destruct restr; repnd; dands; tcsp.
    apply in_implies_select in iv; exrepnd.
    exists n.
    applydup sat in iv0.
    destruct (lt_dec n (length l)).
    { apply cor2 in iv1; auto.
      unfold cterm_is_nth in iv1; exrepnd; exrepnd.
      pose proof (cor2 n v) as q; autodimp q hyp; subst; eauto 2 with slow. }
    { apply cor in iv1; auto; try omega. }
  }
Qed.

Lemma compatible_cs_kind_0_implies_find_nat {o} :
  forall (lib : @library o) name e v,
    compatible_cs_kind 0 (csn_kind name)
    -> safe_library lib
    -> find_cs lib name = Some e
    -> last_cs_entry e = Some v
    -> exists (n : nat), CSVal2term v = mk_nat n.
Proof.
  introv comp safe find lcs.
  assert (entry_in_library (lib_cs name e) lib) as i by eauto 2 with slow.
  clear find.
  apply safe in i; simpl in *.
  destruct e as [vals restr]; simpl in *; repnd.
  apply last_cs_entry_implies_in in lcs.
  eapply compatible_cs_kind_0_implies_is_nat_restriction in comp; eauto; exrepnd.
  unfold is_nat in comp0; exrepnd; subst.
  exists i1; simpl; auto.
Qed.

Lemma in_ext_exists_ccomputes_to_valc_mkc_last_cs_choice_seq {o} :
  forall (lib : @library o) name k,
    safe_library lib
    -> compatible_choice_sequence_name 0 name
    -> in_ext lib (fun lib => exists n, ccomputes_to_valc lib (mkc_last_cs (mkc_choice_seq name) (mkc_nat k)) (mkc_nat n)).
Proof.
  introv safe comp ext.

  assert (compute_step lib' (mk_last_cs (mk_choice_seq name) (mk_nat k)) = csuccess (find_last_entry_default lib' name (mk_nat k))) as w.
  { csunf; simpl; auto. }

  assert (exists (n : nat), find_last_entry_default lib' name (mk_nat k) = mk_nat n) as z.
  {
    unfold find_last_entry_default.
    remember (find_cs lib' name) as fcs; symmetry in Heqfcs; destruct fcs;[|eexists; eauto].
    remember (last_cs_entry c) as lcs; symmetry in Heqlcs; destruct lcs;[|eexists; eauto].
    unfold compatible_choice_sequence_name in *.
    eapply compatible_cs_kind_0_implies_find_nat in Heqfcs; eauto; eauto 3 with slow.
  }

  exrepnd.
  exists n.
  rewrite z0 in w; clear z0.
  spcast.
  unfold computes_to_valc, computes_to_value; simpl; dands; eauto 2 with slow.
Qed.
Hint Resolve in_ext_exists_ccomputes_to_valc_mkc_last_cs_choice_seq : slow.

Lemma exists_ccomputes_to_valc_mkc_last_cs_choice_seq {o} :
  forall (lib : @library o) name k,
    safe_library lib
    -> compatible_choice_sequence_name 0 name
    -> exists n, ccomputes_to_valc lib (mkc_last_cs (mkc_choice_seq name) (mkc_nat k)) (mkc_nat n).
Proof.
  introv safe comp.

  assert (compute_step lib (mk_last_cs (mk_choice_seq name) (mk_nat k)) = csuccess (find_last_entry_default lib name (mk_nat k))) as w.
  { csunf; simpl; auto. }

  assert (exists (n : nat), find_last_entry_default lib name (mk_nat k) = mk_nat n) as z.
  {
    unfold find_last_entry_default.
    remember (find_cs lib name) as fcs; symmetry in Heqfcs; destruct fcs;[|eexists; eauto].
    remember (last_cs_entry c) as lcs; symmetry in Heqlcs; destruct lcs;[|eexists; eauto].
    unfold compatible_choice_sequence_name in *.
    eapply compatible_cs_kind_0_implies_find_nat in Heqfcs; eauto; eauto 3 with slow.
  }

  exrepnd.
  exists n.
  rewrite z0 in w; clear z0.
  spcast.
  unfold computes_to_valc, computes_to_value; simpl; dands; eauto 2 with slow.
Qed.
Hint Resolve exists_ccomputes_to_valc_mkc_last_cs_choice_seq : slow.

Lemma in_ext_exists_ccomputes_to_valc_nat {o} :
  forall (lib : @library o) k,
    in_ext lib (fun lib => exists n, ccomputes_to_valc lib (mkc_nat k) (mkc_nat n)).
Proof.
  introv ext; exists k; spcast; eauto 3 with slow.
Qed.
Hint Resolve in_ext_exists_ccomputes_to_valc_nat : slow.

Lemma equality_nat_in_qnat {o} :
  forall (lib : @library o) k, equality lib (mkc_nat k) (mkc_nat k) mkc_qnat.
Proof.
  introv.
  apply equality_in_qnat; eauto 2 with slow.
  apply in_ext_implies_all_in_ex_bar; introv xt.
  unfold equality_of_qnat.
  dands; eexists; spcast; eauto 3 with slow.
Qed.
Hint Resolve equality_nat_in_qnat : slow.




(**

<<
   H |- mk_last_cs(f,d) ∈ ℕ\\True

     By RefWf

     H |- f ∈ Free(0)
     H |- d ∈ ℕ
>>

 *)


Definition rule_ref_wf {o}
           (lib   : @library o)
           (f d   : NTerm)
           (e1 e2 : NTerm)
           (H     : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member (mk_last_cs f d) mk_qnat)))
    [mk_baresequent H (mk_concl (mk_member f (mk_csname 0)) e1),
     mk_baresequent H (mk_concl (mk_member d mk_tnat) e2)]
    [].

Lemma rule_ref_wf_true {o} :
  forall lib (f d e1 e2 : NTerm) (H : @bhyps o) (safe : safe_library lib),
    rule_true lib (rule_ref_wf lib f d e1 e2 H).
Proof.
  unfold rule_ref_wf, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (@covered o mk_axiom (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp. }
  exists cv.

  (* pick a fresh choice sequence name, and define a constraint based on [hyp1] and [hyp2] *)

  vr_seq_true.
  lsubst_tac.

  rw <- @member_member_iff.
  pose proof (teq_and_member_if_member
                lib' mk_qnat (mk_last_cs f d) s1 s2 H wT wt ct1 ct2 cT cT0) as q.
  lsubst_tac.
  repeat (autodimp q hyp); eauto 2 with slow.

  clear dependent s1.
  clear dependent s2.
  introv eqh sim.

  vr_seq_true in hyp1.
  pose proof (hyp1 lib' ext s1 s2 eqh sim) as hyp1; exrepnd.
  vr_seq_true in hyp2.
  pose proof (hyp2 lib' ext s1 s2 eqh sim) as hyp2; exrepnd.

  lsubst_tac.
  apply member_if_inhabited in hyp1.
  apply tequality_mkc_member_implies_sp in hyp0; auto;[].
  apply member_if_inhabited in hyp2.
  apply tequality_mkc_member_implies_sp in hyp3; auto;[].
  autorewrite with slow in *.

  clear hyp1 hyp2.
  apply equality_in_csname in hyp0.
  apply equality_in_tnat in hyp3.

  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens2;
    [|exact hyp0|exact hyp3]; clear hyp0 hyp3; introv y hyp0 hyp3.
  unfold equality_of_csname in hyp0; exrepnd.
  unfold equality_of_nat in hyp3; exrepnd.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in hyp1.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in hyp2.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in hyp3.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in hyp4.
  eapply equality_respects_cequivc_left; [apply ccequivc_ext_sym;apply implies_ccequivc_ext_last_cs;eauto|].
  eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym;apply implies_ccequivc_ext_last_cs;eauto|].

  apply equality_in_qnat.
  apply in_ext_implies_all_in_ex_bar; introv xt.

  assert (safe_library lib'1) as safe' by eauto 4 with slow.
  unfold equality_of_qnat.
  dands; eauto 3 with slow.
Qed.



(**

<<
   H |- n ∈ ℕ\\True

     By QNat_subtype Nat

     H |- n ∈ ℕ
>>

 *)


Definition rule_qnat_subtype_nat {o}
           (lib : @library o)
           (n   : NTerm)
           (e   : NTerm)
           (H   : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member n mk_qnat)))
    [mk_baresequent H (mk_concl (mk_member n mk_tnat) e)]
    [].

Lemma rule_qnat_subtype_nat_true {o} :
  forall lib (n e : NTerm) (H : @bhyps o) (safe : safe_library lib),
    rule_true lib (rule_qnat_subtype_nat lib n e H).
Proof.
  unfold rule_qnat_subtype_nat, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  assert (@covered o mk_axiom (nh_vars_hyps H)) as cv.
  { dwfseq; tcsp. }
  exists cv.

  (* pick a fresh choice sequence name, and define a constraint based on [hyp1] and [hyp2] *)

  vr_seq_true.
  lsubst_tac.

  rw <- @member_member_iff.
  pose proof (teq_and_member_if_member
                lib' mk_qnat n s1 s2 H wT wt ct0 ct1 cT cT0) as q.
  lsubst_tac.
  repeat (autodimp q hyp); eauto 2 with slow.

  clear dependent s1.
  clear dependent s2.
  introv eqh sim.

  vr_seq_true in hyp1.
  pose proof (hyp1 lib' ext s1 s2 eqh sim) as hyp1; exrepnd.

  lsubst_tac.
  apply member_if_inhabited in hyp1.
  apply tequality_mkc_member_implies_sp in hyp0; auto;[].
  autorewrite with slow in *.

  clear hyp1.
  apply equality_in_tnat in hyp0.

  apply all_in_ex_bar_equality_implies_equality.
  eapply all_in_ex_bar_modus_ponens1;[|exact hyp0]; clear hyp0; introv y hyp0.
  unfold equality_of_nat in hyp0; exrepnd.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in hyp0.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in hyp1.
  eapply equality_respects_cequivc_left; [apply ccequivc_ext_sym;eauto|].
  eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym;eauto|].
  eauto 3 with slow.
Qed.
