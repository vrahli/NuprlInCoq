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



(* MOVE *)
Lemma sat_qnat_no_cond {o} :
  forall (lib : @library o) a,
    sat_qnat_cond lib qnat_no_cond a.
Proof.
  introv h; ginv.
Qed.
Hint Resolve sat_qnat_no_cond : slow.


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
    (mk_baresequent H (mk_conclax (mk_member (mk_last_cs f d) (mk_qnat qnat_no_cond))))
    [mk_baresequent H (mk_concl (mk_member f (mk_csname 0)) e1),
     mk_baresequent H (mk_concl (mk_member d mk_tnat) e2)]
    [].

Lemma rule_ref_wf_true {o} :
  forall uk (lib : library) (f d e1 e2 : NTerm) (H : @bhyps o) (safe : safe_library lib),
    rule_true uk lib (rule_ref_wf lib f d e1 e2 H).
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
  lsubst_tac; autorewrite with slow.

  rw <- @member_member_iff.
  pose proof (teq_and_member_if_member
                uk lib' (mk_qnat qnat_no_cond) (mk_last_cs f d) s1 s2 H wT wt ct1 ct2 cT cT0) as q.
  lsubst_tac; autorewrite with slow in q.
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

  split; eauto 3 with slow;[].
  introv xt'.
  assert (safe_library lib'1) as safea by eauto 4 with slow.
  assert (safe_library lib'2) as safeb by eauto 2 with slow.
  eapply exists_ccomputes_to_valc_mkc_last_cs_choice_seq in hyp0; try exact safeb; exrepnd.
  eexists; dands; spcast; eauto 3 with slow.
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
           (c   : qnat_cond)
           (n   : NTerm)
           (e   : NTerm)
           (H   : @bhyps o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_member n (mk_qnat c))))
    [mk_baresequent H (mk_concl (mk_member n mk_tnat) e)]
    [].

Lemma rule_qnat_subtype_nat_true {o} :
  forall uk (lib : library) c (n e : NTerm) (H : @bhyps o) (safe : safe_library lib),
    rule_true uk lib (rule_qnat_subtype_nat lib c n e H).
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
                uk lib' (mk_qnat c) n s1 s2 H wT wt ct0 ct1 cT cT0) as q.
  lsubst_tac; autorewrite with slow in *.
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
