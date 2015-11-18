(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


Require Export cequiv_bind.
Require Export sequents2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export per_props_equality.
Require Export per_can.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)





(* end hide *)

(**

  We now prove the truth of several rules about the approximation and
  computational equivalence types.

*)

(* [9] ============ CEQUIV REFL ============ *)

(**

  We can state the computational equivalence reflexivity rule as
  follows:
<<
   H |- a ~ a
     no subgoals
>>
 *)

Definition rule_cequiv_refl {o}
           (H  : @barehypotheses o)
           (a  : NTerm) :=
  mk_rule (mk_baresequent H (mk_conclax (mk_cequiv a a))) [] [].

Lemma rule_cequiv_refl_true {o} :
  forall lib (H  : @barehypotheses o) (a  : NTerm),
    rule_true lib (rule_cequiv_refl H a).
Proof.
  intros.
  unfold rule_cequiv_refl, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs hyps.

  assert (closed_extract H (mk_conclax (mk_cequiv a a))) as ce by prove_seq.

  exists ce.

  vr_seq_true.
  lift_lsubst.
  rw @member_eq.
  rw <- @member_cequiv_iff; sp;
  try (spcast; apply cequiv_refl; apply isprogram_get_cterm).
  apply equal_cequiv.
Qed.

(* begin hide *)

Lemma rule_cequiv_refl_true_ex {o} :
  forall lib H a, rule_true_if lib (@rule_cequiv_refl o H a).
Proof.
  intros.
  generalize (rule_cequiv_refl_true lib H a); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Lemma rule_cequiv_refl_true2 {o} :
  forall lib H a, rule_true2 lib (@rule_cequiv_refl o H a).
Proof.
  intros.
  generalize (rule_cequiv_refl_true lib H a); intro rt.
  apply rule_true_iff_rule_true2; sp.
Qed.



(* end hide *)

(* [10] ============ APPROX REFL ============ *)

(**

  We can state the approximation reflexivity rule as follows:
<<
   H |- a <= a
     no subgoals
>>
 *)

Definition rule_approx_refl_concl {o} a (H : @bhyps o) :=
  mk_baresequent H (mk_conclax (mk_approx a a)).

Definition rule_approx_refl {o}
           (H  : @barehypotheses o)
           (a  : NTerm) :=
  mk_rule (rule_approx_refl_concl a H) [] [].

Lemma rule_approx_refl_true3 {o} :
  forall lib (H : @bhyps o) (a  : NTerm),
    rule_true3 lib (rule_approx_refl H a).
Proof.
  intros.
  unfold rule_approx_refl, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs hyps.

  assert (closed_extract H (mk_conclax (mk_approx a a))) as ce by prove_seq.
  assert (wf_csequent (rule_approx_refl_concl a H)) as wfc by prove_seq.

  exists wfc.

  vr_seq_true.
  lift_lsubst.
  rw @member_eq.
  rw <- @member_approx_iff; sp;
  try (spcast; apply approx_refl; apply isprogram_get_cterm).
  apply equal_approx.
Qed.

Lemma rule_approx_refl_true {o} :
  forall lib (H : @bhyps o) (a  : NTerm),
    rule_true lib (rule_approx_refl H a).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_approx_refl_true3.
Qed.

Lemma rule_approx_refl_true2 {o} :
  forall lib (H  : @bhyps o) (a  : NTerm),
    rule_true2 lib (rule_approx_refl H a).
Proof.
  introv.
  apply rule_true_iff_rule_true2.
  apply rule_approx_refl_true.
Qed.

(* begin hide *)



(* end hide *)

(* [11] ============ CEQUIV INTENSIONAL EQUALITY (SIMPLE) ============ *)

(* In general we can say that all the hypotheses have to be in base *)

(**

  We can state the computational equivalence intensional equality rule
  as follows:

<<
   |- a ~ b = a ~ b in Type(i)

     By cequivIntensionalEquality (simple)
>>

*)

Definition rule_cequiv_intensional_equality_simple {o}
           (i : nat)
           (a b : @NTerm o) :=
  mk_rule
    (mk_baresequent []
                   (mk_conclax (mk_equality (mk_cequiv a b)
                                            (mk_cequiv a b)
                                            (mk_uni i))))
    []
    [].

Lemma rule_cequiv_intensional_equality_simple_true {o} :
  forall lib (i : nat)
         (a b : @NTerm o),
    rule_true lib (rule_cequiv_intensional_equality_simple i a b).
Proof.
  intros.
  unfold rule_cequiv_intensional_equality_simple, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs hyps.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.

  allunfold @closed_type; allunfold @closed_extract; allunfold @nh_vars_hyps; allsimpl.

  exists (@covered_axiom o []).

  (* Now we prove the rule *)
  vr_seq_true.
  lift_lsubst.
  rw @member_eq.
  rw <- @member_equality_iff.

  inversion sim; cpx; subst; clear_irr.

  sp.

  rw @tequality_mkc_equality; sp;
  try (apply tequality_mkc_uni);
  try (complete (right; spcast; apply cequiv_refl; apply isprogram_get_cterm)).

  rw @mkc_cequiv_equality_in_uni; sp.
Qed.

(* begin hide *)

Lemma rule_cequiv_intensional_equality_simple_true_ex {o} :
  forall lib i a b,
    rule_true_if lib (@rule_cequiv_intensional_equality_simple o i a b).
Proof.
  intros.
  generalize (rule_cequiv_intensional_equality_simple_true lib i a b); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.



(* end hide *)

(* [12] ============ APPROX INTENSIONAL EQUALITY (SIMPLE) ============ *)

(* In general we can say that all the hypotheses have to be in base *)

(**

  We can state the approximation intensional equality rule as follows:
<<
   |- a <= b = a <= b in Type(i)

     By approxIntensionalEquality (simple)
>>
*)

Definition rule_approx_intensional_equality_simple {o}
           (i : nat)
           (a b : @NTerm o) :=
  mk_rule
    (mk_baresequent []
                   (mk_conclax (mk_equality (mk_approx a b)
                                            (mk_approx a b)
                                            (mk_uni i))))
    []
    [].

Lemma rule_approx_intensional_equality_simple_true {o} :
  forall lib (i : nat)
         (a b : @NTerm o),
    rule_true lib (rule_approx_intensional_equality_simple i a b).
Proof.
  intros.
  unfold rule_approx_intensional_equality_simple, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs hyps.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.

  allunfold @closed_type; allunfold @closed_extract; allunfold @nh_vars_hyps; allsimpl.

  exists (@covered_axiom o []).

  (* Now we prove the rule *)
  vr_seq_true.
  lift_lsubst.
  rw @member_eq.
  rw <- @member_equality_iff.

  inversion sim; cpx; subst; clear_irr.

  sp.

  rw @tequality_mkc_equality; sp;
  try (apply tequality_mkc_uni);
  try (complete (right; spcast; apply cequiv_refl; apply isprogram_get_cterm)).

  rw @mkc_approx_equality_in_uni; sp.
Qed.

(* begin hide *)

Lemma rule_approx_intensional_equality_simple_true_ex {o} :
  forall lib i a b,
    rule_true_if lib (@rule_approx_intensional_equality_simple o i a b).
Proof.
  intros.
  generalize (rule_approx_intensional_equality_simple_true lib i a b); intro rt.
  rw <- @rule_true_eq_ex in rt.
  unfold rule_true_ex in rt; sp.
Qed.

Lemma rule_approx_intensional_equality_simple_true2 {o} :
  forall lib i a b,
    rule_true2 lib(@rule_approx_intensional_equality_simple o i a b).
Proof.
  intros.
  generalize (rule_approx_intensional_equality_simple_true lib i a b); intro rt.
  apply rule_true_iff_rule_true2; auto.
Qed.

Lemma rule_approx_intensional_equality_simple_wf {o} :
  forall i a b,
    wf_rule (@rule_approx_intensional_equality_simple o i a b).
Proof.
  intros.
  introv pwf m.
  allsimpl; sp.
Qed.



(* end hide *)

(* [22] ============ CEQUIV BASE ============ *)

(**

  The following rule says that to prove that [a] is computationally
  equivalent to [b] it is enough to prove that they are equal in
  [Base]:
<<
   H |- a ~ b
     H |- a = b in Base
>>
 *)
Definition rule_cequiv_base {o}
           (H   : @barehypotheses o)
           (a b : NTerm) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_cequiv a b)))
    [ mk_baresequent H (mk_conclax (mk_equality a b mk_base))
    ]
    [].

Lemma rule_cequiv_base_true {o} :
  forall lib (H : @barehypotheses o) (a b : NTerm),
    rule_true lib (rule_cequiv_base H a b).
Proof.
  unfold rule_cequiv_base, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent H (mk_conclax (mk_equality a b mk_base)))
                   (inl eq_refl));
    simpl; intros hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  assert (closed_extract H (mk_conclax (mk_cequiv a b))) as cs.
  clear hyp1.
  dwfseq; prove_seq; unfold covered; allrw subvars_prop; sp.

  exists cs.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  allrw @equality_in_base_iff.
  rw <- @member_cequiv_iff.
  sp.
  rw @tequality_mkc_cequiv.
  allrw @tequality_mkc_equality_base_iff; repnd.
  split; sp; spcast; allunfold @cequivc.
  apply @cequiv_trans with (b := get_cterm (lsubstc a w1 s1 c1)); auto.
  apply cequiv_sym; auto.
  apply @cequiv_trans with (b := get_cterm (lsubstc b w2 s1 c2)); auto.
Qed.

(* begin hide *)

(* !! MOVE *)
Lemma cequivc_iff_approxc {o} :
  forall lib (a b : @CTerm o),
    cequivc lib a b <=> (approxc lib a b # approxc lib b a).
Proof.
  introv.
  destruct_cterms; unfold cequivc, approxc, cequiv; simpl; sp.
Qed.

(* end hide *)


(* [22] ============ CEQUIV APPROX ============ *)

(**

  The following rule says that to prove that [a] is computationally
  equivalent to [b] it is enough to prove that [a] is an approximation
  of [b] and vice versa:

<<
   H |- a ~ b
     H |- a <= b
     H |- b <= a
>>
 *)

Definition rule_cequiv_approx_concl {o} (a b : @NTerm o) H :=
  mk_baresequent H (mk_conclax (mk_cequiv a b)).

Definition rule_cequiv_approx_hyp {o} (a b : @NTerm o) H :=
  mk_baresequent H (mk_conclax (mk_approx a b)).

Definition rule_cequiv_approx {o}
           (H   : @barehypotheses o)
           (a b : NTerm) :=
  mk_rule
    (rule_cequiv_approx_concl a b H)
    [ rule_cequiv_approx_hyp a b H,
      rule_cequiv_approx_hyp b a H
    ]
    [].

Lemma rule_cequiv_approx_true3 {o} :
  forall lib (H : @barehypotheses o) (a b : NTerm),
    rule_true3 lib (rule_cequiv_approx H a b).
Proof.
  unfold rule_cequiv_approx, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.
  assert (wf_csequent (rule_cequiv_approx_concl a b H)) as wfc by prove_seq.
  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2.
  exrepnd.
  lsubst_tac.
  allrw @member_eq.
  rw <- @member_cequiv_iff.
  allrw <- @member_approx_iff.
  rw @tequality_mkc_cequiv.
  allrw @tequality_mkc_approx.
  applydup hyp3 in hyp1; clear hyp3.
  applydup hyp0 in hyp2; clear hyp0.

  dands.

  split; intro k; spcast.
  rw @cequivc_iff_approxc; dands; auto.
  rw @cequivc_iff_approxc; dands; auto.

  spcast.
  rw @cequivc_iff_approxc; dands; auto.
Qed.

Lemma rule_cequiv_approx_true {o} :
  forall lib (H : @barehypotheses o) (a b : NTerm),
    rule_true lib (rule_cequiv_approx H a b).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_cequiv_approx_true3.
Qed.

Lemma rule_cequiv_approx_true2 {o} :
  forall lib (H : @barehypotheses o) (a b : NTerm),
    rule_true2 lib (rule_cequiv_approx H a b).
Proof.
  introv.
  apply rule_true_iff_rule_true2; auto.
  apply rule_cequiv_approx_true.
Qed.

Lemma rule_cequiv_approx_wf {o} :
  forall (a b : NTerm) (H : @barehypotheses o),
    wf_rule (rule_cequiv_approx H a b).
Proof.
  introv pwf m.

  allsimpl; repndors; tcsp; subst; allunfold @pwf_sequent; wfseq;
  allrw @covered_cequiv; allrw @covered_approx; repnd; tcsp.
  allrw <- @wf_cequiv_iff; tcsp.
Qed.

Lemma rule_cequiv_approx_wf2 {o} :
  forall (a b : NTerm) (H : @barehypotheses o),
    wf_rule2 (rule_cequiv_approx H a b).
Proof.
  introv pwf m.

  allsimpl; repndors; tcsp; subst; allunfold @wf_bseq; wfseq;
  allrw @covered_cequiv; allrw @covered_approx; repnd; tcsp.
  allrw <- @wf_cequiv_iff; tcsp.
Qed.


(* begin hide *)


(* [22] ============ CEQUIV LAMBDA D ============ *)

(**

  The following rule is used to prove that lambda abstraction are
  computationally equivalent:

<<
   H |- \x.a ~ \x.b
     H, x : Base |- a ~ b
>>
 *)
Definition rule_cequiv_lambda_d {o}
           (H : @barehypotheses o)
           (x : NVar)
           (a b : NTerm) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_cequiv (mk_lam x a) (mk_lam x b))))
    [ mk_baresequent (snoc H (mk_hyp x mk_base)) (mk_conclax (mk_cequiv a b))
    ]
    [].

Lemma rule_cequiv_lambda_d_true {o} :
  forall lib (H : @barehypotheses o) (x : NVar) (a b : NTerm)
         (cond : !LIn x (vars_hyps H)),
    rule_true lib (rule_cequiv_lambda_d H x a b).
Proof.
  unfold rule_cequiv_lambda_d, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.
  exists (@covered_axiom o (nh_vars_hyps H)).

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_cequiv_iff.
  rw @tequality_mkc_cequiv.

  dands.

  - split; intro h; clear h.

    + vr_seq_true in hyp1.
      spcast.
      apply implies_cequivc_lam2.
      introv.
      apply cequiv_stable.
      pose proof (hyp1 (snoc s2 (x,u)) (snoc s2 (x,u))) as hh; clear hyp1.
      repeat (autodimp hh hyp).

      * apply hyps_functionality_snoc2; simpl; auto.

        { introv equ sim'.
          lsubst_tac; eauto 3 with slow. }

        { eapply similarity_hyps_functionality_trans; eauto. }

      * sim_snoc2; dands; auto.

        { apply similarity_sym in sim; auto.
          apply similarity_refl in sim; auto. }

        { lsubst_tac.
          apply equality_in_base_iff; spcast; auto. }

      * exrepnd.
        clear hh0.
        lsubst_tac.
        rw <- @member_cequiv_iff in hh1; spcast.

        repeat (substc_lsubstc_vars3;[]).

        pose proof (lsubstc_snoc_move a s2 [] x u w0) as e1.
        pose proof (lsubstc_snoc_move b s2 [] x u w3) as e2.
        allrw app_nil_r.
        pose proof (e1 c8) as k1; clear e1.
        pose proof (e2 c9) as k2; clear e2.
        autodimp k1 hyp.
        { apply similarity_dom in sim; repnd; rw sim; auto. }
        autodimp k2 hyp.
        { apply similarity_dom in sim; repnd; rw sim; auto. }
        exrepnd.
        proof_irr.
        rw <- k2; rw <- k0; auto.

    + vr_seq_true in hyp1.
      spcast.
      apply implies_cequivc_lam2.
      introv.
      apply cequiv_stable.
      pose proof (hyp1 (snoc s1 (x,u)) (snoc s1 (x,u))) as hh; clear hyp1.
      repeat (autodimp hh hyp).

      * apply hyps_functionality_snoc2; simpl; auto.

        introv equ sim'.
        lsubst_tac; eauto 3 with slow.

      * sim_snoc2; dands; auto.

        { apply similarity_refl in sim; auto. }

        { lsubst_tac.
          apply equality_in_base_iff; spcast; auto. }

      * exrepnd.
        clear hh0.
        lsubst_tac.
        rw <- @member_cequiv_iff in hh1; spcast.

        repeat (substc_lsubstc_vars3;[]).

        pose proof (lsubstc_snoc_move a s1 [] x u w0) as e1.
        pose proof (lsubstc_snoc_move b s1 [] x u w3) as e2.
        allrw app_nil_r.
        pose proof (e1 c8) as k1; clear e1.
        pose proof (e2 c9) as k2; clear e2.
        autodimp k1 hyp.
        { apply similarity_dom in sim; repnd; rw sim0; auto. }
        autodimp k2 hyp.
        { apply similarity_dom in sim; repnd; rw sim0; auto. }
        exrepnd.
        proof_irr.
        rw <- k2; rw <- k0; auto.

  - vr_seq_true in hyp1.
    spcast.
    apply implies_cequivc_lam2.
    introv.
    apply cequiv_stable.
    pose proof (hyp1 (snoc s1 (x,u)) (snoc s1 (x,u))) as hh; clear hyp1.
    repeat (autodimp hh hyp).

    * apply hyps_functionality_snoc2; simpl; auto.

      introv equ sim'.
      lsubst_tac; eauto 3 with slow.

    * sim_snoc2; dands; auto.

      { apply similarity_refl in sim; auto. }

      { lsubst_tac.
        apply equality_in_base_iff; spcast; auto. }

    * exrepnd.
      clear hh0.
      lsubst_tac.
      rw <- @member_cequiv_iff in hh1; spcast.

      repeat (substc_lsubstc_vars3;[]).

      pose proof (lsubstc_snoc_move a s1 [] x u w0) as e1.
      pose proof (lsubstc_snoc_move b s1 [] x u w3) as e2.
      allrw app_nil_r.
      pose proof (e1 c8) as k1; clear e1.
      pose proof (e2 c9) as k2; clear e2.
      autodimp k1 hyp.
      { apply similarity_dom in sim; repnd; rw sim0; auto. }
      autodimp k2 hyp.
      { apply similarity_dom in sim; repnd; rw sim0; auto. }
      exrepnd.
      proof_irr.
      rw <- k2; rw <- k0; auto.
Qed.


(* end hide *)


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
