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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export sequents2.
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export Classical_Prop.
Require Export per_props_union.
Require Export per_props_equality.
Require Export per_props_squash.
Require Export per_props_not.
Require Export sequents_squash.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)

(* begin hide *)


(* end hide*)

(**

  Using the axiom of excluded middle from [Classical_Prop], we can
  easily prove the following squashed excluded middle rule:
<<
   H |- squash(P \/ ~P) ext Ax

     By SquashedEM

     H |- P in Type(i) ext Ax
>>

  where [mk_squash] is defined as
  [Definition mk_squash T := mk_image T (mk_lam nvarx mk_axiom)], i.e.,
  we map all the elements of [T] to [mk_axiom].
  The only inhabitant of [mk_squash T] is [mk_axiom],
  and we can prove that [mkc_axiom] is a member of [mkc_squash T] iff
  [T] is inhabited.  However, in the theory, there is in general no
  way to know which terms inhabit [T].

 *)

Definition rule_squashed_excluded_middle {o}
           (P : NTerm)
           (u i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_squash (mk_or P (mk_not P)))))
    [ mk_baresequent H (mk_conclax (mk_member P (mk_uni u i)))
    ]
    [].

Lemma rule_squashed_excluded_middle_true {o} :
  forall uk lib (P : NTerm),
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true uk lib (rule_squashed_excluded_middle P uk i H).
Proof.
  unfold rule_squashed_excluded_middle, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [wf1 hyp1].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  rw @tequality_mkc_squash.
  rw @tequality_mkc_or.
  rw @tequality_not.
  rw @member_eq.
  rw @equality_in_mkc_squash.

  assert (tequality uk lib' (lsubstc P w0 s1 c0) (lsubstc P w0 s2 c4)) as teq.
  (* begin proof of assert *)
  {
    vr_seq_true in hyp1.
    generalize (hyp1 lib' ext s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd; eauto 3 with slow.
    lsubst_tac.
    rw @member_eq in hyp1.
    rw <- @member_member_iff in hyp1.
    apply member_in_uni in hyp1.
    apply tequality_in_uni_implies_tequality in hyp0; eauto 3 with slow.
  }
  (* end proof of assert *)

  clear hyp1.
  clear lib ext.
  rename lib' into lib.
  dands; spcast; eauto 3 with slow;[].

  (*
  apply in_ext_implies_all_in_ex_bar; introv xt.
  eapply tequality_monotone in teq;[|eauto].
  clear lib xt sim eqh.
  rename lib' into lib.
   *)

  introv ext.

  generalize (classic (exists (lib'' : library) (ext'' : lib_extends lib'' lib'), inhabited_type uk lib'' (lsubstc P w0 s1 c0))); intro inh.
  destruct inh as [inh | ninh].

  {
    exrepnd.
    exists lib'' ext''.
    introv xta.
    eapply lib_extends_inhabited_type in inh1; eauto.
    destruct inh1 as [t inh].
    exists (mkc_inl t).
    applydup @inhabited_implies_tequality in inh.
    rw @equality_mkc_union; dands; auto;
      try (complete (allapply @tequality_refl; eauto 3 with slow));
      try (complete (rw @tequality_not; allapply @tequality_refl; eauto 3 with slow));[].
    apply equality_implies_all_in_ex_bar_equality in inh.
    eapply in_open_bar_pres; try exact inh; clear inh; introv xtb inh.
    left.
    exists t t; auto; dands; spcast; eauto 3 with slow.
  }

  {
    (* Now, we assume that P is not inhabited *)
    exists lib' (lib_extends_refl lib'); introv xta.
    exists (@mkc_inr o mkc_axiom).
    rw @equality_mkc_union; dands; auto;
      try (complete (allapply @tequality_refl; eauto 3 with slow));
      try (complete (rw @tequality_not; allapply @tequality_refl; eauto 3 with slow));[].
    apply in_ext_implies_all_in_ex_bar; introv xt'.
    right.
    exists (@mkc_axiom o) (@mkc_axiom o); auto; dands; spcast; eauto 3 with slow.
    rw @equality_in_not; dands; auto; allapply @tequality_refl; eauto 4 with slow.

    (*
        To prove the negation of this squashed LEM, we need a proposition which is false
        in the current library and some extensions
     *)

    introv y inh.
    destruct ninh.
    assert (lib_extends lib'2 lib') as xtb by eauto 3 with slow.
    exists lib'2 xtb; auto.
  }
Qed.

(* begin hide *)

(* end hide *)



(*

(*
   H |- squash(P)

     By classicalIntroduction

     H |- P in Type(i)
     H, x : not(P) |- Void
 *)
Definition rule_classical_introduction {o}
           (H : @bhyps o)
           (P : NTerm)
           (i : nat)
           (x : NVar) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_squash P)))
    [
      mk_baresequent H (mk_conclax (mk_member P (mk_uni i))),
      mk_baresequent (snoc H (mk_hyp x (mk_not P))) (mk_conclax mk_void)
    ]
    [].

Lemma rule_classical_introduction_true3 {o} :
  forall lib (H : @bhyps o) P i x,
    rule_true3 lib (rule_classical_introduction H P i x).
Proof.
  intros.
  unfold rule_classical_introduction, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  { clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as h; exrepnd.
  lsubst_tac.

  rw <- @member_member_iff in h1.
  repeat (rw <- @fold_mkc_member in h0).
  apply equality_commutes in h0; auto.
  clear h1.
  apply equality_in_uni in h0.

  rw @equality_in_mkc_squash_ax.
  eapply teq_and_eq_if_squash; eauto.

  destruct (classic (inhabited_type lib (lsubstc P wt s1 ct1))) as [inh|inh]; auto;[].

  assert False;[|sp];[].

  vr_seq_true in hyp2.
  pose proof (hyp2 (snoc s1 (x,mkc_axiom))
                   (snoc s2 (x,mkc_axiom)))
    as q; clear hyp2; exrepnd.
  repeat (autodimp q hyp).

  {
    apply hyps_functionality_snoc2; simpl; auto.
    introv equ sim'.
    lsubst_tac.
    apply tequality_not; auto.

    pose proof (hyp1 s1 s' eqh sim') as q; exrepnd.
    lsubst_tac.
    rw <- @member_member_iff in q1.
    repeat (rw <- @fold_mkc_member in q0).
    apply equality_commutes in q0; auto.
    apply equality_in_uni in q0; auto.
  }

  {
    sim_snoc2.
    dands; auto.
    lsubst_tac.
    apply equality_in_not; dands; auto.
    apply tequality_refl in h0; auto.
  }

  exrepnd.
  unfold mk_void in *.
  lsubst_tac.
  allrw @lsubstc_mk_false.
  apply equality_in_false in q1; auto.
Qed.
*)
