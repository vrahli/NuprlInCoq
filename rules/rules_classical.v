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


Require Export sequents_tacs.
Require Export Classical_Prop.
Require Export per_props_union.
Require Export per_props_equality.
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
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_squash (mk_or P (mk_not P)))))
    [ mk_baresequent H (mk_conclax (mk_member P (mk_uni i)))
    ]
    [].

Lemma rule_squashed_excluded_middle_true {o} :
  forall lib (P : NTerm),
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_squashed_excluded_middle P i H).
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

  assert (tequality lib (lsubstc P w0 s1 c0) (lsubstc P w0 s2 c4)) as teq.
  (* begin proof of assert *)
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  rw @member_eq in hyp1.
  rw <- @member_member_iff in hyp1.
  apply member_in_uni in hyp1.
  apply tequality_in_uni_implies_tequality in hyp0; auto.
  (* end proof of assert *)

  dands; auto; try (spcast; computes_to_value_refl).

  generalize (classic (inhabited_type lib (lsubstc P w0 s1 c0))); intro inh.
  destruct inh as [inh | ninh].

  (* First, we assume that P is inhabited *)
  destruct inh as [t inh].
  exists (mkc_inl t).
  rw @equality_mkc_union; dands; auto;
  try (complete (allapply @tequality_refl; auto));
  try (complete (rw @tequality_not; allapply @tequality_refl; auto)).
  left.
  exists t t; auto; dands; try (spcast; computes_to_value_refl); auto.

  (* Now, we assume that P is not inhabited *)
  exists (@mkc_inr o mkc_axiom).
  rw @equality_mkc_union; dands; auto;
  try (complete (allapply @tequality_refl; auto));
  try (complete (rw @tequality_not; allapply @tequality_refl; auto)).
  right.
  exists (@mkc_axiom o) (@mkc_axiom o); auto; dands; try (spcast; computes_to_value_refl); auto.
  rw @equality_in_not; dands; auto; allapply @tequality_refl; auto.
Qed.

(* begin hide *)

(* end hide *)



(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
