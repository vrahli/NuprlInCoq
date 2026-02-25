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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export rules_useful.
Require Export domain_th.
Require Export per_props_equality.
Require Export per_props_equality_more.
Require Export per_props_iff.
Require Export per_props_admiss.
Require Export per_props_mono.
Require Export per_props_partial.
Require Export sequents_equality.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ #⪯# *)
(** printing ~=~  $\sim$ #~# *)
(* printing ===>  $\longmapsto$ *)
(** printing ===>  $\Downarrow$ #⇓# *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)
(** printing <=2=> $\Leftarrow\!\!{\scriptstyle{2}}\!\!\Rightarrow$ *)
(** printing $  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing |- $\vdash$ *)

(** %\noindent% In this section we prove rules about partial types.
  We assume that the reader has seen the definitions
  of [per_partial], [fix_approxc], [per_mono] and [per_admiss]
  in %\ref{sec:type:ind:per}%
  We will also use the domain theoretic properties we proved in Sec.
  %\ref{sec:comp:domain}%.

*)


(* begin hide *)


Hint Resolve tequality_trans tequality_sym tequality_refl: tequality_equiv.
(* MOVE to csubst? *)
Hint Resolve cequivc_mkcfix : cequivc_congr.


(*  match type of  Hypa1 with
  context [lsubstc (mk_fun ?A ?B) _ ?s _] =>
    match goal with
    [Aw:wf_term A, Bw:wf_term B, Ac : cover_vars A s, Bc : cover_vars B s  |- _]
      => idtac Aw
    end
  end. *)


(* !! MOVE  *)
Lemma mkc_equality_alpha_congr {o} : forall a b T U : @CTerm o,
  alphaeqc T U
  -> alphaeqc (mkc_equality a b T) (mkc_equality a b U).
Proof.
  introv Hal. repnud Hal. destruct T. destruct U.
  allsimpl.
  unfold alphaeqc, mkc_equality.
  allsimpl. destruct a. destruct  b.
  allsimpl.
  unfold_all_mk2.
  prove_alpha_eq3.
Qed.

(*
Definition inhabited (T: CTerm) := {t : CTerm, member t T}.
*)

(*
Ltac dest_imps :=
match goal with
  [H1: ?A , H2 : ?A-> _ |- _] => apply H2 in H1
end.
*)

(* end hide *)

(* begin hide *)

Lemma equorsq_member {o} :
  forall lib (a b T : @CTerm o),
    equorsq lib a b T
    -> member lib a T
    -> member lib b T.
Proof.
  introv e m.
  apply cequorsq_equality_trans1 with (t2 := a); auto.
  apply cequorsq_sym; auto.
  apply cequorsq_equality_trans2 with (t2 := a); auto.
Qed.

Lemma equorsq_preserves_tequality {o} :
  forall lib (A B a b : @CTerm o),
    equorsq lib a b A
    -> tequality lib A B
    -> equorsq lib a b B.
Proof.
  introv e t.
  allunfold @equorsq; repdors; sp.
  left.
  apply @tequality_preserving_equality with (A := A); auto.
Qed.

Lemma sequent_true_equality_refl {o} :
  forall lib H a b A w,
    sequent_true lib (mk_wcseq (mk_baresequent H (mk_conclax (@mk_equality o a b A))) w)
    -> {w' : wf_csequent (mk_baresequent H (mk_conclax (mk_member a A)))
        & sequent_true lib (mk_wcseq (mk_baresequent H (mk_conclax (mk_member a A))) w')}.
Proof.
  introv seq.

  assert (wf_csequent (mk_baresequent H (mk_conclax (mk_member a A))))
    as w' by (clear seq; wfseq).

  exists w'.
  vr_seq_true in seq.
  vr_seq_true; allsimpl.
  generalize (seq s1 s2 eqh sim); intro h2; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  dands.
  rw @tequality_mkc_equality in h0; repnd.
  destruct h0 as [e1 e2]. apply equality_sym in h1. apply equality_refl in h1; auto.
  apply tequality_mkc_member_if_equal; sp.
  - apply h4. apply equality_refl in h1; auto.
  - rw <- @member_member_iff.
  apply equality_refl in h1; auto.
  
Qed.

Lemma sequent_true_equality_sym {o} :
  forall lib H a b A w,
    @sequent_true o lib (mk_wcseq (mk_baresequent H (mk_conclax (mk_equality a b A))) w)
    -> {w' : wf_csequent (mk_baresequent H (mk_conclax (mk_equality b a A)))
        & sequent_true lib (mk_wcseq (mk_baresequent H (mk_conclax (mk_equality b a A))) w')}.
Proof.
  introv seq.

  assert (wf_csequent (mk_baresequent H (mk_conclax (mk_equality b a A))))
    as w' by (clear seq; wfseq).

  exists w'.
  vr_seq_true in seq.
  vr_seq_true; allsimpl.
  generalize (seq s1 s2 eqh sim); intro h2; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  dup h1 as h2; apply equality_sym in h2; apply equality_refl in h2.
  dup h1 as h3; apply equality_refl in h3.
  rw @tequality_mkc_equality in h0; repnd.
  sp.
  { apply @tequality_mkc_equality_if_equal; dands; auto. }
  { eapply equality_trans. exact h0. apply equality_sym. auto.
    eapply equality_trans. exact h1. auto.
  }
Qed.

Lemma sequent_true_implies_prop {o} :
  forall lib H a b e w,
    @sequent_true o lib (mk_wcseq (mk_baresequent H (mk_concl (mk_iff a b) e)) w)
    -> {w' : wf_csequent (mk_baresequent H (mk_concl_t a))
        & sequent_true lib (mk_wcseq (mk_baresequent H (mk_concl_t a)) w')}.
Proof.
  introv seq.

  assert (wf_csequent (mk_baresequent H (mk_concl_t a)))
    as w' by (clear seq; wfseq; allrw @wf_prod; repnd; auto; allrw @covered_iff; sp).

  exists w'.
  vr_seq_true in seq.
  vr_seq_true; allsimpl.
  generalize (seq s1 s2 eqh sim); intro h2; exrepnd.
  lsubst_tac.
  wfseq; proof_irr.
  rw @tequality_mkc_iff in h0; repnd; auto.
Qed.
(* end hide *)

(* ============ PARTIAL EQUALITY ============ *)

(**

  The following rule states when two partial types are equal.
<<
   H |- partial(A) = partial(B) in Type(i)

     By partialEquality a ()

     H |- A = B in Type(i)
     H a : A |- halts(a)
>>

 *)

Definition rule_partial_equality {o}
           (A B : NTerm)
           (a : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_partial A) (mk_partial B) (mk_uni i))))
    [ mk_baresequent H (mk_conclax (mk_equality A B (mk_uni i))),
      mk_baresequent
        (snoc H (mk_hyp a A))
        (mk_conclax (mk_halts (mk_var a)))
    ]
    [ sarg_var a ].

Lemma rule_partial_equality_true {o} :
  forall lib (A B : NTerm),
  forall a : NVar,
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_partial_equality A B a i H).
Proof.
  unfold rule_partial_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  clear cargs.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert (!LIn a (vars_hyps H)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp.

  rename vhyps into niah.
  (* done with proving these simple facts *)

  vr_seq_true.

  lift_lsubst.
  rewrite member_eq.
  rw <- @member_equality_iff.

  dup sim as sim1.
  apply similarity_refl in sim1.


  assert (forall s c,
            similarity lib s1 s H
            -> equality lib (lsubstc A w0 s1 c0) (lsubstc B w3 s c) (mkc_uni i)) as teq1.
  intros s c sim'.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s eqh sim'); intro hyp; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  apply equality_commutes4 in hyp0; auto.
  (* end proof teq *)

  assert (forall s c,
            similarity lib s1 s H
            -> equality lib (lsubstc A w0 s1 c0) (lsubstc A w0 s c) (mkc_uni i)) as teq2.
  intros s c sim'.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s eqh sim'); intro hyp; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  apply equality_commutes2 in hyp0; auto.
  (* end proof teq *)

  assert (forall s c,
            similarity lib s1 s H
            -> equality lib (lsubstc B w3 s1 c3) (lsubstc B w3 s c) (mkc_uni i)) as teq3.
  intros s c sim'.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s eqh sim'); intro hyp; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  apply equality_commutes5 in hyp0; auto.
  (* end proof teq *)


  assert (hyps_functionality lib s2 H) as hf2.
  apply @similarity_hyps_functionality_trans with (s1 := s1); auto.


  dands;
    try (apply @tequality_mkc_equality_if_equal; auto);
    try (apply @tequality_mkc_uni);
    try (apply equality_partial_in_uni).


  (* - 1 - *)
  dands; auto.
  introv m.
  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s1 (a,t)) (snoc s1 (a,t))); clear hyp2; intro hyp2.

  autodimp hyp2 hyp.
  apply hyps_functionality_snoc2; auto; introv e sim'; allsimpl.

  apply sequent_true_equality_refl in hyp1; exrepnd.
  vr_seq_true in hyp0.
  generalize (hyp0 s1 s' eqh sim'); intro hyp; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  allrw <- @member_member_iff.
  apply @tequality_in_uni_implies_tequality in hyp1. exrepnd.
  apply hyp1. auto.
  
  autodimp hyp2 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s1 t t w0 c0; sp.

  exrepnd.
  lsubst_tac.
  allrw @member_eq.
  apply member_halts_iff; auto.


  (* - 2 - *)
  dands; auto.
  introv m.
  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s1 (a,t)) (snoc s1 (a,t))); clear hyp2; intro hyp2.

  autodimp hyp2 hyp.
  apply hyps_functionality_snoc2; auto; introv e sim'; allsimpl.

  apply sequent_true_equality_refl in hyp1; exrepnd.
  vr_seq_true in hyp0.
  generalize (hyp0 s1 s' eqh sim'); intro hyp; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  allrw <- @member_member_iff.
  apply @tequality_in_uni_implies_tequality in hyp1.
  sp; eauto 3 with slow.
  sp; eauto 3 with slow.

  autodimp hyp2 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s1 t t w0 c0; sp.
  generalize (teq1 s1 c3 sim1); intro teq.
  apply equality_in_uni in teq.
  apply @tequality_preserving_equality with (A := lsubstc B w3 s1 c3); auto.
  apply @tequality_sym; auto.

  exrepnd.
  lsubst_tac.
  allrw @member_eq.
  apply member_halts_iff; auto.


  (* - 3 - *)
  dands; auto.
  introv m.
  vr_seq_true in hyp2.
  generalize (hyp2 (snoc s1 (a,t)) (snoc s1 (a,t))); clear hyp2; intro hyp2.

  autodimp hyp2 hyp.
  apply hyps_functionality_snoc2; auto; introv e sim'; allsimpl.

  apply sequent_true_equality_refl in hyp1; exrepnd.
  vr_seq_true in hyp0.
  generalize (hyp0 s1 s' eqh sim'); intro hyp; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  allrw <- @member_member_iff.
  apply @tequality_in_uni_implies_tequality in hyp1.
  sp.
  sp.
  
  autodimp hyp2 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s1 t t w0 c0; sp.

  exrepnd.
  lsubst_tac.
  allrw @member_eq.
  apply member_halts_iff; auto.
Qed.



(* ============ PARTIAL INCLUSION ============ *)

(**

  To prove that two terms are equal in a partial(A), it is enough to
  prove that they are equal in A:
<<
   H |- a = b in partial(A)

     By partialInclusion (i)

     H |- a = b in A
     H |- partial(A) in Type(i)
>>

 *)

Definition rule_partial_inclusion {o}
           (a b A : NTerm)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b (mk_partial A))))
    [ mk_baresequent H (mk_conclax (mk_equality a b A)),
      mk_baresequent H (mk_conclax (mk_member (mk_partial A) (mk_uni i)))
    ]
    [].

Lemma rule_partial_inclusion_true {o} :
  forall lib (a b A : NTerm),
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_partial_inclusion a b A i H).
Proof.
  unfold rule_partial_inclusion, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  clear cargs.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.

  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  allrw <- @member_member_iff.
  apply @tequality_in_uni_implies_tequality in hyp0; auto.
  sp.
  clear hyp2.
  dup hyp0 as teqpart.
  apply @tequality_mkc_partial in hyp0; repnd.

  dands.


  (* - tequality part - *)
  apply @tequality_mkc_equality_if_equal; auto.

  applydup @sequent_true_equality_refl in hyp1; exrepnd.
  rename hyp4 into hyp5.
  vr_seq_true in hyp5.
  generalize (hyp5 s1 s2 eqh sim); clear hyp1; intro hyp4; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  allrw <- @member_member_iff.
  apply @tequality_mkc_member in hyp1; repnd.
  apply equality_in_mkc_partial.
  apply hyp1 in hyp3. clear hyp1.

  dands; auto.

  apply @tequality_refl in teqpart; auto.

 { split; intro k; try (complete sp); apply hyp0.
   apply equality_sym in hyp3; apply equality_refl in hyp3; auto.
   apply equality_refl in hyp3; auto.
 }

  applydup @sequent_true_equality_sym in hyp1; exrepnd.
  applydup @sequent_true_equality_refl in hyp4; exrepnd.
  vr_seq_true in hyp5.
  generalize (hyp5 s1 s2 eqh sim); clear hyp5; intro hyp5; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  allrw <- @member_member_iff.
  apply @tequality_mkc_member in hyp3; repnd.
  apply equality_in_mkc_partial.
  sp.

  dands; auto.

  apply @tequality_refl in teqpart; auto.

  split; intro k; try (complete sp); apply hyp0; auto.
  apply equality_sym in hyp3; apply equality_refl in hyp3; auto.

  (* - equality part - *)
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  apply @tequality_mkc_equality in hyp3; repnd.
  apply equality_in_mkc_partial.
  sp.

  dands; auto.

  apply @tequality_refl in hyp0; auto.
  apply tequality_mkc_partial in hyp0. sp.

  split; intro k; try (complete sp); apply hyp0.
  apply equality_sym in hyp1.
  apply equality_refl in hyp1.
  apply equality_refl in hyp1.
  auto.
  apply equality_refl in hyp1.
  auto.

Qed.




(* ============ PARTIAL MEMBER EQUALITY ============ *)

(**

  To prove that two terms $a$ and $b$ are equal in a partial(A), it
  is enough to prove that they are equal in T assuming that $a$ has a
  value; that $a$ and $b$ have the same convergence behavior; and
  that partial(A) is a type:
<<
   H |- a = b in partial(A)

     By partialInclusion z i

     H, z : halts(a) |- a = b in A
     H |- halts(a) <=> halts(b)
     H |- partial(A) in Type(i)
>>

 *)

Definition rule_partial_member_equality {o}
           (a b A e : NTerm)
           (z : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b (mk_partial A))))
    [ mk_baresequent (snoc H (mk_hyp z (mk_halts a))) (mk_conclax (mk_equality a b A)),
      mk_baresequent H (mk_concl (mk_iff (mk_halts a) (mk_halts b)) e),
      mk_baresequent H (mk_conclax (mk_member (mk_partial A) (mk_uni i)))
    ]
    [].

Lemma rule_partial_member_equality_true {o} :
  forall lib (a b A e : NTerm),
  forall z : NVar,
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_partial_member_equality a b A e z i H).
Proof.
  unfold rule_partial_member_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  clear cargs.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  rename Hyp2 into hyp3.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  assert (!LIn z (vars_hyps H)
          # !LIn z (free_vars a)
          # !LIn z (free_vars b)
          # !LIn z (free_vars A)) as vhyps.

  clear hyp1 hyp2 hyp3.
  dwfseq.
  sp.

  destruct vhyps as [nizh vhyps].
  destruct vhyps as [niah vhyps].
  destruct vhyps as [nibh niAh].
  (* done with proving these simple facts *)

  vr_seq_true.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality
                lib (mk_partial A) a b s1 s2 H
                wT w1 w2 c1 c3 c2 c4 cT cT0
                eqh sim); intro k.
  repeat (autodimp k hyp); auto; lsubst_tac; auto.


  (* - tequality part - *)
  vr_seq_true in hyp3.
  generalize (hyp3 s1 s2 eqh sim); clear hyp3; intro hyp3; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  allrw <- @member_member_iff.
  apply @tequality_in_uni_implies_tequality in hyp0; repnd; sp.

  (* - equality part - *)
  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.
  apply equality_in_mkc_partial.

  dands.


  (* -- type part -- *)
  vr_seq_true in hyp3.
  generalize (hyp3 s1 s2 hf sim); clear hyp3; intro hyp3; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  allrw <- @member_member_iff.
  apply member_in_uni in hyp3; auto.


  (* -- iff part -- *)
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  rw @equality_in_iff in hyp2; exrepnd.
  rw @tequality_mkc_iff in hyp0; repnd.
  allrw @tequality_mkc_halts.
  clear hyp5 hyp4.

  assert (chaltsc lib (lsubstc a w1 s1 ca1) <=> chaltsc lib (lsubstc b w2 s1 c3)) as ciff.
  (* begin proof of assert *)
  split; intro k; applydup @member_halts_iff in k as k1.
  apply hyp8 in k1; apply inhabited_type_if_equality in k1; apply inhabited_halts in k1; auto.
  apply hyp2 in k1; apply inhabited_type_if_equality in k1; apply inhabited_halts in k1; auto.
  (* end proof of assert *)

  apply tiff_trans with (b := chaltsc lib (lsubstc b w2 s1 c3)); auto.

  autodimp hyp0 hyp.
  exists (@mkc_id o).
  rw @equality_in_fun; dands; auto.
  introv equ; apply equality_in_halts in equ; repnd.
  apply ciff in equ0.
  spcast.
  apply equality_respects_cequivc_left with (t1 := mkc_axiom); auto.
  apply @cequivc_trans with (b := a0); auto.
  apply cequivc_sym; auto; apply computes_to_valc_implies_cequivc; auto.
  apply cequivc_sym; auto.
  apply equality_respects_cequivc_right with (t2 := mkc_axiom); auto.
  apply @cequivc_trans with (b := a'); auto.
  apply cequivc_sym; auto; apply computes_to_valc_implies_cequivc; auto.
  apply cequivc_sym; auto.
  apply member_halts_iff; auto; spcast; auto.


  (* -- equality part -- *)
  introv ha.
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z,mkc_axiom)) (snoc s2 (z,mkc_axiom))); clear hyp1; intro hyp1.

  autodimp hyp1 hyp.
  apply hyps_functionality_snoc2; auto; introv equ sim'; allsimpl.
  lsubst_tac.
  apply @tequality_mkc_halts.
  apply equality_refl in equ; apply member_halts_iff in equ.
  vr_seq_true in hyp3.
  generalize (hyp3 s1 s' hf sim'); clear hyp3; intro hyp3; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  allrw <- @member_member_iff.
  apply sequent_true_implies_prop in hyp2; exrepnd.
  vr_seq_true in hyp3.
  generalize (hyp3 s1 s' hf sim'); clear hyp3; intro hyp3; exrepnd.
  lsubst_tac.
  rw @tequality_mkc_halts in hyp2; auto.

  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  assert (wf_term (mk_halts a)) as wfha by (rw <- @wf_halts_iff; sp).
  assert (cover_vars (mk_halts a) s1) as cvh by (rw @cover_vars_halts; sp).
  exists s1 s2 (@mkc_axiom o) (@mkc_axiom o) wfha cvh; dands; auto.
  lsubst_tac.
  apply member_halts_iff; auto.

  exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  apply equality_commutes4 in hyp0; auto.
Qed.



(* ============ TERMINATION ============ *)

(**

  To prove that two terms [a] and [b] are equal in a type [A], it is
  enough to prove that [a] converges and that they are equal in
  [mk_partial(A)]:
<<
   H |- a = b in A

     By termination

     H |- halts(a)
     H |- a = b in partial(A)
>>

 *)

Definition rule_termination {o}
           (a b A : @NTerm o)
           (H : barehypotheses) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality a b A)))
    [ mk_baresequent H (mk_conclax (mk_halts a)),
      mk_baresequent H (mk_conclax (mk_equality a b (mk_partial A)))
    ]
    [].

Lemma rule_termination_true {o} :
  forall lib (a b A : NTerm),
  forall H : @barehypotheses o,
    rule_true lib (rule_termination a b A H).
Proof.
  unfold rule_termination, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  clear cargs.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality lib A a b s1 s2 H
                wT w1 w2 c1 c0 c2 c3 cT cT0
                eqh sim); intro k.
  apply k; clear k.


  (* - tequality part - *)
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  rw @tequality_mkc_equality in hyp0; repnd.
  allrw @tequality_mkc_partial; repnd; auto.


  (* - equality part - *)
  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  rw @equality_in_mkc_partial in hyp2; repnd.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_halts_iff.
  applydup hyp2 in hyp1.
  apply equality_trans with (t2 := lsubstc b w2 s1 c2); auto.
  rw @tequality_mkc_equality in hyp0; repnd.
  dimp hyp0.
   { apply equality_sym in hyp6; apply equality_refl in hyp6; auto.
     apply @equality_in_mkc_partial. sp.
   }
  rw @equality_in_mkc_partial in hyp; repnd.
  apply hyp; apply hyp4; auto.
  
Qed.




(* ============ HASVALUE EQUALITY ============ *)

(**

  To prove that two ``halts'' terms [mk_halts(a)] and [mk_halts(b)]
  are equal types, it is enough to prove that [a] and [b] are equal in
  some partial type [mk_partial(A)]:
<<
   H |- halts(a) = halts(b) in Type(i)

     By HasValueEquality A

     H |- a = b in partial(A)
>>

 *)

Definition rule_hasvalue_equality {o}
           (a b A : @NTerm o)
           (i : nat)
           (H : barehypotheses) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_halts a) (mk_halts b) (mk_uni i))))
    [ mk_baresequent H (mk_conclax (mk_equality a b (mk_partial A)))
    ]
    [].

Lemma rule_hasvalue_equality_true {o} :
  forall lib (a b A : NTerm),
  forall i : nat,
  forall H : @barehypotheses o,
    rule_true lib (rule_hasvalue_equality a b A i H).
Proof.
  unfold rule_hasvalue_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  clear cargs.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  vr_seq_true.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.

  generalize (teq_and_eq_if_equality
                lib (mk_uni i) (mk_halts a) (mk_halts b) s1 s2 H
                wT w1 w2 c1 c4 c2 c5 cT cT0 eqh sim); intro k.
  lsubst_tac.
  apply k; clear k; try (apply @tequality_mkc_uni).

  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.
  rw @equality_in_uni_mkc_halts.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  rw @tequality_mkc_equality in hyp0; repnd.
  dup hyp1 as h1. apply equality_refl in h1.
  dup hyp1 as h2. apply equality_sym in h2; apply equality_refl in h2.
  sp.
  assert (equality lib (lsubstc a w0 s1 c1) (lsubstc b w3 s2 c0) (mkc_partial (lsubstc A w4 s1 c2))).
  eapply equality_trans. exact hyp1. auto.
  rw @equality_in_mkc_partial in H0; sp.
 
Qed.
