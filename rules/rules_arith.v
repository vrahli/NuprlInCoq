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


  Websites: http://nuprl.org/html/verification/
            http://nuprl.org/html/Nuprl2Coq
            https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli

*)


Require Export sequents2.
Require Export sequents_tacs.
Require Export sequents_equality.
Require Export per_props_nat.
Require Export cequiv_arith_props2.


Lemma mkc_arithop_as_add {o} :
  forall (a b : @CTerm o), mkc_arithop ArithOpAdd a b = mkc_add a b.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.

Definition mkc_mul {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_mul a b) (isprog_arithop ArithOpMul a b x y).

Definition mkc_div {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_div a b) (isprog_arithop ArithOpDiv a b x y).

Definition mkc_sub {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_sub a b) (isprog_arithop ArithOpSub a b x y).

Definition mkc_rem {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_rem a b) (isprog_arithop ArithOpRem a b x y).

Lemma mkc_arithop_as_mul {o} :
  forall (a b : @CTerm o), mkc_arithop ArithOpMul a b = mkc_mul a b.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.

Lemma mkc_arithop_as_div {o} :
  forall (a b : @CTerm o), mkc_arithop ArithOpDiv a b = mkc_div a b.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.

Lemma mkc_arithop_as_sub {o} :
  forall (a b : @CTerm o), mkc_arithop ArithOpSub a b = mkc_sub a b.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.

Lemma mkc_arithop_as_rem {o} :
  forall (a b : @CTerm o), mkc_arithop ArithOpRem a b = mkc_rem a b.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.

Lemma cequiv_mk_mul_integer {o} :
  forall lib (k1 k2 : Z),
    @cequiv o lib (mk_mul (mk_integer k1) (mk_integer k2)) (mk_integer (k1 * k2)).
Proof.
  introv.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_eq; apply isprog_arithop; eauto 3 with slow.
Qed.

Lemma cequivc_mkc_mul_integer {o} :
  forall lib (k1 k2 : Z),
    @cequivc o lib (mkc_mul (mkc_integer k1) (mkc_integer k2)) (mkc_integer (k1 * k2)).
Proof.
  introv.
  unfold cequivc; simpl.
  apply cequiv_mk_mul_integer.
Qed.

Lemma cequiv_mk_sub_integer {o} :
  forall lib (k1 k2 : Z),
    @cequiv o lib (mk_sub (mk_integer k1) (mk_integer k2)) (mk_integer (k1 - k2)).
Proof.
  introv.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_eq; apply isprog_arithop; eauto 3 with slow.
Qed.

Lemma cequivc_mkc_sub_integer {o} :
  forall lib (k1 k2 : Z),
    @cequivc o lib (mkc_sub (mkc_integer k1) (mkc_integer k2)) (mkc_integer (k1 - k2)).
Proof.
  introv.
  unfold cequivc; simpl.
  apply cequiv_mk_sub_integer.
Qed.

Lemma cequiv_mk_div_integer {o} :
  forall lib (k1 k2 : Z),
    @cequiv o lib (mk_div (mk_integer k1) (mk_integer k2)) (mk_integer (Z.quot k1  k2)).
Proof.
  introv.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_eq; apply isprog_arithop; eauto 3 with slow.
Qed.

Lemma cequivc_mkc_div_integer {o} :
  forall lib (k1 k2 : Z),
    @cequivc o lib (mkc_div (mkc_integer k1) (mkc_integer k2)) (mkc_integer (Z.quot k1 k2)).
Proof.
  introv.
  unfold cequivc; simpl.
  apply cequiv_mk_div_integer.
Qed.

Lemma cequiv_mk_rem_integer {o} :
  forall lib (k1 k2 : Z),
    @cequiv o lib (mk_rem (mk_integer k1) (mk_integer k2)) (mk_integer (Z.rem k1 k2)).
Proof.
  introv.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_eq; apply isprog_arithop; eauto 3 with slow.
Qed.

Lemma cequivc_mkc_rem_integer {o} :
  forall lib (k1 k2 : Z),
    @cequivc o lib (mkc_rem (mkc_integer k1) (mkc_integer k2)) (mkc_integer (Z.rem k1 k2)).
Proof.
  introv.
  unfold cequivc; simpl.
  apply cequiv_mk_rem_integer.
Qed.


(*
   H |- op a1 b1 = op a2 b2 in Z

     By arithEquality

     H |- a1 = a2 in Z
     H |- b1 = b2 in Z
 *)
Definition rule_arithop_equality {o}
           (H : @bhyps o) op (a1 a2 b1 b2: NTerm) :=
  mk_rule
    (mk_baresequent H (mk_conclax (mk_equality (mk_arithop op a1 b1) (mk_arithop op a2 b2) mk_int)))
    [
      mk_baresequent H (mk_conclax (mk_equality a1 a2 mk_int)),
      mk_baresequent H (mk_conclax (mk_equality b1 b2 mk_int))
    ]
    [].

Lemma rule_arithop_equality_true3 {o} :
  forall lib (H : @bhyps o) op a1 a2 b1 b2,
    rule_true3 lib (rule_arithop_equality H op a1 a2 b1 b2).
Proof.
  intros.
  unfold rule_arithop_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent (H) ||- (mk_conclax (mk_equality (mk_arithop op a1 b1) (mk_arithop op a2 b2) mk_int))) as wfc.
  { clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp.
    introv i; allrw in_app_iff; tcsp. }

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  lsubst_tac.
  pose proof (teq_and_eq_if_equality lib mk_int (mk_arithop op a1 b1) (mk_arithop op a2 b2) s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT0) as q.
  rw <- @member_equality_iff.
  lsubst_tac.
  apply q; auto; clear q.

  { apply tequality_int. }

  clear dependent s1.
  clear dependent s2.
  introv hf sim.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2) as q1; clear hyp1.
  pose proof (hyp2 s1 s2) as q2; clear hyp2.
  repeat (autodimp q1 hyp1).
  repeat (autodimp q2 hyp2).
  exrepnd.
  lsubst_tac.
  rw <- @member_equality_iff in q1.
  rw <- @member_equality_iff in q2.
  apply equality_commutes in q0; auto;[].
  apply equality_commutes in q3; auto;[].
  clear q1 q2.
  apply equality_in_int in q0.
  apply equality_in_int in q3.
  unfold equality_of_int in *; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;
     apply implies_cequivc_mkc_arithop;
     apply computes_to_valc_implies_cequivc;
     [apply q3|apply q0]
    |].

  eapply equality_respects_cequivc;
    [apply cequivc_sym;
     apply implies_cequivc_mkc_arithop;
     apply computes_to_valc_implies_cequivc;
     [apply q2|apply q1]
    |].

  destruct op.

  {
    rewrite mkc_arithop_as_add.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;apply cequivc_mkc_add_integer|].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_add_integer|].
    apply equality_in_int.
    exists (k0 + k)%Z; dands; spcast; apply computes_to_valc_refl; auto 3 with slow.
  }

  {
    rewrite mkc_arithop_as_mul.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;apply cequivc_mkc_mul_integer|].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_mul_integer|].
    apply equality_in_int.
    exists (k0 * k)%Z; dands; spcast; apply computes_to_valc_refl; auto 3 with slow.
  }

  {
    rewrite mkc_arithop_as_sub.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;apply cequivc_mkc_sub_integer|].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_sub_integer|].
    apply equality_in_int.
    exists (k0 - k)%Z; dands; spcast; apply computes_to_valc_refl; auto 3 with slow.
  }

  {
    rewrite mkc_arithop_as_div.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;apply cequivc_mkc_div_integer|].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_div_integer|].
    apply equality_in_int.
    exists (Z.quot k0  k)%Z; dands; spcast; apply computes_to_valc_refl; auto 3 with slow.
  }

  {
    rewrite mkc_arithop_as_rem.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;apply cequivc_mkc_rem_integer|].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;apply cequivc_mkc_rem_integer|].
    apply equality_in_int.
    exists (Z.rem k0 k)%Z; dands; spcast; apply computes_to_valc_refl; auto 3 with slow.
  }
Qed.
