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


(*Require Export per_props.*)
Require Export per_props_cequiv.


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


(* begin hide *)

Lemma implies_equality_aequality {p} :
  forall lib (t1 t2 T : @CTerm p),
    equality lib t1 t2 T
    -> equality lib (mkc_refl t1) (mkc_refl t2) (mkc_aequality t1 t2 T).
Proof.
  unfold member, equality; introv e; exrepnd.
  exists (per_aeq_eq lib t1 t2 eq); unfold per_aeq_eq; dands;
    [|exists t1 t2; dands; spcast; tcsp; try computes_to_value_refl].
  apply CL_aeq.
  unfold per_aeq.
  exists T t1 t2 eq; sp; spcast; try computes_to_value_refl;
    pose proof (nuprl_eq_implies_eqorceq_refl lib T T eq t1 t2); sp.
(* universe inconsistency *)
Qed.

Lemma implies_equality_aequality_all {p} :
  forall lib (t1 t2 T : @CTerm p) a b,
    equality lib a b T
    -> equality lib t1 t2 T
    -> equality lib (mkc_refl a) (mkc_refl b) (mkc_aequality t1 t2 T).
Proof.
  unfold member, equality; introv w e; exrepnd.
  eapply nuprl_uniquely_valued in w1;[|exact e1].
  apply w1 in w0; clear dependent eq0.
  exists (per_aeq_eq lib t1 t2 eq); unfold per_aeq_eq; dands;
    [|exists a b; dands; spcast; tcsp; try computes_to_value_refl].
  apply CL_aeq.
  unfold per_aeq.
  exists T t1 t2 eq; sp; spcast; try computes_to_value_refl;
    pose proof (nuprl_eq_implies_eqorceq_refl lib T T eq t1 t2); sp.
(* universe inconsistency *)
Qed.

(* end hide *)

(**

  Using the type definitions we can prove various useful equivalences
  that are true about the Nuprl type system [nuprl].  These
  equivalences provide characterizations of our types.  For example,
  we can prove that two terms [t1] and [t2] are equal in a type [T] if
  and only if the type [mkc_equality t1 t2 T] is inhabited by
  [mkc_axiom].  This equivalence shows the relations between the
  [equality] meta-relation and the [mkc_equality] type.

 *)

Lemma member_aequality_iff {p} :
  forall lib (t1 t2 T : @CTerm p),
    equality lib t1 t2 T
    <=> member lib (mkc_refl t1) (mkc_aequality t1 t2 T).
Proof.
  sp; split; intro e.

  { apply implies_equality_aequality in e.
    apply equality_refl in e; auto. }

  allunfold @member; allunfold @equality; exrepnd.

  inversion e1; subst; try not_univ; clear e1.

  match goal with
  | [ H : per_aeq _ _ _ _ |- _ ] => rename H into h
  end.

  allunfold_per.
  computes_to_value_isvalue.
  exists eqa; sp.
  apply e in e0.
  unfold per_aeq_eq in *; exrepnd; auto.
Qed.

Lemma member_aequality_iff_all {p} :
  forall lib (t1 t2 T : @CTerm p) a,
    member lib a T
    -> (equality lib t1 t2 T
        <=> member lib (mkc_refl a) (mkc_aequality t1 t2 T)).
Proof.
  introv mem.
  split; intro e.

  { apply (implies_equality_aequality_all _ _ _ _ a a) in e; eauto 2 with slow. }

  allunfold @member; allunfold @equality; exrepnd.

  inversion e1; subst; try not_univ; clear e1.

  match goal with
  | [ H : per_aeq _ _ _ _ |- _ ] => rename H into h
  end.

  allunfold_per.
  computes_to_value_isvalue.
  exists eqa; sp.
  apply e in e0.
  unfold per_aeq_eq in *; exrepnd; auto.
Qed.

(* begin hide *)

Lemma member_amember_iff {p} :
  forall lib (t T : @CTerm p),
    member lib t T
    <=> member lib (mkc_refl t) (mkc_amember t T).
Proof.
  sp; rewrite <- fold_mkc_amember.
  apply member_aequality_iff.
Qed.

Lemma member_aequality_is_axiom {p} :
  forall lib (t1 t2 T a b : @CTerm p),
    equality lib a b (mkc_aequality t1 t2 T)
    -> { t , u : CTerm
       , a ===>(lib) (mkc_refl t)
       # b ===>(lib) (mkc_refl u)
       # equality lib t1 t2 T
       # equality lib t u T }.
Proof.
  unfold equality, nuprl; introv e; exrepd.
  inversion c; subst; try not_univ.

  match goal with
  | [ H : per_aeq _ _ _ _ |- _ ] => rename H into h
  end.

  allunfold @per_aeq; exrepnd.
  computes_to_value_isvalue.
  apply h1 in e.
  unfold per_aeq_eq in e; exrepnd.
  exists x1 x2; dands; auto; exists eqa; auto.
Qed.

Hint Resolve iscvalue_mkc_aequality : slow.

Lemma type_mkc_aequality {o} :
  forall lib (t1 t2 A : @CTerm o),
    type lib (mkc_aequality t1 t2 A) <=> type lib A.
Proof.
  introv; split; unfold type; intro teq; exrepnd.

  - inversion teq0; subst; try (not_univ); clear teq0.

    match goal with
    | [ H : per_aeq _ _ _ _ |- _ ] => rename H into h
    end.

    allunfold @per_aeq; exrepnd.
    computes_to_value_isvalue.
    exists eqa; auto.

  - exists (per_aeq_eq lib t1 t2 eq).
    apply CL_aeq.
    exists A t1 t2 eq; dands; spcast;
      try (apply computes_to_valc_refl; eauto 2 with slow); tcsp.
Qed.

Lemma equality_in_mkc_aequality {p} :
  forall lib (t1 t2 T a b : @CTerm p),
    equality lib a b (mkc_aequality t1 t2 T)
    <=>
    { x1 , x2 : CTerm
    , equality lib x1 x2 T
    # equality lib t1 t2 T
    # a ===>(lib) (mkc_refl x1)
    # b ===>(lib) (mkc_refl x2) }.
Proof.
  introv; split; intro i.

  {
    apply member_aequality_is_axiom in i; exrepnd.
    exists t u; dands; auto.
  }

  {
    exrepnd.
    allunfold @equality; allunfold @nuprl; exrepnd.

    eapply nuprl_uniquely_valued in i0;[|exact i2].
    apply i0 in i5.
    clear dependent eq0.

    exists (per_aeq_eq lib t1 t2 eq).
    unfold per_aeq_eq; dands; tcsp;[|exists x1 x2; dands; auto].

    apply CL_aeq.
    unfold per_aeq.
    exists T t1 t2 eq; sp; spcast;
      try (apply computes_to_valc_refl; eauto 2 with slow).
  }
Qed.

Lemma tequality_aequality_if_cequivc {p} :
  forall lib (t1 t2 t3 t4 A B : @CTerm p),
    tequality lib A B
    -> cequivc lib t1 t3
    -> cequivc lib t2 t4
    -> tequality
         lib
         (mkc_aequality t1 t2 A)
         (mkc_aequality t3 t4 B).
Proof.
  introv teq ceq1 ceq2.
  apply ext_eq_implies_tequality.

  - apply type_mkc_aequality; eauto 2 with slow.

  - apply type_mkc_aequality; eauto 2 with slow.

  - introv.
    repeat (rw @equality_in_mkc_aequality).
    split; intro h; exrepnd.

    + exists x1 x2; dands; auto; eauto 4 with slow nequality.

    + exists x1 x2; dands; auto; eauto 3 with slow nequality.
      eapply equality_respects_cequivc_left;[apply cequivc_sym;eauto|].
      eapply equality_respects_cequivc_right;[apply cequivc_sym;eauto|].
      eauto 3 with slow nequality.
Qed.

Lemma per_aeq_eq_eq_iff {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o) eqa1 eqa2,
    ((per_aeq_eq lib a1 b1 eqa1) <=2=> (per_aeq_eq lib a2 b2 eqa2))
      <=> (forall t1 t2, (eqa1 t1 t2 # eqa1 a1 b1) <=> eqa2 t1 t2 # eqa2 a2 b2).
Proof.
  introv; split; intro h; introv.

  - pose proof (h (mkc_refl t1) (mkc_refl t2)) as q; clear h; destruct q as [q1 q2].
    split; introv w; repnd;[clear q2|clear q1].

    + autodimp q1 hyp.

      {
        unfold per_aeq_eq.
        exists t1 t2; dands; spcast; auto;
          try (apply computes_to_valc_refl; eauto 2 with slow).
      }

      { unfold per_aeq_eq in q1; exrepnd; spcast; computes_to_value_isvalue. }

    + autodimp q2 hyp.

      {
        unfold per_aeq_eq.
        exists t1 t2; dands; spcast; auto;
          try (apply computes_to_valc_refl; eauto 2 with slow).
      }

      { unfold per_aeq_eq in q2; exrepnd; spcast; computes_to_value_isvalue. }

  - unfold per_aeq_eq; split; intro w; exrepnd.

    + pose proof (h x1 x2) as z; destruct z as [z z']; clear z'.
      autodimp z hyp; repnd.
      exists x1 x2; dands; auto.

    + pose proof (h x1 x2) as z; destruct z as [z' z]; clear z'.
      autodimp z hyp; repnd.
      exists x1 x2; dands; auto.
Qed.

Lemma tequality_mkc_aequality {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_aequality a1 a2 A) (mkc_aequality b1 b2 B)
    <=>
    (
      type lib A
      # type lib B
      # forall t1 t2,
          (equality lib t1 t2 A # equality lib a1 a2 A)
            <=> (equality lib t1 t2 B # equality lib b1 b2 B)
    ).
Proof.
  introv; split; intro k.

  - unfold tequality in k; exrepnd.
    destruct k0 as [k1 k2].

    inversion k1; subst; try not_univ; clear k1.
    inversion k2; subst; try not_univ; clear k2.

    match goal with
    | [ H1 : per_aeq _ _ _ _ , H2 : per_aeq _ _ _ _ |- _ ] =>
      rename H1 into h; rename H2 into q
    end.

    allunfold @per_aeq; exrepnd.
    computes_to_value_isvalue.

    dands; eauto 2 with slow.

    eapply eq_term_equals_trans in q1;[|apply eq_term_equals_sym;exact h1]; clear h1.
    rw @per_aeq_eq_eq_iff in q1.

    introv.
    pose proof (q1 t1 t2) as q.

    rw <- (equality_eq lib A1 t1 t2 eqa0 h2).
    rw <- (equality_eq lib A1 a0 b0 eqa0 h2).

    rw <- (equality_eq lib A0 t1 t2 eqa q2).
    rw <- (equality_eq lib A0 a b eqa q2).
    tcsp.

  - repnd.
    apply ext_eq_implies_tequality; try (apply type_mkc_aequality); auto.

    introv.
    repeat (rw @equality_in_mkc_aequality).
    split; intro q; exrepnd; exists x1 x2; dands; auto;
      try (complete (apply k; auto)).

    + pose proof (k x1 x2) as q; destruct q as [q q']; clear q'; autodimp q hyp; tcsp.

    + pose proof (k x1 x2) as q; destruct q as [q' q]; clear q'; autodimp q hyp; tcsp.
Qed.

Lemma tequality_mkc_aequality_if_mem {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    equality lib a1 a2 A
    -> equality lib b1 b2 B
    ->
    (
      tequality lib (mkc_aequality a1 a2 A) (mkc_aequality b1 b2 B)
      <=>
      (
        type lib A
        # type lib B
        # (forall t1 t2, equality lib t1 t2 A <=> equality lib t1 t2 B)
      )
    ).
Proof.
  introv e1 e2.
  rw @tequality_mkc_aequality; split; intro h; repnd; dands; auto.

  - introv.
    pose proof (h t1 t2) as w.
    destruct w as [w1 w2].
    split; intro q; tcsp.
    + autodimp w1 hyp; tcsp.
    + autodimp w2 hyp; tcsp.

  - introv.
    pose proof (h t1 t2) as w.
    destruct w as [w1 w2].
    split; intro q; tcsp.
Qed.

Lemma equality_in_mkc_amember {p} :
  forall lib (t T a b : @CTerm p),
    equality lib a b (mkc_amember t T)
    <=>
    { x1 , x2 : CTerm
    , equality lib x1 x2 T
    # member lib t T
    # a ===>(lib) (mkc_refl x1)
    # b ===>(lib) (mkc_refl x2) }.
Proof.
  introv.
  rw <- @fold_mkc_amember.
  rw @equality_in_mkc_aequality.
  split; intro h; exrepnd; exists x1 x2; dands; auto.
Qed.

(*
Lemma tequality_mkc_aequality_implies {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_aequality a1 a2 A) (mkc_aequality b1 b2 B)
    ->
    (
      tequality lib A B
      # (equality lib a1 a2 A -> equality lib b1 b2 B)
      # (equality lib a1 b1 A {+} ccequivc lib a1 b1)
    ).
Proof.
  unfold tequality, nuprl; introv teq; exrepnd.
  inversion teq0; subst; try (not_univ).

  allunfold @per_aeq; exrepnd.
  computes_to_value_isvalue.
  allfold @nuprl.
  dands.

  - exists eqa; sp.

  - intro e; allunfold @equality; exrepnd.
    assert (eq_term_equals eq0 eqa)
      as etq
        by (apply uniquely_valued_eq with (ts := nuprl lib) (T := A0) (T1 := A0) (T2 := B0);
            sp; nts; sp).
    exists eqa; sp.
    allapply @nuprl_refl2; sp.
    unfold eq_term_equals in etq; discover.
    apply (eqorceq_commutes_nuprl lib) with (a := a0) (c := a3) (A := A0) (B := A0); sp.
    apply nuprl_uniquely_eq_ext with (eq1 := eq0); sp.

  - allunfold @eqorceq; sp;
    left; unfold equality; exists eqa; sp;
    allapply @nuprl_refl; sp.
Qed.
*)

(*
Lemma tequality_mkc_aequality_in_universe_true {p} :
  forall lib (a1 b1 a2 b2 : @CTerm p) i,
    tequality lib (mkc_aequality a1 b1 (mkc_uni i)) (mkc_aequality a2 b2 (mkc_uni i))
    -> equality lib a1 b1 (mkc_uni i)
    -> equality lib a2 b2 (mkc_uni i).
Proof.
  introv t e.
  allapply @tequality_mkc_aequality_implies; sp.
Qed.
*)

(*
Lemma aequality_in_universe {p} :
  forall lib (a1 b1 a2 b2 : @CTerm p) i,
    tequality lib (mkc_aequality a1 b1 (mkc_uni i)) (mkc_aequality a2 b2 (mkc_uni i))
    -> equality lib a1 b1 (mkc_uni i)
    -> tequality lib a2 b2.
Proof.
  introv t e.
  apply tequality_mkc_aequality_in_universe_true in t; sp.
  apply @equality_in_uni with (i := i); sp.
Qed.
*)

(*
Lemma tequality_mkc_aequality {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_aequality a1 a2 A) (mkc_aequality b1 b2 B)
    <=>
    (
      tequality lib A B
      # (equality lib a1 a2 A <=> equality lib b1 b2 B)
      # (equality lib a1 b1 A {+} ccequivc lib a1 b1)
      # (equality lib a2 b2 A {+} ccequivc lib a2 b2)
    ).
Proof.
  introv; split; intro k.

  - unfold tequality, nuprl in k; exrepnd.
    inversion k0; subst; try not_univ.
    allunfold @per_aeq; exrepnd.
    computes_to_value_isvalue.
    allfold (@nuprl p).
    allapplydup @tequality_if_nuprl.
    allapplydup @nuprl_refl.
    sp;
      try (complete (apply @eqorceq_implies_equality_or_cequivc with (eq := eqa); auto));
      try (complete (apply @eqorceq_commutes_equality with (eq := eqa); auto)).

  - repnd.
    allunfold @tequality; exrepnd.
    assert (nuprl lib A A eq) as n by (allapplydup @nuprl_refl; sp).

    exists (per_aeq_eq lib a1 a2 eq).
    apply CL_aeq; unfold per_aeq; fold @nuprl.

    exists A B a1 a2 b1 b2 eq; dands; auto.
    { spcast; apply computes_to_valc_refl; apply iscvalue_mkc_aequality; auto. }
    { spcast; apply computes_to_valc_refl; apply iscvalue_mkc_aequality; auto. }
    { apply equality_or_cequivc_eqorceq with (a := a1) (b := b1) in n.
      apply n; sp. }
    { apply equality_or_cequivc_eqorceq with (a := a2) (b := b2) in n.
      apply n; sp; try (intros; split; auto). }
Qed.

Lemma tequality_mkc_aequality_sp {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_aequality a1 a2 A) (mkc_aequality b1 b2 B)
    <=>
    (
      tequality lib A B
      # (equality lib a1 b1 A {+} ccequivc lib a1 b1)
      # (equality lib a2 b2 A {+} ccequivc lib a2 b2)
    ).
Proof.
  introv; split; intro k.

  - unfold tequality, nuprl in k; exrepnd.
    inversion k0; subst; try not_univ.
    allunfold @per_aeq; exrepnd.
    computes_to_value_isvalue.
    allfold (@nuprl p).
    allapplydup @tequality_if_nuprl.
    allapplydup @nuprl_refl.
    sp;
      try (complete (apply @eqorceq_implies_equality_or_cequivc with (eq := eqa); auto));
      try (complete (apply @eqorceq_commutes_equality with (eq := eqa); auto)).

  - repnd.
    allunfold @tequality; exrepnd.
    assert (nuprl lib A A eq) as n by (allapplydup @nuprl_refl; sp).

    exists (per_aeq_eq lib a1 a2 eq).
    apply CL_aeq; unfold per_aeq; fold @nuprl.

    exists A B a1 a2 b1 b2 eq; dands; auto.
    { spcast; apply computes_to_valc_refl; apply iscvalue_mkc_aequality; auto. }
    { spcast; apply computes_to_valc_refl; apply iscvalue_mkc_aequality; auto. }
    { apply equality_or_cequivc_eqorceq with (a := a1) (b := b1) in n.
      apply n; sp. }
    { apply equality_or_cequivc_eqorceq with (a := a2) (b := b2) in n.
      apply n; sp; try (intros; split; auto). }
Qed.

Lemma tequality_mkc_aequality_if_equal {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib A B
    -> equality lib a1 b1 A
    -> equality lib a2 b2 A
    -> tequality lib (mkc_aequality a1 a2 A) (mkc_aequality b1 b2 B).
Proof.
  introv teq e1 e2.
  rw @tequality_mkc_aequality; dands; auto.
  split; intro e.
  { apply equality_trans with (t2 := a1); eauto with nequality. }
  { apply equality_trans with (t2 := b1); sp.
    apply equality_trans with (t2 := b2); eauto with nequality. }
Qed.

Lemma tequality_mkc_aequality2 {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_aequality a1 a2 A) (mkc_aequality b1 b2 B)
    <=>
    (
      tequality lib A B
      # (equality lib a1 a2 A <=> equality lib b1 b2 B)
      # equorsq2 lib a1 b1 a2 b2 A
    ).
Proof.
  intros.
  rw @tequality_mkc_aequality.
  repeat (rw @fold_equorsq).
  rw @fold_equorsq2; sp.
Qed.

Lemma tequality_mkc_aequality2_sp {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_aequality a1 a2 A) (mkc_aequality b1 b2 B)
    <=>
    (
      tequality lib A B
      # equorsq2 lib a1 b1 a2 b2 A
    ).
Proof.
  intros.
  rw @tequality_mkc_aequality_sp.
  repeat (rw @fold_equorsq).
  rw @fold_equorsq2; sp.
Qed.
*)

Lemma tequality_mkc_amember {p} :
  forall lib (a b A B : @CTerm p),
    tequality lib (mkc_amember a A) (mkc_amember b B)
    <=>
    (
      type lib A
      # type lib B
      # forall t1 t2,
          (equality lib t1 t2 A # member lib a A)
            <=> (equality lib t1 t2 B # member lib b B)
    ).
Proof.
  sp; repeat (rewrite <- fold_mkc_amember).
  trw @tequality_mkc_aequality; split; sp.
Qed.

Lemma tequality_mkc_amember_if_mem {p} :
  forall lib (a b A B : @CTerm p),
    member lib a A
    -> member lib b B
    ->
    (
      tequality lib (mkc_amember a A) (mkc_amember b B)
      <=>
      (
        type lib A
        # type lib B
        # forall t1 t2, equality lib t1 t2 A <=> equality lib t1 t2 B
      )
    ).
Proof.
  sp; repeat (rewrite <- fold_mkc_amember).
  pose proof (tequality_mkc_aequality_if_mem lib a a b b A B) as q.
  repeat (autodimp q hyp).
Qed.

(*
Lemma tequality_mkc_amember_sp {p} :
  forall lib (a b A B : @CTerm p),
    tequality lib (mkc_amember a A) (mkc_amember b B)
    <=>
    (
      tequality lib A B
      # (equality lib a b A {+} ccequivc lib a b)
    ).
Proof.
  sp; repeat (rewrite <- fold_mkc_amember).
  trw @tequality_mkc_aequality_sp; split; sp.
Qed.
*)

(*
Lemma aequality_commutes {p} :
  forall lib (T a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_aequality a1 a2 T) (mkc_aequality a3 a4 T)
    -> equality lib a1 a2 T
    -> equality lib a1 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_aequality in teq; sp;
    try (complete (apply equality_trans with (t2 := a2); auto));
    try (complete (spcast; apply equality_respects_cequivc_right with (t2 := a2); sp)).
Qed.

Lemma aequality_commutes2 {p} :
  forall lib (T a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_aequality a1 a2 T) (mkc_aequality a3 a4 T)
    -> equality lib a1 a2 T
    -> equality lib a1 a3 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_aequality in teq; sp;
  spcast; apply equality_respects_cequivc_right with (t2 := a1); auto;
  apply equality_refl in eq; auto.
Qed.

Lemma aequality_commutes3 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_aequality a1 a2 T) (mkc_aequality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a1 a3 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_aequality in teq; sp;
  spcast; apply equality_respects_cequivc_right with (t2 := a1); auto;
  apply equality_refl in eq; auto.
Qed.

Lemma aequality_commutes4 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_aequality a1 a2 T) (mkc_aequality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a1 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_aequality in teq; sp;
  try (complete (apply equality_trans with (t2 := a2); auto));
  try (complete (spcast; apply equality_respects_cequivc_right with (t2 := a2); sp)).
Qed.

Lemma aequality_commutes5 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_aequality a1 a2 T) (mkc_aequality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a2 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_aequality in teq; sp;
  spcast; apply equality_respects_cequivc_right with (t2 := a2); sp;
  apply equality_sym in eq; apply equality_refl in eq; auto.
Qed.
*)

(*
Lemma tequality_mkc_aequality_base_iff {p} :
  forall lib (t1 t2 t3 t4 : @CTerm p),
    tequality lib (mkc_aequality t1 t2 mkc_base) (mkc_aequality t3 t4 mkc_base)
    <=>
    (ccequivc lib t1 t3 # ccequivc lib t2 t4).
Proof.
  introv; split; intro k.

  - unfold tequality in k; exrepnd.
    inversion k0; try not_univ.
    allunfold @per_aeq; exrepnd.
    computes_to_value_isvalue.
    doneclose; try not_univ.
    allunfold @per_base; repnd.
    computes_to_value_isvalue; GC.
    allunfold @eqorceq.
    sp; discover; sp.

  - repnd; unfold tequality.
    exists (per_aeq_eq lib t1 t2 (ccequivc lib)).

    apply CL_aeq; unfold per_aeq.
    exists (@mkc_base p) (@mkc_base p) t1 t2 t3 t4 (@ccequivc p lib); dands; spcast;
      try (apply computes_to_valc_refl);
      try (apply iscvalue_mkc_aequality);
      try (apply iscvalue_mkc_base);
      try (complete (left; spcast; sp));
      auto.

    apply CL_base.
    unfold per_base; sp;
    try (spcast; apply computes_to_valc_refl);
    try (apply iscvalue_mkc_base);
    auto;

    try (introv; split; sp).
Qed.

Lemma tequality_aequality_if_eqorceq {p} :
  forall lib (t1 t2 t3 t4 A B : @CTerm p),
    tequality lib A B
    -> t1 ~=~(lib) t3 [+] equality lib t1 t3 A
    ->  t2 ~=~(lib) t4 [+] equality lib t2 t4 A
    -> tequality
         lib
         (mkc_aequality t1 t2 A)
         (mkc_aequality t3 t4 B).
Proof.
  introv Ht H13 H24.
  apply tequality_mkc_aequality.
  dorn H13; dorn H24; dands; auto; cpx; spcast.
  - applydup @tequality_sym in Ht. split; introv Hyp; rwgs H24; rwgs H13;
    eauto 2 with nequality.
  - applydup @tequality_sym in Ht. split; introv Hyp; rwgs H13.
    eapply tequality_preserving_equality; eauto.
    apply (equality_trans lib t1 t2 t4); auto.
    apply (equality_trans lib t3 t4 t2); auto.
    eapply tequality_preserving_equality; eauto.
    apply equality_sym; auto.
  - applydup @tequality_sym in Ht. split; introv Hyp; rwgs H24;
    eauto 4 with nequality.
  - applydup @tequality_sym in Ht. split; introv Hyp.
    eapply tequality_preserving_equality; eauto.
    apply (equality_trans lib t3 t1 t4); auto.
    apply equality_sym; auto.
    apply (equality_trans lib t1 t2 t4); auto.
    apply (equality_trans lib t1 t3 t2); auto.
    apply (equality_trans lib t3 t4 t2); auto.
    eapply tequality_preserving_equality; eauto.
    apply equality_sym; auto.
Qed.

Lemma tequality_mkc_amember_base {p} :
  forall lib (a b : @CTerm p),
    tequality lib (mkc_amember a mkc_base) (mkc_amember b mkc_base)
    <=>
    ccequivc lib a b.
Proof.
  introv.
  rw @tequality_mkc_amember; split; intro e; repnd.
  repdors; try (complete auto).
  rw @equality_in_base_iff in e2; auto.
  dands; try (complete sp).
  split; intro m; apply member_base.
Qed.
*)

Lemma aequality_on_closed_terms_is_a_type {p} :
  forall lib (A x y : @CTerm p), type lib A -> type lib (mkc_aequality x y A).
Proof.
  introv ta.
  apply type_mkc_aequality; auto.
Qed.

Lemma inhabited_mkc_aequality {p} :
  forall lib (A x y : @CTerm p),
    inhabited_type lib (mkc_aequality x y A) <=> equality lib x y A.
Proof.
  introv; split; intro k.
  { unfold inhabited_type in k; exrepnd.
    rw @equality_in_mkc_aequality in k0; sp. }
  { exists (mkc_refl x).
    rw <- @member_aequality_iff; sp. }
Qed.

Lemma inhabited_type_mkc_aequality_sym {p} :
  forall lib (A x y : @CTerm p),
    inhabited_type lib (mkc_aequality x y A)
    -> inhabited_type lib (mkc_aequality y x A).
Proof.
  introv inh.
  allrw @inhabited_mkc_aequality.
  apply equality_sym; sp.
Qed.

Lemma inhabited_type_mkc_aequality_trans {p} :
  forall lib (A x y z : @CTerm p),
    inhabited_type lib (mkc_aequality x y A)
    -> inhabited_type lib (mkc_aequality y z A)
    -> inhabited_type lib (mkc_aequality x z A).
Proof.
  introv inh1 inh2.
  allrw @inhabited_mkc_aequality.
  apply equality_trans with (t2 := y); sp.
Qed.

Lemma amember_if_inhabited {p} :
  forall lib (t1 t2 t T : @CTerm p),
    equality lib t1 t2 (mkc_amember t T)
    -> member lib t T.
Proof.
  introv; allrw <- @fold_mkc_amember; unfold member, equality, nuprl; intro i; exrepnd.

  inversion i1; try not_univ.
  allunfold @per_aeq; sp.
  computes_to_value_isvalue; subst.
  exists eqa; sp.
  subst.
  match goal with
  | [ H : _ <=2=> _ |- _ ] => apply H in i0
  end; unfold per_aeq_eq in i0; tcsp.
Qed.

(*
Lemma tequality_amember_in_uni_implies_tequality {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality
      lib
      (mkc_amember T1 (mkc_uni i))
      (mkc_amember T2 (mkc_uni i))
    -> type lib T1
    -> tequality lib T1 T2.
Proof.
  introv teq typ.
  rw @tequality_mkc_amember in teq; repnd.
  repdors.
  allapply @equality_in_uni; sp.
  spcast; apply type_respects_cequivc_right; sp.
Qed.

Lemma iff_inhabited_type_if_tequality_amemember {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality lib (mkc_amember T1 (mkc_uni i)) (mkc_amember T2 (mkc_uni i))
    -> (inhabited_type lib T1 <=> inhabited_type lib T2).
Proof.
  introv teq.
  rw @tequality_mkc_amember in teq; repnd.
  split; intro inh; repdors; allapply @equality_in_uni.
  - apply inhabited_type_tequality with (a := T1); sp.
  - spcast; apply inhabited_type_cequivc with (a := T1); sp.
  - apply inhabited_type_tequality with (a := T2); sp.
    apply tequality_sym; sp.
  - spcast; apply inhabited_type_cequivc with (a := T2); sp.
    apply cequivc_sym; sp.
Qed.

Lemma equality_mkc_aequality2_sp_in_uni {p} :
  forall lib i (a1 a2 b1 b2 A B : @CTerm p),
    equality lib (mkc_aequality a1 a2 A) (mkc_aequality b1 b2 B) (mkc_uni i)
    <=>
    (
      equality lib A B (mkc_uni i)
      # equorsq2 lib a1 b1 a2 b2 A
    ).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    introv e.
    unfold equality, nuprl in e; exrepnd.
    inversion e1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    rename eqa into eqi.
    ioneclose; subst; try not_univ.

    allunfold @per_aeq; exrepnd.
    computes_to_value_isvalue; GC.
    allfold (@nuprl p).
    allfold (@nuprli p lib j0).
    dands.

    + exists eq; sp.
      allrw.
      exists eqa; sp.

    + unfold equorsq2; dands; auto.

      * allapply @nuprli_implies_nuprl.
        pose proof (eqorceq_iff_equorsq lib A0 B0 a0 b0 eqa) as h.
        autodimp h hyp.
        apply h; auto.

      * allapply @nuprli_implies_nuprl.
        pose proof (eqorceq_iff_equorsq lib A0 B0 a3 b3 eqa) as h.
        autodimp h hyp.
        apply h; auto.

  - Case "<-".
    intro e.
    destruct e as [e eo].
    destruct eo as [eo1 eo2].
    unfold equality in e; exrepnd.
    inversion e1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli p lib j0).

    exists eq; sp.
    allrw.

    exists (per_aeq_eq lib a1 a2 eqa).
    apply CL_aeq; fold (@nuprli p lib j0).
    unfold per_aeq.
    exists A B a1 a2 b1 b2 eqa; dands; auto;
      try (complete (spcast; apply computes_to_valc_refl;
                     try (apply iscvalue_mkc_aequality))).

    { allapply @nuprli_implies_nuprl.
      pose proof (eqorceq_iff_equorsq lib A B a1 b1 eqa) as h.
      autodimp h hyp.
      apply h; auto. }

    { allapply @nuprli_implies_nuprl.
      pose proof (eqorceq_iff_equorsq lib A B a2 b2 eqa) as h.
      autodimp h hyp.
      apply h; auto. }
Qed.

Lemma equality_in_amember {p} :
  forall lib (a b t T : @CTerm p),
    equality lib a b (mkc_amember t T)
    <=> ((a ===>(lib) mkc_axiom)
         # (b ===>(lib) mkc_axiom)
         # member lib t T).
Proof.
  introv.
  rw <- @fold_mkc_amember.
  rw @equality_in_mkc_aequality.
  split; sp.
Qed.
*)

(* end hide *)
