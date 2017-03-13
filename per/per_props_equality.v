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

Lemma eq_per_eq_eq_iff_eq_equality {o} :
  forall lib (a1 b1 a2 b2 A1 A2 : @CTerm o) eqa1 eqa2,
    nuprl lib A1 eqa1
    -> nuprl lib A2 eqa2
    ->
    (
      ((per_eq_eq lib a1 b1 eqa1) <=2=> (per_eq_eq lib a2 b2 eqa2))
        <=>
        (forall x y z,
            (equality lib x a1 A1 # equality lib x b1 A1 # equality lib y z A1)
              <=>
              (equality lib x a2 A2 # equality lib x b2 A2 # equality lib y z A2))
    ).
Proof.
  introv n1 n2; split; intro w.

  - introv; split; intro h; repnd.

    + pose proof (w (mkc_prefl x y) (mkc_prefl x z)) as q.
      destruct q as [q q']; clear q'.
      autodimp q hyp.

      { exists x x y z; dands; spcast; eauto 2 with slow.
        - eapply equality_implies_eq; eauto.
          eapply equality_trans;[|eauto]; eauto 2 with nequality.
        - eapply equality_implies_eq; eauto 2 with nequality.
        - eapply equality_implies_eq; eauto 2 with nequality.
        - eapply equality_implies_eq; eauto 2 with nequality. }

      unfold per_eq_eq in q; exrepnd.
      computes_to_value_isvalue.

      dands; eauto 3 with slow nequality.

    + pose proof (w (mkc_prefl x y) (mkc_prefl x z)) as q.
      destruct q as [q' q]; clear q'.
      autodimp q hyp.

      { exists x x y z; dands; spcast; eauto 2 with slow.
        - eapply equality_implies_eq; eauto.
          eapply equality_trans;[|eauto]; eauto 2 with nequality.
        - eapply equality_implies_eq; eauto 2 with nequality.
        - eapply equality_implies_eq; eauto 2 with nequality.
        - eapply equality_implies_eq; eauto. }

      unfold per_eq_eq in q; exrepnd.
      computes_to_value_isvalue.

      dands; eauto 3 with slow nequality.

  - introv.
    unfold per_eq_eq; split; intro q; exrepnd; exists x1 x2 y1 y2; dands; auto.

    + pose proof (w a1 y1 y2) as q; destruct q as [q q']; clear q'.
      autodimp q hyp; dands; eauto 2 with slow nequality.
      { apply (equality_trans _ _ b1); eauto 3 with slow nequality. }
      repnd.
      eapply equality_implies_eq; eauto.
      eauto 3 with slow nequality.

    + pose proof (w x1 y1 y2) as q; destruct q as [q q']; clear q'.
      autodimp q hyp; dands; eauto 3 with slow nequality.
      { apply (equality_trans _ _ a1); eauto 3 with slow nequality. }
      repnd.
      eapply equality_implies_eq; eauto.
      eauto 3 with slow nequality.

    + pose proof (w x2 y1 y2) as q; destruct q as [q q']; clear q'.
      autodimp q hyp; dands; eauto 3 with slow nequality.
      { apply (equality_trans _ _ b1); eauto 3 with slow nequality. }
      repnd.
      eapply equality_implies_eq; eauto.
      eauto 3 with slow nequality.

    + pose proof (w a1 y1 y2) as q; destruct q as [q q']; clear q'.
      autodimp q hyp; dands; eauto 3 with slow nequality.
      { apply (equality_trans _ _ b1); eauto 3 with slow nequality. }
      repnd.
      eapply equality_implies_eq; eauto.

    + pose proof (w a2 y1 y2) as q; destruct q as [q' q]; clear q'.
      autodimp q hyp; dands; eauto 2 with slow nequality.
      { apply (equality_trans _ _ b2); eauto 3 with slow nequality. }
      repnd.
      eapply equality_implies_eq; try (exact n1).
      eauto 3 with slow nequality.

    + pose proof (w x1 y1 y2) as q; destruct q as [q' q]; clear q'.
      autodimp q hyp; dands; eauto 3 with slow nequality.
      { apply (equality_trans _ _ a2); eauto 3 with slow nequality. }
      repnd.
      eapply equality_implies_eq; try (exact n1).
      eauto 3 with slow nequality.

    + pose proof (w x2 y1 y2) as q; destruct q as [q' q]; clear q'.
      autodimp q hyp; dands; eauto 3 with slow nequality.
      { apply (equality_trans _ _ b2); eauto 3 with slow nequality. }
      repnd.
      eapply equality_implies_eq; try (exact n1).
      eauto 3 with slow nequality.

    + pose proof (w a2 y1 y2) as q; destruct q as [q' q]; clear q'.
      autodimp q hyp; dands; eauto 3 with slow nequality.
      { apply (equality_trans _ _ b2); eauto 3 with slow nequality. }
      repnd.
      eapply equality_implies_eq; eauto.
Qed.

Lemma type_mkc_equality {o} :
  forall lib (a1 a2 A : @CTerm o),
    type lib (mkc_equality a1 a2 A)
    <=>
    type lib A.
Proof.
  introv; split; introv ty.

  - unfold type in ty; exrepnd.
    inversion ty0; subst; try not_univ.

    match goal with
    | [ H : per_eq _ _ _ _ |- _ ] => rename H into h
    end.

    allunfold @per_eq; exrepnd.
    computes_to_value_isvalue; eauto 2 with slow.

  - allunfold @type; exrepnd.
    exists (per_eq_eq lib a1 a2 eq).
    apply CL_eq; unfold per_eq; fold @nuprl.

    exists A a1 a2 eq; dands; auto.
    spcast; apply computes_to_valc_refl; apply iscvalue_mkc_equality; auto.
Qed.

Lemma equality_mkc_equality_implies {p} :
  forall lib (t1 t2 T : @CTerm p) a b,
    equality lib a b (mkc_equality t1 t2 T)
    ->
    { x1 , x2 , y1 , y2 : CTerm
    , a ===>(lib) (mkc_prefl x1 y1)
    # b ===>(lib) (mkc_prefl x2 y2)
    # equality lib t1 x1 T
    # equality lib t2 x2 T
    # equality lib t1 t2 T
    # equality lib y1 y2 T }.
Proof.
  introv e.

  allunfold @equality; exrepnd.

  inversion e1; subst; try not_univ.

  allunfold_per.
  computes_to_value_isvalue.
  apply e in e0.
  unfold per_eq_eq in e0; exrepnd.
  exists x1 x2 y1 y2; dands; auto; exists eqa; dands; auto.
Qed.

Lemma equality_in_mkc_equality {p} :
  forall lib (t1 t2 T a b : @CTerm p),
    equality lib a b (mkc_equality t1 t2 T)
    <=>
    { x1 , x2 , y1, y2 : CTerm
    , a ===>(lib) (mkc_prefl x1 y1)
    # b ===>(lib) (mkc_prefl x2 y2)
    # equality lib t1 x1 T
    # equality lib t2 x2 T
    # equality lib t1 t2 T
    # equality lib y1 y2 T }.
Proof.
  introv; split; intro i.

  { apply equality_mkc_equality_implies; auto. }

  exrepnd.
  unfold equality in *; exrepnd.
  eapply nuprl_uniquely_valued in i3;[|exact i1].
  eapply nuprl_uniquely_valued in i4;[|exact i1].
  eapply nuprl_uniquely_valued in i5;[|exact i1].

  exists (per_eq_eq lib t1 t2 eq); dands; auto.

  { apply CL_eq.
    unfold per_eq.
    exists T t1 t2 eq; sp; spcast;
      try (apply computes_to_valc_refl);
      try (apply iscvalue_mkc_equality; auto);
      pose proof (nuprl_eq_implies_eqorceq_refl lib T T eq t1 t2); sp. }

  { exists x1 x2 y1 y2; dands; spcast; auto;
      try (complete (apply i3; auto));
      try (complete (apply i4; auto));
      try (complete (apply i5; auto)). }
Qed.

Lemma per_eq_eq_iff_ext_eq_mkc_equality {o} :
  forall lib a1 a2 b1 b2 (A B : @CTerm o) eqa eqb,
    nuprl lib A eqa
    -> nuprl lib B eqb
    -> ext_eq lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
       <=> (per_eq_eq lib a1 a2 eqa) <=2=> (per_eq_eq lib b1 b2 eqb).
Proof.
  introv n1 n2; split; intro h.

  - introv; unfold per_eq_eq; split; intro q; exrepnd.

    + eapply eq_equality0 in q3;[|eauto].
      eapply eq_equality0 in q4;[|eauto].
      eapply eq_equality0 in q5;[|eauto].
      eapply eq_equality0 in q1;[|eauto].
      pose proof (h (mkc_prefl x1 y1) (mkc_prefl x2 y2)) as z.
      destruct z as [z z']; clear z'.
      repeat (rw @equality_in_mkc_equality in z).
      autodimp z hyp.

      { exists x1 x2 y1 y2; dands; spcast; eauto 2 with slow. }

      exrepnd; computes_to_value_isvalue.
      exists x0 x3 y0 y3; dands; spcast; eauto 2 with slow;
        eapply equality_implies_eq; try (exact n2); auto.

    + eapply eq_equality0 in q3;[|eauto].
      eapply eq_equality0 in q4;[|eauto].
      eapply eq_equality0 in q5;[|eauto].
      eapply eq_equality0 in q1;[|eauto].
      pose proof (h (mkc_prefl x1 y1) (mkc_prefl x2 y2)) as z.
      destruct z as [z' z]; clear z'.
      repeat (rw @equality_in_mkc_equality in z).
      autodimp z hyp.

      { exists x1 x2 y1 y2; dands; spcast; eauto 2 with slow. }

      exrepnd; computes_to_value_isvalue.
      exists x0 x3 y0 y3; dands; spcast; eauto 2 with slow;
        eapply equality_implies_eq; try (exact n1); auto.

  - introv; repeat (rw @equality_in_mkc_equality); split; intro q; exrepnd.

    + pose proof (h a b) as z; unfold per_eq_eq in z; destruct z as [z z']; clear z'.
      autodimp z hyp; exrepnd.

      { exists x1 x2 y1 y2; dands; auto;
          eapply equality_implies_eq; try (exact n1); auto. }

      ccomputes_to_eqval.
      exists x1 x2 y1 y2; dands; spcast; auto;
        eapply eq_equality0; eauto.

    + pose proof (h a b) as z; unfold per_eq_eq in z; destruct z as [z' z]; clear z'.
      autodimp z hyp; exrepnd.

      { exists x1 x2 y1 y2; dands; auto;
          eapply equality_implies_eq; try (exact n2); auto. }

      ccomputes_to_eqval.
      exists x1 x2 y1 y2; dands; spcast; auto;
        eapply eq_equality0; eauto.
Qed.

Lemma tequality_mkc_equality {o} :
  forall lib (a1 a2 b1 b2 A B : @CTerm o),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=> (type lib A
         # type lib B
         # forall x y z,
              (equality lib x a1 A # equality lib x a2 A # equality lib y z A)
                <=>
                (equality lib x b1 B # equality lib x b2 B # equality lib y z B)).
Proof.
  introv.
  rw @tequality_iff_ext_eq.
  repeat (rw @type_mkc_equality).
  split; intro h; repnd; dands; auto.

  - destruct h0 as [eqa ta].
    destruct h1 as [eqb tb].
    eapply eq_per_eq_eq_iff_eq_equality; eauto.

    eapply per_eq_eq_iff_ext_eq_mkc_equality; eauto.

  - destruct h0 as [eqa ta].
    destruct h1 as [eqb tb].

    eapply per_eq_eq_iff_ext_eq_mkc_equality; eauto.
    eapply eq_per_eq_eq_iff_eq_equality; eauto.
Qed.

Lemma member_equality {o} :
  forall lib (t1 t2 T : @CTerm o),
    equality lib t1 t2 T
    -> equality lib (mkc_prefl t1 t1) (mkc_prefl t2 t2) (mkc_equality t1 t2 T).
Proof.
  unfold equality; introv h; exrepnd.
  exists (per_eq_eq lib t1 t2 eq); dands; spcast; tcsp.
  { apply CL_eq.
    unfold per_eq.
    exists T t1 t2 eq; sp; spcast; try computes_to_value_refl;
      pose proof (nuprl_eq_implies_eqorceq_refl lib T T eq t1 t2); sp. }
  { exists t1 t2 t1 t2; dands; auto; spcast;
      try (apply computes_to_valc_refl; eauto 3 with slow).
    { eapply equality_eq_refl;[eauto|];eauto. }
    { eapply equality_eq_refl;[eauto|].
      eapply equality_eq_sym;[eauto|]; eauto. }
  }
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

Lemma member_equality_iff {p} :
  forall lib (t1 t2 T : @CTerm p),
    equality lib t1 t2 T
    <=> { a , b : CTerm
        , equality lib a b T
        # equality lib (mkc_prefl t1 a) (mkc_prefl t2 b) (mkc_equality t1 t2 T) }.
Proof.
  introv; split; intro e.

  { exists t1 t2; dands; auto.
    apply member_equality; sp. }

  exrepnd.
  apply equality_in_mkc_equality in e1; exrepnd; computes_to_value_isvalue.
Qed.

(* begin hide *)

Lemma member_member_iff {p} :
  forall lib (t T : @CTerm p),
    member lib t T
    <=> { a : CTerm , member lib a T # member lib (mkc_prefl t a) (mkc_member t T) }.
Proof.
  sp; rewrite <- fold_mkc_member.
  rw @member_equality_iff.
  split; intro h; exrepnd.

  - exists a; dands; eauto 2 with slow.

  - exists a a; dands; eauto 2 with slow.
Qed.

Lemma member_mkc_member_implies {p} :
  forall lib (t T : @CTerm p) a,
    member lib a (mkc_member t T)
    ->
    { x , y : CTerm
    , a ===>(lib) (mkc_prefl x y)
    # member lib y T
    # equality lib t x T }.
Proof.
  introv e.
  rewrite <- fold_mkc_member in e.
  apply equality_mkc_equality_implies in e; exrepnd; ccomputes_to_eqval.
  exists x1 y1; dands; spcast; auto.
Qed.

Lemma member_equality_is_refl {p} :
  forall lib (t1 t2 T a b : @CTerm p),
    equality lib a b (mkc_equality t1 t2 T)
    -> { x1 , x2 , y1 , y2 : CTerm
       , a ===>(lib) (mkc_prefl x1 y1)
       # b ===>(lib) (mkc_prefl x2 y2) }.
Proof.
  introv e; apply equality_mkc_equality_implies in e; exrepnd.
  exists x1 x2 y1 y2; dands; auto.
Qed.

Lemma per_eq_eq_preserves_cequivc {o} :
  forall lib A (t1 t2 t3 t4 : @CTerm o) eq,
    nuprl lib A eq
    -> cequivc lib t1 t3
    -> cequivc lib t2 t4
    -> (per_eq_eq lib t1 t2 eq) <=2=> (per_eq_eq lib t3 t4 eq).
Proof.
  introv n ceq1 ceq2; introv; unfold per_eq_eq; split; intro h; exrepnd; spcast.

  - eapply eq_equality0 in h1;[|eauto].
    eapply eq_equality0 in h3;[|eauto].
    eapply eq_equality0 in h4;[|eauto].
    eapply eq_equality0 in h5;[|eauto].

    exists x1 x2 y1 y2; dands; spcast; auto;
      eapply equality_implies_eq; try (exact n);
        eauto 3 with slow nequality.

  - eapply eq_equality0 in h1;[|eauto].
    eapply eq_equality0 in h3;[|eauto].
    eapply eq_equality0 in h4;[|eauto].
    eapply eq_equality0 in h5;[|eauto].

    exists x1 x2 y1 y2; dands; spcast; auto;
      eapply equality_implies_eq; try (exact n);
        eauto 2 with slow nequality.

    + eapply equality_respects_cequivc_left;[apply cequivc_sym;eauto|].
      eapply equality_respects_cequivc_right;[apply cequivc_sym;eauto|].
      auto.

    + eapply equality_respects_cequivc_left;[apply cequivc_sym;eauto|]; auto.

    + eapply equality_respects_cequivc_left;[apply cequivc_sym;eauto|]; auto.
Qed.

Lemma tequality_equality_if_cequivc {p} :
  forall lib (t1 t2 t3 t4 A B : @CTerm p),
    tequality lib A B
    -> cequivc lib t1 t3
    -> cequivc lib t2 t4
    -> tequality lib (mkc_equality t1 t2 A) (mkc_equality t3 t4 B).
Proof.
  unfold tequality, equality; introv teq ceq1 ceq2; exrepnd.
  exists (per_eq_eq lib t1 t2 eq).

  split; try (apply CL_eq; unfold per_eq; try (fold (nuprl lib))).

  - exists A t1 t2 eq; sp; spcast;
      try (apply computes_to_valc_refl);
      try (apply iscvalue_mkc_equality; auto);
      eauto 2 with slow.

  - exists B t3 t4 eq; sp; spcast;
      try (apply computes_to_valc_refl);
      try (apply iscvalue_mkc_equality; auto);
      eauto 2 with slow.

    destruct teq0 as [teq1 teq2].
    eapply per_eq_eq_preserves_cequivc; eauto.
Qed.

Lemma per_eq_eq_iff_equality {o} :
  forall lib (A : @CTerm o) eq a b t u,
    nuprl lib A eq
    ->
    (
      per_eq_eq lib a b eq t u
      <=>
      { x1 , x2 , y1 , y2 : CTerm
      , equality lib a b A
      # equality lib a x1 A
      # equality lib b x2 A
      # equality lib y1 y2 A
      # t ===>(lib) (mkc_prefl x1 y1)
      # u ===>(lib) (mkc_prefl x2 y2) }
    ).
Proof.
  introv n; split; intro h; exrepnd; spcast.

  - unfold per_eq_eq in h; exrepnd; spcast.

    exists x1 x2 y1 y2; dands; spcast; auto.
    + apply (equality_eq lib A a b eq); auto.
    + apply (equality_eq lib A a x1 eq); auto.
    + apply (equality_eq lib A b x2 eq); auto.
    + apply (equality_eq lib A y1 y2 eq); auto.

  - exists x1 x2 y1 y2; dands; spcast; auto; eapply equality_eq; eauto.
Qed.

Hint Resolve equality_refl : slow.

(*
Lemma per_eq_eq_iff_equality_refl {o} :
  forall lib (A : @CTerm o) eq a b t u,
    nuprl lib A eq
    ->
    (
      per_eq_eq lib a b eq (mkc_refl t) (mkc_refl u)
      <=>
      (equality lib a b A
       # equality lib a t A
       # equality lib b u A)
    ).
Proof.
  introv n.
  rw (per_eq_eq_iff_equality lib A eq a b (mkc_refl t) (mkc_refl u) n).
  split; intro h; exrepnd; spcast; computes_to_value_isvalue.
  exists t u; dands; spcast; auto;
    try (apply computes_to_valc_refl; eauto 2 with slow).
Qed.

Lemma per_eq_eq_iff_equality_refl_eq {o} :
  forall lib (A : @CTerm o) eq a b,
    nuprl lib A eq
    ->
    (
      per_eq_eq lib a b eq (mkc_refl a) (mkc_refl b)
      <=>
      equality lib a b A
    ).
Proof.
  introv n.
  rw (per_eq_eq_iff_equality_refl lib A eq a b a b n).
  split; intro h; repnd; dands; auto; eauto 2 with slow.
  { eapply equality_refl; eauto. }
  { eapply equality_refl; apply equality_sym; eauto. }
Qed.
*)

Lemma tequality_mkc_equality_implies {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    ->
    (
      type lib A
      # type lib B
      # (equality lib a1 a2 A <=> equality lib b1 b2 B)
    ).
Proof.
  introv teq.
  apply tequality_mkc_equality in teq; repnd.
  dands; auto.
  split; intro h.

  - pose proof (teq a1 a1 a1) as q; destruct q as [q q']; clear q'.
    autodimp q hyp; repnd; dands; eauto 3 with slow nequality.

  - pose proof (teq b1 b1 b1) as q; destruct q as [q' q]; clear q'.
    autodimp q hyp; repnd; dands; eauto 3 with slow nequality.
Qed.

Lemma tequality_mkc_equality_in_universe_true {p} :
  forall lib (a1 b1 a2 b2 : @CTerm p) i,
    tequality lib (mkc_equality a1 b1 (mkc_uni i)) (mkc_equality a2 b2 (mkc_uni i))
    -> equality lib a1 b1 (mkc_uni i)
    -> equality lib a2 b2 (mkc_uni i).
Proof.
  introv t e.
  allapply @tequality_mkc_equality_implies; sp.
  apply t; auto.
Qed.

Lemma equality_in_universe {p} :
  forall lib (a1 b1 a2 b2 : @CTerm p) i,
    tequality lib (mkc_equality a1 b1 (mkc_uni i)) (mkc_equality a2 b2 (mkc_uni i))
    -> equality lib a1 b1 (mkc_uni i)
    -> tequality lib a2 b2.
Proof.
  introv t e.
  apply tequality_mkc_equality_in_universe_true in t; sp.
  apply @equality_in_uni with (i := i); sp.
Qed.

(*
Lemma ext_eq_mkc_equality_iff {o} :
  forall lib (a1 a2 b1 b2 A B : @CTerm o),
    ext_eq lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=> (equality lib a1 a2 A <=> equality lib b1 b2 B).
Proof.
  introv; split; intro h.

  - split; intro e.

    + pose proof (h (mkc_refl a1) (mkc_refl a2)) as z; clear h.
      rw <- @member_equality_iff in z.
      apply z in e; clear z.
      apply equality_mkc_equality_implies in e; exrepnd; auto.

    + pose proof (h (mkc_refl b1) (mkc_refl b2)) as z; clear h.
      rw <- @member_equality_iff in z.
      apply z in e; clear z.
      apply equality_mkc_equality_implies in e; exrepnd; auto.

  - introv; split; intro z; apply equality_in_mkc_equality in z;
      apply equality_in_mkc_equality; exrepnd; spcast;
        appdup h in z1; exists x1 x2; dands; spcast; auto.

      *

Abort.
*)

(*
Lemma ext_eq_mkc_equality_iff {o} :
  forall lib (a1 a2 b1 b2 A B : @CTerm o),
    ext_eq lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=>
    (
      (forall a, equality lib a a1 A -> equality lib a a2 A -> equality lib a b1 B # equality lib a b2 B)
      #
      (forall b, equality lib b b1 B -> equality lib b b2 B -> equality lib b a1 A # equality lib b a2 A)
    ).
Proof.
  introv; split; intro h.

  - split; introv e1 e2.

    + pose proof (h (mkc_refl a) (mkc_refl a1)) as z; clear h.
      destruct z as [z z']; clear z'.
      autodimp z hyp.
      { apply equality_in_mkc_equality.
        exists a a1; dands; spcast; auto; eauto 3 with slow nequality;
          try (apply computes_to_valc_refl; eauto 2 with slow). }
      apply equality_in_mkc_equality in z; exrepnd; spcast; computes_to_value_isvalue.
      dands; eauto 3 with nequality.

    + pose proof (h (mkc_refl b) (mkc_refl b1)) as z; clear h.
      destruct z as [z' z]; clear z'.
      autodimp z hyp.
      { apply equality_in_mkc_equality.
        exists b b1; dands; spcast; auto; eauto 3 with slow nequality;
          try (apply computes_to_valc_refl; eauto 2 with slow). }
      apply equality_in_mkc_equality in z; exrepnd; spcast; computes_to_value_isvalue.
      dands; eauto 3 with nequality.

  - introv; split; intro z; apply equality_in_mkc_equality in z;
      apply equality_in_mkc_equality; exrepnd; spcast;
        exists x1 x2; dands; spcast; auto.

    + pose proof (h0 x1) as q; repeat (autodimp q hyp); eauto 3 with nequality.
      repnd; eauto 2 with nequality.

    + pose proof (h0 x2) as q; repeat (autodimp q hyp); eauto 3 with nequality.
      repnd; eauto 2 with nequality.

    + pose proof (h0 x1) as q; repeat (autodimp q hyp); eauto 3 with nequality.
      repnd; eauto 3 with nequality.

    + pose proof (h x1) as q; repeat (autodimp q hyp); eauto 3 with nequality.
      repnd; eauto 2 with nequality.

    + pose proof (h x2) as q; repeat (autodimp q hyp); eauto 3 with nequality.
      repnd; eauto 2 with nequality.

    + pose proof (h x1) as q; repeat (autodimp q hyp); eauto 3 with nequality.
      repnd; eauto 3 with nequality.
Qed.
*)

(*
Lemma tequality_mkc_equality {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=>
    (tequality lib A B
     # (forall x,
           (equality lib x a1 A # equality lib x a2 A)
             <=>
             (equality lib x b1 B # equality lib x b2 B))).
Proof.
  apply tequality_iff_ext_eq2.
Qed.
*)

(*
Lemma tequality_mkc_equality_sp {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
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
    allunfold @per_eq; exrepnd.
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

    exists (per_eq_eq lib a1 a2 eq).
    apply CL_eq; unfold per_eq; fold @nuprl.

    exists A B a1 a2 b1 b2 eq; dands; auto.
    spcast; apply computes_to_valc_refl; apply iscvalue_mkc_equality; auto.
    spcast; apply computes_to_valc_refl; apply iscvalue_mkc_equality; auto.
    apply equality_or_cequivc_eqorceq with (a := a1) (b := b1) in n.
    apply n; sp.
    apply equality_or_cequivc_eqorceq with (a := a2) (b := b2) in n.
    apply n; sp; try (intros; split; auto).
Qed.
*)

Lemma tequality_mkc_equality_if_equal {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib A B
    -> equality lib a1 b1 A
    -> equality lib a2 b2 A
    -> tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B).
Proof.
  introv teq e1 e2.
  rw @tequality_mkc_equality; dands; auto; eauto 2 with slow.
  introv; split; intro h; repnd; dands.
  - eapply tequality_preserving_equality;[|eauto].
    eauto 3 with nequality.
  - eapply tequality_preserving_equality;[|eauto].
    eauto 3 with nequality.
  - eauto 3 with slow nequality.
  - eapply tequality_preserving_equality;[|apply tequality_sym;eauto].
    eapply equality_trans;[exact h0|]; eauto 3 with nequality.
  - eapply tequality_preserving_equality;[|apply tequality_sym;eauto].
    eapply equality_trans;[exact h1|]; eauto 3 with nequality.
  - eauto 3 with slow nequality.
Qed.

(*
Lemma tequality_mkc_equality2 {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=>
    (
      tequality lib A B
      # (equality lib a1 a2 A <=> equality lib b1 b2 B)
      # equorsq2 lib a1 b1 a2 b2 A
    ).
Proof.
  intros.
  rw @tequality_mkc_equality.
  repeat (rw @fold_equorsq).
  rw @fold_equorsq2; sp.
Qed.
*)

(*
Lemma tequality_mkc_equality2_sp {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=>
    (
      tequality lib A B
      # equorsq2 lib a1 b1 a2 b2 A
    ).
Proof.
  intros.
  rw @tequality_mkc_equality_sp.
  repeat (rw @fold_equorsq).
  rw @fold_equorsq2; sp.
Qed.
*)

Lemma tequality_mkc_member {p} :
  forall lib (a b A B : @CTerm p),
    tequality lib (mkc_member a A) (mkc_member b B)
    <=>
    (
      type lib A
      # type lib B
      # (forall x y z : CTerm,
            (equality lib x a A # equality lib y z A)
              <=> (equality lib x b B # equality lib y z B))
    ).
Proof.
  sp; repeat (rewrite <- fold_mkc_member).
  trw @tequality_mkc_equality; split; intro h; repnd; dands; tcsp; introv;
    split; introv q; repnd; dands; auto;
      try (complete (pose proof (h x y z) as w; destruct w as [w w']; clear w'; autodimp w hyp; tcsp));
      try (complete (pose proof (h x y z) as w; destruct w as [w' w]; clear w'; autodimp w hyp; tcsp)).
Qed.

(*
Lemma tequality_mkc_member_sp {p} :
  forall lib (a b A B : @CTerm p),
    tequality lib (mkc_member a A) (mkc_member b B)
    <=>
    (
      tequality lib A B
      # (equality lib a b A {+} ccequivc lib a b)
    ).
Proof.
  sp; repeat (rewrite <- fold_mkc_member).
  trw @tequality_mkc_equality_sp; split; sp.
Qed.
*)

Lemma equality_commutes {p} :
  forall lib (T a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 T)
    -> equality lib a1 a2 T
    -> equality lib a1 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; repnd.
  pose proof (teq a1 a1 a1) as q.
  apply q; dands; tcsp; eauto 3 with slow nequality.
Qed.

Lemma equality_commutes2 {p} :
  forall lib (T a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 T)
    -> equality lib a1 a2 T
    -> equality lib a1 a3 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; repnd.
  pose proof (teq a1 a1 a1) as q.
  apply q; dands; tcsp; eauto 3 with slow nequality.
Qed.

Lemma equality_commutes3 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a1 a3 T.
Proof.
  introv teq e.
  rw @tequality_mkc_equality in teq; repnd.

  pose proof (teq a1 a1 a1) as q; destruct q as [q q']; clear q'.
  repeat (autodimp q hyp); dands; tcsp; repnd; eauto 3 with slow nequality.

  pose proof (teq a3 a3 a3) as z; destruct z as [z' z]; clear z'.
  repeat (autodimp z hyp); dands; tcsp; repnd; eauto 3 with slow nequality.
Qed.

Lemma equality_commutes4 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a1 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; repnd.

  pose proof (teq a1 a1 a1) as q; destruct q as [q q']; clear q'.
  repeat (autodimp q hyp); dands; tcsp; repnd; eauto 3 with slow nequality.

  pose proof (teq a4 a4 a4) as z; destruct z as [z' z]; clear z'.
  repeat (autodimp z hyp); dands; tcsp; repnd; eauto 3 with slow nequality.
Qed.

Lemma equality_commutes5 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a2 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; repnd.

  pose proof (teq a2 a2 a2) as q; destruct q as [q q']; clear q'.
  repeat (autodimp q hyp); dands; tcsp; repnd; eauto 3 with slow nequality.

  pose proof (teq a4 a4 a4) as z; destruct z as [z' z]; clear z'.
  repeat (autodimp z hyp); dands; tcsp; repnd; eauto 3 with slow nequality.
Qed.

(*
Not true anymore!
Lemma tequality_mkc_equality_base_iff {p} :
  forall lib (t1 t2 t3 t4 : @CTerm p),
    tequality lib (mkc_equality t1 t2 mkc_base) (mkc_equality t3 t4 mkc_base)
    <=>
    (ccequivc lib t1 t3 # ccequivc lib t2 t4).
Proof.
  introv; split; intro k.

  - unfold tequality in k; exrepnd.

    inversion k0; try not_univ.
    allunfold @per_eq; exrepnd.
    computes_to_value_isvalue.
    doneclose; try not_univ.
    allunfold @per_base; repnd.
    computes_to_value_isvalue; GC.
    allunfold @eqorceq.
    sp; discover; sp.

  - repnd; unfold tequality.
    exists (per_eq_eq lib t1 t2 (ccequivc lib)).
    apply CL_eq; unfold per_eq.
    exists (@mkc_base p) (@mkc_base p) t1 t2 t3 t4 (@ccequivc p lib); dands; spcast;
      try (apply computes_to_valc_refl);
      try (apply iscvalue_mkc_equality);
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
*)

(*
Lemma tequality_equality_if_eqorceq {p} :
  forall lib (t1 t2 t3 t4 A B : @CTerm p),
    tequality lib A B
    -> t1 ~=~(lib) t3 [+] equality lib t1 t3 A
    ->  t2 ~=~(lib) t4 [+] equality lib t2 t4 A
    -> tequality lib (mkc_equality t1 t2 A)
                 (mkc_equality t3 t4 B).
Proof.
  introv Ht H13 H24.
  apply tequality_mkc_equality.
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
 *)


Lemma tequality_mkc_member_base {p} :
  forall lib (a b : @CTerm p),
    tequality lib (mkc_member a mkc_base) (mkc_member b mkc_base)
    <=>
    ccequivc lib a b.
Proof.
  introv.
  rw @tequality_mkc_member; split; intro e; repnd; dands; eauto 2 with slow.

  - pose proof (e a a a) as h; destruct h as [h h']; clear h'.
    autodimp h hyp; eauto 2 with slow; repnd.
    apply equality_in_base in h0; auto.

  - introv; split; intro eb; repnd.

    + apply equality_in_base in eb.
      apply equality_in_base in eb0.
      dands; apply equality_in_base_iff; spcast;
        eapply cequivc_trans;eauto.

    + apply equality_in_base in eb.
      apply equality_in_base in eb0.
      dands; apply equality_in_base_iff; spcast;
        eapply cequivc_trans;eauto.
      apply cequivc_sym; auto.
Qed.

Lemma equality_on_closed_terms_is_a_type {p} :
  forall lib (A x y : @CTerm p), type lib A -> type lib (mkc_equality x y A).
Proof.
  introv ta.
  apply type_mkc_equality; auto.
Qed.

Lemma type_mkc_equality2 {p} :
  forall lib (A : @CTerm p), (forall x y, type lib (mkc_equality x y A)) <=> type lib A.
Proof.
  introv; split; intro k; introv.
  - pose proof (k mkc_axiom mkc_axiom) as k.
    apply type_mkc_equality in k; auto.
  - apply type_mkc_equality; auto.
Qed.

Lemma inhabited_mkc_equality {p} :
  forall lib (A x y : @CTerm p),
    inhabited_type lib (mkc_equality x y A) <=> equality lib x y A.
Proof.
  introv; split; intro k.

  { unfold inhabited_type in k; exrepnd.
    rw @equality_in_mkc_equality in k0; sp. }

  { exists (mkc_prefl x x).
    apply (equality_trans _ _ (mkc_prefl y y)).
    - apply member_equality; sp.
    - apply equality_sym; apply member_equality; sp. }
Qed.

Lemma inhabited_type_mkc_equality_sym {p} :
  forall lib (A x y : @CTerm p),
    inhabited_type lib (mkc_equality x y A)
    -> inhabited_type lib (mkc_equality y x A).
Proof.
  introv inh.
  allrw @inhabited_mkc_equality.
  apply equality_sym; sp.
Qed.

Lemma inhabited_type_mkc_equality_trans {p} :
  forall lib (A x y z : @CTerm p),
    inhabited_type lib (mkc_equality x y A)
    -> inhabited_type lib (mkc_equality y z A)
    -> inhabited_type lib (mkc_equality x z A).
Proof.
  introv inh1 inh2.
  allrw @inhabited_mkc_equality.
  apply equality_trans with (t2 := y); sp.
Qed.

Lemma member_if_inhabited {p} :
  forall lib (t1 t2 t T : @CTerm p),
    equality lib t1 t2 (mkc_member t T)
    -> member lib t T.
Proof.
  introv; allrw <- @fold_mkc_member; unfold member, equality, nuprl; intro i; exrepnd.

  inversion i1; try not_univ.
  allunfold @per_eq; sp.
  computes_to_value_isvalue; repeat subst.
  exists eqa; sp.
  match goal with
  | [ H : _ <=2=> _ |- _ ] => apply H in i0
  end.
  unfold per_eq_eq in i0; exrepnd; auto.
Qed.

(*
Lemma tequality_in_uni_implies_tequality {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality
      lib
      (mkc_member T1 (mkc_uni i))
      (mkc_member T2 (mkc_uni i))
    -> type lib T1
    -> tequality lib T1 T2.
Proof.
  introv teq typ.
  rw @tequality_mkc_member in teq; repnd.

  repdors.
  allapply @equality_in_uni; sp.
  spcast; apply type_respects_cequivc_right; sp.
Qed.
 *)

Lemma tequality_in_uni_implies_tequality {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality
      lib
      (mkc_member T1 (mkc_uni i))
      (mkc_member T2 (mkc_uni i))
    -> type lib T1
    -> (forall x, equality lib x T1 (mkc_uni i) <=> equality lib x T2 (mkc_uni i)).
Proof.
  introv teq typ.
  rw @tequality_mkc_member in teq; repnd; auto.
  introv.
  pose proof (teq x x x) as q; destruct q as [q1 q2].
  split; intro h;[autodimp q1 hyp|autodimp q2 hyp];
    dands; tcsp; eauto 3 with slow nequality.
Qed.

(*

Not true anymore

Lemma iff_inhabited_type_if_tequality_mem {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality lib (mkc_member T1 (mkc_uni i)) (mkc_member T2 (mkc_uni i))
    -> (inhabited_type lib T1 <=> inhabited_type lib T2).
Proof.
  introv teq.
  rw @tequality_mkc_member in teq; repnd.
  split; intro inh; repdors; allapply @equality_in_uni.

  { apply inhabited_type_tequality with (a := T1); sp.
    spcast; apply inhabited_type_cequivc with (a := T1); sp.

    apply inhabited_type_tequality with (a := T2); sp.
    apply tequality_sym; sp.
    spcast; apply inhabited_type_cequivc with (a := T2); sp.
    apply cequivc_sym; sp.
Qed.
*)

Lemma equality_in_member {o} :
  forall lib (a b t T : @CTerm o),
    equality lib a b (mkc_member t T)
    <=> { x , y , z , w : @CTerm o
        , a ===>(lib) (mkc_prefl x z)
        # b ===>(lib) (mkc_prefl y w)
        # equality lib t x T
        # equality lib t y T
        # equality lib z w T }.
Proof.
  introv.
  rw <- @fold_mkc_member.
  rw @equality_in_mkc_equality.
  split; intro xx; exrepnd.

  - exists x1 x2 y1 y2; dands; auto.

  - exists x y z w; dands; auto.
    eapply equality_refl; eauto.
Qed.

Hint Resolve iscvalue_mkc_equality : slow.
Hint Resolve eq_equality4 : slow.

Lemma typei_mkc_equality {p} :
  forall lib i (a1 a2 A : @CTerm p),
    typei lib i (mkc_equality a1 a2 A) <=> typei lib i A.
Proof.
  introv; unfold typei, tequalityi, equality; split; intro h; exrepnd.

  - inversion h1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    exists eq; dands; auto.
    apply e in h0; apply e.
    unfold univi_eq in *; exrepnd.
    destruct h2 as [h h']; GC.
    inversion h; subst; try not_univ.

    match goal with
    | [ H : per_eq _ _ _ _ |- _ ] => rename H into q
    end.

    unfold per_eq in q; exrepnd; computes_to_value_isvalue.
    fold (nuprli lib j0) in *.
    exists eqa0; split; auto.

  - inversion h1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    exists eq; dands; auto.
    apply e in h0; apply e.
    unfold univi_eq in *; exrepnd.
    destruct h2 as [h h']; GC.

    exists (per_eq_eq lib a1 a2 eqa).
    split; apply CL_eq; exists A a1 a2 eqa; dands; spcast; eauto 2 with slow.
Qed.

Lemma equality_mkc_equality2_sp_in_uni {p} :
  forall lib i (a1 a2 b1 b2 A B : @CTerm p),
    equality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) (mkc_uni i)
    <=>
    (member lib A (mkc_uni i)
     # member lib B (mkc_uni i)
     # forall x y z,
          (equality lib x a1 A # equality lib x a2 A # equality lib y z A)
            <=>
            (equality lib x b1 B # equality lib x b2 B # equality lib y z B)).
Proof.
  introv.
  rw @tequalityi_iff_ext_eq.
  allrw @typei_mkc_equality.

  split; intro h; repnd; dands; auto.

  - allrw @typei_iff_nuprli; exrepnd.
    eapply eq_per_eq_eq_iff_eq_equality; eauto 2 with slow.
    eapply per_eq_eq_iff_ext_eq_mkc_equality; eauto 2 with slow.

  - allrw <- @typei_iff_member_mkc_uni.
    allrw @typei_iff_nuprli; exrepnd.
    eapply eq_per_eq_eq_iff_eq_equality in h; eauto 2 with slow.
    eapply per_eq_eq_iff_ext_eq_mkc_equality; eauto 2 with slow.
Qed.


Lemma tequality_implies_if_equality {o} :
  forall lib (a1 a2 b1 b2 A B : @CTerm o),
    equality lib a1 a2 A
    -> equality lib b1 b2 B
    -> tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    -> tequality lib A B.
Proof.
  introv e1 e2 teq.
  allrw @tequality_mkc_equality; repnd.
  rw @tequality_iff_ext_eq; dands; auto.
  introv; split; intro h.

  - pose proof (teq a1 a b) as q; destruct q as [q q']; clear q'.
    autodimp q hyp; dands; repnd; eauto 3 with slow nequality.

  - pose proof (teq b1 a b) as q; destruct q as [q' q]; clear q'.
    autodimp q hyp; dands; repnd; eauto 3 with slow nequality.
Qed.


(* end hide *)

(* !!MOVE *)
Lemma covered_prefl_same {o} :
  forall (t : @NTerm o) l, covered (mk_prefl t t) l <=> covered t l.
Proof.
  introv.
  rw @covered_prefl; split; tcsp.
Qed.

Lemma tequality_implies_if_member {o} :
  forall lib (a b A B : @CTerm o),
    member lib a A
    -> member lib b B
    -> tequality lib (mkc_member a A) (mkc_member b B)
    -> tequality lib A B.
Proof.
  introv m1 m2 teq.
  eapply tequality_implies_if_equality; eauto.
  allrw @fold_mkc_member; auto.
Qed.
