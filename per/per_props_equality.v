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
Require Export per_props_function.

(*Require Export per_props_uni.*)


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

(* MOVE *)
Lemma implies_all_in_bar_ext_trivial_bar {o} :
  forall (lib : @library o) F,
    in_ext_ext lib F
    -> all_in_bar_ext (trivial_bar lib) F.
Proof.
  introv i br ext; simpl in *.
  eapply i; eauto 3 with slow.
Qed.

(* MOVE *)
Lemma choice_ext_lib_eq {o} :
  forall lib (a b A : @CTerm o),
    (forall lib' (x : lib_extends lib' lib), equality lib' a b A)
    -> {eqa : lib-per(lib,o),
        forall lib' (x : lib_extends lib' lib), nuprl lib' A A (eqa lib' x) # eqa lib' x a b}.
Proof.
  introv F.

  pose proof (FunctionalChoice_on
                {lib' : library & lib_extends lib' lib}
                per(o)
                (fun x y => nuprl (projT1 x) A A y # y a b)) as C.
  autodimp C hyp.

  {
    unfold equality in F.
    introv; exrepnd; simpl in *; auto.
  }

  clear F.
  exrepnd.

  exists (fun (lib' : library) (ext : lib_extends lib' lib) =>
            f (existT (fun lib' => lib_extends lib' lib) lib' ext)).
  introv.
  pose proof (C0 (existT (fun lib' => lib_extends lib' lib) lib' x)) as C.
  simpl in *; auto.
Qed.

Lemma member_equality {o} :
  forall lib (t1 t2 T : @CTerm o),
    equality lib t1 t2 T
    -> member lib mkc_axiom (mkc_equality t1 t2 T).
Proof.
  introv h.
  assert (forall lib' (x : lib_extends lib' lib), equality lib' t1 t2 T) as q by eauto 3 with slow.
  clear h.
  apply choice_ext_lib_eq in q; exrepnd.

  exists (per_eq_eq lib t1 t2 eqa).
  dands; auto.

  {
    apply CL_eq.
    unfold per_eq_bar.
    exists T T t1 t2 t1 t2 eqa.
    dands; auto.
    exists (trivial_bar lib); dands; eauto 3 with slow refl.
    fold (@nuprl o) in *.
    apply implies_all_in_bar_ext_trivial_bar.
    introv; apply q0.
  }

  {
    unfold per_eq_eq.
    exists (trivial_bar lib).
    unfold per_eq_eq1.
    apply implies_all_in_bar_ext_trivial_bar.
    introv; dands; spcast; eauto 3 with slow refl; try apply q0.
  }
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

Lemma member_equality_iff {o} :
  forall lib (t1 t2 T : @CTerm o),
    equality lib t1 t2 T
    <=> member lib mkc_axiom (mkc_equality t1 t2 T).
Proof.
  introv; split; intro e.

  { apply member_equality; sp. }

  allunfold @member; allunfold @equality; exrepnd.

  inversion e1; subst; try not_univ; clear e1; [].
  rename_hyp_with @per_eq_bar h.
  unfold per_eq_bar in *; exrepnd.
  apply h0 in e0; clear h0.
  fold (@nuprl o) in *.

  unfold per_eq_eq, per_eq_eq1 in e0.

  (* have another clause in [close] for bared types?
     If a type is defined at a bar of a library, then it is defined at the library?
   *)

  SearchAbout computes_to_valc_ceq_bar mkc_equality.

XXXXXX

  allunfold_per.
  computes_to_value_isvalue.
  exists eqa; sp.
  discover; sp.
Qed.

(* begin hide *)

Lemma member_member_iff {p} :
  forall lib (t T : @CTerm p),
    member lib t T
    <=> member lib mkc_axiom (mkc_member t T).
Proof.
  sp; rewrite <- fold_mkc_member.
  apply member_equality_iff.
Qed.

Lemma if_member_vsubtype {p} :
  forall lib (A : @CTerm p) v B,
    member lib mkc_axiom (mkc_vsubtype A v B)
    -> forall x y, equality lib x y A -> equality lib x y B.
Proof.
  introv; rewrite <- fold_mkc_vsubtype; introv m e.
  apply member_member_iff in m.

  apply @if_member_function with (f := mkc_id)
                                  (v := v)
                                  (B := cvterm_var v B) in e; sp.


  apply equality_respects_cequivc_left with (t := x) in e;
    try (apply reduces_toc_implies_cequivc; apply reduces_toc_apply_id).
  apply equality_respects_cequivc_right with (t := y) in e;
    try (apply reduces_toc_implies_cequivc; apply reduces_toc_apply_id).

  rewrite substc_cvterm_var in e; sp.
Qed.

Lemma member_equality_is_axiom {p} :
  forall lib (t1 t2 T a b : @CTerm p),
    equality lib a b (mkc_equality t1 t2 T)
    -> a ===>(lib) mkc_axiom # b ===>(lib) mkc_axiom.
Proof.
  unfold equality, nuprl; introv e; exrepd.
  inversion c; subst; try not_univ.

  allunfold @per_eq; exrepnd.
  computes_to_value_isvalue.
  discover; sp.
Qed.

Lemma tequality_equality_if_cequivc {p} :
  forall lib (t1 t2 t3 t4 A B : @CTerm p),
    tequality lib A B
    -> cequivc lib t1 t3
    -> cequivc lib t2 t4
    -> tequality lib (mkc_equality t1 t2 A)
                 (mkc_equality t3 t4 B).
Proof.
  unfold tequality, equality; sp.
  exists (fun a b : @CTerm p =>
            a ===>(lib) mkc_axiom
            # b ===>(lib) mkc_axiom
            # eq t3 t4).
  unfold nuprl.
  apply CL_eq; unfold per_eq.
  exists A B t1 t2 t3 t4 eq; sp; spcast;
  try (apply computes_to_valc_refl);
  try (apply iscvalue_mkc_equality; auto);
  try (unfold eqorceq; right; auto; spcast; sp).

  allapply @nuprl_refl.
  split; sp; spcast.

  apply (eqorceq_commutes_nuprl lib) with (a := t3) (c := t4) (A := A) (B := A); sp.
  apply @eqorceq_sym_trans with (A := A) (B := A); sp; try (complete (right; spcast; sp)).
  apply @eqorceq_sym_trans with (A := A) (B := A); sp; try (complete (right; spcast; sp)).

  apply (eqorceq_commutes_nuprl lib) with (a := t1) (c := t2) (A := A) (B := A); sp;
  try (complete (right; spcast; sp)).
Qed.

Lemma tequality_mkc_equality_implies {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    ->
    (
      tequality lib A B
      # (equality lib a1 a2 A -> equality lib b1 b2 B)
      # (equality lib a1 b1 A {+} ccequivc lib a1 b1)
    ).
Proof.
  unfold tequality, nuprl; introv teq; exrepnd.
  inversion teq0; subst; try (not_univ).

  allunfold @per_eq; exrepnd.
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

Lemma tequality_mkc_equality_in_universe_true {p} :
  forall lib (a1 b1 a2 b2 : @CTerm p) i,
    tequality lib (mkc_equality a1 b1 (mkc_uni i)) (mkc_equality a2 b2 (mkc_uni i))
    -> equality lib a1 b1 (mkc_uni i)
    -> equality lib a2 b2 (mkc_uni i).
Proof.
  introv t e.
  allapply @tequality_mkc_equality_implies; sp.
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

Lemma tequality_mkc_equality {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
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

    exists (fun x y : @CTerm p => x ===>(lib) mkc_axiom
                       # y ===>(lib) mkc_axiom
                       # eq a1 a2).
    apply CL_eq; unfold per_eq; fold @nuprl.

    exists A B a1 a2 b1 b2 eq; dands; auto.
    spcast; apply computes_to_valc_refl; apply iscvalue_mkc_equality; auto.
    spcast; apply computes_to_valc_refl; apply iscvalue_mkc_equality; auto.
    apply equality_or_cequivc_eqorceq with (a := a1) (b := b1) in n.
    apply n; sp.
    apply equality_or_cequivc_eqorceq with (a := a2) (b := b2) in n.
    apply n; sp; try (intros; split; auto).
Qed.

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

    exists (fun x y : @CTerm p => x ===>(lib) mkc_axiom
                       # y ===>(lib) mkc_axiom
                       # eq a1 a2).
    apply CL_eq; unfold per_eq; fold @nuprl.

    exists A B a1 a2 b1 b2 eq; dands; auto.
    spcast; apply computes_to_valc_refl; apply iscvalue_mkc_equality; auto.
    spcast; apply computes_to_valc_refl; apply iscvalue_mkc_equality; auto.
    apply equality_or_cequivc_eqorceq with (a := a1) (b := b1) in n.
    apply n; sp.
    apply equality_or_cequivc_eqorceq with (a := a2) (b := b2) in n.
    apply n; sp; try (intros; split; auto).
Qed.

Lemma tequality_mkc_equality_if_equal {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib A B
    -> equality lib a1 b1 A
    -> equality lib a2 b2 A
    -> tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B).
Proof.
  introv teq e1 e2.
  rw @tequality_mkc_equality; dands; auto.
  split; intro e.
  apply equality_trans with (t2 := a1); eauto with nequality.
  apply equality_trans with (t2 := b1); sp.
  apply equality_trans with (t2 := b2); eauto with nequality.
Qed.

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

Lemma tequality_mkc_member {p} :
  forall lib (a b A B : @CTerm p),
    tequality lib (mkc_member a A) (mkc_member b B)
    <=>
    (
      tequality lib A B
      # (member lib a A <=> member lib b B)
      # (equality lib a b A {+} ccequivc lib a b)
    ).
Proof.
  sp; repeat (rewrite <- fold_mkc_member).
  trw @tequality_mkc_equality; split; sp.
Qed.

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

Lemma equality_commutes {p} :
  forall lib (T a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 T)
    -> equality lib a1 a2 T
    -> equality lib a1 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; sp;
  try (complete (apply equality_trans with (t2 := a2); auto));
  try (complete (spcast; apply equality_respects_cequivc_right with (t2 := a2); sp)).
Qed.

Lemma equality_commutes2 {p} :
  forall lib (T a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 T)
    -> equality lib a1 a2 T
    -> equality lib a1 a3 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; sp;
  spcast; apply equality_respects_cequivc_right with (t2 := a1); auto;
  apply equality_refl in eq; auto.
Qed.

Lemma equality_commutes3 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a1 a3 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; sp;
  spcast; apply equality_respects_cequivc_right with (t2 := a1); auto;
  apply equality_refl in eq; auto.
Qed.

Lemma equality_commutes4 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a1 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; sp;
  try (complete (apply equality_trans with (t2 := a2); auto));
  try (complete (spcast; apply equality_respects_cequivc_right with (t2 := a2); sp)).
Qed.

Lemma equality_commutes5 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a2 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; sp;
  spcast; apply equality_respects_cequivc_right with (t2 := a2); sp;
  apply equality_sym in eq; apply equality_refl in eq; auto.
Qed.

Lemma equality_in_mkc_equality {p} :
  forall lib (t1 t2 T a b : @CTerm p),
    equality lib a b (mkc_equality t1 t2 T)
    <=> (equality lib t1 t2 T
         # a ===>(lib) mkc_axiom
         # b ===>(lib) mkc_axiom).
Proof.
  introv; split; intro i.

  applydup @member_equality_is_axiom in i; repnd; sp.
  allunfold @equality; allunfold @nuprl; exrepnd.
  inversion i3; subst; try not_univ.
  allunfold @per_eq; exrepnd.
  computes_to_value_isvalue.
  exists eqa; sp.
  discover; sp.

  repnd.
  allunfold @equality; allunfold @nuprl; exrepnd.
  exists (fun t t' : @CTerm p => t ===>(lib) mkc_axiom
              # t' ===>(lib) mkc_axiom
              # eq t1 t2); sp.
  apply CL_eq.
  unfold per_eq.
  exists T T t1 t2 t1 t2 eq; sp; spcast;
  try (apply computes_to_valc_refl);
  try (apply iscvalue_mkc_equality; auto);
  pose proof (nuprl_eq_implies_eqorceq_refl lib T T eq t1 t2); sp.
Qed.

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
    exists (fun t t' : @CTerm p => t ===>(lib) mkc_axiom
              # t' ===>(lib) mkc_axiom
              # ccequivc lib t1 t2).

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

Lemma tequality_mkc_member_base {p} :
  forall lib (a b : @CTerm p),
    tequality lib (mkc_member a mkc_base) (mkc_member b mkc_base)
    <=>
    ccequivc lib a b.
Proof.
  introv.
  rw @tequality_mkc_member; split; intro e; repnd.
  repdors; try (complete auto).
  rw @equality_in_base_iff in e2; auto.
  dands; try (complete sp).
  split; intro m; apply member_base.
Qed.

Lemma equality_on_closed_terms_is_a_type {p} :
  forall lib (A x y : @CTerm p), type lib A -> type lib (mkc_equality x y A).
Proof.
  introv ta.
  apply tequality_equality_if_cequivc; sp.
Qed.

Lemma type_mkc_equality {p} :
  forall lib (A x y : @CTerm p), type lib (mkc_equality x y A) <=> type lib A.
Proof.
  introv; split; intro k.
  rw @tequality_mkc_equality in k; sp.
  apply equality_on_closed_terms_is_a_type; sp.
Qed.

Lemma type_mkc_equality2 {p} :
  forall lib (A : @CTerm p), (forall x y, type lib (mkc_equality x y A)) <=> type lib A.
Proof.
  introv; split; intro k; introv.
  generalize (k mkc_axiom mkc_axiom); clear k; intro k.
  rw @tequality_mkc_equality in k; sp.
  apply equality_on_closed_terms_is_a_type; sp.
Qed.

Lemma inhabited_mkc_equality {p} :
  forall lib (A x y : @CTerm p),
    inhabited_type lib (mkc_equality x y A) <=> equality lib x y A.
Proof.
  introv; split; intro k.
  unfold inhabited_type in k; exrepnd.
  rw @equality_in_mkc_equality in k0; sp.
  exists (@mkc_axiom p).
  apply member_equality; sp.
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
  computes_to_value_isvalue; subst.
  exists eqa; sp.
  subst; discover; sp.
Qed.

Lemma tequality_in_uni_implies_tequality {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality lib (mkc_member T1 (mkc_uni i))
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

Lemma iff_inhabited_type_if_tequality_mem {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality lib (mkc_member T1 (mkc_uni i)) (mkc_member T2 (mkc_uni i))
    -> (inhabited_type lib T1 <=> inhabited_type lib T2).
Proof.
  introv teq.
  rw @tequality_mkc_member in teq; repnd.
  split; intro inh; repdors; allapply @equality_in_uni.
  apply inhabited_type_tequality with (a := T1); sp.
  spcast; apply inhabited_type_cequivc with (a := T1); sp.
  apply inhabited_type_tequality with (a := T2); sp.
  apply tequality_sym; sp.
  spcast; apply inhabited_type_cequivc with (a := T2); sp.
  apply cequivc_sym; sp.
Qed.

Lemma equality_mkc_equality2_sp_in_uni {p} :
  forall lib i (a1 a2 b1 b2 A B : @CTerm p),
    equality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) (mkc_uni i)
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

    allunfold @per_eq; exrepnd.
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

    exists (fun t1 t2 : @CTerm p => (t1 ===>(lib) mkc_axiom # t2 ===>(lib) mkc_axiom # eqa a1 a2)).
    apply CL_eq; fold (@nuprli p lib j0).
    unfold per_eq.
    exists A B a1 a2 b1 b2 eqa; dands; auto;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_equality))).

    allapply @nuprli_implies_nuprl.
    pose proof (eqorceq_iff_equorsq lib A B a1 b1 eqa) as h.
    autodimp h hyp.
    apply h; auto.

    allapply @nuprli_implies_nuprl.
    pose proof (eqorceq_iff_equorsq lib A B a2 b2 eqa) as h.
    autodimp h hyp.
    apply h; auto.
Qed.

Lemma equality_in_member {p} :
  forall lib (a b t T : @CTerm p),
    equality lib a b (mkc_member t T)
    <=> ((a ===>(lib) mkc_axiom)
         # (b ===>(lib) mkc_axiom)
         # member lib t T).
Proof.
  introv.
  rw <- @fold_mkc_member.
  rw @equality_in_mkc_equality.
  split; sp.
Qed.

Lemma tequality_mkc_member_implies_sp {o} :
  forall lib (a b A B : @CTerm o),
    tequality lib (mkc_member a A) (mkc_member b B)
    -> member lib a A
    -> equality lib a b A.
Proof.
  introv teq mem.
  allrw @tequality_mkc_member_sp; repnd.
  repndors; tcsp; spcast.
  eapply equality_respects_cequivc_right;[exact teq|]; auto.
Qed.

Lemma tequality_mkc_equality_sp_eq {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    equality lib a1 a2 A
    -> (tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
        <=> (tequality lib A B # equality lib a1 b1 A # equality lib a2 b2 A)).
Proof.
  introv eqa.
  split; intro h; repnd; dands; auto.
  - rw @tequality_mkc_equality_sp in h; sp.
  - rw @tequality_mkc_equality_sp in h; repnd.
    repndors; spcast; eauto 3 with nequality.
  - rw @tequality_mkc_equality_sp in h; repnd.
    repndors; spcast; eauto 3 with nequality.
    + eapply equality_respects_cequivc_right;[exact h|].
      apply equality_sym in eqa; apply equality_refl in eqa; auto.
    + eapply equality_respects_cequivc_right;[exact h|].
      apply equality_sym in eqa; apply equality_refl in eqa; auto.
  - apply tequality_mkc_equality_sp; dands; auto.
Qed.

(* end hide *)
