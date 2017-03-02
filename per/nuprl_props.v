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


Require Export nuprl_type_sys.
Require Export univ_tacs.
Require Import rel_nterm.

(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing ~<~  $\preceq$ *)
(** printing ~=~  $\sim$ *)
(* printing ===>  $\longmapsto$ *)
(** printing ===>  $\Downarrow$ *)
(** printing [[  $[$ *)
(** printing ]]  $]$ *)
(** printing \\  $\backslash$ *)
(** printing mkc_axiom   $\mathtt{Ax}$ *)
(** printing mkc_base    $\mathtt{Base}$ *)
(** printing mkc_int     $\intg$ *)
(** printing mkc_integer $\mathtt{int}$ *)

(*
Lemma nuprli_refl {p} :
  forall lib i t1 t2 eq,
    @nuprli p lib i t1 t2 eq -> nuprli lib i t1 t1 eq.
Proof.
  intros.
  generalize (@nuprli_type_system p lib i); intro nts.
  dest_ts nts.
  apply ts_tyt with (T2 := t2); sp.
Qed.
*)

(*
(* COMMENTED OUT BECAUSE MIGHT CAUSE A UNIVERSE INCONSISTENCY *)
Lemma tequalityi_eq :
  forall i T1 T2,
    tequalityi i T1 T2 <=> {eq : per , nuprli i T1 T2 eq}.
Proof.
  unfold tequalityi, equality; split; introv e; exrepnd.

  - inversion e1; try not_univ.
    duniv j h.
    allrw univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (nuprli j0).
    exists eqa; sp.

  - exists (fun A A' => {eq : per , close (univi i) A A' eq}).
    allfold (nuprli i); dands.
    apply CL_init; unfold univ.
    exists (S i); simpl; left; sp; try (spcast; apply computes_to_valc_refl; sp).
    exists eq; sp.
Qed.

Lemma univi_exists_iff2 :
  forall i T T' eq,
    univi i T T' eq
    <=> {j : nat
          , j < i
          # ccomputes_to_valc T  (mkc_uni j)
          # ccomputes_to_valc T' (mkc_uni j)
          # eq_term_equals eq (tequalityi j)}.
Proof.
  introv.
  rw univi_exists_iff; split; sp.

  exists j; sp.
  unfold eq_term_equals; sp.
  allrw.
  rw tequalityi_eq; sp.

  exists j; sp.
  allrw.
  rw tequalityi_eq; sp.
Qed.
*)

Lemma equality_eq_refl {p} :
  forall lib A a b eq,
    @nuprl p lib A eq
    -> eq a b
    -> eq a a.
Proof.
  sp; nts.
  eapply type_system_term_mem; eauto.
Qed.

Lemma equality_eq_sym {p} :
  forall lib A a b eq,
    @nuprl p lib A eq
    -> eq a b
    -> eq b a.
Proof.
  sp; nts.
  eapply nts_tes; eauto.
Qed.

Lemma equality_eq_trans {p} :
  forall lib A a b c eq,
    @nuprl p lib A eq
    -> eq a b
    -> eq b c
    -> eq a c.
Proof.
  sp; nts.
  eapply nts_tet; eauto.
Qed.

Lemma equality_sym {p} :
  forall lib t1 t2 T,
    @equality p lib t1 t2 T -> equality lib t2 t1 T.
Proof.
  unfold equality; sp.
  exists eq; sp.
  eapply equality_eq_sym; eauto.
Qed.
Hint Resolve equality_sym : nequality.

Lemma equality_trans {p} :
  forall lib t1 t2 t3 T,
    @equality p lib t1 t2 T -> equality lib t2 t3 T -> equality lib t1 t3 T.
Proof.
  unfold equality; introv e1 e2; exrepnd.
  apply nuprl_uniquely_valued with (eq1 := eq0) in e2; auto.
  exists eq0; auto.
  rw <- e2 in e0; sp.
  eapply equality_eq_trans; eauto.
Qed.
Hint Resolve equality_trans : nequality.

Lemma tequality_sym {p} :
  forall lib t1 t2,
    @tequality p lib t1 t2 -> tequality lib t2 t1.
Proof.
  unfold tequality; sp.
  exists eq.
  apply Nuprl_sym; sp.
Qed.
Hint Resolve tequality_sym : nequality.

Lemma tequality_refl {p} :
  forall lib t1 t2,
    @tequality p lib t1 t2 -> tequality lib t1 t1.
Proof.
  unfold tequality; introv t; exrepnd.
  exists eq.
  apply Nuprl_refl in t0; sp.
Qed.
Hint Resolve tequality_refl : nequality.

Lemma tequality_trans {p} :
  forall lib t1 t2 t3,
    @tequality p lib t1 t2 -> tequality lib t2 t3 -> tequality lib t1 t3.
Proof.
  unfold tequality; sp.
  exists eq0.
  eapply Nuprl_trans; eauto.
Qed.
Hint Resolve tequality_trans : nequality.

Lemma member_eq {p} :
  forall lib t T,
    @equality p lib t t T = member lib t T.
Proof.
  unfold member; auto.
Qed.

Lemma fold_type {o} :
  forall lib (T : @CTerm o),
    tequality lib T T <-> type lib T.
Proof.
  unfold tequality, type, Nuprl, extts; introv; split; intro h; exrepnd; eexists; eauto.
Qed.

Lemma fold_equorsq {p} :
  forall lib t1 t2 T,
    (@equality p lib t1 t2 T {+} ccequivc lib t1 t2) = equorsq lib t1 t2 T.
Proof. sp. Qed.

Lemma fold_equorsq2 {p} :
  forall lib t1 t2 t3 t4 T,
    (@equorsq p lib t1 t2 T # equorsq lib t3 t4 T) = equorsq2 lib t1 t2 t3 t4 T.
Proof. sp. Qed.

Lemma equality_refl {p} :
  forall lib t1 t2 T,
    @equality p lib t1 t2 T -> member lib t1 T.
Proof.
  unfold member, equality; sp.
  exists eq; sp.
  eapply equality_eq_refl; eauto.
Qed.
Hint Resolve equality_refl : nequality.

Lemma tequality_iff_nuprl {p} :
  forall lib a b,
    {eq : per(p) , Nuprl lib a b eq} <=> tequality lib a b.
Proof.
  sp.
Qed.

Lemma tequality_if_nuprl {p} :
  forall lib a b eq,
    @Nuprl p lib a b eq -> tequality lib a b.
Proof.
  sp.
  apply tequality_iff_nuprl; exists eq; sp.
Qed.

Lemma equality_eq {p} :
  forall lib A a b eq,
    @nuprl p lib A eq
    -> (eq a b <=> equality lib a b A).
Proof.
  sp; split; intro k.
  unfold equality; exists eq; sp.
  unfold equality in k; sp.
  assert (eq_term_equals eq eq0) as eqt.
  eapply nuprl_uniquely_valued with (t := A); eauto.
  unfold eq_term_equals in eqt.
  apply eqt; sp.
Qed.

Lemma equality_eq1 {p} :
  forall lib A B a b eq,
    @Nuprl p lib A B eq
    -> (eq a b <=> equality lib a b A).
Proof.
  introv n; split; intro k.

  { unfold equality; exists eq; sp.
    unfold Nuprl, extts in n; tcsp. }

  { unfold equality in k; exrepnd.
    unfold Nuprl, extts in n; repnd.
    assert (eq_term_equals eq eq0) as eqt.
    { eapply nuprl_uniquely_valued with (t := A); eauto. }
    apply eqt; auto. }
Qed.

Lemma eqorceq_commutes_equality {p} :
  forall lib a b c d eq A B,
    @Nuprl p lib A B eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq c d
    -> (equality lib a c A <=> equality lib b d B).
Proof.
  introv n eos1 eos2.
  unfold Nuprl, extts in n; repnd.
  rw <- (equality_eq lib A a c eq n0).
  rw <- (equality_eq lib B b d eq n).
  nts.
  split; intro h.

  { apply (eqorceq_commutes lib) with (a := a) (c := c); auto.
    - eapply nts_tev; eauto.
    - eapply nts_tes; eauto.
    - eapply nts_tet; eauto. }

  { apply (eqorceq_commutes lib) with (a := b) (c := d); auto.
    - eapply nts_tev; eauto.
    - eapply nts_tes; eauto.
    - eapply nts_tet; eauto.
    - eapply eqorceq_sym; eauto.
    - eapply eqorceq_sym; eauto. }
Qed.

Lemma eq_equality0 {p} :
  forall lib a b A (eq : per(p)),
    eq a b
    -> nuprl lib A eq
    -> equality lib a b A.
Proof.
  introv e n.
  exists eq; sp.
Defined.

Lemma eq_equality1 {p} :
  forall lib a b A (eq : per(p)),
    eq a b
    -> Nuprl lib A A eq
    -> equality lib a b A.
Proof.
  introv e n.
  unfold Nuprl, extts in n; repnd.
  exists eq; sp.
Defined.

Lemma eq_equality2 {p} :
  forall lib a b A B (eq : per(p)),
    eq a b
    -> Nuprl lib A B eq
    -> equality lib a b A.
Proof.
  introv e n.
  unfold Nuprl, extts in n; repnd.
  exists eq; sp.
Defined.

Lemma Nuprli_implies_Nuprl {o} :
  forall lib (A B : @CTerm o) i eq,
    Nuprli lib i A B eq
    -> Nuprl lib A B eq.
Proof.
  introv n; destruct n as [n1 n2].
  split; auto; eapply nuprli_implies_nuprl; eauto.
Qed.
Hint Resolve Nuprli_implies_Nuprl : slow.

Lemma Nuprl_implies_nuprl_left {o} :
  forall lib (A B : @CTerm o) eq,
    Nuprl lib A B eq
    -> nuprl lib A eq.
Proof.
  introv n; destruct n as [n1 n2]; tcsp.
Qed.
Hint Resolve Nuprl_implies_nuprl_left : slow.

Lemma Nuprl_implies_nuprl_right {o} :
  forall lib (A B : @CTerm o) eq,
    Nuprl lib A B eq
    -> nuprl lib B eq.
Proof.
  introv n; destruct n as [n1 n2]; tcsp.
Qed.
Hint Resolve Nuprl_implies_nuprl_right : slow.

Lemma eq_equality3 {p} :
  forall lib a b A B (eq : per(p)) i,
    eq a b
    -> Nuprli lib i A B eq
    -> equality lib a b A.
Proof.
  introv e n.
  exists eq; dands; auto.
  eauto 3 with slow.
Qed.

Hint Resolve nuprli_implies_nuprl : slow.

Lemma eq_equality4 {p} :
  forall lib a b A (eq : per(p)) i,
    eq a b
    -> nuprli lib i A eq
    -> equality lib a b A.
Proof.
  introv e n.
  exists eq; dands; auto.
  eauto 3 with slow.
Qed.

Lemma equality_respects_cequivc {p} :
  forall lib t1 t2 T,
    @cequivc p lib t1 t2
    -> member lib t1 T
    -> equality lib t1 t2 T.
Proof.
  unfold member, equality; sp.
  exists eq; sp.
  nts.
  apply nts_tev with (T := T); sp; spcast; sp.
Qed.
Hint Resolve equality_respects_cequivc : nequality.

Lemma equality_respects_alphaeqc {p} :
  forall lib t1 t2 T,
    @alphaeqc p t1 t2
    -> member lib t1 T
    -> equality lib t1 t2 T.
Proof.
  unfold member, equality; introv a m; exrepnd.
  exists eq; sp.
  nts.
  apply nts_tev with (T := T); sp; spcast.
  apply alphaeqc_implies_cequivc; sp.
Qed.
Hint Resolve equality_respects_alphaeqc : nequality.

Lemma equality_respects_cequivc_left {p} :
  forall lib t1 t2 t T,
    @cequivc p lib t1 t
    -> equality lib t1 t2 T
    -> equality lib t t2 T.
Proof.
  sp.
  apply @equality_trans with (t2 := t1); sp.
  apply equality_sym.
  apply equality_respects_cequivc; sp.
  allapply @equality_refl; sp.
Qed.
Hint Resolve equality_respects_cequivc_left : nequality.

Lemma equality_respects_cequivc_right {p} :
  forall lib t1 t2 t T,
    @cequivc p lib t2 t
    -> equality lib t1 t2 T
    -> equality lib t1 t T.
Proof.
  introv c e.
  apply @equality_trans with (t2 := t2); sp.
  apply equality_respects_cequivc; sp.
  apply equality_sym in e.
  allapply @equality_refl; sp.
Qed.
Hint Resolve equality_respects_cequivc_right : nequality.

Lemma equality_respects_alphaeqc_left {p} :
  forall lib t1 t2 t T,
    @alphaeqc p t1 t
    -> equality lib t1 t2 T
    -> equality lib t t2 T.
Proof.
  sp.
  apply @equality_trans with (t2 := t1); sp.
  apply equality_sym.
  apply equality_respects_cequivc; sp.
  apply alphaeqc_implies_cequivc; sp.
  allapply @equality_refl; sp.
Qed.
Hint Resolve equality_respects_alphaeqc_left : nequality.

Lemma equality_respects_alphaeqc_right {p} :
  forall lib t1 t2 t T,
    @alphaeqc p t2 t
    -> equality lib t1 t2 T
    -> equality lib t1 t T.
Proof.
  introv a e.
  apply @equality_trans with (t2 := t2); sp.
  apply equality_respects_cequivc; sp.
  apply alphaeqc_implies_cequivc; sp.
  apply equality_sym in e.
  allapply @equality_refl; sp.
Qed.
Hint Resolve equality_respects_alphaeqc_right : nequality.

Lemma tequality_respects_cequivc_left {p} :
  forall lib T1 T2 T3,
    @cequivc p lib T1 T3
    -> tequality lib T1 T2
    -> tequality lib T3 T2.
Proof.
  unfold tequality; sp.
  exists eq.
  eauto 2 with slow.
Qed.
Hint Resolve tequality_respects_cequivc_left : nequality.

Lemma tequality_respects_cequivc_right {p} :
  forall lib T1 T2 T3,
    @cequivc p lib T2 T3
    -> tequality lib T1 T2
    -> tequality lib T1 T3.
Proof.
  unfold tequality; sp.
  exists eq.
  eauto 2 with slow.
Qed.
Hint Resolve tequality_respects_cequivc_right : nequality.

Hint Resolve alphaeqc_implies_cequivc : slow.

Lemma tequality_respects_alphaeqc_left {p} :
  forall lib T1 T2 T3,
    @alphaeqc p T1 T3
    -> tequality lib T1 T2
    -> tequality lib T3 T2.
Proof.
  unfold tequality; sp.
  exists eq.
  eauto 3 with slow.
Qed.
Hint Resolve tequality_respects_alphaeqc_left : nequality.

Lemma tequality_respects_alphaeqc_right {p} :
  forall lib T1 T2 T3,
    @alphaeqc p T2 T3
    -> tequality lib T1 T2
    -> tequality lib T1 T3.
Proof.
  unfold tequality; sp.
  exists eq.
  eauto 3 with slow.
Qed.
Hint Resolve tequality_respects_alphaeqc_right : nequality.

Lemma type_respects_cequivc_left {p} :
  forall lib T T',
    @cequivc p lib T T'
    -> type lib T
    -> tequality lib T' T.
Proof.
  unfold type; sp.
  exists eq; split; eauto 2 with slow.
Qed.
Hint Resolve type_respects_cequivc_left : nequality.

Lemma type_respects_cequivc_right {p} :
  forall lib T T',
    @cequivc p lib T T'
    -> type lib T
    -> tequality lib T T'.
Proof.
  unfold type; sp.
  exists eq; split; eauto 2 with slow.
Qed.
Hint Resolve type_respects_cequivc_right : nequality.

Lemma type_respects_alphaeqc_left {p} :
  forall lib T T',
    @alphaeqc p T T'
    -> type lib T
    -> tequality lib T' T.
Proof.
  unfold type; sp.
  exists eq; split; eauto 3 with slow.
Qed.

Lemma type_respects_alphaeqc_right {p} :
  forall lib T T',
    @alphaeqc p T T'
    -> type lib T
    -> tequality lib T T'.
Proof.
  unfold type; sp.
  exists eq; split; eauto 3 with slow.
Qed.

Lemma cequivc_preserving_equality {p} :
  forall lib a b A B,
    @equality p lib a b A
    -> cequivc lib A B
    -> equality lib a b B.
Proof.
  unfold equality; introv e c; exrepnd.
  exists eq; dands; auto.
  eauto 3 with slow.
Qed.

Lemma alphaeqc_preserving_equality {p} :
  forall lib a b A B,
    @equality p lib a b A
    -> alphaeqc A B
    -> equality lib a b B.
Proof.
  unfold equality; introv e al; exrepnd.
  exists eq; dands; auto.
  eauto 3 with slow.
Qed.

Lemma tequality_preserving_equality {p} :
  forall lib a b A B,
    @equality p lib a b A
    -> tequality lib A B
    -> equality lib a b B.
Proof.
  unfold tequality, equality; introv e t; exrepnd.
  exists eq; dands; eauto 3 with slow.
  eapply nuprl_uniquely_valued;eauto.
  eauto 2 with slow.
Qed.
Hint Resolve tequality_preserving_equality : nequality.

Lemma tequalityi_refl {p} :
  forall lib l T1 T2, @tequalityi p lib l T1 T2 -> tequalityi lib l T1 T1.
Proof.
  unfold tequalityi; sp.
  allapply @equality_refl; sp.
Qed.

Lemma eqtypes_refl {p} :
  forall lib l T1 T2, @eqtypes p lib l T1 T2 -> eqtypes lib l T1 T1.
Proof.
  destruct l; simpl; sp.
  allapply @tequality_refl; sp.
  allapply @tequalityi_refl; sp.
Qed.

Lemma tequalityi_preserving_equality {p} :
  forall lib i a b A B,
    @equality p lib a b A
    -> tequalityi lib i A B
    -> equality lib a b B.
Proof.
  unfold tequalityi, equality; introv e teq; exrepnd.
  inversion teq1; try not_univ.
  duniv j h.
  allrw @univi_exists_iff; exrepd.
  computes_to_value_isvalue; GC.
  apply e in teq0.
  unfold univi_eq, extts in teq0; exrepnd.
  allapply @nuprli_implies_nuprl.
  eapply nuprl_uniquely_valued in e1;[|eauto].
  exists eqa; dands; auto; apply e1; auto.
Qed.

Lemma eqtypes_preserving_equality {p} :
  forall lib l a b A B,
    @equality p lib a b A
    -> eqtypes lib l A B
    -> equality lib a b B.
Proof.
  destruct l; introv eq eqt.
  apply @tequality_preserving_equality with (A := A); sp.
  apply @tequalityi_preserving_equality with (A := A) (i := n); sp.
Qed.

Lemma tequalityi_sym {p} :
  forall lib i T1 T2, @tequalityi p lib i T1 T2 -> tequalityi lib i T2 T1.
Proof.
  unfold tequalityi; introv teq.
  apply equality_sym; sp.
Qed.

Lemma eqtypes_sym {p} :
  forall lib l T1 T2, @eqtypes p lib l T1 T2 -> eqtypes lib l T2 T1.
Proof.
  destruct l; introv eqt.
  apply tequality_sym; sp.
  apply tequalityi_sym; sp.
Qed.

Lemma tequalityi_trans {p} :
  forall lib i t1 t2 t3,
    @tequalityi p lib i t1 t2
    -> tequalityi lib i t2 t3
    -> tequalityi lib i t1 t3.
Proof.
  unfold tequalityi; introv teq1 teq2.
  apply @equality_trans with (t2 := t2); sp.
Qed.

Lemma eqtypes_trans {p} :
  forall lib l t1 t2 t3,
    @eqtypes p lib l t1 t2
    -> eqtypes lib l t2 t3
    -> eqtypes lib l t1 t3.
Proof.
  destruct l; introv teq1 teq2.
  apply @tequality_trans with (t2 := t2); sp.
  apply @tequalityi_trans with (t2 := t2); sp.
Qed.

Lemma equality3_implies_cequorsq2 {p} :
  forall lib a b c d T,
    @equality p lib a c T
    -> equality lib b d T
    -> equality lib a b T
    -> equorsq2 lib a b c d T.
Proof.
  sp.
  unfold equorsq2, equorsq; sp.
  left.
  apply equality_trans with (t2 := b); auto.
  apply equality_trans with (t2 := a); auto.
  apply equality_sym; auto.
Qed.

Lemma inhabited_implies_tequality {p} :
  forall lib t1 t2 T,
    @equality p lib t1 t2 T -> type lib T.
Proof.
  unfold equality, type, tequality; introv eq; exrepnd.
  exists eq0; sp.
Qed.

Hint Resolve tequality_preserving_equality cequivc_preserving_equality : nequality.

Lemma cequivc_equality {p} : forall lib, respects3 (cequivc lib) (@equality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.
Hint Resolve cequivc_equality : respects.

Lemma sym_cequivc_eauto {p} : forall lib, symm_rel (@cequivc p lib).
Proof.
  introv Hab.
  apply cequivc_sym; auto.
Qed.
Hint Resolve sym_cequivc_eauto : nequality.
Hint Resolve sym_cequivc_eauto : respects.

Lemma cequorsq2_prop {p} :
  forall lib A a1 a2 b1 b2,
    @equorsq2 p lib a1 b1 a2 b2 A
    -> equality lib a1 a2 A
    -> equality lib a1 b2 A.
Proof.
  introv ceq e1.
  unfold equorsq2, equorsq in ceq; repnd; repdors; spcast.

  apply equality_trans with (t2 := a2); sp.

  apply equality_trans with (t2 := a2); sp.

  apply equality_trans with (t2 := a2); sp.
  apply cequivc_sym in ceq.
  rwg ceq.
  apply equality_sym in e1; apply equality_refl in e1; auto.

  apply equality_trans with (t2 := a2); sp.
  apply cequivc_sym in ceq.
  rwg ceq.
  apply equality_sym in e1; apply equality_refl in e1; auto.
Qed.

Lemma cequorsq_equality_trans1 {p} :
  forall lib t1 t2 t3 T,
    @equorsq p lib t1 t2 T
    -> equality lib t2 t3 T
    -> equality lib t1 t3 T.
Proof.
  introv c e.
  unfold equorsq in c; sp.
  apply @equality_trans with (t2 := t2); sp.
  spcast; apply @equality_respects_cequivc_left with (t1 := t2); sp.
  apply cequivc_sym; sp.
Qed.

Lemma cequorsq_equality_trans2 {p} :
  forall lib t1 t2 t3 T,
    @equality p lib t1 t2 T
    -> equorsq lib t2 t3 T
    -> equality lib t1 t3 T.
Proof.
  introv e c.
  unfold equorsq in c; sp.
  apply @equality_trans with (t2 := t2); sp.
  spcast; apply @equality_respects_cequivc_right with (t2 := t2); sp.
Qed.

Lemma cequorsq_sym {p} :
  forall lib a b T, @equorsq p lib a b T -> equorsq lib b a T.
Proof.
  unfold equorsq; introv ceq; sp.
  left; apply equality_sym; sp.
  right; spcast; sp; apply cequivc_sym; sp.
Qed.

Hint Resolve alphaeqc_preserving_equality : nequality.


Lemma respects_alphaeqc_equality {p} : forall lib, respects3 alphaeqc (@equality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.

Lemma sym_alphaeqc_eauto {p} : symm_rel (@alphaeqc p).
Proof.
  introv Hab.
  apply alphaeqc_sym; auto.
Qed.

Hint Resolve respects_alphaeqc_equality sym_alphaeqc_eauto : respects.

Lemma respects_alphaeqc_tequality {p} : forall lib, respects2 alphaeqc (@tequality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.

Hint Resolve respects_alphaeqc_tequality : respects.

Lemma respects_cequivc_tequality {p} :
  forall lib, respects2 (cequivc lib) (@tequality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.

Hint Resolve respects_cequivc_tequality : respects.

Lemma respects_cequivc_equality {p} : forall lib, respects3 (cequivc lib) (@equality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.

Hint Resolve respects_cequivc_equality : respects.

Lemma nuprli_sym {p} :
  forall lib i t1 t2 eq,
    @Nuprli p lib i t1 t2 eq -> Nuprli lib i t2 t1 eq.
Proof.
  introv n.
  pose proof (@Nuprli_etype_system p lib i) as nts.
  dest_ets nts.
  apply ts_tys; sp.
Qed.

Lemma nuprl_ext {o} :
  forall lib (t : @CTerm o) eq1 eq2,
    nuprl lib t eq1
    -> (eq1 <=2=> eq2)
    -> nuprl lib t eq2.
Proof.
  introv n1 eqs; nts.
  apply nts_ext with (eq := eq1); sp.
Qed.

Lemma Nuprl_ext {o} :
  forall lib (t1 t2 : @CTerm o) eq1 eq2,
    Nuprl lib t1 t2 eq1
    -> (eq1 <=2=> eq2)
    -> Nuprl lib t1 t2 eq2.
Proof.
  introv n1 eqs; ents.
  apply nts_ext with (eq := eq1); sp.
Qed.

Lemma nuprli_ext {o} :
  forall lib i (t : @CTerm o) eq1 eq2,
    nuprli lib i t eq1
    -> eq1 <=2=> eq2
    -> nuprli lib i t eq2.
Proof.
  introv n1 eqs.
  pose proof (nuprli_type_system lib i) as nts.
  dest_ts nts.
  eapply ts_ext; eauto.
Qed.

Lemma Nuprli_ext {o} :
  forall lib i (t1 t2 : @CTerm o) eq1 eq2,
    Nuprli lib i t1 t2 eq1
    -> eq1 <=2=> eq2
    -> Nuprli lib i t1 t2 eq2.
Proof.
  introv n1 eqs.
  pose proof (Nuprli_etype_system lib i) as nts.
  dest_ets nts.
  apply ts_ext with (eq := eq1); sp.
Qed.

Lemma eqorceq_iff_equorsq {o} :
  forall lib (A B a b : @CTerm o) eq,
    Nuprl lib A B eq
    -> (eqorceq lib eq a b <=> equorsq lib a b A).
Proof.
  introv n.
  unfold eqorceq, equorsq.
  split; intro k; repndors; tcsp.
  - left; exists eq; dands; eauto 2 with slow.
  - left; eapply equality_eq; eauto; eauto 2 with slow.
Qed.

Lemma equorsq_tequality {o} :
  forall lib (A B a b : @CTerm o),
    equorsq lib a b A
    -> tequality lib A B
    -> equorsq lib a b B.
Proof.
  introv e t.
  allunfold @equorsq.
  dorn e; auto.
  left.
  eapply tequality_preserving_equality; eauto.
Qed.


Lemma respects_cequivc_equorsq {p} : forall lib, respects3 (cequivc lib) (@equorsq p lib).
Proof.
  unfold equorsq; introv; unfolds_base; dands; introv Hr Heq; allsimpl; dorn Heq;
  try (complete (left; eauto 3 with nequality));
  right; spcast; eauto 3 with nequality.
  apply (cequivc_trans lib a' a b); auto; apply cequivc_sym; auto.
  apply (cequivc_trans lib a b b'); auto; apply cequivc_sym; auto.
Qed.
Hint Resolve respects_cequivc_equorsq : respects.

Lemma respects_alphaeqc_equorsq {p} : forall lib, respects3 alphaeqc (@equorsq p lib).
Proof.
  unfold equorsq; introv; unfolds_base; dands; introv Hr Heq; allsimpl; dorn Heq;
  try (complete (left; eauto 3 with nequality));
  right; spcast; eauto 3 with nequality.
  apply (cequivc_trans lib a' a b); auto; apply cequivc_sym; apply alphaeqc_implies_cequivc; auto.
  apply (cequivc_trans lib a b b'); auto; apply alphaeqc_implies_cequivc; auto.
Qed.
Hint Resolve respects_alphaeqc_equorsq : respects.


Lemma equorsq_sym {o} :
  forall lib (A a b : @CTerm o),
    equorsq lib a b A -> equorsq lib b a A.
Proof.
  introv e.
  allunfold @equorsq; sp.
  left; apply equality_sym; auto.
  right; spcast; sp; apply cequivc_sym; sp.
Qed.

Lemma tequality_implies_type_left {o} :
  forall lib (a b : @CTerm o),
    tequality lib a b -> type lib a.
Proof.
  introv teq.
  unfold tequality in teq; exrepnd; exists eq; eauto 3 with slow.
Qed.
Hint Resolve tequality_implies_type_left : slow.

Lemma tequality_implies_type_right {o} :
  forall lib (a b : @CTerm o),
    tequality lib a b -> type lib b.
Proof.
  introv teq.
  unfold tequality in teq; exrepnd; exists eq; eauto 3 with slow.
Qed.
Hint Resolve tequality_implies_type_right : slow.

Lemma nuprl_implies_Nuprl {o} :
  forall lib (t1 t2 : @CTerm o) eq,
    nuprl lib t1 eq
    -> nuprl lib t2 eq
    -> Nuprl lib t1 t2 eq.
Proof.
  introv n1 n2; split; auto.
Qed.
Hint Resolve nuprl_implies_Nuprl : slow.

Lemma Nuprl_uniquely_valued_left {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq1 eq2,
    Nuprl lib t1 t2 eq1
    -> Nuprl lib t1 t3 eq2
    -> (eq1) <=2=> (eq2).
Proof.
  introv n1 n2.
  ents.
  apply Nuprl_refl in n1.
  apply Nuprl_refl in n2.
  eapply nts_uv;eauto.
Qed.

Lemma Nuprl_uniquely_valued_right {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq1 eq2,
    Nuprl lib t2 t1 eq1
    -> Nuprl lib t3 t1 eq2
    -> (eq1) <=2=> (eq2).
Proof.
  introv n1 n2.
  ents.
  apply Nuprl_sym in n1.
  apply Nuprl_sym in n2.
  apply Nuprl_refl in n1.
  apply Nuprl_refl in n2.
  eapply nts_uv;eauto.
Qed.

Lemma eqorceq_commutes_nuprl {p} :
  forall lib (a b c d : @CTerm p) eq A,
    nuprl lib A eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq c d
    -> eq a c
    -> eq b d.
Proof.
  introv n e1 e2 e3.
  apply (eqorceq_commutes lib) with (a := a) (c := c); sp.

  - nts.
    unfold term_value_respecting in nts_tev.
    eapply nts_tev; eauto.

  - nts.
    unfold term_symmetric in nts_tes.
    eapply nts_tes; eauto.

  - nts.
    unfold term_transitive in nts_tet.
    eapply nts_tet; eauto.
Qed.

Lemma eqorceq_sym_trans {p} :
  forall lib eq (a b A : @CTerm p),
    nuprl lib A eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq b a.
Proof.
  introv n e.
  apply eqorceq_sym; sp.
  nts.
  unfold term_symmetric in nts_tes.
  eapply nts_tes; eauto.
Qed.

Lemma Nuprl_refl2 {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    Nuprl lib t1 t2 eq -> Nuprl lib t2 t2 eq.
Proof.
  introv n.
  apply Nuprl_sym in n.
  apply Nuprl_refl in n; sp.
Qed.

Lemma nuprl_uniquely_eq_ext {p} :
  forall lib (t : @CTerm p) eq1 eq2,
    nuprl lib t eq1
    -> eq1 <=2=> eq2
    -> nuprl lib t eq2.
Proof.
  introv n e.
  eapply nuprl_ext; eauto.
Qed.

Lemma Nuprl_uniquely_eq_ext {p} :
  forall lib (t1 t2 : @CTerm p) eq1 eq2,
    Nuprl lib t1 t2 eq1
    -> eq1 <=2=> eq2
    -> Nuprl lib t1 t2 eq2.
Proof.
  introv n e.
  eapply Nuprl_ext; eauto.
Qed.

Lemma equality_or_cequivc_eqorceq {p} :
  forall lib (A a b : @CTerm p) eq,
    nuprl lib A eq
    -> (eqorceq lib eq a b <=> (equality lib a b A {+} ccequivc lib a b)).
Proof.
  unfold eqorceq; introv n; split; intro e; repdors; try (complete sp);
  left;
  apply @equality_eq with (a := a) (b := b) in n;
  allrw <-; sp;
  allrw; sp.
Qed.

Lemma eqorceq_implies_equality_or_cequivc {p} :
  forall lib (A a b : @CTerm p) eq,
    nuprl lib A eq
    -> eqorceq lib eq a b
    -> (equality lib a b A {+} ccequivc lib a b).
Proof.
  introv n e.
  generalize (equality_or_cequivc_eqorceq lib A a b eq); sp.
  allrw <-; sp.
Qed.

Lemma equality3_implies_equorsq2 {p} :
  forall lib (a b c d T : @CTerm p),
    equality lib a c T
    -> equality lib b d T
    -> equality lib a b T
    -> equorsq2 lib a b c d T.
Proof.
  sp.
  unfold equorsq2, equorsq; sp.
  left.
  apply equality_trans with (t2 := b); auto.
  apply equality_trans with (t2 := a); auto.
  apply equality_sym; auto.
Qed.


Definition inhabited_type {p} lib (T : @CTerm p) := {t : CTerm , member lib t T}.

Definition sym_type {p} lib (R : @CTerm p) :=
  forall x y,
    inhabited_type lib (mkc_apply2 R x y)
    -> inhabited_type lib (mkc_apply2 R y x).

Definition trans_type {p} lib (R : @CTerm p) :=
  forall x y z,
    inhabited_type lib (mkc_apply2 R x y)
    -> inhabited_type lib (mkc_apply2 R y z)
    -> inhabited_type lib (mkc_apply2 R x z).

Definition is_per_type {p} lib (R : @CTerm p) :=
  sym_type lib R # trans_type lib R.

Lemma is_per_type_iff {p} :
  forall lib R1 R2,
    (forall x y : @CTerm p,
       inhabited_type lib (mkc_apply2 R1 x y)
       <=>
       inhabited_type lib (mkc_apply2 R2 x y))
    -> is_per_type lib R1
    -> is_per_type lib R2.
Proof.
  unfold is_per_type, sym_type, trans_type; introv iff per; dands; introv.

  intro inh.
  rw <- iff; rw <- iff in inh; sp.

  intros inh1 inh2.
  rw <- iff; rw <- iff in inh1; rw <- iff in inh2.
  apply per with (y := y); sp.
Qed.

Lemma inhabited_type_if_equality {p} :
  forall lib (a b R : @CTerm p), equality lib a b R -> inhabited_type lib R.
Proof.
  introv eq.
  unfold inhabited_type; exists a.
  apply equality_refl in eq; sp.
Qed.

Lemma inhabited_if_inhabited_type {p} :
  forall lib (T : @CTerm p) eq,
    inhabited_type lib T
    -> nuprl lib T eq
    -> inhabited eq.
Proof.
  introv inh neq.
  unfold inhabited_type in inh; exrepnd.
  unfold member, equality in inh0; exrepnd.
  generalize (nuprl_uniquely_valued lib T eq0 eq); intro i.
  repeat (dest_imp i hyp); try (complete (apply nuprl_refl with (t2 := U); sp)).
  rw i in inh1.
  clear inh0 i eq0.
  unfold nuprl in neq.
  unfold inhabited; exists t; sp.
Qed.

Lemma inhabited_type_if_inhabited {p} :
  forall lib (T : @CTerm p) eq,
    nuprl lib T eq
    -> inhabited eq
    -> inhabited_type lib T.
Proof.
  introv neq inh.
  unfold inhabited_type.
  unfold inhabited in inh; exrepnd.
  exists t.
  unfold member, equality.
  exists eq; sp.
Qed.

Lemma inhabited_type_iff_inhabited {p} :
  forall lib (T : @CTerm p) eq,
    nuprl lib T eq
    -> (inhabited eq <=> inhabited_type lib T).
Proof.
  introv neq; split; intro i.
  eapply inhabited_type_if_inhabited; eauto.
  eapply inhabited_if_inhabited_type; eauto.
Qed.

Lemma inhabited_if_inhabited_type_i {p} :
  forall lib (T : @CTerm p) eq i,
    inhabited_type lib T
    -> nuprli lib i T eq
    -> inhabited eq.
Proof.
  introv inh neq.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_if_inhabited_type in neq; auto.
Qed.

Lemma inhabited_type_if_inhabited_i {p} :
  forall lib (T : @CTerm p) eq i,
    nuprli lib i T eq
    -> inhabited eq
    -> inhabited_type lib T.
Proof.
  introv neq inh.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_type_if_inhabited in neq; auto.
Qed.

Lemma inhabited_type_iff_inhabited_i {p} :
  forall lib (T : @CTerm p) eq i,
    nuprli lib i T eq
    -> (inhabited eq <=> inhabited_type lib T).
Proof.
  introv neq.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_type_iff_inhabited in neq; auto.
Qed.

Lemma is_per_type_iff_is_per {p} :
  forall lib R eq,
    (forall x y : @CTerm p, nuprl lib (mkc_apply2 R x y) (eq x y))
    -> (is_per eq <=> is_per_type lib R).
Proof.
  introv n.
  split; intro isper.

  - destruct isper as [sym trans].
    unfold is_per_type, sym_type, trans_type; dands; introv.

    + intro inh.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y x) (eq y x)).
      intro iff2; dest_imp iff2 hyp.
      rw <- iff2.
      apply sym.
      rw iff1; sp.

    + intros inh1 inh2.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y z) (eq y z)).
      intro iff2; dest_imp iff2 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x z) (eq x z)).
      intro iff3; dest_imp iff3 hyp.
      rw <- iff3.
      apply trans with (y := y).
      rw iff1; sp.
      rw iff2; sp.

  - destruct isper as [sym trans].
    unfold sym_type in sym.
    unfold trans_type in trans.
    unfold is_per; dands; introv.

    + intro inh.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y x) (eq y x)).
      intro iff2; dest_imp iff2 hyp.
      rw iff2.
      apply sym.
      rw <- iff1; sp.

    + intros inh1 inh2.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y z) (eq y z)).
      intro iff2; dest_imp iff2 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x z) (eq x z)).
      intro iff3; dest_imp iff3 hyp.
      rw iff3.
      apply trans with (y := y).
      rw <- iff1; sp.
      rw <- iff2; sp.
Qed.

Lemma is_per_type_iff_is_per1 {p} :
  forall lib R eq,
    (forall x y : @CTerm p, nuprl lib (mkc_apply2 R x y) (eq x y))
    -> (is_per eq <=> is_per_type lib R).
Proof.
  introv n.
  apply is_per_type_iff_is_per; introv.
  generalize (n x y); intro k; auto.
Qed.

Lemma inhabited_type_iff {p} :
  forall lib (T1 T2 : @CTerm p) eq1 eq2,
    nuprl lib T1 eq1
    -> nuprl lib T2 eq2
    -> ((inhabited eq1 <=> inhabited eq2)
        <=> (inhabited_type lib T1 <=> inhabited_type lib T2)).
Proof.
  introv n1 n2.
  generalize (inhabited_type_iff_inhabited lib T1 eq1); intro i1.
  dest_imp i1 hyp.
  generalize (inhabited_type_iff_inhabited lib T2 eq2); intro i2.
  dest_imp i2 hyp.
  allrw; sp.
Qed.


Lemma inhabited_type_cequivc {p} :
  forall lib (a b : @CTerm p),
    cequivc lib a b
    -> inhabited_type lib a
    -> inhabited_type lib b.
Proof.
  introv ceq inh.
  allunfold @inhabited_type; exrepnd.
  allunfold @member.
  exists t.
  apply cequivc_preserving_equality with (A := a); sp.
Qed.

Lemma inhabited_type_respects_cequivc {p} :
  forall lib, respects1 (@cequivc p lib) (inhabited_type lib).
Proof.
  introv; introv.
  apply inhabited_type_cequivc.
Qed.
Hint Resolve inhabited_type_respects_cequivc : respects.

Lemma inhabited_type_tequality {p} :
  forall lib (a b : @CTerm p),
    tequality lib a b
    -> inhabited_type lib a
    -> inhabited_type lib b.
Proof.
  introv teq inh.
  allunfold @inhabited_type; exrepnd.
  allunfold @tequality; exrepnd.
  allunfold @member.
  allunfold @equality; exrepnd.
  exists t.
  generalize (nuprl_uniquely_valued lib a eq eq0); intro i; repeat (dest_imp i hyp).
  { apply Nuprl_refl with (t2 := b); sp. }
  exists eq; sp.
  { apply Nuprl_refl with (t2 := a); sp.
    apply Nuprl_sym; sp. }
  rw i; sp.
Qed.

Lemma inhabited_type_respects_alphaeqc {o} :
  forall lib, respects1 alphaeqc (@inhabited_type o lib).
Proof.
  introv aeq inh.
  apply (alphaeqc_implies_cequivc lib) in aeq.
  apply @inhabited_type_cequivc with (a := a); auto.
Qed.
Hint Resolve inhabited_type_respects_alphaeqc : respects.

Lemma type_respects_cequivc {o} :
  forall lib, respects1 (cequivc lib) (@type o lib).
Proof.
  introv ceq typ.
  apply type_respects_cequivc_left in ceq; auto.
  apply tequality_refl in ceq; eauto 3 with slow.
Qed.
Hint Resolve type_respects_cequivc : respects.

Lemma type_respects_alphaeqc {o} :
  forall lib, respects1 alphaeqc (@type o lib).
Proof.
  introv aeq inh.
  apply (alphaeqc_implies_cequivc lib) in aeq.
  apply type_respects_cequivc_left in aeq; auto.
  apply tequality_refl in aeq; eauto 2 with slow.
Qed.
Hint Resolve type_respects_alphaeqc : respects.

Lemma Nuprl_type_family_equality_to_eq {o} :
  forall lib (A1 A2 : @CTerm o) v1 v2 B1 B2 eqa f (n : Nuprl lib A1 A2 eqa),
    (forall (a1 a2 : CTerm) (e : equality lib a1 a2 A1),
        Nuprl lib (B1) [[v1 \\ a1]] (B2) [[v2 \\ a2]] (f a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           Nuprl lib (B1) [[v1 \\ a1]] (B2) [[v2 \\ a2]] (f a1 a2 (eq_equality2 lib a1 a2 A1 A2 eqa e n))).
Proof.
  introv imp; introv.
  apply imp.
Qed.

Lemma Nuprl_type_family_equality_to_nuprl_left {o} :
  forall lib v1 v2 B1 B2 (eqa : per(o)) f,
    (forall (a1 a2 : CTerm) (e : eqa a1 a2),
        Nuprl lib (B1) [[v1 \\ a1]] (B2) [[v2 \\ a2]] (f a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           nuprl lib (B1) [[v1 \\ a1]] (f a1 a2 e)).
Proof.
  introv imp; introv.
  apply imp.
Qed.

Lemma Nuprl_type_family_equality_to_Nuprl_left {o} :
  forall lib A v1 v2 B1 B2 (eqa : per(o)) f,
    nuprl lib A eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
        Nuprl lib (B1)[[v1\\a1]] (B2)[[v2\\a2]] (f a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           Nuprl lib (B1)[[v1\\a1]] (B1)[[v1\\a2]] (f a1 a2 e)).
Proof.
  introv na imp; introv.

  assert (eqa a2 a2) as ea.
  { nts; eapply nts_tet; eauto.
    eapply nts_tes; eauto. }

  pose proof (imp a1 a2 e) as h1.
  pose proof (imp a2 a2 ea) as h2.

  apply Nuprl_sym in h2.
  eapply Nuprl_trans; eauto.
Qed.

Lemma Nuprl_trans2 {o} :
  forall lib (t1 t2 t3 : @CTerm o) (eq1 eq2 : per(o)),
    Nuprl lib t1 t2 eq1 -> Nuprl lib t2 t3 eq2 -> Nuprl lib t1 t3 eq2.
Proof.
  introv n1 n2.
  pose proof (Nuprl_trans lib t1 t2 t3 eq1 eq2) as q; repeat (autodimp q hyp).
  dup q as h.
  eapply Nuprl_uniquely_valued_right in q;[|exact n2].
  eapply Nuprl_ext;[|apply eq_term_equals_sym;eauto]; auto.
Qed.

Lemma Nuprl_type_family_equality_to_Nuprl_right {o} :
  forall lib A v1 v2 B1 B2 (eqa : per(o)) f,
    nuprl lib A eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
        Nuprl lib (B1)[[v1\\a1]] (B2)[[v2\\a2]] (f a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           Nuprl lib (B2)[[v2\\a1]] (B2)[[v2\\a2]] (f a1 a2 e)).
Proof.
  introv na imp; introv.

  assert (eqa a1 a1) as ea.
  { nts; eapply nts_tet; eauto.
    eapply nts_tes; eauto. }

  pose proof (imp a1 a2 e) as h1.
  pose proof (imp a1 a1 ea) as h2.

  apply Nuprl_sym in h2.
  eapply Nuprl_trans2; eauto.
Qed.

Lemma Nuprl_implies_type_family_members_eq {o} :
  forall lib A v B (eqa : per(o)) f,
    nuprl lib A eqa
    -> (forall a1 a2 (e : eqa a1 a2), Nuprl lib (B)[[v\\a1]] (B)[[v\\a2]] (f a1 a2 e))
    -> type_family_members_eq (nuprl lib) v B eqa f.
Proof.
  introv na imp.

  split; auto.

  { introv; apply imp. }

  split; introv.

  - assert (eqa a a) as ea.
    { nts; eapply nts_tet; eauto. }

    pose proof (imp a a' e1) as h1.
    pose proof (imp a' a e2) as h2.
    pose proof (imp a a ea) as h3.

    eapply Nuprl_uniquely_valued_left in h1;[|exact h3].
    eapply Nuprl_uniquely_valued_right in h2;[|exact h3].
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - assert (eqa a2 a2) as ea.
    { nts; eapply nts_tet; eauto.
      eapply nts_tes; eauto. }

    pose proof (imp a1 a2 e1) as h1.
    pose proof (imp a2 a3 e2) as h2.
    pose proof (imp a2 a2 ea) as h3.

    eapply Nuprl_uniquely_valued_right in h1;[|exact h3].
    eapply Nuprl_uniquely_valued_left in h2;[|exact h3].
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.

Lemma Nuprl_type_family_equality_to_eq2 {o} :
  forall lib (A : @CTerm o) v1 v2 B1 B2 eqa f (n : nuprl lib A eqa),
    (forall (a1 a2 : CTerm) (e : equality lib a1 a2 A),
        Nuprl lib (B1) [[v1 \\ a1]] (B2) [[v2 \\ a2]] (f a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           Nuprl lib (B1) [[v1 \\ a1]] (B2) [[v2 \\ a2]] (f a1 a2 (eq_equality0 lib a1 a2 A eqa e n))).
Proof.
  introv imp; introv.
  apply imp.
Qed.

Lemma Nuprl_type_family_equality_to_eq3 {o} :
  forall lib (A : @CTerm o) v1 v2 B1 B2 eqa f1 f2 (n : nuprl lib A eqa),
    (forall (a1 a2 : CTerm) (e : equality lib a1 a2 A),
        Nuprl lib (B1)[[v1\\a1]] (B2)[[v2\\a1]] (f1 a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : equality lib a1 a2 A),
           Nuprl lib (B1)[[v1\\a1]] (B2)[[v2\\a2]] (f2 a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           Nuprl lib (B1)[[v1\\a1]] (B2)[[v2\\a2]] (f1 a1 a2 (eq_equality0 lib a1 a2 A eqa e n))).
Proof.
  introv imp1 imp2; introv.

  pose proof (imp1 a1 a2 (eq_equality0 lib a1 a2 A eqa e n)) as h1.
  pose proof (imp2 a1 a2 (eq_equality0 lib a1 a2 A eqa e n)) as h2.

  apply Nuprl_refl in h1.

  eapply Nuprl_trans; eauto.
Qed.

Lemma type_family_members_eq_implies_tequality {o} :
  forall lib (A : @CTerm o) v B eqa eqb a1 a2,
    nuprl lib A eqa
    -> type_family_members_eq (nuprl lib) v B eqa eqb
    -> eqa a1 a2
    -> tequality lib (B)[[v\\a1]] (B)[[v\\a2]].
Proof.
  introv n tf ea.
  destruct tf as [tb tf].

  pose proof (tb a1 a2 ea) as q.
  destruct tf as [sym tran].
  exists (eqb a1 a2 ea); split; auto.

  assert (eqa a2 a2) as ea2.
  { nts; eapply nts_tet; eauto.
    eapply nts_tes; eauto. }

  pose proof (tb a2 a2 ea2) as h.

  eapply nuprl_ext;eauto.
  apply eq_term_equals_sym; apply tran.
Qed.

Lemma Nuprli_type_family_equality_to_eq {o} :
  forall lib i (A : @CTerm o) v1 v2 B1 B2 eqa f (n : nuprli lib i A eqa),
    (forall (a1 a2 : CTerm) (e : equality lib a1 a2 A),
        Nuprli lib i (B1) [[v1 \\ a1]] (B2) [[v2 \\ a2]] (f a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           Nuprli lib i (B1) [[v1 \\ a1]] (B2) [[v2 \\ a2]] (f a1 a2 (eq_equality4 lib a1 a2 A eqa i e n))).
Proof.
  introv imp; introv.
  apply imp.
Qed.

Lemma Nuprli_type_family_equality_to_nuprli_left {o} :
  forall lib i v1 v2 B1 B2 (eqa : per(o)) f,
    (forall (a1 a2 : CTerm) (e : eqa a1 a2),
        Nuprli lib i (B1) [[v1 \\ a1]] (B2) [[v2 \\ a2]] (f a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           nuprli lib i (B1) [[v1 \\ a1]] (f a1 a2 e)).
Proof.
  introv imp; introv.
  apply imp.
Qed.

Ltac ntsi i :=
  match goal with
      [ p : POpid , lib : library |- _ ] =>
      pose proof (@nuprli_type_system p lib i) as nts;
        destruct nts as [ nts_uv nts ];
        destruct nts as [ nts_ext nts ];
        destruct nts as [ nts_tyv nts ];
        destruct nts as [ nts_tes nts ];
        destruct nts as [ nts_tet nts_tev ]
  end.

Ltac entsi i :=
  match goal with
      [ p : POpid , lib : library |- _ ] =>
      pose proof (@Nuprli_etype_system p lib i) as nts;
        destruct nts as [ nts_uv nts ];
        destruct nts as [ nts_ext nts ];
        destruct nts as [ nts_tys nts ];
        destruct nts as [ nts_tyt nts ];
        destruct nts as [ nts_tyv nts ];
        destruct nts as [ nts_tes nts ];
        destruct nts as [ nts_tet nts_tev ]
  end.

Lemma Nuprli_refl {p} :
  forall lib i (t1 t2 : @CTerm p) eq,
    Nuprli lib i t1 t2 eq -> Nuprli lib i t1 t1 eq.
Proof.
  intros.
  entsi i.
  eapply nts_tyt; eauto.
Qed.

Lemma Nuprli_sym {p} :
  forall lib i (t1 t2 : @CTerm p) eq,
    Nuprli lib i t1 t2 eq -> Nuprli lib i t2 t1 eq.
Proof.
  intros; entsi i; sp.
Qed.

Lemma Nuprli_trans {p} :
  forall lib i (t1 t2 t3 : @CTerm p) eq1 eq2,
    Nuprli lib i t1 t2 eq1 -> Nuprli lib i t2 t3 eq2 -> Nuprli lib i t1 t3 eq1.
Proof.
  introv n1 n2; entsi i.
  eapply nts_tyt; eauto.
  eapply nts_ext;[eauto|].
  apply Nuprli_sym in n1.
  apply Nuprli_refl in n1.
  apply Nuprli_refl in n2.
  eapply nts_uv; eauto.
Qed.

Lemma Nuprli_uniquely_valued_left {o} :
  forall lib i (t1 t2 t3 : @CTerm o) eq1 eq2,
    Nuprli lib i t1 t2 eq1
    -> Nuprli lib i t1 t3 eq2
    -> (eq1) <=2=> (eq2).
Proof.
  introv n1 n2.
  entsi i.
  apply Nuprli_refl in n1.
  apply Nuprli_refl in n2.
  eapply nts_uv;eauto.
Qed.

Lemma Nuprli_uniquely_valued_right {o} :
  forall lib i (t1 t2 t3 : @CTerm o) eq1 eq2,
    Nuprli lib i t2 t1 eq1
    -> Nuprli lib i t3 t1 eq2
    -> (eq1) <=2=> (eq2).
Proof.
  introv n1 n2.
  entsi i.
  apply Nuprli_sym in n1.
  apply Nuprli_sym in n2.
  apply Nuprli_refl in n1.
  apply Nuprli_refl in n2.
  eapply nts_uv;eauto.
Qed.

Lemma Nuprli_trans2 {o} :
  forall lib i (t1 t2 t3 : @CTerm o) (eq1 eq2 : per(o)),
    Nuprli lib i t1 t2 eq1 -> Nuprli lib i t2 t3 eq2 -> Nuprli lib i t1 t3 eq2.
Proof.
  introv n1 n2.
  pose proof (Nuprli_trans lib i t1 t2 t3 eq1 eq2) as q; repeat (autodimp q hyp).
  dup q as h.
  eapply Nuprli_uniquely_valued_right in q;[|exact n2].
  eapply Nuprli_ext;[|apply eq_term_equals_sym;eauto]; auto.
Qed.

Lemma Nuprli_type_family_equality_to_Nuprli_left {o} :
  forall lib i A v1 v2 B1 B2 (eqa : per(o)) f,
    nuprli lib i A eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
        Nuprli lib i (B1)[[v1\\a1]] (B2)[[v2\\a2]] (f a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           Nuprli lib i (B1)[[v1\\a1]] (B1)[[v1\\a2]] (f a1 a2 e)).
Proof.
  introv na imp; introv.

  assert (eqa a2 a2) as ea.
  { ntsi i; eapply nts_tet; eauto.
    eapply nts_tes; eauto. }

  pose proof (imp a1 a2 e) as h1.
  pose proof (imp a2 a2 ea) as h2.

  apply Nuprli_sym in h2.
  eapply Nuprli_trans; eauto.
Qed.

Lemma Nuprli_type_family_equality_to_Nuprli_right {o} :
  forall lib i A v1 v2 B1 B2 (eqa : per(o)) f,
    nuprli lib i A eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
        Nuprli lib i (B1)[[v1\\a1]] (B2)[[v2\\a2]] (f a1 a2 e))
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
           Nuprli lib i (B2)[[v2\\a1]] (B2)[[v2\\a2]] (f a1 a2 e)).
Proof.
  introv na imp; introv.

  assert (eqa a1 a1) as ea.
  { ntsi i; eapply nts_tet; eauto.
    eapply nts_tes; eauto. }

  pose proof (imp a1 a2 e) as h1.
  pose proof (imp a1 a1 ea) as h2.

  apply Nuprli_sym in h2.
  eapply Nuprli_trans2; eauto.
Qed.

Lemma Nuprli_implies_type_family_members_eq {o} :
  forall lib i A v B (eqa : per(o)) f,
    nuprli lib i A eqa
    -> (forall a1 a2 (e : eqa a1 a2), Nuprli lib i (B)[[v\\a1]] (B)[[v\\a2]] (f a1 a2 e))
    -> type_family_members_eq (nuprli lib i) v B eqa f.
Proof.
  introv na imp.

  split; auto.

  { introv; apply imp. }

  split; introv.

  - assert (eqa a a) as ea.
    { ntsi i; eapply nts_tet; eauto. }

    pose proof (imp a a' e1) as h1.
    pose proof (imp a' a e2) as h2.
    pose proof (imp a a ea) as h3.

    eapply Nuprli_uniquely_valued_left in h1;[|exact h3].
    eapply Nuprli_uniquely_valued_right in h2;[|exact h3].
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - assert (eqa a2 a2) as ea.
    { ntsi i; eapply nts_tet; eauto.
      eapply nts_tes; eauto. }

    pose proof (imp a1 a2 e1) as h1.
    pose proof (imp a2 a3 e2) as h2.
    pose proof (imp a2 a2 ea) as h3.

    eapply Nuprli_uniquely_valued_right in h1;[|exact h3].
    eapply Nuprli_uniquely_valued_left in h2;[|exact h3].
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.

Definition ext_eq {o} lib (A B : @CTerm o) :=
  forall a b, equality lib a b A <=> equality lib a b B.

Lemma type_family_members_eq_implies_eqbs {o} :
  forall ts v B (eqa1 eqa2 : per(o)) eqb1 eqb2,
    uniquely_valued ts
    -> (eqa1 <=2=> eqa2)
    -> type_family_members_eq ts v B eqa1 eqb1
    -> type_family_members_eq ts v B eqa2 eqb2
    -> (forall (a1 a2 : CTerm) (e1 : eqa1 a1 a2) (e2 : eqa2 a1 a2),
           (eqb1 a1 a2 e1) <=2=> (eqb2 a1 a2 e2)).
Proof.
  introv uv eqas tf1 tf2; introv.
  unfold type_family_members_eq in *; repnd.

  pose proof (tf3 a1 a2 e1) as h1.
  pose proof (tf0 a1 a2 e2) as h2.
  eapply uv; eauto.
Qed.

Lemma uniquely_valued_nuprl {o} :
  forall lib, @uniquely_valued o (nuprl lib).
Proof.
  introv; nts; tcsp.
Qed.
Hint Resolve uniquely_valued_nuprl : slow.
