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
  unfold tequality, type, Nuprl; introv; split; intro h; exrepnd; eexists; eauto.
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
    unfold Nuprl in n; tcsp. }

  { unfold equality in k; exrepnd.
    unfold Nuprl in n; repnd.
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
  unfold Nuprl in n; repnd.
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

Lemma eq_equality1 {p} :
  forall lib a b A (eq : per(p)),
    eq a b
    -> Nuprl lib A A eq
    -> equality lib a b A.
Proof.
  introv e n.
  unfold Nuprl in n; repnd.
  unfold equality.
  exists eq; sp.
Defined.

Lemma eq_equality2 {p} :
  forall lib a b A B (eq : per(p)),
    eq a b
    -> Nuprl lib A B eq
    -> equality lib a b A.
Proof.
  introv e n.
  unfold Nuprl in n; repnd.
  unfold equality.
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
  unfold univi_eq in teq0; exrepnd.
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
