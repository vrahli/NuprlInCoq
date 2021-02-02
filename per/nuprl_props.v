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


Lemma nuprli_refl {p} :
  forall lib i t1 t2 eq,
    @nuprli p lib i t1 t2 eq -> nuprli lib i t1 t1 eq.
Proof.
  intros.
  generalize (@nuprli_type_system p lib i); intro nts.
  dest_ts nts.
  apply ts_tyt with (T2 := t2); sp.
Qed.

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
  forall lib A B a b eq,
    @nuprl p lib A B eq
    -> eq a b
    -> eq a a.
Proof.
  sp; nts.
  eapply type_system_term_mem; eauto.
Qed.

Lemma equality_eq_sym {p} :
  forall lib A B a b eq,
    @nuprl p lib A B eq
    -> eq a b
    -> eq b a.
Proof.
  sp; nts.
  apply nts_tes with (T := A) (T' := B); sp.
Qed.

Lemma equality_eq_trans {p} :
  forall lib A B a b c eq,
    @nuprl p lib A B eq
    -> eq a b
    -> eq b c
    -> eq a c.
Proof.
  sp; nts.
  apply nts_tet with (T := A) (T' := B) (t2 := b); sp.
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
  apply nuprl_sym; sp.
Qed.
Hint Resolve tequality_sym : nequality.

Lemma tequality_refl {p} :
  forall lib t1 t2,
    @tequality p lib t1 t2 -> tequality lib t1 t1.
Proof.
  unfold tequality; introv t; exrepnd.
  exists eq.
  apply nuprl_refl in t0; sp.
Qed.
Hint Resolve tequality_refl : nequality.

Lemma tequality_trans {p} :
  forall lib t1 t2 t3,
    @tequality p lib t1 t2 -> tequality lib t2 t3 -> tequality lib t1 t3.
Proof.
  unfold tequality; sp.
  exists eq0.
  eapply nuprl_trans; eauto.
Qed.
Hint Resolve tequality_trans : nequality.

Lemma member_eq {p} :
  forall lib t T,
    @equality p lib t t T = member lib t T.
Proof.
  unfold member; auto.
Qed.

Lemma fold_type {p} :
  forall lib T,
    @tequality p lib T T = type lib T.
Proof.
  unfold type; auto.
Qed.

Lemma fold_equorsq {p} :
  forall lib t1 t2 T,
    (@equality p lib t1 t2 T {+} ccequivcn lib t1 t2) = equorsq lib t1 t2 T.
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
    {eq : per(p) , nuprl lib a b eq} <=> tequality lib a b.
Proof.
  sp.
Qed.

Lemma tequality_if_nuprl {p} :
  forall lib a b eq,
    @nuprl p lib a b eq -> tequality lib a b.
Proof.
  sp.
  apply tequality_iff_nuprl; exists eq; sp.
Qed.

Lemma equality_eq {p} :
  forall lib A a b eq,
    @nuprl p lib A A eq
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
    @nuprl p lib A B eq
    -> (eq a b <=> equality lib a b A).
Proof.
  introv n; split; intro k.
  unfold equality; exists eq; sp.
  apply nuprl_refl in n; sp.
  unfold equality in k; sp.
  assert (eq_term_equals eq eq0) as eqt.
  eapply nuprl_uniquely_valued with (t := A); eauto.
  apply nuprl_refl in n; sp.
  unfold eq_term_equals in eqt.
  apply eqt; sp.
Qed.

Lemma eqindomain_sym {p} :
  forall(a b : @cterm p),
  forall (eqa: per),
  term_equality_symmetric eqa ->
  eqindomain eqa a b -> eqindomain eqa b a.
Proof.  intros. unfold eqindomain.
 unfold term_equality_symmetric in H.
 split; try split; intro. apply H0; auto. apply H0; auto. 
 assert (eqa a b). apply H0; auto. apply H0; auto. apply H. auto.
 
Qed.

Lemma eqindomain_commutes {p} :
  forall  (a b c d : @cterm p) eq,
    term_equality_symmetric eq
    -> term_equality_transitive eq
    -> eqindomain eq a b
    -> eqindomain eq c d
    -> eq a c
    -> eq b d.
Proof.  intros. unfold eqindomain.
 unfold term_equality_symmetric in H.
 unfold term_equality_transitive in H0.
 assert (eq a b). apply H1. eapply H0; eauto.
 assert (eq c d). apply H2. eapply H0; eauto.
 eapply H0; eauto.
 
Qed.


Lemma eqindomain_commutes_equality {p} :
  forall lib a b c d eq A B,
    @nuprl p lib A B eq
    -> eqindomain eq a b
    -> eqindomain eq c d
    -> (equality lib a c A <=> equality lib b d B).
Proof.
  introv n eos1 eos2.
  applydup @nuprl_sym  in n  as n0.
  applydup @nuprl_refl in n0 as n1.
  applydup @nuprl_refl in n  as n2.
  rw <- (equality_eq1 lib A B a c eq n).
  rw <- (equality_eq1 lib B A b d eq n0).
  nts.
  split; sp.
  eapply (eqindomain_commutes); eauto. 
  eapply (eqindomain_commutes); eauto;
  apply eqindomain_sym; auto;
  eapply nts_tes; eauto.
  
Qed.

Lemma eq_equality1 {p} :
  forall lib a b A (eq : per(p)),
    eq a b
    -> nuprl lib A A eq
    -> equality lib a b A.
Proof.
  introv e n.
  unfold equality.
  exists eq; sp.
Defined.

Lemma eq_equality2 {p} :
  forall lib a b A B (eq : per(p)),
    eq a b
    -> nuprl lib A B eq
    -> equality lib a b A.
Proof.
  introv e n.
  unfold equality.
  exists eq; sp.
  apply nuprl_refl in n; sp.
Defined.

Lemma eq_equality3 {p} :
  forall lib a b A B (eq : per(p)) i,
    eq a b
    -> nuprli lib i A B eq
    -> equality lib a b A.
Proof.
  introv e n.
  exists eq; sp.
  apply nuprli_implies_nuprl in n; sp.
  apply nuprl_refl in n; sp.
Qed.

Lemma equality_respects_cequivcn {p} :
  forall lib t1 t2 T,
    @cequivcn p lib t1 t2
    -> member lib t1 T
    -> equality lib t1 t2 T.
Proof.
  unfold member, equality; sp.
  exists eq; sp.
  nts.
  apply nts_tev with (T := T); sp; spcast; sp.
Qed.
Hint Resolve equality_respects_cequivcn : nequality.

Lemma equality_respects_alphaeqcn {p} :
  forall lib t1 t2 T,
    @alphaeqcn p t1 t2
    -> member lib t1 T
    -> equality lib t1 t2 T.
Proof.
  unfold member, equality; introv a m; exrepnd.
  exists eq; sp.
  nts.
  apply nts_tev with (T := T); sp; spcast.
  apply alphaeqcn_implies_cequivcn; sp.
Qed.
Hint Resolve equality_respects_alphaeqcn : nequality.

Lemma equality_respects_cequivcn_left {p} :
  forall lib t1 t2 t T,
    @cequivcn p lib t1 t
    -> equality lib t1 t2 T
    -> equality lib t t2 T.
Proof.
  sp.
  apply @equality_trans with (t2 := t1); sp.
  apply equality_sym.
  apply equality_respects_cequivcn; sp.
  allapply @equality_refl; sp.
Qed.
Hint Resolve equality_respects_cequivcn_left : nequality.

Lemma equality_respects_cequivcn_right {p} :
  forall lib t1 t2 t T,
    @cequivcn p lib t2 t
    -> equality lib t1 t2 T
    -> equality lib t1 t T.
Proof.
  introv c e.
  apply @equality_trans with (t2 := t2); sp.
  apply equality_respects_cequivcn; sp.
  apply equality_sym in e.
  allapply @equality_refl; sp.
Qed.
Hint Resolve equality_respects_cequivcn_right : nequality.

Lemma equality_respects_alphaeqcn_left {p} :
  forall lib t1 t2 t T,
    @alphaeqcn p t1 t
    -> equality lib t1 t2 T
    -> equality lib t t2 T.
Proof.
  sp.
  apply @equality_trans with (t2 := t1); sp.
  apply equality_sym.
  apply equality_respects_cequivcn; sp.
  apply alphaeqcn_implies_cequivcn; sp.
  allapply @equality_refl; sp.
Qed.
Hint Resolve equality_respects_alphaeqcn_left : nequality.

Lemma equality_respects_alphaeqcn_right {p} :
  forall lib t1 t2 t T,
    @alphaeqcn p t2 t
    -> equality lib t1 t2 T
    -> equality lib t1 t T.
Proof.
  introv a e.
  apply @equality_trans with (t2 := t2); sp.
  apply equality_respects_cequivcn; sp.
  apply alphaeqcn_implies_cequivcn; sp.
  apply equality_sym in e.
  allapply @equality_refl; sp.
Qed.
Hint Resolve equality_respects_alphaeqcn_right : nequality.

Lemma tequality_respects_cequivcn_left {p} :
  forall lib T1 T2 T3,
    @cequivcn p lib T1 T3
    -> tequality lib T1 T2
    -> tequality lib T3 T2.
Proof.
  unfold tequality; sp.
  exists eq.
  apply nuprl_value_respecting_left with (t1 := T1); auto.
Qed.
Hint Resolve tequality_respects_cequivcn_left : nequality.

Lemma tequality_respects_cequivcn_right {p} :
  forall lib T1 T2 T3,
    @cequivcn p lib T2 T3
    -> tequality lib T1 T2
    -> tequality lib T1 T3.
Proof.
  unfold tequality; sp.
  exists eq.
  apply nuprl_value_respecting_right with (t2 := T2); auto.
Qed.
Hint Resolve tequality_respects_cequivcn_right : nequality.

Lemma tequality_respects_alphaeqcn_left {p} :
  forall lib T1 T2 T3,
    @alphaeqcn p T1 T3
    -> tequality lib T1 T2
    -> tequality lib T3 T2.
Proof.
  unfold tequality; sp.
  exists eq.
  apply nuprl_value_respecting_left with (t1 := T1); auto.
  apply alphaeqcn_implies_cequivcn; sp.
Qed.
Hint Resolve tequality_respects_alphaeqcn_left : nequality.

Lemma tequality_respects_alphaeqcn_right {p} :
  forall lib T1 T2 T3,
    @alphaeqcn p T2 T3
    -> tequality lib T1 T2
    -> tequality lib T1 T3.
Proof.
  unfold tequality; sp.
  exists eq.
  apply nuprl_value_respecting_right with (t2 := T2); auto.
  apply alphaeqcn_implies_cequivcn; sp.
Qed.
Hint Resolve tequality_respects_alphaeqcn_right : nequality.

Lemma type_respects_cequivcn_left {p} :
  forall lib T T',
    @cequivcn p lib T T'
    -> type lib T
    -> tequality lib T' T.
Proof.
  unfold type; sp.
  apply tequality_respects_cequivcn_left with (T1 := T); auto.
Qed.
Hint Resolve type_respects_cequivcn_left : nequality.

Lemma type_respects_cequivcn_right {p} :
  forall lib T T',
    @cequivcn p lib T T'
    -> type lib T
    -> tequality lib T T'.
Proof.
  unfold type; sp.
  apply tequality_respects_cequivcn_right with (T2 := T); auto.
Qed.
Hint Resolve type_respects_cequivcn_right : nequality.

Lemma type_respects_alphaeqcn_left {p} :
  forall lib T T',
    @alphaeqcn p T T'
    -> type lib T
    -> tequality lib T' T.
Proof.
  unfold type; sp.
  apply tequality_respects_alphaeqcn_left with (T1 := T); auto.
Qed.

Lemma type_respects_alphaeqcn_right {p} :
  forall lib T T',
    @alphaeqcn p T T'
    -> type lib T
    -> tequality lib T T'.
Proof.
  unfold type; sp.
  apply tequality_respects_alphaeqcn_right with (T2 := T); auto.
Qed.

Lemma cequivcn_preserving_equality {p} :
  forall lib a b A B,
    @equality p lib a b A
    -> cequivcn lib A B
    -> equality lib a b B.
Proof.
  unfold equality; introv e c; exrepnd.
  nts.
  unfold type_value_respecting in nts_tyv.
  apply nts_tyv with (eq := eq) in c; sp.
  exists eq; sp.
  generalize (type_system_type_mem2 (nuprl lib) A B eq); sp.
Qed.

Lemma alphaeqcn_preserving_equality {p} :
  forall lib a b A B,
    @equality p lib a b A
    -> alphaeqcn A B
    -> equality lib a b B.
Proof.
  unfold equality; introv e al; exrepnd.
  nts.
  unfold type_value_respecting in nts_tyv.
  apply (alphaeqcn_implies_cequivcn lib) in al.
  apply nts_tyv with (eq := eq) in al; sp.
  exists eq; sp.
  generalize (type_system_type_mem2 (nuprl lib) A B eq); sp.
Qed.

Lemma tequality_preserving_equality {p} :
  forall lib a b A B,
    @equality p lib a b A
    -> tequality lib A B
    -> equality lib a b B.
Proof.
  unfold tequality, equality; introv e t; exrepnd.
  nts.
  assert (nuprl lib A A eq # nuprl lib B B eq) as n; repd.
  apply type_system_type_mem2; sp.
  exists eq; sp.
  assert (eq_term_equals eq0 eq) as eqt.
  apply uniquely_valued_eq with (ts := nuprl lib) (T := A) (T1 := A) (T2 := A); sp.
  apply eqt; sp.
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
  discover; exrepnd.
  allfold (@nuprli p lib j0).
  allapply @nuprli_implies_nuprl.
  nts.
  assert (nuprl lib A A eqa # nuprl lib B B eqa); repd.
  apply type_system_type_mem2; sp.
  exists eqa; sp.
  assert (eq_term_equals eq0 eqa) as k.
  apply uniquely_valued_eq with (ts := nuprl lib) (T := A) (T1 := A) (T2 := A); sp.
  allunfold @eq_term_equals.
  apply k; auto.
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

Hint Resolve tequality_preserving_equality cequivcn_preserving_equality : nequality.

Lemma cequivcn_equality {p} : forall lib, respects3 (cequivcn lib) (@equality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.
Hint Resolve cequivcn_equality : respects.

Lemma sym_cequivcn_eauto {p} : forall lib, symm_rel (@cequivcn p lib).
Proof.
  introv Hab.
  apply cequivcn_sym; auto.
Qed.
Hint Resolve sym_cequivcn_eauto : nequality.
Hint Resolve sym_cequivcn_eauto : respects.

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
  apply cequivcn_sym in ceq.
  rwg ceq.
  apply equality_sym in e1; apply equality_refl in e1; auto.

  apply equality_trans with (t2 := a2); sp.
  apply cequivcn_sym in ceq.
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
  spcast; apply @equality_respects_cequivcn_left with (t1 := t2); sp.
  apply cequivcn_sym; sp.
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
  spcast; apply @equality_respects_cequivcn_right with (t2 := t2); sp.
Qed.

Lemma cequorsq_sym {p} :
  forall lib a b T, @equorsq p lib a b T -> equorsq lib b a T.
Proof.
  unfold equorsq; introv ceq; sp.
  left; apply equality_sym; sp.
  right; spcast; sp; apply cequivcn_sym; sp.
Qed.

Hint Resolve alphaeqcn_preserving_equality : nequality.


Lemma respects_alphaeqcn_equality {p} : forall lib, respects3 alphaeqcn (@equality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.

Lemma sym_alphaeqcn_eauto {p} : symm_rel (@alphaeqcn p).
Proof.
  introv Hab.
  apply alphaeqcn_sym; auto.
Qed.

Hint Resolve respects_alphaeqcn_equality sym_alphaeqcn_eauto : respects.

Lemma respects_alphaeqcn_tequality {p} : forall lib, respects2 alphaeqcn (@tequality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.

Hint Resolve respects_alphaeqcn_tequality : respects.

Lemma respects_cequivcn_tequality {p} :
  forall lib, respects2 (cequivcn lib) (@tequality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.

Hint Resolve respects_cequivcn_tequality : respects.

Lemma respects_cequivcn_equality {p} : forall lib, respects3 (cequivcn lib) (@equality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.

Hint Resolve respects_cequivcn_equality : respects.

Lemma nuprli_sym {p} :
  forall lib i t1 t2 eq,
    @nuprli p lib i t1 t2 eq -> nuprli lib i t2 t1 eq.
Proof.
  intros.
  generalize (@nuprli_type_system p lib i); intro nts.
  dest_ts nts.
  apply ts_tys; sp.
Qed.

Lemma nuprl_ext {p} :
  forall lib t1 t2 eq1 eq2,
    @nuprl p lib t1 t2 eq1
    -> eq_term_equals eq1 eq2
    -> nuprl lib t1 t2 eq2.
Proof.
  introv n1 eqs; nts.
  apply nts_ext with (eq := eq1); sp.
Qed.

Lemma nuprli_ext {p} :
  forall lib i t1 t2 eq1 eq2,
    @nuprli p lib i t1 t2 eq1
    -> eq1 <=2=> eq2
    -> nuprli lib i t1 t2 eq2.
Proof.
  introv n1 eqs.
  generalize (@nuprli_type_system p lib i); intro nts.
  dest_ts nts.
  apply ts_ext with (eq := eq1); sp.
Qed.


Lemma equorsq_tequality {o} :
  forall lib (A B a b : @cterm o),
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


Lemma respects_cequivcn_equorsq {p} : forall lib, respects3 (cequivcn lib) (@equorsq p lib).
Proof.
  unfold equorsq; introv; unfolds_base; dands; introv Hr Heq; allsimpl; dorn Heq;
  try (complete (left; eauto 3 with nequality));
  right; spcast; eauto 3 with nequality.
  apply (cequivcn_trans lib a' a b); auto; apply cequivcn_sym; auto.
  apply (cequivcn_trans lib a b b'); auto; apply cequivcn_sym; auto.
Qed.
Hint Resolve respects_cequivcn_equorsq : respects.

Lemma respects_alphaeqcn_equorsq {p} : forall lib, respects3 alphaeqcn (@equorsq p lib).
Proof.
  unfold equorsq; introv; unfolds_base; dands; introv Hr Heq; allsimpl; dorn Heq;
  try (complete (left; eauto 3 with nequality));
  right; spcast; eauto 3 with nequality.
  apply (cequivcn_trans lib a' a b); auto; apply cequivcn_sym; apply alphaeqcn_implies_cequivcn; auto.
  apply (cequivcn_trans lib a b b'); auto; apply alphaeqcn_implies_cequivcn; auto.
Qed.
Hint Resolve respects_alphaeqcn_equorsq : respects.


Lemma equorsq_sym {o} :
  forall lib (A a b : @cterm o),
    equorsq lib a b A -> equorsq lib b a A.
Proof.
  introv e.
  allunfold @equorsq; sp.
  left; apply equality_sym; auto.
  right; spcast; sp; apply cequivcn_sym; sp.
Qed.


Lemma eqindomain_commutes_nuprl {p} :
  forall lib (a b c d : @cterm p) eq A B,
    nuprl lib A B eq
    -> eqindomain eq a b
    -> eqindomain eq c d
    -> eq a c
    -> eq b d.
Proof.
  introv n e1 e2 e3.
  eapply (eqindomain_commutes); eauto; sp; nts.

  eapply nts_tes; eauto.
  eapply nts_tet; eauto.
  
Qed.

Lemma eqindomain_sym_trans {p} :
  forall lib eq (a b A B : @cterm p),
    nuprl lib A B eq
    -> eqindomain eq a b
    -> eqindomain eq b a.
Proof.
  introv n e.
  apply eqindomain_sym; sp.
  nts.
  unfold term_symmetric in nts_tes.
  apply nts_tes with (T := A) (T' := B); sp.
Qed.

Lemma nuprl_refl2 {p} :
  forall lib (t1 t2 : @cterm p) eq,
    nuprl lib t1 t2 eq -> nuprl lib t2 t2 eq.
Proof.
  introv n.
  apply nuprl_sym in n.
  apply nuprl_refl in n; sp.
Qed.

Lemma nuprl_uniquely_eq_ext {p} :
  forall lib (t1 t2 : @cterm p) eq1 eq2,
    nuprl lib t1 t2 eq1
    -> eq_term_equals eq1 eq2
    -> nuprl lib t1 t2 eq2.
Proof.
  introv n e; nts.
  apply nts_ext with (T := t1) (T' := t2) (eq := eq1); sp.
Qed.


Lemma false_not_inhabited {p} :
  forall lib (t : @cterm p), !member lib t mkcn_false.
Proof.
  introv m.
  rewrite mkcn_false_eq in m.
  unfold member, equality, nuprl in m; exrepnd.
  inversion m1; subst; try not_univ.
  allunfold @per_approx; exrepnd.
  computes_to_value_isvalue.
  discover; sp; GC.
  spcast; allapply @not_axiom_approxc_bot; sp.
Qed.

Lemma equality3_implies_equorsq2 {p} :
  forall lib (a b c d T : @cterm p),
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


Definition inhabited_type {p} lib (T : @cterm p) := {t : cterm , member lib t T}.

Definition sym_type {p} lib (R : @cterm p) :=
  forall x y,
    inhabited_type lib (mkcn_apply2 R x y)
    -> inhabited_type lib (mkcn_apply2 R y x).

Definition trans_type {p} lib (R : @cterm p) :=
  forall x y z,
    inhabited_type lib (mkcn_apply2 R x y)
    -> inhabited_type lib (mkcn_apply2 R y z)
    -> inhabited_type lib (mkcn_apply2 R x z).

Definition is_per_type {p} lib (R : @cterm p) :=
  sym_type lib R # trans_type lib R.

Lemma is_per_type_iff {p} :
  forall lib R1 R2,
    (forall x y : @cterm p,
       inhabited_type lib (mkcn_apply2 R1 x y)
       <=>
       inhabited_type lib (mkcn_apply2 R2 x y))
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
  forall lib (a b R : @cterm p), equality lib a b R -> inhabited_type lib R.
Proof.
  introv eq.
  unfold inhabited_type; exists a.
  apply equality_refl in eq; sp.
Qed.

Lemma inhabited_if_inhabited_type {p} :
  forall lib (T U : @cterm p) eq,
    inhabited_type lib T
    -> nuprl lib T U eq
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
  forall lib (T U : @cterm p) eq,
    nuprl lib T U eq
    -> inhabited eq
    -> inhabited_type lib T.
Proof.
  introv neq inh.
  unfold inhabited_type.
  unfold inhabited in inh; exrepnd.
  exists t.
  unfold member, equality.
  exists eq; sp.
  apply nuprl_refl with (t2 := U); sp.
Qed.

Lemma inhabited_type_iff_inhabited {p} :
  forall lib (T U : @cterm p) eq,
    nuprl lib T U eq
    -> (inhabited eq <=> inhabited_type lib T).
Proof.
  introv neq; split; intro i.
  apply @inhabited_type_if_inhabited with (U := U) (eq := eq); sp.
  eapply inhabited_if_inhabited_type; eauto.
Qed.

Lemma inhabited_if_inhabited_type_i {p} :
  forall lib (T U : @cterm p) eq i,
    inhabited_type lib T
    -> nuprli lib i T U eq
    -> inhabited eq.
Proof.
  introv inh neq.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_if_inhabited_type in neq; auto.
Qed.

Lemma inhabited_type_if_inhabited_i {p} :
  forall lib (T U : @cterm p) eq i,
    nuprli lib i T U eq
    -> inhabited eq
    -> inhabited_type lib T.
Proof.
  introv neq inh.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_type_if_inhabited in neq; auto.
Qed.

Lemma inhabited_type_iff_inhabited_i {p} :
  forall lib (T U : @cterm p) eq i,
    nuprli lib i T U eq
    -> (inhabited eq <=> inhabited_type lib T).
Proof.
  introv neq.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_type_iff_inhabited in neq; auto.
Qed.

Lemma is_per_type_iff_is_per {p} :
  forall lib R eq,
    (forall x y : @cterm p, nuprl lib (mkcn_apply2 R x y) (mkcn_apply2 R x y) (eq x y))
    -> (is_per eq <=> is_per_type lib R).
Proof.
  introv n.
  split; intro isper.

  - destruct isper as [sym trans].
    unfold is_per_type, sym_type, trans_type; dands; introv.

    + intro inh.
      generalize (inhabited_type_iff_inhabited lib (mkcn_apply2 R x y) (mkcn_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkcn_apply2 R y x) (mkcn_apply2 R y x) (eq y x)).
      intro iff2; dest_imp iff2 hyp.
      rw <- iff2.
      apply sym.
      rw iff1; sp.

    + intros inh1 inh2.
      generalize (inhabited_type_iff_inhabited lib (mkcn_apply2 R x y) (mkcn_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkcn_apply2 R y z) (mkcn_apply2 R y z) (eq y z)).
      intro iff2; dest_imp iff2 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkcn_apply2 R x z) (mkcn_apply2 R x z) (eq x z)).
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
      generalize (inhabited_type_iff_inhabited lib (mkcn_apply2 R x y) (mkcn_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkcn_apply2 R y x) (mkcn_apply2 R y x) (eq y x)).
      intro iff2; dest_imp iff2 hyp.
      rw iff2.
      apply sym.
      rw <- iff1; sp.

    + intros inh1 inh2.
      generalize (inhabited_type_iff_inhabited lib (mkcn_apply2 R x y) (mkcn_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkcn_apply2 R y z) (mkcn_apply2 R y z) (eq y z)).
      intro iff2; dest_imp iff2 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkcn_apply2 R x z) (mkcn_apply2 R x z) (eq x z)).
      intro iff3; dest_imp iff3 hyp.
      rw iff3.
      apply trans with (y := y).
      rw <- iff1; sp.
      rw <- iff2; sp.
Qed.

Lemma is_per_type_iff_is_per1 {p} :
  forall lib R1 R2 eq,
    (forall x y : @cterm p, nuprl lib (mkcn_apply2 R1 x y) (mkcn_apply2 R2 x y) (eq x y))
    -> (is_per eq <=> is_per_type lib R1).
Proof.
  introv n.
  apply is_per_type_iff_is_per; introv.
  generalize (n x y); intro k.
  apply nuprl_refl in k; auto.
Qed.

Lemma inhabited_type_iff {p} :
  forall lib (T1 T2 : @cterm p) eq1 eq2,
    nuprl lib T1 T1 eq1
    -> nuprl lib T2 T2 eq2
    -> ((inhabited eq1 <=> inhabited eq2)
        <=> (inhabited_type lib T1 <=> inhabited_type lib T2)).
Proof.
  introv n1 n2.
  generalize (inhabited_type_iff_inhabited lib T1 T1 eq1); intro i1.
  dest_imp i1 hyp.
  generalize (inhabited_type_iff_inhabited lib T2 T2 eq2); intro i2.
  dest_imp i2 hyp.
  allrw; sp.
Qed.


Ltac dest_per :=
  match goal with
      [ H : per_pertype ?lib ?ts ?T1 ?T2 ?eq |- _ ] =>
      let R1     := fresh "R1"     in
      let R2     := fresh "R2"     in
      let eq1    := fresh "eq1"    in
      let eq2    := fresh "eq2"    in
      let c1     := fresh "c1"     in
      let c2     := fresh "c2"     in
      let typ1   := fresh "typ1"   in
      let typ2   := fresh "typ2"   in
      let inhiff := fresh "inhiff" in
      let pereq  := fresh "pereq"  in
      unfold per_pertype in H;
        destruct H as [ R1     H ];
        destruct H as [ R2     H ];
        destruct H as [ eq1    H ];
        destruct H as [ eq2    H ];
        destruct H as [ c1     H ];
        destruct H as [ c2     H ];
        destruct H as [ typ1   H ];
        destruct H as [ typ2   H ];
        destruct H as [ inhiff H ];
        destruct H as [ isper  pereq ]
    | [ H : per_ipertype ?lib ?ts ?T1 ?T2 ?eq |- _ ] =>
      let R1     := fresh "R1"     in
      let R2     := fresh "R2"     in
      let eq1    := fresh "eq1"    in
      let c1     := fresh "c1"     in
      let c2     := fresh "c2"     in
      let typ1   := fresh "eqtyps" in
      let pereq  := fresh "pereq"  in
      unfold per_ipertype in H;
        destruct H as [ R1    H ];
        destruct H as [ R2    H ];
        destruct H as [ eq1   H ];
        destruct H as [ c1    H ];
        destruct H as [ c2    H ];
        destruct H as [ typ1  H ];
        destruct H as [ isper pereq ]
    | [ H : per_spertype ?lib ?ts ?T1 ?T2 ?eq |- _ ] =>
      let R1     := fresh "R1"      in
      let R2     := fresh "R2"      in
      let eq1    := fresh "eq1"     in
      let c1     := fresh "c1"      in
      let c2     := fresh "c2"      in
      let typ1   := fresh "eqtyps1" in
      let typ2   := fresh "eqtyps2" in
      let typ3   := fresh "eqtyps3" in
      let pereq  := fresh "pereq"   in
      unfold per_spertype in H;
        destruct H as [ R1    H ];
        destruct H as [ R2    H ];
        destruct H as [ eq1   H ];
        destruct H as [ c1    H ];
        destruct H as [ c2    H ];
        destruct H as [ typ1  H ];
        destruct H as [ typ2  H ];
        destruct H as [ typ3  H ];
        destruct H as [ isper pereq ]
  end.

Lemma inhabited_type_cequivcn {p} :
  forall lib (a b : @cterm p),
    cequivcn lib a b
    -> inhabited_type lib a
    -> inhabited_type lib b.
Proof.
  introv ceq inh.
  allunfold @inhabited_type; exrepnd.
  allunfold @member.
  exists t.
  apply cequivcn_preserving_equality with (A := a); sp.
Qed.

Lemma inhabited_type_respects_cequivcn {p} :
  forall lib, respects1 (@cequivcn p lib) (inhabited_type lib).
Proof.
  introv; introv.
  apply inhabited_type_cequivcn.
Qed.
Hint Resolve inhabited_type_respects_cequivcn : respects.

Lemma inhabited_type_tequality {p} :
  forall lib (a b : @cterm p),
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
  apply nuprl_refl with (t2 := b); sp.
  exists eq; sp.
  apply nuprl_refl with (t2 := a); sp.
  apply nuprl_sym; sp.
  rw i; sp.
Qed.

Lemma inhabited_type_respects_alphaeqcn {o} :
  forall lib, respects1 alphaeqcn (@inhabited_type o lib).
Proof.
  introv aeq inh.
  apply (alphaeqcn_implies_cequivcn lib) in aeq.
  apply @inhabited_type_cequivcn with (a := a); auto.
Qed.
Hint Resolve inhabited_type_respects_alphaeqcn : respects.

Lemma type_respects_cequivcn {o} :
  forall lib, respects1 (cequivcn lib) (@type o lib).
Proof.
  introv ceq typ.
  apply type_respects_cequivcn_left in ceq; auto.
  apply tequality_refl in ceq; auto.
Qed.
Hint Resolve type_respects_cequivcn : respects.

Lemma type_respects_alphaeqcn {o} :
  forall lib, respects1 alphaeqcn (@type o lib).
Proof.
  introv aeq inh.
  apply (alphaeqcn_implies_cequivcn lib) in aeq.
  apply type_respects_cequivcn_left in aeq; auto.
  apply tequality_refl in aeq; auto.
Qed.
Hint Resolve type_respects_alphaeqcn : respects.

Lemma reduces_toc_eapply_nseq {o} :
  forall lib s (t u : @cterm o),
    reduces_tocn lib t u
    -> reduces_tocn lib (mkcn_eapply (mkcn_nseq s) t) (mkcn_eapply (mkcn_nseq s) u).
Proof.
  introv r.
  destruct_cnterms.
  allunfold @reduces_tocn; allsimpl.
  apply implies_eapply_red_aux; eauto 3 with slow.
Qed.

Lemma reduces_toc_trans {o} :
  forall lib (a b c : @cterm o),
    reduces_tocn lib a b
    -> reduces_tocn lib b c
    -> reduces_tocn lib a c.
Proof.
  introv r1 r2.
  destruct_cnterms.
  allunfold @reduces_tocn; allsimpl.
  eapply reduces_to_trans; eauto.
Qed.

Lemma member_respects_reduces_toc {o} :
  forall lib (t1 t2 T : @cterm o),
  reduces_tocn lib t1 t2
  -> member lib t2 T
  -> member lib t1 T.
Proof.
  introv r m.
  apply reduces_tocn_implies_cequivcn in r.
  apply cequivcn_sym in r.
  eapply equality_respects_cequivcn in r;[|exact m].
  apply equality_sym in r; apply equality_refl in r; auto.
Qed.

Lemma member_respects_cequivcn {o} :
  forall lib (t1 t2 T : @cterm o),
  cequivcn lib t1 t2
  -> member lib t1 T
  -> member lib t2 T.
Proof.
  introv c m.
  eapply equality_respects_cequivcn in c;[|exact m].
  apply equality_sym in c; apply equality_refl in c; auto.
Qed.

Lemma member_respects_cequivcn_type {o} :
  forall lib (t T1 T2 : @cterm o),
  cequivcn lib T1 T2
  -> member lib t T1
  -> member lib t T2.
Proof.
  introv c m.
  eapply cequivcn_preserving_equality; eauto.
Qed.

Lemma substcv_as_substc2 {o} :
  forall x (t : @cterm o) v (u : cvterm [x,v]),
    substcnv [x] t v u = substcn2 x t v u.
Proof.
  introv.
  destruct_cnterms; simpl.
  apply cvnterm_eq; simpl; auto.
Qed.

(* !!MOVE *)
Hint Resolve alphaeqcn_trans : slow.
Hint Resolve alphaeqcn_sym : slow.

Lemma respects_alphaeqcn_alphaeqcn {o} : respects2 alphaeqcn (@alphaeqcn o).
Proof.
  unfold respects2; dands; introv aeq1 aeq2; eauto 3 with slow.
Qed.
Hint Resolve respects_alphaeqcn_alphaeqcn : respects.

Lemma member_respects_alphaeqcn_l {o} :
  forall lib (t1 t2 T : @cterm o),
    alphaeqcn t1 t2 -> member lib t1 T -> member lib t2 T.
Proof.
  introv aeq mem.
  allunfold @member.
  eapply equality_respects_alphaeqcn_left;[exact aeq|].
  eapply equality_respects_alphaeqcn_right;[exact aeq|].
  auto.
Qed.

Lemma member_respects_alphaeqcn_r {o} :
  forall lib (t T1 T2 : @cterm o),
    alphaeqcn T1 T2 -> member lib t T1 -> member lib t T2.
Proof.
  introv aeq mem.
  allunfold @member.
  eapply alphaeqcn_preserving_equality; eauto.
Qed.

Lemma respects_alphaeqcn_member {o} :
  forall (lib : @library o), respects2 alphaeqcn (member lib).
Proof.
  introv; unfold respects2; dands; introv aeq1 aeq2; eauto 3 with slow.
  - eapply member_respects_alphaeqcn_l; eauto.
  - eapply member_respects_alphaeqcn_r; eauto.
Qed.
Hint Resolve respects_alphaeqcn_member : respects.

Lemma respects_alphaeqcn_equorsq3 {o} :
  forall lib (t1 t2 T1 T2 : @cterm o),
    alphaeqcn T1 T2
    -> equorsq lib t1 t2 T1
    -> equorsq lib t1 t2 T2.
Proof.
  introv aeq e.
  eauto 3 with slow.
  pose proof (respects_alphaeqcn_equorsq lib) as h.
  destruct h as [h1 h]; repnd.
  eapply h; eauto.
Qed.

Lemma respects_alphaeqcn_cequivcn {p} : forall lib, respects2 alphaeqcn (@cequivcn p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq; allsimpl;
  try (complete (left; eauto 3 with nequality)).
  - apply (cequivcn_trans lib a' a b); auto; apply cequivcn_sym; apply alphaeqcn_implies_cequivcn; auto.
  - apply (cequivcn_trans lib a b b'); auto; apply alphaeqcn_implies_cequivcn; auto.
Qed.
Hint Resolve respects_alphaeqcn_cequivcn : respects.
