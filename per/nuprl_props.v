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

  Authors: Vincent Rahli & Abhishek Anand

*)


Require Export per_ceq_bar.
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


(* !!MOVE *)
Hint Resolve nuprli_implies_nuprl : slow.

Lemma nuprli_refl {p} :
  forall lib i t1 t2 eq,
    @nuprli p i lib t1 t2 eq -> nuprli i lib t1 t1 eq.
Proof.
  intros.
  generalize (@nuprli_type_system p i); intro nts.
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
  eapply nts_tes; eauto.
Qed.

Lemma equality_eq_trans {p} :
  forall lib A B a b c eq,
    @nuprl p lib A B eq
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
    (@equality p lib t1 t2 T {+} ccequivc_ext lib t1 t2) = equorsq lib t1 t2 T.
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

Lemma eqorceq_commutes_equality {p} :
  forall lib a b c d eq A B,
    @nuprl p lib A B eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq c d
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

  { apply (eqorceq_commutes lib) with (a := a) (c := c); auto.
    - apply nts_tev with (T := A); auto.
    - eapply nts_tes; eauto.
    - eapply nts_tet; eauto. }

  { apply (eqorceq_commutes lib) with (a := b) (c := d); auto.
    - apply nts_tev with (T := A); auto.
    - eapply nts_tes; eauto.
    - eapply nts_tet; eauto.
    - apply eqorceq_sym; auto.
      eapply nts_tes; eauto.
    - apply eqorceq_sym; auto.
      eapply nts_tes; eauto. }
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
    -> nuprli i lib A B eq
    -> equality lib a b A.
Proof.
  introv e n.
  exists eq; sp.
  apply nuprli_implies_nuprl in n; sp.
  apply nuprl_refl in n; sp.
Qed.

Lemma equality_respects_cequivc {p} :
  forall lib t1 t2 T,
    @ccequivc_ext p lib t1 t2
    -> member lib t1 T
    -> equality lib t1 t2 T.
Proof.
  unfold member, equality; sp.
  exists eq; sp.
  nts.
  eapply nts_tev; eauto.
Qed.
Hint Resolve equality_respects_cequivc : nequality.

Lemma alphaeqc_implies_ccequivc_ext {o} :
  forall lib (t1 t2 : @CTerm o),
    alphaeqc t1 t2
    -> ccequivc_ext lib t1 t2.
Proof.
  introv aeq ext; spcast.
  apply alphaeqc_implies_cequivc; auto.
Qed.
Hint Resolve alphaeqc_implies_ccequivc_ext : slow.

Lemma equality_respects_alphaeqc {p} :
  forall lib t1 t2 T,
    @alphaeqc p t1 t2
    -> member lib t1 T
    -> equality lib t1 t2 T.
Proof.
  unfold member, equality; introv a m; exrepnd.
  exists eq; sp.
  nts.
  eapply nts_tev; eauto; eauto 3 with slow.
Qed.
Hint Resolve equality_respects_alphaeqc : nequality.

Lemma equality_respects_cequivc_left {p} :
  forall lib t1 t2 t T,
    @ccequivc_ext p lib t1 t
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
    @ccequivc_ext p lib t2 t
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
  apply equality_respects_cequivc; sp; eauto 3 with slow.
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
  apply equality_respects_cequivc; sp; eauto 3 with slow.
  apply equality_sym in e.
  allapply @equality_refl; sp.
Qed.
Hint Resolve equality_respects_alphaeqc_right : nequality.

Lemma tequality_respects_cequivc_left {p} :
  forall lib T1 T2 T3,
    @ccequivc_ext p lib T1 T3
    -> tequality lib T1 T2
    -> tequality lib T3 T2.
Proof.
  unfold tequality; sp.
  exists eq.
  apply nuprl_value_respecting_left with (t1 := T1); auto.
Qed.
Hint Resolve tequality_respects_cequivc_left : nequality.

Lemma tequality_respects_cequivc_right {p} :
  forall lib T1 T2 T3,
    @ccequivc_ext p lib T2 T3
    -> tequality lib T1 T2
    -> tequality lib T1 T3.
Proof.
  unfold tequality; sp.
  exists eq.
  apply nuprl_value_respecting_right with (t2 := T2); auto.
Qed.
Hint Resolve tequality_respects_cequivc_right : nequality.

Lemma tequality_respects_alphaeqc_left {p} :
  forall lib T1 T2 T3,
    @alphaeqc p T1 T3
    -> tequality lib T1 T2
    -> tequality lib T3 T2.
Proof.
  unfold tequality; sp.
  exists eq.
  apply nuprl_value_respecting_left with (t1 := T1); auto; eauto 3 with slow.
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
  apply nuprl_value_respecting_right with (t2 := T2); auto; eauto 3 with slow.
Qed.
Hint Resolve tequality_respects_alphaeqc_right : nequality.

Lemma type_respects_cequivc_left {p} :
  forall lib T T',
    @ccequivc_ext p lib T T'
    -> type lib T
    -> tequality lib T' T.
Proof.
  unfold type; sp.
  apply tequality_respects_cequivc_left with (T1 := T); auto.
Qed.
Hint Resolve type_respects_cequivc_left : nequality.

Lemma type_respects_cequivc_right {p} :
  forall lib T T',
    @ccequivc_ext p lib T T'
    -> type lib T
    -> tequality lib T T'.
Proof.
  unfold type; sp.
  apply tequality_respects_cequivc_right with (T2 := T); auto.
Qed.
Hint Resolve type_respects_cequivc_right : nequality.

Lemma type_respects_alphaeqc_left {p} :
  forall lib T T',
    @alphaeqc p T T'
    -> type lib T
    -> tequality lib T' T.
Proof.
  unfold type; sp.
  apply tequality_respects_alphaeqc_left with (T1 := T); auto.
Qed.

Lemma type_respects_alphaeqc_right {p} :
  forall lib T T',
    @alphaeqc p T T'
    -> type lib T
    -> tequality lib T T'.
Proof.
  unfold type; sp.
  apply tequality_respects_alphaeqc_right with (T2 := T); auto.
Qed.

Lemma cequivc_preserving_equality {p} :
  forall lib a b A B,
    @equality p lib a b A
    -> ccequivc_ext lib A B
    -> equality lib a b B.
Proof.
  unfold equality; introv e c; exrepnd.
  nts.
  unfold type_value_respecting in nts_tyv.
  eapply nts_tyv in c; eauto.
Qed.

Lemma alphaeqc_preserving_equality {p} :
  forall lib a b A B,
    @equality p lib a b A
    -> alphaeqc A B
    -> equality lib a b B.
Proof.
  unfold equality; introv e al; exrepnd.
  nts.
  unfold type_value_respecting in nts_tyv.
  apply (alphaeqc_implies_ccequivc_ext lib) in al.
  apply nts_tyv with (eq := eq) in al; sp.
  exists eq; sp.
  generalize (type_system_type_mem2 nuprl lib A B eq); sp.
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
  eapply uniquely_valued_eq; eauto.
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

Lemma dest_nuprl_uni {o} :
  forall (lib : @library o) i eq,
    nuprl lib (mkc_uni i) (mkc_uni i) eq
    -> univ lib  (mkc_uni i) (mkc_uni i) eq.
Proof.
  introv cl.
  eapply dest_close_per_uni_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma ccomputes_to_valc_ext_implies_ccequivc_ext {o} :
  forall lib (a b : @CTerm o),
    ccomputes_to_valc_ext lib a b
    -> ccequivc_ext lib a b.
Proof.
  introv comp ext; apply comp in ext; clear comp; exrepnd; spcast.
  eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;eauto|].
  apply cequivc_sym;auto.
Qed.

Lemma univ_implies_univi_bar {o} :
  forall lib i (eq : per(o)),
    univ lib (mkc_uni i) (mkc_uni i) eq
    -> exists j, i < j # univi_bar j lib (mkc_uni i) (mkc_uni i) eq.
Proof.
  introv u.
  exists (S i); dands; try omega.
  unfold univ, univi_bar, per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
  unfold univ_ex in u1; exrepnd.
  allrw @univi_exists_iff; exrepnd; GC.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in u3.
  apply ccequivc_ext_uni_uni_implies in u3; subst.
  exists j; dands; eauto 3 with slow.
Qed.

Lemma univ_implies_univi_bar2 {o} :
  forall lib i (eq : per(o)),
    univ lib (mkc_uni i) (mkc_uni i) eq
    ->
    exists (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq lib eqa))
        # in_open_bar_ext lib (fun lib' x => (eqa lib' x) <=2=> (univi_eq (univi_bar i) lib')).
Proof.
  introv u.
  unfold univ, univi_bar, per_bar in u; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
  unfold univ_ex in u1; exrepnd.
  allrw @univi_exists_iff; exrepnd; GC.
  apply ccomputes_to_valc_ext_implies_ccequivc_ext in u3.
  apply ccequivc_ext_uni_uni_implies in u3; subst; auto.
Qed.

Lemma univ_implies_univi_bar3 {o} :
  forall lib i (eq : per(o)),
    univ lib (mkc_uni i) (mkc_uni i) eq
    -> eq <=2=> (per_bar_eq lib (univi_eq_lib_per lib i)).
Proof.
  introv u.
  apply univ_implies_univi_bar2 in u; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  apply implies_eq_term_equals_per_bar_eq; auto.
Qed.

Lemma ts_implies_per_bar_nuprl {o} :
  @ts_implies_per_bar o nuprl.
Proof.
  introv h.
  apply close_implies_per_bar; auto; eauto 3 with slow.
Qed.
Hint Resolve ts_implies_per_bar_nuprl : slow.

Lemma local_ts_nuprl {o} :
  @local_ts o nuprl.
Proof.
  introv e alla.
  apply CL_bar.
  exists eqa; dands; auto.
Qed.
Hint Resolve local_ts_nuprl : slow.

Lemma type_transitive_nuprl {o} :
  @type_transitive o nuprl.
Proof.
  apply nuprl_type_system.
Qed.
Hint Resolve type_transitive_nuprl : slow.

Lemma type_transitive_nuprli {o} :
  forall i, @type_transitive o (nuprli i).
Proof.
  introv; apply nuprli_type_system.
Qed.
Hint Resolve type_transitive_nuprli : slow.

Lemma type_symmetric_nuprl {o} :
  @type_symmetric o nuprl.
Proof.
  apply nuprl_type_system.
Qed.
Hint Resolve type_symmetric_nuprl : slow.

Lemma type_symmetric_nuprli {o} :
  forall i, @type_symmetric o (nuprli i).
Proof.
  apply nuprli_type_system.
Qed.
Hint Resolve type_symmetric_nuprli : slow.

Lemma uniquely_valued_nuprl {o} :
  @uniquely_valued o nuprl.
Proof.
  apply nuprl_type_system.
Qed.
Hint Resolve uniquely_valued_nuprl : slow.

Lemma type_extensionality_nuprl {o} :
  @type_extensionality o nuprl.
Proof.
  apply nuprl_type_system.
Qed.
Hint Resolve type_extensionality_nuprl : slow.

Lemma univi_eq_preserves_nuprl {o} :
  forall i lib (A B : @CTerm o) eq,
    univi_eq (univi_bar i) lib A B
    -> nuprl lib A A eq
    -> nuprl lib B B eq.
Proof.
  introv u n.
  unfold univi_eq in u; exrepnd.
  fold (@nuprli o i) in *.
  apply nuprli_implies_nuprl in u0.

  assert (nuprl lib A A eqa) as h.
  { eapply type_transitive_nuprl; eauto.
    apply type_symmetric_nuprl; auto. }

  eapply uniquely_valued_nuprl in h; autodimp h hyp; try exact n.
  eapply type_extensionality_nuprl;[|eauto].

  eapply type_transitive_nuprl; eauto.
  apply type_symmetric_nuprl; auto.
Qed.
Hint Resolve univi_eq_preserves_nuprl : slow.

(* CRAZY *)
Lemma tequalityi_preserving_equality {o} :
  forall lib i a b (A B : @CTerm o),
    equality lib a b A
    -> tequalityi lib i A B
    -> equality lib a b B.
Proof.
  unfold tequalityi, equality; introv e teq; exrepnd.
  apply dest_nuprl_uni in teq1.
  apply univ_implies_univi_bar3 in teq1; exrepnd.

  apply teq1 in teq0; clear teq1.
  unfold per_bar_eq in teq0.
  exists eq0; dands; auto.
  apply ts_implies_per_bar_nuprl in e1.
  unfold per_bar in e1; exrepnd.
  apply CL_bar.
  fold (@nuprl o) in *.

  exists eqa; dands; auto;[].
  eapply in_open_bar_ext_comb; try exact e1; clear e1.
  eapply in_open_bar_ext_pres; eauto; clear teq0; introv teq0 e1.
  simpl in *; eauto 3 with slow.
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

Lemma cequivc_equality {p} : forall lib, respects3 (ccequivc_ext lib) (@equality p lib).
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

Lemma sym_ccequivc_ext_eauto {p} : forall lib, symm_rel (@ccequivc_ext p lib).
Proof.
  introv Hab.
  apply ccequivc_ext_sym; auto.
Qed.
Hint Resolve sym_ccequivc_ext_eauto : nequality.
Hint Resolve sym_ccequivc_ext_eauto : respects.

Lemma cequorsq2_prop {p} :
  forall lib A a1 a2 b1 b2,
    @equorsq2 p lib a1 b1 a2 b2 A
    -> equality lib a1 a2 A
    -> equality lib a1 b2 A.
Proof.
  introv ceq e1.
  unfold equorsq2, equorsq in ceq; repnd; repdors; spcast.

  { apply equality_trans with (t2 := a2); sp. }

  { apply equality_trans with (t2 := a2); sp. }

  { apply equality_trans with (t2 := a2); sp.
    apply ccequivc_ext_sym in ceq.
    rwg ceq.
    apply equality_sym in e1; apply equality_refl in e1; auto. }

  { apply equality_trans with (t2 := a2); sp.
    apply ccequivc_ext_sym in ceq.
    rwg ceq.
    apply equality_sym in e1; apply equality_refl in e1; auto. }
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
  apply ccequivc_ext_sym; sp.
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
  right; spcast; sp; apply ccequivc_ext_sym; sp.
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
  forall lib, respects2 (ccequivc_ext lib) (@tequality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.

Hint Resolve respects_cequivc_tequality : respects.

Lemma respects_cequivc_equality {p} :
  forall lib, respects3 (ccequivc_ext lib) (@equality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.

Hint Resolve respects_cequivc_equality : respects.

Lemma nuprli_sym {p} :
  forall lib i t1 t2 eq,
    @nuprli p i lib t1 t2 eq -> nuprli i lib t2 t1 eq.
Proof.
  intros.
  generalize (@nuprli_type_system p i); intro nts.
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
    @nuprli p i lib t1 t2 eq1
    -> eq1 <=2=> eq2
    -> nuprli i lib t1 t2 eq2.
Proof.
  introv n1 eqs.
  generalize (@nuprli_type_system p i); intro nts.
  dest_ts nts.
  apply ts_ext with (eq := eq1); sp.
Qed.

Lemma eqorceq_iff_equorsq {o} :
  forall lib (A B a b : @CTerm o) eq,
    nuprl lib A B eq
    -> (eqorceq lib eq a b <=> equorsq lib a b A).
Proof.
  introv n.
  unfold eqorceq, equorsq.
  split; intro k; dorn k; auto; left; apply nuprl_refl in n; auto.
  - exists eq; dands; auto.
  - pose proof (equality_eq lib A a b eq n) as h; apply h; auto.
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


Lemma respects_cequivc_equorsq {p} :
  forall lib, respects3 (ccequivc_ext lib) (@equorsq p lib).
Proof.
  unfold equorsq; introv; unfolds_base; dands; introv Hr Heq; allsimpl; dorn Heq;
  try (complete (left; eauto 3 with nequality));
  right; spcast; eauto 3 with nequality.
  apply (ccequivc_ext_trans lib a' a b); auto; apply ccequivc_ext_sym; auto.
  apply (ccequivc_ext_trans lib a b b'); auto; apply ccequivc_ext_sym; auto.
Qed.
Hint Resolve respects_cequivc_equorsq : respects.

Lemma respects_alphaeqc_equorsq {p} :
  forall lib, respects3 alphaeqc (@equorsq p lib).
Proof.
  unfold equorsq; introv; unfolds_base; dands; introv Hr Heq; allsimpl; dorn Heq;
  try (complete (left; eauto 3 with nequality));
  right; spcast; eauto 3 with nequality.
  { apply (ccequivc_ext_trans lib a' a b); auto; apply ccequivc_ext_sym; eauto 3 with slow. }
  { apply (ccequivc_ext_trans lib a b b'); auto; eauto 3 with slow. }
Qed.
Hint Resolve respects_alphaeqc_equorsq : respects.


Lemma equorsq_sym {o} :
  forall lib (A a b : @CTerm o),
    equorsq lib a b A -> equorsq lib b a A.
Proof.
  introv e.
  allunfold @equorsq; sp.
  left; apply equality_sym; auto.
  right; spcast; sp; apply ccequivc_ext_sym; sp.
Qed.


Lemma eqorceq_commutes_nuprl {p} :
  forall lib (a b c d : @CTerm p) eq A B,
    nuprl lib A B eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq c d
    -> eq a c
    -> eq b d.
Proof.
  introv n e1 e2 e3.
  apply (eqorceq_commutes lib) with (a := a) (c := c); sp.

  { nts.
    unfold term_value_respecting in nts_tev.
    apply nts_tev with (T := A).
    allapply @nuprl_refl; sp. }

  { nts.
    unfold term_symmetric in nts_tes.
    eapply nts_tes; eauto. }

  { nts.
    unfold term_transitive in nts_tet.
    eapply nts_tet; eauto. }
Qed.

Lemma eqorceq_sym_trans {p} :
  forall lib eq (a b A B : @CTerm p),
    nuprl lib A B eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq b a.
Proof.
  introv n e.
  apply eqorceq_sym; sp.
  nts.
  unfold term_symmetric in nts_tes.
  eapply nts_tes; eauto.
Qed.

Lemma nuprl_refl2 {p} :
  forall lib (t1 t2 : @CTerm p) eq,
    nuprl lib t1 t2 eq -> nuprl lib t2 t2 eq.
Proof.
  introv n.
  apply nuprl_sym in n.
  apply nuprl_refl in n; sp.
Qed.

Lemma nuprl_uniquely_eq_ext {p} :
  forall lib (t1 t2 : @CTerm p) eq1 eq2,
    nuprl lib t1 t2 eq1
    -> eq_term_equals eq1 eq2
    -> nuprl lib t1 t2 eq2.
Proof.
  introv n e; nts.
  apply nts_ext with (T := t1) (T' := t2) (eq := eq1); sp.
Qed.

Lemma equality_or_cequivc_eqorceq {p} :
  forall lib (A a b : @CTerm p) eq,
    nuprl lib A A eq
    -> (eqorceq lib eq a b <=> (equality lib a b A {+} ccequivc_ext lib a b)).
Proof.
  unfold eqorceq; introv n; split; intro e; repdors; try (complete sp);
  left;
  apply @equality_eq with (a := a) (b := b) in n;
  allrw <-; sp;
  allrw; sp.
Qed.

Lemma eqorceq_implies_equality_or_cequivc {p} :
  forall lib (A a b : @CTerm p) eq,
    nuprl lib A A eq
    -> eqorceq lib eq a b
    -> (equality lib a b A {+} ccequivc_ext lib a b).
Proof.
  introv n e.
  generalize (equality_or_cequivc_eqorceq lib A a b eq); sp.
  allrw <-; sp.
Qed.

(*Lemma mkc_approx_computes_to_valc_ceq_bar_implies {o} :
  forall lib (bar : BarLib lib) (a b c d : @CTerm o),
    ((mkc_approx a b) ==b==>(bar) (mkc_approx c d))
    -> all_in_bar bar (fun lib => ccequivc lib a c # ccequivc lib b d).
Proof.
  introv comp br ext.
  pose proof (comp lib' br lib'0 ext) as comp; simpl in *; exrepnd; spcast.
  computes_to_value_isvalue.
  apply cequivc_decomp_approx in comp0; repnd.
  dands; spcast; auto.
Qed.*)

Lemma dest_nuprl_approx {o} :
  forall (lib : @library o) (a b c d : @CTerm o) eq,
    nuprl lib (mkc_approx a b) (mkc_approx c d) eq
    -> per_bar (per_approx nuprl) lib (mkc_approx a b) (mkc_approx c d) eq.
Proof.
  introv cl.
  eapply dest_close_per_approx_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

(*Lemma implies_all_in_bar_in_ext {o} :
  forall {lib} (bar : @BarLib o lib) F,
    all_in_bar bar F
    -> all_in_bar bar (fun lib' => in_ext lib' F).
Proof.
  introv h br ext x.
  apply (h _ br lib'1); eauto 3 with slow.
Qed.*)

(*Lemma all_in_bar_in_ext_implies {o} :
  forall {lib} (bar : @BarLib o lib) F,
    all_in_bar bar (fun lib' => in_ext lib' F)
    -> all_in_bar bar F.
Proof.
  introv h br ext.
  apply (h _ br lib'0); eauto 3 with slow.
Qed.*)

Lemma ccequivc_ext_implies_eq_term_equals_per_approx_eq_bar {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o),
    ccequivc_ext lib a1 a2
    -> ccequivc_ext lib b1 b2
    -> (per_approx_eq_bar lib a1 b1) <=2=> (per_approx_eq_bar lib a2 b2).
Proof.
  introv ceq1 ceq2; introv; split; intro h;
    eapply per_approx_eq_bar_respects_ccequivc_ext; eauto; eauto 3 with slow.
Qed.

Lemma implies_in_ext_ccequiv_iff {o} :
  forall lib (a a' b b' c c' d d' : @CTerm o),
    ccequivc_ext lib a a'
    -> ccequivc_ext lib b b'
    -> ccequivc_ext lib c c'
    -> ccequivc_ext lib d d'
    -> in_ext lib (fun lib => a' ~<~(lib) b' <=> c' ~<~(lib) d')
    -> in_ext lib (fun lib => a ~<~(lib) b <=> c ~<~(lib) d).
Proof.
  introv ceqa ceqb ceqc ceqd h ext.
  pose proof (ceqa _ ext) as ceqa.
  pose proof (ceqb _ ext) as ceqb.
  pose proof (ceqc _ ext) as ceqc.
  pose proof (ceqd _ ext) as ceqd.
  pose proof (h _ ext) as h.
  simpl in *.
  split; intro q; spcast.

  { eapply cequivc_approxc_trans;[exact ceqc|].
    eapply approxc_cequivc_trans;[|apply cequivc_sym;exact ceqd].
    apply approx_stable; apply h; spcast.
    eapply cequivc_approxc_trans;[apply cequivc_sym;exact ceqa|].
    eapply approxc_cequivc_trans;[|exact ceqb]; auto. }

  { eapply cequivc_approxc_trans;[exact ceqa|].
    eapply approxc_cequivc_trans;[|apply cequivc_sym;exact ceqb].
    apply approx_stable; apply h; spcast.
    eapply cequivc_approxc_trans;[apply cequivc_sym;exact ceqc|].
    eapply approxc_cequivc_trans;[|exact ceqd]; auto. }
Qed.

Lemma dest_nuprl_approx2 {o} :
  forall lib (eq : per(o)) a b c d,
    nuprl lib (mkc_approx a b) (mkc_approx c d) eq
    ->
    (
      (eq <=2=> (per_bar_eq lib (per_approx_eq_bar_lib_per lib a b)))
        # in_open_bar lib (fun lib => (capproxc lib a b <=> capproxc lib c d))
    ).
Proof.
  introv u.
  apply dest_nuprl_approx in u.
  unfold per_bar in u; exrepnd.

  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_bar_eq.
    eapply in_open_bar_ext_pres; eauto; clear u1; introv u1; simpl.
    unfold per_approx in *; exrepnd; spcast.

    apply ccomputes_to_valc_ext_implies_ccequivc_ext in u2.
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in u3.
    apply cequivc_ext_mkc_approx_right in u2.
    apply cequivc_ext_mkc_approx_right in u3.
    repnd.
    eapply eq_term_equals_trans;[eauto|].
    apply ccequivc_ext_implies_eq_term_equals_per_approx_eq_bar; eauto 3 with slow.
  }

  {
    eapply in_open_bar_comb2; eauto; clear u1.
    apply in_ext_ext_implies_in_open_bar_ext; introv u1.
    unfold per_approx in *; exrepnd.

    apply ccomputes_to_valc_ext_implies_ccequivc_ext in u2.
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in u3.
    apply cequivc_ext_mkc_approx_right in u2.
    apply cequivc_ext_mkc_approx_right in u3.
    repnd.
    eapply implies_in_ext_ccequiv_iff; eauto 3 with slow.
  }
Qed.

Lemma false_not_inhabited {p} :
  forall lib (t : @CTerm p), !member lib t mkc_false.
Proof.
  introv m.
  rewrite mkc_false_eq in m.
  unfold member, equality, nuprl in m; exrepnd.
  apply dest_nuprl_approx2 in m1; exrepnd.
  apply m2 in m0; clear m2.

  unfold per_bar_eq in m0.
  apply (in_open_bar_ext_const lib).
  eapply in_open_bar_ext_comb2; try exact m1; clear m1.
  eapply in_open_bar_ext_pres; try exact m0; clear m0; introv m0 m1; simpl in *.

  unfold per_approx_eq_bar in m0.
  apply (in_open_bar_const lib').
  eapply in_open_bar_pres; eauto; clear m0; introv ext m0.

  unfold per_approx_eq in m0; repnd; spcast.
  apply not_axiom_approxc_bot in m0; auto.
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
  forall lib (T U : @CTerm p) eq,
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
  forall lib (T U : @CTerm p) eq,
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
  forall lib (T U : @CTerm p) eq,
    nuprl lib T U eq
    -> (inhabited eq <=> inhabited_type lib T).
Proof.
  introv neq; split; intro i.
  apply @inhabited_type_if_inhabited with (U := U) (eq := eq); sp.
  eapply inhabited_if_inhabited_type; eauto.
Qed.

Lemma inhabited_if_inhabited_type_i {p} :
  forall lib (T U : @CTerm p) eq i,
    inhabited_type lib T
    -> nuprli i lib T U eq
    -> inhabited eq.
Proof.
  introv inh neq.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_if_inhabited_type in neq; auto.
Qed.

Lemma inhabited_type_if_inhabited_i {p} :
  forall lib (T U : @CTerm p) eq i,
    nuprli i lib T U eq
    -> inhabited eq
    -> inhabited_type lib T.
Proof.
  introv neq inh.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_type_if_inhabited in neq; auto.
Qed.

Lemma inhabited_type_iff_inhabited_i {p} :
  forall lib (T U : @CTerm p) eq i,
    nuprli i lib T U eq
    -> (inhabited eq <=> inhabited_type lib T).
Proof.
  introv neq.
  apply nuprli_implies_nuprl in neq.
  apply inhabited_type_iff_inhabited in neq; auto.
Qed.

Lemma is_per_type_iff_is_per {p} :
  forall lib R eq,
    (forall x y : @CTerm p, nuprl lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq x y))
    -> (is_per eq <=> is_per_type lib R).
Proof.
  introv n.
  split; intro isper.

  - destruct isper as [sym trans].
    unfold is_per_type, sym_type, trans_type; dands; introv.

    + intro inh.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y x) (mkc_apply2 R y x) (eq y x)).
      intro iff2; dest_imp iff2 hyp.
      rw <- iff2.
      apply sym.
      rw iff1; sp.

    + intros inh1 inh2.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y z) (mkc_apply2 R y z) (eq y z)).
      intro iff2; dest_imp iff2 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x z) (mkc_apply2 R x z) (eq x z)).
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
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y x) (mkc_apply2 R y x) (eq y x)).
      intro iff2; dest_imp iff2 hyp.
      rw iff2.
      apply sym.
      rw <- iff1; sp.

    + intros inh1 inh2.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x y) (mkc_apply2 R x y) (eq x y)).
      intro iff1; dest_imp iff1 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R y z) (mkc_apply2 R y z) (eq y z)).
      intro iff2; dest_imp iff2 hyp.
      generalize (inhabited_type_iff_inhabited lib (mkc_apply2 R x z) (mkc_apply2 R x z) (eq x z)).
      intro iff3; dest_imp iff3 hyp.
      rw iff3.
      apply trans with (y := y).
      rw <- iff1; sp.
      rw <- iff2; sp.
Qed.

Lemma is_per_type_iff_is_per1 {p} :
  forall lib R1 R2 eq,
    (forall x y : @CTerm p, nuprl lib (mkc_apply2 R1 x y) (mkc_apply2 R2 x y) (eq x y))
    -> (is_per eq <=> is_per_type lib R1).
Proof.
  introv n.
  apply is_per_type_iff_is_per; introv.
  generalize (n x y); intro k.
  apply nuprl_refl in k; auto.
Qed.

Lemma inhabited_type_iff {p} :
  forall lib (T1 T2 : @CTerm p) eq1 eq2,
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

Lemma inhabited_type_cequivc {p} :
  forall lib (a b : @CTerm p),
    ccequivc_ext lib a b
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
  forall lib, respects1 (@ccequivc_ext p lib) (inhabited_type lib).
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
  apply nuprl_refl with (t2 := b); sp.
  exists eq; sp.
  apply nuprl_refl with (t2 := a); sp.
  apply nuprl_sym; sp.
  rw i; sp.
Qed.

Lemma inhabited_type_respects_alphaeqc {o} :
  forall lib, respects1 alphaeqc (@inhabited_type o lib).
Proof.
  introv aeq inh.
  apply (alphaeqc_implies_ccequivc_ext lib) in aeq.
  apply @inhabited_type_cequivc with (a := a); auto; eauto 3 with slow.
Qed.
Hint Resolve inhabited_type_respects_alphaeqc : respects.

Lemma type_respects_cequivc {o} :
  forall lib, respects1 (ccequivc_ext lib) (@type o lib).
Proof.
  introv ceq typ.
  apply type_respects_cequivc_left in ceq; auto.
  apply tequality_refl in ceq; auto.
Qed.
Hint Resolve type_respects_cequivc : respects.

Lemma type_respects_alphaeqc {o} :
  forall lib, respects1 alphaeqc (@type o lib).
Proof.
  introv aeq inh.
  apply (alphaeqc_implies_ccequivc_ext lib) in aeq.
  apply type_respects_cequivc_left in aeq; auto.
  apply tequality_refl in aeq; auto.
Qed.
Hint Resolve type_respects_alphaeqc : respects.

Lemma reduces_toc_trans {o} :
  forall lib (a b c : @CTerm o),
    reduces_toc lib a b
    -> reduces_toc lib b c
    -> reduces_toc lib a c.
Proof.
  introv r1 r2.
  destruct_cterms.
  allunfold @reduces_toc; allsimpl.
  eapply reduces_to_trans; eauto.
Qed.

Definition reduces_toc_ext {o} lib (a b : @CTerm o) :=
  in_ext lib (fun lib => Cast (reduces_toc lib a b)).

Lemma reduces_toc_ext_implies_ccequivc_ext {o} :
  forall lib (t x : @CTerm o),
    reduces_toc_ext lib t x
    -> ccequivc_ext lib t x.
Proof.
  introv r ext; apply r in ext; clear r; spcast.
  destruct_cterms.
  unfold reduces_toc in *; simpl in *.
  spcast; unfold cequivc; simpl.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
Qed.

Lemma member_respects_reduces_toc_ext {o} :
  forall lib (t1 t2 T : @CTerm o),
  reduces_toc_ext lib t1 t2
  -> member lib t2 T
  -> member lib t1 T.
Proof.
  introv r m.
  apply reduces_toc_ext_implies_ccequivc_ext in r.
  apply ccequivc_ext_sym in r.
  eapply equality_respects_cequivc in r;[|exact m].
  apply equality_sym in r; apply equality_refl in r; auto.
Qed.

Lemma member_respects_cequivc {o} :
  forall lib (t1 t2 T : @CTerm o),
    ccequivc_ext lib t1 t2
    -> member lib t1 T
    -> member lib t2 T.
Proof.
  introv c m.
  eapply equality_respects_cequivc in c;[|exact m].
  apply equality_sym in c; apply equality_refl in c; auto.
Qed.

Lemma member_respects_cequivc_type {o} :
  forall lib (t T1 T2 : @CTerm o),
    ccequivc_ext lib T1 T2
    -> member lib t T1
    -> member lib t T2.
Proof.
  introv c m.
  eapply cequivc_preserving_equality; eauto.
Qed.

Lemma substcv_as_substc2 {o} :
  forall x (t : @CTerm o) v (u : CVTerm [x,v]),
    substcv [x] t v u = substc2 x t v u.
Proof.
  introv.
  destruct_cterms; simpl.
  apply cvterm_eq; simpl; auto.
Qed.

(* !!MOVE *)
Hint Resolve alphaeqc_trans : slow.
Hint Resolve alphaeqc_sym : slow.

Lemma respects_alphaeqc_alphaeqc {o} : respects2 alphaeqc (@alphaeqc o).
Proof.
  unfold respects2; dands; introv aeq1 aeq2; eauto 3 with slow.
Qed.
Hint Resolve respects_alphaeqc_alphaeqc : respects.

Lemma member_respects_alphaeqc_l {o} :
  forall lib (t1 t2 T : @CTerm o),
    alphaeqc t1 t2 -> member lib t1 T -> member lib t2 T.
Proof.
  introv aeq mem.
  allunfold @member.
  eapply equality_respects_alphaeqc_left;[exact aeq|].
  eapply equality_respects_alphaeqc_right;[exact aeq|].
  auto.
Qed.

Lemma member_respects_alphaeqc_r {o} :
  forall lib (t T1 T2 : @CTerm o),
    alphaeqc T1 T2 -> member lib t T1 -> member lib t T2.
Proof.
  introv aeq mem.
  allunfold @member.
  eapply alphaeqc_preserving_equality; eauto.
Qed.

Lemma respects_alphaeqc_member {o} :
  forall (lib : @library o), respects2 alphaeqc (member lib).
Proof.
  introv; unfold respects2; dands; introv aeq1 aeq2; eauto 3 with slow.
  - eapply member_respects_alphaeqc_l; eauto.
  - eapply member_respects_alphaeqc_r; eauto.
Qed.
Hint Resolve respects_alphaeqc_member : respects.

Lemma respects_alphaeqc_equorsq3 {o} :
  forall lib (t1 t2 T1 T2 : @CTerm o),
    alphaeqc T1 T2
    -> equorsq lib t1 t2 T1
    -> equorsq lib t1 t2 T2.
Proof.
  introv aeq e.
  eauto 3 with slow.
  pose proof (respects_alphaeqc_equorsq lib) as h.
  destruct h as [h1 h]; repnd.
  eapply h; eauto.
Qed.

Lemma respects_alphaeqc_cequivc {p} : forall lib, respects2 alphaeqc (@cequivc p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq; allsimpl;
  try (complete (left; eauto 3 with nequality)).
  - apply (cequivc_trans lib a' a b); auto; apply cequivc_sym; apply alphaeqc_implies_cequivc; auto.
  - apply (cequivc_trans lib a b b'); auto; apply alphaeqc_implies_cequivc; auto.
Qed.
Hint Resolve respects_alphaeqc_cequivc : respects.
