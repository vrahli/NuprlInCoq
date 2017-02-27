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


Require Export nuprl_props.
Require Export enuprl_type_sys.

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


Lemma enuprli_refl {p} :
  forall lib i t1 t2 eq,
    @enuprli p lib i t1 t2 eq -> enuprli lib i t1 t1 eq.
Proof.
  intros.
  generalize (@enuprli_type_system p lib i); intro nts.
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

Lemma eequality_eq_refl {p} :
  forall lib A B a b eq,
    @enuprl p lib A B eq
    -> eq a b
    -> eq a a.
Proof.
  introv n e; ents.
  eapply type_system_term_mem; eauto.
Qed.

Lemma eequality_eq_sym {p} :
  forall lib A B a b eq,
    @enuprl p lib A B eq
    -> eq a b
    -> eq b a.
Proof.
  sp; ents.
  apply nts_tes with (T := A) (T' := B); sp.
Qed.

Lemma eequality_eq_trans {p} :
  forall lib A B a b c eq,
    @enuprl p lib A B eq
    -> eq a b
    -> eq b c
    -> eq a c.
Proof.
  sp; ents.
  apply nts_tet with (T := A) (T' := B) (t2 := b); sp.
Qed.

Lemma eequality_sym {p} :
  forall lib t1 t2 T,
    @eequality p lib t1 t2 T -> eequality lib t2 t1 T.
Proof.
  unfold eequality; sp.
  exists eq; sp.
  eapply eequality_eq_sym; eauto.
Qed.
Hint Resolve eequality_sym : nequality.

Lemma eequality_trans {p} :
  forall lib t1 t2 t3 T,
    @eequality p lib t1 t2 T -> eequality lib t2 t3 T -> eequality lib t1 t3 T.
Proof.
  unfold eequality; introv e1 e2; exrepnd.
  apply enuprl_uniquely_valued with (eq1 := eq0) in e2; auto.
  exists eq0; auto.
  rw <- e2 in e0; sp.
  eapply eequality_eq_trans; eauto.
Qed.
Hint Resolve eequality_trans : nequality.

Lemma etequality_sym {p} :
  forall lib t1 t2,
    @etequality p lib t1 t2 -> etequality lib t2 t1.
Proof.
  unfold etequality; sp.
  exists eq.
  apply enuprl_sym; sp.
Qed.
Hint Resolve etequality_sym : nequality.

Lemma etequality_refl {p} :
  forall lib t1 t2,
    @etequality p lib t1 t2 -> etequality lib t1 t1.
Proof.
  unfold etequality; introv t; exrepnd.
  exists eq.
  apply enuprl_refl in t0; sp.
Qed.
Hint Resolve etequality_refl : nequality.

Lemma etequality_trans {p} :
  forall lib t1 t2 t3,
    @etequality p lib t1 t2 -> etequality lib t2 t3 -> etequality lib t1 t3.
Proof.
  unfold etequality; sp.
  exists eq0.
  eapply enuprl_trans; eauto.
Qed.
Hint Resolve etequality_trans : nequality.

Lemma emember_eq {p} :
  forall lib t T,
    @eequality p lib t t T = emember lib t T.
Proof.
  reflexivity.
Qed.

Lemma fold_etype {p} :
  forall lib T,
    @etequality p lib T T = etype lib T.
Proof.
  reflexivity.
Qed.

Lemma fold_eequorsq {p} :
  forall lib t1 t2 T,
    (@eequality p lib t1 t2 T {+} ccequivc lib t1 t2) = eequorsq lib t1 t2 T.
Proof. sp. Qed.

Lemma fold_eequorsq2 {p} :
  forall lib t1 t2 t3 t4 T,
    (@eequorsq p lib t1 t2 T # eequorsq lib t3 t4 T) = eequorsq2 lib t1 t2 t3 t4 T.
Proof. sp. Qed.

Lemma eequality_refl {p} :
  forall lib t1 t2 T,
    @eequality p lib t1 t2 T -> emember lib t1 T.
Proof.
  unfold emember, eequality; sp.
  exists eq; sp.
  eapply eequality_eq_refl; eauto.
Qed.
Hint Resolve eequality_refl : nequality.

Lemma etequality_iff_enuprl {p} :
  forall lib a b,
    {eq : per(p) , enuprl lib a b eq} <=> etequality lib a b.
Proof.
  sp.
Qed.

Lemma etequality_if_enuprl {p} :
  forall lib a b eq,
    @enuprl p lib a b eq -> etequality lib a b.
Proof.
  sp.
  apply etequality_iff_enuprl; exists eq; sp.
Qed.

Lemma eequality_eq {p} :
  forall lib A a b eq,
    @enuprl p lib A A eq
    -> (eq a b <=> eequality lib a b A).
Proof.
  sp; split; intro k.
  unfold eequality; exists eq; sp.
  unfold eequality in k; sp.
  assert (eq_term_equals eq eq0) as eqt.
  { eapply enuprl_uniquely_valued with (t := A); eauto. }
  unfold eq_term_equals in eqt.
  apply eqt; sp.
Qed.

Lemma eequality_eq1 {p} :
  forall lib A B a b eq,
    @enuprl p lib A B eq
    -> (eq a b <=> eequality lib a b A).
Proof.
  introv n; split; intro k.
  unfold eequality; exists eq; sp.
  { apply enuprl_refl in n; sp. }
  unfold eequality in k; sp.
  assert (eq_term_equals eq eq0) as eqt.
  { eapply enuprl_uniquely_valued with (t := A); eauto.
    apply enuprl_refl in n; sp. }
  unfold eq_term_equals in eqt.
  apply eqt; sp.
Qed.

Lemma eeqorceq_commutes_eequality {p} :
  forall lib a b c d eq A B,
    @enuprl p lib A B eq
    -> eqorceq lib eq a b
    -> eqorceq lib eq c d
    -> (eequality lib a c A <=> eequality lib b d B).
Proof.
  introv n eos1 eos2.
  applydup @enuprl_sym  in n  as n0.
  applydup @enuprl_refl in n0 as n1.
  applydup @enuprl_refl in n  as n2.
  rw <- (eequality_eq1 lib A B a c eq n).
  rw <- (eequality_eq1 lib B A b d eq n0).
  ents.
  split; sp.
  { apply (eqorceq_commutes lib) with (a := a) (c := c); auto.
    - apply nts_tev with (T := A); auto.
    - apply nts_tes with (T := A) (T' := A); auto.
    - apply nts_tet with (T := A) (T' := A); auto. }
  { apply (eqorceq_commutes lib) with (a := b) (c := d); auto.
    - apply nts_tev with (T := A); auto.
    - apply nts_tes with (T := A) (T' := A); auto.
    - apply nts_tet with (T := A) (T' := A); auto.
    - apply eqorceq_sym; auto.
      apply nts_tes with (T := A) (T' := A); auto.
    - apply eqorceq_sym; auto.
      apply nts_tes with (T := A) (T' := A); auto. }
Qed.

Lemma eq_eequality1 {p} :
  forall lib a b A (eq : per(p)),
    eq a b
    -> enuprl lib A A eq
    -> eequality lib a b A.
Proof.
  introv e n.
  unfold eequality.
  exists eq; sp.
Defined.

Lemma eq_eequality2 {p} :
  forall lib a b A B (eq : per(p)),
    eq a b
    -> enuprl lib A B eq
    -> eequality lib a b A.
Proof.
  introv e n.
  unfold eequality.
  exists eq; sp.
  apply enuprl_refl in n; sp.
Defined.

Lemma eq_eequality3 {p} :
  forall lib a b A B (eq : per(p)) i,
    eq a b
    -> enuprli lib i A B eq
    -> eequality lib a b A.
Proof.
  introv e n.
  exists eq; sp.
  apply enuprli_implies_enuprl in n; sp.
  apply enuprl_refl in n; sp.
Qed.

Lemma eequality_respects_cequivc {p} :
  forall lib t1 t2 T,
    @cequivc p lib t1 t2
    -> emember lib t1 T
    -> eequality lib t1 t2 T.
Proof.
  unfold emember, eequality; sp.
  exists eq; sp.
  ents.
  apply nts_tev with (T := T); sp; spcast; sp.
Qed.
Hint Resolve eequality_respects_cequivc : nequality.

Lemma eequality_respects_alphaeqc {p} :
  forall lib t1 t2 T,
    @alphaeqc p t1 t2
    -> emember lib t1 T
    -> eequality lib t1 t2 T.
Proof.
  unfold emember, eequality; introv a m; exrepnd.
  exists eq; sp.
  ents.
  apply nts_tev with (T := T); sp; spcast.
  apply alphaeqc_implies_cequivc; sp.
Qed.
Hint Resolve eequality_respects_alphaeqc : nequality.

Lemma eequality_respects_cequivc_left {p} :
  forall lib t1 t2 t T,
    @cequivc p lib t1 t
    -> eequality lib t1 t2 T
    -> eequality lib t t2 T.
Proof.
  sp.
  apply @eequality_trans with (t2 := t1); sp.
  apply eequality_sym.
  apply eequality_respects_cequivc; sp.
  allapply @eequality_refl; sp.
Qed.
Hint Resolve eequality_respects_cequivc_left : nequality.

Lemma eequality_respects_cequivc_right {p} :
  forall lib t1 t2 t T,
    @cequivc p lib t2 t
    -> eequality lib t1 t2 T
    -> eequality lib t1 t T.
Proof.
  introv c e.
  apply @eequality_trans with (t2 := t2); sp.
  apply eequality_respects_cequivc; sp.
  apply eequality_sym in e.
  allapply @eequality_refl; sp.
Qed.
Hint Resolve eequality_respects_cequivc_right : nequality.

Lemma eequality_respects_alphaeqc_left {p} :
  forall lib t1 t2 t T,
    @alphaeqc p t1 t
    -> eequality lib t1 t2 T
    -> eequality lib t t2 T.
Proof.
  sp.
  apply @eequality_trans with (t2 := t1); sp.
  apply eequality_sym.
  apply eequality_respects_cequivc; sp.
  apply alphaeqc_implies_cequivc; sp.
  allapply @eequality_refl; sp.
Qed.
Hint Resolve eequality_respects_alphaeqc_left : nequality.

Lemma eequality_respects_alphaeqc_right {p} :
  forall lib t1 t2 t T,
    @alphaeqc p t2 t
    -> eequality lib t1 t2 T
    -> eequality lib t1 t T.
Proof.
  introv a e.
  apply @eequality_trans with (t2 := t2); sp.
  apply eequality_respects_cequivc; sp.
  apply alphaeqc_implies_cequivc; sp.
  apply eequality_sym in e.
  allapply @eequality_refl; sp.
Qed.
Hint Resolve eequality_respects_alphaeqc_right : nequality.

Lemma etequality_respects_cequivc_left {p} :
  forall lib T1 T2 T3,
    @cequivc p lib T1 T3
    -> etequality lib T1 T2
    -> etequality lib T3 T2.
Proof.
  unfold etequality; sp.
  exists eq.
  apply enuprl_value_respecting_left with (t1 := T1); auto.
Qed.
Hint Resolve etequality_respects_cequivc_left : nequality.

Lemma etequality_respects_cequivc_right {p} :
  forall lib T1 T2 T3,
    @cequivc p lib T2 T3
    -> etequality lib T1 T2
    -> etequality lib T1 T3.
Proof.
  unfold etequality; sp.
  exists eq.
  apply enuprl_value_respecting_right with (t2 := T2); auto.
Qed.
Hint Resolve etequality_respects_cequivc_right : nequality.

Lemma etequality_respects_alphaeqc_left {p} :
  forall lib T1 T2 T3,
    @alphaeqc p T1 T3
    -> etequality lib T1 T2
    -> etequality lib T3 T2.
Proof.
  unfold etequality; sp.
  exists eq.
  apply enuprl_value_respecting_left with (t1 := T1); auto.
  apply alphaeqc_implies_cequivc; sp.
Qed.
Hint Resolve etequality_respects_alphaeqc_left : nequality.

Lemma etequality_respects_alphaeqc_right {p} :
  forall lib T1 T2 T3,
    @alphaeqc p T2 T3
    -> etequality lib T1 T2
    -> etequality lib T1 T3.
Proof.
  unfold etequality; sp.
  exists eq.
  apply enuprl_value_respecting_right with (t2 := T2); auto.
  apply alphaeqc_implies_cequivc; sp.
Qed.
Hint Resolve etequality_respects_alphaeqc_right : nequality.

Lemma etype_respects_cequivc_left {p} :
  forall lib T T',
    @cequivc p lib T T'
    -> etype lib T
    -> etequality lib T' T.
Proof.
  unfold etype; sp.
  apply etequality_respects_cequivc_left with (T1 := T); auto.
Qed.
Hint Resolve etype_respects_cequivc_left : nequality.

Lemma etype_respects_cequivc_right {p} :
  forall lib T T',
    @cequivc p lib T T'
    -> etype lib T
    -> etequality lib T T'.
Proof.
  unfold etype; sp.
  apply etequality_respects_cequivc_right with (T2 := T); auto.
Qed.
Hint Resolve etype_respects_cequivc_right : nequality.

Lemma etype_respects_alphaeqc_left {p} :
  forall lib T T',
    @alphaeqc p T T'
    -> etype lib T
    -> etequality lib T' T.
Proof.
  unfold etype; sp.
  apply etequality_respects_alphaeqc_left with (T1 := T); auto.
Qed.

Lemma etype_respects_alphaeqc_right {p} :
  forall lib T T',
    @alphaeqc p T T'
    -> etype lib T
    -> etequality lib T T'.
Proof.
  unfold etype; sp.
  apply etequality_respects_alphaeqc_right with (T2 := T); auto.
Qed.

Lemma cequivc_preserving_eequality {p} :
  forall lib a b A B,
    @eequality p lib a b A
    -> cequivc lib A B
    -> eequality lib a b B.
Proof.
  unfold eequality; introv e c; exrepnd.
  ents.
  unfold type_value_respecting in nts_tyv.
  apply nts_tyv with (eq := eq) in c; sp.
  exists eq; sp.
  generalize (type_system_type_mem2 (enuprl lib) A B eq); sp.
Qed.

Lemma alphaeqc_preserving_eequality {p} :
  forall lib a b A B,
    @eequality p lib a b A
    -> alphaeqc A B
    -> eequality lib a b B.
Proof.
  unfold eequality; introv e al; exrepnd.
  ents.
  unfold type_value_respecting in nts_tyv.
  apply (alphaeqc_implies_cequivc lib) in al.
  apply nts_tyv with (eq := eq) in al; sp.
  exists eq; sp.
  generalize (type_system_type_mem2 (enuprl lib) A B eq); sp.
Qed.
Hint Resolve alphaeqc_preserving_eequality : nequality.

Lemma etequality_preserving_eequality {p} :
  forall lib a b A B,
    @eequality p lib a b A
    -> etequality lib A B
    -> eequality lib a b B.
Proof.
  unfold etequality, eequality; introv e t; exrepnd.
  ents.
  assert (enuprl lib A A eq # enuprl lib B B eq) as n; repd.
  apply type_system_type_mem2; sp.
  exists eq; sp.
  assert (eq_term_equals eq0 eq) as eqt.
  apply uniquely_valued_eq with (ts := enuprl lib) (T := A) (T1 := A) (T2 := A); sp.
  apply eqt; sp.
Qed.
Hint Resolve etequality_preserving_eequality : nequality.

Lemma etequalityi_refl {p} :
  forall lib l T1 T2, @etequalityi p lib l T1 T2 -> etequalityi lib l T1 T1.
Proof.
  unfold etequalityi; sp.
  allapply @eequality_refl; sp.
Qed.

Lemma eeqtypes_refl {p} :
  forall lib l T1 T2, @eeqtypes p lib l T1 T2 -> eeqtypes lib l T1 T1.
Proof.
  destruct l; simpl; sp.
  allapply @etequality_refl; sp.
  allapply @etequalityi_refl; sp.
Qed.

Lemma etequalityi_preserving_eequality {p} :
  forall lib i a b A B,
    @eequality p lib a b A
    -> etequalityi lib i A B
    -> eequality lib a b B.
Proof.
  unfold etequalityi, eequality; introv e teq; exrepnd.
  inversion teq1; try not_univ.
  duniv j h.
  allrw @eunivi_exists_iff; exrepd.
  computes_to_value_isvalue.
  exists eq0; dands; auto.
  apply e in teq0; clear e.
  unfold eunivi_eq in teq0; exrepnd.
  allfold (@enuprli p lib j0).
  allapply @enuprli_implies_enuprl.
  ents.

  pose proof (nts_uv A A eqa eq0) as q1; repeat (autodimp q1 hyp).
  eapply nts_ext;[|eauto].
  eapply nts_ext;[|apply eq_term_equals_sym;exact teq0].
  auto.
Qed.

Lemma eeqtypes_preserving_eequality {p} :
  forall lib l a b A B,
    @eequality p lib a b A
    -> eeqtypes lib l A B
    -> eequality lib a b B.
Proof.
  destruct l; introv eq eqt.
  apply @etequality_preserving_eequality with (A := A); sp.
  apply @etequalityi_preserving_eequality with (A := A) (i := n); sp.
Qed.

Lemma etequalityi_sym {p} :
  forall lib i T1 T2, @etequalityi p lib i T1 T2 -> etequalityi lib i T2 T1.
Proof.
  unfold etequalityi; introv teq.
  apply eequality_sym; sp.
Qed.

Lemma eeqtypes_sym {p} :
  forall lib l T1 T2, @eeqtypes p lib l T1 T2 -> eeqtypes lib l T2 T1.
Proof.
  destruct l; introv eqt.
  apply etequality_sym; sp.
  apply etequalityi_sym; sp.
Qed.

Lemma etequalityi_trans {p} :
  forall lib i t1 t2 t3,
    @etequalityi p lib i t1 t2
    -> etequalityi lib i t2 t3
    -> etequalityi lib i t1 t3.
Proof.
  unfold etequalityi; introv teq1 teq2.
  apply @eequality_trans with (t2 := t2); sp.
Qed.

Lemma eeqtypes_trans {p} :
  forall lib l t1 t2 t3,
    @eeqtypes p lib l t1 t2
    -> eeqtypes lib l t2 t3
    -> eeqtypes lib l t1 t3.
Proof.
  destruct l; introv teq1 teq2.
  apply @etequality_trans with (t2 := t2); sp.
  apply @etequalityi_trans with (t2 := t2); sp.
Qed.

Lemma eequality3_implies_eequorsq2 {p} :
  forall lib a b c d T,
    @eequality p lib a c T
    -> eequality lib b d T
    -> eequality lib a b T
    -> eequorsq2 lib a b c d T.
Proof.
  introv e1 e2 e3.
  unfold eequorsq2, eequorsq; dands; auto.
  left.
  apply eequality_trans with (t2 := b); auto.
  apply eequality_trans with (t2 := a); auto.
  apply eequality_sym; auto.
Qed.

Lemma inhabited_implies_etequality {p} :
  forall lib t1 t2 T,
    @eequality p lib t1 t2 T -> etype lib T.
Proof.
  unfold eequality, etype, etequality; introv eq; exrepnd.
  exists eq0; sp.
Qed.

Hint Resolve etequality_preserving_eequality cequivc_preserving_eequality : nequality.

Lemma cequivc_eequality {p} : forall lib, respects3 (cequivc lib) (@eequality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq; eauto 3 with nequality.
Qed.
Hint Resolve cequivc_eequality : respects.

Lemma eequorsq2_prop {p} :
  forall lib A a1 a2 b1 b2,
    @eequorsq2 p lib a1 b1 a2 b2 A
    -> eequality lib a1 a2 A
    -> eequality lib a1 b2 A.
Proof.
  introv ceq e1.
  unfold eequorsq2, eequorsq in ceq; repnd; repdors; spcast.

  apply eequality_trans with (t2 := a2); sp.

  apply eequality_trans with (t2 := a2); sp.

  apply eequality_trans with (t2 := a2); sp.
  apply cequivc_sym in ceq.
  rwg ceq.
  apply eequality_sym in e1; apply eequality_refl in e1; auto.

  apply eequality_trans with (t2 := a2); sp.
  apply cequivc_sym in ceq.
  rwg ceq.
  apply eequality_sym in e1; apply eequality_refl in e1; auto.
Qed.

Lemma eequorsq_eequality_trans1 {p} :
  forall lib t1 t2 t3 T,
    @eequorsq p lib t1 t2 T
    -> eequality lib t2 t3 T
    -> eequality lib t1 t3 T.
Proof.
  introv c e.
  unfold eequorsq in c; sp.
  { apply @eequality_trans with (t2 := t2); sp. }
  spcast; apply @eequality_respects_cequivc_left with (t1 := t2); sp.
  apply cequivc_sym; sp.
Qed.

Lemma eequorsq_eequality_trans2 {p} :
  forall lib t1 t2 t3 T,
    @eequality p lib t1 t2 T
    -> eequorsq lib t2 t3 T
    -> eequality lib t1 t3 T.
Proof.
  introv e c.
  unfold eequorsq in c; sp.
  { apply @eequality_trans with (t2 := t2); sp. }
  spcast; apply @eequality_respects_cequivc_right with (t2 := t2); sp.
Qed.

Lemma eequorsq_sym {p} :
  forall lib a b T, @eequorsq p lib a b T -> eequorsq lib b a T.
Proof.
  unfold eequorsq; introv ceq; sp.
  { left; apply eequality_sym; sp. }
  right; spcast; sp; apply cequivc_sym; sp.
Qed.


Lemma respects_alphaeqc_eequality {p} :
  forall lib, respects3 alphaeqc (@eequality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.
Hint Resolve respects_alphaeqc_eequality : respects.

Lemma respects_alphaeqc_etequality {p} :
  forall lib, respects2 alphaeqc (@etequality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.
Hint Resolve respects_alphaeqc_etequality : respects.

Lemma respects_cequivc_etequality {p} :
  forall lib, respects2 (cequivc lib) (@etequality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.
Hint Resolve respects_cequivc_etequality : respects.

Lemma respects_cequivc_eequality {p} :
  forall lib, respects3 (cequivc lib) (@eequality p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq;
  eauto 3 with nequality.
Qed.
Hint Resolve respects_cequivc_eequality : respects.

Lemma enuprli_sym {p} :
  forall lib i t1 t2 eq,
    @enuprli p lib i t1 t2 eq -> enuprli lib i t2 t1 eq.
Proof.
  intros.
  generalize (@enuprli_type_system p lib i); intro nts.
  dest_ts nts.
  apply ts_tys; sp.
Qed.

Lemma enuprl_ext {p} :
  forall lib t1 t2 eq1 eq2,
    @enuprl p lib t1 t2 eq1
    -> eq_term_equals eq1 eq2
    -> enuprl lib t1 t2 eq2.
Proof.
  introv n1 eqs; ents.
  apply nts_ext with (eq := eq1); sp.
Qed.

Lemma enuprli_ext {p} :
  forall lib i t1 t2 eq1 eq2,
    @enuprli p lib i t1 t2 eq1
    -> eq1 <=2=> eq2
    -> enuprli lib i t1 t2 eq2.
Proof.
  introv n1 eqs.
  generalize (@enuprli_type_system p lib i); intro nts.
  dest_ts nts.
  apply ts_ext with (eq := eq1); sp.
Qed.

Lemma eqorceq_iff_eequorsq {o} :
  forall lib (A B a b : @CTerm o) eq,
    enuprl lib A B eq
    -> (eqorceq lib eq a b <=> eequorsq lib a b A).
Proof.
  introv n.
  unfold eqorceq, eequorsq.
  split; intro k; dorn k; auto; left; apply enuprl_refl in n; auto.
  - exists eq; dands; auto.
  - pose proof (eequality_eq lib A a b eq n) as h; apply h; auto.
Qed.

Lemma eequorsq_etequality {o} :
  forall lib (A B a b : @CTerm o),
    eequorsq lib a b A
    -> etequality lib A B
    -> eequorsq lib a b B.
Proof.
  introv e t.
  allunfold @eequorsq.
  dorn e; auto.
  left.
  eapply etequality_preserving_eequality; eauto.
Qed.


Lemma respects_cequivc_eequorsq {p} :
  forall lib, respects3 (cequivc lib) (@eequorsq p lib).
Proof.
  unfold eequorsq; introv; unfolds_base; dands; introv Hr Heq; allsimpl; dorn Heq;
    try (complete (left; eauto 3 with nequality));
    right; spcast; eauto 3 with nequality.
  - apply (cequivc_trans lib a' a b); auto; apply cequivc_sym; auto.
  - apply (cequivc_trans lib a b b'); auto; apply cequivc_sym; auto.
Qed.
Hint Resolve respects_cequivc_eequorsq : respects.

Lemma respects_alphaeqc_eequorsq {p} :
  forall lib, respects3 alphaeqc (@eequorsq p lib).
Proof.
  unfold eequorsq; introv; unfolds_base; dands; introv Hr Heq; allsimpl; dorn Heq;
    try (complete (left; eauto 3 with nequality));
    right; spcast; eauto 3 with nequality.
  - apply (cequivc_trans lib a' a b); auto; apply cequivc_sym; apply alphaeqc_implies_cequivc; auto.
  - apply (cequivc_trans lib a b b'); auto; apply alphaeqc_implies_cequivc; auto.
Qed.
Hint Resolve respects_alphaeqc_eequorsq : respects.


Lemma equorsq_sym {o} :
  forall lib (A a b : @CTerm o),
    eequorsq lib a b A -> eequorsq lib b a A.
Proof.
  introv e.
  allunfold @eequorsq; sp.
  { left; apply eequality_sym; auto. }
  right; spcast; sp; apply cequivc_sym; sp.
Qed.
