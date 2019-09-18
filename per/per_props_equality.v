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


Require Export per_props_tacs.
Require Export per_props_cequiv.
Require Export per_props_function.
Require Export per_props_uni.
Require Export per_props_util2.


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

Lemma member_equality {o} :
  forall lib (t1 t2 T : @CTerm o),
    equality lib t1 t2 T
    -> member lib mkc_axiom (mkc_equality t1 t2 T).
Proof.
  introv h.
  assert (forall lib' (x : lib_extends lib' lib), equality lib' t1 t2 T) as q by eauto 3 with slow.
  clear h.
  apply choice_ext_lib_eq in q; exrepnd.

  exists (eq_per_eq_bar lib t1 t2 eqa).
  dands; auto.

  {
    apply CL_eq.
    exists T T t1 t2 t1 t2 eqa.
    dands; spcast; eauto 3 with slow.
    introv; apply q0.
  }

  {
    unfold eq_per_eq_bar; apply e_all_in_ex_bar_ext_as.
    apply in_ext_ext_implies_in_open_bar_ext; introv; simpl.
    introv; unfold eq_per_eq; dands; spcast; eauto 3 with slow refl; try apply q0.
  }
Qed.

(* end hide *)

Lemma type_extensionality_per_eq_nuprl {o} :
  @type_extensionality o (per_eq nuprl).
Proof.
  introv per e.
  unfold per_eq in *; exrepnd.
  exists A B a1 a2 b1 b2 eqa; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_eq_nuprl : slow.

Lemma type_extensionality_per_eq_nuprli {o} :
  forall i, @type_extensionality o (per_eq (nuprli i)).
Proof.
  introv per e.
  unfold per_eq in *; exrepnd.
  exists A B a1 a2 b1 b2 eqa; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_per_eq_nuprli : slow.

Lemma ccequivc_ext_implies_eq_per_eq_bar {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o) (eqa eqb : lib-per(lib, o)),
    in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> ccequivc_ext lib a1 a2
    -> ccequivc_ext lib b1 b2
    -> (eq_per_eq_bar lib a1 b1 eqa) <=2=> (eq_per_eq_bar lib a2 b2 eqb).
Proof.
  introv resp sym trans alla ceqa ceqb; introv.
  unfold eq_per_eq_bar, eq_per_eq; split; introv h;
    apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as;
      eapply in_open_bar_ext_pres; try exact h; clear h; introv h;
        repnd; dands; auto.

  - apply alla.

    assert (eqa lib' e a1 a2) as w.
    { apply resp; eauto 3 with slow.
      eapply trans;[eauto|].
      apply sym; auto. }

    assert (eqa lib' e b1 b2) as z.
    { apply resp; eauto 3 with slow.
      eapply trans;[|eauto].
      apply sym; auto. }

    eapply trans;[apply sym;eauto|].
    eapply trans;[exact h|]; auto.

  - apply alla in h.

    assert (eqa lib' e a1 a2) as w.
    { apply sym; apply resp; eauto 3 with slow.
      eapply trans;[eauto|].
      apply sym; auto. }

    assert (eqa lib' e b1 b2) as z.
    { apply sym; apply resp; eauto 3 with slow.
      eapply trans;[|eauto].
      apply sym; auto. }

    eapply trans;[exact w|].
    eapply trans;[exact h|].
    apply sym; auto.
Qed.

Lemma uniquely_valued_per_eq_nuprl {o} :
  @uniquely_valued o (per_eq nuprl).
Proof.
  introv pera perb.
  unfold per_eq in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq.
  apply ccequivc_ext_mkc_equality_implies in ceq0.
  repnd.

  eapply in_ext_ext_nuprl_value_respecting_left  in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprl_value_respecting_right in pera3;[|apply ccequivc_ext_sym;eauto].

  apply ccequivc_ext_implies_eq_per_eq_bar; eauto 2 with slow.

  introv.
  pose proof (pera3 _ e) as pera3.
  pose proof (perb3 _ e) as perb3.
  simpl in *.
  apply nuprl_refl in pera3.
  apply nuprl_refl in perb3.
  eapply nuprl_uniquely_valued; eauto.
Qed.
Hint Resolve uniquely_valued_per_eq_nuprl : slow.

Lemma uniquely_valued_per_eq_nuprli {o} :
  forall i, @uniquely_valued o (per_eq (nuprli i)).
Proof.
  introv pera perb.
  unfold per_eq in *; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq.
  apply ccequivc_ext_mkc_equality_implies in ceq0.
  repnd.

  eapply in_ext_ext_nuprli_value_respecting_left  in pera3;[|apply ccequivc_ext_sym;eauto].
  eapply in_ext_ext_nuprli_value_respecting_right in pera3;[|apply ccequivc_ext_sym;eauto].

  apply ccequivc_ext_implies_eq_per_eq_bar; eauto 2 with slow.

  introv.
  pose proof (pera3 _ e) as pera3.
  pose proof (perb3 _ e) as perb3.
  simpl in *.
  apply nuprli_refl in pera3.
  apply nuprli_refl in perb3.
  eapply nuprli_uniquely_valued; eauto.
Qed.
Hint Resolve uniquely_valued_per_eq_nuprli : slow.

Lemma local_per_bar_per_eq_nuprl {o} :
  @local_ts o (per_bar (per_eq nuprl)).
Proof.
  apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_eq_nuprl : slow.

Lemma local_per_bar_per_eq_nuprli {o} :
  forall i, @local_ts o (per_bar (per_eq (nuprli i))).
Proof.
  introv; apply local_per_bar; eauto 3 with slow.
Qed.
Hint Resolve local_per_bar_per_eq_nuprli : slow.

Lemma dest_nuprl_per_eq_l {o} :
  forall (ts : cts(o)) lib T a1 a2 A T' eq,
    ts = univ
    -> ccomputes_to_valc_ext lib T (mkc_equality a1 a2 A)
    -> close ts lib T T' eq
    -> per_bar (per_eq (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_eq_nuprl; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprli_per_eq_l {o} :
  forall i (ts : cts(o)) lib T a1 a2 A T' eq,
    ts = univi_bar i
    -> ccomputes_to_valc_ext lib T (mkc_equality a1 a2 A)
    -> close ts lib T T' eq
    -> per_bar (per_eq (close ts)) lib T T' eq.
Proof.
  introv equ comp cl.
  assert (type_system ts) as sys by (subst; eauto 3 with slow).
  assert (defines_only_universes ts) as dou by (subst; eauto 3 with slow).
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_eq_nuprli; eauto.
  eapply in_open_bar_ext_pres; try exact reca; clear reca; introv reca.
  eapply reca; eauto 3 with slow.
Qed.

Lemma dest_nuprl_equality {o} :
  forall (lib : @library o) a1 a2 A b1 b2 B eq,
    nuprl lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) eq
    -> per_bar (per_eq nuprl) lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) eq.
Proof.
  introv cl.
  unfold nuprl in cl.
  eapply dest_nuprl_per_eq_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprli_equality {o} :
  forall i (lib : @library o) a1 a2 A b1 b2 B eq,
    nuprli i lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) eq
    -> per_bar (per_eq (nuprli i)) lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) eq.
Proof.
  introv cl.
  unfold nuprli in cl.
  eapply dest_nuprli_per_eq_l in cl; auto;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprl_equality2 {o} :
  forall lib (eq : per(o)) a1 a2 A b1 b2 B,
    nuprl lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) eq
    ->
    exists (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq lib (eq_per_eq_bar_lib_per lib a1 a2 eqa)))
        # in_open_bar_ext lib (fun lib' x => nuprl lib' A B (eqa lib' x))
        # in_open_bar_ext lib (fun lib' x => eqorceq lib' (eqa lib' x) a1 b1)
        # in_open_bar_ext lib (fun lib' x => eqorceq lib' (eqa lib' x) a2 b2).
Proof.
  introv u.
  apply dest_nuprl_equality in u.
  unfold per_bar in u; exrepnd.

  assert (in_open_bar_ext
            lib
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprl lib'' A B (eqa0 lib'' y))
               # eqorceq_ext lib' eqa0 a1 b1
               # eqorceq_ext lib' eqa0 a2 b2
               # (eqa lib' x) <=2=> (eq_per_eq_bar lib' a1 a2 eqa0) })) as e.
  {
    eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
    unfold per_eq in *; exrepnd.
    repeat ccomputes_to_valc_ext_val.
    eapply in_ext_ext_nuprl_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprl_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].
    eapply eqorceq_ext_ccequivc_ext_trans_left  in u5; eauto; eauto 3 with slow;[].
    eapply eqorceq_ext_ccequivc_ext_trans_right in u5; try apply ccequivc_ext_sym; eauto; eauto 3 with slow;[].
    eapply eqorceq_ext_ccequivc_ext_trans_left  in u6; eauto; eauto 3 with slow;[].
    eapply eqorceq_ext_ccequivc_ext_trans_right in u6; try apply ccequivc_ext_sym; eauto; eauto 3 with slow;[].
    exists eqa0; dands; auto; eauto 2 with slow.
    eapply eq_term_equals_trans;[eauto|].
    eapply ccequivc_ext_implies_eq_per_eq_bar; eauto 3 with slow.
  }
  clear u1.

  apply in_open_bar_ext_choice in e; exrepnd.
  apply in_open_bar_eqa_choice in e0; exrepnd.

  exists (fun_lib_dep_eqa Feqa).
  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq; simpl.
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd.
    eapply eq_term_equals_trans;[eauto|]; simpl.
    apply simple_implies_iff_per_eq_eq; simpl in *.
    apply in_ext_ext_implies_in_open_bar_ext; introv.
    introv; simpl; unfold raise_ext_per; split; intro q.

    { exists lib' e lib'0 e0 z e2; auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e3 _ z0) as e3; simpl in *.
    pose proof (h0 _ e2) as h0; simpl in *.
    apply nuprl_refl in h0; apply nuprl_refl in e3.
    eapply nuprl_uniquely_valued in h0; try exact e3; apply h0; auto.
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd; simpl.
    pose proof (h0 _ (lib_extends_refl _)) as h0; simpl in *.
    eapply type_extensionality_nuprl;[eauto|].
    introv; split; intro q.

    { exists lib' e lib'0 e0 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e2 _ z0) as e2; simpl in *.
    apply nuprl_refl in h0; apply nuprl_refl in e2.
    eapply nuprl_uniquely_valued in h0; try exact e2; apply h0; auto.
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd; simpl.
    pose proof (h0 _ (lib_extends_refl _)) as h0; simpl in *.
    pose proof (h1 _ (lib_extends_refl _)) as h1; simpl in *.
    eapply eqorceq_eq_term_equals; eauto.
    apply eq_term_equals_sym.
    introv; split; intro q.

    { exists lib' e lib'0 e0 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e2 _ z0) as e2; simpl in *.
    apply nuprl_refl in h0; apply nuprl_refl in e2.
    eapply nuprl_uniquely_valued in h0; try exact e2; apply h0; auto.
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd; simpl.
    pose proof (h0 _ (lib_extends_refl _)) as h0; simpl in *.
    pose proof (h2 _ (lib_extends_refl _)) as h2; simpl in *.
    eapply eqorceq_eq_term_equals; eauto.
    apply eq_term_equals_sym.
    introv; split; intro q.

    { exists lib' e lib'0 e0 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e2 _ z0) as e2; simpl in *.
    apply nuprl_refl in h0; apply nuprl_refl in e2.
    eapply nuprl_uniquely_valued in h0; try exact e2; apply h0; auto.
  }
Qed.

Lemma dest_nuprli_equality2 {o} :
  forall i lib (eq : per(o)) a1 a2 A b1 b2 B,
    nuprli i lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) eq
    ->
    exists (eqa : lib-per(lib,o)),
      (eq <=2=> (per_bar_eq lib (eq_per_eq_bar_lib_per lib a1 a2 eqa)))
        # in_open_bar_ext lib (fun lib' x => nuprli i lib' A B (eqa lib' x))
        # in_open_bar_ext lib (fun lib' x => eqorceq lib' (eqa lib' x) a1 b1)
        # in_open_bar_ext lib (fun lib' x => eqorceq lib' (eqa lib' x) a2 b2).
Proof.
  introv u.
  apply dest_nuprli_equality in u.
  unfold per_bar in u; exrepnd.

  assert (in_open_bar_ext
            lib
            (fun lib' x =>
               {eqa0 : lib-per(lib',o)
               , in_ext_ext lib' (fun lib'' y => nuprli i lib'' A B (eqa0 lib'' y))
               # eqorceq_ext lib' eqa0 a1 b1
               # eqorceq_ext lib' eqa0 a2 b2
               # (eqa lib' x) <=2=> (eq_per_eq_bar lib' a1 a2 eqa0) })) as e.
  {
    eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
    unfold per_eq in *; exrepnd.
    repeat ccomputes_to_valc_ext_val.
    eapply in_ext_ext_nuprli_value_respecting_left  in u4;[|apply ccequivc_ext_sym;eauto].
    eapply in_ext_ext_nuprli_value_respecting_right in u4;[|apply ccequivc_ext_sym;eauto].
    eapply eqorceq_ext_ccequivc_ext_trans_left  in u5; eauto; eauto 3 with slow;[].
    eapply eqorceq_ext_ccequivc_ext_trans_right in u5; try apply ccequivc_ext_sym; eauto; eauto 3 with slow;[].
    eapply eqorceq_ext_ccequivc_ext_trans_left  in u6; eauto; eauto 3 with slow;[].
    eapply eqorceq_ext_ccequivc_ext_trans_right in u6; try apply ccequivc_ext_sym; eauto; eauto 3 with slow;[].
    exists eqa0; dands; auto; eauto 2 with slow.
    eapply eq_term_equals_trans;[eauto|].
    eapply ccequivc_ext_implies_eq_per_eq_bar; eauto 3 with slow.
  }
  clear u1.

  apply in_open_bar_ext_choice in e; exrepnd.
  apply in_open_bar_eqa_choice in e0; exrepnd.

  exists (fun_lib_dep_eqa Feqa).
  dands.

  {
    eapply eq_term_equals_trans;[eauto|].
    clear dependent eq.

    apply implies_eq_term_equals_per_bar_eq; simpl.
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd.
    eapply eq_term_equals_trans;[eauto|]; simpl.
    apply simple_implies_iff_per_eq_eq; simpl in *.
    apply in_ext_ext_implies_in_open_bar_ext; introv.
    introv; simpl; unfold raise_ext_per; split; intro q.

    { exists lib' e lib'0 e0 z e2; auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e3 _ z0) as e3; simpl in *.
    pose proof (h0 _ e2) as h0; simpl in *.
    apply nuprli_refl in h0; apply nuprli_refl in e3.
    eapply nuprli_uniquely_valued in h0; try exact e3; apply h0; auto.
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd; simpl.
    pose proof (h0 _ (lib_extends_refl _)) as h0; simpl in *.
    eapply nuprli_type_extensionality;[eauto|].
    introv; split; intro q.

    { exists lib' e lib'0 e0 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e2 _ z0) as e2; simpl in *.
    apply nuprli_refl in h0; apply nuprli_refl in e2.
    eapply nuprli_uniquely_valued in h0; try exact e2; apply h0; auto.
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd; simpl.
    pose proof (h0 _ (lib_extends_refl _)) as h0; simpl in *.
    pose proof (h1 _ (lib_extends_refl _)) as h1; simpl in *.
    eapply eqorceq_eq_term_equals; eauto.
    apply eq_term_equals_sym.
    introv; split; intro q.

    { exists lib' e lib'0 e0 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e2 _ z0) as e2; simpl in *.
    apply nuprli_refl in h0; apply nuprli_refl in e2.
    eapply nuprli_uniquely_valued in h0; try exact e2; apply h0; auto.
  }

  {
    eapply in_ext_ext_Flib_implies_in_open_bar_ext; try exact e1.
    introv h; repnd; simpl.
    pose proof (h0 _ (lib_extends_refl _)) as h0; simpl in *.
    pose proof (h2 _ (lib_extends_refl _)) as h2; simpl in *.
    eapply eqorceq_eq_term_equals; eauto.
    apply eq_term_equals_sym.
    introv; split; intro q.

    { exists lib' e lib'0 e0 z (lib_extends_refl lib'0); auto. }

    exrepnd.
    pose proof (e1 _ ext1 _ ext2 extz) as e1; repnd.
    pose proof (e2 _ z0) as e2; simpl in *.
    apply nuprli_refl in h0; apply nuprli_refl in e2.
    eapply nuprli_uniquely_valued in h0; try exact e2; apply h0; auto.
  }
Qed.


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
  apply dest_nuprl_equality2 in e1; exrepnd.
  apply e1 in e0.
  exists (per_bar_eq lib eqa); dands.

  { apply CL_bar; exists eqa; dands; auto. }

  apply in_open_bar_ext_dup.
  eapply in_open_bar_ext_pres; try exact e0; clear e0; introv e0; simpl in *.
  unfold eq_per_eq_bar in e0; apply e_all_in_ex_bar_ext_as in e0.
  eapply in_open_bar_ext_pres; try exact e0; clear e0; introv m0; simpl in *; introv.
  unfold eq_per_eq, raise_ext_per in *; exrepnd.
  eapply lib_per_cond; eauto.
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

  pose proof (if_member_function lib mkc_id A v (cvterm_var v B) m lib (lib_extends_refl lib) x y e) as q.

  eapply equality_respects_cequivc_left in q;
    [|introv ext; spcast; apply reduces_toc_implies_cequivc; apply reduces_toc_apply_id].
  eapply equality_respects_cequivc_right in q;
    [|introv ext; spcast; apply reduces_toc_implies_cequivc; apply reduces_toc_apply_id].

  rewrite substc_cvterm_var in q; sp.
Qed.

Lemma member_equality_is_axiom {p} :
  forall lib (t1 t2 T a b : @CTerm p),
    equality lib a b (mkc_equality t1 t2 T)
    -> in_open_bar lib (fun lib => a ===>(lib) mkc_axiom # b ===>(lib) mkc_axiom).
Proof.
  unfold equality, nuprl; introv e; exrepd.
  apply dest_nuprl_equality2 in c; exrepnd.
  apply c1 in e.
  clear dependent eq.

  apply in_open_bar_ext_in_open_bar.
  eapply in_open_bar_ext_pres; try exact e; clear e; introv h; simpl in *.
  unfold eq_per_eq_bar in h; apply e_all_in_ex_bar_ext_as in h.
  eapply in_open_bar_comb2; try exact h; clear h.
  apply in_ext_ext_implies_in_open_bar_ext; introv h; simpl in *.
  unfold eq_per_eq, raise_ext_per in *; exrepnd; dands; auto.
Qed.

Lemma tequality_equality_if_cequivc {p} :
  forall lib (t1 t2 t3 t4 A B : @CTerm p),
    tequality lib A B
    -> ccequivc_ext lib t1 t3
    -> ccequivc_ext lib t2 t4
    -> tequality lib (mkc_equality t1 t2 A) (mkc_equality t3 t4 B).
Proof.
  introv teq ceq1 ceq2.
  unfold tequality in teq; exrepnd.
  pose proof (nuprl_monotone_func lib A B eq teq0) as tya; exrepnd.
  rename eq' into eqa.

  exists (eq_per_eq_bar lib t1 t2 eqa).
  apply CL_eq.
  exists A B t1 t2 t3 t4 eqa; dands; spcast; eauto 3 with slow;[].
  introv; apply tya0.
Qed.

Lemma tequality_mkc_equality_implies {o} :
  forall lib (a1 a2 b1 b2 A B : @CTerm o),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    ->
    (
      tequality lib A B
      # (equality lib a1 a2 A -> equality lib b1 b2 B)
      # in_open_bar lib (fun lib => (equality lib a1 b1 A {+} ccequivc_ext lib a1 b1))
    ).
Proof.
  introv teq; unfold tequality in teq; exrepnd.

  apply dest_nuprl_equality2 in teq0; exrepnd.
  dands; tcsp; eauto 3 with slow;[].

  introv ea.
  eapply (all_in_bar_ext_eqorceq_commutes_equality lib a1 b1 a2 b2); eauto.
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

Lemma tequality_mkc_equality {o} :
  forall lib (a1 a2 b1 b2 A B : @CTerm o),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=>
    (
      tequality lib A B
      # (equality lib a1 a2 A <=> equality lib b1 b2 B)
      # in_open_bar lib (fun lib' => equality lib' a1 b1 A {+} ccequivc_ext lib' a1 b1)
      # in_open_bar lib (fun lib' => equality lib' a2 b2 A {+} ccequivc_ext lib' a2 b2)
    ).
Proof.
  introv; split; intro k.

  - unfold tequality, nuprl in k; exrepnd.
    apply dest_nuprl_equality2 in k0; exrepnd.
    dands; eauto 3 with slow;
      try (eapply all_in_bar_ext_eqorceq_commutes_equality; eauto).

  - repnd.
    allunfold @tequality; exrepnd.

    pose proof (nuprl_monotone_func lib A B eq k3) as tya; exrepnd.
    rename eq' into eqa.
    exists (per_bar_eq lib (eq_per_eq_bar_lib_per lib a1 a2 eqa)).
    apply CL_bar; exists (eq_per_eq_bar_lib_per lib a1 a2 eqa).
    dands; tcsp;[]; simpl.
    eapply in_open_bar_ext_comb2; try exact k2; clear k2.
    eapply in_open_bar_ext_comb2; try exact k; clear k.
    apply in_ext_ext_implies_in_open_bar_ext; introv k k2.
    apply CL_eq.
    exists A B a1 a2 b1 b2 (raise_lib_per eqa e); simpl.
    fold (@nuprl o) in *.
    dands; spcast; eauto 3 with slow; simpl in *.

    {
      introv; simpl; unfold raise_ext_per.
      pose proof (tya0 _ (lib_extends_trans e0 e)) as q; repnd; auto.
    }

    {
      introv.
      unfold eqorceq; simpl; unfold raise_ext_per.
      repndors; tcsp; eauto 3 with slow; left;
        pose proof (tya0 _ (lib_extends_trans e0 e)) as tya0; repnd;
        try (eapply equality_monotone in k; eauto);
        try (eapply equality_monotone in k2; eauto);
        eapply (equality_eq1 lib'0 A B); auto.
    }

    {
      introv.
      unfold eqorceq; simpl; unfold raise_ext_per.
      repndors; tcsp; eauto 3 with slow; left;
        pose proof (tya0 _ (lib_extends_trans e0 e)) as tya0; repnd;
        try (eapply equality_monotone in k; eauto);
        try (eapply equality_monotone in k2; eauto);
        eapply (equality_eq1 lib'0 A B); auto.
    }
Qed.

Lemma tequality_mkc_equality_sp {o} :
  forall lib (a1 a2 b1 b2 A B : @CTerm o),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=>
    (
      tequality lib A B
      # in_open_bar lib (fun lib => equality lib a1 b1 A {+} ccequivc_ext lib a1 b1)
      # in_open_bar lib (fun lib => equality lib a2 b2 A {+} ccequivc_ext lib a2 b2)
    ).
Proof.
  introv; split; intro k.

  - unfold tequality, nuprl in k; exrepnd.
    apply dest_nuprl_equality2 in k0; exrepnd.
    dands; eauto 3 with slow;
      try (eapply all_in_bar_ext_eqorceq_commutes_equality; eauto).

  - repnd.
    allunfold @tequality; exrepnd.

    pose proof (nuprl_monotone_func lib A B eq k2) as tya; exrepnd.
    rename eq' into eqa.
    exists (per_bar_eq lib (eq_per_eq_bar_lib_per lib a1 a2 eqa)).
    apply CL_bar; exists (eq_per_eq_bar_lib_per lib a1 a2 eqa).
    dands; tcsp;[]; simpl.
    eapply in_open_bar_ext_comb2; try exact k1; clear k1.
    eapply in_open_bar_ext_comb2; try exact k; clear k.
    apply in_ext_ext_implies_in_open_bar_ext; introv k k1.
    apply CL_eq.
    exists A B a1 a2 b1 b2 (raise_lib_per eqa e); simpl.
    fold (@nuprl o) in *.
    dands; spcast; eauto 3 with slow; simpl in *.

    {
      introv; simpl; unfold raise_ext_per.
      pose proof (tya0 _ (lib_extends_trans e0 e)) as q; repnd; auto.
    }

    {
      introv.
      unfold eqorceq; simpl; unfold raise_ext_per.
      repndors; tcsp; eauto 3 with slow; left;
        pose proof (tya0 _ (lib_extends_trans e0 e)) as tya0; repnd;
        try (eapply equality_monotone in k; eauto);
        try (eapply equality_monotone in k1; eauto);
        eapply (equality_eq1 lib'0 A B); auto.
    }

    {
      introv.
      unfold eqorceq; simpl; unfold raise_ext_per.
      repndors; tcsp; eauto 3 with slow; left;
        pose proof (tya0 _ (lib_extends_trans e0 e)) as tya0; repnd;
        try (eapply equality_monotone in k; eauto);
        try (eapply equality_monotone in k1; eauto);
        eapply (equality_eq1 lib'0 A B); auto.
    }
Qed.

Lemma tequality_mkc_equality_if_equal {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib A B
    -> equality lib a1 b1 A
    -> equality lib a2 b2 A
    -> tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B).
Proof.
  introv teq e1 e2.
  rw @tequality_mkc_equality_sp; dands; auto; eauto 3 with slow.
Qed.

Lemma tequality_mkc_equality2 {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=>
    (
      tequality lib A B
      # (equality lib a1 a2 A <=> equality lib b1 b2 B)
      # equorsq2_bar lib a1 b1 a2 b2 A
    ).
Proof.
  intros.
  rw @tequality_mkc_equality.
  repeat (rw @fold_equorsq_bar).
  rw @fold_equorsq2_bar; sp.
Qed.

Lemma tequality_mkc_equality2_sp {p} :
  forall lib (a1 a2 b1 b2 A B : @CTerm p),
    tequality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B)
    <=>
    (
      tequality lib A B
      # equorsq2_bar lib a1 b1 a2 b2 A
    ).
Proof.
  intros.
  rw @tequality_mkc_equality_sp.
  repeat (rw @fold_equorsq_bar).
  rw @fold_equorsq2_bar; sp.
Qed.

Lemma tequality_mkc_member {p} :
  forall lib (a b A B : @CTerm p),
    tequality lib (mkc_member a A) (mkc_member b B)
    <=>
    (
      tequality lib A B
      # (member lib a A <=> member lib b B)
      # in_open_bar lib (fun lib => equality lib a b A {+} ccequivc_ext lib a b)
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
      # in_open_bar lib (fun lib => equality lib a b A {+} ccequivc_ext lib a b)
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
  rw @tequality_mkc_equality in teq; sp.
  allrw @fold_equorsq_bar; eauto 3 with slow.
Qed.

Lemma equality_commutes2 {p} :
  forall lib (T a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 T)
    -> equality lib a1 a2 T
    -> equality lib a1 a3 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; repnd.
  allrw @fold_equorsq_bar; eauto 3 with slow.
Qed.

Lemma equality_commutes3 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a1 a3 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; repnd.
  allrw @fold_equorsq_bar; eauto 3 with slow.
Qed.

Lemma equality_commutes4 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a1 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; repnd.
  allrw @fold_equorsq_bar; eauto 3 with slow.
Qed.

Lemma equality_commutes5 {p} :
  forall lib (T U a1 a2 a3 a4 : @CTerm p),
    tequality lib (mkc_equality a1 a2 T) (mkc_equality a3 a4 U)
    -> equality lib a1 a2 T
    -> equality lib a2 a4 T.
Proof.
  introv teq eq.
  rw @tequality_mkc_equality in teq; repnd.
  allrw @fold_equorsq_bar; eauto 3 with slow.
Qed.

Lemma equality_in_mkc_equality {o} :
  forall lib (t1 t2 T a b : @CTerm o),
    equality lib a b (mkc_equality t1 t2 T)
    <=> (equality lib t1 t2 T
         # in_open_bar lib (fun lib => a ===>(lib) mkc_axiom)
         # in_open_bar lib (fun lib => b ===>(lib) mkc_axiom)).
Proof.
  introv; split; intro i.

  {
    applydup @member_equality_is_axiom in i; repnd; sp;
      try (complete (eapply in_open_bar_pres; eauto; clear i0; introv ext i0; tcsp)).

    clear i0.
    unfold equality in i; exrepnd.
    apply dest_nuprl_equality2 in i1; exrepnd.
    apply i1 in i0.
    clear dependent eq.
    exists (per_bar_eq lib eqa); dands; auto; eauto 3 with slow;[].

    apply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; try exact i0; clear i0; introv h; simpl in *.
    unfold eq_per_eq_bar in h; apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; simpl in *; introv.
    unfold eq_per_eq, raise_ext_per in *; exrepnd; dands; auto.
    eapply lib_per_cond; eauto.
  }

  {
    repnd.
    unfold equality in i0; exrepnd.

    pose proof (nuprl_monotone_func lib T T eq i0) as tya; exrepnd.
    rename eq' into eqa.
    exists (eq_per_eq_bar lib t1 t2 eqa).
    dands.

    {
      apply CL_eq.
      exists T T t1 t2 t1 t2 eqa; dands; spcast; eauto 3 with slow.
      fold (@nuprl o).
      introv; apply tya0.
    }

    {
      unfold eq_per_eq_bar; apply e_all_in_ex_bar_ext_as.
      eapply in_open_bar_ext_comb2; try exact i1; clear i1.
      eapply in_open_bar_ext_comb2; try exact i; clear i.
      apply in_ext_ext_implies_in_open_bar_ext; introv i i1.
      unfold eq_per_eq; dands; auto.
      pose proof (tya0 _ e) as tya0; repnd; tcsp.
    }
  }
Qed.

Lemma tequality_mkc_equality_base_iff {o} :
  forall lib (t1 t2 t3 t4 : @CTerm o),
    tequality lib (mkc_equality t1 t2 mkc_base) (mkc_equality t3 t4 mkc_base)
    <=>
    (ccequivc_bar lib t1 t3 # ccequivc_bar lib t2 t4).
Proof.
  introv; split; intro k.

  - unfold tequality in k; exrepnd.
    apply dest_nuprl_equality2 in k0; exrepnd.
    dands.

    + apply ccequivc_ext_bar_iff_ccequivc_bar.
      apply in_open_bar_ext_in_open_bar.
      eapply in_open_bar_ext_comb; try exact k2; clear k2.
      eapply in_open_bar_ext_comb; try exact k3; clear k3.
      eapply in_open_bar_ext_pres; try exact k1; clear k1; introv k1 k3 k2.
      apply dest_nuprl_base2 in k2.
      unfold eqorceq in k3; repndors; tcsp; eauto 3 with slow.
      apply k2 in k3.
      unfold per_base_eq in *; apply e_all_in_ex_bar_as in k3.
      apply ccequivc_ext_bar_iff_ccequivc_bar in k3; auto.

    + apply ccequivc_ext_bar_iff_ccequivc_bar.
      apply in_open_bar_ext_in_open_bar.
      eapply in_open_bar_ext_comb; try exact k2; clear k2.
      eapply in_open_bar_ext_comb; try exact k3; clear k3.
      eapply in_open_bar_ext_pres; try exact k1; clear k1; introv k1 k3 k2.
      apply dest_nuprl_base2 in k2.
      unfold eqorceq in k1; repndors; tcsp; eauto 3 with slow.
      apply k2 in k1.
      unfold per_base_eq in *; apply e_all_in_ex_bar_as in k1.
      apply ccequivc_ext_bar_iff_ccequivc_bar in k1; auto.

  - repnd.
    apply ccequivc_ext_bar_iff_ccequivc_bar in k0.
    apply ccequivc_ext_bar_iff_ccequivc_bar in k.
    unfold ccequivc_ext_bar in *.
    exists (eq_per_eq_bar lib t1 t2 (per_base_eq_lib_per lib)).
    apply CL_eq.
    exists (@mkc_base o) (@mkc_base o) t1 t2 t3 t4 (per_base_eq_lib_per lib).
    dands; spcast; simpl; eauto 3 with slow.

    {
      introv e.
      apply CL_base.
      unfold per_base; dands; spcast; eauto 3 with slow.
    }

    {
      introv; simpl.
      left; unfold per_base_eq; apply e_all_in_ex_bar_as.
      apply ccequivc_ext_bar_iff_ccequivc_bar; auto.
      unfold ccequivc_ext_bar; eauto 3 with slow.
    }

    {
      introv; simpl.
      left; unfold per_base_eq; apply e_all_in_ex_bar_as.
      apply ccequivc_ext_bar_iff_ccequivc_bar; auto.
      unfold ccequivc_ext_bar; eauto 3 with slow.
    }
Qed.

Lemma tequality_equality_if_eqorceq {p} :
  forall lib (t1 t2 t3 t4 A B : @CTerm p),
    tequality lib A B
    -> ccequivc_ext lib t1 t3 [+] equality lib t1 t3 A
    -> ccequivc_ext lib t2 t4 [+] equality lib t2 t4 A
    -> tequality lib (mkc_equality t1 t2 A)
                 (mkc_equality t3 t4 B).
Proof.
  introv teq eoa eob.
  apply tequality_mkc_equality.
  repndors; dands; eauto 3 with slow;
    try (complete (apply in_ext_implies_in_open_bar; introv ext; right; eauto 3 with slow)).

  - split; intro h.
    { eapply equality_respects_cequivc_left;[eauto|].
      eapply equality_respects_cequivc_right;[eauto|].
      eapply tequality_preserving_equality; eauto. }
    { eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym;eauto|].
      eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym;eauto|].
      eapply tequality_preserving_equality; eauto.
      apply tequality_sym;auto. }

  - split; intro h.
    { eapply tequality_preserving_equality;eauto.
      eapply equality_trans;[apply equality_sym;eauto|].
      eapply equality_respects_cequivc_right;[eauto|]; auto. }
    { eapply equality_trans;[eauto|].
      eapply equality_respects_cequivc_right;[apply ccequivc_ext_sym;eauto|].
      eapply tequality_preserving_equality; eauto.
      apply tequality_sym;auto. }

  - split; intro h.
    { eapply tequality_preserving_equality;eauto.
      eapply equality_trans;[|eauto].
      eapply equality_respects_cequivc_left;[eauto|]; auto. }
    { eapply equality_trans;[|apply equality_sym;eauto].
      eapply equality_respects_cequivc_left;[apply ccequivc_ext_sym;eauto|].
      eapply tequality_preserving_equality; eauto.
      apply tequality_sym;auto. }

  - split; intro h.
    { eapply tequality_preserving_equality;eauto.
      eapply equality_trans;[|eauto].
      eapply equality_trans;[apply equality_sym;eauto|]; auto. }
    { eapply equality_trans;[eauto|].
      eapply equality_trans;[|apply equality_sym;eauto].
      eapply tequality_preserving_equality; eauto.
      apply tequality_sym;auto. }
Qed.

Lemma tequality_mkc_member_base {p} :
  forall lib (a b : @CTerm p),
    tequality lib (mkc_member a mkc_base) (mkc_member b mkc_base)
    <=>
    ccequivc_bar lib a b.
Proof.
  introv.
  rw @tequality_mkc_member; split; intro e; repnd; dands; eauto 3 with slow.

  {
    apply collapse_all_in_ex_bar.
    eapply in_open_bar_pres; eauto; clear e; introv ext h; repndors; eauto 3 with slow;[].
    apply equality_in_base_iff in h.
    unfold per_base_eq in h; apply e_all_in_ex_bar_as in h; auto.
  }

  { split; intro h; eauto 3 with slow. }

  {
    apply ccequivc_ext_bar_iff_ccequivc_bar in e.
    eapply in_open_bar_pres; try exact e; clear e; introv ext h; tcsp.
  }
Qed.

Lemma equality_on_closed_terms_is_a_type {p} :
  forall lib (A x y : @CTerm p), type lib A -> type lib (mkc_equality x y A).
Proof.
  introv ta.
  apply tequality_equality_if_cequivc; eauto 3 with slow.
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
  introv; allrw <- @fold_mkc_member.
  introv e.
  apply equality_in_mkc_equality in e; repnd; auto.
Qed.

Lemma tequality_in_uni_implies_tequality {p} :
  forall lib (T1 T2 : @CTerm p) i,
    tequality lib (mkc_member T1 (mkc_uni i))
              (mkc_member T2 (mkc_uni i))
    -> type lib T1
    -> tequality lib T1 T2.
Proof.
  introv teq typ.
  rw @tequality_mkc_member_sp in teq; repnd.
  apply all_in_ex_bar_tequality_implies_tequality.
  eapply in_open_bar_pres; try exact teq; clear teq; introv ext teq; repndors; eauto 3 with slow.
  apply tequality_sym; apply type_respects_cequivc_left; eauto 3 with slow.
Qed.

Lemma iff_inhabited_type_if_tequality_mem {o} :
  forall lib (T1 T2 : @CTerm o) i,
    tequality lib (mkc_member T1 (mkc_uni i)) (mkc_member T2 (mkc_uni i))
    -> (inhabited_type lib T1 <=> inhabited_type lib T2).
Proof.
  introv teq.
  rw @tequality_mkc_member in teq; repnd.
  split; intro inh.

  {
    allrw @inhabited_type_iff_exists_per; exrepnd.

    pose proof (nuprl_monotone_func lib T1 T1 eq inh0) as tya; exrepnd.
    rename eq' into eqa.
    exists (per_bar_eq lib eqa) t.
    dands.

    {
      apply CL_bar; exists eqa; dands; auto.
      fold (@nuprl o).
      eapply in_open_bar_ext_comb2; try exact teq; clear teq.
      apply in_ext_ext_implies_in_open_bar_ext; introv teq.
      pose proof (tya0 _ e) as tya0; repnd.
      repndors; eauto 3 with slow.

      - apply equality_in_uni in teq.
        unfold tequality in teq; exrepnd.
        eapply nuprl_trans;[|eauto].
        eapply nuprl_trans;[|eauto].
        apply nuprl_sym.
        eapply type_extensionality_nuprl;[eauto|].
        eapply uniquely_valued_nuprl;[|eauto].
        eapply nuprl_refl;eauto.

      - eapply nuprl_value_respecting_right;[|eauto].
        eapply nuprl_value_respecting_left;[|eauto]; auto.
    }

    {
      apply in_ext_ext_implies_in_open_bar_ext; introv.
      pose proof (tya0 _ e) as tya0; repnd.
      apply tya0; auto.
    }
  }

  {
    allrw @inhabited_type_iff_exists_per; exrepnd.

    pose proof (nuprl_monotone_func lib T2 T2 eq inh0) as tya; exrepnd.
    rename eq' into eqa.
    exists (per_bar_eq lib eqa) t.
    dands.

    {
      apply CL_bar; exists eqa; dands; auto.
      fold (@nuprl o).
      eapply in_open_bar_ext_comb2; try exact teq; clear teq.
      apply in_ext_ext_implies_in_open_bar_ext; introv teq.
      pose proof (tya0 _ e) as tya0; repnd.
      repndors; eauto 3 with slow.

      - apply equality_in_uni in teq.
        unfold tequality in teq; exrepnd.
        eapply nuprl_trans;[|apply nuprl_sym;eauto].
        applydup @nuprl_refl2 in teq2.
        eapply uniquely_valued_nuprl in teq3; autodimp teq3 hyp; try exact tya1.
        eapply type_extensionality_nuprl;eauto.

      - eapply nuprl_value_respecting_right;[|apply ccequivc_ext_sym;eauto].
        eapply nuprl_value_respecting_left;[|apply ccequivc_ext_sym;eauto]; auto.
    }

    {
      apply in_ext_ext_implies_in_open_bar_ext; introv.
      pose proof (tya0 _ e) as tya0; repnd.
      apply tya0; auto.
    }
  }
Qed.

Lemma equality_in_member {p} :
  forall lib (a b t T : @CTerm p),
    equality lib a b (mkc_member t T)
    <=> (in_open_bar lib (fun lib => a ===>(lib) mkc_axiom)
         # in_open_bar lib (fun lib => b ===>(lib) mkc_axiom)
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
  unfold all_in_ex_bar in *; exrepnd.

  unfold member, equality in mem; exrepnd.
  pose proof (nuprl_monotone_func lib A A eq mem1) as tya; exrepnd.
  rename eq' into eqa.
  exists (per_bar_eq lib eqa).
  dands.

  {
    apply CL_bar; exists eqa; dands; auto.
    fold (@nuprl o).
    eapply in_ext_ext_implies_in_open_bar_ext; introv; apply tya0.
  }

  {
    eapply in_open_bar_ext_comb2; try exact teq; clear teq.
    apply in_ext_ext_implies_in_open_bar_ext; introv teq.
    pose proof (tya0 _ e) as tya0; repnd.
    repndors.
    { eapply equality_eq1; eauto. }
    eapply equality_eq1; eauto.
    eapply equality_respects_cequivc_right;[eauto|]; auto.
    apply tya0 in mem0.
    eapply equality_eq1 in mem0; eauto.
  }
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
  - rw @tequality_mkc_equality_sp in h; repnd; eauto 3 with slow.
  - rw @tequality_mkc_equality_sp in h; repnd; eauto 3 with slow.
  - apply tequality_mkc_equality_sp; dands; eauto 3 with slow.
Qed.

Lemma equality_mkc_equality2_sp_in_uni {o} :
  forall lib i (a1 a2 b1 b2 A B : @CTerm o),
    equality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) (mkc_uni i)
    <=>
    (
      equality lib A B (mkc_uni i)
      # equorsq2_bar lib a1 b1 a2 b2 A
    ).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    introv e.
    unfold equality in e; exrepnd.

    applydup @dest_nuprl_uni in e1.
    apply univ_implies_univi_bar3 in e2; exrepnd.
    apply e2 in e0.

    apply per_bar_eq_univi_eq_lib_per_implies_eq_nuprli in e0; exrepnd.
    apply dest_nuprli_equality2 in e3; exrepnd.
    unfold equorsq2_bar.
    dands.

    + exists eq; dands; auto.
      apply e2.
      eapply in_open_bar_ext_pres; try exact e4; clear e4; introv h; simpl.
      exists (eqa lib' e); auto.

    + eapply in_open_bar_comb2; try exact e4; clear e4.
      eapply in_open_bar_ext_pres; try exact e5; clear e5; introv h q; simpl.
      eapply eqorceq_iff_equorsq; eauto 3 with slow.

    + eapply in_open_bar_comb2; try exact e4; clear e4.
      eapply in_open_bar_ext_pres; try exact e0; clear e0; introv h q; simpl.
      eapply eqorceq_iff_equorsq; eauto 3 with slow.

  - Case "<-".
    intro e.
    destruct e as [e eo].
    destruct eo as [eo1 eo2].
    unfold equality in e; exrepnd.

    applydup @dest_nuprl_uni in e1.
    apply univ_implies_univi_bar3 in e2; exrepnd.
    apply e2 in e0.

    apply per_bar_eq_univi_eq_lib_per_implies_eq_nuprli in e0; exrepnd.
    exists eq; dands; auto.
    apply e2.
    clear dependent eq.

    eapply in_open_bar_ext_comb2; try exact eo1; clear eo1.
    eapply in_open_bar_ext_comb2; try exact eo2; clear eo2.
    apply in_ext_ext_implies_in_open_bar_ext; introv eo2 eo1; simpl.

    pose proof (nuprli_monotone_func i lib A B eq' e3) as tya; exrepnd.
    rename eq'0 into eqa.

    exists (eq_per_eq_bar lib' a1 a2 (raise_lib_per eqa e)).
    fold (@nuprli o i).
    apply CL_eq.
    exists A B a1 a2 b1 b2 (raise_lib_per eqa e).
    fold (@nuprli o i).
    pose proof (tya0 _ e) as tyb; repnd.
    dands; spcast; eauto 3 with slow; simpl; try unfold raise_ext_per.

    + introv; eapply tya0.

    + introv; simpl; unfold raise_ext_per.
      eapply lib_extends_preserves_equorsq in eo1; eauto.
      eapply eqorceq_iff_equorsq; eauto.
      eapply nuprli_implies_nuprl; eapply tya0.

    + introv; simpl; unfold raise_ext_per.
      eapply lib_extends_preserves_equorsq in eo2; eauto.
      eapply eqorceq_iff_equorsq; eauto.
      eapply nuprli_implies_nuprl; eapply tya0.
Qed.

(* end hide *)
