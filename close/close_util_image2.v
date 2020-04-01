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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys_useful.
Require Export dest_close.
Require Export per_ceq_bar.

Require Export close_util_image.
Require Export close_util1.
Require Export close_util2.


Lemma eq_term_equals_per_image_eq_if {p} :
  forall lib (eqa1 eqa2 : per(p)) f1 f2,
    ccequivc_ext lib f1 f2
    -> eq_term_equals eqa1 eqa2
    -> eq_term_equals (per_image_eq lib eqa1 f1) (per_image_eq lib eqa2 f2).
Proof.
  introv ceq eqt.
  unfold eq_term_equals; introv; split; intro k; induction k.

  - apply @image_eq_cl with (t := t); sp.

  - apply @image_eq_eq with (a1 := a1) (a2 := a2); sp; spcast.

    { apply eqt; sp. }

    { apply ccequivc_ext_trans with (b := mkc_apply f1 a1); auto.
      apply implies_ccequivc_ext_apply; eauto 3 with slow. }

    { apply ccequivc_ext_trans with (b := mkc_apply f1 a2); auto.
      apply implies_ccequivc_ext_apply; eauto 3 with slow. }

  - apply @image_eq_cl with (t := t); sp.

  - apply @image_eq_eq with (a1 := a1) (a2 := a2); sp; spcast.

    { apply eqt; sp. }

    { apply ccequivc_ext_trans with (b := mkc_apply f2 a1); auto.
      apply implies_ccequivc_ext_apply; eauto 3 with slow. }

    { apply ccequivc_ext_trans with (b := mkc_apply f2 a2); auto.
      apply implies_ccequivc_ext_apply; eauto 3 with slow. }
Qed.

Lemma per_image_eq_sym {p} :
  forall lib (eqa : per(p)) f t1 t2,
    term_equality_symmetric eqa
    -> per_image_eq lib eqa f t1 t2
    -> per_image_eq lib eqa f t2 t1.
Proof.
  introv tes per.
  induction per.
  apply @image_eq_cl with (t := t); sp.
  apply @image_eq_eq with (a1 := a2) (a2 := a1); sp.
Qed.

Lemma per_image_eq_trans {p} :
  forall lib (eqa : per(p)) f t1 t2 t3,
    term_equality_transitive eqa
    -> per_image_eq lib eqa f t1 t2
    -> per_image_eq lib eqa f t2 t3
    -> per_image_eq lib eqa f t1 t3.
Proof.
  introv tet per1 per2.
  apply image_eq_cl with (t := t2); sp.
Qed.

Lemma per_image_eq_cequiv {p} :
  forall lib (eqa : per(p)) f t t',
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> ccequivc_ext lib t t'
    -> per_image_eq lib eqa f t t
    -> per_image_eq lib eqa f t t'.
Proof.
  introv tes tet ceq per.
  revert_dependents t'.
  induction per; introv ceq.
  { apply IHper2; auto. }
  apply @image_eq_eq with (a1 := a2) (a2 := a2); sp.
  { apply tet with (t2 := a1); sp. }
  spcast.
  apply ccequivc_ext_trans with (b := t2); sp.
  apply ccequivc_ext_sym; sp.
Qed.

Lemma per_bar_per_image_implies_eq_term_equals_per_image_eq_bar {o} :
  forall (ts : cts(o)) uk lib T T' eq (eqa : lib-per(lib,o)) A A' f,
    ccomputes_to_valc_ext lib T (mkc_image A f)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_bar (per_image ts) uk lib T T' eq
    -> eq <=2=> (per_image_eq_bar lib eqa f).
Proof.
  introv comp tsa per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per0.

  introv; split; intro h.

  - unfold per_image_eq_bar.
    apply in_open_bar_ext_dup.
    unfold per_bar_eq in *.
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    eapply in_open_bar_ext_comb; try exact h; clear h.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv h per1; exrepnd.

    unfold per_image in per1; exrepnd.
    apply per0 in h; clear per0.
    unfold per_image_eq_bar in h.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; introv.

    eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_image_implies in ceq; repnd.

    dup per3 as eqas.
    eapply (in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 _ _ e) in eqas;
      [|exact tsa|]; eauto 3 with slow;[].

    eapply eq_term_equals_per_image_eq_if; try exact h; eauto 3 with slow.
    pose proof (eqas _ e0) as q; simpl in q.
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
    apply lib_per_cond.

  - eapply in_open_bar_ext_comb; try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv per1; introv.
    unfold per_image in per1; exrepnd.
    apply per0; clear per0.

    eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_image_implies in ceq; repnd.

    dup per3 as eqas.
    eapply (in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 _ _ e) in eqas;
      [|exact tsa|]; eauto 3 with slow.

    apply (sub_per_per_image_eq_bar _ _ e) in h.
    eapply implies_eq_term_equals_per_image_eq_bar;[| |eauto]; eauto 3 with slow.
Qed.

Lemma per_bar_per_image_implies_close {o} :
  forall (ts : cts(o)) uk lib T T' eq,
    per_bar (per_image (close ts)) uk lib T T' eq
    -> close ts uk lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.
  apply CL_image; auto.
Qed.

Lemma ccequivc_ext_image {o} :
  forall lib (T T' : @CTerm o) A f,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_image A f)
    -> ccomputes_to_valc_ext lib T' (mkc_image A f).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma type_value_respecting_trans_per_bar_per_image1 {o} :
  forall uk lib (ts : cts(o)) T T1 T2 A f A' f' C (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccomputes_to_valc_ext lib T1 (mkc_image A' f')
    -> ccomputes_to_valc_ext lib T (mkc_image A f)
    -> ccequivc_ext lib A A'
    -> ccequivc_ext lib f f'
    -> per_bar (per_image ts) uk lib T1 T2 eq
    -> per_bar (per_image ts) uk lib T T2 eq.
Proof.
  introv tsa comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_image in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].
  eapply ccomputes_to_valc_ext_monotone in comp2;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq; repnd.

  exists eqa1 A A2 f f2; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1; eauto; eauto 3 with slow. }
  { eauto 4 with slow. }
  { eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_image_eq_bar; eauto 4 with slow. }
Qed.

Lemma type_value_respecting_trans_per_bar_per_image2 {o} :
  forall uk lib (ts : cts(o)) T T1 T2 A f A' f' C (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccomputes_to_valc_ext lib T1 (mkc_image A' f')
    -> ccomputes_to_valc_ext lib T (mkc_image A f)
    -> ccequivc_ext lib A A'
    -> ccequivc_ext lib f f'
    -> per_bar (per_image ts) uk lib T2 T1 eq
    -> per_bar (per_image ts) uk lib T T2 eq.
Proof.
  introv tsa comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_image in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].
  eapply ccomputes_to_valc_ext_monotone in comp2;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq; repnd.

  exists eqa1 A A1 f f1; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props_type_value_respecting_trans2; eauto; eauto 3 with slow. }
  { eapply ccequivc_ext_trans;[eapply lib_extends_preserves_ccequivc_ext;[|eauto];eauto 3 with slow|].
    eauto 3 with slow. }
  { eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply implies_eq_term_equals_per_image_eq_bar; eauto 3 with slow.
    eapply ccequivc_ext_trans;[eapply lib_extends_preserves_ccequivc_ext;[|eauto];eauto 3 with slow|].
    eauto 3 with slow. }
Qed.

Lemma per_image_sym {o} :
  forall ts uk lib (T1 T2 : @CTerm o) A A' f equ (eqa : lib-per(lib,o)),
    ccomputes_to_valc_ext lib T1 (mkc_image A f)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_image ts uk lib T1 T2 equ
    -> per_image ts uk lib T2 T1 equ.
Proof.
  introv comp tspa per.

  unfold per_image in *; exrepnd.
  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq; repnd.

  exists eqa0 A2 A f2 f; dands; spcast; auto; eauto 3 with slow.
  { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
      try exact tspa; eauto; eauto 3 with slow. }
  { eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_image_eq_bar; eauto 3 with slow. }
Qed.

Lemma per_image_sym_rev {o} :
  forall ts uk lib (T1 T2 : @CTerm o) A A' f equ (eqa : lib-per(lib,o)),
    ccomputes_to_valc_ext lib T1 (mkc_image A f)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_image ts uk lib T2 T1 equ
    -> per_image ts uk lib T1 T2 equ.
Proof.
  introv comp tspa per.

  unfold per_image in *; exrepnd.
  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq; repnd.

  exists eqa0 A A1 f f1; dands; spcast; auto; eauto 3 with slow.
  { eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
      try exact tspa; eauto; eauto 3 with slow. }
  { eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_image_eq_bar; eauto 3 with slow. }
Qed.

Lemma per_bar_per_image_sym {o} :
  forall (ts : cts(o)) uk lib T T' A f A' (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_image A f)
    -> per_bar (per_image ts) uk lib T T' eq
    -> per_bar (per_image ts) uk lib T' T eq.
Proof.
  introv tsa comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_image_sym; try exact comp; eauto.
Qed.

Lemma per_bar_per_image_sym_rev {o} :
  forall (ts : cts(o)) uk lib T T' A f A' (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_image A f)
    -> per_bar (per_image ts) uk lib T' T eq
    -> per_bar (per_image ts) uk lib T T' eq.
Proof.
  introv tsa comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_image_sym_rev; try exact comp; eauto.
Qed.

Lemma per_image_trans1 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A f A',
    ccomputes_to_valc_ext lib T (mkc_image A f)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_image ts uk lib T T2 eq2
    -> per_image ts uk lib T1 T eq1
    -> per_image ts uk lib T1 T2 eq1.
Proof.
  introv comp tsa pera perb.
  unfold per_image in *; exrepnd.

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq; repnd.
  apply cequivc_ext_mkc_image_implies in ceq0; repnd.

  exists eqa0 A1 A3 f1 f3; dands; spcast; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans1; try exact tsa; eauto.

  { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
      try exact tsa; try exact perb3; eauto 3 with slow. }

  { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
      try exact tsa; try exact pera3; eauto 3 with slow. }
Qed.

Lemma per_image_trans2 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A f A',
    ccomputes_to_valc_ext lib T (mkc_image A f)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_image ts uk lib T T2 eq2
    -> per_image ts uk lib T1 T eq1
    -> per_image ts uk lib T1 T2 eq2.
Proof.
  introv comp tsa pera perb.
  unfold per_image in *; exrepnd.
  spcast.

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq; repnd.
  apply cequivc_ext_mkc_image_implies in ceq0; repnd.

  exists eqa1 A1 A3 f1 f3; dands; spcast; auto; eauto 3 with slow.

  {
    eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans2;
      try exact tsa; eauto.
    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }

  { eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_image_eq_bar; eauto 3 with slow. }
Qed.

Lemma per_image_trans3 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A A' f',
    ccomputes_to_valc_ext lib T (mkc_image A' f')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_image ts uk lib T T2 eq2
    -> per_image ts uk lib T1 T eq1
    -> per_image ts uk lib T1 T2 eq1.
Proof.
  introv comp tsa pera perb.
  unfold per_image in *; exrepnd.

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq; repnd.
  apply cequivc_ext_mkc_image_implies in ceq0; repnd.

  exists eqa0 A1 A3 f1 f3; dands; spcast; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans3; try exact tsa; eauto.

  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
      try exact tsa; try exact perb3; eauto 3 with slow. }

  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
      try exact tsa; try exact pera3; eauto 3 with slow. }
Qed.

Lemma per_image_trans4 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa : lib-per(lib,o)) A A' f',
    ccomputes_to_valc_ext lib T (mkc_image A' f')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_image ts uk lib T T2 eq2
    -> per_image ts uk lib T1 T eq1
    -> per_image ts uk lib T1 T2 eq2.
Proof.
  introv comp tsa pera perb.
  unfold per_image in *; exrepnd.

  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq; repnd.
  apply cequivc_ext_mkc_image_implies in ceq0; repnd.

  exists eqa1 A1 A3 f1 f3; dands; spcast; eauto 3 with slow.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans4; try exact tsa; eauto.

    { apply in_ext_ext_type_sys_props4_sym in tsa.
      eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }

    { apply in_ext_ext_type_sys_props4_sym in tsa.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }
  { eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_image_eq_bar; eauto 3 with slow. }
Qed.

Lemma per_bar_per_image_trans1 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A f A' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_image A f)
    -> per_bar (per_image ts) uk lib T1 T eq1
    -> per_bar (per_image ts) uk lib T T2 eq2
    -> per_bar (per_image ts) uk lib T1 T2 eq1.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; eauto; clear pera1; introv pera1 perb1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_image_trans1; try exact comp; eauto.
Qed.

Lemma per_bar_per_image_trans2 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A f A' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_image A f)
    -> per_bar (per_image ts) uk lib T1 T eq1
    -> per_bar (per_image ts) uk lib T T2 eq2
    -> per_bar (per_image ts) uk lib T1 T2 eq2.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; eauto; clear pera1; introv pera1 perb1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_image_trans2; try exact comp; eauto.
Qed.

Lemma per_bar_per_image_trans3 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A A' f' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_image A' f')
    -> per_bar (per_image ts) uk lib T1 T eq1
    -> per_bar (per_image ts) uk lib T T2 eq2
    -> per_bar (per_image ts) uk lib T1 T2 eq1.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; eauto; clear pera1; introv pera1 perb1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_image_trans3; try exact comp; eauto.
Qed.

Lemma per_bar_per_image_trans4 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A A' f' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_image A' f')
    -> per_bar (per_image ts) uk lib T1 T eq1
    -> per_bar (per_image ts) uk lib T T2 eq2
    -> per_bar (per_image ts) uk lib T1 T2 eq2.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; eauto; clear pera1; introv pera1 perb1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  eapply per_image_trans4; try exact comp; eauto.
Qed.

Lemma per_image_eq_bar_symmetric {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) f t1 t2,
    in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> per_image_eq_bar lib eqa f t1 t2
    -> per_image_eq_bar lib eqa f t2 t1.
Proof.
  introv tes per.
  unfold per_image_eq_bar in *; exrepnd.
  eapply in_open_bar_ext_comb; try exact tes; clear tes.
  eapply in_open_bar_ext_pres; eauto; clear per; introv per tes.
  apply per_image_eq_sym; auto.
Qed.

Lemma per_image_eq_bar_transitive {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) f t1 t2 t3,
    in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> per_image_eq_bar lib eqa f t1 t2
    -> per_image_eq_bar lib eqa f t2 t3
    -> per_image_eq_bar lib eqa f t1 t3.
Proof.
  introv teta pera perb.
  unfold per_image_eq_bar in *.
  exrepnd.
  eapply in_open_bar_ext_comb; try exact perb; clear perb.
  eapply in_open_bar_ext_comb; try exact pera; clear pera.
  eapply in_open_bar_ext_pres; eauto; clear teta; introv teta pera perb.
  eapply per_image_eq_trans; eauto.
Qed.

Lemma per_image_eq_bar_cequiv {o} :
  forall (lib : @library o) (eqa : lib-per(lib,o)) f t1 t2,
    in_open_bar_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> ccequivc_ext lib t1 t2
    -> per_image_eq_bar lib eqa f t1 t1
    -> per_image_eq_bar lib eqa f t1 t2.
Proof.
  introv tera tesa teta ceq per.

  unfold per_image_eq_bar in *; exrepnd.
  eapply in_open_bar_ext_comb; try exact per; clear per.
  eapply in_open_bar_ext_comb; try exact teta; clear teta.
  eapply in_open_bar_ext_comb; try exact tesa; clear tesa.
  eapply in_open_bar_ext_pres; eauto; clear tera; introv tera tesa teta per.
  eapply per_image_eq_cequiv; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans1_per_image {o} :
  forall uk lib ts T T' eq A A' f f' (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_image A f)
    -> T' ===>(lib) (mkc_image A' f')
    -> in_ext_ext lib (fun lib' x => close ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' A A' (eqa lib' x))
    -> (eq <=2=> (per_image_eq_bar lib eqa f))
    -> type_equality_respecting_trans1 (close ts) uk lib T T'.
Proof.
  introv tysys dou c1 c2 cla tsa eqiff.
  introv h ceq cl.
  repndors; subst.

  {
    eapply ccequivc_ext_image in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_image_implies_close.
    eapply type_value_respecting_trans_per_bar_per_image1;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    eapply ccequivc_ext_image in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_image_implies_close.
    eapply type_value_respecting_trans_per_bar_per_image1;
      try exact h; try exact c2; eauto 3 with slow.
  }

  {
    eapply ccequivc_ext_image in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_image_implies_close.
    eapply type_value_respecting_trans_per_bar_per_image2;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    eapply ccequivc_ext_image in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_image_implies_close.
    eapply type_value_respecting_trans_per_bar_per_image2;
      try exact h; try exact c2; eauto 3 with slow.
  }
Qed.

Lemma type_value_respecting_trans_per_bar_per_image3 {o} :
  forall uk lib (ts : cts(o)) T T1 T2 A f C (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_image A f)
    -> ccequivc_ext lib T1 T2
    -> per_bar (per_image ts) uk lib T T1 eq
    -> per_bar (per_image ts) uk lib T T2 eq.
Proof.
  introv tsa comp1 ceqa per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_image in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.

  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq; repnd.

  exists eqa1 A A2 f f2; dands; spcast; auto; eauto 3 with slow.
  { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1; eauto; eauto 3 with slow. }
  { eapply eq_term_equals_trans;[eauto|].
    apply implies_eq_term_equals_per_image_eq_bar; eauto 4 with slow. }
Qed.

Lemma implies_type_value_respecting_trans2_per_image {o} :
  forall uk lib ts T T' eq A A' f f' (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_image A f)
    -> T' ===>(lib) (mkc_image A' f')
    -> in_ext_ext lib (fun lib' x => close ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' A A' (eqa lib' x))
    -> (eq <=2=> (per_image_eq_bar lib eqa f))
    -> type_equality_respecting_trans2 (close ts) uk lib T T'.
Proof.
  introv tysys dou c1 c2 cla tsa eqiff.
  introv h cl ceq.
  repndors; subst.

  {
    dclose_lr; clear cl.
    apply per_bar_per_image_implies_close.
    eapply type_value_respecting_trans_per_bar_per_image3;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_image_implies_close.
    eapply type_value_respecting_trans_per_bar_per_image3;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_image_implies_close.
    eapply per_bar_per_image_sym_rev in h; try exact tsa; eauto.
    eapply type_value_respecting_trans_per_bar_per_image3;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_image_implies_close.
    eapply per_bar_per_image_sym_rev in h; try exact tsa'; eauto.
    eapply type_value_respecting_trans_per_bar_per_image3;
      try exact h; try exact c1; eauto 3 with slow.
  }
Qed.
