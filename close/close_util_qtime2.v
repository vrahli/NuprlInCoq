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

Require Export close_util_qtime.
Require Export close_util1.
Require Export close_util2.

Lemma per_bar_per_qtime_implies_eq_term_equals_per_qtime_eq_bar {o} :
  forall (ts : cts(o)) lib T T' eq (eqa : lib-per(lib,o)) A A',
    ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_bar (per_qtime ts) lib T T' eq
    -> eq <=2=> (per_qtime_eq_bar lib eqa).
Proof.
  introv comp tsa per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per1.

  introv; split; intro h.

  - unfold per_qtime_eq_bar, per_qtime_eq.
    apply collapse2bars_ext.
    { introv; split; intro q; introv; introv.
      - exrepnd; eexists; eexists; dands; eauto.
        eapply (lib_per_cond _ eqa); eauto.
      - exrepnd; eexists; eexists; dands; eauto.
        eapply (lib_per_cond _ eqa); eauto. }

    exists bar.
    introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *.
    exrepnd.

    apply collapse2bars_ext.
    { introv; split; intro q; introv; introv.
      - exrepnd; eexists; eexists; dands; eauto.
        eapply (lib_per_cond _ eqa); eauto.
      - exrepnd; eexists; eexists; dands; eauto.
        eapply (lib_per_cond _ eqa); eauto. }

    exists bar'.
    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.

    assert (lib_extends lib'2 lib') as xt1 by eauto 3 with slow.
    pose proof (per0 _ br lib'2 xt1 (lib_extends_trans x0 x)) as per0; simpl in *.
    unfold per_qtime in per0; exrepnd.
    apply per1 in h0; clear per1.
    unfold per_qtime_eq_bar, per_qtime_eq in h0; exrepnd.

    exists bar0.
    introv br'' ext''; introv.
    pose proof (h1 _ br'' _ ext'' x1) as h1; simpl in *; exrepnd.
    eexists; eexists; dands; eauto.

    assert (lib_extends lib'2 lib) as xt2 by eauto 3 with slow.
    eapply lib_extends_preserves_ccomputes_to_valc in comp; try exact xt2; eauto.
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.

    eapply (in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 _ xt2) in per3;
      try exact tsa; eauto 3 with slow.
    pose proof (per3 _ x1) as per3; simpl in *.
    eapply (lib_per_cond _ eqa); apply per3; auto.

  - introv br ext; introv.
    exists (raise_bar bar x); introv br' ext'; introv; simpl in *; exrepnd.
    pose proof (per0 _ br'1 lib'2 (lib_extends_trans ext' br'2) (lib_extends_trans x0 x)) as per0; simpl in *.
    unfold per_qtime in per0; exrepnd.
    apply per1; clear per1.

    assert (lib_extends lib'2 lib) as xt by eauto 3 with slow.
    eapply lib_extends_preserves_ccomputes_to_valc in comp; try exact xt2; eauto.
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.

    apply (sub_per_per_qtime_eq_bar _ _ (lib_extends_trans x0 x)) in h.
    eapply implies_eq_term_equals_per_qtime_eq_bar; try exact h.

    eapply (in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 _ xt) in per3;
      try exact tsa; eauto 3 with slow.
    simpl; unfold raise_ext_per; auto.
    introv.
    pose proof (per3 _ e) as per3; simpl in *.
    eapply eq_term_equals_trans;[eauto|].
    introv; split; intro w; eapply (lib_per_cond _ eqa); eauto.
Qed.

Lemma per_bar_per_qtime_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_qtime (close ts)) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  apply CL_qtime; auto.
Qed.

Lemma type_value_respecting_trans_per_bar_per_qtime1 {o} :
  forall lib (ts : cts(o)) T T1 T2 A A' C (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> ccomputes_to_valc_ext lib T1 (mkc_qtime A')
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> ccequivc_ext lib A A'
    -> per_bar (per_qtime ts) lib T1 T2 eq
    -> per_bar (per_qtime ts) lib T T2 eq.
Proof.
  introv tsa comp1 comp2 ceqa per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  unfold per_qtime in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact x].
  eapply ccomputes_to_valc_ext_monotone in comp2;[|exact x].
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  exists eqa1 A B; dands; eauto 3 with slow.

  eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
    try exact tsa; eauto; eauto 3 with slow.
Qed.

Lemma type_value_respecting_trans_per_bar_per_qtime2 {o} :
  forall lib (ts : cts(o)) T T1 T2 A A' C (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> ccomputes_to_valc_ext lib T1 (mkc_qtime A')
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> ccequivc_ext lib A A'
    -> per_bar (per_qtime ts) lib T2 T1 eq
    -> per_bar (per_qtime ts) lib T T2 eq.
Proof.
  introv tsa comp1 comp2 ceqa per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  unfold per_qtime in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact x].
  eapply ccomputes_to_valc_ext_monotone in comp2;[|exact x].
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  exists eqa1 A A0; dands; eauto 3 with slow.

  eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
    try exact tsa; eauto; eauto 3 with slow.
Qed.

Lemma per_qtime_eq_bar_sym {o} :
  forall ts lib (eqa : lib-per(lib,o)) A A' t1 t2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_qtime_eq_bar lib eqa t1 t2
    -> per_qtime_eq_bar lib eqa t2 t1.
Proof.
  introv tsa per.

  unfold per_qtime_eq_bar in *; exrepnd.
  exists bar; introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  pose proof (tsa _ x) as tsa; simpl in *.
  apply type_sys_props4_implies_term_equality_symmetric in tsa.

  unfold per_qtime_eq in *; exrepnd.
  exists y x0; dands; eauto 3 with slow.
Qed.

Lemma per_qtime_eq_bar_trans {o} :
  forall ts lib (eqa : lib-per(lib,o)) A A' t1 t2 t3,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_qtime_eq_bar lib eqa t1 t2
    -> per_qtime_eq_bar lib eqa t2 t3
    -> per_qtime_eq_bar lib eqa t1 t3.
Proof.
  introv tsa pera perb.

  unfold per_qtime_eq_bar in *; exrepnd.
  exists (intersect_bars bar0 bar); introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  pose proof (tsa _ x) as tsa; simpl in *.
  apply type_sys_props4_implies_term_equality_transitive in tsa.

  unfold per_qtime_eq in *; exrepnd; spcast.
  pose proof (pera3 _ (lib_extends_refl _)) as h1; simpl in *.
  pose proof (perb3 _ (lib_extends_refl _)) as h2; simpl in *.
  spcast.
  exists x1 y0; dands; spcast; eauto 3 with slow.
  eapply cequivc_trans;[apply cequivc_sym|]; eauto.
Qed.

Lemma per_qtime_eq_bar_resp {o} :
  forall ts lib (eqa : lib-per(lib,o)) A A' t t',
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_qtime_eq_bar lib eqa t t
    -> ccequivc_ext lib t t'
    -> per_qtime_eq_bar lib eqa t t'.
Proof.
  introv tsa per ceq.

  unfold per_qtime_eq_bar in *; exrepnd.
  exists bar; introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  pose proof (tsa _ x) as tsa; simpl in *.
  applydup @type_sys_props4_implies_term_equality_symmetric in tsa as syma.
  applydup @type_sys_props4_implies_term_equality_transitive in tsa as transa.
  applydup @type_sys_props4_implies_term_equality_respecing in tsa as respa.

  unfold per_qtime_eq in *; exrepnd.
  pose proof (ceq _ x) as h1; simpl in *.
  exists x0 y; dands; spcast; eauto 3 with slow.
  eapply cequivc_trans;[|eauto]; apply cequivc_sym;auto.
Qed.

Lemma per_bar_per_qtime_sym {o} :
  forall (ts : cts(o)) lib T T' A A' (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> per_bar (per_qtime ts) lib T T' eq
    -> per_bar (per_qtime ts) lib T' T eq.
Proof.
  introv tsa comp per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact x].
  unfold per_qtime in *; exrepnd.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  exists eqa1 B A; dands; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto;
    try (complete (eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
                   try exact tspa; eauto; eauto 3 with slow)).
Qed.

Lemma per_bar_per_qtime_sym_rev {o} :
  forall (ts : cts(o)) lib T T' A A' (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> per_bar (per_qtime ts) lib T' T eq
    -> per_bar (per_qtime ts) lib T T' eq.
Proof.
  introv tsa comp per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact x].
  unfold per_qtime in *; exrepnd.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  exists eqa1 A A0; dands; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
    try exact tspa; eauto; eauto 3 with slow.
Qed.

Lemma per_bar_per_qtime_trans1 {o} :
  forall (ts : cts(o)) lib T T1 T2 A A' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> per_bar (per_qtime ts) lib T1 T eq1
    -> per_bar (per_qtime ts) lib T T2 eq2
    -> per_bar (per_qtime ts) lib T1 T2 eq1.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa1; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_left].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact x].
  unfold per_qtime in *; exrepnd.
  computes_to_eqval_ext.
  hide_hyp perb0.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.
  apply cequivc_ext_mkc_qtime_right in ceq0; eauto 3 with slow;[]; repnd.

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  exists eqa3 A1 B; dands; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans1; try exact tsa; eauto.
  { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
      try exact tsa; eauto 3 with slow. }
  { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
      try exact tsa; try exact perb4; eauto 3 with slow. }
Qed.

Lemma per_bar_per_qtime_trans2 {o} :
  forall (ts : cts(o)) lib T T1 T2 A A' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> per_bar (per_qtime ts) lib T1 T eq1
    -> per_bar (per_qtime ts) lib T T2 eq2
    -> per_bar (per_qtime ts) lib T1 T2 eq2.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa0; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_right].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact x].
  unfold per_qtime in *; exrepnd.
  computes_to_eqval_ext.
  hide_hyp perb0.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.
  apply cequivc_ext_mkc_qtime_right in ceq0; eauto 3 with slow;[]; repnd.

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  exists eqa2 A1 B; dands; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans2; try exact tsa; eauto.
  { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
      try exact tsa; eauto 3 with slow. }
  { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
      try exact tsa; try exact perb4; eauto 3 with slow. }
Qed.

Lemma per_bar_per_qtime_trans3 {o} :
  forall (ts : cts(o)) lib T T1 T2 A A' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_qtime A')
    -> per_bar (per_qtime ts) lib T1 T eq1
    -> per_bar (per_qtime ts) lib T T2 eq2
    -> per_bar (per_qtime ts) lib T1 T2 eq1.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa1; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_left].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact x].
  unfold per_qtime in *; exrepnd.
  computes_to_eqval_ext.
  hide_hyp perb0.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.
  apply cequivc_ext_mkc_qtime_right in ceq0; eauto 3 with slow;[]; repnd.

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  exists eqa3 A1 B; dands; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans3; try exact tsa; eauto.
  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
      try exact tsa; eauto 3 with slow. }
  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
      try exact tsa; try exact perb4; eauto 3 with slow. }
Qed.

Lemma per_bar_per_qtime_trans4 {o} :
  forall (ts : cts(o)) lib T T1 T2 A A' (eqa : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_qtime A')
    -> per_bar (per_qtime ts) lib T1 T eq1
    -> per_bar (per_qtime ts) lib T T2 eq2
    -> per_bar (per_qtime ts) lib T1 T2 eq2.
Proof.
  introv tsa comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa0; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_right].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact x].
  unfold per_qtime in *; exrepnd.
  computes_to_eqval_ext.
  hide_hyp perb0.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.
  apply cequivc_ext_mkc_qtime_right in ceq0; eauto 3 with slow;[]; repnd.

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  exists eqa2 A1 B; dands; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans4; try exact tsa; eauto.
  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
      try exact tsa; eauto 3 with slow. }
  { apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
      try exact tsa; try exact perb4; eauto 3 with slow. }
Qed.

Lemma ccequivc_ext_qtime {o} :
  forall lib (T T' : @CTerm o) A,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> ccomputes_to_valc_ext lib T' (mkc_qtime A).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans1_per_qtime {o} :
  forall lib ts T T' eq A A' (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_qtime A)
    -> T' ===>(lib) (mkc_qtime A')
    -> in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> (eq <=2=> (per_qtime_eq_bar lib eqa))
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv tsts dou comp1 comp2 cla tsa eqiff.
  introv ee ceq cl.
  repndors; subst.

  {
    dup ceq as c.
    eapply ccequivc_ext_qtime in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_qtime_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qtime1;
      try exact h; try exact comp1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_qtime in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_qtime_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qtime1;
      try exact h; try exact comp2; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_qtime in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    progress dclose_lr; clear cl.
    apply per_bar_per_qtime_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qtime2;
      try exact h; try exact comp1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_qtime in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_qtime_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qtime2;
      try exact h; try exact comp2; eauto 3 with slow.
  }
Qed.

Lemma type_value_respecting_trans_per_bar_per_qtime3 {o} :
  forall lib (ts : cts(o)) T T1 T2 A C (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> ccequivc_ext lib T1 T2
    -> per_bar (per_qtime ts) lib T T1 eq
    -> per_bar (per_qtime ts) lib T T2 eq.
Proof.
  introv tsa comp1 ceqa per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact x].
  unfold per_qtime in *; exrepnd.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.

  exists eqa1 A B; dands; eauto 3 with slow.
  eapply in_ext_ext_type_sys_props_type_value_respecting_trans1; eauto; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans2_per_qtime {o} :
  forall lib ts T T' eq A A' (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_qtime A)
    -> T' ===>(lib) (mkc_qtime A')
    -> in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> (eq <=2=> (per_qtime_eq_bar lib eqa))
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv tsts dou comp1 comp2 cla tsa eqiff.
  introv ee cl ceq.
  repndors; subst.

  {
    dclose_lr.
    apply per_bar_per_qtime_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qtime3; eauto.
  }

  {
    apply in_ext_ext_type_sys_props4_sym in tsa.
    dclose_lr; clear cl.
    apply per_bar_per_qtime_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qtime3; eauto.
  }

  {
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_qtime_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qtime3; try exact tsa; try exact tsb; eauto.
    eapply per_bar_per_qtime_sym_rev; try exact tsa; try exact tsb; auto.
  }

  {
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dclose_lr; clear cl.
    apply per_bar_per_qtime_implies_close.
    eapply type_value_respecting_trans_per_bar_per_qtime3; try exact tsa'; try exact tsb'; eauto.
    eapply per_bar_per_qtime_sym_rev; try exact tsa'; try exact tsb'; auto.
  }
Qed.
