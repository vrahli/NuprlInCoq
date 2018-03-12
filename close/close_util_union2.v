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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys_useful.
Require Export dest_close.
Require Export per_ceq_bar.

Require Export close_util_union.
Require Export close_util1.
Require Export close_util2.


Lemma per_bar_per_union_implies_eq_term_equals_per_union_eq_bar {o} :
  forall (ts : cts(o)) lib T T' eq (eqa eqb : lib-per(lib,o)) A B A' B',
    computes_to_valc lib T (mkc_union A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_bar (per_union ts) lib T T' eq
    -> eq <=2=> (per_union_eq_bar lib eqa eqb).
Proof.
  introv comp tsa tsb per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per1.

  introv; split; intro h.

  - unfold per_union_eq_bar, per_union_eq, per_union_eq_L, per_union_eq_R.
    apply collapse2bars_ext.
    { introv; split; intro q; introv; repndors;[left|right|left|right];
        exrepnd; eexists; eexists; dands; eauto;
          try (apply (lib_per_cond _ eqa lib' x y); eauto);
          try (apply (lib_per_cond _ eqb lib' x y); eauto). }

    exists bar.
    introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *.
    exrepnd.

    apply collapse2bars_ext.
    { introv; split; intro q; introv; repndors;[left|right|left|right];
        exrepnd; eexists; eexists; dands; eauto;
          try (apply (lib_per_cond _ eqa lib'1 (lib_extends_trans y x) (lib_extends_trans x0 x)); eauto);
          try (apply (lib_per_cond _ eqb lib'1 (lib_extends_trans y x) (lib_extends_trans x0 x)); eauto). }

    exists bar'.
    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.

    assert (lib_extends lib'2 lib') as xt1 by eauto 3 with slow.
    pose proof (per0 _ br lib'2 xt1 (lib_extends_trans x0 x)) as per0; simpl in *.
    unfold per_union in per0; exrepnd.
    apply per0 in h0; clear per0.
    unfold per_union_eq_bar, per_union_eq, per_union_eq_L, per_union_eq_R in h0; exrepnd.

    exists bar0.
    introv br'' ext''; introv.
    pose proof (h1 _ br'' _ ext'' x1) as h1; simpl in *.

    assert (lib_extends lib'2 lib) as xt2 by eauto 3 with slow.

    spcast.
    apply (lib_extends_preserves_computes_to_valc _ _ xt2) in comp.
    computes_to_eqval.

    dup per3 as eqas.
    eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 _ xt2) in eqas;[|exact tsa].

    dup per4 as eqbs.
    eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 _ xt2) in eqbs;[|exact tsb].

    repndors; exrepnd;[left|right]; eexists; eexists; dands; eauto.

    { eapply (lib_per_cond _ eqa); apply (eqas _ x1); auto. }

    { eapply (lib_per_cond _ eqb); apply (eqbs _ x1); auto. }

  - introv br ext; introv.
    exists (raise_bar bar x); introv br' ext'; introv; simpl in *; exrepnd.
    pose proof (per0 _ br'1 lib'2 (lib_extends_trans ext' br'2) (lib_extends_trans x0 x)) as per0; simpl in *.
    unfold per_union in per0; exrepnd; spcast.
    apply (lib_extends_preserves_computes_to_valc _ _ (lib_extends_trans x0 x)) in comp.
    computes_to_eqval.
    apply per0.

    assert (lib_extends lib'2 lib) as xt by eauto 3 with slow.

    dup per3 as eqas.
    eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 _ (lib_extends_trans x0 x)) in eqas;[|exact tsa].

    dup per4 as eqbs.
    eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 _ (lib_extends_trans x0 x)) in eqbs;[|exact tsb].

    apply (sub_per_per_union_eq_bar _ _ (lib_extends_trans x0 x)) in h.
    eapply (implies_eq_term_equals_per_union_bar _ (trivial_bar lib'2));[| |eauto];
      apply in_ext_ext_implies_all_in_bar_ext_trivial_bar; introv; simpl;
        unfold raise_ext_per; eauto.
Qed.

Lemma per_bar_per_union_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_union (close ts)) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  apply CL_union; auto.
Qed.

Lemma ccequivc_ext_union {o} :
  forall lib (T T' : @CTerm o) A B,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_union A B)
    -> {A' : CTerm , {B' : CTerm ,
        ccomputes_to_valc lib T' (mkc_union A' B')
        # ccequivc_ext lib A A'
        # ccequivc_ext lib B B' }}.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_mkc_union in ceq';[|eauto]; exrepnd.
  exists a' b'; dands; spcast; auto.

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_union A B) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_union a' b') ceq'0) as z.
    eapply cequivc_mkc_union in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_union A B) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_union a' b') ceq'0) as z.
    eapply cequivc_mkc_union in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }
Qed.

Lemma type_value_respecting_trans_per_bar_per_union1 {o} :
  forall lib (ts : cts(o)) T T1 T2 A B A' B' C D (eqa eqb : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B D (eqb lib' x))
    -> computes_to_valc lib T1 (mkc_union A' B')
    -> computes_to_valc lib T (mkc_union A B)
    -> ccequivc_ext lib A A'
    -> ccequivc_ext lib B B'
    -> per_bar (per_union ts) lib T1 T2 eq
    -> per_bar (per_union ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  unfold per_union in *; exrepnd.

  eapply lib_extends_preserves_computes_to_valc in comp1;[|exact x].
  eapply lib_extends_preserves_computes_to_valc in comp2;[|exact x].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsb.

  spcast; computes_to_eqval.

  exists eqa1 eqb0 A A2 B B2; dands; spcast; auto;
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans1; eauto; eauto 3 with slow.
Qed.

Lemma type_value_respecting_trans_per_bar_per_union2 {o} :
  forall lib (ts : cts(o)) T T1 T2 A B A' B' C D (eqa eqb : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B D (eqb lib' x))
    -> computes_to_valc lib T1 (mkc_union A' B')
    -> computes_to_valc lib T (mkc_union A B)
    -> ccequivc_ext lib A A'
    -> ccequivc_ext lib B B'
    -> per_bar (per_union ts) lib T2 T1 eq
    -> per_bar (per_union ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  unfold per_union in *; exrepnd.

  eapply lib_extends_preserves_computes_to_valc in comp1;[|exact x].
  eapply lib_extends_preserves_computes_to_valc in comp2;[|exact x].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsb.

  spcast; computes_to_eqval.

  exists eqa1 eqb0 A A1 B B1; dands; spcast; auto;
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans2; eauto; eauto 3 with slow.
Qed.

Lemma per_union_sym {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' B B' equ (eqa eqb : lib-per(lib,o)),
    computes_to_valc lib T1 (mkc_union A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T1 T2 equ
    -> per_union ts lib T2 T1 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_union in *; exrepnd.
  spcast; computes_to_eqval.
  exists eqa0 eqb0 A2 A B2 B; dands; spcast; auto;
    eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
Qed.

Lemma per_union_sym_rev {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' B B' equ (eqa eqb : lib-per(lib,o)),
    computes_to_valc lib T1 (mkc_union A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T2 T1 equ
    -> per_union ts lib T1 T2 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_union in *; exrepnd.
  spcast; computes_to_eqval.
  exists eqa0 eqb0 A A1 B B1; dands; spcast; auto;
    eapply in_ext_ext_type_sys_props4_in_ext_ext_sym_rev; eauto.
Qed.

Lemma per_bar_per_union_sym {o} :
  forall (ts : cts(o)) lib T T' A B A' B' (eqa eqb : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> computes_to_valc lib T (mkc_union A B)
    -> per_bar (per_union ts) lib T T' eq
    -> per_bar (per_union ts) lib T' T eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsb.

  eapply per_union_sym; try exact comp; eauto.
Qed.

Lemma per_bar_per_union_sym_rev {o} :
  forall (ts : cts(o)) lib T T' A B A' B' (eqa eqb : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> computes_to_valc lib T (mkc_union A B)
    -> per_bar (per_union ts) lib T' T eq
    -> per_bar (per_union ts) lib T T' eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsb.

  eapply per_union_sym_rev; try exact comp; eauto.
Qed.

Lemma per_union_trans1 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa eqb : lib-per(lib,o)) A B A' B',
    computes_to_valc lib T (mkc_union A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T T2 eq2
    -> per_union ts lib T1 T eq1
    -> per_union ts lib T1 T2 eq1.
Proof.
  introv comp tsa tsb pera perb.
  unfold per_union in *; exrepnd.
  spcast.
  repeat computes_to_eqval.
  exists eqa0 eqb0 A1 A3 B1 B3; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans1; try exact tsa; eauto. }
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans1; try exact tsb; eauto. }
Qed.

Lemma per_union_trans2 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa eqb : lib-per(lib,o)) A B A' B',
    computes_to_valc lib T (mkc_union A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T T2 eq2
    -> per_union ts lib T1 T eq1
    -> per_union ts lib T1 T2 eq2.
Proof.
  introv comp tsa tsb pera perb.
  unfold per_union in *; exrepnd.
  spcast.
  repeat computes_to_eqval.
  exists eqa1 eqb1 A1 A3 B1 B3; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans2; try exact tsa; eauto. }
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans2; try exact tsb; eauto. }
Qed.

Lemma per_union_trans3 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa eqb : lib-per(lib,o)) A B A' B',
    computes_to_valc lib T (mkc_union A' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T T2 eq2
    -> per_union ts lib T1 T eq1
    -> per_union ts lib T1 T2 eq1.
Proof.
  introv comp tsa tsb pera perb.
  unfold per_union in *; exrepnd.
  spcast.
  repeat computes_to_eqval.
  exists eqa0 eqb0 A1 A3 B1 B3; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans3; try exact tsa; eauto. }
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans3; try exact tsb; eauto. }
Qed.

Lemma per_union_trans4 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa eqb : lib-per(lib,o)) A B A' B',
    computes_to_valc lib T (mkc_union A' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T T2 eq2
    -> per_union ts lib T1 T eq1
    -> per_union ts lib T1 T2 eq2.
Proof.
  introv comp tsa tsb pera perb.
  unfold per_union in *; exrepnd.
  spcast.
  repeat computes_to_eqval.
  exists eqa1 eqb1 A1 A3 B1 B3; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans4; try exact tsa; eauto. }
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans4; try exact tsb; eauto. }
Qed.

Lemma per_bar_per_union_trans1 {o} :
  forall (ts : cts(o)) lib T T1 T2 A B A' B' (eqa eqb : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> computes_to_valc lib T (mkc_union A B)
    -> per_bar (per_union ts) lib T1 T eq1
    -> per_bar (per_union ts) lib T T2 eq2
    -> per_bar (per_union ts) lib T1 T2 eq1.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa1; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_left].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsb.

  eapply per_union_trans1; try exact comp; eauto.
Qed.

Lemma per_bar_per_union_trans2 {o} :
  forall (ts : cts(o)) lib T T1 T2 A B A' B' (eqa eqb : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> computes_to_valc lib T (mkc_union A B)
    -> per_bar (per_union ts) lib T1 T eq1
    -> per_bar (per_union ts) lib T T2 eq2
    -> per_bar (per_union ts) lib T1 T2 eq2.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa0; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_right].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsb.

  eapply per_union_trans2; try exact comp; eauto.
Qed.

Lemma per_bar_per_union_trans3 {o} :
  forall (ts : cts(o)) lib T T1 T2 A B A' B' (eqa eqb : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> computes_to_valc lib T (mkc_union A' B')
    -> per_bar (per_union ts) lib T1 T eq1
    -> per_bar (per_union ts) lib T T2 eq2
    -> per_bar (per_union ts) lib T1 T2 eq1.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa1; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_left].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsb.

  eapply per_union_trans3; try exact comp; eauto.
Qed.

Lemma per_bar_per_union_trans4 {o} :
  forall (ts : cts(o)) lib T T1 T2 A B A' B' (eqa eqb : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> computes_to_valc lib T (mkc_union A' B')
    -> per_bar (per_union ts) lib T1 T eq1
    -> per_bar (per_union ts) lib T T2 eq2
    -> per_bar (per_union ts) lib T1 T2 eq2.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists (intersect_bars bar0 bar) eqa0; dands; auto;
    [|eapply eq_term_equals_trans;[eauto|];
      apply eq_term_equals_sym;
      apply per_bar_eq_intersect_bars_right].
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsb.

  eapply per_union_trans4; try exact comp; eauto.
Qed.
