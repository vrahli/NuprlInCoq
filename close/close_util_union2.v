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


Lemma per_bar_per_union_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_union (close ts)) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.
  apply CL_union; auto.
Qed.

Lemma ccequivc_ext_union {o} :
  forall lib (T T' : @CTerm o) A B,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> ccomputes_to_valc_ext lib T' (mkc_union A B).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma per_bar_per_union_implies_eq_term_equals_per_union_eq_bar {o} :
  forall (ts : cts(o)) lib T T' eq (eqa eqb : lib-per(lib,o)) A B A' B',
    ccomputes_to_valc_ext lib T (mkc_union A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_bar (per_union ts) lib T T' eq
    -> eq <=2=> (per_union_eq_bar lib eqa eqb).
Proof.
  introv comp tsa tsb per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per0.

  introv; split; intro h.

  - unfold per_union_eq_bar, per_union_eq.
    apply e_all_in_ex_bar_ext_as.
    apply in_open_bar_ext_dup.
    unfold per_bar_eq in *.
    unfold per_union in *.
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    eapply in_open_bar_ext_comb; try exact h; clear h.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv h per1; exrepnd.
    apply per1 in h; clear per1.

    unfold per_union_eq_bar, per_union in h; apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; introv.

    eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_union_right in ceq; repnd.

    dup per3 as eqas.
    eapply (in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 _ e) in eqas;
      [|exact tsa|]; eauto 3 with slow;[].

    dup per4 as eqbs.
    eapply (in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 _ e) in eqbs;
      [|exact tsb|]; eauto 3 with slow;[].

    unfold per_union_eq, per_union_eq_L, per_union_eq_R in *.
    repndors; exrepnd;[left|right]; eexists; eexists; dands; eauto.

    { eapply (lib_per_cond _ eqa); apply (eqas _ e0); auto. }

    { eapply (lib_per_cond _ eqb); apply (eqbs _ e0); auto. }

  - eapply in_open_bar_ext_comb; try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv per1; introv.
    unfold per_union in per1; exrepnd.
    apply per1; clear per1.

    eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_union_right in ceq; repnd.

    dup per3 as eqas.
    eapply (in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 _ e) in eqas;
      [|exact tsa|]; eauto 3 with slow;[].

    dup per4 as eqbs.
    eapply (in_ext_ext_type_sys_props4_ccequivc_ext_implies_in_ext_ext_eq_term_equals4 _ e) in eqbs;
      [|exact tsb|]; eauto 3 with slow;[].

    apply (sub_per_per_union_eq_bar _ _ e) in h.
    eapply implies_eq_term_equals_per_union_bar; try exact h; simpl;
      apply in_ext_ext_implies_in_open_bar_ext; introv; simpl;
        unfold raise_ext_per; eauto.
Qed.

Lemma type_value_respecting_trans_per_bar_per_union1 {o} :
  forall lib (ts : cts(o)) T T1 T2 A B A' B' C D (eqa eqb : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B D (eqb lib' x))
    -> ccomputes_to_valc_ext lib T1 (mkc_union A' B')
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> ccequivc_ext lib A A'
    -> ccequivc_ext lib B B'
    -> per_bar (per_union ts) lib T1 T2 eq
    -> per_bar (per_union ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_union in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].
  eapply ccomputes_to_valc_ext_monotone in comp2;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsb.

  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_union_right in ceq; repnd.

  exists eqa1 eqb0 A A2 B B2; dands; spcast; auto;
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans1; eauto; eauto 3 with slow.
Qed.

Lemma type_value_respecting_trans_per_bar_per_union2 {o} :
  forall lib (ts : cts(o)) T T1 T2 A B A' B' C D (eqa eqb : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B D (eqb lib' x))
    -> ccomputes_to_valc_ext lib T1 (mkc_union A' B')
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> ccequivc_ext lib A A'
    -> ccequivc_ext lib B B'
    -> per_bar (per_union ts) lib T2 T1 eq
    -> per_bar (per_union ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_union in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].
  eapply ccomputes_to_valc_ext_monotone in comp2;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsb.

  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_union_right in ceq; repnd.

  exists eqa1 eqb0 A A1 B B1; dands; spcast; auto;
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans2; eauto; eauto 3 with slow.
Qed.

Lemma per_union_sym {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' B B' equ (eqa eqb : lib-per(lib,o)),
    ccomputes_to_valc_ext lib T1 (mkc_union A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T1 T2 equ
    -> per_union ts lib T2 T1 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_union in *; exrepnd.
  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_union_right in ceq; repnd.
  exists eqa0 eqb0 A2 A B2 B; dands; spcast; auto;
    eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto;
      try (complete (eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
                     try exact tspa; eauto; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
                     try exact tspb; eauto; eauto 3 with slow)).
Qed.

Lemma per_union_sym_rev {o} :
  forall ts lib (T1 T2 : @CTerm o) A A' B B' equ (eqa eqb : lib-per(lib,o)),
    ccomputes_to_valc_ext lib T1 (mkc_union A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T2 T1 equ
    -> per_union ts lib T1 T2 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_union in *; exrepnd.
  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_union_right in ceq; repnd.

  exists eqa0 eqb0 A A1 B B1; dands; spcast; auto;
    try (complete (eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
                   try exact tspa; eauto; eauto 3 with slow));
    try (complete (eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
                   try exact tspb; eauto; eauto 3 with slow)).
Qed.

Lemma per_bar_per_union_sym {o} :
  forall (ts : cts(o)) lib T T' A B A' B' (eqa eqb : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> per_bar (per_union ts) lib T T' eq
    -> per_bar (per_union ts) lib T' T eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsb.

  eapply per_union_sym; try exact comp; eauto.
Qed.

Lemma per_bar_per_union_sym_rev {o} :
  forall (ts : cts(o)) lib T T' A B A' B' (eqa eqb : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> per_bar (per_union ts) lib T' T eq
    -> per_bar (per_union ts) lib T T' eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsb.

  eapply per_union_sym_rev; try exact comp; eauto.
Qed.

Lemma per_union_trans1 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa eqb : lib-per(lib,o)) A B A' B',
    ccomputes_to_valc_ext lib T (mkc_union A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T T2 eq2
    -> per_union ts lib T1 T eq1
    -> per_union ts lib T1 T2 eq1.
Proof.
  introv comp tsa tsb pera perb.
  unfold per_union in *; exrepnd.

  computes_to_eqval_ext.
  hide_hyp pera0.
  computes_to_eqval_ext.
  hide_hyp perb2.
  apply cequivc_ext_mkc_union_right in ceq; repnd.
  apply cequivc_ext_mkc_union_right in ceq0; repnd.

  exists eqa0 eqb0 A1 A3 B1 B3; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans1; try exact tsa; eauto.
    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans1; try exact tsb; eauto.
    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsb; try exact perb4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsb; try exact pera4; eauto 3 with slow. }
  }
Qed.

Lemma per_union_trans2 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa eqb : lib-per(lib,o)) A B A' B',
    ccomputes_to_valc_ext lib T (mkc_union A B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T T2 eq2
    -> per_union ts lib T1 T eq1
    -> per_union ts lib T1 T2 eq2.
Proof.
  introv comp tsa tsb pera perb.
  unfold per_union in *; exrepnd.

  computes_to_eqval_ext.
  hide_hyp pera0.
  computes_to_eqval_ext.
  hide_hyp perb2.
  apply cequivc_ext_mkc_union_right in ceq; repnd.
  apply cequivc_ext_mkc_union_right in ceq0; repnd.

  exists eqa1 eqb1 A1 A3 B1 B3; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans2; try exact tsa; eauto.
    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans2; try exact tsb; eauto.
    { eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsb; try exact perb4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsb; try exact pera4; eauto 3 with slow. }
  }
Qed.

Lemma per_union_trans3 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa eqb : lib-per(lib,o)) A B A' B',
    ccomputes_to_valc_ext lib T (mkc_union A' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T T2 eq2
    -> per_union ts lib T1 T eq1
    -> per_union ts lib T1 T2 eq1.
Proof.
  introv comp tsa tsb pera perb.
  unfold per_union in *; exrepnd.

  computes_to_eqval_ext.
  hide_hyp pera0.
  computes_to_eqval_ext.
  hide_hyp perb2.
  apply cequivc_ext_mkc_union_right in ceq; repnd.
  apply cequivc_ext_mkc_union_right in ceq0; repnd.

  exists eqa0 eqb0 A1 A3 B1 B3; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans3; try exact tsa; eauto.
    { apply in_ext_ext_type_sys_props4_sym in tsa.
      eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }
    { apply in_ext_ext_type_sys_props4_sym in tsa.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans3; try exact tsb; eauto.
    { apply in_ext_ext_type_sys_props4_sym in tsb.
      eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsb; try exact perb4; eauto 3 with slow. }
    { apply in_ext_ext_type_sys_props4_sym in tsb.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsb; try exact pera4; eauto 3 with slow. }
  }
Qed.

Lemma per_union_trans4 {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2 (eqa eqb : lib-per(lib,o)) A B A' B',
    ccomputes_to_valc_ext lib T (mkc_union A' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> per_union ts lib T T2 eq2
    -> per_union ts lib T1 T eq1
    -> per_union ts lib T1 T2 eq2.
Proof.
  introv comp tsa tsb pera perb.
  unfold per_union in *; exrepnd.

  computes_to_eqval_ext.
  hide_hyp pera0.
  computes_to_eqval_ext.
  hide_hyp perb2.
  apply cequivc_ext_mkc_union_right in ceq; repnd.
  apply cequivc_ext_mkc_union_right in ceq0; repnd.

  exists eqa1 eqb1 A1 A3 B1 B3; dands; spcast; auto.
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans4; try exact tsa; eauto.
    { apply in_ext_ext_type_sys_props4_sym in tsa.
      eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsa; try exact perb3; eauto 3 with slow. }
    { apply in_ext_ext_type_sys_props4_sym in tsa.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsa; try exact pera3; eauto 3 with slow. }
  }
  { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_trans4; try exact tsb; eauto.
    { apply in_ext_ext_type_sys_props4_sym in tsb.
      eapply in_ext_ext_type_sys_props4_in_ext_ext_sym; eauto.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans2;
        try exact tsb; try exact perb4; eauto 3 with slow. }
    { apply in_ext_ext_type_sys_props4_sym in tsb.
      eapply in_ext_ext_type_sys_props_type_value_respecting_trans1;
        try exact tsb; try exact pera4; eauto 3 with slow. }
  }
Qed.

Lemma per_bar_per_union_trans1 {o} :
  forall (ts : cts(o)) lib T T1 T2 A B A' B' (eqa eqb : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> per_bar (per_union ts) lib T1 T eq1
    -> per_bar (per_union ts) lib T T2 eq2
    -> per_bar (per_union ts) lib T1 T2 eq1.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsb.

  eapply per_union_trans1; try exact comp; eauto.
Qed.

Lemma per_bar_per_union_trans2 {o} :
  forall (ts : cts(o)) lib T T1 T2 A B A' B' (eqa eqb : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> per_bar (per_union ts) lib T1 T eq1
    -> per_bar (per_union ts) lib T T2 eq2
    -> per_bar (per_union ts) lib T1 T2 eq2.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsb.

  eapply per_union_trans2; try exact comp; eauto.
Qed.

Lemma per_bar_per_union_trans3 {o} :
  forall (ts : cts(o)) lib T T1 T2 A B A' B' (eqa eqb : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_union A' B')
    -> per_bar (per_union ts) lib T1 T eq1
    -> per_bar (per_union ts) lib T T2 eq2
    -> per_bar (per_union ts) lib T1 T2 eq1.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsb.

  eapply per_union_trans3; try exact comp; eauto.
Qed.

Lemma per_bar_per_union_trans4 {o} :
  forall (ts : cts(o)) lib T T1 T2 A B A' B' (eqa eqb : lib-per(lib,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_union A' B')
    -> per_bar (per_union ts) lib T1 T eq1
    -> per_bar (per_union ts) lib T T2 eq2
    -> per_bar (per_union ts) lib T1 T2 eq2.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsb.

  eapply per_union_trans4; try exact comp; eauto.
Qed.

Lemma implies_type_value_respecting_trans1_per_union {o} :
  forall ts lib T T' eq A1 A2 B1 B2 (eqa eqb : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_union A1 B1)
    -> T' ===>( lib) (mkc_union A2 B2)
    -> in_ext_ext lib (fun lib' x => close ts lib' A1 A2 (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A1 A2 (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => close ts lib' B1 B2 (eqb lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' B1 B2 (eqb lib' x))
    -> (eq <=2=> (per_union_eq_bar lib eqa eqb))
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv tysys dou c1 c2 cla tsa clb tsb eqiff.
  introv h ceq cl.
  repndors; subst.

  {
    dup ceq as c.
    eapply ccequivc_ext_union in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_union_implies_close.
    eapply type_value_respecting_trans_per_bar_per_union1;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_union in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_union_implies_close.
    eapply type_value_respecting_trans_per_bar_per_union1;
      try exact h; try exact c2; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_union in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsb'.
    dclose_lr; clear cl.
    apply per_bar_per_union_implies_close.
    eapply type_value_respecting_trans_per_bar_per_union2;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_union in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsb'.
    dclose_lr; clear cl.
    apply per_bar_per_union_implies_close.
    eapply type_value_respecting_trans_per_bar_per_union2;
      try exact h; try exact c2; eauto 3 with slow.
  }
Qed.

Lemma type_value_respecting_trans_per_bar_per_union3 {o} :
  forall lib (ts : cts(o)) T T1 T2 A B A' B' (eqa eqb : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> ccequivc_ext lib T1 T2
    -> per_bar (per_union ts) lib T T1 eq
    -> per_bar (per_union ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 ceqa per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_union in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsb.

  spcast; computes_to_eqval_ext.
  apply cequivc_ext_mkc_union_right in ceq; repnd.

  exists eqa1 eqb0 A A2 B B2; dands; spcast; auto; eauto 3 with slow;
    eapply in_ext_ext_type_sys_props_type_value_respecting_trans1; eauto; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans2_per_union {o} :
  forall ts lib T T' eq A1 A2 B1 B2 (eqa eqb : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_union A1 B1)
    -> T' ===>( lib) (mkc_union A2 B2)
    -> in_ext_ext lib (fun lib' x => close ts lib' A1 A2 (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A1 A2 (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => close ts lib' B1 B2 (eqb lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' B1 B2 (eqb lib' x))
    -> (eq <=2=> (per_union_eq_bar lib eqa eqb))
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv tysys dou c1 c2 cla tsa clb tsb eqiff.
  introv h cl ceq.
  repndors; subst.

  {
    dclose_lr; clear cl.
    apply per_bar_per_union_implies_close.
    eapply type_value_respecting_trans_per_bar_per_union3;
      try exact h; try exact c1; eauto 3 with slow.
  }

  {
    apply in_ext_ext_type_sys_props4_sym in tsa.
    apply in_ext_ext_type_sys_props4_sym in tsb.
    dclose_lr; clear cl.
    apply per_bar_per_union_implies_close.
    eapply type_value_respecting_trans_per_bar_per_union3;
      try exact h; try exact c2; eauto 3 with slow.
  }

  {
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsb'.
    dclose_lr; clear cl.
    apply per_bar_per_union_implies_close.
    eapply type_value_respecting_trans_per_bar_per_union3;
      try exact c1; try exact tsa; try exact tsb; eauto 3 with slow.
    eapply per_bar_per_union_sym_rev; try exact c1; try exact tsa; try exact tsb; auto.
  }

  {
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsb'.
    dclose_lr; clear cl.
    apply per_bar_per_union_implies_close.
    eapply type_value_respecting_trans_per_bar_per_union3;
      try exact c2; try exact tsa'; try exact tsb'; eauto 3 with slow.
    eapply per_bar_per_union_sym_rev; try exact c2; try exact tsa'; try exact tsb'; auto.
  }
Qed.
