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

Require Export close_util_func.
Require Export close_util1.
Require Export close_util2.


Lemma per_bar_per_func_ext_implies_eq_term_equals_per_func_ext_eq {o} :
  forall inh (ts : cts(o)) lib T T' eq (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) A v B A' v' B',
    ccomputes_to_valc_ext inh lib T (mkc_function A v B)
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x =>
                         forall a a' (e : eqa lib' x a a'),
                           type_sys_props4 inh ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> per_bar inh (per_func_ext inh ts) lib T T' eq
    -> eq <=2=> (per_func_ext_eq inh lib eqa eqb).
Proof.
  introv comp tsa tsb per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per0.

  introv; split; intro h.

  - unfold per_func_ext_eq, per_func_eq.
    apply in_open_bar_ext_dup.
    unfold per_bar_eq in *.
    unfold per_func_ext in *.
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    eapply in_open_bar_ext_comb; try exact h; clear h.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv h per1; exrepnd.
    apply per1 in h; clear per1.

    unfold per_func_ext_eq in h.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; introv.
    unfold per_func_eq in h; exrepnd.

    dup per0 as eqas.
    eapply type_family_ext_implies_in_ext_eqas in eqas;
      try (apply (lib_extends_preserves_in_ext_ext e) in tsa; exact tsa);
      try (eapply lib_extends_preserves_computes_to_valc; try exact z; eauto);
      eauto 3 with slow; simpl in *;[].

    dup per0 as eqbs.
    eapply type_family_ext_implies_in_ext_eqbs in eqbs;
      try (apply (lib_extends_preserves_in_ext_ext e) in tsa; exact tsa);
      try (apply (lib_extends_preserves_in_ext_ext e) in tsb; exact tsb);
      try (eapply lib_extends_preserves_computes_to_valc; try exact xt2; eauto);
      eauto 3 with slow; simpl in *;[].

    pose proof (eqas _ e0) as eqas; simpl in *.
    assert (eqa lib'0 (lib_extends_trans e0 e) a a') as e' by (eapply (lib_per_cond _ _ eqa); eauto).
    dup e1 as f.
    eapply (lib_per_cond _ _ eqa) in f; apply eqas in f.
    pose proof (eqbs _ e0 a a' e' f) as eqbs; simpl in *.

    pose proof (h _ _ f) as h1.
    eapply (lib_per_fam_cond _ _ eqb); apply eqbs; auto.

  - eapply in_open_bar_ext_comb; try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv per1; introv.
    unfold per_func_ext in per1; exrepnd.
    apply per1; clear per1.

    apply (sub_per_per_func_ext_eq _ _ _ e) in h.
    eapply implies_eq_term_equals_per_func_ext_eq; try exact h.

    { apply in_ext_ext_eq_term_equals_sym.
      eapply type_family_ext_implies_in_ext_eqas;
        try exact per0;
        simpl; try unfold raise_ext_per;
          try (apply (lib_extends_preserves_in_ext_ext e) in tsa; exact tsa);
          try (eapply lib_extends_preserves_computes_to_valc; try exact e; eauto);
          eauto 3 with slow. }

    { apply in_ext_ext_eqbs_sym.
      eapply type_family_ext_implies_in_ext_eqbs;
        try exact per0;
        simpl; try unfold raise_ext_per, raise_ext_per_fam;
          try (apply (lib_extends_preserves_in_ext_ext e) in tsb; exact tsb);
          try (apply (lib_extends_preserves_in_ext_ext e) in tsa; exact tsa);
          try (eapply lib_extends_preserves_computes_to_valc; try exact xt; eauto);
          eauto 3 with slow. }
Qed.

Lemma per_bar_per_func_ext_implies_close {o} :
  forall inh (ts : cts(o)) lib T T' eq,
    per_bar inh (per_func_ext inh (close inh ts)) lib T T' eq
    -> close inh ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.
  apply CL_func; auto.
Qed.

Lemma type_value_respecting_trans_per_bar_per_func_ext1 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A v B A' v' B' C w D (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A C (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T1 (mkc_function A' v' B')
    -> ccomputes_to_valc_ext inh lib T (mkc_function A v B)
    -> ccequivc_ext inh lib A A'
    -> bcequivc_ext inh lib [v] B [v'] B'
    -> per_bar inh (per_func_ext inh ts) lib T1 T2 eq
    -> per_bar inh (per_func_ext inh ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_func_ext in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].
  eapply ccomputes_to_valc_ext_monotone in comp2;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  dup per2 as tf.

  eapply type_family_ext_value_respecting_trans1 in tf;
    try exact comp2; try exact comp1; try exact tsb; try exact tsa;
      eauto 3 with slow.
  exists eqa1 eqb0; dands; auto.
Qed.

Lemma type_value_respecting_trans_per_bar_per_func_ext2 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A v B A' v' B' C w D (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A C (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T1 (mkc_function A' v' B')
    -> ccomputes_to_valc_ext inh lib T (mkc_function A v B)
    -> ccequivc_ext inh lib A A'
    -> bcequivc_ext inh lib [v] B [v'] B'
    -> per_bar inh (per_func_ext inh ts) lib T2 T1 eq
    -> per_bar inh (per_func_ext inh ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_func_ext in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].
  eapply ccomputes_to_valc_ext_monotone in comp2;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  dup per2 as tf.

  eapply type_family_ext_value_respecting_trans3 in tf;
    try exact comp2; try exact comp1; try exact tsb; try exact tsa;
      eauto 3 with slow.
  exists eqa1 eqb0; dands; auto.
Qed.

Lemma per_func_ext_eq_sym {o} :
  forall inh ts lib (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) A v B A' v' B' t1 t2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_func_ext_eq inh lib eqa eqb t1 t2
    -> per_func_ext_eq inh lib eqa eqb t2 t1.
Proof.
  introv tsa tsb per.

  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  unfold per_func_ext_eq in *; exrepnd.
  eapply in_open_bar_ext_pres; eauto; clear per; introv per.

  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.
  pose proof (symb _ e) as sym; simpl in *.

  unfold per_func_eq in *; introv.

  apply symb.

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  assert (term_equality_symmetric (eqa lib' e)) as syma by eauto 3 with slow.
  dup e0 as f.
  apply syma in f.
  apply (eqbs _ _ e0 f).
  apply per.
Qed.

Lemma per_func_ext_eq_trans {o} :
  forall inh ts lib (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) A v B A' v' B' t1 t2 t3,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_func_ext_eq inh lib eqa eqb t1 t2
    -> per_func_ext_eq inh lib eqa eqb t2 t3
    -> per_func_ext_eq inh lib eqa eqb t1 t3.
Proof.
  introv tsa tsb pera perb.

  dup tsb as transb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep in transb.

  unfold per_func_ext_eq in *; exrepnd.
  eapply in_open_bar_ext_comb; try exact pera; clear pera.
  eapply in_open_bar_ext_comb; try exact perb; clear perb.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb pera.

  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.
  pose proof (transb _ e) as sym; simpl in *.

  unfold per_func_eq in *; introv.

  eapply transb;[|apply perb].

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  assert (term_equality_symmetric (eqa lib' e)) as syma by eauto 3 with slow.
  assert (term_equality_transitive (eqa lib' e)) as transa by eauto 3 with slow.

  assert (eqa lib' e a a) as f by (eapply transa;[exact e0|]; auto).

  apply (eqbs0 _ _ e0 f).
  apply pera.
Qed.

Hint Resolve sp_implies_ccequivc_ext_apply : slow.

Lemma per_func_ext_eq_resp {o} :
  forall inh ts lib (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) A v B A' v' B' t t',
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_func_ext_eq inh lib eqa eqb t t
    -> ccequivc_ext inh lib t t'
    -> per_func_ext_eq inh lib eqa eqb t t'.
Proof.
  introv tsa tsb per ceq.

  dup tsb as respb.
  dup tsb as transb.
  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_respecting_dep in respb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep in transb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  unfold per_func_ext_eq in *; exrepnd.
  eapply in_open_bar_ext_pres; eauto; clear per; introv per.

  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.
  pose proof (respb _ e) as sym; simpl in *.

  unfold per_func_eq in *; introv.

  assert (term_equality_symmetric (eqa lib' e)) as syma by eauto 3 with slow.
  assert (term_equality_transitive (eqa lib' e)) as transa by eauto 3 with slow.

  assert (eqa lib' e a' a') as f by (eapply transa;[|exact e0]; auto).

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  eapply transb;[apply per|].
  apply respb; eauto 3 with slow.
  apply (eqbs1 _ _ e0 f); auto.
Qed.

Lemma per_bar_per_func_ext_sym {o} :
  forall inh (ts : cts(o)) lib T T' A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_function A v B)
    -> per_bar inh (per_func_ext inh ts) lib T T' eq
    -> per_bar inh (per_func_ext inh ts) lib T' T eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  eapply per_func_ext_sym; try exact comp; eauto.
Qed.

Lemma per_bar_per_func_ext_sym_rev {o} :
  forall inh (ts : cts(o)) lib T T' A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_function A v B)
    -> per_bar inh (per_func_ext inh ts) lib T' T eq
    -> per_bar inh (per_func_ext inh ts) lib T T' eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  eapply per_func_ext_sym_rev; try exact comp; eauto.
Qed.

Lemma per_bar_per_func_ext_trans1 {o} :
  forall inh (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq1 eq2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_function A v B)
    -> per_bar inh (per_func_ext inh ts) lib T1 T eq1
    -> per_bar inh (per_func_ext inh ts) lib T T2 eq2
    -> per_bar inh (per_func_ext inh ts) lib T1 T2 eq1.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  eapply per_func_ext_function_trans1; try exact comp; eauto.
Qed.

Lemma per_bar_per_func_ext_trans2 {o} :
  forall inh (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq1 eq2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_function A v B)
    -> per_bar inh (per_func_ext inh ts) lib T1 T eq1
    -> per_bar inh (per_func_ext inh ts) lib T T2 eq2
    -> per_bar inh (per_func_ext inh ts) lib T1 T2 eq2.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  eapply per_func_ext_function_trans2; try exact comp; eauto.
Qed.

Lemma per_bar_per_func_ext_trans3 {o} :
  forall inh (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq1 eq2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_function A' v' B')
    -> per_bar inh (per_func_ext inh ts) lib T1 T eq1
    -> per_bar inh (per_func_ext inh ts) lib T T2 eq2
    -> per_bar inh (per_func_ext inh ts) lib T1 T2 eq1.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  eapply per_func_ext_function_trans3; try exact comp; eauto.
Qed.

Lemma per_bar_per_func_ext_trans4 {o} :
  forall inh (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq1 eq2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_function A' v' B')
    -> per_bar inh (per_func_ext inh ts) lib T1 T eq1
    -> per_bar inh (per_func_ext inh ts) lib T T2 eq2
    -> per_bar inh (per_func_ext inh ts) lib T1 T2 eq2.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  eapply per_func_ext_function_trans4; try exact comp; eauto.
Qed.

Lemma implies_type_value_respecting_trans1_per_func {o} :
  forall inh lib ts T T' eq A A' v v' B B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> T ===>(inh,lib) (mkc_function A v B)
    -> T' ===>(inh,lib) (mkc_function A' v' B')
    -> in_ext_ext inh lib (fun lib' x => close inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close inh ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh (close inh ts) lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> (eq <=2=> (per_func_ext_eq inh lib eqa eqb))
    -> type_equality_respecting_trans1 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou comp1 comp2 cla tsa clb tsb eqiff.
  introv ee ceq cl.
  repndors; subst.

  {
    dup ceq as c.
    eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_func_ext_implies_close.
    eapply type_value_respecting_trans_per_bar_per_func_ext1;
      try exact h; try exact comp1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_func_ext_implies_close.
    eapply type_value_respecting_trans_per_bar_per_func_ext1;
      try exact h; try exact comp2; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_func_ext_implies_close.
    eapply type_value_respecting_trans_per_bar_per_func_ext2;
      try exact h; try exact comp1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_func_ext_implies_close.
    eapply type_value_respecting_trans_per_bar_per_func_ext2;
      try exact h; try exact comp2; eauto 3 with slow.
  }
Qed.

Lemma type_value_respecting_trans_per_bar_per_func_ext3 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A v B C w D (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A C (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_function A v B)
    -> ccequivc_ext inh lib T1 T2
    -> per_bar inh (per_func_ext inh ts) lib T T1 eq
    -> per_bar inh (per_func_ext inh ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 ceqa per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.

  unfold per_func_ext in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  dup per2 as tf.

  exists eqa1 eqb0; dands; auto.
  eapply type_family_ext_value_respecting_trans5; eauto; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans2_per_func {o} :
  forall inh lib ts T T' eq A A' v v' B B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> T ===>(inh,lib) (mkc_function A v B)
    -> T' ===>(inh,lib) (mkc_function A' v' B')
    -> in_ext_ext inh lib (fun lib' x => close inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close inh ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh (close inh ts) lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> (eq <=2=> (per_func_ext_eq inh lib eqa eqb))
    -> type_equality_respecting_trans2 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou comp1 comp2 cla tsa clb tsb eqiff.
  introv ee cl ceq.
  repndors; subst.

  {
    dclose_lr.
    apply per_bar_per_func_ext_implies_close.
    eapply type_value_respecting_trans_per_bar_per_func_ext3; eauto.
  }

  {
    apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb;[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_func_ext_implies_close.
    eapply type_value_respecting_trans_per_bar_per_func_ext3; eauto.
  }

  {
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb';[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_func_ext_implies_close.
    eapply type_value_respecting_trans_per_bar_per_func_ext3; try exact tsa; try exact tsb; eauto.
    eapply per_bar_per_func_ext_sym_rev; try exact tsa; try exact tsb; auto.
  }

  {
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb';[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_func_ext_implies_close.
    eapply type_value_respecting_trans_per_bar_per_func_ext3; try exact tsa'; try exact tsb'; eauto.
    eapply per_bar_per_func_ext_sym_rev; try exact tsa'; try exact tsb'; auto.
  }
Qed.
