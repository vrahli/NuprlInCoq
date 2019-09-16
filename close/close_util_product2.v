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

Require Export close_util_product.
Require Export close_util1.
Require Export close_util2.


Lemma per_bar_per_product_bar_implies_eq_term_equals_per_product_bar_eq {o} :
  forall (ts : cts(o)) lib T T' eq (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B',
    ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a a' (e : eqa lib' x a a'),
                           type_sys_props4 ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> per_bar (per_product_bar ts) lib T T' eq
    -> eq <=2=> (per_product_eq_bar lib eqa eqb).
Proof.
  introv comp tsa tsb per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per0.

  introv; split; intro h.

  - unfold per_product_eq_bar, per_product_eq.
    apply e_all_in_ex_bar_ext_as.
    apply in_open_bar_ext_dup.
    unfold per_bar_eq in *.
    unfold per_product_bar in *.
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    eapply in_open_bar_ext_comb; try exact h; clear h.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv h per1; exrepnd.
    apply per1 in h; clear per1.

    unfold per_product_eq_bar in h; apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; introv.
    unfold per_product_eq in h; exrepnd.

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
    assert (eqa lib'0 (lib_extends_trans e0 e) a a') as e' by (apply eqas; auto).
    assert (eqa lib'0 z a a') as e'' by (eapply (lib_per_cond _ eqa); eauto).
    pose proof (eqbs _ e0 a a' e' e1) as eqbs; simpl in *.

    exists a a' b b' e''; dands; auto.
    eapply (lib_per_fam_cond _ eqb); apply eqbs; auto.

  - eapply in_open_bar_ext_comb; try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv per1; introv.
    unfold per_product_bar in per1; exrepnd.
    apply per1; clear per1.

    apply (sub_per_per_product_bar_eq _ _ e) in h.
    eapply implies_eq_term_equals_per_product_eq_bar; try exact h.

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

Lemma per_bar_per_product_bar_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_product_bar (close ts)) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.
  apply CL_product; auto.
Qed.

Lemma type_value_respecting_trans_per_bar_per_product_bar1 {o} :
  forall lib (ts : cts(o)) T T1 T2 A v B A' v' B' C w D (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T1 (mkc_product A' v' B')
    -> ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> ccequivc_ext lib A A'
    -> bcequivc_ext lib [v] B [v'] B'
    -> per_bar (per_product_bar ts) lib T1 T2 eq
    -> per_bar (per_product_bar ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_product_bar in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].
  eapply ccomputes_to_valc_ext_monotone in comp2;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ e) in tsb.

  dup per2 as tf.

  eapply type_family_ext_value_respecting_trans1 in tf;
    try exact comp2; try exact comp1; try exact tsb; try exact tsa;
      eauto 3 with slow.
  exists eqa1 eqb0; dands; auto.
Qed.

Lemma type_value_respecting_trans_per_bar_per_product_bar2 {o} :
  forall lib (ts : cts(o)) T T1 T2 A v B A' v' B' C w D (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T1 (mkc_product A' v' B')
    -> ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> ccequivc_ext lib A A'
    -> bcequivc_ext lib [v] B [v'] B'
    -> per_bar (per_product_bar ts) lib T2 T1 eq
    -> per_bar (per_product_bar ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_product_bar in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].
  eapply ccomputes_to_valc_ext_monotone in comp2;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ e) in tsb.

  dup per2 as tf.

  eapply type_family_ext_value_respecting_trans3 in tf;
    try exact comp2; try exact comp1; try exact tsb; try exact tsa;
      eauto 3 with slow.
  exists eqa1 eqb0; dands; auto.
Qed.

Lemma per_product_eq_bar_sym {o} :
  forall ts lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B' t1 t2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_product_eq_bar lib eqa eqb t1 t2
    -> per_product_eq_bar lib eqa eqb t2 t1.
Proof.
  introv tsa tsb per.

  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  unfold per_product_eq_bar in *; exrepnd.
  apply e_all_in_ex_bar_ext_as in per; apply e_all_in_ex_bar_ext_as.
  eapply in_open_bar_ext_pres; eauto; clear per; introv per.

  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.
  pose proof (symb _ e) as sym; simpl in *.

  unfold per_product_eq in *; introv.
  exrepnd.

  assert (term_equality_symmetric (eqa lib' e)) as syma by eauto 3 with slow.
  dup e0 as f.
  apply syma in f.

  exists a' a b' b f; dands; auto.

  apply symb.

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  apply (eqbs _ _ e0 f); auto.
Qed.

Lemma per_product_eq_bar_trans {o} :
  forall ts lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B' t1 t2 t3,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_product_eq_bar lib eqa eqb t1 t2
    -> per_product_eq_bar lib eqa eqb t2 t3
    -> per_product_eq_bar lib eqa eqb t1 t3.
Proof.
  introv tsa tsb pera perb.

  dup tsb as transb.
  dup tsb as respb.
  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep in transb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_respecting_dep in respb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  unfold per_product_eq_bar in *; exrepnd.
  apply e_all_in_ex_bar_ext_as in pera; apply e_all_in_ex_bar_ext_as in perb; apply e_all_in_ex_bar_ext_as.
  eapply in_open_bar_ext_comb; try exact perb; clear perb.
  eapply in_open_bar_ext_comb; try exact pera; clear pera.
  apply in_ext_ext_implies_in_open_bar_ext; introv pera perb.

  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.
  pose proof (transb _ e) as sym; simpl in *.

  unfold per_product_eq in *; introv.
  exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_pair_pair_implies in ceq; repnd.

  assert (term_equality_symmetric (eqa lib' e)) as syma by eauto 3 with slow.
  assert (term_equality_transitive (eqa lib' e)) as transa by eauto 3 with slow.
  assert (term_equality_respecting lib' (eqa lib' e)) as respa by eauto 3 with slow.

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  assert (eqa lib' e a0 a') as f.
  {
    eapply transa;[|exact e0].
    eapply transa;[exact e1|].
    eapply respa; eauto 3 with slow.
  }
  exists a0 a' b0 b' f.
  dands; spcast; auto.

  assert (eqa lib' e a'0 a'0) as g by (eapply transa; eauto).
  assert (eqa lib' e a0 a0) as h by (eapply transa; eauto).
  assert (eqa lib' e a' a') as k by (eapply transa; eauto).

  eapply transb;[apply (eqbs0 _ _ f h);apply (eqbs0 _ _ e1 h);exact pera0|].
  apply (eqbs1 _ _ f k); apply (eqbs1 _ _ e0 k); auto.
  eapply transb;[|exact perb0].
  eapply respb; eauto 3 with slow.
  apply (eqbs1 _ _ e0 k); apply (eqbs1 _ _ f k); auto.
  apply (eqbs0 _ _ f h); apply (eqbs0 _ _ e1 h); auto.
  eapply transb;[|exact pera0].
  apply symb; auto.
Qed.

Lemma type_sys_props4_implies_term_equality_respecting {o} :
  forall (lib : library) (ts : cts(o)) (A B : CTerm) (eqa : per(o)),
    type_sys_props4 ts lib A B eqa -> term_equality_respecting lib eqa.
Proof.
  introv tsp.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve type_sys_props4_implies_term_equality_respecting : slow.

Lemma per_product_eq_bar_resp {o} :
  forall ts lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B' t t',
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_product_eq_bar lib eqa eqb t t
    -> ccequivc_ext lib t t'
    -> per_product_eq_bar lib eqa eqb t t'.
Proof.
  introv tsa tsb per ceq.

  dup tsb as respb.
  dup tsb as transb.
  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_respecting_dep in respb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep in transb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  unfold per_product_eq_bar in *; exrepnd.
  apply e_all_in_ex_bar_ext_as in per; apply e_all_in_ex_bar_ext_as.
  eapply in_open_bar_ext_pres; eauto; clear per; introv per.

  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.
  pose proof (respb _ e) as sym; simpl in *.

  unfold per_product_eq in *; introv.
  exrepnd.
  computes_to_eqval_ext.
  apply ccequivc_ext_pair_pair_implies in ceq0; repnd.

  dup per1 as c.
  eapply (ccequivc_ext_pair _ t t') in c; eauto 3 with slow; exrepnd; spcast.

  assert (term_equality_symmetric (eqa lib' e)) as syma by eauto 3 with slow.
  assert (term_equality_transitive (eqa lib' e)) as transa by eauto 3 with slow.
  assert (term_equality_respecting lib' (eqa lib' e)) as respa by eauto 3 with slow.

  assert (eqa lib' e a a) as f.
  { eapply transa; eauto 3 with slow. }

  exists a a b b f; dands; spcast; auto.

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  apply (eqbs0 _ _ e0 f).
  eapply transb; eauto; apply symb; auto.
Qed.

Lemma per_bar_per_product_bar_sym {o} :
  forall (ts : cts(o)) lib T T' A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> per_bar (per_product_bar ts) lib T T' eq
    -> per_bar (per_product_bar ts) lib T' T eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ e) in tsb.

  eapply per_product_bar_sym; try exact comp; eauto.
Qed.

Lemma per_bar_per_product_bar_sym_rev {o} :
  forall (ts : cts(o)) lib T T' A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> per_bar (per_product_bar ts) lib T' T eq
    -> per_bar (per_product_bar ts) lib T T' eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ e) in tsb.

  eapply per_product_bar_sym_rev; try exact comp; eauto.
Qed.

Lemma per_bar_per_product_bar_trans1 {o} :
  forall (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> per_bar (per_product_bar ts) lib T1 T eq1
    -> per_bar (per_product_bar ts) lib T T2 eq2
    -> per_bar (per_product_bar ts) lib T1 T2 eq1.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ e) in tsb.

  eapply per_product_bar_trans1; try exact comp; eauto.
Qed.

Lemma per_bar_per_product_bar_trans2 {o} :
  forall (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> per_bar (per_product_bar ts) lib T1 T eq1
    -> per_bar (per_product_bar ts) lib T T2 eq2
    -> per_bar (per_product_bar ts) lib T1 T2 eq2.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ e) in tsb.

  eapply per_product_bar_trans2; try exact comp; eauto.
Qed.

Lemma per_bar_per_product_bar_trans3 {o} :
  forall (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_product A' v' B')
    -> per_bar (per_product_bar ts) lib T1 T eq1
    -> per_bar (per_product_bar ts) lib T T2 eq2
    -> per_bar (per_product_bar ts) lib T1 T2 eq1.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ e) in tsb.

  eapply per_product_bar_trans3; try exact comp; eauto.
Qed.

Lemma per_bar_per_product_bar_trans4 {o} :
  forall (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_product A' v' B')
    -> per_bar (per_product_bar ts) lib T1 T eq1
    -> per_bar (per_product_bar ts) lib T T2 eq2
    -> per_bar (per_product_bar ts) lib T1 T2 eq2.
Proof.
  introv tsa tsb comp pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact pera1; clear pera1.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb1 pera1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ e) in tsb.

  eapply per_product_bar_trans4; try exact comp; eauto.
Qed.

Lemma implies_type_value_respecting_trans1_per_product {o} :
  forall lib ts T T' eq A A' v v' B B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_product A v B)
    -> T' ===>(lib) (mkc_product A' v' B')
    -> in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 (close ts) lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> (eq <=2=> (per_product_eq_bar lib eqa eqb))
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv tsts dou comp1 comp2 cla tsa clb tsb eqiff.
  introv ee ceq cl.
  repndors; subst.

  {
    dup ceq as c.
    eapply ccequivc_ext_product in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_product_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_product_bar1;
      try exact h; try exact comp1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_product in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_product_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_product_bar1;
      try exact h; try exact comp2; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_product in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_product_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_product_bar2;
      try exact h; try exact comp1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_product in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_product_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_product_bar2;
      try exact h; try exact comp2; eauto 3 with slow.
  }
Qed.

Lemma type_value_respecting_trans_per_bar_per_product_bar3 {o} :
  forall lib (ts : cts(o)) T T1 T2 A v B C w D (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_product A v B)
    -> ccequivc_ext lib T1 T2
    -> per_bar (per_product_bar ts) lib T T1 eq
    -> per_bar (per_product_bar ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 ceqa per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.

  unfold per_product_bar in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ e) in tsb.

  dup per2 as tf.

  exists eqa1 eqb0; dands; auto.
  eapply type_family_ext_value_respecting_trans5; eauto; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans2_per_product {o} :
  forall lib ts T T' eq A A' v v' B B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_product A v B)
    -> T' ===>(lib) (mkc_product A' v' B')
    -> in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 (close ts) lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> (eq <=2=> (per_product_eq_bar lib eqa eqb))
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv tsts dou comp1 comp2 cla tsa clb tsb eqiff.
  introv ee cl ceq.
  repndors; subst.

  {
    dclose_lr.
    apply per_bar_per_product_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_product_bar3; eauto.
  }

  {
    apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb;[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_product_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_product_bar3; eauto.
  }

  {
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb';[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_product_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_product_bar3; try exact tsa; try exact tsb; eauto.
    eapply per_bar_per_product_bar_sym_rev; try exact tsa; try exact tsb; auto.
  }

  {
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb';[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_product_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_product_bar3; try exact tsa'; try exact tsb'; eauto.
    eapply per_bar_per_product_bar_sym_rev; try exact tsa'; try exact tsb'; auto.
  }
Qed.
