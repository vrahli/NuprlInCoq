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

Require Export close_util_set.
Require Export close_util1.
Require Export close_util2.


Lemma constructor_inj_set {o} :
  @constructor_inj o mkc_set.
Proof.
  split; introv h; ginv; eqconstr h; tcsp.
  eapply cequivc_mkc_set in h;[|eauto 3 with slow]; exrepnd.
  apply computes_to_valc_isvalue_eq in h1; eauto 3 with slow; eqconstr h1; tcsp.
Qed.
Hint Resolve constructor_inj_set : slow.

Lemma per_bar_per_set_implies_eq_term_equals_per_set_eq {o} :
  forall inh (ts : cts(o)) lib T T' eq (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) A v B A' v' B',
    ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x =>
                         forall a a' (e : eqa lib' x a a'),
                           type_sys_props4 inh ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> per_bar inh (per_set inh ts) lib T T' eq
    -> eq <=2=> (per_set_eq_bar inh lib eqa eqb).
Proof.
  introv comp tsa tsb per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per0.

  introv; split; intro h.

  - unfold per_set_eq_bar, per_set_eq.
    apply in_open_bar_ext_dup.
    unfold per_bar_eq in *.
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    eapply in_open_bar_ext_comb; try exact h; clear h.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv h per1; unfold per_set in *; exrepnd.
    apply per1 in h; clear per1.

    unfold per_set_eq_bar in h.
    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; introv.
    unfold per_set_eq in h; exrepnd.

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
    assert (eqa lib'0 (lib_extends_trans e0 e) t1 t2) as e' by (eapply (lib_per_cond _ _ eqa); eauto; apply eqas; auto).
    assert (eqa lib'0 z t1 t2) as e'' by (eapply (lib_per_cond _ _ eqa); eauto; apply eqas; auto).
    exists e''.
    eapply eq_term_equals_preserves_inhabited;[|eauto].
    pose proof (eqbs lib'0 e0 t1 t2 e' e1) as q.
    eapply eq_term_equals_trans;[apply eq_term_equals_sym;eauto|].
    eapply lib_per_fam_cond; eauto.

  - eapply in_open_bar_ext_comb; try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv per1; introv.
    unfold per_set in per1; exrepnd.
    apply per1; clear per1.

    apply (sub_per_per_set_eq_bar _ _ _ e) in h.
    eapply implies_eq_term_equals_per_set_eq_bar; try exact h.

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

Lemma per_bar_per_set_implies_close {o} :
  forall inh (ts : cts(o)) lib T T' eq,
    per_bar inh (per_set inh (close inh ts)) lib T T' eq
    -> close inh ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.
  apply CL_set; auto.
Qed.

Lemma type_value_respecting_trans_per_bar_per_set1 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A v B A' v' B' C w D (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A C (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T1 (mkc_set A' v' B')
    -> ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> ccequivc_ext inh lib A A'
    -> bcequivc_ext inh lib [v] B [v'] B'
    -> per_bar inh (per_set inh ts) lib T1 T2 eq
    -> per_bar inh (per_set inh ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_set in *; exrepnd.

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

Lemma type_value_respecting_trans_per_bar_per_set2 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A v B A' v' B' C w D (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A C (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T1 (mkc_set A' v' B')
    -> ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> ccequivc_ext inh lib A A'
    -> bcequivc_ext inh lib [v] B [v'] B'
    -> per_bar inh (per_set inh ts) lib T2 T1 eq
    -> per_bar inh (per_set inh ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_set in *; exrepnd.

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

Lemma per_set_eq_bar_sym {o} :
  forall inh ts lib (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) A v B A' v' B' t1 t2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_set_eq_bar inh lib eqa eqb t1 t2
    -> per_set_eq_bar inh lib eqa eqb t2 t1.
Proof.
  introv tsa tsb per.

  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  unfold per_set_eq_bar in *; exrepnd.
  eapply in_open_bar_ext_pres; eauto; clear per; introv per.

  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.
  pose proof (symb _ e) as sym; simpl in *.

  unfold per_set_eq in *; introv.
  exrepnd.

  assert (term_equality_symmetric (eqa lib' e)) as syma by eauto 3 with slow.
  dup e0 as f.
  apply syma in f.
  exists f.
  eapply eq_term_equals_preserves_inhabited;[|eauto].
  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.
  apply (eqbs _ _ e0 f); auto.
Qed.

Lemma per_set_eq_bar_trans {o} :
  forall inh ts lib (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) A v B A' v' B' t1 t2 t3,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_set_eq_bar inh lib eqa eqb t1 t2
    -> per_set_eq_bar inh lib eqa eqb t2 t3
    -> per_set_eq_bar inh lib eqa eqb t1 t3.
Proof.
  introv tsa tsb pera perb.

  dup tsb as transb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep in transb.

  unfold per_set_eq_bar in *; exrepnd.
  eapply in_open_bar_ext_comb; try exact pera; clear pera.
  eapply in_open_bar_ext_comb; try exact perb; clear perb.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb pera.

  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.
  pose proof (transb _ e) as sym; simpl in *.

  unfold per_set_eq in *; introv.
  exrepnd.
  spcast.

  assert (term_equality_symmetric (eqa lib' e)) as syma by eauto 3 with slow.
  assert (term_equality_transitive (eqa lib' e)) as transa by eauto 3 with slow.

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  assert (eqa lib' e t1 t3) as f by (eapply transa; eauto).
  exists f.
  eapply eq_term_equals_preserves_inhabited;[|exact perb0].

  assert (eqa lib' e t3 t3) as g by (eapply transa; eauto).

  eapply eq_term_equals_trans;[apply (eqbs1 _ _ e1 g)|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;apply (eqbs1 _ _ f g)]; auto.
Qed.

Lemma type_sys_props4_implies_term_equality_respecting {o} :
  forall inh (lib : library) (ts : cts(o)) (A B : CTerm) (eqa : per(o)),
    type_sys_props4 inh ts lib A B eqa -> term_equality_respecting inh lib eqa.
Proof.
  introv tsp.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve type_sys_props4_implies_term_equality_respecting : slow.

Lemma per_set_eq_bar_resp {o} :
  forall inh ts lib (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) A v B A' v' B' t t',
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_set_eq_bar inh lib eqa eqb t t
    -> ccequivc_ext inh lib t t'
    -> per_set_eq_bar inh lib eqa eqb t t'.
Proof.
  introv tsa tsb per ceq.

  dup tsb as respb.
  dup tsb as transb.
  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_respecting_dep in respb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep in transb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  unfold per_set_eq_bar in *; exrepnd.
  eapply in_open_bar_ext_pres; eauto; clear per; introv per.

  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.
  pose proof (respb _ e) as sym; simpl in *.

  unfold per_set_eq in *; introv.
  exrepnd.
  spcast.

  assert (term_equality_symmetric (eqa lib' e)) as syma by eauto 3 with slow.
  assert (term_equality_transitive (eqa lib' e)) as transa by eauto 3 with slow.
  assert (term_equality_respecting inh lib' (eqa lib' e)) as respa by eauto 3 with slow.

  assert (eqa lib' e t t') as f by (eapply respa; eauto 3 with slow).
  exists f.

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  eapply eq_term_equals_preserves_inhabited;[|eauto].

  apply eq_term_equals_sym.
  apply (eqbs0 _ _ f e0).
Qed.

Lemma per_set_sym {o} :
  forall inh ts lib (T1 T2 : @CTerm o) A A' v v' B B' equ eqa eqb,
    ccomputes_to_valc_ext inh lib T1 (mkc_set A v B)
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib
                  (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 inh ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_set inh ts lib T1 T2 equ
    -> per_set inh ts lib T2 T1 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_set in *; exrepnd.
  exists eqa0 eqb0; dands; auto;[].
  eapply type_family_ext_sym; eauto 3 with slow.
Qed.

Lemma per_set_sym_rev {o} :
  forall inh ts lib (T1 T2 : @CTerm o) A A' v v' B B' equ eqa eqb,
    ccomputes_to_valc_ext inh lib T1 (mkc_set A v B)
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         inh lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 inh ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_set inh ts lib T2 T1 equ
    -> per_set inh ts lib T1 T2 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_set in *; exrepnd.
  exists eqa0 eqb0; dands; auto;[].

  eapply type_family_ext_value_respecting_trans3;
    try (exact tspa);
    try (exact tspb); eauto; eauto 3 with slow.
Qed.

Lemma per_bar_per_set_sym {o} :
  forall inh (ts : cts(o)) lib T T' A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> per_bar inh (per_set inh ts) lib T T' eq
    -> per_bar inh (per_set inh ts) lib T' T eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  eapply per_set_sym; try exact comp; eauto.
Qed.

Lemma per_bar_per_set_sym_rev {o} :
  forall inh (ts : cts(o)) lib T T' A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> per_bar inh (per_set inh ts) lib T' T eq
    -> per_bar inh (per_set inh ts) lib T T' eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  eapply per_set_sym_rev; try exact comp; eauto.
Qed.

Lemma per_set_trans1 {o} :
  forall inh ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         inh lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 inh ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_set inh ts lib T T2 eq2
    -> per_set inh ts lib T1 T eq1
    -> per_set inh ts lib T1 T2 eq1.
Proof.
  introv comp tspa tspb pera perb.
  unfold per_set in *; exrepnd.
  exists eqa0 eqb0; dands; auto.
  eapply type_family_ext_trans1; eauto 3 with slow.
Qed.

Lemma per_set_trans2 {o} :
  forall inh ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         inh lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 inh ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_set inh ts lib T T2 eq2
    -> per_set inh ts lib T1 T eq1
    -> per_set inh ts lib T1 T2 eq2.
Proof.
  introv comp tspa tspb pera perb.
  unfold per_set in *; exrepnd.
  exists eqa1 eqb1; dands; auto.
  eapply type_family_ext_trans2; eauto 3 with slow.
Qed.

Lemma per_bar_per_set_trans1 {o} :
  forall inh (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq1 eq2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> per_bar inh (per_set inh ts) lib T1 T eq1
    -> per_bar inh (per_set inh ts) lib T T2 eq2
    -> per_bar inh (per_set inh ts) lib T1 T2 eq1.
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

  eapply per_set_trans1; try exact comp; eauto.
Qed.

Lemma per_bar_per_set_trans2 {o} :
  forall inh (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq1 eq2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> per_bar inh (per_set inh ts) lib T1 T eq1
    -> per_bar inh (per_set inh ts) lib T T2 eq2
    -> per_bar inh (per_set inh ts) lib T1 T2 eq2.
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

  eapply per_set_trans2; try exact comp; eauto.
Qed.

Lemma per_set_trans3 {o} :
  forall inh ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext inh lib T (mkc_set A' v' B')
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         inh lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 inh ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_set inh ts lib T T2 eq2
    -> per_set inh ts lib T1 T eq1
    -> per_set inh ts lib T1 T2 eq1.
Proof.
  introv comp tspa tspb pera perb.
  apply (per_set_trans1 inh ts lib T T1 T2 eq1 eq2 eqa eqb A' v' B' A v B);
    try exact pera; try exact perb; eauto.

  - apply in_ext_ext_type_sys_props4_sym; auto.

  - repeat introv.
    pose proof (tspa lib' e) as tspa; simpl in *.
    pose proof (tspb lib' e) as tspb; simpl in *.
    apply type_sys_props4_sym.

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa lib' e a' a) as e1 by tcsp.
    pose proof (tspb a' a e1) as q.

    pose proof (type_sys_props4_implies_eq_term_equals_sym
                  inh ts lib' (eqa lib' e) (eqb lib' e) v B v' B') as w.
    repeat (autodimp w hyp); repnd.

    pose proof (w a a' e0 e1) as w.
    eapply type_sys_props4_change_per;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.

Lemma per_set_trans4 {o} :
  forall inh ts lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext inh lib T (mkc_set A' v' B')
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         inh lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 inh ts lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_set inh ts lib T T2 eq2
    -> per_set inh ts lib T1 T eq1
    -> per_set inh ts lib T1 T2 eq2.
Proof.
  introv comp tspa tspb pera perb.
  apply (per_set_trans2 inh ts lib T T1 T2 eq1 eq2 eqa eqb A' v' B' A v B);
    try exact pera; try exact perb; eauto.

  - apply in_ext_ext_type_sys_props4_sym; auto.

  - repeat introv.
    pose proof (tspa lib' e) as tspa; simpl in *.
    pose proof (tspb lib' e) as tspb; simpl in *.
    apply type_sys_props4_sym.

    assert (term_equality_symmetric (eqa lib' e)) as tees by (eauto 3 with slow).
    assert (term_equality_transitive (eqa lib' e)) as teet by (eauto 3 with slow).

    assert (eqa lib' e a' a) as e1 by tcsp.
    pose proof (tspb a' a e1) as q.

    pose proof (type_sys_props4_implies_eq_term_equals_sym
                  inh ts lib' (eqa lib' e) (eqb lib' e) v B v' B') as w.
    repeat (autodimp w hyp); repnd.

    pose proof (w a a' e0 e1) as w.
    eapply type_sys_props4_change_per;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.

Lemma per_bar_per_set_trans3 {o} :
  forall inh (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq1 eq2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_set A' v' B')
    -> per_bar inh (per_set inh ts) lib T1 T eq1
    -> per_bar inh (per_set inh ts) lib T T2 eq2
    -> per_bar inh (per_set inh ts) lib T1 T2 eq1.
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

  eapply per_set_trans3; try exact comp; eauto.
Qed.

Lemma per_bar_per_set_trans4 {o} :
  forall inh (ts : cts(o)) lib T T1 T2 A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq1 eq2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_set A' v' B')
    -> per_bar inh (per_set inh ts) lib T1 T eq1
    -> per_bar inh (per_set inh ts) lib T T2 eq2
    -> per_bar inh (per_set inh ts) lib T1 T2 eq2.
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

  eapply per_set_trans4; try exact comp; eauto.
Qed.

Lemma ccequivc_ext_set {o} :
  forall inh lib (T T' : @CTerm o) A v B,
    ccequivc_ext inh lib T T'
    -> ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> ccomputes_to_valc_ext inh lib T' (mkc_set A v B).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans1_per_set {o} :
  forall inh lib ts T T' eq A A' v v' B B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> T ===>(inh,lib) (mkc_set A v B)
    -> T' ===>(inh,lib) (mkc_set A' v' B')
    -> in_ext_ext inh lib (fun lib' x => close inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close inh ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh (close inh ts) lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> (eq <=2=> (per_set_eq_bar inh lib eqa eqb))
    -> type_equality_respecting_trans1 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou comp1 comp2 cla tsa clb tsb eqiff.
  introv ee ceq cl.
  repndors; subst.

  {
    dup ceq as c.
    eapply ccequivc_ext_set in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_set_implies_close.
    eapply type_value_respecting_trans_per_bar_per_set1;
      try exact h; try exact comp1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_set in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_set_implies_close.
    eapply type_value_respecting_trans_per_bar_per_set1;
      try exact h; try exact comp2; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_set in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_set_implies_close.
    eapply type_value_respecting_trans_per_bar_per_set2;
      try exact h; try exact comp1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_set in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_set_implies_close.
    eapply type_value_respecting_trans_per_bar_per_set2;
      try exact h; try exact comp2; eauto 3 with slow.
  }
Qed.

Lemma type_value_respecting_trans_per_bar_per_set3 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A v B C w D (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A C (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_set A v B)
    -> ccequivc_ext inh lib T1 T2
    -> per_bar inh (per_set inh ts) lib T T1 eq
    -> per_bar inh (per_set inh ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 ceqa per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.

  unfold per_set in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  dup per2 as tf.

  exists eqa1 eqb0; dands; auto.
  eapply type_family_ext_value_respecting_trans5; eauto; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans2_per_set {o} :
  forall inh lib ts T T' eq A A' v v' B B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> T ===>(inh,lib) (mkc_set A v B)
    -> T' ===>(inh,lib) (mkc_set A' v' B')
    -> in_ext_ext inh lib (fun lib' x => close inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close inh ts lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh (close inh ts) lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> (eq <=2=> (per_set_eq_bar inh lib eqa eqb))
    -> type_equality_respecting_trans2 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou comp1 comp2 cla tsa clb tsb eqiff.
  introv ee cl ceq.
  repndors; subst.

  {
    dclose_lr.
    apply per_bar_per_set_implies_close.
    eapply type_value_respecting_trans_per_bar_per_set3; eauto.
  }

  {
    apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb;[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_set_implies_close.
    eapply type_value_respecting_trans_per_bar_per_set3; eauto.
  }

  {
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb';[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_set_implies_close.
    eapply type_value_respecting_trans_per_bar_per_set3; try exact tsa; try exact tsb; eauto.
    eapply per_bar_per_set_sym_rev; try exact tsa; try exact tsb; auto.
  }

  {
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb';[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_set_implies_close.
    eapply type_value_respecting_trans_per_bar_per_set3; try exact tsa'; try exact tsb'; eauto.
    eapply per_bar_per_set_sym_rev; try exact tsa'; try exact tsb'; auto.
  }
Qed.
