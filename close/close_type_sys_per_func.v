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


  Website: http://nuprl.org/html/verification/

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys_useful.
Require Export dest_close.
Require Export per_ceq_bar.

Require Export close_util_func.
Require Export close_util1.


Lemma in_ext_ext_eqbs_sym {o} :
  forall {lib} (eqa1 eqa2 : lib-per(lib,o)) (eqb1 : lib-per-fam(lib,eqa1,o)) (eqb2 : lib-per-fam(lib,eqa2,o)),
    in_ext_ext lib (fun lib' x => forall a a' (u : eqa1 lib' x a a') (v : eqa2 lib' x a a'), (eqb1 lib' x a a' u) <=2=> (eqb2 lib' x a a' v))
    -> in_ext_ext lib (fun lib' x => forall a a' (u : eqa2 lib' x a a') (v : eqa1 lib' x a a'), (eqb2 lib' x a a' u) <=2=> (eqb1 lib' x a a' v)).
Proof.
  introv h; introv.
  apply eq_term_equals_sym; apply h.
Qed.

Lemma per_bar_per_func_ext_implies_eq_term_equals_per_func_ext_eq {o} :
  forall (ts : cts(o)) lib T T' eq (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B',
    computes_to_valc lib T (mkc_function A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a a' (e : eqa lib' x a a'),
                           type_sys_props4 (close ts) lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> per_bar (per_func_ext (close ts)) lib T T' eq
    -> eq <=2=> (per_func_ext_eq lib eqa eqb).
Proof.
  introv comp tsa tsb per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per1.

  introv; split; intro h.

  - unfold per_func_ext_eq, per_func_eq.
    apply collapse2bars_ext.
    { introv; split; intro q; introv; introv.
      - dup e as f.
        apply (lib_per_cond _ eqa lib' x y) in f.
        apply (lib_per_fam_cond _ eqb lib' x y a a' f e); auto.
      - dup e as f.
        apply (lib_per_cond _ eqa lib' x y) in f.
        apply (lib_per_fam_cond _ eqb lib' x y a a' e f); auto. }

    exists bar.
    introv br ext; introv.
    pose proof (h _ br _ ext x) as h; simpl in *.
    exrepnd.

    apply collapse2bars_ext.
    { introv; split; intro q; introv; introv.
      - dup e as f.
        apply (lib_per_cond _ eqa lib'1 (lib_extends_trans y x) (lib_extends_trans x0 x)) in f.
        apply (lib_per_fam_cond _ eqb lib'1 (lib_extends_trans x0 x) (lib_extends_trans y x) a a' f e); auto.
      - dup e as f.
        apply (lib_per_cond _ eqa lib'1 (lib_extends_trans y x) (lib_extends_trans x0 x)) in f.
        apply (lib_per_fam_cond _ eqb lib'1 (lib_extends_trans x0 x) (lib_extends_trans y x) a a' e f); auto. }

    exists bar'.
    introv br' ext'; introv.
    pose proof (h0 _ br' _ ext' x0) as h0; simpl in *.

    assert (lib_extends lib'2 lib') as xt1 by eauto 3 with slow.
    pose proof (per0 _ br lib'2 xt1 (lib_extends_trans x0 x)) as per0; simpl in *.
    unfold per_func_ext in per0; exrepnd.
    apply per0 in h0; clear per0.
    unfold per_func_ext_eq, per_func_eq in h0; exrepnd.

    exists bar0.
    introv br'' ext''; introv.
    pose proof (h1 _ br'' _ ext'' x1) as h1; simpl in *.

    assert (lib_extends lib'2 lib) as xt2 by eauto 3 with slow.

    dup per1 as eqas.
    eapply type_family_ext_implies_in_ext_eqas in eqas;
      try (apply (lib_extends_preserves_in_ext_ext xt2) in tsa; exact tsa);
      try (eapply lib_extends_preserves_computes_to_valc; try exact xt2; eauto);
      eauto 3 with slow; simpl in *;[].

    dup per1 as eqbs.
    eapply type_family_ext_implies_in_ext_eqbs in eqbs;
      try (apply (lib_extends_preserves_in_ext_ext xt2) in tsa; exact tsa);
      try (apply (lib_extends_preserves_in_ext_ext xt2) in tsb; exact tsb);
      try (eapply lib_extends_preserves_computes_to_valc; try exact xt2; eauto);
      eauto 3 with slow; simpl in *;[].

    pose proof (eqas _ x1) as eqas; simpl in *.
    assert (eqa lib'4 (lib_extends_trans x1 xt2) a a') as e' by (eapply (lib_per_cond _ eqa); eauto).
    dup e as f.
    eapply (lib_per_cond _ eqa) in f; apply eqas in f.
    pose proof (eqbs _ x1 a a' e' f) as eqbs; simpl in *.

    pose proof (h1 _ _ f) as h1.
    apply (lib_per_fam_cond _ eqb lib'4 (lib_extends_trans (lib_extends_trans x1 x0) x) (lib_extends_trans x1 xt2) a a' e e').
    apply eqbs; auto.

  - introv br ext; introv.
    exists (raise_bar bar x); introv br' ext'; introv; simpl in *; exrepnd.
    pose proof (per0 _ br'1 lib'2 (lib_extends_trans ext' br'2) (lib_extends_trans x0 x)) as per0; simpl in *.
    unfold per_func_ext in per0; exrepnd.
    apply per0.

    assert (lib_extends lib'2 lib) as xt by eauto 3 with slow.

    apply (sub_per_per_func_ext_eq _ _ (lib_extends_trans x0 x)) in h.
    eapply implies_eq_term_equals_per_func_ext_eq; try exact h.

    { apply in_ext_ext_eq_term_equals_sym.
      eapply type_family_ext_implies_in_ext_eqas;
        try exact per1;
        simpl; try unfold raise_ext_per;
          try (apply (lib_extends_preserves_in_ext_ext (lib_extends_trans x0 x)) in tsa; exact tsa);
          try (eapply lib_extends_preserves_computes_to_valc; try exact xt; eauto);
          eauto 3 with slow. }

    { apply in_ext_ext_eqbs_sym.
      eapply type_family_ext_implies_in_ext_eqbs;
        try exact per1;
        simpl; try unfold raise_ext_per, raise_ext_per_fam;
          try (apply (lib_extends_preserves_in_ext_ext (lib_extends_trans x0 x)) in tsb; exact tsb);
          try (apply (lib_extends_preserves_in_ext_ext (lib_extends_trans x0 x)) in tsa; exact tsa);
          try (eapply lib_extends_preserves_computes_to_valc; try exact xt; eauto);
          eauto 3 with slow. }
Qed.

Lemma per_bar_per_func_ext_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_func_ext (close ts)) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  apply CL_func; auto.
Qed.

Hint Resolve bcequivc_ext_implies_ccequivc_ext : slow.

Lemma ccequivc_ext_preserves_in_ext_ext_type_sys_props4_fam {o} :
  forall ts lib va (A : @CVTerm o [va]) va' A' vb B (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    bcequivc_ext lib [va] A [va'] A'
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a va A) (substc a' vb B) (eqb lib' x a a' e))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a va' A') (substc a' vb B) (eqb lib' x a a' e)).
Proof.
  introv ceq tsp; introv.
  pose proof (tsp _ e a a' e0) as tsp; simpl in *.
  eapply ccequivc_ext_preserves_in_type_sys_props4; eauto; eauto 3 with slow.
Qed.

Lemma lib_extends_preserves_in_ext_ext_fam {o} :
  forall {lib lib'} (ext : @lib_extends o lib' lib) (eqa : lib-per(lib,o))
         (F : forall (lib' : library) (x : lib_extends lib' lib) (a a' : CTerm) (e : eqa lib' x a a'), Prop),
    in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), F lib' x a a' e)
    -> in_ext_ext lib' (fun lib'' x => forall a a' (e : raise_lib_per eqa ext lib'' x a a'), F lib'' (lib_extends_trans x ext) a a' e).
Proof.
  introv h; introv.
  eapply h.
Qed.

Lemma lib_extends_preserves_bcequivc_ext {o} :
  forall {lib lib'} (x : @lib_extends o lib' lib) v B v' B',
    bcequivc_ext lib [v] B [v'] B'
    -> bcequivc_ext lib' [v] B [v'] B'.
Proof.
  introv x ceq ext.
  eapply ceq; eauto 3 with slow.
Qed.
Hint Resolve lib_extends_preserves_bcequivc_ext : slow.

Lemma bcequivc_sym {o} :
  forall (lib : @library o) v B v' B',
    bcequivc lib [v] B [v'] B'
    -> bcequivc lib [v'] B' [v] B.
Proof.
  introv ceq.
  destruct_cterms.
  unfold bcequivc, bcequiv in *; simpl in *.
  unfold blift in *; exrepnd.
  exists lv nt2 nt1; dands; auto.
  apply olift_cequiv_approx in ceq1; repnd.
  apply olift_approx_cequiv; auto.
Qed.
Hint Resolve bcequivc_sym : slow.

Lemma bcequivc_ext_sym {o} :
  forall (lib : @library o) v B v' B',
    bcequivc_ext lib [v] B [v'] B'
    -> bcequivc_ext lib [v'] B' [v] B.
Proof.
  introv ceq ext.
  pose proof (ceq _ ext) as ceq; simpl in *; spcast; eauto 3 with slow.
Qed.
Hint Resolve bcequivc_ext_sym : slow.

Lemma type_value_respecting_trans_per_bar_per_func_ext1 {o} :
  forall lib (ts : cts(o)) T T1 T2 A v B A' v' B' C w D (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> computes_to_valc lib T1 (mkc_function A' v' B')
    -> computes_to_valc lib T (mkc_function A v B)
    -> ccequivc_ext lib A A'
    -> bcequivc_ext lib [v] B [v'] B'
    -> per_bar (per_func_ext ts) lib T1 T2 eq
    -> per_bar (per_func_ext ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  unfold per_func_ext in *; exrepnd.

  eapply lib_extends_preserves_computes_to_valc in comp1;[|exact x].
  eapply lib_extends_preserves_computes_to_valc in comp2;[|exact x].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ x) in tsb.

  dup per2 as tf.

  eapply type_family_ext_value_respecting_trans1 in tf;
    try exact comp2; try exact comp1; try exact tsb; try exact tsa;
      eauto 3 with slow.
  exists eqa1 eqb0; dands; auto.
Qed.

Lemma type_value_respecting_trans_per_bar_per_func_ext2 {o} :
  forall lib (ts : cts(o)) T T1 T2 A v B A' v' B' C w D (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> computes_to_valc lib T1 (mkc_function A' v' B')
    -> computes_to_valc lib T (mkc_function A v B)
    -> ccequivc_ext lib A A'
    -> bcequivc_ext lib [v] B [v'] B'
    -> per_bar (per_func_ext ts) lib T2 T1 eq
    -> per_bar (per_func_ext ts) lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  unfold per_func_ext in *; exrepnd.

  eapply lib_extends_preserves_computes_to_valc in comp1;[|exact x].
  eapply lib_extends_preserves_computes_to_valc in comp2;[|exact x].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ x) in tsb.

  dup per2 as tf.

  eapply type_family_ext_value_respecting_trans3 in tf;
    try exact comp2; try exact comp1; try exact tsb; try exact tsa;
      eauto 3 with slow.
  exists eqa1 eqb0; dands; auto.
Qed.

Lemma in_ext_ext_type_sys_props4_sym_eq {o} :
  forall (ts : cts(o)) {lib lib'} (x : lib_extends lib' lib) A A' (eqa : lib-per(lib,o)) a a',
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> eqa lib' x a a'
    -> eqa lib' x a' a.
Proof.
  introv tsp e.
  pose proof (tsp _ x) as tsp; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_sym_eq : slow.

Lemma in_ext_ext_type_sys_props4_trans1_eq {o} :
  forall (ts : cts(o)) {lib lib'} (x : lib_extends lib' lib) A A' (eqa : lib-per(lib,o)) a a',
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> eqa lib' x a a'
    -> eqa lib' x a a.
Proof.
  introv tsp e.
  pose proof (tsp _ x) as tsp; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
  eapply tet;[eauto|]; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_trans1_eq : slow.

Lemma in_ext_ext_type_sys_props4_trans2_eq {o} :
  forall (ts : cts(o)) {lib lib'} (x : lib_extends lib' lib) A A' (eqa : lib-per(lib,o)) a a',
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> eqa lib' x a a'
    -> eqa lib' x a' a'.
Proof.
  introv tsp e.
  pose proof (tsp _ x) as tsp; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
  eapply tet;[|eauto]; auto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_trans2_eq : slow.

Lemma in_ext_ext_type_sys_props4_fam_sym {o} :
  forall (ts : cts(o)) lib A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v' B') (substc a' v B) (eqb lib' x a a' e)).
Proof.
  introv tsa tsb; repeat introv.
  pose proof (tsb lib' e) as tcsp; simpl in *.
  apply type_sys_props4_sym; auto.
  apply type_sys_props4_eqb_comm; auto; eauto 3 with slow.
Qed.

Lemma per_func_ext_eq_sym {o} :
  forall ts lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B' t1 t2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_func_ext_eq lib eqa eqb t1 t2
    -> per_func_ext_eq lib eqa eqb t2 t1.
Proof.
  introv tsa tsb per.

  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  unfold per_func_ext_eq in *; exrepnd.
  exists bar; introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  pose proof (tsa _ x) as tsa; simpl in *.
  pose proof (tsb _ x) as tsb; simpl in *.
  pose proof (symb _ x) as sym; simpl in *.

  unfold per_func_eq in *; introv.

  apply symb.

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  assert (term_equality_symmetric (eqa lib'0 x)) as syma by eauto 3 with slow.
  dup e as f.
  apply syma in f.
  apply (eqbs _ _ e f).
  apply per0.
Qed.

Lemma per_func_ext_eq_trans {o} :
  forall ts lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B' t1 t2 t3,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_func_ext_eq lib eqa eqb t1 t2
    -> per_func_ext_eq lib eqa eqb t2 t3
    -> per_func_ext_eq lib eqa eqb t1 t3.
Proof.
  introv tsa tsb pera perb.

  dup tsb as transb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep in transb.

  unfold per_func_ext_eq in *; exrepnd.
  exists (intersect_bars bar0 bar); introv br ext; introv; simpl in *; exrepnd.
  pose proof (pera0 _ br0 _ (lib_extends_trans ext br3) x) as pera0; simpl in *.
  pose proof (perb0 _ br2 _ (lib_extends_trans ext br1) x) as perb0; simpl in *.

  pose proof (tsa _ x) as tsa; simpl in *.
  pose proof (tsb _ x) as tsb; simpl in *.
  pose proof (transb _ x) as sym; simpl in *.

  unfold per_func_eq in *; introv.

  eapply transb;[|apply perb0].

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  assert (term_equality_symmetric (eqa lib'0 x)) as syma by eauto 3 with slow.
  assert (term_equality_transitive (eqa lib'0 x)) as transa by eauto 3 with slow.

  assert (eqa lib'0 x a a) as f by (eapply transa;[exact e|]; auto).

  apply (eqbs0 _ _ e f).
  apply pera0.
Qed.

Hint Resolve sp_implies_ccequivc_ext_apply : slow.

Lemma per_func_ext_eq_resp {o} :
  forall ts lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B' t t',
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_func_ext_eq lib eqa eqb t t
    -> ccequivc_ext lib t t'
    -> per_func_ext_eq lib eqa eqb t t'.
Proof.
  introv tsa tsb per ceq.

  dup tsb as respb.
  dup tsb as transb.
  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_respecting_dep in respb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep in transb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  unfold per_func_ext_eq in *; exrepnd.
  exists bar; introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  pose proof (tsa _ x) as tsa; simpl in *.
  pose proof (tsb _ x) as tsb; simpl in *.
  pose proof (respb _ x) as sym; simpl in *.

  unfold per_func_eq in *; introv.

  assert (term_equality_symmetric (eqa lib'0 x)) as syma by eauto 3 with slow.
  assert (term_equality_transitive (eqa lib'0 x)) as transa by eauto 3 with slow.

  assert (eqa lib'0 x a' a') as f by (eapply transa;[|exact e]; auto).

  dup tsb as eqbs.
  apply type_sys_props4_implies_eq_term_equals_sym in eqbs; eauto 3 with slow; repnd.

  eapply transb;[apply per0|].
  apply respb; eauto 3 with slow.
  apply (eqbs1 _ _ e f); auto.
Qed.

Lemma per_bar_per_func_ext_sym {o} :
  forall (ts : cts(o)) lib T T' A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> computes_to_valc lib T (mkc_function A v B)
    -> per_bar (per_func_ext ts) lib T T' eq
    -> per_bar (per_func_ext ts) lib T' T eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ x) in tsb.

  eapply per_func_ext_sym; try exact comp; eauto.
Qed.

Lemma per_bar_per_func_ext_sym_rev {o} :
  forall (ts : cts(o)) lib T T' A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> computes_to_valc lib T (mkc_function A v B)
    -> per_bar (per_func_ext ts) lib T' T eq
    -> per_bar (per_func_ext ts) lib T T' eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact x].
  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ x) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ x) in tsb.

  eapply per_func_ext_sym_rev; try exact comp; eauto.
Qed.


Lemma close_type_system_func {o} :
  forall lib (ts : cts(o))
         T T'
         (eq : per)
         A A' v v' B B'
         (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> computes_to_valc lib T (mkc_function A v B)
    -> computes_to_valc lib T' (mkc_function A' v' B')
    -> in_ext_ext lib (fun lib' x => close ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall (a a' : CTerm) (e : eqa lib' x a a'),
              close ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall (a a' : CTerm) (e : eqa lib' x a a'),
              type_sys_props4 (close ts) lib' (substc a v B) (substc a' v' B')
                              (eqb lib' x a a' e))
    -> (eq <=2=> (per_func_ext_eq lib eqa eqb))
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp1 comp2 cla tsa clb tsb eqiff.

  prove_type_sys_props4 SCase; introv.

  + SCase "uniquely_valued".
    introv cl.
    dclose_lr; clear cl.
    eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    eapply per_bar_per_func_ext_implies_eq_term_equals_per_func_ext_eq;
      try exact comp1; eauto.

  + SCase "type_symmetric".
    introv cl eqs.
    dclose_lr; clear cl.
    apply per_bar_per_func_ext_implies_close.
    eapply type_extensionality_per_bar;[eauto|]; auto.

  + SCase "type_value_respecting".
    introv ee ceq; repndors; subst;
      apply CL_func; exists eqa eqb; dands; auto.

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      eapply type_family_ext_cequivc; eauto.
    }

    {
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      eapply type_family_ext_cequivc2; eauto.
    }

  + SCase "type_value_respecting_trans".
    introv ee ceq cl.
    repndors; subst.

    {
      dup ceq as c.
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      dup tsa as tsa'.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsa';[|eauto].
      dup tsb as tsb'.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4_fam in tsb';[|eauto].
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
      dup tsa' as tsa''.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsa';[|eauto].
      dup tsb as tsb'.
      eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
      dup tsb' as tsb''.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4_fam in tsb';[|eauto].
      dclose_lr; clear cl.
      apply per_bar_per_func_ext_implies_close.
      eapply type_value_respecting_trans_per_bar_per_func_ext1;
        try exact h; try exact comp2; eauto 3 with slow.
    }

    {
      dup ceq as c.
      eapply ccequivc_ext_function in ceq;[|eauto]; exrepnd; spcast.
      dup tsa as tsa'.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsa';[|eauto].
      dup tsb as tsb'.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4_fam in tsb';[|eauto].
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
      dup tsa' as tsa''.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in tsa';[|eauto].
      dup tsb as tsb'.
      eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
      dup tsb' as tsb''.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4_fam in tsb';[|eauto].
      apply in_ext_ext_type_sys_props4_sym in tsa'.
      eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
      dclose_lr; clear cl.
      apply per_bar_per_func_ext_implies_close.
      eapply type_value_respecting_trans_per_bar_per_func_ext2;
        try exact h; try exact comp2; eauto 3 with slow.
    }

  + SCase "term_symmetric".
    introv ee.
    apply eqiff in ee; apply eqiff; clear eqiff.
    eapply per_func_ext_eq_sym; eauto.

  + SCase "term_transitive".
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff; clear eqiff.
    eapply per_func_ext_eq_trans; eauto.

  + SCase "term_value_respecting".
    introv ee ceq.
    apply eqiff in ee; apply eqiff; clear eqiff.
    eapply per_func_ext_eq_resp; eauto.

  + SCase "type_gsymmetric".
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    split; intro cl; dclose_lr; clear cl; apply per_bar_per_func_ext_implies_close.
    { eapply per_bar_per_func_ext_sym; try exact comp1;eauto. }
    { eapply per_bar_per_func_ext_sym_rev; try exact comp1;eauto. }

  + SCase "type_gtransitive".
    apply CL_func.
    exists eqa eqb; dands; auto.
    eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.

  + SCase "type_mtransitive".
    introv ee cl1 cl2.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.

    repndors; subst; clear cl1 cl2; dands; apply per_bar_per_func_ext_implies_close.

    {
      
    }

    { eapply per_func_ext_function_trans1; try exact h; try exact h0; eauto. }
    { eapply per_func_ext_function_trans2; try exact h; try exact h0; eauto. }
    { eapply per_func_ext_function_trans3; try exact h; try exact h0; eauto. }
    { eapply per_func_ext_function_trans4; try exact h; try exact h0; eauto. }
Qed.
