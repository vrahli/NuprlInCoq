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

Require Export close_util_w.
Require Export close_util1.
Require Export close_util2.


Lemma per_bar_per_w_bar_implies_eq_term_equals_weq_bar {o} :
  forall (ts : cts(o)) uk lib T T' eq (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B',
    ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x =>
                         forall a a' (e : eqa lib' x a a'),
                           type_sys_props4 ts uk lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> per_bar (per_w_bar ts) uk lib T T' eq
    -> eq <=2=> (weq_bar lib eqa eqb).
Proof.
  introv comp tsa tsb per.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|]; clear per0.

  introv; split; intro h.

  - apply in_open_bar_ext_dup.
    unfold per_bar_eq in *.
    eapply in_open_bar_ext_comb; try exact per1; clear per1.
    eapply in_open_bar_ext_comb; try exact h; clear h.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv h per1; exrepnd.
    unfold per_w_bar in per1; exrepnd.
    apply per1 in h; clear per1.

    eapply in_open_bar_ext_pres; try exact h; clear h; introv h; introv.

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
    eapply weq_eq_term_equals; try exact h; auto.
    { introv; apply eq_term_equals_sym.
      assert (eqa lib'0 (lib_extends_trans e0 e) a1 a2) as e' by (eapply (lib_per_cond _ eqa); eauto).
      eapply eq_term_equals_trans;[|eapply (eqbs _ e0 a1 a2 e')]; apply lib_per_fam_cond. }
    { apply eq_term_equals_sym.
      eapply eq_term_equals_trans;[|eapply eqas]; apply lib_per_cond. }

  - eapply in_open_bar_ext_comb; try exact per1; clear per1.
    apply in_ext_ext_implies_in_open_bar_ext.
    introv per1; introv.
    unfold per_w_bar in per1; exrepnd.
    apply per1; clear per1.

    apply (sub_per_weq_bar _ _ e) in h.
    eapply implies_eq_term_equals_weq_bar; try exact h.

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

Lemma per_bar_per_w_bar_implies_close {o} :
  forall (ts : cts(o)) uk lib T T' eq,
    per_bar (per_w_bar (close ts)) uk lib T T' eq
    -> close ts uk lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.
  apply CL_w; auto.
Qed.

Lemma type_value_respecting_trans_per_bar_per_w_bar1 {o} :
  forall uk lib (ts : cts(o)) T T1 T2 A v B A' v' B' C w D (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T1 (mkc_w A' v' B')
    -> ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> ccequivc_ext lib A A'
    -> bcequivc_ext lib [v] B [v'] B'
    -> per_bar (per_w_bar ts) uk lib T1 T2 eq
    -> per_bar (per_w_bar ts) uk lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_w_bar in *; exrepnd.

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

Lemma type_value_respecting_trans_per_bar_per_w_bar2 {o} :
  forall uk lib (ts : cts(o)) T T1 T2 A v B A' v' B' C w D (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T1 (mkc_w A' v' B')
    -> ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> ccequivc_ext lib A A'
    -> bcequivc_ext lib [v] B [v'] B'
    -> per_bar (per_w_bar ts) uk lib T2 T1 eq
    -> per_bar (per_w_bar ts) uk lib T T2 eq.
Proof.
  introv tsa tsb comp1 comp2 ceqa ceqb per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_w_bar in *; exrepnd.

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

Lemma weq_bar_sym {o} :
  forall ts uk lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B' t1 t2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> weq_bar lib eqa eqb t1 t2
    -> weq_bar lib eqa eqb t2 t1.
Proof.
  introv tsa tsb per.

  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  eapply in_open_bar_ext_pres; eauto; clear per; introv per.

  pose proof (tsa _ e) as tsa; simpl in *.
  pose proof (tsb _ e) as tsb; simpl in *.
  pose proof (symb _ e) as sym; simpl in *.

  eapply weq_sym;
    try (introv; apply type_sys_props4_implies_type_sys_props; eauto); eauto 3 with slow.
Qed.

Hint Resolve iscvalue_mkc_sup : slow.

Lemma ccequivc_ext_sup_sup_implies {o} :
  forall lib (a b c d : @CTerm o),
    ccequivc_ext lib (mkc_sup a b) (mkc_sup c d)
    -> ccequivc_ext lib a c /\ ccequivc_ext lib b d.
Proof.
  introv ceq; split; introv ext; pose proof (ceq _ ext) as ceq; simpl in *; spcast.
  { eapply cequivc_mkc_sup in ceq;[|eapply computes_to_valc_refl;eauto 2 with slow].
    exrepnd.
    apply computes_to_valc_isvalue_eq in ceq0; eauto 3 with slow.
    eqconstr ceq0; auto. }
  { eapply cequivc_mkc_sup in ceq;[|eapply computes_to_valc_refl;eauto 2 with slow].
    exrepnd.
    apply computes_to_valc_isvalue_eq in ceq0; eauto 3 with slow.
    eqconstr ceq0; auto. }
Qed.

Lemma weq_cequivc_rev {o} :
  forall uk (lib : @library o) eqa eqb t t1 t2 ts v1 B1 v2 B2,
    term_equality_respecting lib eqa
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall (a1 a2 : @CTerm o) (e : eqa a1 a2),
          type_sys_props ts uk lib
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> weq lib eqa eqb t1 t
    -> ccequivc_ext lib t1 t2
    -> weq lib eqa eqb t2 t.
Proof.
  introv tera tesa teta ftspb weq1.
  generalize t2; clear t2.
  induction weq1 as [t t' a f a' f' e c c' h h'].
  introv ceq.
  rename t' into t1.
  rename a' into a1.
  rename f' into f1.
  spcast.
  pose proof (ccequivc_ext_mkc_sup lib t t2 a f) as i.
  repeat (dest_imp i hyp); exrepnd.
  eapply weq_cons; eauto.
Qed.

Lemma weq_trans {o} :
  forall uk (lib : @library o) eqa eqb t1 t2 t3 ts v1 B1 v2 B2,
    term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> term_equality_respecting lib eqa
    -> (forall (a1 a2 : @CTerm o) (e : eqa a1 a2),
          type_sys_props ts uk lib
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> weq lib eqa eqb t1 t2
    -> weq lib eqa eqb t2 t3
    -> weq lib eqa eqb t1 t3.
Proof.
  introv teqsa teqta respa ftsp weq1.
  generalize t3; clear t3.
  induction weq1 as [t t' a f a' f' e c c' h h'].
  introv weq2.
  inversion weq2 as [x g a'0 f'0 e0 d d' h1].
  computes_to_eqval_ext.
  eapply ccequivc_ext_sup_sup_implies in ceq; repnd.

  assert (eqa a a'0) as e'.
  { eapply teqta;[eauto|].
    eapply teqta;[|eauto].
    apply respa;[|apply ccequivc_ext_sym;auto].
    eapply teqta; eauto. }

  apply @weq_cons with (a := a) (f := f) (a' := a'0) (f' := f'0) (e := e');
    try (complete (spcast; sp)); introv hyp.
  apply h' with (b' := b'); sp.
  { apply (eq_family_trans1 uk lib) with (a1 := a'0) (ts := ts) (v1 := v1) (B1 := B1) (v2 := v2) (B2 := B2) (e1 := e'); sp. }

  assert (weq lib eqa eqb (mkc_apply g b') (mkc_apply f'0 b')) as wa;
    [|eapply weq_cequivc_rev; eauto 3 with slow];[].

  apply h1.
  generalize (eq_term_equals_sym_tsp2 ts uk lib eqa eqb v1 B1 v2 B2); intro i; sp.

  assert (eqa a'0 a'0) as ea by (eapply teqta;eauto).

  apply (i1 a'0 a e' ea) in hyp.
  apply (i1 a'0 x e0 ea).

  pose proof (ftsp a'0 a'0 ea) as tspb.
  onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 dum1; sp.
  eauto.
Qed.

(*
Lemma weq_cequivc2 :
  forall eqa eqb ts v1 B1 v2 B2 a a' e f f' b b',
    term_equality_respecting eqa
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (forall (a1 a2 : CTerm) (e : eqa a1 a2),
          type_sys_props ts
                         (substc a1 v1 B1)
                         (substc a2 v2 B2)
                         (eqb a1 a2 e))
    -> weq eqa eqb (mkc_apply f b) (mkc_apply f b)
    -> eqb a a' e b b'
    -> cequivc f f'
    -> weq eqa eqb (mkc_apply f b) (mkc_apply f' b').
Proof.
  introv tera tesa teta ftspb weq1 eqb1 ceq.
  generalize f' b' eqb1 ceq; clear ceq eqb1 b' f'.
  remember (mkc_apply f b).
  generalize Heqc; clear Heqc.
  induction weq1.
  introv eq eqb1 ceq; subst.
  generalize (cequivc_mkc_sup t' t'0 a' f'); intros i.
  repeat (dest_imp i hyp); exrepnd.
  rename b' into f'0.
  unfold term_equality_respecting in tera.
  generalize (tera a' a'0); intro j.
  repeat (dest_imp j hyp).
  apply teta with (t2 := a); sp.
  apply weq_cons with (a := a') (f := f') (a' := a'0) (f' := f'0) (e := j); sp.
  apply X with (b := b'); sp.

  generalize (eq_term_equals_sym_tsp2 ts eqa eqb v1 B1 v2 B2); introv i.
  repeat (dest_imp i hyp); repnd.
  assert (eqa a' a) as e' by sp.
  generalize (i a a' e e'); intro eqt; rw eqt.
  generalize (ftspb a' a e'); intro tspb.
  onedtsp uv tys tyt tyst tyvr tes tet tevr tygs tygt dum.
  apply tes.
  generalize (eq_family_trans1 eqa eqb a' a'0 a b b' ts v1 B1 v2 B2 j e'); sp.

Abort.
*)

Lemma weq_bar_trans {o} :
  forall ts uk lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B' t1 t2 t3,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> weq_bar lib eqa eqb t1 t2
    -> weq_bar lib eqa eqb t2 t3
    -> weq_bar lib eqa eqb t1 t3.
Proof.
  introv tsa tsb pera perb.

  dup tsb as transb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep in transb.

  eapply in_open_bar_ext_comb; try exact pera; clear pera.
  eapply in_open_bar_ext_comb; try exact perb; clear perb.
  apply in_ext_ext_implies_in_open_bar_ext; introv perb pera.

  eapply weq_trans; eauto; eauto 3 with slow.
Qed.

Hint Resolve sp_implies_ccequivc_ext_apply : slow.

Lemma weq_bar_resp {o} :
  forall ts uk lib (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) A v B A' v' B' t t',
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> weq_bar lib eqa eqb t t
    -> ccequivc_ext lib t t'
    -> weq_bar lib eqa eqb t t'.
Proof.
  introv tsa tsb per ceq.

  dup tsb as respb.
  dup tsb as transb.
  dup tsb as symb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_respecting_dep in respb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_transitive_dep in transb.
  apply in_ext_ext_type_sys_props4_dep_implies_in_ext_term_equality_symmetric_dep in symb.

  eapply in_open_bar_ext_pres; eauto; clear per; introv per.
  eapply weq_cequivc; eauto; eauto 3 with slow.
Qed.

Lemma per_w_bar_sym {o} :
  forall ts uk lib (T1 T2 : @CTerm o) A A' v v' B B' equ eqa eqb,
    ccomputes_to_valc_ext lib T1 (mkc_w A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 ts uk lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_w_bar ts uk lib T1 T2 equ
    -> per_w_bar ts uk lib T2 T1 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_w_bar in *; exrepnd.
  exists eqa0 eqb0; dands; auto;[].
  eapply type_family_ext_sym; eauto 3 with slow.
Qed.

Lemma per_bar_per_w_bar_sym {o} :
  forall (ts : cts(o)) uk lib T T' A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> per_bar (per_w_bar ts) uk lib T T' eq
    -> per_bar (per_w_bar ts) uk lib T' T eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  eapply per_w_bar_sym; try exact comp; eauto.
Qed.

Lemma per_w_bar_sym_rev {o} :
  forall ts uk lib (T1 T2 : @CTerm o) A A' v v' B B' equ eqa eqb,
    ccomputes_to_valc_ext lib T1 (mkc_w A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib
                  (fun lib' x =>
                     forall a a' (e : eqa lib' x a a'),
                       type_sys_props4 ts uk lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_w_bar ts uk lib T2 T1 equ
    -> per_w_bar ts uk lib T1 T2 equ.
Proof.
  introv comp tspa tspb per.

  unfold per_w_bar in *; exrepnd.
  exists eqa0 eqb0; dands; auto;[].

  eapply type_family_ext_value_respecting_trans3;
    try (exact tspa);
    try (exact tspb); eauto; eauto 3 with slow.
Qed.

Lemma per_bar_per_w_bar_sym_rev {o} :
  forall (ts : cts(o)) uk lib T T' A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> per_bar (per_w_bar ts) uk lib T' T eq
    -> per_bar (per_w_bar ts) uk lib T T' eq.
Proof.
  introv tsa tsb comp per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  eapply ccomputes_to_valc_ext_monotone in comp;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  eapply per_w_bar_sym_rev; try exact comp; eauto.
Qed.

Lemma per_w_bar_w_trans1 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts uk lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_w_bar ts uk lib T T2 eq2
    -> per_w_bar ts uk lib T1 T eq1
    -> per_w_bar ts uk lib T1 T2 eq1.
Proof.
  introv comp tspa tspb pera perb.
  unfold per_w_bar in *; exrepnd.
  exists eqa0 eqb0; dands; auto.
  eapply type_family_ext_trans1; eauto 3 with slow.
Qed.

Lemma per_bar_per_w_bar_trans1 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> per_bar (per_w_bar ts) uk lib T1 T eq1
    -> per_bar (per_w_bar ts) uk lib T T2 eq2
    -> per_bar (per_w_bar ts) uk lib T1 T2 eq1.
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

  eapply per_w_bar_w_trans1; try exact comp; eauto.
Qed.

Lemma per_w_bar_w_trans2 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts uk lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_w_bar ts uk lib T T2 eq2
    -> per_w_bar ts uk lib T1 T eq1
    -> per_w_bar ts uk lib T1 T2 eq2.
Proof.
  introv comp tspa tspb pera perb.
  unfold per_w_bar in *; exrepnd.
  exists eqa1 eqb1; dands; auto.
  eapply type_family_ext_trans2; eauto 3 with slow.
Qed.

Lemma per_bar_per_w_bar_trans2 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> per_bar (per_w_bar ts) uk lib T1 T eq1
    -> per_bar (per_w_bar ts) uk lib T T2 eq2
    -> per_bar (per_w_bar ts) uk lib T1 T2 eq2.
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

  eapply per_w_bar_w_trans2; try exact comp; eauto.
Qed.

Lemma per_w_bar_w_trans3 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext lib T (mkc_w A' v' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts uk lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_w_bar ts uk lib T T2 eq2
    -> per_w_bar ts uk lib T1 T eq1
    -> per_w_bar ts uk lib T1 T2 eq1.
Proof.
  introv comp tspa tspb pera perb.
  apply (per_w_bar_w_trans1 ts uk lib T T1 T2 eq1 eq2 eqa eqb A' v' B' A v B);
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
                  ts uk lib' (eqa lib' e) (eqb lib' e) v B v' B') as w.
    repeat (autodimp w hyp); repnd.

    pose proof (w a a' e0 e1) as w.
    eapply type_sys_props4_change_per;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.

Lemma per_w_bar_w_trans4 {o} :
  forall ts uk lib (T T1 T2 : @CTerm o) eq1 eq2 eqa eqb A v B A' v' B',
    ccomputes_to_valc_ext lib T (mkc_w A' v' B')
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts uk lib' (B)[[v\\a]] (B')[[v'\\a']] (eqb lib' x a a' e))
    -> per_w_bar ts uk lib T T2 eq2
    -> per_w_bar ts uk lib T1 T eq1
    -> per_w_bar ts uk lib T1 T2 eq2.
Proof.
  introv comp tspa tspb pera perb.
  apply (per_w_bar_w_trans2 ts uk lib T T1 T2 eq1 eq2 eqa eqb A' v' B' A v B);
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
                  ts uk lib' (eqa lib' e) (eqb lib' e) v B v' B') as w.
    repeat (autodimp w hyp); repnd.

    pose proof (w a a' e0 e1) as w.
    eapply type_sys_props4_change_per;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.

Lemma per_bar_per_w_bar_trans3 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_w A' v' B')
    -> per_bar (per_w_bar ts) uk lib T1 T eq1
    -> per_bar (per_w_bar ts) uk lib T T2 eq2
    -> per_bar (per_w_bar ts) uk lib T1 T2 eq1.
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

  eapply per_w_bar_w_trans3; try exact comp; eauto.
Qed.

Lemma per_bar_per_w_bar_trans4 {o} :
  forall (ts : cts(o)) uk lib T T1 T2 A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq1 eq2,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_w A' v' B')
    -> per_bar (per_w_bar ts) uk lib T1 T eq1
    -> per_bar (per_w_bar ts) uk lib T T2 eq2
    -> per_bar (per_w_bar ts) uk lib T1 T2 eq2.
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

  eapply per_w_bar_w_trans4; try exact comp; eauto.
Qed.

Lemma ccequivc_ext_w {o} :
  forall lib (T T' : @CTerm o) A v B,
    ccequivc_ext lib T T'
    -> ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> ccomputes_to_valc_ext lib T' (mkc_w A v B).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans1_per_w {o} :
  forall uk lib ts T T' eq A A' v v' B B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_w A v B)
    -> T' ===>(lib) (mkc_w A' v' B')
    -> in_ext_ext lib (fun lib' x => close ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close ts uk lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 (close ts) uk lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> (eq <=2=> (weq_bar lib eqa eqb))
    -> type_equality_respecting_trans1 (close ts) uk lib T T'.
Proof.
  introv tsts dou comp1 comp2 cla tsa clb tsb eqiff.
  introv ee ceq cl.
  repndors; subst.

  {
    dup ceq as c.
    eapply ccequivc_ext_w in ceq;[|eauto]; exrepnd; spcast.
    dclose_lr; clear cl.
    apply per_bar_per_w_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_w_bar1;
      try exact h; try exact comp1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_w in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_w_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_w_bar1;
      try exact h; try exact comp2; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_w in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_w_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_w_bar2;
      try exact h; try exact comp1; eauto 3 with slow.
  }

  {
    dup ceq as c.
    eapply ccequivc_ext_w in ceq;[|eauto]; exrepnd; spcast.
    dup tsa as tsa'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    dup tsb as tsb'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb'; eauto.
    dclose_lr; clear cl.
    apply per_bar_per_w_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_w_bar2;
      try exact h; try exact comp2; eauto 3 with slow.
  }
Qed.

Lemma type_value_respecting_trans_per_bar_per_w_bar3 {o} :
  forall uk lib (ts : cts(o)) T T1 T2 A v B C w D (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A C (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 ts uk lib' (B)[[v\\a]] (D)[[w\\a']] (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_w A v B)
    -> ccequivc_ext lib T1 T2
    -> per_bar (per_w_bar ts) uk lib T T1 eq
    -> per_bar (per_w_bar ts) uk lib T T2 eq.
Proof.
  introv tsa tsb comp1 ceqa per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; try exact per1; clear per1; introv per1.

  unfold per_w_bar in *; exrepnd.

  eapply ccomputes_to_valc_ext_monotone in comp1;[|exact e].

  apply (implies_in_ext_ext_ts_raise_lib_per _ _ _ _ e) in tsa.
  apply (implies_in_ext_ext_ts_raise_lib_per_fam _ _ _ _ e) in tsb.

  dup per2 as tf.

  exists eqa1 eqb0; dands; auto.
  eapply type_family_ext_value_respecting_trans5; eauto; eauto 3 with slow.
Qed.

Lemma implies_type_value_respecting_trans2_per_w {o} :
  forall uk lib ts T T' eq A A' v v' B B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    type_system ts
    -> defines_only_universes ts
    -> T ===>(lib) (mkc_w A v B)
    -> T' ===>(lib) (mkc_w A' v' B')
    -> in_ext_ext lib (fun lib' x => close ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), close ts uk lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 (close ts) uk lib' (B) [[v \\ a]] (B') [[v' \\ a']] (eqb lib' x a a' e))
    -> (eq <=2=> (weq_bar lib eqa eqb))
    -> type_equality_respecting_trans2 (close ts) uk lib T T'.
Proof.
  introv tsts dou comp1 comp2 cla tsa clb tsb eqiff.
  introv ee cl ceq.
  repndors; subst.

  {
    dclose_lr.
    apply per_bar_per_w_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_w_bar3; eauto.
  }

  {
    apply in_ext_ext_type_sys_props4_sym in tsa.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb;[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_w_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_w_bar3; eauto.
  }

  {
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb';[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_w_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_w_bar3; try exact tsa; try exact tsb; eauto.
    eapply per_bar_per_w_bar_sym_rev; try exact tsa; try exact tsb; auto.
  }

  {
    dup tsa as tsa'.
    dup tsb as tsb'.
    apply in_ext_ext_type_sys_props4_sym in tsa'.
    eapply in_ext_ext_type_sys_props4_fam_sym in tsb';[|eauto].
    dclose_lr; clear cl.
    apply per_bar_per_w_bar_implies_close.
    eapply type_value_respecting_trans_per_bar_per_w_bar3; try exact tsa'; try exact tsb'; eauto.
    eapply per_bar_per_w_bar_sym_rev; try exact tsa'; try exact tsb'; auto.
  }
Qed.