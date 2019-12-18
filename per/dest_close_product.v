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


Require Export dest_close_tacs.
Require Export bar_fam.
Require Export per_ceq_bar.
Require Export nuprl_mon_func.
Require Export local.

Require Export close_util_product.
Require Export dest_close_util.


Lemma per_product_bar_implies_per_bar {o} :
  forall inh ts lib (T T' : @CTerm o) eq,
    per_product_bar inh ts lib T T' eq
    -> per_bar inh (per_product_bar inh ts) lib T T' eq.
Proof.
  introv per.

  unfold per_product_bar in *; exrepnd.
  exists (per_product_eq_bar_lib_per eqa eqb).
  dands; auto.

  {
    apply in_ext_ext_implies_in_open_bar_ext.
    introv.
    exists (raise_lib_per inh eqa e) (raise_lib_per_fam inh eqb e); simpl.
    dands; spcast; eauto 3 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv.
    apply eq_term_equals_sym.
    apply per_bar_eq_per_product_eq_bar_lib_per.
  }
Qed.
Hint Resolve per_product_bar_implies_per_bar : slow.

Lemma per_product_eq_bar_change_pers {o} :
  forall inh ts (lib lib0 : @library o) A A' v B v' B' A1 A2 A3 A4 v1 B1 v2 B2 v3 B3 v4 B4
         (eqa : lib-per(inh,lib,o))
         (eqb : lib-per-fam(inh,lib,eqa,o))
         (eqa1 eqa2 : lib-per(inh,lib0,o))
         (eqb1 : lib-per-fam(inh,lib0,eqa1,o))
         (eqb2 : lib-per-fam(inh,lib0,eqa2,o))
         t1 t2,
    lib_extends inh lib0 lib
    -> ccequivc_ext inh lib0 A4 A2
    -> bcequivc_ext inh lib0 [v4] B4 [v2] B2
    -> ccequivc_ext inh lib0 A3 A1
    -> bcequivc_ext inh lib0 [v3] B3 [v1] B1
    -> ccequivc_ext inh lib0 A1 A
    -> bcequivc_ext inh lib0 [v1] B1 [v] B
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> in_ext_ext inh lib0 (fun lib' x => ts lib' A1 A2 (eqa1 lib' x))
    -> in_ext_ext inh lib0 (fun lib' x => forall a a' (e : eqa1 lib' x a a'), ts lib' (substc a v1 B1) (substc a' v2 B2) (eqb1 lib' x a a' e))
    -> in_ext_ext inh lib0 (fun lib' x => ts lib' A3 A4 (eqa2 lib' x))
    -> in_ext_ext inh lib0 (fun lib' x => forall a a' (e : eqa2 lib' x a a'), ts lib' (substc a v3 B3) (substc a' v4 B4) (eqb2 lib' x a a' e))
    -> per_product_eq_bar inh lib0 eqa2 eqb2 t1 t2
    -> per_product_eq_bar inh lib0 eqa1 eqb1 t1 t2.
Proof.
  introv ext ceqa ceqb ceqc ceqd ceqe ceqf.
  introv tya tyb tsa tsb tsc tsd per.

  eapply implies_eq_term_equals_per_product_eq_bar;[| |eauto].

  {
    eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
      try (exact tya); eauto.

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
        try exact tya; eauto 3 with slow. }

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies in tsc;
        try exact tya; eauto 3 with slow.
      eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
        try exact tya; eauto 3 with slow. }
  }

  {
    pose proof (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4
                  inh ts ext A A' A2 eqa eqa1) as q1.
    repeat (autodimp q1 hype);[|].

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
        try exact tya; eauto 3 with slow. }

    pose proof (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4
                  inh ts ext A A' A4 eqa eqa2) as q2.
    repeat (autodimp q2 hyp);[|].

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
        try exact tya; try exact tsc; eauto 3 with slow. }

    eapply in_ext_ext_type_sys_props4_fam_implies_in_ext_ext_eq_term_equals_fam2;
      try exact tyb; eauto 3 with slow.

    { eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies;
        try exact tyb; eauto 3 with slow. }

    { eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies in tsd;
        try exact tsa; eauto 3 with slow;[].
      eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies2;
        try exact tsa; eauto 3 with slow. }
  }
Qed.

Lemma per_product_eq_bar_change_pers2 {o} :
  forall inh ts (lib lib0 : @library o) T T' A A' v v' B B'
         (eqa : lib-per(inh,lib,o))
         (eqb : lib-per-fam(inh,lib,eqa,o))
         eqa' eqb' t1 t2,
    lib_extends inh lib0 lib
    -> (T ===>(inh,lib) (mkc_product A v B))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_product_bar inh ts lib0 T T' eqa'
    -> per_product_bar inh ts lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp tya tyb pera perb eqs.
  unfold per_product_bar, type_family_ext in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb3.
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; eauto 3 with slow;[]; repnd.
  apply constructor_inj_implies_ext in ceq0; eauto 3 with slow;[]; repnd.
  apply constructor_inj_implies_ext in ceq1; eauto 3 with slow;[]; repnd.

  apply pera1 in eqs.
  apply perb1.

  eapply (per_product_eq_bar_change_pers
            inh ts lib lib0 A A' v B v' B'
            A0 A'0 A1 A'1
            v0 B0 v'0 B'0
            v1 B1 v'1 B'1); eauto; eauto 3 with slow.
Qed.

Lemma per_product_eq_bar_change_pers3 {o} :
  forall inh ts (lib lib0 : @library o) T T' A A' v v' B B'
         (eqa  : lib-per(inh,lib,o))
         (eqb  : lib-per-fam(inh,lib,eqa,o))
         eqa' eqb' t1 t2,
    lib_extends inh lib0 lib
    -> (T' ===>(inh,lib) (mkc_product A v B))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> per_product_bar inh ts lib0 T T' eqa'
    -> per_product_bar inh ts lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp tya tyb pera perb eqs.
  unfold per_product_bar, type_family_ext in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb3.
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  apply constructor_inj_implies_ext in ceq; eauto 3 with slow;[]; repnd.
  apply constructor_inj_implies_ext in ceq0; eauto 3 with slow;[]; repnd.
  apply constructor_inj_implies_ext in ceq1; eauto 3 with slow;[]; repnd.

  apply pera1 in eqs.
  apply perb1.

  eapply (per_product_eq_bar_change_pers
            inh ts lib lib0 A A' v B v' B'
            A'0 A0 A'1 A1
            v'0 B'0 v0 B0
            v'1 B'1 v1 B1); eauto;
    try (eapply (in_ext_ext_type_ceq_sym_fam _ _ _ _ ext); try exact tya; try exact tyb);
    eauto 3 with slow.
Qed.

Lemma local_per_bar_per_product_bar {o} :
  forall inh (ts : cts(o)) lib T A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         inh lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 inh ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> T ===>(inh,lib) (mkc_product A v B)
    -> local_ts_T inh (per_bar inh (per_product_bar inh ts)) lib T.
Proof.
  introv tsa tsb comp eqiff alla.
  unfold per_bar in *.

  apply in_open_bar_ext_choice in alla; exrepnd.
  apply in_open_bar_eqa_choice in alla0; exrepnd.
  apply in_open_data_open_choice in alla1; exrepnd.
  exists (lib_fun_dep_eqa Feqa Flib2).
  dands.

  {
    introv ext.
    pose proof (alla0 _ ext) as alla1; simpl in *.
    apply in_ext_ext_implies in alla1.
    pose proof (alla1 (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)) as alla1; repnd.
    pose proof (alla2 _ (lib_extends_refl _ _)) as alla2; simpl in *.

    assert (lib_extends _
              (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl _ (Flib lib' ext))
                     (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                     (lib_extends_refl _ (Flib lib' ext))) lib') as xta by eauto 3 with slow.

    exists (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl _ (Flib lib' ext))
                  (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                  (lib_extends_refl _ (Flib lib' ext))) xta.
    introv xtb xtc.
    assert (lib_extends inh lib'0 (Flib lib' ext)) as xtd by eauto 3 with slow.
    pose proof (alla2 _ xtb xtd) as alla2; simpl in *.

    unfold per_product_bar in *; exrepnd.
    exists eqa1 eqb0; dands; tcsp;[].

    apply eq_term_equals_sym; introv; split; introv w.

    { exists lib' ext (Flib lib' ext) (lib_extends_refl inh (Flib lib' ext))
             (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)
             (Flib lib' ext) (lib_extends_refl inh (Flib lib' ext)).
      exists lib'0 xtb.
      exists xtd (lib_extends_refl inh lib'0); auto.
      apply alla2; auto. }

    exrepnd.

    pose proof (alla0 lib1 ext1 lib2 ext2 extz) as xx; simpl in *; repnd; clear xx.
    assert (lib_extends inh lib4 lib2) as xte by eauto 3 with slow.
    pose proof (xx0 lib3 ext3 lib'0 (lib_extends_trans w ext4) z) as xx0; simpl in *.

    exrepnd.
    apply xx0 in w0.

    apply (ccomputes_to_valc_ext_monotone _ _ lib'0) in comp;[|eauto 3 with slow];[].

    unfold type_family_ext in alla3, xx1; exrepnd.

    computes_to_eqval_ext.
    hide_hyp xx3.
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    apply constructor_inj_implies_ext in ceq; eauto 3 with slow;[]; repnd.
    apply constructor_inj_implies_ext in ceq0; eauto 3 with slow;[]; repnd.
    apply constructor_inj_implies_ext in ceq1; eauto 3 with slow;[]; repnd.

    eapply (per_product_eq_bar_change_pers
              inh ts lib lib'0 A A' v B v' B'
              A1 A'1 A0 A'0
              v1 B1 v'1 B'1
              v0 B0 v'0 B'0); eauto.
  }

  {
    rename alla0 into imp.
    eapply eq_term_equals_trans;[eauto|].
    introv.
    split; intro h; exrepnd.

    { eapply eq_per_bar_eq_lib_fun_dep_eqa_part1; eauto. }

    unfold per_bar_eq in *.
    introv ext; simpl in *.

    pose proof (h (Flib lib' ext)) as h; exrepnd; simpl in *.
    autodimp h hyp; eauto 3 with slow;[]; exrepnd.

    assert (lib_extends inh lib'' lib') as xta by eauto 3 with slow.
    exists lib'' xta; introv xtb; introv.

    assert (lib_extends inh lib'' lib) as xtc by eauto 3 with slow.
    pose proof (imp _ ext lib'0 (lib_extends_trans xtb y) z) as imp'; simpl in *; repnd.
    apply imp'; clear imp'.
    introv xtd.

    exists (Flib2 lib' ext lib'0 (lib_extends_trans xtb y) z lib'1 xtd).
    exists (lib_ext_ext (Flib2 lib' ext lib'0 (lib_extends_trans xtb y) z lib'1 xtd)).
    introv xte; introv.

    pose proof (h1 lib'2) as h1; simpl in *.
    repeat (autodimp h1 hyp); eauto 3 with slow.
    exrepnd.

    pose proof (imp'0 lib'1 xtd _ xte z0) as imp'0; simpl in *.

    pose proof (imp lib1 ext1 lib2 ext2 extz) as imp; simpl in *; repnd; clear imp.
    pose proof (imp0 lib3 ext3 lib'2 (lib_extends_trans w ext4) z1) as imp0; simpl in *.

    eapply (per_product_eq_bar_change_pers2 inh ts lib lib'2 T T' A A' v v' B B');
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_product_bar : slow.

Lemma local_per_bar_per_product_bar2 {o} :
  forall inh (ts : cts(o)) lib T A v B A' v' B' (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A' A (eqa lib' x))
    -> in_ext_ext
         inh lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 inh ts lib' (substc a v' B') (substc a' v B) (eqb lib' x a a' e))
    -> T ===>(inh,lib) (mkc_product A v B)
    -> local_ts_T2 inh (per_bar inh (per_product_bar inh ts)) lib T.
Proof.
  introv tsa tsb comp eqiff alla.
  unfold per_bar in *.

  apply in_open_bar_ext_choice in alla; exrepnd.
  apply in_open_bar_eqa_choice in alla0; exrepnd.
  apply in_open_data_open_choice in alla1; exrepnd.
  exists (lib_fun_dep_eqa Feqa Flib2).
  dands.

  {
    introv ext.
    pose proof (alla0 _ ext) as alla1; simpl in *.
    apply in_ext_ext_implies in alla1.
    pose proof (alla1 (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)) as alla1; repnd.
    pose proof (alla2 _ (lib_extends_refl _ _)) as alla2; simpl in *.

    assert (lib_extends _
              (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl _ (Flib lib' ext))
                     (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                     (lib_extends_refl _ (Flib lib' ext))) lib') as xta by eauto 3 with slow.

    exists (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl _ (Flib lib' ext))
                  (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                  (lib_extends_refl _ (Flib lib' ext))) xta.
    introv xtb xtc.
    assert (lib_extends inh lib'0 (Flib lib' ext)) as xtd by eauto 3 with slow.
    pose proof (alla2 _ xtb xtd) as alla2; simpl in *.

    unfold per_product_bar in *; exrepnd.
    exists eqa1 eqb0; dands; auto.

    apply eq_term_equals_sym; introv; split; introv w.

    { exists lib' ext (Flib lib' ext) (lib_extends_refl inh (Flib lib' ext))
             (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)
             (Flib lib' ext) (lib_extends_refl inh (Flib lib' ext)).
      exists lib'0 xtb.
      exists xtd (lib_extends_refl inh lib'0); auto.
      apply alla2; auto. }

    exrepnd.

    pose proof (alla0 lib1 ext1 lib2 ext2 extz) as xx; simpl in *; repnd; clear xx.
    assert (lib_extends inh lib4 lib2) as xte by eauto 3 with slow.
    pose proof (xx0 lib3 ext3 lib'0 (lib_extends_trans w ext4) z) as xx0; simpl in *.

    exrepnd.
    apply xx0 in w0.

    apply (ccomputes_to_valc_ext_monotone _ _ lib'0) in comp;[|eauto 3 with slow];[].

    unfold type_family_ext in alla3, xx1; exrepnd.

    computes_to_eqval_ext.
    hide_hyp xx3.
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    apply constructor_inj_implies_ext in ceq; eauto 3 with slow;[]; repnd.
    apply constructor_inj_implies_ext in ceq0; eauto 3 with slow;[]; repnd.
    apply constructor_inj_implies_ext in ceq1; eauto 3 with slow;[]; repnd.

    applydup @in_ext_ext_type_sys_props4_sym in tsa.
    applydup (@in_ext_ext_type_sys_props4_fam_sym o inh ts lib eqa eqb A' A v' B' v B) in tsb; auto;[].
    eapply (per_product_eq_bar_change_pers
              inh ts lib lib'0 A A' v B v' B'
              A'1 A1 A'0 A0
              v'1 B'1 v1 B1
              v'0 B'0 v0 B0); eauto; eauto 2 with slow.
    { eapply (in_ext_ext_type_ceq_sym_fam _ _ _ _ xtc);
        auto; try exact tsa0; try exact tsb0; auto; eauto 3 with slow. }
    { eauto 3 with slow. }
    { eapply (in_ext_ext_type_ceq_sym_fam _ _ _ _ xtc);
        auto; try exact tsa0; try exact tsb0; auto; eauto 3 with slow. }
  }

  {
    rename alla0 into imp.
    eapply eq_term_equals_trans;[eauto|].
    introv.
    split; intro h; exrepnd.

    { eapply eq_per_bar_eq_lib_fun_dep_eqa_part1; eauto. }

    unfold per_bar_eq in *.
    introv ext; simpl in *.

    pose proof (h (Flib lib' ext)) as h; exrepnd; simpl in *.
    autodimp h hyp; eauto 3 with slow;[]; exrepnd.

    assert (lib_extends inh lib'' lib') as xta by eauto 3 with slow.
    exists lib'' xta; introv xtb; introv.

    assert (lib_extends inh lib'' lib) as xtc by eauto 3 with slow.
    pose proof (imp _ ext lib'0 (lib_extends_trans xtb y) z) as imp'; simpl in *; repnd.
    apply imp'; clear imp'.
    introv xtd.

    exists (Flib2 lib' ext lib'0 (lib_extends_trans xtb y) z lib'1 xtd).
    exists (lib_ext_ext (Flib2 lib' ext lib'0 (lib_extends_trans xtb y) z lib'1 xtd)).
    introv xte; introv.

    pose proof (h1 lib'2) as h1; simpl in *.
    repeat (autodimp h1 hyp); eauto 3 with slow.
    exrepnd.

    pose proof (imp'0 lib'1 xtd _ xte z0) as imp'0; simpl in *.

    pose proof (imp lib1 ext1 lib2 ext2 extz) as imp; simpl in *; repnd; clear imp.
    pose proof (imp0 lib3 ext3 lib'2 (lib_extends_trans w ext4) z1) as imp0; simpl in *.

    applydup @in_ext_ext_type_sys_props4_sym in tsa.
    applydup (@in_ext_ext_type_sys_props4_fam_sym o inh ts lib eqa eqb A' A v' B' v B) in tsb; auto;[].

    eapply (per_product_eq_bar_change_pers3
              inh ts lib lib'2 T0 T A A' v v' B B');
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_product_bar2 : slow.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_product_l {o} :
  forall inh (ts : cts(o)) lib T A v B A' v' B' T' eq (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh (close inh ts) lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T (mkc_product A v B)
    -> close inh ts lib T T' eq
    -> per_bar inh (per_product_bar inh (close inh ts)) lib T T' eq.
Proof.
  introv tysys dou tsa tsb comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_product_bar; spcast; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  eapply (reca (raise_lib_per inh eqa e)); eauto 3 with slow.
Qed.

Lemma dest_close_per_product_r {o} :
  forall inh (ts : cts(o)) lib T A v B A' v' B' T' eq (eqa : lib-per(inh,lib,o)) (eqb : lib-per-fam(inh,lib,eqa,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A' A (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 inh (close inh ts) lib' (substc a v' B') (substc a' v B) (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext inh lib T' (mkc_product A v B)
    -> close inh ts lib T T' eq
    -> per_bar inh (per_product_bar inh (close inh ts)) lib T T' eq.
Proof.
  introv tysys dou tsa tsb comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_product_bar2; spcast; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  eapply (reca (raise_lib_per inh eqa e)); eauto 3 with slow.
Qed.

(*
Definition per_product_bar_or {o} ts lib (T T' : @CTerm o) eq :=
  per_product_bar ts lib T T' eq
  {+} per_bar ts lib T T' eq.

Lemma dest_close_per_product_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_product A v B)
    -> close ts lib T T' eq
    -> per_product_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_product_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_product_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_product A v B)
    -> close ts lib T T' eq
    -> per_product_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_product_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.
*)
