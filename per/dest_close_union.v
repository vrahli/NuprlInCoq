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

Require Export close_util_union.
Require Export dest_close_util.


(*Definition per_union_bar_or {o} ts lib (T T' : @CTerm o) eq :=
  per_union ts lib T T' eq
  {+} per_bar ts lib T T' eq.*)

Lemma per_union_implies_per_bar {o} :
  forall inh ts lib (T T' : @CTerm o) eq,
    per_union inh ts lib T T' eq
    -> per_bar inh (per_union inh ts) lib T T' eq.
Proof.
  introv per.

  unfold per_union, per_bar in *; exrepnd.
  exists (per_union_eq_bar_lib_per eqa eqb).
  dands; auto.

  {
    apply in_ext_ext_implies_in_open_bar_ext.
    introv.
    exists (raise_lib_per inh eqa e) (raise_lib_per inh eqb e) A1 A2 B1 B2; simpl.
    dands; spcast; eauto 3 with slow;
      apply implies_in_ext_ext_ts_raise_lib_per; auto.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv.
    apply eq_term_equals_sym.
    apply per_bar_eq_per_union_eq_bar_lib_per.
  }
Qed.
Hint Resolve per_union_implies_per_bar : slow.

Lemma cequivc_ext_mkc_union_right {o} :
  forall inh lib (a b c d : @CTerm o),
    ccequivc_ext inh lib (mkc_union a b) (mkc_union c d)
    -> ccequivc_ext inh lib a c # ccequivc_ext inh lib b d.
Proof.
  introv ceq; dands; introv ext; pose proof (ceq lib' ext) as q; simpl in q;
    clear ceq; spcast; apply cequivc_decomp_union in q; sp.
Qed.

Lemma per_union_eq_bar_change_pers {o} :
  forall inh ts (lib lib0 : @library o) A A' B B' A1 A2 A3 A4 B1 B2 B3 B4
         (eqa eqb : lib-per(inh,lib,o)) (eqa1 eqa2 eqb1 eqb2 : lib-per(inh,lib0,o)) t1 t2,
    lib_extends inh lib0 lib
    -> ccequivc_ext inh lib0 A4 A2
    -> ccequivc_ext inh lib0 B4 B2
    -> ccequivc_ext inh lib0 A3 A1
    -> ccequivc_ext inh lib0 B3 B1
    -> ccequivc_ext inh lib0 A1 A
    -> ccequivc_ext inh lib0 B1 B
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' B B' (eqb lib' x))
    -> in_ext_ext inh lib0 (fun lib' x => ts lib' A1 A2 (eqa1 lib' x))
    -> in_ext_ext inh lib0 (fun lib' x => ts lib' B1 B2 (eqb1 lib' x))
    -> in_ext_ext inh lib0 (fun lib' x => ts lib' A3 A4 (eqa2 lib' x))
    -> in_ext_ext inh lib0 (fun lib' x => ts lib' B3 B4 (eqb2 lib' x))
    -> per_union_eq_bar inh lib0 eqa2 eqb2 t1 t2
    -> per_union_eq_bar inh lib0 eqa1 eqb1 t1 t2.
Proof.
  introv ext ceqa ceqb ceqc ceqd ceqe ceqf.
  introv tya tyb tsa tsb tsc tsd per.

  eapply implies_eq_term_equals_per_union_bar;[| |eauto];
    apply in_ext_ext_implies_in_open_bar_ext;[|].

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
    eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
      try (exact tyb); eauto.

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
        try exact tyb; eauto 3 with slow. }

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies in tsd;
        try exact tyb; eauto 3 with slow.
      eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
        try exact tyb; eauto 3 with slow. }
  }
Qed.

Lemma per_union_eq_bar_change_pers2 {o} :
  forall inh ts (lib lib0 : @library o) T T' A A' B B' (eqa eqb : lib-per(inh,lib,o)) eqa' eqb' t1 t2,
    lib_extends inh lib0 lib
    -> (T ===>(inh,lib) (mkc_union A B))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' B B' (eqb lib' x))
    -> per_union inh ts lib0 T T' eqa'
    -> per_union inh ts lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp tya tyb pera perb eqs.
  unfold per_union in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  hide_hyp perb0.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_union_right in ceq.
  apply cequivc_ext_mkc_union_right in ceq0.
  apply cequivc_ext_mkc_union_right in ceq1.
  repnd.

  apply pera1 in eqs.
  apply perb1.

  eapply (per_union_eq_bar_change_pers inh ts lib lib0 A A' B B' A1 A2 A0 A3 B1 B2 B0 B3); eauto; eauto 3 with slow.
Qed.

Lemma per_union_eq_bar_change_pers3 {o} :
  forall inh ts (lib lib0 : @library o) T T' A A' B B' (eqa eqb : lib-per(inh,lib,o)) eqa' eqb' t1 t2,
    lib_extends inh lib0 lib
    -> (T' ===>(inh,lib) (mkc_union A B))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' B B' (eqb lib' x))
    -> per_union inh ts lib0 T T' eqa'
    -> per_union inh ts lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp tya tyb pera perb eqs.
  unfold per_union in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  hide_hyp perb0.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_union_right in ceq.
  apply cequivc_ext_mkc_union_right in ceq0.
  apply cequivc_ext_mkc_union_right in ceq1.
  repnd.

  apply pera1 in eqs.
  apply perb1.

  eapply (per_union_eq_bar_change_pers inh ts lib lib0 A A' B B' A2 A1 A3 A0 B2 B1 B3 B0); eauto; eauto 3 with slow.
Qed.

Lemma local_per_bar_per_union {o} :
  forall inh (ts : cts(o)) lib T A B A' B' (eqa eqb : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' B B' (eqb lib' x))
    -> T ===>(inh,lib) (mkc_union A B)
    -> local_ts_T inh (per_bar inh (per_union inh ts)) lib T.
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

    unfold per_union in *; exrepnd.
    exists eqa1 eqb0 A1 A2 B1 B2; dands; auto.

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
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    hide_hyp xx1.
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_union_right in ceq.
    apply cequivc_ext_mkc_union_right in ceq0.
    apply cequivc_ext_mkc_union_right in ceq1.
    repnd.

    eapply (per_union_eq_bar_change_pers inh ts lib lib'0 A A' B B' A1 A2 A0 A3 B1 B2 B0 B3); eauto.
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

    eapply (per_union_eq_bar_change_pers2 inh ts lib lib'2 T T' A A' B B');
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_union : slow.

Lemma local_per_bar_per_union2 {o} :
  forall inh (ts : cts(o)) lib T A B A' B' (eqa eqb : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A' A (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' B' B (eqb lib' x))
    -> T ===>(inh,lib) (mkc_union A B)
    -> local_ts_T2 inh (per_bar inh (per_union inh ts)) lib T.
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

    unfold per_union in *; exrepnd.
    exists eqa1 eqb0 A1 A2 B1 B2; dands; auto.

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
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    hide_hyp xx1.
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_union_right in ceq.
    apply cequivc_ext_mkc_union_right in ceq0.
    apply cequivc_ext_mkc_union_right in ceq1.
    repnd.

    applydup @in_ext_ext_type_sys_props4_sym in tsa.
    applydup @in_ext_ext_type_sys_props4_sym in tsb.
    eapply (per_union_eq_bar_change_pers inh ts lib lib'0 A A' B B' A2 A1 A3 A0 B2 B1 B3 B0); eauto.
    { eapply in_ext_ext_type_ceq_sym; try exact tsa0; auto. }
    { eapply in_ext_ext_type_ceq_sym; try exact tsb0; auto. }
    { eauto 3 with slow. }
    { eauto 3 with slow. }
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
    applydup @in_ext_ext_type_sys_props4_sym in tsb.

    eapply (per_union_eq_bar_change_pers3 inh ts lib lib'2 T0 T A A' B B');
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_union2 : slow.



(* ====== dest lemmas ====== *)

Lemma dest_close_per_union_l {o} :
  forall inh (ts : cts(o)) lib T A B A' B' T' eq (eqa eqb : lib-per(inh,lib,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' B B' (eqb lib' x))
    -> ccomputes_to_valc_ext inh lib T (mkc_union A B)
    -> close inh ts lib T T' eq
    -> per_bar inh (per_union inh (close inh ts)) lib T T' eq.
Proof.
  introv tysys dou tsa tsb comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_union; spcast; try exact comp; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply (reca (raise_lib_per inh eqa e) (raise_lib_per inh eqb e)); eauto 3 with slow.
Qed.

Lemma dest_close_per_union_r {o} :
  forall inh (ts : cts(o)) lib T A B A' B' T' eq (eqa eqb : lib-per(inh,lib,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A' A (eqa lib' x))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' B' B (eqb lib' x))
    -> ccomputes_to_valc_ext inh lib T' (mkc_union A B)
    -> close inh ts lib T T' eq
    -> per_bar inh (per_union inh (close inh ts)) lib T T' eq.
Proof.
  introv tysys dou tsa tsb comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_union2; spcast; try exact comp; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply (reca (raise_lib_per inh eqa e) (raise_lib_per inh eqb e)); eauto 3 with slow.
Qed.

(*Lemma dest_close_per_union_bar_l {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar bar (fun lib => T ===>(inh,lib) (mkc_union A B))
    -> close inh ts lib T T' eq
    -> per_union_bar_or (close inh ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_union_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_union_bar_r {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar bar (fun lib => T' ===>(inh,lib) (mkc_union A B))
    -> close inh ts lib T T' eq
    -> per_union_bar_or (close inh ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_union_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_union_ceq_bar_l {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> T ==b==>(bar) (mkc_union A B)
    -> close inh ts lib T T' eq
    -> per_union_bar_or (close inh ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_union_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_union_ceq_bar_r {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> T' ==b==>(bar) (mkc_union A B)
    -> close inh ts lib T T' eq
    -> per_union_bar_or (close inh ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_union_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.*)

(*Lemma dest_close_per_eunion_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_eunion A B)
    -> close inh ts lib T T' eq
    -> per_eunion (close inh ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_eunion_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_eunion A B)
    -> close inh ts lib T T' eq
    -> per_eunion (close inh ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.*)
