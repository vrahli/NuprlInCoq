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


Definition per_eq_bar_or {o} ts lib (T T' : @CTerm o) eq :=
  per_eq_bar ts lib T T' eq
  {+} per_bar ts lib T T' eq.

Lemma local_equality_of_eq_bar {o} :
  forall (lib : @library o) a b (eqa : lib-per(lib,o)) t1 t2,
    in_open_bar_ext lib (fun lib' (x : lib_extends lib' lib) => eq_per_eq_bar lib' a b (raise_lib_per eqa x) t1 t2)
    -> eq_per_eq_bar lib a b eqa t1 t2.
Proof.
  introv alla.
  unfold eq_per_eq_bar; apply e_all_in_ex_bar_ext_as.
  apply in_open_bar_ext_dup.
  eapply in_open_bar_ext_pres; eauto; clear alla.
  introv h.
  unfold eq_per_eq_bar in h; apply e_all_in_ex_bar_ext_as in h.
  eapply in_open_bar_ext_pres; eauto; clear h.
  introv h; introv.
  simpl in *.
  unfold raise_ext_per in *.
  unfold eq_per_eq in *; repnd; dands; auto.
  eapply (lib_per_cond lib eqa);eauto 4 with slow.
Qed.

(*Definition per_eq_eq_lib_per
           {o}
           {lib : @library o}
           (eqa : lib-per(lib,o)) (a1 a2 : @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) =>
            per_eq_eq lib' a1 a2 (raise_lib_per eqa x)).

  repeat introv.
  unfold per_eq_eq, per_eq_eq1, raise_lib_per, raise_ext_per; simpl.
  split; intro h; exrepnd.

  - exists bar; introv br ext; introv.
    pose proof (h0 _ br _ ext x) as h0; simpl in *; repnd.
    dands; auto.
    eapply (lib_per_cond _ eqa); eauto.

  - exists bar; introv br ext; introv.
    pose proof (h0 _ br _ ext x) as h0; simpl in *; repnd.
    dands; auto.
    eapply (lib_per_cond _ eqa); eauto.
Defined.

Lemma per_eq_bar_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_eq_bar ts lib T T' eq
    -> per_bar (per_eq_bar ts) lib T T' eq.
Proof.
  introv per.

  unfold per_eq_bar in *; exrepnd.

  assert (all_in_bar_ext bar (fun lib' x => forall y, (eqa lib' x) <=2=> (eqa lib' y))) as w.
  {
    introv br ext; introv.
    pose proof (per4 _ br _ ext x) as q; simpl in q.
    pose proof (per4 _ br _ ext y) as h; simpl in h.
    eapply (lib_per_cond lib eqa); eauto.
  }

  exists (trivial_bar lib) (per_eq_eq_lib_per eqa a1 a2).
  dands; auto.

  - introv br ext; introv; simpl in *.
    exists A B a1 a2 b1 b2.
    exists (raise_lib_per eqa x); dands; auto.
    exists (raise_bar bar x); dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv; split; intro h.

    + introv br ext; introv.
      simpl in *.
      eapply sub_per_per_eq_eq; eauto.

    + pose proof (h lib (lib_extends_refl lib) lib (lib_extends_refl lib) (lib_extends_refl lib)) as h; simpl in *; auto.
      unfold per_eq_eq, per_eq_eq1, raise_lib_per in *; simpl in *; exrepnd.
      apply (implies_all_in_bar_ext_intersect_bars_left _ bar) in h0.
      apply (implies_all_in_bar_ext_intersect_bars_right _ bar0) in w.
      exists (intersect_bars bar0 bar); dands.
      introv br ext; introv.
      pose proof (h0 _ br _ ext x) as h0; simpl in h0.
      repnd; dands; auto.
      eapply w; eauto.
Qed.
Hint Resolve per_eq_bar_implies_per_bar : slow.*)

Lemma per_eq_implies_per_eq_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_eq ts lib T T' eq
    -> per_eq_bar ts lib T T' eq.
Proof.
  introv per.
  unfold per_eq in per; exrepnd.
  unfold per_eq_bar.
  exists A B a1 a2 b1 b2 eqa.
  dands; auto; eauto 3 with slow.
Qed.
Hint Resolve per_eq_implies_per_eq_bar : slow.

Lemma simple_implies_iff_per_eq_eq {o} :
  forall (lib : @library o) a b (eqa eqb : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> (eq_per_eq_bar lib a b eqa) <=2=> (eq_per_eq_bar lib a b eqb).
Proof.
  introv alla; introv.
  unfold eq_per_eq_bar, eq_per_eq; split; introv h; exrepnd;
    apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as.

  - eapply in_open_bar_ext_comb;[|exact h];clear h.
    eapply in_open_bar_ext_comb;[|exact alla];clear alla.
    apply in_ext_ext_implies_in_open_bar_ext; introv alla h.
    repnd; dands; tcsp.
    apply alla; auto.

  - eapply in_open_bar_ext_comb;[|exact h];clear h.
    eapply in_open_bar_ext_comb;[|exact alla];clear alla.
    apply in_ext_ext_implies_in_open_bar_ext; introv alla h.
    repnd; dands; tcsp.
    apply alla; auto.
Qed.
Hint Resolve simple_implies_iff_per_eq_eq : slow.

Lemma ccequivc_ext_mkc_equality_implies {o} :
  forall lib (a b c d A B : @CTerm o),
    ccequivc_ext lib (mkc_equality a b A) (mkc_equality c d B)
    -> ccequivc_ext lib a c # ccequivc_ext lib b d # ccequivc_ext lib A B.
Proof.
  introv ceq; dands; introv ext; pose proof (ceq lib' ext) as q; simpl in q;
    clear ceq; spcast; apply cequivc_decomp_equality in q; sp.
Qed.

Lemma eq_per_eq_bar_respects_ccequivc_ext {o} :
  forall lib (a1 a2 b1 b2 : @CTerm o) (eqa : lib-per(lib,o)) t1 t2,
    in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> eq_per_eq_bar lib a1 b1 eqa t1 t2
    -> ccequivc_ext lib a1 a2
    -> ccequivc_ext lib b1 b2
    -> eq_per_eq_bar lib a2 b2 eqa t1 t2.
Proof.
  introv resp sym trans per ceqa ceqb.
  unfold eq_per_eq_bar in *; exrepnd.
  apply e_all_in_ex_bar_ext_as in per; apply e_all_in_ex_bar_ext_as.
  eapply in_open_bar_ext_comb; eauto; clear per.
  apply in_ext_ext_implies_in_open_bar_ext; introv per.
  unfold eq_per_eq in *; repnd; dands; auto.

  eapply lib_extends_preserves_ccequivc_ext in ceqa;[|exact e].
  eapply lib_extends_preserves_ccequivc_ext in ceqb;[|exact e].
  eapply (resp _ e) in ceqa;[|eapply (trans _ e); eauto; apply (sym _ e); auto].
  eapply (resp _ e) in ceqb;[|eapply (trans _ e); eauto; apply (sym _ e); auto].

  eapply (trans _ e);[apply (sym _ e);eauto|].
  eapply (trans _ e);[|eauto]; auto.
Qed.
Hint Resolve eq_per_eq_bar_respects_ccequivc_ext : slow.

Lemma implies_eq_term_equals_eq_per_eq_bar {o} :
  forall (lib : @library o) a b c d (eqa eqb : lib-per(lib,o)),
    in_open_bar_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_open_bar lib (fun lib' => ccequivc_ext lib' a c)
    -> in_open_bar lib (fun lib' => ccequivc_ext lib' b d)
    -> in_open_bar_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> (eq_per_eq_bar lib a b eqa) <=2=> (eq_per_eq_bar lib c d eqb).
Proof.
  introv resp sym tran ceqa ceqb alla; introv.
  unfold eq_per_eq_bar, eq_per_eq; split; introv h; exrepnd;
    apply e_all_in_ex_bar_ext_as in h; apply e_all_in_ex_bar_ext_as.

  - eapply in_open_bar_ext_comb;[|exact h];clear h.
    eapply in_open_bar_ext_comb;[|exact alla];clear alla.
    eapply in_open_bar_ext_comb2;[|exact ceqa];clear ceqa.
    eapply in_open_bar_ext_comb2;[|exact ceqb];clear ceqb.
    eapply in_open_bar_ext_comb;[|exact resp];clear resp.
    eapply in_open_bar_ext_comb;[|exact sym];clear sym.
    eapply in_open_bar_ext_comb;[|exact tran];clear tran.

    apply in_ext_ext_implies_in_open_bar_ext; introv tran sym resp ceqb ceqa alla h.
    repnd; dands; tcsp.
    apply alla; auto.
    eapply pre_commutes; eauto.

  - eapply in_open_bar_ext_comb;[|exact h];clear h.
    eapply in_open_bar_ext_comb;[|exact alla];clear alla.
    eapply in_open_bar_ext_comb2;[|exact ceqa];clear ceqa.
    eapply in_open_bar_ext_comb2;[|exact ceqb];clear ceqb.
    eapply in_open_bar_ext_comb;[|exact resp];clear resp.
    eapply in_open_bar_ext_comb;[|exact sym];clear sym.
    eapply in_open_bar_ext_comb;[|exact tran];clear tran.

    apply in_ext_ext_implies_in_open_bar_ext; introv tran sym resp ceqb ceqa alla h.
    repnd; dands; tcsp.
    apply alla in h; auto.
    eapply pre_commutes; try apply ccequivc_ext_sym; eauto; eauto 3 with slow.
Qed.
Hint Resolve implies_eq_term_equals_eq_per_eq_bar : slow.

Lemma eq_per_eq_bar_change_pers {o} :
  forall ts (lib lib0 : @library o) A A' A1 A2 A3 A4
         a1 a2 b1 b2
         (eqa : lib-per(lib,o)) (eqa1 eqa2 : lib-per(lib0,o)) t1 t2,
    lib_extends lib0 lib
    -> ccequivc_ext lib0 A4 A2
    -> ccequivc_ext lib0 A3 A1
    -> ccequivc_ext lib0 A1 A
    -> ccequivc_ext lib0 a1 b1
    -> ccequivc_ext lib0 a2 b2
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib0 (fun lib' x => ts lib' A1 A2 (eqa1 lib' x))
    -> in_ext_ext lib0 (fun lib' x => ts lib' A3 A4 (eqa2 lib' x))
    -> eq_per_eq_bar lib0 a1 a2 eqa2 t1 t2
    -> eq_per_eq_bar lib0 b1 b2 eqa1 t1 t2.
Proof.
  introv ext ceqa ceqb ceqc ceqd ceqe.
  introv tya tsa tsb per.

  eapply implies_eq_term_equals_eq_per_eq_bar; try exact per;
    try apply in_ext_implies_in_open_bar;
    try apply in_ext_ext_implies_in_open_bar_ext;
    eauto 3 with slow.

  {
    eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
      try (exact tya); eauto.

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
        try exact tya; eauto 3 with slow. }

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies in tsb;
        try exact tya; eauto 3 with slow.
      eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
        try exact tya; eauto 3 with slow. }
  }
Qed.

Lemma eq_per_eq_bar_change_pers2 {o} :
  forall ts (lib lib0 : @library o) T T' a b A A' (eqa : lib-per(lib,o)) eqa' eqb' t1 t2,
    lib_extends lib0 lib
    -> (T ===>(lib) (mkc_equality a b A))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_eq ts lib0 T T' eqa'
    -> per_eq ts lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp tya pera perb eqs.
  unfold per_eq in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq.
  apply ccequivc_ext_mkc_equality_implies in ceq0.
  apply ccequivc_ext_mkc_equality_implies in ceq1.
  repnd.

  apply pera0 in eqs.
  apply perb0.

  eapply (eq_per_eq_bar_change_pers ts lib lib0 A A' A0 B A1 B0 a0 a3 a1 a2); eauto; eauto 3 with slow.
Qed.

Lemma eq_per_eq_bar_change_pers3 {o} :
  forall ts (lib lib0 : @library o) T T' A A' a b (eqa : lib-per(lib,o)) eqa' eqb' t1 t2,
    lib_extends lib0 lib
    -> (T' ===>(lib) (mkc_equality a b A))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> per_eq ts lib0 T T' eqa'
    -> per_eq ts lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp tya pera perb eqs.
  unfold per_eq in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq.
  apply ccequivc_ext_mkc_equality_implies in ceq0.
  apply ccequivc_ext_mkc_equality_implies in ceq1.
  repnd.

  apply pera0 in eqs.
  apply perb0.

  eapply (eq_per_eq_bar_change_pers ts lib lib0 A A' B A0 B0 A1 a0 a3 a1 a2); eauto; eauto 3 with slow.
Qed.

Lemma local_per_bar_per_eq_bar {o} :
  forall (ts : cts(o)) lib T a b A B (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> T ===>(lib) (mkc_equality a b A)
    -> local_ts_T (per_bar (per_eq ts)) lib T.
Proof.
  introv tsp comp eqiff alla.
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
    pose proof (alla2 _ (lib_extends_refl _)) as alla2; simpl in *.

    assert (lib_extends
              (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
                     (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                     (lib_extends_refl (Flib lib' ext))) lib') as xta by eauto 3 with slow.

    exists (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
                  (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                  (lib_extends_refl (Flib lib' ext))) xta.
    introv xtb xtc.
    assert (lib_extends lib'0 (Flib lib' ext)) as xtd by eauto 3 with slow.
    pose proof (alla2 _ xtb xtd) as alla2; simpl in *.

    unfold per_eq in *; exrepnd.
    exists A0 B0 a1 a2 b1 b2 eqa1; dands; auto.

    apply eq_term_equals_sym; introv; split; introv w.

    { exists lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
             (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)
             (Flib lib' ext) (lib_extends_refl (Flib lib' ext)).
      exists lib'0 xtb.
      exists xtd (lib_extends_refl lib'0); auto.
      apply alla3; auto. }

    exrepnd.

    pose proof (alla0 lib1 ext1 lib2 ext2 extz) as xx; simpl in *; repnd; clear xx.
    assert (lib_extends lib4 lib2) as xte by eauto 3 with slow.
    pose proof (xx0 lib3 ext3 lib'0 (lib_extends_trans w ext4) z) as xx0; simpl in *.

    exrepnd.
    apply xx1 in w0.

    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    hide_hyp xx0.
    computes_to_eqval_ext.
    apply ccequivc_ext_mkc_equality_implies in ceq.
    apply ccequivc_ext_mkc_equality_implies in ceq0.
    apply ccequivc_ext_mkc_equality_implies in ceq1.
    repnd.

    eapply (eq_per_eq_bar_change_pers ts lib lib'0 A B A0 B0 A1 B1 a0 a3 a1 a2); eauto.
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

    assert (lib_extends lib'' lib') as xta by eauto 3 with slow.
    exists lib'' xta; introv xtb; introv.

    assert (lib_extends lib'' lib) as xtc by eauto 3 with slow.
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

    eapply (eq_per_eq_bar_change_pers2 ts lib lib'2 T T' a b A B);
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_eq_bar : slow.

Lemma implies_eq_term_equals_eq_per_eq {o} :
  forall lib a b (eqa eqb : per(o)),
    (eqa <=2=> eqb)
    -> (eq_per_eq lib a b eqa) <=2=> (eq_per_eq lib a b eqb).
Proof.
  introv eqas; introv.
  unfold eq_per_eq; introv; split; intro h; introv; repnd; dands; auto; apply eqas; auto.
Qed.

Lemma per_bar_eq_eq_per_eq_bar_lib_per {o} :
  forall (lib : @library o) a b (eqa : lib-per(lib,o)),
    (per_bar_eq lib (eq_per_eq_bar_lib_per lib a b eqa))
    <=2=> (eq_per_eq_bar lib a b eqa).
Proof.
  introv; simpl; unfold per_bar_eq; split; intro h; eauto 3 with slow.

  - unfold eq_per_eq_bar; apply e_all_in_ex_bar_ext_as.
    eapply in_open_bar_ext_dup.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold eq_per_eq_bar in h.
    apply e_all_in_ex_bar_ext_as in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_eq_per_eq; try exact h;
      try apply (lib_per_cond _ eqa).

  - unfold eq_per_eq_bar in *.
    apply e_all_in_ex_bar_ext_as in h.
    apply in_open_bar_ext_twice in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    unfold eq_per_eq_bar.
    apply e_all_in_ex_bar_ext_as.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; introv; simpl in *.
    eapply implies_eq_term_equals_eq_per_eq; try exact h;
      try apply (lib_per_cond _ eqa).
Qed.

Lemma per_eq_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_eq ts lib T T' eq
    -> per_bar (per_eq ts) lib T T' eq.
Proof.
  introv per.

  unfold per_eq in *; exrepnd.
  exists (eq_per_eq_bar_lib_per lib a1 a2 eqa).
  dands; auto.

  {
    apply in_ext_ext_implies_in_open_bar_ext.
    introv.
    exists A B a1 a2 b1 b2 (raise_lib_per eqa e); simpl.
    dands; spcast; eauto 3 with slow.
    apply (implies_in_ext_ext_raise_ext_per (fun lib e => ts lib A B e)); auto.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv.
    apply eq_term_equals_sym.
    apply per_bar_eq_eq_per_eq_bar_lib_per.
  }
Qed.
Hint Resolve per_eq_implies_per_bar : slow.

Lemma local_per_bar_per_eq_bar2 {o} :
  forall (ts : cts(o)) lib T a b A B (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B A (eqa lib' x))
    -> T ===>(lib) (mkc_equality a b A)
    -> local_ts_T2 (per_bar (per_eq ts)) lib T.
Proof.
  introv tsp comp eqiff alla.
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
    pose proof (alla2 _ (lib_extends_refl _)) as alla2; simpl in *.

    assert (lib_extends
              (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
                     (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                     (lib_extends_refl (Flib lib' ext))) lib') as xta by eauto 3 with slow.

    exists (Flib2 lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
                  (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext) (Flib lib' ext)
                  (lib_extends_refl (Flib lib' ext))) xta.
    introv xtb xtc.
    assert (lib_extends lib'0 (Flib lib' ext)) as xtd by eauto 3 with slow.
    pose proof (alla2 _ xtb xtd) as alla2; simpl in *.

    unfold per_eq in *; exrepnd.
    exists A0 B0 a1 a2 b1 b2 eqa1; dands; auto.

    apply eq_term_equals_sym; introv; split; introv w.

    { exists lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
             (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)
             (Flib lib' ext) (lib_extends_refl (Flib lib' ext)).
      exists lib'0 xtb.
      exists xtd (lib_extends_refl lib'0); auto.
      apply alla3; auto. }

    exrepnd.

    pose proof (alla0 lib1 ext1 lib2 ext2 extz) as xx; simpl in *; repnd; clear xx.
    assert (lib_extends lib4 lib2) as xte by eauto 3 with slow.
    pose proof (xx0 lib3 ext3 lib'0 (lib_extends_trans w ext4) z) as xx0; simpl in *.

    exrepnd.
    apply xx1 in w0.

    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    hide_hyp xx0.
    computes_to_eqval_ext.
    apply ccequivc_ext_mkc_equality_implies in ceq.
    apply ccequivc_ext_mkc_equality_implies in ceq0.
    apply ccequivc_ext_mkc_equality_implies in ceq1.
    repnd.

    applydup @in_ext_ext_type_sys_props4_sym in tsp.
    eapply (eq_per_eq_bar_change_pers ts lib lib'0 A B B0 A0 B1 A1 a0 a3 a1 a2); eauto.
    { eapply in_ext_ext_type_ceq_sym; auto; try exact tsp0; auto. }
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

    assert (lib_extends lib'' lib') as xta by eauto 3 with slow.
    exists lib'' xta; introv xtb; introv.

    assert (lib_extends lib'' lib) as xtc by eauto 3 with slow.
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

    applydup @in_ext_ext_type_sys_props4_sym in tsp.

    eapply (eq_per_eq_bar_change_pers3 ts lib lib'2 T0 T A B);
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_eq_bar2 : slow.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_equality_l {o} :
  forall (ts : cts(o)) lib T a b A B T' eq (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A B (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_bar (per_eq (close ts)) lib T T' eq.
Proof.
  introv tysys dou tsp comp cl; try unfold per_eq_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_eq_bar; spcast; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply (reca (raise_lib_per eqa e)); eauto 3 with slow.
Qed.

Lemma dest_close_per_equality_r {o} :
  forall (ts : cts(o)) lib T a b A B T' eq (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' B A (eqa lib' x))
    -> ccomputes_to_valc_ext lib T' (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_bar (per_eq (close ts)) lib T T' eq.
Proof.
  introv tysys dou tsp comp cl; unfold per_eq_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_eq_bar2; spcast; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply (reca (raise_lib_per eqa e)); eauto 3 with slow.
Qed.

(*Lemma dest_close_per_equality_bar_l {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar bar (fun lib => T ===>(lib) (mkc_equality a b A))
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_eq_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_bar_r {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar bar (fun lib => T' ===>(lib) (mkc_equality a b A))
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_eq_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_ceq_bar_l {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> T ==b==>(bar) (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_eq_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_ceq_bar_r {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> T' ==b==>(bar) (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_eq_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.*)
