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

Require Export close_util_qlt.
Require Export dest_close_util.


Lemma per_qlt_implies_per_bar {o} :
  forall ts uk lib (T T' : @CTerm o) eq,
    per_qlt ts uk lib T T' eq
    -> per_bar (per_qlt ts) uk lib T T' eq.
Proof.
  introv per.

  unfold per_qlt in *; exrepnd.
  exists (equality_of_qlt_bar_lib_per lib a b).
  dands; auto; eauto 3 with slow.

  {
    apply in_ext_ext_implies_in_open_bar_ext.
    introv.
    eexists; eexists; eexists; eexists; dands; eauto 3 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv.
    apply eq_term_equals_sym.
    apply per_bar_eq_equality_of_qlt_bar_lib_per.
  }
Qed.
Hint Resolve per_qlt_implies_per_bar : slow.

Lemma approx_decomp_qlt {o} :
  forall lib (a b c d : @NTerm o),
    approx lib (mk_qlt a b) (mk_qlt c d)
    <=> approx lib a c # approx lib b d.
Proof.
  split; unfold mk_union; introv Hyp.
  - applydup @approx_relates_only_progs in Hyp. repnd.
    apply  approx_canonical_form2 in Hyp.
    unfold lblift in Hyp.
    repnd; allsimpl.
    alpharelbtd; GC.
    applydup @isprogram_qlt_iff in Hyp1.
    applydup @isprogram_qlt_iff in Hyp0.
    repnd.
    eapply blift_approx_open_nobnd in Hyp1bt; eauto 3 with slow.
    eapply blift_approx_open_nobnd in Hyp0bt; eauto 3 with slow.
  - repnd.
    applydup @approx_relates_only_progs in Hyp; repnd.
    applydup @approx_relates_only_progs in Hyp0; repnd.
    apply approx_canonical_form3.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      repndors; subst; tcsp; apply implies_isprogram_bt0; eauto 3 with slow.
    + apply isprogram_ot_iff. allsimpl. dands; auto. introv Hin.
      repndors; subst; tcsp; apply implies_isprogram_bt0; eauto 3 with slow.
    + unfold lblift. allsimpl. split; auto.
      introv Hin. unfold selectbt.
      repeat(destruct n; try (omega;fail); allsimpl);
      apply blift_approx_open_nobnd2; sp.
Qed.

Lemma cequiv_decomp_qlt {o} :
  forall lib (a b c d : @NTerm o),
    cequiv lib (mk_qlt a b) (mk_qlt c d)
    <=> cequiv lib a c # cequiv lib b d.
Proof.
  intros.
  unfold cequiv.
  generalize (approx_decomp_qlt lib a b c d); intro X.
  trewrite X; clear X.
  generalize (approx_decomp_qlt lib c d a b); intro X.
  trewrite X; clear X.
  split; sp.
Qed.

Lemma cequivc_decomp_qlt {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib (mkc_qlt a b) (mkc_qlt c d)
    <=> cequivc lib a c # cequivc lib b d.
Proof.
  introv; destruct_cterms; unfold cequivc; simpl.
  apply cequiv_decomp_qlt.
Qed.

Lemma cequivc_ext_mkc_qlt_right {o} :
  forall lib (a b c d : @CTerm o),
    ccequivc_ext lib (mkc_qlt a b) (mkc_qlt c d)
    -> ccequivc_ext lib a c # ccequivc_ext lib b d.
Proof.
  introv ceq; dands; introv ext; pose proof (ceq lib' ext) as q; simpl in q;
    clear ceq; spcast; apply cequivc_decomp_qlt in q; sp.
Qed.

Lemma per_qlt_eq_bar_change_pers2 {o} :
  forall ts uk (lib lib0 : @library o) T T' a b eqa' eqb' t1 t2,
    lib_extends lib0 lib
    -> (T ===>(lib) (mkc_qlt a b))
    -> per_qlt ts uk lib0 T T' eqa'
    -> per_qlt ts uk lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp pera perb eqs.
  unfold per_qlt in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qlt_right in ceq.
  apply cequivc_ext_mkc_qlt_right in ceq0.
  apply cequivc_ext_mkc_qlt_right in ceq1.
  repnd.

  apply pera1 in eqs.
  apply perb1.

  eapply implies_eq_term_equals_per_qlt_bar2; try exact eqs; eauto 3 with slow.
Qed.

Lemma per_qlt_eq_bar_change_pers3 {o} :
  forall ts uk (lib lib0 : @library o) T T' a b eqa' eqb' t1 t2,
    lib_extends lib0 lib
    -> (T' ===>(lib) (mkc_qlt a b))
    -> per_qlt ts uk lib0 T T' eqa'
    -> per_qlt ts uk lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp pera perb eqs.
  unfold per_qlt in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_qlt_right in ceq.
  apply cequivc_ext_mkc_qlt_right in ceq0.
  apply cequivc_ext_mkc_qlt_right in ceq1.
  repnd.

  apply pera1 in eqs.
  apply perb1.

  eapply implies_eq_term_equals_per_qlt_bar2; try exact eqs; eauto 3 with slow.
Qed.

Lemma local_per_bar_per_qlt {o} :
  forall (ts : cts(o)) uk lib T a b,
    T ===>(lib) (mkc_qlt a b)
    -> local_ts_T (per_bar (per_qlt ts)) uk lib T.
Proof.
  introv comp eqiff alla.
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

    unfold per_qlt in *; exrepnd.
    eexists; eexists; eexists; eexists; dands; eauto 3 with slow.

    apply eq_term_equals_sym; introv; split; introv w.

    { exists lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
             (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)
             (Flib lib' ext) (lib_extends_refl (Flib lib' ext)).
      exists lib'0 xtb.
      exists xtd (lib_extends_refl lib'0); auto.
      apply alla2; auto. }

    exrepnd.

    pose proof (alla0 lib1 ext1 lib2 ext2 extz) as xx; simpl in *; repnd; clear xx.
    assert (lib_extends lib4 lib2) as xte by eauto 3 with slow.
    pose proof (xx0 lib3 ext3 lib'0 (lib_extends_trans w ext4) z) as xx0; simpl in *.

    exrepnd.
    apply xx0 in w0.

    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    hide_hyp xx0.
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_qlt_right in ceq.
    apply cequivc_ext_mkc_qlt_right in ceq0.
    apply cequivc_ext_mkc_qlt_right in ceq1.
    repnd.

    eapply implies_eq_term_equals_per_qlt_bar2; try exact w0; eauto 3 with slow.
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

    eapply (per_qlt_eq_bar_change_pers2 ts uk lib lib'2 T T' a b);
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_qlt : slow.

Lemma local_per_bar_per_qlt2 {o} :
  forall (ts : cts(o)) uk lib T a b,
    T ===>(lib) (mkc_qlt a b)
    -> local_ts_T2 (per_bar (per_qlt ts)) uk lib T.
Proof.
  introv comp eqiff alla.
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

    unfold per_qlt in *; exrepnd.
    eexists; eexists; eexists; eexists; dands; eauto 3 with slow.

    apply eq_term_equals_sym; introv; split; introv w.

    { exists lib' ext (Flib lib' ext) (lib_extends_refl (Flib lib' ext))
             (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)
             (Flib lib' ext) (lib_extends_refl (Flib lib' ext)).
      exists lib'0 xtb.
      exists xtd (lib_extends_refl lib'0); auto.
      apply alla2; auto. }

    exrepnd.

    pose proof (alla0 lib1 ext1 lib2 ext2 extz) as xx; simpl in *; repnd; clear xx.
    assert (lib_extends lib4 lib2) as xte by eauto 3 with slow.
    pose proof (xx0 lib3 ext3 lib'0 (lib_extends_trans w ext4) z) as xx0; simpl in *.

    exrepnd.
    apply xx0 in w0.

    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    hide_hyp xx0.
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_qlt_right in ceq.
    apply cequivc_ext_mkc_qlt_right in ceq0.
    apply cequivc_ext_mkc_qlt_right in ceq1.
    repnd.
    eapply implies_eq_term_equals_per_qlt_bar2; try exact w0; eauto 3 with slow.
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

    eapply (per_qlt_eq_bar_change_pers3 ts uk lib lib'2 T0 T);
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_qlt2 : slow.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_qlt_l {o} :
  forall (ts : cts(o)) uk lib T a b T' eq,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T (mkc_qlt a b)
    -> close ts uk lib T T' eq
    -> per_bar (per_qlt (close ts)) uk lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_qlt; spcast; try exact comp; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply reca; eauto 3 with slow.
Qed.

Lemma dest_close_per_qlt_r {o} :
  forall (ts : cts(o)) uk lib T a b T' eq,
    type_system ts
    -> defines_only_universes ts
    -> ccomputes_to_valc_ext lib T' (mkc_qlt a b)
    -> close ts uk lib T T' eq
    -> per_bar (per_qlt (close ts)) uk lib T T' eq.
Proof.
  introv tysys dou comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_qlt2; spcast; try exact comp; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply reca; eauto 3 with slow.
Qed.
