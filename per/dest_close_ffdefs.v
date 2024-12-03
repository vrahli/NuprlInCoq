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

Require Export close_util_ffdefs.
Require Export dest_close_util.


Lemma per_ffdefs_implies_per_bar {o} :
  forall ts uk lib (T T' : @CTerm o) eq,
    per_ffdefs ts uk lib T T' eq
    -> per_bar (per_ffdefs ts) uk lib T T' eq.
Proof.
  introv per.

  unfold per_ffdefs in *; exrepnd.
  exists (per_ffdefs_eq_bar_lib_per lib eqa x1).
  dands; auto.

  {
    apply in_ext_ext_implies_in_open_bar_ext.
    introv.
    exists A1 A2 x1 x2 (raise_lib_per eqa e); simpl.
    dands; spcast; eauto 3 with slow;
      try (apply implies_in_ext_ext_ts_raise_lib_per; auto);
      try (introv; apply per4).
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv.
    apply eq_term_equals_sym.
    apply per_bar_eq_per_ffdefs_eq_bar_lib_per.
  }
Qed.
Hint Resolve per_ffdefs_implies_per_bar : slow.

Lemma ex_nodefsc_change_per_and_term {o} :
  forall (eqa : per(o))
         (eqb : per(o))
         t1 t2 t,
    term_equality_transitive eqa
    -> term_equality_symmetric eqa
    -> (eqa <=2=> eqb)
    -> eqa t1 t
    -> eqb t2 t
    -> ex_nodefsc eqa t1
    -> ex_nodefsc eqb t2.
Proof.
  introv trans sym imp eqt1 eqt2 h.
  unfold ex_nodefsc in *; exrepnd.
  exists u; dands; auto; apply imp; auto.
  eapply trans;[|eauto].
  eapply trans;[apply imp;eauto|].
  apply sym; auto.
Qed.
Hint Resolve ex_nodefsc_change_per_and_term : slow.

Lemma implies_eq_term_equals_per_ffdefs_bar {p} :
  forall lib (eqa1 eqa2 : lib-per(lib,p)) t1 t2 t,
    in_ext_ext lib (fun lib' x => term_equality_transitive (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa1 lib' x))
    -> in_open_bar_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x t1 t)
    -> in_ext_ext lib (fun lib' x => eqa2 lib' x t2 t)
    -> (per_ffdefs_eq_bar lib eqa1 t1) <=2=> (per_ffdefs_eq_bar lib eqa2 t2).
Proof.
  introv trans sym eqta eqt1 eqt2 ; introv.
  unfold per_ffdefs_eq_bar; split; introv h; exrepnd;
      eapply in_open_bar_ext_comb; try exact eqta; clear eqta;
        eapply in_open_bar_ext_pres; eauto; clear h; introv h eqta;
          unfold per_ffdefs_eq in *; repnd; dands; eauto 3 with slow.
  eapply ex_nodefsc_change_per_and_term; try exact h; eauto 3 with slow.
  apply eq_term_equals_sym; eauto 3 with slow.
Qed.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive_ext {o} :
  forall ts uk lib lib' (ext : lib_extends lib' lib) (A A1 A2 : @CTerm o) (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A1 (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts uk lib'' A A2 (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts.
  applydup @in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive in tsp.
  eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 ts uk ext) in tsp;
    try exact tsts;[].
  apply (lib_extends_preserves_in_ext_ext ext) in tsp0.
  introv h1 h2.
  apply tsp.
  eapply tsp0; apply tsp; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive_ext : slow.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric_ext {o} :
  forall ts uk lib lib' (ext : lib_extends lib' lib) (A A1 A2 : @CTerm o) (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A1 (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts uk lib'' A A2 (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts.
  applydup @in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric in tsp.
  eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 ts uk ext) in tsp;
    try exact tsts;[].
  apply (lib_extends_preserves_in_ext_ext ext) in tsp0.
  introv h1.
  apply tsp.
  eapply tsp0; apply tsp; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric_ext : slow.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive_ext2 {o} :
  forall ts uk lib lib' (ext : lib_extends lib' lib) (A A1 A2 : @CTerm o) (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A1 A (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts uk lib'' A2 A (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts.
  applydup @in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive in tsp.
  eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals5 ts uk ext) in tsp;
    try exact tsts;[].
  apply (lib_extends_preserves_in_ext_ext ext) in tsp0.
  introv h1 h2.
  apply tsp.
  eapply tsp0; apply tsp; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive_ext2 : slow.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric_ext2 {o} :
  forall ts uk lib lib' (ext : lib_extends lib' lib) (A A1 A2 : @CTerm o) (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A1 A (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts uk lib'' A2 A (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts.
  applydup @in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric in tsp.
  eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals5 ts uk ext) in tsp;
    try exact tsts;[].
  apply (lib_extends_preserves_in_ext_ext ext) in tsp0.
  introv h1.
  apply tsp.
  eapply tsp0; apply tsp; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric_ext2 : slow.

Lemma approx_decomp_free_from_defs {o} :
  forall lib (a b c d : @NTerm o),
    approx lib (mk_free_from_defs a b) (mk_free_from_defs c d)
    <=> approx lib a c # approx lib b d.
Proof.
  split; unfold mk_union; introv Hyp.
  - applydup @approx_relates_only_progs in Hyp. repnd.
    apply  approx_canonical_form2 in Hyp.
    unfold lblift in Hyp.
    repnd; allsimpl.
    alpharelbtd; GC.
    applydup @isprogram_free_from_defs_iff in Hyp1.
    applydup @isprogram_free_from_defs_iff in Hyp0.
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
      repeat(destruct n; try (lia;fail); allsimpl);
      apply blift_approx_open_nobnd2; sp.
Qed.

Lemma cequiv_decomp_free_from_defs {o} :
  forall lib (a b c d : @NTerm o),
    cequiv lib (mk_free_from_defs a b) (mk_free_from_defs c d)
    <=> cequiv lib a c # cequiv lib b d.
Proof.
  intros.
  unfold cequiv.
  generalize (approx_decomp_free_from_defs lib a b c d); intro X.
  trewrite X; clear X.
  generalize (approx_decomp_free_from_defs lib c d a b); intro X.
  trewrite X; clear X.
  split; sp.
Qed.

Lemma cequivc_decomp_free_from_defs {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib (mkc_free_from_defs a b) (mkc_free_from_defs c d)
    <=> cequivc lib a c # cequivc lib b d.
Proof.
  introv; destruct_cterms; unfold cequivc, mkc_cequiv; simpl.
  apply cequiv_decomp_free_from_defs.
Qed.

Lemma cequivc_ext_mkc_free_from_defs_right {o} :
  forall lib (a b c d : @CTerm o),
    ccequivc_ext lib (mkc_free_from_defs a b) (mkc_free_from_defs c d)
    -> ccequivc_ext lib a c # ccequivc_ext lib b d.
Proof.
  introv ceq; dands; introv ext; pose proof (ceq lib' ext) as q; simpl in q;
    clear ceq; spcast; apply cequivc_decomp_free_from_defs in q; sp.
Qed.

Lemma ex_nodefsc_change_per_ceq {o} :
  forall (eqa : per(o))
         (eqb : per(o))
         lib t1 t2,
    term_equality_respecting lib eqa
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> (eqa <=2=> eqb)
    -> ccequivc_ext lib t1 t2
    -> ex_nodefsc eqa t1
    -> ex_nodefsc eqb t2.
Proof.
  introv resp sym tran imp ceq h.
  unfold ex_nodefsc in *; exrepnd.
  exists u; dands; auto; apply imp; auto.
  apply resp in ceq.
  { eapply tran; eauto. }
  eapply tran;[eauto|]; apply sym; auto.
Qed.
Hint Resolve ex_nodefsc_change_per_ceq : slow.

Lemma eq_term_equals_preserves_term_equality_respecting {o} :
  forall lib (eqa1 eqa2 : per(o)),
    eqa1 <=2=> eqa2
    -> term_equality_respecting lib eqa1
    -> term_equality_respecting lib eqa2.
Proof.
  introv eqiff resp h ceq; apply eqiff; apply resp; auto; apply eqiff; auto.
Qed.
Hint Resolve eq_term_equals_preserves_term_equality_respecting : slow.

Lemma implies_eq_term_equals_eq_ffdefs_eq2 {o} :
  forall lib (eqa eqb : per(o)) f g,
    term_equality_respecting lib eqa
    -> term_equality_symmetric eqa
    -> term_equality_transitive eqa
    -> ccequivc_ext lib f g
    -> (eqa <=2=> eqb)
    -> (per_ffdefs_eq lib eqa f) <=2=> (per_ffdefs_eq lib eqb g).
Proof.
  introv resp sym trans ceq h; introv; split; intro p; induction p; auto; repnd.

  - unfold per_ffdefs_eq; dands; tcsp.
    eapply ex_nodefsc_change_per_ceq; eauto.

  - unfold per_ffdefs_eq; dands; tcsp.
    eapply ex_nodefsc_change_per_ceq; try exact b; try apply ccequivc_ext_sym;
      eauto 3 with slow; try apply eq_term_equals_sym; auto.
Qed.

Lemma implies_eq_term_equals_per_ffdefs_eq_bar {o} :
  forall lib (eqa eqb : lib-per(lib,o)) f g,
    in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> ccequivc_ext lib f g
    -> in_ext_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> (per_ffdefs_eq_bar lib eqa f) <=2=> (per_ffdefs_eq_bar lib eqb g).
Proof.
  introv trans sym resp ceq h; introv.
  unfold per_ffdefs_eq_bar; split; intro q; exrepnd;
      eapply in_open_bar_ext_pres; eauto; clear q; introv q;
        eapply implies_eq_term_equals_eq_ffdefs_eq2; try exact q; eauto 3 with slow;
          try (apply eq_term_equals_sym; eapply h).
Qed.

Lemma per_ffdefs_eq_bar_change_pers {o} :
  forall ts uk (lib lib0 : @library o) A A' A1 A2 A3 A4
         (eqa : lib-per(lib,o)) (eqa1 eqa2 : lib-per(lib0,o)) f g t1 t2,
    lib_extends lib0 lib
    -> ccequivc_ext lib0 A4 A2
    -> ccequivc_ext lib0 A3 A1
    -> ccequivc_ext lib0 A1 A
    -> ccequivc_ext lib0 f g
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> in_ext_ext lib0 (fun lib' x => ts uk lib' A1 A2 (eqa1 lib' x))
    -> in_ext_ext lib0 (fun lib' x => ts uk lib' A3 A4 (eqa2 lib' x))
    -> per_ffdefs_eq_bar lib0 eqa2 f t1 t2
    -> per_ffdefs_eq_bar lib0 eqa1 g t1 t2.
Proof.
  introv ext ceqa ceqc ceqd ceqe.
  introv tya tsa tsb per.

  eapply implies_eq_term_equals_per_ffdefs_eq_bar; try exact per; eauto 3 with slow.

  eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
    try (exact tya); eauto.

  { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
      try exact tya; eauto 3 with slow. }

  { eapply trans_ccequivc_ext_in_ext_eq_types_implies in tsb;
      try exact tya; eauto 3 with slow.
    eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
      try exact tya; eauto 3 with slow. }
Qed.

Lemma per_ffdefs_eq_bar_change_pers2 {o} :
  forall ts uk (lib lib0 : @library o) T T' A A' f (eqa : lib-per(lib,o)) eqa' eqb' t1 t2,
    lib_extends lib0 lib
    -> (T ===>(lib) (mkc_free_from_defs A f))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_ffdefs ts uk lib0 T T' eqa'
    -> per_ffdefs ts uk lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp tya pera perb eqs.
  unfold per_ffdefs in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq.
  apply cequivc_ext_mkc_free_from_defs_right in ceq0.
  apply cequivc_ext_mkc_free_from_defs_right in ceq1.
  repnd.

  apply pera0 in eqs.
  apply perb0.

  eapply (per_ffdefs_eq_bar_change_pers ts uk lib lib0 A A' A1 A2 A0 A3); eauto; eauto 3 with slow.
Qed.

Lemma per_ffdefs_eq_bar_change_pers3 {o} :
  forall ts uk (lib lib0 : @library o) T T' A A' f (eqa : lib-per(lib,o)) eqa' eqb' t1 t2,
    lib_extends lib0 lib
    -> (T' ===>(lib) (mkc_free_from_defs A f))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> per_ffdefs ts uk lib0 T T' eqa'
    -> per_ffdefs ts uk lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp tya pera perb eqs.
  unfold per_ffdefs in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_free_from_defs_right in ceq.
  apply cequivc_ext_mkc_free_from_defs_right in ceq0.
  apply cequivc_ext_mkc_free_from_defs_right in ceq1.
  repnd.

  apply pera0 in eqs.
  apply perb0.

  eapply (per_ffdefs_eq_bar_change_pers ts uk lib lib0 A A' A2 A1 A3 A0); eauto; eauto 3 with slow.
Qed.

Lemma local_per_bar_per_ffdefs {o} :
  forall (ts : cts(o)) uk lib T A a A' (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A A' (eqa lib' x))
    -> T ===>(lib) (mkc_free_from_defs A a)
    -> local_ts_T (per_bar (per_ffdefs ts)) uk lib T.
Proof.
  introv tsa comp eqiff alla.
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

    unfold per_ffdefs in *; exrepnd.
    exists A1 A2 x1 x2 eqa1; dands; auto.

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
    apply cequivc_ext_mkc_free_from_defs_right in ceq.
    apply cequivc_ext_mkc_free_from_defs_right in ceq0.
    apply cequivc_ext_mkc_free_from_defs_right in ceq1.
    repnd.

    pose proof (implies_eq_term_equals_per_ffdefs_bar lib'0 eqa1 eqa2 x1 x0) as xx.

    eapply (per_ffdefs_eq_bar_change_pers ts uk lib lib'0 A A' A1 A2 A0 A3); eauto.
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

    eapply (per_ffdefs_eq_bar_change_pers2 ts uk lib lib'2 T T' A A');
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_ffdefs : slow.

Lemma local_per_bar_per_ffdefs2 {o} :
  forall (ts : cts(o)) uk lib T A a A' (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts uk lib' A' A (eqa lib' x))
    -> T ===>(lib) (mkc_free_from_defs A a)
    -> local_ts_T2 (per_bar (per_ffdefs ts)) uk lib T.
Proof.
  introv tsa comp eqiff alla.
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

    unfold per_ffdefs in *; exrepnd.
    exists A1 A2 x1 x2 eqa1; dands; auto.

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
    apply cequivc_ext_mkc_free_from_defs_right in ceq.
    apply cequivc_ext_mkc_free_from_defs_right in ceq0.
    apply cequivc_ext_mkc_free_from_defs_right in ceq1.
    repnd.

    applydup @in_ext_ext_type_sys_props4_sym in tsa.
    eapply (per_ffdefs_eq_bar_change_pers ts uk lib lib'0 A A' A2 A1 A3 A0); eauto.
    { eapply (in_ext_ext_type_ceq_sym ts uk lib lib'0); auto; try exact tsa0; auto. }
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

    applydup @in_ext_ext_type_sys_props4_sym in tsa.

    eapply (per_ffdefs_eq_bar_change_pers3 ts uk lib lib'2 T0 T A A');
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_ffdefs2 : slow.



(* ====== dest lemmas ====== *)

Lemma dest_close_per_ffdefs_l {o} :
  forall (ts : cts(o)) uk lib T A a A' T' eq (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_free_from_defs A a)
    -> close ts uk lib T T' eq
    -> per_bar (per_ffdefs (close ts)) uk lib T T' eq.
Proof.
  introv tysys dou tsa comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_ffdefs; spcast; try exact comp; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply (reca (raise_lib_per eqa e)); eauto 3 with slow.
Qed.

Lemma dest_close_per_ffdefs_r {o} :
  forall (ts : cts(o)) uk lib T A a A' T' eq (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) uk lib' A' A (eqa lib' x))
    -> ccomputes_to_valc_ext lib T' (mkc_free_from_defs A a)
    -> close ts uk lib T T' eq
    -> per_bar (per_ffdefs (close ts)) uk lib T T' eq.
Proof.
  introv tysys dou tsa comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_ffdefs2; spcast; try exact comp; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply (reca (raise_lib_per eqa e)); eauto 3 with slow.
Qed.
