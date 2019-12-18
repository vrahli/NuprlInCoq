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

Require Export close_util_image.
Require Export dest_close_util.



Lemma per_image_implies_per_bar {o} :
  forall inh ts lib (T T' : @CTerm o) eq,
    per_image inh ts lib T T' eq
    -> per_bar inh (per_image inh ts) lib T T' eq.
Proof.
  introv per.

  unfold per_image in *; exrepnd.
  exists (per_image_eq_bar_lib_per inh lib eqa f1).
  dands; auto.

  {
    apply in_ext_ext_implies_in_open_bar_ext.
    introv.
    exists (raise_lib_per inh eqa e) A1 A2 f1 f2; simpl.
    dands; spcast; eauto 3 with slow;
      apply implies_in_ext_ext_ts_raise_lib_per; auto.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv.
    apply eq_term_equals_sym.
    apply per_bar_eq_per_image_eq_bar_lib_per.
  }
Qed.
Hint Resolve per_image_implies_per_bar : slow.

Lemma implies_eq_term_equals_eq_image_eq2 {o} :
  forall inh lib (eqa eqb : per(o)) f g,
    ccequivc_ext inh lib f g
    -> (eqa <=2=> eqb)
    -> (per_image_eq inh lib eqa f) <=2=> (per_image_eq inh lib eqb g).
Proof.
  introv ceq h; introv; split; intro p; induction p; auto.

  - eapply image_eq_cl; eauto.

  - eapply image_eq_eq; try apply h; eauto;
      eapply ccequivc_ext_trans; eauto;
        apply implies_ccequivc_ext_apply; eauto 3 with slow.

  - eapply image_eq_cl; eauto.

  - eapply image_eq_eq; try apply h; eauto;
      eapply ccequivc_ext_trans; eauto;
        apply implies_ccequivc_ext_apply; eauto 3 with slow.
Qed.

Lemma implies_eq_term_equals_per_image_eq_bar {o} :
  forall inh lib (eqa eqb : lib-per(inh,lib,o)) f g,
    ccequivc_ext inh lib f g
    -> in_ext_ext inh lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> (per_image_eq_bar inh lib eqa f) <=2=> (per_image_eq_bar inh lib eqb g).
Proof.
  introv ceq h; introv.
  unfold per_image_eq_bar; split; intro q; exrepnd;
      eapply in_open_bar_ext_pres; eauto; clear q; introv q;
        eapply implies_eq_term_equals_eq_image_eq2; try exact q; eauto 3 with slow;
          apply eq_term_equals_sym; eapply h.
Qed.

Lemma approx_decomp_image {o} :
  forall lib (a b c d : @NTerm o),
    approx lib (mk_image a b) (mk_image c d)
    <=> approx lib a c # approx lib b d.
Proof.
  split; unfold mk_image; introv Hyp.
  - applydup @approx_relates_only_progs in Hyp. repnd.
    apply  approx_canonical_form2 in Hyp.
    unfold lblift in Hyp.
    repnd; allsimpl.
    alpharelbtd; GC.
    applydup @isprogram_image_iff in Hyp1.
    applydup @isprogram_image_iff in Hyp0.
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

Lemma cequiv_decomp_image {o} :
  forall lib (a b c d : @NTerm o),
    cequiv lib (mk_image a b) (mk_image c d)
    <=> cequiv lib a c # cequiv lib b d.
Proof.
  intros.
  unfold cequiv.
  generalize (approx_decomp_image lib a b c d); intro X.
  trewrite X; clear X.
  generalize (approx_decomp_image lib c d a b); intro X.
  trewrite X; clear X.
  split; sp.
Qed.

Lemma cequivc_decomp_image {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib (mkc_image a b) (mkc_image c d)
    <=> cequivc lib a c # cequivc lib b d.
Proof.
  introv.
  introv; destruct_cterms; unfold cequivc, mkc_cequiv; simpl.
  apply cequiv_decomp_image.
Qed.

Lemma cequivc_ext_mkc_image_implies {o} :
  forall inh lib (a b c d : @CTerm o),
    ccequivc_ext inh lib (mkc_image a b) (mkc_image c d)
    -> ccequivc_ext inh lib a c # ccequivc_ext inh lib b d.
Proof.
  introv ceq; dands; introv ext; pose proof (ceq lib' ext) as q; simpl in q;
    clear ceq; spcast; apply cequivc_decomp_image in q; sp.
Qed.

Lemma per_image_eq_bar_change_pers {o} :
  forall inh ts (lib lib0 : @library o) A A' A1 A2 A3 A4
         (eqa : lib-per(inh,lib,o)) (eqa1 eqa2 : lib-per(inh,lib0,o)) f g t1 t2,
    lib_extends inh lib0 lib
    -> ccequivc_ext inh lib0 A4 A2
    -> ccequivc_ext inh lib0 A3 A1
    -> ccequivc_ext inh lib0 A1 A
    -> ccequivc_ext inh lib0 f g
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> in_ext_ext inh lib0 (fun lib' x => ts lib' A1 A2 (eqa1 lib' x))
    -> in_ext_ext inh lib0 (fun lib' x => ts lib' A3 A4 (eqa2 lib' x))
    -> per_image_eq_bar inh lib0 eqa2 f t1 t2
    -> per_image_eq_bar inh lib0 eqa1 g t1 t2.
Proof.
  introv ext ceqa ceqc ceqd ceqe.
  introv tya tsa tsb per.

  eapply implies_eq_term_equals_per_image_eq_bar;[| |eauto]; eauto 3 with slow;[].

  eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
    try (exact tya); eauto.

  { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
      try exact tya; eauto 3 with slow. }

  { eapply trans_ccequivc_ext_in_ext_eq_types_implies in tsb;
      try exact tya; eauto 3 with slow.
    eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
      try exact tya; eauto 3 with slow. }
Qed.

Lemma per_image_eq_bar_change_pers2 {o} :
  forall inh ts (lib lib0 : @library o) T T' A A' f (eqa : lib-per(inh,lib,o)) eqa' eqb' t1 t2,
    lib_extends inh lib0 lib
    -> (T ===>(inh,lib) (mkc_image A f))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> per_image inh ts lib0 T T' eqa'
    -> per_image inh ts lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp tya pera perb eqs.
  unfold per_image in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq.
  apply cequivc_ext_mkc_image_implies in ceq0.
  apply cequivc_ext_mkc_image_implies in ceq1.
  repnd.

  apply pera0 in eqs.
  apply perb0.

  eapply (per_image_eq_bar_change_pers inh ts lib lib0 A A' A1 A2 A0 A3); eauto; eauto 3 with slow.
Qed.

Lemma per_image_eq_bar_change_pers3 {o} :
  forall inh ts (lib lib0 : @library o) T T' A A' f (eqa : lib-per(inh,lib,o)) eqa' eqb' t1 t2,
    lib_extends inh lib0 lib
    -> (T' ===>(inh,lib) (mkc_image A f))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> per_image inh ts lib0 T T' eqa'
    -> per_image inh ts lib0 T T' eqb'
    -> eqa' t1 t2
    -> eqb' t1 t2.
Proof.
  introv ext comp tya pera perb eqs.
  unfold per_image in *; exrepnd.

  apply (ccomputes_to_valc_ext_monotone _ _ lib0) in comp;[|eauto 3 with slow];[].
  computes_to_eqval_ext.
  hide_hyp perb2.
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  apply cequivc_ext_mkc_image_implies in ceq.
  apply cequivc_ext_mkc_image_implies in ceq0.
  apply cequivc_ext_mkc_image_implies in ceq1.
  repnd.

  apply pera0 in eqs.
  apply perb0.

  eapply (per_image_eq_bar_change_pers inh ts lib lib0 A A' A2 A1 A3 A0); eauto; eauto 3 with slow.
Qed.

Lemma local_per_bar_per_image {o} :
  forall inh (ts : cts(o)) lib T A A' f (eqa : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A A' (eqa lib' x))
    -> T ===>(inh,lib) (mkc_image A f)
    -> local_ts_T inh (per_bar inh (per_image inh ts)) lib T.
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

    unfold per_image in *; exrepnd.
    exists eqa1 A1 A2 f1 f2; dands; auto.

    apply eq_term_equals_sym; introv; split; introv w.

    { exists lib' ext (Flib lib' ext) (lib_extends_refl inh (Flib lib' ext))
             (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)
             (Flib lib' ext) (lib_extends_refl inh (Flib lib' ext)).
      exists lib'0 xtb.
      exists xtd (lib_extends_refl inh lib'0); auto.
      apply alla3; auto. }

    exrepnd.

    pose proof (alla0 lib1 ext1 lib2 ext2 extz) as xx; simpl in *; repnd; clear xx.
    assert (lib_extends inh lib4 lib2) as xte by eauto 3 with slow.
    pose proof (xx0 lib3 ext3 lib'0 (lib_extends_trans w ext4) z) as xx0; simpl in *.

    exrepnd.
    apply xx1 in w0.

    apply (ccomputes_to_valc_ext_monotone _ _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    hide_hyp xx0.
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_image_implies in ceq.
    apply cequivc_ext_mkc_image_implies in ceq0.
    apply cequivc_ext_mkc_image_implies in ceq1.
    repnd.

    eapply (per_image_eq_bar_change_pers inh ts lib lib'0 A A' A1 A2 A0 A3); eauto.
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

    eapply (per_image_eq_bar_change_pers2 inh ts lib lib'2 T T' A A');
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_image : slow.

Lemma local_per_bar_per_image2 {o} :
  forall inh (ts : cts(o)) lib T A A' f (eqa : lib-per(inh,lib,o)),
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A' A (eqa lib' x))
    -> T ===>(inh,lib) (mkc_image A f)
    -> local_ts_T2 inh (per_bar inh (per_image inh ts)) lib T.
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

    unfold per_image in *; exrepnd.
    exists eqa1 A1 A2 f1 f2; dands; auto.

    apply eq_term_equals_sym; introv; split; introv w.

    { exists lib' ext (Flib lib' ext) (lib_extends_refl inh (Flib lib' ext))
             (lib_extends_trans (lib_ext_ext (Flib lib' ext)) ext)
             (Flib lib' ext) (lib_extends_refl inh (Flib lib' ext)).
      exists lib'0 xtb.
      exists xtd (lib_extends_refl inh lib'0); auto.
      apply alla3; auto. }

    exrepnd.

    pose proof (alla0 lib1 ext1 lib2 ext2 extz) as xx; simpl in *; repnd; clear xx.
    assert (lib_extends inh lib4 lib2) as xte by eauto 3 with slow.
    pose proof (xx0 lib3 ext3 lib'0 (lib_extends_trans w ext4) z) as xx0; simpl in *.

    exrepnd.
    apply xx1 in w0.

    apply (ccomputes_to_valc_ext_monotone _ _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp xx2.
    computes_to_eqval_ext.
    hide_hyp xx0.
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_image_implies in ceq.
    apply cequivc_ext_mkc_image_implies in ceq0.
    apply cequivc_ext_mkc_image_implies in ceq1.
    repnd.

    applydup @in_ext_ext_type_sys_props4_sym in tsa.
    eapply (per_image_eq_bar_change_pers inh ts lib lib'0 A A' A2 A1 A3 A0); eauto.
    { eapply in_ext_ext_type_ceq_sym; try exact tsa0; auto. }
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

    eapply (per_image_eq_bar_change_pers3 inh ts lib lib'2 T0 T A A');
      auto; try exact imp0; eauto; eauto 3 with slow.
  }
Qed.
Hint Resolve local_per_bar_per_image2 : slow.



(* ====== dest lemmas ====== *)


Lemma dest_close_per_image_l {o} :
  forall inh (ts : cts(o)) lib T A A' f T' eq (eqa : lib-per(inh,lib,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext inh lib T (mkc_image A f)
    -> close inh ts lib T T' eq
    -> per_bar inh (per_image inh (close inh ts)) lib T T' eq.
Proof.
  introv tysys dou tsa comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_image; spcast; try exact comp; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply (reca (raise_lib_per inh eqa e)); eauto 3 with slow.
Qed.

Lemma dest_close_per_image_r {o} :
  forall inh (ts : cts(o)) lib T A A' f T' eq (eqa : lib-per(inh,lib,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A' A (eqa lib' x))
    -> ccomputes_to_valc_ext inh lib T' (mkc_image A f)
    -> close inh ts lib T T' eq
    -> per_bar inh (per_image inh (close inh ts)) lib T T' eq.
Proof.
  introv tysys dou tsa comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_image2; spcast; try exact comp; eauto.
  eapply in_open_bar_ext_comb;[|exact reca];clear reca.
  apply in_ext_ext_implies_in_open_bar_ext; introv reca.
  apply (reca (raise_lib_per inh eqa e)); eauto 3 with slow.
Qed.
