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


Require Export type_sys_useful.
Require Export dest_close.
Require Export per_ceq_bar.



(*Lemma per_union_eq_symmetric {p} :
  forall lib (eqa eqb : per(p)) t1 t2,
    term_equality_symmetric eqa
    -> term_equality_symmetric eqb
    -> per_union_eq lib eqa eqb t1 t2
    -> per_union_eq lib eqa eqb t2 t1.
Proof.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R.
  introv tesa tesb per; repdors; exrepnd.

  left.
  exists y x; sp.

  right.
  exists y x; sp.
Qed.

Lemma per_union_eq_transitive {p} :
  forall lib (eqa eqb : per(p)) t1 t2 t3,
    term_equality_transitive eqa
    -> term_equality_transitive eqb
    -> per_union_eq lib eqa eqb t1 t2
    -> per_union_eq lib eqa eqb t2 t3
    -> per_union_eq lib eqa eqb t1 t3.
Proof.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R.
  introv teta tetb per1 per2; repdors; exrepnd; ccomputes_to_eqval.

  left.
  exists x0 y; sp; spcast; sp.
  apply teta with (t2 := y0); sp.

  right.
  exists x0 y; sp; spcast; sp.
  apply tetb with (t2 := y0); sp.
Qed.

Lemma per_union_eq_cequiv {p} :
  forall lib (eqa eqb : per(p)) t1 t2,
    term_equality_respecting lib eqa
    -> term_equality_respecting lib eqb
    -> term_equality_symmetric eqa
    -> term_equality_symmetric eqb
    -> term_equality_transitive eqa
    -> term_equality_transitive eqb
    -> cequivc lib t1 t2
    -> per_union_eq lib eqa eqb t1 t1
    -> per_union_eq lib eqa eqb t1 t2.
Proof.
  unfold per_union_eq, per_union_eq_L, per_union_eq_R.
  introv resa resb syma symb tra trb ceq per; repdors; exrepnd.

  left; spcast.
  generalize (cequivc_mkc_inl lib t1 t2 x); introv k;
  repeat (autodimp k hyp); exrepnd.
  exists x b; sp; spcast; sp.
  apply resa; spcast; sp.
  apply tra with (t2 := y); sp.

  right; spcast.
  generalize (cequivc_mkc_inr lib t1 t2 x); introv k;
  repeat (autodimp k hyp); exrepnd.
  exists x b; sp; spcast; sp.
  apply resb; spcast; sp.
  apply trb with (t2 := y); sp.
Qed.*)


Lemma implies_eq_term_equals_per_union_bar {p} :
  forall lib (eqa1 eqa2 eqb1 eqb2 : per(p)),
    (eqa1 <=2=> eqa2)
    -> (eqb1 <=2=> eqb2)
    -> (per_union_eq_bar lib eqa1 eqb1) <=2=> (per_union_eq_bar lib eqa2 eqb2).
Proof.
  introv eqta eqtb; introv.
  unfold per_union_eq_bar; split; introv h; exrepnd; exists bar;
    introv br ext;
    pose proof (h0 lib' br lib'0 ext) as h0; simpl in *;
      unfold per_union_eq, per_union_eq_L, per_union_eq_R in *;
      repndors; exrepnd;[left|right|left|right];
        eexists; eexists; dands; eauto;
          try (complete (apply eqta; auto));
          try (complete (apply eqtb; auto)).
Qed.

Lemma approx_decomp_union {o} :
  forall lib (a b c d : @NTerm o),
    approx lib (mk_union a b) (mk_union c d)
    <=> approx lib a c # approx lib b d.
Proof.
  split; unfold mk_union; introv Hyp.
  - applydup @approx_relates_only_progs in Hyp. repnd.
    apply  approx_canonical_form2 in Hyp.
    unfold lblift in Hyp.
    repnd; allsimpl.
    alpharelbtd; GC.
    applydup @isprogram_union_iff in Hyp1.
    applydup @isprogram_union_iff in Hyp0.
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

Lemma cequiv_decomp_union {o} :
  forall lib (a b c d : @NTerm o),
    cequiv lib (mk_union a b) (mk_union c d)
    <=> cequiv lib a c # cequiv lib b d.
Proof.
  intros.
  unfold cequiv.
  generalize (approx_decomp_union lib a b c d); intro X.
  trewrite X; clear X.
  generalize (approx_decomp_union lib c d a b); intro X.
  trewrite X; clear X.
  split; sp.
Qed.

Lemma cequivc_decomp_union {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib (mkc_union a b) (mkc_union c d)
    <=> cequivc lib a c # cequivc lib b d.
Proof.
  introv; destruct_cterms; unfold cequivc, mkc_cequiv; simpl.
  apply cequiv_decomp_union.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_union {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar1) (mkc_union a1 b1)
    -> T ==b==>(bar2) (mkc_union a2 b2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2 # ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_implies in comp2; try exact comp1.
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q.
  spcast.
  apply cequivc_decomp_union in q; repnd; dands; spcast; auto.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_union1 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar1) (mkc_union a1 b1)
    -> T ==b==>(bar2) (mkc_union a2 b2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib a1 a2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_union in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.

Lemma two_computes_to_valc_ceq_bar_mkc_union2 {o} :
  forall {lib} (bar1 bar2 : BarLib lib) (T : @CTerm o) a1 b1 a2 b2,
    T ==b==>(bar1) (mkc_union a1 b1)
    -> T ==b==>(bar2) (mkc_union a2 b2)
    -> all_in_bar (intersect_bars bar1 bar2) (fun lib => ccequivc lib b1 b2).
Proof.
  introv comp1 comp2.
  eapply two_computes_to_valc_ceq_bar_mkc_union in comp2;[|exact comp1].
  introv b ext.
  pose proof (comp2 lib' b lib'0 ext) as q; simpl in q; tcsp.
Qed.

Lemma all_in_bar_type_sys_props4_sym {o} :
  forall ts lib (bar : BarLib lib) (A B : @CTerm o) eqa,
    all_in_bar bar (fun lib => type_sys_props4 ts lib A B eqa)
    -> all_in_bar bar (fun lib => type_sys_props4 ts lib B A eqa).
Proof.
  introv alla br ext.
  pose proof (alla lib' br lib'0 ext) as alla; simpl in *.
  apply type_sys_props4_sym; auto.
Qed.
Hint Resolve all_in_bar_type_sys_props4_sym : slow.

Lemma close_type_system_union {o} :
  forall (ts : cts(o))
         lib (bar : BarLib lib)
         T T'
         (eq : per)
         A1 A2 B1 B2 eqa eqb,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> (T ==b==>(bar) (mkc_union A1 B1))
    -> (T' ==b==>(bar) (mkc_union A2 B2))
    -> all_in_bar bar (fun lib => close ts lib A1 A2 eqa)
    -> all_in_bar bar (fun lib => type_sys_props4 (close ts) lib A1 A2 eqa)
    -> all_in_bar bar (fun lib => close ts lib B1 B2 eqb)
    -> all_in_bar bar (fun lib => type_sys_props4 (close ts) lib B1 B2 eqb)
    -> (eq <=2=> (per_union_eq_bar lib eqa eqb))
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tysys dou mon c1 c2 cla reca clb recb eqiff.

  prove_type_sys_props4 SCase; introv.

  - SCase "uniquely_valued".
    introv cl.
    dclose_lr.
    clear cl.

    allunfold @per_union_bar; exrepnd.

    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T A1 B1 A0 B0) as ceq1.
    repeat (autodimp ceq1 hyp).
    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq1.
    pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T A1 B1 A0 B0) as ceq2.
    repeat (autodimp ceq2 hyp).
    apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq2.

    apply implies_eq_term_equals_per_union_bar.

    { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans; eauto. }

    { eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans; eauto. }

  - SCase "type_symmetric".
    introv cl ee.
    dclose_lr; clear cl.
    apply CL_union.
    allunfold @per_union_bar; exrepnd.
    exists eqa0 eqb0 A0 A3 B0 B3; dands; auto; eauto.
    eapply eq_term_equals_trans;[apply eq_term_equals_sym;eauto|]; auto.

  - SCase "type_value_respecting".
    introv h ceq.
    repndors; subst; apply CL_union.

    { eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto].
      exists eqa eqb A1 A1 B1 B1; dands; auto.
      exists bar; dands; auto; eauto 3 with slow. }

    { eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto].
      exists eqa eqb A2 A2 B2 B2; dands; auto.
      exists bar; dands; auto; eauto 3 with slow. }

  - SCase "type_value_respecting_trans".
    introv h ceq cl.
    repndors; subst;
      eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;eauto;
        dclose_lr; clear cl; apply CL_union.

    {
      unfold per_union_bar in *; exrepnd.

      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T3 A1 B1 A0 B0) as ceq1.
      repeat (autodimp ceq1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T3 A1 B1 A0 B0) as ceq2.
      repeat (autodimp ceq2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq2.

      exists eqa eqb; eexists; eexists; eexists; eexists; dands; eauto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow;
          eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans2; eauto.

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym.
        apply implies_eq_term_equals_per_union_bar;
          eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans; eauto.
    }

    {
      unfold per_union_bar in *; exrepnd.

      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T3 A2 B2 A0 B0) as ceq1.
      repeat (autodimp ceq1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T3 A2 B2 A0 B0) as ceq2.
      repeat (autodimp ceq2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq2.

      exists eqa eqb; eexists; eexists; eexists; eexists; dands; eauto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow;
          eapply all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans2; eauto.

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym.
        apply implies_eq_term_equals_per_union_bar;
          eapply all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans; eauto.
    }

    {
      unfold per_union_bar in *; exrepnd.

      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T3 A1 B1 A3 B3) as ceq1.
      repeat (autodimp ceq1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T3 A1 B1 A3 B3) as ceq2.
      repeat (autodimp ceq2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq2.

      exists eqa eqb; eexists; eexists; eexists; eexists; dands; eauto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow;
          eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans4; eauto.

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym.
        apply implies_eq_term_equals_per_union_bar;
          eapply all_in_bar_type_sys_props4_implies_type_equality_respecting_trans3; eauto.
    }

    {
      unfold per_union_bar in *; exrepnd.

      pose proof (two_computes_to_valc_ceq_bar_mkc_union1 bar bar0 T3 A2 B2 A3 B3) as ceq1.
      repeat (autodimp ceq1 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq1.
      pose proof (two_computes_to_valc_ceq_bar_mkc_union2 bar bar0 T3 A2 B2 A3 B3) as ceq2.
      repeat (autodimp ceq2 hyp).
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in ceq2.

      exists eqa eqb; eexists; eexists; eexists; eexists; dands; eauto.

      - exists (intersect_bars bar bar0); dands; eauto 3 with slow;
          eapply all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans4; eauto.

      - eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym.
        apply implies_eq_term_equals_per_union_bar;
          eapply all_in_bar_type_sys_props4_sym_implies_type_equality_respecting_trans3; eauto.
    }

  - SCase "term_symmetric".

XXXXXX
    unfold term_equality_symmetric; introv eqt.
    rw eqiff in eqt; rw eqiff.
    apply per_union_eq_symmetric; sp;
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 tymt1; sp;
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2; sp.

  - SCase "term_transitive".
    unfold term_equality_transitive; introv eqt1 eqt2.
    rw eqiff in eqt1; rw eqiff in eqt2; rw eqiff.
    apply @per_union_eq_transitive with (t2 := t2); sp;
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 tymt1; sp;
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2; sp.

  - SCase "term_value_respecting".
    unfold term_equality_respecting; introv eqt ceq.
    rw eqiff in eqt; rw eqiff.
    spcast.
    apply per_union_eq_cequiv; sp;
    onedtsp uv1 tys1 tyt1 tyst1 tyvr1 tes1 tet1 tevr1 tygs1 tygt1 tymt1; sp;
    onedtsp uv2 tys2 tyt2 tyst2 tyvr2 tes2 tet2 tevr2 tygs2 tygt2 tymt2; sp.

  - SCase "type_gsymmetric".
    repdors; subst; split; sp; dclose_lr;
    apply CL_union;
    clear per;
    allunfold @per_union; exrepd;
    ccomputes_to_eqval;
    unfold per_union.

    (* 1 *)
    exists eqa0 eqb0 A3 A1 B3 B1; sp; spcast; sp.
    generalize (type_sys_props_ts_sym3 lib (close lib ts) A1 A3 A2 eqa eqa0); sp.
    generalize (type_sys_props_ts_sym3 lib (close lib ts) B1 B3 B2 eqb eqb0); sp.

    (* 2 *)
    exists eqa0 eqb0 A1 A0 B1 B0; sp; spcast; sp.
    generalize (type_sys_props_ts_sym2 lib (close lib ts) A1 A0 A2 eqa eqa0); sp.
    generalize (type_sys_props_ts_sym2 lib (close lib ts) B1 B0 B2 eqb eqb0); sp.

  - SCase "type_gtransitive"; sp.

  - SCase "type_mtransitive".
    repdors; subst; dclose_lr;
    try (move_term_to_top (per_union lib (close lib ts) T T4 eq2));
    try (move_term_to_top (per_union lib (close lib ts) T' T4 eq2));
    allunfold @per_union; exrepd;
    ccomputes_to_eqval.

    + dands; apply CL_union; unfold per_union.

      * exists eqa1 eqb1 A4 A3 B4 B3; sp; spcast; sp.
        generalize (type_sys_props_ts_trans3 lib (close lib ts) A4 A1 A3 A2 eqa1 eqa0 eqa); sp.
        generalize (type_sys_props_ts_trans3 lib (close lib ts) B4 B1 B3 B2 eqb1 eqb0 eqb); sp.

      * exists eqa0 eqb0 A4 A3 B4 B3; sp; spcast; sp.
        generalize (type_sys_props_ts_trans4 lib (close lib ts) A4 A1 A3 A2 eqa1 eqa0 eqa); sp.
        generalize (type_sys_props_ts_trans4 lib (close lib ts) B4 B1 B3 B2 eqb1 eqb0 eqb); sp.

    + dands; apply CL_union; unfold per_union.

      * exists eqa1 eqb1 A4 A3 B4 B3; sp; spcast; sp.
        apply type_sys_props_sym in reca.
        generalize (type_sys_props_ts_trans3 lib (close lib ts) A4 A2 A3 A1 eqa1 eqa0 eqa); sp.
        apply type_sys_props_sym in recb.
        generalize (type_sys_props_ts_trans3 lib (close lib ts) B4 B2 B3 B1 eqb1 eqb0 eqb); sp.

      * exists eqa0 eqb0 A4 A3 B4 B3; sp; spcast; sp.
        apply type_sys_props_sym in reca.
        generalize (type_sys_props_ts_trans4 lib (close lib ts) A4 A2 A3 A1 eqa1 eqa0 eqa); sp.
        apply type_sys_props_sym in recb.
        generalize (type_sys_props_ts_trans4 lib (close lib ts) B4 B2 B3 B1 eqb1 eqb0 eqb); sp.
Qed.

