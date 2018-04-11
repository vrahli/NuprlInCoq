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

Require Export close_util_qtime.
Require Export dest_close_util.


Lemma per_qtime_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_qtime ts lib T T' eq
    -> per_bar (per_qtime ts) lib T T' eq.
Proof.
  introv per.
  unfold per_qtime in per; exrepnd.

  exists (trivial_bar lib) (per_qtime_eq_bar_lib_per eqa).
  dands; auto.

  {
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
    introv.
    exists (raise_lib_per eqa e) A B.
    dands; spcast; eauto 3 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv.
    apply eq_term_equals_sym.
    apply per_bar_eq_per_qtime_eq_bar_lib_per.
  }
Qed.
Hint Resolve per_qtime_implies_per_bar : slow.

Lemma approx_decomp_qtime {o} :
  forall lib (a b : @NTerm o),
    approx lib (mk_qtime a) (mk_qtime b)
    <=> approx lib a b.
Proof.
  split; unfold mk_qtime; introv Hyp.
  - applydup @approx_relates_only_progs in Hyp. repnd.
    apply  approx_canonical_form2 in Hyp.
    unfold lblift in Hyp.
    repnd; allsimpl.
    alpharelbtd; GC.
    applydup @isprogram_qtime_implies in Hyp1.
    applydup @isprogram_qtime_implies in Hyp0.
    eapply blift_approx_open_nobnd in Hyp0bt; eauto 3 with slow.
  - repnd.
    applydup @approx_relates_only_progs in Hyp; repnd.
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

Lemma cequiv_decomp_qtime {o} :
  forall lib (a b : @NTerm o),
    cequiv lib (mk_qtime a) (mk_qtime b)
    <=> cequiv lib a b.
Proof.
  intros.
  unfold cequiv.
  generalize (approx_decomp_qtime lib a b); intro X.
  trewrite X; clear X.
  generalize (approx_decomp_qtime lib b a); intro X.
  trewrite X; clear X.
  split; sp.
Qed.

Lemma cequivc_decomp_qtime {o} :
  forall lib (a b : @CTerm o),
    cequivc lib (mkc_qtime a) (mkc_qtime b)
    <=> cequivc lib a b.
Proof.
  introv; destruct_cterms; unfold cequivc, mkc_cequiv; simpl.
  apply cequiv_decomp_qtime.
Qed.

Lemma cequivc_ext_mkc_qtime_right {o} :
  forall lib (a b : @CTerm o),
    ccequivc_ext lib (mkc_qtime a) (mkc_qtime b)
    -> ccequivc_ext lib a b.
Proof.
  introv ceq; dands; introv ext; pose proof (ceq lib' ext) as q; simpl in q;
    clear ceq; spcast; apply (cequivc_decomp_qtime _ a b) in q; sp.
Qed.

Lemma local_per_bar_per_qtime {o} :
  forall (ts : cts(o)) (lib : SL) T A A' (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> T ===>(lib) (mkc_qtime A)
    -> local_ts_T (per_bar (per_qtime ts)) lib T.
Proof.
  introv tsa comp eqiff alla.
  unfold per_bar in *.

  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  apply all_in_bar_ext2_exists_eqa_implies in alla0; exrepnd.

  exists (lib_per_per_bar fbar feqa).
  dands.

  {
    introv br ext; introv.
    simpl in *; exrepnd.

    pose proof (alla1 lib1 br lib2 ext0 x0) as alla0.
    exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as bb.
    pose proof (alla2
                  lib' br0 lib'0 ext
                  (lib_extends_trans ext (bar_lib_ext bb lib' br0)))
      as alla2; simpl in *.
    unfold per_qtime in *; exrepnd.
    exists eqa1 A0 B; dands; auto.
    apply eq_term_equals_sym; introv; split; introv w.

    { subst.
      apply alla3 in w.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      eauto. }

    exrepnd.

    pose proof (alla1 lib0 br1 lib3 ext1 x1) as z; repnd.
    pose proof (z0 lib4 fb lib'0 w (lib_extends_trans w (bar_lib_ext (fbar lib0 br1 lib3 ext1 x1) lib4 fb))) as z0; simpl in *.
    exrepnd.
    apply z1 in w1; clear z1.

    apply (@ccomputes_to_valc_ext_monotone _ _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp z2.
    computes_to_eqval_ext.
    hide_hyp z0.
    computes_to_eqval_ext.

    apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.
    apply cequivc_ext_mkc_qtime_right in ceq0; eauto 3 with slow;[]; repnd.
    apply cequivc_ext_mkc_qtime_right in ceq1; eauto 3 with slow;[]; repnd.

    eapply implies_eq_term_equals_per_qtime_eq_bar;[|eauto];[].

    eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
      try (exact tsa); eauto.

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
        try exact tsa; try exact alla6; eauto 3 with slow. }

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies in z3;
        try exact tsa; eauto 3 with slow.
      eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
        try exact tsa; try exact z3; eauto 3 with slow. }
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    introv.
    split; intro h; exrepnd.

    - rw @per_bar_eq_iff in h; unfold per_bar_eq_bi in *; exrepnd.
      apply per_bar_eq_iff2.
      exists bar'.
      introv br ext; introv; simpl in *; exrepnd.
      pose proof (h0 lib') as h0; simpl in *; autodimp h0 hyp.
      { eexists; eexists; dands; eauto 4 with slow. }
      pose proof (h0 _ ext x) as h0; simpl in *.

      assert (lib_extends lib'0 lib0) as xt1 by eauto 5 with slow.

      pose proof (alla1 _ br lib'0 xt1 x) as allb; repnd.
      apply allb in h0.
      rw @per_bar_eq_iff in h0; unfold per_bar_eq_bi in *; exrepnd.

      exists (intersect_bars (fbar lib0 br lib'0 xt1 x) bar'0).
      introv br' ext' x'.
      pose proof (h1 _ br' _ ext' x') as h1; simpl in h1.
      simpl in *; exrepnd.

      exists lib0 br lib'0 xt1 x lib4 (lib_extends_trans ext' br'3) br'0.
      remember (feqa lib0 br lib'0 xt1 x) as eqz.
      eapply (lib_per_cond _ eqz); eauto.

    - rw @per_bar_eq_iff.
      exists (bar_of_bar_fam fbar).
      introv br ext; introv; simpl in *; exrepnd.
      assert (lib_extends lib'0 lib0) as xt1 by eauto 5 with slow.
      pose proof (alla1 _ br lib'0 xt1 x) as allb; simpl in *; repnd.
      apply allb; clear allb.

      introv br' ext'; introv.
      pose proof (h lib'1) as h; simpl in *; autodimp h hyp.
      { eexists; eexists; eexists; eexists; eexists; eauto. }
      assert (lib_extends lib'2 lib) as xt2 by eauto 3 with slow.
      pose proof (h lib'2 ext' xt2) as h; simpl in h; exrepnd.
      exists bar'.

      introv br'' ext''; introv.
      pose proof (h0 _ br'' _ ext'' x2) as h0; simpl in *; exrepnd.

      assert (lib_extends lib'4 lib'1) as xt3 by eauto 3 with slow.
      assert (lib_extends lib'4 lib'0) as xt4 by eauto 3 with slow.
      pose proof (allb0 _ br' lib'4 xt3 xt4) as allb0; simpl in *.

      pose proof (alla1 _ br2 _ ext1 x3) as q; repnd.
      assert (lib_extends lib'4 lib5) as xt5 by eauto 3 with slow.
      pose proof (q0 _ fb _ w xt5) as q0; simpl in *.

      unfold per_qtime in allb0.
      unfold per_qtime in q0.
      exrepnd.

      remember (feqa lib0 br lib'0 xt1 x) as eqz.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqw.

      eapply (lib_per_cond _ eqz); apply allb1; clear allb1.
      eapply (lib_per_cond _ eqw) in h0; apply q1 in h0; clear q1.

      assert (lib_extends lib'4 lib) as xx by eauto 3 with slow.

      apply (@ccomputes_to_valc_ext_monotone _ _ lib'4) in comp;[|eauto 3 with slow];[].
      computes_to_eqval_ext.
      hide_hyp q2.
      computes_to_eqval_ext.
      hide_hyp q0.
      computes_to_eqval_ext.

      apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.
      apply cequivc_ext_mkc_qtime_right in ceq0; eauto 3 with slow;[]; repnd.
      apply cequivc_ext_mkc_qtime_right in ceq1; eauto 3 with slow;[]; repnd.

      eapply implies_eq_term_equals_per_qtime_eq_bar;[|eauto];[].

      eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
        try (exact tsa); eauto.

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
          try exact tsa; try exact allb4; eauto 3 with slow. }

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies in q3;
          try exact tsa; eauto 3 with slow.
        eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
          try exact tsa; try exact q4; eauto 3 with slow. }
  }
Qed.
Hint Resolve local_per_bar_per_qtime : slow.

Lemma local_per_bar_per_qtime2 {o} :
  forall (ts : cts(o)) lib T A A' (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A' A (eqa lib' x))
    -> T ===>(lib) (mkc_qtime A)
    -> local_ts_T2 (per_bar (per_qtime ts)) lib T.
Proof.
  introv tsa comp eqiff alla.
  unfold per_bar in *.

  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  apply all_in_bar_ext2_exists_eqa_implies in alla0; exrepnd.

  exists (lib_per_per_bar fbar feqa).
  dands.

  {
    introv br ext; introv.
    simpl in *; exrepnd.

    pose proof (alla1 lib1 br lib2 ext0 x0) as alla0.
    exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as bb.
    pose proof (alla2
                  lib' br0 lib'0 ext
                  (lib_extends_trans ext (bar_lib_ext bb lib' br0)))
      as alla2; simpl in *.
    unfold per_qtime in *; exrepnd.
    exists eqa1 A0 B; dands; auto.
    apply eq_term_equals_sym; introv; split; introv w.

    { subst.
      apply alla3 in w.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      eauto. }

    exrepnd.

    pose proof (alla1 lib0 br1 lib3 ext1 x1) as z; repnd.
    pose proof (z0 lib4 fb lib'0 w (lib_extends_trans w (bar_lib_ext (fbar lib0 br1 lib3 ext1 x1) lib4 fb))) as z0; simpl in *.
    exrepnd.
    apply z1 in w1; clear z1.

    apply (@ccomputes_to_valc_ext_monotone _ _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp z2.
    computes_to_eqval_ext.
    hide_hyp z0.
    computes_to_eqval_ext.

    apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.
    apply cequivc_ext_mkc_qtime_right in ceq0; eauto 3 with slow;[]; repnd.
    apply cequivc_ext_mkc_qtime_right in ceq1; eauto 3 with slow;[]; repnd.

    eapply implies_eq_term_equals_per_qtime_eq_bar;[|eauto];[].

    eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
      try (exact tsa); eauto.

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
        try exact tsa; try exact alla6; eauto 3 with slow. }

    { eapply trans_ccequivc_ext_in_ext_eq_types_implies3 in z3;
        try exact tsa; eauto 3 with slow.
      eapply trans_ccequivc_ext_in_ext_eq_types_implies4;
        try exact tsa; try exact z3; eauto 3 with slow. }
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    introv.
    split; intro h; exrepnd.

    - rw @per_bar_eq_iff in h; unfold per_bar_eq_bi in *; exrepnd.
      apply per_bar_eq_iff2.
      exists bar'.
      introv br ext; introv; simpl in *; exrepnd.
      pose proof (h0 lib') as h0; simpl in *; autodimp h0 hyp.
      { eexists; eexists; dands; eauto 4 with slow. }
      pose proof (h0 _ ext x) as h0; simpl in *.

      assert (lib_extends lib'0 lib0) as xt1 by eauto 5 with slow.

      pose proof (alla1 _ br lib'0 xt1 x) as allb; repnd.
      apply allb in h0.
      rw @per_bar_eq_iff in h0; unfold per_bar_eq_bi in *; exrepnd.

      exists (intersect_bars (fbar lib0 br lib'0 xt1 x) bar'0).
      introv br' ext' x'.
      pose proof (h1 _ br' _ ext' x') as h1; simpl in h1.
      simpl in *; exrepnd.

      exists lib0 br lib'0 xt1 x lib4 (lib_extends_trans ext' br'3) br'0.
      remember (feqa lib0 br lib'0 xt1 x) as eqz.
      eapply (lib_per_cond _ eqz); eauto.

    - rw @per_bar_eq_iff.
      exists (bar_of_bar_fam fbar).
      introv br ext; introv; simpl in *; exrepnd.
      assert (lib_extends lib'0 lib0) as xt1 by eauto 5 with slow.
      pose proof (alla1 _ br lib'0 xt1 x) as allb; simpl in *; repnd.
      apply allb; clear allb.

      introv br' ext'; introv.
      pose proof (h lib'1) as h; simpl in *; autodimp h hyp.
      { eexists; eexists; eexists; eexists; eexists; eauto. }
      assert (lib_extends lib'2 lib) as xt2 by eauto 3 with slow.
      pose proof (h lib'2 ext' xt2) as h; simpl in h; exrepnd.
      exists bar'.

      introv br'' ext''; introv.
      pose proof (h0 _ br'' _ ext'' x2) as h0; simpl in *; exrepnd.

      assert (lib_extends lib'4 lib'1) as xt3 by eauto 3 with slow.
      assert (lib_extends lib'4 lib'0) as xt4 by eauto 3 with slow.
      pose proof (allb0 _ br' lib'4 xt3 xt4) as allb0; simpl in *.

      pose proof (alla1 _ br2 _ ext1 x3) as q; repnd.
      assert (lib_extends lib'4 lib5) as xt5 by eauto 3 with slow.
      pose proof (q0 _ fb _ w xt5) as q0; simpl in *.

      unfold per_qtime in allb0.
      unfold per_qtime in q0.
      exrepnd.

      remember (feqa lib0 br lib'0 xt1 x) as eqz.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqw.

      eapply (lib_per_cond _ eqz); apply allb1; clear allb1.
      eapply (lib_per_cond _ eqw) in h0; apply q1 in h0; clear q1.

      assert (lib_extends lib'4 lib) as xx by eauto 3 with slow.

      apply (@ccomputes_to_valc_ext_monotone _ _ lib'4) in comp;[|eauto 3 with slow];[].
      computes_to_eqval_ext.
      hide_hyp q2.
      computes_to_eqval_ext.
      hide_hyp q0.
      computes_to_eqval_ext.

      apply cequivc_ext_mkc_qtime_right in ceq; eauto 3 with slow;[]; repnd.
      apply cequivc_ext_mkc_qtime_right in ceq0; eauto 3 with slow;[]; repnd.
      apply cequivc_ext_mkc_qtime_right in ceq1; eauto 3 with slow;[]; repnd.

      eapply implies_eq_term_equals_per_qtime_eq_bar;[|eauto];[].

      eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
        try (exact tsa); eauto.

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
          try exact tsa; try exact allb4; eauto 3 with slow. }

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies3 in q3;
          try exact tsa; eauto 3 with slow.
        eapply trans_ccequivc_ext_in_ext_eq_types_implies4;
          try exact tsa; try exact q4; eauto 3 with slow. }
  }
Qed.
Hint Resolve local_per_bar_per_qtime2 : slow.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_qtime_l {o} :
  forall (ts : cts(o)) lib T A A' T' eq (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_qtime A)
    -> close ts lib T T' eq
    -> per_bar (per_qtime (close ts)) lib T T' eq.
Proof.
  introv tysys dou tsa comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_qtime; spcast; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x (raise_lib_per eqa x)) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
  apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib A A' e)); auto.
Qed.

Lemma dest_close_per_qtime_r {o} :
  forall (ts : cts(o)) lib T A A' T' eq (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A' A (eqa lib' x))
    -> ccomputes_to_valc_ext lib T' (mkc_qtime A)
    -> close ts lib T T' eq
    -> per_bar (per_qtime (close ts)) lib T T' eq.
Proof.
  introv tysys dou tsa comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_qtime2; spcast; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x (raise_lib_per eqa x)) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
  apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib A' A e)); auto.
Qed.
