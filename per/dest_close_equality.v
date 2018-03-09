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
  forall {lib} (bar : @BarLib o lib) a b (eqa : lib-per(lib,o)) t1 t2,
    all_in_bar_ext bar (fun lib' (x : lib_extends lib' lib) => eq_per_eq_bar lib' a b (raise_lib_per eqa x) t1 t2)
    -> eq_per_eq_bar lib a b eqa t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (alla0 _ br _ ext0 x0) as alla0.
  unfold eq_per_eq, raise_lib_per in alla0.
  pose proof (alla0 _ br0 _ ext (lib_extends_trans ext (bar_lib_ext _ _ br0))) as alla0; simpl in *.
  unfold eq_per_eq; repnd; dands; auto.
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
  dands; auto;[].
  exists (trivial_bar lib); dands; eauto 3 with slow.
Qed.
Hint Resolve per_eq_implies_per_eq_bar : slow.

Lemma simple_implies_iff_per_eq_eq {o} :
  forall lib (bar : @BarLib o lib) a b (eqa eqb : lib-per(lib,o)),
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> (eq_per_eq_bar lib a b eqa) <=2=> (eq_per_eq_bar lib a b eqb).
Proof.
  introv alla; introv.
  unfold eq_per_eq_bar, eq_per_eq; split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv br e; repeat introv.
    simpl in *; exrepnd.

    simpl in *; exrepnd.
    pose proof (h0 _ br2 lib'0 (lib_extends_trans e br1) x) as q; simpl in q; repnd.
    dands; auto.
    eapply alla; eauto 3 with slow.

  - exists (intersect_bars bar bar0).
    introv br e; repeat introv.
    simpl in *; exrepnd.

    simpl in *; exrepnd.
    pose proof (h0 _ br2 lib'0 (lib_extends_trans e br1) x) as q; simpl in q; repnd.
    dands; auto.
    eapply alla; eauto 3 with slow.
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
  unfold eq_per_eq_bar in *; exrepnd; exists bar.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  unfold eq_per_eq in *; repnd; dands; eauto 3 with slow.

  eapply lib_extends_preserves_ccequivc_ext in ceqa;[|exact x].
  eapply lib_extends_preserves_ccequivc_ext in ceqb;[|exact x].
  eapply (resp _ x) in ceqa;[|eapply (trans _ x); eauto; apply (sym _ x); auto].
  eapply (resp _ x) in ceqb;[|eapply (trans _ x); eauto; apply (sym _ x); auto].

  eapply (trans _ x);[apply (sym _ x);eauto|].
  eapply (trans _ x);[|eauto]; auto.
Qed.
Hint Resolve eq_per_eq_bar_respects_ccequivc_ext : slow.

Lemma local_per_bar_per_eq_bar {o} :
  forall (ts : cts(o)) lib T a b A B (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> T ===>(lib) (mkc_equality a b A)
    -> local_ts_T (per_bar (per_eq ts)) lib T.
Proof.
  introv tsp comp eqiff alla.
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
    unfold per_eq in *; exrepnd.
    exists A0 B0 a1 a2 b1 b2 eqa1; dands; auto.
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

    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp z2.
    computes_to_eqval_ext.
    hide_hyp z0.
    computes_to_eqval_ext.
    apply ccequivc_ext_mkc_equality_implies in ceq.
    apply ccequivc_ext_mkc_equality_implies in ceq0.
    apply ccequivc_ext_mkc_equality_implies in ceq1.
    repnd.

    eapply (simple_implies_iff_per_eq_eq _ (trivial_bar lib'0));[|eauto].

    { apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
      eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
        try (exact tsp); eauto.

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
          try exact tsp; try exact z3; eauto 3 with slow. }

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies in z3;
          try exact tsp; eauto 3 with slow.
        eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
          try exact tsp; try exact z3; eauto 3 with slow. }
    }

    { eapply eq_per_eq_bar_respects_ccequivc_ext; try exact w1; eauto 4 with slow. }
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
      remember (feqa lib0 br lib'0 xt1 x) as eqb.
      eapply (lib_per_cond _ eqb); eauto.

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

      unfold per_eq in allb0.
      unfold per_eq in q0.
      exrepnd.

      remember (feqa lib0 br lib'0 xt1 x) as eqb.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqc.

      eapply (lib_per_cond _ eqb); apply allb1; clear allb1.
      eapply (lib_per_cond _ eqc) in h0; apply q1 in h0; clear q1.

      assert (lib_extends lib'4 lib) as xx by eauto 3 with slow.
      dup comp as c.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in c;[|eauto 3 with slow];[].
      computes_to_eqval_ext.
      apply ccequivc_ext_mkc_equality_implies in ceq; repnd.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in comp;[|eauto 3 with slow];[].
      hide_hyp q0.
      computes_to_eqval_ext.
      apply ccequivc_ext_mkc_equality_implies in ceq2; repnd.

      hide_hyp c.
      computes_to_eqval_ext.
      apply ccequivc_ext_mkc_equality_implies in ceq5; repnd.

      eapply (simple_implies_iff_per_eq_eq _ (trivial_bar lib'4));[|].

      { apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
        eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
          try (exact tsp); eauto 3 with slow.

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
            try exact tsp; try exact allb3; eauto 3 with slow. }

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies in q3;
            try exact tsp; eauto 3 with slow.
          eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
            try exact tsp; try exact q3; eauto 3 with slow. }
      }

      { eapply eq_per_eq_bar_respects_ccequivc_ext; try exact h0; eauto 3 with slow. }
  }
Qed.
Hint Resolve local_per_bar_per_eq_bar : slow.

Lemma per_eq_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_eq ts lib T T' eq
    -> per_bar (per_eq ts) lib T T' eq.
Proof.
  introv per.

  unfold per_eq in *; exrepnd.
  exists (trivial_bar lib) (eq_per_eq_bar_lib_per lib a1 a2 eqa).
  dands; auto.

  {
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
    introv.
    exists A B a1 a2 b1 b2 (raise_lib_per eqa e); simpl.
    dands; spcast; eauto 3 with slow.
    apply (implies_in_ext_ext_raise_ext_per (fun lib e => ts lib A B e)); auto.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv.
    split; intro h; exrepnd.

    - introv br ext; introv; simpl in *.
      unfold eq_per_eq_bar, eq_per_eq_bar in *; exrepnd.
      exists (raise_bar bar x).
      introv br' ext'; introv; simpl in *; exrepnd.
      unfold raise_ext_per.

      assert (lib_extends lib'2 lib) as w by eauto 3 with slow.
      exists (raise_bar bar w).
      introv br'' ext''; introv; simpl in *; exrepnd.

      assert (lib_extends lib'4 lib1) as xt1 by eauto 3 with slow.
      assert (lib_extends lib'4 lib) as xt2 by eauto 3 with slow.
      pose proof (h0 _ br'1 lib'4 xt1 (lib_extends_trans x1 (lib_extends_trans x0 x))) as h0; simpl in *; auto.

    - apply all_in_bar_ext_trivial_bar_implies_in_ext_ext in h.
      simpl in *.
      pose proof (h lib (lib_extends_refl lib)) as h; simpl in h; exrepnd.

      apply all_in_bar_ext_exists_bar_implies in h0; exrepnd.
      exists (bar_of_bar_fam fbar).
      introv br ext; introv; simpl in *; exrepnd.

      assert (lib_extends lib'0 lib2) as xt1 by eauto 4 with slow.
      pose proof (h1 _ br _ ext0 x0 _ br0 _ ext xt1) as h1; simpl in *.
      eapply sub_per_eq_per_eq; try exact h1; eauto 3 with slow.
      introv w; simpl in *; unfold raise_ext_per in w.
      eapply (lib_per_cond _ eqa); eauto.
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
    unfold per_eq in *; exrepnd.
    exists A0 B0 a1 a2 b1 b2 eqa1; dands; auto.
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

    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp z2.
    computes_to_eqval_ext.
    hide_hyp z0.
    computes_to_eqval_ext.
    apply ccequivc_ext_mkc_equality_implies in ceq.
    apply ccequivc_ext_mkc_equality_implies in ceq0.
    apply ccequivc_ext_mkc_equality_implies in ceq1.
    repnd.

    eapply (simple_implies_iff_per_eq_eq _ (trivial_bar lib'0));[|eauto].

    { apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
      eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
        try (exact tsp); eauto.

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
          try exact tsp; try exact z3; eauto 3 with slow. }

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies3 in z3;
          try exact tsp; eauto 3 with slow.
        eapply trans_ccequivc_ext_in_ext_eq_types_implies4;
          try exact tsp; try exact z3; eauto 3 with slow. }
    }

    { eapply eq_per_eq_bar_respects_ccequivc_ext; try exact w1; eauto 4 with slow. }
  }

  {
    eapply eq_term_equals_trans;[eauto|].
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
      remember (feqa lib0 br lib'0 xt1 x) as eqb.
      eapply (lib_per_cond _ eqb); eauto.

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

      unfold per_eq in allb0.
      unfold per_eq in q0.
      exrepnd.

      remember (feqa lib0 br lib'0 xt1 x) as eqb.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqc.

      eapply (lib_per_cond _ eqb); apply allb1; clear allb1.
      eapply (lib_per_cond _ eqc) in h0; apply q1 in h0; clear q1.

      assert (lib_extends lib'4 lib) as xx by eauto 3 with slow.
      dup comp as c.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in c;[|eauto 3 with slow];[].
      computes_to_eqval_ext.
      apply ccequivc_ext_mkc_equality_implies in ceq; repnd.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in comp;[|eauto 3 with slow];[].
      hide_hyp q2.
      computes_to_eqval_ext.
      apply ccequivc_ext_mkc_equality_implies in ceq2; repnd.

      hide_hyp c.
      computes_to_eqval_ext.
      apply ccequivc_ext_mkc_equality_implies in ceq5; repnd.

      eapply (simple_implies_iff_per_eq_eq _ (trivial_bar lib'4));[|].

      { apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
        eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
          try (exact tsp); eauto.

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
            try exact tsp; try exact allb3; eauto 3 with slow. }

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies3 in q3;
            try exact tsp; eauto 3 with slow.
          eapply trans_ccequivc_ext_in_ext_eq_types_implies4;
            try exact tsp; try exact q3; eauto 3 with slow. }
      }

      { eapply eq_per_eq_bar_respects_ccequivc_ext; try exact h0; eauto 3 with slow. }
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
  introv br ext; introv.
  pose proof (reca _ br _ ext x (raise_lib_per eqa x)) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
  apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib A B e)); auto.
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
  introv br ext; introv.
  pose proof (reca _ br _ ext x (raise_lib_per eqa x)) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
  apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib B A e)); auto.
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
