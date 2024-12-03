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
  forall ts lib (T T' : @CTerm o) eq,
    per_ffdefs ts lib T T' eq
    -> per_bar (per_ffdefs ts) lib T T' eq.
Proof.
  introv per.

  unfold per_ffdefs in *; exrepnd.
  exists (trivial_bar lib) (per_ffdefs_eq_bar_lib_per lib eqa x1).
  dands; auto.

  {
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
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
  forall lib (bar : BarLib lib) (eqa1 eqa2 : lib-per(lib,p)) t1 t2 t,
    in_ext_ext lib (fun lib' x => term_equality_transitive (eqa1 lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa1 lib' x))
    -> all_in_bar_ext bar (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => eqa1 lib' x t1 t)
    -> in_ext_ext lib (fun lib' x => eqa2 lib' x t2 t)
    -> (per_ffdefs_eq_bar lib eqa1 t1) <=2=> (per_ffdefs_eq_bar lib eqa2 t2).
Proof.
  introv trans sym eqta eqt1 eqt2 ; introv.
  unfold per_ffdefs_eq_bar; split; introv h; exrepnd.

  - exists (intersect_bars bar bar0).
    introv br ext; introv; simpl in *; exrepnd.
    pose proof (h0 lib2 br2 lib'0 (lib_extends_trans ext br1) x) as h0; simpl in *.
    pose proof (eqta lib1 br0 lib'0 (lib_extends_trans ext br3) x) as eqta; simpl in *.
    pose proof (eqt1 _ x) as eqt1; simpl in *.
    pose proof (eqt2 _ x) as eqt2; simpl in *.
    unfold per_ffdefs_eq in *; repnd; dands; auto; eauto 3 with slow.

  - exists (intersect_bars bar bar0).
    introv br ext; introv; simpl in *; exrepnd.
    pose proof (h0 lib2 br2 lib'0 (lib_extends_trans ext br1) x) as h0; simpl in *.
    pose proof (eqta lib1 br0 lib'0 (lib_extends_trans ext br3) x) as eqta; simpl in *.
    unfold per_ffdefs_eq in *; repnd; dands; auto.
    eapply ex_nodefsc_change_per_and_term; try exact h0; eauto 3 with slow.
    apply eq_term_equals_sym;eauto.
Qed.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive_ext {o} :
  forall ts lib lib' (ext : lib_extends lib' lib) (A A1 A2 : @CTerm o) (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A1 (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A A2 (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts.
  applydup @in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive in tsp.
  eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 ts ext) in tsp;
    try exact tsts;[].
  apply (lib_extends_preserves_in_ext_ext ext) in tsp0.
  introv h1 h2.
  apply tsp.
  eapply tsp0; apply tsp; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive_ext : slow.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric_ext {o} :
  forall ts lib lib' (ext : lib_extends lib' lib) (A A1 A2 : @CTerm o) (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A1 (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A A2 (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts.
  applydup @in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric in tsp.
  eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4 ts ext) in tsp;
    try exact tsts;[].
  apply (lib_extends_preserves_in_ext_ext ext) in tsp0.
  introv h1.
  apply tsp.
  eapply tsp0; apply tsp; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric_ext : slow.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive_ext2 {o} :
  forall ts lib lib' (ext : lib_extends lib' lib) (A A1 A2 : @CTerm o) (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A1 A (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A2 A (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts.
  applydup @in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive in tsp.
  eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals5 ts ext) in tsp;
    try exact tsts;[].
  apply (lib_extends_preserves_in_ext_ext ext) in tsp0.
  introv h1 h2.
  apply tsp.
  eapply tsp0; apply tsp; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_transitive_ext2 : slow.

Lemma in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric_ext2 {o} :
  forall ts lib lib' (ext : lib_extends lib' lib) (A A1 A2 : @CTerm o) (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A1 A (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A2 A (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts.
  applydup @in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric in tsp.
  eapply (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals5 ts ext) in tsp;
    try exact tsts;[].
  apply (lib_extends_preserves_in_ext_ext ext) in tsp0.
  introv h1.
  apply tsp.
  eapply tsp0; apply tsp; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_prop4_implies_in_ext_term_equality_symmetric_ext2 : slow.

Lemma local_per_bar_per_ffdefs {o} :
  forall (ts : cts(o)) lib T A a A' (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> T ===>(lib) (mkc_free_from_defs A a)
    -> local_ts_T (per_bar (per_ffdefs ts)) lib T.
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
    unfold per_ffdefs in *; exrepnd.
    exists A1 A2 x1 x2 eqa1; dands; auto.
    apply eq_term_equals_sym; introv; split; introv w.

    { subst.
      apply alla3 in w.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      eauto. }

    exrepnd.

    pose proof (alla1 lib0 br1 lib3 ext1 x3) as z; repnd.
    pose proof (z0 lib4 fb lib'0 w (lib_extends_trans w (bar_lib_ext (fbar lib0 br1 lib3 ext1 x3) lib4 fb))) as z0; simpl in *.
    exrepnd.
    apply z1 in w1; clear z1.

    dup comp as c.
    apply (lib_extends_preserves_ccomputes_to_valc x) in c.
    spcast; repeat computes_to_eqval.

    eapply (implies_eq_term_equals_per_ffdefs_bar _ (trivial_bar lib'0));
      try exact w1; eauto 2 with slow;[].
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.

    eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
      try (exact tsa); eauto.
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

      unfold per_ffdefs in allb0.
      unfold per_ffdefs in q0.
      exrepnd; spcast; repeat computes_to_eqval.

      remember (feqa lib0 br lib'0 xt1 x) as eqz.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqw.

      eapply (lib_per_cond _ eqz); apply allb1; clear allb1.
      eapply (lib_per_cond _ eqw) in h0; apply q1 in h0; clear q1.

      assert (lib_extends lib'4 lib) as xx by eauto 3 with slow.
      dup comp as c.
      apply (lib_extends_preserves_computes_to_valc _ _ xx) in c.
      spcast; repeat computes_to_eqval.

      apply (lib_extends_preserves_computes_to_valc _ lib'4) in comp;[|eauto 3 with slow];[].
      repeat computes_to_eqval.

      eapply (implies_eq_term_equals_per_ffdefs_bar _ (trivial_bar lib'4));
        try exact h0; eauto 3 with slow;[].
      apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.

      eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
        try (exact tsa); eauto.
  }
Qed.
Hint Resolve local_per_bar_per_ffdefs : slow.

Lemma local_per_bar_per_ffdefs2 {o} :
  forall (ts : cts(o)) lib T A a A' (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A' A (eqa lib' x))
    -> T ===>(lib) (mkc_free_from_defs A a)
    -> local_ts_T2 (per_bar (per_ffdefs ts)) lib T.
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
    unfold per_ffdefs in *; exrepnd.
    exists A1 A2 x1 x2 eqa1; dands; auto.
    apply eq_term_equals_sym; introv; split; introv w.

    { subst.
      apply alla3 in w.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      eauto. }

    exrepnd.

    pose proof (alla1 lib0 br1 lib3 ext1 x3) as z; repnd.
    pose proof (z0 lib4 fb lib'0 w (lib_extends_trans w (bar_lib_ext (fbar lib0 br1 lib3 ext1 x3) lib4 fb))) as z0; simpl in *.
    exrepnd.
    apply z1 in w1; clear z1.

    dup comp as c.
    apply (lib_extends_preserves_ccomputes_to_valc x) in c.
    spcast; repeat computes_to_eqval.

    eapply (implies_eq_term_equals_per_ffdefs_bar _ (trivial_bar lib'0));
      try exact w1; eauto 2 with slow;[].
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
    eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
      try (exact tsa); eauto.
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

      unfold per_ffdefs in allb0.
      unfold per_ffdefs in q0.
      exrepnd; spcast; repeat computes_to_eqval.

      remember (feqa lib0 br lib'0 xt1 x) as eqz.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqw.

      eapply (lib_per_cond _ eqz); apply allb1; clear allb1.
      eapply (lib_per_cond _ eqw) in h0; apply q1 in h0; clear q1.

      assert (lib_extends lib'4 lib) as xx by eauto 3 with slow.
      dup comp as c.
      apply (lib_extends_preserves_computes_to_valc _ _ xx) in c.
      spcast; repeat computes_to_eqval.

      apply (lib_extends_preserves_computes_to_valc _ lib'4) in comp;[|eauto 3 with slow];[].
      repeat computes_to_eqval.

      eapply (implies_eq_term_equals_per_ffdefs_bar _ (trivial_bar lib'4));
        try exact h0; eauto 3 with slow;[].
      apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
      eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
        try (exact tsa); eauto.
  }
Qed.
Hint Resolve local_per_bar_per_ffdefs2 : slow.



(* ====== dest lemmas ====== *)

Lemma dest_close_per_ffdefs_l {o} :
  forall (ts : cts(o)) lib T A a A' T' eq (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> computes_to_valc lib T (mkc_free_from_defs A a)
    -> close ts lib T T' eq
    -> per_bar (per_ffdefs (close ts)) lib T T' eq.
Proof.
  introv tysys dou tsa comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_ffdefs; spcast; try exact comp; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x (raise_lib_per eqa x)) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
  apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib A A' e)); auto.
Qed.

Lemma dest_close_per_ffdefs_r {o} :
  forall (ts : cts(o)) lib T A a A' T' eq (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A' A (eqa lib' x))
    -> computes_to_valc lib T' (mkc_free_from_defs A a)
    -> close ts lib T T' eq
    -> per_bar (per_ffdefs (close ts)) lib T T' eq.
Proof.
  introv tysys dou tsa comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_ffdefs2; spcast; try exact comp; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x (raise_lib_per eqa x)) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
  apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib A' A e)); auto.
Qed.
