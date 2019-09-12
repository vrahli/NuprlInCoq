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
  forall ts lib (T T' : @CTerm o) eq,
    per_union ts lib T T' eq
    -> per_bar (per_union ts) lib T T' eq.
Proof.
  introv per.

  unfold per_union, per_bar in *; exrepnd.
  exists (per_union_eq_bar_lib_per eqa eqb).
  dands; auto.

  {
    apply in_ext_ext_implies_in_open_bar_ext.
    introv.
    exists (raise_lib_per eqa e) (raise_lib_per eqb e) A1 A2 B1 B2; simpl.
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
  forall lib (a b c d : @CTerm o),
    ccequivc_ext lib (mkc_union a b) (mkc_union c d)
    -> ccequivc_ext lib a c # ccequivc_ext lib b d.
Proof.
  introv ceq; dands; introv ext; pose proof (ceq lib' ext) as q; simpl in q;
    clear ceq; spcast; apply cequivc_decomp_union in q; sp.
Qed.

Lemma local_per_bar_per_union {o} :
  forall (ts : cts(o)) lib T A B A' B' (eqa eqb : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B B' (eqb lib' x))
    -> T ===>(lib) (mkc_union A B)
    -> local_ts_T (per_bar (per_union ts)) lib T.
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

    unfold per_union in *; exrepnd.
    exists eqa1 eqb0 A1 A2 B1 B2; dands; auto.
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

XXXXXXXXXXx
Check implies_eq_term_equals_per_union_bar.

    eapply uv in xx0; autodimp xx0 hyp;[exact alla2|].
    apply xx0; auto.


XXXXXXXXXXXX

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
    unfold per_union in *; exrepnd.
    exists eqa1 eqb0 A1 A2 B1 B2; dands; auto.
    apply eq_term_equals_sym; introv; split; introv w.

    { subst.
      apply alla2 in w.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      eauto. }

    exrepnd.

    pose proof (alla1 lib0 br1 lib3 ext1 x1) as z; repnd.
    pose proof (z0 lib4 fb lib'0 w (lib_extends_trans w (bar_lib_ext (fbar lib0 br1 lib3 ext1 x1) lib4 fb))) as z0; simpl in *.
    exrepnd.
    apply z0 in w1; clear z0.

    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp z2.
    computes_to_eqval_ext.
    hide_hyp z1.
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_union_right in ceq.
    apply cequivc_ext_mkc_union_right in ceq0.
    apply cequivc_ext_mkc_union_right in ceq1.
    repnd.

    eapply (implies_eq_term_equals_per_union_bar _ (trivial_bar lib'0));[| |eauto];
      apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;[|].

    {
      eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
        try (exact tsa); eauto.

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
          try exact tsa; try exact alla5; eauto 3 with slow. }

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies in z3;
          try exact tsa; eauto 3 with slow.
        eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
          try exact tsa; try exact z3; eauto 3 with slow. }
    }

    {
      eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
        try (exact tsb); eauto.

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
          try exact tsb; try exact alla6; eauto 3 with slow. }

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies in z4;
          try exact tsb; eauto 3 with slow.
        eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
          try exact tsb; try exact z4; eauto 3 with slow. }
    }
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

      unfold per_union in allb0.
      unfold per_union in q0.
      exrepnd; spcast.

      remember (feqa lib0 br lib'0 xt1 x) as eqz.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqw.

      eapply (lib_per_cond _ eqz); apply allb0; clear allb0.
      eapply (lib_per_cond _ eqw) in h0; apply q0 in h0; clear q0.

      assert (lib_extends lib'4 lib) as xx by eauto 3 with slow.
      dup comp as c.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in c;[|eauto 3 with slow];[].
      computes_to_eqval_ext.
      apply cequivc_ext_mkc_union_right in ceq; repnd.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in comp;[|eauto 3 with slow];[].
      hide_hyp q1.
      computes_to_eqval_ext.
      apply cequivc_ext_mkc_union_right in ceq1; repnd.

      hide_hyp c.
      computes_to_eqval_ext.
      apply cequivc_ext_mkc_union_right in ceq3; repnd.

      eapply (implies_eq_term_equals_per_union_bar _ (trivial_bar lib'4));[| |eauto];
        apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;[|].

      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
          try (exact tsa); eauto.

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
            try exact tsa; try exact allb3; eauto 3 with slow. }

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies in q3;
            try exact tsa; eauto 3 with slow.
          eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
            try exact tsa; try exact q3; eauto 3 with slow. }
      }

      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
          try (exact tsb); eauto.

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
            try exact tsb; try exact allb4; eauto 3 with slow. }

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies in q4;
            try exact tsb; eauto 3 with slow.
          eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
            try exact tsb; try exact q4; eauto 3 with slow. }
      }
  }
Qed.
Hint Resolve local_per_bar_per_union : slow.

Lemma local_per_bar_per_union2 {o} :
  forall (ts : cts(o)) lib T A B A' B' (eqa eqb : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A' A (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B' B (eqb lib' x))
    -> T ===>(lib) (mkc_union A B)
    -> local_ts_T2 (per_bar (per_union ts)) lib T.
Proof.
  introv tsa tsb comp eqiff alla.
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
    unfold per_union in *; exrepnd.
    exists eqa1 eqb0 A1 A2 B1 B2; dands; auto.
    apply eq_term_equals_sym; introv; split; introv w.

    { subst.
      apply alla2 in w.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      eauto. }

    exrepnd.

    pose proof (alla1 lib0 br1 lib3 ext1 x1) as z; repnd.
    pose proof (z0 lib4 fb lib'0 w (lib_extends_trans w (bar_lib_ext (fbar lib0 br1 lib3 ext1 x1) lib4 fb))) as z0; simpl in *.
    exrepnd.
    apply z0 in w1; clear z0.

    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp z2.
    computes_to_eqval_ext.
    hide_hyp z1.
    computes_to_eqval_ext.
    apply cequivc_ext_mkc_union_right in ceq.
    apply cequivc_ext_mkc_union_right in ceq0.
    apply cequivc_ext_mkc_union_right in ceq1.
    repnd.

    eapply (implies_eq_term_equals_per_union_bar _ (trivial_bar lib'0));[| |eauto];
      apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;[|].

    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
        try (exact tsa); eauto.

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
          try exact tsa; try exact alla5; eauto 3 with slow. }

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies3 in z3;
          try exact tsa; eauto 3 with slow.
        eapply trans_ccequivc_ext_in_ext_eq_types_implies4;
          try exact tsa; try exact z3; eauto 3 with slow. }
    }

    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
        try (exact tsb); eauto.

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
          try exact tsb; try exact alla6; eauto 3 with slow. }

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies3 in z4;
          try exact tsb; eauto 3 with slow.
        eapply trans_ccequivc_ext_in_ext_eq_types_implies4;
          try exact tsb; try exact z4; eauto 3 with slow. }
    }
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

      unfold per_union in allb0.
      unfold per_union in q0.
      exrepnd.

      remember (feqa lib0 br lib'0 xt1 x) as eqz.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqw.

      eapply (lib_per_cond _ eqz); apply allb0; clear allb0.
      eapply (lib_per_cond _ eqw) in h0; apply q0 in h0; clear q0.

      assert (lib_extends lib'4 lib) as xx by eauto 3 with slow.
      dup comp as c.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in c;[|eauto 3 with slow];[].
      computes_to_eqval_ext.
      apply cequivc_ext_mkc_union_right in ceq; repnd.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in comp;[|eauto 3 with slow];[].
      hide_hyp q2.
      computes_to_eqval_ext.
      apply cequivc_ext_mkc_union_right in ceq1; repnd.

      hide_hyp c.
      computes_to_eqval_ext.
      apply cequivc_ext_mkc_union_right in ceq3; repnd.

      eapply (implies_eq_term_equals_per_union_bar _ (trivial_bar lib'4));[| |eauto];
        apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;[|].

      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
          try (exact tsa); eauto.

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
            try exact tsa; try exact allb3; eauto 3 with slow. }

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies3 in q3;
            try exact tsa; eauto 3 with slow.
          eapply trans_ccequivc_ext_in_ext_eq_types_implies4;
            try exact tsa; try exact q3; eauto 3 with slow. }
      }

      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
          try (exact tsb); eauto.

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
            try exact tsb; try exact allb4; eauto 3 with slow. }

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies3 in q4;
            try exact tsb; eauto 3 with slow.
          eapply trans_ccequivc_ext_in_ext_eq_types_implies4;
            try exact tsb; try exact q4; eauto 3 with slow. }
      }
  }
Qed.
Hint Resolve local_per_bar_per_union2 : slow.



(* ====== dest lemmas ====== *)

Lemma dest_close_per_union_l {o} :
  forall (ts : cts(o)) lib T A B A' B' T' eq (eqa eqb : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' B B' (eqb lib' x))
    -> ccomputes_to_valc_ext lib T (mkc_union A B)
    -> close ts lib T T' eq
    -> per_bar (per_union (close ts)) lib T T' eq.
Proof.
  introv tysys dou tsa tsb comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_union; spcast; try exact comp; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x (raise_lib_per eqa x) (raise_lib_per eqb x)) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
  { apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib A A' e)); auto. }
  { apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib B B' e)); auto. }
Qed.

Lemma dest_close_per_union_r {o} :
  forall (ts : cts(o)) lib T A B A' B' T' eq (eqa eqb : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A' A (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' B' B (eqb lib' x))
    -> ccomputes_to_valc_ext lib T' (mkc_union A B)
    -> close ts lib T T' eq
    -> per_bar (per_union (close ts)) lib T T' eq.
Proof.
  introv tysys dou tsa tsb comp cl.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_union2; spcast; try exact comp; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x (raise_lib_per eqa x) (raise_lib_per eqb x)) as reca; simpl in *.
  eapply reca; eauto 3 with slow.
  { apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib A' A e)); auto. }
  { apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib B' B e)); auto. }
Qed.

(*Lemma dest_close_per_union_bar_l {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar bar (fun lib => T ===>(lib) (mkc_union A B))
    -> close ts lib T T' eq
    -> per_union_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_union_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_union_bar_r {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar bar (fun lib => T' ===>(lib) (mkc_union A B))
    -> close ts lib T T' eq
    -> per_union_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_union_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_union_ceq_bar_l {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> T ==b==>(bar) (mkc_union A B)
    -> close ts lib T T' eq
    -> per_union_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_union_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_union_ceq_bar_r {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> T' ==b==>(bar) (mkc_union A B)
    -> close ts lib T T' eq
    -> per_union_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_union_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.*)

(*Lemma dest_close_per_eunion_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_eunion A B)
    -> close ts lib T T' eq
    -> per_eunion (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.

Lemma dest_close_per_eunion_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_eunion A B)
    -> close ts lib T T' eq
    -> per_eunion (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff; auto.
Qed.*)
