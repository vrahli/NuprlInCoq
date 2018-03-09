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

Require Export close_util_func.
Require Export dest_close_util.



(*Definition per_func_ext_or {o} ts lib (T T' : @CTerm o) eq :=
  per_func_ext ts lib T T' eq
  {+} per_bar ts lib T T' eq.*)

Lemma per_func_ext_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_func_ext ts lib T T' eq
    -> per_bar (per_func_ext ts) lib T T' eq.
Proof.
  introv per.

  unfold per_func_ext in *; exrepnd.
  exists (trivial_bar lib) (per_func_ext_eq_lib_per eqa eqb).
  dands; auto.

  {
    apply in_ext_ext_implies_all_in_bar_ext_trivial_bar.
    introv.
    exists (raise_lib_per eqa e) (raise_lib_per_fam eqb e); simpl.
    dands; spcast; eauto 3 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv.
    apply eq_term_equals_sym.
    apply per_bar_eq_per_func_ext_eq_lib_per.
  }
Qed.
Hint Resolve per_func_ext_implies_per_bar : slow.

Lemma local_per_bar_per_func_ext {o} :
  forall (ts : cts(o)) lib T A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A A' (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> T ===>(lib) (mkc_function A v B)
    -> local_ts_T (per_bar (per_func_ext ts)) lib T.
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
    unfold per_func_ext in *; exrepnd.
    exists eqa1 eqb0; dands; auto.
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

    unfold type_family_ext in *; exrepnd.
    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp z2.
    computes_to_eqval_ext.
    hide_hyp z0.
    computes_to_eqval_ext.
    apply constructor_inj_implies_ext in ceq; eauto 3 with slow;[]; repnd.
    apply constructor_inj_implies_ext in ceq0; eauto 3 with slow;[]; repnd.
    apply constructor_inj_implies_ext in ceq1; eauto 3 with slow;[]; repnd.

    eapply implies_eq_term_equals_per_func_ext_eq;[| |eauto];[|].

    {
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
      pose proof (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4
                    ts x A A' A'1 eqa eqa1) as q1.
      repeat (autodimp q1 hype);[|].

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
          try exact tsa; try exact alla6 ; eauto 3 with slow. }

      pose proof (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4
                    ts x A A' A'0 eqa eqa2) as q2.
      repeat (autodimp q2 hyp);[|].

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
          try exact tsa; try exact z3; eauto 3 with slow. }

      eapply in_ext_ext_type_sys_props4_fam_implies_in_ext_ext_eq_term_equals_fam2;
        try exact tsb; eauto.

      { eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies;
          try exact tsb; try exact alla3; eauto 3 with slow. }

      { eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies in z1;
          try exact tsa; eauto 3 with slow;
            [|eapply bcequivc_ext_trans; eauto];[].
        eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies2;
          try exact tsa; try exact z1; eauto 3 with slow. }
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

      unfold per_func_ext in allb0.
      unfold per_func_ext in q0.
      exrepnd.
      unfold type_family_ext in *; exrepnd; spcast.

      remember (feqa lib0 br lib'0 xt1 x) as eqz.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqw.

      eapply (lib_per_cond _ eqz); apply allb0; clear allb0.
      eapply (lib_per_cond _ eqw) in h0; apply q0 in h0; clear q0.

      assert (lib_extends lib'4 lib) as xx by eauto 3 with slow.
      dup comp as c.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in c;[|eauto 3 with slow];[].
      computes_to_eqval_ext.
      apply constructor_inj_implies_ext in ceq; eauto 3 with slow;[]; repnd.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in comp;[|eauto 3 with slow];[].
      hide_hyp q2.
      computes_to_eqval_ext.
      apply constructor_inj_implies_ext in ceq1; eauto 3 with slow;[]; repnd.

      hide_hyp c.
      computes_to_eqval_ext.
      apply constructor_inj_implies_ext in ceq3; eauto 3 with slow;[]; repnd.

      eapply implies_eq_term_equals_per_func_ext_eq;[| |eauto];[|].

      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals2;
          try (exact tsa); eauto.

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
            try exact tsa; try exact allb4; eauto 3 with slow. }

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies in q4;
            try exact tsa; eauto 3 with slow.
          eapply trans_ccequivc_ext_in_ext_eq_types_implies2;
            try exact tsa; try exact q4; eauto 3 with slow. }
      }

      { pose proof (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4
                      ts xx A A' A'0 eqa eqa1) as qq1.
        repeat (autodimp qq1 hyp);[|].

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
            try exact tsa; try exact q4; eauto 3 with slow. }

        pose proof (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals4
                      ts xx A A' A'1 eqa eqa2) as qq2.
        repeat (autodimp qq2 hyp);[|].

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
            try exact tsa; try exact allb4; eauto 3 with slow. }

        eapply in_ext_ext_type_sys_props4_fam_implies_in_ext_ext_eq_term_equals_fam2;
          try exact tsb; eauto.

        { eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies;
            try exact tsb; try exact allb1; eauto 3 with slow.
          eapply bcequivc_ext_sym; auto. }

        { eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies in q1;
            try exact tsa; eauto 3 with slow;
              [|eapply bcequivc_ext_sym; eauto];[].
          eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies2;
            try exact tsa; try exact q1; eauto 3 with slow. }
      }
  }
Qed.
Hint Resolve local_per_bar_per_func_ext : slow.

Lemma local_per_bar_per_func_ext2 {o} :
  forall (ts : cts(o)) lib T A v B A' v' B' (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A' A (eqa lib' x))
    -> in_ext_ext
         lib
         (fun lib' x =>
            forall a a' (e : eqa lib' x a a'),
              type_sys_props4 ts lib' (substc a v' B') (substc a' v B) (eqb lib' x a a' e))
    -> T ===>(lib) (mkc_function A v B)
    -> local_ts_T2 (per_bar (per_func_ext ts)) lib T.
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
    unfold per_func_ext in *; exrepnd.
    exists eqa1 eqb0; dands; auto.
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

    unfold type_family_ext in *; exrepnd.
    apply (ccomputes_to_valc_ext_monotone _ lib'0) in comp;[|eauto 3 with slow];[].
    computes_to_eqval_ext.
    hide_hyp z2.
    computes_to_eqval_ext.
    hide_hyp z0.
    computes_to_eqval_ext.
    apply constructor_inj_implies_ext in ceq; eauto 3 with slow;[]; repnd.
    apply constructor_inj_implies_ext in ceq0; eauto 3 with slow;[]; repnd.
    apply constructor_inj_implies_ext in ceq1; eauto 3 with slow;[]; repnd.

    eapply implies_eq_term_equals_per_func_ext_eq;[| |eauto];[|].

    {
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
      pose proof (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals5
                    ts x A A' A1 eqa eqa1) as q1.
      repeat (autodimp q1 hyp);[|].

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
          try exact tsa; try exact alla6 ; eauto 3 with slow. }

      pose proof (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals5
                    ts x A A' A0 eqa eqa2) as q2.
      repeat (autodimp q2 hyp);[|].

      { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
          try exact tsa; try exact z3; eauto 3 with slow. }

      eapply in_ext_ext_type_sys_props4_fam_implies_in_ext_ext_eq_term_equals_fam3;
        try exact tsb; eauto.

      { eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies3;
          try exact tsb; try exact alla3; eauto 3 with slow. }

      { eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies3 in z1;
          try exact tsa; eauto 3 with slow;
            [|eapply bcequivc_ext_trans; eauto];[].
        eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies4;
          try exact tsa; try exact z1; eauto 3 with slow. }
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

      unfold per_func_ext in allb0.
      unfold per_func_ext in q0.
      exrepnd.
      unfold type_family_ext in *; exrepnd; spcast.

      remember (feqa lib0 br lib'0 xt1 x) as eqz.
      remember (feqa lib4 br2 lib5 ext1 x3) as eqw.

      eapply (lib_per_cond _ eqz); apply allb0; clear allb0.
      eapply (lib_per_cond _ eqw) in h0; apply q0 in h0; clear q0.

      assert (lib_extends lib'4 lib) as xx by eauto 3 with slow.
      dup comp as c.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in c;[|eauto 3 with slow];[].
      computes_to_eqval_ext.
      apply constructor_inj_implies_ext in ceq; eauto 3 with slow;[]; repnd.

      apply (ccomputes_to_valc_ext_monotone _ lib'4) in comp;[|eauto 3 with slow];[].
      hide_hyp q3.
      computes_to_eqval_ext.
      apply constructor_inj_implies_ext in ceq1; eauto 3 with slow;[]; repnd.

      hide_hyp c.
      computes_to_eqval_ext.
      apply constructor_inj_implies_ext in ceq3; eauto 3 with slow;[]; repnd.

      eapply implies_eq_term_equals_per_func_ext_eq;[| |eauto];[|].

      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals3;
          try (exact tsa); eauto.

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
            try exact tsa; try exact allb4; eauto 3 with slow. }

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies3 in q4;
            try exact tsa; eauto 3 with slow.
          eapply trans_ccequivc_ext_in_ext_eq_types_implies4;
            try exact tsa; try exact q4; eauto 3 with slow. }
      }

      { pose proof (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals5
                      ts xx A A' A0 eqa eqa1) as qq1.
        repeat (autodimp qq1 hyp);[|].

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
            try exact tsa; try exact q4; eauto 3 with slow. }

        pose proof (in_ext_ext_type_sys_props4_implies_in_ext_ext_eq_term_equals5
                      ts xx A A' A1 eqa eqa2) as qq2.
        repeat (autodimp qq2 hyp);[|].

        { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
            try exact tsa; try exact allb4; eauto 3 with slow. }

        eapply in_ext_ext_type_sys_props4_fam_implies_in_ext_ext_eq_term_equals_fam3;
          try exact tsb; eauto.

        { eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies3;
            try exact tsb; try exact allb1; eauto 3 with slow.
          eapply bcequivc_ext_sym; auto. }

        { eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies3 in q1;
            try exact tsa; eauto 3 with slow;
              [|eapply bcequivc_ext_sym; eauto];[].
          eapply trans_ccequivc_ext_in_ext_eq_types_fam_implies4;
            try exact tsa; try exact q1; eauto 3 with slow. }
      }
  }
Qed.
Hint Resolve local_per_bar_per_func_ext2 : slow.


(* ====== dest lemmas ====== *)

Lemma dest_close_per_func_l {o} :
  forall (ts : cts(o)) lib T A v B A' v' B' T' eq (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A A' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 (close ts) lib' (substc a v B) (substc a' v' B') (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T (mkc_function A v B)
    -> close ts lib T T' eq
    -> per_bar (per_func_ext (close ts)) lib T T' eq.
Proof.
  introv tysys dou tsa tsb comp cl; try unfold per_func_ext_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_func_ext; spcast; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x (raise_lib_per eqa x)) as reca; simpl in *.
  eapply reca; eauto 3 with slow.

  { apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib A A' e)); auto. }

  { eapply (implies_in_ext_ext_raise_ext_per_fam (fun lib a a' e => type_sys_props4 (close ts) lib (substc a v B) (substc a' v' B') e)); eauto. }
Qed.

Lemma dest_close_per_func_r {o} :
  forall (ts : cts(o)) lib T A v B A' v' B' T' eq (eqa : lib-per(lib,o)) (eqb : lib-per-fam(lib,eqa,o)),
    type_system ts
    -> defines_only_universes ts
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A' A (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => forall a a' (e : eqa lib' x a a'), type_sys_props4 (close ts) lib' (substc a v' B') (substc a' v B) (eqb lib' x a a' e))
    -> ccomputes_to_valc_ext lib T' (mkc_function A v B)
    -> close ts lib T T' eq
    -> per_bar (per_func_ext (close ts)) lib T T' eq.
Proof.
  introv tysys dou tsa tsb comp cl; try unfold per_func_ext_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar_per_func_ext2; spcast; eauto.
  introv br ext; introv.
  pose proof (reca _ br _ ext x (raise_lib_per eqa x)) as reca; simpl in *.
  eapply reca; eauto 3 with slow.

  { apply (implies_in_ext_ext_raise_ext_per (fun lib e => type_sys_props4 (close ts) lib A' A e)); auto. }

  { eapply (implies_in_ext_ext_raise_ext_per_fam (fun lib a a' e => type_sys_props4 (close ts) lib (substc a v' B') (substc a' v B) e)); eauto. }
Qed.

(*Lemma dest_close_per_func_bar_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) (mkc_function A v B))
    -> close ts lib T T' eq
    -> per_func_ext_or (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl; unfold per_func_ext_or.
  inversion cl; clear cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_bar_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T' ===>(lib) (mkc_function A v B))
    -> close ts lib T T' eq
    -> per_func_ext_or (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl; unfold per_func_ext_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_ext_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> in_ext lib (fun lib => T ===>(lib) (mkc_function A v B))
    -> close ts lib T T' eq
    -> per_func_ext_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_func_ext_or.
  inversion cl; clear cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_ext_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> in_ext lib (fun lib => T' ===>(lib) (mkc_function A v B))
    -> close ts lib T T' eq
    -> per_func_ext_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_func_ext_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.*)
