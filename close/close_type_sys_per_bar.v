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

  Authors: Vincent Rahli

*)


Require Export type_sys.
Require Export dest_close.
Require Export per_ceq_bar.


Lemma type_sys_props4_implies_eq_term_equals {o} :
  forall ts lib (T T1 T2 : @CTerm o) eq1 eq2,
    type_sys_props4 ts lib T T1 eq1
    -> ts lib T T2 eq2
    -> eq1 <=2=> eq2.
Proof.
  introv tsp eqt.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  eapply uv; eauto.
Qed.

Lemma type_sys_props4_implies_ts {o} :
  forall (ts : cts(o)) (lib : library) (T1 T2 : CTerm) eq,
    type_sys_props4 ts lib T1 T2 eq -> ts lib T1 T2 eq.
Proof.
  introv h.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum; auto.
Qed.

Lemma all_in_bar_ext_type_sys_props4_implies_ts {o} :
  forall (ts : cts(o)) (lib : library) (bar : BarLib lib) (T1 T2 : CTerm) eq,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 ts lib' T1 T2 (eq lib' x))
    -> all_in_bar_ext bar (fun lib' x => ts lib' T1 T2 (eq lib' x)).
Proof.
  introv h br ext; introv.
  apply type_sys_props4_implies_ts; eapply h; eauto 3 with slow.
Qed.

Lemma all_in_bar_close_int {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_int))
    -> all_in_bar_ext bar (fun lib' x => per_int_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_nat {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_Nat))
    -> all_in_bar_ext bar (fun lib' x => per_nat_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_csname {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_csname))
    -> all_in_bar_ext bar (fun lib' x => per_csname_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_atom {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_atom))
    -> all_in_bar_ext bar (fun lib' x => per_atom_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_uatom {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_uatom))
    -> all_in_bar_ext bar (fun lib' x => per_uatom_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_base {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar bar (fun lib => (T) ===>(lib) (mkc_base))
    -> all_in_bar_ext bar (fun lib' x => per_base_bar (close ts) lib' T T' (eqa lib' x)).
Proof.
  introv tsts dou alla allb br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  pose proof (allb lib' br lib'0 ext) as allb.
  simpl in *; spcast.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_eq_term_equals_implies {o} :
  forall {lib} (bar : @BarLib o lib) (eqa eqb : lib-per(lib,o)) t1 t2,
    all_in_bar_ext bar (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> all_in_bar_ext bar (fun lib' x => eqa lib' x t1 t2)
    -> all_in_bar_ext bar (fun lib' x => eqb lib' x t1 t2).
Proof.
  introv alla allb br ext; introv.
  eapply alla; eauto 3 with slow.
  eapply allb; eauto 3 with slow.
Qed.

Lemma all_in_bar_close_approx {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa a b,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> T ==b==>(bar) (mkc_approx a b)
    -> per_bar (per_approx_bar (close ts)) lib T T' (per_bar_eq bar eqa).
Proof.
  introv tsts dou alla allb.
  eapply local_per_bar; eauto 3 with slow.
  introv br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  simpl in *; spcast.
  apply (implies_computes_to_valc_seq_bar_raise_bar _ x) in allb.
  dclose_lr; auto.
Qed.

Lemma all_in_bar_close_cequiv {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eqa a b,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> T ==b==>(bar) (mkc_cequiv a b)
    -> per_bar (per_cequiv_bar (close ts)) lib T T' (per_bar_eq bar eqa).
Proof.
  introv tsts dou alla allb.
  eapply local_per_bar; eauto 3 with slow.
  introv br ext; introv.
  pose proof (alla lib' br lib'0 ext x) as alla.
  simpl in *; spcast.
  apply (implies_computes_to_valc_seq_bar_raise_bar _ x) in allb.
  dclose_lr; auto.
Qed.

Lemma close_type_system_bar {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T T' eq eqa,
    local_ts ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone2 ts
    -> all_in_bar_ext bar (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> all_in_bar_ext bar (fun lib' x => type_sys_props4 (close ts) lib' T T' (eqa lib' x))
    -> (eq <=2=> (per_bar_eq bar eqa))
    -> per_bar (close ts) lib T T' eq
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv locts tysys dou mon allcl alltsp eqiff per.

  prove_type_sys_props4 SCase; introv.

  + SCase "uniquely_valued".
    introv cl.
    clear per.
    eapply eq_term_equals_trans;[eauto|]; clear eqiff.

    introv; apply eq_term_equals_sym; split; intro h.

    {
      introv br ext; introv.
      pose proof (alltsp lib' br lib'0 ext x) as alltsp; simpl in *.
      apply (close_monotone2 _ mon _ lib'0) in cl; auto; exrepnd.
      apply cl0 in h.
      eapply type_sys_props4_implies_eq_term_equals in cl1;[|eauto].
      apply cl1; auto.
    }

    {
      unfold per_bar_eq in *.

      Lemma xxx {o} :
        forall ts lib (bar : @BarLib o lib) T T1 T2 eq eqa t1 t2,
          type_system ts
          -> defines_only_universes ts
          -> all_in_bar_ext bar (fun lib' x => type_sys_props4 (close ts) lib' T T1 (eqa lib' x))
          -> all_in_bar_ext bar (fun lib' x => eqa lib' x t1 t2)
          -> close ts lib T T2 eq
          -> eq t1 t2.
      Proof.
        introv tsts dou tysys eqt cl.
        close_cases (induction cl using @close_ind') Case; introv.

        - Case "CL_init".

          (* prove that this is true about universes,
             and assume that it is true about [ts] *)
          admit.

        - Case "CL_bar".
          apply eqiff.
          introv br ext; introv.
          pose proof (reca lib' br lib'0 ext x (raise_bar bar x) (raise_lib_per eqa x)) as reca; simpl in *.
          repeat (autodimp reca hyp).

          {
            introv b e; introv.
            simpl in *; unfold raise_lib_per; exrepnd.
            eapply tysys; eauto 3 with slow.
          }

          {
            introv b e; introv.
            simpl in *; unfold raise_lib_per; exrepnd.
            eapply eqt; eauto 3 with slow.
          }

        - Case "CL_int".
          unfold per_int_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_int in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_int_bar in tysys; auto.

        - Case "CL_nat".
          unfold per_nat_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_nat in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_nat_bar in tysys; auto.

        - Case "CL_csname".
          unfold per_csname_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_csname in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_csname_bar in tysys; auto.

        - Case "CL_atom".
          unfold per_atom_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_atom in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_atom_bar in tysys; auto.

        - Case "CL_uatom".
          unfold per_uatom_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_uatom in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_uatom_bar in tysys; auto.

        - Case "CL_base".
          unfold per_base_bar in *; exrepnd.
          apply per; clear per.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per0.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per1.
          remember (intersect_bars bar bar0) as b; clear Heqb.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          apply all_in_bar_close_base in tysys; auto.
          apply all_in_bar_ext_and_implies in tysys; repnd.
          eapply all_in_bar_eq_term_equals_implies in tysys;[|eauto 3 with slow].
          apply local_equality_of_base_bar in tysys; auto.

        - Case "CL_approx".
          unfold per_approx_bar in *; exrepnd.
          apply per1; clear per1.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_computes_to_valc_ceq_bar_intersect_bars_right _ bar) in per0.
          apply (implies_computes_to_valc_ceq_bar_intersect_bars_right _ bar) in per3.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per2.
          remember (intersect_bars bar bar0) as bar1; clear Heqbar1.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          eapply all_in_bar_close_approx in tysys; eauto.
          unfold per_bar in tysys; exrepnd.
          fold (per_bar_eq bar1 eqa t1 t2) in *.
          apply tysys1 in eqt; clear tysys1.

          apply (local_equality_of_approx_bar bar2).
          introv br ext x.
          pose proof (tysys0 lib' br lib'0 ext x) as tysys0; simpl in *.
          pose proof (eqt lib' br lib'0 ext x) as eqt; simpl in *.
          unfold per_approx_bar in tysys0; exrepnd.
          apply tysys0 in eqt; clear tysys0.
          eapply (eq_per_approx_eq_bar (intersect_bars (raise_bar bar1 x) bar3)); eauto.
          eapply two_computes_to_valc_ceq_bar_mkc_approx; eauto 3 with slow.

        - Case "CL_cequiv".
          unfold per_cequiv_bar in *; exrepnd.
          apply per1; clear per1.

          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in tysys.
          apply (implies_all_in_bar_ext_intersect_bars_left _ bar0) in eqt.
          apply (implies_computes_to_valc_ceq_bar_intersect_bars_right _ bar) in per0.
          apply (implies_computes_to_valc_ceq_bar_intersect_bars_right _ bar) in per3.
          apply (implies_all_in_bar_intersect_bars_right _ bar) in per2.
          remember (intersect_bars bar bar0) as bar1; clear Heqbar1.

          apply all_in_bar_ext_type_sys_props4_implies_ts in tysys.
          eapply all_in_bar_close_cequiv in tysys; eauto.
          unfold per_bar in tysys; exrepnd.
          fold (per_bar_eq bar1 eqa t1 t2) in *.
          apply tysys1 in eqt; clear tysys1.

          apply (local_equality_of_cequiv_bar bar2).
          introv br ext x.
          pose proof (tysys0 lib' br lib'0 ext x) as tysys0; simpl in *.
          pose proof (eqt lib' br lib'0 ext x) as eqt; simpl in *.
          unfold per_cequiv_bar in tysys0; exrepnd.
          apply tysys0 in eqt; clear tysys0.
          eapply (eq_per_cequiv_eq_bar (intersect_bars (raise_bar bar1 x) bar3)); eauto.
          eapply two_computes_to_valc_ceq_bar_mkc_cequiv; eauto 3 with slow.

        - Case "CL_eq".

      Qed.

    }

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
      apply CL_int; auto;
        assert (type_symmetric (per_int_bar (close ts))) as tys
          by (apply per_int_bar_type_symmetric);
        assert (type_extensionality (per_int_bar (close ts))) as tye
            by (apply per_int_bar_type_extensionality);
        apply tye with (eq := eq); auto.

  + SCase "type_value_respecting"; sp; subst; apply CL_int;
      assert (type_value_respecting (per_int_bar (close ts)))
      as tvr by (apply per_int_bar_type_value_respecting).

    * apply tvr; auto;
        apply @type_system_type_mem with (T' := T'); auto;
          try (apply per_int_bar_type_symmetric);
          try (apply per_int_bar_type_transitive).

    * apply tvr; auto.
      apply @type_system_type_mem1 with (T := T); auto;
        try (apply per_int_bar_type_transitive);
        try (apply per_int_bar_type_symmetric).

  + SCase "type_value_respecting_trans".
    eapply type_equality_respecting_trans_per_int_bar_implies; eauto.
    apply type_system_implies_type_equality_respecting_trans.
    apply per_int_type_system.

  + SCase "term_symmetric".
    assert (term_symmetric (per_int_bar (close ts))) as tes
        by (apply per_int_bar_term_symmetric).
    eapply tes; eauto.

  + SCase "term_transitive".
    assert (term_transitive (per_int_bar (close ts))) as tet
        by (apply per_int_bar_term_transitive).
    eapply tet; eauto.

  + SCase "term_value_respecting".
    assert (term_value_respecting (per_int_bar (close ts))) as tvr
        by (apply per_int_bar_term_value_respecting).
    apply tvr with (T := T); auto.
    apply @type_system_type_mem with (T' := T'); auto.

    * apply per_int_bar_type_symmetric.

    * apply per_int_bar_type_transitive.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr.

    * apply CL_int; allunfold @per_int_bar; sp.
      exists bar0; dands; auto.

    * apply CL_int; allunfold @per_int_bar; sp.
      exists bar0; dands; auto.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive"; repdors; subst; dclose_lr;
      dands; apply CL_int; allunfold @per_int_bar; sp;
        exists (intersect_bars bar1 bar0); dands; eauto 2 with slow.
Qed.
