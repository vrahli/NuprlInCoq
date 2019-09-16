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

  Authors: Vincent Rahli

*)


Require Export close_util_bar1.


Lemma close_type_system_bar {o} :
  forall (ts : cts(o)) (lib : @library o) T T' eq (eqa : lib-per(lib,o)),
    ts_implies_per_bar ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> in_open_bar_ext lib (fun lib' x => close ts lib' T T' (eqa lib' x))
    -> in_open_bar_ext lib (fun lib' x => type_sys_props4 (close ts) lib' T T' (eqa lib' x))
    -> (eq <=2=> (per_bar_eq lib eqa))
    -> per_bar (close ts) lib T T' eq
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv ibar tysys dou mon allcl alltsp eqiff per.

  prove_type_sys_props4 SCase; introv; tcsp.

  + SCase "uniquely_valued".
    introv cl.

    eapply eq_term_equals_trans;[eauto|]; clear eqiff.

    apply eq_term_equals_sym; introv; split; intro h.

    {
      eapply in_open_bar_ext_comb; try exact allcl; clear allcl.
      eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp.
      apply in_ext_ext_implies_in_open_bar_ext; introv alltsp allcl.
      apply (close_monotone _ mon _ lib') in cl; auto; exrepnd; eauto 3 with slow.
      apply cl0 in h.
      eapply type_sys_props4_implies_eq_term_equals in cl1;[|eauto].
      apply cl1; auto.
    }

    {
      assert (close ts lib T T' eq) as cl'.
      { apply CL_bar; auto. }

      eapply (close_implies_per_bar_above _ lib) in cl;[|eauto]; eauto 3 with slow.
      unfold per_bar_above in cl; exrepnd.
      apply cl0; clear cl0.

      eapply in_open_bar_ext_comb; try exact h; clear h;[].
      eapply in_open_bar_ext_comb; try exact cl1; clear cl1;[].
      eapply in_open_bar_ext_comb; try exact alltsp; clear alltsp;[].
      eapply in_open_bar_ext_comb; try exact allcl; clear allcl;[].
      apply in_ext_ext_implies_in_open_bar_ext; introv allcl alltsp cl1 h.

      eapply type_sys_props4_implies_eq_term_equals in cl1;[|eauto].
      eapply (lib_per_cond _ eqa0); apply cl1.
      eapply (lib_per_cond _ eqa); eauto.
    }

  + SCase "type_symmetric".
    introv cl eqs.
    apply close_implies_per_bar in cl; auto;[].
    apply CL_bar.
    eapply type_extensionality_per_bar; eauto.

  + SCase "type_value_respecting".
    introv h ceq; apply CL_bar;
      eapply all_in_bar_ext_type_sys_props4_implies_type_value_respecting_per_bar; eauto.

  + SCase "type_value_respecting_trans1".
    introv h ceq cl; apply CL_bar; repndors; subst;
      apply close_implies_per_bar in cl; auto;
        eapply all_in_bar_ext_type_sys_props4_implies_type_value_respecting_trans_per_bar1; eauto.

  + SCase "type_value_respecting_trans2".
    introv h cl ceq; apply CL_bar; repndors; subst;
      apply close_implies_per_bar in cl; auto;
        eapply all_in_bar_ext_type_sys_props4_implies_type_value_respecting_trans_per_bar2; eauto.

  + SCase "term_symmetric".
    introv e.
    unfold per_bar in *; exrepnd.
    allrw per0.
    eapply per_bar_eq_sym; auto; eauto 4 with slow.

  + SCase "term_transitive".
    introv e1 e2.
    unfold per_bar in *; exrepnd.
    allrw per0.
    eapply per_bar_eq_trans; auto; eauto 4 with slow.

  + SCase "term_value_respecting".
    introv e ceq.
    unfold per_bar in *; exrepnd.
    allrw per0.
    eapply per_bar_eq_value_respecting; auto; eauto 4 with slow.

  + SCase "type_gsymmetric".
    split; intro cl; dclose_lr.

    * apply close_implies_per_bar in cl; auto.
      apply CL_bar.
      eapply (all_in_bar_ext_type_sys_props4_implies_type_symmetric_per_bar1 _ _ T T'); eauto.

    * apply close_implies_per_bar in cl; auto.
      apply CL_bar.
      eapply (all_in_bar_ext_type_sys_props4_implies_type_symmetric_per_bar1 _ _ T T'); eauto.

  + SCase "type_mtransitive".
    introv h cl1 cl2.
    apply close_implies_per_bar in cl1; auto.
    apply close_implies_per_bar in cl2; auto.
    dands; apply CL_bar;
      pose proof (all_in_bar_ext_type_sys_props4_implies_type_transitive_per_bar1
                    (close ts) lib T T' eqa eq alltsp per T0 T3 T4 eq1 eq2) as q;
      repeat (autodimp q hyp); tcsp.
Qed.
