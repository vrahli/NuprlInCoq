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


Lemma close_type_system_product {o} :
  forall lib (ts : cts(o))
         T T'
         (eq : per)
         A A' v v' B B' eqa eqb,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> computes_to_valc lib T (mkc_product A v B)
    -> computes_to_valc lib T' (mkc_product A' v' B')
    -> in_ext lib (fun lib => close ts lib A A' (eqa lib))
    -> in_ext lib (fun lib => type_sys_props4 (close ts) lib A A' (eqa lib))
    -> in_ext lib
              (fun lib =>
                 forall a a' (e : eqa lib a a'),
                   close ts lib (B)[[v\\a]] (B')[[v'\\a']] (eqb lib a a' e))
    -> in_ext lib
              (fun lib =>
                 forall a a' (e : eqa lib a a'),
                   type_sys_props4 (close ts) lib (B)[[v\\a]] (B')[[v'\\a']] (eqb lib a a' e))
    -> (eq <=2=> (per_product_eq_bar lib eqa eqb))
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tsts dou mon c1 c2 cla tspa clb tspb eqiff.

  prove_type_sys_props4 SCase; introv.

  + SCase "uniquely_valued".
    introv cl.
    dclose_lr; clear cl.

    unfold per_product_bar in h; exrepd.
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;exact e].
    eapply eq_term_equals_trans;[eauto|].

    apply eq_term_equals_per_product_eq_bar; eauto 3 with slow.

  + SCase "type_symmetric".
    introv cl ee.
    dclose_lr; clear cl; apply CL_product; eauto 3 with slow.

  + SCase "type_value_respecting".
    introv ee ceq; repndors; subst; apply CL_product;
      exists eqa eqb; dands; auto.

    {
      eapply ccequivc_ext_product in ceq;[|eauto]; exrepnd; spcast.
      eapply type_family_ext_cequivc; eauto.
    }

    {
      eapply ccequivc_ext_product in ceq;[|eauto]; exrepnd; spcast.
      eapply type_family_ext_cequivc2; eauto.
    }

  + SCase "type_value_respecting_trans".
    introv ee ceq cl.
    repndors; subst.

    {
      eapply ccequivc_ext_product in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_product.
      unfold per_product_bar in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].


      eapply type_family_ext_value_respecting_trans1; eauto 3 with slow.
    }

    {
      eapply ccequivc_ext_product in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_product.
      unfold per_product_bar in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans2; eauto 3 with slow.
    }

    {
      eapply ccequivc_ext_product in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_product.
      unfold per_product_bar in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans3; eauto 3 with slow.
    }

    {
      eapply ccequivc_ext_product in ceq;[|eauto]; exrepnd; spcast.
      dclose_lr.
      clear cl.
      apply CL_product.
      unfold per_product_bar in *; exrepnd.
      exists eqa0 eqb0; dands; auto;[].
      eapply type_family_ext_value_respecting_trans4; eauto 3 with slow.
    }

  + SCase "term_symmetric".
    introv ee.
    apply eqiff in ee; apply eqiff; clear eqiff.
    apply per_product_eq_bar_sym; eauto 3 with slow.

  + SCase "term_transitive".
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff; clear eqiff.
    eapply per_product_eq_bar_trans; try exact ee1; eauto; eauto 3 with slow.

  + SCase "term_value_respecting".
    introv ee ceq.
    apply eqiff in ee; apply eqiff; clear eqiff.
    apply per_product_eq_bar_cequivc; eauto 3 with slow.

  + SCase "type_gsymmetric".
    split; intro cl; dclose_lr; clear cl; apply CL_product.
    { eapply per_product_bar_sym; eauto. }
    { eapply per_product_bar_sym_rev; eauto. }

  + SCase "type_gtransitive".
    apply CL_product.
    exists eqa eqb; dands; auto.
    eexists; eexists; eexists; eexists; eexists; eexists; dands; spcast; eauto.

  + SCase "type_mtransitive".
    introv ee cl1 cl2; repndors; subst; dclose_lr; clear cl1 cl2;
      dands; apply CL_product.
    { eapply per_product_bar_trans1; try exact h; try exact h0; eauto. }
    { eapply per_product_bar_trans2; try exact h; try exact h0; eauto. }
    { eapply per_product_bar_trans3; try exact h; try exact h0; eauto. }
    { eapply per_product_bar_trans4; try exact h; try exact h0; eauto. }
Qed.
