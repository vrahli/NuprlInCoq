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


Require Export close_util_nat.


Lemma close_type_system_nat {p} :
  forall (ts : cts(p)) lib T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> per_nat_bar (close ts) lib T T' eq
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv X X0 mon per.

  duplicate per as pi.
  unfold per_nat_bar in pi; exrepnd; spcast.

  prove_type_sys_props4 SCase; intros.

  + SCase "uniquely_valued".

    (* We need to extend the dclose_lr tactic to handle all_in_bar bar (fun lib => T ===>(lib) T') *)
    dclose_lr.

    * SSCase "CL_int".
      assert (uniquely_valued (per_nat_bar (close ts))) as uv
        by (apply per_nat_bar_uniquely_valued).
      eapply uv;eauto.
      eapply uniquely_valued_trans5;eauto.
      { apply per_nat_bar_type_extensionality. }
      { apply per_nat_bar_type_symmetric. }
      { apply per_nat_bar_type_transitive. }

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
      apply CL_nat; auto;
        assert (type_symmetric (per_nat_bar (close ts))) as tys
          by (apply per_nat_bar_type_symmetric);
        assert (type_extensionality (per_nat_bar (close ts))) as tye
            by (apply per_nat_bar_type_extensionality);
        eapply tye; eauto.

  + SCase "type_value_respecting"; sp; subst; apply CL_nat;
    assert (type_value_respecting (per_nat_bar (close ts)))
           as tvr
           by (apply per_nat_bar_type_value_respecting).

    * apply tvr; auto;
        apply @type_system_type_mem with (T' := T'); auto;
          try (apply per_nat_bar_type_symmetric);
          try (apply per_nat_bar_type_transitive).

    * apply tvr; auto.
      apply @type_system_type_mem1 with (T := T); auto;
        try (apply per_nat_bar_type_transitive);
        try (apply per_nat_bar_type_symmetric).

  + SCase "type_value_respecting_trans".
    eapply type_equality_respecting_trans_per_nat_bar_implies; eauto.
    apply type_system_implies_type_equality_respecting_trans.
    apply per_nat_type_system.

  + SCase "term_symmetric".
    assert (term_symmetric (per_nat_bar (close ts))) as tes
        by (apply per_nat_bar_term_symmetric).
    eapply tes; eauto.

  + SCase "term_transitive".
    assert (term_transitive (per_nat_bar (close ts))) as tet
        by (apply per_nat_bar_term_transitive).
    eapply tet; eauto.

  + SCase "term_value_respecting".
    assert (term_value_respecting (per_nat_bar (close ts))) as tvr
        by (apply per_nat_bar_term_value_respecting).
    apply tvr with (T := T); auto.
    apply @type_system_type_mem with (T' := T'); auto.

    * apply per_nat_bar_type_symmetric.

    * apply per_nat_bar_type_transitive.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr.

    * apply CL_nat; allunfold @per_nat_bar; sp.
      exists bar0; dands; auto.

    * apply CL_nat; allunfold @per_nat_bar; sp.
      exists bar0; dands; auto.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive"; repdors; subst; dclose_lr;
      dands; apply CL_nat; allunfold @per_nat_bar; sp;
        exists (intersect_bars bar1 bar0); dands; eauto 2 with slow.
Qed.
