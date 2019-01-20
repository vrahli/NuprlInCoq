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


  Website: http://nuprl.org/html/verification/
  Authors: Vincent Rahli

*)


Require Export close_util_csname.


Lemma close_type_system_csname {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> per_csname (close ts) lib T T' eq
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tysys dou mon per.

  duplicate per as pi.
  unfold per_csname in pi; exrepnd; spcast.

  prove_type_sys_props4 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    assert (uniquely_valued (per_bar (per_csname (close ts)))) as uv
        by (apply per_bar_per_csname_uniquely_valued).
    eapply uv; eauto.
    eapply uniquely_valued_trans5; eauto 3 with slow.

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
      apply per_bar_per_csname_implies_close;
      apply per_csname_implies_per_bar_per_csname in per.

    assert (type_symmetric (per_bar (per_csname (close ts)))) as tys
        by (apply per_bar_per_csname_type_symmetric).
    assert (type_extensionality (per_bar (per_csname (close ts)))) as tye
        by (apply per_bar_per_csname_type_extensionality).
    apply tye with (eq := eq); auto.

  + SCase "type_value_respecting"; repndors; subst;
      apply per_bar_per_csname_implies_close;
      apply per_csname_implies_per_bar_per_csname in per;
      assert (type_value_respecting (per_bar (per_csname (close ts))))
        as tvr by (apply per_bar_per_csname_type_value_respecting).

    * apply tvr; auto;
        apply @type_system_type_mem with (T' := T'); auto;
          try (apply per_bar_per_csname_type_symmetric);
          try (apply per_bar_per_csname_type_transitive).

    * apply tvr; auto.
      apply @type_system_type_mem1 with (T := T); auto;
        try (apply per_bar_per_csname_type_transitive);
        try (apply per_bar_per_csname_type_symmetric).

  + SCase "type_value_respecting_trans".
    eapply type_equality_respecting_trans_per_bar_per_csname_implies; eauto.
    apply type_system_implies_type_equality_respecting_trans.
    apply per_bar_per_csname_type_system.

  + SCase "term_symmetric".
    assert (term_symmetric (per_bar (per_csname (close ts)))) as tes
      by (apply per_bar_per_csname_term_symmetric).
    eapply tes; eauto 3 with slow.

  + SCase "term_transitive".
    assert (term_transitive (per_bar (per_csname (close ts)))) as tet
      by (apply per_bar_per_csname_term_transitive).
    eapply tet; eauto 3 with slow.

  + SCase "term_value_respecting".
    assert (term_value_respecting (per_bar (per_csname (close ts)))) as tvr
      by (apply per_bar_per_csname_term_value_respecting).
    apply tvr with (T := T); auto.
    apply @type_system_type_mem with (T' := T'); auto; eauto 3 with slow.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr.

    { apply per_bar_per_csname_implies_close.
      apply per_bar_per_csname_type_symmetric; auto. }

    { apply per_bar_per_csname_implies_close.
      apply per_bar_per_csname_type_symmetric; auto. }

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive"; repdors; subst; dclose_lr;
      dands; apply per_bar_per_csname_implies_close.

    { apply per_bar_per_csname_type_transitive with (T2 := T); auto.
      eapply per_bar_per_csname_type_extensionality;[eauto|].
      apply per_bar_per_csname_type_symmetric in h0.
      eapply per_bar_per_csname_uniquely_valued2; eauto. }

    { apply per_bar_per_csname_type_transitive with (T2 := T); auto.
      eapply per_bar_per_csname_type_extensionality;[eauto|].
      apply per_bar_per_csname_type_symmetric in h0.
      eapply per_bar_per_csname_uniquely_valued2; eauto. }

    { apply per_bar_per_csname_type_transitive with (T2 := T'); auto.
      eapply per_bar_per_csname_type_extensionality;[eauto|].
      apply per_bar_per_csname_type_symmetric in h0.
      eapply per_bar_per_csname_uniquely_valued2; eauto. }

    { apply per_bar_per_csname_type_transitive with (T2 := T'); auto.
      eapply per_bar_per_csname_type_extensionality;[eauto|].
      apply per_bar_per_csname_type_symmetric in h0.
      eapply per_bar_per_csname_uniquely_valued2; eauto. }
Qed.