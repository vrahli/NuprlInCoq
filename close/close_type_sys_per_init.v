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


Require Export type_sys.
Require Export dest_close.
Require Export per_ceq_bar.



Lemma type_equality_respecting_trans_init_implies {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) T T' i j,
    local_ts ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) (mkc_uni i))
    -> all_in_bar bar (fun lib => T' ===>(lib) (mkc_uni j))
    -> type_equality_respecting_trans ts lib T T'
    -> type_equality_respecting_trans (close ts) lib T T'.
Proof.
  introv locts tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply CL_init.
  eapply trans; eauto.
  repndors; subst.

  - eapply ccequivc_ext_preserves_all_in_bar in ceq;[|eauto];[].
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_all_in_bar in ceq;[|eauto];[].
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_all_in_bar in ceq;[|eauto];[].
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_all_in_bar in ceq;[|eauto];[].
    dclose_lr; auto.
Qed.

Lemma computes_to_valc_uni_implies_all_in_bar_trivial {o} :
  forall lib (T : @CTerm o) i,
    (T ===>(lib) (mkc_uni i))
    -> all_in_bar (trivial_bar lib) (fun lib => (T ===>(lib) (mkc_uni i))).
Proof.
  introv comp br ext; simpl in *.
  pose proof (computes_to_valc_preserves_lib_extends lib lib'0) as q.
  autodimp q hyp; eauto 3 with slow.
  spcast.
  apply q in comp; exrepnd.
  apply alphaeqc_mkc_uni in comp0; subst; auto.
Qed.
Hint Resolve computes_to_valc_uni_implies_all_in_bar_trivial : slow.

Lemma close_type_system_init {p} :
  forall (ts : cts(p)) lib T T' eq,
    local_ts ts
    -> type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> ts lib T T' eq
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv locts tysys dou mon e.
  use_dou.

  prove_type_sys_props4 SCase; introv.

  + SCase "uniquely_valued".
    introv cl.
    spcast; dest_close_lr h; try spts.

  + SCase "type_symmetric".
    introv cl eqiff.
    repdors; subst; spcast; dest_close_lr h; apply CL_init; spts.

  + SCase "type_value_respecting".
    introv h ceq.
    apply CL_init; sp; subst; try spts.

  + SCase "type_value_respecting_trans".
    introv h ceq cl.
    eapply type_equality_respecting_trans_init_implies;
      try (exact h); eauto 3 with slow.
    apply type_system_implies_type_equality_respecting_trans; auto.

  + SCase "term_symmetric".
    onedts uv tye tys tyt tyvr tes tet tevr.
    apply tes with (lib := lib) (T := T) (T' := T'); auto.

  + SCase "term_transitive".
    onedts uv tye tys tyt tyvr tes tet tevr.
    apply tet with (lib := lib) (T := T) (T' := T'); auto.

  + SCase "term_value_respecting".
    onedts uv tye tys tyt tyvr tes tet tevr.
    apply tevr with (T := T); auto.
    use_trans T'; sp.

  + SCase "type_gsymmetric".
    sp; split; sp; subst; spcast; dest_close_lr h; apply CL_init; sp; try spts.

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    introv h cl1 cl2.
    repdors; subst; spcast; dclose_lr; dands; apply CL_init; sp; spts.
Qed.
