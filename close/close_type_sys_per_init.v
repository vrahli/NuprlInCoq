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


Require Export type_sys.
Require Export dest_close.
Require Export per_ceq_bar.


Lemma ccequivc_ext_preserves_computes_to_uni {o} :
  forall lib (T T' : @CTerm o),
    ccequivc_ext lib T T'
    -> computes_to_uni lib T
    -> computes_to_uni lib T'.
Proof.
  introv ceq comp.
  unfold computes_to_uni in *; exrepnd.
  exists bar.
  introv br ext.
  pose proof (comp0 _ br _ ext) as comp0; simpl in *.
  assert (lib_extends lib'0 lib) as x by eauto 3 with slow.
  exrepnd; exists i; eauto 3 with slow.
Qed.
Hint Resolve ccequivc_ext_preserves_computes_to_uni : slow.

Lemma type_equality_respecting_trans1_init_implies {o} :
  forall (ts : cts(o)) lib T T',
    local_ts ts
    -> computes_to_uni lib T
    -> computes_to_uni lib T'
    -> type_equality_respecting_trans1 ts lib T T'
    -> type_equality_respecting_trans1 (close ts) lib T T'.
Proof.
  introv locts inbar1 inbar2 trans h ceq cl.
  apply CL_init.
  eapply trans; eauto.
  repndors; subst.

  - apply ccequivc_ext_preserves_computes_to_uni in ceq; auto.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_uni in ceq; auto.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_uni in ceq; auto.
    dclose_lr; auto.

  - apply ccequivc_ext_preserves_computes_to_uni in ceq; auto.
    dclose_lr; auto.
Qed.

Lemma type_equality_respecting_trans2_init_implies {o} :
  forall (ts : cts(o)) lib T T',
    local_ts ts
    -> computes_to_uni lib T
    -> computes_to_uni lib T'
    -> type_equality_respecting_trans2 ts lib T T'
    -> type_equality_respecting_trans2 (close ts) lib T T'.
Proof.
  introv locts inbar1 inbar2 trans h cl ceq.
  apply CL_init.
  eapply trans; eauto.
  repndors; subst; dclose_lr; auto.
Qed.

Lemma computes_to_valc_uni_implies_all_in_bar_trivial {o} :
  forall lib (T : @CTerm o) i,
    (T ===>(lib) (mkc_uni i))
    -> all_in_bar (trivial_bar lib) (fun lib => (T ===>(lib) (mkc_uni i))).
Proof.
  introv comp br ext; simpl in *.
  apply (ccomputes_to_valc_ext_monotone lib lib'0); eauto 3 with slow.
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
  usedou.

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

  + SCase "type_value_respecting_trans1".
    introv h ceq cl.
    eapply type_equality_respecting_trans1_init_implies;
      try (exact h); eauto 3 with slow.
    apply type_system_implies_type_equality_respecting_trans1; auto.

  + SCase "type_value_respecting_trans2".
    introv h ceq cl.
    eapply type_equality_respecting_trans2_init_implies;
      try (exact h); eauto 3 with slow.
    apply type_system_implies_type_equality_respecting_trans2; auto.

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
