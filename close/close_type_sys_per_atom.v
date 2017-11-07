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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys.
Require Import dest_close.
Require Export per_ceq_bar.


Lemma per_atom_bar_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_atom_bar ts).
Proof.
 unfold uniquely_valued, per_atom_bar, eq_term_equals; sp.
 allrw; sp.
Qed.

Lemma per_atom_bar_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_atom_bar ts).
Proof.
  unfold type_extensionality, per_atom_bar, eq_term_equals; sp.
  allrw <-; sp.
Qed.

Lemma per_atom_bar_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_atom_bar ts).
Proof.
  introv h; unfold per_atom_bar in *; exrepnd; dands; auto.
  exists bar; dands; auto.
Qed.

Lemma per_atom_bar_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_atom_bar ts).
Proof.
  introv per1 per2.
  unfold per_atom_bar in *; exrepnd; dands; auto.

  exists (intersect_bars bar bar0).
  dands.

  - introv i j; simpl in *; exrepnd.
    pose proof (per3 lib2) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.

  - introv i j; simpl in *; exrepnd.
    pose proof (per4 lib1) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.
Qed.

Lemma per_atom_bar_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_atom_bar ts).
Proof.
  introv per ceq.
  unfold type_value_respecting, per_atom_bar in *; exrepnd.
  dands; auto;[].
  exists bar; dands; auto.
  introv ie i.
  applydup per0 in i; auto.
  pose proof (ceq lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q;[].
  spcast.
  eapply cequivc_atom; eauto.
Qed.

Lemma per_atom_bar_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_atom_bar ts).
Proof.
  introv; unfold term_symmetric, term_equality_symmetric, per_atom_bar.
  introv k e; repnd.
  allrw.
  apply k in e.
  unfold equality_of_atom_bar in *; exrepnd.
  exists bar.
  introv ie i.
  apply e0 in i; eauto 3 with slow.
  exrepnd; exists s; tcsp.
Qed.

Lemma per_atom_bar_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_atom_bar ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_atom_bar.
  introv cts per i j.
  exrepnd.
  rw per in i; rw per in j; rw per; clear per.
  allunfold @equality_of_atom_bar; exrepnd.

  exists (intersect_bars bar1 bar0).
  unfold equality_of_atom_bar1 in *.
  introv i j; simpl in *; exrepnd.

  pose proof (i0 lib1) as q; autodimp q hyp; clear i0.
  pose proof (q lib'0) as w; clear q; autodimp w hyp; eauto 2 with slow; simpl in w.

  pose proof (j0 lib2) as q; autodimp q hyp; clear j0.
  pose proof (q lib'0) as z; clear q; autodimp z hyp; eauto 2 with slow; simpl in z.
  exrepnd; spcast.
  computes_to_eqval.
  eexists; dands; spcast; eauto.
Qed.

(* !! MOVE to cequiv *)
Lemma cequiv_token {pp} :
  forall lib T T' s,
    @computes_to_value pp lib T (mk_token s)
    -> cequiv lib T T'
    -> computes_to_value lib T' (mk_token s).
Proof.
  sp.
  apply cequiv_canonical_form with (t' := T') in X; sp.
  apply @lblift_cequiv0 in p; subst; auto.
Qed.

(* !! MOVE to cequiv *)
Lemma cequivc_token {pp} :
  forall lib T T' s,
    computes_to_valc lib T (mkc_token s)
    -> @cequivc pp lib T T'
    -> computes_to_valc lib T' (mkc_token s).
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

Lemma per_atom_bar_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_atom_bar ts).
Proof.
  introv h e ceq.
  unfold per_nat_bar in *; exrepnd; spcast.
  apply h in e; apply h; clear h.
  unfold equality_of_atom_bar in *.
  exrepnd; exists bar.
  introv ie i; applydup e0 in i; auto.
  unfold equality_of_atom_bar1 in *; exrepnd.
  exists s; repnd; dands; auto.
  pose proof (ceq lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q;[].
  spcast.
  eapply cequivc_token; eauto.
Qed.

Lemma per_atom_bar_type_system {p} :
  forall (ts : cts(p)), type_system (per_atom_bar ts).
Proof.
  intros; unfold type_system; sp.
  - apply per_atom_bar_uniquely_valued; auto.
  - apply per_atom_bar_type_extensionality; auto.
  - apply per_atom_bar_type_symmetric; auto.
  - apply per_atom_bar_type_transitive; auto.
  - apply per_atom_bar_type_value_respecting; auto.
  - apply per_atom_bar_term_symmetric; auto.
  - apply per_atom_bar_term_transitive; auto.
  - apply per_atom_bar_term_value_respecting; auto.
Qed.

Lemma type_equality_respecting_trans_per_atom_bar_implies {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) T T',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) mkc_atom)
    -> all_in_bar bar (fun lib => T' ===>(lib) mkc_atom)
    -> type_equality_respecting_trans (per_atom_bar (close ts)) lib T T'
    -> type_equality_respecting_trans (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply CL_atom.
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

Lemma close_type_system_atom {p} :
  forall lib (ts : cts(p)) T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> per_atom_bar (close ts) lib T T' eq
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv X X0 mon per.

  duplicate per as pi.
  unfold per_atom_bar in pi; exrepnd; spcast.

  prove_type_sys_props4 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    * SSCase "CL_atom".
      assert (uniquely_valued (per_atom_bar (close ts))) as uv
        by (apply per_atom_bar_uniquely_valued).
      eapply uv; eauto.
      eapply uniquely_valued_trans5; eauto.
      { apply per_atom_bar_type_extensionality. }
      { apply per_atom_bar_type_symmetric. }
      { apply per_atom_bar_type_transitive. }

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_atom; auto;
    assert (type_symmetric (per_atom_bar (close ts))) as tys
      by (apply per_atom_bar_type_symmetric);
    assert (type_extensionality (per_atom_bar (close ts))) as tye
      by (apply per_atom_bar_type_extensionality);
    apply tye with (eq := eq); auto.

  + SCase "type_value_respecting"; sp; subst; apply CL_atom;
    assert (type_value_respecting (per_atom_bar (close ts)))
           as tvr
           by (apply per_atom_bar_type_value_respecting).

    apply tvr; auto;
    apply @type_system_type_mem with (T' := T'); auto;
    try (apply per_atom_bar_type_symmetric);
    try (apply per_atom_bar_type_transitive).

    apply tvr; auto.
    apply @type_system_type_mem1 with (T := T); auto;
    try (apply per_atom_bar_type_transitive);
    try (apply per_atom_bar_type_symmetric).

  + SCase "type_value_respecting_trans".
    eapply type_equality_respecting_trans_per_atom_bar_implies; eauto.
    apply type_system_implies_type_equality_respecting_trans.
    apply per_atom_bar_type_system.

  + SCase "term_symmetric".
    assert (term_symmetric (per_atom_bar (close ts))) as tes
      by (apply per_atom_bar_term_symmetric).
    eapply tes; eauto.

  + SCase "term_transitive".
    assert (term_transitive (per_atom_bar (close ts))) as tet
      by (apply per_atom_bar_term_transitive).
    eapply tet; eauto.

  + SCase "term_value_respecting".
    assert (term_value_respecting (per_atom_bar (close ts))) as tvr
      by (apply per_atom_bar_term_value_respecting).
    apply tvr with (T := T); auto.
    apply @type_system_type_mem with (T' := T'); auto.
    apply per_atom_bar_type_symmetric.
    apply per_atom_bar_type_transitive.

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr.

    { apply CL_atom; allunfold @per_atom_bar; sp.
      eexists; dands; eauto. }

    { apply CL_atom; allunfold @per_atom_bar; sp.
      eexists; dands; eauto. }

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive"; repdors; subst; dclose_lr;
      dands; apply CL_atom; allunfold @per_atom_bar; sp;
        exists (intersect_bars bar1 bar0); dands; eauto 2 with slow.
Qed.
