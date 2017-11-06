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
Require Import dest_close.
Require Import per_ceq_bar.


Lemma per_nat_bar_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_nat_bar ts).
Proof.
 unfold uniquely_valued, per_nat_bar, eq_term_equals; sp.
 allrw; sp.
Qed.

Lemma per_nat_bar_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_nat_bar ts).
Proof.
  unfold type_extensionality, per_nat_bar, eq_term_equals; sp.
  allrw <-; sp.
Qed.

Lemma per_nat_bar_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_nat_bar ts).
Proof.
  unfold type_symmetric, per_nat_bar; sp.
  exists bar; dands; auto.
Qed.

Lemma equality_of_nat_sym {o} :
  forall lib (t1 t2 : @CTerm o),
    equality_of_nat lib t1 t2
    -> equality_of_nat lib t2 t1.
Proof.
  introv e; unfold equality_of_nat in *; exrepnd.
  exists n; auto.
Qed.
Hint Resolve equality_of_nat_sym : slow.

Lemma per_nat_bar_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_nat_bar ts).
Proof.
  introv h e.
  unfold per_nat_bar in h; exrepnd.
  apply h in e; apply h.
  unfold equality_of_nat_bar in *; exrepnd; exists bar0.
  introv ie i; apply e0 in i; eauto 2 with slow.
Qed.

Lemma cequivc_Nat {o} :
  forall lib (T T' : @CTerm o),
    computes_to_valc lib T mkc_Nat
    -> cequivc lib T T'
    -> computes_to_valc lib T' mkc_Nat.
Proof.
  sp.
  allapply @computes_to_valc_to_valuec; allsimpl.
  apply cequivc_canonical_form with (t' := T') in X; sp.
  apply lblift_cequiv0 in p; subst; auto.
Qed.

Lemma per_nat_bar_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_nat_bar ts).
Proof.
  introv per ceq.
  unfold type_value_respecting, per_nat_bar in *; exrepnd; GC.
  dands; auto;[].
  exists bar; dands; auto.
  introv ie i.
  applydup per0 in i; auto.
  pose proof (ceq lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q;[].
  spcast.
  eapply cequivc_Nat; eauto.
Qed.

Lemma per_nat_bar_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_nat_bar ts).
Proof.
  introv h e ceq.
  unfold per_nat_bar in *; exrepnd; spcast.
  apply h in e; apply h; clear h.
  unfold equality_of_nat_bar in *.
  exrepnd; exists bar0.
  introv ie i; applydup e0 in i; auto.
  unfold equality_of_nat in *; exrepnd.
  exists n; repnd; dands; auto.
  pose proof (ceq lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q;[].
  spcast.
  apply @cequivc_integer with (t := t); auto.
Qed.

Lemma per_nat_bar_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_nat_bar ts).
Proof.
  introv per1 per2.
  unfold type_transitive, per_nat_bar in *; exrepnd.
  dands; auto.

  exists (intersect_bars bar bar0).
  dands.

  - introv i j; simpl in *; exrepnd.
    pose proof (per3 lib2) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.

  - introv i j; simpl in *; exrepnd.
    pose proof (per4 lib1) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.
Qed.

Lemma per_nat_bar_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_nat_bar ts).
Proof.
  introv per i j.
  unfold per_nat_bar in per; exrepnd.
  apply per in i; apply per in j; apply per.
  unfold equality_of_nat_bar in *.
  exrepnd.

  clear per per0 per1.

  exists (intersect_bars bar1 bar0).
  unfold equality_of_nat in *.
  introv i j; simpl in *; exrepnd.

  pose proof (i0 lib1) as q; autodimp q hyp; clear i0.
  pose proof (q lib'0) as w; clear q; autodimp w hyp; eauto 2 with slow; simpl in w.

  pose proof (j0 lib2) as q; autodimp q hyp; clear j0.
  pose proof (q lib'0) as z; clear q; autodimp z hyp; eauto 2 with slow; simpl in z.
  exrepnd; spcast.
  computes_to_eqval.
  eexists; dands; spcast; eauto.
Qed.

Lemma per_nat_type_system {p} :
  forall (ts : cts(p)), type_system (per_nat_bar ts).
Proof.
  intros; unfold type_system; sp.
  - apply per_nat_bar_uniquely_valued.
  - apply per_nat_bar_type_extensionality.
  - apply per_nat_bar_type_symmetric.
  - apply per_nat_bar_type_transitive.
  - apply per_nat_bar_type_value_respecting.
  - apply per_nat_bar_term_symmetric.
  - apply per_nat_bar_term_transitive.
  - apply per_nat_bar_term_value_respecting.
Qed.

Lemma type_equality_respecting_trans_per_nat_bar_implies {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) T T',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) mkc_Nat)
    -> all_in_bar bar (fun lib => T' ===>(lib) mkc_Nat)
    -> type_equality_respecting_trans (per_nat_bar (close ts)) lib T T'
    -> type_equality_respecting_trans (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply CL_nat.
  eapply trans; eauto.
  repndors; subst.

  - eapply ccequivc_ext_preserves_all_in_bar in ceq;[|eauto];[].
    dclose_lr; auto.

  - eapply ccequivc_ext_preserves_all_in_bar in ceq;[|eauto];[].
    dclose_lr; auto.
Qed.

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
