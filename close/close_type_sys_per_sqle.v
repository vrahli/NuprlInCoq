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
Require Export dest_close.
Require Export per_ceq_bar.


Lemma per_approx_bar_uniquely_valued {p} :
  forall (ts : cts(p)), uniquely_valued (per_approx_bar ts).
Proof.
  unfold uniquely_valued, per_approx_bar, eq_term_equals; sp.
  pose proof (two_computes_to_valc_ceq_bar_mkc_approx bar0 bar T a0 b0 a b) as q; repeat (autodimp q hyp).
  allrw; sp.
  eapply eq_per_approx_eq_bar; eauto.
Qed.

Lemma per_approx_bar_type_extensionality {p} :
  forall (ts : cts(p)), type_extensionality (per_approx_bar ts).
Proof.
  unfold type_extensionality, per_approx_bar, eq_term_equals; sp.
  exists a b c d; sp; allrw <-; sp.
  exists bar; dands; tcsp.
Qed.

Lemma per_approx_bar_type_symmetric {p} :
  forall (ts : cts(p)), type_symmetric (per_approx_bar ts).
Proof.
  introv per.
  unfold per_approx_bar in *; exrepnd.
  exists c d a b; sp.
  { exists bar; dands; tcsp.
    introv i j; symm; eapply per2; eauto. }
  introv; rw per1; clear per1.

  split; intro h; unfold per_approx_eq_bar, per_approx_eq_bar1 in *; exrepnd.

  { exists (intersect_bars bar bar0).
    introv i j; simpl in *; exrepnd.
    pose proof (h0 lib2) as q; clear h0; autodimp q hyp.
    pose proof (q lib'0) as z; autodimp z hyp; eauto 2 with slow; simpl in z; repnd.
    dands; auto.
    pose proof (per2 lib1) as w; clear per2; autodimp w hyp.
    pose proof (w lib'0) as u; autodimp u hyp; eauto 2 with slow; simpl in u; repnd.
    apply u; auto. }

  { exists (intersect_bars bar bar0).
    introv i j; simpl in *; exrepnd.
    pose proof (h0 lib2) as q; clear h0; autodimp q hyp.
    pose proof (q lib'0) as z; autodimp z hyp; eauto 2 with slow; simpl in z; repnd.
    dands; auto.
    pose proof (per2 lib1) as w; clear per2; autodimp w hyp.
    pose proof (w lib'0) as u; autodimp u hyp; eauto 2 with slow; simpl in u; repnd.
    apply u; auto. }
Qed.

Lemma per_approx_bar_type_transitive {p} :
  forall (ts : cts(p)), type_transitive (per_approx_bar ts).
Proof.
  introv per1 per2.
  unfold per_approx_bar in *; exrepnd.

  exists a0 b0 c d; sp; spcast; sp.
  exists (intersect_bars bar0 bar).
  dands.

  - introv i j; simpl in *; exrepnd.
    pose proof (per5 lib1) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.

  - introv i j; simpl in *; exrepnd.
    pose proof (per4 lib2) as q; autodimp q hyp.
    pose proof (q lib'0) as w; simpl in w; autodimp w hyp; eauto 2 with slow.

  - introv i j; simpl in *; exrepnd.
    pose proof (per6 lib1) as q; autodimp q hyp.
    pose proof (per3 lib2) as w; autodimp w hyp.
    pose proof (q lib'0) as z; autodimp z hyp; eauto 2 with slow; clear q.
    pose proof (w lib'0) as u; autodimp u hyp; eauto 2 with slow; clear w.
    simpl in *.
    rw z.
    rw <- u.

    pose proof (two_computes_to_valc_ceq_bar_mkc_approx bar0 bar T2 c0 d0 a b) as h; repeat (autodimp h hyp).
    pose proof (h lib') as w; simpl in w; autodimp w hyp; clear h;
      [exists lib1 lib2; dands; auto|].
    pose proof (w lib'0 j) as w; simpl in w; repnd; spcast.

    split; introv h; spcast.

    { eapply approxc_cequivc_trans;[|eauto].
      eapply cequivc_approxc_trans;[apply cequivc_sym;eauto|].
      auto. }

    { eapply approxc_cequivc_trans;[|apply cequivc_sym;eauto].
      eapply cequivc_approxc_trans;[eauto|].
      auto. }
Qed.

(*Lemma cequivc_exc_all_in_bar {o} :
  forall {lib} (bar : @BarLib o lib) T U T',
    all_in_bar bar (fun lib => T ===>(lib) U)
    -> ccequivc_ext lib T T'
    -> exists U',
        all_in_bar bar (fun lib => T' ===>(lib) U' /\ ccequivc lib U U').
Proof.
  introv ib eceq.

  pose proof (bar_non_empty bar) as h.
  destruct h as [lib' h].
  pose proof (ib lib') as q; autodimp q hyp.
  pose proof (q lib') as w; autodimp w hyp; eauto 2 with slow; simpl in w.
  pose proof (eceq lib') as z; autodimp z hyp; eauto 2 with slow; simpl in z.
  spcast.
  eapply cequivc_preserves_computes_to_valc in z;[|eauto].
  exrepnd.
  exists U'.

  introv i j.

  SearchAbout computes_to_valc cequivc.
  Locate cequivc_mkc_requality.
  exists U
Qed.*)

Lemma per_approx_bar_type_value_respecting {p} :
  forall (ts : cts(p)), type_value_respecting (per_approx_bar ts).
Proof.
  introv per eceq.
  unfold per_approx_bar in *; exrepnd.

  pose proof (two_computes_to_valc_ceq_bar_mkc_approx_same_bar bar T a b c d) as q.
  repeat (autodimp q hyp).

  exists a b a b.
  dands; auto.

  exists bar; dands; auto;[|introv w z; tcsp];[].

  eapply cequivc_ext_preserves_computes_to_valc_ceq_bar; eauto.
Qed.

Lemma per_approx_bar_term_symmetric {p} :
  forall (ts : cts(p)), term_symmetric (per_approx_bar ts).
Proof.
  unfold term_symmetric, term_equality_symmetric, per_approx_bar.
  introv cts i e.
  exrepnd.

  apply i1 in e; apply i1; clear i1.
  unfold per_approx_eq_bar, per_approx_eq_bar1 in *; exrepnd.
  exists bar0.
  introv w z.
  pose proof (e0 lib' w lib'0 z) as q; simpl in q; tcsp.
Qed.

Lemma per_approx_bar_term_transitive {p} :
  forall (ts : cts(p)), term_transitive (per_approx_bar ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_approx_bar.
  introv cts i e1 e2.
  exrepnd.

  apply i1 in e1; apply i1 in e2; apply i1; clear i1.
  unfold per_approx_eq_bar, per_approx_eq_bar1 in *; exrepnd.
  exists (intersect_bars bar1 bar0).
  introv w z.
  simpl in *; exrepnd.
  pose proof (e2 lib1 w0 lib'0) as q; autodimp q hyp; eauto 3 with slow; simpl in q; tcsp.
  pose proof (e0 lib2 w2 lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h; tcsp.
Qed.

Lemma per_approx_bar_term_value_respecting {p} :
  forall (ts : cts(p)), term_value_respecting (per_approx_bar ts).
Proof.
  sp; unfold term_value_respecting, term_equality_respecting, per_approx_bar.
  introv i e c; exrepnd.

  apply i1 in e; apply i1; clear i1.
  unfold per_approx_eq_bar, per_approx_eq_bar1 in *; exrepnd.
  exists bar0; introv w z.
  pose proof (e0 lib' w lib'0 z) as q; clear e0; simpl in q.
  repnd; dands; auto.

  pose proof (c lib'0) as h; autodimp h hyp; eauto 3 with slow; simpl in h.
  spcast.
  eapply cequivc_axiom; eauto.
Qed.

Lemma per_approx_bar_type_system {p} :
  forall (ts : cts(p)), type_system (per_approx_bar ts).
Proof.
  intros; unfold type_system; sp.
  - apply per_approx_bar_uniquely_valued; auto.
  - apply per_approx_bar_type_extensionality; auto.
  - apply per_approx_bar_type_symmetric; auto.
  - apply per_approx_bar_type_transitive; auto.
  - apply per_approx_bar_type_value_respecting; auto.
  - apply per_approx_bar_term_symmetric; auto.
  - apply per_approx_bar_term_transitive; auto.
  - apply per_approx_bar_term_value_respecting; auto.
Qed.

Lemma type_equality_respecting_trans_per_approx_bar_implies {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) T T' a b a' b',
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> T ==b==>(bar) (mkc_approx a b)
    -> T' ==b==>(bar) (mkc_approx a' b')
    -> type_equality_respecting_trans (per_approx_bar (close ts)) lib T T'
    -> type_equality_respecting_trans (close ts) lib T T'.
Proof.
  introv tsts dou mon inbar1 inbar2 trans h ceq cl.
  apply CL_approx.
  eapply trans; eauto.
  repndors; subst.

  - eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto];[].
    dclose_lr; auto.

  - eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto];[].
    dclose_lr; auto.

  - eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto];[].
    dclose_lr; auto.

  - eapply cequivc_ext_preserves_computes_to_valc_ceq_bar in ceq;[|eauto];[].
    dclose_lr; auto.
Qed.


Lemma close_type_system_approx {p} :
  forall lib (ts : cts(p)),
  forall T T' eq,
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> per_approx_bar (close ts) lib T T' eq
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tsts dou mon per.

  dup per as ps; unfold per_approx_bar in ps; exrepnd; spcast.

  prove_type_sys_props4 SCase; intros.

  + SCase "uniquely_valued".
    dclose_lr.

    * SSCase "CL_approx".
      assert (uniquely_valued (per_approx_bar (close ts)))
        as uv
          by (apply per_approx_bar_uniquely_valued).
      apply (uv lib T T'); auto.
      apply uniquely_valued_trans5 with (T2 := T3) (eq2 := eq); auto.
      { apply per_approx_bar_type_extensionality. }
      { apply per_approx_bar_type_symmetric. }
      { apply per_approx_bar_type_transitive. }

  + SCase "type_symmetric"; repdors; subst; dclose_lr;
    apply CL_approx; auto;
    assert (type_symmetric (per_approx_bar (close ts)))
      as tys
        by (apply per_approx_bar_type_symmetric);
    assert (type_extensionality (per_approx_bar (close ts)))
      as tye
        by (apply per_approx_bar_type_extensionality);
    apply tye with (eq := eq); auto.

  + SCase "type_value_respecting"; repdors; subst;
    apply CL_approx;
    assert (type_value_respecting (per_approx_bar (close ts)))
           as tvr
           by (apply per_approx_bar_type_value_respecting).

    { apply tvr; auto.
      apply @type_system_type_mem with (T' := T'); auto.
      apply per_approx_bar_type_symmetric.
      apply per_approx_bar_type_transitive. }

    { apply tvr; auto.
      apply @type_system_type_mem1 with (T := T); auto.
      apply per_approx_bar_type_symmetric.
      apply per_approx_bar_type_transitive. }

  + SCase "type_value_respecting_trans".
    eapply type_equality_respecting_trans_per_approx_bar_implies; eauto.
    apply type_system_implies_type_equality_respecting_trans.
    apply per_approx_bar_type_system.

  + SCase "term_symmetric".
    assert (term_symmetric (per_approx_bar (close ts)))
      as tes
        by (apply per_approx_bar_term_symmetric).
    apply (tes lib T T'); auto.

  + SCase "term_transitive".
    assert (term_transitive (per_approx_bar (close ts)))
      as tet
        by (apply per_approx_bar_term_transitive).
    apply (tet lib T T'); auto.

  + SCase "term_value_respecting".
    assert (term_value_respecting (per_approx_bar (close ts)))
      as tvr
        by (apply per_approx_bar_term_value_respecting).
    apply tvr with (T := T); auto.
    apply @type_system_type_mem with (T' := T'); auto.
    { apply per_approx_bar_type_symmetric. }
    { apply per_approx_bar_type_transitive. }

  + SCase "type_gsymmetric"; repdors; subst; split; sp; dclose_lr.

    { apply CL_approx; apply per_approx_bar_type_symmetric; auto. }

    { apply CL_approx; apply per_approx_bar_type_symmetric; auto. }

  + SCase "type_gtransitive"; sp.

  + SCase "type_mtransitive".
    repdors; subst; dclose_lr.

    dands; apply CL_approx; try (complete sp).

    { apply per_approx_bar_type_transitive with (T2 := T); auto.
      allunfold @per_approx_bar; sp.
      exists a1 b1 c1 d1; dands; auto;[exists bar1; dands; auto|];[].
      eapply eq_term_equals_trans;[eauto|].
      pose proof (two_computes_to_valc_ceq_bar_mkc_approx bar1 bar0 T a1 b1 c0 d0) as q; repeat (autodimp q hyp).
      apply eq_per_approx_eq_bar in q.
      apply eq_term_equals_sym in q.
      eapply eq_term_equals_trans;[|exact q]; clear q.
      eapply approx_iff_implies_eq_per_approx_eq_bar; eauto. }

    { apply per_approx_bar_type_transitive with (T2 := T); auto.
      allunfold @per_approx_bar; sp.
      exists a0 b0 c0 d0; dands; auto;[exists bar0; dands; auto|];[].
      eapply eq_term_equals_trans;[eauto|].
      pose proof (two_computes_to_valc_ceq_bar_mkc_approx bar1 bar0 T a1 b1 c0 d0) as q; repeat (autodimp q hyp).
      apply eq_per_approx_eq_bar in q.
      eapply eq_term_equals_trans;[exact q|]; clear q.
      apply eq_term_equals_sym.
      eapply approx_iff_implies_eq_per_approx_eq_bar; eauto. }

    dands; apply CL_approx.

    { apply per_approx_bar_type_transitive with (T2 := T'); auto.
      allunfold @per_approx_bar; sp.
      exists a1 b1 c1 d1; dands; auto;[exists bar1; dands; auto|];[].
      eapply eq_term_equals_trans;[eauto|].
      pose proof (two_computes_to_valc_ceq_bar_mkc_approx bar1 bar0 T' a1 b1 c0 d0) as q; repeat (autodimp q hyp).
      apply eq_per_approx_eq_bar in q.
      apply eq_term_equals_sym in q.
      eapply eq_term_equals_trans;[|exact q]; clear q.
      eapply approx_iff_implies_eq_per_approx_eq_bar; eauto. }

    { apply per_approx_bar_type_transitive with (T2 := T'); auto.
      allunfold @per_approx_bar; sp.
      exists a0 b0 c0 d0; dands; auto;[exists bar0; dands; auto|];[].
      eapply eq_term_equals_trans;[eauto|].
      pose proof (two_computes_to_valc_ceq_bar_mkc_approx bar1 bar0 T' a1 b1 c0 d0) as q; repeat (autodimp q hyp).
      apply eq_per_approx_eq_bar in q.
      eapply eq_term_equals_trans;[exact q|]; clear q.
      apply eq_term_equals_sym.
      eapply approx_iff_implies_eq_per_approx_eq_bar; eauto. }
Qed.
