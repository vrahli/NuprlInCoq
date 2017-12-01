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


Require Export dest_close_tacs.
Require Export bar_fam.
Require Export per_ceq_bar.


Lemma local_equality_of_eq_bar {o} :
  forall {lib} (bar : @BarLib o lib) a b (eqa : lib-per(lib,o)) t1 t2,
    all_in_bar_ext bar (fun lib' (x : lib_extends lib' lib) => per_eq_eq lib' a b (raise_lib_per eqa x) t1 t2)
    -> per_eq_eq lib a b eqa t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; introv; simpl in *; exrepnd.
  pose proof (alla0 _ br _ ext0 x0) as alla0.
  unfold per_eq_eq1, raise_lib_per in alla0.
  pose proof (alla0 _ br0 _ ext (lib_extends_trans ext (bar_lib_ext _ _ br0))) as alla0; simpl in *.
  repnd; dands; auto.
  eapply (lib_per_cond lib eqa);eauto 4 with slow.
Qed.

Definition per_eq_bar_or {o} ts lib (T T' : @CTerm o) eq :=
  per_eq_bar ts lib T T' eq
  {+} per_bar ts lib T T' eq.

Definition per_eq_eq_lib_per
           {o}
           {lib : @library o}
           (eqa : lib-per(lib,o)) (a1 a2 : @CTerm o) : lib-per(lib,o).
Proof.
  exists (fun lib' (x : lib_extends lib' lib) =>
            per_eq_eq lib' a1 a2 (raise_lib_per eqa x)).

  repeat introv.
  unfold per_eq_eq, per_eq_eq1, raise_lib_per, raise_ext_per; simpl.
  split; intro h; exrepnd.

  - exists bar; introv br ext; introv.
    pose proof (h0 _ br _ ext x) as h0; simpl in *; repnd.
    dands; auto.
    eapply (lib_per_cond _ eqa); eauto.

  - exists bar; introv br ext; introv.
    pose proof (h0 _ br _ ext x) as h0; simpl in *; repnd.
    dands; auto.
    eapply (lib_per_cond _ eqa); eauto.
Defined.

Lemma per_eq_bar_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_eq_bar ts lib T T' eq
    -> per_bar (per_eq_bar ts) lib T T' eq.
Proof.
  introv per.

  unfold per_eq_bar in *; exrepnd.

  assert (all_in_bar_ext bar (fun lib' x => forall y, (eqa lib' x) <=2=> (eqa lib' y))) as w.
  {
    introv br ext; introv.
    pose proof (per4 _ br _ ext x) as q; simpl in q.
    pose proof (per4 _ br _ ext y) as h; simpl in h.
    eapply (lib_per_cond lib eqa); eauto.
  }

  exists (trivial_bar lib) (per_eq_eq_lib_per eqa a1 a2).
  dands; auto.

  - introv br ext; introv; simpl in *.
    exists A B a1 a2 b1 b2.
    exists (raise_lib_per eqa x); dands; auto.
    exists (raise_bar bar x); dands; auto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per0.
    introv; split; intro h.

    + introv br ext; introv.
      simpl in *.
      eapply sub_per_per_eq_eq; eauto.

    + pose proof (h lib (lib_extends_refl lib) lib (lib_extends_refl lib) (lib_extends_refl lib)) as h; simpl in *; auto.
      unfold per_eq_eq, per_eq_eq1, raise_lib_per in *; simpl in *; exrepnd.
      apply (implies_all_in_bar_ext_intersect_bars_left _ bar) in h0.
      apply (implies_all_in_bar_ext_intersect_bars_right _ bar0) in w.
      exists (intersect_bars bar0 bar); dands.
      introv br ext; introv.
      pose proof (h0 _ br _ ext x) as h0; simpl in h0.
      repnd; dands; auto.
      eapply w; eauto.
Qed.
Hint Resolve per_eq_bar_implies_per_bar : slow.

Lemma dest_close_per_equality_l {p} :
  forall (ts : cts(p)) lib T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; try unfold per_eq_bar_or.
(*
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

Lemma local_per_bar_per_eq_bar {o} :
  forall (ts : cts(o)) lib (bar : BarLib lib) T T' a b A B (eqa : lib-per(lib,o)) eq,
    all_in_bar_ext bar (fun lib' x => type_sys_props4 (close ts) lib' A B (eqa lib' x))
    -> T ==b==>(bar) (mkc_equality a b A)
    -> (eq <=2=> (per_bar_eq bar eqa))
    -> all_in_bar_ext bar (fun lib' x => per_bar (per_eq_bar ts) lib' T T' (eqa lib' x))
    -> per_bar (per_eq_bar ts) lib T T' eq.
Proof.
  introv tsp comp eqiff alla.
  unfold per_bar in *.

  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  apply all_in_bar_ext2_exists_eqa_implies in alla0; exrepnd.

  exists (lib_per_per_bar fbar feqa).
  dands.

  {
    introv br ext; introv.
    simpl in *; exrepnd.

    pose proof (alla1 lib1 br lib2 ext0 x0) as alla0.
    exrepnd.
    remember (fbar lib1 br lib2 ext0 x0) as bb.
    pose proof (alla2
                  lib' br0 lib'0 ext
                  (lib_extends_trans ext (bar_lib_ext bb lib' br0)))
      as alla2; simpl in *.
    unfold per_eq_bar in *; exrepnd.
    exists A0 B0 a1 a2 b1 b2 eqa0; dands; auto.
    { exists bar0; dands; auto. }
    apply eq_term_equals_sym; introv; split; introv w.

    { subst.
      apply alla3 in w.
      eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists.
      eauto. }

    exrepnd.

    pose proof (alla1 lib0 br1 lib3 ext1 x1) as z; repnd.
    pose proof (z0 lib4 fb lib'0 w (lib_extends_trans w (bar_lib_ext (fbar lib0 br1 lib3 ext1 x1) lib4 fb))) as z0; simpl in *.
    exrepnd.
    apply z1 in w1.

    pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar0 bar1 T a1 a2 a0 a3 A0 A1) as h1; repeat (autodimp h1 hyp).
    pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar0 bar1 T a1 a2 a0 a3 A0 A1) as h2; repeat (autodimp h2 hyp).
    pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar0 bar1 T a1 a2 a0 a3 A0 A1) as h3; repeat (autodimp h3 hyp).

    pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a b a1 a2 A A0) as h4; repeat (autodimp h4 hyp).
    pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a b a1 a2 A A0) as h5; repeat (autodimp h5 hyp).
    pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a b a1 a2 A A0) as h6; repeat (autodimp h6 hyp).

    eapply implies_iff_per_eq_eq; try exact w1.

    SearchAbout computes_to_valc_ceq_bar mkc_equality.
    SearchAbout per_eq_eq.

    Print per_eq_eq1.

    eapply uv in z0; autodimp z0 hyp;[exact alla2|].
    apply z0; auto.
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    introv.
    unfold per_bar_eq; split; introv h br ext; introv.

    - introv.
      simpl in *; exrepnd.
      pose proof (alla1 lib1 br lib2 ext0 x0) as q; repnd.
      pose proof (h lib1 br lib2 ext0 x0) as h; simpl in *.
      apply q in h.

      clear q q0.

      exists lib1 br lib2 ext0 x0 lib' ext br0.
      eapply h; eauto.

    - pose proof (alla1 lib' br lib'0 ext x) as z; repnd.
      apply z.
      introv fb w; introv.

      pose proof (h lib'1) as h.
      simpl in h.

      autodimp h hyp.
      { exists lib' br lib'0 ext x; auto. }

      pose proof (h lib'2 w) as h; simpl in *.
      autodimp h hyp; eauto 3 with slow.
      exrepnd.

      pose proof (z0 lib'1 fb lib'2 w x0) as z0; simpl in *.

      pose proof (alla1 lib1 br0 lib2 ext0 x1) as q; repnd.
      pose proof (q0 lib0 fb0 lib'2 w0 (lib_extends_trans w0 (bar_lib_ext (fbar lib1 br0 lib2 ext0 x1) lib0 fb0))) as q0; simpl in *.
      eapply uv in q0; autodimp q0 hyp;[exact z0|].
      apply q0; auto.
  }
Qed.
Hint Resolve local_per_bar : slow.

  Print local_ts.
  SearchAbout local_ts.

  eapply local_per_bar_unf; eauto; eauto 3 with slow;
    try (complete (introv br ext; introv; eapply reca; eauto 3 with slow)).

  Lemma uniquely_valued_close_ts {o} :
    forall (ts : cts(o)) lib T T' eq,
      uniquely_valued_body (per_eq_bar ts) lib T T' eq.
  Proof.
    introv pera.
    unfold per_eq_bar in *; exrepnd.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
    eapply two_computes_to_valc_ceq_bar_mkc_equality in pera1; try exact perb1.



    Check implies_iff_per_eq_eq.
  Qed.

  Lemma uniquely_valued_close_ts {o} :
    forall (ts : cts(o)),
      type_system ts
      -> defines_only_universes ts
      -> uniquely_valued (close ts).
  Proof.
    introv tysys dou cl.
    close_cases (induction cl using @close_ind') Case; introv cl'.

    - Case "CL_init".
      close_cases (induction cl' using @close_ind') SCase; subst; try close_diff_all; auto; eauto 3 with slow.

      Focus 2.
      eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
      +
  Qed.

XXXXXXXX
  eapply local_per_bar; eauto; eauto 3 with slow.
  introv br ext; introv; eapply reca; eauto 3 with slow.
*)
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_r {p} :
  forall (ts : cts(p)) lib T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_eq_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_bar_l {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar bar (fun lib => T ===>(lib) (mkc_equality a b A))
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_eq_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_bar_r {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> all_in_bar bar (fun lib => T' ===>(lib) (mkc_equality a b A))
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_eq_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_ceq_bar_l {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> T ==b==>(bar) (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_eq_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_equality_ceq_bar_r {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> T' ==b==>(bar) (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_eq_bar_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.
