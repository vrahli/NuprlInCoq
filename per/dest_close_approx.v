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


Lemma local_equality_of_approx_bar {o} :
  forall {lib} (bar : @BarLib o lib) a b t1 t2,
    all_in_bar_ext bar (fun lib' (x : lib_extends lib' lib) => per_approx_eq_bar lib' a b t1 t2)
    -> per_approx_eq_bar lib a b t1 t2.
Proof.
  introv alla.
  apply all_in_bar_ext_exists_bar_implies in alla; exrepnd.
  exists (bar_of_bar_fam fbar).
  introv br ext; simpl in *; exrepnd.
  eapply alla0; eauto.
Qed.

Lemma per_approx_bar_eq {o} :
  forall ts lib (T1 T2 : @CTerm o) eq,
    per_approx_bar ts lib T1 T2 eq
    <=>
    {bar : BarLib lib
    , {a, b, c, d : CTerm
    , T1 ==b==>(bar) (mkc_approx a b)
    # T2 ==b==>(bar) (mkc_approx c d)
    # all_in_bar bar (fun lib => (a ~<~(lib) b <=> c ~<~(lib) d))
    # eq <=2=> (per_approx_eq_bar lib a b) }}.
Proof.
  introv; unfold per_approx_bar; split; intro h; exrepnd.
  { eexists; eexists; eexists; eexists; eexists; dands; eauto. }
  { eexists; eexists; eexists; eexists; dands; eauto. }
Qed.

Lemma all_in_bar_ext_per_approx_bar_eq {o} :
  forall ts lib (bar : @BarLib o lib) (T1 T2 : @CTerm o) eqa,
    all_in_bar_ext bar (fun lib' x => per_approx_bar ts lib' T1 T2 (eqa lib' x))
    <=>
    (all_in_bar_ext
       bar
       (fun lib' x =>
          {bar : BarLib lib'
          , {a, b, c, d : CTerm
          , T1 ==b==>(bar) (mkc_approx a b)
          # T2 ==b==>(bar) (mkc_approx c d)
          # all_in_bar bar (fun lib => (a ~<~(lib) b <=> c ~<~(lib) d))
          # (eqa lib' x) <=2=> (per_approx_eq_bar lib' a b) }})).
Proof.
  introv; split; introv h br ext; introv.
  { pose proof (h lib' br lib'0 ext x) as h; simpl in h.
    apply per_approx_bar_eq in h; auto. }
  { apply per_approx_bar_eq; eapply h; eauto. }
Qed.

(*Lemma local_per_approx_bar {o} :
  forall {lib} (bar : @BarLib o lib) ts T T' eq eqa,
    (eq <=2=> (per_bar_eq bar eqa))
    -> all_in_bar_ext bar (fun lib' x => per_approx_bar ts lib' T T' (eqa lib' x))
    -> per_approx_bar ts lib T T' eq.
Proof.
  introv eqiff alla.
  allrw @per_approx_bar_eq.
  allrw @all_in_bar_ext_per_approx_bar_eq.
  apply all_in_bar_ext_exists_bar_implies in alla.
  exrepnd.

  exists (bar_of_bar_fam fbar).

  dands; introv br ext; simpl in *; exrepnd; eapply alla1; eauto.
  }

  eapply eq_term_equals_trans;[eauto|].
  introv.
  split; introv h.

  {
    eapply per_bar_eq_preserves_all_in_bar_ext_eq_term_equals in alla;[|eauto].
    eapply local_equality_of_approx_bar; eauto.
  }

  {
    introv br ext; introv.
    eapply alla; eauto.
    eapply sub_per_equality_of_approx_bar; eauto.
  }
Qed.*)

Definition per_approx_bar_or {o} ts lib (T T' : @CTerm o) eq :=
  per_approx_bar ts lib T T' eq
  {+} per_bar (per_approx_bar ts) lib T T' eq.

Lemma per_approx_bar_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_approx_bar ts lib T T' eq
    -> per_bar (per_approx_bar ts) lib T T' eq.
Proof.
  introv per.
  unfold per_approx_bar in *; exrepnd.
  exists (trivial_bar lib) (fun lib' (x : lib_extends lib' lib) => per_approx_eq_bar lib' a b).
  dands; auto.
  - introv br ext x; simpl in *.
    exists a b c d; dands; tcsp.
    exists (raise_bar bar x); dands; eauto 3 with slow.
  - eapply eq_term_equals_trans;[eauto|].
    introv; split; introv h.
    + introv br ext x; simpl in *.
      eapply sub_per_approx_eq_bar; eauto 3 with slow.
    + pose proof (h lib (lib_extends_refl lib) lib (lib_extends_refl lib) (lib_extends_refl lib)) as h; simpl in *; auto.
Qed.
Hint Resolve per_approx_bar_implies_per_bar : slow.

Lemma dest_close_per_approx_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_bar (per_approx_bar (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_approx_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.

  eapply local_per_bar; eauto; eauto 3 with slow.
  introv br ext; introv; eapply reca; eauto 3 with slow.
Qed.

Lemma dest_close_per_approx_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_bar (per_approx_bar (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_approx_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar; eauto; eauto 3 with slow.
  introv br ext; introv; eapply reca; eauto 3 with slow.
Qed.

Lemma dest_close_per_approx_l_ceq {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc_ceq_bar bar T (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_bar (per_approx_bar (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_approx_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar; eauto; eauto 3 with slow.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.

Lemma dest_close_per_approx_r_ceq {p} :
  forall (ts : cts(p)) lib (bar : BarLib lib) T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc_ceq_bar bar T' (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_bar (per_approx_bar (close ts)) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_approx_bar_or.
  close_cases (induction cl using @close_ind') Case; subst; try close_diff_all; auto; eauto 3 with slow.
  eapply local_per_bar; eauto; eauto 3 with slow.
  introv br ext; introv; apply (reca lib' br lib'0 ext x (raise_bar bar x)); eauto 3 with slow.
Qed.
