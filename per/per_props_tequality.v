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


Require Export nuprl_props.
Require Export univ_tacs.
Require Import rel_nterm.


Lemma tequality_iff_mkc_tequality {o} :
  forall lib (A B : @CTerm o),
    type lib (mkc_tequality A B) <=> tequality lib A B.
Proof.
  introv.
  split; intro k.

  - unfold type, tequality in k; exrepnd.
    inversion k0; subst; try not_univ.
    allunfold_per; computes_to_value_isvalue; allfold (@nuprl o).
    exists eqa; auto.

  - unfold tequality in k; exrepnd.
    exists (@true_per o).
    apply CL_teq; unfold per_teq.
    fold (@nuprl o).
    exists A B A B eq; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_tequality))).
    apply nuprl_refl in k0; auto.
    apply nuprl_sym in k0; apply nuprl_refl in k0; auto.
Qed.

Lemma tequality_mkc_tequality {o} :
  forall lib (A B C D : @CTerm o),
    tequality lib (mkc_tequality A B) (mkc_tequality C D)
    <=> (tequality lib A C # tequality lib B D # tequality lib A B).
Proof.
  introv.
  split; intro k.

  - unfold tequality in k; exrepnd.
    inversion k0; subst; try not_univ.
    allunfold_per; computes_to_value_isvalue; allfold (@nuprl o).
    dands; exists eqa; auto.

  - unfold tequality in k; exrepnd.
    exists (@true_per o).
    apply CL_teq; unfold per_teq.
    fold (@nuprl o).

    assert (eq1 <=2=> eq)
      as eqs1
        by (apply nuprl_refl in k1; apply nuprl_refl in k2;
            generalize (nuprl_uniquely_valued lib A eq1 eq); intro k;
            repeat (autodimp k hyp)).

    assert (eq0 <=2=> eq)
      as eqs2
        by (apply nuprl_sym in k2; apply nuprl_refl in k3; apply nuprl_refl in k2;
            generalize (nuprl_uniquely_valued lib B eq0 eq); intro k;
            repeat (autodimp k hyp)).

    exists A B C D eq; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_tequality))).
    apply @nuprl_ext with (eq1 := eq1); auto.
    apply @nuprl_ext with (eq1 := eq0); auto.
Qed.

Lemma mkc_tequality_equality_in_uni {o} :
  forall lib (A B C D : @CTerm o) i,
    tequalityi lib i (mkc_tequality A B) (mkc_tequality C D)
    <=> (tequalityi lib i A C # tequalityi lib i B D # tequalityi lib i A B).
Proof.
  introv.
  split; intro k.

  - unfold tequalityi, equality in k; exrepnd.
    inversion k1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    inversion h2; subst; try not_univ.
    allunfold_per; computes_to_value_isvalue; allfold (@nuprl o).
    dands; exists eq; sp; allrw; exists eqa0; auto.

  - unfold tequalityi, equality in k; exrepnd.
    generalize (nuprl_uniquely_valued lib (mkc_uni i) eq0 eq k1 k3); intro eqs1.
    generalize (nuprl_uniquely_valued lib (mkc_uni i) eq1 eq k0 k3); intro eqs2.
    clear k0 k1.
    rw eqs1 in k4; clear eqs1.
    rw eqs2 in k5; clear eqs2.
    exists eq; dands; auto.
    inversion k3; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepnd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    fold (@nuprli o lib j0) in h2, h3, h4.
    rw h0; exists (@true_per o).
    dup h2 as na1; apply nuprli_refl in na1.
    dup h4 as na2; apply nuprli_refl in na2.
    generalize (nuprli_uniquely_valued lib j0 j0 A A eqa1 eqa na1 na2); clear na1 na2; intro eqs1.
    dup h3 as nb1; apply nuprli_refl in nb1.
    dup h4 as nb2; apply nuprli_sym in nb2; apply nuprli_refl in nb2.
    generalize (nuprli_uniquely_valued lib j0 j0 B B eqa0 eqa nb1 nb2); clear nb1 nb2; intro eqs2.
    apply CL_teq; fold (@nuprli o lib j0).
    exists A B C D eqa; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_tequality))).
    apply nuprli_ext with (eq1 := eqa1); auto.
    apply nuprli_ext with (eq1 := eqa0); auto.
Qed.

Lemma equality_in_mkc_tequality {o} :
  forall lib (a b A B : @CTerm o),
    equality lib a b (mkc_tequality A B) <=> tequality lib A B.
Proof.
  introv; split; intro k.

  - apply inhabited_implies_tequality in k.
    rw @tequality_iff_mkc_tequality in k; auto.

  - exists (@true_per o); dands; auto; try (complete (unfold true_per; auto)).
    unfold tequality in k; exrepnd.
    apply CL_teq.
    exists A B A B eq; fold (@nuprl o); sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_tequality))).
    apply nuprl_refl in k0; auto.
    apply nuprl_sym in k0; apply nuprl_refl in k0; auto.
Qed.
