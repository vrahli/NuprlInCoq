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


Definition per_eq_bar_or {o} ts lib (T T' : @CTerm o) eq :=
  per_eq_bar ts lib T T' eq
  {+} per_bar ts lib T T' eq.

Lemma dest_close_per_equality_l {p} :
  forall (ts : cts(p)) lib T a b A T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_equality a b A)
    -> close ts lib T T' eq
    -> per_eq_bar_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_eq_bar_or.
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
