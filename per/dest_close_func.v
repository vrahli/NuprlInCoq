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



Definition per_func_ext_or {o} ts lib (T T' : @CTerm o) eq :=
  per_func_ext ts lib T T' eq
  {+} per_bar ts lib T T' eq.

Lemma dest_close_per_func_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_function A v B)
    -> close ts lib T T' eq
    -> per_func_ext_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_func_ext_or.
  inversion cl; clear cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_function A v B)
    -> close ts lib T T' eq
    -> per_func_ext_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_func_ext_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_bar_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T ===>(lib) (mkc_function A v B))
    -> close ts lib T T' eq
    -> per_func_ext_or (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl; unfold per_func_ext_or.
  inversion cl; clear cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_bar_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq (bar : BarLib lib),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> all_in_bar bar (fun lib => T' ===>(lib) (mkc_function A v B))
    -> close ts lib T T' eq
    -> per_func_ext_or (close ts) lib T T' eq.
Proof.
  introv tysys dou mon comp cl; unfold per_func_ext_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_ext_l {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> in_ext lib (fun lib => T ===>(lib) (mkc_function A v B))
    -> close ts lib T T' eq
    -> per_func_ext_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_func_ext_or.
  inversion cl; clear cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_func_ext_r {p} :
  forall (ts : cts(p)) lib T A v B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> in_ext lib (fun lib => T' ===>(lib) (mkc_function A v B))
    -> close ts lib T T' eq
    -> per_func_ext_or (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl; unfold per_func_ext_or.
  inversion cl; subst; try close_diff_all; auto.
Qed.
