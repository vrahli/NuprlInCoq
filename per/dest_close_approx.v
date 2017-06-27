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


Lemma dest_close_per_approx_l {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_approx_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.

Lemma dest_close_per_approx_r {p} :
  forall (ts : cts(p)) lib T A B T' eq,
    type_system ts
    -> defines_only_universes ts
    -> computes_to_valc lib T' (mkc_approx A B)
    -> close ts lib T T' eq
    -> per_approx_bar (close ts) lib T T' eq.
Proof.
  introv tysys dou comp cl.
  inversion cl; subst; try close_diff_all; auto.
Qed.
