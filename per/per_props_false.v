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


Require Export per_props_cequiv.



Lemma tequality_false {p} :
  forall lib, @tequality p lib mkcn_false mkcn_false.
Proof.
  introv.
  rw @mkcn_false_eq.
  rw @tequality_mkcn_approx; split; intro k; spcast;
  apply not_axiom_approxc_bot in k; sp.
Qed.
Hint Immediate tequality_false.

Lemma equality_in_false {p} :
  forall lib (t1 t2 : @cterm p), equality lib t1 t2 mkcn_false <=> False.
Proof.
  introv; split; intro e; sp.
  rw @mkcn_false_eq in e.
  rw <- @equality_in_approx in e; repnd; spcast.
  allapply @not_axiom_approxc_bot; sp.
Qed.

Lemma equality_in_void {p} :
  forall lib (t1 t2 : @cterm p), equality lib t1 t2 mkcn_void <=> False.
Proof.
  introv.
  rw @mkcn_void_eq_mkcn_false; sp.
  apply equality_in_false.
Qed.
