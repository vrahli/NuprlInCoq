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


Require Export nuprl_mon.


Definition type_bar {o} (ts : cts(o)) :=
  forall lib (bar : @BarLib o lib) T1 T2 eqa,
    all_in_bar_ext bar (fun lib' x => ts lib' T1 T2 (eqa lib' x))
    ->
    exists eqa',
      ts lib T1 T2 eqa'
         # forall lib' (x : lib_extends lib' lib), sub_per eqa' (eqa lib' x).

Lemma nuprl_bar {o} : @type_bar o nuprl.
Proof.
  introv u.
  exists (eqa lib (lib_extends_refl lib)).

  (* Does this need something like bar induction?
     Coquand/Bassel seem to pick a particular path to prove that. *)
Qed.
Hint Resolve nuprl_bar : slow.
