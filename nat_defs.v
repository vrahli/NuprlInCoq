(*

  Copyright 2014 Cornell University

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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export terms4.
Require Export terms_union.

Definition int2int {o} := @mk_fun o mk_int mk_int.
Definition int2int_c {o} := @mkc_fun o mkc_int mkc_int.

Definition with_nexc_c {o} a (T E : @CTerm o) := mkc_bunion T (mkc_ntexc a E).
Definition natE {o} (a : @get_patom_set o) := with_nexc_c a mkc_tnat mkc_unit.

Definition nat2nat {o} := @mkc_fun o mkc_tnat mkc_tnat.
Definition nat2natE {o} (a : @get_patom_set o) := mkc_fun mkc_tnat (natE a).
Definition natk2nat {o} (t : @CTerm o) := mkc_fun (mkc_natk t) mkc_tnat.
