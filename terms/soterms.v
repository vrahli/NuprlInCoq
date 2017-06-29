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


Require Export sovar.


Definition sonobnd {o} (t : @SOTerm o) : SOBTerm := sobterm [] t.

Definition mk_so_equality {o} (t1 t2 T : @SOTerm o) :=
  soterm (Can NEquality) [sonobnd t1, sonobnd t2, sonobnd T].

Definition mk_so_apply {o} (t1 t2 : @SOTerm o) :=
  soterm (NCan NApply) [sonobnd t1, sonobnd t2].

Definition mk_so_isect {o} (t1 : @SOTerm o) v t2 :=
  soterm (Can NIsect) [sonobnd t1, sobterm [v] t2].

Definition mk_so_uni {o} (i : nat) :=
  @soterm o (Can (NUni i)) [].
