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


Definition sonobnd {o} (t : @SOTerm o) : SOBTerm :=
  sobterm [] t.

Definition mk_so_equality {o} (t1 t2 T : @SOTerm o) : SOTerm :=
  soterm (Can NEquality) [sonobnd t1, sonobnd t2, sonobnd T].

Definition mk_so_apply {o} (t1 t2 : @SOTerm o) : SOTerm :=
  soterm (NCan NApply) [sonobnd t1, sonobnd t2].

Definition mk_so_isect {o} (t1 : @SOTerm o) v t2 : SOTerm :=
  soterm (Can NIsect) [sonobnd t1, sobterm [v] t2].

Definition mk_so_function {o} (t1 : @SOTerm o) v t2 : SOTerm :=
  soterm (Can NFunction) [sonobnd t1, sobterm [v] t2].

Definition mk_so_uni {o} (i : nat) : @SOTerm o :=
  soterm (Can (NUni i)) [].

Definition mk_so_abs {o} abs (l : list (@SOBTerm o)) : SOTerm :=
  soterm (Abs abs) l.

Definition mk_so_integer {o} n : @SOTerm o :=
  soterm (Can (Nint n)) [].

Definition mk_so_nat {o} (n : nat) : @SOTerm o :=
  mk_so_integer (Z_of_nat n).

Definition mk_so_int {o} : @SOTerm o :=
  soterm (Can NInt) [].

Definition mk_so_lam {o} (v : NVar) (b : @SOTerm o) : SOTerm :=
  soterm (Can NLambda) [sobterm [v] b].
