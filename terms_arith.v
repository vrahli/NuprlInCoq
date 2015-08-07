(*
  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)

Require Export terms2.
Require Export arith_props.


Definition mkc_mul {p} m n := @mkc_arithop p ArithOpMul m n.
Definition mkc_sub {p} m n := @mkc_arithop p ArithOpSub m n.
Definition mkc_div {p} m n := @mkc_arithop p ArithOpDiv m n.
Definition mkc_rem {p} m n := @mkc_arithop p ArithOpRem m n.

Lemma mkc_add_is_mkc_arithop {o} :
  forall a b,  @mkc_add o a b = mkc_arithop ArithOpAdd a b.
Proof. intros. destruct_cterms. apply cterm_eq. simpl. auto.
Qed.
