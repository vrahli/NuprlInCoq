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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export list.


Definition hidden_disjoint {T} a b := @disjoint T a b.

Ltac disj_flat_map_step :=
  match goal with
    | [ H1 : disjoint ?a (flat_map ?f ?l), H2 : LIn ?x ?l |- _ ] =>
      let k := fresh H1 in
      let h := fresh H2 in
      assert (disjoint a (flat_map f l)) as k by trivial;
        trw_h disjoint_flat_map_r k;
        assert (LIn x l) as h by trivial;
        apply k in h;
        clear k;
         fold (hidden_disjoint a (flat_map f l)) in H1
    | [ H1 : disjoint (flat_map ?f ?l) ?a, H2 : LIn ?x ?l |- _ ] =>
      let k := fresh H1 in
      let h := fresh H2 in
      assert (disjoint (flat_map f l) a) as k by trivial;
        trw_h disjoint_flat_map_l k;
        assert (LIn x l) as h by trivial;
        apply k in h;
        clear k;
         fold (hidden_disjoint (flat_map f l) a) in H1
   end.

Ltac disj_flat_map := (repeat disj_flat_map_step); allunfold (@hidden_disjoint).
