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

Require Export sequents.

Ltac sim_snoc :=
  match goal with
    | [ w : wf_term ?t
            , c : cover_vars ?t ?s1
        |- similarity _ _ (snoc ?s1 (?x,?t1)) (snoc ?s2 (?x,?t2)) (snoc _ (mk_hhyp ?x ?t))
      ] =>
      apply similarity_snoc; simpl;
      exists s1 s2 t1 t2 w c
    | [ w : wf_term ?t
            , c : cover_vars ?t ?s1
        |- similarity _ _ (snoc ?s1 (?x,?t1)) (snoc ?s2 (?x,?t2)) (snoc _ (mk_hyp ?x ?t))
      ] =>
      apply similarity_snoc; simpl;
      exists s1 s2 t1 t2 w c
  end.

Ltac sim_snoc2 :=
  match goal with
    | [ |- similarity _ _ (snoc ?s1 (?x,?t1)) (snoc ?s2 (?x,?t2)) (snoc _ (mk_hhyp ?x ?t)) ] =>
      let w := fresh "w" in
      let c := fresh "c" in
      assert (wf_term t) as w;
        [ auto
        | assert (cover_vars t s1) as c;
          [ auto
          | apply similarity_snoc; simpl;
            exists s1 s2 t1 t2 w c
          ]
        ]
    | [ |- similarity _ _ (snoc ?s1 (?x,?t1)) (snoc ?s2 (?x,?t2)) (snoc _ (mk_hyp ?x ?t)) ] =>
      let w := fresh "w" in
      let c := fresh "c" in
      assert (wf_term t) as w;
        [ auto
        | assert (cover_vars t s1) as c;
          [ auto
          | apply similarity_snoc; simpl;
            exists s1 s2 t1 t2 w c
          ]
        ]
  end.

Ltac generalize_lsubstc_terms nm :=
  match goal with
  | [ |- context[lsubstc ?x ?y ?z ?w] ] =>
    remember (lsubstc x y z w) as nm; clear_eq nm (lsubstc x y z w)
 end.
