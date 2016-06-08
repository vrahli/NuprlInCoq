 (*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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

Require Export subst_tacs.

Tactic Notation "lsubstc_snoc_move2" ident(h) :=
  match type of h with
    | context[lsubstc ?t ?w (snoc ?s1 (?x,?a) ++ ?s2) ?c] =>
      let ni := fresh "ni" in
      let e  := fresh "e"  in
      let ch := fresh "c"  in
      assert (!LIn x (dom_csub s1)) as ni by auto;
        pose proof (lsubstc_snoc_move t s1 s2 x a w c ni) as e;
        destruct e as [ch e];
        rewrite e in h; clear e; clear_irr
  end.

Tactic Notation "lsubstc_snoc_move2" :=
  match goal with
    | [ |- context[lsubstc ?t ?w (snoc ?s1 (?x,?a) ++ ?s2) ?c] ] =>
      let ni := fresh "ni" in
      let e  := fresh "e"  in
      let ch := fresh "c"  in
      assert (!LIn x (dom_csub s1)) as ni by auto;
        pose proof (lsubstc_snoc_move t s1 s2 x a w c ni) as e;
        destruct e as [ch e];
        rewrite e; clear e; clear_irr
  end.
