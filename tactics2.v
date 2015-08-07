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


Require Export UsefulTypes.


Ltac prove_and h :=
  match goal with
    | [ |- ?x # ?y ] =>
        assert x as h;
        [ try (complete auto)
        | constructor; try (complete auto)
        ]
  end.

Ltac clear_dependencies h :=
  repeat match goal with
             [ H : context[h] |- _ ] => clear H
         end.

Ltac spFalseHyp :=
  repeat
    (match goal with
       | [ H : ?x <> ?x |- _ ] => provefalse; apply H; auto
       | [ H : !(?x = ?x) |- _ ] => provefalse; apply H; auto
       | [ H : context[?x = ?x] |- _ ] => trw_h true_eq_same H
       | [ H : context[?t [+] False] |- _ ] => trw_h or_false_r H
       | [ H : context[False [+] ?t] |- _ ] => trw_h or_false_l H
       | [ H : context[?t [+] True] |- _ ] => trw_h or_true_r H
       | [ H : context[True [+] ?t] |- _ ] => trw_h or_true_l H
       | [ H : context[!False] |- _ ] => trw_h not_false_is_true H
     end; try subst).

Ltac ginv_step :=
  match goal with
    | [H : _ = _ |- _ ] =>
      first [ complete (inversion H)
            | destruct H; complete auto
            | inversion H; simpl in H; subst;
              match type of H with
                | ?x = ?x => clear H
              end
            ]
  end.

Ltac ginv := repeat ginv_step.

Ltac repndors :=
  repeat match goal with
           | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
           | [ H : sum _ _ |- _ ] => destruct H as [H|H]
         end.
