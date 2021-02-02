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


Notation "[U]" := Prop.

Notation "{ a : T , P }" := (exists (a : T), P) (at level 0, a at level 99).
Notation "T {+} U" := (T \/ U)%type (at level 80, right associativity).


Require Export cequiv.
Require Export cnterm2.


Definition ccomputes_to_valc {p} lib t1 t2 := Cast (@computes_to_valc p lib t1 t2).
Definition ccomputes_to_excc {p} lib a t e := Cast (@computes_to_excc p lib a t e).
Definition ccequivc {p} lib t1 t2 := Cast (@cequivc p lib t1 t2).
Definition capproxc {p} lib t1 t2 := Cast (@approxc p lib t1 t2).
Definition ccompute_1step {p} lib t1 t2 := Cast (@compute_1step p lib t1 t2).
Definition chaltsc {p} lib t := Cast (@hasvaluec p lib t).
Definition reduces_kstepsc {o} lib (t1 t2 : @CTerm o) k := Cast (@reduces_in_atmost_k_stepsc o lib t1 t2 k).
Definition reduces_ksteps_excc {o} lib (t1 t2 : @CTerm o) k := Cast (@reduces_in_atmost_k_steps_excc o lib t1 t2 k).

Ltac uncast_step :=
  match goal with
    | [ H : ccomputes_to_valc _ _ _     |- _ ] => destruct H as [H]
    | [ H : ccomputes_to_excc _ _ _ _   |- _ ] => destruct H as [H]
    | [ H : ccequivc _ _ _              |- _ ] => destruct H as [H]
    | [ H : capproxc _ _ _              |- _ ] => destruct H as [H]
    | [ H : ccompute_1step _ _ _        |- _ ] => destruct H as [H]
    | [ H : chaltsc _ _                 |- _ ] => destruct H as [H]
    | [ H : reduces_kstepsc _ _ _ _     |- _ ] => destruct H as [H]
    | [ H : reduces_ksteps_excc _ _ _ _ |- _ ] => destruct H as [H]

    | [ H : ccomputes_to_valcn _ _ _     |- _ ] => destruct H as [H]
    | [ H : ccomputes_to_exccn _ _ _ _   |- _ ] => destruct H as [H]
    | [ H : ccequivcn _ _ _              |- _ ] => destruct H as [H]
    | [ H : capproxcn _ _ _              |- _ ] => destruct H as [H]
    | [ H : chaltscn _ _                 |- _ ] => destruct H as [H]

    | [ H : Cast _                      |- _ ] => destruct H as [H]
  end.

Ltac uncast := repeat uncast_step.

Ltac uncastc :=
  match goal with
    | [ |- ccomputes_to_valc _ _ _     ] => constructor
    | [ |- ccomputes_to_excc _ _ _ _   ] => constructor
    | [ |- ccequivc _ _ _              ] => constructor
    | [ |- capproxc _ _ _              ] => constructor
    | [ |- ccompute_1step _ _ _        ] => constructor
    | [ |- chaltsc _ _                 ] => constructor
    | [ |- reduces_kstepsc _ _ _ _     ] => constructor
    | [ |- reduces_ksteps_excc _ _ _ _ ] => constructor

    | [ |- ccomputes_to_valcn _ _ _     ] => constructor
    | [ |- ccomputes_to_exccn _ _ _ _   ] => constructor
    | [ |- ccequivcn _ _ _              ] => constructor
    | [ |- capproxcn _ _ _              ] => constructor
    | [ |- chaltscn _ _                 ] => constructor

    | [ |- Cast _                      ] => constructor
  end.

Ltac spcast := uncast; try uncastc.
