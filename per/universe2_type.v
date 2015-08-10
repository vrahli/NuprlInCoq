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


Notation "[U]" := Type.

Notation "{ a : T , P }" := ({a : T & P}) (at level 0, a at level 99).
Notation "T {+} U" := (T + U)%type (at level 80, right associativity).


Require Export cequiv.

Definition ccomputes_to_valc {o} lib (t1 t2 : @CTerm o) := computes_to_valc lib t1 t2.
Definition ccomputes_to_excc {o} lib (a t e : @CTerm o) := computes_to_excc lib a t e.
Definition ccequivc {o} lib (t1 t2 : @CTerm o) := cequivc lib t1 t2.
Definition capproxc {o} lib (t1 t2 : @CTerm o) := approxc lib t1 t2.
Definition ccompute_1step {o} lib (t1 t2 : @CTerm o) := compute_1step lib t1 t2.
Definition chaltsc {o} lib (t : @CTerm o) := hasvaluec lib t.
Definition reduces_kstepsc {o} lib (t1 t2 : @CTerm o) k := reduces_in_atmost_k_stepsc lib t1 t2 k.
Definition reduces_ksteps_excc {o} lib (t1 t2 : @CTerm o) k := reduces_in_atmost_k_steps_excc lib t1 t2 k.

Ltac uncast_step :=
  match goal with
    | [ H : ccomputes_to_valc _ _ _     |- _ ] => unfold ccomputes_to_valc   in H
    | [ H : ccomputes_to_excc _ _ _ _   |- _ ] => unfold ccomputes_to_valc   in H
    | [ H : ccequivc _ _ _              |- _ ] => unfold ccequivc            in H
    | [ H : capproxc _ _ _              |- _ ] => unfold capproxc            in H
    | [ H : ccompute_1step _ _ _        |- _ ] => unfold ccompute_1step      in H
    | [ H : chaltsc _ _                 |- _ ] => unfold chaltsc             in H
    | [ H : reduces_kstepsc _ _ _ _     |- _ ] => unfold reduces_kstepsc     in H
    | [ H : reduces_ksteps_excc _ _ _ _ |- _ ] => unfold reduces_ksteps_excc in H
  end.

Ltac uncast := repeat uncast_step.

Ltac uncastc :=
  match goal with
    | [ |- ccomputes_to_valc _ _ _     ] => unfold ccomputes_to_valc
    | [ |- ccomputes_to_excc _ _ _ _   ] => unfold ccomputes_to_excc
    | [ |- ccequivc _ _ _              ] => unfold ccequivc
    | [ |- capproxc _ _ _              ] => unfold capproxc
    | [ |- ccompute_1step _ _ _        ] => unfold ccompute_1step
    | [ |- chaltsc _ _                 ] => unfold chaltsc
    | [ |- reduces_kstepsc _ _ _ _     ] => unfold reduces_kstepsc
    | [ |- reduces_ksteps_excc _ _ _ _ ] => unfold reduces_ksteps_excc
  end.

Ltac spcast := uncast; try uncastc.
