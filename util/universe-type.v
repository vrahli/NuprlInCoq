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


(** printing #  $\times$ #×# *)
(** printing <=>  $\Leftrightarrow$ #&hArr;# *)
(** printing $  $\times$ #×# *)
(** printing &  $\times$ #×# *)

Notation "[univ]" := Type.
Notation tuniv := Type.

(*
Notation "! x" := (notT x)%type (at level 45, right associativity).
Notation "T # U" := (T * U)%type (at level 55, no associativity) : NupCoqScope.
Notation "T [+] U" := (T + U)%type (at level 50, left associativity) : NupCoqScope.
*)

Notation "! x" := (notT x)%type (at level 75, right associativity).
Notation "T # U" := (T * U)%type (at level 80, right associativity).
Notation "T [+] U" := (T + U)%type (at level 80, right associativity).

Notation "{ a : T $ P }" := {a : T & P} (at level 0, a at level 99).

Notation "injL( a )" := (inl a) (at level 0).
Notation "injR( a )" := (inr a) (at level 0).
Notation "exI( a , b )" := (existT _ a b) (at level 0).

(*Open Scope NupCoqScope.*)

