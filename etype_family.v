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


Require Import type_sys_useful2.
Require Import tactics2.

Definition eq_term_equals_efam (eqa1 eqa1' : per) eqb1 eqa2 eqa2' eqb2 :=
  forall (a a' : CTerm)
         (e1  : eqa1 a a)
         (e1' : eqa1' a' a')
         (e2  : eqa2 a a)
         (e2' : eqa2' a' a'),
    (eqb1 a a' e1 e1') <=2=> (eqb2 a a' e2 e2').

Lemma eisect_eq_equal :
  forall eqa1 eqa1' eqb1 eqa2 eqa2' eqb2,
    (eqa1 <=2=> eqa2)
    -> (eqa1' <=2=> eqa2')
    -> eq_term_equals_efam eqa1 eqa1' eqb1 eqa2 eqa2' eqb2
    -> ((eisect_eq eqa1 eqa1' eqb1) <=2=> (eisect_eq eqa2 eqa2' eqb2)).
Proof.
  introv eq1 eq2 eq3.
  introv.
  unfold eisect_eq.
  split; intro k; introv.

  dup e as e1.
  apply eq1 in e1.
  dup e' as e1'.
  apply eq2 in e1'.
  generalize (eq3 a a' e1 e1' e e'); intro j.
  apply j; sp.

  dup e as e2.
  apply eq1 in e2.
  dup e' as e2'.
  apply eq2 in e2'.
  generalize (eq3 a a' e e' e2 e2'); intro j.
  apply j; sp.
Qed.

Lemma etype_family_eq_term_equals :
  forall TC ts T T1 T2 eqa1 eqa1' eqb1 eqa2 eqa2' eqb2
         A v (B : CVTerm [v]),
    (forall x y z a b c, TC x y z = TC a b c -> x = a # y = b)
    -> (forall x y z c, TC x y z = TC x y c -> z = c)
    -> computes_to_valc T (TC A v B)
    -> type_sys_props ts A A eqa1
    -> etype_family TC ts T T1 eqa1 eqa1' eqb1
    -> etype_family TC ts T T2 eqa2 eqa2' eqb2
    -> ((eqa1 <=2=> eqa2)
        # (eqa1' <=2=> eqa2')
        # eq_term_equals_efam eqa1 eqa1' eqb1 eqa2 eqa2' eqb2).
Proof.
  introv c1 c2 c tspa1 efam1 efam2.

  allunfold etype_family; exrepnd.
  spcast.
  computes_to_eqval.
  applydup c1 in eq; repnd; subst.
  apply c2 in eq; subst; GC.
  computes_to_eqval.
  applydup c1 in eq; repnd; subst.
  apply c2 in eq; subst; GC.

  (* - 1 - *)
  prove_and eqas1.
  apply type_sys_props_eq_term_equals with (ts := ts) (A := A) (B := A) (C := A); auto.

  (* - 2 - *)
  prove_and eqas2.

Abort.
