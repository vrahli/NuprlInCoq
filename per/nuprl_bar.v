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


Require Export type_sys.
Require Import dest_close.
Require Export per_ceq_bar.

Require Export nuprl_mon.


Definition type_bar {o} (ts : cts(o)) :=
  forall lib (bar : @BarLib o lib) T1 T2 eqa,
    all_in_bar_ext bar (fun lib' x => ts lib' T1 T2 (eqa lib' x))
    ->
    exists eqa',
      ts lib T1 T2 eqa'
         (*# forall lib' (x : lib_extends lib' lib), sub_per eqa' (eqa lib' x)*).

(*Lemma univi_bar {o} : forall i, @type_bar o (univi i).
Proof.
Qed.*)

(*Lemma close_bar {o} :
  forall (ts : cts(o)),
    defines_only_universes ts
    -> type_bar ts
    -> type_bar (close ts).
Proof.
  introv dou tb u.

  pose proof (bar_non_empty bar) as q; exrepnd.
  pose proof (u lib' q0 lib' (lib_extends_refl lib') (bar_lib_ext bar lib' q0)) as h; simpl in h.

  close_cases (induction h using @close_ind') Case.

  Focus 2.

  - Case "CL_int".
    exists (equality_of_int_bar lib).
    apply CL_int.
    unfold per_int_bar; dands; auto.
    unfold per_int_bar in *; exrepnd.
    exists bar0; dands; auto.


  - Case "CL_init".
    pose proof (tb lib bar T T' eqa) as q.
    autodimp q hyp;[|exrepnd; exists eqa'; apply CL_init; auto].

    introv br ext; introv.
    pose proof (u lib' br lib'0 ext x) as q; simpl in q.

    Print defines_only_universes.

    close_cases (induction q using @close_ind') SCase; auto.

    + SCase "CL_int".
      unfold per_int_bar in *; exrepnd.

Qed.*)

Lemma nuprl_bar {o} : @type_bar o nuprl.
Proof.
  introv u.


  (* Does this need something like bar induction?
     Coquand/Bassel seem to pick a particular path to prove that. *)
Qed.
Hint Resolve nuprl_bar : slow.
