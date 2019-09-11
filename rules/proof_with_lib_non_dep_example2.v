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


Require Export proof_with_lib_non_dep.


Definition opabs_foo : opabs := Build_opabs "foo" [] [].
Definition opabs_bar : opabs := Build_opabs "bar" [] [].

Definition cmds1 {o} : @commands o :=
  [
    (* We define a new abstraction on top of the one we got from "int_member"'s proof *)
    COM_add_def
      (MkAbstraction
         opabs_foo
         []
         (mk_simple_so_abs (opname2opabs "bar"))
         (eq_refl, (eq_refl, (eq_refl, (eq_refl, eq_refl))))),
    COM_add_def
      (MkAbstraction
         opabs_bar
         []
         (mk_simple_so_abs (opname2opabs "foo"))
         (eq_refl, (eq_refl, (eq_refl, (eq_refl, eq_refl)))))
  ].

Definition lib1 {o} : @UpdRes o := update_list_from_init cmds1.
Eval compute in lib1.

Time Eval compute in (update_list_from_init_with_validity cmds1).
