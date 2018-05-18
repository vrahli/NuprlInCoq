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



Definition csa : choice_sequence_name :=
  MkChoiceSequenceName "a" (cs_kind_nat 0).


Definition cmds1 {o} : @commands o :=
  [
    (* We add the 'csa' abstraction *)
    COM_add_cs
      (MkChoiceSeq
         _
         csa
         csc_nat
         (correct_restriction_csc_nat csa I))
  ].

Definition lib1 {o} : @UpdRes o := update_list_from_init cmds1.
Eval compute in lib1.

Time Eval compute in (update_list_from_init_with_validity cmds1).
