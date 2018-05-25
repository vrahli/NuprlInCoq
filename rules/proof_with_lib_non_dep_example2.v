(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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
      (MkNewChoiceSeq
         _
         csa
         csc_nat
         (correct_restriction_csc_nat csa I))
  ].

Definition lib1 {o} : @ValidUpdRes o := initValidUpdRes.
Eval compute in lib1.
Time Eval compute in (lib1).


Definition lib2 {o} : @ValidUpdRes o := update_list_with_validity lib1 cmds1.
Eval compute in lib2.
Time Eval compute in (lib2).


Definition bad_sat {o} : @nth_choice_satisfies_soft o lib2 (mkc_nat 0) := right_set _ _ I.
Definition lib3_bad {o} : @ValidUpdRes o := update_cs_with_validity lib2 csa (mkc_nat 0) bad_sat.
Eval compute in lib3_bad.
Time Eval compute in (lib3_bad).


Definition good_sat {o} : @nth_choice_satisfies_soft o lib2 (mkc_nat 0) := left_set _ _ (ex_intro _ _ eq_refl).
Definition lib3 {o} : @ValidUpdRes o := update_cs_with_validity lib2 csa (mkc_nat 0) good_sat.
Eval compute in lib3.
Time Eval compute in (lib3).

