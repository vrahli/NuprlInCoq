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


Definition csa : choice_sequence_name := MkChoiceSequenceName "a" (cs_kind_nat 0).


Definition cmds1 {o} : @commands o :=
  [
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


(* [2] means that the choices are unconstrained *)
Definition csb : choice_sequence_name := MkChoiceSequenceName "b" (cs_kind_nat 2).


(* MOVE *)
(* =============== *)
(* nat->nat restriction *)
Definition zero_fun {o} := @mkc_lam o nvarx (mkcv_zero _).

(* TODO: restrictions should depend on the current library *)
Definition is_nat_fun {o} : @RestrictionPred o :=
  fun _ t => member [] t nat2nat.

Lemma is_nat_fun_zero_fun {o} : forall n, @is_nat_fun o n zero_fun.
Proof.
  introv.
  unfold is_nat_fun.
  apply implies_member_nat2nat_bar2.
  apply in_ext_implies_all_in_ex_bar; introv ext1; introv.
  apply in_ext_implies_all_in_ex_bar; introv ext2; introv.
  exists 0.
  spcast.
  unfold computes_to_valc; simpl.
  eapply computes_to_value_step;[|csunf; simpl; eauto].
  unfold apply_bterm; simpl; unflsubst.
Qed.
Hint Resolve is_nat_fun_zero_fun : slow.

Definition csc_nat_fun {o} : @ChoiceSeqRestriction o :=
  csc_type (fun _ => zero_fun) is_nat_fun is_nat_fun_zero_fun.
(* =============== *)


Definition cmds2 {o} : @commands o :=
  [
    COM_add_cs (MkNewChoiceSeq _ csb csc_nat_fun I)
  ].


Definition lib4 {o} : @ValidUpdRes o := update_list_with_validity lib3 cmds2.
(* TODO: Why does this run forever? *)
(*Eval compute in lib4.
Time Eval compute in (lib4).*)

(* TODO: next step is to add the choice [zero_fun].
     We'll have to prove [is_nat_fun_zero_fun].
     For that, this lemma should be in the library.
 *)
