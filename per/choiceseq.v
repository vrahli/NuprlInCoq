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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export nuprl.
Require Export nat_defs.


Definition memNat {o} : @Mem o :=
  fun c T => exists (n : nat), c = mkc_nat n.

Definition nmember {o} := @member o memNat.

Definition const0 {o} : nat -> @CTerm o := fun n => mkc_nat 0.

Definition seq0 : choice_sequence_name := "seq0".

Definition lib0 {o} : @library o :=
  [lib_cs seq0 (MkChoiceSeqEntry _ [] (csc_coq_law const0))].

Lemma isprog_mk_choice_seq {o} :
  forall (n : choice_sequence_name), @isprog o (mk_choice_seq n).
Proof.
  introv; apply isprog_eq; apply isprogram_mk_choice_seq.
Qed.

Definition mkc_choice_seq {o} name : @CTerm o :=
  exist isprog (mk_choice_seq name) (isprog_mk_choice_seq name).

Lemma seq0_in_nat2nat {o} :
  @nmember o lib0 (mkc_choice_seq seq0) nat2nat.
Proof.
  unfold nat2nat, nmember, member, equality.
  eexists; dands.

  {
    apply CL_func.
    unfold per_func_ext.
    eexists; eexists.
    dands;[|apply eq_term_equals_refl].

    unfold type_family_ext.
    allrw <- @fold_mkc_fun.
    eexists; eexists; eexists; eexists; eexists; eexists.
    dands.

    {
      introv i.
      spcast.
      apply computes_to_valc_refl; eauto 2 with slow.
    }

    {
      introv i.
      spcast.
      apply computes_to_valc_refl; eauto 2 with slow.
    }

    {
      introv i.
      apply CL_set.
      allrw @mkc_tnat_eq.
      unfold per_set.
      eexists; eexists.
      dands.

      {
        unfold type_family.
        eexists; eexists; eexists; eexists; eexists; eexists.
        dands.

        {
          spcast.
          apply computes_to_valc_refl; eauto 2 with slow.
        }

        {
          spcast.
          apply computes_to_valc_refl; eauto 2 with slow.
        }

        {
          apply CL_int.
          unfold per_int_bar.
          dands;[|apply eq_term_equals_refl].

          assert (BarLib memNat lib') as bar.
          {
            exists [lib'].
            unfold BarLibCond.
            introv j.
            exists lib'; simpl; dands; tcsp.
            eauto 2 with slow.
          }
          exists bar.
          dands; auto.

          {
            introv j.
            spcast.
            apply computes_to_valc_refl; eauto 2 with slow.
          }

          {
            introv j.
            spcast.
            apply computes_to_valc_refl; eauto 2 with slow.
          }
        }

        {
          introv.
          allrw @mkcv_le_substc2.
          allrw @mkcv_zero_substc.
          allrw @mkc_var_substc.

          unfold equality_of_int_bar in e; exrepnd.
          unfold equality_of_int_bar1 in e0.

          (* For testing, it would be easier if we had a primitive nat type *)

Qed.