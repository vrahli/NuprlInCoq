(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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


Require Import approx_star0.
Require Import approx_star_abs.


Lemma nuprl_extensional_abs {p} :
  forall x : opabs, @extensional_op p (Abs x).
Proof.
  introv Hpra Hprt Hprt' Hcv Has Hi.
  allfold (approx_starbts lib).
  apply computes_to_val_like_in_max_k_steps_S in Hcv; exrepnd.
  csunf Hcv1; allsimpl.
  apply compute_step_lib_success in Hcv1; exrepnd; subst.
  dup Hcv2 as fe1.
  pose proof (approx_starbts_numvars lib (Abs x) lbt lbt' Has) as eqnum.
  apply @found_entry_change_bs with (bs2 := lbt') in Hcv2; auto.
  rename Hcv2 into fe2.

  unfold extensional_op_ind in Hi.

  apply Hi with (v := mk_instance vars lbt' rhs) in Hcv0; auto;
  [ | complete (eapply isprogram_subst_lib; eauto;
                apply isprogram_ot_iff in Hprt; repnd; auto)
    | complete (eapply isprogram_subst_lib; eauto;
                apply isprogram_ot_iff in Hprt'; repnd; auto)
    | ]; clear Hi.

  - apply @approx_star_open_trans with (b := mk_instance vars lbt' rhs); auto.
    apply approx_implies_approx_open.
    apply reduces_to_implies_approx_eauto; prove_isprogram.
    apply reduces_to_if_step; simpl.
    eapply compute_step_lib_success_change_bs; eauto.

  - unfold correct_abs in correct;repnd.
    eapply mk_instance_approx_star_congr; eauto; try (complete (intro xxx; ginv)).

    + apply found_entry_implies_matching_entry in fe1.
      unfold matching_entry in fe1; sp.

    + apply found_entry_implies_matching_entry in fe2.
      unfold matching_entry in fe2; sp.
Qed.
