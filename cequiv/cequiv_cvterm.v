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

  Authors: Vincent Rahli

*)


Require Export cvterm4.
Require Export cequiv.


Lemma cequivc_mkc_inteq_int {o} :
  forall lib i1 i2 (t1 t2 : @CTerm o),
    cequivc
      lib
      (mkc_inteq (mkc_integer i1) (mkc_integer i2) t1 t2)
      (if Z.eq_dec i1 i2 then t1 else t2).
Proof.
  introv.
  destruct_cterms.
  unfold cequivc; simpl.
  boolvar; subst; simpl; apply reduces_to_implies_cequiv;
  allrw @isprogram_eq; try (apply isprog_inteq_implies); eauto 3 with slow;
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl;
  unfold compute_step_comp; simpl;
  boolvar; tcsp; try lia.
  ginv; tcsp.
Qed.

Lemma cequivc_mkc_inteq_nat {o} :
  forall lib (i1 i2 : nat) (t1 t2 : @CTerm o),
    cequivc lib
            (mkc_inteq (mkc_nat i1) (mkc_nat i2) t1 t2)
            (if eq_nat_dec i2 i1 then t1 else t2).
Proof.
  introv.
  allrw @mkc_nat_eq.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_int|].
  boolvar; tcsp; try lia.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/")
*** End:
*)
