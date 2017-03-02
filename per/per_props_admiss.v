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


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.


Lemma tequality_admiss {p} :
  forall lib (A1 A2 : @CTerm p),
    tequality lib (mkc_admiss A1) (mkc_admiss A2)
    <=> tequality lib A1 A2.
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    introv teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.
    allunfold @per_admiss; exrepnd.
    computes_to_value_isvalue.
    allfold @nuprl.
    dands.
    exists eqa; auto.

  - Case "<-".
    intro teq.
    unfold tequality in teq; destruct teq as [eqa n].
    exists (per_admiss_eq lib eqa).
    apply CL_admiss.
    unfold per_admiss.
    exists A1 A2 eqa; dands; fold @nuprl; auto;
    try (complete (spcast; apply computes_to_valc_refl; apply_iscvalue)).
Qed.
