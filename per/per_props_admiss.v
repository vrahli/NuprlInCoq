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
    intros teq.
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

Lemma member_admiss_is_axiom {o} :
  forall lib (T a b : @CTerm o),
    equality lib a b (mkc_admiss T)
    -> a ===>(lib) mkc_axiom # b ===>(lib) mkc_axiom.
Proof.
  unfold equality, nuprl; introv e; exrepd.
  inversion c; subst; try not_univ.


  allunfold @per_admiss; allunfold @per_admiss_eq; exrepnd.
  computes_to_value_isvalue.
  match goal with
      [H1 : eq _ _ , H2:eq_term_equals _ _ |- _] => apply H2 in H1
  end. repnd. auto.
Qed.



(*
Lemma mkc_admiss_inhabited:
  forall T, member mkc_axiom (mkc_admiss T)
  -> admissible_equality (get_per_of T).
Proof.
  introv Hmc.
  repnud Hmc.
Qed.
*)


Lemma equality_in_mkc_admiss {o} :
  forall lib (A t1 t2 : @CTerm o),
    equality lib t1 t2 (mkc_admiss A)
    <=> {eqa : term_equality ,  t1 ===>(lib) mkc_axiom # t2 ===>(lib) mkc_axiom
      # close lib (univ lib) A A eqa # admissible_equality eqa}.
Proof.
  introv; split; intro i.

  - applydup @member_admiss_is_axiom in i; repnd;
    allunfold @equality; allunfold @nuprl; exrepnd.
    inversion i3; subst; try not_univ.
    allunfold @per_eq; exrepnd. dands; spcast;
    allunfold @per_admiss; exrepnd; exists eqa; dands; computes_to_value_isvalue;
    spcast; auto.
    match goal with
      [H1 : eq _ _ , H2:eq_term_equals _ _ |- _] => apply H2 in H1; clear H2
    end.
      allunfold @per_admiss_eq. repnd; auto.

  -   repnd.
      allunfold @type.
      allunfold @tequality. exrepnd.
      allunfold @equality; allunfold @nuprl; exrepnd.
      exists (fun t t' : @CTerm o => ccomputes_to_valc lib t mkc_axiom
              # ccomputes_to_valc lib t' mkc_axiom
              # admissible_equality eqa); sp.
      apply CL_admiss.
      unfold per_admiss.
      exists A A eqa; sp; spcast;
      try (apply computes_to_valc_refl);
      try (apply iscvalue_mkc_admiss; auto).
Qed.
