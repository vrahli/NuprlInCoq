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



Lemma member_mono_is_axiom {o} :
  forall lib (T a b : @CTerm o),
    equality lib a b (mkc_mono T)
    -> a ===>(lib) mkc_axiom # b ===>(lib) mkc_axiom.
Proof.
  unfold equality, nuprl; introv e; exrepd.
  inversion c; subst; try not_univ.

  allunfold @per_mono; allunfold @per_mono_eq; exrepnd.
  computes_to_value_isvalue.
  match goal with
      [H1 : eq _ _ , H2:eq_term_equals _ _ |- _] => apply H2 in H1
  end. repnd. auto.
Qed.

Lemma equality_in_mkc_mono {o} :
  forall lib (A t1 t2 : @CTerm o),
    equality lib t1 t2 (mkc_mono A)
    <=> {eqa : term_equality , t1 ===>(lib) mkc_axiom # t2 ===>(lib) mkc_axiom 
      # close lib (univ lib) A A eqa # mono_equality lib eqa}.
Proof.
  introv; split; intro i.

  - applydup @member_mono_is_axiom in i; repnd;
    allunfold @equality; allunfold @nuprl; exrepnd.
    inversion i3; subst; try not_univ.
    allunfold @per_eq; exrepnd. dands; spcast;
    allunfold @per_mono; exrepnd; exists eqa; dands; computes_to_value_isvalue;
    spcast; auto.
    match goal with
      [H1 : eq _ _ , H2:eq_term_equals _ _ |- _] => apply H2 in H1; clear H2
    end.
      allunfold @per_mono_eq. repnd; auto.

  -   repnd.
      allunfold @type.
      allunfold @tequality. exrepnd.
      allunfold @equality; allunfold @nuprl; exrepnd.
      exists (fun t t' : @CTerm o => ccomputes_to_valc lib t mkc_axiom
              # ccomputes_to_valc lib t' mkc_axiom
              # mono_equality lib eqa); sp.
      apply CL_mono.
      unfold per_mono.
      exists A A eqa; sp; spcast;
      try (apply computes_to_valc_refl);
      try (apply iscvalue_mkc_mono; auto).
Qed.

(*
(* !! MOVE  *)
Lemma equality_in_nodep_fun_implies :
  forall f g A B,
    equality f g (mkc_fun A B)
    ->
    (type A # forall a a' : CTerm, equality a a' A -> type B)
     # (forall a a',
          equality a a' A
          -> equality (mkc_apply f a) (mkc_apply g a') B).
Proof.
  introv. rw <- fold_mkc_fun.
  rw equality_in_function. introv Hyp.
  exrepnd; dands; auto; introv Heq.
  - apply Hyp1 in Heq.
    rw substc_cnewvar in Heq.
    rw substc_cnewvar in Heq.
    auto.
  - apply Hyp in Heq.
    rw substc_cnewvar in Heq. auto.
Qed.
*)

(** The following lemma expresses the key property of Mono types.
    Intuitively a type [T] is mono (i.e. [mkc_mono T] is inhabited) if,  whenever we
    have some [a] in that type, anything above it in the 
    [approx] ordering (say [b]) is equal to it.

*)

Ltac equality_unique:= let H := fresh "Huniq" in
allunfold nuprl;
match goal with
| [ H1: close ?lib (univ ?lib) ?T1 ?T1 _ , H2 : close ?lib (univ ?lib) ?T1 ?T1 _ |- _ ] => 
    pose proof (nuprl_uniquely_valued lib _ _ _ H1 H2) as H
end.

Lemma mono_inhabited_implies {o} : forall lib T,
member lib mkc_axiom (mkc_mono T)
-> (forall (a b : @CTerm o),
        member lib a T
        -> approxc lib a b
        -> equality lib a b T).
Proof.
  introv Hm.
  apply equality_in_mkc_mono in Hm.
  exrepnd.
  clear Hm1 Hm2.
  repnud Hm0.
  introv Hm Hap.
  repnud Hm.  repnud Hm.
  exrepnd.
  equality_unique.
  apply Huniq in Hm1.
  eapply Hm0 in Hap; eauto;[].
  exists eqa. dands; auto.
Qed.

Lemma tequality_mono {o} :
  forall lib (A1 A2 : @CTerm o),
    tequality lib (mkc_mono A1) (mkc_mono A2)
    <=> tequality lib A1 A2.
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.
    allunfold @per_mono; exrepnd.
    computes_to_value_isvalue.
    allfold @nuprl.
    dands.
    exists eqa; auto.

  - Case "<-".
    intro teq.
    unfold tequality in teq; destruct teq as [eqa n].
    exists (per_mono_eq lib eqa).
    apply CL_mono.
    unfold per_mono.
    exists A1 A2 eqa; dands; fold @nuprl; auto;
    try (complete (spcast; apply computes_to_valc_refl; apply_iscvalue)).
Qed.
