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


Require Export nuprl_props.


Lemma ccequivc_ext_mkc_function_implies {o} :
  forall lib (A A' : @CTerm o) v v' B B',
    ccequivc_ext lib (mkc_function A v B) (mkc_function A' v' B')
    -> ccequivc_ext lib A A' # bcequivc_ext lib [v] B [v'] B'.
Proof.
  introv ceq; dands; introv ext; apply ceq in ext; simpl in *; spcast;
    apply cequivc_mkc_function_implies in ext; exrepnd;
      apply computes_to_valc_isvalue_eq in ext1; eauto 3 with slow; eqconstr ext1; auto.
Qed.

Lemma ccequivc_ext_mkc_product_implies {o} :
  forall lib (A A' : @CTerm o) v v' B B',
    ccequivc_ext lib (mkc_product A v B) (mkc_product A' v' B')
    -> ccequivc_ext lib A A' # bcequivc_ext lib [v] B [v'] B'.
Proof.
  introv ceq; dands; introv ext; apply ceq in ext; simpl in *; spcast;
    eapply cequivc_mkc_product in ext; exrepnd;eauto 3 with slow;
      apply computes_to_valc_isvalue_eq in ext1; eauto 3 with slow; eqconstr ext1; auto.
Qed.

Lemma ccequivc_ext_mkc_set_implies {o} :
  forall lib (A A' : @CTerm o) v v' B B',
    ccequivc_ext lib (mkc_set A v B) (mkc_set A' v' B')
    -> ccequivc_ext lib A A' # bcequivc_ext lib [v] B [v'] B'.
Proof.
  introv ceq; dands; introv ext; apply ceq in ext; simpl in *; spcast;
    eapply cequivc_mkc_set in ext; exrepnd;eauto 3 with slow;
      apply computes_to_valc_isvalue_eq in ext1; eauto 3 with slow; eqconstr ext1; auto.
Qed.

Lemma inl_ccomputes_to_valc_ext_inr_false {o} :
  forall lib (a b : @CTerm o),
    (mkc_inl a) ===>(lib) (mkc_inr b) -> False.
Proof.
  introv comp.
  pose proof (comp _ (lib_extends_refl _)) as comp; simpl in *; exrepnd; spcast.
  eapply cequivc_mkc_inr in comp0;[|eauto 3 with slow]; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow; subst.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow; subst.
  eqconstr comp1.
Qed.

Lemma inr_ccomputes_to_valc_ext_inl_false {o} :
  forall lib (a b : @CTerm o),
    (mkc_inr a) ===>(lib) (mkc_inl b) -> False.
Proof.
  introv comp.
  pose proof (comp _ (lib_extends_refl _)) as comp; simpl in *; exrepnd; spcast.
  eapply cequivc_mkc_inl in comp0;[|eauto 3 with slow]; exrepnd.
  apply computes_to_valc_isvalue_eq in comp0; eauto 3 with slow; subst.
  apply computes_to_valc_isvalue_eq in comp1; eauto 3 with slow; subst.
  eqconstr comp1.
Qed.

Lemma iscvalue_qtime {o} : forall (A : @CTerm o), iscvalue (mkc_qtime A).
Proof.
  introv; destruct_cterms; unfold iscvalue; simpl; split; simpl; tcsp.
  apply implies_isprogram_qtime; eauto 3 with slow.
Qed.
Hint Resolve iscvalue_qtime : slow.


Ltac ccomputes_to_valc_ext_val :=
  match goal with
  | [ H : (mkc_function _ _ _) ===>(_) (mkc_function _ _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_mkc_function_implies in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_function _ _ _) (mkc_function _ _ _) |- _ ] =>
    apply ccequivc_ext_mkc_function_implies in H;
    repnd

  | [ H : (mkc_product _ _ _) ===>(_) (mkc_product _ _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_mkc_product_implies in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_product _ _ _) (mkc_product _ _ _) |- _ ] =>
    apply ccequivc_ext_mkc_product_implies in H;
    repnd

  | [ H : (mkc_set _ _ _) ===>(_) (mkc_set _ _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_mkc_set_implies in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_set _ _ _) (mkc_set _ _ _) |- _ ] =>
    apply ccequivc_ext_mkc_set_implies in H;
    repnd

  | [ H : (mkc_cequiv _ _) ===>(_) (mkc_cequiv _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply cequivc_ext_mkc_cequiv_right in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_cequiv _ _) (mkc_cequiv _ _) |- _ ] =>
    apply cequivc_ext_mkc_cequiv_right in H;
    repnd

  | [ H : (mkc_approx _ _) ===>(_) (mkc_approx _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply cequivc_ext_mkc_approx_right in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_approx _ _) (mkc_approx _ _) |- _ ] =>
    apply cequivc_ext_mkc_approx_right in H;
    repnd

  | [ H : (mkc_equality _ _ _) ===>(_) (mkc_equality _ _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_mkc_equality_implies in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_equality _ _ _) (mkc_equality _ _ _) |- _ ] =>
    apply ccequivc_ext_mkc_equality_implies in H;
    repnd

  | [ H : (mkc_union _ _) ===>(_) (mkc_union _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply cequivc_ext_mkc_union_right in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_union _ _) (mkc_union _ _) |- _ ] =>
    apply cequivc_ext_mkc_union_right in H;
    repnd

  | [ H : (mkc_qtime _) ===>(_) (mkc_qtime _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply cequivc_ext_mkc_qtime_right in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_qtime _) (mkc_qtime _) |- _ ] =>
    apply cequivc_ext_mkc_qtime_right in H;
    repnd

  | [ H : (mkc_image _ _) ===>(_) (mkc_image _ _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply cequivc_ext_mkc_image_implies in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_image _ _) (mkc_image _ _) |- _ ] =>
    apply cequivc_ext_mkc_image_implies in H;
    repnd

  | [ H : (mkc_inl _) ===>(_) (mkc_inl _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_inl_inl_implies in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_inl _) (mkc_inl _) |- _ ] =>
    apply ccequivc_ext_inl_inl_implies in H;
    repnd

  | [ H : (mkc_inr _) ===>(_) (mkc_inr _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_inr_inr_implies in H;
    repnd

  | [ H : ccequivc_ext _ (mkc_inr _)(mkc_inr _) |- _ ] =>
    apply ccequivc_ext_inr_inr_implies in H;
    repnd

  | [ H : (mkc_csname _) ===>(_) (mkc_csname _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_mkc_csname_implies in H;
    try subst

  | [ H : ccequivc_ext _ (mkc_csname _) (mkc_csname _) |- _ ] =>
    apply ccequivc_ext_mkc_csname_implies in H;
    try subst

  | [ H : (mkc_uni _) ===>(_) (mkc_uni _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_uni_uni_implies in H;
    try subst

  | [ H : ccequivc_ext _ (mkc_uni _) (mkc_uni _) |- _ ] =>
    apply ccequivc_ext_uni_uni_implies in H;
    try subst

  | [ H : (mkc_integer _) ===>(_) (mkc_integer _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_mkc_integer_implies in H;
    try subst

  | [ H : ccequivc_ext _ (mkc_integer _) (mkc_integer _) |- _ ] =>
    apply ccequivc_ext_mkc_integer_implies in H;
    try subst

  | [ H : (mkc_choice_seq _) ===>(_) (mkc_choice_seq _) |- _ ] =>
    apply ccomputes_to_valc_ext_implies_ccequivc_ext in H;
    apply ccequivc_ext_mkc_choice_seq_implies in H;
    try subst

  | [ H : ccequivc_ext _ (mkc_choice_seq _) (mkc_choice_seq _) |- _ ] =>
    apply ccequivc_ext_mkc_choice_seq_implies in H;
    try subst

  | [ H : (mkc_inr _) ===>(_) (mkc_inl _) |- _ ] =>
    apply inr_ccomputes_to_valc_ext_inl_false in H; inversion H

  | [ H : (mkc_inl _) ===>(_) (mkc_inr _) |- _ ] =>
    apply inl_ccomputes_to_valc_ext_inr_false in H; inversion H
  end.
