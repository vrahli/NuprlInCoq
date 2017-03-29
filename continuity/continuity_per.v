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



Require Export per_props_equality_more.
Require Export per_props_set.
(*Require Export per_props3.*)
Require Export per_props_nat.

Require Export continuity_defs2.


Lemma computes_to_val_absolute_value {o} :
  forall lib (t : @NTerm o) k,
    computes_to_value lib t (mk_integer k)
    -> computes_to_value lib (absolute_value t) (mk_integer (Z.abs k)).
Proof.
  introv comp.
  allunfold @computes_to_value; repnd; dands; eauto with slow.
  unfold absolute_value.
  eapply reduces_to_trans;
    [eapply reduces_to_prinarg;exact comp0|].
  destruct (Z_lt_ge_dec k 0) as [i|i].

  - apply (reduces_to_if_split2
             _ _ (mk_minus t)); simpl.

    * csunf; simpl.
      dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp; try omega.

    * eapply reduces_to_trans;
      [eapply reduces_to_prinarg;exact comp0|].
      apply reduces_to_if_step; csunf; simpl.
      unfold compute_step_minus; simpl.
      f_equal; f_equal.
      destruct k; allsimpl; try omega.
      pose proof (Pos2Z.is_pos p); omega.

  - apply (reduces_to_if_split2
             _ _ t); simpl.

    * csunf; simpl.
      dcwf h; simpl.
      unfold compute_step_comp; simpl; boolvar; tcsp; try omega.

    * eapply reduces_to_trans; [exact comp0|].
      apply reduces_to_if_step; csunf; simpl.
      f_equal; f_equal; fold_terms; f_equal.
      destruct k; allsimpl; try omega.
      pose proof (Pos2Z.neg_is_neg p); try omega.
Qed.

Definition absolute_value_c {o} (t : @CTerm o) : CTerm :=
  mkc_less t mkc_zero (mkc_minus t) t.

Lemma computes_to_valc_absolute_value {o} :
  forall lib (t : @CTerm o) k,
    computes_to_valc lib t (mkc_integer k)
    -> computes_to_valc lib (absolute_value_c t) (mkc_integer (Z.abs k)).
Proof.
  introv comp.
  destruct_cterms; allunfold @computes_to_valc; allsimpl;
  apply computes_to_val_absolute_value; auto.
Qed.

Lemma equal_absolute_values {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_int
    -> equality lib (absolute_value_c a) (absolute_value_c b) mkc_int.
Proof.
  introv e.
  apply equality_in_int in e.
  unfold equality_of_int in e; exrepnd; spcast.

  apply equality_in_int.
  unfold equality_of_int.
  exists (Z.abs k); dands; spcast;
  apply computes_to_valc_absolute_value; auto.
Qed.

Lemma isprogram_absolute_value {o} :
  forall (a : @NTerm o), isprogram (absolute_value a) <=> isprogram a.
Proof.
  introv; split; intro k.
  - allunfold @isprogram; allunfold @closed; repnd; allsimpl.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    allrw app_eq_nil_iff; repnd; allrw; dands; auto.
    unfold absolute_value in k.
    allrw @nt_wf_eq.
    apply wf_less_iff in k; sp.
  - allunfold @isprogram; allunfold @closed; repnd; allsimpl.
    allrw remove_nvars_nil_l; allrw app_nil_r.
    allrw app_eq_nil_iff; repnd; allrw; dands; auto.
    unfold absolute_value.
    allrw @nt_wf_eq.
    apply wf_less_iff; sp.
    apply wf_minus; auto.
Qed.

Lemma cequiv_absolute_value {o} :
  forall lib (a b : @NTerm o) k,
    isprogram a
    -> isprogram b
    -> reduces_to lib a (mk_integer k)
    -> reduces_to lib b (mk_integer k)
    -> cequiv lib (absolute_value a) (absolute_value b).
Proof.
  introv ispa ispb r1 r2.
  apply (cequiv_trans _ _ (mk_integer (Z.abs k))).
  - apply reduces_to_implies_cequiv;
    [apply isprogram_absolute_value; auto|].
    pose proof (computes_to_val_absolute_value lib a k) as h.
    autodimp h hyp.
    { unfold computes_to_value; dands; eauto with slow. }
    unfold computes_to_value in h; sp.
  - apply cequiv_sym.
    apply reduces_to_implies_cequiv;
    [apply isprogram_absolute_value; auto|].
    pose proof (computes_to_val_absolute_value lib b k) as h.
    autodimp h hyp.
    { unfold computes_to_value; dands; eauto with slow. }
    unfold computes_to_value in h; sp.
Qed.

Lemma cequivc_absolute_value {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_int
    -> cequivc lib (absolute_value_c a) (absolute_value_c b).
Proof.
  introv e.
  apply equality_in_int in e.
  apply equality_of_int_imp_tt in e.
  unfold equality_of_int_tt in e; exrepnd.
  destruct_cterms; allunfold @computes_to_valc; allunfold @cequivc; allsimpl.
  fold (absolute_value x0).
  fold (absolute_value x).
  allunfold @computes_to_value; repnd.
  apply (cequiv_absolute_value _ _ _ k);
    auto; try (apply isprogram_eq; auto).
Qed.

Ltac clear_cv :=
  repeat match goal with
           | [ H : cover_vars _ _ |- _ ] => clear H
           | [ H : wf_term _ |- _ ] => clear H
         end.

Ltac keepdimp H hyp :=
  match type of H with
    | ?T1 -> ?T2 =>
      assert T1 as hyp;
        [ clear H; try (complete auto)
        | try (let concl := fresh "hyp" in
                 pose proof (H hyp) as concl;
               clear H;
               rename concl into H)
          ; try (complete auto)
        ]
  end.
