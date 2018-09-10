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
Require Export cvterm4.
(*Require Export per_props.*)


Lemma fold_less {o} :
  forall a b c d : @NTerm o,
    oterm (NCan (NCompOp CompOpLess)) [nobnd a, nobnd b, nobnd c, nobnd d]
    = mk_less a b c d.
Proof. sp. Qed.

Lemma mkc_less_than_comp1 {o} :
  forall lib (a b : @CTerm o) n m,
    computes_to_valc lib a (mkc_integer n)
    -> computes_to_valc lib b (mkc_integer m)
    -> (n < m)%Z
    -> computes_to_valc lib (mkc_less_than a b) mkc_true.
Proof.
  introv comp1 comp2 h.
  rw @mkc_less_than_eq.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto.
  pose proof (reduce_to_prinargs_comp
                lib CompOpLess
                x0 x
                [nobnd mk_true, nobnd mk_false]
                (mk_integer n)
                (mk_integer m)) as r.
  repeat (autodimp r hyp).
  { unfold computes_to_value; dands; auto. }
  { unfold iswfpk; eauto 3 with slow. }
  allrw @fold_nobnd.
  allrw @fold_less.
  eapply reduces_to_trans; eauto.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf q; allsimpl.
  unfold compute_step_comp; simpl.
  boolvar; auto; try omega.
Qed.





Lemma mkc_less_than_comp2 {o} :
  forall lib (a b : @CTerm o) n m,
    computes_to_valc lib a (mkc_integer n)
    -> computes_to_valc lib b (mkc_integer m)
    -> (m <= n)%Z
    -> computes_to_valc lib (mkc_less_than a b) mkc_false.
Proof.
  introv comp1 comp2 h.
  rw @mkc_less_than_eq.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto.
  pose proof (reduce_to_prinargs_comp
                lib CompOpLess
                x0 x
                [nobnd mk_true, nobnd mk_false]
                (mk_integer n)
                (mk_integer m)) as r.
  repeat (autodimp r hyp).
  { unfold computes_to_value; dands; auto. }
  { unfold iswfpk; eauto 3 with slow. }
  allrw @fold_nobnd.
  allrw @fold_less.
  eapply reduces_to_trans; eauto.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf q; allsimpl.
  unfold compute_step_comp; simpl.
  boolvar; auto; try omega.
Qed.

Definition mk_not_less_than {p} (a b : @NTerm p) := mk_less a b mk_false mk_true.
Definition mk_eqint {p} (a b : @NTerm p) := mk_int_eq a b mk_true mk_false.
Definition mk_not_eqint {p} (a b : @NTerm p) := mk_int_eq a b mk_false mk_true.
Definition mkc_not_less_than {p} (a b : @CTerm p) := mkc_less a b mkc_false mkc_true.
Definition mkc_eqint {p} (a b : @CTerm p) := mkc_inteq a b mkc_true mkc_false.
Definition mkc_not_eqint {p} (a b : @CTerm p) := mkc_inteq a b mkc_false mkc_true.

Lemma mkc_eqint_eq {o} :
  forall a b : @CTerm o,
    mkc_eqint a b = mkc_inteq a b mkc_true mkc_false.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma mkc_not_eqint_eq {o} :
  forall a b : @CTerm o,
    mkc_not_eqint a b = mkc_inteq a b mkc_false mkc_true.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma mkc_not_less_than_eq {o} :
  forall a b : @CTerm o,
    mkc_not_less_than a b = mkc_less a b mkc_false mkc_true.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma mkc_not_less_than_comp1 {o} :
  forall lib (a b : @CTerm o) n m,
    computes_to_valc lib a (mkc_integer n)
    -> computes_to_valc lib b (mkc_integer m)
    -> (n < m)%Z
    -> computes_to_valc lib (mkc_not_less_than a b) mkc_false.
Proof.
  introv comp1 comp2 h.
  rw @mkc_not_less_than_eq.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto.
  pose proof (reduce_to_prinargs_comp
                lib CompOpLess
                x0 x
                [nobnd mk_false, nobnd mk_true]
                (mk_integer n)
                (mk_integer m)) as r.
  repeat (autodimp r hyp).
  { unfold computes_to_value; dands; auto. }
  { unfold iswfpk; eauto 3 with slow. }
  allrw @fold_nobnd.
  allrw @fold_less.
  eapply reduces_to_trans; eauto.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf q; allsimpl.
  unfold compute_step_comp; simpl.
  boolvar; auto; try omega.
Qed.





Lemma mkc_not_less_than_comp2 {o} :
  forall lib (a b : @CTerm o) n m,
    computes_to_valc lib a (mkc_integer n)
    -> computes_to_valc lib b (mkc_integer m)
    -> (m <= n)%Z
    -> computes_to_valc lib (mkc_not_less_than a b) mkc_true.
Proof.
  introv comp1 comp2 h.
  rw @mkc_not_less_than_eq.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto.
  pose proof (reduce_to_prinargs_comp
                lib CompOpLess
                x0 x
                [nobnd mk_false, nobnd mk_true]
                (mk_integer n)
                (mk_integer m)) as r.
  repeat (autodimp r hyp).
  { unfold computes_to_value; dands; auto. }
  { unfold iswfpk; eauto 3 with slow. }
  allrw @fold_nobnd.
  allrw @fold_less.
  eapply reduces_to_trans; eauto.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf q; allsimpl.
  unfold compute_step_comp; simpl.
  boolvar; auto; try omega.
Qed.


Lemma mkc_eqint_comp1 {o} :
  forall lib (a b : @CTerm o) n m,
    computes_to_valc lib a (mkc_integer n)
    -> computes_to_valc lib b (mkc_integer m)
    -> (n = m)
    -> computes_to_valc lib (mkc_eqint a b) mkc_true.
Proof.
  introv comp1 comp2 h.
  rw @mkc_eqint_eq.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto. 
  rw h in comp3. clear h comp1.
  pose proof (reduce_to_prinargs_comp
                lib CompOpEq
                x0 x
                [nobnd mk_true, nobnd mk_false]
                (mk_integer m)
                (mk_integer m)) as r.
  repeat (autodimp r hyp).
  { unfold computes_to_value; dands; auto. }
  { unfold iswfpk; eauto 3 with slow. }
  allrw @fold_nobnd.
  allrw @fold_less.
  eapply reduces_to_trans; eauto.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf q; allsimpl.
  unfold compute_step_comp; simpl.
  boolvar; auto; try omega.  destruct n0. reflexivity.
Qed.

Lemma mkc_eqint_comp2 {o} :
  forall lib (a b : @CTerm o) n m,
    computes_to_valc lib a (mkc_integer n)
    -> computes_to_valc lib b (mkc_integer m)
    -> (n <> m)
    -> computes_to_valc lib (mkc_eqint a b) mkc_false.
Proof.
  introv comp1 comp2 h.
  rw @mkc_eqint_eq.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto. 
  pose proof (reduce_to_prinargs_comp
                lib CompOpEq
                x0 x
                [nobnd mk_true, nobnd mk_false]
                (mk_integer n)
                (mk_integer m)) as r.
  repeat (autodimp r hyp).
  { unfold computes_to_value; dands; auto. }
  { unfold iswfpk; eauto 3 with slow. }
  allrw @fold_nobnd.
  allrw @fold_less.
  eapply reduces_to_trans; eauto.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf q; allsimpl.
  unfold compute_step_comp; simpl.
  boolvar; auto; try omega. inversion e. destruct h. auto.
Qed.

Lemma mkc_not_eqint_comp1 {o} :
  forall lib (a b : @CTerm o) n m,
    computes_to_valc lib a (mkc_integer n)
    -> computes_to_valc lib b (mkc_integer m)
    -> (n = m)
    -> computes_to_valc lib (mkc_not_eqint a b) mkc_false.
Proof.
  introv comp1 comp2 h.
  rw @mkc_not_eqint_eq.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto. 
  rw h in comp3. clear h comp1.
  pose proof (reduce_to_prinargs_comp
                lib CompOpEq
                x0 x
                [nobnd mk_false, nobnd mk_true]
                (mk_integer m)
                (mk_integer m)) as r.
  repeat (autodimp r hyp).
  { unfold computes_to_value; dands; auto. }
  { unfold iswfpk; eauto 3 with slow. }
  allrw @fold_nobnd.
  allrw @fold_less.
  eapply reduces_to_trans; eauto.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf q; allsimpl.
  unfold compute_step_comp; simpl.
  boolvar; auto; try omega.  destruct n0. reflexivity.
Qed.

Lemma mkc_not_eqint_comp2 {o} :
  forall lib (a b : @CTerm o) n m,
    computes_to_valc lib a (mkc_integer n)
    -> computes_to_valc lib b (mkc_integer m)
    -> (n <> m)
    -> computes_to_valc lib (mkc_not_eqint a b) mkc_true.
Proof.
  introv comp1 comp2 h.
  rw @mkc_not_eqint_eq.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto. 
  pose proof (reduce_to_prinargs_comp
                lib CompOpEq
                x0 x
                [nobnd mk_false, nobnd mk_true]
                (mk_integer n)
                (mk_integer m)) as r.
  repeat (autodimp r hyp).
  { unfold computes_to_value; dands; auto. }
  { unfold iswfpk; eauto 3 with slow. }
  allrw @fold_nobnd.
  allrw @fold_less.
  eapply reduces_to_trans; eauto.
  apply reduces_to_if_step.
  csunf; simpl.
  dcwf q; allsimpl.
  unfold compute_step_comp; simpl.
  boolvar; auto; try omega. inversion e. destruct h. auto.
Qed.



Lemma nuprl_computes_left {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    nuprl lib t1 t2 eq
    -> computes_to_valc lib t3 t1
    -> nuprl lib t3 t2 eq.
Proof.
  introv n c.
  apply @nuprl_value_respecting_left with (t1 := t1); auto.
  apply cequivc_sym.
  apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma nuprl_computes_right {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    nuprl lib t1 t2 eq
    -> computes_to_valc lib t3 t2
    -> nuprl lib t1 t3 eq.
Proof.
  introv n c.
  apply @nuprl_value_respecting_right with (t2 := t2); auto.
  apply cequivc_sym.
  apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma computes_to_valc_tuni {o} :
  forall lib (t : @CTerm o) k,
    (0 <= k)%Z
    -> computes_to_valc lib t (mkc_integer k)
    -> computes_to_valc lib (mkc_tuni t) (mkc_uni (Z.to_nat k)).
Proof.
  introv le c.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto; try (apply isvalue_mk_uni).
  apply reduces_to_trans with (b := mk_tuni (mk_integer k)).
  apply reduces_to_prinarg; auto.
  apply reduces_to_if_step.
  csunf; simpl.
  unfold compute_step_tuni; simpl.
  destruct (Z_le_gt_dec 0 k); auto; omega.
Qed.

Lemma ccomputes_to_valc_tuni {o} :
  forall lib (t : @CTerm o) k,
    (0 <= k)%Z
    -> t ===>(lib) (mkc_integer k)
    -> (mkc_tuni t) ===>(lib) (mkc_uni (Z.to_nat k)).
Proof.
  introv le c.
  spcast.
  destruct_cterms.
  allunfold @computes_to_valc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto; try (apply isvalue_mk_uni).
  apply reduces_to_trans with (b := mk_tuni (mk_integer k)).
  apply reduces_to_prinarg; auto.
  apply reduces_to_if_step.
  csunf; simpl.
  unfold compute_step_tuni; simpl.
  destruct (Z_le_gt_dec 0 k); auto; omega.
Qed.

Lemma computes_to_valc_implies_hasvaluec {o} :
  forall lib (a b : @CTerm o), computes_to_valc lib a b -> hasvaluec lib a.
Proof.
  introv c.
  unfold computes_to_valc in c.
  unfold hasvaluec, hasvalue.
  exists (get_cterm b); auto.
Qed.
