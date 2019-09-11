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
           Abhishek Anand

*)


Require Export nuprl_props.
Require Export choice.
Require Export cvterm.


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

(*Lemma computes_to_valc_implies_ccequivc_ext {o} :
  forall lib (t1 t2 : @CTerm o),
    computes_to_valc lib t1 t2
    -> ccequivc_ext lib t1 t2.
Proof.
  introv c e; spcast.
  apply computes_to_valc_implies_cequivc; eauto 3 with slow.
Qed.
Hint Resolve computes_to_valc_implies_ccequivc_ext : slow.*)

Hint Resolve ccomputes_to_valc_ext_implies_ccequivc_ext : slow.

Lemma nuprl_computes_left {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    nuprl lib t1 t2 eq
    -> ccomputes_to_valc_ext lib t3 t1
    -> nuprl lib t3 t2 eq.
Proof.
  introv n c.
  apply @nuprl_value_respecting_left with (t1 := t1); auto.
  apply ccequivc_ext_sym; eauto 3 with slow.
Qed.

Lemma nuprl_computes_right {o} :
  forall lib (t1 t2 t3 : @CTerm o) eq,
    nuprl lib t1 t2 eq
    -> ccomputes_to_valc_ext lib t3 t2
    -> nuprl lib t1 t3 eq.
Proof.
  introv n c.
  apply @nuprl_value_respecting_right with (t2 := t2); auto.
  apply ccequivc_ext_sym; eauto 3 with slow.
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
  introv ext; apply c in ext; clear c; exrepnd.
  spcast.
  eapply cequivc_integer in ext0;[|eauto 3 with slow].
  apply computes_to_valc_isvalue_eq in ext0; eauto 3 with slow; subst.

  exists (@mkc_uni o (Z.to_nat k)).
  dands; spcast; auto.
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
