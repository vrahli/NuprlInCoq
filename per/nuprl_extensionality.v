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



Require Export computation_lib_extends2.
Require Export type_sys.


Lemma close_extensionality {o} :
  forall {ts : cts(o)},
    type_extensionality ts
    -> type_extensionality (close ts).
Proof.
  introv text cl.
  close_cases (induction cl using @close_ind') Case; introv ext.

  - Case "CL_init".
    apply CL_init.
    eapply text; eauto.

  - Case "CL_bar".
    apply CL_bar.
    unfold per_bar.
    exists bar eqa; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_int".
    apply CL_int.
    unfold per_int in *; repnd; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_nat".
    apply CL_nat.
    unfold per_nat in *; repnd; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_csname".
    apply CL_csname.
    unfold per_csname in *; repnd; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_atom".
    apply CL_atom.
    unfold per_atom in *; repnd; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_uatom".
    apply CL_uatom.
    unfold per_uatom in *; repnd; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_base".
    apply CL_base.
    unfold per_base in *; repnd; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_approx".
    apply CL_approx.
    unfold per_approx in *; exrepnd; dands; auto.
    exists a b c d; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_cequiv".
    apply CL_cequiv.
    unfold per_cequiv in *; exrepnd; dands; auto.
    exists a b c d; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_eq".
    apply CL_eq.
    exists A B a1 a2 b1 b2 eqa; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_func".
    apply CL_func.
    exists eqa eqb; dands; auto.
    { exists A A' v v' B B'; dands; auto. }
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_union".
    apply CL_union.
    exists eqa eqb A A' B B'; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_image".
    apply CL_image.
    exists eqa A A' f f'; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_set".
    apply CL_set.
    exists eqa eqb; dands; auto.
    { exists A A' v v' B B'; dands; auto. }
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_product".
    apply CL_product.
    exists eqa eqb; dands; auto.
    { exists A A' v v' B B'; dands; auto. }
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.
Qed.
Hint Resolve close_extensionality : slow.

Lemma type_extensionality_univi {o} :
  forall i, @type_extensionality o (univi i).
Proof.
  introv h e.
  allrw @univi_exists_iff; exrepnd.
  exists j; sp.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_univi : slow.

Lemma type_extensionality_univi_bar {o} :
  forall i, @type_extensionality o (univi_bar i).
Proof.
  introv h ext.
  unfold univi_bar, per_bar in *; exrepnd.
  exists bar eqa; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_univi_bar : slow.

Lemma type_extensionality_univ_ex {o} : @type_extensionality o univ_ex.
Proof.
  introv u e.
  unfold univ_ex in *; exrepnd; exists i.
  eapply type_extensionality_univi; eauto.
Qed.
Hint Resolve type_extensionality_univ_ex : slow.

Lemma type_extensionality_univ {o} : @type_extensionality o univ.
Proof.
  introv u e.
  unfold univ in *; exrepnd.
  unfold per_bar in *; exrepnd.
  exists bar eqa; dands;auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_univ : slow.
