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
  forall inh {ts : cts(o)},
    type_extensionality ts
    -> type_extensionality (close inh ts).
Proof.
  introv text cl.
  close_cases (induction cl using @close_ind') Case; introv ext.

  - Case "CL_init".
    apply CL_init.
    eapply text; eauto.

  - Case "CL_bar".
    apply CL_bar.
    unfold per_bar.
    exists eqa; dands; auto.
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

  - Case "CL_qnat".
    apply CL_qnat.
    unfold per_qnat in *; repnd; dands; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - Case "CL_csname".
    apply CL_csname.
    unfold per_csname in *; exrepnd; dands; auto.
    exists n; dands; auto.
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

  - Case "CL_qtime".
    apply CL_qtime.
    exists eqa A B; dands; auto.
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
  forall inh uni i, @type_extensionality o (univi i inh uni).
Proof.
  introv h e.
  allrw @univi_exists_iff; exrepnd.
  exists j; sp.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_univi : slow.

Lemma type_extensionality_univi_bar {o} :
  forall inh uni i, @type_extensionality o (univi_bar i inh uni).
Proof.
  introv h ext.
  unfold univi_bar, per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_univi_bar : slow.

(*Lemma type_extensionality_univ_ex {o} inh : @type_extensionality o (univ_ex inh).
Proof.
  introv u e.
  unfold univ_ex in *; exrepnd; exists i.
  eapply type_extensionality_univi; eauto.
Qed.
Hint Resolve type_extensionality_univ_ex : slow.*)

Lemma type_extensionality_univ {o} : @type_extensionality o univ.
Proof.
  introv u e.
  unfold univ, univi_ex_bar, per_bar in *; exrepnd.
  exists eqa; dands;auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_univ : slow.

Lemma type_extensionality_univi_ex_bar {o} :
  forall inh uni, @type_extensionality o (univi_ex_bar inh uni).
Proof.
  introv h ext.
  unfold univi_ex_bar, per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_univi_ex_bar : slow.

Lemma type_extensionality_univa {o} : forall i, @type_extensionality o (univa i).
Proof.
  introv u e.
  allrw @univa_iff; exrepnd.
  exists j; dands; tcsp.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_univa : slow.

Lemma type_extensionality_univa_ex {o} : @type_extensionality o univa_ex.
Proof.
  introv u e.
  unfold univa_ex in *; exrepnd.
  exists i; eauto 3 with slow.
  eapply type_extensionality_univa; eauto.
Qed.
Hint Resolve type_extensionality_univa_ex : slow.

Lemma type_extensionality_univa_ex_bar {o} :
  @type_extensionality o univa_ex_bar.
Proof.
  introv h ext.
  unfold univa_ex_bar, per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_univa_ex_bar : slow.

Lemma type_extensionality_univia {o} : @type_extensionality o univia.
Proof.
  introv u e.
  unfold univia, per_bar in *; exrepnd.
  exists eqa; dands; auto.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym; auto.
Qed.
Hint Resolve type_extensionality_univia : slow.

Lemma type_extensionality_nuprl {o} : @type_extensionality o nuprl.
Proof.
  introv u e.
  unfold nuprl in *; exrepnd.
  eapply close_extensionality; try exact u; auto; eauto 3 with slow.
Qed.
Hint Resolve type_extensionality_nuprl : slow.
