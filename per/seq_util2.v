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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export cequiv_cvterm.
Require Export seq_util.


Definition const_seq {o} (n : nat) : @CTerm o := mkc_lam nvarx (mk_cv [nvarx] (mkc_nat n)).

Definition emseqc {o} : @CTerm o := const_seq 0.

Definition eq_seq {o} lib (s1 s2 : @CTerm o) :=
  equality lib s1 s2 nat2nat.

Lemma eq_seq_implies_eq_kseq {o} :
  forall lib (s1 s2 : @CTerm o),
    eq_seq lib s1 s2
    -> forall n, eq_kseq lib s1 s2 n.
Proof.
  introv e; introv.
  unfold eq_kseq.
  unfold eq_seq in e.
  apply equality_nat2nat_to_natk2nat; auto.
  apply nat_in_nat.
Qed.

Lemma seq2kseq_prop1 {o} :
  forall lib (s1 s2 : @CTerm o) n v,
    eq_kseq lib s1 s2 n
    -> eq_kseq lib (seq2kseq s1 n v) (seq2kseq s2 n v) n.
Proof.
  introv equ.
  apply implies_equality_natk2nat.
  introv ltm.
  apply (equality_natk2nat_implies _ m) in equ; auto; exrepnd.
  exists k.
  dands.

  - apply cequivc_nat_implies_computes_to_valc.
    unfold seq2kseq.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_less_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_bot_substc.
    allrw @csubst_mk_cv.
    allrw @mkcv_nat_substc.
    allrw @mkcv_zero_substc.
    allrw @mkc_zero_eq.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega.
    apply computes_to_valc_implies_cequivc; auto.

  - apply cequivc_nat_implies_computes_to_valc.
    unfold seq2kseq.
    eapply cequivc_trans;[apply cequivc_beta|].
    allrw @mkcv_less_substc.
    allrw @mkcv_apply_substc.
    allrw @mkc_var_substc.
    allrw @mkcv_bot_substc.
    allrw @csubst_mk_cv.
    allrw @mkcv_nat_substc.
    allrw @mkcv_zero_substc.
    allrw @mkc_zero_eq.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega.
    eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
    boolvar; try omega.
    apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma seq2kseq_prop2 {o} :
  forall lib v (s1 s2 : @CTerm o) n,
    eq_kseq lib s1 s2 n
    -> cequivc lib (seq2kseq s1 n v) (seq2kseq s2 n v).
Proof.
  introv equ.
  apply implies_cequivc_lam.
  introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  apply implies_cequivc_mkc_less1.
  introv compu.
  allrw @mkc_zero_eq.
  allrw (@mkc_nat_eq o 0).

  eapply cequivc_trans;[apply cequivc_mkc_less_int|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_int].
  boolvar; auto.

  eapply cequivc_trans;
    [apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    ].

  apply Wf_Z.Z_of_nat_complete_inf in l; exrepnd; subst; fold_terms.
  allrw <- @mkc_nat_eq.

  eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_nat].

  boolvar; auto.

  eapply cequivc_trans;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact compu]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact compu]
    ].

  apply (equality_natk2nat_implies _ n0) in equ; auto.
  exrepnd.
  eapply cequivc_trans;
    [apply computes_to_valc_implies_cequivc;exact equ1
    |apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact equ0].
Qed.

Definition is_kseq {o} lib (s : @CTerm o) (n : nat) := eq_kseq lib s s n.

Definition is_seq {o} lib (s : @CTerm o) := member lib s nat2nat.

Lemma eq_kseq_0 {o} :
  forall lib (s1 s2 : @CTerm o),
    eq_kseq lib s1 s2 0.
Proof.
  introv.
  unfold eq_kseq, natk2nat.
  apply equality_in_fun; dands; eauto 3 with slow.

  { apply type_mkc_natk.
    exists 0%Z; spcast.
    apply computes_to_valc_refl; eauto 3 with slow. }

  introv e.
  apply equality_in_natk in e; exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in e3; eauto 3 with slow.
  allrw @mkc_nat_eq; ginv; omega.
Qed.

Lemma is_kseq_0 {o} : forall lib (t : @CTerm o), is_kseq lib t 0.
Proof.
  introv.
  apply eq_kseq_0.
Qed.

Lemma eq_kseq_update {o} :
  forall lib (s1 s2 : @CTerm o) (n m : nat) (v : NVar),
    eq_kseq lib s1 s2 n
    -> eq_kseq lib (update_seq s1 n m v) (update_seq s2 n m v) (S n).
Proof.
  introv i.
  allunfold @eq_kseq.
  unfold update_seq.
  apply implies_equality_natk2nat.
  introv ltm0.

  destruct (deq_nat m0 n) as [d|d]; subst.

  - exists m.
    dands.

    + apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp.

    + apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp.

  - pose proof (equality_natk2nat_implies lib m0 s1 s2 n) as h.
    repeat (autodimp h hyp); try omega.
    exrepnd.
    exists k.
    dands.

    + apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC.
      apply computes_to_valc_implies_cequivc; auto.

    + apply cequivc_nat_implies_computes_to_valc.
      eapply cequivc_trans;[apply cequivc_beta|].
      allrw @mkcv_inteq_substc.
      allrw @mkcv_apply_substc.
      allrw @mkc_var_substc.
      allrw @csubst_mk_cv.
      eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
      boolvar; tcsp; GC.
      apply computes_to_valc_implies_cequivc; auto.
Qed.

Lemma is_kseq_update {o} :
  forall lib (s : @CTerm o) (n m : nat) (v : NVar),
    is_kseq lib s n
    -> is_kseq lib (update_seq s n m v) (S n).
Proof.
  introv i.
  apply eq_kseq_update; auto.
Qed.

Lemma eq_kseq_implies {o} :
  forall lib m (s1 s2 : @CTerm o) n,
    m < n
    -> eq_kseq lib s1 s2 n
    -> {k : nat
        & computes_to_valc lib (mkc_apply s1 (mkc_nat m)) (mkc_nat k)
        # computes_to_valc lib (mkc_apply s2 (mkc_nat m)) (mkc_nat k)}.
Proof.
  introv ltm i.
  unfold eq_kseq in i.
  eapply equality_natk2nat_implies in i;[|exact ltm]; auto.
Qed.

Lemma is_kseq_implies {o} :
  forall lib m (s : @CTerm o) n,
    m < n
    -> is_kseq lib s n
    -> {k : nat & computes_to_valc lib (mkc_apply s (mkc_nat m)) (mkc_nat k)}.
Proof.
  introv ltm i.
  unfold is_kseq in i.
  eapply member_natk2nat_implies in i;[|exact ltm]; auto.
Qed.

Lemma cequivc_beta_nseq {o} :
  forall (lib : @library o) s n,
    cequivc lib (mkc_apply (mkc_nseq s) (mkc_nat n)) (mkc_nat (s n)).
Proof.
  introv.
  unfold cequivc; simpl.
  apply reduces_to_implies_cequiv;
    [apply isprogram_apply;eauto 3 with slow;apply isprogram_mk_nseq|].
  eapply reduces_to_if_split2;[csunf;simpl;auto|].
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl.
  boolvar; try omega.
  rw Znat.Nat2Z.id; auto.
Qed.

Lemma is_seq_nseq {o} :
  forall (lib : @library o) s, is_seq lib (mkc_nseq s).
Proof.
  introv.
  apply member_nseq_nat2nat.
Qed.
Hint Resolve is_seq_nseq : slow.

Lemma eq_seq_nseq {o} :
  forall (lib : @library o) s, eq_seq lib (mkc_nseq s) (mkc_nseq s).
Proof.
  introv.
  apply member_nseq_nat2nat.
Qed.
Hint Resolve eq_seq_nseq : slow.

Lemma is_kseq_nseq {o} :
  forall (lib : @library o) s n, is_kseq lib (mkc_nseq s) n.
Proof.
  introv.
  pose proof (is_seq_nseq lib s) as h.
  apply equality_nat2nat_to_natk2nat; auto.
  apply nat_in_nat.
Qed.
Hint Resolve is_kseq_nseq : slow.

Lemma implies_is_kseq_seq2kseq {o} :
  forall lib (s : @CTerm o) m v,
    is_kseq lib s m
    -> is_kseq lib (seq2kseq s m v) m.
Proof.
  introv i.
  apply seq2kseq_prop1; auto.
Qed.


Lemma seq_normalizable_update {o} :
  forall lib (s : @CTerm o) n k v,
    seq_normalizable lib s n v
    -> seq_normalizable lib (update_seq s n k v) (S n) v.
Proof.
  introv norm.
  allunfold @seq_normalizable.

  unfold update_seq, seq2kseq.
  apply implies_cequivc_lam.
  introv.
  allrw @mkcv_inteq_substc.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_trans;
    [|apply cequivc_mkc_less;
       [apply cequivc_refl
       |apply cequivc_refl
       |apply cequivc_refl
       |apply cequivc_mkc_less;
         [apply cequivc_refl
         |apply cequivc_refl
         |apply cequivc_sym;apply cequivc_beta
         |apply cequivc_refl]
       ]
    ].
  allrw @mkcv_inteq_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.

  eapply cequivc_trans;
    [apply cequivc_mkc_inteq;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply implies_cequivc_apply;
        [exact norm|apply cequivc_refl]
      ]
    |].
  unfold seq2kseq.

  eapply cequivc_trans;
    [apply cequivc_mkc_inteq;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_beta]
    |].
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_trans;
    [allrw @mkc_zero_eq; apply cequivc_inteq_less_swap1; try omega|].
  allrw <- @mkc_zero_eq.

  apply implies_cequivc_mkc_less1.
  introv compu.
  allrw @mkc_zero_eq.
  allrw @mkc_nat_eq.

  eapply cequivc_trans;
    [apply cequivc_mkc_less_int|].
  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less_int].
  boolvar; tcsp.
  apply Wf_Z.Z_of_nat_complete_inf in l; exrepnd; subst; fold_terms.
  allrw <- @mkc_nat_eq.

  eapply cequivc_trans;
    [apply cequivc_mkc_inteq;
      [apply computes_to_valc_implies_cequivc; exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_less;
        [apply computes_to_valc_implies_cequivc; exact compu
        |apply cequivc_refl
        |apply cequivc_refl
        |apply cequivc_refl]
      ]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
       [apply computes_to_valc_implies_cequivc; exact compu
       |apply cequivc_refl
       |apply cequivc_mkc_inteq;
         [apply computes_to_valc_implies_cequivc; exact compu
         |apply cequivc_refl
         |apply cequivc_refl
         |apply cequivc_refl]
       |apply cequivc_refl
       ]
    ].

  eapply cequivc_trans;
    [apply cequivc_inteq_less_swap1; try omega|].

  eapply cequivc_trans;
    [apply cequivc_mkc_less;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_inteq_nat]
    |].

  eapply cequivc_trans;
    [apply cequivc_mkc_less_nat|].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_inteq_nat
      |apply cequivc_refl]
    ].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less_nat].

  boolvar; subst; tcsp; try omega.
Qed.

Lemma eq_kseq_seq2kseq_0 {o} :
  forall lib v (s1 s2 : @CTerm o),
    eq_kseq lib (seq2kseq s1 0 v) (seq2kseq s2 0 v) 0.
Proof.
  introv.
  apply implies_equality_natk2nat.
  introv ltm; omega.
Qed.

Lemma cequivc_seq2kseq_0 {o} :
  forall lib v (s1 s2 : @CTerm o),
    cequivc lib (seq2kseq s1 0 v) (seq2kseq s2 0 v).
Proof.
  introv.
  eapply cequivc_trans;[apply cequivc_seq2kseq_twice|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_seq2kseq_twice].
  apply seq2kseq_prop2.
  apply eq_kseq_seq2kseq_0.
Qed.

Lemma implies_cequivc_seq2kseq {o} :
  forall lib v n (s1 s2 : @CTerm o),
    cequivc lib s1 s2
    -> cequivc lib (seq2kseq s1 n v) (seq2kseq s2 n v).
Proof.
  introv ceq.
  unfold seq2kseq.
  apply implies_cequivc_lam; introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_bot_substc.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_mkc_less;
    [apply cequivc_refl
    |apply cequivc_refl
    |apply cequivc_refl
    |eapply cequivc_mkc_less;
      [apply cequivc_refl
      |apply cequivc_refl
      |apply sp_implies_cequivc_apply;auto
      |apply cequivc_refl]
    ].
Qed.

Lemma cequivc_update_seq {o} :
  forall lib (s1 s2 : @CTerm o) n m v,
    cequivc lib s1 s2
    -> cequivc lib (update_seq s1 n m v) (update_seq s2 n m v).
Proof.
  introv ceq.

  unfold update_seq.
  apply implies_cequivc_lam; introv.
  allrw @mkcv_inteq_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.

  eapply cequivc_mkc_inteq;
    [apply cequivc_refl
    |apply cequivc_refl
    |apply cequivc_refl
    |apply sp_implies_cequivc_apply;auto].
Qed.

Lemma is_kseq_seq2kseq_0 {o} :
  forall lib v (s : @CTerm o),
    is_kseq lib (seq2kseq s 0 v) 0.
Proof.
  introv.
  apply implies_equality_natk2nat.
  introv ltm; omega.
Qed.

Lemma cequivc_preserves_eq_kseq_left {o} :
  forall lib (s s1 s2 : @CTerm o) n,
    cequivc lib s1 s2
    -> eq_kseq lib s1 s n
    -> eq_kseq lib s2 s n.
Proof.
  introv ceq ek.
  allunfold @eq_kseq.
  eapply equality_respects_cequivc_left;[|exact ek]; auto.
Qed.

Lemma cequivc_preserves_eq_kseq_right {o} :
  forall lib (s s1 s2 : @CTerm o) n,
    cequivc lib s1 s2
    -> eq_kseq lib s s1 n
    -> eq_kseq lib s s2 n.
Proof.
  introv ceq ek.
  allunfold @eq_kseq.
  eapply equality_respects_cequivc_right;[|exact ek]; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/")
*** End:
*)
