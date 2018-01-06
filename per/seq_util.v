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


Require Export cequiv_seq_util.
Require Export sequents_tacs2.
(*Require Export per_props4.*)
Require Export per_can.
Require Export per_props_atom.
Require Export per_props_ffatom.
Require Export per_props_squash.
Require Export per_props_nat2.
Require Export per_props_natk2nat.


(* !!MOVE *)
Lemma member_mkc_squash {p} :
  forall lib (T : @CTerm p),
    member lib mkc_axiom (mkc_squash T)
    <=> inhabited_type lib T.
Proof.
  intros.
  rw @equality_in_mkc_squash.
  split; intro h; repnd; dands; auto; spcast;
  apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Lemma equality_in_nout {o} :
  forall lib (a b : @CTerm o),
    equality lib a b mkc_nout
    <=> {u : CTerm
         , noutokensc u
         # ccequivc lib a u
         # ccequivc lib b u}.
Proof.
  introv.
  unfold mkc_nout.
  rw @equality_in_set.
  split; intro h; repnd.

  - allrw @mkcv_ffatoms_substc.
    allrw @mkc_var_substc.
    apply inhabited_free_from_atoms in h; exrepnd.
    allrw @equality_in_base_iff; spcast.
    exists u; dands; spcast; auto.
    eapply cequivc_trans;[|eauto].
    apply cequivc_sym; auto.

  - exrepnd.
    dands.

    + introv equ.
      allrw @equality_in_base_iff; spcast.
      allrw @mkcv_ffatoms_substc.
      allrw @mkc_var_substc.
      unfold mkc_ffatoms.
      apply tequality_free_from_atoms; dands; eauto 3 with slow.
      apply equality_in_base_iff; spcast; auto.

    + spcast.
      apply equality_in_base_iff; spcast; auto.
      eapply cequivc_trans;[eauto|].
      apply cequivc_sym; auto.

    + spcast.
      allrw @mkcv_ffatoms_substc.
      allrw @mkc_var_substc.
      unfold mkc_ffatoms.
      apply inhabited_free_from_atoms.
      exists u; dands; eauto 3 with slow.

      * apply tequality_base.

      * apply equality_in_base_iff; spcast; auto.
Qed.

Lemma type_mkc_nout {o} :
  forall lib, @type o lib mkc_nout.
Proof.
  introv.
  unfold mkc_nout.
  apply tequality_set; dands; auto.
  introv eb.
  allrw @mkcv_ffatoms_substc.
  allrw @mkc_var_substc.
  unfold mkc_ffatoms.
  apply tequality_free_from_atoms; dands; eauto 3 with slow.
Qed.
Hint Resolve type_mkc_nout : slow.

Lemma tequality_natk2nout {o} :
  forall lib (a b : @CTerm o),
    tequality lib (natk2nout a) (natk2nout b)
     <=> {k1 : Z
          , {k2 : Z
          , (a) ===>(lib) (mkc_integer k1)
          # (b) ===>(lib) (mkc_integer k2)
          # (forall k : Z,
               (0 <= k)%Z ->
               ((k < k1)%Z # (k < k2)%Z){+}(k1 <= k)%Z # (k2 <= k)%Z)}}.
Proof.
  introv.
  unfold natk2nout.
  rw @tequality_mkc_fun.
  rw @tequality_mkc_natk.
  split; intro k; exrepnd; dands; eauto 3 with slow.

  - spcast; exists k1 k0; dands; spcast; auto.

  - spcast; exists k1 k2; dands; spcast; auto.

  - introv inh; apply type_mkc_nout.
Qed.

Lemma tequality_natk2nout_nat {o} :
  forall lib n,
    @tequality o lib (natk2nout (mkc_nat n)) (natk2nout (mkc_nat n)).
Proof.
  introv.
  apply tequality_natk2nout.
  exists (Z.of_nat n) (Z.of_nat n).
  dands; spcast; try (apply computes_to_valc_refl; eauto 3 with slow).
  introv ltk.
  destruct (Z_lt_le_dec k (Z.of_nat n)); sp.
Qed.
Hint Resolve tequality_natk2nout_nat : slow.

Lemma type_nat2nout {o} :
  forall (lib : @library o), type lib nat2nout.
Proof.
  introv.
  unfold nat2nout.
  apply type_mkc_fun; dands; eauto 3 with slow.
Qed.
Hint Resolve type_nat2nout : slow.

(* ========================== *)

(* ========================== *)


Definition eq_kseq {o} lib (s1 s2 : @CTerm o) (n : nat) :=
  equality lib s1 s2 (natk2nat (mkc_nat n)).

Lemma eq_kseq_left {o} :
  forall lib (seq1 seq2 : @CTerm o) k,
    eq_kseq lib seq1 seq2 k
    -> eq_kseq lib seq1 seq1 k.
Proof.
  introv e.
  apply equality_refl in e; auto.
Qed.

Definition fun_sim_eq {o} lib s1 H (t : @NTerm o) w (u : CTerm) :=
  {s2 : CSub
   & {c2 : cover_vars t s2
   & similarity lib s1 s2 H
   # u = lsubstc t w s2 c2}}.
