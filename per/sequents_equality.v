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


Require Export sequents_tacs.
Require Export per_props_equality.



(* This lemma is useful to prove equalities *)
Lemma teq_and_eq_if_equality {o} :
  forall lib (A : @NTerm o) a b s1 s2 H wA wa wb ca1 ca2 cb1 cb2 cA1 cA2,
    hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> tequality lib (lsubstc A wA s1 cA1) (lsubstc A wA s2 cA2)
    -> (forall s1 s2 ca1 cb2 cA1,
          hyps_functionality lib s1 H
          -> similarity lib s1 s2 H
          -> equality lib (lsubstc a wa s1 ca1) (lsubstc b wb s2 cb2) (lsubstc A wA s1 cA1))
    -> (tequality lib
          (mkc_equality (lsubstc a wa s1 ca1) (lsubstc b wb s1 cb1) (lsubstc A wA s1 cA1))
          (mkc_equality (lsubstc a wa s2 ca2) (lsubstc b wb s2 cb2) (lsubstc A wA s2 cA2))
        # equality lib (lsubstc a wa s1 ca1) (lsubstc b wb s1 cb1) (lsubstc A wA s1 cA1)).
Proof.
  introv hf sim teq equs.

  assert (hyps_functionality lib s2 H)
    as hf2
      by (apply @similarity_hyps_functionality_trans with (s1 := s1); auto).

  assert (similarity lib s2 s1 H) as sim21 by (apply similarity_sym; auto).
  assert (similarity lib s1 s1 H) as sim11 by (apply similarity_refl in sim; auto).
  assert (similarity lib s2 s2 H) as sim22 by (apply similarity_refl in sim21; auto).

  dands.

  apply tequality_mkc_equality_if_equal; auto.

  generalize (equs s1 s2 ca1 cb2 cA1 hf sim); intro eq1.
  generalize (equs s2 s2 ca2 cb2 cA2 hf2 sim22); intro eq2.
  apply equality_trans with (t2 := lsubstc b wb s2 cb2); auto.
  apply equality_sym.
  apply @tequality_preserving_equality with (A := lsubstc A wA s2 cA2); auto.
  apply tequality_sym; auto.

  generalize (equs s1 s1 ca1 cb1 cA1 hf sim11); intro eq1.
  generalize (equs s1 s2 ca1 cb2 cA1 hf sim); intro eq2.
  apply equality_trans with (t2 := lsubstc a wa s1 ca1); auto.
  apply equality_sym; auto.

  apply equs; auto.
Qed.

Lemma teq_and_eq_if_equality2 {o} :
  forall lib (A : @NTerm o) a b s1 s2 H wA wa wb ca1 ca2 cb1 cb2 cA1 cA2,
    hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> tequality lib (lsubstc A wA s1 cA1) (lsubstc A wA s2 cA2)
    -> (forall s1 s2 ca1 cb2 cA1,
          hyps_functionality lib s1 H
          -> similarity lib s1 s2 H
          -> equality lib (lsubstc a wa s1 ca1) (lsubstc b wb s2 cb2) (lsubstc A wA s1 cA1))
    ->
    (
      tequality
        lib
        (mkc_equality (lsubstc a wa s1 ca1) (lsubstc b wb s1 cb1) (lsubstc A wA s1 cA1))
        (mkc_equality (lsubstc a wa s2 ca2) (lsubstc b wb s2 cb2) (lsubstc A wA s2 cA2))
      #
      equality
        lib
        (mkc_prefl (lsubstc a wa s1 ca1) (lsubstc a wa s1 ca1))
        (mkc_prefl (lsubstc a wa s2 ca2) (lsubstc a wa s2 ca2))
        (mkc_equality (lsubstc a wa s1 ca1) (lsubstc b wb s1 cb1) (lsubstc A wA s1 cA1))
    ).
Proof.
  introv hf sim teq equs.

  assert (hyps_functionality lib s2 H)
    as hf2 by (eapply @similarity_hyps_functionality_trans; eauto).

  assert (similarity lib s2 s1 H) as sim21 by (apply similarity_sym; auto).
  assert (similarity lib s1 s1 H) as sim11 by (apply similarity_refl in sim; auto).
  assert (similarity lib s2 s2 H) as sim22 by (apply similarity_refl in sim21; auto).

  dands.

  {
    apply tequality_mkc_equality_if_equal; auto.

    - pose proof (equs s1 s2 ca1 cb2 cA1 hf sim) as eq1.
      pose proof (equs s2 s2 ca2 cb2 cA2 hf2 sim22) as eq2.
      apply equality_trans with (t2 := lsubstc b wb s2 cb2); auto.
      apply equality_sym.
      apply @tequality_preserving_equality with (A := lsubstc A wA s2 cA2); auto.
      apply tequality_sym; auto.

    - pose proof (equs s1 s1 ca1 cb1 cA1 hf sim11) as eq1.
      pose proof (equs s1 s2 ca1 cb2 cA1 hf sim) as eq2.
      apply equality_trans with (t2 := lsubstc a wa s1 ca1); auto.
      apply equality_sym; auto.
  }

  {
    apply equality_in_mkc_equality.
    eexists; eexists; eexists; eexists; dands; spcast;
      try (complete (apply computes_to_valc_refl; eauto 2 with slow)).

    - pose proof (equs s1 s1 ca1 cb1 cA1) as q1; repeat (autodimp q1 hyp).
      eauto 3 with nequality slow.

    - pose proof (equs s2 s1 ca2 cb1 cA2) as q1; repeat (autodimp q1 hyp).
      apply equality_sym.
      eapply tequality_preserving_equality; eauto 2 with nequality.

    - pose proof (equs s1 s1 ca1 cb1 cA1) as q1; repeat (autodimp q1 hyp).

    - pose proof (equs s1 s2 ca1 cb2 cA1) as q1; repeat (autodimp q1 hyp).
      pose proof (equs s2 s2 ca2 cb2 cA2) as q2; repeat (autodimp q2 hyp).
      eapply tequality_preserving_equality in q2;[|apply tequality_sym;exact teq].
      eauto 3 with nequality slow.
  }
Qed.

(* This lemma is useful to prove membeships *)
Lemma teq_and_member_if_member {o} :
  forall lib (A : @NTerm o) a s1 s2 H wA wa ca1 ca2 cA1 cA2,
    hyps_functionality lib s1 H
    -> similarity lib s1 s2 H
    -> tequality lib (lsubstc A wA s1 cA1) (lsubstc A wA s2 cA2)
    -> (forall s1 s2 ca1 ca2 cA1,
          hyps_functionality lib s1 H
          -> similarity lib s1 s2 H
          -> equality lib (lsubstc a wa s1 ca1) (lsubstc a wa s2 ca2) (lsubstc A wA s1 cA1))
    -> (tequality lib
          (mkc_member (lsubstc a wa s1 ca1) (lsubstc A wA s1 cA1))
          (mkc_member (lsubstc a wa s2 ca2) (lsubstc A wA s2 cA2))
          # member lib (lsubstc a wa s1 ca1) (lsubstc A wA s1 cA1)).
Proof.
  introv hf sim teq mem.
  generalize (teq_and_eq_if_equality lib
                A a a s1 s2 H wA wa wa ca1 ca2 ca1 ca2 cA1 cA2
                hf sim teq mem); intro h; repnd; dands.

  {
    allrw @fold_mkc_member.
    auto.
  }

  allapply @equality_refl; sp.
Qed.

Ltac lsubst_tac_c :=
  lift_lsubst_concl;
  lsubstc_snoc;
  lift_lsubst_concl.

Ltac teq_and_eq T a b s1 s2 H :=
  let hyp := fresh "hyp" in
  match goal with
    | [ lib : library
      , wT  : wf_term T
      , wa  : wf_term a
      , wb  : wf_term b
      , ca1 : cover_vars a s1
      , ca2 : cover_vars a s2
      , cb1 : cover_vars b s1
      , cb2 : cover_vars b s2
      , cT1 : cover_vars T s1
      , cT2 : cover_vars T s2
      , hf  : hyps_functionality _ s1 H
      , sim : similarity _ s1 s2 H |- _ ] =>
      pose proof (teq_and_eq_if_equality
                    lib T a b s1 s2 H
                    wT wa wb ca1 ca2 cb1 cb2 cT1 cT2
                    hf sim) as hyp;
        lsubst_tac_h hyp;
        apply hyp;
        clear hyp;
        [|clear dependent s1;
           clear dependent s2;
           let hf := fresh "hf" in
           let sim := fresh "sim" in
           introv hf sim;
             lsubst_tac_c
        ]
  end.
