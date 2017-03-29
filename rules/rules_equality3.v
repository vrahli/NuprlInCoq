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


Require Export rules_useful.
Require Export per_props_equality.
Require Export per_props_union.
Require Export per_props_cequiv.
Require Export per_props_squash.
Require Export subst_tacs.
Require Export sequents_equality.
Require Export sequents_tacs2.


Lemma inhabited_mkc_or {o} :
  forall lib (A B : @CTerm o),
    inhabited_type lib (mkc_or A B)
    <=> (type lib A
         # type lib B
         # (inhabited_type lib A {+} inhabited_type lib B)).
Proof.
  introv.
  unfold inhabited_type.
  split; introv h; exrepnd.

  - apply equality_mkc_or in h0; exrepnd; dands; auto.
    repndors; exrepnd.

    + left; exists a1.
      apply equality_refl in h0; auto.

    + right; exists b1.
      apply equality_refl in h0; auto.

  - repndors; exrepnd.

    + exists (mkc_inl t).
      apply equality_mkc_or; dands; auto.
      left.
      exists t t; dands; auto; spcast;
      apply computes_to_valc_refl; eauto 3 with slow.

    + exists (mkc_inr t).
      apply equality_mkc_or; dands; auto.
      right.
      exists t t; dands; auto; spcast;
      apply computes_to_valc_refl; eauto 3 with slow.
Qed.


(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase

     H |- A = B in U(i)
     H |- squash(a1 = b1 in A \/ a1 ~ b1)
     H |- squash(a2 = b2 in A \/ a2 ~ b2)
>>
 *)
Definition rule_equality_equality_base_or {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 : NTerm)
           (i : nat) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_equality a1 a2 A)
                      (mk_equality b1 b2 B)
                      (mk_uni i))))
    [ mk_baresequent H (mk_conclax (mk_equality A B (mk_uni i))),
      mk_baresequent H (mk_conclax (mk_squash (mk_or (mk_equality a1 b1 A) (mk_cequiv a1 b1)))),
      mk_baresequent H (mk_conclax (mk_squash (mk_or (mk_equality a2 b2 A) (mk_cequiv a2 b2))))
    ]
    [].

Lemma rule_equality_equality_base_or_true {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 : NTerm)
         (i : nat),
    rule_true lib (rule_equality_equality_base_or H A B a1 a2 b1 b2 i).
Proof.
  unfold rule_equality_equality_base_or, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  exists (@covered_axiom o (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.
  lsubst_tac.
  rw <- @member_equality_iff.

  pose proof (teq_and_eq_if_equality
                lib (mk_uni i) (mk_equality a1 a2 A) (mk_equality b1 b2 B)
                s1 s2 H wT w1 w2 c1 c6 c2 c7 cT cT2
                eqh sim) as eqp.
  lsubst_tac.
  repeat (autodimp eqp hyp);[apply tequality_mkc_uni|].

  clear dependent s1.
  clear dependent s2.

  introv hf sim.
  lsubst_tac.
  apply equality_mkc_equality2_sp_in_uni; dands.

  - vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as h; clear hyp1; exrepnd.
    lsubst_tac.
    rw <- @member_equality_iff in h1.
    apply equality_commutes in h0; auto.

  - split.

    + vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply equality_in_mkc_squash in h1; repnd.
      clear h2 h3.
      rw @tequality_mkc_squash in h0.
      apply tequality_mkc_or in h0; repnd.
      rw @tequality_mkc_equality_sp in h2; repnd.
      allrw @fold_equorsq.
      apply inhabited_mkc_or in h1; repnd.

      repndors.

      * apply inhabited_mkc_equality in h1.
        eapply cequorsq_equality_trans2 in h1;[|eauto].
        left; auto.

      * rw @inhabited_cequiv in h1.
        destruct h2 as [d|d]; spcast.

        { eapply equality_respects_cequivc_left in d;[|apply cequivc_sym; eauto].
          left; auto. }

        { eapply cequivc_trans in d;[|eauto].
          right; spcast; auto. }

    + vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as h; clear hyp2; exrepnd.
      lsubst_tac.
      apply equality_in_mkc_squash in h1; repnd.
      clear h2 h3.
      rw @tequality_mkc_squash in h0.
      apply tequality_mkc_or in h0; repnd.
      rw @tequality_mkc_equality_sp in h2; repnd.
      allrw @fold_equorsq.
      apply inhabited_mkc_or in h1; repnd.

      repndors.

      * apply inhabited_mkc_equality in h1.
        eapply cequorsq_equality_trans2 in h1;[|eauto].
        left; auto.

      * rw @inhabited_cequiv in h1.
        destruct h2 as [d|d]; spcast.

        { eapply equality_respects_cequivc_left in d;[|apply cequivc_sym; eauto].
          left; auto. }

        { eapply cequivc_trans in d;[|eauto].
          right; spcast; auto. }
Qed.
