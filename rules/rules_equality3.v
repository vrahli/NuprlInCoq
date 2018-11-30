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


Require Export sequents2.
Require Export sequents_lib.
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

Lemma equality_base_implies_equality {o} :
  forall lib (x y T : @CTerm o),
     type lib T -> equality lib x y mkc_base -> member lib x T -> equality lib x y T.
Proof. 
   intros. 
   rw @equality_in_base_iff in H0.
   spcast.
   eapply equality_respects_cequivc_right; eauto.
Qed.

Lemma equality_mkc_equality_in_uni_equal_base {o} :
  forall (lib : library) (i : nat) (a1 a2 b1 b2 A B : @CTerm o),
  equality lib A B (mkc_uni i) ->
  equality lib a1 b1 A ->
  equality lib a2 b2 mkc_base ->
  equality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) (mkc_uni i) .
Proof. intros. dup H0 as h1. dup H0 as h2. 
       apply equality_refl in h1. apply equality_sym in h2. apply equality_refl in h2.
       dup H1 as e. apply equality_in_base in e. spcast.
       apply equality_mkc_equality2_sp_in_uni; dands; sp; try (split; intro).
       - pose proof (equality_respects_cequivc lib a2 b2 A e H2).
         apply equality_sym in H3. apply equality_refl in H3. auto.
       - apply cequivc_sym in e.
         pose proof (equality_respects_cequivc lib b2 a2 A e H2).
         apply equality_sym in H3. apply equality_refl in H3. auto.
       - apply equality_respects_cequivc; auto.
Qed.

Lemma equality_mkc_equality_in_uni_equal_equal {o} :
  forall (lib : library) (i : nat) (a1 a2 b1 b2 A B : @CTerm o),
  equality lib A B (mkc_uni i) ->
  equality lib a1 b1 A ->
  equality lib a2 b2 A ->
  equality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) (mkc_uni i) .
Proof. intros. dup H0 as h1. dup H0 as h2. 
       apply equality_refl in h1. apply equality_sym in h2. apply equality_refl in h2.
       dup H1 as r1. dup H1 as r2. 
       apply equality_refl in r1. apply equality_sym in r2. apply equality_refl in r2.
       
       apply equality_mkc_equality2_sp_in_uni; dands; sp; try (split; intro).
       
Qed.

Lemma equality_mkc_equality_in_uni_base_equal {o} :
  forall (lib : library) (i : nat) (a1 a2 b1 b2 A B : @CTerm o),
  equality lib A B (mkc_uni i) ->
  equality lib a1 b1 mkc_base ->
  equality lib a2 b2 A ->
  equality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) (mkc_uni i) .
Proof. intros. dup H1 as h1. dup H1 as h2. 
       apply equality_refl in h1. apply equality_sym in h2. apply equality_refl in h2.
       dup H0 as e. apply equality_in_base in e. spcast.
       apply equality_mkc_equality2_sp_in_uni; dands; sp; try (split; intro).
       - pose proof (equality_respects_cequivc lib a1 b1 A e H2).
         apply equality_sym in H3. apply equality_refl in H3. auto.
       - apply cequivc_sym in e.
         pose proof (equality_respects_cequivc lib b1 a1 A e H2).
         apply equality_sym in H3. apply equality_refl in H3. auto.
       - apply equality_respects_cequivc; auto.
Qed.

Lemma equality_mkc_equality_in_uni_base_base {o} :
  forall (lib : library) (i : nat) (a1 a2 b1 b2 A B : @CTerm o),
  equality lib A B (mkc_uni i) ->
  equality lib a1 b1 mkc_base ->
  equality lib a2 b2 mkc_base ->
  equality lib (mkc_equality a1 a2 A) (mkc_equality b1 b2 B) (mkc_uni i) .
Proof. intros. 
       apply equality_in_base in H0. spcast. 
       apply equality_in_base in H1. spcast.
       dup H0 as e0. apply cequivc_sym in e0.
       dup H1 as e1. apply cequivc_sym in e1.
       pose proof (equality_respects_cequivc lib a1 b1 A H0) as X0.
       pose proof (equality_respects_cequivc lib b1 a1 A e0) as Y0.
       pose proof (equality_respects_cequivc lib a2 b2 A H1) as X1.
       pose proof (equality_respects_cequivc lib b2 a2 A e1) as Y1.
       apply equality_mkc_equality2_sp_in_uni; dands; sp; try (split; intro).
       - apply X0 in H2.
         apply equality_sym in H2. apply equality_refl in H2. auto.
       - apply Y0 in H2.
         apply equality_sym in H2. apply equality_refl in H2. auto.
       - apply X1 in H2.
         apply equality_sym in H2. apply equality_refl in H2. auto.
       - apply Y1 in H2.
         apply equality_sym in H2. apply equality_refl in H2. auto.
       
Qed.



Definition rule_equality_equality_concl {o} (H : @bhyps o) a1 a2 b1 b2 A B i :=
  mk_baresequent
    H
    (mk_conclax (mk_equality
                   (mk_equality a1 a2 A)
                   (mk_equality b1 b2 B)
                   (mk_uni i))).

Definition rule_equality_equality_hyp1 {o} (H : @bhyps o) A B i e :=
  mk_baresequent H (mk_concl (mk_equality A B (mk_uni i)) e).

Definition rule_equality_equality_hyp2 {o} (H : @bhyps o) a b A e :=
  mk_baresequent H (mk_concl (mk_equality a b A) e).

(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEquality

     H |- A = B in U(i)
     H |- a1 = b1 in A
     H |- a2 = b2 in A
>>
 *)
Definition rule_equality_equality {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (i : nat) :=
  mk_rule
    (rule_equality_equality_concl H a1 a2 b1 b2 A B i)
    [ rule_equality_equality_hyp1 H A B i e1,
      rule_equality_equality_hyp2 H a1 b1 A e2,
      rule_equality_equality_hyp2 H a2 b2 A e3
    ]
    [].

Lemma rule_equality_equality_true3 {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true3 lib (rule_equality_equality H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  unfold rule_equality_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2 hyp3.
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; auto.
    - apply wf_axiom.
    - unfold closed_extract; simpl; auto.
  }
  exists wfc.
  destseq; simpl in *.

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
  vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as X; clear hyp1; exrepnd.
    lsubst_tac.
   vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as Y; clear hyp2; exrepnd.
      lsubst_tac.
   vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as Z; clear hyp3; exrepnd.
      lsubst_tac.
    rw @tequality_mkc_equality in X0; 
    rw @tequality_mkc_equality in Y0;
    rw @tequality_mkc_equality in Z0.
    apply equality_in_mkc_equality in X1;
    apply equality_in_mkc_equality in Y1;
    apply equality_in_mkc_equality in Z1.
    repnd.
    dup Z6 as ZZ1. apply equality_refl in ZZ1.
    dup Z6 as ZZ2. apply equality_sym in ZZ2. apply equality_refl in ZZ2.
    dimp Z4. auto. clear Z4.
    dimp Z0. auto. clear Z0.
    dup Y6 as YY1. apply equality_refl in YY1.
    dup Y6 as YY2. apply equality_sym in YY2. apply equality_refl in YY2.
    dimp Y4. auto. clear Y4.
    dimp Y0. auto. clear Y0.
    apply @equality_mkc_equality_in_uni_equal_equal.
    
   - eapply equality_trans. exact X6. apply X0.
     apply equality_sym in X6; apply equality_refl in X6; auto.
   - eapply equality_trans. exact Y6.  auto.
   - eapply equality_trans. exact Z6. auto.
 
Qed.

Lemma rule_equality_equality_true_ext_lib {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true_ext_lib lib (rule_equality_equality H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_equality_equality_true3.
Qed.

Lemma rule_equality_equality_wf2 {o} :
  forall (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    wf_rule2 (rule_equality_equality H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv wf m; allsimpl.
  repndors; subst; tcsp;
    allunfold @wf_bseq; allsimpl; repnd; dands; auto.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.
Qed.



Definition rule_equality_equality_hyp3 {o} (H : @bhyps o) a b e :=
  mk_baresequent H (mk_concl (mk_equality a b mk_base) e).

(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase

     H |- A = B in U(i)
     H |- a1 = b1 in Base
     H |- a2 = b2 in Base
>>
 *)
Definition rule_equality_equality_base {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (i : nat) :=
  mk_rule
    (rule_equality_equality_concl H a1 a2 b1 b2 A B i)
    [ rule_equality_equality_hyp1 H A B i e1,
      rule_equality_equality_hyp3 H a1 b1 e2,
      rule_equality_equality_hyp3 H a2 b2 e3
    ]
    [].

Lemma rule_equality_equality_base_true3 {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true3 lib (rule_equality_equality_base H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  unfold rule_equality_equality_base, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2 hyp3.
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; auto.
    - apply wf_axiom.
    - unfold closed_extract; simpl; auto.
  }
  exists wfc.
  destseq; simpl in *.

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
  vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as X; clear hyp1; exrepnd.
    lsubst_tac.
   vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as Y; clear hyp2; exrepnd.
      lsubst_tac.
   vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as Z; clear hyp3; exrepnd.
      lsubst_tac.
    rw @tequality_mkc_equality in X0; 
    rw @tequality_mkc_equality in Y0;
    rw @tequality_mkc_equality in Z0.
    apply equality_in_mkc_equality in X1;
    apply equality_in_mkc_equality in Y1;
    apply equality_in_mkc_equality in Z1.
    repnd.
    dimp Z0. apply member_base. clear Z0 Z5.
    dimp Z4. apply member_base. clear Z3 Z4.
    dup Y6 as YY1. apply equality_refl in YY1.
    dup Y6 as YY2. apply equality_sym in YY2. apply equality_refl in YY2.
    dimp Y4. auto. clear Y4.
    dimp Y0. auto. clear Y0.
    apply @equality_mkc_equality_in_uni_base_base.
    
   - eapply equality_trans. exact X6. apply X0.
     apply equality_sym in X6; apply equality_refl in X6; auto.
   - eapply equality_trans. exact Y6.  auto.
   - eapply equality_trans. exact Z6.  auto.
  
Qed.

Lemma rule_equality_equality_base_true_ext_lib {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true_ext_lib lib (rule_equality_equality_base H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_equality_equality_base_true3.
Qed.

Lemma rule_equality_equality_base_wf2 {o} :
  forall (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    wf_rule2 (rule_equality_equality_base H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv wf m; allsimpl.
  repndors; subst; tcsp;
    allunfold @wf_bseq; allsimpl; repnd; dands; auto.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.
Qed.


(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase1

     H |- A = B in U(i)
     H |- a1 = b1 in Base
     H |- a2 = b2 in A
>>
 *)
Definition rule_equality_equality_base1 {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (i : nat) :=
  mk_rule
    (rule_equality_equality_concl H a1 a2 b1 b2 A B i)
    [ rule_equality_equality_hyp1 H A B i e1,
      rule_equality_equality_hyp3 H a1 b1 e2,
      rule_equality_equality_hyp2 H a2 b2 A e3
    ]
    [].

Lemma rule_equality_equality_base1_true3 {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true3 lib (rule_equality_equality_base1 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  unfold rule_equality_equality_base1, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2 hyp3.
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; auto.
    - apply wf_axiom.
    - unfold closed_extract; simpl; auto.
  }
  exists wfc.
  destseq; simpl in *.

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
  vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as X; clear hyp1; exrepnd.
    lsubst_tac.
   vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as Y; clear hyp2; exrepnd.
      lsubst_tac.
   vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as Z; clear hyp3; exrepnd.
      lsubst_tac.
    rw @tequality_mkc_equality in X0; 
    rw @tequality_mkc_equality in Y0;
    rw @tequality_mkc_equality in Z0.
    apply equality_in_mkc_equality in X1;
    apply equality_in_mkc_equality in Y1;
    apply equality_in_mkc_equality in Z1.
    repnd.
    dimp Y0. apply member_base. clear Y0 Y5.
    dimp Y4. apply member_base. clear Y3 Y4.
    dup Z6 as ZZ1. apply equality_refl in ZZ1.
    dup Z6 as ZZ2. apply equality_sym in ZZ2. apply equality_refl in ZZ2.
    dimp Z4. auto. clear Z4.
    dimp Z0. auto. clear Z0.
    apply @equality_mkc_equality_in_uni_base_equal.
    
   - eapply equality_trans. exact X6. apply X0.
     apply equality_sym in X6; apply equality_refl in X6; auto.
   - eapply equality_trans. exact Y6.  auto.
   - eapply equality_trans. exact Z6. auto.
 
Qed.

Lemma rule_equality_equality_base1_true_ext_lib {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true_ext_lib lib (rule_equality_equality_base1 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_equality_equality_base1_true3.
Qed.

Lemma rule_equality_equality_base1_wf2 {o} :
  forall (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    wf_rule2 (rule_equality_equality_base1 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv wf m; allsimpl.
  repndors; subst; tcsp;
    allunfold @wf_bseq; allsimpl; repnd; dands; auto.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.
Qed.

(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEqualityBase2

     H |- A = B in U(i)
     H |- a1 = b1 in A
     H |- a2 = b2 in Base
>>
 *)
Definition rule_equality_equality_base2 {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
           (i : nat) :=
  mk_rule
    (rule_equality_equality_concl H a1 a2 b1 b2 A B i)
    [ rule_equality_equality_hyp1 H A B i e1,
      rule_equality_equality_hyp2 H a1 b1 A e2,
      rule_equality_equality_hyp3 H a2 b2 e3
    ]
    [].




Lemma rule_equality_equality_base2_true3 {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true3 lib (rule_equality_equality_base2 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  unfold rule_equality_equality_base2, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2 hyp3.
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; auto.
    - apply wf_axiom.
    - unfold closed_extract; simpl; auto.
  }
  exists wfc.
  destseq; simpl in *.

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
  vr_seq_true in hyp1.
    pose proof (hyp1 s1 s2 hf sim) as X; clear hyp1; exrepnd.
    lsubst_tac.
   vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as Y; clear hyp2; exrepnd.
      lsubst_tac.
   vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as Z; clear hyp3; exrepnd.
      lsubst_tac.
    rw @tequality_mkc_equality in X0; 
    rw @tequality_mkc_equality in Y0;
    rw @tequality_mkc_equality in Z0.
    apply equality_in_mkc_equality in X1;
    apply equality_in_mkc_equality in Y1;
    apply equality_in_mkc_equality in Z1.
    repnd.
    dimp Z0. apply member_base. clear Z0 Z5.
    dimp Z4. apply member_base. clear Z3 Z4.
    dup Y6 as YY1. apply equality_refl in YY1.
    dup Y6 as YY2. apply equality_sym in YY2. apply equality_refl in YY2.
    dimp Y4. auto. clear Y4.
    dimp Y0. auto. clear Y0.
    apply @equality_mkc_equality_in_uni_equal_base.
    
   - eapply equality_trans. exact X6. apply X0.
     apply equality_sym in X6; apply equality_refl in X6; auto.
   - eapply equality_trans. exact Y6.  auto.
   - apply equality_base_implies_equality. apply equality_refl in X6; auto.
       eapply equality_trans. exact Z6. auto.
       apply member_base.
 
Qed.

Lemma rule_equality_equality_base2_true_ext_lib {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    rule_true_ext_lib lib (rule_equality_equality_base2 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_equality_equality_base2_true3.
Qed.

Lemma rule_equality_equality_base2_wf2 {o} :
  forall (H : @barehypotheses o)
         (A B a1 a2 b1 b2 e1 e2 e3 : NTerm)
         (i : nat),
    wf_rule2 (rule_equality_equality_base2 H A B a1 a2 b1 b2 e1 e2 e3 i).
Proof.
  introv wf m; allsimpl.
  repndors; subst; tcsp;
    allunfold @wf_bseq; allsimpl; repnd; dands; auto.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.

  - allrw <- @wf_equality_iff; tcsp.

  - unfold closed_type_baresequent in *; simpl in *.
    unfold closed_type in *; simpl in *.
    allrw @covered_equality; tcsp.
Qed.
