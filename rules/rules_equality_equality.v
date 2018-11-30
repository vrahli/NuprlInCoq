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


Require Export rules_equality3.


Definition rule_equality_equality_concl {o} (H : @bhyps o) a1 a2 b1 b2 A B i :=
  mk_baresequent
    H
    (mk_conclax (mk_equality
                   (mk_equality a1 a2 A)
                   (mk_equality b1 b2 B)
                   (mk_uni i))).

Definition rule_equality_equality_hyp1 {o} (H : @bhyps o) A B i :=
  mk_baresequent H (mk_conclax (mk_equality A B (mk_uni i))).

Definition rule_equality_equality_hyp2 {o} (H : @bhyps o) a b X :=
  mk_baresequent H (mk_conclax (mk_equality a b X)).

Definition rule_equality_equality_hyp3 {o} (H : @bhyps o) 
           (X A: @NTerm o) x y z u :=
  let eqA := mk_equality (mk_var x) (mk_var y) A in
  let xA := mk_member (mk_var x) A in
  let yA := mk_member (mk_var y) A in
  let eqX:= mk_equality (mk_var x) (mk_var y) X in
  let J :=  snoc (snoc (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base)) (mk_hyp u xA)) (mk_hyp z eqX)  in
  mk_baresequent J (mk_conclax eqA).

(**

<<
   H |- (a1 = a2 in A) = (b1 = b2 in B) in U(i)

     By equalityEquality

     H |- A = B in U(i)
     H |- a1 = b1 in X
     H |- a2 = b2 in Y
    H x:Base, y:Base, u: x in A, z: x=y in X |- x=y in A
    H x:Base, y:Base, u: x in A, z: x=y in Y |- x=y in A
>>
 *)
Definition rule_equality_equality {o}
           (H  : @barehypotheses o)
           (A B a1 a2 b1 b2 X Y: NTerm)
           (x y z u : NVar)
           (i : nat) :=
  mk_rule
    (rule_equality_equality_concl H a1 a2 b1 b2 A B i)
    [ rule_equality_equality_hyp1 H A B i,
      rule_equality_equality_hyp2 H a1 b1 X,
      rule_equality_equality_hyp2 H a2 b2 Y,
      rule_equality_equality_hyp3 H X A x y z u,
      rule_equality_equality_hyp3 H Y A x y z u
    ]
    [].

Lemma rule_equality_equality_true3 {o} :
  forall lib (H : @barehypotheses o)
         (A B a1 a2 b1 b2 X Y : NTerm)
         (x y z u : NVar)
         (i : nat),
    ! LIn x (vars_hyps H) ->
    ! LIn y (vars_hyps H) ->
    ! LIn z (vars_hyps H) ->
    ! LIn u (vars_hyps H) ->
    ! (x = y) ->
    ! (x = u) ->
    ! (y = u) ->
    rule_true3 lib (rule_equality_equality H A B a1 a2 b1 b2 X Y x y z u i).
Proof.
  unfold rule_equality_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs. rename H5 into xneu. rename H6 into yneu.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destruct Hyp2 as [wf4 hyp4].
  destruct Hyp3 as [wf5 hyp5].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc
  end.
  {
    clear hyp1 hyp2 hyp3.
    unfold wf_csequent, wf_sequent, wf_concl; simpl.
    dands; auto.
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
    pose proof (hyp1 s1 s2 hf sim) as eU; exrepnd.
    lsubst_tac.
  assert (forall sa sb w1 w2 c1 c2,
            hyps_functionality lib sa H ->
            similarity lib sa sb H ->
            tequality lib (lsubstc A w1 sa c1) (lsubstc A w2 sb c2)) as Atype.
   { intros. pose proof (hyp1 sa sb H5 H6) as xx. exrepnd. lsubst_tac.
     eapply equality_in_uni.
     rw @tequality_mkc_equality in xx0. repnd.
     apply xx4. apply equality_in_mkc_equality in xx1. repnd.
     apply equality_refl in xx6. auto.
   }
   clear hyp1.
   vr_seq_true in hyp2.
      pose proof (hyp2 s1 s2 hf sim) as eX;  exrepnd.
      lsubst_tac.
   assert (forall sa sb w1 w2 c1 c2,
            hyps_functionality lib sa H ->
            similarity lib sa sb H ->
            tequality lib (lsubstc X w1 sa c1) (lsubstc X w2 sb c2)) as Xtype.
   { intros. pose proof (hyp2 sa sb H5 H6) as xx. exrepnd. lsubst_tac.
      rw @tequality_mkc_equality in xx0. sp.
   }
   clear hyp2.
   vr_seq_true in hyp3.
      pose proof (hyp3 s1 s2 hf sim) as eY; exrepnd.
      lsubst_tac.
   assert (forall sa sb w1 w2 c1 c2,
            hyps_functionality lib sa H ->
            similarity lib sa sb H ->
            tequality lib (lsubstc Y w1 sa c1) (lsubstc Y w2 sb c2)) as Ytype.
   { intros. pose proof (hyp3 sa sb H5 H6) as xx. exrepnd. lsubst_tac.
      rw @tequality_mkc_equality in xx0. sp.
   }
   clear hyp3.
    rw @tequality_mkc_equality in eU0; 
    rw @tequality_mkc_equality in eX0;
    rw @tequality_mkc_equality in eY0.
    apply equality_in_mkc_equality in eU1;
    apply equality_in_mkc_equality in eX1;
    apply equality_in_mkc_equality in eY1.
    repnd.
    apply equality_mkc_equality2_sp_in_uni.
    split.
    { eapply equality_trans. exact eU6. apply eU0. 
     apply equality_sym in eU6. apply equality_refl in eU6.
     auto.
    }
    clear dependent B.
    pose proof (subvars_if_cover_vars_sim lib A s1 s2 H cT sim) as AsubH.
    rw subvars_eq in AsubH.
    pose proof (subvars_if_cover_vars_sim lib X s1 s2 H cT2 sim) as XsubH.
    rw subvars_eq in XsubH.
    pose proof (subvars_if_cover_vars_sim lib Y s1 s2 H cT4 sim) as YsubH.
    rw subvars_eq in YsubH.
    assert (! LIn x (free_vars A)).
     { intro. apply H0. eapply AsubH. auto. }
    assert (! LIn y (free_vars A)).
     { intro. apply H1. eapply AsubH. auto. }
    assert (! LIn z (free_vars A)).
     { intro. apply H2. eapply AsubH. auto. }
    assert (! LIn u (free_vars A)).
     { intro. apply H3. eapply AsubH. auto. }
    assert (! LIn x (free_vars X)).
     { intro. apply H0. eapply XsubH. auto. }
    assert (! LIn y (free_vars X)).
     { intro. apply H1. eapply XsubH. auto. }
    assert (! LIn z (free_vars X)).
     { intro. apply H2. eapply XsubH. auto. }
    assert (! LIn u (free_vars X)).
     { intro. apply H3. eapply XsubH. auto. }
    assert (! LIn x (free_vars Y)).
     { intro. apply H0. eapply YsubH. auto. }
    assert (! LIn y (free_vars Y)).
     { intro. apply H1. eapply YsubH. auto. }
    assert (! LIn z (free_vars Y)).
     { intro. apply H2. eapply YsubH. auto. }
    assert (! LIn u (free_vars Y)).
     { intro. apply H3. eapply YsubH. auto. }
    assert (forall x0 y0, hyps_functionality lib (snoc (snoc s1 (x, x0)) (y, y0)) 
                                       (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base))).
         { intros. apply hyps_functionality_snoc2;  simpl; intros; lsubst_tac; auto.
          apply hyps_functionality_snoc2;  simpl; intros; lsubst_tac; auto. }
    assert (forall x0 y0, 
             member lib x0 (lsubstc A wT0 s1 cT) ->
             hyps_functionality lib (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (u, mkc_axiom))
                                       (snoc (snoc (snoc H (mk_hyp x mk_base)) (mk_hyp y mk_base)) 
                                        (mk_hyp u (mk_member (mk_var x) A)))).
         { intros. apply hyps_functionality_snoc2;  simpl; intros; lsubst_tac; auto.
           rw @similarity_snoc in H20. exrepnd. simpl in H20.
           apply snoc_inj in H21.
           rw @similarity_snoc in H23. exrepnd. simpl in H23. 
           simpl in H22.
           simpl in H26.
           simpl in H25.
           assert (snoc s1 (x, x0) = snoc s1a0 (x, t0)). rw H24. auto.
           apply snoc_inj in H28. repnd.
           assert (s' = snoc (snoc s2a0 (x, t3)) (y, t2)). rw H22. rw H26. auto.
           lsubst_tac.
           inversion H28.
           rw H32 in H24.
           assert ((lsubstc (mk_var x) wt s' ct4) = t3).
           { proof_irr. lsubst_tac. auto. }
           rw H31. apply equality_in_base in H23. spcast.
           apply tequality_mkc_member_if_cequivc. split; auto.
           proof_irr. lsubst_tac.
           apply Atype; auto.
           }
    assert (forall x y, 
     equality lib x y (lsubstc X wT2 s1 cT2) ->
     member lib x (lsubstc A wT0 s1 cT) ->
     equality lib x y  (lsubstc A wT0 s1 cT)) as XA.
    {intros. 
     vr_seq_true in hyp4.
      pose proof (hyp4 (snoc (snoc (snoc (snoc s1 (x,x0)) (y,y0)) (u,mkc_axiom)) (z,mkc_axiom)) 
                       (snoc (snoc (snoc (snoc s2 (x,x0)) (y,y0)) (u,mkc_axiom)) (z,mkc_axiom))  ) 
                  as eY; clear hyp4; exrepnd.
      dimp eY.
      { apply hyps_functionality_snoc2;  simpl; intros; lsubst_tac; auto.
        proof_irr.
        rw @similarity_snoc in H22. exrepnd. simpl in H22. simpl in H24. simpl in H23. 
        lsubst_tac.
        rw @similarity_snoc in H25. exrepnd. simpl in H24. simpl in H25. simpl in H26.
        rw @similarity_snoc in H27. exrepnd. simpl in H27. simpl in H28. simpl in H29.
        assert ( s2a = snoc (snoc s2a1 (x, t5)) (y, t3)).
         {rw <- H29. auto. }
        proof_irr. lsubst_tac.
        apply snoc_inj in H23. destruct H23.
        apply snoc_inj in e. destruct e. inversion e1. clear e1.
        apply snoc_inj in e. destruct e. inversion e1. clear e1.
        apply equality_in_base in H25. spcast.
        apply equality_in_base in H27. spcast.
        apply tequality_equality_if_cequivc; auto.
        apply Xtype; auto. 
        rw e.
        auto.
      } 
      { exrepnd. lsubst_tac.  rw @equality_in_mkc_equality in hyp1. sp. }
      { (* similarity *)
        apply similarity_snoc. simpl.
        exists  (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (u, mkc_axiom)).
        exists  (snoc (snoc (snoc s2 (x, x0)) (y, y0)) (u, mkc_axiom)).
        exists (@mkc_axiom o) (@mkc_axiom o).
        eexists. eexists. sp.
        apply similarity_snoc. simpl.
        exists  ((snoc (snoc s1 (x, x0)) (y, y0))).
        exists  ((snoc (snoc s2 (x, x0)) (y, y0))).
        exists (@mkc_axiom o) (@mkc_axiom o).
        eexists. eexists. sp.
        apply similarity_snoc. simpl.
        exists  (( (snoc s1 (x, x0)))).
        exists  (((snoc s2 (x, x0)))).
        exists y0 y0.
        eexists. eexists. sp.
        apply similarity_snoc. simpl.
        exists s1 s2 x0 x0.
        eexists. eexists. sp.
        (* four equalities to prove *)
        - lsubst_tac. apply equality_in_base_iff. spcast. apply cequivc_refl.
        - lsubst_tac. apply equality_in_base_iff. spcast. apply cequivc_refl.
        - lsubst_tac. rw <- @fold_mkc_member. rw @equality_in_mkc_equality. sp.
        - lsubst_tac. rw @equality_in_mkc_equality. sp.
       }
    }
   assert (forall x y, 
     equality lib x y (lsubstc Y wT3 s1 cT4) ->
     member lib x (lsubstc A wT0 s1 cT) ->
     equality lib x y  (lsubstc A wT0 s1 cT)) as YA.
   {intros. 
     vr_seq_true in hyp5.
      pose proof (hyp5 (snoc (snoc (snoc (snoc s1 (x,x0)) (y,y0)) (u,mkc_axiom)) (z,mkc_axiom)) 
                       (snoc (snoc (snoc (snoc s2 (x,x0)) (y,y0)) (u,mkc_axiom)) (z,mkc_axiom))  ) as eY; clear hyp4; exrepnd.
      dimp eY.
      { apply hyps_functionality_snoc2;  simpl; intros; lsubst_tac; auto.
        proof_irr.
        rw @similarity_snoc in H22. exrepnd. simpl in H22. simpl in H24. simpl in H23. 
        lsubst_tac.
        rw @similarity_snoc in H25. exrepnd. simpl in H24. simpl in H25. simpl in H26.
        rw @similarity_snoc in H27. exrepnd. simpl in H27. simpl in H28. simpl in H29.
        assert ( s2a = snoc (snoc s2a1 (x, t5)) (y, t3)).
         {rw <- H29. auto. }
        proof_irr. lsubst_tac.
        apply snoc_inj in H23. destruct H23.
        apply snoc_inj in e. destruct e. inversion e1. clear e1.
        apply snoc_inj in e. destruct e. inversion e1. clear e1.
        apply equality_in_base in H25. spcast.
        apply equality_in_base in H27. spcast.
        apply tequality_equality_if_cequivc; auto.
        apply Ytype; auto. 
        rw e.
        auto.
      } 
      { exrepnd. lsubst_tac.  rw @equality_in_mkc_equality in hyp1. sp. }
      { (* similarity *)
        apply similarity_snoc. simpl.
        exists  (snoc (snoc (snoc s1 (x, x0)) (y, y0)) (u, mkc_axiom)).
        exists  (snoc (snoc (snoc s2 (x, x0)) (y, y0)) (u, mkc_axiom)).
        exists (@mkc_axiom o) (@mkc_axiom o).
        eexists. eexists. sp.
        apply similarity_snoc. simpl.
        exists  ((snoc (snoc s1 (x, x0)) (y, y0))).
        exists  ((snoc (snoc s2 (x, x0)) (y, y0))).
        exists (@mkc_axiom o) (@mkc_axiom o).
        eexists. eexists. sp.
        apply similarity_snoc. simpl.
        exists  (( (snoc s1 (x, x0)))).
        exists  (((snoc s2 (x, x0)))).
        exists y0 y0.
        eexists. eexists. sp.
        apply similarity_snoc. simpl.
        exists s1 s2 x0 x0.
        eexists. eexists. sp.
        (* four equalities to prove *)
        - lsubst_tac. apply equality_in_base_iff. spcast. apply cequivc_refl.
        - lsubst_tac. apply equality_in_base_iff. spcast. apply cequivc_refl.
        - lsubst_tac. rw <- @fold_mkc_member. rw @equality_in_mkc_equality. sp.
        - lsubst_tac. rw @equality_in_mkc_equality. sp.
       }
    }
    
    sp.
    { split; intro. 
      - rename H19 into mem. eapply XA in mem. 
        apply equality_sym in mem. apply equality_refl in mem. exact mem. 
        eapply equality_trans. exact eX6. apply eX0.
        apply equality_sym in eX6. apply equality_refl in eX6. exact eX6. 
      - rename H19 into mem. eapply XA in mem. 
        apply equality_sym in mem. apply equality_refl in mem. exact mem. 
        apply equality_sym.
        eapply equality_trans. exact eX6. apply eX0.
        apply equality_sym in eX6. apply equality_refl in eX6. exact eX6. 
     }
     { apply XA.        
        eapply equality_trans. exact eX6. apply eX0.
        apply equality_sym in eX6. apply equality_refl in eX6. auto. auto.
     } 
     { split; intro. 
      - rename H19 into mem. eapply YA in mem. 
        apply equality_sym in mem. apply equality_refl in mem. exact mem. 
        eapply equality_trans. exact eY6. apply eY0.
        apply equality_sym in eY6. apply equality_refl in eY6. exact eY6. 
      - rename H19 into mem. eapply YA in mem. 
        apply equality_sym in mem. apply equality_refl in mem. exact mem. 
        apply equality_sym.
        eapply equality_trans. exact eY6. apply eY0.
        apply equality_sym in eY6. apply equality_refl in eY6. exact eY6. 
     }
     { apply YA.        
        eapply equality_trans. exact eY6. apply eY0.
        apply equality_sym in eY6. apply equality_refl in eY6. auto. auto.
     } 
     (* We still have to prove a bunch of wf_term and cover_vars goals
        that we deferred by using eexists above. 
        There may be better tactics to knock these off, but they are fairly simple. *)
     Unshelve. 
     - apply wf_equality; eauto 3 with slow.
     - apply cover_vars_equality; sp.
       + apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak_r. simpl. intros. destruct H21; auto. destruct f.
       + apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak_r. simpl. intros. destruct H21; auto. destruct f.
       + apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak. auto.
     - apply wf_member; eauto 3 with slow.
     - apply cover_vars_member; sp.
       + apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak_r. simpl. intros. destruct H21; auto. destruct f.
       + apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak.
         auto.
     - eauto 3 with slow.
     - eauto 3 with slow.
     - eauto 3 with slow.
     - eauto 3 with slow.
     - apply wf_equality; eauto 3 with slow.
     - apply cover_vars_equality; sp.
       + apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak_r. simpl. intros. destruct H21; auto. destruct f.
       + apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak_r. simpl. intros. destruct H21; auto. destruct f.
       + apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak. auto.
     - apply wf_member; eauto 3 with slow.
     - apply cover_vars_member; sp.
       + apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak_r. simpl. intros. destruct H21; auto. destruct f.
       + apply cover_vars_snoc_weak.
         apply cover_vars_snoc_weak.
         auto.
     - eauto 3 with slow.
     - eauto 3 with slow.
     - eauto 3 with slow.
     - eauto 3 with slow.
Qed.

