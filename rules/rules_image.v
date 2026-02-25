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

  Authors: Abhishek Anand &  Vincent Rahli & Mark Bickford

*)


Require Import sequents_tacs.
Require Import subst_tacs_aeq.
Require Import cequiv_tacs.
Require Import cequiv_lsubst.
Require Import tactics2.
Require Import sequents_equality.
Require Import sequents_tacs2.
Require Import per_props_image.
Require Import lsubst_hyps.
Require Import list.



Lemma tequality_image {p} :
  forall lib (A1 A2 F1 F2 : @CTerm p),
    tequality lib
              (mkc_image A1 F1)
              (mkc_image A2 F2)
    <=>
    (tequality lib A1 A2
     # equality lib F1 F2 mkc_base
    ).
Proof.
  intros.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold tequality, nuprl in teq; exrepnd.
    inversion teq0; subst; try not_univ.
    allunfold_per.
    computes_to_value_isvalue.
    unfold tequality; sp.
    + exists eqa; sp.
    + apply equality_in_base_iff; spcast; auto.

  - Case "<-".
    introv e; exrepnd.
    rename e0 into teqa; rename e into teqb.
    unfold tequality in teqa; exrepnd.
    rename eq into eqa.
    exists (per_image_eq lib eqa F1).
    apply CL_image; fold (@nuprl p lib).
    unfold per_image.
    exists eqa A1 A2 F1 F2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_image))).
    apply equality_in_base in teqb; spcast; auto.
Qed.


Lemma equality_image {p} :
  forall lib (A1 A2 F1 F2 : @CTerm p) i,
    equality lib (mkc_image A1 F1)
             (mkc_image A2 F2)
             (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
     #  equality lib F1 F2 mkc_base).
Proof.
  introv.
  sp_iff Case.

  - Case "->".
    intros teq.
    unfold equality, nuprl in teq; exrepnd.
    inversion teq1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    rename eqa into eqi.
    ioneclose; subst; try not_univ.

    destruct H as [eqa H]; exrepnd.
    computes_to_value_isvalue; GC.
    dands.

    exists eq; sp.
    allrw.
    exists eqa; sp.
    apply equality_in_base_iff; spcast; auto.

  - Case "<-".
    intro eqs.
    destruct eqs as [eqa eqb].
    unfold equality in eqa; exrepnd.
    inversion eqa1; subst; try not_univ.
    duniv j h.
    allrw @univi_exists_iff; exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli p lib j0).

    exists eq; sp.
    allrw.

    exists (per_image_eq lib eqa F1).
    unfold nuprli.
    apply CL_image; fold (@nuprli p lib j0).
    unfold per_image.
    exists eqa.

    exists A1 A2 F1 F2; sp;
    try (complete (spcast; apply computes_to_valc_refl; try (apply iscvalue_mkc_image))).
    apply equality_in_base_iff; auto.
Qed.

(**

<<
   H, x : Image (A,f), J |- C ext e

     By imageElimination w

     H, x: Image(A,f), [w:A],  J[f w\x] |- C[f w\x] ext e
>>

 *)

Definition rule_image_elimination {p}
           (A f C e : NTerm)
           (x w : NVar)
           (H J : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp x (mk_image A f)) ++ J)
       (mk_concl C e))
    [ mk_baresequent
        ((snoc (snoc H (mk_hyp x (mk_image A f))) (mk_hhyp w A))  
           ++ (lsubst_hyps [(x, mk_apply f (mk_var w))] J))
        (mk_concl (lsubst  C [(x, mk_apply f (mk_var w))] ) e)
    ]
    [].

Hint Rewrite @nh_vars_hyps_app : core.
Hint Rewrite @nh_vars_hyps_snoc : core.

Lemma rule_image_elimination_true {p} :
  forall lib,
  forall A f C e : NTerm,
  forall x w : NVar,
  forall H J: @barehypotheses p,
    rule_true lib 
         (rule_image_elimination
                 A f C e x w H J).
Proof.
   unfold rule_image_elimination, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
    (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  destseq; allsimpl; proof_irr; GC.
  assert (covered e (nh_vars_hyps (snoc H (mk_hyp x (mk_image A f)) ++ J))) as ce2.
  - clear hyp1.
    autorewrite with core in *. allsimpl; auto.
  - exists ce2.

   (* We prove some simple facts about our sequents *)
  assert (disjoint (free_vars A) (vars_hyps J)
          # disjoint (free_vars f) (vars_hyps J)
          # subset (free_vars_hyps J) (x :: vars_hyps H)
          # subset (free_vars f) (vars_hyps H)

          # !LIn x (vars_hyps H)
          # !LIn x (vars_hyps J)
          # !LIn x (free_vars f)
          # !LIn x (free_vars A)

          # !LIn w (free_vars C)
          # !LIn w (vars_hyps H)
          # !LIn w (vars_hyps J)
          # !LIn w (hyps_free_vars J)
          # !LIn w (free_vars_hyps J)
          # !LIn w (free_vars f)
          # !LIn w (free_vars A)


          # (x <> w)
         ) as vhyps.
  {clear hyp1.
    dwfseq.
    autorewrite with slow core in *.
    sp;
      try (complete (introv i; discover; allunfold @disjoint; discover; auto));
      try (complete (discover; allrw in_app_iff; allrw in_snoc; repndors; tcsp));
      try (complete (introv i; discover; allrw in_app_iff; allrw in_snoc; allsimpl;
            repndors; tcsp)).
  }
  destruct vhyps as [ daj    vhyps ].
  destruct vhyps as [ dbf    vhyps ].
  destruct vhyps as [ ssj    vhyps ].
  destruct vhyps as [ ssf    vhyps ].
  destruct vhyps as [ nixh   vhyps ].
  destruct vhyps as [ nixj   vhyps ].
  destruct vhyps as [ nixf   vhyps ].
  destruct vhyps as [ nixa   vhyps ].
  destruct vhyps as [ niwc   vhyps ].
  destruct vhyps as [ niwh   vhyps ].
  destruct vhyps as [ niwj  vhyps ].
  destruct vhyps as [ niwjhf   vhyps ].
  destruct vhyps as [ niwhfh   vhyps ].
  destruct vhyps as [ niwf   vhyps ].
  destruct vhyps as [ niwa    dxw ].
  
 (* we now start proving the sequent *)
  vr_seq_true.
  rw  @similarity_app in sim; exrepnd.
  rw @similarity_snoc in sim5; exrepnd.
  allsimpl.
  lsubst_tac.
  dup sim5 as eqimg.
  apply equality_in_mkc_image in sim5.
  destruct sim5 as [tA imeq].
  apply equal_in_image_prop in imeq.
  exrepnd.
   subst.
  vr_seq_true  in hyp1.
 
  pose proof (hyp1 (snoc (snoc s1a0 (x, t1)) (w, a1) ++ s1b) 
                   (snoc (snoc s2a0 (x, t2)) (w, a1) ++ s2b)) as hh.
  clear hyp1.
  dimp hh.
  + (*  hyp functionality *)
     clear hh.
     introv sim.
     apply similarity_app in sim; exrepnd; subst.
     apply similarity_snoc in sim9; exrepnd; subst.
     apply similarity_snoc in sim11; exrepnd; subst.
     spcast.
     autorewrite with core in *.
     allrw @length_snoc; cpx.
     apply app_split in sim0; allrw @length_snoc; cpx; try lia.
     repnd; subst. 
     apply snoc_inj in sim5.
     repnd; ginv; subst. 
     apply snoc_inj in sim0.
     repnd; ginv; subst. 
     pose proof (eqh (snoc s2a (x, t5) ++ s2b0)) as eqhh.
     autodimp eqhh xx.
     { apply similarity_app.
       eexists; eexists; eexists; eexists; dands; eauto;
       try (allrw length_snoc; lia).
       apply similarity_snoc; simpl.
        eexists; eexists;eexists; eexists. exists w4 p0; dands; eauto.
       allsimpl.
       lsubst_tac; auto.
       repeat (match goal with
              | [ H : context[htyp (mk_hyp _ _)] |- _ ] => simpl in H
            end).
     assert (alpha_eq_hyps
              (substitute_hyps (snoc (snoc s1a (x, t4)) (w, t0))
              (lsubst_hyps [(x, mk_apply f (mk_var w))] J)) 
                 
             (substitute_hyps (snoc s1a (x, mkc_apply (lsubstc f w2 s1a c2) t0)) J))
              as eqsubs.
    {  repeat (rw @substitute_hyps_as_lsubst_hyps).
          eapply alpha_eq_hyps_trans;[apply combine_lsubst_hyps_aeq|].
          unfold lsubst_sub; simpl.
          rw @lsubst_mk_apply; eauto 3 with slow.
          allrw @csub2sub_snoc.
          rw (cl_lsubst_snoc_not_in f w); simpl; tcsp; eauto 2 with slow;
          [|repeat (apply implies_cl_sub_snoc);eauto 2 with slow].
          assert (!(LIn w (dom_csub s1a))).
          { allapply @similarity_dom; repnd; allrw; auto. }
          rw (@cl_lsubst_var_snoc_in p w); eauto 3 with slow;
           [|repeat (rw @dom_sub_snoc); rw in_snoc; rw @dom_csub_eq; tcsp].

          apply alpha_eq_hyps_lsubst_if_ext_eq; eauto 2 with slow.

          introv i; allsimpl.
          allrw @sub_find_snoc.
           boolvar; simpl; tcsp;
          remember (sub_find (csub2sub s1a) v) as sf; symmetry in Heqsf;
          destruct sf; eauto 2 with slow;
          allapply @sub_find_some;
          allapply @sub_find_none2;
          allapply @in_sub_eta; repnd;
          allrw @dom_csub_eq; GC.
           - destruct nixh.
            allapply @similarity_dom; repnd. rw <- sim5; auto.
           
           - destruct_cterms; simpl; eauto 3 with slow.
             apply implies_alpha_eq_mk_apply; eauto 3 with slow.
             rw @cl_lsubst_snoc_not_in; eauto 3 with slow.
             
    }
    eapply similarity_preserves_alpha_eq_hyps in sim2;
          [| |exact eqsubs];
          [|autorewrite with slow core; auto];[].

    apply vswf_hypotheses_nil_eq in wfh.
    apply wf_hypotheses_implies_wf_hyps in wfh.
    rw @wf_hyps_app in wfh; repnd.
    eapply similarity_preserves_cequiv_open_hyps; try (exact sim2);
        autorewrite with slow core; auto.
    - rw @substitute_hyps_as_lsubst_hyps.
          apply implies_wf_hyps_lsubst_hyps; auto.
    - introv i.
       repeat (rw @substitute_hyps_as_lsubst_hyps in i).
       repeat (rw @lsubst_hyps_as_map in i).
       rw <- @map_combine in i.
       rw in_map_iff in i; exrepnd; ginv.
       apply in_combine_same in i1; repnd; subst.
       destruct a; unfold eq_free_vars_hyp; simpl.
       repeat (rw @free_vars_cl_lsubst; eauto 3 with slow;[]).
       allrw @csub2sub_snoc.
       allrw @dom_sub_snoc; auto.
    - repeat (rw @substitute_hyps_as_lsubst_hyps).
      apply cequiv_open_hyps_same_hyps; auto.
      repeat (rw @csub2sub_snoc).
      apply cequiv_subst_snoc; eauto 2 with slow.
    }
   
   apply eq_hyps_app in eqhh; exrepnd.
    apply eq_hyps_snoc in eqhh5; exrepnd; subst.
    allrw length_snoc.
    apply app_split in eqhh2;[|repeat (rw length_snoc); lia]; repnd; subst.
    apply app_split in eqhh0;[|repeat (rw length_snoc); lia]; repnd; subst.
    cpx; simpl in *; GC; ginv.
    repeat (match goal with
              | [ H : context[htyp (mk_hyp _ _)] |- _ ] => simpl in H
              | [ H : context[hvar (mk_hyp _ _)] |- _ ] => simpl in H
            end).

    assert (cover_vars A (snoc s2a2 (x, t6))) as covA.
    { eapply cover_vars_change_sub;[|exact p1].
      repeat (rw @dom_csub_snoc); simpl.
      apply eq_hyps_dom in eqhh8; repnd.
      rw eqhh0; rw eqhh8; auto. }
    assert (cover_vars (mk_image A f)  s2a2 ) as covIm.
    { eapply cover_vars_change_sub;[|exact p4].
      repeat (rw @dom_csub_snoc); simpl.
      apply eq_hyps_dom in eqhh8; repnd.
     auto.
    }
    
    
   apply eq_hyps_app.
    eexists; eexists; eexists; eexists; dands; eauto;
    repeat (rw length_snoc); try lia.
  
   { apply eq_hyps_snoc; simpl.
      eexists; eexists; eexists; eexists.
      exists w3 p1 covA; dands; eauto.

      - apply eq_hyps_snoc; simpl.
        exists s1a1 s2a2.
        eexists; eexists.
        exists w4 p2 covIm; dands; eauto.

        + lsubst_tac.
          apply tequality_image.
          apply tequality_image in eqhh6; sp.
     
      - lsubst_tac.
        apply tequality_image in eqhh6; repnd.
        auto.
        
     }
        

    


   
     

(* UNIFINISHED *)

Abort.


(* [17] ============ IMAGE EQUALITY ============ *)

  (*
   H |-image(A1,f1) = image(A2,f2) in Type

     By imageEquality ()

     H |- f1 = f2 in Base
     H |- A1 = A2 in Type
 *)
Definition rule_image_equality {p}
           (A1 A2 f1 f2 : NTerm)
           (i : nat)
           (H : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_image A1 f1)
                      (mk_image A2 f2)
                      (mk_uni i))))
    [ mk_baresequent H (mk_conclax (mk_equality f1 f2 mk_base)),
      mk_baresequent H (mk_conclax (mk_equality A1 A2 (mk_uni i)))
    ]
    [].

(* [17] ============ IMAGE MEMBER EQUALITY ============ *)

  (*
   H |-f a1 = f a2 in image(A,f)

     By imageMemberEquality ()

     H |- a1 = a2 in A
     H |- f = f in Base
 *)
Definition rule_image_member_equality {p}
           (A f a1 a2 : NTerm)
           (H : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_apply f a1)
                      (mk_apply f a2)
                      (mk_image A f)
                      )))
    [ mk_baresequent H (mk_conclax (mk_equality a1 a2 A)),
      mk_baresequent H (mk_conclax (mk_equality f f mk_base))
    ]
    [].


Lemma rule_image_member_equality_true {p} :
  forall lib,
  forall A f a1 a2 : NTerm,
  forall H : @barehypotheses p,
    rule_true lib 
         (rule_image_member_equality
                 A f a1 a2 H).
Proof.
   unfold rule_image_member_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.
    (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.
  exists (@covered_axiom p (nh_vars_hyps H)).
   (* we now start proving the sequent *)
  vr_seq_true.
  lift_lsubst.
  rw @member_eq.
  rw <- @member_equality_iff.

  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2); intro h.
  repeat (autodimp h hyp); exrepnd.
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2); intro h.
  repeat (autodimp h hyp); exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  apply tequality_mkc_equality_implies in h0.
  apply tequality_mkc_equality_implies in h2.
  repnd.
  generalize (teq_and_eq_if_equality lib (mk_image A f) (mk_apply f a1) (mk_apply f a2) s1 s2 H
              wT w1 w2 c1 c4 c2 c6 cT cT0 eqh sim
              ); intro k; lsubst_tac; apply k; clear k; auto.
 
  - apply tequality_image; dands; auto; destruct h2 as [xx | yy]; auto.
    
  - clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.
  generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  apply tequality_mkc_equality_implies in hyp3.
  repnd.
  assert ((lsubstc f w0 s1 c1) ~=~( lib)(lsubstc f w0 s2 c0)). 
   { dimp hyp3. apply equality_refl in hyp2; auto. apply equality_in_base in hyp. auto. }
  
  spcast.
  generalize_lsubstc_terms f1.
  generalize_lsubstc_terms a11.
  generalize_lsubstc_terms f2.
  generalize_lsubstc_terms a22.
  generalize_lsubstc_terms A1.
  revert hyp1.
  generalize_lsubstc_terms a21.
  revert hyp0.
  generalize_lsubstc_terms a12.
  generalize_lsubstc_terms A2.
  introv teq eq.
  apply tequality_mkc_equality_implies in teq.
  repnd.
  dimp teq1.
  assert (equality lib a11 a22  A1) as eq2.
  
  + eapply equality_trans with (t2 := a12). 
    { apply teq3. apply equality_refl in eq. auto. }
    { eapply tequality_preserving_equality; [exact hyp |apply tequality_sym;auto ]. }
  +  apply equality_in_mkc_image; dands.
  * eapply tequality_refl; eauto.
  * eapply eq_in_image_eq; [exact eq2 | spcast | spcast]; eauto 3 with slow.
    apply implies_cequivc_apply; auto; apply cequivc_sym; auto.
Qed.


Lemma rule_image_equality_true {p} :
  forall lib,
  forall A1 A2 f1 f2 : NTerm,
  forall i : nat,
  forall H : @barehypotheses p,
    rule_true lib
         (rule_image_equality
                 A1 A2 f1 f2
                 i
                 H).
Proof.
  unfold rule_image_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  inversion wg as [ wfh wfc ]; allsimpl.
  inversion wfc as [ wtt wte ]; allsimpl; clear wfc.
  generalize (hyps (mk_baresequent H (mk_conclax (mk_equality f1 f2 mk_base)))
                   (inl eq_refl))
             (hyps (mk_baresequent H (mk_conclax (mk_equality A1 A2 (mk_uni i))))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2; clear hyps.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destruct ws1 as [ ws1 ws1' ]; allsimpl.
  destruct ws2 as [ ws2 ws2' ]; allsimpl.
  destruct ws1 as [ wh1 wc1 ]; allsimpl.
  destruct ws2 as [ wh2 wc2 ]; allsimpl.
  destruct ws1' as [ ct1 ce1 ]; allsimpl.
  destruct ws2' as [ ct2 ce2 ]; allsimpl.
  allunfold @closed_type; allsimpl.
  allunfold @closed_extract; allsimpl;
  GC.

  allunfold @closed_type; allunfold @closed_extract; allunfold @nh_vars_hyps; allsimpl.

  assert (covered (@mk_axiom p) (vars_hyps (filter is_nh H))) as ce by prove_seq.
  exists ce.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  allrw @sequent_true_eq_VR.
  rw @VR_sequent_true_all; simpl; introv sim eqh.
  intros.
  lsubst_tac.
  assert ( tequality lib (mkc_uni i) (mkc_uni i)) as Z by
   (apply tequality_mkc_uni).
  assert (wf_term (mk_image A1 f1)) as wfa by (apply wf_image; auto).
  assert (wf_term (mk_image A2 f2)) as wfb by (apply wf_image; auto).

  pose proof (teq_and_eq_if_equality lib (@mk_uni p i) (mk_image A1 f1) (mk_image A2 f2)
              s1 s2 H wT wfa wfb c1 c0 c2 c3 cT cT0 eqh sim) as X.
  lsubst_tac.
  allrw @member_eq;
  allrw <- @member_equality_iff.
  apply X; auto.
  introv hfun ss.
  lsubst_tac.
  clear dependent s1.
  clear dependent s2.
  rename s0 into s1.
  rename s3 into s2.
  apply equality_image.
  rw @VR_sequent_true_ex in hyp1; rw @VR_sequent_true_ex in hyp2. allsimpl.
  generalize (hyp1 s1 s2) (hyp2 s1 s2); clear hyp1 hyp2; intros hyp1 hyp2.
  repeat (dest_imp hyp1 h); repeat (dest_imp hyp2 h); exrepnd.
  lsubst_tac.
  allrw @member_eq;
  allrw <- @member_equality_iff.
  rw @tequality_mkc_equality in hyp0; rw @tequality_mkc_equality in hyp3; repnd.
  dands; auto.
  - generalize_lsubstc_terms A11.
    generalize_lsubstc_terms A22.
    revert hyp0. generalize_lsubstc_terms A21.
    revert hyp9. generalize_lsubstc_terms A12.
    introv aa.
    assert (equality lib A11 A12 (mkc_uni i)) as eq1.
     { apply hyp10. apply equality_refl in hyp2; auto. }
    assert (equality lib A21 A11 (mkc_uni i)) by
      (apply equality_sym; auto).
    introv bb.
    assert (equality lib A21 A22 (mkc_uni i)) as eq2.
     { apply bb. apply equality_sym in hyp2; apply equality_refl in hyp2; auto. }
      
    eapply equality_trans; [exact hyp2 | auto].

  - allrw @equality_in_base_iff.
    revert hyp3. revert hyp6.
    generalize_lsubstc_terms f11.
    generalize_lsubstc_terms f12.
    generalize_lsubstc_terms f21.
    generalize_lsubstc_terms f22.
    introv aa.
    assert ((f11) ~=~( lib)(f12)) as e1.
     {apply aa; auto. spcast. apply cequivc_refl. }
    introv bb.
    assert ((f21) ~=~( lib)(f22)) as e2.
     {apply bb; auto; spcast. apply cequivc_refl. }
    spcast.
    eapply cequivc_trans; [exact hyp1| auto].
Qed.
