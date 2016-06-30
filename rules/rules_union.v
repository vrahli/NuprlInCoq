(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University

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

  Authors: Abhishek Anand
           Vincent Rahli
           Mark Bickford

*)


Require Export sequents2.
Require Import sequents_tacs.
Require Import subst_tacs_aeq.
Require Import cequiv_tacs.
Require Import cequiv_lsubst.
Require Import tactics2.
Require Import sequents_equality.
Require Import sequents_tacs2.
Require Import per_props_union.
Require Import lsubst_hyps.
Require Import list.


Lemma equality_union_in_uni {p} :
  forall lib (A1 A2 B1 B2 : @CTerm p) i,
    equality lib (mkc_union A1 B1)
             (mkc_union A2 B2)
             (mkc_uni i)
    <=>
    (equality lib A1 A2 (mkc_uni i)
     #  equality lib B1 B2 (mkc_uni i)).
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
    + exists eq; sp.
      allrw.
      exists eqa; sp.
    + exists eq; sp.
      allrw.
      exists eqb; sp.
  - Case "<-".
    intro eqs.
    destruct eqs as [eqa eqb].
    unfold equality in eqa; exrepnd.
    inversion eqa1; subst; try not_univ.
    unfold equality in eqb; exrepnd.
    inversion eqb1; subst; try not_univ.
    duniv j1 h1.
    duniv j2 h2.
    allrw @univi_exists_iff. exrepd.
    computes_to_value_isvalue; GC.
    discover; exrepnd.
    allfold (@nuprli p lib j0).

    exists eq; sp.
    allrw.

    exists (per_union_eq lib eqa eqa2).
    unfold nuprli.
    apply CL_union; fold (@nuprli p lib j0).
    unfold per_union.
    exists eqa eqa2.

    exists A1 A2 B1 B2; sp;
    spcast; apply computes_to_valc_refl; apply iscvalue_mkc_union.
Qed.




(* ============ UNION EQUALITY ============ *)

  (*
   H |- union(A1,B1) = union(A2,B2) in Type

     By unionEquality ()

     H |- A1 = A2 in Type
     H |- B1 = B2 in Type
 *)
Definition rule_union_equality {p}
           (A1 A2 B1 B2 : NTerm)
           (i : nat)
           (H : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_union A1 B1)
                      (mk_union A2 B2)
                      (mk_uni i))))
    [ mk_baresequent H (mk_conclax (mk_equality A1 A2 (mk_uni i))),
      mk_baresequent H (mk_conclax (mk_equality B1 B2 (mk_uni i)))
    ]
    [].

(* ============ INL EQUALITY ============ *)

  (*
   H |- inl a1 = inl a2 in union(A,B)

     By inlEquality i

     H |- a1 = a2 in A
     H |- B = B in U_i
 *)
Definition rule_inl_equality {p}
           (A B a1 a2 : NTerm)
           (i : nat)
           (H : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_inl a1)
                      (mk_inl a2)
                      (mk_union A B)
                      )))
    [ mk_baresequent H (mk_conclax (mk_equality a1 a2 A)),
      mk_baresequent H (mk_conclax (mk_equality B B (mk_uni i)))
    ]
    [].

(* ============ INR EQUALITY ============ *)

  (*
   H |- inr b1 = inr b2 in union(A,B)

     By inrEquality i

     H |- b1 = b2 in B
     H |- A = A in U_i
 *)

Definition rule_inr_equality {p}
           (A B b1 b2 : NTerm)
           (i : nat)
           (H : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality
                      (mk_inr b1)
                      (mk_inr b2)
                      (mk_union A B)
                      )))
    [ mk_baresequent H (mk_conclax (mk_equality b1 b2 B)),
      mk_baresequent H (mk_conclax (mk_equality A A (mk_uni i)))
    ]
    [].

(* ============ INL FORMATION ============ *)

  (*
   H |- union(A,B) ext inl(s)

     By inlEquality i

     H |- A ext s
     H |- B in U_i
 *)
Definition rule_inl_formation {p}
           (A B s : NTerm)
           (i : nat)
           (H : @barehypotheses p) :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_union A B) (mk_inl s)))
    [
      mk_baresequent H (mk_concl A s),
      mk_baresequent H (mk_conclax (mk_member B (mk_uni i)))
    ]
    [].

(* ============ INR FORMATION ============ *)

  (*
   H |- union(A,B) ext inr(s)

     By inrEquality i

     H |- B ext s
     H |- A in U_i
 *)

Definition rule_inr_formation {p}
           (A B s : NTerm)
           (i : nat)
           (H : @barehypotheses p) :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_union A B) (mk_inr s)))
    [
      mk_baresequent H (mk_concl B s),
      mk_baresequent H (mk_conclax (mk_member A (mk_uni i)))
    ]
    [].



Lemma rule_inl_equality_true {p} :
  forall lib,
  forall A B a1 a2 : NTerm,
  forall i : nat,
  forall H : @barehypotheses p,
    rule_true lib 
         (rule_inl_equality
                 A B a1 a2 i H).
Proof.
   unfold rule_inl_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  generalize (teq_and_eq_if_equality lib (mk_union A B) (mk_inl a1) (mk_inl a2) s1 s2 H
              wT w1 w2 c1 c0 c2 c3  cT cT0  eqh sim 
              ); intro k; lsubst_tac; apply k; clear k; auto.
 
  - apply tequality_mkc_union; dands; auto; destruct h2 as [xx | yy];  auto.
    + apply equality_in_uni in xx; auto.
    + spcast. eapply equality_in_uni. apply equality_respects_cequivc; eauto.
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
  generalize_lsubstc_terms a11.
  generalize_lsubstc_terms a22.
  generalize_lsubstc_terms A1.
  generalize_lsubstc_terms B1.
  revert hyp1.
  generalize_lsubstc_terms a21.
  revert hyp0.
  generalize_lsubstc_terms a12.
  generalize_lsubstc_terms A2.
  introv teq eq.
  apply tequality_mkc_equality_implies in teq.
  repnd.
  dimp teq1.
  assert ( type lib B1 ) as Btyp.
  { apply equality_in_uni in hyp2.
   eapply tequality_refl; eauto. }
  
  assert (equality lib a11 a22  A1) as eq2.
  + eapply equality_trans with (t2 := a12). 
    { destruct teq; auto; spcast. apply equality_respects_cequivc; auto. eapply equality_refl. eauto. }
    { eapply tequality_preserving_equality; [exact hyp |apply tequality_sym;auto ]. }
  + apply equality_mkc_union; dands; auto.
  * eapply tequality_refl; eauto.
  * left. eexists; eexists; dands; [spcast | spcast | exact eq2];
    apply computes_to_valc_refl; apply iscvalue_mkc_inl.
Qed.

Lemma rule_inr_equality_true {p} :
  forall lib,
  forall A B b1 b2 : NTerm,
  forall i : nat,
  forall H : @barehypotheses p,
    rule_true lib
         (rule_inr_equality
                 A B b1 b2 i H).
Proof.
   unfold rule_inr_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  generalize (teq_and_eq_if_equality lib (mk_union A B) (mk_inr b1) (mk_inr b2) s1 s2 H
              wT w1 w2 c1 c0 c2 c3  cT cT0  eqh sim
              ); intro k; lsubst_tac; apply k; clear k; auto.

  - apply tequality_mkc_union; dands; auto; destruct h2 as [xx | yy];  auto.
    + apply equality_in_uni in xx; auto.
    + spcast. eapply equality_in_uni. apply equality_respects_cequivc; eauto.
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
  generalize_lsubstc_terms b11.
  generalize_lsubstc_terms b22.
  generalize_lsubstc_terms A1.
  generalize_lsubstc_terms B1.
  revert hyp1.
  generalize_lsubstc_terms b21.
  revert hyp0.
  generalize_lsubstc_terms b12.
  generalize_lsubstc_terms B2.
  introv teq eq.
  apply tequality_mkc_equality_implies in teq.
  repnd.
  dimp teq1.
  assert ( type lib A1 ) as Atyp.
  { apply equality_in_uni in hyp2.
   eapply tequality_refl; eauto. }

  assert (equality lib b11 b22  B1) as eq2.
  + eapply equality_trans with (t2 := b12).
    { destruct teq; auto; spcast. apply equality_respects_cequivc; auto. eapply equality_refl. eauto. }
    { eapply tequality_preserving_equality; [exact hyp |apply tequality_sym;auto ]. }
  + apply equality_mkc_union; dands; auto.
  * eapply tequality_refl; eauto.
  * right. eexists; eexists; dands; [spcast | spcast | exact eq2];
    apply computes_to_valc_refl; apply iscvalue_mkc_inr.
Qed.

Lemma rule_inl_formation_true3 {p} :
  forall lib,
  forall A B s : NTerm,
  forall i : nat,
  forall H : @barehypotheses p,
    rule_true3 lib (rule_inl_formation A B s i H).
Proof.
  unfold rule_inl_formation, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H) ||- (mk_concl (mk_union A B) (mk_inl s)))) as wfs.
  { clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp; try (apply wf_inl; auto).
    introv xx; allrw in_app_iff; tcsp. }
  exists wfs.
  unfold wf_csequent, wf_sequent, wf_concl in wfs; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 eqh sim) as q.
  pose proof (hyp2 s1 s2 eqh sim) as h.
  clear hyp1 hyp2.
  exrepnd.
  lsubst_tac.

  rw <- @member_member_iff in h1.
  apply tequality_in_uni_implies_tequality in h0;
    [|eapply member_in_uni; eauto].
  rw @tequality_mkc_union.
  rw @equality_mkc_union.
  dands; auto;
    try (complete (eapply member_in_uni; eauto));
    try (complete (eapply inhabited_implies_tequality; eauto)).

  left.
  exists (lsubstc s wfce0 s1 pt4) (lsubstc s wfce0 s2 pt5).
  dands; spcast; auto; try (apply computes_to_valc_refl; eauto 3 with slow).
Qed.

Lemma rule_inr_formation_true3 {p} :
  forall lib,
  forall A B s : NTerm,
  forall i : nat,
  forall H : @barehypotheses p,
    rule_true3 lib (rule_inr_formation A B s i H).
Proof.
  unfold rule_inl_formation, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros; repnd.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  destruct Hyp  as [ ws1 hyp1 ].
  destruct Hyp0 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  assert (wf_csequent ((H) ||- (mk_concl (mk_union A B) (mk_inr s)))) as wfs.
  { clear hyp1 hyp2.
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw @vswf_hypotheses_nil_eq.
    dands; tcsp; try (apply wf_inl; auto).
    introv xx; allrw in_app_iff; tcsp. }
  exists wfs.
  unfold wf_csequent, wf_sequent, wf_concl in wfs; allsimpl; repnd; proof_irr; GC.

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  pose proof (hyp1 s1 s2 eqh sim) as q.
  pose proof (hyp2 s1 s2 eqh sim) as h.
  clear hyp1 hyp2.
  exrepnd.
  lsubst_tac.

  rw <- @member_member_iff in h1.
  apply tequality_in_uni_implies_tequality in h0;
    [|eapply member_in_uni; eauto].
  rw @tequality_mkc_union.
  rw @equality_mkc_union.
  dands; auto;
    try (complete (eapply member_in_uni; eauto));
    try (complete (eapply inhabited_implies_tequality; eauto)).

  right.
  exists (lsubstc s wfce0 s1 pt4) (lsubstc s wfce0 s2 pt5).
  dands; spcast; auto; try (apply computes_to_valc_refl; eauto 3 with slow).
Qed.

Lemma rule_union_equality_true {p} :
  forall lib,
  forall A1 A2 B1 B2 : NTerm,
  forall i : nat,
  forall H : @barehypotheses p,
    rule_true lib 
         (rule_union_equality
                 A1 A2 B1 B2
                 i
                 H).
Proof.
  unfold rule_union_equality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  inversion wg as [ wfh wfc ]; allsimpl.
  inversion wfc as [ wtt wte ]; allsimpl; clear wfc.
  generalize (hyps (mk_baresequent H (mk_conclax (mk_equality A1 A2 (mk_uni i))))
                   (inl eq_refl))
             (hyps (mk_baresequent H (mk_conclax (mk_equality B1 B2 (mk_uni i))))
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
  assert (wf_term (mk_union A1 B1)) as wfa by (apply wf_union; auto).
  assert (wf_term (mk_union A2 B2)) as wfb by (apply wf_union; auto).
   
  pose proof (teq_and_eq_if_equality lib (@mk_uni p i) (mk_union A1 B1) (mk_union A2 B2)
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
  
  
  apply equality_union_in_uni.
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
    revert hyp3. generalize_lsubstc_terms A21.
    revert hyp6. generalize_lsubstc_terms A12.
    introv aa. 
    assert (equality lib A11 A12 (mkc_uni i)) as eq1 by
      ( destruct aa; auto;
        spcast; apply equality_respects_cequivc; auto;
         eapply equality_refl; eauto).
    assert (equality lib A21 A11 (mkc_uni i)) by
      (apply equality_sym; auto).
    introv bb. 
    assert (equality lib A21 A22 (mkc_uni i)) as eq2 by
      (destruct bb; auto;
        spcast; apply equality_respects_cequivc; auto;
         eapply equality_refl; eauto).
    eapply equality_trans; [exact hyp1 | auto].
    
  -  generalize_lsubstc_terms B11.
    generalize_lsubstc_terms B22.
    revert hyp0. generalize_lsubstc_terms B21.
    revert hyp9. generalize_lsubstc_terms B12.
    introv aa. 
    assert (equality lib B11 B12 (mkc_uni i)) as eq1 by
      ( destruct aa; auto;
        spcast; apply equality_respects_cequivc; auto;
         eapply equality_refl; eauto).
    assert (equality lib B21 B11 (mkc_uni i)) by
      (apply equality_sym; auto).
    introv bb. 
    assert (equality lib B21 B22 (mkc_uni i)) as eq2 by
      (destruct bb; auto;
        spcast; apply equality_respects_cequivc; auto;
         eapply equality_refl; eauto).
    eapply equality_trans; [exact hyp2 | auto].
Qed.



Lemma covered_decide {o} :
  forall (a : @NTerm o) v b w c vs,
    covered (mk_decide a v b w c) vs
    <=> (covered a vs # covered b (v :: vs) # covered c (w :: vs)).
Proof.
  unfold covered; sp; simpl.
  repeat (rw remove_nvars_nil_l).
  rewrite app_nil_r.
  repeat (rw subvars_app_l); sp.
Qed.


(**

<<
   H, z : A+B, J |- C ext decide z x.left y.right

     By unionElimination x y

     H, z: A+B, x:A,  J[inl x\z] |- C[inl x\z] ext left
     H, z: A+B, y:B,  J[inr y\z] |- C[inr y\z] ext right
>>

 *)

Definition rule_union_elimination {p}
           (A B C l r : NTerm)
           (z x y : NVar)
           (H J : @barehypotheses p) :=
  mk_rule
    (mk_baresequent
       (snoc H (mk_hyp z (mk_union A B)) ++ J)
       (mk_concl C (mk_decide (mk_var z) x l y r )))
    [ mk_baresequent
        ((snoc (snoc H (mk_hyp z (mk_union A B))) (mk_hyp x A))
           ++ (lsubst_hyps [(z, mk_inl (mk_var x))] J))
        (mk_concl (lsubst  C [(z, mk_inl (mk_var x))] ) l),
     mk_baresequent
        ((snoc (snoc H (mk_hyp z (mk_union A B))) (mk_hyp y B))
           ++ (lsubst_hyps [(z, mk_inr (mk_var y))] J))
        (mk_concl (lsubst  C [(z, mk_inr (mk_var y))] ) r)
    ]
    [].

Hint Rewrite @nh_vars_hyps_app : core.
Hint Rewrite @nh_vars_hyps_snoc : core.
Hint Rewrite @nh_vars_hyps_lsubst_hyps : slow core.

Lemma rule_union_elimination_true {p} :
  forall lib,
  forall A B C l r : NTerm,
  forall z x y : NVar,
  forall H J: @barehypotheses p,
    rule_true lib 
         (rule_union_elimination
                 A B C l r z x y H J).
Proof.
  unfold rule_union_elimination, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp0 into hyp1.
  rename Hyp1 into hyp2.
  destseq; allsimpl; proof_irr; GC.

  assert (covered (mk_decide (mk_var z) x l y r) (nh_vars_hyps (snoc H (mk_hyp z (mk_union A B)) ++ J))) as ce2.
  { clear hyp1. clear hyp2.
    dwfseq.
    introv i; allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff.
    rw in_snoc.
    repndors; repnd; subst; tcsp.
    - apply ce0 in i0.
      allrw in_app_iff.
      allrw in_snoc.
      autorewrite with slow core in *.
      tcsp.
    - apply ce in i0.
      allrw in_app_iff.
      allrw in_snoc.
      autorewrite with slow core in *.
      tcsp. }
  exists ce2.
Abort.

(*
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
  apply equality_in_mkc_union in sim5.
  destruct sim5 as [tA imeq].
  apply equal_in_union_prop in imeq.
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
     apply app_split in sim0; allrw @length_snoc; cpx; try omega.
     repnd; subst. 
     apply snoc_inj in sim5.
     repnd; ginv; subst. 
     apply snoc_inj in sim0.
     repnd; ginv; subst. 
     pose proof (eqh (snoc s2a (x, t5) ++ s2b0)) as eqhh.
     autodimp eqhh xx.
     { apply similarity_app.
       eexists; eexists; eexists; eexists; dands; eauto;
       try (allrw length_snoc; omega).
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
           [|repeat (apply implies_cl_sub_snoc);eauto 2 with slow
           |repeat (rw @dom_sub_snoc); rw in_snoc; rw @dom_csub_eq; tcsp].
          
         
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
    apply app_split in eqhh2;[|repeat (rw length_snoc); omega]; repnd; subst.
    apply app_split in eqhh0;[|repeat (rw length_snoc); omega]; repnd; subst.
    cpx; ginv.
    repeat (match goal with
              | [ H : context[htyp (mk_hyp _ _)] |- _ ] => simpl in H
              | [ H : context[hvar (mk_hyp _ _)] |- _ ] => simpl in H
            end).

    assert (cover_vars A (snoc s2a2 (x, t6))) as covA.
    { eapply cover_vars_change_sub;[|exact p1].
      repeat (rw @dom_csub_snoc); simpl.
      apply eq_hyps_dom in eqhh8; repnd.
      rw eqhh0; rw eqhh8; auto. }
    assert (cover_vars (mk_union A f)  s2a2 ) as covIm.
    { eapply cover_vars_change_sub;[|exact p4].
      repeat (rw @dom_csub_snoc); simpl.
      apply eq_hyps_dom in eqhh8; repnd.
     auto.
    }
    
    
   apply eq_hyps_app.
    eexists; eexists; eexists; eexists; dands; eauto;
    repeat (rw length_snoc); try omega.
  
   { apply eq_hyps_snoc; simpl.
      eexists; eexists; eexists; eexists.
      exists w3 p1 covA; dands; eauto.

      - apply eq_hyps_snoc; simpl.
        exists s1a1 s2a2.
        eexists; eexists.
        exists w4 p2 covIm; dands; eauto.

        + lsubst_tac.
          apply tequality_union.
          apply tequality_union in eqhh6; sp.
     
      - lsubst_tac.
        apply tequality_union in eqhh6; repnd.
        auto.
     }


(* UNIFINISHED *)

Abort.
*)