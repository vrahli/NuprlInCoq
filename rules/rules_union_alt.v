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


Require Export rules_union.
Require Import rules_typehood.



(* ============ INL EQUALITY (ALT) ============ *)

  (*
   H |- inl a1 = inl a2 in union(A,B)

     By inlEquality_alt 

     H |- a1 = a2 in A
     H |- istype(B)
 *)
Definition rule_inl_equality_alt {p}
           (A B a1 a2 : NTerm)
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
      mk_baresequent H (mk_conclax (mk_istype B ))
    ]
    [].

(* ============ INR EQUALITY (ALT) ============ *)

  (*
   H |- inr b1 = inr b2 in union(A,B)

     By inrEquality_alt 

     H |- b1 = b2 in B
     H |- istype(A)
 *)

Definition rule_inr_equality_alt {p}
           (A B b1 b2 : NTerm)
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
      mk_baresequent H (mk_conclax (mk_istype A))
    ]
    [].

(* ============ INL FORMATION (ALT)============ *)

  (*
   H |- union(A,B) ext inl(s)

     By inlEquality_alt 

     H |- A ext s
     H |- istype(B)
 *)
Definition rule_inl_formation_alt {p}
           (A B s : NTerm)
           (H : @barehypotheses p) :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_union A B) (mk_inl s)))
    [
      mk_baresequent H (mk_concl A s),
      mk_baresequent H (mk_conclax (mk_istype B ))
    ]
    [].

(* ============ INR FORMATION ============ *)

  (*
   H |- union(A,B) ext inr(s)

     By inrEquality i

     H |- B ext s
     H |- istype(A)
 *)

Definition rule_inr_formation_alt {p}
           (A B s : NTerm)
           (H : @barehypotheses p) :=
  mk_rule
    (mk_baresequent H (mk_concl (mk_union A B) (mk_inr s)))
    [
      mk_baresequent H (mk_concl B s),
      mk_baresequent H (mk_conclax (mk_istype A ))
    ]
    [].



Lemma rule_inl_equality_alt_true {p} :
  forall lib,
  forall A B a1 a2 : NTerm,
  forall H : @barehypotheses p,
    rule_true lib 
         (rule_inl_equality_alt
                 A B a1 a2 H).
Proof.
   unfold rule_inl_equality_alt, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  pose proof (@tequality_mkc_istype p lib) as teqistype.
  rw teqistype in h2.
  apply equality_axiom_in_mkc_istype in h3.
  repnd.
  generalize (teq_and_eq_if_equality lib (mk_union A B) (mk_inl a1) (mk_inl a2) s1 s2 H
              wT w1 w2 c1 c0 c2 c3  cT cT0  eqh sim 
              ); intro k; lsubst_tac; apply k; clear k; auto.
 
  - apply tequality_mkc_union; dands; auto; destruct h2 as [xx | yy];  auto.
  - clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.
  generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  rw teqistype in hyp3.
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
  { apply equality_axiom_in_mkc_istype in hyp2. auto. }

  assert (equality lib a11 a22  A1) as eq2.
  + apply equality_trans with (t2 := a12); auto. apply teq3. 
    apply equality_refl in eq. auto.
    eapply tequality_preserving_equality; [exact hyp |apply tequality_sym;auto ]. 
  + apply equality_mkc_union; dands; auto.
  * eapply tequality_refl; eauto.
  * left. eexists; eexists; dands; [spcast | spcast | exact eq2];
    apply computes_to_valc_refl; apply iscvalue_mkc_inl.
Qed.

Lemma rule_inr_equality_alt_true {p} :
  forall lib,
  forall A B b1 b2 : NTerm,
  forall H : @barehypotheses p,
    rule_true lib
         (rule_inr_equality_alt
                 A B b1 b2 H).
Proof.
   unfold rule_inr_equality_alt, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  pose proof (@tequality_mkc_istype p lib) as teqistype.

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
  rw teqistype in h2.
  repnd.
  generalize (teq_and_eq_if_equality lib (mk_union A B) (mk_inr b1) (mk_inr b2) s1 s2 H
              wT w1 w2 c1 c0 c2 c3  cT cT0  eqh sim
              ); intro k; lsubst_tac; apply k; clear k; auto.

  - apply tequality_mkc_union; dands; auto; destruct h2 as [xx | yy];  auto.
  - clear dependent s1.
  clear dependent s2.
  introv hf sim.
  lsubst_tac.
  generalize (hyp1 s1 s2 hf sim); clear hyp1; intro hyp1; exrepnd.
  generalize (hyp2 s1 s2 hf sim); clear hyp2; intro hyp2; exrepnd.
  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  rw teqistype in hyp3.
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
  { apply equality_axiom_in_mkc_istype in hyp2.
    auto. }
  assert (equality lib b11 b22  B1) as eq2.
  + eapply equality_trans with (t2 := b12); auto. apply teq3.
    apply equality_refl in eq. auto.
    { eapply tequality_preserving_equality; [exact hyp |apply tequality_sym;auto ]. }
  + apply equality_mkc_union; dands; auto.
  * eapply tequality_refl; eauto.
  * right. eexists; eexists; dands; [spcast | spcast | exact eq2];
    apply computes_to_valc_refl; apply iscvalue_mkc_inr.
Qed.

Lemma rule_inl_formation_alt_true3 {p} :
  forall lib,
  forall A B s : NTerm,
  forall H : @barehypotheses p,
    rule_true3 lib (rule_inl_formation_alt A B s H).
Proof.
  unfold rule_inl_formation_alt, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
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
  pose proof (@tequality_mkc_istype p lib) as teqistype.

  rw teqistype in h0.
  apply equality_axiom_in_mkc_istype in h1.
  rw @tequality_mkc_union.
  rw @equality_mkc_union.
  dands; auto;
    try (complete (eapply member_in_uni; eauto));
    try (complete (eapply inhabited_implies_tequality; eauto)).

  left.
  exists (lsubstc s wfce0 s1 pt4) (lsubstc s wfce0 s2 pt5).
  dands; spcast; auto; try (apply computes_to_valc_refl; eauto 3 with slow).
Qed.

Lemma rule_inr_formation_alt_true3 {p} :
  forall lib,
  forall A B s : NTerm,
  forall H : @barehypotheses p,
    rule_true3 lib (rule_inr_formation_alt A B s H).
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
  pose proof (@tequality_mkc_istype p lib) as teqistype.

  rw teqistype in h0.
  apply equality_axiom_in_mkc_istype in h1.
  rw @tequality_mkc_union.
  rw @equality_mkc_union.
  dands; auto;
    try (complete (eapply member_in_uni; eauto));
    try (complete (eapply inhabited_implies_tequality; eauto)).

  right.
  exists (lsubstc s wfce0 s1 pt4) (lsubstc s wfce0 s2 pt5).
  dands; spcast; auto; try (apply computes_to_valc_refl; eauto 3 with slow).
Qed.


