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
Require Export sequents_tacs.
Require Export sequents_tacs2.
Require Export rules_useful.
Require Export per_props_equality.
Require Export sequents_equality.
Require Export rules_tyfam.
Require Export subst_tacs_aeq.
Require Export cequiv_tacs.
Require Export lsubstc_weak.

(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)


Hint Rewrite @nh_vars_hyps_app : slow.
Hint Rewrite @nh_vars_hyps_snoc : slow.



(* end hide *)



(* begin hide *)



(* end hide *)

(* [26] ============ APPLY @EQUALITY ============ *)

(**

  We following rule called ``apply @equality`` allows one to prove that
  applications are well-typed.
<<
   H |- f1 t1 = f2 t2 in B[x\t1]

     By applyEquality ()

     H |- f1 = f2 in x:A->B
     H |- t1 = t2 in A
>>
 *)

Definition rule_apply_equality_concl {o} (H : @bhyps o) f1 t1 f2 t2 B x :=
  mk_baresequent H (mk_conclax (mk_equality
                                  (mk_apply f1 t1)
                                  (mk_apply f2 t2)
                                  (subst B x t1))).

Definition rule_apply_equality_hyp1 {o} (H : @bhyps o) f1 f2 A x B e1 :=
  mk_baresequent H (mk_concl (mk_equality f1 f2 (mk_function A x B)) e1).

Definition rule_apply_equality_hyp2 {o} (H : @bhyps o) t1 t2 A e2 :=
  mk_baresequent H (mk_concl (mk_equality t1 t2 A) e2).

Definition rule_apply_equality {o}
           (A B f1 f2 t1 t2 : NTerm)
           (e1 e2 : NTerm)
           (x : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (rule_apply_equality_concl H f1 t1 f2 t2 B x)
    [ rule_apply_equality_hyp1 H f1 f2 A x B e1,
      rule_apply_equality_hyp2 H t1 t2 A e2
    ]
    [].

Lemma rule_apply_equality_true3 {o} :
  forall lib (A B f1 f2 t1 t2 e1 e2 : NTerm)
         (x : NVar)
         (H : @bhyps o),
    rule_true3 lib (rule_apply_equality A B f1 f2 t1 t2 e1 e2 x H).
Proof.
  intros.
  unfold rule_apply_equality, rule_true3, wf_bseq, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp; exrepnd.
  rename Hyp into hyp1.
  rename Hyp0 into hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  match goal with
  | [ |- sequent_true2 _ ?s ] => assert (wf_csequent s) as wfc by (prove_seq; eauto 3 with slow)
  end.

  exists wfc.
  unfold wf_csequent, wf_sequent, wf_concl in wfc; allsimpl; repnd; proof_irr; GC.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  vr_seq_true in hyp2.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd.

  lsubst_tac.
  apply equality_in_mkc_equality in hyp1.
  apply equality_in_mkc_equality in hyp2.
  repnd.

  repeat match goal with
         | [ H : _ ===>(_) mkc_axiom |- _ ] => clear H
         end.
  rw @tequality_mkc_equality in hyp3.
  rw @tequality_mkc_equality in hyp0.
  
  repeat (rw prod_assoc).
  repnd.
  rw @tequality_function in hyp1; repnd.

  (* a few assertions *)
  assert (equality
            lib
            (lsubstc t1 w1 s1 c1)
            (lsubstc t1 w1 s2 c0)
            (lsubstc A wT s1 cT))
    as eq1. { apply @equality_refl in hyp4; sp. }
      
  assert (equality lib (lsubstc t2 w2 s1 c2)
                   (lsubstc t2 w2 s2 c3)
                   (lsubstc A wT s1 cT))
    as eq5.
  {
    apply @equality_trans with (t2 := lsubstc t2 w2 s1 c2); sp.
    apply @equality_sym in hyp4; apply @equality_refl in hyp4; sp.
    apply hyp3.
    apply @equality_sym in hyp4; apply @equality_refl in hyp4; sp.
    
  }

  assert (equality lib (lsubstc f2 w3 s1 c5)
                   (lsubstc f2 w3 s2 c8)
                   (mkc_function (lsubstc A wT s1 cT) x
                                 (lsubstc_vars B w5 (csub_filter s1 [x]) [x] c7)))
    as eq6.
  {
    apply @equality_trans with (t2 := lsubstc f2 w3 s1 c5); sp.
    apply @equality_sym in hyp6; apply @equality_refl in hyp6; sp.
    apply hyp0.
    apply @equality_sym in hyp6; apply @equality_refl in hyp6; sp.
  }

  assert (equality lib (lsubstc t1 w1 s1 c1)
                   (lsubstc t2 w2 s2 c3)
                   (lsubstc A wT s1 cT))
         as eq7 by (apply @equality_trans with (t2 := lsubstc t2 w2 s1 c2); sp).

  assert (wf_term (subst B x t2))
         as wfs2
         by (apply lsubst_preserves_wf_term; sp;
             unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp).

  assert (cover_vars (subst B x t2) s1) as cv2.
  {
    rw @cover_vars_eq.
    rw @cover_vars_eq in cT3.
    unfold subst.
    rw subvars_prop; introv k.
    generalize (eqvars_free_vars_disjoint B [(x,t1)]); intro u1.
    generalize (eqvars_free_vars_disjoint B [(x,t2)]); intro u2.
    rw eqvars_prop in u1.
    rw eqvars_prop in u2.
    rw u2 in k; simpl in k.
    rw in_app_iff in k; rw in_remove_nvars in k; rw in_single_iff in k; repdors; repnd.
    rw subvars_prop in cT3.
    apply cT3; unfold subst.
    rw u1.
    rw in_app_iff; rw in_remove_nvars; rw in_single_iff; sp.
    revert k.
    boolvar; simpl; allrw app_nil_r; intro k; sp.
    clear_dependents c2.
    rw @cover_vars_eq in c2.
    rw subvars_prop in c2.
    apply c2; sp.
  }

  assert (cover_vars (subst B x t2) s2) as cv3.
  {
    rw @cover_vars_eq.
    rw @cover_vars_eq in cv2.
    allapply @similarity_dom; repnd; allrw.
    rw sim0 in cv2; sp.
  }

  assert (tequality lib (lsubstc (subst B x t1) wT1 s1 cT3)
                    (lsubstc (subst B x t2) wfs2 s1 cv2)) as teqB.
  {
    generalize (hyp1 (lsubstc t1 w1 s1 c1) (lsubstc t2 w2 s2 c3)); intro k1.
    autodimp k1 hyp; sp.
    generalize (hyp1 (lsubstc t2 w2 s1 c2) (lsubstc t2 w2 s2 c3)); intro k2.
    autodimp k2 hyp; sp.

    repeat lsubstc_subst_aeq2.
    proof_irr.
    eapply tequality_trans;[eauto|].
    apply tequality_sym; auto.
  }



  (* now we start proving our conclusion *)
  dands.
  { apply @tequality_mkc_equality_if_equal; auto. 
     {
    (* from hyp 4 *)
    generalize (hyp1 (lsubstc t1 w1 s1 c1) (lsubstc t1 w1 s2 c0) eq1); intro teq.
    repeat lsubstc_subst_aeq2.
    proof_irr.
    auto.
  }
  {
    (* from eq1 and hyp5 *)
    dimp hyp5. apply equality_refl in hyp6; auto.
    rw @equality_in_function in hyp; repnd.
    apply hyp in eq1.
    repeat lsubstc_subst_aeq2.
    proof_irr.
    tcsp.
  }

  {
    (* from eq6 and eq5 *)
    
    rw @equality_in_function in eq6; repnd.
    apply eq6 in eq5.
    repeat lsubstc_subst_aeq2.
    proof_irr.
    tcsp.
   eapply tequality_preserving_equality. exact eq5. 
   apply tequality_sym. exact teqB.
  }
   
   
  }
  {(* from hyp1 and hyp2 *)
    apply member_equality; auto.
    repeat lsubstc_subst_aeq2.
    proof_irr.
    tcsp.

    rw @equality_in_function in hyp6; repnd.
    apply hyp6 in hyp4; auto.
  }

 
Qed.

Lemma rule_apply_equality_true {o} :
  forall lib (A B f1 f2 t1 t2 e1 e2 : NTerm)
         (x : NVar)
         (H : @barehypotheses o),
    rule_true lib (rule_apply_equality A B f1 f2 t1 t2 e1 e2 x H).
Proof.
  introv.
  apply rule_true3_implies_rule_true.
  apply rule_apply_equality_true3; auto.
Qed.

Lemma rule_apply_equality_true_ext_lib {o} :
  forall lib (A B f1 f2 t1 t2 e1 e2 : NTerm)
         (x : NVar)
         (H : @barehypotheses o),
    rule_true_ext_lib lib (rule_apply_equality A B f1 f2 t1 t2 e1 e2 x H).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_apply_equality_true3; auto.
Qed.

Lemma rule_apply_equality_true_ext_lib2 {o} :
  forall lib (A B f1 f2 t1 t2 e1 e2 : NTerm)
         (x : NVar)
         (H : @barehypotheses o),
    rule_true_ext_lib lib (rule_apply_equality A B f1 f2 t1 t2 e1 e2 x H).
Proof.
  introv.
  apply rule_true3_implies_rule_true_ext_lib.
  introv.
  apply rule_apply_equality_true3; auto.
Qed.

Lemma rule_apply_equality_wf2 {o} :
  forall (A B f1 f2 t1 t2 e1 e2 : NTerm)
         (x : NVar)
         (H : @barehypotheses o),
    wf_term A
    -> covered A (vars_hyps H)
    -> wf_rule2 (rule_apply_equality A B f1 f2 t1 t2 e1 e2 x H).
Proof.
  introv wfA covA wf j.
  allsimpl; repndors; subst; tcsp;
    allunfold @wf_bseq; repnd; allsimpl; wfseq;
      allrw <- @wf_apply_iff; allrw @covered_apply; repnd; tcsp.

  - apply lsubst_wf_term in w1; dands; auto.

  - allunfold @covered.
    allrw subvars_eq.
    introv i; simpl.
    destruct (deq_nvar x x0) as [d|d]; subst; tcsp.
    right.
    apply c1.
    apply eqset_free_vars_disjoint; simpl.
    rw in_app_iff; rw in_remove_nvars; rw in_single_iff.
    left; tcsp.
Qed.

(* begin hide *)



(* end hide *)


(* [27] ============ APPLY REDUCE ============ *)

(**

  The following rule called the ``apply reduce'' rule is the
  computation rule for applications.
<<
   H |- (\x.t)s = u in T

     By applyReduce ()

     H |- t[x\s] = u in T
>>
 *)

Definition rule_apply_reduce {o}
           (T t s u : NTerm)
           (x : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality (mk_apply (mk_lam x t) s) u T)))
    [ mk_baresequent
        H
        (mk_conclax (mk_equality (subst t x s) u T))
    ]
    [].

Lemma rule_apply_reduce_true {o} :
  forall lib (T t s u : NTerm)
         (x   : NVar)
         (H   : @barehypotheses o)
         (bc1 : disjoint (free_vars s) (bound_vars t)),
    rule_true lib (rule_apply_reduce T t s u x H).
Proof.
  intros.
  unfold rule_apply_reduce, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent H (mk_conclax (mk_equality (subst t x s) u T)))
                   (inl eq_refl));
    simpl; intros hyp1.
  destruct hyp1 as [ ws1 hyp1 ].
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.
  duplicate wfct as wfi.
  rw <- @wf_equality_iff in wfct.
  destruct wfct as [ wa wfct ].
  destruct wfct as [ wu wT ].
  rw <- @wf_apply_iff in wa.
  destruct wa as [ wt ws ].
  rw <- @wf_lam_iff in wt.

  exists (@covered_axiom o (nh_vars_hyps H)); GC.

  (* We prove some simple facts on our sequents *)
  (* xxx *)
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd.

  lsubst_tac.
  allrw @member_eq.
  allrw <- @member_equality_iff.
  rw @tequality_mkc_equality in hyp0; repnd.
  
  assert (cequivc lib
            (mkc_apply
               (mkc_lam x (lsubstc_vars t wt (csub_filter s1 [x]) [x] c10))
               (lsubstc s ws s1 c6))
            (lsubstc (subst t x s) w1 s1 c1))
         as ceq1.
  (* begin proof of assert *)
  destruct_cterms; unfold cequivc; simpl.
  generalize (cequiv_beta lib x (csubst t (csub_filter s1 [x])) (csubst s s1)); intro k.
  autodimp k hyp.
  rw <- @isprog_vars_csubst_iff.
  rw @isprog_vars_eq; sp.
  rw @nt_wf_eq; sp.
  autodimp k hyp.
  apply isprogram_csubst; sp.
  rw @nt_wf_eq; sp.
  eapply cequiv_trans.
  exact k.
  rw <- @simple_csubst_subst; sp.
  apply cequiv_refl.
  apply isprogram_csubst; sp.
  unfold subst; apply lsubst_wf_iff; try (rw @nt_wf_eq; sp).
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp.
  (* end proof of assert *)

  assert (cequivc lib
            (mkc_apply
               (mkc_lam x (lsubstc_vars t wt (csub_filter s2 [x]) [x] c11))
               (lsubstc s ws s2 c9))
            (lsubstc (subst t x s) w1 s2 c0))
         as ceq2.
  (* begin proof of assert *)
  destruct_cterms; unfold cequivc; simpl.
  generalize (cequiv_beta lib x (csubst t (csub_filter s2 [x])) (csubst s s2)); intro k.
  autodimp k hyp.
  rw <- @isprog_vars_csubst_iff.
  rw @isprog_vars_eq; sp.
  rw @nt_wf_eq; sp.
  autodimp k hyp.
  apply isprogram_csubst; sp.
  rw @nt_wf_eq; sp.
  eapply cequiv_trans.
  exact k.
  rw <- @simple_csubst_subst; sp.
  apply cequiv_refl.
  apply isprogram_csubst; sp.
  unfold subst; apply lsubst_wf_iff; try (rw @nt_wf_eq; sp).
  unfold wf_sub, sub_range_sat; simpl; sp; cpx; rw @nt_wf_eq; sp.
  (* end proof of assert *)


  (* we start proving our conclusion *)
  dands; try (complete sp).
  apply @tequality_mkc_equality_if_equal; auto.
  
  eapply @equality_respects_cequivc_left.
  apply cequivc_sym.  exact ceq1.
  apply @equality_sym.
  eapply @equality_respects_cequivc_left.
  apply cequivc_sym.
  exact ceq2.
  apply @equality_sym. apply hyp4; apply equality_refl in hyp1; auto.
  apply hyp0. apply equality_sym in hyp1; apply equality_refl in hyp1; auto.
  
  eapply @equality_respects_cequivc_left.
  apply cequivc_sym.
  exact ceq1.
  sp.
Qed.

(* begin hide *)



(* end hide *)


(* [28] ============ FUNCTION EXTENSIONALITY ============ *)

(**

  The following rule called the ``function extensionality rule''
  states that the equality between functions in Nuprl is extensional.
<<
   H |- f1 = f2 in x:A->B

     By functionExtensionality lvl(i) z ()

     H z : A |- f1 z = f2 z in B[x\z]
     H |- A = A in Type(i)
>>
 *)

Definition rule_function_extensionality {o}
           (A B f1 f2 : NTerm)
           (x z : NVar)
           (i : nat)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_baresequent
       H
       (mk_conclax (mk_equality f1 f2 (mk_function A x B))))
    [ mk_baresequent
        (snoc H (mk_hyp z A))
        (mk_conclax (mk_equality
                       (mk_apply f1 (mk_var z))
                       (mk_apply f2 (mk_var z))
                       (subst B x (mk_var z)))),
      mk_baresequent
        H
        (mk_conclax (mk_equality A A (mk_uni i))) ]
    [sarg_var z].

Lemma rule_function_extensionality_true {o} :
  forall lib (A B f1 f2 : NTerm)
         (x z : NVar)
         (i   : nat)
         (H   : @barehypotheses o)
         (bc1 : !LIn z (bound_vars B)),
    rule_true lib (rule_function_extensionality A B f1 f2 x z i H).
Proof.
  intros.
  unfold rule_function_extensionality, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  generalize (hyps (mk_baresequent (snoc H (mk_hyp z A))
                                  (mk_conclax (mk_equality
                                                 (mk_apply f1 (mk_var z))
                                                 (mk_apply f2 (mk_var z))
                                                 (subst B x (mk_var z)))))
                   (inl eq_refl))
             (hyps (mk_baresequent H (mk_conclax (mk_equality A A (mk_uni i))))
                   (inr (inl eq_refl)));
    simpl; intros hyp1 hyp2.
  destruct hyp1 as [ ws1 hyp1 ].
  destruct hyp2 as [ ws2 hyp2 ].
  destseq; allsimpl; proof_irr; GC.

  allunfold @closed_type; allunfold @closed_extract; allsimpl.
  duplicate wfct as wfi.
  rw <- @wf_equality_iff in wfct.
  destruct wfct as [ wf1 wfct ].
  destruct wfct as [ wf2 wfct ].
  rw <- @wf_function_iff in wfct.
  destruct wfct as [ wA wB ].

  exists (@covered_axiom o (nh_vars_hyps H)); GC.

  (* We prove some simple facts on our sequents *)
  assert ((z <> x -> !LIn z (free_vars B))
          # !LIn z (free_vars f1)
          # !LIn z (free_vars f2)
          # !LIn z (free_vars A)
          # !LIn z (vars_hyps H)) as vhyps.

  clear hyp1 hyp2.
  dwfseq.
  sp;
  try (complete (generalize (cg z); sp;
                 allrw in_remove_nvars; allsimpl;
                 autodimp X0 h; sp));
  try (complete (generalize (cg0 z); sp;
                 allrw in_remove_nvars; allsimpl;
                 autodimp X0 h; sp));
  try (complete (generalize (cg1 z); sp;
                 allrw in_remove_nvars; allsimpl;
                 autodimp X0 h; sp));
  try (complete (apply_in_hyp p;
                 generalize (subvars_hs_vars_hyps H); intro sv;
                 rw subvars_prop in sv;
                 apply sv in p; sp)).

  destruct vhyps as [ nzB  vhyps ].
  destruct vhyps as [ nzf1 vhyps ].
  destruct vhyps as [ nzf2 vhyps ].
  destruct vhyps as [ nzA  nzH ].
  (* done with proving these simple facts *)

  (* we now start proving the sequent *)
  vr_seq_true.

  lift_lsubst.
  rw @member_eq.
  rw <- @member_equality_iff.

  assert (tequality lib
            (mkc_function (lsubstc A wA s1 c4) x
                          (lsubstc_vars B wB (csub_filter s1 [x]) [x] c5))
            (mkc_function (lsubstc A wA s2 c6) x
                          (lsubstc_vars B wB (csub_filter s2 [x]) [x] c7))) as eqfunc.

  rw @tequality_function.

  split.

  (* First, we prove that the a's are types *)
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2.
  exrepd.
  lift_lsubst in t.
  lift_lsubst in e.
  rw @member_eq in e.
  rw <- @member_equality_iff in e.
  applydup @equality_in_uni in e as e'.
  rw @fold_type in e'.
  apply @equality_commutes2 in t; try (complete auto).
  apply @equality_in_uni in t; sp.

  (* Then we prove that the b's are type families *)
  intros a a' eqaa'.
  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s1 (z, a)) (snoc s2 (z, a'))); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  (* we have to prove the functionality of our hypotheses *)
  apply hyps_functionality_snoc2; simpl; try (complete sp).
  introv eq s.
  vr_seq_true in hyp2.
  generalize (hyp2 s1 s' eqh s); clear hyp2; intro hyp2.
  exrepd.
  lift_lsubst in t.
  lift_lsubst in e.
  rw @member_eq in e.
  rw <- @member_equality_iff in e.
  applydup @equality_in_uni in e as e'.
  rw @fold_type in e'.
  apply @equality_commutes2 in t; try (complete auto).
  apply @equality_in_uni in t; sp.

  (* we have to prove the similarity of our hypotheses *)
  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  exists s1 s2 a a' wA c4; sp.

  (* we can now use hyp1 *)
  exrepnd; lsubst_tac.

  (* we use hyp0 *)
  rw @tequality_mkc_equality in hyp0; repnd.

  (* we use hyp3 *)
  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s1 (z, a)) cT1
          = substc a x (lsubstc_vars B wB (csub_filter s1 [x]) [x] c5)) as eq1
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq1 in hyp3.

  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s2 (z, a')) cT2
          = substc a' x (lsubstc_vars B wB (csub_filter s2 [x]) [x] c7)) as eq2
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq2 in hyp3.

  sp.


  (* we prove the membership *)
  assert (forall a a' s1 s2,
            hyps_functionality lib s1 H
            -> similarity lib s1 s2 H
            -> {c1f : cover_vars f1 s1
                , {c2f : cover_vars f2 s2
                , {c1A : cover_vars A s1
                , {c1B : cover_vars_upto B (csub_filter s1 [x]) [x]
                , equality lib a a' (lsubstc A wA s1 c1A)
                  -> equality lib
                       (mkc_apply (lsubstc f1 wf1 s1 c1f) a)
                       (mkc_apply (lsubstc f2 wf2 s2 c2f) a')
                       (substc a x (lsubstc_vars B wB (csub_filter s1 [x]) [x] c1B))}}}}) as eqlam.
  introv eqh0 sim0.

  assert (cover_vars f1 s0) as c1f1.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allrw @cover_vars_eq.
  allrw.
  rw sim2 in c1; sp.

  assert (cover_vars f1 s3) as c2f1.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allrw @cover_vars_eq.
  allrw.
  rw sim2 in c1; sp.

  assert (cover_vars f2 s0) as c1f2.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allrw @cover_vars_eq.
  allrw.
  rw sim2 in c2; sp.

  assert (cover_vars f2 s3) as c2f2.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allrw @cover_vars_eq.
  allrw.
  rw sim2 in c2; sp.

  assert (cover_vars_upto B (csub_filter s0 [x]) [x]) as cB0.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allunfold @cover_vars_upto.
  allrw @dom_csub_csub_filter.
  allrw.
  rw sim in c7; sp.

  assert (cover_vars_upto B (csub_filter s3 [x]) [x]) as cB3.
  clear eqfunc.
  allapply @similarity_dom; repnd.
  allunfold @cover_vars_upto.
  allrw @dom_csub_csub_filter.
  allrw.
  rw sim in c7; sp.

  assert (cover_vars A s0) as cA0.
  clear eqfunc.
  allrw @cover_vars_eq.
  allapply @similarity_dom; repnd.
  allrw.
  rw sim in c6; sp.

  assert (cover_vars A s3) as cA3.
  clear eqfunc.
  allrw @cover_vars_eq.
  allapply @similarity_dom; repnd.
  allrw.
  rw sim in c6; sp.

  exists c1f1 c2f2 cA0 cB0.
  introv eqaa'.

  vr_seq_true in hyp1.
  generalize (hyp1 (snoc s0 (z, a)) (snoc s3 (z, a'))); clear hyp1; intro hyp1.
  autodimp hyp1 hyp.

  (* we have to prove the functionality of our hypotheses *)
  apply hyps_functionality_snoc2; simpl; try (complete sp).
  introv eq s.
  vr_seq_true in hyp2.
  generalize (hyp2 s0 s' eqh0 s); clear hyp2; intro hyp2.
  exrepd.
  lift_lsubst in t.
  lift_lsubst in e.
  rw @member_eq in e.
  rw <- @member_equality_iff in e.
  applydup @equality_in_uni in e as e'.
  rw @fold_type in e'.
  apply @equality_commutes2 in t; try (complete auto).
  apply @equality_in_uni in t; sp.

  (* we have to prove the similarity of our hypotheses *)
  autodimp hyp1 hyp.
  rw @similarity_snoc; simpl.
  exists s0 s3 a a' wA cA0; sp.

  (* we can now use hyp1 *)
  exrepnd; lsubst_tac.
  rw @tequality_mkc_equality in hyp0; repnd.
  rw @member_eq in hyp1.
  rw <- @member_equality_iff in hyp1.
  clear_irr; GC.

  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s0 (z, a)) cT1
          = substc a x (lsubstc_vars B wB (csub_filter s0 [x]) [x] cB0)) as eq1
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  allrw eq1.
  clear eq1.

  assert (lsubstc (subst B x (mk_var z)) wT0 (snoc s3 (z, a')) cT2
          = substc a' x (lsubstc_vars B wB (csub_filter s3 [x]) [x] cB3)) as eq2
         by (apply lsubstc_subst_snoc_eq; try (complete sp);
             allapply @similarity_dom; exrepd; allrw; sp).

  rewrite eq2 in hyp3.
  clear eq2.
  eapply equality_trans. exact hyp1. apply hyp0.
  apply equality_sym in hyp1; apply equality_refl in hyp1; auto.


  (* a few useful assertions *)
  assert (similarity lib s1 s1 H)
         as sim1
         by (allapply @similarity_refl; sp).
  assert (similarity lib s2 s2 H)
         as sim2
         by (apply @similarity_sym in sim; allapplydup @similarity_refl; sp;
             apply eqh in sim; sp).
  assert (hyps_functionality lib s2 H)
         as eqh2
         by (apply @similarity_hyps_functionality_trans with (s1 := s1); sp).


  (* we start proving our conclusion *)
  rw @equality_in_function2.
  dands; try (complete sp).


  (* tequality *)
  apply @tequality_mkc_equality_if_equal.
  dands; try (complete sp).

  (* application in B *)
  rw @equality_in_function2.
  split; try (complete (apply @tequality_refl in eqfunc; sp)).
  introv e.
  assert (equality lib a' a' (lsubstc A wA s2 c6))
         as e'
         by (apply @equality_sym in e; apply @equality_refl in e;
             rw @tequality_function in eqfunc; repnd;
             eapply @tequality_preserving_equality;
             try (exact e); sp).

  generalize (eqlam a a' s1 s2 eqh sim); intro k1; exrepnd; clear_irr; sp.
  generalize (eqlam a' a' s2 s2 eqh2 sim2); intro k2; exrepnd; clear_irr; sp.

  eapply @equality_trans; sp.
  exact k1.
  apply @equality_sym.
  eapply @tequality_preserving_equality.
  exact k2.
  apply @tequality_sym.
  rw @tequality_function in eqfunc; repnd; sp.

  (* application in B *)
  rw @equality_in_function2.
  split; try (complete (apply @tequality_refl in eqfunc; sp)).
  introv e.
  assert (equality lib a a (lsubstc A wA s1 c4)) as e' by (allapply @equality_refl; sp).

  generalize (eqlam a a' s1 s2 eqh sim); intro k1; exrepnd; clear_irr; sp.
  generalize (eqlam a a s1 s1 eqh sim1); intro k2; exrepnd; clear_irr; sp.

  eapply @equality_trans; sp.
  apply equality_sym.
  exact k2.
  auto.


  (* type *)
  apply @tequality_refl in eqfunc; sp.


  (* application in B *)
  introv e.
  generalize (eqlam a a' s1 s1 eqh sim1); intro k; exrepnd; clear_irr; sp.
Qed.

(* end hide *)
