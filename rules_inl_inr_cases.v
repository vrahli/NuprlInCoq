(*

  Copyright 2014 Cornell University

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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export rules_cft.
(** printing |- $\vdash$ *)
(** printing ->  $\rightarrow$ *)
(* begin hide *)
(* end hide *)

(**

  We now prove some rules involving our canonical form tests.
  In this file:  isinl  and  isinr

 *)
Definition mk_not_inl {o} u v (t : @NTerm o) :=
  mk_uall
    mk_base
    u
    (mk_uall
       mk_base
       v
       (mk_cequiv
          (mk_isinl t (mk_var u) (mk_var v))
          (mk_var v))).

Definition mk_not_inr {o} u v (t : @NTerm o) :=
  mk_uall
    mk_base
    u
    (mk_uall
       mk_base
       v
       (mk_cequiv
          (mk_isinr t (mk_var u) (mk_var v))
          (mk_var v))).

Lemma wf_mk_not_inl {o} :
  forall u v t, @wf_term o t -> wf_term (mk_not_inl u v t).
Proof.
  introv wt.
  repeat (apply @wf_isect); eauto 3 with slow.
  apply wf_cequiv; eauto 3 with slow.
  apply wf_isinl; eauto 3 with slow.
Qed.

Lemma wf_mk_not_inr {o} :
  forall u v t, @wf_term o t -> wf_term (mk_not_inr u v t).
Proof.
  introv wt.
  repeat (apply @wf_isect); eauto 3 with slow.
  apply wf_cequiv; eauto 3 with slow.
  apply wf_isinl; eauto 3 with slow.
Qed.

Lemma cover_vars_eta_inl {p} :
  forall t s, cover_vars (@mk_eta_inl p t) s <=> cover_vars t s.
Proof.
  introv.
  rw @cover_vars_inl.
  allrw @cover_vars_decide.
  allrw @cover_vars_upto_var.
  allrw in_app_iff; simpl; split; sp.
Qed.

Lemma cover_vars_eta_inr {p} :
  forall t s, cover_vars (@mk_eta_inr p t) s <=> cover_vars t s.
Proof.
  introv.
  rw @cover_vars_inr.
  allrw @cover_vars_decide.
  allrw @cover_vars_upto_var.
  allrw in_app_iff; simpl; split; sp.
Qed.

Lemma subst_isinl {p} :
  forall t a b x u,
    @isprogram p u
    -> subst (mk_isinl t a b) x u
       = mk_isinl (subst t x u) (subst a x u) (subst b x u).
Proof.
  introv ipu.
  destruct ipu as [cl wf].
  unfold subst.
  change_to_lsubst_aux4; simpl; allrw app_nil_r; allrw; sp.
Qed.

Lemma subst_isinr {p} :
  forall t a b x u,
    @isprogram p u
    -> subst (mk_isinr t a b) x u
       = mk_isinr (subst t x u) (subst a x u) (subst b x u).
Proof.
  introv ipu.
  destruct ipu as [cl wf].
  unfold subst.
  change_to_lsubst_aux4; simpl; allrw app_nil_r; allrw; sp.
Qed.

Lemma cequiv_can_test {p} :
  forall lib test (t1 a1 b1 t2 a2 b2 : @NTerm p),
    cequiv lib t1 t2
    -> cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib (mk_can_test test t1 a1 b1) (mk_can_test test t2 a2 b2).
Proof.
  introv c1 c2 c3.
  applydup @cequiv_isprogram in c1.
  applydup @cequiv_isprogram in c2.
  applydup @cequiv_isprogram in c3.
  repnd.
  unfold mk_can_test, nobnd.
  repeat prove_cequiv; auto.
Qed.

Lemma cequiv_isinl {p} :
  forall lib (t1 a1 b1 t2 a2 b2 : @NTerm p),
    cequiv lib t1 t2
    -> cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib (mk_isinl t1 a1 b1) (mk_isinl t2 a2 b2).
Proof.
  introv c1 c2 c3.
  apply cequiv_can_test; auto.
Qed.

Lemma cequiv_isinr {p} :
  forall lib (t1 a1 b1 t2 a2 b2 : @NTerm p),
    cequiv lib t1 t2
    -> cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib (mk_isinr t1 a1 b1) (mk_isinr t2 a2 b2).
Proof.
  introv c1 c2 c3.
  apply cequiv_can_test; auto.
Qed.

Lemma isprogram_eta_inl {p} :
  forall t : @NTerm p, isprogram (mk_eta_inl t) <=> isprogram t.
Proof.
  introv.
  rw <- @isprogram_inl_iff.
  rw @isprogram_outl; sp.
Qed.

Lemma isprogram_eta_inr {p} :
  forall t : @NTerm p, isprogram (mk_eta_inr t) <=> isprogram t.
Proof.
  introv.
  rw <- @isprogram_inr_iff.
  rw @isprogram_outr; sp.
Qed.

Lemma cequivc_mkc_isinl_of_inl {p} :
  forall lib (t a b : @CTerm p),
    cequivc lib t (mkc_eta_inl t)
    -> cequivc lib (mkc_isinl t a b) a.
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allrw @isprog_eq.
  assert (cequiv lib (mk_isinl x1 x0 x) (mk_isinl (mk_eta_inl x1) x0 x))
         as c' by (apply cequiv_isinl; sp; try (complete (apply cequiv_refl; sp))).
  apply cequiv_trans with (b := mk_isinl (mk_eta_inl x1) x0 x); auto.
  apply reduces_to_implies_cequiv; sp.
  { apply isprogram_isinl; sp.
    apply isprogram_eta_inl; sp. }
  apply reduces_to_if_step.
  simpl; sp.
Qed.

Lemma cequivc_mkc_isinr_of_inr {p} :
  forall lib (t a b : @CTerm p),
    cequivc lib t (mkc_eta_inr t)
    -> cequivc lib (mkc_isinr t a b) a.
Proof.
  introv c.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allrw @isprog_eq.
  assert (cequiv lib (mk_isinr x1 x0 x) (mk_isinr (mk_eta_inr x1) x0 x))
         as c' by (apply cequiv_isinr; sp; try (complete (apply cequiv_refl; sp))).
  apply cequiv_trans with (b := mk_isinr (mk_eta_inr x1) x0 x); auto.
  apply reduces_to_implies_cequiv; sp.
  { apply isprogram_isinr; sp.
    apply isprogram_eta_inr; sp. }
  apply reduces_to_if_step.
  simpl; sp.
Qed.

Lemma mk_not_inl_red {o} :
  forall u v (t : @NTerm o),
    mk_not_inl u v t
    = mk_uall mk_base u
              (mk_uall mk_base v
                       (mk_cequiv
                          (mk_isinl t (mk_var u) (mk_var v))
                          (mk_var v))).
Proof.
  introv; auto.
Qed.

Lemma mk_not_inr_red {o} :
  forall u v (t : @NTerm o),
    mk_not_inr u v t
    = mk_uall mk_base u
              (mk_uall mk_base v
                       (mk_cequiv
                          (mk_isinr t (mk_var u) (mk_var v))
                          (mk_var v))).
Proof.
  introv; auto.
Qed.

Lemma implies_cequivc_isinl {p} :
  forall lib a1 b1 c1 a2 b2 c2,
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> @cequivc p lib c1 c2
    -> cequivc lib (mkc_isinl a1 b1 c1) (mkc_isinl a2 b2 c2).
Proof.
  unfold cequivc.
  introv ceqa ceqb ceqc.
  destruct_cterms.
  allsimpl.
  apply cequiv_isinl; auto.
Qed.

Lemma implies_cequivc_isinr {p} :
  forall lib a1 b1 c1 a2 b2 c2,
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> @cequivc p lib c1 c2
    -> cequivc lib (mkc_isinr a1 b1 c1) (mkc_isinr a2 b2 c2).
Proof.
  unfold cequivc.
  introv ceqa ceqb ceqc.
  destruct_cterms.
  allsimpl.
  apply cequiv_isinr; auto.
Qed.

Lemma cover_vars_mk_not_inl {o} :
  forall u v t s, @cover_vars o t s -> cover_vars (mk_not_inl u v t) s.
Proof.
  introv cvt.
  apply cover_vars_isect; dands; eauto 3 with slow.
  apply cover_vars_upto_isect; dands; eauto 3 with slow.
  apply cover_vars_upto_cequiv; dands; eauto 3 with slow.
  - apply cover_vars_upto_ispair; dands; eauto 3 with slow.
    + unfold cover_vars_upto.
      rw @cover_vars_eq in cvt.
      allrw subvars_eq; introv i.
      apply cvt in i.
      simpl.
      allrw @dom_csub_csub_filter.
      allrw in_remove_nvars.
      destruct (deq_nvar v x) as [d1|d1]; tcsp.
      destruct (deq_nvar u x) as [d2|d2]; tcsp.
      allrw in_single_iff.
      right; right; sp.
    + apply cover_vars_upto_var; simpl; tcsp.
    + apply cover_vars_upto_var; simpl; tcsp.
  - apply cover_vars_upto_var; simpl; tcsp.
Qed.

Lemma cover_vars_mk_not_inr {o} :
  forall u v t s, @cover_vars o t s -> cover_vars (mk_not_inr u v t) s.
Proof.
  introv cvt.
  apply cover_vars_isect; dands; eauto 3 with slow.
  apply cover_vars_upto_isect; dands; eauto 3 with slow.
  apply cover_vars_upto_cequiv; dands; eauto 3 with slow.
  - apply cover_vars_upto_ispair; dands; eauto 3 with slow.
    + unfold cover_vars_upto.
      rw @cover_vars_eq in cvt.
      allrw subvars_eq; introv i.
      apply cvt in i.
      simpl.
      allrw @dom_csub_csub_filter.
      allrw in_remove_nvars.
      destruct (deq_nvar v x) as [d1|d1]; tcsp.
      destruct (deq_nvar u x) as [d2|d2]; tcsp.
      allrw in_single_iff.
      right; right; sp.
    + apply cover_vars_upto_var; simpl; tcsp.
    + apply cover_vars_upto_var; simpl; tcsp.
  - apply cover_vars_upto_var; simpl; tcsp.
Qed.

(* [18] ============ ISINL CASES ============ *)

(**

 We state the isinlCases rule as follows:
<<
   H |- C ext isinl(t,ea,eb)[x\Ax]

     By isinlCases x z t u v

     H |- halts(t)
     H |- t in Base
     H x : t ~ inl (outl t) |- C ext ea
     H x : uall u v : Base, isinl(t,u,v) ~ v |- C ext eb
>>

  This rule allows one to do a proof by case on whether or not a term
  is injection-left.  Therefore, we need to know that the term computes to a
  value.  Also, because on this rule, the [t] is provided by the user
  and is used in the final extract, we have to ensure that [t] only
  depends on the non-hidden variables of [H].  This is done by the
  side-condition [sarg_term t]

 *)

Definition rule_isinl_cases {o}
           (C t ea eb : NTerm)
           (x u v : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_bsequent H (mk_concl C (subst (mk_isinl t ea eb) x mk_axiom)))
    [ mk_bsequent H (mk_conclax (mk_halts t)),
      mk_bsequent H (mk_conclax (mk_member t mk_base)),
      mk_bsequent (snoc H (mk_hyp x (mk_cequiv t (mk_inl (mk_outl t)))))
                    (mk_concl C ea),
      mk_bsequent (snoc H (mk_hyp x (mk_not_inl u v t)))
                    (mk_concl C eb)
    ]
    [sarg_term t].

Lemma rule_isinl_cases_true {o} :
  forall lib (C t ea eb : NTerm),
  forall x u v : NVar,
  forall H : @barehypotheses o,
  forall sc1 : !LIn v (vars_hyps H),
  forall sc2 : !LIn u (vars_hyps H),
  forall sc3 : v <> u,
    rule_true lib (rule_isinl_cases
                 C t ea eb
                 x u v
                 H).
Proof.
  unfold rule_isinl_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs.
  generalize (cargs (sarg_term t)); clear cargs; rw in_single_iff; intro argt.
  autodimp argt hyp.
  unfold arg_constraints in argt.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destruct Hyp2 as [wf4 hyp4].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.

  assert (covered (subst (mk_isinl t ea eb) x mk_axiom) (nh_vars_hyps H)) as cv.
  clear hyp1 hyp2 hyp3 hyp4.
  dwfseq.
  introv i.
  generalize (eqvars_free_vars_disjoint (mk_isinl t ea eb) [(x,mk_axiom)]); introv e.
  rw eqvars_prop in e; apply e in i; clear e.
  rw in_app_iff in i; rw in_remove_nvars in i; simpl in i.
  repeat (rw remove_nvars_nil_l in i); rw app_nil_r in i; repeat (rw in_app_iff in i).
  repeat (rw memvar_app in i); rw not_over_or in i.
  revert i; boolvar; intro i; simpl in i; repdors; repnd; repdors;
  try (complete sp); try (complete (discover; allrw in_snoc; repdors; sp)).

  exists cv.
  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps H)
          # !LIn x (free_vars t)
          # !LIn x (free_vars C)
          # !LIn u (free_vars t)
          # !LIn v (free_vars t)) as vhyps.

  clear hyp1 hyp2 hyp3 hyp4.
  dwfseq.
  sp.

  destruct vhyps as [ nixH vhyps ].
  destruct vhyps as [ nixt vhyps ].
  destruct vhyps as [ nixC vhyps ].
  destruct vhyps as [ niut nivt ].
  (* done with proving these simple facts *)

  vr_seq_true.

  dup hyp1 as halts.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd; proof_irr; GC.

  lsubst_tac.
  rw @member_eq in hyp1.
  rw @tequality_mkc_halts in hyp0.
  rw <- @member_halts_iff in hyp1.

  spcast.
  generalize (isinl_cases_c lib (lsubstc t w1 s1 c1)); introv isp; autodimp isp hyp.
  destruct isp as [isl | nisl]; exrepnd.
  


  (* in the first case, t computes to a inl *)
  applydup @computes_to_inl_eta_c in isl0.
  clear hyp4.
  vr_seq_true in hyp3.
  generalize (hyp3 (snoc s1 (x, mkc_axiom)) (snoc s2 (x, mkc_axiom))); clear hyp3; intro hyp3.

  (* we prove the hyps_functionality part of hyp3 *)
  autodimp hyp3 hyp.
  introv sim'.
  rw @similarity_snoc in sim'; simpl in sim'; exrepnd; subst; cpx.
  lsubst_tac.
  apply equality_refl in sim'1.
  rw <- @member_cequiv_iff in sim'1.

  assert (cover_vars (mk_cequiv t (mk_eta_inl t)) s2a)
         as p2
         by (apply cover_vars_change_sub with (sub1 := s1a); auto;
             allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists s1a s2a (@mkc_axiom o) t2 w p p2; sp.
  lsubst_tac.
  apply tequality_mkc_cequiv.
  split; intro e; try (complete sp).

  vr_seq_true in hyp2.
  generalize (hyp2 s1a s2a eqh sim'3); clear hyp2; intro hyp2; exrepnd; proof_irr; GC.
  lsubst_tac.
  clear hyp2.
  rw @tequality_mkc_member_base in hyp3.
  spcast.
  apply @cequivc_eta_inl_replace with (t := lsubstc t w1 s1a c1); auto.

  (* we prove the similarity part of hyp3 *)
  autodimp hyp3 hyp.
  rw @similarity_snoc; simpl.
  assert (wf_term (mk_cequiv t (mk_eta_inl t)))
         as wep by (apply wf_cequiv; sp).

  assert (cover_vars (mk_cequiv t (mk_eta_inl t)) s1)
         as cep by (rw @cover_vars_cequiv; rw @cover_vars_eta_inl; sp).

  exists s1 s2 (@mkc_axiom o) (@mkc_axiom o) wep cep; sp.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_cequiv_iff.
  spcast; sp.

  (* now we start using hyp3 *)
  exrepnd.
  lsubst_tac.
  dands; auto.

  revert dependent pt1.
  revert dependent pt2.
  revert dependent wfce.
  repeat (rw @subst_isinl; try (complete sp)).

  generalize (lsubst_trivial t [(x,mk_axiom)]); intro e.
  autodimp e hyp; try (complete (simpl; sp; cpx)).
  rw @fold_subst in e.
  rw e; clear e.

  introv.
  lsubst_tac.

  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd; proof_irr; GC.
  lsubst_tac.
  clear hyp2.
  rw @tequality_mkc_member_base in hyp5.
  spcast.
  applydup @cequivc_eta_inl_replace in hyp5 as cep; auto.

  apply equality_respects_cequivc_left with (t1 := lsubstc ea wfce1 (snoc s1 (x, mkc_axiom)) pt4);
    try (apply equality_respects_cequivc_right with (t2 := lsubstc ea wfce1 (snoc s2 (x, mkc_axiom)) pt5); auto).

  { apply cequivc_sym.
    apply @cequivc_trans with (b := lsubstc (subst ea x mk_axiom) w2 s1 c3).
    apply cequivc_mkc_isinl_of_inl; auto.
    apply cequivc_eq_weak.

    assert (cover_vars_upto ea (csub_filter s1 [x]) [x])
      as cvea1
        by (generalize (cover_vars_csubst3 ea [(x,mkc_axiom)] s1); intro e; simpl in e; apply e;
            unfold csubst; simpl; auto).

    generalize (simple_lsubstc_subst
                  mk_axiom x ea w2 s1 c3 wfce3 pt0 wfce1 cvea1); intro e1.
    autodimp e1 hyp; try (complete (simpl; sp)).

    generalize (simple_substc2 mkc_axiom x ea s1 wfce1 pt4 cvea1); intro e2.
    autodimp e2 hyp; try (complete (allapply @similarity_dom; repnd; allrw; sp)).

    lsubst_tac.
    rw <- e1 in e2; auto. }

  { apply cequivc_sym.
    apply @cequivc_trans with (b := lsubstc (subst ea x mk_axiom) w2 s2 c5).
    apply cequivc_mkc_isinl_of_inl; auto.
    apply cequivc_eq_weak.

    assert (cover_vars_upto ea (csub_filter s2 [x]) [x])
      as cvea1
        by (generalize (cover_vars_csubst3 ea [(x,mkc_axiom)] s2); intro e; simpl in e; apply e;
            unfold csubst; simpl; auto).

    generalize (simple_lsubstc_subst
                  mk_axiom x ea w2 s2 c5 wfce3 pt3 wfce1 cvea1); intro e1.
    autodimp e1 hyp; try (complete (simpl; sp)).

    generalize (simple_substc2 mkc_axiom x ea s2 wfce1 pt5 cvea1); intro e2.
    autodimp e2 hyp; try (complete (allapply @similarity_dom; repnd; allrw; sp)).

    lsubst_tac.
    rw <- e1 in e2; auto. }


  (* In the 2nd branch, we assume that t does not compute to a inl *)
  clear hyp3.
  vr_seq_true in hyp4.
  generalize (hyp4 (snoc s1 (x, mkc_axiom)) (snoc s2 (x, mkc_axiom))); clear hyp4; intro hyp4.

  (* we prove the hyps_functionality part of hyp4 *)
  autodimp hyp4 hyp.

  introv sim'.
  rw @similarity_snoc in sim'; simpl in sim'; exrepnd; cpx.
  revert w p sim'1.
  rewrite mk_not_inl_red; auto; introv equ.
  allunfold @mk_uall.
  lsubst_tac.
  rw @equality_in_isect in equ; repnd.
  rw @eq_hyps_snoc; simpl.
  assert (cover_vars
            (mk_isect mk_base u
                      (mk_isect mk_base v
                                (mk_cequiv (mk_isinl t (mk_var u) (mk_var v)) (mk_var v))))
            s2a)
    as cv2
      by (apply cover_vars_change_sub with (sub1 := s1a); auto;
          allapply @similarity_dom; repnd; allrw; auto).
  exists s1a s2a (@mkc_axiom o) t2 w p cv2; dands; auto.
  lsubst_tac.
  rw @tequality_isect; dands; auto.
  introv eqa.

  assert (!LIn u (dom_csub s1a)) as niu1 by (allapply @similarity_dom; repnd; allrw; auto).
  assert (!LIn u (dom_csub s2a)) as niu2 by (allapply @similarity_dom; repnd; allrw; auto).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  apply tequality_isect; dands; auto.
  introv eqa'.

  assert (!LIn v (dom_csub (snoc s1a (u,a))))
    as niv1
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).

  assert (!LIn v (dom_csub (snoc s2a (u,a'))))
    as niv2
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).

  repeat substc_lsubstc_vars2.
  lsubst_tac.
  apply tequality_mkc_cequiv.

  vr_seq_true in hyp2.
  generalize (hyp2 s1a s2a eqh sim'3); clear hyp2; intro hyp2; exrepnd; proof_irr; GC.
  lsubst_tac.
  clear hyp2.
  rw @tequality_mkc_member_base in hyp3.

  split; intro k; spcast.
  generalize (nisl a' a'0); intro redc.
  apply reduces_toc_implies_cequivc in redc.
  apply cequivc_trans with (b := mkc_isinl (lsubstc t w1 s1a c1) a' a'0); auto.
  apply implies_cequivc_isinl; auto.
  apply cequivc_sym; auto.
  generalize (nisl a a0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.

  (* now we prove the similarity part of hyp4 *)
  autodimp hyp4 hyp.

  rw @similarity_snoc; simpl.
  exists s1 s2 (@mkc_axiom o) (@mkc_axiom o)
         (wf_mk_not_inl u v t w1) (cover_vars_mk_not_inl u v t s1 c1);
    dands; auto.
  remember (wf_mk_not_inl u v t w1).
  remember (cover_vars_mk_not_inl u v t s1 c1).
  clear Heqw Heqc.
  revert w c.
  rewrite mk_not_inl_red; auto.
  unfold mk_uall; introv.
  lsubst_tac.
  rw @equality_in_isect; dands; auto; try (apply tequality_base).

  introv eqa.

  assert (!LIn u (dom_csub s1)) as niu1 by (allapply @similarity_dom; repnd; allrw; auto).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  apply tequality_isect; dands; auto; try (apply tequality_base).
  introv eqa'.

  assert (!LIn v (dom_csub (snoc s1 (u,a))))
    as niv1
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).
  assert (!LIn v (dom_csub (snoc s1 (u,a'))))
    as niv2
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  apply tequality_mkc_cequiv.

  split; intro k; spcast.
  generalize (nisl a' a'0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.
  generalize (nisl a a0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.

  introv eqa.

  assert (!LIn u (dom_csub s1)) as niu1 by (allapply @similarity_dom; repnd; allrw; auto).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  rw @equality_in_isect; dands; auto; try (apply tequality_base).

  introv eqa'.

  assert (!LIn v (dom_csub (snoc s1 (u,a))))
    as niv1
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  apply tequality_mkc_cequiv.

  split; intro k; spcast.
  generalize (nisl a a'0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.
  generalize (nisl a a0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.

  introv eqa'.

  assert (!LIn v (dom_csub (snoc s1 (u,a))))
    as niv1
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  rw <- @member_cequiv_iff.
  spcast.
  generalize (nisl a a0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.


  (* now, we start using hyp4 *)
  exrepnd.
  lsubst_tac.
  dands; auto.

  revert dependent pt1.
  revert dependent pt2.
  revert dependent wfce.
  repeat (rw @subst_isinl; try (complete sp)).

  generalize (lsubst_trivial t [(x,mk_axiom)]); intro e.
  autodimp e hyp; try (complete (simpl; sp; cpx)).
  rw @fold_subst in e.
  rw e; clear e.

  introv.
  lsubst_tac.

  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd; proof_irr; GC.
  lsubst_tac.
  clear hyp2.
  rw @tequality_mkc_member_base in hyp5.
  spcast.
(*  applydup cequivc_eta_inl_replace in hyp5 as cep; auto.*)

  assert (!LIn x (dom_csub s1)) as nix1 by (allapply @similarity_dom; repnd; allrw; auto).
  assert (!LIn x (dom_csub s2)) as nix2 by (allapply @similarity_dom; repnd; allrw; auto).
  repeat substc_lsubstc_vars2; try (complete (simpl; sp)).
  revert c c2 c7 c8.
  lsubst_tac; introv.
  clear_irr; GC.

  apply equality_respects_cequivc_left with (t1 := lsubstc eb wfce0 (snoc s1 (x, mkc_axiom)) pt4);
    try (apply equality_respects_cequivc_right with (t2 := lsubstc eb wfce0 (snoc s2 (x, mkc_axiom)) pt5); auto).

  apply cequivc_sym.
  generalize (nisl
                (lsubstc ea wfce1 (snoc s1 (x, mkc_axiom)) c)
                (lsubstc eb wfce0 (snoc s1 (x, mkc_axiom)) pt4)); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.

  apply cequivc_sym.
  generalize (nisl
                (lsubstc ea wfce1 (snoc s2 (x, mkc_axiom)) c7)
                (lsubstc eb wfce0 (snoc s2 (x, mkc_axiom)) pt5)); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.
  apply cequivc_trans
  with (b := mkc_isinl (lsubstc t w1 s1 c1)
                        (lsubstc ea wfce1 (snoc s2 (x, mkc_axiom)) c7)
                        (lsubstc eb wfce0 (snoc s2 (x, mkc_axiom)) pt5)); auto.
  apply implies_cequivc_isinl; auto.
  apply cequivc_sym; auto.
Qed.

Definition rule_isinr_cases {o}
           (C t ea eb : NTerm)
           (x u v : NVar)
           (H : @barehypotheses o) :=
  mk_rule
    (mk_bsequent H (mk_concl C (subst (mk_isinr t ea eb) x mk_axiom)))
    [ mk_bsequent H (mk_conclax (mk_halts t)),
      mk_bsequent H (mk_conclax (mk_member t mk_base)),
      mk_bsequent (snoc H (mk_hyp x (mk_cequiv t (mk_inr (mk_outr t)))))
                    (mk_concl C ea),
      mk_bsequent (snoc H (mk_hyp x (mk_not_inr u v t)))
                    (mk_concl C eb)
    ]
    [sarg_term t].

Lemma rule_isinr_cases_true {o} :
  forall lib (C t ea eb : NTerm),
  forall x u v : NVar,
  forall H : @barehypotheses o,
  forall sc1 : !LIn v (vars_hyps H),
  forall sc2 : !LIn u (vars_hyps H),
  forall sc3 : v <> u,
    rule_true lib (rule_isinr_cases
                 C t ea eb
                 x u v
                 H).
Proof.
  unfold rule_isinr_cases, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.

  unfold args_constraints in cargs.
  generalize (cargs (sarg_term t)); clear cargs; rw in_single_iff; intro argt.
  autodimp argt hyp.
  unfold arg_constraints in argt.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  destruct Hyp  as [wf1 hyp1].
  destruct Hyp0 as [wf2 hyp2].
  destruct Hyp1 as [wf3 hyp3].
  destruct Hyp2 as [wf4 hyp4].
  destseq; allsimpl; proof_irr; GC.

  unfold closed_extract; simpl.

  assert (covered (subst (mk_isinr t ea eb) x mk_axiom) (nh_vars_hyps H)) as cv.
  clear hyp1 hyp2 hyp3 hyp4.
  dwfseq.
  introv i.
  generalize (eqvars_free_vars_disjoint (mk_isinr t ea eb) [(x,mk_axiom)]); introv e.
  rw eqvars_prop in e; apply e in i; clear e.
  rw in_app_iff in i; rw in_remove_nvars in i; simpl in i.
  repeat (rw remove_nvars_nil_l in i); rw app_nil_r in i; repeat (rw in_app_iff in i).
  repeat (rw memvar_app in i); rw not_over_or in i.
  revert i; boolvar; intro i; simpl in i; repdors; repnd; repdors;
  try (complete sp); try (complete (discover; allrw in_snoc; repdors; sp)).

  exists cv.
  (* We prove some simple facts on our sequents *)
  assert (!LIn x (vars_hyps H)
          # !LIn x (free_vars t)
          # !LIn x (free_vars C)
          # !LIn u (free_vars t)
          # !LIn v (free_vars t)) as vhyps.

  clear hyp1 hyp2 hyp3 hyp4.
  dwfseq.
  sp.

  destruct vhyps as [ nixH vhyps ].
  destruct vhyps as [ nixt vhyps ].
  destruct vhyps as [ nixC vhyps ].
  destruct vhyps as [ niut nivt ].
  (* done with proving these simple facts *)

  vr_seq_true.

  dup hyp1 as halts.
  vr_seq_true in hyp1.
  generalize (hyp1 s1 s2 eqh sim); clear hyp1; intro hyp1; exrepnd; proof_irr; GC.

  lsubst_tac.
  rw @member_eq in hyp1.
  rw @tequality_mkc_halts in hyp0.
  rw <- @member_halts_iff in hyp1.

  spcast.
  generalize (isinr_cases_c lib (lsubstc t w1 s1 c1)); introv isp; autodimp isp hyp.
  destruct isp as [isr | nisr]; exrepnd.
  


  (* in the first case, t computes to a inr *)
  applydup @computes_to_inr_eta_c in isr0.
  clear hyp4.
  vr_seq_true in hyp3.
  generalize (hyp3 (snoc s1 (x, mkc_axiom)) (snoc s2 (x, mkc_axiom))); clear hyp3; intro hyp3.

  (* we prove the hyps_functionality part of hyp3 *)
  autodimp hyp3 hyp.
  introv sim'.
  rw @similarity_snoc in sim'; simpl in sim'; exrepnd; subst; cpx.
  lsubst_tac.
  apply equality_refl in sim'1.
  rw <- @member_cequiv_iff in sim'1.

  assert (cover_vars (mk_cequiv t (mk_eta_inr t)) s2a)
         as p2
         by (apply cover_vars_change_sub with (sub1 := s1a); auto;
             allapply @similarity_dom; repnd; allrw; sp).

  rw @eq_hyps_snoc; simpl.
  exists s1a s2a (@mkc_axiom o) t2 w p p2; sp.
  lsubst_tac.
  apply tequality_mkc_cequiv.
  split; intro e; try (complete sp).

  vr_seq_true in hyp2.
  generalize (hyp2 s1a s2a eqh sim'3); clear hyp2; intro hyp2; exrepnd; proof_irr; GC.
  lsubst_tac.
  clear hyp2.
  rw @tequality_mkc_member_base in hyp3.
  spcast.
  apply @cequivc_eta_inr_replace with (t := lsubstc t w1 s1a c1); auto.

  (* we prove the similarity part of hyp3 *)
  autodimp hyp3 hyp.
  rw @similarity_snoc; simpl.
  assert (wf_term (mk_cequiv t (mk_eta_inr t)))
         as wep by (apply wf_cequiv; sp).

  assert (cover_vars (mk_cequiv t (mk_eta_inr t)) s1)
         as cep by (rw @cover_vars_cequiv; rw @cover_vars_eta_inr; sp).

  exists s1 s2 (@mkc_axiom o) (@mkc_axiom o) wep cep; sp.
  lsubst_tac.
  rw @member_eq.
  rw <- @member_cequiv_iff.
  spcast; sp.

  (* now we start using hyp3 *)
  exrepnd.
  lsubst_tac.
  dands; auto.

  revert dependent pt1.
  revert dependent pt2.
  revert dependent wfce.
  repeat (rw @subst_isinr; try (complete sp)).

  generalize (lsubst_trivial t [(x,mk_axiom)]); intro e.
  autodimp e hyp; try (complete (simpl; sp; cpx)).
  rw @fold_subst in e.
  rw e; clear e.

  introv.
  lsubst_tac.

  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd; proof_irr; GC.
  lsubst_tac.
  clear hyp2.
  rw @tequality_mkc_member_base in hyp5.
  spcast.
  applydup @cequivc_eta_inr_replace in hyp5 as cep; auto.

  apply equality_respects_cequivc_left with (t1 := lsubstc ea wfce1 (snoc s1 (x, mkc_axiom)) pt4);
    try (apply equality_respects_cequivc_right with (t2 := lsubstc ea wfce1 (snoc s2 (x, mkc_axiom)) pt5); auto).

  { apply cequivc_sym.
    apply @cequivc_trans with (b := lsubstc (subst ea x mk_axiom) w2 s1 c3).
    apply cequivc_mkc_isinr_of_inr; auto.
    apply cequivc_eq_weak.

    assert (cover_vars_upto ea (csub_filter s1 [x]) [x])
      as cvea1
        by (generalize (cover_vars_csubst3 ea [(x,mkc_axiom)] s1); intro e; simpl in e; apply e;
            unfold csubst; simpl; auto).

    generalize (simple_lsubstc_subst
                  mk_axiom x ea w2 s1 c3 wfce3 pt0 wfce1 cvea1); intro e1.
    autodimp e1 hyp; try (complete (simpl; sp)).

    generalize (simple_substc2 mkc_axiom x ea s1 wfce1 pt4 cvea1); intro e2.
    autodimp e2 hyp; try (complete (allapply @similarity_dom; repnd; allrw; sp)).

    lsubst_tac.
    rw <- e1 in e2; auto. }

  { apply cequivc_sym.
    apply @cequivc_trans with (b := lsubstc (subst ea x mk_axiom) w2 s2 c5).
    apply cequivc_mkc_isinr_of_inr; auto.
    apply cequivc_eq_weak.

    assert (cover_vars_upto ea (csub_filter s2 [x]) [x])
      as cvea1
        by (generalize (cover_vars_csubst3 ea [(x,mkc_axiom)] s2); intro e; simpl in e; apply e;
            unfold csubst; simpl; auto).

    generalize (simple_lsubstc_subst
                  mk_axiom x ea w2 s2 c5 wfce3 pt3 wfce1 cvea1); intro e1.
    autodimp e1 hyp; try (complete (simpl; sp)).

    generalize (simple_substc2 mkc_axiom x ea s2 wfce1 pt5 cvea1); intro e2.
    autodimp e2 hyp; try (complete (allapply @similarity_dom; repnd; allrw; sp)).

    lsubst_tac.
    rw <- e1 in e2; auto. }


  (* In the 2nd branch, we assume that t does not compute to a inr *)
  clear hyp3.
  vr_seq_true in hyp4.
  generalize (hyp4 (snoc s1 (x, mkc_axiom)) (snoc s2 (x, mkc_axiom))); clear hyp4; intro hyp4.

  (* we prove the hyps_functionality part of hyp4 *)
  autodimp hyp4 hyp.

  introv sim'.
  rw @similarity_snoc in sim'; simpl in sim'; exrepnd; cpx.
  revert w p sim'1.
  rewrite mk_not_inr_red; auto; introv equ.
  allunfold @mk_uall.
  lsubst_tac.
  rw @equality_in_isect in equ; repnd.
  rw @eq_hyps_snoc; simpl.
  assert (cover_vars
            (mk_isect mk_base u
                      (mk_isect mk_base v
                                (mk_cequiv (mk_isinr t (mk_var u) (mk_var v)) (mk_var v))))
            s2a)
    as cv2
      by (apply cover_vars_change_sub with (sub1 := s1a); auto;
          allapply @similarity_dom; repnd; allrw; auto).
  exists s1a s2a (@mkc_axiom o) t2 w p cv2; dands; auto.
  lsubst_tac.
  rw @tequality_isect; dands; auto.
  introv eqa.

  assert (!LIn u (dom_csub s1a)) as niu1 by (allapply @similarity_dom; repnd; allrw; auto).
  assert (!LIn u (dom_csub s2a)) as niu2 by (allapply @similarity_dom; repnd; allrw; auto).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  apply tequality_isect; dands; auto.
  introv eqa'.

  assert (!LIn v (dom_csub (snoc s1a (u,a))))
    as niv1
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).

  assert (!LIn v (dom_csub (snoc s2a (u,a'))))
    as niv2
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).

  repeat substc_lsubstc_vars2.
  lsubst_tac.
  apply tequality_mkc_cequiv.

  vr_seq_true in hyp2.
  generalize (hyp2 s1a s2a eqh sim'3); clear hyp2; intro hyp2; exrepnd; proof_irr; GC.
  lsubst_tac.
  clear hyp2.
  rw @tequality_mkc_member_base in hyp3.

  split; intro k; spcast.
  generalize (nisr a' a'0); intro redc.
  apply reduces_toc_implies_cequivc in redc.
  apply cequivc_trans with (b := mkc_isinr (lsubstc t w1 s1a c1) a' a'0); auto.
  apply implies_cequivc_isinr; auto.
  apply cequivc_sym; auto.
  generalize (nisr a a0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.

  (* now we prove the similarity part of hyp4 *)
  autodimp hyp4 hyp.

  rw @similarity_snoc; simpl.
  exists s1 s2 (@mkc_axiom o) (@mkc_axiom o)
         (wf_mk_not_inr u v t w1) (cover_vars_mk_not_inr u v t s1 c1);
    dands; auto.
  remember (wf_mk_not_inr u v t w1).
  remember (cover_vars_mk_not_inr u v t s1 c1).
  clear Heqw Heqc.
  revert w c.
  rewrite mk_not_inr_red; auto.
  unfold mk_uall; introv.
  lsubst_tac.
  rw @equality_in_isect; dands; auto; try (apply tequality_base).

  introv eqa.

  assert (!LIn u (dom_csub s1)) as niu1 by (allapply @similarity_dom; repnd; allrw; auto).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  apply tequality_isect; dands; auto; try (apply tequality_base).
  introv eqa'.

  assert (!LIn v (dom_csub (snoc s1 (u,a))))
    as niv1
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).
  assert (!LIn v (dom_csub (snoc s1 (u,a'))))
    as niv2
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  apply tequality_mkc_cequiv.

  split; intro k; spcast.
  generalize (nisr a' a'0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.
  generalize (nisr a a0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.

  introv eqa.

  assert (!LIn u (dom_csub s1)) as niu1 by (allapply @similarity_dom; repnd; allrw; auto).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  rw @equality_in_isect; dands; auto; try (apply tequality_base).

  introv eqa'.

  assert (!LIn v (dom_csub (snoc s1 (u,a))))
    as niv1
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  apply tequality_mkc_cequiv.

  split; intro k; spcast.
  generalize (nisr a a'0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.
  generalize (nisr a a0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.

  introv eqa'.

  assert (!LIn v (dom_csub (snoc s1 (u,a))))
    as niv1
      by (rw @dom_csub_snoc; simpl; rw in_snoc; rw not_over_or;
          allapply @similarity_dom; repnd; allrw; sp).
  repeat substc_lsubstc_vars2.
  lsubst_tac.
  rw <- @member_cequiv_iff.
  spcast.
  generalize (nisr a a0); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.


  (* now, we start using hyp4 *)
  exrepnd.
  lsubst_tac.
  dands; auto.

  revert dependent pt1.
  revert dependent pt2.
  revert dependent wfce.
  repeat (rw @subst_isinr; try (complete sp)).

  generalize (lsubst_trivial t [(x,mk_axiom)]); intro e.
  autodimp e hyp; try (complete (simpl; sp; cpx)).
  rw @fold_subst in e.
  rw e; clear e.

  introv.
  lsubst_tac.

  vr_seq_true in hyp2.
  generalize (hyp2 s1 s2 eqh sim); clear hyp2; intro hyp2; exrepnd; proof_irr; GC.
  lsubst_tac.
  clear hyp2.
  rw @tequality_mkc_member_base in hyp5.
  spcast.
(*  applydup cequivc_eta_inr_replace in hyp5 as cep; auto.*)

  assert (!LIn x (dom_csub s1)) as nix1 by (allapply @similarity_dom; repnd; allrw; auto).
  assert (!LIn x (dom_csub s2)) as nix2 by (allapply @similarity_dom; repnd; allrw; auto).
  repeat substc_lsubstc_vars2; try (complete (simpl; sp)).
  revert c c2 c7 c8.
  lsubst_tac; introv.
  clear_irr; GC.

  apply equality_respects_cequivc_left with (t1 := lsubstc eb wfce0 (snoc s1 (x, mkc_axiom)) pt4);
    try (apply equality_respects_cequivc_right with (t2 := lsubstc eb wfce0 (snoc s2 (x, mkc_axiom)) pt5); auto).

  apply cequivc_sym.
  generalize (nisr
                (lsubstc ea wfce1 (snoc s1 (x, mkc_axiom)) c)
                (lsubstc eb wfce0 (snoc s1 (x, mkc_axiom)) pt4)); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.

  apply cequivc_sym.
  generalize (nisr
                (lsubstc ea wfce1 (snoc s2 (x, mkc_axiom)) c7)
                (lsubstc eb wfce0 (snoc s2 (x, mkc_axiom)) pt5)); intro redc.
  apply reduces_toc_implies_cequivc in redc; auto.
  apply cequivc_trans
  with (b := mkc_isinr (lsubstc t w1 s1 c1)
                        (lsubstc ea wfce1 (snoc s2 (x, mkc_axiom)) c7)
                        (lsubstc eb wfce0 (snoc s2 (x, mkc_axiom)) pt5)); auto.
  apply implies_cequivc_isinr; auto.
  apply cequivc_sym; auto.
Qed.


(* begin hide *)

(* end hide *)


(*
*** Local Variables:
*** coq-load-path: ("." "./close/")
*** End:
*)
