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

  Authors: Vincent Rahli

*)


Require Export choice_sequence_ind.
Require Export per_props_cequiv2.
Require Export per_props_nat.
Require Export types_converge.
Require Export subst_tacs.
Require Export sequents_equality.
Require Export list. (* WTF! *)


(*

 Change this for:

   \n,s. if n = 0 then True
         if n = 1 then s(0) ~ 0
         if s(0) = 0 then True
         else *

*)
Definition nwf_pred {o} (n s : NVar) :=
  @mk_lam
    o
    n
    (mk_lam
       s
       (mk_int_eq
          (mk_var n)
          mk_zero
          mk_true
          (mk_int_eq
             (mk_var n)
             mk_one
             (mk_cequiv (mk_apply (mk_var s) mk_zero) mk_zero)
             (mk_int_eq
                (mk_apply (mk_var s) mk_zero)
                mk_zero
                mk_true
                mk_axiom)))).

Definition lam0 {o} : @NTerm o := mk_lam nvarx mk_zero.
Definition lam1 {o} : @NTerm o := mk_lam nvarx mk_one.

Hint Rewrite @lsubstc_mk_zero : slow.
Hint Rewrite @substc_mkcv_zero : slow.
Hint Rewrite @mkcv_cequiv_substc : slow.
Hint Rewrite @mkcv_apply_substc : slow.
Hint Rewrite @mkcv_true_substc : slow.

Lemma substc2_cequiv {o} :
  forall v x (w : @CTerm o) (a b : CVTerm [v,x]),
    substc2 v w x (mkcv_cequiv [v,x] a b)
    = mkcv_cequiv [v] (substc2 v w x a) (substc2 v w x b).
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl.
  repeat unfsubst.
Qed.
Hint Rewrite @substc2_cequiv : slow.

Lemma implies_approx_cequiv {p} :
  forall lib f g a b,
    approx lib f g
    -> @approx p lib a b
    -> approx lib (mk_cequiv f a) (mk_cequiv g b).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_cequiv {p} :
  forall lib f g a b,
    cequivc lib f g
    -> @cequivc p lib a b
    -> cequivc lib (mkc_cequiv f a) (mkc_cequiv g b).
Proof.
  unfold cequivc. introv H1c H2c.
  destruct_cterms. allsimpl. apply isprogram_eq in i0.
  allrw @isprog_eq.
  repnud H1c.
  repnud H2c.
  repnd.
  split; apply implies_approx_cequiv; auto.
Qed.

Lemma base_nwf_pred {o} :
  forall lib H n s f,
    s <> n
    -> wf_term f
    -> wf_hypotheses H
    -> covered f (vars_hyps H)
    -> @sequent_true2
         o
         lib
         (choice_sequence_ind_base H (nwf_pred n s) f mk_axiom).
Proof.
  introv d1 wf wfH covf.

  assert (wf_csequent (choice_sequence_ind_base H (nwf_pred n s) f mk_axiom)) as wfc.
  {
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    rw <- @wf_apply_iff.
    dands; tcsp;
    try (complete (rw @vswf_hypotheses_nil_eq; auto)).
    introv i; allrw in_app_iff; allrw in_remove_nvars; allsimpl; allrw not_over_or.
    repnd; repndors; tcsp.
  }

  exists wfc.
  vr_seq_true.
  unfold nwf_pred, lam0.
  lsubst_tac.

  dands.

  - eapply tequality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_beta2|].
    eapply tequality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_beta2|].
    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.
    repeat (rewrite mkcv_lam_substc; auto;[]).
    eapply tequality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_beta|].
    eapply tequality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_beta|].
    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    rewrite mkc_zero_eq.
    eapply tequality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_mkc_inteq_nat|].
    eapply tequality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_mkc_inteq_nat|].
    boolvar; try omega; GC;[]; eauto 3 with slow.

  - eapply cequivc_preserving_equality;[|apply cequivc_sym;apply cequivc_beta2].
    repeat lsubstc_vars_as_mkcv.
    autorewrite with slow.
    repeat (rewrite mkcv_lam_substc; auto;[]).
    eapply cequivc_preserving_equality;[|apply cequivc_sym;apply cequivc_beta].
    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.

    rewrite mkc_zero_eq.
    eapply cequivc_preserving_equality;[|apply cequivc_sym;apply cequivc_mkc_inteq_nat].
    boolvar; try omega; GC;[].

    apply equality_in_true;
    dands; spcast; auto;
    try (complete (apply computes_to_valc_refl; eauto 3 with slow)).
Qed.

Hint Rewrite @vars_hyps_snoc : slow.

Lemma isprog_vars_natk_iff {o} :
  forall (vs : list NVar) (n : @NTerm o),
    isprog_vars vs (mk_natk n) <=> isprog_vars vs n.
Proof.
  introv.
  unfold mk_natk.
  unfold mk_natk_aux.
  rw <- @isprog_vars_set_iff.
  rw <- @isprog_vars_prod.
  rw @isprog_vars_le.
  rw @isprog_vars_less_than.
  allrw <- @isprog_vars_var_iff.
  simpl; split; intro h; repnd; dands; eauto 3 with slow.
  apply isprog_vars_cons_if2 in h; auto.
  apply newvar_prop.
Qed.

Lemma isprog_vars_tnat {o} :
  forall vs, @isprog_vars o vs mk_tnat.
Proof.
  introv.
  unfold mk_tnat.
  rw <- @isprog_vars_set_iff.
  rw @isprog_vars_le.
  rw <- @isprog_vars_var_iff.
  simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_tnat : slow.

Lemma isprog_vars_mk_natk2nat {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs (mk_natk2nat t) <=> isprog_vars vs t.
Proof.
  introv.
  unfold mk_natk2nat.
  rw <- @isprog_vars_fun.
  rw @isprog_vars_natk_iff.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma isprog_vars_cequiv_iff {o} :
  forall vs (a b : @NTerm o),
    isprog_vars vs (mk_cequiv a b) <=> (isprog_vars vs a # isprog_vars vs b).
Proof.
  introv.
  allrw @isprog_vars_eq.
  simpl; autorewrite with slow.
  rw @subvars_app_l.
  allrw @nt_wf_eq.
  rw <- @wf_cequiv_iff.
  split; intro h; repnd; dands; auto.
Qed.

Lemma isprog_nwf_pred {o} :
  forall k s, @isprog o (nwf_pred k s).
Proof.
  introv; unfold nwf_pred.
  apply isprog_lam.
  apply isprog_vars_lam.
  allrw @isprog_vars_inteq.
  rw @isprog_vars_cequiv_iff.
  allrw @isprog_vars_apply.
  dands; eauto 3 with slow.
Qed.
Hint Resolve isprog_nwf_pred : slow.

Ltac clear_wf_cov :=
  match goal with
  | [ H : wf_term _ |- _ ] => clear H
  | [ H : cover_vars _ _ |- _ ] => clear H
  | [ H : cover_vars_upto _ _ _ |- _ ] => clear H
  end.

Lemma substc2_lam {o} :
  forall (v x : NVar) (w : @CTerm o) y (u : CVTerm [y,v,x]),
    y <> x
    -> alphaeqcv
         [v]
         (substc2 v w x (mkcv_lam [v, x] y u))
         (mkcv_lam
            [v]
            y
            (substc3 y v w x u)).
Proof.
  introv d.
  destruct_cterms.
  unfold alphaeqcv; simpl.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).

  simpl.
  autorewrite with slow.
  boolvar; tcsp.
Qed.

Definition mkcv_nwf_pred {o} vs (n s : NVar) :=
  @mkcv_lam
    o
    vs
    n
    (mkcv_lam
       (n :: vs)
       s
       (mkcv_inteq
          (s :: n :: vs)
          (mk_cv_app_r vs [s,n] (mk_cv_app_l [s] [n] (mkc_var n)))
          (mkcv_zero (s :: n :: vs))
          (mkcv_true (s :: n :: vs))
          (mkcv_inteq
             (s :: n :: vs)
             (mk_cv_app_r vs [s,n] (mk_cv_app_l [s] [n] (mkc_var n)))
             (mkcv_one (s :: n :: vs))
             (mkcv_cequiv
                (s :: n :: vs)
                (mkcv_apply
                   (s :: n :: vs)
                   (mk_cv_app_r (n :: vs) [s] (mkc_var s))
                   (mkcv_zero (s :: n :: vs)))
                (mkcv_zero (s :: n :: vs)))
             (mkcv_inteq
                (s :: n :: vs)
                (mkcv_apply
                   (s :: n :: vs)
                   (mk_cv_app_r (n :: vs) [s] (mkc_var s))
                   (mkcv_zero (s :: n :: vs)))
                (mkcv_zero (s :: n :: vs))
                (mkcv_true (s :: n :: vs))
                (mk_cv (s :: n :: vs) (mkc_axiom)))))).

Definition mkc_nwf_pred {o} (n s : NVar) :=
  @mkc_lam
    o
    n
    (mkcv_lam
       [n]
       s
       (mkcv_inteq
          [s,n]
          (mk_cv_app_l [s] [n] (mkc_var n))
          (mkcv_zero [s,n])
          (mkcv_true [s,n])
          (mkcv_inteq
             [s,n]
             (mk_cv_app_l [s] [n] (mkc_var n))
             (mkcv_one [s,n])
             (mkcv_cequiv
                [s,n]
                (mkcv_apply
                   [s,n]
                   (mk_cv_app_r [n] [s] (mkc_var s))
                   (mkcv_zero [s,n]))
                (mkcv_zero [s,n]))
             (mkcv_inteq
                [s,n]
                (mkcv_apply
                   [s,n]
                   (mk_cv_app_r [n] [s] (mkc_var s))
                   (mkcv_zero [s,n]))
                (mkcv_zero [s,n])
                (mkcv_true [s,n])
                (mk_cv [s,n] (mkc_axiom)))))).

Lemma cl_lsubst_nwf_pred {o} :
  forall k f (s : @Sub o),
    cl_sub s -> lsubst (nwf_pred k f) s = nwf_pred k f.
Proof.
  introv cl.
  unflsubst; simpl; autorewrite with slow.
  auto.
Qed.

Lemma cl_subst_nwf_pred {o} :
  forall k f x (t : @NTerm o),
    closed t -> subst (nwf_pred k f) x t = nwf_pred k f.
Proof.
  introv cl.
  unfold subst.
  rewrite cl_lsubst_nwf_pred; eauto 3 with slow.
Qed.

Lemma csubst_nwf_pred {o} :
  forall k f (s : @CSub o), csubst (nwf_pred k f) s = nwf_pred k f.
Proof.
  introv.
  unfold csubst.
  unflsubst; simpl; autorewrite with slow.
  auto.
Qed.
Hint Rewrite @csubst_nwf_pred : slow.

Lemma lsubstc_vars_nwf_pred_as_mkcv {o} :
  forall k f w s vs c,
    @lsubstc_vars o (nwf_pred k f) w s vs c
    = mkcv_nwf_pred vs k f.
Proof.
  introv.
  apply cvterm_eq; simpl.
  autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_vars_nwf_pred_as_mkcv : slow.

Lemma substc_nwf_pred {o} :
  forall t x k f,
    @substc o t x (mkcv_nwf_pred [x] k f)
    = mkc_nwf_pred k f.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  fold (@nwf_pred o k f).
  rewrite cl_subst_nwf_pred; eauto 3 with slow.
Qed.
Hint Rewrite @substc_nwf_pred : slow.

Lemma lsubstc_nwf_pred {o} :
  forall k f w s c,
    @lsubstc o (nwf_pred k f) w s c
    = mkc_nwf_pred k f.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  fold (@nwf_pred o k f).
  autorewrite with slow; auto.
Qed.
Hint Rewrite @lsubstc_nwf_pred : slow.

Lemma substc2_mkcv_true {o} :
  forall (u : @CTerm o) v x,
    substc2 v u x (mkcv_true [v,x])
    = mkcv_true [v].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc2_mkcv_true : slow.

Lemma computes_to_valc_mkc_inteq {o} :
  forall lib (a b c d : @CTerm o) v,
    computes_to_valc lib (mkc_inteq a b c d) v
    -> {pk1 : param_kind
        & {pk2 : param_kind
        & reduces_toc lib a (pk2termc pk1)
        # reduces_toc lib b (pk2termc pk2)
        #
        (
          (pk1 = pk2 # computes_to_valc lib c v)
          [+]
          (pk1 <> pk2 # computes_to_valc lib d v)
       ) }}.
Proof.
  introv comp.
  destruct_cterms.
  unfold computes_to_valc in comp; simpl in comp.
  apply computes_to_value_mk_int_eq in comp; eauto 2 with slow.
Qed.

Lemma isvalue_implies_isprog {o} :
  forall (t : @NTerm o), isvalue t -> isprog t.
Proof.
  introv isv.
  destruct isv; eauto 3 with slow.
Qed.

Lemma hasvaluec_implies_computes_to_valc {o} :
  forall lib (a : @CTerm o),
    hasvaluec lib a
    -> {b : CTerm & computes_to_valc lib a b}.
Proof.
  introv hv.
  destruct_cterms.
  unfold hasvaluec in hv; allsimpl.
  unfold hasvalue in hv; exrepnd.
  unfold computes_to_value in hv0; repnd.
  applydup @isvalue_implies_isprog in hv0 as isp.
  exists (mk_ct t' isp).
  unfold computes_to_valc; simpl.
  unfold computes_to_value; dands; auto.
Qed.

Lemma iscvalue_pk2termc {o} :
  forall pk, @iscvalue o (pk2termc pk).
Proof.
  introv.
  unfold iscvalue; simpl.
  destruct pk; simpl; eauto 3 with slow.
Qed.
Hint Resolve iscvalue_pk2termc : slow.

Lemma equality_in_inteq_implies {o} :
  forall lib (t1 t2 a b c d : @CTerm o),
    equality lib t1 t2 (mkc_inteq a b c d)
    -> {pk1 : param_kind
        , {pk2 : param_kind
        , ccomputes_to_valc lib a (pk2termc pk1)
        /\ ccomputes_to_valc lib b (pk2termc pk2)
        /\
        (
          (pk1 = pk2
           /\ ccequivc lib (mkc_inteq a b c d) c
           /\ equality lib t1 t2 c)
            {+}
            (pk1 <> pk2
             /\ ccequivc lib (mkc_inteq a b c d) d
             /\ equality lib t1 t2 d
            )
        ) }}.
Proof.
  introv e.
  applydup @inhabited_implies_tequality in e as t.
  apply types_converge in t; spcast.
  apply hasvaluec_implies_computes_to_valc in t.
  exrepnd.
  applydup @computes_to_valc_mkc_inteq in t0; exrepnd.
  exists pk1 pk2.
  dands; spcast; auto;
  try (apply computes_to_valc_iff_reduces_toc; dands; eauto 3 with slow).
  repndors; repnd;[left|right]; dands; auto; spcast.

  - eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;exact t0|].
    apply cequivc_sym; eauto 3 with slow.

  - eapply cequivc_preserving_equality;
    [|apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact t3].
    eapply cequivc_preserving_equality;
      [|apply computes_to_valc_implies_cequivc;exact t0].
    auto.

  - eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;exact t0|].
    apply cequivc_sym; eauto 3 with slow.

  - eapply cequivc_preserving_equality;
    [|apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact t3].
    eapply cequivc_preserving_equality;
      [|apply computes_to_valc_implies_cequivc;exact t0].
    auto.
Qed.

Lemma reduces_toc_mkc_inteq_eq {o} :
  forall lib pk (a b : @CTerm o),
    reduces_toc lib (mkc_inteq (pk2termc pk) (pk2termc pk) a b) a.
Proof.
  introv.
  destruct_cterms; unfold reduces_toc; simpl.
  apply reduces_to_if_step.
  csunf; simpl; simpl.
  rewrite pk2term_eq.
  dcwf h; simpl.
  - unfold compute_step_comp; simpl.
    rw @get_param_from_cop_pk2can; boolvar; auto; tcsp.
  - apply co_wf_false_implies_not in Heqh.
    unfold co_wf_def in Heqh; destruct Heqh; simpl.
    rw @get_param_from_cop_pk2can.
    eexists; dands; eauto.
Qed.

Lemma reduces_toc_mkc_inteq_diff {o} :
  forall lib pk1 pk2 (a b : @CTerm o),
    pk1 <> pk2 -> reduces_toc lib (mkc_inteq (pk2termc pk1) (pk2termc pk2) a b) b.
Proof.
  introv d.
  destruct_cterms; unfold reduces_toc; simpl.
  apply reduces_to_if_step.
  csunf; simpl; simpl.
  rewrite pk2term_eq.
  dcwf h; simpl.
  - rewrite pk2term_eq.
    unfold compute_step_comp; simpl.
    repeat (rw @get_param_from_cop_pk2can; boolvar; auto; tcsp).
  - apply co_wf_false_implies_not in Heqh.
    unfold co_wf_def in Heqh; destruct Heqh; simpl.
    rw @get_param_from_cop_pk2can.
    eexists; dands; eauto.
Qed.

Lemma implies_equality_in_inteq {o} :
  forall lib (t1 t2 a b c d : @CTerm o),
    {pk1 : param_kind
     , {pk2 : param_kind
     , ccomputes_to_valc lib a (pk2termc pk1)
     /\ ccomputes_to_valc lib b (pk2termc pk2)
     /\
     (
       (pk1 = pk2
        /\ ccequivc lib (mkc_inteq a b c d) c
        /\ equality lib t1 t2 c)
         {+}
         (pk1 <> pk2
          /\ ccequivc lib (mkc_inteq a b c d) d
          /\ equality lib t1 t2 d)
    ) }}
    -> equality lib t1 t2 (mkc_inteq a b c d).
Proof.
  introv comp; exrepnd; spcast.
  eapply cequivc_preserving_equality;
    [|apply cequivc_sym;apply cequivc_mkc_inteq;
      [apply computes_to_valc_implies_cequivc;exact comp0
      |apply computes_to_valc_implies_cequivc;exact comp2
      |apply cequivc_refl
      |apply cequivc_refl]
    ].

  repndors; repnd; subst.

  - eapply cequivc_preserving_equality;
    [|apply cequivc_sym;
       apply reduces_toc_implies_cequivc;
       apply reduces_toc_mkc_inteq_eq].
    auto.

  - eapply cequivc_preserving_equality;
    [|apply cequivc_sym;
       apply reduces_toc_implies_cequivc;
       apply reduces_toc_mkc_inteq_diff;auto].
    auto.
Qed.

Lemma equality_in_inteq_iff {o} :
  forall lib (t1 t2 a b c d : @CTerm o),
    equality lib t1 t2 (mkc_inteq a b c d)
    <=>
    {pk1 : param_kind
     , {pk2 : param_kind
     , ccomputes_to_valc lib a (pk2termc pk1)
     /\ ccomputes_to_valc lib b (pk2termc pk2)
     /\
     (
       (pk1 = pk2
        /\ ccequivc lib (mkc_inteq a b c d) c
        /\ equality lib t1 t2 c)
         {+}
         (pk1 <> pk2
          /\ ccequivc lib (mkc_inteq a b c d) d
          /\ equality lib t1 t2 d)
    ) }}.
Proof.
  introv; split; intro h.
  - apply equality_in_inteq_implies; auto.
  - apply implies_equality_in_inteq; auto.
Qed.

Lemma mkc_zero_eq_pk2term_implies {o} :
  forall pk, @mkc_zero o = pk2termc pk -> pk = PKi 0.
Proof.
  introv e.
  destruct pk; allsimpl; inversion e; auto.
Qed.

Lemma mkc_one_eq_pk2term_implies {o} :
  forall pk, @mkc_one o = pk2termc pk -> pk = PKi 1.
Proof.
  introv e.
  destruct pk; allsimpl; inversion e; auto.
Qed.

Lemma cequivc_nat_implies {o} :
  forall lib (t t' : @CTerm o) n,
    computes_to_valc lib t (mkc_nat n)
    -> cequivc lib t t'
    -> computes_to_valc lib t' (mkc_nat n).
Proof.
  introv comp ceq.
  destruct_cterms.
  unfold computes_to_valc in *; allsimpl.
  unfold cequivc in ceq; allsimpl.
  eapply cequiv_nat in ceq; eauto.
Qed.

Lemma not_type_axiom {o} :
  forall (lib : @library o), !type lib mkc_axiom.
Proof.
  introv t.
  unfold type, tequality, nuprl in t; exrepnd.
  inversion t0; try not_univ.
  duniv j h.
  allrw @univi_exists_iff; exrepd; spcast.
  apply computes_to_valc_isvalue_eq in c; eauto 3 with slow.
  inversion c.
Qed.

Lemma not_equality_in_axiom {o} :
  forall lib (t1 t2 : @CTerm o), !equality lib t1 t2 mkc_axiom.
Proof.
  introv e.
  apply inhabited_implies_tequality in e.
  apply not_type_axiom in e; sp.
Qed.

Hint Resolve iscvalue_mkc_true : slow.

Lemma isvalue_one {o} : @isvalue o mk_one.
Proof.
  constructor; eauto 3 with slow; sp.
Qed.
Hint Resolve isvalue_one : slow.

Lemma iscvalue_one {o} : @iscvalue o mkc_one.
Proof.
  unfold iscvalue; simpl; eauto 3 with slow.
Qed.
Hint Resolve iscvalue_one : slow.

Lemma implies_eq_get_cterm {o} :
  forall (t u : @CTerm o), t = u -> get_cterm t = get_cterm u.
Proof.
  introv e; subst; auto.
Qed.

Lemma eq_pk2termc {o} :
  forall pk1 pk2, @pk2termc o pk1 = pk2termc pk2 -> pk1 = pk2.
Proof.
  introv e.
  apply implies_eq_get_cterm in e; allsimpl.
  destruct pk1, pk2; allsimpl; ginv; auto.
Qed.

Lemma equality_in_mkc_apply2_mkc_nwf_pred_implies {o} :
  forall lib (t1 t2 n f : @CTerm o) k s,
    s <> k
    -> equality lib t1 t2 (mkc_apply2 (mkc_nwf_pred k s) n f)
    ->
    (
      ccomputes_to_valc lib t1 mkc_axiom
      /\ ccomputes_to_valc lib t2 mkc_axiom
      /\
      (
        (
          ccomputes_to_valc lib n mkc_zero
          /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) mkc_true
        )
        {+}
        (
          ccomputes_to_valc lib n mkc_one
          /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
          /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) (mkc_cequiv (mkc_apply f mkc_zero) mkc_zero)
        )
        {+}
        {pk : param_kind
         , ccomputes_to_valc lib n (pk2termc pk)
         /\ pk <> PKi 0
         /\ pk <> PKi 1
         /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
         /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) mkc_true
        }
      )
    ).
Proof.
  introv d1 e.
  unfold mkc_nwf_pred in e.
  eapply cequivc_preserving_equality in e;[|apply cequivc_beta2].
  rewrite mkcv_lam_substc in e; auto.
  eapply cequivc_preserving_equality in e;[|apply cequivc_beta].
  autorewrite with slow in e.
  repeat (rewrite substc2_mk_cv_app_r in e; auto;[]).
  autorewrite with slow in e.
  apply equality_in_inteq_iff in e; exrepnd; spcast.
  apply computes_to_valc_isvalue_eq in e2; eauto 2 with slow.
  apply mkc_zero_eq_pk2term_implies in e2; subst.
  repndors; repnd; subst; spcast.

  - rewrite <- mkc_integer_eq_pk2termc in e0.
    assert (0%Z = Z.of_nat 0) as xx by auto.
    rewrite xx in e0; clear xx.
    rewrite <- mkc_nat_eq in e0.
    rewrite <- mkc_zero_eq in e0.
    apply equality_in_true in e1; repnd; spcast.

    dands; spcast; auto.

    left; dands; spcast; auto.

    unfold mkc_nwf_pred.
    eapply cequivc_trans;[apply cequivc_beta2|].
    rewrite mkcv_lam_substc; auto.
    eapply cequivc_trans;[apply cequivc_beta|].
    autorewrite with slow.
    repeat (rewrite substc2_mk_cv_app_r; auto;[]).
    autorewrite with slow.
    auto.

  - apply equality_in_inteq_iff in e1; exrepnd; spcast.
    apply computes_to_valc_isvalue_eq in e5; eauto 2 with slow.
    apply mkc_one_eq_pk2term_implies in e5; subst.
    repndors; repnd; subst; spcast.

    + rewrite <- mkc_integer_eq_pk2termc in e4.
      assert (1%Z = Z.of_nat 1) as xx by auto.
      rewrite xx in e4; clear xx.
      rewrite <- mkc_nat_eq in e4.
      rewrite <- mkc_one_eq in e4.

      apply equality_in_mkc_cequiv in e1; repnd; spcast.
      eapply cequivc_sym in e1.
      eapply cequivc_nat_implies in e1;
        [|rewrite mkc_zero_eq; apply computes_to_valc_refl; eauto 3 with slow].
      rewrite <- mkc_zero_eq in e1.

      eapply computes_to_valc_eq in e0;[|exact e4].
      apply mkc_one_eq_pk2term_implies in e0; subst.

      dands; spcast; auto.
      right; left; dands; spcast; auto.

      unfold mkc_nwf_pred.
      eapply cequivc_trans;[apply cequivc_beta2|].
      rewrite mkcv_lam_substc; auto.
      eapply cequivc_trans;[apply cequivc_beta|].
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; auto;[]).
      autorewrite with slow.

      eapply cequivc_trans; eauto.

    + apply equality_in_inteq_iff in e1; exrepnd; spcast.
      apply computes_to_valc_isvalue_eq in e8; eauto 2 with slow.
      apply mkc_zero_eq_pk2term_implies in e8; subst.
      eapply computes_to_valc_eq in e0;[|exact e4].
      apply eq_pk2termc in e0; subst.

      repndors; repnd; subst; spcast.

      * apply equality_in_true in e1; repnd; spcast.
        rewrite <- mkc_integer_eq_pk2termc in e7.
        assert (0%Z = Z.of_nat 0) as xx by auto.
        rewrite xx in e7; clear xx.
        rewrite <- mkc_nat_eq in e7.
        rewrite <- mkc_zero_eq in e7.

        dands; spcast; auto.
        right; right.
        exists pk1; dands; spcast; auto.

        unfold mkc_nwf_pred.
        eapply cequivc_trans;[apply cequivc_beta2|].
        rewrite mkcv_lam_substc; auto.
        eapply cequivc_trans;[apply cequivc_beta|].
        autorewrite with slow.
        repeat (rewrite substc2_mk_cv_app_r; auto;[]).
        autorewrite with slow.
        auto.
        eapply cequivc_trans;[exact e3|]; auto.
        eapply cequivc_trans; eauto.

      * apply not_equality_in_axiom in e1; sp.
Qed.

Lemma implies_equality_in_mkc_apply2_mkc_nwf_pred {o} :
  forall lib (t1 t2 n f : @CTerm o) k s,
    s <> k
    ->
    (
      ccomputes_to_valc lib t1 mkc_axiom
      /\ ccomputes_to_valc lib t2 mkc_axiom
      /\
      (
        (
          ccomputes_to_valc lib n mkc_zero
          /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) mkc_true
        )
        {+}
        (
          ccomputes_to_valc lib n mkc_one
          /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
          /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) (mkc_cequiv (mkc_apply f mkc_zero) mkc_zero)
        )
        {+}
        {pk : param_kind
         , ccomputes_to_valc lib n (pk2termc pk)
         /\ pk <> PKi 0
         /\ pk <> PKi 1
         /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
         /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) mkc_true
        }
      )
    )
    -> equality lib t1 t2 (mkc_apply2 (mkc_nwf_pred k s) n f).
Proof.
  introv d comp.
  repnd; repndors; exrepnd; spcast.

  - eapply cequivc_preserving_equality;[|apply cequivc_sym;exact comp].
    apply equality_in_true; dands; spcast; auto.

  - eapply cequivc_preserving_equality;[|apply cequivc_sym;exact comp].
    apply equality_in_mkc_cequiv; dands; spcast; eauto 3 with slow.

  - eapply cequivc_preserving_equality;[|apply cequivc_sym;exact comp2].
    apply equality_in_true; dands; spcast; eauto 3 with slow.
Qed.

Lemma equality_in_mkc_apply2_mkc_nwf_pred_iff {o} :
  forall lib (t1 t2 n f : @CTerm o) k s (d : s <> k),
    equality lib t1 t2 (mkc_apply2 (mkc_nwf_pred k s) n f)
    <=>
    (
      ccomputes_to_valc lib t1 mkc_axiom
      /\ ccomputes_to_valc lib t2 mkc_axiom
      /\
      (
        (
          ccomputes_to_valc lib n mkc_zero
          /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) mkc_true
        )
        {+}
        (
          ccomputes_to_valc lib n mkc_one
          /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
          /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) (mkc_cequiv (mkc_apply f mkc_zero) mkc_zero)
        )
        {+}
        {pk : param_kind
         , ccomputes_to_valc lib n (pk2termc pk)
         /\ pk <> PKi 0
         /\ pk <> PKi 1
         /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
         /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) mkc_true
        }
      )
    ).
Proof.
  introv d; split; intro h.
  - apply equality_in_mkc_apply2_mkc_nwf_pred_implies; auto.
  - apply implies_equality_in_mkc_apply2_mkc_nwf_pred; auto.
Qed.

Lemma tequality_implies_type {o}:
  forall lib (t1 t2 : @CTerm o),
    tequality lib t1 t2 -> (type lib t1 # type lib t2).
Proof.
  introv t.
  applydup @tequality_refl in t.
  apply tequality_sym in t.
  applydup @tequality_refl in t.
  sp.
Qed.

Lemma tequality_inteq_left_implies {o} :
  forall lib (a b c d u : @CTerm o),
    tequality lib (mkc_inteq a b c d) u
    -> {pka : param_kind
        , {pkb : param_kind
        , ccomputes_to_valc lib a (pk2termc pka)
        /\ ccomputes_to_valc lib b (pk2termc pkb)
        /\
        (
          (pka = pkb
           /\ ccequivc lib (mkc_inteq a b c d) c
           /\ tequality lib c u)
            {+}
            (pka <> pkb
             /\ ccequivc lib (mkc_inteq a b c d) d
             /\ tequality lib d u
            )
       ) }}.
Proof.
  introv t.
  applydup @tequality_implies_type in t; repnd.
  apply types_converge in t1; spcast.
  apply hasvaluec_implies_computes_to_valc in t1.
  exrepnd.
  applydup @computes_to_valc_mkc_inteq in t2; exrepnd.

  exists pk1 pk2.
  dands; spcast; auto;
  try (apply computes_to_valc_iff_reduces_toc; dands; eauto 3 with slow).

  repndors; repnd;[left|right]; dands; auto; spcast.

  - eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;exact t2|].
    apply cequivc_sym; eauto 3 with slow.

  - eapply tequality_respects_cequivc_left;
    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact t1|].
    eapply tequality_respects_cequivc_left;
      [apply computes_to_valc_implies_cequivc;exact t2|].
    auto.

  - eapply cequivc_trans;[apply computes_to_valc_implies_cequivc;exact t2|].
    apply cequivc_sym; eauto 3 with slow.

  - eapply tequality_respects_cequivc_left;
    [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact t1|].
    eapply tequality_respects_cequivc_left;
      [apply computes_to_valc_implies_cequivc;exact t2|].
    auto.
Qed.

Lemma implies_tequality_inteq_left {o} :
  forall lib (a b c d u : @CTerm o),
    {pka : param_kind
     , {pkb : param_kind
     , ccomputes_to_valc lib a (pk2termc pka)
     /\ ccomputes_to_valc lib b (pk2termc pkb)
     /\
     (
       (pka = pkb
        /\ ccequivc lib (mkc_inteq a b c d) c
        /\ tequality lib c u)
         {+}
         (pka <> pkb
          /\ ccequivc lib (mkc_inteq a b c d) d
          /\ tequality lib d u)
    ) }}
    -> tequality lib (mkc_inteq a b c d) u.
Proof.
  introv comp; exrepnd; spcast.

  eapply tequality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_mkc_inteq;
     [apply computes_to_valc_implies_cequivc;exact comp0
     |apply computes_to_valc_implies_cequivc;exact comp2
     |apply cequivc_refl
     |apply cequivc_refl]
    |].

  repndors; repnd; subst.

  - eapply tequality_respects_cequivc_left;
    [apply cequivc_sym;
      apply reduces_toc_implies_cequivc;
      apply reduces_toc_mkc_inteq_eq|].
    auto.

  - eapply tequality_respects_cequivc_left;
    [apply cequivc_sym;
      apply reduces_toc_implies_cequivc;
      apply reduces_toc_mkc_inteq_diff;auto|].
    auto.
Qed.

Lemma tequality_inteq_left_iff {o} :
  forall lib (a b c d u : @CTerm o),
    tequality lib (mkc_inteq a b c d) u
    <=>
    {pka : param_kind
     , {pkb : param_kind
     , ccomputes_to_valc lib a (pk2termc pka)
     /\ ccomputes_to_valc lib b (pk2termc pkb)
     /\
     (
       (pka = pkb
        /\ ccequivc lib (mkc_inteq a b c d) c
        /\ tequality lib c u)
         {+}
         (pka <> pkb
          /\ ccequivc lib (mkc_inteq a b c d) d
          /\ tequality lib d u)
    ) }}.
Proof.
  introv; split; intro h.
  - apply tequality_inteq_left_implies; auto.
  - apply implies_tequality_inteq_left; auto.
Qed.

Lemma tequality_cequiv_left_implies {o} :
  forall lib (a b c : @CTerm o),
    tequality lib (mkc_cequiv a b) c
    -> {a' : CTerm
        , {b' : CTerm
        , ccomputes_to_valc lib c (mkc_cequiv a' b') }}.
Proof.
  introv teq.
  unfold tequality, nuprl in teq; exrepnd.
  inversion teq0; try not_univ.
  allunfold @per_cequiv; exrepnd.
  eexists; eexists; eauto.
Qed.

Lemma tequality_in_mkc_apply2_mkc_nwf_pred_implies {o} :
  forall lib (n1 n2 f1 f2 : @CTerm o) k s,
    s <> k
    -> tequality
         lib
         (mkc_apply2 (mkc_nwf_pred k s) n1 f1)
         (mkc_apply2 (mkc_nwf_pred k s) n2 f2)
    ->
    (
      (
        ccomputes_to_valc lib n1 mkc_zero
        /\ ccomputes_to_valc lib n2 mkc_zero
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true
      )
      {+}
      (
        ccomputes_to_valc lib n1 mkc_one
        /\ ccomputes_to_valc lib n2 mkc_one
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) (mkc_cequiv (mkc_apply f1 mkc_zero) mkc_zero)
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) (mkc_cequiv (mkc_apply f2 mkc_zero) mkc_zero)
        /\ (((mkc_apply f1 mkc_zero) ~=~(lib) (mkc_zero))
            <=>
            ((mkc_apply f2 mkc_zero) ~=~(lib) (mkc_zero)))
      )
      {+}
      {pk : param_kind
       , ccomputes_to_valc lib n1 mkc_zero
       /\ ccomputes_to_valc lib n2 (pk2termc pk)
       /\ pk <> PKi 0
       /\ pk <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f2 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }
      {+}
      {pk : param_kind
       , ccomputes_to_valc lib n1 (pk2termc pk)
       /\ ccomputes_to_valc lib n2 mkc_zero
       /\ pk <> PKi 0
       /\ pk <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f1 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }
      {+}
      {pk1 : param_kind
       , {pk2 : param_kind
       , ccomputes_to_valc lib n1 (pk2termc pk1)
       /\ ccomputes_to_valc lib n2 (pk2termc pk2)
       /\ pk1 <> PKi 0
       /\ pk2 <> PKi 0
       /\ pk1 <> PKi 1
       /\ pk2 <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f1 mkc_zero) mkc_zero
       /\ ccomputes_to_valc lib (mkc_apply f2 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }}
    ).
Proof.
  introv d1 e.
  unfold mkc_nwf_pred in e.
  eapply tequality_respects_cequivc_left in e;[|apply cequivc_beta2].
  eapply tequality_respects_cequivc_right in e;[|apply cequivc_beta2].
  repeat (rewrite mkcv_lam_substc in e; auto;[]).
  eapply tequality_respects_cequivc_left in e;[|apply cequivc_beta].
  eapply tequality_respects_cequivc_right in e;[|apply cequivc_beta].
  autorewrite with slow in e.
  repeat (rewrite substc2_mk_cv_app_r in e; auto;[]).
  autorewrite with slow in e.

  applydup @tequality_inteq_left_iff in e.
  apply tequality_sym in e.
  applydup @tequality_inteq_left_iff in e.
  exrepnd; spcast.

  apply computes_to_valc_isvalue_eq in e5; eauto 3 with slow.
  apply computes_to_valc_isvalue_eq in e3; eauto 3 with slow.
  apply mkc_zero_eq_pk2term_implies in e5.
  apply mkc_zero_eq_pk2term_implies in e3.
  subst.

  repndors; exrepnd; subst; spcast.

  - rewrite <- mkc_integer_eq_pk2termc in e4.
    rewrite <- mkc_integer_eq_pk2termc in e2.
    assert (0%Z = Z.of_nat 0) as xx by auto.
    rewrite xx in e4; rewrite xx in e2; clear xx.
    rewrite <- mkc_nat_eq in e2.
    rewrite <- mkc_nat_eq in e4.
    rewrite <- mkc_zero_eq in e4.
    rewrite <- mkc_zero_eq in e2.
    eapply tequality_respects_cequivc_right in e0;[|exact e7].

    left.
    dands; spcast; auto.

    + unfold mkc_nwf_pred.
      eapply cequivc_trans;[apply cequivc_beta2|].
      rewrite mkcv_lam_substc; auto.
      eapply cequivc_trans;[apply cequivc_beta|].
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; auto;[]).
      autorewrite with slow.
      auto.

    + unfold mkc_nwf_pred.
      eapply cequivc_trans;[apply cequivc_beta2|].
      rewrite mkcv_lam_substc; auto.
      eapply cequivc_trans;[apply cequivc_beta|].
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; auto;[]).
      autorewrite with slow.
      auto.

  - rewrite <- mkc_integer_eq_pk2termc in e4.
    assert (0%Z = Z.of_nat 0) as xx by auto.
    rewrite xx in e4; clear xx.
    rewrite <- mkc_nat_eq in e4.
    rewrite <- mkc_zero_eq in e4.
    eapply tequality_respects_cequivc_right in e0;[|exact e7].

    apply tequality_sym in e0.
    applydup @tequality_inteq_left_iff in e0.
    exrepnd; spcast.

    apply computes_to_valc_isvalue_eq in e9; eauto 3 with slow.
    apply mkc_one_eq_pk2term_implies in e9; subst.
    eapply computes_to_valc_eq in e8;[|exact e2].
    apply eq_pk2termc in e8; subst.

    repndors; exrepnd; subst.

    + apply tequality_cequiv_left_implies in e3; exrepnd; spcast.
      apply computes_to_valc_isvalue_eq in e3; eauto 3 with slow.
      apply implies_eq_get_cterm in e3; simpl in e3.
      destruct_cterms; inversion e3.

    + applydup @tequality_inteq_left_iff in e3.
      exrepnd; spcast.

      apply computes_to_valc_isvalue_eq in e12; eauto 3 with slow.
      apply mkc_zero_eq_pk2term_implies in e12; subst.

      repndors; exrepnd; subst.

      * rewrite <- mkc_integer_eq_pk2termc in e11.
        assert (0%Z = Z.of_nat 0) as xx by auto.
        rewrite xx in e11; clear xx.
        rewrite <- mkc_nat_eq in e11.
        rewrite <- mkc_zero_eq in e11.

        right; right; left.
        exists pka0.
        dands; spcast; auto.

        {
          unfold mkc_nwf_pred.
          eapply cequivc_trans;[apply cequivc_beta2|].
          rewrite mkcv_lam_substc; auto.
          eapply cequivc_trans;[apply cequivc_beta|].
          autorewrite with slow.
          repeat (rewrite substc2_mk_cv_app_r; auto;[]).
          autorewrite with slow.
          auto.
        }

        {
          unfold mkc_nwf_pred.
          eapply cequivc_trans;[apply cequivc_beta2|].
          rewrite mkcv_lam_substc; auto.
          eapply cequivc_trans;[apply cequivc_beta|].
          autorewrite with slow.
          repeat (rewrite substc2_mk_cv_app_r; auto;[]).
          autorewrite with slow.
          eapply cequivc_trans; eauto.
          eapply cequivc_trans; eauto.
        }

      * apply tequality_refl in e10.
        apply not_type_axiom in e10; sp.

  - rewrite <- mkc_integer_eq_pk2termc in e2.
    assert (0%Z = Z.of_nat 0) as xx by auto.
    rewrite xx in e2; clear xx.
    rewrite <- mkc_nat_eq in e2.
    rewrite <- mkc_zero_eq in e2.
    eapply tequality_respects_cequivc_right in e0;[|exact e7].

    applydup @tequality_inteq_left_iff in e0.
    exrepnd; spcast.
    apply computes_to_valc_isvalue_eq in e9; eauto 3 with slow.
    apply mkc_one_eq_pk2term_implies in e9; subst.

    eapply computes_to_valc_eq in e8;[|exact e4].
    apply eq_pk2termc in e8; subst.

    repndors; exrepnd; subst; spcast.

    + apply tequality_cequiv_left_implies in e6; exrepnd; spcast.
      apply computes_to_valc_isvalue_eq in e6; eauto 3 with slow.
      apply implies_eq_get_cterm in e6; simpl in e6.
      destruct_cterms; inversion e6.

    + applydup @tequality_inteq_left_iff in e6.
      exrepnd; spcast.

      apply computes_to_valc_isvalue_eq in e12; eauto 3 with slow.
      apply mkc_zero_eq_pk2term_implies in e12; subst.

      repndors; exrepnd; subst; spcast.

      * rewrite <- mkc_integer_eq_pk2termc in e11.
        assert (0%Z = Z.of_nat 0) as xx by auto.
        rewrite xx in e11; clear xx.
        rewrite <- mkc_nat_eq in e11.
        rewrite <- mkc_zero_eq in e11.

        right; right; right; left.
        exists pka.
        dands; spcast; auto.

        {
          unfold mkc_nwf_pred.
          eapply cequivc_trans;[apply cequivc_beta2|].
          rewrite mkcv_lam_substc; auto.
          eapply cequivc_trans;[apply cequivc_beta|].
          autorewrite with slow.
          repeat (rewrite substc2_mk_cv_app_r; auto;[]).
          autorewrite with slow.
          eapply cequivc_trans; eauto.
          eapply cequivc_trans; eauto.
        }

        {
          unfold mkc_nwf_pred.
          eapply cequivc_trans;[apply cequivc_beta2|].
          rewrite mkcv_lam_substc; auto.
          eapply cequivc_trans;[apply cequivc_beta|].
          autorewrite with slow.
          repeat (rewrite substc2_mk_cv_app_r; auto;[]).
          autorewrite with slow.
          auto.
        }

      * apply tequality_refl in e10.
        apply not_type_axiom in e10; sp.

  - eapply tequality_respects_cequivc_right in e0;[|exact e7].

    applydup @tequality_inteq_left_iff in e0.
    exrepnd; spcast.

    apply computes_to_valc_isvalue_eq in e10; eauto 3 with slow.
    apply mkc_one_eq_pk2term_implies in e10; subst.

    eapply computes_to_valc_eq in e9;[|exact e4].
    apply eq_pk2termc in e9; subst.

    repndors; exrepnd; spcast; subst.

    + rewrite <- mkc_integer_eq_pk2termc in e4.
      assert (1%Z = Z.of_nat 1) as xx by auto.
      rewrite xx in e4; clear xx.
      rewrite <- mkc_nat_eq in e4.
      rewrite <- mkc_one_eq in e4.

      apply tequality_sym in e8.
      applydup @tequality_inteq_left_iff in e8.

      exrepnd; spcast.
      apply computes_to_valc_isvalue_eq in e12; eauto 3 with slow.
      apply mkc_one_eq_pk2term_implies in e12; subst.

      eapply computes_to_valc_eq in e11;[|exact e2].
      apply eq_pk2termc in e11; subst.

      repndors; exrepnd; subst; spcast.

      * apply tequality_mkc_cequiv in e9.

        rewrite <- mkc_integer_eq_pk2termc in e2.
        assert (1%Z = Z.of_nat 1) as xx by auto.
        rewrite xx in e2; clear xx.
        rewrite <- mkc_nat_eq in e2.
        rewrite <- mkc_one_eq in e2.

        right; left.
        dands; spcast; auto; try (rw e9); tcsp.

        {
          unfold mkc_nwf_pred.
          eapply cequivc_trans;[apply cequivc_beta2|].
          rewrite mkcv_lam_substc; auto.
          eapply cequivc_trans;[apply cequivc_beta|].
          autorewrite with slow.
          repeat (rewrite substc2_mk_cv_app_r; auto;[]).
          autorewrite with slow.
          eapply cequivc_trans; eauto.
        }

        {
          unfold mkc_nwf_pred.
          eapply cequivc_trans;[apply cequivc_beta2|].
          rewrite mkcv_lam_substc; auto.
          eapply cequivc_trans;[apply cequivc_beta|].
          autorewrite with slow.
          repeat (rewrite substc2_mk_cv_app_r; auto;[]).
          autorewrite with slow.
          eapply cequivc_trans; eauto.
        }

      * applydup @tequality_inteq_left_iff in e9.

        exrepnd; spcast.
        apply computes_to_valc_isvalue_eq in e15; eauto 3 with slow.
        apply mkc_zero_eq_pk2term_implies in e15; subst.

        repndors; exrepnd; subst; spcast.

        {
          apply tequality_sym in e13.
          apply tequality_cequiv_left_implies in e13; exrepnd; spcast.
          apply computes_to_valc_isvalue_eq in e13; eauto 3 with slow.
          apply implies_eq_get_cterm in e13; simpl in e13.
          destruct_cterms; inversion e13.
        }

        {
          apply tequality_refl in e13.
          apply not_type_axiom in e13; sp.
        }

    + apply tequality_sym in e8.
      applydup @tequality_inteq_left_iff in e8.
      exrepnd; spcast.

      apply computes_to_valc_isvalue_eq in e13; eauto 3 with slow.
      apply mkc_one_eq_pk2term_implies in e13; subst.

      eapply computes_to_valc_eq in e12;[|exact e2].
      apply eq_pk2termc in e12; subst.

      repndors; exrepnd; spcast; subst.

      {
        rewrite <- mkc_integer_eq_pk2termc in e2.
        assert (1%Z = Z.of_nat 1) as xx by auto.
        rewrite xx in e2; clear xx.
        rewrite <- mkc_nat_eq in e2.
        rewrite <- mkc_one_eq in e2.

        apply tequality_sym in e11.
        applydup @tequality_inteq_left_iff in e11.

        exrepnd; spcast.
        apply computes_to_valc_isvalue_eq in e15; eauto 3 with slow.
        apply mkc_zero_eq_pk2term_implies in e15; subst.

        repndors; exrepnd; subst; spcast.

        {
          apply tequality_sym in e12.
          apply tequality_cequiv_left_implies in e12; exrepnd; spcast.
          apply computes_to_valc_isvalue_eq in e12; eauto 3 with slow.
          apply implies_eq_get_cterm in e12; simpl in e12.
          destruct_cterms; inversion e12.
        }

        {
          apply tequality_refl in e12.
          apply not_type_axiom in e12; sp.
        }
      }

      {
        applydup @tequality_inteq_left_iff in e11.

        exrepnd; spcast.
        apply computes_to_valc_isvalue_eq in e16; eauto 3 with slow.
        apply mkc_zero_eq_pk2term_implies in e16; subst.

        repndors; exrepnd; subst; spcast.

        {
          apply tequality_sym in e14.
          applydup @tequality_inteq_left_iff in e14.
          exrepnd; spcast.
          apply computes_to_valc_isvalue_eq in e19; eauto 3 with slow.
          apply mkc_zero_eq_pk2term_implies in e19; subst.

          repndors; repnd; spcast; subst.

          - rewrite <- mkc_integer_eq_pk2termc in e18.
            assert (0%Z = Z.of_nat 0) as xx by auto.
            rewrite xx in e18; clear xx.
            rewrite <- mkc_nat_eq in e18.
            rewrite <- mkc_zero_eq in e18.

            right; right; right; right.
            exists pka1 pka0.
            dands; spcast; auto.

            {
              unfold mkc_nwf_pred.
              eapply cequivc_trans;[apply cequivc_beta2|].
              rewrite mkcv_lam_substc; auto.
              eapply cequivc_trans;[apply cequivc_beta|].
              autorewrite with slow.
              repeat (rewrite substc2_mk_cv_app_r; auto;[]).
              autorewrite with slow.
              eapply cequivc_trans; eauto.
              eapply cequivc_trans; eauto.
            }

            {
              unfold mkc_nwf_pred.
              eapply cequivc_trans;[apply cequivc_beta2|].
              rewrite mkcv_lam_substc; auto.
              eapply cequivc_trans;[apply cequivc_beta|].
              autorewrite with slow.
              repeat (rewrite substc2_mk_cv_app_r; auto;[]).
              autorewrite with slow.
              eapply cequivc_trans; eauto.
              eapply cequivc_trans; eauto.
            }

          - apply tequality_refl in e16.
            apply not_type_axiom in e16; sp.
        }

        {
          apply tequality_refl in e14.
          apply not_type_axiom in e14; sp.
        }
      }
Qed.

Lemma implies_tequality_in_mkc_apply2_mkc_nwf_pred {o} :
  forall lib (n1 n2 f1 f2 : @CTerm o) k s,
    s <> k
    ->
    (
      (
        ccomputes_to_valc lib n1 mkc_zero
        /\ ccomputes_to_valc lib n2 mkc_zero
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true
      )
      {+}
      (
        ccomputes_to_valc lib n1 mkc_one
        /\ ccomputes_to_valc lib n2 mkc_one
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) (mkc_cequiv (mkc_apply f1 mkc_zero) mkc_zero)
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) (mkc_cequiv (mkc_apply f2 mkc_zero) mkc_zero)
        /\ (((mkc_apply f1 mkc_zero) ~=~(lib) (mkc_zero))
            <=>
            ((mkc_apply f2 mkc_zero) ~=~(lib) (mkc_zero)))
      )
      {+}
      {pk : param_kind
       , ccomputes_to_valc lib n1 mkc_zero
       /\ ccomputes_to_valc lib n2 (pk2termc pk)
       /\ pk <> PKi 0
       /\ pk <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f2 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }
      {+}
      {pk : param_kind
       , ccomputes_to_valc lib n1 (pk2termc pk)
       /\ ccomputes_to_valc lib n2 mkc_zero
       /\ pk <> PKi 0
       /\ pk <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f1 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }
      {+}
      {pk1 : param_kind
       , {pk2 : param_kind
       , ccomputes_to_valc lib n1 (pk2termc pk1)
       /\ ccomputes_to_valc lib n2 (pk2termc pk2)
       /\ pk1 <> PKi 0
       /\ pk2 <> PKi 0
       /\ pk1 <> PKi 1
       /\ pk2 <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f1 mkc_zero) mkc_zero
       /\ ccomputes_to_valc lib (mkc_apply f2 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }}
    )
    -> tequality
         lib
         (mkc_apply2 (mkc_nwf_pred k s) n1 f1)
         (mkc_apply2 (mkc_nwf_pred k s) n2 f2).
Proof.
  introv d1 h.

  repndors; exrepnd; spcast.

  - eapply tequality_respects_cequivc_left;[apply cequiv_sym;exact h2|].
    eapply tequality_respects_cequivc_right;[apply cequiv_sym;exact h|].
    eauto 3 with slow.

  - eapply tequality_respects_cequivc_left;[apply cequiv_sym;exact h2|].
    eapply tequality_respects_cequivc_right;[apply cequiv_sym;exact h3|].
    apply tequality_mkc_cequiv; auto.

  - eapply tequality_respects_cequivc_left;[apply cequiv_sym;exact h6|].
    eapply tequality_respects_cequivc_right;[apply cequiv_sym;exact h0|].
    eauto 3 with slow.

  - eapply tequality_respects_cequivc_left;[apply cequiv_sym;exact h6|].
    eapply tequality_respects_cequivc_right;[apply cequiv_sym;exact h0|].
    eauto 3 with slow.

  - eapply tequality_respects_cequivc_left;[apply cequiv_sym;exact h9|].
    eapply tequality_respects_cequivc_right;[apply cequiv_sym;exact h1|].
    eauto 3 with slow.
Qed.

Lemma tequality_in_mkc_apply2_mkc_nwf_pred_iff {o} :
  forall lib (n1 n2 f1 f2 : @CTerm o) k s,
    s <> k
    ->
    (
      tequality
        lib
        (mkc_apply2 (mkc_nwf_pred k s) n1 f1)
        (mkc_apply2 (mkc_nwf_pred k s) n2 f2)
      <=>
    (
      (
        ccomputes_to_valc lib n1 mkc_zero
        /\ ccomputes_to_valc lib n2 mkc_zero
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true
      )
      {+}
      (
        ccomputes_to_valc lib n1 mkc_one
        /\ ccomputes_to_valc lib n2 mkc_one
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) (mkc_cequiv (mkc_apply f1 mkc_zero) mkc_zero)
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) (mkc_cequiv (mkc_apply f2 mkc_zero) mkc_zero)
        /\ (((mkc_apply f1 mkc_zero) ~=~(lib) (mkc_zero))
            <=>
            ((mkc_apply f2 mkc_zero) ~=~(lib) (mkc_zero)))
      )
      {+}
      {pk : param_kind
       , ccomputes_to_valc lib n1 mkc_zero
       /\ ccomputes_to_valc lib n2 (pk2termc pk)
       /\ pk <> PKi 0
       /\ pk <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f2 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }
      {+}
      {pk : param_kind
       , ccomputes_to_valc lib n1 (pk2termc pk)
       /\ ccomputes_to_valc lib n2 mkc_zero
       /\ pk <> PKi 0
       /\ pk <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f1 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }
      {+}
      {pk1 : param_kind
       , {pk2 : param_kind
       , ccomputes_to_valc lib n1 (pk2termc pk1)
       /\ ccomputes_to_valc lib n2 (pk2termc pk2)
       /\ pk1 <> PKi 0
       /\ pk2 <> PKi 0
       /\ pk1 <> PKi 1
       /\ pk2 <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f1 mkc_zero) mkc_zero
       /\ ccomputes_to_valc lib (mkc_apply f2 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }}
    )
    ).
Proof.
  introv d1; split; introv h.
  - apply tequality_in_mkc_apply2_mkc_nwf_pred_implies; auto.
  - apply implies_tequality_in_mkc_apply2_mkc_nwf_pred; auto.
Qed.

Lemma reduce_toc_beta {o} :
  forall lib (v : NVar) (b : CVTerm [v]) (a : @CTerm o),
    reduces_toc lib (mkc_apply (mkc_lam v b) a) (substc a v b).
Proof.
  introv.
  destruct_cterms; unfold reduces_toc; simpl.
  apply reduces_to_if_step; csunf; simpl; auto.
Qed.

Lemma computes_to_valc_reduces_toc_trans {o} :
  forall lib (a b v : @CTerm o),
    reduces_toc lib a b
    -> computes_to_valc lib b v
    -> computes_to_valc lib a v.
Proof.
  introv comp1 comp2; destruct_cterms; allunfold @computes_to_valc;
  allunfold @reduces_toc; allsimpl.
  allunfold @computes_to_value; repnd; dands; auto.
  eapply reduces_to_trans; eauto.
Qed.

Lemma isprogram_mk_two {o} :
  @isprogram o mk_two.
Proof.
  repeat constructor; simpl; sp.
Qed.
Hint Immediate isprogram_mk_two.

Lemma isprog_mk_two {o} :
  @isprog o mk_two.
Proof.
  rw @isprog_eq.
  apply isprogram_mk_two.
Qed.
Hint Immediate isprog_mk_two.

Definition mkc_two {o} : @CTerm o := exist isprog mk_two isprog_mk_two.
Definition mkcv_two {o} (vs : list NVar) : @CVTerm o vs := mk_cv vs mkc_two.

Lemma lsubstc_vars_two {o} :
  forall (w : @wf_term o mk_two) s vs c,
    lsubstc_vars mk_two w s vs c
    = mkcv_two vs.
Proof.
  introv; apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @lsubstc_vars_two : slow.

Lemma substc3_mkcv_two {o} :
  forall (u : @CTerm o) v w x,
    substc3 v w u x (mkcv_two [v,w,x])
    = mkcv_two [v,w].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc3_mkcv_two : slow.

Lemma substc2_mkcv_two {o} :
  forall (u : @CTerm o) v x,
    substc2 v u x (mkcv_two [v,x])
    = mkcv_two [v].
Proof.
  introv.
  destruct_cterms.
  apply cvterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc2_mkcv_two : slow.

Lemma mkcv_two_substc {o} :
  forall v (t : @CTerm o),
    substc t v (mkcv_two [v]) = mkc_two.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.
Hint Rewrite @mkcv_two_substc : slow.

Lemma mkc_integer_as_mkc_two {o} : @mkc_integer o 2 = mkc_two.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma mkc_two_eq {o} : @mkc_two o = mkc_nat 2.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; sp.
Qed.

Lemma isvalue_two {o} : @isvalue o mk_two.
Proof.
  constructor; eauto 3 with slow; sp.
Qed.
Hint Resolve isvalue_two : slow.

Lemma iscvalue_two {o} : @iscvalue o mkc_two.
Proof.
  unfold iscvalue; simpl; eauto 3 with slow.
Qed.
Hint Resolve iscvalue_two : slow.

Lemma cequivc_mkc_inteq_one_one {o} :
  forall lib (t1 t2 : @CTerm o),
  cequivc lib (mkc_inteq mkc_one mkc_one t1 t2) t1.
Proof.
  introv.
  rw @mkc_one_eq.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; auto; try omega.
Qed.

Lemma cequivc_mkc_inteq_zero_zero {o} :
  forall lib (t1 t2 : @CTerm o),
  cequivc lib (mkc_inteq mkc_zero mkc_zero t1 t2) t1.
Proof.
  introv.
  rw @mkc_zero_eq.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; auto; try omega.
Qed.

Lemma cequivc_mkc_inteq_one_zero {o} :
  forall lib (t1 t2 : @CTerm o),
  cequivc lib (mkc_inteq mkc_one mkc_zero t1 t2) t2.
Proof.
  introv.
  rw @mkc_one_eq.
  rw @mkc_zero_eq.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; auto; try omega.
Qed.

Lemma cequivc_mkc_inteq_zero_one {o} :
  forall lib (t1 t2 : @CTerm o),
  cequivc lib (mkc_inteq mkc_zero mkc_one t1 t2) t2.
Proof.
  introv.
  rw @mkc_one_eq.
  rw @mkc_zero_eq.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; auto; try omega.
Qed.

Lemma cequivc_mkc_inteq_two_zero {o} :
  forall lib (t1 t2 : @CTerm o),
  cequivc lib (mkc_inteq mkc_two mkc_zero t1 t2) t2.
Proof.
  introv.
  rw @mkc_two_eq.
  rw @mkc_zero_eq.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; auto; try omega.
Qed.

Lemma cequivc_mkc_inteq_zero_two {o} :
  forall lib (t1 t2 : @CTerm o),
  cequivc lib (mkc_inteq mkc_zero mkc_two t1 t2) t2.
Proof.
  introv.
  rw @mkc_two_eq.
  rw @mkc_zero_eq.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; auto; try omega.
Qed.

Lemma cequivc_mkc_inteq_two_one {o} :
  forall lib (t1 t2 : @CTerm o),
  cequivc lib (mkc_inteq mkc_two mkc_one t1 t2) t2.
Proof.
  introv.
  rw @mkc_two_eq.
  rw @mkc_one_eq.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; auto; try omega.
Qed.

Lemma cequivc_mkc_inteq_one_two {o} :
  forall lib (t1 t2 : @CTerm o),
  cequivc lib (mkc_inteq mkc_one mkc_two t1 t2) t2.
Proof.
  introv.
  rw @mkc_two_eq.
  rw @mkc_one_eq.
  eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|].
  boolvar; auto; try omega.
Qed.

Lemma reduces_toc_mkc_inteq_one_one {o} :
  forall lib (t1 t2 : @CTerm o),
  reduces_toc lib (mkc_inteq mkc_one mkc_one t1 t2) t1.
Proof.
  introv.
  rw @mkc_one_eq.
  rewrite mkc_nat_eq.
  rewrite mkc_integer_eq_pk2termc.
  apply reduces_toc_mkc_inteq_eq.
Qed.

Lemma reduces_to_mkc_inteq_zero_zero {o} :
  forall lib (t1 t2 : @CTerm o),
  reduces_toc lib (mkc_inteq mkc_zero mkc_zero t1 t2) t1.
Proof.
  introv.
  rw @mkc_zero_eq.
  rewrite mkc_nat_eq.
  rewrite mkc_integer_eq_pk2termc.
  apply reduces_toc_mkc_inteq_eq.
Qed.

Lemma reduces_toc_mkc_inteq_one_zero {o} :
  forall lib (t1 t2 : @CTerm o),
  reduces_toc lib (mkc_inteq mkc_one mkc_zero t1 t2) t2.
Proof.
  introv.
  rw @mkc_one_eq.
  rw @mkc_zero_eq.
  repeat rewrite mkc_nat_eq.
  repeat rewrite mkc_integer_eq_pk2termc.
  apply reduces_toc_mkc_inteq_diff.
  intro xx; inversion xx.
Qed.

Lemma reduces_toc_mkc_inteq_zero_one {o} :
  forall lib (t1 t2 : @CTerm o),
  reduces_toc lib (mkc_inteq mkc_zero mkc_one t1 t2) t2.
Proof.
  introv.
  rw @mkc_one_eq.
  rw @mkc_zero_eq.
  repeat rewrite mkc_nat_eq.
  repeat rewrite mkc_integer_eq_pk2termc.
  apply reduces_toc_mkc_inteq_diff.
  intro xx; inversion xx.
Qed.

Lemma tequality_equality_in_mkc_apply2_mkc_nwf_pred_iff {o} :
  forall lib (t1 t2 n1 n2 f1 f2 : @CTerm o) k s,
    s <> k
    ->
    (
      (
        equality lib t1 t2 (mkc_apply2 (mkc_nwf_pred k s) n1 f1)
        /\ tequality
             lib
             (mkc_apply2 (mkc_nwf_pred k s) n1 f1)
             (mkc_apply2 (mkc_nwf_pred k s) n2 f2)
      )
      <=>
    (
    ccomputes_to_valc lib t1 mkc_axiom
    /\ ccomputes_to_valc lib t2 mkc_axiom
    /\
    (
      (
        ccomputes_to_valc lib n1 mkc_zero
        /\ ccomputes_to_valc lib n2 mkc_zero
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true
      )
      {+}
      (
        ccomputes_to_valc lib n1 mkc_one
        /\ ccomputes_to_valc lib n2 mkc_one
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) (mkc_cequiv (mkc_apply f1 mkc_zero) mkc_zero)
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) (mkc_cequiv (mkc_apply f2 mkc_zero) mkc_zero)
        /\ ccomputes_to_valc lib (mkc_apply f1 mkc_zero) mkc_zero
        /\ ccomputes_to_valc lib (mkc_apply f2 mkc_zero) mkc_zero
      )
      {+}
      {pk : param_kind
       , ccomputes_to_valc lib n1 mkc_zero
       /\ ccomputes_to_valc lib n2 (pk2termc pk)
       /\ pk <> PKi 0
       /\ pk <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f2 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }
      {+}
      {pk : param_kind
       , ccomputes_to_valc lib n1 (pk2termc pk)
       /\ ccomputes_to_valc lib n2 mkc_zero
       /\ pk <> PKi 0
       /\ pk <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f1 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }
      {+}
      {pk1 : param_kind
       , {pk2 : param_kind
       , ccomputes_to_valc lib n1 (pk2termc pk1)
       /\ ccomputes_to_valc lib n2 (pk2termc pk2)
       /\ pk1 <> PKi 0
       /\ pk2 <> PKi 0
       /\ pk1 <> PKi 1
       /\ pk2 <> PKi 1
       /\ ccomputes_to_valc lib (mkc_apply f1 mkc_zero) mkc_zero
       /\ ccomputes_to_valc lib (mkc_apply f2 mkc_zero) mkc_zero
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n1 f1) mkc_true
       /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n2 f2) mkc_true }}
    )
   )
    ).
Proof.
  introv d1; split; introv h; repnd.

  - apply tequality_in_mkc_apply2_mkc_nwf_pred_implies in h; auto.
    apply equality_in_mkc_apply2_mkc_nwf_pred_implies in h0; auto.
    repnd; repndors; exrepnd; dands; auto.

    + spcast.
      eapply computes_to_valc_eq in h3;[|exact h7].
      apply implies_eq_get_cterm in h3; simpl in h3.
      inversion h3.

    + right; left; dands; eauto 3 with slow.
      destruct h as [ceq1 ceq2]; clear ceq2.
      autodimp ceq1 hyp; spcast; eauto 3 with slow.
      allrw @mkc_zero_eq.
      apply cequivc_nat_implies_computes_to_valc in ceq1; auto.

    + spcast.
      eapply computes_to_valc_eq in h3;[|exact h0].
      symmetry in h3; apply mkc_one_eq_pk2term_implies in h3; subst; tcsp.

    + right; right; left.
      exists pk; dands; auto.

    + spcast.
      eapply computes_to_valc_eq in h3;[|exact h6].
      apply implies_eq_get_cterm in h3; simpl in h3.
      inversion h3.

    + right; right; left.
      exists pk; dands; auto.

    + spcast.
      eapply computes_to_valc_eq in h3;[|exact h6].
      symmetry in h3; apply mkc_one_eq_pk2term_implies in h3; subst; tcsp.

    + right; right; right; left.
      exists pk; dands; auto.

    + spcast.
      eapply computes_to_valc_eq in h3;[|exact h4].
      symmetry in h3; apply mkc_zero_eq_pk2term_implies in h3; subst; tcsp.

    + spcast.
      eapply computes_to_valc_eq in h3;[|exact h5].
      symmetry in h3; apply mkc_one_eq_pk2term_implies in h3; subst; tcsp.

    + right; right; right; right.
      exists pk1 pk2; dands; auto.

  - dands.

    + apply equality_in_mkc_apply2_mkc_nwf_pred_iff; auto.
      dands; auto.
      repndors; exrepnd; auto.

      * right; right.
        exists pk; dands; auto.

      * right; right.
        exists pk1; dands; auto.

    + apply tequality_in_mkc_apply2_mkc_nwf_pred_iff; auto.
      repndors; exrepnd; auto.

      * right; left.
        dands; auto.
        split; introv ceq; spcast; eauto 3 with slow.

      * right; right; left.
        exists pk; dands; auto.

      * right; right; right; left.
        exists pk; dands; auto.

      * right; right; right; right.
        exists pk1 pk2; dands; auto.
Qed.

Lemma mkc_nat_eq_pk2term_implies {o} :
  forall k pk, @mkc_nat o k = pk2termc pk -> pk = PKi (Z.of_nat k).
Proof.
  introv e.
  destruct pk; allsimpl; inversion e; auto.
Qed.

Lemma eq_PKi_implies {o} :
  forall i1 i2, @PKi o i1 = PKi i2 -> i1 = i2.
Proof.
  introv e; injection e; auto.
Qed.

Lemma reduces_toc_mkc_inteq_nat_diff {o} :
  forall lib n1 n2 (a b : @CTerm o),
    n1 <> n2
    -> reduces_toc lib (mkc_inteq (mkc_nat n1) (mkc_nat n2) a b) b.
Proof.
  introv d.
  allrw @mkc_nat_eq.
  allrw @mkc_integer_eq_pk2termc.
  apply reduces_toc_mkc_inteq_diff; auto.
  intro xx.
  apply eq_PKi_implies in xx.
  apply Znat.Nat2Z.inj in xx; tcsp.
Qed.

Lemma reduces_toc_mkc_inteq_nat_eq {o} :
  forall lib n (a b : @CTerm o),
    reduces_toc lib (mkc_inteq (mkc_nat n) (mkc_nat n) a b) a.
Proof.
  introv.
  allrw @mkc_nat_eq.
  allrw @mkc_integer_eq_pk2termc.
  apply reduces_toc_mkc_inteq_eq; auto.
Qed.

Lemma ind_nwf_pred {o} :
  forall lib H k s f n m z v,
    s <> k
    -> z <> n
    -> z <> f
    -> f <> n
    -> k <> m
    -> z <> m
    -> n <> m
    -> f <> m
    -> v <> n
    -> v <> f
    -> v <> m
    -> !LIn n (vars_hyps H)
    -> !LIn f (vars_hyps H)
    -> !LIn z (vars_hyps H)
    -> wf_hypotheses H
    -> @sequent_true2
         o
         lib
         (choice_sequence_ind_ind H (nwf_pred k s) f n m z v).
Proof.
  introv d1 d2 d3 d4 d5;
  introv d6 d7 d8 d9 d10 d11;
  introv ni1 ni2 ni3 wfH.

  assert (wf_csequent (choice_sequence_ind_ind H (nwf_pred k s) f n m z v)) as wfc.
  {
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    dands; tcsp.

    {
      repeat (rw @vswf_hypotheses_snoc); simpl.
      autorewrite with slow; simpl.
      allrw in_snoc; allrw not_over_or.
      rw @isprog_vars_mk_natk2nat.
      rw @isprog_vars_apply2.
      repeat (rw <- @isprog_vars_var_iff; simpl).
      allrw in_snoc.
      dands; auto; eauto 3 with slow;
      try (complete (rw @vswf_hypotheses_nil_eq; auto)).
    }

    {
      introv i.
      allrw in_remove_nvars; allsimpl.
      allrw in_app_iff; allsimpl.
      allrw in_remove_nvars; allsimpl.
      allrw not_over_or.
      allrw in_snoc; sp.
    }
  }

  exists wfc.
  vr_seq_true.
  unfold mk_exists.
  lsubst_tac.

  apply similarity_snoc in sim; simpl in sim; exrepnd; subst.
  apply similarity_snoc in sim3; simpl in sim3; exrepnd; subst.
  apply similarity_snoc in sim4; simpl in sim4; exrepnd; subst.
  autorewrite with slow in *.

  assert (!LIn n (dom_csub s1a)) as nin1.
  {
    apply similarity_dom in sim5; repnd; allrw; auto.
  }

  assert (!LIn f (dom_csub s1a)) as nif1.
  {
    apply similarity_dom in sim5; repnd; allrw; auto.
  }

  assert (!LIn n (dom_csub s2a)) as nin2.
  {
    apply similarity_dom in sim5; repnd; allrw; auto.
  }

  assert (!LIn f (dom_csub s2a)) as nif2.
  {
    apply similarity_dom in sim5; repnd; allrw; auto.
  }

  eapply alphaeqc_preserving_equality in sim2;
    [|apply lsubstc_mk_natk2nat_sp2; auto];[].
  lsubst_tac.
  clear_wf_cov.
  autorewrite with slow in *.

  assert (!LIn z (@free_vars o (mk_update_seq (mk_var f) (mk_var n) (mk_var m) v))) as niz.
  {
    simpl; autorewrite with slow.
    rw in_remove_nvars; simpl; sp.
  }

  pose proof (eqh (snoc (snoc (snoc s2a (n, t5)) (f, t3)) (z, t2))) as hf.
  autodimp hf hyp.

  {
    sim_snoc2; dands; auto.

    {
      sim_snoc2; dands; auto.

      {
        sim_snoc2; dands; auto.
        autorewrite with slow; auto.
      }

      {
        eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym; apply lsubstc_mk_natk2nat_sp2; auto];[].
        auto.
      }
    }

    {
      lsubst_tac_c.
      autorewrite with slow.
      auto.
    }
  }

  apply eq_hyps_snoc in hf; simpl in hf; exrepnd.
  apply snoc_inj in hf1; apply snoc_inj in hf2; repnd; subst; ginv; spcast.
  lsubst_tac_h hf0.
  autorewrite with slow in hf0.
  clear_wf_cov.

  pose proof (tequality_equality_in_mkc_apply2_mkc_nwf_pred_iff
                lib t6 t7 t4 t5 t0 t3 k s) as comp.
  repeat (autodimp comp hyp).
  destruct comp as [comp comp2]; clear comp2.
  autodimp comp hyp.

  apply implies_tequality_equality_mkc_squash_and.
  rw @tequality_product.
  rw @inhabited_product.
  autorewrite with slow.

  repeat (lsubstc_vars_as_mkcv; clear_wf_cov).
  autorewrite with slow.

  assert (!LIn z (free_vars (@mk_var o n))) as nizn by (simpl; introv h; repndors; subst; tcsp).
  assert (!LIn f (free_vars (@mk_var o n))) as nifn by (simpl; introv h; repndors; subst; tcsp).
  assert (!LIn z (free_vars (@mk_one o))) as nizo by (simpl; introv h; repndors; subst; tcsp).
  assert (!LIn f (free_vars (@mk_one o))) as nifo by (simpl; introv h; repndors; subst; tcsp).

  lift_lsubst_concl.
  repeat (lsubstc_snoc_step_concl auto).
  lift_lsubst_concl.
  autorewrite with slow.

  match goal with
  | [ |- (_ # ?a) # (_ # _ # ?b) ] => rev_assert (a /\ b) xx
  end.

  {
    repnd; dands; eauto 3 with slow.
    introv ea.
    applydup xx0 in ea.
    apply equality_in_tnat in ea.
    unfold equality_of_nat in ea; exrepnd; spcast.
    eapply tequality_respects_cequivc_left;
      [apply substc_cequivc;apply cequivc_sym;
       apply computes_to_valc_implies_cequivc;exact ea2|].
    eapply tequality_respects_cequivc_right;
      [apply substc_cequivc;apply cequivc_sym;
       apply computes_to_valc_implies_cequivc;exact ea1|].
    rewrite @fold_type.
    eapply tequality_respects_cequivc_left in ea0;
      [|apply substc_cequivc;apply computes_to_valc_implies_cequivc;exact ea2].
    apply tequality_refl in ea0; auto.
  }

  dands; eauto 3 with slow.

  {
    introv ea.
    autorewrite with slow.

    apply equality_in_tnat in ea.
    unfold equality_of_nat in ea; exrepnd; spcast.

    apply equality_in_tnat in sim3.
    unfold equality_of_nat in sim3; exrepnd; spcast.

    repndors; exrepnd; spcast.

    - eapply computes_to_valc_eq in sim3;[|exact comp2].
      rewrite mkc_zero_eq in sim3.
      apply mkc_nat_eq_implies in sim3; subst.
      rewrite <- mkc_zero_eq in sim0; GC.

      repeat substc_lsubstc_vars3.
      revert dependent c0; revert dependent c4.
      repeat (rewrite cons_snoc).
      introv.
      lsubst_tac.
      clear_wf_cov.
      revert dependent c26; revert dependent c28.
      repeat (rewrite <- cons_snoc).
      introv.

      pose proof (cequivc_lsubstc_mk_update_seq_sp2 lib f n m v w8 s1a a 0 k0 t0 t4 c26) as h1.
      repeat (autodimp h1 hyp); tcsp.
      pose proof (cequivc_lsubstc_mk_update_seq_sp2 lib f n m v w8 s2a a' 0 k0 t3 t5 c28) as h2.
      repeat (autodimp h2 hyp); tcsp.
      eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |exact h1]
        |].
      eapply tequality_respects_cequivc_right;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |exact h2]
        |].
      clear h1 h2; proof_irr.

      eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply implies_cequivc_mkc_add;
            [apply computes_to_valc_implies_cequivc;exact comp2
            |apply cequivc_refl]
          |apply cequivc_refl]
        |].
      eapply tequality_respects_cequivc_right;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply implies_cequivc_mkc_add;
            [apply computes_to_valc_implies_cequivc;exact comp3
            |apply cequivc_refl]
          |apply cequivc_refl]
        |].
      eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_mkc_add_integer
          |apply cequivc_refl]
        |].
      eapply tequality_respects_cequivc_right;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_mkc_add_integer
          |apply cequivc_refl]
        |].

      assert (@mkc_integer o (Z.of_nat 0 + Z.of_nat 1) = mkc_one) as e.
      { apply cterm_eq; simpl; auto. }
      rewrite e; clear e.

      apply tequality_in_mkc_apply2_mkc_nwf_pred_iff; auto.

      right; left.
      dands; spcast; auto;
      try (apply computes_to_valc_refl; eauto 3 with slow);
      try (complete (intro xx; inversion xx)).

      + eapply cequivc_trans;[apply cequivc_beta2|].
        rewrite mkcv_lam_substc; auto.
        eapply cequivc_trans;[apply cequivc_beta|].
        autorewrite with slow.
        repeat (rewrite substc2_mk_cv_app_r; auto;[]).
        autorewrite with slow.

        eapply cequivc_trans;[apply cequivc_mkc_inteq_one_zero|].
        eapply cequivc_trans;[apply cequivc_mkc_inteq_one_one|].
        auto.

      + unfold mkc_nwf_pred.
        eapply cequivc_trans;[apply cequivc_beta2|].
        rewrite mkcv_lam_substc; auto.
        eapply cequivc_trans;[apply cequivc_beta|].
        autorewrite with slow.
        repeat (rewrite substc2_mk_cv_app_r; auto;[]).
        autorewrite with slow.

        eapply cequivc_trans;[apply cequivc_mkc_inteq_one_zero|].
        eapply cequivc_trans;[apply cequivc_mkc_inteq_one_one|].
        auto.

      + unfold update_seq; split; intro h; spcast;
        eapply cequivc_trans; try (apply cequivc_beta);
        eapply cequivc_trans in h; try (apply cequivc_sym; apply cequivc_beta);
        autorewrite with slow in *;
        rewrite <- mkc_zero_eq in *.

        * autorewrite with slow in h.
          rewrite <- mkc_zero_eq in h.
          eapply cequivc_trans;[apply cequivc_mkc_inteq_zero_zero|].
          eapply cequivc_trans in h;[|apply cequivc_sym;apply cequivc_mkc_inteq_zero_zero].
          auto.

        * autorewrite with slow in h.
          rewrite <- mkc_zero_eq in h.
          eapply cequivc_trans;[apply cequivc_mkc_inteq_zero_zero|].
          eapply cequivc_trans in h;[|apply cequivc_sym;apply cequivc_mkc_inteq_zero_zero].
          auto.

    - eapply computes_to_valc_eq in sim3;[|exact comp2].
      rewrite mkc_one_eq in sim3.
      apply mkc_nat_eq_implies in sim3; subst.
      GC.

      repeat substc_lsubstc_vars3.
      revert dependent c0; revert dependent c4.
      repeat (rewrite cons_snoc).
      introv.
      lsubst_tac.
      clear_wf_cov.
      revert dependent c26; revert dependent c28.
      repeat (rewrite <- cons_snoc).
      introv.

      pose proof (cequivc_lsubstc_mk_update_seq_sp2 lib f n m v w8 s1a a 1 k0 t0 t4 c26) as h1.
      repeat (autodimp h1 hyp); tcsp.
      pose proof (cequivc_lsubstc_mk_update_seq_sp2 lib f n m v w8 s2a a' 1 k0 t3 t5 c28) as h2.
      repeat (autodimp h2 hyp); tcsp.
      eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |exact h1]
        |].
      eapply tequality_respects_cequivc_right;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |exact h2]
        |].
      clear h1 h2; proof_irr.

      eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply implies_cequivc_mkc_add;
            [apply computes_to_valc_implies_cequivc;exact comp2
            |apply cequivc_refl]
          |apply cequivc_refl]
        |].
      eapply tequality_respects_cequivc_right;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply implies_cequivc_mkc_add;
            [apply computes_to_valc_implies_cequivc;exact comp3
            |apply cequivc_refl]
          |apply cequivc_refl]
        |].
      eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_mkc_add_integer
          |apply cequivc_refl]
        |].
      eapply tequality_respects_cequivc_right;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_mkc_add_integer
          |apply cequivc_refl]
        |].

      assert (@mkc_integer o (Z.of_nat 1 + Z.of_nat 1) = mkc_two) as e.
      { apply cterm_eq; simpl; auto. }
      rewrite e; clear e.

      apply tequality_in_mkc_apply2_mkc_nwf_pred_iff; auto.

      right; right; right; right.
      exists (@PKi o 2) (@PKi o 2).
      rewrite <- mkc_integer_eq_pk2termc.
      rewrite mkc_integer_as_mkc_two.
      dands; spcast; auto;
      try (apply computes_to_valc_refl; eauto 3 with slow);
      try (complete (intro xx; inversion xx)).

      + eapply computes_to_valc_reduces_toc_trans;[apply reduce_toc_beta|].
        autorewrite with slow.
        rewrite <- mkc_one_eq.
        eapply computes_to_valc_reduces_toc_trans;[apply reduces_toc_mkc_inteq_zero_one|].
        auto.

      + eapply computes_to_valc_reduces_toc_trans;[apply reduce_toc_beta|].
        autorewrite with slow.
        rewrite <- mkc_one_eq.
        eapply computes_to_valc_reduces_toc_trans;[apply reduces_toc_mkc_inteq_zero_one|].
        auto.

      + eapply cequivc_trans;[apply cequivc_beta2|].
        rewrite mkcv_lam_substc; auto.
        eapply cequivc_trans;[apply cequivc_beta|].
        autorewrite with slow.
        repeat (rewrite substc2_mk_cv_app_r; auto;[]).
        autorewrite with slow.

        eapply cequivc_trans;[apply cequivc_mkc_inteq_two_zero|].
        eapply cequivc_trans;[apply cequivc_mkc_inteq_two_one|].

        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply cequivc_beta
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        autorewrite with slow.
        rewrite <- mkc_one_eq.
        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply cequivc_mkc_inteq_zero_one
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply computes_to_valc_implies_cequivc;exact comp6
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        eapply cequivc_trans;[apply cequivc_mkc_inteq_zero_zero|].
        auto.

      + unfold mkc_nwf_pred.
        eapply cequivc_trans;[apply cequivc_beta2|].
        rewrite mkcv_lam_substc; auto.
        eapply cequivc_trans;[apply cequivc_beta|].
        autorewrite with slow.
        repeat (rewrite substc2_mk_cv_app_r; auto;[]).
        autorewrite with slow.

        eapply cequivc_trans;[apply cequivc_mkc_inteq_two_zero|].
        eapply cequivc_trans;[apply cequivc_mkc_inteq_two_one|].
        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply cequivc_beta
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        autorewrite with slow.
        rewrite <- mkc_one_eq.
        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply cequivc_mkc_inteq_zero_one
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply computes_to_valc_implies_cequivc;exact comp
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        eapply cequivc_trans;[apply cequivc_mkc_inteq_zero_zero|].
        auto.

    - (* false *)
      eapply computes_to_valc_eq in sim3;[|exact comp3].
      rewrite mkc_zero_eq in sim3.
      apply mkc_nat_eq_implies in sim3; subst.
      eapply computes_to_valc_eq in sim0;[|exact comp4].
      symmetry in sim0.
      rewrite <- mkc_zero_eq in sim0.
      apply mkc_zero_eq_pk2term_implies in sim0; subst; tcsp.

    - (* false *)
      eapply computes_to_valc_eq in sim3;[|exact comp3].
      eapply computes_to_valc_eq in sim0;[|exact comp4].
      rewrite mkc_zero_eq in sim0.
      apply mkc_nat_eq_implies in sim0; subst.
      symmetry in sim3.
      rewrite <- mkc_zero_eq in sim3.
      apply mkc_zero_eq_pk2term_implies in sim3; subst; tcsp.

    - repeat substc_lsubstc_vars3.
      revert dependent c37; revert dependent c38.
      repeat (rewrite cons_snoc).
      introv.
      lsubst_tac.
      clear_wf_cov.
      revert dependent c39; revert dependent c40.
      repeat (rewrite <- cons_snoc).
      introv.

      eapply computes_to_valc_eq in sim3;[|exact comp2].
      eapply computes_to_valc_eq in sim0;[|exact comp4].
      symmetry in sim3; apply mkc_nat_eq_pk2term_implies in sim3.
      symmetry in sim0; apply mkc_nat_eq_pk2term_implies in sim0.
      subst; GC.
      rewrite <- mkc_integer_eq_pk2termc in comp4; rewrite <- mkc_nat_eq in comp4.
      rewrite <- mkc_integer_eq_pk2termc in comp2; rewrite <- mkc_nat_eq in comp2.

      pose proof (cequivc_lsubstc_mk_update_seq_sp2 lib f n m v w8 s1a a k1 k0 t0 t4 c39) as h1.
      repeat (autodimp h1 hyp); tcsp.
      pose proof (cequivc_lsubstc_mk_update_seq_sp2 lib f n m v w8 s2a a' k1 k0 t3 t5 c40) as h2.
      repeat (autodimp h2 hyp); tcsp.
      eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |exact h1]
        |].
      eapply tequality_respects_cequivc_right;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |exact h2]
        |].
      clear h1 h2; proof_irr.

      eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply implies_cequivc_mkc_add;
            [apply computes_to_valc_implies_cequivc;exact comp2
            |apply cequivc_refl]
          |apply cequivc_refl]
        |].
      eapply tequality_respects_cequivc_right;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply implies_cequivc_mkc_add;
            [apply computes_to_valc_implies_cequivc;exact comp4
            |apply cequivc_refl]
          |apply cequivc_refl]
        |].
      eapply tequality_respects_cequivc_left;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_mkc_add_integer
          |apply cequivc_refl]
        |].
      eapply tequality_respects_cequivc_right;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_mkc_add_integer
          |apply cequivc_refl]
        |].

      assert (@mkc_integer o (Z.of_nat k1 + Z.of_nat 1) = mkc_nat (S k1)) as e.
      { rewrite <- Znat.Nat2Z.inj_add.
        rewrite <- mkc_nat_eq.
        rewrite plus_comm; auto. }
      rewrite e; clear e.

      assert (k1 > 1) as k1gt1.
      { destruct k1; allsimpl; tcsp.
        destruct k1; allsimpl; tcsp.
        omega. }

      apply tequality_in_mkc_apply2_mkc_nwf_pred_iff; auto.

      right; right; right; right.
      exists (@PKi o (Z.of_nat (S k1))) (@PKi o (Z.of_nat (S k1))).
      rewrite <- mkc_integer_eq_pk2termc.
      rewrite <- mkc_nat_eq.
      dands; spcast; auto;
      try (apply computes_to_valc_refl; eauto 3 with slow);
      try (complete (intro xx; inversion xx)).

      + introv xx.
        apply eq_PKi_implies in xx.
        assert (1%Z = Z.of_nat 1) as yy by auto; rewrite yy in xx; clear yy.
        apply Znat.Nat2Z.inj in xx.
        destruct k1; try omega.

      + introv xx.
        apply eq_PKi_implies in xx.
        assert (1%Z = Z.of_nat 1) as yy by auto; rewrite yy in xx; clear yy.
        apply Znat.Nat2Z.inj in xx.
        destruct k1; try omega.

      + eapply computes_to_valc_reduces_toc_trans;[apply reduce_toc_beta|].
        autorewrite with slow.
        rewrite mkc_zero_eq.
        eapply computes_to_valc_reduces_toc_trans;[apply reduces_toc_mkc_inteq_nat_diff|]; try omega.
        rewrite <- mkc_zero_eq.
        auto.

      + eapply computes_to_valc_reduces_toc_trans;[apply reduce_toc_beta|].
        autorewrite with slow.
        rewrite mkc_zero_eq.
        eapply computes_to_valc_reduces_toc_trans;[apply reduces_toc_mkc_inteq_nat_diff|]; try omega.
        rewrite <- mkc_zero_eq.
        auto.

      + eapply cequivc_trans;[apply cequivc_beta2|].
        rewrite mkcv_lam_substc; auto.
        eapply cequivc_trans;[apply cequivc_beta|].
        autorewrite with slow.
        repeat (rewrite substc2_mk_cv_app_r; auto;[]).
        autorewrite with slow.

        rewrite mkc_zero_eq.
        eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|]; boolvar; try omega.
        rewrite mkc_one_eq.
        eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|]; boolvar; try omega.

        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply cequivc_beta
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        autorewrite with slow.
        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply cequivc_mkc_inteq_nat
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        boolvar; try omega.
        rewrite <- mkc_zero_eq.
        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply computes_to_valc_implies_cequivc;exact comp9
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        eapply cequivc_trans;[apply cequivc_mkc_inteq_zero_zero|].
        auto.

      + eapply cequivc_trans;[apply cequivc_beta2|].
        rewrite mkcv_lam_substc; auto.
        eapply cequivc_trans;[apply cequivc_beta|].
        autorewrite with slow.
        repeat (rewrite substc2_mk_cv_app_r; auto;[]).
        autorewrite with slow.

        rewrite mkc_zero_eq.
        eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|]; boolvar; try omega.
        rewrite mkc_one_eq.
        eapply cequivc_trans;[apply cequivc_mkc_inteq_nat|]; boolvar; try omega.

        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply cequivc_beta
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        autorewrite with slow.
        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply cequivc_mkc_inteq_nat
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        boolvar; try omega.
        rewrite <- mkc_zero_eq.
        eapply cequivc_trans;
          [apply cequivc_mkc_inteq;
            [apply computes_to_valc_implies_cequivc;exact comp10
            |apply cequivc_refl
            |apply cequivc_refl
            |apply cequivc_refl] |].
        eapply cequivc_trans;[apply cequivc_mkc_inteq_zero_zero|].
        auto.
  }

  {
    repnd; repndors; exrepnd; spcast.

    - exists (@mkc_zero o).
      rewrite mkc_zero_eq.
      dands;[apply nat_in_nat|].
      autorewrite with slow.
      rewrite <- mkc_zero_eq.

      repeat substc_lsubstc_vars3.
      revert dependent c37.
      repeat (rewrite cons_snoc).
      introv.
      lsubst_tac.
      clear_wf_cov.
      revert dependent c38.
      repeat (rewrite <- cons_snoc).
      introv.

      pose proof (cequivc_lsubstc_mk_update_seq_sp2 lib f n m v w8 s1a mkc_zero 0 0 t0 t4 c38) as h1.
      rewrite <- mkc_zero_eq in h1.
      repeat (autodimp h1 hyp); tcsp.
      { apply computes_to_valc_refl; eauto 3 with slow. }
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |exact h1]
        |].
      clear h1; proof_irr.

      eapply inhabited_type_cequivc;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply implies_cequivc_mkc_add;
            [apply computes_to_valc_implies_cequivc;exact comp2
            |apply cequivc_refl]
          |apply cequivc_refl]
        |].
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_mkc_add_integer
          |apply cequivc_refl]
        |].

      assert (@mkc_integer o (Z.of_nat 0 + Z.of_nat 1) = mkc_one) as e.
      { apply cterm_eq; simpl; auto. }
      rewrite e; clear e.

      eapply inhabited_type_cequivc;[apply cequivc_sym;apply cequivc_beta2|].
      rewrite mkcv_lam_substc; auto.
      eapply inhabited_type_cequivc;[apply cequivc_sym;apply cequivc_beta|].
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; auto;[]).
      autorewrite with slow.
      eapply inhabited_type_cequivc;[apply cequivc_sym;apply cequivc_mkc_inteq_one_zero|].
      eapply inhabited_type_cequivc;[apply cequivc_sym;apply cequivc_mkc_inteq_one_one|].

      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply implies_cequivc_cequiv;
         [apply cequivc_beta|apply cequivc_refl]
        |].
      autorewrite with slow.
      rewrite <- mkc_zero_eq.
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply implies_cequivc_cequiv;
         [apply cequivc_mkc_inteq_zero_zero|apply cequivc_refl]
        |].
      apply inhabited_cequiv; spcast; eauto 3 with slow.

    - exists (@mkc_zero o).
      rewrite mkc_zero_eq.
      dands;[apply nat_in_nat|].
      autorewrite with slow.
      rewrite <- mkc_zero_eq.

      repeat substc_lsubstc_vars3.
      revert dependent c37.
      repeat (rewrite cons_snoc).
      introv.
      lsubst_tac.
      clear_wf_cov.
      revert dependent c38.
      repeat (rewrite <- cons_snoc).
      introv.

      pose proof (cequivc_lsubstc_mk_update_seq_sp2 lib f n m v w8 s1a mkc_zero 1 0 t0 t4 c38) as h1.
      rewrite <- mkc_zero_eq in h1.
      repeat (autodimp h1 hyp); tcsp.
      { apply computes_to_valc_refl; eauto 3 with slow. }
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |exact h1]
        |].
      clear h1; proof_irr.

      eapply inhabited_type_cequivc;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply implies_cequivc_mkc_add;
            [apply computes_to_valc_implies_cequivc;exact comp2
            |apply cequivc_refl]
          |apply cequivc_refl]
        |].
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_mkc_add_integer
          |apply cequivc_refl]
        |].

      assert (@mkc_integer o (Z.of_nat 1 + Z.of_nat 1) = mkc_two) as e.
      { apply cterm_eq; simpl; auto. }
      rewrite e; clear e.

      eapply inhabited_type_cequivc;[apply cequivc_sym;apply cequivc_beta2|].
      rewrite mkcv_lam_substc; auto.
      eapply inhabited_type_cequivc;[apply cequivc_sym;apply cequivc_beta|].
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; auto;[]).
      autorewrite with slow.
      eapply inhabited_type_cequivc;[apply cequivc_sym;apply cequivc_mkc_inteq_two_zero|].
      eapply inhabited_type_cequivc;[apply cequivc_sym;apply cequivc_mkc_inteq_two_one|].

      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_inteq;
         [apply cequivc_beta|apply cequivc_refl|apply cequivc_refl|apply cequivc_refl]
        |].
      autorewrite with slow.
      rewrite <- mkc_zero_eq.
      rewrite <- mkc_one_eq.
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_inteq;
         [apply cequivc_mkc_inteq_zero_one|apply cequivc_refl|apply cequivc_refl|apply cequivc_refl]
        |].
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_inteq;
         [apply computes_to_valc_implies_cequivc; exact comp6
         |apply cequivc_refl|apply cequivc_refl|apply cequivc_refl]
        |].
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_inteq_zero_zero|].
      exists (@mkc_axiom o); eauto 3 with slow.
      apply equality_in_true; dands; spcast;
      try (apply computes_to_valc_refl; eauto 3 with slow).

    - (* false *)
      apply equality_in_tnat in sim3.
      unfold equality_of_nat in sim3; exrepnd; spcast.
      eapply computes_to_valc_eq in sim3;[|exact comp3].
      rewrite mkc_zero_eq in sim3.
      apply mkc_nat_eq_implies in sim3; subst.
      eapply computes_to_valc_eq in sim0;[|exact comp4].
      symmetry in sim0.
      rewrite <- mkc_zero_eq in sim0.
      apply mkc_zero_eq_pk2term_implies in sim0; subst; tcsp.

    - (* false *)
      apply equality_in_tnat in sim3.
      unfold equality_of_nat in sim3; exrepnd; spcast.
      eapply computes_to_valc_eq in sim3;[|exact comp3].
      eapply computes_to_valc_eq in sim0;[|exact comp4].
      rewrite mkc_zero_eq in sim0.
      apply mkc_nat_eq_implies in sim0; subst.
      symmetry in sim3.
      rewrite <- mkc_zero_eq in sim3.
      apply mkc_zero_eq_pk2term_implies in sim3; subst; tcsp.

    - exists (@mkc_zero o).
      rewrite mkc_zero_eq.
      dands;[apply nat_in_nat|].
      autorewrite with slow.
      rewrite <- mkc_zero_eq.

      repeat substc_lsubstc_vars3.
      revert dependent c37.
      repeat (rewrite cons_snoc).
      introv.
      lsubst_tac.
      clear_wf_cov.
      revert dependent c38.
      repeat (rewrite <- cons_snoc).
      introv.

      apply equality_in_tnat in sim3.
      unfold equality_of_nat in sim3; exrepnd; spcast.

      eapply computes_to_valc_eq in sim3;[|exact comp2].
      eapply computes_to_valc_eq in sim0;[|exact comp4].
      symmetry in sim3; apply mkc_nat_eq_pk2term_implies in sim3.
      symmetry in sim0; apply mkc_nat_eq_pk2term_implies in sim0.
      subst; GC.
      rewrite <- mkc_integer_eq_pk2termc in comp4; rewrite <- mkc_nat_eq in comp4.
      rewrite <- mkc_integer_eq_pk2termc in comp2; rewrite <- mkc_nat_eq in comp2.

      assert (k0 > 1) as k0gt1.
      { destruct k0; allsimpl; tcsp.
        destruct k0; allsimpl; tcsp.
        omega. }

      pose proof (cequivc_lsubstc_mk_update_seq_sp2 lib f n m v w8 s1a mkc_zero k0 0 t0 t4 c38) as h1.
      rewrite <- mkc_zero_eq in h1.
      repeat (autodimp h1 hyp); tcsp.
      { apply computes_to_valc_refl; eauto 3 with slow. }
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_refl
          |exact h1]
        |].
      clear h1; proof_irr.

      eapply inhabited_type_cequivc;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply implies_cequivc_mkc_add;
            [apply computes_to_valc_implies_cequivc;exact comp2
            |apply cequivc_refl]
          |apply cequivc_refl]
        |].
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;
          apply implies_cequivc_apply2;
          [apply cequivc_refl
          |apply cequivc_mkc_add_integer
          |apply cequivc_refl]
        |].

      assert (@mkc_integer o (Z.of_nat k0 + Z.of_nat 1) = mkc_nat (S k0)) as e.
      { rewrite <- Znat.Nat2Z.inj_add.
        rewrite <- mkc_nat_eq.
        rewrite plus_comm; auto. }
      rewrite e; clear e.

      eapply inhabited_type_cequivc;[apply cequivc_sym;apply cequivc_beta2|].
      rewrite mkcv_lam_substc; auto.
      eapply inhabited_type_cequivc;[apply cequivc_sym;apply cequivc_beta|].
      autorewrite with slow.
      repeat (rewrite substc2_mk_cv_app_r; auto;[]).
      autorewrite with slow.
      rewrite mkc_zero_eq.
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_inteq_nat|].
      boolvar; try omega;[].
      rewrite mkc_one_eq.
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_inteq_nat|].
      boolvar; try omega;[].
      rewrite <- mkc_zero_eq.

      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_inteq;
         [apply cequivc_beta|apply cequivc_refl|apply cequivc_refl|apply cequivc_refl]
        |].
      autorewrite with slow.
      rewrite mkc_zero_eq.
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_inteq;
         [apply cequivc_mkc_inteq_nat
         |apply cequivc_refl|apply cequivc_refl|apply cequivc_refl]
        |].
      boolvar;try omega;[].
      rewrite <- mkc_zero_eq.
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_inteq;
         [apply computes_to_valc_implies_cequivc; exact comp9
         |apply cequivc_refl|apply cequivc_refl|apply cequivc_refl]
        |].
      eapply inhabited_type_cequivc;
        [apply cequivc_sym;apply cequivc_mkc_inteq_zero_zero|].
      exists (@mkc_axiom o); eauto 3 with slow.
      apply equality_in_true; dands; spcast;
      try (apply computes_to_valc_refl; eauto 3 with slow).
  }
Qed.

Definition lamc1 {o} : @CTerm o := mkc_lam nvarx (mkcv_one [nvarx]).

Lemma equality_lamc1_nat2nat {o} :
  forall lib, @equality o lib lamc1 lamc1 nat2nat.
Proof.
  introv.
  apply equality_in_fun; dands; eauto 3 with slow.
  introv ea.

  eapply equality_respects_cequivc_left;[apply cequivc_sym;apply cequivc_beta|].
  eapply equality_respects_cequivc_right;[apply cequivc_sym;apply cequivc_beta|].
  autorewrite with slow.
  rewrite mkc_one_eq.
  eauto 3 with slow.
Qed.
Hint Resolve equality_lamc1_nat2nat : slow.

(* I get a universe inconsistency error when using notT instead of _ -> False *)
Lemma not_concl_nwf_pred {o} :
  forall lib H k s f n s1,
    f <> n
    -> s <> k
    -> hyps_functionality lib s1 H
    -> similarity lib s1 s1 H
    -> @sequent_true2
         o
         lib
         (choice_sequence_ind_concl H (nwf_pred k s) f n)
    -> False.
Proof.
  introv d1 d2 hf sim seq.
  destruct seq as [wf seq].
  vr_seq_true in seq.

  pose proof (seq s1 s1) as h; clear seq; repeat (autodimp h hyp).
  exrepnd.
  unfold mk_exists in *.
  unfold mk_forall in *.
  lsubst_tac.

  clear h0.
  apply equality_in_mkc_squash in h1; repnd.
  clear h0 h2.
  apply inhabited_product in h1; repnd.
  clear h0 h1.

  pose proof (h2 lamc1 lamc1) as h; clear h2.
  autodimp h hyp.
  {
    eapply respects_alphaeqc_equality;[apply alphaeqc_sym;apply lsubstc_mk_nat2nat|].
    eauto 3 with slow.
  }

  repeat lsubstc_vars_as_mkcv.
  autorewrite with slow in h.
  rewrite substc_mkcv_function in h; auto;[].
  autorewrite with slow in h.
  apply tequality_function in h; repnd.
  clear h0.
  pose proof (h mkc_two mkc_two) as q; clear h.
  autodimp q hyp.
  { rw @mkc_two_eq; eauto 3 with slow. }

  autorewrite with slow in q.
  repeat (rewrite substcv_as_substc2 in q).
  autorewrite with slow in q.
  rw @tequality_mkc_squash in q.
  repeat (rewrite substc2_mk_cv_app_r in q; auto;[]).
  autorewrite with slow in q.

  apply tequality_in_mkc_apply2_mkc_nwf_pred_iff in q; auto.
  repndors; exrepnd; spcast.

  - apply computes_to_valc_isvalue_eq in q0; eauto 3 with slow.
    apply implies_eq_get_cterm in q0; simpl in q0; inversion q0.

  - apply computes_to_valc_isvalue_eq in q0; eauto 3 with slow.
    apply implies_eq_get_cterm in q0; simpl in q0; inversion q0.

  - apply computes_to_valc_isvalue_eq in q1; eauto 3 with slow.
    apply implies_eq_get_cterm in q1; simpl in q1; inversion q1.

  - apply computes_to_valc_isvalue_eq in q2; eauto 3 with slow.
    apply implies_eq_get_cterm in q2; simpl in q2; inversion q2.

  - eapply computes_to_valc_reduces_toc in q7;[|apply reduce_toc_beta].
    autorewrite with slow in q7.
    apply computes_to_valc_isvalue_eq in q7; eauto 3 with slow.
    apply implies_eq_get_cterm in q7; simpl in q7; inversion q7.
Qed.
