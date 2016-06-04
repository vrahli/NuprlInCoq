 (*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University

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
Require Export types_converge.
Require Export list. (* WTF! *)


Definition nwf_pred {o} (n s : NVar) :=
  @mk_lam
    o
    n
    (mk_lam
       s
       (mk_int_eq
          (mk_var n)
          mk_zero
          (mk_cequiv (mk_apply (mk_var s) mk_zero) mk_zero)
          (mk_int_eq
             (mk_apply (mk_var s) mk_zero)
             mk_zero
             mk_true
             mk_axiom))).

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
  forall lib H n s,
    s <> n
    -> wf_hypotheses H
    -> @sequent_true2
         o
         lib
         (choice_sequence_ind_base H (nwf_pred n s) lam0 mk_axiom).
Proof.
  introv d1 wfH.

  assert (wf_csequent (choice_sequence_ind_base H (nwf_pred n s) lam0 mk_axiom)) as wfc.
  {
    unfold wf_csequent, closed_type, closed_extract, wf_sequent, wf_concl; simpl.
    dwfseq.
    dands; tcsp;
    try (complete (rw @vswf_hypotheses_nil_eq; auto)).
    introv i; allrw in_remove_nvars; allsimpl; allrw not_over_or.
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
    boolvar; try omega; GC;[].

    eapply tequality_respects_cequivc_left;
      [apply cequivc_sym;
        apply implies_cequivc_cequiv;
        [apply cequivc_beta|apply cequivc_refl]
      |].
    eapply tequality_respects_cequivc_right;
      [apply cequivc_sym;
        apply implies_cequivc_cequiv;
        [apply cequivc_beta|apply cequivc_refl]
      |].
    autorewrite with slow.
    eauto 3 with slow.

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

    eapply cequivc_preserving_equality;
      [|apply cequivc_sym;
         apply implies_cequivc_cequiv;
         [apply cequivc_beta|apply cequivc_refl]
      ].
    autorewrite with slow.
    apply equality_in_mkc_cequiv.
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
  apply isprog_vars_inteq.
  rw @isprog_vars_cequiv_iff.
  allrw @isprog_vars_inteq.
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
             (mk_cv (s :: n :: vs) (mkc_axiom))))).

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
             (mk_cv [s,n] (mkc_axiom))))).

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

Lemma equality_in_mkc_apply2_mkc_nwf_pred_implies {o} :
  forall lib (t1 t2 n f : @CTerm o) k s,
    s <> k
    -> equality lib t1 t2 (mkc_apply2 (mkc_nwf_pred k s) n f)
    ->
    (
      (
        ccomputes_to_valc lib t1 mkc_axiom
        /\ ccomputes_to_valc lib t2 mkc_axiom
        /\ ccomputes_to_valc lib n mkc_zero
        /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) (mkc_cequiv (mkc_apply f mkc_zero) mkc_zero)

      )
        {+}
        {pk : param_kind
         , ccomputes_to_valc lib n (pk2termc pk)
         /\ pk <> PKi 0
         /\ ccomputes_to_valc lib t1 mkc_axiom
         /\ ccomputes_to_valc lib t2 mkc_axiom
         /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
         /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) mkc_true
        }
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
    apply equality_in_mkc_cequiv in e1; repnd; spcast.
    eapply cequivc_sym in e1.
    eapply cequivc_nat_implies in e1;
      [|rewrite mkc_zero_eq; apply computes_to_valc_refl; eauto 3 with slow].
    rewrite <- mkc_zero_eq in e1.

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
    apply mkc_zero_eq_pk2term_implies in e5; subst.
    repndors; repnd; subst; spcast.

    + apply equality_in_true in e1; repnd; spcast.
      rewrite <- mkc_integer_eq_pk2termc in e4.
      assert (0%Z = Z.of_nat 0) as xx by auto.
      rewrite xx in e4; clear xx.
      rewrite <- mkc_nat_eq in e4.
      rewrite <- mkc_zero_eq in e4.

      right.
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

    + apply not_equality_in_axiom in e1; sp.
Qed.

Lemma implies_equality_in_mkc_apply2_mkc_nwf_pred {o} :
  forall lib (t1 t2 n f : @CTerm o) k s,
    s <> k
    ->
    (
      (
        ccomputes_to_valc lib t1 mkc_axiom
        /\ ccomputes_to_valc lib t2 mkc_axiom
        /\ ccomputes_to_valc lib n mkc_zero
        /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) (mkc_cequiv (mkc_apply f mkc_zero) mkc_zero)
      )
        {+}
        {pk : param_kind
         , ccomputes_to_valc lib n (pk2termc pk)
         /\ pk <> PKi 0
         /\ ccomputes_to_valc lib t1 mkc_axiom
         /\ ccomputes_to_valc lib t2 mkc_axiom
         /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
         /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) mkc_true
        }
    )
    -> equality lib t1 t2 (mkc_apply2 (mkc_nwf_pred k s) n f).
Proof.
  introv d comp.
  repndors; exrepnd; spcast.

  - eapply cequivc_preserving_equality;[|apply cequivc_sym;exact comp].
    apply equality_in_mkc_cequiv; dands; spcast; eauto 3 with slow.

  - eapply cequivc_preserving_equality;[|apply cequivc_sym;exact comp0].
    apply equality_in_true; dands; spcast; eauto 3 with slow.
Qed.

Lemma equality_in_mkc_apply2_mkc_nwf_pred_iff {o} :
  forall lib (t1 t2 n f : @CTerm o) k s (d : s <> k),
    equality lib t1 t2 (mkc_apply2 (mkc_nwf_pred k s) n f)
    <=>
    (
      (
        ccomputes_to_valc lib t1 mkc_axiom
        /\ ccomputes_to_valc lib t2 mkc_axiom
        /\ ccomputes_to_valc lib n mkc_zero
        /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
        /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) (mkc_cequiv (mkc_apply f mkc_zero) mkc_zero)

      )
        {+}
        {pk : param_kind
         , ccomputes_to_valc lib n (pk2termc pk)
         /\ pk <> PKi 0
         /\ ccomputes_to_valc lib t1 mkc_axiom
         /\ ccomputes_to_valc lib t2 mkc_axiom
         /\ ccomputes_to_valc lib (mkc_apply f mkc_zero) mkc_zero
         /\ ccequivc lib (mkc_apply2 (mkc_nwf_pred k s) n f) mkc_true
        }
    ).
Proof.
  introv d; split; intro h.
  - apply equality_in_mkc_apply2_mkc_nwf_pred_implies; auto.
  - apply implies_equality_in_mkc_apply2_mkc_nwf_pred; auto.
Qed.

Lemma ind_nwf_pred {o} :
  forall lib H k s f n m z v,
    s <> k
    -> z <> n
    -> z <> f
    -> f <> n
    -> k <> m
    -> !LIn n (vars_hyps H)
    -> !LIn f (vars_hyps H)
    -> !LIn z (vars_hyps H)
    -> wf_hypotheses H
    -> @sequent_true2
         o
         lib
         (choice_sequence_ind_ind H (nwf_pred k s) f n m z v).
Proof.
  introv d1 d2 d3 d4 d5 ni1 ni2 ni3 wfH.

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

  apply implies_tequality_equality_mkc_squash_and.
  rw @tequality_product.
  rw @inhabited_product.
  autorewrite with slow.

  dands; eauto 3 with slow.

  {
    introv ea.
    repeat (lsubstc_vars_as_mkcv; clear_wf_cov).
    autorewrite with slow.

    pose proof (lsubstc_vars_mk_add_as_mkcv
                  (mk_var n) mk_one w4 (csub_filter s1 [m]) [m] c7) as h1.
    exrepnd; rewrite h1; clear h1.

    pose proof (lsubstc_vars_mk_add_as_mkcv
                  (mk_var n) mk_one w4 (csub_filter s2 [m]) [m] c10) as h1.
    exrepnd; rewrite h1; clear h1.

    repeat (lsubstc_vars_as_mkcv; clear_wf_cov).
    autorewrite with slow.

    apply similarity_snoc in sim; simpl in sim; exrepnd; subst.
    apply similarity_snoc in sim3; simpl in sim3; exrepnd; subst.
    apply similarity_snoc in sim4; simpl in sim4; exrepnd; subst.
    autorewrite with slow in *.

    assert (!LIn n (dom_csub s1a)) as nin1.
    {
      apply similarity_dom in sim5; repnd; allrw; auto.
    }

    eapply alphaeqc_preserving_equality in sim2;
      [|apply lsubstc_mk_natk2nat_sp2; auto];[].
    lsubst_tac.
    clear_wf_cov.
    autorewrite with slow in *.

    apply equality_in_mkc_apply2_mkc_nwf_pred_iff in sim1.

  }
Qed.

Lemma not_well_formed {o} :
  forall lib,
    not (tequality
           lib
           ()
        )


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../per/" "../close/")
*** End:
*)
