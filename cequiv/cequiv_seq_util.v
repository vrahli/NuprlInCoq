(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Require Export cvterm4.
Require Export cequiv_bind.
Require Export csubst7.
Require Export cnterm.
Require Export continuity_defs_ceq.


Lemma free_vars_mk_natk2nat {o} :
  forall v, @free_vars o (mk_natk2nat (mk_var v)) = [v].
Proof.
  introv; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw remove_nvars_cons.
  allrw remove_nvars_nil_l.

  pose proof (@newvar_prop o (mk_var v)) as nvp.
  remember (newvar (mk_var v)) as nv.
  clear Heqnv; simphyps.
  allrw not_over_or; repnd; GC.

  pose proof (@newvar_prop o (mk_less_than (mk_var nv) (mk_var v))) as nvp'.
  remember (newvar (mk_less_than (mk_var nv) (mk_var v))) as nv'.
  clear Heqnv'; simphyps.
  allrw not_over_or; repnd; GC.

  allsimpl; boolvar; tcsp.
  simpl.
  boolvar; tcsp.
Qed.

Lemma lsubstc_mk_natk2nat_sp1 {o} :
  forall v (t : @CTerm o) w s c,
    alphaeqc
      (lsubstc (mk_natk2nat (mk_var v)) w ((v,t) :: s) c)
      (natk2nat t).
Proof.
  introv.
  unfold alphaeqc; simpl.
  unfold csubst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
  simpl.
  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_trivial.
  allrw @sub_find_sub_filter_trivial2.
  allrw memvar_singleton.
  repeat (rw @beq_var_newvar_trivial1; simpl; tcsp;[]).
  allrw memvar_singleton.
  repeat (rw @beq_var_newvar_trivial1; simpl; tcsp;[]).
  allrw @sub_find_sub_filter_trivial.
  allrw @sub_find_sub_filter_trivial2.
  allrw <- beq_var_refl.
  fold_terms.

  destruct_cterms; allsimpl.
  unfold mk_fun, mk_function, nobnd.
  prove_alpha_eq4.

  introv j.
  repeat (destruct n; tcsp; try omega); clear j;[].
  apply alphaeqbt_nilv2.

  unfold mk_natk, mk_natk_aux, mk_set, nobnd.
  prove_alpha_eq4;[].
  introv j.
  repeat (destruct n; tcsp; try omega); clear j;[].

  pose proof (ex_fresh_var (newvar (mk_less_than (mk_var (newvar (@mk_var o v))) (@mk_var o v))
                                   :: (newvar (mk_less_than (mk_var (newvar x)) x))
                                   :: (all_vars
         (@mk_product o
            (mk_function (mk_less_than (mk_var (newvar (@mk_var o v))) mk_zero)
               (newvar (@mk_void o)) mk_void)
            (newvar (mk_less_than (mk_var (newvar (@mk_var o v))) (@mk_var o v)))
            (mk_less_than (mk_var (newvar (@mk_var o v))) x)) ++
       all_vars
         (mk_prod (mk_le mk_zero (mk_var (newvar x)))
            (mk_less_than (mk_var (newvar x)) x))))) as fv.
  exrepnd.
  rw @in_cons_iff in fv0.
  rw @in_cons_iff in fv0.
  rw not_over_or in fv0.
  rw not_over_or in fv0.
  repnd.

  apply (al_bterm_aux [v0]); auto.

  { apply disjoint_singleton_l; fold_terms; auto. }

  Opaque beq_var.
  simpl.
  allrw @sub_filter_nil_r.
  allrw memvar_singleton.
  fold_terms.
  repeat (rw @beq_var_newvar_trivial1; simpl; tcsp;[]).
  allrw <- beq_var_refl.
  repeat (rw (beq_var_newvar_trivial1 (newvar (@mk_var o v))
                                      (mk_less_than (mk_var (newvar (@mk_var o v))) (@mk_var o v)));
          simpl; tcsp;[]).
  repeat (rw (beq_var_newvar_trivial1 (newvar x)
                                      (mk_less_than (mk_var (newvar x)) x));
          simpl; tcsp;[]).
  allrw <- beq_var_refl.
  allrw memvar_singleton; simpl.

  repeat (rw (lsubst_aux_trivial_cl_term2 x); eauto 2 with slow;[]).

  unfold mk_product, nobnd.
  prove_alpha_eq4.
  introv j.
  repeat (destruct n; tcsp; try omega); clear j;[|].

  { apply alphaeqbt_nilv2.

    unfold mk_function, nobnd.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try omega); clear j;[|].

    { apply alphaeqbt_nilv2.
      unfold mk_less, nobnd.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alphaeqbt_nilv2.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alphaeqbt_nilv2.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alphaeqbt_nilv2.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alpha_eq_bterm_congr.
      repeat (boolvar; simpl); tcsp.
    }

    { apply alpha_eq_bterm_congr.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alpha_eq_bterm_congr.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alpha_eq_bterm_congr.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try omega); clear j;[].

      apply alpha_eq_bterm_congr.
      repeat (boolvar; simpl); tcsp.
    }
  }

  { pose proof (ex_fresh_var ((newvar (mk_less_than (mk_var (newvar (@mk_var o v))) (@mk_var o v)))
                                :: (newvar (mk_less_than (mk_var (newvar x)) x))
                                :: (all_vars
         (mk_less (mk_var v0) x
            mk_true
            (mk_approx mk_axiom
               (mk_fix
                  (mk_lam nvarx
                     match
                       sub_find
                         (if beq_var (newvar (@mk_var o v)) nvarx
                          then []
                          else [(newvar (@mk_var o v), mk_var v0)]) nvarx
                     with
                     | Some t => t
                     | None => mk_var nvarx
                     end)))) ++
       all_vars
         (mk_less (mk_var v0) x mk_true
            (mk_approx mk_axiom
               (mk_fix
                  (mk_lam nvarx
                     match
                       sub_find
                         (if beq_var (newvar x) nvarx
                          then []
                          else [(newvar x, mk_var v0)]) nvarx
                     with
                     | Some t => t
                     | None => mk_var nvarx
                     end))))))) as fv.
    exrepnd.
    rw @in_cons_iff in fv3.
    rw @in_cons_iff in fv3.
    rw not_over_or in fv3.
    rw not_over_or in fv3.
    repnd.

    apply (al_bterm_aux [v1]); auto.

    { apply disjoint_singleton_l; fold_terms; auto. }

    simpl.
    fold_terms.
    repeat (rw not_eq_beq_var_false;tcsp;[]).
    repeat (rw (not_eq_beq_var_false (newvar (mk_less_than (mk_var (newvar x)) x))); tcsp;[]).

    repeat (rw (lsubst_aux_trivial_cl_term2 x); eauto 2 with slow;[]).

    unfold mk_less, nobnd.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try omega); clear j;[].

    apply alpha_eq_bterm_congr.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try omega); clear j;[].

    apply alpha_eq_bterm_congr.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try omega); clear j;[].

    apply alpha_eq_bterm_congr.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try omega); clear j;[].

    apply alpha_eq_bterm_congr.
    repeat (boolvar; subst; simpl; tcsp);
      try (complete (rw not_over_or in Heqb; tcsp));
      try (complete (rw not_over_or in Heqb0; tcsp)).
  }
Qed.

Lemma lsubstc_mk_natk2nat_sp2 {o} :
  forall v (t : @CTerm o) w s c,
    !LIn v (dom_csub s)
    -> alphaeqc
         (lsubstc (mk_natk2nat (mk_var v)) w (snoc s (v,t)) c)
         (natk2nat t).
Proof.
  introv niv.

  assert (cover_vars (mk_natk2nat (mk_var v)) ((v, t) :: s)) as cv.
  { allrw @cover_vars_mk_natk2nat.
    allrw @cover_vars_var_iff.
    allsimpl.
    allrw @dom_csub_snoc; allsimpl.
    allrw in_snoc; sp. }

  pose proof (lsubstc_mk_natk2nat_sp1 v t w s cv) as h.
  eapply alphaeqc_trans;[|exact h].

  unfold alphaeqc; simpl.
  apply alpha_eq_lsubst_if_ext_eq; auto.
  unfold ext_alpha_eq_subs.
  rw @free_vars_mk_natk2nat; simpl.
  introv e; repndors; tcsp; subst.
  boolvar; tcsp.
  rw @csub2sub_snoc.
  rw @sub_find_snoc.
  boolvar.
  rw @sub_find_none_if; eauto 3 with slow.
  rw @dom_csub_eq; auto.
Qed.

Lemma mkc_nat_eq_implies {o} :
  forall n m, @mkc_nat o n = mkc_nat m -> n = m.
Proof.
  introv h.
  inversion h as [q].
  apply Znat.Nat2Z.inj in q; auto.
Qed.

Lemma wf_or {o} :
  forall (a b : @NTerm o),
    wf_term (mk_or a b) <=> (wf_term a # wf_term b).
Proof.
  introv.
  unfold mk_or.
  rw @wf_union; sp.
Qed.

Lemma wf_dec {o} :
  forall (a : @NTerm o),
    wf_term (mk_dec a) <=> wf_term a.
Proof.
  introv.
  unfold mk_dec.
  rw @wf_or.
  rw @wf_not.
  split; sp.
Qed.

Lemma cover_vars_union {o} :
  forall (a b : @NTerm o) s,
    cover_vars (mk_union a b) s <=> (cover_vars a s # cover_vars b s).
Proof.
  introv.
  allrw @cover_vars_eq; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma cover_vars_or {o} :
  forall (a b : @NTerm o) s,
    cover_vars (mk_or a b) s <=> (cover_vars a s # cover_vars b s).
Proof.
  introv.
  unfold mk_or.
  rw @cover_vars_union; sp.
Qed.

Lemma cover_vars_dec {o} :
  forall (a : @NTerm o) s,
    cover_vars (mk_dec a) s <=> cover_vars a s.
Proof.
  introv.
  unfold mk_dec.
  rw @cover_vars_or.
  rw @cover_vars_not.
  split; sp.
Qed.

Lemma covered_union {o} :
  forall (a b : @NTerm o) vs,
    covered (mk_union a b) vs <=> (covered a vs # covered b vs).
Proof.
  introv.
  unfold covered; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l; sp.
Qed.

Lemma covered_or {o} :
  forall (a b : @NTerm o) vs,
    covered (mk_or a b) vs <=> (covered a vs # covered b vs).
Proof.
  introv.
  unfold mk_or.
  rw @covered_union; sp.
Qed.

Lemma covered_not {o} :
  forall (a : @NTerm o) vs,
    covered (mk_not a) vs <=> covered a vs.
Proof.
  introv.
  unfold mk_not.
  rw @covered_fun.
  split; sp.
Qed.

Lemma covered_dec {o} :
  forall (a : @NTerm o) vs,
    covered (mk_dec a) vs <=> covered a vs.
Proof.
  introv.
  unfold mk_dec.
  rw @covered_or.
  rw @covered_not.
  split; sp.
Qed.

Lemma covered_snoc_implies {o} :
  forall (t : @NTerm o) (v : NVar) (vs : list NVar),
    !LIn v (free_vars t)
    -> covered t (snoc vs v)
    -> covered t vs.
Proof.
  introv ni cov.
  allunfold @covered; allsimpl.
  allrw subvars_eq.
  introv i.
  applydup cov in i.
  allrw in_snoc.
  repndors; subst; tcsp.
Qed.

Lemma wf_term_mk_nat2nat {o} : @wf_term o mk_nat2nat.
Proof.
  introv.
  unfold mk_nat2nat.
  apply wf_fun; dands; apply wf_tnat.
Qed.

Lemma cover_vars_mk_nat2nat {o} :
  forall (s : @CSub o), cover_vars mk_nat2nat s.
Proof.
  introv.
  unfold mk_nat2nat.
  apply cover_vars_fun; dands; apply cover_vars_mk_tnat.
Qed.

Definition mk_update_seq {o} (s n m : @NTerm o) v :=
  mk_lam v (mk_int_eq (mk_var v) n m (mk_apply s (mk_var v))).

Definition mk_seq2kseq {o} (s n : @NTerm o) (v : NVar) : NTerm :=
  mk_lam
    v
    (mk_less
       (mk_var v)
       mk_zero
       mk_bot
       (mk_less
          (mk_var v)
          n
          (mk_apply s (mk_var v))
          mk_bot)).

Lemma wf_seq2kseq {o} :
  forall (t : @NTerm o) n v,
    wf_term (mk_seq2kseq t n v) <=> (wf_term t # wf_term n).
Proof.
  introv.
  unfold mk_seq2kseq.
  rw <- @wf_lam_iff.
  allrw <- @wf_less_iff.
  rw <- @wf_apply_iff.
  split; intro h; repnd; dands; eauto 3 with slow.
Qed.

Lemma cover_vars_upto_mk_nat {o} :
  forall n (s : @CSub o) vs,
    cover_vars_upto (mk_nat n) s vs.
Proof.
  introv.
  unfold cover_vars_upto; simpl; sp.
Qed.
Hint Resolve cover_vars_upto_mk_nat : slow.

Lemma cover_vars_seq2kseq {o} :
  forall (t : @NTerm o) n v s,
    !LIn v (free_vars t)
    -> !LIn v (free_vars n)
    -> (cover_vars (mk_seq2kseq t n v) s <=> (cover_vars t s # cover_vars n s)).
Proof.
  introv nit niv.
  unfold mk_seq2kseq.
  rw @cover_vars_lam.
  allrw @cover_vars_upto_less.
  allrw @cover_vars_upto_apply.
  allrw @cover_vars_upto_var.
  allsimpl.
  split; intro h; repnd; dands; eauto 3 with slow.
  - apply cover_vars_upto_csub_filter_disjoint in h6; auto.
    apply disjoint_singleton_r; auto.
  - apply cover_vars_upto_csub_filter_disjoint in h4; auto.
    apply disjoint_singleton_r; auto.
  - apply cover_vars_upto_csub_filter_disjoint; auto.
    apply disjoint_singleton_r; auto.
  - apply cover_vars_upto_csub_filter_disjoint; auto.
    apply disjoint_singleton_r; auto.
Qed.

Lemma csubst_mk_less {o} :
  forall (a b c d : @NTerm o) s,
    csubst (mk_less a b c d) s
    = mk_less (csubst a s) (csubst b s) (csubst c s) (csubst d s).
Proof.
  introv.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd. sp.
Qed.

Lemma csubst_mk_bot {o} :
  forall (sub : @CSub o), csubst mk_bot sub = mk_bot.
Proof.
  introv.
  rw @csubst_trivial; auto.
  simpl; auto.
Qed.

Lemma csubst_mk_nat {o} :
  forall n (sub : @CSub o), csubst (mk_nat n) sub = mk_nat n.
Proof.
  introv.
  rw @csubst_trivial; auto.
  simpl; auto.
Qed.

Definition seq2kseq2 {o} (s n : @CTerm o) (v : NVar) : CTerm :=
  mkc_lam
    v
    (mkcv_less
       [v]
       (mkc_var v)
       (mkcv_zero [v])
       (mkcv_bot [v])
       (mkcv_less
          [v]
          (mkc_var v)
          (mk_cv [v] n)
          (mkcv_apply [v] (mk_cv [v] s) (mkc_var v))
          (mkcv_bot [v]))).

Definition seq2kseq {o} (s : @CTerm o) (n : nat) (v : NVar) : CTerm :=
  mkc_lam
    v
    (mkcv_less
       [v]
       (mkc_var v)
       (mkcv_zero [v])
       (mkcv_bot [v])
       (mkcv_less
          [v]
          (mkc_var v)
          (mkcv_nat [v] n)
          (mkcv_apply [v] (mk_cv [v] s) (mkc_var v))
          (mkcv_bot [v]))).

Lemma isprog_vars_mk_less {p} :
  forall (a b c d : @NTerm p) vs,
    isprog_vars vs (mk_less a b c d)
    <=> (isprog_vars vs a
         # isprog_vars vs b
         # isprog_vars vs c
         # isprog_vars vs d).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l).
  repeat (rw <- @wf_term_eq).
  allrw <- @wf_less_iff; split; sp.
Qed.

Lemma isprogram_mk_less {p} :
  forall (a b c d : @NTerm p),
    isprogram (mk_less a b c d)
    <=> (isprogram a
         # isprogram b
         # isprogram c
         # isprogram d).
Proof.
  introv.
  pose proof (isprog_vars_mk_less a b c d []) as h.
  allrw <- @isprog_vars_nil_iff_isprog.
  allrw @isprogram_eq; auto.
Qed.

Lemma implies_approxc_mkc_less1 {o} :
  forall lib (a b c d e f g : @CTerm o),
    (forall i : Z,
       computes_to_valc lib a (mkc_integer i)
       -> cequivc lib (mkc_less (mkc_integer i) b c d) (mkc_less (mkc_integer i) e f g))
    -> approxc lib (mkc_less a b c d) (mkc_less a e f g).
Proof.
  introv imp.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  allunfold @computes_to_valc; allsimpl.

  constructor.
  unfold close_comput; dands; auto;
  try (apply isprogram_mk_less; dands; eauto 3 with slow).

  + introv comp.
    apply computes_to_value_mk_less in comp; eauto 3 with slow; exrepnd.

    pose proof (imp k1) as h; clear imp.
    autodimp h hyp.
    { split; eauto 3 with slow. }
    destruct h as [h1 h2]; clear h2.
    inversion h1 as [cl]; clear h1.
    unfold close_comput in cl; repnd.

    pose proof (cl2 c tl_subterms) as h.
    autodimp h hyp.

    * split;[|allunfold @computes_to_value; sp];[].
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp;
          [apply computes_to_value_isvalue_refl;eauto 3 with slow
          |eauto 3 with slow
          |exact comp2]
        |].
      repndors; repnd; allunfold @computes_to_value; repnd.

      { eapply reduces_to_if_split2;[|exact comp4].
        csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl.
        boolvar;try omega;auto. }

      { eapply reduces_to_if_split2;[|exact comp4].
        csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl.
        boolvar;try omega;auto. }

    * exrepnd.
      exists tr_subterms; dands; auto.

      allunfold @computes_to_value; repnd.
      split; tcsp.
      eapply reduces_to_trans;[apply reduces_to_prinarg;exact comp0|].
      auto.

  + introv comp.
    apply computes_to_exception_mk_less in comp; eauto 3 with slow.
    repndors; exrepnd.

    * pose proof (imp k1) as h; clear imp.
      autodimp h hyp.
      { split; eauto 3 with slow. }
      destruct h as [h1 h2]; clear h2.
      inversion h1 as [cl]; clear h1.
      unfold close_comput in cl; repnd.

      pose proof (cl3 a e) as h.
      autodimp h hyp.

      { eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp;
          [apply computes_to_value_isvalue_refl;eauto 3 with slow
          |eauto 3 with slow
          |exact comp2]
        |].
        repndors; repnd.

        { eapply reduces_to_if_split2;[|exact comp1].
          csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl.
          boolvar;try omega;auto. }

        { eapply reduces_to_if_split2;[|exact comp1].
          csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl.
          boolvar;try omega;auto. }
      }

      { exrepnd.
        exists a' e'; dands; auto.

        eapply reduces_to_trans;[apply reduces_to_prinarg;exact comp0|].
        auto.
      }

    * applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
      exists a e; dands; eauto 3 with slow;
      try (left; apply approx_refl; eauto 3 with slow).
      eapply reduces_to_trans;[apply reduces_to_prinarg;exact comp|].
      apply reduces_to_if_step.
      csunf; simpl; auto.

    * applydup @preserve_program_exc2 in comp0; eauto 3 with slow; repnd.

      pose proof (imp z) as h; clear imp.
      autodimp h hyp.
      { split; eauto 3 with slow. }
      destruct h as [h1 h2]; clear h2.
      inversion h1 as [cl]; clear h1.
      unfold close_comput in cl; repnd.

      pose proof (cl3 a e) as h.
      autodimp h hyp.

      { eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp;
          [apply computes_to_value_isvalue_refl;eauto 3 with slow
          |eauto 3 with slow
          |exact comp0]
        |]; fold_terms.
        apply reduces_to_if_step.
        csunf; simpl; dcwf h; simpl; auto.
      }

      { exrepnd.
        exists a' e'; dands; auto.

        eapply reduces_to_trans;[apply reduces_to_prinarg;exact comp1|].
        auto.
      }
Qed.

Lemma implies_cequivc_mkc_less1 {o} :
  forall lib (a b c d e f g : @CTerm o),
    (forall i : Z,
       computes_to_valc lib a (mkc_integer i)
       -> cequivc lib (mkc_less (mkc_integer i) b c d) (mkc_less (mkc_integer i) e f g))
    -> cequivc lib (mkc_less a b c d) (mkc_less a e f g).
Proof.
  introv imp.
  apply cequivc_iff_approxc; dands.
  - apply implies_approxc_mkc_less1; auto.
  - apply implies_approxc_mkc_less1; auto.
    introv comp.
    apply cequivc_sym; auto.
Qed.

Lemma mkcv_nat_substc {o} :
  forall v (t : @CTerm o) n,
    substc t v (mkcv_nat [v] n) = mkc_nat n.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma seq2kseq2_as_seq2kseq {o} :
  forall lib (s : @CTerm o) n m v,
    computes_to_valc lib n (mkc_nat m)
    -> cequivc lib (seq2kseq2 s n v) (seq2kseq s m v).
Proof.
  introv comp.
  unfold seq2kseq, seq2kseq2.
  apply implies_cequivc_lam; introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.
  allrw @mkc_zero_eq.
  eapply cequivc_mkc_less;
    [apply cequivc_refl
    |apply cequivc_refl
    |apply cequivc_refl
    |eapply cequivc_mkc_less;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc; auto
      |apply cequivc_refl
      |apply cequivc_refl]
    ].
Qed.

Lemma seq2kseq2_as_seq2kseq2 {o} :
  forall (s : @CTerm o) n v,
   seq2kseq2 s (mkc_nat n) v = seq2kseq s n v.
Proof.
  introv.
  apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_seq2kseq2 {o} :
  forall (t : @NTerm o) n v w s c,
    !LIn v (free_vars t)
    -> !LIn v (free_vars n)
    -> {wt : wf_term t
        & {ct : cover_vars t s
        & {wn : wf_term n
        & {cn : cover_vars n s
        & lsubstc (mk_seq2kseq t n v) w s c
          = seq2kseq2 (lsubstc t wt s ct) (lsubstc n wn s cn) v }}}}.
Proof.
  introv nit nin.

  assert (wf_term t) as wt.
  { apply wf_seq2kseq in w; sp. }

  assert (cover_vars t s) as ct.
  { apply cover_vars_seq2kseq in c; sp. }

  assert (wf_term n) as wn.
  { apply wf_seq2kseq in w; sp. }

  assert (cover_vars n s) as cn.
  { apply cover_vars_seq2kseq in c; sp. }

  exists wt ct wn cn.
  apply cterm_eq; simpl.
  unfold mk_seq2kseq.
  rw @csubst_mk_lam.
  allrw @csubst_mk_less.
  allrw @csubst_mk_apply.
  allrw @csubst_mk_zero.
  allrw @csubst_mk_bot.
  allrw @csubst_mk_nat.
  repeat (rw @csubst_var_not_in;
          [|rw @dom_csub_csub_filter;rw in_remove_nvars;rw in_single_iff;sp]).
  allrw @csubst_csub_filter; auto; apply disjoint_singleton_r; auto.
Qed.

Lemma lsubstc_mk_nat {o} :
  forall n w (s : @CSub o) c,
    lsubstc (mk_nat n) w s c = mkc_nat n.
Proof.
  unfold lsubstc, mkc_axiom; sp.
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_seq2kseq {o} :
  forall (t : @NTerm o) n v w s c,
    !LIn v (free_vars t)
    -> {wt : wf_term t
        & {ct : cover_vars t s
        & lsubstc (mk_seq2kseq t (mk_nat n) v) w s c
          = seq2kseq (lsubstc t wt s ct) n v }}.
Proof.
  introv nit.
  pose proof (lsubstc_mk_seq2kseq2 t (mk_nat n) v w s c) as h.
  simpl in h.
  repeat (autodimp h hyp); tcsp; exrepnd.
  allrw @lsubstc_mk_nat.
  exists wt ct; auto.
  rw @seq2kseq2_as_seq2kseq2 in h1; auto.
Qed.

Lemma implies_cequivc_seq2kseq2 {o} :
  forall lib (v : NVar) (s1 s2 n1 n2 : @CTerm o),
    cequivc lib s1 s2
    -> cequivc lib n1 n2
    -> cequivc lib (seq2kseq2 s1 n1 v) (seq2kseq2 s2 n2 v).
Proof.
  introv ceq1 ceq2.
  unfold seq2kseq2.
  apply implies_cequivc_lam; introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_bot_substc.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_mkc_less;
    [apply cequivc_refl
    |apply cequivc_refl
    |apply cequivc_refl
    |eapply cequivc_mkc_less;
      [apply cequivc_refl
      |auto
      |apply sp_implies_cequivc_apply;auto
      |apply cequivc_refl]
    ].
Qed.

Lemma implies_cequivc_natk2nat {o} :
  forall lib (t1 t2 : @CTerm o),
    cequivc lib t1 t2
    -> cequivc lib (natk2nat t1) (natk2nat t2).
Proof.
  introv ceq.
  unfold natk2nat.
  apply cequivc_mkc_fun;[|apply cequivc_refl].
  apply cequivc_mkc_natk; auto.
Qed.

Lemma cequivc_lsubstc_mk_plus1 {o} :
  forall lib n (w : @wf_term o (mk_plus1 (mk_var n))) m a (sub : @CSub o) n k s t c,
    m <> n
    -> !LIn n (dom_csub sub)
    -> cequivc
         lib
         (lsubstc (mk_plus1 (mk_var n)) w
                  ((m, a) :: snoc (snoc sub (n, mkc_nat k)) (s, t)) c)
         (mkc_nat (S k)).
Proof.
  introv d1 ni.
  unfold cequivc; simpl.
  unfold csubst, mk_plus1.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  boolvar; simpl; tcsp.
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_snoc.
  rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto).
  boolvar; tcsp; fold_terms.
  apply reduces_to_implies_cequiv;
    [rw @isprogram_eq; apply isprog_add_implies;eauto 3 with slow|].
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl; auto.
  unfold mk_nat, mk_integer.

  assert (1%Z = Z.of_nat 1) as e by (simpl; auto).
  rw e.
  rw <- @Znat.Nat2Z.inj_add.
  rw plus_comm; auto.
Qed.

Lemma implies_cequivc_mkc_image {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib a c
    -> cequivc lib b d
    -> cequivc lib (mkc_image a b) (mkc_image c d).
Proof.
  introv ceq1 ceq2.
  destruct_cterms; allunfold @cequivc; allsimpl.
  destruct ceq1, ceq2.
  split; repeat prove_approx; eauto 3 with slow.
Qed.

Lemma implies_cequivc_mkc_squash {o} :
  forall lib (t u : @CTerm o),
    cequivc lib t u
    -> cequivc lib (mkc_squash t) (mkc_squash u).
Proof.
  introv c.
  unfold mkc_squash.
  apply implies_cequivc_mkc_image; auto.
Qed.

Lemma cequivc_lsubstc_mk_plus1_sp1 {o} :
  forall lib n w (sub : @CSub o) k c,
    !LIn n (dom_csub sub)
    -> cequivc
         lib
         (lsubstc (mk_plus1 (mk_var n)) w
                  (snoc sub (n, mkc_nat k)) c)
         (mkc_nat (S k)).
Proof.
  introv ni.
  unfold cequivc; simpl.
  unfold csubst, mk_plus1.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  boolvar; simpl; tcsp.
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_snoc.
  rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto).
  boolvar; tcsp; fold_terms.
  apply reduces_to_implies_cequiv;
    [rw @isprogram_eq; apply isprog_add_implies;eauto 3 with slow|].
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl; auto.
  unfold mk_nat, mk_integer.

  assert (1%Z = Z.of_nat 1) as e by (simpl; auto).
  rw e.
  rw <- @Znat.Nat2Z.inj_add.
  rw plus_comm; auto.
Qed.

Lemma implies_cequiv_mk_add {o} :
  forall lib (a b c d : @NTerm o),
    cequiv lib a c
    -> cequiv lib b d
    -> cequiv lib (mk_add a b) (mk_add c d).
Proof.
  introv ceq1 ceq2.
  destruct ceq1, ceq2.
  unfold mk_add.
  applydup @approx_relates_only_progs in a0.
  applydup @approx_relates_only_progs in a2.
  repnd.
  split; repeat prove_approx; eauto 3 with slow.
Qed.

Lemma implies_cequivc_mkc_add {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib a c
    -> cequivc lib b d
    -> cequivc lib (mkc_add a b) (mkc_add c d).
Proof.
  introv ceq1 ceq2.
  destruct_cterms; allunfold @cequivc; allsimpl.
  apply implies_cequiv_mk_add; auto.
Qed.

Lemma cequivc_lsubstc_mk_plus1_sp2 {o} :
  forall lib n w (sub : @CSub o) t k c,
    !LIn n (dom_csub sub)
    -> cequivc lib t (mkc_nat k)
    -> cequivc
         lib
         (lsubstc (mk_plus1 (mk_var n)) w
                  (snoc sub (n,t)) c)
         (mkc_nat (S k)).
Proof.
  introv ni ceq.
  allunfold @cequivc; simpl.
  unfold csubst, mk_plus1.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  boolvar; simpl; tcsp.
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_snoc.
  rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto).
  boolvar; tcsp; fold_terms.
  eapply cequiv_trans;
    [apply implies_cequiv_mk_add;
      [exact ceq
      |apply cequiv_refl;eauto 3 with slow]
    |].

  apply reduces_to_implies_cequiv;
    [rw @isprogram_eq; apply isprog_add_implies;eauto 3 with slow|].
  apply reduces_to_if_step; csunf; simpl; dcwf h; simpl; auto.
  unfold mk_nat, mk_integer.

  assert (1%Z = Z.of_nat 1) as e by (simpl; auto).
  rw e.
  rw <- @Znat.Nat2Z.inj_add.
  rw plus_comm; auto.
Qed.

Lemma implies_approx_lam {o} :
  forall lib v (t1 t2 : @NTerm o),
    isprog_vars [v] t1
    -> isprog_vars [v] t2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v u) (subst t2 v u))
    -> approx lib (mk_lam v t1) (mk_lam v t2).
Proof.
  introv isp1 isp2 imp.

  constructor.
  unfold close_comput; dands;
  try (apply isprogram_lam);
  eauto 3 with slow.

  + introv comp.
    apply computes_to_value_isvalue_eq in comp;
      try (apply isvalue_mk_lam); eauto 3 with slow.
    unfold mk_lam in comp; ginv; fold_terms.
    exists [bterm [v] t2]; fold_terms.
    dands.
    { apply computes_to_value_isvalue_refl;
      try (apply isvalue_mk_lam); eauto 3 with slow. }

    unfold lblift; simpl; dands; auto.
    introv ltn.
    destruct n; try omega; clear ltn.
    unfold selectbt; simpl.
    unfold blift.
    exists [v] t1 t2; dands; eauto 3 with slow.
    apply clearbots_olift.
    apply cl_olift_implies_olift; eauto 3 with slow.

    pose proof (cl_olift_iff_pv_olift (approx lib) t1 t2 [v]) as xx.
    repeat (autodimp xx hyp).
    apply xx; clear xx.
    introv ps e.
    destruct sub as [|p s]; allsimpl; ginv.
    destruct s; ginv.
    destruct p as [z u]; allsimpl.
    allrw @fold_subst.
    allrw @prog_sub_cons; repnd.
    pose proof (imp u) as h; clear imp; allsimpl.
    destruct h; eauto 3 with slow.

  + introv comp.
    apply can_doesnt_raise_an_exception in comp; sp.
Qed.

Lemma implies_cequiv_lam {o} :
  forall lib v (t1 t2 : @NTerm o),
    isprog_vars [v] t1
    -> isprog_vars [v] t2
    -> (forall u : NTerm, isprog u -> cequiv lib (subst t1 v u) (subst t2 v u))
    -> cequiv lib (mk_lam v t1) (mk_lam v t2).
Proof.
  introv isp1 isp2 imp.
  split.
  - apply implies_approx_lam; auto.
  - apply implies_approx_lam; auto.
    introv ispu.
    apply cequiv_sym; auto.
Qed.

Lemma lsubst_aux_get_cterm {o} :
  forall (t : @CTerm o) sub,
    lsubst_aux (get_cterm t) sub = get_cterm t.
Proof.
  introv.
  apply lsubst_aux_trivial_cl_term2; eauto 3 with slow.
Qed.

Hint Resolve isprogram_mk_nat : slow.


Lemma cequivc_nat_implies_computes_to_valc {o} :
  forall lib (t : @CTerm o) (n : nat),
    cequivc lib t (mkc_nat n)
    -> computes_to_valc lib t (mkc_nat n).
Proof.
  introv ceq.
  pose proof (cequivc_integer lib (mkc_nat n) t (Z.of_nat n)) as h.
  repeat (autodimp h hyp); eauto 3 with slow.

  { apply computes_to_valc_refl; eauto 3 with slow. }

  apply cequivc_sym; auto.
Qed.

Lemma computes_to_value_mk_int_eq {o} :
  forall lib (a b c d v : @NTerm o),
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> computes_to_value lib (mk_int_eq a b c d) v
    -> {pk1 : param_kind
        & {pk2 : param_kind
        & reduces_to lib a (pk2term pk1)
        # reduces_to lib b (pk2term pk2)
        # ((pk1 = pk2 # computes_to_value lib c v)
           [+]
           (pk1 <> pk2 # computes_to_value lib d v)
          )}}.
Proof.
  introv wfa wfb wfc wfd hv.
  unfold computes_to_value in hv; repnd.
  unfold reduces_to in hv0; exrepnd.
  pose proof (computes_to_val_like_in_max_k_steps_comp_implies
                lib k CompOpEq a b c d v) as h.
  repeat (autodimp h hyp).
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto with slow. }

  repndors; exrepnd; repndors; exrepnd; ginv.

  - allunfold @spcan; fold_terms.
    allunfold @computes_to_can_in_max_k_steps; repnd.
    exists pk1 pk2; dands; eauto with slow.
    boolvar; subst.
    + left; dands; auto.
      allunfold @computes_to_val_like_in_max_k_steps; repnd.
      unfold computes_to_value; dands; auto.
      exists (k - (k1 + k2 + 1)); auto.
    + right; dands; auto.
      allunfold @computes_to_val_like_in_max_k_steps; repnd.
      unfold computes_to_value; dands; auto.
      exists (k - (k1 + k2 + 1)); auto.

  - provefalse; subst; inversion hv; allsimpl; tcsp.

  - provefalse; subst; inversion hv; allsimpl; tcsp.
Qed.

Lemma approx_pk2term_implies_reduces_to {o} :
  forall lib pk (t : @NTerm o),
    approx lib (pk2term pk) t
    -> reduces_to lib t (pk2term pk).
Proof.
  introv ap.
  destruct ap as [c].
  unfold close_comput in c; repnd.
  destruct pk; allsimpl.

  - pose proof (c2 (NTok s) []) as h; fold_terms.
    autodimp h hyp.
    { apply computes_to_value_isvalue_refl; eauto with slow. }
    exrepnd.
    unfold lblift in h0; allsimpl; repnd; cpx; fold_terms.
    unfold computes_to_value in h1; repnd; auto.

  - pose proof (c2 (NUTok g) []) as h; fold_terms.
    autodimp h hyp.
    { apply computes_to_value_isvalue_refl; eauto with slow. }
    exrepnd.
    unfold lblift in h0; allsimpl; repnd; cpx; fold_terms.
    unfold computes_to_value in h1; repnd; auto.

  - pose proof (c2 (Nint z) []) as h; fold_terms.
    autodimp h hyp.
    { apply computes_to_value_isvalue_refl; eauto with slow. }
    exrepnd.
    unfold lblift in h0; allsimpl; repnd; cpx; fold_terms.
    unfold computes_to_value in h1; repnd; auto.

  - pose proof (c2 (Ncseq c4) []) as h; fold_terms.
    autodimp h hyp.
    { apply computes_to_value_isvalue_refl; eauto with slow. }
    exrepnd.
    unfold lblift in h0; allsimpl; repnd; cpx; fold_terms.
    unfold computes_to_value in h1; repnd; auto.
Qed.

Lemma computes_to_exception_mk_int_eq {o} :
  forall lib (a b c d : @NTerm o) n e,
    wf_term a
    -> wf_term b
    -> wf_term c
    -> wf_term d
    -> computes_to_exception lib n (mk_int_eq a b c d) e
    -> {pk1 : param_kind
        & {pk2 : param_kind
        & reduces_to lib a (pk2term pk1)
        # reduces_to lib b (pk2term pk2)
        # ((pk1 = pk2 # computes_to_exception lib n c e)
           [+]
           (pk2 <> pk1 # computes_to_exception lib n d e)
          )}}
       [+] computes_to_exception lib n a e
       [+] {pk : param_kind
            & reduces_to lib a (pk2term pk)
            # computes_to_exception lib n b e}.
Proof.
  introv wfa wfb wfc wfd comp.
  unfold computes_to_exception, reduces_to in comp; exrepnd.
  pose proof (computes_to_val_like_in_max_k_steps_comp_implies
                lib k CompOpEq a b c d (mk_exception n e)) as h.
  repeat (autodimp h hyp).
  { unfold computes_to_val_like_in_max_k_steps; dands; eauto 3 with slow. }

  repndors; exrepnd; repndors; exrepnd; ginv.

  - left.
    allunfold @computes_to_can_in_max_k_steps; repnd.
    allunfold @spcan; fold_terms.
    exists pk1 pk2; dands; eauto with slow.
    boolvar;[left|right]; dands; auto;
    allunfold @computes_to_val_like_in_max_k_steps; repnd;
    exists (k - (k1 + k2 + 1)); auto.

  - right; left.
    exists k1; auto.

  - right; right; allsimpl.
    exists pk; dands; auto.
    + allunfold @computes_to_can_in_max_k_steps; repnd.
      unfold computes_to_can; dands; eauto with slow.
    + exists k2; auto.
Qed.

Lemma approx_open_mk_int_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    approx_open lib a1 a2
    -> approx_open lib b1 b2
    -> approx_open lib c1 c2
    -> approx_open lib d1 d2
    -> approx_open lib (mk_int_eq a1 b1 c1 d1) (mk_int_eq a2 b2 c2 d2).
Proof.
  introv apro1 apro2 apro3 apro4.

  allrw <- @approx_open_simpler_equiv.
  allunfold @simpl_olift; repnd.
  allrw @nt_wf_eq.
  dands; try (apply wf_int_eq; auto).
  introv prs ispl1 ispl2.

  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow).
  repeat (rw @cl_lsubst_lsubst_aux in ispl1; eauto 3 with slow).
  repeat (rw @cl_lsubst_lsubst_aux in ispl2; eauto 3 with slow).
  allsimpl; fold_terms; allrw @sub_filter_nil_r.

  allrw @isprogram_eq.
  allrw @isprog_inteq; repnd.

  pose proof (apro1 sub) as h1.
  repeat (rw @cl_lsubst_lsubst_aux in h1; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h1 hyp);[].

  pose proof (apro2 sub) as h2.
  repeat (rw @cl_lsubst_lsubst_aux in h2; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h2 hyp);[].

  pose proof (apro3 sub) as h3.
  repeat (rw @cl_lsubst_lsubst_aux in h3; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h3 hyp);[].

  pose proof (apro4 sub) as h4.
  repeat (rw @cl_lsubst_lsubst_aux in h4; eauto 3 with slow).
  allrw @isprogram_eq.
  repeat (autodimp h4 hyp);[].

  constructor.
  unfold close_comput.
  allrw @isprogram_eq; allrw @isprog_inteq; dands; auto;[|].

  - introv comp.
    apply computes_to_value_mk_int_eq in comp; exrepnd;
    try (apply lsubst_aux_preserves_wf_term2; eauto 3 with slow);[].

    eapply approx_comput_functionality_left in h1;[|exact comp0].
    eapply approx_comput_functionality_left in h2;[|exact comp2].
    allapply @approx_pk2term_implies_reduces_to.

    repndors; repnd; subst;[|].

    + eapply approx_canonical_form in h3;[|exact comp1].
      destruct h3 as [tr_subterms apr]; repnd.
      exists tr_subterms; dands; try (apply clearbot_relbt2); auto.
      allunfold @computes_to_value; repnd; dands; tcsp.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
      eapply reduces_to_if_split2;
        [csunf; simpl; allrw @pk2term_eq; dcwf h;
         allsimpl; unfold compute_step_comp; simpl;
         allrw @get_param_from_cop_pk2can; auto;
         allrw @co_wf_pk2can;ginv|];[].
      boolvar;tcsp;try omega.

    + eapply approx_canonical_form in h4;[|exact comp1].
      destruct h4 as [tr_subterms apr]; repnd.
      exists tr_subterms; dands; try (apply clearbot_relbt2); auto.
      allunfold @computes_to_value; repnd; dands; tcsp.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
      eapply reduces_to_if_split2;
        [csunf; simpl; allrw @pk2term_eq; dcwf h;
         allsimpl; unfold compute_step_comp; simpl;
         allrw @get_param_from_cop_pk2can; auto;
         allrw @co_wf_pk2can;ginv|];[].
      boolvar;tcsp;try omega.

  - introv comp.
    apply computes_to_exception_mk_int_eq in comp; repndors; exrepnd;
    try (apply lsubst_aux_preserves_wf_term2; eauto 3 with slow);[|idtac|].

    + eapply approx_comput_functionality_left in h1;[|exact comp0].
      eapply approx_comput_functionality_left in h2;[|exact comp2].
      allapply @approx_pk2term_implies_reduces_to.

      repndors; repnd;[|].

      * apply computes_to_exception_implies_approx in comp1; eauto 3 with slow;[]; repnd.
        eapply approx_trans in h3;[|exact comp4].
        apply approx_exception in h3; exrepnd.
        exists x c; dands; tcsp.
        allunfold @computes_to_exception.
        eapply reduces_to_trans;
          [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
        eapply reduces_to_if_split2;
          [csunf; simpl; allrw @pk2term_eq; dcwf h;
           allsimpl; unfold compute_step_comp; simpl;
           allrw @get_param_from_cop_pk2can; auto;
           allrw @co_wf_pk2can;ginv|];[].
        boolvar;tcsp;try omega.

      * apply computes_to_exception_implies_approx in comp1; eauto 3 with slow;[]; repnd.
        eapply approx_trans in h4;[|exact comp4].
        apply approx_exception in h4; exrepnd.
        exists x c; dands; tcsp.
        allunfold @computes_to_exception.
        eapply reduces_to_trans;
          [apply reduce_to_prinargs_comp2;[exact h1|idtac|]; eauto 3 with slow|];[].
        eapply reduces_to_if_split2;
          [csunf; simpl; allrw @pk2term_eq; dcwf h;
           allsimpl; unfold compute_step_comp; simpl;
           allrw @get_param_from_cop_pk2can; auto;
           allrw @co_wf_pk2can;ginv|];[].
        boolvar;tcsp;try omega.

    + apply computes_to_exception_implies_approx in comp; eauto 3 with slow;[]; repnd.
      eapply approx_trans in h1;[|exact comp0].
      apply approx_exception in h1; exrepnd.
      exists x c; dands; tcsp;[].
      allunfold @computes_to_exception.
      unfold mk_less, nobnd.
      eapply reduces_to_trans;[eapply reduces_to_prinarg;exact h0|].
      apply reduces_to_if_step.
      csunf; simpl; auto.

    + apply computes_to_exception_implies_approx in comp0; eauto 3 with slow;[]; repnd.
      eapply approx_trans in h2;[|exact comp2].
      apply approx_exception in h2; exrepnd.

      exists x c; dands; tcsp;[].
      apply reduces_to_implies_approx1 in comp1; eauto 3 with slow;[].
      eapply approx_trans in h1;[|exact comp1].
      apply approx_pk2term_implies_reduces_to in h1.
      allunfold @computes_to_exception.
      eapply reduces_to_trans;
        [apply reduce_to_prinargs_comp2;[exact h1|idtac|exact h0] |]; eauto 3 with slow.
      apply reduces_to_if_step.
      csunf; simpl.
      allrw @pk2term_eq.
      dcwf h; try (complete (allrw @co_wf_pk2can;ginv));[].
      simpl; auto.
Qed.

Lemma approx_mk_int_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    approx lib a1 a2
    -> approx lib b1 b2
    -> approx lib c1 c2
    -> approx lib d1 d2
    -> approx lib (mk_int_eq a1 b1 c1 d1) (mk_int_eq a2 b2 c2 d2).
Proof.
  introv apra aprb aprc aprd.

  applydup @approx_isprog in apra.
  applydup @approx_isprog in aprb.
  applydup @approx_isprog in aprc.
  applydup @approx_isprog in aprd.
  repnd.

  apply approx_open_approx; allrw @isprogram_eq; try (apply isprog_inteq_implies); auto.
  apply approx_open_mk_int_eq; apply approx_implies_approx_open; auto.
Qed.

Lemma cequiv_mk_int_eq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @NTerm o),
    cequiv lib a1 a2
    -> cequiv lib b1 b2
    -> cequiv lib c1 c2
    -> cequiv lib d1 d2
    -> cequiv lib (mk_int_eq a1 b1 c1 d1) (mk_int_eq a2 b2 c2 d2).
Proof.
  introv ceqa ceqb ceqc ceqd.
  allunfold @cequiv; repnd; dands; apply approx_mk_int_eq; auto.
Qed.

Lemma cequivc_mkc_inteq {o} :
  forall lib (a1 a2 b1 b2 c1 c2 d1 d2 : @CTerm o),
    cequivc lib a1 a2
    -> cequivc lib b1 b2
    -> cequivc lib c1 c2
    -> cequivc lib d1 d2
    -> cequivc lib (mkc_inteq a1 b1 c1 d1) (mkc_inteq a2 b2 c2 d2).
Proof.
  introv ceqa ceqb ceqc ceqd.
  destruct_cterms.
  allunfold @cequivc; allsimpl.
  apply cequiv_mk_int_eq; auto.
Qed.

Lemma isprog_vars_mk_int_eq {p} :
  forall (a b c d : @NTerm p) vs,
    isprog_vars vs (mk_int_eq a b c d)
    <=> (isprog_vars vs a
         # isprog_vars vs b
         # isprog_vars vs c
         # isprog_vars vs d).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l).
  repeat (rw <- @wf_term_eq).
  allrw <- @wf_inteq_iff; split; sp.
Qed.

Lemma isprogram_mk_int_eq {p} :
  forall (a b c d : @NTerm p),
    isprogram (mk_int_eq a b c d)
    <=> (isprogram a
         # isprogram b
         # isprogram c
         # isprogram d).
Proof.
  introv.
  pose proof (isprog_vars_mk_int_eq a b c d []) as h.
  allrw <- @isprog_vars_nil_iff_isprog.
  allrw @isprogram_eq; auto.
Qed.

Lemma approx_bts_refl {o} :
  forall lib (bs : list (@BTerm o)),
    (forall b, LIn b bs -> bt_wf b)
    -> approx_bts lib bs bs.
Proof.
  introv imp.
  unfold approx_bts, lblift.
  dands; auto.
  introv i.
  unfold blift.
  remember (selectbt bs n) as b.
  destruct b as [l t].
  exists l t t; dands; eauto 3 with slow.
  apply approx_open_refl.
  pose proof (imp (bterm l t)) as h.
  autodimp h hyp.
  { rw Heqb; apply selectbt_in; auto. }
  allrw @bt_wf_iff; auto.
Qed.

Lemma approx_inteq_less_swap1 {o} :
  forall lib (t : @NTerm o) n m u v w,
    m <= n
    -> isprog t
    -> isprog u
    -> isprog v
    -> isprog w
    -> approx
         lib
         (mk_int_eq t (mk_nat n) u (mk_less t (mk_nat m) v w))
         (mk_less t (mk_nat m) v (mk_int_eq t (mk_nat n) u w)).
Proof.
  introv ltm ispt ispu ispv ispw.
  constructor.
  unfold close_comput.
  dands; auto;
    repeat (try (apply isprogram_mk_int_eq; dands; eauto 3 with slow);
            try (apply isprogram_mk_less; dands; eauto 3 with slow)).

  - introv comp.
    apply computes_to_value_mk_int_eq in comp;
      try (apply wf_less); eauto 3 with slow.
    exrepnd.
    apply reduces_to_if_isvalue_like in comp2; eauto 3 with slow.
    destruct pk2; allsimpl; ginv.
    unfold mk_nat in comp2; ginv; fold_terms.
    repndors; repnd; subst.

    + exists tl_subterms.
      dands; auto.

      * allunfold @computes_to_value; repnd; dands; auto.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; try omega.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; tcsp.

      * apply clearbot_relbt2.
        fold (approx_open lib).
        fold (approx_bts lib).
        apply approx_bts_refl.
        allunfold @computes_to_value; repnd.
        apply compute_max_steps_eauto2 in comp1.
        apply isprogram_ot_iff in comp1; repnd.
        introv j; apply comp1 in j; eauto 3 with slow.

    + apply computes_to_value_mk_less in comp1; eauto 3 with slow.
      exrepnd.
      apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow.
      unfold mk_nat in comp4; ginv; fold_terms.
      eapply reduces_to_eq_val_like in comp0;
        [|exact comp3
         |eauto 3 with slow
         |eauto 3 with slow].
      destruct pk1; allsimpl; ginv.
      repndors; repnd; subst.

      * exists tl_subterms.
        dands; auto.

        { allunfold @computes_to_value; repnd; dands; auto.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar; try omega; auto. }

        { apply clearbot_relbt2.
          fold (approx_open lib).
          fold (approx_bts lib).
          apply approx_bts_refl.
          allunfold @computes_to_value; repnd.
          apply compute_max_steps_eauto2 in comp1.
          apply isprogram_ot_iff in comp1; repnd.
          introv j; apply comp1 in j; eauto 3 with slow. }

      * exists tl_subterms.
        dands; auto.

        { allunfold @computes_to_value; repnd; dands; auto.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar; try omega; auto.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar;tcsp. }

        { apply clearbot_relbt2.
          fold (approx_open lib).
          fold (approx_bts lib).
          apply approx_bts_refl.
          allunfold @computes_to_value; repnd.
          apply compute_max_steps_eauto2 in comp1.
          apply isprogram_ot_iff in comp1; repnd.
          introv j; apply comp1 in j; eauto 3 with slow. }

  - introv comp.
    apply computes_to_exception_mk_int_eq in comp;
      try (apply wf_less); eauto 3 with slow.
    repndors; exrepnd.

    + apply reduces_to_if_isvalue_like in comp2; eauto 3 with slow.
      destruct pk2; allsimpl; ginv.
      unfold mk_nat in comp2; ginv; fold_terms.
      repndors; repnd; subst.

      * exists a e.
        applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
        dands; try (complete (left; apply approx_refl; eauto with slow)).

        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; try omega.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; tcsp.

      * apply computes_to_exception_mk_less in comp1; eauto 3 with slow.
        repndors; exrepnd.

        { apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow.
          unfold mk_nat in comp4; ginv; fold_terms.
          eapply reduces_to_eq_val_like in comp0;
            [|exact comp3
             |eauto 3 with slow
             |eauto 3 with slow].
          destruct pk1; allsimpl; ginv.
          repndors; repnd; subst.

          - exists a e.
            applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
            dands; try (complete (left; apply approx_refl; eauto with slow)).

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; auto.

          - exists a e.
            applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
            dands; try (complete (left; apply approx_refl; eauto with slow)).

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; auto.

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; ginv; tcsp.
        }

        { exists a e.
          applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
          dands; try (complete (left; apply approx_refl; eauto with slow)).

          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp1|].
          apply reduces_to_if_step; csunf; simpl; auto.
        }

        { apply can_doesnt_raise_an_exception in comp3; sp. }

    + exists a e.
      applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
      dands; try (complete (left; apply approx_refl; eauto with slow)).

      eapply reduces_to_trans;
        [apply reduces_to_prinarg;exact comp|].
      apply reduces_to_if_step; csunf; simpl; auto.

    + apply can_doesnt_raise_an_exception in comp0; sp.
Qed.

Lemma approx_less_inteq_swap1 {o} :
  forall lib (t : @NTerm o) n m u v w,
    m <= n
    -> isprog t
    -> isprog u
    -> isprog v
    -> isprog w
    -> approx
         lib
         (mk_less t (mk_nat m) v (mk_int_eq t (mk_nat n) u w))
         (mk_int_eq t (mk_nat n) u (mk_less t (mk_nat m) v w)).
Proof.
  introv ltm ispt ispu ispv ispw.
  constructor.
  unfold close_comput.
  dands; auto;
    repeat (try (apply isprogram_mk_int_eq; dands; eauto 3 with slow);
            try (apply isprogram_mk_less; dands; eauto 3 with slow)).

  - introv comp.
    apply computes_to_value_mk_less in comp;
      try (apply wf_less); eauto 3 with slow.
    exrepnd.
    apply reduces_to_if_isvalue_like in comp2; eauto 3 with slow.
    unfold mk_nat in comp2; ginv; fold_terms.
    repndors; repnd; subst.

    + exists tl_subterms.
      dands; auto.

      * allunfold @computes_to_value; repnd; dands; auto.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; ginv; try omega.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; tcsp; try omega.

      * apply clearbot_relbt2.
        fold (approx_open lib).
        fold (approx_bts lib).
        apply approx_bts_refl.
        allunfold @computes_to_value; repnd.
        apply compute_max_steps_eauto2 in comp1.
        apply isprogram_ot_iff in comp1; repnd.
        introv j; apply comp1 in j; eauto 3 with slow.

    + apply computes_to_value_mk_int_eq in comp1; eauto 3 with slow.
      exrepnd.
      apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow.
      destruct pk2; allsimpl; ginv.
      unfold mk_nat in comp4; ginv; fold_terms.
      eapply reduces_to_eq_val_like in comp0;
        [|exact comp3
         |eauto 3 with slow
         |eauto 3 with slow].
      destruct pk1; allsimpl; ginv.
      repndors; repnd; subst; ginv.

      * exists tl_subterms.
        dands; auto.

        { allunfold @computes_to_value; repnd; dands; auto.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar; try omega; tcsp. }

        { apply clearbot_relbt2.
          fold (approx_open lib).
          fold (approx_bts lib).
          apply approx_bts_refl.
          allunfold @computes_to_value; repnd.
          apply compute_max_steps_eauto2 in comp1.
          apply isprogram_ot_iff in comp1; repnd.
          introv j; apply comp1 in j; eauto 3 with slow. }

      * exists tl_subterms.
        dands; auto.

        { allunfold @computes_to_value; repnd; dands; auto.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar; ginv; try omega; tcsp.
          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp3|].
          eapply reduces_to_if_split2;
            [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
          boolvar;tcsp;try omega. }

        { apply clearbot_relbt2.
          fold (approx_open lib).
          fold (approx_bts lib).
          apply approx_bts_refl.
          allunfold @computes_to_value; repnd.
          apply compute_max_steps_eauto2 in comp1.
          apply isprogram_ot_iff in comp1; repnd.
          introv j; apply comp1 in j; eauto 3 with slow. }

  - introv comp.
    apply computes_to_exception_mk_less in comp;
      try (apply wf_less); eauto 3 with slow.
    repndors; exrepnd.

    + apply reduces_to_if_isvalue_like in comp2; eauto 3 with slow.
      unfold mk_nat in comp2; ginv; fold_terms.
      repndors; repnd; subst.

      * exists a e.
        applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
        dands; try (complete (left; apply approx_refl; eauto with slow)).

        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; ginv; try omega.
        eapply reduces_to_trans;
          [apply reduces_to_prinarg;exact comp0|].
        eapply reduces_to_if_split2;
          [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
        boolvar; tcsp; try omega.

      * apply computes_to_exception_mk_int_eq in comp1; eauto 3 with slow.
        repndors; exrepnd.

        { apply reduces_to_if_isvalue_like in comp4; eauto 3 with slow.
          destruct pk2; allsimpl; ginv.
          unfold mk_nat in comp4; ginv; fold_terms.
          eapply reduces_to_eq_val_like in comp0;
            [|exact comp3
             |eauto 3 with slow
             |eauto 3 with slow].
          destruct pk1; allsimpl; ginv.
          repndors; repnd; subst; ginv.

          - exists a e.
            applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
            dands; try (complete (left; apply approx_refl; eauto with slow)).

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; tcsp.

          - exists a e.
            applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
            dands; try (complete (left; apply approx_refl; eauto with slow)).

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; tcsp.

            eapply reduces_to_trans;
              [apply reduces_to_prinarg;exact comp3|].
            eapply reduces_to_if_split2;
              [csunf;simpl;dcwf h;simpl;unfold compute_step_comp;simpl;auto|].
            boolvar; try omega; ginv; tcsp.
        }

        { exists a e.
          applydup @preserve_program_exc2 in comp1; eauto 3 with slow; repnd.
          dands; try (complete (left; apply approx_refl; eauto with slow)).

          eapply reduces_to_trans;
            [apply reduces_to_prinarg;exact comp1|].
          apply reduces_to_if_step; csunf; simpl; auto.
        }

        { apply can_doesnt_raise_an_exception in comp3; sp. }

    + exists a e.
      applydup @preserve_program_exc2 in comp; eauto 3 with slow; repnd.
      dands; try (complete (left; apply approx_refl; eauto with slow)).

      eapply reduces_to_trans;
        [apply reduces_to_prinarg;exact comp|].
      apply reduces_to_if_step; csunf; simpl; auto.

    + apply can_doesnt_raise_an_exception in comp0; sp.
Qed.

Lemma cequivc_inteq_less_swap1 {o} :
  forall lib (t : @CTerm o) n m u v w,
    m <= n
    -> cequivc
         lib
         (mkc_inteq t (mkc_nat n) u (mkc_less t (mkc_nat m) v w))
         (mkc_less t (mkc_nat m) v (mkc_inteq t (mkc_nat n) u w)).
Proof.
  introv ltm.
  destruct_cterms.
  unfold cequivc; simpl.
  split.
  - apply approx_inteq_less_swap1; auto.
  - apply approx_less_inteq_swap1; auto.
Qed.

Definition update_seq {o} (s : @CTerm o) (n m : nat) (v : NVar) :=
  mkc_lam
    v
    (mkcv_inteq
       [v]
       (mkc_var v)
       (mk_cv [v] (mkc_nat n))
       (mk_cv [v] (mkc_nat m))
       (mkcv_apply [v] (mk_cv [v] s) (mkc_var v))).

Definition update_seq_nout {o} (s : @CTerm o) (n : nat) (u : CTerm) (v : NVar) :=
  mkc_lam
    v
    (mkcv_inteq
       [v]
       (mkc_var v)
       (mk_cv [v] (mkc_nat n))
       (mk_cv [v] u)
       (mkcv_apply [v] (mk_cv [v] s) (mkc_var v))).

Lemma cequivc_lsubstc_mk_update_seq_sp0 {o} :
  forall lib s n m v w (sub : @CSub o) a b k t c,
    n <> m
    -> s <> n
    -> s <> m
    -> n <> v
    -> s <> v
    -> m <> v
    -> !LIn n (dom_csub sub)
    -> !LIn s (dom_csub sub)
    -> cequivc lib a b
    -> cequivc
         lib
         (lsubstc (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v) w
                  ((m,a) :: snoc (snoc sub (n,mkc_nat k)) (s,t)) c)
         (update_seq_nout t k b v).
Proof.
  introv d1 d2 d3 d4 d5 d6 ni1 ni2 ceq.
  allunfold @cequivc; simpl.
  unfold csubst, mk_update_seq.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  allrw memvar_singleton.

  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_find_snoc.
  repeat (rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto);[]).
  repeat (boolvar; simpl; tcsp; fold_terms;[]).

  apply implies_cequiv_lam;
    try (apply isprog_vars_mk_int_eq; dands);
    try (apply isprog_vars_apply_implies);
    try (apply mk_cv_pf);
    eauto 2 with slow.

  introv ispu.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[]).
  simpl; boolvar; tcsp.
  allrw @lsubst_aux_get_cterm.

  apply cequiv_mk_int_eq;
    [apply cequiv_refl;fold_terms;eauto 3 with slow
    |apply cequiv_refl;fold_terms;eauto 3 with slow
    |
    |apply cequiv_refl;apply isprogram_apply;eauto 3 with slow].

  auto.
Qed.

Lemma cequivc_lsubstc_mk_update_seq_sp1 {o} :
  forall lib s n m v w (sub : @CSub o) a k j t c,
    n <> m
    -> s <> n
    -> s <> m
    -> n <> v
    -> s <> v
    -> m <> v
    -> !LIn n (dom_csub sub)
    -> !LIn s (dom_csub sub)
    -> computes_to_valc lib a (mkc_nat j)
    -> cequivc
         lib
         (lsubstc (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v) w
                  ((m,a) :: snoc (snoc sub (n,mkc_nat k)) (s,t)) c)
         (update_seq t k j v).
Proof.
  introv d1 d2 d3 d4 d5 d6 ni1 ni2 comp.
  unfold cequivc; simpl.
  unfold csubst, mk_update_seq.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  allrw memvar_singleton.

  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_find_snoc.
  repeat (rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto);[]).
  repeat (boolvar; simpl; tcsp; fold_terms;[]).

  apply implies_cequiv_lam;
    try (apply isprog_vars_mk_int_eq; dands);
    try (apply isprog_vars_apply_implies);
    try (apply mk_cv_pf);
    eauto 2 with slow.

  introv ispu.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[]).
  simpl; boolvar; tcsp.
  allrw @lsubst_aux_get_cterm.

  apply cequiv_mk_int_eq;
    [apply cequiv_refl;fold_terms;eauto 3 with slow
    |apply cequiv_refl;fold_terms;eauto 3 with slow
    |
    |apply cequiv_refl;apply isprogram_apply;eauto 3 with slow].

  apply reduces_to_implies_cequiv; eauto 3 with slow.
Qed.

Lemma cequivc_lsubstc_mk_update_seq_sp2 {o} :
  forall lib s n m v w (sub : @CSub o) a k j t u c,
    n <> m
    -> s <> n
    -> s <> m
    -> n <> v
    -> s <> v
    -> m <> v
    -> !LIn n (dom_csub sub)
    -> !LIn s (dom_csub sub)
    -> computes_to_valc lib a (mkc_nat j)
    -> computes_to_valc lib u (mkc_nat k)
    -> cequivc
         lib
         (lsubstc (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v) w
                  ((m,a) :: snoc (snoc sub (n,u)) (s,t)) c)
         (update_seq t k j v).
Proof.
  introv d1 d2 d3 d4 d5 d6 ni1 ni2 comp1 comp2.
  unfold cequivc; simpl.
  unfold csubst, mk_update_seq.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  allrw memvar_singleton.

  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_find_snoc.
  repeat (rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto);[]).
  repeat (boolvar; simpl; tcsp; fold_terms;[]).

  apply implies_cequiv_lam;
    try (apply isprog_vars_mk_int_eq; dands);
    try (apply isprog_vars_apply_implies);
    try (apply mk_cv_pf);
    eauto 2 with slow.

  introv ispu.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[]).
  simpl; boolvar; tcsp.
  allrw @lsubst_aux_get_cterm.

  allunfold @computes_to_valc.
  allunfold @computes_to_value; repnd.

  apply cequiv_mk_int_eq;
    [apply cequiv_refl;eauto 3 with slow
    |apply reduces_to_implies_cequiv;eauto
    |
    |apply cequiv_refl;apply isprogram_apply;eauto 3 with slow].

  apply reduces_to_implies_cequiv; eauto 3 with slow.
Qed.

Lemma cequivc_lsubstc_mk_update_seq_sp3 {o} :
  forall lib s n m v w (sub : @CSub o) a b k t u c,
    n <> m
    -> s <> n
    -> s <> m
    -> n <> v
    -> s <> v
    -> m <> v
    -> !LIn n (dom_csub sub)
    -> !LIn s (dom_csub sub)
    -> cequivc lib a b
    -> cequivc lib u (mkc_nat k)
    -> cequivc
         lib
         (lsubstc (mk_update_seq (mk_var s) (mk_var n) (mk_var m) v) w
                  ((m,a) :: snoc (snoc sub (n,u)) (s,t)) c)
         (update_seq_nout t k b v).
Proof.
  introv d1 d2 d3 d4 d5 d6 ni1 ni2 comp1 comp2.
  unfold cequivc; simpl.
  unfold csubst, mk_update_seq.
  rw @cl_lsubst_lsubst_aux; eauto 3 with slow; simpl.
  allrw memvar_singleton.

  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_filter_nil_r.
  allrw @csub2sub_snoc.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  repeat (boolvar; simpl; tcsp;[]).
  allrw @sub_find_snoc.
  repeat (rw @sub_find_none_if; auto; try (rw @dom_csub_eq;auto);[]).
  repeat (boolvar; simpl; tcsp; fold_terms;[]).

  apply implies_cequiv_lam;
    try (apply isprog_vars_mk_int_eq; dands);
    try (apply isprog_vars_apply_implies);
    try (apply mk_cv_pf);
    eauto 2 with slow.

  introv ispu.
  unfold subst.
  repeat (rw @cl_lsubst_lsubst_aux; eauto 3 with slow;[]).
  simpl; boolvar; tcsp.
  allrw @lsubst_aux_get_cterm.

  allunfold @cequivc.

  apply cequiv_mk_int_eq;
    [apply cequiv_refl;eauto 3 with slow
    |auto
    |auto
    |apply cequiv_refl;apply isprogram_apply;eauto 3 with slow].
Qed.

Lemma cover_vars_upto_add {o} :
  forall (a b : @NTerm o) sub vs,
    cover_vars_upto (mk_add a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  unfold cover_vars_upto; introv; simpl.
  rw app_nil_r.
  allrw remove_nvars_nil_l.
  rw subvars_app_l; sp.
Qed.

Lemma cover_vars_upto_one {o} :
  forall (sub : @CSub o) vs,
    cover_vars_upto mk_one sub vs.
Proof.
  unfold cover_vars_upto; introv; simpl; auto.
Qed.
Hint Resolve cover_vars_upto_one : slow.

Lemma cover_vars_upto_int_eq {o} :
  forall vs (a b c d : @NTerm o) sub,
    cover_vars_upto (mk_int_eq a b c d) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs
        # cover_vars_upto c sub vs
        # cover_vars_upto d sub vs.
Proof.
  introv.
  unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw subvars_app_l.
  sp.
Qed.

Lemma cequivc_mkc_apply_lam_axiom {o} :
  forall lib (a : @CTerm o),
    cequivc lib (mkc_apply lam_axiom a) mkc_axiom.
Proof.
  introv.
  unfold lam_axiom.
  eapply cequivc_trans;[apply cequivc_beta|].
  autorewrite with slow; auto.
Qed.

Ltac clear_wf_hyps :=
  repeat match goal with
           | [ H : cover_vars _ _ |- _ ] => clear H
           | [ H : wf_term _ |- _ ] => clear H
         end.

Definition seq_normalizable {o} lib (s : @CTerm o) n v :=
  cequivc lib s (seq2kseq s n v).

Lemma cequivc_seq2kseq_twice {o} :
  forall lib (s : @CTerm o) n v,
    cequivc lib (seq2kseq s n v) (seq2kseq (seq2kseq s n v) n v).
Proof.
  introv.
  unfold seq2kseq.

  apply implies_cequivc_lam.
  introv.
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  apply implies_cequivc_mkc_less1.
  introv compu.
  allrw @mkc_zero_eq.
  allrw (@mkc_nat_eq o 0).

  eapply cequivc_trans;[apply cequivc_mkc_less_int|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_int].
  boolvar; auto.

  eapply cequivc_trans;
    [apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_refl]
    ].

  apply Wf_Z.Z_of_nat_complete_inf in l; exrepnd; subst; fold_terms.
  allrw <- @mkc_nat_eq.

  eapply cequivc_trans;[apply cequivc_mkc_less_nat|].
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_nat].

  boolvar; auto.

  eapply cequivc_trans;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact compu]
    |].

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_beta].
  allrw @mkcv_less_substc.
  allrw @mkcv_apply_substc.
  allrw @mkc_var_substc.
  allrw @mkcv_bot_substc.
  allrw @csubst_mk_cv.
  allrw @mkcv_nat_substc.
  allrw @mkcv_zero_substc.

  eapply cequivc_trans;
    [|apply cequivc_sym;apply cequivc_mkc_less;
      [apply computes_to_valc_implies_cequivc;exact compu
      |apply cequivc_refl
      |apply cequivc_refl
      |apply cequivc_mkc_less;
        [apply computes_to_valc_implies_cequivc;exact compu
        |apply cequivc_refl
        |apply cequivc_refl
        |apply cequivc_refl]
      ]
    ].

  allrw @mkc_zero_eq.

  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_nat].
  boolvar; auto; try omega.
  eapply cequivc_trans;[|apply cequivc_sym;apply cequivc_mkc_less_nat].
  boolvar; auto; try omega.

  eapply cequivc_trans;
    [|apply cequivc_sym;apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact compu]
    ].
  auto.
Qed.

Lemma seq_normalizable_seq2kseq {o} :
  forall lib (s : @CTerm o) n v,
    seq_normalizable lib (seq2kseq s n v) n v.
Proof.
  introv.
  apply cequivc_seq2kseq_twice.
Qed.

Lemma implies_cequivc_natk2nout {o} :
  forall lib (t1 t2 : @CTerm o),
    cequivc lib t1 t2
    -> cequivc lib (natk2nout t1) (natk2nout t2).
Proof.
  introv ceq.
  unfold natk2nout.
  apply cequivc_mkc_fun;[|apply cequivc_refl].
  apply cequivc_mkc_natk; auto.
Qed.

Lemma covered_member {o} :
  forall (a b : @NTerm o)s,
    covered (mk_member a b) s <=> (covered a s # covered b s).
Proof.
  introv; unfold covered; simpl; autorewrite with slow.
  allrw subvars_app_l; split; sp.
Qed.
