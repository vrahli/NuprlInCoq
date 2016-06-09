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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export natk2.
Require Export stronger_continuity_rule.
Require Export list. (* !!WTF *)


Definition mod_fun_type_v2 {o} (x : NVar) (T : @NTerm o) : NTerm :=
  mk_function
    mk_tnat
    x
    (mk_fun (mk_natk2T (mk_var x) T) mk_natU).

Lemma wf_term_mod_fun_type_v2 {o} :
  forall v (T : @NTerm o),
    wf_term (mod_fun_type_v2 v T) <=> wf_term T.
Proof.
  introv.
  unfold mod_fun_type_v2.
  rw <- @wf_function_iff.
  rw @wf_fun_iff.
  rw @wf_term_mk_natk2T.
  split; intro k; repnd; dands; eauto 3 with slow.
Qed.

Lemma cover_vars_upto_union {o} :
  forall a b (s : @CSub o) vs,
    cover_vars_upto (mk_union a b) s vs
    <=> (cover_vars_upto a s vs # cover_vars_upto b s vs).
Proof.
  introv.
  unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  rw subvars_app_l; sp.
Qed.

Lemma cover_vars_upto_bool {o} :
  forall (s : @CSub o) vs, cover_vars_upto mk_bool s vs.
Proof.
  introv.
  unfold mk_bool.
  apply cover_vars_upto_union; dands; eauto 3 with slow.
Qed.
Hint Resolve cover_vars_upto_bool : slow.

Lemma cover_vars_upto_bunion {o} :
  forall a b (s : @CSub o) vs,
    cover_vars_upto (mk_bunion a b) s vs
    <=> (cover_vars_upto a s vs # cover_vars_upto b s vs).
Proof.
  introv.
  unfold mk_bunion.
  rw @cover_vars_upto_tunion.
  rw @cover_vars_upto_ite.
  rw @cover_vars_upto_var.

  pose proof (newvarlst_prop [a,b]) as p.
  remember (newvarlst [a,b]) as v; clear Heqv.
  allsimpl; allrw app_nil_r; allrw in_app_iff; allrw not_over_or; repnd.

  rw (cover_vars_upto_csub_filter_single_cons_disj a s v vs p0).
  rw (cover_vars_upto_csub_filter_single_cons_disj b s v vs p).

  split; intro k; repnd; dands; eauto 3 with slow.
Qed.

Lemma cover_vars_upto_tnat {o} :
  forall (s : @CSub o) vs, cover_vars_upto mk_tnat s vs.
Proof.
  introv.
  unfold mk_tnat.
  apply cover_vars_upto_set; dands; eauto 3 with slow.
  apply cover_vars_upto_le; dands; eauto 3 with slow.
  apply cover_vars_upto_var; simpl; tcsp.
Qed.
Hint Resolve cover_vars_upto_tnat : slow.

Lemma cover_vars_upto_natU {o} :
  forall (s : @CSub o) vs, cover_vars_upto mk_natU s vs.
Proof.
  introv.
  unfold mk_natU.
  apply cover_vars_upto_bunion; dands; eauto 3 with slow.
Qed.
Hint Resolve cover_vars_upto_natU : slow.

Lemma cover_vars_upto_natk2T {o} :
  forall (t1 t2 : @NTerm o) s vs,
    cover_vars_upto (mk_natk2T t1 t2) s vs
    <=> (cover_vars_upto t1 s vs # cover_vars_upto t2 s vs).
Proof.
  introv.
  unfold mk_natk2T.
  rw @cover_vars_upto_fun.
  rw @cover_vars_upto_natk; sp.
Qed.

Lemma cover_vars_upto_nat2T {o} :
  forall (t : @NTerm o) s vs,
    cover_vars_upto (mk_nat2T t) s vs
    <=> cover_vars_upto t s vs.
Proof.
  introv.
  unfold mk_nat2T.
  rw @cover_vars_upto_fun.
  split; introv k; repnd; dands; eauto 3 with slow.
Qed.

Lemma cover_vars_nat2T {o} :
  forall (t : @NTerm o) s,
    cover_vars (mk_nat2T t) s
    <=> cover_vars t s.
Proof.
  introv.
  allrw <- @cover_vars_upto_nil_iff.
  apply cover_vars_upto_nat2T.
Qed.

Lemma cover_vars_mod_fun_type_v2 {o} :
  forall v (T : @NTerm o) s,
    !LIn v (free_vars T)
    -> (cover_vars (mod_fun_type_v2 v T) s <=> cover_vars T s).
Proof.
  introv niv; unfold mod_fun_type_v2.
  rw @cover_vars_function.
  rw @cover_vars_upto_fun.
  rw @cover_vars_upto_natk2T.
  rw @cover_vars_upto_var.
  rw (cover_vars_upto_csub_filter_single_cons_disj T s v [] niv).
  simpl.
  split; intro k; repnd; dands; eauto 3 with slow.
Qed.

Definition modulus_fun_type_u_v2 {o} (T : @CTerm o) : CTerm :=
  mkc_function
    mkc_tnat
    nvarx
    (mkcv_fun
       [nvarx]
       (mkcv_fun [nvarx] (mkcv_natk [nvarx] (mkc_var nvarx)) (mk_cv [nvarx] T))
       (mk_cv [nvarx] (mkc_bunion mkc_tnat mkc_unit))).

Lemma cl_lsubst_aux_cons_weak {o} :
  forall (t : @NTerm o) sub v u,
    cl_sub sub
    -> closed u
    -> !LIn v (free_vars t)
    -> lsubst_aux t ((v, u) :: sub) = lsubst_aux t sub.
Proof.
  nterm_ind t as [v|f|op bs ind] Case; introv cls clu ni; allsimpl; auto.

  - Case "vterm".
    boolvar; auto.
    allrw not_over_or; repnd; tcsp.

  - Case "oterm".
    f_equal.
    apply eq_maps; introv i.
    destruct x as [l t]; simpl.
    f_equal; simpl.
    boolvar; tcsp.

    eapply ind; eauto with slow.
    intro j; destruct ni.
    rw lin_flat_map; eexists; dands; eauto.
    simpl.
    rw in_remove_nvars; sp.
Qed.

Lemma lsubstc_mk_natk2T_sp1 {o} :
  forall v T (t : @CTerm o) w s c w' c',
    !LIn v (free_vars T) ->
    alphaeqc
      (lsubstc (mk_natk2T (mk_var v) T) w ((v,t) :: s) c)
      (natk2T t (lsubstc T w' s c')).
Proof.
  introv niv.
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
  repeat (destruct n; tcsp; try omega); clear j;[|].

  { apply alphaeqbt_nilv2.

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
  }

  { boolvar.

    { pose proof (ex_fresh_var (all_vars (lsubst_aux T (sub_filter (csub2sub s) [newvar T])) ++
       all_vars (csubst T s))) as fvs; exrepnd.
      apply (al_bterm_aux [v]); simpl; auto.
      { apply disjoint_singleton_l.
        allrw in_app_iff; sp. }

      rw @lsubst_aux_sub_filter;[|apply disjoint_singleton_r;apply newvar_prop].

      rw (lsubst_aux_trivial_cl_term (lsubst_aux T (csub2sub s)));
        [|simpl;rw @free_vars_lsubst_aux_cl; eauto 2 with slow;
          apply disjoint_singleton_r;
          rw in_remove_nvars; intro k; repnd;
          apply newvar_prop in k0; sp].

      rw (lsubst_aux_trivial_cl_term (csubst T s));
        [|simpl; apply disjoint_singleton_r;
          apply newvar_prop].

      unfold csubst.
      unflsubst.
    }

    { pose proof (ex_fresh_var (all_vars (lsubst_aux T ((v,x) :: sub_filter (csub2sub s) [newvar T])) ++
       all_vars (csubst T s))) as fvs; exrepnd.
      apply (al_bterm_aux [v0]); simpl; auto.
      { apply disjoint_singleton_l.
        allrw in_app_iff; sp; allrw not_over_or; sp. }

      rw @cl_lsubst_aux_cons_weak; eauto 3 with slow.

      rw @lsubst_aux_sub_filter;[|apply disjoint_singleton_r;apply newvar_prop].

      rw (lsubst_aux_trivial_cl_term (lsubst_aux T (csub2sub s)));
        [|simpl;rw @free_vars_lsubst_aux_cl; eauto 2 with slow;
          apply disjoint_singleton_r;
          rw in_remove_nvars; intro k; repnd;
          apply newvar_prop in k0; sp].

      rw (lsubst_aux_trivial_cl_term (csubst T s));
        [|simpl; apply disjoint_singleton_r;
          apply newvar_prop].

      unfold csubst.
      unflsubst.
    }
  }
Qed.

Lemma lsubstc_mod_fun_type_v2_aux {o} :
  forall v T w (s : @CSub o) c w' c',
    !LIn v (free_vars T) ->
    alphaeqc
      (lsubstc (mod_fun_type_v2 v T) w s c)
      (modulus_fun_type_u_v2 (lsubstc T w' s c')).
Proof.
  introv niv.

  unfold mod_fun_type_v2.
  lsubst_tac.
  allrw @lsubstc_mkc_tnat.
  unfold modulus_fun_type_u_v2.

  apply implies_alphaeqc_mkc_function; eauto 2 with slow.
  introv.
  repeat substc_lsubstc_vars3.
  eapply alphaeqc_trans;[|apply alphaeqc_sym;apply substc_mkcv_fun].

  match goal with
    | [ |- context[lsubstc (mk_fun ?a ?b) ?w ?s ?c] ] =>
      pose proof (lsubstc_mk_fun_ex a b s w c) as h;
        exrepnd; clear_irr
  end.
  eapply alphaeqc_trans;[exact h1|]; clear h1.

  apply alphaeqc_mkc_fun.

  - eapply alphaeqc_trans;[|apply alphaeqc_sym;apply substc_mkcv_fun].
    eapply alphaeqc_trans;
      [|apply alphaeqc_sym;apply alphaeqc_mkc_fun;
        [apply mkcv_natk_substc
        |apply alphaeqc_refl]
      ].
    rw @mkc_var_substc.
    rw @csubst_mk_cv.

    eapply alphaeqc_trans;[apply lsubstc_mk_natk2T_sp1; eauto|].
    apply alphaeqc_refl.

  - eapply alphaeqc_trans;[apply lsubstc_mk_natU|].
    rw @csubst_mk_cv; eauto 3 with slow.
Qed.

Lemma lsubstc_mod_fun_type_v2 {o} :
  forall v T w (s : @CSub o) c,
    !LIn v (free_vars T) ->
    {w' : wf_term T
     & {c' : cover_vars T s
     &  alphaeqc
          (lsubstc (mod_fun_type_v2 v T) w s c)
          (modulus_fun_type_u_v2 (lsubstc T w' s c')) }}.
Proof.
  introv niv.

  dup w as w'.
  apply @wf_term_mod_fun_type_v2 in w'.

  dup c as c'.
  apply (cover_vars_mod_fun_type_v2 v T s niv) in c'.

  exists w' c'.

  apply lsubstc_mod_fun_type_v2_aux; auto.
Qed.

Lemma lsubstc_mk_nat2T_sp1 {o} :
  forall (T : @NTerm o) w s c w' c',
    alphaeqc
      (lsubstc (mk_nat2T T) w s c)
      (nat2T (lsubstc T w' s c')).
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
  repeat prove_alpha_eq4.

  pose proof (ex_fresh_var (all_vars (lsubst_aux T (sub_filter (csub2sub s) [newvar T])) ++
                                     all_vars (lsubst_aux T (csub2sub s)))) as fvs; exrepnd.
  apply (al_bterm_aux [v]); simpl; auto.
  { apply disjoint_singleton_l.
    allrw in_app_iff; sp; allrw not_over_or; sp. }

  rw @lsubst_aux_sub_filter;[|apply disjoint_singleton_r;apply newvar_prop].

  rw (lsubst_aux_trivial_cl_term (lsubst_aux T (csub2sub s)));
    [|simpl;rw @free_vars_lsubst_aux_cl; eauto 2 with slow;
      apply disjoint_singleton_r;
      rw in_remove_nvars; intro k; repnd;
      apply newvar_prop in k0; sp].

  rw (lsubst_aux_trivial_cl_term (lsubst_aux T (csub2sub s)));
    [|simpl; apply disjoint_singleton_r;
      apply newvar_prop].
  auto.
Qed.

Lemma tequality_modulus_fun_type_u_v2 {o} :
  forall (lib : @library o) T1 T2,
    tequality lib (modulus_fun_type_u_v2 T1) (modulus_fun_type_u_v2 T2)
    <=> tequality lib T1 T2.
Proof.
  introv.
  unfold modulus_fun_type_u_v2.
  rw @tequality_function.

  split; intro k; repnd; dands; eauto 3 with slow;
  try (apply type_tnat).

  - pose proof (k (mkc_nat 1) (mkc_nat 1)) as h; clear k.
    autodimp h hyp; eauto 3 with slow.
    eapply tequality_respects_alphaeqc_left in h;[|apply substc_mkcv_fun].
    eapply tequality_respects_alphaeqc_right in h;[|apply substc_mkcv_fun].
    allrw @csubst_mk_cv.
    apply tequality_fun in h; repnd; clear h.
    eapply tequality_respects_alphaeqc_left in h0;[|apply substc_mkcv_fun].
    eapply tequality_respects_alphaeqc_right in h0;[|apply substc_mkcv_fun].
    apply tequality_fun in h0; repnd; clear h1.
    allrw @csubst_mk_cv.
    autodimp h0 hyp.
    eapply inhabited_type_respects_alphaeqc;
      [apply alphaeqc_sym; apply mkcv_natk_substc|].
    allrw @mkc_var_substc.
    exists (@mkc_zero o).
    apply equality_in_natk.
    exists 0 (Z.of_nat 1).
    rw @mkc_zero_eq.
    dands; spcast; try (apply computes_to_valc_refl; eauto 3 with slow).
    apply Znat.inj_lt; auto.

  - introv e.
    eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply substc_mkcv_fun|].
    eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_fun|].

    apply tequality_fun.
    dands.

    + eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply substc_mkcv_fun|].
      eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply substc_mkcv_fun|].
      allrw @mkcv_tnat_substc.

      apply tequality_fun.
      dands.

      * eapply tequality_respects_alphaeqc_left;[apply alphaeqc_sym;apply mkcv_natk_substc|].
        eapply tequality_respects_alphaeqc_right;[apply alphaeqc_sym;apply mkcv_natk_substc|].
        allrw @mkc_var_substc.

        apply equality_in_tnat in e.
        unfold equality_of_nat in e; exrepnd; spcast.
        apply tequality_mkc_natk.
        allrw @mkc_nat_eq.
        exists (Z.of_nat k0) (Z.of_nat k0); dands; spcast; auto.
        introv i.
        destruct (Z_lt_le_dec k1 (Z.of_nat k0)); tcsp.

      * introv inh.
        allrw @csubst_mk_cv; auto.

    + introv inh.
      allrw @csubst_mk_cv.
      apply tequality_bunion; dands.
      * apply type_tnat.
      * apply type_mkc_unit.
Qed.

Lemma tequality_nat2T {o} :
  forall (lib : @library o) T1 T2,
    tequality lib (nat2T T1) (nat2T T2)
    <=> tequality lib T1 T2.
Proof.
  introv.
  unfold nat2T.
  rw @tequality_fun.

  split; intro k; repnd; dands; eauto 3 with slow;
  try (apply type_tnat).

  autodimp k hyp; eauto 3 with slow.
  exists (@mkc_nat o 0); unfold member; eauto 3 with slow.
Qed.

Lemma inhabited_type_tnat {o} :
  forall (lib : @library o), inhabited_type lib mkc_tnat.
Proof.
  introv.
  exists (@mkc_nat o 0).
  unfold member; eauto 3 with slow.
Qed.
Hint Resolve inhabited_type_tnat : slow.

Lemma equality_nat2T_to_natk2T {o} :
  forall lib (n f g : @CTerm o) T,
    member lib n mkc_tnat
    -> equality lib f g (nat2T T)
    -> equality lib f g (natk2T n T).
Proof.
  introv m e.

  allrw @equality_in_tnat.
  allunfold @equality_of_nat; exrepnd; spcast; GC.

  allrw @equality_in_fun; repnd; dands; eauto 3 with slow.
  { apply type_mkc_natk.
    exists (Z.of_nat k); spcast; auto. }

  introv en.
  apply equality_natk_to_tnat in en; apply e in en; auto.
Qed.

Lemma equality_in_natk2T_implies_equality_bound {o} :
  forall lib (f g : @CTerm o) k T,
    type lib T
    -> value_type lib T
    -> equality lib f g (natk2T (mkc_nat k) T)
    -> forall a x,
         equality lib
                  (bound_c (mkc_utoken a) (mkc_nat k) f x)
                  (bound_c (mkc_utoken a) (mkc_nat k) g x)
                  (nat2TE a T).
Proof.
  introv tT vT equ; introv.
  unfold nat2TE.

  apply equality_in_fun.
  dands; eauto 3 with slow.
  { introv inh; apply tequality_TE; auto. }
  introv i.

  (* beta reduce *)
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_apply_bound_c|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_apply_bound_c|].
  allrw @boundl_c_eq.

  (* let's get rid of [a0] and [a'] *)
  rw @equality_in_tnat in i.
  unfold equality_of_nat in i; exrepnd; spcast.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_mkc_less;
     [apply computes_to_valc_implies_cequivc;exact i1
     |apply cequivc_refl
     |apply implies_cequivc_apply;
       [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact i1]
     |apply cequivc_refl]
    |].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_less;
     [apply computes_to_valc_implies_cequivc;exact i0
     |apply cequivc_refl
     |apply implies_cequivc_apply;
       [apply cequivc_refl|apply computes_to_valc_implies_cequivc;exact i0]
     |apply cequivc_refl]
    |].
  clear dependent a0.
  clear dependent a'.

  allrw @mkc_nat_eq.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym; apply cequivc_mkc_less_int|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym; apply cequivc_mkc_less_int|].
  allrw <- @mkc_nat_eq.

  boolvar.

  - assert (k0 < k) as ltk by omega.
    unfold natk2T in equ.
    apply equality_in_fun in equ; repnd.
    clear equ0 equ1.
    pose proof (equ (mkc_nat k0) (mkc_nat k0)) as h; clear equ.
    autodimp h hyp.
    { apply equality_in_natk.
      exists k0 (Z.of_nat k); dands; spcast; tcsp; allrw <- @mkc_nat_eq;
      apply computes_to_valc_refl; eauto 2 with slow. }
    allrw @equality_in_tnat.
    apply equality_in_TE; tcsp.

  - apply equality_in_TE;auto.
    right.
    fold (spexc a); dands; spcast; eauto with slow.
Qed.

Lemma ccequivc_as_approx {o} :
  forall lib (t1 t2 : @CTerm o),
    ccequivc lib t1 t2 <=> (capproxc lib t1 t2 # capproxc lib t2 t1).
Proof.
  introv; split; intro k; dands; repnd; spcast; auto.
  - destruct k; auto.
  - destruct k; auto.
  - split; auto.
Qed.

Lemma reduces_in_atmost_k_steps_exc_impossible2 {o} :
  forall lib v a k1 k2 (t : @NTerm o),
    iscan v
    -> reduces_in_atmost_k_steps_exc lib t (spexc a) k1
    -> reduces_in_atmost_k_steps_exc lib t v k2
    -> False.
Proof.
  induction k1; introv isc r1 r2.

  - allrw @reduces_in_atmost_k_steps_exc_0; subst.
    apply reduces_in_atmost_k_steps_exc_done in r2; eauto 3 with slow; ginv.
    subst; allsimpl; tcsp.

  - allrw @reduces_in_atmost_k_steps_exc_S;
    repndors; exrepnd; subst; repndors; exrepnd; subst; allsimpl.

    + destruct k2.

      * allrw @reduces_in_atmost_k_steps_exc_0; ginv.

      * allrw @reduces_in_atmost_k_steps_exc_S;
        repndors; exrepnd; subst; repndors; exrepnd; subst; allsimpl; tcsp;
        eauto 3 with slow; ginv.

        { rw r7 in r4; ginv.
          eapply IHk1 in r1; eauto. }

        { apply isvalue_like_implies_not_isnoncan_like in r0; sp. }

    + destruct k2.

      * allrw @reduces_in_atmost_k_steps_exc_0; ginv.

      * allrw @reduces_in_atmost_k_steps_exc_S;
        repndors; exrepnd; subst; repndors; exrepnd; subst; allsimpl; tcsp;
        eauto 3 with slow; ginv.

        { apply isvalue_like_implies_not_isnoncan_like in r6; sp. }

        { rw r7 in r4; ginv.
          eapply IHk1 in r1; eauto. }

    + destruct k2.

      * allrw @reduces_in_atmost_k_steps_exc_0; ginv; subst; allsimpl; tcsp; GC.
        apply iscan_implies in isc; repndors; exrepnd; subst;
        csunf r1; allsimpl; ginv;
        apply reduces_in_atmost_k_steps_exc_iscan in r3; subst; tcsp; ginv.

      * allrw @reduces_in_atmost_k_steps_exc_S;
        repndors; exrepnd; subst; repndors; exrepnd; subst; allsimpl; tcsp;
        eauto 3 with slow; ginv.
        rw r1 in r2; ginv.
        eapply IHk1 in r3; eauto.
Qed.

Lemma reduces_in_atmost_k_steps_excc_impossible2 {o} :
  forall lib v a k1 k2 (t : @CTerm o),
    iscanc v
    -> reduces_in_atmost_k_steps_excc lib t (spexcc a) k1
    -> reduces_in_atmost_k_steps_excc lib t v k2
    -> False.
Proof.
  introv isc r1 r2; destruct_cterms.
  allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
  eapply (reduces_in_atmost_k_steps_exc_impossible2 lib x0) in r1; eauto.
Qed.

Lemma member_in_TE_implies {o} :
  forall lib (t : @CTerm o) a T,
    value_type lib T
    -> member lib t (TE a T)
    -> hasvaluec lib t [+] cequivc lib t (spexcc a).
Proof.
  introv vT equ.

  applydup @inhabited_implies_tequality in equ as tT.
  apply tequality_TE in tT.

  apply equality_in_TE in equ; auto.

  assert {k : nat
          , {v : CTerm , reduces_ksteps_excc lib t v k # iscanc v}
            {+} reduces_ksteps_excc lib t (spexcc a) k } as j.
  { repndors.

    - apply vT in equ.
      apply hasvaluec_computes_to_valc_implies in equ; exrepnd.
      rw @computes_to_valc_iff_reduces_in_atmost_k_stepsc in equ0; exrepnd.
      exists k; left.
      exists b.
      dands; eauto 3 with slow; spcast.
      apply reduces_in_atmost_k_steps_excc_can; eauto 3 with slow.

    - repnd; spcast.
      clear equ0.
      apply cequivc_spexcc in equ.
      exrepnd.
      allrw @computes_to_valc_iff_reduces_in_atmost_k_stepsc; exrepnd.
      allrw @computes_to_excc_iff_reduces_in_atmost_k_stepsc; exrepnd.

      exists (k1 + k + k0).
      right; dands; spcast.

      apply (reduces_in_atmost_k_steps_excc_le_exc _ (k1 + k + k0));
        eauto 3 with slow; tcsp;
        try (apply Nat.le_max_l; auto).
      pose proof (reduces_in_atmost_k_steps_excc_exception
                    lib k k0 n e (mkc_utoken a) mkc_axiom) as h.
      repeat (autodimp h hyp); tcsp; exrepnd.
      pose proof (reduces_in_atmost_k_steps_excc_trans2
                    lib k1 i
                    t
                    (mkc_exception n e)
                    (mkc_exception (mkc_utoken a) mkc_axiom)) as q.
      repeat (autodimp q hyp); exrepnd.
      apply (reduces_in_atmost_k_steps_excc_le_exc _ i0); tcsp; try omega.
  }

  apply (constructive_indefinite_ground_description nat (fun x => x) (fun x => x))
    in j; auto.

  { exrepnd.
    pose proof (dec_reduces_ksteps_excc lib x t (spexcc a)) as q.
    autodimp q hyp; simpl; try (fold (spexc a)); eauto 3 with slow.

    destruct q as [q|q];[right|left].

    { apply reduces_ksteps_excc_spexcc_decompose in q.
      exrepnd.
      allunfold @reduces_in_atmost_k_stepsc; allsimpl.
      allrw @get_cterm_apply; allsimpl.
      allrw @get_cterm_mkc_exception; allsimpl.
      dands;
        apply cequiv_spexc_if;
        try (apply isprog_apply);
        try (apply isprog_mk_nat);
        eauto 3 with slow.
      exists (get_cterm a') (get_cterm e'); dands; eauto 3 with slow.
      unfold computes_to_exception; exists k1; auto. }

    { pose proof (dec_ex_reduces_in_atmost_k_steps_excc lib x t) as h.
      clear equ.
      destruct h as [h|h].
      - exrepnd.
        destruct (dec_iscanc v) as [i|i].
        + apply (computes_to_valc_implies_hasvaluec lib t v).
          apply computes_to_valc_iff_reduces_in_atmost_k_stepsc.
          dands; eauto 3 with slow.
          exists x.
          apply reduces_in_atmost_k_steps_excc_can_implies; auto.
        + provefalse.
          destruct j0 as [j0|j0]; exrepnd; spcast.
          * destruct_cterms.
            allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
            allunfold @reduces_in_atmost_k_steps_exc.
            rw j0 in h0; ginv.
          * destruct q; spcast; auto.
      - provefalse; repndors; exrepnd; spcast.
        + destruct h.
          exists v; auto.
        + destruct q; auto; spcast; auto.
    }
  }

  { clear j; introv.

    pose proof (dec_ex_reduces_in_atmost_k_steps_excc lib x t) as h.
    pose proof (dec_reduces_ksteps_excc lib x t (spexcc a)) as q.
    autodimp q hyp; simpl; try (fold (spexc a)); eauto 3 with slow.

    clear equ.

    destruct h as [h|h];
      destruct q as [q|q];
      exrepnd;
      try (destruct (deq_nat n0 n) as [d|d]); subst;
      tcsp;
      try (complete (eapply reduces_ksteps_excc_impossible1 in h0; eauto; tcsp));
      try (complete (eapply reduces_ksteps_excc_impossible1 in j0; eauto; tcsp));
      try (complete (provefalse; repndors; repnd; tcsp));
      try (complete (right; intro xx; exrepnd; repndors; repnd; tcsp;
                     try (complete (destruct h; eexists; eauto));
                     try (complete (destruct j; eexists; eauto))));
      try (complete (left; exists n; left; tcsp));
      try (complete (left; exists 0; right; tcsp)).

    - destruct (dec_iscanc v) as [i|i].

      + left; left.
        exists v; dands; auto.
        spcast; auto.

      + right.
        introv r; repndors; exrepnd; spcast; tcsp.

        * destruct_cterms.
          allunfold @reduces_in_atmost_k_steps_excc; allsimpl.
          allunfold @reduces_in_atmost_k_steps_exc.
          rw r1 in h0; ginv.

        * destruct q; spcast; auto.

    - right.
      introv r; repndors; exrepnd; spcast; tcsp.

      * destruct h; exists v; auto.

      * destruct q; spcast; auto.
  }
Qed.

Lemma reduces_in_atmost_k_steps_exc_eq {o} :
  forall lib (t : @NTerm o) v1 v2 k,
    reduces_in_atmost_k_steps_exc lib t v1 k
    -> reduces_in_atmost_k_steps_exc lib t v2 k
    -> v1 = v2.
Proof.
  introv r1 r2.
  allunfold @reduces_in_atmost_k_steps_exc.
  rw r1 in r2; ginv.
Qed.

Lemma cequivc_bound_nat_c_sp_bound_nat_c_v2 {o} :
  forall lib a (f : @CTerm o) x e z T,
    e <> x
    -> value_type lib T
    -> member lib f (nat2TE a T)
    -> cequivc
         lib
         (bound_nat_c a x e z f)
         (sp_bound_nat_c x z f).
Proof.
  introv d1 vT mem.

  applydup @inhabited_implies_tequality in mem as tT.
  apply tequality_fun in tT; repnd.
  clear tT0.
  autodimp tT hyp; eauto 3 with slow.
  apply tequality_TE in tT.

  unfold bound_nat_c, sp_bound_nat_c.

  apply cequivc_lam; introv.
  allrw @mkcv_cbv_substc_same.
  allrw @mkcv_cont1_dup1.
  allrw @mkcv_less_substc.
  allrw @substc_mkcv_zero.
  allrw @mkcv_apply_substc.
  allrw @csubst_mk_cv.
  allrw @mkc_var_substc.
  allrw @mkcv_vbot_substc.

  apply approxc_implies_cequivc; apply approxc_assume_hasvalue; intro hv.

  - apply @hasvalue_likec_cbv in hv.
    apply @hasvalue_likec_implies_or in hv.
    repndors.

    + apply hasvaluec_computes_to_valc_implies in hv; exrepnd.
      eapply cequivc_approxc_trans;
        [apply simpl_cequivc_mkc_cbv;
          apply computes_to_valc_implies_cequivc;
          exact hv0|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_mkc_less;
           [apply cequivc_sym
           |apply cequivc_refl
           |apply cequivc_refl
           |apply cequivc_refl];
           apply computes_to_valc_implies_cequivc;
           exact hv0
        ].
      rw @computes_to_valc_iff_reduces_toc in hv0; repnd.
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_cbv;complete auto|].

      allrw @mkcv_less_substc.
      rw @mkcv_try_substc; try (complete (intro xx; ginv)).
      allrw @mkcv_apply_substc.
      allrw @substc_mkcv_zero.
      allrw @mkc_var_substc.
      allrw @mkcv_vbot_substc.
      allrw @csubst_mk_cv.
      allrw @mkcv_utoken_substc.
      unfold spexccv; rw @substc2_mk_cv; fold (spexccv [nvare] a).

      apply approxc_assume_hasvalue; intro hv.

      apply hasvalue_likec_less in hv; repndors; exrepnd.

      * eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact hv2
          |apply cequivc_refl
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply cequivc_mkc_less;
             [apply reduces_toc_implies_cequivc;exact hv2
             |apply cequivc_refl
             |apply cequivc_refl
             |apply cequivc_refl]
          ].
        rw @mkc_zero_eq.
        rw @mkc_nat_eq.
        eapply cequivc_approxc_trans;
          [apply cequivc_mkc_less_int|].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;apply cequivc_mkc_less_int].

        clear hv3.

        boolvar; eauto 3 with slow; try (apply approxc_refl).

        pose proof (Wf_Z.Z_of_nat_complete_inf i1) as q.
        autodimp q hyp;[]; exrepnd; subst.
        rw <- @mkc_nat_eq in hv2.

        eapply cequivc_approxc_trans;
          [apply simpl_cequivc_mkc_try;
            [apply implies_cequivc_apply;
              [apply cequivc_refl
              |apply reduces_toc_implies_cequivc;exact hv2]
            |apply cequivc_refl]
          |].

        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply implies_cequivc_apply;
             [apply cequivc_refl
             |apply reduces_toc_implies_cequivc;
               eapply reduces_toc_trans;
               [exact hv1|exact hv2]
             ]
          ].

        apply equality_in_fun in mem; repnd.
        clear mem0 mem1.
        pose proof (mem (mkc_nat n) (mkc_nat n)) as h.
        autodimp h hyp; eauto 3 with slow.
        allrw @member_eq.

        applydup @member_in_TE_implies in h; auto; repndors;[|].

        { apply hasvaluec_computes_to_valc_implies in h0; exrepnd.
          eapply cequivc_approxc_trans;
            [apply computes_to_valc_implies_cequivc;
              eapply computes_to_valc_mkc_try;
              [exact h1|apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
            |].
          apply computes_to_valc_implies_approxc in h1; sp. }

        { repnd; GC.
          eapply approxc_cequivc_trans;
            [|apply cequivc_sym;exact h0].

          eapply cequivc_approxc_trans;
            [apply simpl_cequivc_mkc_try;
              [exact h0
              |apply cequivc_refl]
            |].
          unfold spexcc.
          eapply cequivc_approxc_trans;
            [apply reduces_toc_implies_cequivc;
              apply reduces_toc_mkc_try_exc
            |].
          unfold spexccv; rw @csubst_mk_cv.
          apply approxc_refl. }

      * assert (computes_to_excc lib a0 b e0) as comp.
        { allrw @computes_to_excc_iff_reduces_toc.
          eapply reduces_toc_trans;[exact hv2|].
          apply reduces_toc_refl. }
        clear hv1 hv2.

        allrw @computes_to_excc_iff_reduces_toc.

        eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact comp
          |apply cequivc_refl
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply cequivc_mkc_less;
             [apply reduces_toc_implies_cequivc;exact comp
             |apply cequivc_refl
             |apply cequivc_refl
             |apply cequivc_refl]
          ].

        eapply cequivc_approxc_trans;
          [apply cequivc_mkc_less_exc|].
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym; apply cequivc_mkc_less_exc].
        apply approxc_refl.

      * apply (computes_to_valc_and_excc_false _ _ _ mkc_zero) in hv4; tcsp.
        apply computes_to_valc_refl; eauto 3 with slow.

    + allrw @raises_exceptionc_as_computes_to_excc; exrepnd.
      allrw @computes_to_excc_iff_reduces_toc.

      eapply cequivc_approxc_trans;
        [apply simpl_cequivc_mkc_cbv;
          apply reduces_toc_implies_cequivc;
          exact hv1|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_mkc_less;
           [apply cequivc_sym
           |apply cequivc_refl
           |apply cequivc_refl
           |apply cequivc_refl];
           apply reduces_toc_implies_cequivc;
           exact hv1
        ].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym; apply cequivc_mkc_less_exc].
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_cbv_exc|].
      apply approxc_refl.

  - apply hasvalue_likec_less in hv.
    repndors; exrepnd.

    + eapply cequivc_approxc_trans;
      [apply cequivc_mkc_less;
        [apply reduces_toc_implies_cequivc;exact hv0
        |apply cequivc_refl
        |apply cequivc_refl
        |apply cequivc_refl]
      |].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply simpl_cequivc_mkc_cbv;
           apply reduces_toc_implies_cequivc;exact hv0
        ].
      rw @mkc_zero_eq.
      rw @mkc_nat_eq.
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_int|].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym; apply cequivc_mkc_cbv]; eauto 3 with slow;[].

      allrw @mkcv_less_substc.
      rw @mkcv_try_substc; try (complete (intro xx; ginv)).
      allrw @mkcv_apply_substc.
      allrw @substc_mkcv_zero.
      allrw @mkc_var_substc.
      allrw @mkcv_vbot_substc.
      allrw @csubst_mk_cv.
      allrw @mkcv_utoken_substc.
      unfold spexccv; rw @substc2_mk_cv; fold (spexccv [nvare] a).
      rw @mkc_zero_eq.
      rw @mkc_nat_eq.
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym; apply cequivc_mkc_less_int].

      clear hv1.

      boolvar; eauto 3 with slow; try (apply approxc_refl).

      pose proof (Wf_Z.Z_of_nat_complete_inf i1) as q.
      autodimp q hyp;[]; exrepnd; subst.
      allrw <- @mkc_nat_eq.

      eapply cequivc_approxc_trans;
        [apply implies_cequivc_apply;
          [apply cequivc_refl
          |apply reduces_toc_implies_cequivc;exact hv0]
        |].

      apply equality_in_fun in mem; repnd.
      clear mem0 mem1.
      pose proof (mem (mkc_nat n) (mkc_nat n)) as h.
      autodimp h hyp; eauto 3 with slow.

      applydup @member_in_TE_implies in h; auto; repndors;[|].

      { apply hasvaluec_computes_to_valc_implies in h0; exrepnd.
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply computes_to_valc_implies_cequivc;
             eapply computes_to_valc_mkc_try;
             [exact h1|apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
          ].
        apply computes_to_valc_implies_approxc in h1; sp. }

      { repnd; GC.
        eapply cequivc_approxc_trans;[exact h0|].

        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply simpl_cequivc_mkc_try;
             [exact h0
             |apply cequivc_refl]
          ].
        unfold spexcc.
        eapply approxc_cequivc_trans;
          [|apply cequivc_sym;
             apply reduces_toc_implies_cequivc;
             apply reduces_toc_mkc_try_exc
          ].
        unfold spexccv; rw @csubst_mk_cv.
        apply approxc_refl. }

    + clear hv1.

      allrw @computes_to_excc_iff_reduces_toc.

      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less;
          [apply reduces_toc_implies_cequivc;exact hv0
          |apply cequivc_refl
          |apply cequivc_refl
          |apply cequivc_refl]
        |].
      eapply cequivc_approxc_trans;
        [apply cequivc_mkc_less_exc|].

      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply simpl_cequivc_mkc_cbv;
           apply reduces_toc_implies_cequivc;exact hv0
        ].
      eapply approxc_cequivc_trans;
        [|apply cequivc_sym;
           apply cequivc_mkc_cbv_exc
        ].
      apply approxc_refl.

    + apply (computes_to_valc_and_excc_false _ _ _ mkc_zero) in hv2; tcsp.
      apply computes_to_valc_refl; eauto 3 with slow.
Qed.

Definition bound_nat_try_c_v2 {o} (a : get_patom_set o) x e z (f : @CTerm o) t :=
  mkc_lam x (mkcv_cbv [x]
                      (mkc_var x)
                      x
                      (mkcv_dup1
                         x
                         (mkcv_less [x]
                                    (mkc_var x)
                                    (mkcv_zero [x])
                                    (mkcv_vbot [x] z)
                                    (mkcv_try [x]
                                              (mkcv_apply [x] (mk_cv [x] f) (mkc_var x))
                                              (mkcv_utoken [x] a)
                                              e
                                              (mk_cv [e,x] t))))).

Lemma implies_equal_bound_nat_try_aux_c_v2 {o} :
  forall lib a x e z (f g : @CTerm o) T t,
    e <> x
    -> value_type lib T
    -> member lib t T
    -> equality lib f g (nat2TE a T)
    -> equality lib (bound_nat_try_c_v2 a x e z f t) (bound_nat_try_c_v2 a x e z g t) (nat2T T).
Proof.
  introv d vT mtT equ.
  unfold nat2T.
  unfold nat2TE in equ.
  allrw @equality_in_fun; repnd.
  autodimp equ1 hyp.
  { apply inhabited_type_tnat. }
  apply tequality_TE in equ1.
  dands; tcsp.

  introv en.
  unfold bound_nat_try_c.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_beta|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_beta|].

  repeat (rw @mkcv_cbv_substc_same).
  repeat (rw @mkc_var_substc).
  allrw @mkcv_cont1_dup1.

  apply equality_in_tnat in en.
  unfold equality_of_nat in en; exrepnd; spcast.
  pose proof (equ (mkc_nat k) (mkc_nat k)) as eqn.
  autodimp eqn hyp.
  { apply equality_in_tnat; unfold equality_of_nat.
    exists k; dands; spcast; apply computes_to_valc_refl;
    eauto 3 with slow. }

  eapply equality_respects_cequivc_left;
    [apply simpl_cequivc_mkc_cbv;
      apply cequivc_sym;
      apply computes_to_valc_implies_cequivc;
      exact en1|].
  eapply equality_respects_cequivc_right;
    [apply simpl_cequivc_mkc_cbv;
      apply cequivc_sym;
      apply computes_to_valc_implies_cequivc;
      exact en0|].

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_mkc_cbv|]; eauto 3 with slow.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_cbv|]; eauto 3 with slow.

  repeat (rw @mkcv_less_substc).
  repeat (rw @mkcv_try_substc; auto).
  repeat (rw @mkcv_apply_substc).
  repeat (rw @csubst_mk_cv).
  repeat (rw @mkc_var_substc).
  repeat (rw @mkcv_utoken_substc).
  repeat (rw @mkcv_vbot_substc).
  repeat (rw @mkcv_zero_substc).
  unfold mkcv_zero.
  repeat (rw @substc2_mk_cv).
  fold (@mkcv_zero o [e]).

  allrw @mkc_zero_eq.
  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_mkc_less_nat|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_less_nat|].
  boolvar; tcsp;[].

  apply @equality_in_TE in eqn; auto.
  repndors.

  - pose proof (vT (mkc_apply f (mkc_nat k))) as hv1.
    pose proof (vT (mkc_apply g (mkc_nat k))) as hv2.
    autodimp hv1 hyp.
    { apply equality_refl in eqn; auto. }
    autodimp hv2 hyp.
    { apply equality_sym in eqn; apply equality_refl in eqn; auto. }
    allapply @hasvaluec_computes_to_valc_implies; exrepnd.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        eapply computes_to_valc_mkc_try;
        [exact hv2|apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply computes_to_valc_implies_cequivc;
        eapply computes_to_valc_mkc_try;
        [exact hv0|apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
      |].
    eapply equality_respects_cequivc_left;
      [apply computes_to_valc_implies_cequivc;exact hv2|].
    eapply equality_respects_cequivc_right;
      [apply computes_to_valc_implies_cequivc;exact hv0|].
    auto.

  - repnd; spcast.
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;
        apply simpl_cequivc_mkc_try;[exact eqn0|apply cequivc_refl]
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply simpl_cequivc_mkc_try;[exact eqn|apply cequivc_refl]
      |].

    eapply equality_respects_cequivc_left;
      [apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        apply reduces_toc_mkc_try_exc
      |].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym;
        apply reduces_toc_implies_cequivc;
        apply reduces_toc_mkc_try_exc
      |].
    allrw @csubst_mk_cv; auto.
Qed.

Definition bound_nat_try_v2 {o} (a : get_patom_set o) x e z (f : @NTerm o) t :=
  mk_lam x (bound_nat_try_aux a (mk_var x) x e z f t).

Lemma wf_bound_nat_try_v2 {o} :
  forall a x e z (f : @NTerm o) t,
    wf_term f
    -> wf_term t
    -> wf_term (bound_nat_try_v2 a x e z f t).
Proof.
  introv wf wt.
  apply wf_lam.
  apply wf_bound_nat_try_aux; eauto 3 with slow.
Qed.
Hint Resolve wf_bound_nat_try_v2 : slow.

Lemma differ_try_compute_to_valc_nat_v2 {o} :
  forall lib a (F f g : @CTerm o) k x e z t T,
    !LIn a (getc_utokens F)
    -> eq_value_type_na lib a T
    -> equality lib f g (nat2TE a T)
    -> computes_to_valc
         lib
         (mkc_apply F (bound_nat_try_c_v2 a x e z f t))
         (mkc_nat k)
    -> {v1 : CTerm
        & {v2 : CTerm
        & reduces_toc lib (mkc_apply F (bound_nat_c a x e z f)) v1
        # reduces_toc lib (mkc_apply F (bound_nat_c a x e z g)) v2
        # ((v1 = mkc_nat k # v2 = mkc_nat k)
           [+] (cequivc lib v1 (spexcc a) # cequivc lib v2 (spexcc a)))}}.
Proof.
  introv nia vT equ comp.
  apply equality_in_nat2TE_implies in equ; auto.
  destruct_cterms.
  unfold computes_to_valc in comp; unfold reduces_toc; allsimpl.
  unfold getc_utokens in nia; allsimpl.
  unfold cequivc; simpl; try (fold (spexc a)).

  fold (@mk_vbot o z) in comp.
  fold (bound_nat_try_aux a (mk_var x) x e z x3 x1) in comp.
  fold (bound_nat_try_v2 a x e z x3 x1) in comp.

  fold (@mk_vbot o z).
  fold (spexc a).
  fold (bound_nat_aux a (mk_var x) x e z x3).
  fold (bound_nat_aux a (mk_var x) x e z x2).
  fold (bound_nat a x e z x3).
  fold (bound_nat a x e z x2).

  unfold computes_to_value, reduces_to in comp; exrepnd.

  pose proof (differ_try_reduces_in_atmost_k_steps_aux
                lib a x3 x2 x1 k0
                (mk_apply x4 (bound_nat_try_v2 a x e z x3 x1))
                (mk_apply x4 (bound_nat a x e z x3))
                (mk_apply x4 (bound_nat a x e z x2))
                (mk_nat k)) as h.
  repeat (autodimp h hyp); eauto 3 with slow.
  { apply wf_apply; eauto 4 with slow. }
  { apply wf_apply; eauto 3 with slow. }
  { apply wf_apply; eauto 3 with slow. }
  { apply differ_try_oterm; simpl; tcsp.
    introv xx; repndors; tcsp; ginv.
    - constructor; apply differ_try_refl; auto.
    - constructor.
      apply differ_try_oterm; simpl; tcsp.
      introv xx; repndors; tcsp; ginv.
      constructor.
      apply differ_try_base; auto. }

  exrepnd.
  apply differ_try_alpha_nat in h1; repndors; exrepnd; subst.

  - exists (@mkc_nat o k) (@mkc_nat o k); simpl; dands; auto.

  - applydup @reduces_to_preserves_isprog in h0;
    [|apply isprog_apply; complete (eauto 3 with slow)].
    applydup @reduces_to_preserves_isprog in h2;
    [|apply isprog_apply; complete (eauto 3 with slow)].

    exists (mk_ct t2' h3) (mk_ct t3' h4); simpl.
    unfold spfexc_pair in h1; exrepnd; subst.
    dands; auto.
    right; dands; tcsp; apply cequiv_spfexc.
Qed.

Lemma apply_nat2natE_aux_v2 {o} :
  forall lib t T (F : @CTerm o) f g a x e z,
    e <> x
    -> !LIn a (getc_utokens F)
    -> member lib t T
    -> eq_value_type_na lib a T
    -> member lib F (mkc_fun (nat2T T) mkc_tnat)
    -> equality lib f g (nat2TE a T)
    -> equality
         lib
         (mkc_apply F (bound_nat_c a x e z f))
         (mkc_apply F (bound_nat_c a x e z g))
         (natE a).
Proof.
  introv d nia mtT vT mem equ.
  rw @equality_in_fun in mem; repnd.
  clear mem0 mem1.

  applydup (implies_equal_bound_nat_try_aux_c_v2 lib a x e z f g T t)
    in equ as eqtry;
    eauto 3 with slow;
    try (complete (intro k; ginv)).
  applydup mem in eqtry as eqn.
  allrw @equality_in_tnat; allunfold @equality_of_nat; exrepnd; spcast.

  pose proof (differ_try_compute_to_valc_nat_v2 lib a F f g k x e z t T) as h.
  repeat (autodimp h hyp); exrepnd.

  apply equality_in_natE; repndors; repnd; subst.
  - left.
    unfold equality_of_nat; exists k; dands; spcast;
    apply computes_to_valc_iff_reduces_toc; dands; auto.
  - right; dands; spcast;
    eapply cequivc_trans;[|exact h3|idtac|exact h1];[|];
    apply reduces_toc_implies_cequivc; auto.
Qed.

Lemma apply_nat2TE_aux2_v2 {o} :
  forall lib (F : @CTerm o) f g a x z t T,
    !LIn a (getc_utokens F)
    -> eq_value_type_na lib a T
    -> member lib t T
    -> member lib F (mkc_fun (nat2T T) mkc_tnat)
    -> equality lib f g (nat2TE a T)
    -> equality
         lib
         (mkc_apply F (sp_bound_nat_c x z f))
         (mkc_apply F (sp_bound_nat_c x z g))
         (natE a).
Proof.
  introv nia vT mT mem equ.
  pose proof (ex_fresh_var [x]) as fv.
  exrepnd; allsimpl; allrw not_over_or; repnd; GC.

  applydup @inhabited_implies_tequality in mem as tT.
  apply tequality_fun in tT; repnd.
  clear tT.
  rw @tequality_nat2T in tT0.

  eapply equality_respects_cequivc_left;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply (cequivc_bound_nat_c_sp_bound_nat_c_v2 _ a _ x v z T);tcsp;
       apply equality_refl in equ;auto
      ]
    |]; eauto 3 with slow.
  eapply equality_respects_cequivc_right;
    [apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply (cequivc_bound_nat_c_sp_bound_nat_c_v2 _ a _ x v z T);tcsp;
       apply equality_sym in equ; apply equality_refl in equ;auto
      ]
    |]; eauto 3 with slow.
  apply (apply_nat2natE_aux_v2 lib t T); auto.
Qed.

Definition no_utokens_t {o} (t : @NTerm o) :=
  get_utokens t = [].

Definition no_utokens_tc {o} (t : @CTerm o) :=
  getc_utokens t = [].

Definition compute_to_eqvals_nut {o} lib (t1 t2 : @CTerm o) :=
  {v : CTerm
   & computes_to_valc lib t1 v
   # computes_to_valc lib t2 v
   # noconstc v
   # noseqc v
   # no_utokens_tc v }.

Definition eq_value_type_nut {o} lib (T : @CTerm o) :=
  forall t1 t2,
    equality lib t1 t2 T
    -> compute_to_eqvals_nut lib t1 t2.

Lemma eq_value_type_nut_implies_na {o} :
  forall lib (T : @CTerm o),
    eq_value_type_nut lib T -> forall a, eq_value_type_na lib a T.
Proof.
  introv eqv equ.
  apply eqv in equ.
  unfold compute_to_eqvals_nut in equ; exrepnd.
  exists v; dands; auto.
  rw equ0; simpl; tcsp.
Qed.
Hint Resolve eq_value_type_nut_implies_na : slow.

Lemma eq_value_type_nut_implies_value_type {o} :
  forall lib (T : @CTerm o),
    eq_value_type_nut lib T -> value_type lib T.
Proof.
  introv eqv equ.
  apply eqv in equ.
  unfold compute_to_eqvals_nut in equ; exrepnd.
  eapply computes_to_valc_implies_hasvaluec; eauto.
Qed.
Hint Resolve eq_value_type_nut_implies_na : slow.

Lemma spM_in_modulus_fun_type_u_v2 {o} :
  forall lib (F : @CTerm o) t T,
    member lib t T
    -> eq_value_type_nut lib T (* so that T is disjoint from exceptions *)
    -> member lib F (mkc_fun (nat2T T) mkc_tnat)
    -> member lib (spM_c F) (modulus_fun_type_u_v2 T).
Proof.
  introv mt vTnut mF.

  applydup @eq_value_type_nut_implies_value_type in vTnut as vT.

  applydup @inhabited_implies_tequality in mF as tT.
  apply tequality_fun in tT; repnd.
  clear tT.
  rw @tequality_nat2T in tT0.
  rename tT0 into tT.

  unfold modulus_fun_type_u_v2.
  apply equality_in_function2.
  fold (@modulus_fun_type_u_v2 o T).
  dands; try (apply tequality_modulus_fun_type_u_v2; auto).
  introv e.
  rename a into n.
  rename a' into m.
  eapply alphaeqc_preserving_equality;[|apply alphaeqc_sym;apply substc_mkcv_fun].
  allrw @csubst_mk_cv.
  apply equality_in_fun.
  dands.

  - eapply type_respects_alphaeqc;[apply alphaeqc_sym;apply substc_mkcv_fun|].
    allrw @mkcv_tnat_substc.
    apply type_mkc_fun.
    dands.
    + eapply type_respects_alphaeqc;[apply alphaeqc_sym;apply mkcv_natk_substc|].
      rw @mkc_var_substc.
      apply equality_in_tnat in e.
      unfold equality_of_nat in e; exrepnd; spcast.
      apply type_mkc_natk.
      allrw @mkc_nat_eq.
      exists (Z.of_nat k); spcast; auto.
    + introv inh.
      allrw @csubst_mk_cv; auto.

  - introv inh.
      apply tequality_bunion; dands.
      * apply type_tnat.
      * apply type_mkc_unit.

  - introv e1.
    allrw <- @mkc_apply2_eq.
    rename a into f.
    rename a' into g.
    eapply alphaeqc_preserving_equality in e1;[|apply substc_mkcv_fun].
    eapply alphaeqc_preserving_equality in e1;
      [|apply alphaeqc_mkc_fun;[apply mkcv_natk_substc|apply alphaeqc_refl] ].
    allrw @mkcv_tnat_substc.
    allrw @mkc_var_substc.
    allrw @csubst_mk_cv; auto.

    apply equality_in_tnat in e.
    unfold equality_of_nat in e; exrepnd; spcast.

    (* let's get rid of [n] and [m] now *)
    eapply cequivc_preserving_equality in e1;
      [|apply cequivc_mkc_fun;[|apply cequivc_refl];
        apply cequivc_mkc_natk;
        apply computes_to_valc_implies_cequivc; exact e2].

    fold (@natk2T o (mkc_nat k) T) in e1.

    eapply equality_respects_cequivc_left;
      [apply implies_cequivc_apply2;[apply cequivc_refl|idtac|apply cequivc_refl];
       apply cequivc_sym; apply computes_to_valc_implies_cequivc; exact e2|].

    eapply equality_respects_cequivc_right;
      [apply implies_cequivc_apply2;[apply cequivc_refl|idtac|apply cequivc_refl];
       apply cequivc_sym; apply computes_to_valc_implies_cequivc; exact e0|].

    clear dependent n.
    clear dependent m.

    (* let's beta-reduce *)
    eapply equality_respects_cequivc_left;
      [apply cequivc_sym; apply cequivc_apply2_spM_c|].
    eapply equality_respects_cequivc_right;
      [apply cequivc_sym; apply cequivc_apply2_spM_c|].

    (* now let's apply bound to [f] and [g] *)
    pose proof (equality_in_natk2T_implies_equality_bound lib f g k T tT vT e1) as h.
    allrw @test_c_eq.

    destruct (fresh_atom o (getc_utokens F ++ getc_utokens f ++ getc_utokens g)) as [a nia].
    allrw in_app_iff; allrw not_over_or; repnd.

    (* let's get rid of fresh in the conclusion *)
    assert (equality
              lib
              (substc (mkc_utoken a) nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat k) f))
              (substc (mkc_utoken a) nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat k) g))
              (mkc_bunion mkc_tnat mkc_unit)) as equ;
      [|pose proof (cequivc_fresh_subst2 lib nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat k) f) a) as h1;
         repeat (autodimp h1 hyp);
         [ destruct_cterms; allsimpl;
           allunfold @getcv_utokens; allunfold @getc_utokens; allsimpl; allrw app_nil_r;
           allrw in_app_iff; tcsp
         | apply equality_refl in equ; apply member_bunion_nat_unit_implies_cis_spcan_not_atom; auto
         |];
         pose proof (cequivc_fresh_subst2 lib nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat k) g) a) as h2;
         repeat (autodimp h2 hyp);
         [ destruct_cterms; allsimpl;
           allunfold @getcv_utokens; allunfold @getc_utokens; allsimpl; allrw app_nil_r;
           allrw in_app_iff; tcsp
         | apply equality_sym in equ; apply equality_refl in equ; apply member_bunion_nat_unit_implies_cis_spcan_not_atom; auto
         |];
         spcast;
         eapply equality_respects_cequivc_left;[apply cequivc_sym;exact h1|];
         eapply equality_respects_cequivc_right;[apply cequivc_sym;exact h2|];
         complete auto
      ].

    repeat (rw @substc_test_try2_cv).

    pose proof (h a nvarx) as q.
    clear h.

    (* This is where we use vTnut *)
    pose proof (apply_nat2TE_aux2_v2
                  lib F
                  (bound_c (mkc_utoken a) (mkc_nat k) f nvarx)
                  (bound_c (mkc_utoken a) (mkc_nat k) g nvarx)
                  a nvarx nvarz
                  t T) as ee.
    repeat (autodimp ee hyp); try (complete (intro xx; ginv)); eauto 3 with slow;[].
    clear q.

    eapply equality_respects_cequivc_left in ee;
      [|apply implies_cequivc_apply;
         [apply cequivc_refl
         |apply cequiv_sp_bound_nat_c_bound_c]
      ].

    eapply equality_respects_cequivc_right in ee;
      [|apply implies_cequivc_apply;
         [apply cequivc_refl
         |apply cequiv_sp_bound_nat_c_bound_c]
      ].

    apply equality_in_natE_implies in ee; repndors.

    { unfold equality_of_nat_tt in ee; exrepnd.
      eapply equality_respects_cequivc_left;
        [apply cequivc_sym;
          apply computes_to_valc_implies_cequivc;
          eapply computes_to_valc_mkc_try;
          [exact ee1|apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
        |].
      eapply equality_respects_cequivc_right;
        [apply cequivc_sym;
          apply computes_to_valc_implies_cequivc;
          eapply computes_to_valc_mkc_try;
          [exact ee0|apply computes_to_pkc_refl;apply mkc_utoken_eq_pk2termc]
        |].
      apply equality_in_disjoint_bunion; eauto 3 with slow.
      dands; eauto 3 with slow. }

    { repnd.
      eapply equality_respects_cequivc_left;
        [apply cequivc_sym;
          apply simpl_cequivc_mkc_try;
          [exact ee0|apply cequivc_refl]
        |].
      eapply equality_respects_cequivc_right;
        [apply cequivc_sym;
          apply simpl_cequivc_mkc_try;
          [exact ee|apply cequivc_refl]
        |].

      eapply equality_respects_cequivc_left;
        [apply cequivc_sym;
          apply reduces_toc_implies_cequivc;
          apply reduces_toc_mkc_try_exc
        |].
      eapply equality_respects_cequivc_right;
        [apply cequivc_sym;
          apply reduces_toc_implies_cequivc;
          apply reduces_toc_mkc_try_exc
        |].

      allrw @substc_mkcv_axiom.
      apply equality_in_disjoint_bunion; eauto 3 with slow.
      dands; eauto 3 with slow.
      right.
      apply equality_in_unit; dands; spcast; apply computes_to_valc_refl; eauto 3 with slow. }
Qed.

Lemma equality_lam_force_nat_c_in_nat2nat_v2 {o} :
  forall lib x z (f : @CTerm o) T,
    member lib f (nat2T T)
    -> equality lib f (lam_force_nat_c x z f) (nat2T T).
Proof.
  introv mem.

  applydup @inhabited_implies_tequality in mem as teq.
  apply tequality_fun in teq; repnd.
  clear teq0.
  autodimp teq hyp; eauto 2 with slow.

  apply equality_in_fun; dands; eauto 3 with slow.
  introv equ.
  apply equality_in_tnat in equ.
  unfold equality_of_nat in equ; exrepnd; spcast.

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;
      apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply computes_to_valc_implies_cequivc;exact equ1]
    |].

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_apply_lam_force_nat_c|].

  unfold force_nat_c.
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply simpl_cequivc_mkc_cbv;
     apply computes_to_valc_implies_cequivc;exact equ0|].
  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_cbv|]; eauto 3 with slow;[].
  rw @mkcv_less_substc.
  rw @substc_mkcv_zero.
  rw @mkcv_vbot_substc.
  rw @mkcv_apply_substc.
  rw @csubst_mk_cv.
  rw @mkc_var_substc.

  rw @mkc_zero_eq.

  eapply equality_respects_cequivc_right;
    [apply cequivc_sym;apply cequivc_mkc_less_nat|].
  boolvar; tcsp.

  allrw @equality_in_fun; repnd.
  clear mem1 mem0.
  apply mem; eauto 3 with slow.
Qed.

Lemma spM_cond_v2 {o} :
  forall lib (F f : @CTerm o) T,
    member lib F (mkc_fun (nat2T T) mkc_tnat)
    -> member lib f (nat2T T)
    -> {n : nat
        & equality lib
                   (mkc_apply2 (spM_c F) (mkc_nat n) f)
                   (mkc_apply F f)
                   (mkc_bunion mkc_tnat mkc_unit) }.
Proof.
  introv mF mf.

  (* Do we want to constrain the f? *)

  apply equality_in_fun in mF; repnd.
  clear mF0 mF1.
  applydup mF in mf.
  dup mf0 as ma; apply equality_refl in ma.
  apply equality_in_tnat in mf0.
  apply equality_of_nat_imp_tt in mf0.
  unfold equality_of_nat_tt in mf0; exrepnd; GC.

  pose proof (equality_lam_force_nat_c_in_nat2nat_v2 lib nvarx nvarz f T mf) as q.
  applydup mF in q.
  apply equality_in_tnat in q0.
  apply equality_of_nat_imp_tt in q0.
  unfold equality_of_nat_tt in q0; exrepnd; spcast.
  computes_to_eqval.
  allapply @eq_mkc_nat_implies; subst; GC.

  pose proof (exists_bigger_than_list_Z
                (get_ints_from_computes_to_valc
                   lib
                   (mkc_apply F (lam_force_nat_c nvarx nvarz f))
                   (mkc_nat k)
                   q1)) as h; exrepnd.

  exists n.

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;apply cequivc_apply2_spM_c
    |].

  apply equality_in_disjoint_bunion; eauto 3 with slow.
  dands; eauto 3 with slow.
  left.

  rw @test_c_eq.

  destruct (fresh_atom o (getc_utokens F ++ getc_utokens f)) as [a nia].
  allrw in_app_iff; allrw not_over_or; repnd.

  assert (equality
            lib
            (substc (mkc_utoken a) nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat n) f))
            (mkc_apply F f)
            (mkc_tnat)) as comp;
    [|pose proof (cequivc_fresh_subst2 lib nvare (test_try2_cv F nvarc nvarx nvarz nvare (mkc_nat n) f) a) as h;
       repeat (autodimp h hyp);
       [destruct_cterms;allsimpl;
        allunfold @getcv_utokens; allunfold @getc_utokens;
        allsimpl; allrw app_nil_r;
        allrw in_app_iff; complete sp
       |exists (@mkc_nat o k); dands; spcast; tcsp;
        allrw @substc_test_try2_cv;
        apply equality_in_tnat in comp;
        apply equality_of_nat_imp_tt in comp;
        unfold equality_of_nat_tt in comp; exrepnd; auto;
        computes_to_eqval; complete ginv
       |spcast; allrw @substc_test_try2_cv;
        eapply equality_respects_cequivc_left;[apply cequivc_sym;exact h|];
        complete auto
       ]
    ];[].

  allrw @substc_test_try2_cv.

  assert (equality
            lib
            (mkc_apply F (bound2_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
            (mkc_apply F f)
            mkc_tnat) as equ;
    [|apply equality_in_tnat in equ;
       unfold equality_of_nat in equ; exrepnd; spcast;
       eapply equality_respects_cequivc_left;
       [apply cequivc_sym;
         apply computes_to_valc_implies_cequivc;
         eapply computes_to_valc_mkc_try;[exact equ1|];
         apply computes_to_pkc_refl;
         complete (apply mkc_utoken_eq_pk2termc)
       |eapply equality_respects_cequivc_right;
         [apply cequivc_sym;apply computes_to_valc_implies_cequivc;exact equ0|];
         eauto 3 with slow
       ]
    ].

  eapply equality_respects_cequivc_left;
    [apply cequivc_sym;
      apply implies_cequivc_apply;
      [apply cequivc_refl
      |apply cequiv_bound2_c_cbv]
    |].

  apply equality_in_tnat.
  exists k; dands; spcast; auto;[].

  pose proof (reduces_toc_nat_differ_force
                lib
                (mkc_apply F (lam_force_nat_c nvarx nvarz f))
                (mkc_apply F (bound2_cbv_c nvarx nvarz (mkc_nat n) f (mkc_utoken a)))
                k q1 n a f) as h.
  repeat (autodimp h hyp).

  allrw @get_cterm_apply; simpl.
  apply differ_force_oterm; simpl; tcsp.
  introv i; repndors; tcsp; ginv; constructor; eauto 3 with slow.
  apply differ_force_oterm; simpl; tcsp.
  introv i; repndors; tcsp; ginv; constructor; eauto 3 with slow.
  apply differ_force_nat; auto.
Qed.



(* XXXXXXXXXXXXXXXXX *)


Definition has_eq_value_type_nut {o} lib (T : @NTerm o) :=
  forall w s c, eq_value_type_nut lib (lsubstc T w s c).

Definition strong_continuous_type_v2 {o} (x M f n : NVar) (F : @NTerm o) T :=
  mk_sqexists
    (mod_fun_type_v2 x T)
    M
    (mk_all
       (mk_nat2T T)
       f
       (mk_sqexists
          mk_tnat
          n
          (mk_equality
             (mk_apply2 (mk_var M) (mk_var n) (mk_var f))
             (mk_apply F (mk_var f))
             mk_natU))).

Definition rule_strong_continuity_v2 {o}
           (F T t : @NTerm o)
           (x M f n : NVar)
           (H : barehypotheses)
           (i : nat) :=
    mk_rule
      (mk_baresequent H (mk_conclax (strong_continuous_type_v2 x M f n F T)))
      [ mk_baresequent H (mk_conclax (mk_member F (mk_fun (mk_nat2T T) mk_tnat))),
        mk_baresequent H (mk_conclax (mk_member t T)) ]
      [].


Lemma rule_strong_continuity_true_v2 {p} :
  forall lib
         (F T t : NTerm)
         (x M f n : NVar)
         (H : @barehypotheses p)
         (i : nat)
         (d1 : M <> f)
         (d2 : n <> f)
         (d3 : n <> M)
         (d4 : !LIn M (free_vars F))
         (d5 : !LIn f (free_vars F))
         (d6 : !LIn n (free_vars F))
         (d7 : !LIn x (free_vars T))
         (d8 : !LIn M (free_vars T))
         (nut : has_eq_value_type_nut lib T),
    rule_true lib (rule_strong_continuity_v2
                     F T t
                     x M f n
                     H i).
Proof.
  unfold rule_strong_continuity_v2, rule_true, closed_type_baresequent, closed_extract_baresequent; simpl.
  intros.
  clear cargs.

  (* We prove the well-formedness of things *)
  destseq; allsimpl.
  dLin_hyp.
  rename Hyp into hyp1.
  destruct hyp1 as [wc1 hyp1].
  rename Hyp0 into hyp2.
  destruct hyp2 as [wc2 hyp2].
  destseq; allsimpl; proof_irr; GC.
  unfold closed_extract; simpl.

  exists (@covered_axiom p (nh_vars_hyps H)).

  (* We prove some simple facts on our sequents *)
  (* done with proving these simple facts *)

  vr_seq_true.

  vr_seq_true in hyp1.
  pose proof (hyp1 s1 s2 eqh sim) as h; exrepnd; clear hyp1.

  vr_seq_true in hyp2.
  pose proof (hyp2 s1 s2 eqh sim) as hTT; exrepnd; clear hyp2.

  allunfold @strong_continuous_type_v2.
  allunfold @mk_sqexists.
  lsubst_tac.

  apply equality_in_member in hTT1; repnd.
  apply tequality_mkc_member_sp in hTT0; repnd.
  clear hTT0 hTT2 hTT3.

  apply member_if_inhabited in h1.
  apply tequality_mkc_member_sp in h0; repnd.
  allrw @fold_equorsq.
  clear h2.

  lsubst_tac.
  allrw @lsubstc_mkc_tnat.

  eapply member_respects_alphaeqc_r in h1;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].
  eapply respects_alphaeqc_equorsq3 in h0;
    [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
      apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].

  dup h1 as memF.
  eapply cequorsq_equality_trans1 in memF;[|apply equorsq_sym;exact h0].
  apply equality_sym in memF.
  clear h0.

  prove_and teq.

  - apply tequality_mkc_squash.

    unfold mk_exists.
    lsubst_tac.

    apply tequality_product.
    dands.

    + eapply tequality_respects_alphaeqc_left;
      [apply alphaeqc_sym; apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c4 wT cT);auto|].
      eapply tequality_respects_alphaeqc_right;
        [apply alphaeqc_sym; apply (lsubstc_mod_fun_type_v2_aux x T w3 s2 c6 wT cT1);auto|].
      apply tequality_modulus_fun_type_u_v2; auto.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;
        [|apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c4 wT cT);auto].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s2 c13 wT cT1)|].
        apply tequality_nat2T; auto.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;
          [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].
        repeat substc_lsubstc_vars3.
        lsubst_tac.
        apply tequality_mkc_squash.
        allrw @lsubstc_mkc_tnat.

        apply tequality_product; dands; eauto 3 with slow.
        { apply type_tnat. }

        intros n1 n2 en.
        repeat substc_lsubstc_vars3.
        a_lsubst_tac.

        apply tequality_mkc_equality_if_equal.

        { eapply tequality_respects_alphaeqc_left;
          [apply alphaeqc_sym; apply lsubstc_mk_natU|].
          eapply tequality_respects_alphaeqc_right;
            [apply alphaeqc_sym; apply lsubstc_mk_natU|].
          apply type_natU. }

        { eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym; apply lsubstc_mk_natU].

          apply equality_in_function2 in em; repnd.
          clear em0.
          applydup em in en as e.
          eapply alphaeqc_preserving_equality in e;[|apply substc_mkcv_fun].
          rw @csubst_mk_cv in e.

          try (fold (@natU p) in e).
          eapply alphaeqc_preserving_equality in e;
            [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
              apply substc_mkcv_fun].
          eapply alphaeqc_preserving_equality in e;
            [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
              apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
              apply mkcv_natk_substc
            ].
          allrw @mkc_var_substc.
          allrw @mkcv_tnat_substc.

          try (fold (natk2nat n1) in e).

          applydup @equality_refl in en.
          apply (equality_nat2T_to_natk2T lib n1) in en2n; auto;[].

          apply equality_in_fun in e; repnd; clear e0 e1.
          allrw @csubst_mk_cv.
          apply e in en2n.
          allrw <- @mkc_apply2_eq; auto. }

        { eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym; apply lsubstc_mk_natU].
          apply equality_in_fun in memF; repnd; clear memF0 memF1.
          apply memF in en2n; auto.
          apply equality_in_bunion_left; eauto 2 with slow. }

  - apply equality_in_mkc_squash; dands;
    try (spcast; apply computes_to_valc_refl; eauto 3 with slow);[].

    unfold mk_exists.
    lsubst_tac.

    exists (mkc_pair (spM_c (lsubstc F wt0 s1 ct2))
                     (mkc_lam f (mkcv_axiom f))).

    apply equality_in_product.
    dands.

    + eapply type_respects_alphaeqc;
      [apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c4 wT cT);auto|].
      apply tequality_modulus_fun_type_u_v2; eauto 3 with slow.
      eapply tequality_refl; eauto.

    + intros M1 M2 em.
      eapply alphaeqc_preserving_equality in em;
        [|apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c4 wT cT);auto].
      repeat substc_lsubstc_vars3.

      unfold mk_all.
      lsubst_tac.

      apply tequality_function; dands.

      * eapply tequality_respects_alphaeqc_left;
        [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)|].
        eapply tequality_respects_alphaeqc_right;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)|].
        apply tequality_nat2T.
        eapply tequality_refl; eauto.

      * intros f1 f2 en2n.
        eapply alphaeqc_preserving_equality in en2n;
          [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].
        repeat substc_lsubstc_vars3.
        lsubst_tac.
        apply tequality_mkc_squash.
        allrw @lsubstc_mkc_tnat.

        apply tequality_product; dands; eauto 3 with slow.
        { apply type_tnat. }

        intros n1 n2 en.
        repeat substc_lsubstc_vars3.
        a_lsubst_tac.

        apply tequality_mkc_equality_if_equal.

        { eapply tequality_respects_alphaeqc_left;
          [apply alphaeqc_sym; apply lsubstc_mk_natU|].
          eapply tequality_respects_alphaeqc_right;
            [apply alphaeqc_sym; apply lsubstc_mk_natU|].
          apply type_natU. }

        { eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym; apply lsubstc_mk_natU].

          apply equality_in_function2 in em; repnd.
          clear em0.
          applydup em in en as e.
          eapply alphaeqc_preserving_equality in e;[|apply substc_mkcv_fun].
          rw @csubst_mk_cv in e.

          try (fold (@natU p) in e).
          eapply alphaeqc_preserving_equality in e;
            [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
              apply substc_mkcv_fun].
          eapply alphaeqc_preserving_equality in e;
            [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
              apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
              apply mkcv_natk_substc
            ].
          allrw @mkc_var_substc.
          allrw @mkcv_tnat_substc.

          try (fold (natk2nat n1) in e).

          applydup @equality_refl in en.
          apply (equality_nat2T_to_natk2T lib n1) in en2n; auto;[].

          apply equality_in_fun in e; repnd; clear e0 e1.
          allrw @csubst_mk_cv.
          apply e in en2n.
          allrw <- @mkc_apply2_eq; auto. }

        { eapply alphaeqc_preserving_equality;
          [|apply alphaeqc_sym; apply lsubstc_mk_natU].
          apply equality_refl in memF.
          apply equality_in_fun in memF; repnd; clear memF0 memF1.
          apply memF in en2n; auto.
          apply equality_in_bunion_left; eauto 2 with slow. }

    + eexists; eexists; eexists; eexists; dands; spcast;
      try (apply computes_to_valc_refl; eauto 3 with slow).

      * eapply alphaeqc_preserving_equality;
        [|apply alphaeqc_sym;apply (lsubstc_mod_fun_type_v2_aux x T w3 s1 c4 wT cT);auto].

        apply (spM_in_modulus_fun_type_u_v2 _ _ (lsubstc t wt s1 ct1)); auto.

      * repeat substc_lsubstc_vars3.
        unfold mk_all.
        lsubst_tac.

        apply equality_in_function.
        dands.

        { eapply type_respects_alphaeqc;
          [apply alphaeqc_sym;apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)|];
          eauto 3 with slow.
          apply tequality_nat2T; eauto 3 with slow.
          eapply tequality_refl; eauto. }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;
            [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].
          repeat substc_lsubstc_vars3.
          lsubst_tac.
          apply tequality_mkc_squash.
          allrw @lsubstc_mkc_tnat.

          apply tequality_product; dands; eauto 3 with slow.
          { apply type_tnat. }

          intros n1 n2 en.
          repeat substc_lsubstc_vars3.
          a_lsubst_tac.

          apply tequality_mkc_equality_if_equal.

          { eapply tequality_respects_alphaeqc_left;
            [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            eapply tequality_respects_alphaeqc_right;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
            apply type_natU. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].

            pose proof (spM_in_modulus_fun_type_u_v2
                          lib
                          (lsubstc F wt0 s1 ct2)
                          (lsubstc t wt s1 ct1)
                          (lsubstc T wT s1 cT)) as h.
            repeat (autodimp h hyp);[].
            rw @equality_in_function in h; repnd.
            applydup h in en as e.
            eapply alphaeqc_preserving_equality in e;[|apply substc_mkcv_fun].
            rw @csubst_mk_cv in e.

            try (fold (@natU p) in e).
            eapply alphaeqc_preserving_equality in e;
              [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                apply substc_mkcv_fun].
            eapply alphaeqc_preserving_equality in e;
              [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                apply mkcv_natk_substc
              ].
            allrw @mkc_var_substc.
            allrw @mkcv_tnat_substc.

            try (fold (natk2nat n1) in e).

            applydup @equality_refl in en.
            apply (equality_nat2T_to_natk2T lib n1) in en2n; auto;[].

            apply equality_in_fun in e; repnd; clear e0 e1.
            allrw @csubst_mk_cv.
            apply e in en2n.
            allrw <- @mkc_apply2_eq; auto. }

          { eapply alphaeqc_preserving_equality;
            [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            apply equality_refl in memF.
            apply equality_in_fun in memF; repnd; clear memF0 memF1.
            apply memF in en2n; auto.
            apply equality_in_bunion_left; eauto 2 with slow. }
        }

        { intros f1 f2 en2n.
          eapply alphaeqc_preserving_equality in en2n;
            [|apply (lsubstc_mk_nat2T_sp1 T w0 s1 c2 wT cT)].
          repeat substc_lsubstc_vars3.
          lsubst_tac.

          eapply equality_respects_cequivc_left;
            [apply cequivc_sym;apply cequivc_beta|].
          eapply equality_respects_cequivc_right;
            [apply cequivc_sym;apply cequivc_beta|].
          allrw @substc_mkcv_axiom.

          apply equality_in_mkc_squash; dands; spcast;
          try (apply computes_to_valc_refl; eauto 3 with slow);[].

          applydup @equality_refl in en2n as mf1.
          pose proof (spM_cond_v2 lib (lsubstc F wt0 s1 ct2) f1 (lsubstc T wT s1 cT) h1 mf1) as h.
          exrepnd.

          allrw @lsubstc_mkc_tnat.

          exists (mkc_pair (mkc_nat n0) (@mkc_axiom p)).

          apply equality_in_product; dands; eauto 3 with slow.

          - intros n1 n2 en.
            repeat substc_lsubstc_vars3.
            a_lsubst_tac.

            apply tequality_mkc_equality_if_equal.

            { eapply tequality_respects_alphaeqc_left;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              eapply tequality_respects_alphaeqc_right;
              [apply alphaeqc_sym; apply lsubstc_mk_natU|].
              apply type_natU. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].

              pose proof (spM_in_modulus_fun_type_u_v2
                            lib
                            (lsubstc F wt0 s1 ct2)
                            (lsubstc t wt s1 ct1)
                            (lsubstc T wT s1 cT)) as h.
              repeat (autodimp h hyp);[].
              rw @equality_in_function in h; repnd.
              applydup h in en as e.
              eapply alphaeqc_preserving_equality in e;[|apply substc_mkcv_fun].
              rw @csubst_mk_cv in e.

              try (fold (@natU p) in e).
              eapply alphaeqc_preserving_equality in e;
                [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                  apply substc_mkcv_fun].
              eapply alphaeqc_preserving_equality in e;
                [|apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                  apply alphaeqc_mkc_fun;[|apply alphaeqc_refl];
                  apply mkcv_natk_substc
                ].
              allrw @mkc_var_substc.
              allrw @mkcv_tnat_substc.
              allrw @csubst_mk_cv.

              try (fold (natk2T n1 (lsubstc T wT s1 cT)) in e).

              applydup @equality_refl in en.
              apply (equality_nat2T_to_natk2T lib n1) in en2n; auto;[].

              apply equality_in_fun in e; repnd; clear e0 e1.
              applydup @equality_refl in en2n as ef.
              allrw @csubst_mk_cv.
              apply e in ef.
              allrw <- @mkc_apply2_eq; auto. }

            { eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
              apply equality_refl in memF.
              apply equality_in_fun in memF; repnd; clear memF0 memF1.
              apply memF in en2n; auto.
              apply equality_in_bunion_left; eauto 2 with slow. }

          - eexists; eexists; eexists; eexists; dands; spcast;
            try (apply computes_to_valc_refl; eauto 3 with slow);
            eauto 3 with slow.

            repeat substc_lsubstc_vars3.
            a_lsubst_tac.

            apply member_equality.
            eapply alphaeqc_preserving_equality;
              [|apply alphaeqc_sym; apply lsubstc_mk_natU].
            auto.
        }
Qed.
