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

  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export cvterm.
Require Export computation3.
Require Export substitution3.
Require Export natk.
Require Export alphaeq3.
Require Export List.


Definition mkcv_free_from_atom {p} vs (t1 t2 t3 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
  exist
    (isprog_vars vs)
    (mk_free_from_atom a b c)
    (isprog_vars_free_from_atom vs a b c x y z).

Definition mkcv_free_from_atoms {p} vs (t1 t2 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  exist
    (isprog_vars vs)
    (mk_free_from_atoms a b)
    (isprog_vars_free_from_atoms vs a b x y).

Definition mkcv_base {o} vs : @CVTerm o vs := mk_cv vs mkc_base.

Definition mkcv_uatom {o} vs : @CVTerm o vs := mk_cv vs mkc_uatom.

Definition mk_ffatoms {o} (t : @NTerm o) : NTerm := mk_free_from_atoms mk_base t.
Definition mkc_ffatoms {o} (t : @CTerm o) : CTerm := mkc_free_from_atoms mkc_base t.

Definition mkcv_ffatoms {o} vs (t : @CVTerm o vs) : CVTerm vs :=
  mkcv_free_from_atoms vs (mkcv_base vs) t.

Definition mk_nout {o} : @NTerm o :=
  mk_set
    mk_base
    nvary
    (mk_ffatoms (mk_var nvary)).

Definition mkc_nout {o} : @CTerm o :=
  mkc_set
    mkc_base
    nvary
    (mkcv_ffatoms [nvary] (mkc_var nvary)).

Lemma mkcv_free_from_atom_substc {o} :
  forall v a b c (t : @CTerm o),
    substc t v (mkcv_free_from_atom [v] a b c)
    = mkc_free_from_atom (substc t v a) (substc t v b) (substc t v c).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma mkcv_ffatoms_substc {o} :
  forall v a (t : @CTerm o),
    substc t v (mkcv_ffatoms [v] a)
    = mkc_ffatoms (substc t v a).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma substc_mkcv_base {o} :
  forall (v : NVar) (t : @CTerm o),
    substc t v (mkcv_base [v]) = mkc_base.
Proof.
  introv.
  unfold mkcv_base.
  allrw @csubst_mk_cv; auto.
Qed.

Definition nat2nout {o} : @CTerm o := mkc_fun mkc_tnat mkc_nout.
Definition natk2nout {o} (t : @CTerm o) : @CTerm o := mkc_fun (mkc_natk t) mkc_nout.

Definition mk_nat2nout {o} : @NTerm o := mk_fun mk_tnat mk_nout.
Definition mk_natk2nout {o} (t : @NTerm o) : NTerm := mk_fun (mk_natk t) mk_nout.

Lemma lsubstc_mk_nout {o} :
  forall sub (w : wf_term (@mk_nout o))
         (c : cover_vars mk_nout sub),
    lsubstc mk_nout w sub c
    = mkc_nout.
Proof.
  introv.
  apply cterm_eq; simpl.
  unfold csubst.
  unflsubst; simpl.
  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton; boolvar; tcsp.
Qed.

Lemma lsubstc_mk_nat2nout {o} :
  forall sub (w : wf_term (@mk_nat2nout o))
         (c : cover_vars mk_nat2nout sub),
    lsubstc mk_nat2nout w sub c
    = nat2nout.
Proof.
  introv.
  apply cterm_eq; simpl.
  unfold csubst.
  unflsubst; simpl.
  allrw @sub_filter_nil_r.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton; boolvar; tcsp.
Qed.

Lemma cover_vars_mk_nout {o} :
  forall (s : @CSub o), cover_vars mk_nout s.
Proof.
  introv.
  unfold mk_nout.
  apply cover_vars_set; dands; eauto 3 with slow.
  unfold mk_ffatoms.
  apply cover_vars_upto_free_from_atoms; dands; eauto 3 with slow.
  apply cover_vars_upto_var; simpl; tcsp.
Qed.
Hint Resolve cover_vars_mk_nout : slow.

Lemma wf_term_mk_natk2nout {o} :
  forall (t : @NTerm o),
    wf_term (mk_natk2nout t) <=> wf_term t.
Proof.
  introv.
  unfold mk_natk2nout.
  rw @wf_fun_iff.
  rw @wf_term_mk_natk.
  split; tcsp.
Qed.

Lemma wf_term_mk_natk2nout_implies {o} :
  forall (t : @NTerm o),
    wf_term (mk_natk2nout t) -> wf_term t.
Proof.
  introv w.
  rw @wf_term_mk_natk2nout in w; auto.
Qed.

Lemma cover_vars_mk_natk2nout {o} :
  forall (t : @NTerm o) s,
    cover_vars (mk_natk2nout t) s <=> cover_vars t s.
Proof.
  introv.
  unfold mk_natk2nout.
  rw @cover_vars_fun.
  rw @cover_vars_mk_natk.
  split; intro k; repnd; dands; eauto 3 with slow.
Qed.

Lemma cover_vars_mk_natk2nout_implies {o} :
  forall (t : @NTerm o) s,
    cover_vars (mk_natk2nout t) s -> cover_vars t s.
Proof.
  introv cv.
  rw @cover_vars_mk_natk2nout in cv; auto.
Qed.

Lemma wf_term_mk_nat2nout {o} :
  @wf_term o mk_nat2nout.
Proof.
  introv.
  unfold mk_nat2nout.
  rw @wf_fun_iff; dands; tcsp.
Qed.
Hint Resolve wf_term_mk_nat2nout : slow.

Lemma cover_vars_mk_nat2nout {o} :
  forall (s : @CSub o), cover_vars mk_nat2nout s.
Proof.
  introv.
  unfold mk_nat2nout.
  rw @cover_vars_fun.
  dands; eauto 3 with slow.
Qed.
Hint Resolve cover_vars_mk_nat2nout : slow.

Lemma cover_vars_var_iff {o} :
  forall (v : NVar) (sub : @CSub o),
    cover_vars (mk_var v) sub <=> LIn v (dom_csub sub).
Proof.
  introv; split; introv h; try (apply cover_vars_var;auto).
  rw @cover_vars_eq in h; allsimpl.
  allrw subvars_singleton_l; auto.
Qed.

Lemma lsubstc_mk_natk2nout_sp1 {o} :
  forall v (t : @CTerm o) w s c,
    alphaeqc
      (lsubstc (mk_natk2nout (mk_var v)) w ((v,t) :: s) c)
      (natk2nout t).
Proof.
  Opaque beq_var.
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
  repeat (destruct n; tcsp; try lia); clear j;[].
  apply alphaeqbt_nilv2.

  unfold mk_natk, mk_natk_aux, mk_set, nobnd.
  prove_alpha_eq4;[].
  introv j.
  repeat (destruct n; tcsp; try lia); clear j;[].

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

  repeat (rw (lsubst_aux_trivial_cl_term2 x); eauto 3 with slow;[]).

  unfold mk_product, nobnd.
  prove_alpha_eq4.
  introv j.
  repeat (destruct n; tcsp; try lia); clear j;[|].

  { apply alphaeqbt_nilv2.

    unfold mk_function, nobnd.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try lia); clear j;[|].

    { apply alphaeqbt_nilv2.
      unfold mk_less, nobnd.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try lia); clear j;[].

      apply alphaeqbt_nilv2.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try lia); clear j;[].

      apply alphaeqbt_nilv2.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try lia); clear j;[].

      apply alphaeqbt_nilv2.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try lia); clear j;[].

      apply alpha_eq_bterm_congr.
      repeat (boolvar; simpl); tcsp.
    }

    { apply alpha_eq_bterm_congr.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try lia); clear j;[].

      apply alpha_eq_bterm_congr.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try lia); clear j;[].

      apply alpha_eq_bterm_congr.
      prove_alpha_eq4.
      introv j.
      repeat (destruct n; tcsp; try lia); clear j;[].

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

    repeat (rw (lsubst_aux_trivial_cl_term2 x); eauto 3 with slow;[]).

    unfold mk_less, nobnd.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try lia); clear j;[].

    apply alpha_eq_bterm_congr.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try lia); clear j;[].

    apply alpha_eq_bterm_congr.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try lia); clear j;[].

    apply alpha_eq_bterm_congr.
    prove_alpha_eq4.
    introv j.
    repeat (destruct n; tcsp; try lia); clear j;[].

    apply alpha_eq_bterm_congr.
    repeat (boolvar; subst; simpl; tcsp);
      try (complete (rw not_over_or in Heqb; tcsp));
      try (complete (rw not_over_or in Heqb0; tcsp)).
  }
Qed.

Lemma free_vars_mk_natk2nout {o} :
  forall v, @free_vars o (mk_natk2nout (mk_var v)) = [v].
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

Lemma lsubstc_mk_natk2nout_sp2 {o} :
  forall v (t : @CTerm o) w s c,
    !LIn v (dom_csub s)
    -> alphaeqc
         (lsubstc (mk_natk2nout (mk_var v)) w (snoc s (v,t)) c)
         (natk2nout t).
Proof.
  introv niv.

  assert (cover_vars (mk_natk2nout (mk_var v)) ((v, t) :: s)) as cv.
  { allrw @cover_vars_mk_natk2nout.
    allrw @cover_vars_var_iff.
    allsimpl.
    allrw @dom_csub_snoc; allsimpl.
    allrw in_snoc; sp. }

  pose proof (lsubstc_mk_natk2nout_sp1 v t w s cv) as h.
  eapply alphaeqc_trans;[|exact h].

  unfold alphaeqc; simpl.
  apply alpha_eq_lsubst_if_ext_eq; auto.
  unfold ext_alpha_eq_subs.
  rw @free_vars_mk_natk2nout; simpl.
  introv e; repndors; tcsp; subst.
  boolvar; tcsp.
  rw @csub2sub_snoc.
  rw @sub_find_snoc.
  boolvar.
  rw @sub_find_none_if; eauto 3 with slow.
  rw @dom_csub_eq; auto.
Qed.


(*
Lemma lsubstc_mk_natk2nout {o} :
  forall (t  : @NTerm o) sub
         (w  : wf_term t)
         (w' : wf_term (mk_natk2nout t))
         (c  : cover_vars t sub)
         (c' : cover_vars (mk_natk2nout t) sub),
    alphaeqc (lsubstc (mk_natk2nout t) w' sub c')
             (natk2nout (lsubstc t w sub c)).
Proof.
  introv.
  unfold alphaeqc; simpl.
  unfold csubst; unflsubst; simpl.
  autorewrite with slow.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton.
  allrw <- beq_var_refl.
  fold_terms.
  boolvar;[|].

  { provefalse.
    pose proof (newvar_prop (mk_less_than (mk_var (newvar t)) t)) as np.
    rw <- Heqb in np; allsimpl.
    allrw not_over_or; sp. }

  constructor; simpl; auto.
  introv ltn.
  repeat (destruct n; try lia);unfold selectbt; simpl;
  eauto 3 with slow;[].

  apply alphaeqbt_nilv2.

  SearchAbout mk_natk.

  unfold mk_natk, mk_natk_aux.
  f_equal.
  f_equal.

  apply alphaeq_function_fun.

  SearchAbout newvar.
Qed.
*)
