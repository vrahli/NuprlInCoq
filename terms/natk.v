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


Require Export cvterm.
Require Export alphaeq.
Require Export list.  (* WTF!!! *)


Lemma wf_less_than {o} :
  forall (a b : @NTerm o),
    wf_term (mk_less_than a b) <=> (wf_term a # wf_term b).
Proof.
  introv.
  unfold mk_less_than.
  rw <- @wf_less_iff; split; intro k; repnd; dands; eauto 3 with slow.
Qed.

Lemma wf_le {o} :
  forall (a b : @NTerm o),
    wf_term (mk_le a b) <=> (wf_term a # wf_term b).
Proof.
  introv.
  unfold mk_le.
  rw @wf_not.
  rw @wf_less_than; dands; split; sp.
Qed.

Lemma wf_term_mk_natk {o} :
  forall (t : @NTerm o), wf_term (mk_natk t) <=> wf_term t.
Proof.
  introv.
  unfold mk_natk, mk_natk_aux.
  rw <- @wf_set_iff.
  rw @wf_prod.
  rw @wf_le.
  rw @wf_less_than.
  split; introv k; repnd; dands; eauto 3 with slow.
Qed.

Lemma cover_vars_upto_product {o} :
  forall vs (a : @NTerm o) v b sub,
    cover_vars_upto (mk_product a v b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b (csub_filter sub [v]) (v :: vs).
Proof.
  sp; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw subvars_prop; simpl; split; sp; apply_in_hyp pp;
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  generalize (deq_nvar v x); intro q; sp.
  right; right; sp.
Qed.

Lemma cover_vars_upto_prod {o} :
  forall vs (a b : @NTerm o) sub,
    cover_vars_upto (mk_prod a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  introv.
  rw @cover_vars_upto_product.
  split; intro k; repnd; dands; auto.
  - allunfold @cover_vars_upto.
    allrw subvars_prop; introv i.
    applydup k in i; allsimpl; allrw in_app_iff; repndors; subst; tcsp.
    + pose proof (newvar_prop b); sp.
    + rw @dom_csub_csub_filter in i0.
      rw in_remove_nvars in i0; sp.
  - allunfold @cover_vars_upto.
    allrw subvars_prop; introv i.
    applydup k in i; allsimpl; allrw in_app_iff; repndors; tcsp.
    rw @dom_csub_csub_filter.
    rw in_remove_nvars; simpl.
    destruct (deq_nvar (newvar b) x) as [j|j]; subst; tcsp.
    right; right; sp.
Qed.

Lemma cover_vars_upto_less {o} :
  forall vs (a b c d : @NTerm o) sub,
    cover_vars_upto (mk_less a b c d) sub vs
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

Lemma cover_vars_upto_mk_true {o} :
  forall (sub : @CSub o) vs, cover_vars_upto mk_true sub vs.
Proof.
  introv; unfold cover_vars_upto; simpl; auto.
Qed.
Hint Resolve cover_vars_upto_mk_true : slow.

Lemma cover_vars_upto_less_than {o} :
  forall vs (a b : @NTerm o) sub,
    cover_vars_upto (mk_less_than a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  introv.
  rw @cover_vars_upto_less.
  split; introv k; repnd; dands; eauto 3 with slow; tcsp.
Qed.

Lemma cover_vars_upto_not {o} :
  forall vs (a : @NTerm o) sub,
    cover_vars_upto (mk_not a) sub vs
    <=> cover_vars_upto a sub vs.
Proof.
  introv.
  unfold mk_not.
  rw @cover_vars_upto_fun; split; introv k; repnd; dands; eauto 3 with slow.
Qed.

Lemma cover_vars_upto_le {o} :
  forall vs (a b : @NTerm o) sub,
    cover_vars_upto (mk_le a b) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b sub vs.
Proof.
  introv.
  unfold mk_le.
  rw @cover_vars_upto_not.
  rw @cover_vars_upto_less_than.
  split; sp.
Qed.

Lemma cover_vars_mk_int {o} :
  forall (s : @CSub o), cover_vars mk_int s.
Proof.
  introv.
  rw @cover_vars_eq; simpl; auto.
Qed.
Hint Resolve cover_vars_mk_int : slow.

Lemma cover_vars_upto_mk_zero {o} :
  forall (s : @CSub o) vs, cover_vars_upto mk_zero s vs.
Proof.
  introv.
  unfold cover_vars_upto; simpl; auto.
Qed.
Hint Resolve cover_vars_upto_mk_zero : slow.

Lemma cover_vars_mk_natk {o} :
  forall (t : @NTerm o) s,
    cover_vars (mk_natk t) s <=> cover_vars t s.
Proof.
  introv.
  unfold mk_natk, mk_natk_aux.
  rw @cover_vars_set.
  rw @cover_vars_upto_prod.
  rw @cover_vars_upto_le.
  rw @cover_vars_upto_less_than.
  split; introv k; repnd; dands; eauto 3 with slow; tcsp;
  try (complete (apply cover_vars_upto_var; simpl; tcsp)).

  - unfold cover_vars_upto in k; allsimpl.
    rw @cover_vars_eq.
    apply subvars_cons_r_weak_if_not_in in k;[|apply newvar_prop].
    rw @dom_csub_csub_filter in k.
    eapply subvars_trans;[exact k|].
    rw subvars_prop; introv i; allsimpl; allrw in_remove_nvars; tcsp.

  - unfold cover_vars_upto; allsimpl.
    rw @cover_vars_eq in k.
    rw @dom_csub_csub_filter.
    eapply subvars_trans;[exact k|].
    rw subvars_prop; introv i; allsimpl; allrw in_remove_nvars; allsimpl.
    destruct (deq_nvar (newvar t) x); tcsp.
    right; sp.
Qed.

Lemma cover_vars_mk_tnat {o} :
  forall (s : @CSub o), cover_vars mk_tnat s.
Proof.
  introv.
  unfold mk_tnat.
  rw @cover_vars_set; dands; eauto 3 with slow.
  apply cover_vars_upto_le; dands; eauto 3 with slow.
  apply cover_vars_upto_var; simpl; sp.
Qed.
Hint Resolve cover_vars_mk_tnat : slow.

Lemma sub_find_sub_filter_trivial {o} :
  forall (s : @Sub o) x, sub_find (sub_filter s [x]) x = None.
Proof.
  introv.
  rw @sub_find_sub_filter_eq; rw memvar_singleton; boolvar; auto.
Qed.

Lemma sub_find_sub_filter_trivial2 {o} :
  forall (s : @Sub o) x y, sub_find (sub_filter (sub_filter s [x]) [y]) x = None.
Proof.
  introv.
  allrw @sub_find_sub_filter_eq.
  allrw memvar_singleton; boolvar; auto.
Qed.

Lemma beq_var_newvar_trivial1 {o} :
  forall v (t : @NTerm o),
    LIn v (free_vars t)
    -> beq_var v (newvar t) = false.
Proof.
  introv i; boolvar; auto.
  pose proof (newvar_prop t) as h; allsimpl; allrw not_over_or; tcsp.
Qed.
