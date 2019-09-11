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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export csubst.

Lemma lsubstc_mk_decide {p} :
  forall t1 x u y v sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p u,
  forall w3 : @wf_term p v,
  forall w  : wf_term (mk_decide t1 x u y v),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto u (csub_filter sub [x]) [x],
  forall c3 : cover_vars_upto v (csub_filter sub [y]) [y],
  forall c  : cover_vars (mk_decide t1 x u y v) sub,
    lsubstc (mk_decide t1 x u y v) w sub c
    = mkc_decide (lsubstc t1 w1 sub c1)
                 x
                 (lsubstc_vars u w2 (csub_filter sub [x]) [x] c2)
                 y
                 (lsubstc_vars v w3 (csub_filter sub [y]) [y] c3).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub.
  rw @fold_decide; sp.
Qed.

Lemma cover_vars_decide {p} :
  forall a v1 t1 v2 t2 sub,
    cover_vars (@mk_decide p a v1 t1 v2 t2) sub
    <=> cover_vars a sub
        # cover_vars_upto t1 (csub_filter sub [v1]) [v1]
        # cover_vars_upto t2 (csub_filter sub [v2]) [v2].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  assert (v1 :: remove_nvars [v1] (dom_csub sub)
          = [v1] ++ remove_nvars [v1] (dom_csub sub)) as eq1 by auto.
  assert (v2 :: remove_nvars [v2] (dom_csub sub)
          = [v2] ++ remove_nvars [v2] (dom_csub sub)) as eq2 by auto.
  rw eq1; rw eq2.
  allrw  subvars_app_remove_nvars_r.
  rw (subvars_swap_r [v1]). rw (subvars_swap_r [v2]). sp.
Qed.

Lemma lsubstc_mk_decide_ex {p} :
  forall t1 x u y v sub,
  forall w  : wf_term (@mk_decide p t1 x u y v),
  forall c  : cover_vars (mk_decide t1 x u y v) sub,
    {w1 : wf_term t1
     & {w2 : wf_term u
     & {w3 : wf_term v
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto u (csub_filter sub [x]) [x]
     & {c3 : cover_vars_upto v (csub_filter sub [y]) [y]
        & lsubstc (mk_decide t1 x u y v) w sub c
          = mkc_decide (lsubstc t1 w1 sub c1)
                       x 
                       (lsubstc_vars u w2 (csub_filter sub [x]) [x] c2)
                       y
                       (lsubstc_vars v w3 (csub_filter sub [y]) [y] c3)}}}}}}.
Proof.
  sp.

  duplicate w.
  rw @wf_decide in w; sp.

  duplicate c.
  rw @cover_vars_decide in c; sp.

  exists w1 w2 w c1 c2 c.
  apply lsubstc_mk_decide.
Qed.

Lemma lsubstc_mk_inl {p} :
  forall t1 sub,
  forall w1 : @wf_term p t1,
  forall w  : wf_term (mk_inl t1),
  forall c1 : cover_vars t1 sub, 
  forall c  : cover_vars (mk_inl t1) sub,
    lsubstc (mk_inl t1) w sub c
    = mkc_inl (lsubstc t1 w1 sub c1).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub; sp. 
Qed.

Lemma cover_vars_inl {p} :
  forall a sub,
    cover_vars (@mk_inl p a ) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter; sp.
Qed.

Lemma lsubstc_mk_inl_ex {p} :
  forall t1 sub,
  forall w  : wf_term (@mk_inl p t1),
  forall c  : cover_vars (mk_inl t1 ) sub,
    {w1 : wf_term t1
     & {c1 : cover_vars t1 sub
        & lsubstc (mk_inl t1 ) w sub c
          = mkc_inl (lsubstc t1 w1 sub c1)}}.
Proof.
  sp.

  duplicate w.
  rw @wf_inl in w; sp.

  duplicate c.
  rw @cover_vars_inl in c; sp.

  exists w c.
  apply lsubstc_mk_inl.
Qed.


Lemma lsubstc_mk_inr {p} :
  forall t1 sub,
  forall w1 : @wf_term p t1,
  forall w  : wf_term (mk_inr t1),
  forall c1 : cover_vars t1 sub, 
  forall c  : cover_vars (mk_inr t1) sub,
    lsubstc (mk_inr t1) w sub c
    = mkc_inr (lsubstc t1 w1 sub c1).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub; sp. 
Qed.

Lemma cover_vars_inr {p} :
  forall a sub,
    cover_vars (@mk_inr p a ) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter; sp.
Qed.

Lemma lsubstc_mk_inr_ex {p} :
  forall t1 sub,
  forall w  : wf_term (@mk_inr p t1),
  forall c  : cover_vars (mk_inr t1 ) sub,
    {w1 : wf_term t1
     & {c1 : cover_vars t1 sub
        & lsubstc (mk_inr t1 ) w sub c
          = mkc_inr (lsubstc t1 w1 sub c1)}}.
Proof.
  sp.

  duplicate w.
  rw @wf_inr in w; sp.

  duplicate c.
  rw @cover_vars_inr in c; sp.

  exists w c.
  apply lsubstc_mk_inr.
Qed.

Definition mkc_outl {p} (t : @CTerm p) : CTerm :=
  let (a,x) := t in exist isprog (mk_outl a) (isprog_outl a x).

Lemma cover_vars_outl {p} :
  forall a sub,
    cover_vars (@mk_outl p a ) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter; sp.
Qed.

Lemma wf_outl {p} :
  forall a : @NTerm p, wf_term (mk_outl a) <=> wf_term a.
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| o l bw e]; subst.
  generalize (bw (nobnd a)); simpl; intros bw1.
  autodimp bw1 hyp.
  inversion bw1; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Definition mkc_outr {p} (t : @CTerm p) : CTerm :=
  let (a,x) := t in exist isprog (mk_outr a) (isprog_outr a x).

Lemma cover_vars_outr {p} :
  forall a sub,
    cover_vars (@mk_outr p a ) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter; sp.
Qed.

Lemma wf_outr {p} :
  forall a : @NTerm p, wf_term (mk_outr a) <=> wf_term a.
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| o l bw e]; subst.
  generalize (bw (nobnd a)); simpl; intros bw1.
  autodimp bw1 hyp.
  inversion bw1; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma lsubstc_mk_outl {p} :
  forall t1 sub,
  forall w1 : @wf_term p t1,
  forall w  : wf_term (mk_outl t1),
  forall c1 : cover_vars t1 sub, 
  forall c  : cover_vars (mk_outl t1) sub,
    lsubstc (mk_outl t1) w sub c
    = mkc_outl (lsubstc t1 w1 sub c1).
Proof.
  introv.
  unfold mk_outl, mkc_outl; simpl.

  pose proof (lsubstc_mk_decide_ex t1 nvarx (mk_var nvarx) nvary mk_bot sub w c) as e.
  exrepnd; rw e1; clear e1.
  apply cterm_eq; simpl.
  unfold mk_outl, mk_bot; allrw @csubst_mk_bottom.
  f_equal.
  apply csubst_var_not_in.
  rw @dom_csub_csub_filter; rw in_remove_nvars; simpl; tcsp.
Qed. 

Lemma lsubstc_mk_outl_ex {p} :
  forall t1 sub,
  forall w  : wf_term (@mk_outl p t1),
  forall c  : cover_vars (mk_outl t1 ) sub,
    {w1 : wf_term t1
     & {c1 : cover_vars t1 sub
        & lsubstc (mk_outl t1 ) w sub c
          = mkc_outl (lsubstc t1 w1 sub c1)}}.
Proof.
  sp.

  duplicate w.
  rw @wf_outl in w; sp.

  duplicate c.
  rw @cover_vars_inl in c; sp.

  exists w c.
  apply lsubstc_mk_outl.
Qed.

Lemma lsubstc_mk_outr {p} :
  forall t1 sub,
  forall w1 : @wf_term p t1,
  forall w  : wf_term (mk_outr t1),
  forall c1 : cover_vars t1 sub, 
  forall c  : cover_vars (mk_outr t1) sub,
    lsubstc (mk_outr t1) w sub c
    = mkc_outr (lsubstc t1 w1 sub c1).
Proof.
  introv.
  unfold mk_outr, mkc_outr; simpl.

  pose proof (lsubstc_mk_decide_ex t1 nvarx mk_bot nvary (mk_var nvary) sub w c) as e.
  exrepnd; rw e1; clear e1.
  apply cterm_eq; simpl.
  unfold mk_outr, mk_bot; allrw @csubst_mk_bottom.
  f_equal.
  apply csubst_var_not_in.
  rw @dom_csub_csub_filter; rw in_remove_nvars; simpl; tcsp.
Qed. 

Lemma lsubstc_mk_outr_ex {p} :
  forall t1 sub,
  forall w  : wf_term (@mk_outr p t1),
  forall c  : cover_vars (mk_outr t1 ) sub,
    {w1 : wf_term t1
     & {c1 : cover_vars t1 sub
        & lsubstc (mk_outr t1 ) w sub c
          = mkc_outr (lsubstc t1 w1 sub c1)}}.
Proof.
  sp.

  duplicate w.
  rw @wf_outr in w; sp.

  duplicate c.
  rw @cover_vars_inl in c; sp.

  exists w c.
  apply lsubstc_mk_outr.
Qed.
