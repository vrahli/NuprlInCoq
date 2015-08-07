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


Require Export csubst.


Definition bot_exc {o} : @NTerm o := mk_exception mk_bot mk_bot.
Definition bot_excc {o} : @CTerm o := mkc_exception mkc_bot mkc_bot.

Definition mk_isexc {o} (t : @NTerm o) : @NTerm o := mk_approx bot_exc t.

Lemma fold_isexc {p} :
  forall (t : @NTerm p),
    mk_approx bot_exc t = mk_isexc t.
Proof. sp. Qed.

Lemma wf_bot_exc {o} : @wf_term o bot_exc.
Proof.
  unfold bot_exc.
  apply wf_exception; eauto 3 with slow.
Qed.
Hint Resolve wf_bot_exc : slow.

Lemma wf_isexc {p} :
  forall a : @NTerm p, wf_term a -> wf_term (mk_isexc a).
Proof.
  sp; unfold mk_isexc.
  allrw @wf_term_eq.
  constructor; repeat (allsimpl; sp; subst; repeat constructor).
Qed.

Lemma wf_isexc_iff {p} :
  forall a : @NTerm p, wf_term a <=> wf_term (mk_isexc a).
Proof.
  sp; split; intro i.
  apply wf_isexc; sp.
  allrw @wf_term_eq.
  allrw @nt_wf_eq.
  apply wf_approx_iff in i; sp.
Qed.

Lemma isprogram_bot_exc {o} : @isprogram o bot_exc.
Proof.
  introv.
  apply isprogram_exception; eauto 3 with slow.
Qed.
Hint Resolve isprogram_bot_exc : slow.

Lemma isprogram_isexc {p} :
  forall t : @NTerm p,
    isprogram t
    -> isprogram (mk_isexc t).
Proof.
  unfold mk_isexc; introv isp.
  apply isprogram_approx; eauto 3 with slow.
Qed.

Lemma isprog_isexc {p} :
  forall t : @NTerm p,
    isprog t
    -> isprog (mk_isexc t).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_isexc; sp.
Qed.

Definition mkc_isexc {p} (t : @CTerm p) : CTerm :=
  let (a,x) := t in
    exist isprog (mk_isexc a) (isprog_isexc a x).

Lemma isprog_vars_isexc {p} :
  forall vs (a : @NTerm p), isprog_vars vs (mk_isexc a) <=> isprog_vars vs a.
Proof.
  introv.
  allrw @isprog_vars_eq; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw @nt_wf_eq.
  allrw <- @wf_isexc_iff; sp.
Qed.

Lemma cover_vars_isexc {p} :
  forall a sub,
    @cover_vars p (mk_isexc a) sub
    <=> cover_vars a sub.
Proof.
  sp; unfold mk_isexc; split; sp; allrw @cover_vars_eq; allsimpl;
  allrw remove_nvars_nil_l; allrw app_nil_r;
  allrw subvars_app_l; sp.
Qed.

Lemma csubst_bot_exc {o} :
  forall (sub : @CSub o), csubst bot_exc sub = bot_exc.
Proof.
  introv.
  apply csubst_trivial.
  simpl; auto.
Qed.

Lemma lsubstc_bot_exc {o} :
  forall (sub : @CSub o)
         (w  : wf_term bot_exc)
         (c  : cover_vars bot_exc sub),
    lsubstc bot_exc w sub c = bot_excc.
Proof.
  introv.
  pose proof (lsubstc_mk_exception_ex mk_bot mk_bot sub w c) as h; exrepnd.
  unfold bot_exc.
  rw h1; clear h1.
  allrw @lsubstc_mk_bot; auto.
Qed.

Lemma lsubstc_vars_bot_exc {o} :
  forall (sub : @CSub o)
         (w  : wf_term bot_exc)
         (vs : list NVar)
         (c  : cover_vars_upto bot_exc sub vs),
    lsubstc_vars bot_exc w sub vs c = mk_cv vs bot_excc.
Proof.
  introv.
  apply cvterm_eq; simpl.
  rw @csubst_bot_exc; auto.
Qed.

Lemma lsubstc_mk_isexc {p} :
  forall t sub,
  forall wt : @wf_term p t,
  forall w  : wf_term (mk_isexc t),
  forall ct : cover_vars t sub,
  forall c  : cover_vars (mk_isexc t) sub,
    lsubstc (mk_isexc t) w sub c
    = mkc_isexc (lsubstc t wt sub ct).
Proof.
  unfold mk_isexc; sp.
  pose proof (lsubstc_mk_approx_ex bot_exc t sub w c) as h.
  exrepnd.
  rw h1; clear h1.
  rw @lsubstc_bot_exc.
  apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_isexc_ex {p} :
  forall t sub,
  forall w  : wf_term (@mk_isexc p t),
  forall c  : cover_vars (mk_isexc t) sub,
    {wt : wf_term t
     & {ct : cover_vars t sub
        & lsubstc (mk_isexc t) w sub c
             = mkc_isexc (lsubstc t wt sub ct)}}.
Proof.
  sp.
  duplicate w; duplicate c.
  rw <- @wf_isexc_iff in w.
  rw @cover_vars_isexc in c.
  exists w c.
  apply lsubstc_mk_isexc.
Qed.

Lemma mkc_isexc_eq {o} :
  forall (t : @CTerm o), mkc_isexc t = mkc_approx bot_excc t.
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl; auto.
Qed.


Definition mk_halts_like {o} (t : @NTerm o) : @NTerm o :=
  mk_approx bot_exc (mk_cbv t nvarx bot_exc).

Lemma fold_halts_like {p} :
  forall (t : @NTerm p),
    mk_approx bot_exc (mk_cbv t nvarx bot_exc) = mk_halts_like t.
Proof. sp. Qed.

Lemma wf_halts_like {p} :
  forall a : @NTerm p, wf_term a -> wf_term (mk_halts_like a).
Proof.
  introv wf; unfold mk_halts_like.
  apply wf_approx; eauto 3 with slow.
  apply wf_cbv; eauto 3 with slow.
Qed.

Lemma wf_halts_like_iff {p} :
  forall a : @NTerm p, wf_term a <=> wf_term (mk_halts_like a).
Proof.
  sp; split; intro i.
  apply wf_halts_like; sp.
  unfold mk_halts_like in i.
  apply wf_approx_iff in i; repnd.
  apply wf_cbv_iff in i; sp.
Qed.

Lemma isprogram_halts_like {p} :
  forall t : @NTerm p,
    isprogram t
    -> isprogram (mk_halts_like t).
Proof.
  unfold mk_halts_like; introv isp.
  apply isprogram_approx; eauto 3 with slow.
  apply isprogram_cbv; eauto 3 with slow.
Qed.

Lemma isprog_halts_like {p} :
  forall t : @NTerm p,
    isprog t
    -> isprog (mk_halts_like t).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_halts_like; sp.
Qed.

Definition mkc_halts_like {p} (t : @CTerm p) : CTerm :=
  let (a,x) := t in
    exist isprog (mk_halts_like a) (isprog_halts_like a x).

Lemma isprog_vars_halts_like {p} :
  forall vs (a : @NTerm p), isprog_vars vs (mk_halts_like a) <=> isprog_vars vs a.
Proof.
  introv.
  allrw @isprog_vars_eq; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw @nt_wf_eq.
  allrw <- @wf_halts_like_iff; sp.
Qed.

Lemma cover_vars_halts_like {p} :
  forall a sub,
    @cover_vars p (mk_halts_like a) sub
    <=> cover_vars a sub.
Proof.
  sp; unfold mk_halts_like; split; sp; allrw @cover_vars_eq; allsimpl;
  allrw remove_nvars_nil_l; allrw app_nil_r;
  allrw subvars_app_l; sp.
Qed.

Lemma lsubstc_mk_halts_like {p} :
  forall t sub,
  forall wt : @wf_term p t,
  forall w  : wf_term (mk_halts_like t),
  forall ct : cover_vars t sub,
  forall c  : cover_vars (mk_halts_like t) sub,
    lsubstc (mk_halts_like t) w sub c
    = mkc_halts_like (lsubstc t wt sub ct).
Proof.
  unfold mk_isexc; sp.
  pose proof (lsubstc_mk_approx_ex bot_exc (mk_cbv t nvarx bot_exc) sub w c) as h.
  exrepnd.
  unfold mk_halts_like.
  rw h1; clear h1.
  pose proof (lsubstc_mk_cbv_ex t nvarx bot_exc sub w2 c2) as h; exrepnd.
  rw h1; clear h1.
  rw @lsubstc_bot_exc.
  rw @lsubstc_vars_bot_exc.
  apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_halts_like_ex {p} :
  forall t sub,
  forall w  : wf_term (@mk_halts_like p t),
  forall c  : cover_vars (mk_halts_like t) sub,
    {wt : wf_term t
     & {ct : cover_vars t sub
     & lsubstc (mk_halts_like t) w sub c
       = mkc_halts_like (lsubstc t wt sub ct)}}.
Proof.
  sp.
  duplicate w; duplicate c.
  rw <- @wf_halts_like_iff in w.
  rw @cover_vars_halts_like in c.
  exists w c.
  apply lsubstc_mk_halts_like.
Qed.
