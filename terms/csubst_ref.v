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
  Authors: Vincent Rahli

*)


Require Export csubst.


Lemma isprogram_last_cs_implies_ex {o} :
  forall (l : list (@BTerm o)),
    isprogram (oterm (NCan NLastCs) l)
    -> {t : NTerm
        & {u : NTerm
        & l = [nobnd t, nobnd u]
        # isprogram t
        # isprogram u}}.
Proof.
  introv isp.
  unfold isprogram, closed in *; repnd; simpl in *.
  inversion isp as [|? ? imp eqm]; subst; simpl in *.
  repeat (destruct l; simpl in *; ginv).
  destruct b as [l1 t1].
  destruct b0 as [l2 t2].
  unfold num_bvars in *; simpl in *.
  destruct l1; simpl in *; ginv.
  destruct l2; simpl in *; ginv.
  autorewrite with slow in *.
  allrw app_eq_nil_iff; repnd.
  pose proof (imp (bterm [] t1)) as q1; autodimp q1 hyp.
  pose proof (imp (bterm [] t2)) as q2; autodimp q2 hyp.
  allrw @bt_wf_iff.
  exists t1 t2; dands; auto.
Qed.

Definition mk_last_cs {o} (t u : @NTerm o) := oterm (NCan NLastCs) [nobnd t, nobnd u].

Lemma isprogram_last_cs_implies {o} :
  forall (a d : @NTerm o),
    isprogram (mk_last_cs a d)
    -> isprogram a # isprogram d.
Proof.
  introv isp.
  apply isprogram_last_cs_implies_ex in isp; exrepnd; ginv; tcsp.
Qed.

Lemma cover_vars_last_cs {p} :
  forall a d sub,
    cover_vars (@mk_last_cs p a d) sub
    <=> (cover_vars a sub # cover_vars d sub ).
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw app_nil_r.
  allrw @dom_csub_csub_filter; sp.
Qed.

Lemma implies_isprog_last_cs {o} :
  forall (a d : @NTerm o),
    isprog a
    -> isprog d
    -> isprog (mk_last_cs a d).
Proof.
  introv ispa ispb.
  allrw <- @isprogram_eq.
  destruct ispa as [cla wfa].
  destruct ispb as [clb wfb].
  split.
  { unfold closed; simpl; rw cla; rw clb; simpl; auto. }
  { repeat constructor; simpl; introv xx; repndors; subst; tcsp;apply bt_wf_iff; auto. }
Qed.

Lemma implies_isprogram_last_cs {o} :
  forall (a b : @NTerm o),
    isprogram a
    -> isprogram b
    -> isprogram (mk_last_cs a b).
Proof.
  introv ispa ispb.
  allrw @isprogram_eq.
  apply implies_isprog_last_cs; auto.
Qed.

Lemma wf_last_cs {o} :
  forall (a b : @NTerm o),
    wf_term (mk_last_cs a b) <=> (wf_term a # wf_term b).
Proof.
  introv; allrw @wf_term_eq; split; intro h; repnd.
  { inversion h as [|? ? imp e]; subst; simpl in *; clear e.
    pose proof (imp (nobnd a)) as impa; autodimp impa hyp.
    pose proof (imp (nobnd b)) as impb; autodimp impb hyp.
    allrw @bt_wf_iff; auto. }
  { repeat constructor; simpl; introv xx; repndors; subst; tcsp; apply bt_wf_iff; auto. }
Qed.

Lemma nt_wf_last_cs {o} :
  forall (a b : @NTerm o),
    nt_wf (mk_last_cs a b) <=> (nt_wf a # nt_wf b).
Proof.
  introv.
  allrw @nt_wf_eq; apply wf_last_cs.
Qed.

Definition mkc_last_cs {p} (t u : @CTerm p) : CTerm :=
  let (a,x) := t in
  let (b,y) := u in
  exist isprog (mk_last_cs a b) (implies_isprog_last_cs a b x y).

Lemma lsubstc_mk_last_cs {o} :
  forall (t1 t2 : @NTerm o) sub
         (w1 : wf_term t1)
         (w2 : wf_term t2)
         (w  : wf_term (mk_last_cs t1 t2))
         (c1 : cover_vars t1 sub)
         (c2 : cover_vars t2 sub)
         (c  : cover_vars (mk_last_cs t1 t2) sub),
    lsubstc (mk_last_cs t1 t2) w sub c
    = mkc_last_cs (lsubstc t1 w1 sub c1) (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub; sp.
Qed.

Lemma lsubstc_mk_last_cs_ex {o} :
  forall (t1 t2 : @NTerm o) sub
         (w : wf_term (mk_last_cs t1 t2))
         (c : cover_vars (mk_last_cs t1 t2) sub),
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
     & lsubstc (mk_last_cs t1 t2) w sub c
       = mkc_last_cs (lsubstc t1 w1 sub c1) (lsubstc t2 w2 sub c2) }}}}.
Proof.
  sp.

  duplicate w.
  rw @wf_last_cs in w; sp.

  duplicate c.
  rw @cover_vars_last_cs in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_last_cs.
Qed.


Definition mk_qnat {o} : @NTerm o := oterm (Can NQNat) [].

Theorem isprog_qnat {o} : @isprog o mk_qnat.
Proof.
  repeat constructor.
Qed.

Definition mkc_qnat {o} : @CTerm o := exist isprog mk_qnat isprog_qnat.

Lemma lsubstc_mk_qnat {o} :
  forall w (s : @CSub o) c, lsubstc mk_qnat w s c = mkc_qnat.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; auto.
Qed.
Hint Rewrite @lsubstc_mk_qnat : slow.


Lemma isprogram_qtime_implies_ex {o} :
  forall (l : list (@BTerm o)),
    isprogram (oterm (Can NQTime) l)
    -> {t : NTerm
        & l = [nobnd t]
        # isprogram t}.
Proof.
  introv isp.
  unfold isprogram, closed in *; repnd; simpl in *.
  inversion isp as [|? ? imp eqm]; subst; simpl in *.
  repeat (destruct l; simpl in *; ginv).
  destruct b as [l1 t1].
  unfold num_bvars in *; simpl in *.
  destruct l1; simpl in *; ginv.
  autorewrite with slow in *.
  allrw app_eq_nil_iff; repnd.
  pose proof (imp (bterm [] t1)) as q1; autodimp q1 hyp.
  allrw @bt_wf_iff.
  exists t1; dands; auto.
Qed.

Definition mk_qtime {o} (t : @NTerm o) := oterm (Can NQTime) [nobnd t].

Lemma isprogram_qtime_implies {o} :
  forall (a : @NTerm o),
    isprogram (mk_qtime a)
    -> isprogram a.
Proof.
  introv isp.
  apply isprogram_qtime_implies_ex in isp; exrepnd; ginv; tcsp.
Qed.

Lemma cover_vars_qtime {o} :
  forall (a : @NTerm o) sub,
    cover_vars (mk_qtime a) sub
    <=> cover_vars a sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw app_nil_r.
  allrw @dom_csub_csub_filter; sp.
Qed.

Lemma implies_isprog_qtime {o} :
  forall (a : @NTerm o),
    isprog a
    -> isprog (mk_qtime a).
Proof.
  introv ispa.
  allrw <- @isprogram_eq.
  destruct ispa as [cla wfa].
  split.
  { unfold closed; simpl; rw cla; simpl; auto. }
  { repeat constructor; simpl; introv xx; repndors; subst; tcsp;apply bt_wf_iff; auto. }
Qed.

Lemma implies_isprogram_qtime {o} :
  forall (a : @NTerm o),
    isprogram a
    -> isprogram (mk_qtime a).
Proof.
  introv ispa.
  allrw @isprogram_eq.
  apply implies_isprog_qtime; auto.
Qed.

Lemma wf_qtime {o} :
  forall (a : @NTerm o),
    wf_term (mk_qtime a) <=> wf_term a.
Proof.
  introv; allrw @wf_term_eq; split; intro h; repnd.
  { inversion h as [|? ? imp e]; subst; simpl in *; clear e.
    pose proof (imp (nobnd a)) as impa; autodimp impa hyp.
    allrw @bt_wf_iff; auto. }
  { repeat constructor; simpl; introv xx; repndors; subst; tcsp; apply bt_wf_iff; auto. }
Qed.

Lemma nt_wf_qtime {o} :
  forall (a : @NTerm o),
    nt_wf (mk_qtime a) <=> nt_wf a.
Proof.
  introv.
  allrw @nt_wf_eq; apply wf_qtime.
Qed.

Definition mkc_qtime {p} (t : @CTerm p) : CTerm :=
  let (a,x) := t in
  exist isprog (mk_qtime a) (implies_isprog_qtime a x).

Lemma lsubstc_mk_qtime {o} :
  forall (t1 : @NTerm o) sub
         (w1 : wf_term t1)
         (w  : wf_term (mk_qtime t1))
         (c1 : cover_vars t1 sub)
         (c  : cover_vars (mk_qtime t1) sub),
    lsubstc (mk_qtime t1) w sub c
    = mkc_qtime (lsubstc t1 w1 sub c1).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub; sp.
Qed.

Lemma lsubstc_mk_qtime_ex {o} :
  forall (t1 : @NTerm o) sub
         (w : wf_term (mk_qtime t1))
         (c : cover_vars (mk_qtime t1) sub),
    {w1 : wf_term t1
     & {c1 : cover_vars t1 sub
     & lsubstc (mk_qtime t1) w sub c
       = mkc_qtime (lsubstc t1 w1 sub c1) }}.
Proof.
  sp.

  duplicate w.
  rw @wf_qtime in w; sp.

  duplicate c.
  rw @cover_vars_qtime in c; sp.

  exists w c.
  apply lsubstc_mk_qtime.
Qed.

Lemma isprogram_qlt_implies_ex {o} :
  forall (l : list (@BTerm o)),
    isprogram (oterm (Can NQLt) l)
    -> {t : NTerm
        & {u : NTerm
        & l = [nobnd t, nobnd u]
        # isprogram t
        # isprogram u}}.
Proof.
  introv isp.
  unfold isprogram, closed in *; repnd; simpl in *.
  inversion isp as [|? ? imp eqm]; subst; simpl in *.
  repeat (destruct l; simpl in *; ginv).
  destruct b as [l1 t1].
  destruct b0 as [l2 t2].
  unfold num_bvars in *; simpl in *.
  destruct l1, l2; simpl in *; ginv.
  autorewrite with slow in *.
  allrw app_eq_nil_iff; repnd.
  pose proof (imp (bterm [] t1)) as q1; autodimp q1 hyp.
  pose proof (imp (bterm [] t2)) as q2; autodimp q2 hyp.
  allrw @bt_wf_iff.
  exists t1 t2; dands; auto.
Qed.

Definition mk_qlt {o} (t u : @NTerm o) := oterm (Can NQLt) [nobnd t, nobnd u].

Lemma isprogram_qlt_implies {o} :
  forall (a b : @NTerm o),
    isprogram (mk_qlt a b)
    -> isprogram a # isprogram b.
Proof.
  introv isp.
  apply isprogram_qlt_implies_ex in isp; exrepnd; ginv; tcsp.
Qed.

Lemma cover_vars_qlt {o} :
  forall (a b : @NTerm o) sub,
    cover_vars (mk_qlt a b) sub
    <=> (cover_vars a sub # cover_vars b sub).
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw app_nil_r.
  allrw @dom_csub_csub_filter; sp.
Qed.

Lemma implies_isprog_qlt {o} :
  forall (a b : @NTerm o),
    isprog a
    -> isprog b
    -> isprog (mk_qlt a b).
Proof.
  introv ispa ispb.
  allrw <- @isprogram_eq.
  destruct ispa as [cla wfa].
  destruct ispb as [clb wfb].
  split.
  { unfold closed; simpl; rw cla; rw clb; simpl; auto. }
  { repeat constructor; simpl; introv xx; repndors; subst; tcsp;apply bt_wf_iff; auto. }
Qed.

Lemma implies_isprogram_qlt {o} :
  forall (a b : @NTerm o),
    isprogram a
    -> isprogram b
    -> isprogram (mk_qlt a b).
Proof.
  introv ispa ispb.
  allrw @isprogram_eq.
  apply implies_isprog_qlt; auto.
Qed.

Lemma wf_qlt {o} :
  forall (a b : @NTerm o),
    wf_term (mk_qlt a b) <=> (wf_term a # wf_term b).
Proof.
  introv; allrw @wf_term_eq; split; intro h; repnd.
  { inversion h as [|? ? imp e]; subst; simpl in *; clear e.
    pose proof (imp (nobnd a)) as impa; autodimp impa hyp.
    pose proof (imp (nobnd b)) as impb; autodimp impb hyp.
    allrw @bt_wf_iff; auto. }
  { repeat constructor; simpl; introv xx; repndors; subst; tcsp; apply bt_wf_iff; auto. }
Qed.

Lemma nt_wf_qlt {o} :
  forall (a b : @NTerm o),
    nt_wf (mk_qlt a b) <=> (nt_wf a # nt_wf b).
Proof.
  introv.
  allrw @nt_wf_eq; apply wf_qlt.
Qed.

Definition mkc_qlt {p} (t u : @CTerm p) : CTerm :=
  let (a,x) := t in
  let (b,y) := u in
  exist isprog (mk_qlt a b) (implies_isprog_qlt a b x y).

Lemma lsubstc_mk_qlt {o} :
  forall (t1 t2 : @NTerm o) sub
         (w1 : wf_term t1)
         (w2 : wf_term t2)
         (w  : wf_term (mk_qlt t1 t2))
         (c1 : cover_vars t1 sub)
         (c2 : cover_vars t2 sub)
         (c  : cover_vars (mk_qlt t1 t2) sub),
    lsubstc (mk_qlt t1 t2) w sub c
    = mkc_qlt (lsubstc t1 w1 sub c1) (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub; sp.
Qed.

Lemma lsubstc_mk_qlt_ex {o} :
  forall (t1 t2 : @NTerm o) sub
         (w : wf_term (mk_qlt t1 t2))
         (c : cover_vars (mk_qlt t1 t2) sub),
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
     & lsubstc (mk_qlt t1 t2) w sub c
       = mkc_qlt (lsubstc t1 w1 sub c1) (lsubstc t2 w2 sub c2) }}}}.
Proof.
  sp.

  duplicate w.
  rw @wf_qlt in w; sp.

  duplicate c.
  rw @cover_vars_qlt in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_qlt.
Qed.
