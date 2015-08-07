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


Require Export terms4.


Lemma isprog_vars_ax {p} :
  forall vs, @isprog_vars p vs mk_axiom.
Proof.
  introv; apply isprog_vars_eq; simpl; dands; eauto 3 with slow.
Qed.
Hint Resolve isprog_vars_ax : slow.

Definition mkcv_ax {p} (vs : list NVar) : @CVTerm p vs :=
  exist (isprog_vars vs) mk_axiom (isprog_vars_ax vs).

Lemma isprog_vars_exception {p} :
  forall vs (a e : @NTerm p),
    isprog_vars vs (mk_exception a e) <=> (isprog_vars vs a # isprog_vars vs e).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  rw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw <- @wf_apply_iff; split; sp.
Qed.

Lemma isprog_vars_exception_implies {p} :
  forall vs (a e : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs e
    -> isprog_vars vs (mk_exception a e).
Proof.
  introv ispa ispe.
  apply isprog_vars_exception; sp.
Qed.

Definition mkcv_exception {p} vs (a e : @CVTerm p vs) : CVTerm vs :=
  let (ta,x) := a in
  let (te,y) := e in
  exist (isprog_vars vs)
        (mk_exception ta te)
        (isprog_vars_exception_implies vs ta te x y).

Definition mkcv_sub {o} vs1 vs2 (p : subvars vs1 vs2) (t : @CVTerm o vs1) : CVTerm vs2 :=
  let (a,x) := t in
  exist (isprog_vars vs2)
        a
        (isprog_vars_subvars a vs1 vs2 p x).

Lemma isprog_vars_try_implies {p} :
  forall vs (a b : @NTerm p) v c,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars (v :: vs) c
    -> isprog_vars vs (mk_try a b v c).
Proof.
  introv ipa ipb ipc.
  allrw @isprog_vars_eq; allrw subvars_prop; allsimpl; repnd.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  dands.
  - introv i.
    allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff.
    repndors; repnd; discover; tcsp.
  - constructor; simpl; tcsp.
    introv i; repndors; subst; tcsp; constructor; auto.
Qed.

Definition mkcv_try {p} vs (t1 : @CVTerm p vs) (n : CVTerm vs) (v : NVar) (t2 : CVTerm (v :: vs)) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := n in
  let (c,z) := t2 in
    exist (isprog_vars vs) (mk_try a b v c) (isprog_vars_try_implies vs a b v c x y z).

Lemma isprog_vars_fresh_implies {p} :
  forall vs v (b : @NTerm p),
    isprog_vars (v :: vs) b
    -> isprog_vars vs (mk_fresh v b).
Proof.
  introv ipv.
  allrw @isprog_vars_eq; simpl.
  rw app_nil_r.
  allrw subvars_prop; sp.
  allrw in_remove_nvars; allrw in_single_iff; allsimpl; sp.
  apply_in_hyp pp; sp.
  constructor; simpl; sp; subst.
  constructor; sp.
Qed.

Definition mkcv_fresh {o} vs (v : NVar) (t : @CVTerm o (v :: vs)) : CVTerm vs :=
  let (a,x) := t in
    exist (isprog_vars vs) (mk_fresh v a) (isprog_vars_fresh_implies vs v a x).

Lemma isprog_vars_inl {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs (mk_inl t) <=> isprog_vars vs t.
Proof.
  introv.
  allrw @isprog_vars_eq; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw @nt_wf_eq.
  allrw @wf_inl; sp.
Qed.

Lemma isprog_vars_inr {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs (mk_inr t) <=> isprog_vars vs t.
Proof.
  introv.
  allrw @isprog_vars_eq; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw @nt_wf_eq.
  allrw @wf_inr; sp.
Qed.

Lemma implies_isprog_vars_inl {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs t -> isprog_vars vs (mk_inl t).
Proof.
  introv isp.
  apply isprog_vars_inl; auto.
Qed.

Definition mkcv_inl {p} vs (t : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t in
    exist (isprog_vars vs) (mk_inl a) (implies_isprog_vars_inl vs a x).

Lemma wf_int_eq_iff {p} :
  forall a b c d : @NTerm p,
    (wf_term a # wf_term b # wf_term c # wf_term d) <=> wf_term (mk_int_eq a b c d).
Proof.
  introv; split; intro i.
  apply wf_int_eq; sp.
  allrw @wf_term_eq.
  inversion i as [| | o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)) (k (nobnd d)); intros k1 k2 k3 k4.
  repeat (dest_imp k1 hyp).
  repeat (dest_imp k2 hyp).
  repeat (dest_imp k3 hyp).
  repeat (dest_imp k4 hyp).
  inversion k1; subst.
  inversion k2; subst.
  inversion k3; subst.
  inversion k4; subst; sp.
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
  allrw <- @wf_int_eq_iff; split; sp.
Qed.

Lemma implies_isprog_vars_mk_int_eq {p} :
  forall (a b c d : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs c
    -> isprog_vars vs d
    -> isprog_vars vs (mk_int_eq a b c d).
Proof.
  introv ispa ispb ispc ispd.
  apply isprog_vars_mk_int_eq; sp.
Qed.

Lemma isprog_vars_cbv_iff {o} :
  forall (vs : list NVar) (a : @NTerm o) (v : NVar) (b : NTerm),
    isprog_vars vs (mk_cbv a v b)
    <=> (isprog_vars vs a # isprog_vars (v :: vs) b).
Proof.
  introv.
  unfold mk_cbv.
  rw @isprog_vars_ot_iff; unfold num_bvars; simpl.
  split; introv k; repnd; GC; dands; tcsp.
  - pose proof (k [] a) as h; autodimp h hyp; allrw app_nil_r; auto.
  - pose proof (k [v] b) as h; autodimp h hyp.
    eapply isprog_vars_subvars;[|exact h].
    rw subvars_prop; introv i; allrw in_app_iff; allsimpl; tcsp.
  - unfold nobnd; introv i; repndors; ginv; allrw app_nil_r; tcsp.
    eapply isprog_vars_subvars;[|exact k].
    rw subvars_prop; introv i; allrw in_app_iff; allsimpl; tcsp.
Qed.

Lemma isprog_vars_sub {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs (mk_sub a b) <=> (isprog_vars vs a # isprog_vars vs b).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  rw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw <- @wf_apply_iff; split; sp.
Qed.

Lemma isprog_vars_sub_implies {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs (mk_sub a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_sub; sp.
Qed.

Lemma isprog_vars_one {p} :
  forall vs,
    @isprog_vars p vs mk_one.
Proof.
  introv.
  apply isprog_vars_eq; simpl; dands; tcsp.
  constructor; simpl; tcsp.
Qed.
Hint Resolve isprog_vars_one : slow.

Lemma implies_isprog_vars {o} :
  forall vs (t : @NTerm o),
    wf_term t
    -> subvars (free_vars t) vs
    -> isprog_vars vs t.
Proof.
  introv w s.
  rw @isprog_vars_eq; dands; eauto with slow.
  apply nt_wf_eq; auto.
Qed.
Hint Resolve implies_isprog_vars : slow.

Lemma wf_isint {p} :
  forall (a b c : @NTerm p),
    wf_term (mk_isint a b c)
    <=> (wf_term a # wf_term b # wf_term c).
Proof.
  introv.
  unfold mk_isint, mk_can_test.
  rw @wf_oterm_iff; unfold num_bvars; simpl.
  split; intro k; repnd; dands; GC; tcsp.
  - pose proof (k (nobnd a)) as h; autodimp h hyp.
  - pose proof (k (nobnd b)) as h; autodimp h hyp.
  - pose proof (k (nobnd c)) as h; autodimp h hyp.
  - introv i; repndors; subst; tcsp.
Qed.

Lemma isprog_vars_isint {p} :
  forall vs (a b c : @NTerm p),
    isprog_vars vs (mk_isint a b c)
    <=> (isprog_vars vs a # isprog_vars vs b # isprog_vars vs c).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw @remove_nvars_nil_l).
  rw @app_nil_r.
  allrw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw @wf_isint.
  split; sp.
Qed.

Lemma isprog_vars_isint_implies {p} :
  forall vs (a b c : @NTerm p),
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs c
    -> isprog_vars vs (mk_isint a b c).
Proof.
  introv ispa ispb ispc.
  apply isprog_vars_isint; sp.
Qed.

Lemma wf_term_apply_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NApply) bs)
    <=> {a, b : NTerm $ bs = [bterm [] a, bterm [] b] # wf_term a # wf_term b}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1]; destruct b0 as [l2 t2].
    allunfold @num_bvars; allsimpl.
    destruct l1, l2; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [] t2)) as h2; autodimp h2 hyp.
    allrw @wf_bterm_iff.
    exists t1 t2; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_lambda_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (Can NLambda) bs)
    <=> {v : NVar & {a : NTerm & bs = [bterm [v] a] # wf_term a}}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    allunfold @num_bvars; allsimpl.
    repeat (destruct l1; allsimpl; ginv).
    pose proof (k (bterm [n] t1)) as h1; autodimp h1 hyp.
    allrw @wf_bterm_iff.
    exists n t1; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_fix_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NFix) bs)
    <=> {a : NTerm & bs = [bterm [] a] # wf_term a}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    allunfold @num_bvars; allsimpl.
    destruct l1; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    allrw @wf_bterm_iff.
    exists t1; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_spread_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NSpread) bs)
    <=> {a : NTerm
         & {v1 : NVar
         & {v2 : NVar
         & {b : NTerm
         & bs = [bterm [] a, bterm [v1,v2] b]
         # wf_term a
         # wf_term b }}}}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    allunfold @num_bvars; allsimpl.
    repeat (destruct l1; allsimpl; ginv).
    repeat (destruct l2; allsimpl; ginv).
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [n,n0] t2)) as h2; autodimp h2 hyp.
    allrw @wf_bterm_iff.
    exists t1 n n0 t2; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_dsup_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NDsup) bs)
    <=> {a : NTerm
         & {v1 : NVar
         & {v2 : NVar
         & {b : NTerm
         & bs = [bterm [] a, bterm [v1,v2] b]
         # wf_term a
         # wf_term b }}}}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    allunfold @num_bvars; allsimpl.
    repeat (destruct l1; allsimpl; ginv).
    repeat (destruct l2; allsimpl; ginv).
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [n,n0] t2)) as h2; autodimp h2 hyp.
    allrw @wf_bterm_iff.
    exists t1 n n0 t2; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_decide_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NDecide) bs)
    <=> {a : NTerm
         & {v1 : NVar
         & {b1 : NTerm
         & {v2 : NVar
         & {b2 : NTerm
         & bs = [bterm [] a, bterm [v1] b1, bterm [v2] b2]
         # wf_term a
         # wf_term b1
         # wf_term b2 }}}}}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp; ginv).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    destruct b1 as [l3 t3].
    allunfold @num_bvars; allsimpl.
    repeat (destruct l1; allsimpl; ginv).
    repeat (destruct l2; allsimpl; ginv).
    repeat (destruct l3; allsimpl; ginv).
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [n] t2)) as h2; autodimp h2 hyp.
    pose proof (k (bterm [n0] t3)) as h3; autodimp h3 hyp.
    allrw @wf_bterm_iff.
    exists t1 n t2 n0 t3; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_cbv_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NCbv) bs)
    <=> {a : NTerm
         & {v1 : NVar
         & {b : NTerm
         & bs = [bterm [] a, bterm [v1] b]
         # wf_term a
         # wf_term b }}}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    allunfold @num_bvars; allsimpl.
    repeat (destruct l1; allsimpl; ginv).
    repeat (destruct l2; allsimpl; ginv).
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [n] t2)) as h2; autodimp h2 hyp.
    allrw @wf_bterm_iff.
    exists t1 n t2; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_try_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NTryCatch) bs)
    <=> {a : NTerm
         & {b : NTerm
         & {v : NVar
         & {c : NTerm
         & bs = [bterm [] a, bterm [] b, bterm [v] c]
         # wf_term a
         # wf_term b
         # wf_term c }}}}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp; ginv).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    destruct b1 as [l3 t3].
    allunfold @num_bvars; allsimpl.
    repeat (destruct l1; allsimpl; ginv).
    repeat (destruct l2; allsimpl; ginv).
    repeat (destruct l3; allsimpl; ginv).
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [] t2)) as h2; autodimp h2 hyp.
    pose proof (k (bterm [n] t3)) as h3; autodimp h3 hyp.
    allrw @wf_bterm_iff.
    exists t1 t2 n t3; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_pair_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (Can NPair) bs)
    <=> {a, b : NTerm $ bs = [bterm [] a, bterm [] b] # wf_term a # wf_term b}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1]; destruct b0 as [l2 t2].
    allunfold @num_bvars; allsimpl.
    destruct l1, l2; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [] t2)) as h2; autodimp h2 hyp.
    allrw @wf_bterm_iff.
    exists t1 t2; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_sup_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (Can NSup) bs)
    <=> {a, b : NTerm $ bs = [bterm [] a, bterm [] b] # wf_term a # wf_term b}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1]; destruct b0 as [l2 t2].
    allunfold @num_bvars; allsimpl.
    destruct l1, l2; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [] t2)) as h2; autodimp h2 hyp.
    allrw @wf_bterm_iff.
    exists t1 t2; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_inl_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (Can (NInj NInl)) bs)
    <=> {a : NTerm & bs = [bterm [] a] # wf_term a}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    allunfold @num_bvars; allsimpl.
    destruct l1; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    allrw @wf_bterm_iff.
    exists t1; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_inr_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (Can (NInj NInr)) bs)
    <=> {a : NTerm & bs = [bterm [] a] # wf_term a}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    allunfold @num_bvars; allsimpl.
    destruct l1; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    allrw @wf_bterm_iff.
    exists t1; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_sleep_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NSleep) bs)
    <=> {a : NTerm & bs = [bterm [] a] # wf_term a}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    allunfold @num_bvars; allsimpl.
    destruct l1; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    allrw @wf_bterm_iff.
    exists t1; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_parallel_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NParallel) bs)
    <=> {a : NTerm
         & {b : NTerm
         & bs = [bterm [] a, bterm [] b]
         # wf_term a
         # wf_term b}}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    destruct b0 as [l2 t2].
    allunfold @num_bvars; allsimpl.
    destruct l1, l2; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    pose proof (k (bterm [] t2)) as h2; autodimp h2 hyp.
    allrw @wf_bterm_iff.
    exists t1 t2; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_tuni_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NTUni) bs)
    <=> {a : NTerm & bs = [bterm [] a] # wf_term a}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    allunfold @num_bvars; allsimpl.
    destruct l1; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    allrw @wf_bterm_iff.
    exists t1; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma wf_term_minus_iff {o} :
  forall (bs : list (@BTerm o)),
    wf_term (oterm (NCan NMinus) bs)
    <=> {a : NTerm & bs = [bterm [] a] # wf_term a}.
Proof.
  introv.
  rw @wf_oterm_iff; simpl.
  split; intro k; exrepnd; subst; allsimpl.
  - repeat (destruct bs; allsimpl; tcsp).
    destruct b as [l1 t1].
    allunfold @num_bvars; allsimpl.
    destruct l1; ginv.
    pose proof (k (bterm [] t1)) as h1; autodimp h1 hyp.
    allrw @wf_bterm_iff.
    exists t1; dands; auto.
  - unfold num_bvars; simpl; dands; auto.
    introv i; repndors; subst; tcsp.
Qed.

Lemma isprog_fresh_implies {p} :
  forall v (b : @NTerm p),
    isprog_vars [v] b
    -> isprog (mk_fresh v b).
Proof.
  introv ipv.
  apply isprog_vars_nil_implies_isprog.
  apply isprog_vars_fresh_implies; auto.
Qed.

Lemma isprog_exception_iff {o} :
  forall (a e : @NTerm o),
    isprog (mk_exception a e) <=> (isprog a # isprog e).
Proof.
  introv.
  allrw @isprog_eq.
  apply isprogram_exception_iff.
Qed.

Lemma isprog_vars_implies_wf {o} :
  forall vs (t : @NTerm o),
    isprog_vars vs t -> wf_term t.
Proof.
  introv isp; allrw @isprog_vars_eq; allrw @nt_wf_eq; sp.
Qed.
Hint Resolve isprog_vars_implies_wf : slow.

Lemma isprog_vars_dup1 {o} :
  forall v (t : @NTerm o),
    isprog_vars [v] t
    -> isprog_vars [v,v] t.
Proof.
  introv isp.
  eapply isprog_vars_subvars;[|exact isp].
  rw subvars_prop; simpl; sp.
Qed.

Definition mkcv_dup1 {o} v (t : @CVTerm o [v]) : CVTerm [v,v] :=
  let (a,x) := t in
  exist (isprog_vars [v,v]) a (isprog_vars_dup1 v a x).

Lemma isprog_vars_cont1 {o} :
  forall v (t : @NTerm o),
    isprog_vars [v,v] t
    -> isprog_vars [v] t.
Proof.
  introv isp.
  eapply isprog_vars_subvars;[|exact isp].
  rw subvars_prop; simpl; sp.
Qed.

Definition mkcv_cont1 {o} v (t : @CVTerm o [v,v]) : CVTerm [v] :=
  let (a,x) := t in
  exist (isprog_vars [v]) a (isprog_vars_cont1 v a x).

Lemma isprog_vars_cont1_dup1 {o} :
  forall v (t : @NTerm o) (i : isprog_vars [v] t),
    isprog_vars_cont1 v t (isprog_vars_dup1 v t i) = i.
Proof.
  introv.
  apply isprog_vars_proof_irrelevance.
Qed.

Lemma mkcv_cont1_dup1 {o} :
  forall v (t : @CVTerm o [v]),
    mkcv_cont1 v (mkcv_dup1 v t) = t.
Proof.
  introv; destruct_cterms; simpl.
  rw @isprog_vars_cont1_dup1; auto.
Qed.
