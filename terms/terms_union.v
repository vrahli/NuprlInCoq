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

  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export alphaeq.
Require Export cvterm2.
Require Export terms_props.


Definition mk_bunion {p} (A B : @NTerm p) :=
  let v := newvarlst [A,B] in
  mk_tunion mk_bool v (mk_ite (mk_var v) A B).

Lemma isprog_bool {o} : @isprog o mk_bool.
Proof.
  apply isprog_union; auto.
Qed.

Lemma isprog_bunion {p} :
  forall a b : @NTerm p,
    isprog a
    -> isprog b
    -> isprog (mk_bunion a b).
Proof.
  unfold mk_bunion; introv ipa ipb.
  apply isprog_tunion; auto.
  apply isprog_bool.
  apply isprog_vars_decide; try (complete (apply isprog_vars_if_isprog; auto)).
  apply isprog_vars_var.
Qed.

Definition mkc_bunion {p} (A B : @CTerm p) : CTerm :=
  let (a,x) := A in
  let (b,y) := B in
  exist isprog (mk_bunion a b) (isprog_bunion a b x y).

Definition cnewvarlst {p} (ts : list (@CTerm p)) :=
  newvarlst (map (fun t : CTerm => proj1_sig t) ts).

Lemma fold_mkc_bunion {p} :
  forall (A B : @CTerm p),
    let v := cnewvarlst [A,B] in
    mkc_tunion mkc_bool v (mkcv_ite [v] (mkc_var v) (mk_cv [v] A) (mk_cv [v] B))
    = mkc_bunion A B.
Proof.
  unfold mkc_bunion, mk_bunion, cnewvarlst; introv; destruct_cterms; simpl.
  apply cterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_bunion {o} :
  forall A B sub,
  forall wA : wf_term A,
  forall wB : @wf_term o B,
  forall w  : wf_term (mk_bunion A B),
  forall cA : cover_vars A sub,
  forall cB : cover_vars B sub,
  forall c  : cover_vars (mk_bunion A B) sub,
    alphaeqc (lsubstc (mk_bunion A B) w sub c)
             (mkc_bunion (lsubstc A wA sub cA)
                         (lsubstc B wB sub cB)).
Proof.
  introv.
  rw <- @fold_mkc_bunion.
  unfold alphaeqc; simpl.
  allunfold @cnewvarlst; allsimpl.

  assert (isprogram (csubst A sub)) as ispa.
  apply isprogram_csubst; auto; apply nt_wf_eq; auto.

  assert (isprogram (csubst B sub)) as ispb.
  apply isprogram_csubst; auto; apply nt_wf_eq; auto.

  rw (newvarlst_prog [csubst A sub, csubst B sub]);
    try (complete (introv k; simpl in k; sp; subst; rw @isprog_eq; auto)).

  allunfold @csubst.

  pose proof (prog_sub_csub2sub sub) as Hpr.
  remember (csub2sub sub) as csub.

  revert ispa ispb.
  change_to_lsubst_aux4.
  intros ispa ispb.

  unfold mk_tunion, nobnd.
  simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  prove_alpha_eq3.
  remember (csub2sub sub) as csub.
  pose proof (newvarlst_prop [A,B]).
  pose proof (newvar_prop A).
  pose proof (newvar_prop B).
  rw @lsubst_aux_sub_filter; auto; disjoint_reasoningv; auto.
  rw @sub_find_sub_filter; tcsp.

  remember (newvarlst [A,B]) as v1.
  remember (newvar A) as v2.
  remember (newvar B) as v3.
  remember (oterm (NCan NDecide)
                  [nobnd (vterm v1),
                   bterm [v2] (lsubst_aux A (sub_filter csub [v1])),
                   bterm [v3] (lsubst_aux B (sub_filter (sub_filter csub [v1]) [v3]))]) as t1.
  remember (mk_ite (mk_var nvarx) (lsubst_aux A csub) (lsubst_aux B csub)) as t2.
  pose proof (ex_fresh_var (v1
                              :: v2
                              :: v2
                              :: (bound_vars (lsubst_aux A (csub2sub sub)))
                              ++ (bound_vars (lsubst_aux B (csub2sub sub)))
                              ++ all_vars A
                              ++ all_vars B
                              ++ all_vars t1
                              ++ all_vars t2)) as h;
              exrepnd.
  allsimpl.
  allrw in_app_iff.
  allrw app_nil_r.
  allrw not_over_or; repnd.
  apply al_bterm with (lv := [v]); allsimpl; auto.
  rw disjoint_singleton_l.
  allrw in_app_iff; sp.

  change_to_lsubst_aux4; auto.
  Opaque newvarlst.
  subst; simpl.

  rw (newvar_prog (lsubst_aux A (csub2sub sub))); auto;
  try (complete (rw @isprog_eq; auto)).

  rw (newvar_prog (lsubst_aux B (csub2sub sub))); auto;
  try (complete (rw @isprog_eq; auto)).

  allrw memvar_singleton.
  allrw <- beq_var_refl; autorewrite with var; simpl.
  prove_alpha_eq3;[|].

  - remember (newvarlst [A, B]) as v1.
    remember (newvar A) as v2.
    remember (lsubst_aux
                (lsubst_aux A (sub_filter (csub2sub sub) [v1]))
                (if beq_var v1 v2 then [] else [(v1, vterm v)])) as t1.
    remember (lsubst_aux (lsubst_aux A (csub2sub sub)) []) as t2.
    pose proof (ex_fresh_var (v1
                                :: (bound_vars (lsubst_aux A (csub2sub sub)))
                                ++ all_vars t1
                                ++ all_vars t2)) as h;
      exrepnd.
    allsimpl.
    repeat (rw in_app_iff in h3).
    repeat (rw not_over_or in h3); repnd.
    apply al_bterm with (lv := [v0]); allsimpl; auto.
    rw disjoint_singleton_l.
    repeat (rw in_app_iff); sp.

    subst.
    rw @lsubst_aux_nil.
    rw @lsubst_aux_sub_filter;
      try (complete (introv k; apply in_csub2sub in k; auto));
      try (complete (rw disjoint_singleton_r;
                     pose proof (newvarlst_prop [A, B]) as h; simpl in h; intro k; apply h;
                     rw in_app_iff; sp)).
    rw (lsubst_trivial4 (lsubst_aux A (csub2sub sub))); simpl;
    try (complete (rw disjoint_singleton_l; destruct ispa as [cl wf]; rw cl; sp));
    try (complete (introv k; sp; cpx; simpl; rw disjoint_singleton_l; auto)).

    boolvar.

    + rw @lsubst_aux_nil.
      rw (lsubst_trivial4 (lsubst_aux A (csub2sub sub))); simpl; auto;
      try (complete (rw disjoint_singleton_l; destruct ispa as [cl wf]; rw cl; sp));
      try (complete (introv k; sp; cpx; simpl; rw disjoint_singleton_l; auto)).

    + rw (lsubst_aux_trivial4 (lsubst_aux A (csub2sub sub))); simpl; auto;
      try (complete (rw disjoint_singleton_l; destruct ispa as [cl wf]; rw cl; sp));
      try (complete (introv k; sp; cpx; simpl; rw disjoint_singleton_l; auto)).

      rw (lsubst_trivial4 (lsubst_aux A (csub2sub sub))); simpl; auto;
      try (complete (rw disjoint_singleton_l; destruct ispa as [cl wf]; rw cl; sp));
      try (complete (introv k; sp; cpx; simpl; rw disjoint_singleton_l; auto)).

  - rw @lsubst_aux_sub_filter; auto; disjoint_reasoningv; auto.
    rw @lsubst_aux_sub_filter; auto; disjoint_reasoningv; auto.
    rw @lsubst_aux_nil.

    remember (newvarlst [A, B]) as v1.
    remember (newvar B) as v2.
    remember (lsubst_aux
                (lsubst_aux B (csub2sub sub))
                (if beq_var v1 v2 then [] else [(v1, vterm v)])) as t1.
    remember (lsubst_aux B (csub2sub sub)) as t2.
    pose proof (ex_fresh_var (v1
                                :: (bound_vars (lsubst_aux B (csub2sub sub)))
                                ++ all_vars t1
                                ++ all_vars t2)) as h;
      exrepnd.
    allsimpl.
    repeat (rw in_app_iff in h3).
    repeat (rw not_over_or in h3); repnd.
    apply al_bterm with (lv := [v0]); allsimpl; auto.
    rw disjoint_singleton_l.
    repeat (rw in_app_iff); sp.

    subst.
    rw (lsubst_trivial4 (lsubst_aux B (csub2sub sub))); simpl;
    try (complete (rw disjoint_singleton_l; destruct ispb as [cl wf]; rw cl; sp));
    try (complete (introv k; sp; cpx; simpl; rw disjoint_singleton_l; auto)).
    rw (lsubst_aux_trivial4 (lsubst_aux B (csub2sub sub))); simpl;
    try (complete (boolvar; simpl; sp; introv k; sp; cpx; allsimpl; sp; subst; sp));
    try (complete (boolvar; simpl; sp;
                   rw disjoint_singleton_l; destruct ispb as [cl wf]; rw cl; sp)).
    rw (lsubst_trivial4 (lsubst_aux B (csub2sub sub))); simpl; auto;
    try (complete (rw disjoint_singleton_l; destruct ispb as [cl wf]; rw cl; sp));
    try (complete (introv k; sp; cpx; simpl; rw disjoint_singleton_l; auto)).
Qed.

Lemma cover_vars_upto_decide {p} :
  forall vs a v1 b1 v2 b2 sub,
    @cover_vars_upto p (mk_decide a v1 b1 v2 b2) sub vs
    <=> cover_vars_upto a sub vs
        # cover_vars_upto b1 (csub_filter sub [v1]) (v1 :: vs)
        # cover_vars_upto b2 (csub_filter sub [v2]) (v2 :: vs).
Proof.
  sp; repeat (rw cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw subvars_prop; simpl; split; sp; apply_in_hyp pp;
  allrw in_app_iff; allrw in_remove_nvars; allrw in_single_iff; sp.
  pose proof (deq_nvar v1 x) as o; sp.
  right; right; sp.
  pose proof (deq_nvar v2 x) as o; sp.
  right; right; sp.
Qed.

Lemma cover_vars_upto_csub_filter_rm {o} :
  forall (t : @NTerm o) sub l vs,
    disjoint l (free_vars t)
    -> (cover_vars_upto t (csub_filter sub l) vs
        <=> cover_vars_upto t sub vs).
Proof.
  introv disj.
  unfold cover_vars_upto; allrw subvars_eq; split;
  intro k; introv i; allrw in_app_iff.
  - apply k in i; allrw in_app_iff; sp.
    rw @dom_csub_csub_filter in l0.
    rw in_remove_nvars in l0; sp.
  - applydup k in i; allrw in_app_iff; sp.
    rw @dom_csub_csub_filter.
    rw in_remove_nvars; sp.
    right; dands; auto; intro h; apply disj in h; sp.
Qed.

Lemma cover_vars_upto_cons_rm {o} :
  forall (t : @NTerm o) sub v vs,
    !LIn v (free_vars t)
    -> (cover_vars_upto t sub (v :: vs)
        <=> cover_vars_upto t sub vs).
Proof.
  introv ni.
  unfold cover_vars_upto; allrw subvars_eq; split;
  intro k; introv i; allrw in_app_iff.
  - applydup k in i; allsimpl; sp; subst; sp.
    allrw in_app_iff; sp.
  - applydup k in i; allrw in_app_iff; sp.
Qed.

Lemma cover_vars_upto_ite {p} :
  forall vs a b c sub,
    @cover_vars_upto p (mk_ite a b c) sub vs
    <=> cover_vars_upto a sub vs
      # cover_vars_upto b sub vs
      # cover_vars_upto c sub vs.
Proof.
  introv.
  rw @cover_vars_upto_decide.

  pose proof (cover_vars_upto_csub_filter_rm b sub [newvar b] (newvar b :: vs)) as h1.
  autodimp h1 hyp.
  rw disjoint_singleton_l; apply newvar_prop.
  rw h1; clear h1.

  pose proof (cover_vars_upto_csub_filter_rm c sub [newvar c] (newvar c :: vs)) as h1.
  autodimp h1 hyp.
  rw disjoint_singleton_l; apply newvar_prop.
  rw h1; clear h1.

  pose proof (cover_vars_upto_cons_rm b sub (newvar b) vs) as h1.
  autodimp h1 hyp.
  apply newvar_prop.
  rw h1; clear h1.

  pose proof (cover_vars_upto_cons_rm c sub (newvar c) vs) as h1.
  autodimp h1 hyp.
  apply newvar_prop.
  rw h1; clear h1.

  sp.
Qed.

Lemma cover_vars_bool {o} : forall sub, @cover_vars o mk_bool sub.
Proof.
  introv.
  rw @cover_vars_eq; rw subvars_eq.
  introv i; allsimpl; sp.
Qed.

Lemma cover_vars_bool_iff {o} : forall sub, @cover_vars o mk_bool sub <=> True.
Proof.
  introv; split; sp.
  apply cover_vars_bool.
Qed.

Lemma cover_vars_upto_nil_iff {o} :
  forall (t : @NTerm o) sub,
    cover_vars_upto t sub [] <=> cover_vars t sub.
Proof.
  introv.
  allrw @cover_vars_eq; sp.
Qed.

Lemma cover_vars_bunion {p} :
  forall a b sub,
    cover_vars (@mk_bunion p a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  introv.
  rw @cover_vars_tunion.
  rw @cover_vars_upto_ite.
  rw @cover_vars_bool_iff.
  rw @cover_vars_upto_var; simpl.

  remember (newvarlst [a,b]) as v.

  pose proof (cover_vars_upto_csub_filter_rm a sub [v] [v]) as h1.
  autodimp h1 hyp.
  rw disjoint_singleton_l; subst.
  pose proof (newvarlst_prop [a,b]) as h; simpl in h.
  allrw in_app_iff; sp.

  pose proof (cover_vars_upto_csub_filter_rm b sub [v] [v]) as h2.
  autodimp h2 hyp.
  rw disjoint_singleton_l; subst.
  pose proof (newvarlst_prop [a,b]) as h; simpl in h.
  allrw in_app_iff; sp.

  rw h1; rw h2; clear h1 h2.

  pose proof (cover_vars_upto_cons_rm a sub v []) as h1.
  autodimp h1 hyp.
  subst.
  pose proof (newvarlst_prop [a,b]) as h; simpl in h.
  allrw in_app_iff; sp.

  pose proof (cover_vars_upto_cons_rm b sub v []) as h2.
  autodimp h2 hyp.
  subst.
  pose proof (newvarlst_prop [a,b]) as h; simpl in h.
  allrw in_app_iff; sp.

  rw h1; rw h2; clear h1 h2.

  allrw @cover_vars_upto_nil_iff; split; sp.
Qed.

Definition tt {o} := @mkc_inl o mkc_axiom.
Definition ff {o} := @mkc_inr o mkc_axiom.

Lemma fold_mkc_bool {o} :
  @mkc_union o mkc_unit mkc_unit = mkc_bool.
Proof.
  apply cterm_eq; simpl; auto.
Qed.

Lemma wf_union {o} :
  forall a b : @NTerm o, wf_term (mk_union a b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| | op l bwf e ]; subst.
  generalize (bwf (nobnd a)) (bwf (nobnd b));
    clear bwf; intros bwf1 bwf2.
  autodimp bwf1 hyp; autodimp bwf2 hyp; try (complete (simpl; sp)).
  inversion bwf1; subst.
  inversion bwf2; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; sp.
  allsimpl; sp; subst; constructor; allrw @nt_wf_eq; sp.
Qed.

Lemma wf_unit {o} : @wf_term o mk_unit.
Proof.
  rw <- @wf_approx_iff; sp.
Qed.

Lemma wf_bool {o} : @wf_term o mk_bool.
Proof.
  apply wf_union; sp; apply wf_unit.
Qed.

Lemma wf_decide {p} :
  forall (a : @NTerm p) v1 b1 v2 b2,
    wf_term (mk_decide a v1 b1 v2 b2) <=> (wf_term a # wf_term b1 # wf_term b2).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [| | o l bwf e ]; subst.
  generalize (bwf (nobnd a)) (bwf (bterm [v1] b1)) (bwf (bterm [v2] b2));
    clear bwf; intros bwf1 bwf2 bwf3.
  autodimp bwf1 hyp; autodimp bwf2 hyp; autodimp bwf3 hyp; try (complete (simpl; sp)).
  inversion bwf1; subst.
  inversion bwf2; subst.
  inversion bwf3; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; sp.
  allsimpl; sp; subst; constructor; allrw @nt_wf_eq; sp.
Qed.

Lemma wf_ite {o} :
  forall (a b c : @NTerm o),
    wf_term (mk_ite a b c) <=> (wf_term a # wf_term b # wf_term c).
Proof.
  introv.
  rw @wf_decide; sp.
Qed.

Lemma wf_bunion {o} :
  forall (a b : @NTerm o),
    wf_term (mk_bunion a b) <=> (wf_term a # wf_term b).
Proof.
  introv.
  rw <- @wf_tunion_iff.
  rw @wf_ite; split; sp.
Qed.

Lemma lsubstc_mk_bunion_ex {o} :
  forall A B sub,
  forall w : wf_term (@mk_bunion o A B),
  forall c  : cover_vars (mk_bunion A B) sub,
    {wA : wf_term A
     & {wB : wf_term B
     & {cA : cover_vars A sub
     & {cB : cover_vars B sub
     & alphaeqc (lsubstc (mk_bunion A B) w sub c)
                (mkc_bunion (lsubstc A wA sub cA)
                         (lsubstc B wB sub cB))}}}}.
Proof.
  sp.

  assert (wf_term A) as wa.
  { allrw @wf_bunion; sp. }

  assert (wf_term B) as wb.
  { allrw @wf_bunion; sp. }

  assert (cover_vars A sub) as ca.
  { rw @cover_vars_bunion in c; sp. }

  assert (cover_vars B sub) as cb.
  { rw @cover_vars_bunion in c; sp. }

  exists wa wb ca cb.
  apply lsubstc_mk_bunion.
Qed.

Lemma free_vars_ite {o} :
  forall a b c : @NTerm o,
    free_vars (mk_ite a b c) = free_vars a ++ free_vars b ++ free_vars c.
Proof.
  introv.
  unfold mk_ite.
  rw @free_vars_decide.
  repeat (rw remove_nvars_cons).
  repeat (rw remove_nvars_nil_l).
  repeat (rw remove_trivial); auto; apply newvar_prop.
Qed.

Lemma free_vars_bunion {o} :
  forall A B, free_vars (@mk_bunion o A B) = free_vars A ++ free_vars B.
Proof.
  introv.
  unfold mk_bunion.

  remember (newvarlst [A,B]) as p; repnd.
  pose proof (newvarlst_prop [A,B]) as ni; rw <- Heqp in ni; clear Heqp.

  rw @free_vars_tunion.
  rw @free_vars_ite.
  rw @free_vars_bool.
  rw remove_nvars_cons; rw remove_nvars_nil_l; simpl.
  destruct (eq_var_dec p p); tcsp.
  rw remove_trivial; auto.
  simpl in ni; allrw app_nil_r; auto.
Qed.

(**

  If we want to add exception to a type, we can use:

 *)
Definition with_exc {o} (T N E : @NTerm o) := mk_bunion T (mk_texc N E).
Definition with_exc_c {o} (T N E : @CTerm o) := mkc_bunion T (mkc_texc N E).
