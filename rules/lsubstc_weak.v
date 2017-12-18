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


Require Export rules_useful.


Hint Resolve wf_term_subst : slow.

Lemma subset_free_vars_csub_app3 {o} :
  forall (t : @NTerm o) sub1 sub2,
    disjoint (remove_nvars (dom_csub sub1) (free_vars t)) (dom_csub sub2)
    -> csubst t (sub1 ++ sub2) = csubst t sub1.
Proof.
  unfold csubst; introv disj.
  rw <- @csub2sub_app.
  apply simple_lsubst_app2.
  - introv i j k.
    assert (cl_sub (csub2sub sub1)) as cl by eauto 3 with slow.
    apply in_sub_eta in i; repnd.
    pose proof (flat_map_free_vars_range_cl_sub (csub2sub sub1) cl) as h.
    assert (LIn t0 (flat_map free_vars (range (csub2sub sub1)))) as it.
    { rw lin_flat_map; eexists; dands; eauto. }
    rw h in it; simpl in it; tcsp.
  - introv i.
    assert (prog_sub (csub2sub sub2)) as prog by eauto 3 with slow.
    rw <- @prog_sub_eq in prog; apply prog.
    apply in_sub_eta in i; tcsp.
  - introv i j k.
    allrw @dom_csub_eq.
    pose proof (disj v) as xx.
    rw in_remove_nvars in xx.
    autodimp xx hyp; tcsp.
Qed.

Lemma lsubstc_app_weak_r {o} :
  forall (t : @NTerm o) w x u s1 s2 c,
    disjoint (remove_nvars [x] (free_vars t)) (dom_csub s2)
    -> {c' : cover_vars t ((x,u) :: s1)
        & lsubstc
            t
            w
            ((x,u) :: s1 ++ s2)
            c
          = lsubstc t w ((x,u) :: s1) c'}.
Proof.
  introv disj.

  assert (cover_vars t ((x,u) :: s1)) as cov.
  {
    allrw @cover_vars_eq.
    allrw subvars_eq.
    introv i; applydup c in i; allsimpl; clear c.
    allrw @dom_csub_app.
    allrw in_app_iff.
    repndors; tcsp.
    apply disjoint_sym in disj.
    apply disj in i0.
    rw in_remove_nvars in i0; simpl in i0.
    destruct (deq_nvar x x0); auto.
    destruct i0; tcsp.
  }

  exists cov.

  apply lsubstc_eq_if_csubst.
  rewrite @app_comm_cons.
  apply subset_free_vars_csub_app3; simpl.
  introv i.
  apply disj.
  allrw in_remove_nvars; repnd; dands; auto.
  allsimpl.
  intro j; destruct i; tcsp.
Qed.

Lemma lsubstc_snoc_weak_r {o} :
  forall (t : @NTerm o) w x u s y v c,
    (x <> y -> !LIn y (free_vars t))
    -> {c' : cover_vars t ((x,u) :: s)
        & lsubstc
            t
            w
            ((x,u) :: snoc s (y,v))
            c
          = lsubstc t w ((x,u) :: s) c'}.
Proof.
  introv disj.

  assert (cover_vars t ((x,u) :: s)) as cov.
  {
    allrw @cover_vars_eq.
    allrw subvars_eq.
    introv i; applydup c in i; allsimpl; clear c.
    allrw @dom_csub_snoc; allsimpl.
    allrw in_snoc.
    repndors; subst; tcsp.
    destruct (deq_nvar x y); tcsp.
  }

  exists cov.

  apply lsubstc_eq_if_csubst.
  rewrite snoc_as_append.
  rewrite @app_comm_cons.
  apply subset_free_vars_csub_app3; simpl.
  introv i j; allsimpl; repndors; subst; tcsp.
  allrw in_remove_nvars; repnd; allsimpl.
  allrw not_over_or; repnd; tcsp.
Qed.

Ltac lsubstc_weak :=
  match goal with
  | [ |- context[lsubstc ?t ?w ((?x,?u) :: ?s1 ++ ?s2) ?c] ] =>
    let disj := fresh "disj" in
    let h    := fresh "h" in
    let cov  := fresh "cov" in
    assert (disjoint (remove_nvars [x] (free_vars t)) (dom_csub s2)) as disj;
      [ auto
      | pose proof (lsubstc_app_weak_r t w x u s1 s2 c disj) as h;
        destruct h as [ cov h ];
        rewrite h; clear h
      ]

  | [ |- context[lsubstc ?t ?w ((?x,?u) :: snoc ?s (?y,?v)) ?c] ] =>
    let disj := fresh "disj" in
    let h    := fresh "h" in
    let cov  := fresh "cov" in
    assert (x <> y -> !LIn y (free_vars t)) as disj;
      [ auto
      | pose proof (lsubstc_snoc_weak_r t w x u s y v c disj) as h;
        destruct h as [ cov h ];
        rewrite h; clear h
      ]
  end.

(* !!MOVE *)
Lemma isprog_vars_equality {p} :
  forall (a b c : @NTerm p) vs,
    isprog_vars vs (mk_equality a b c)
                <=> (isprog_vars vs a # isprog_vars vs b # isprog_vars vs c).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  autorewrite with slow.
  allrw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw <- @wf_equality_iff; split; sp.
Qed.

(* !!MOVE *)
Lemma isprog_vars_member {p} :
  forall (a b : @NTerm p) vs,
    isprog_vars vs (mk_member a b)
                <=> (isprog_vars vs a # isprog_vars vs b).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  autorewrite with slow.
  allrw subvars_app_l.
  allrw <- @wf_term_eq.
  allrw <- @wf_equality_iff; split; sp.
Qed.

(* !!MOVE *)
Lemma isprog_vars_iff_covered {o} :
  forall (t : @NTerm o) (vs : list NVar),
    isprog_vars vs t <=> (covered t vs # wf_term t).
Proof.
  tcsp.
Qed.

(* !!MOVE *)
Lemma isprog_vars_lsubst2 {o} :
  forall (t : @NTerm o) vs sub,
    wf_term t
    -> (forall v u, LIn (v, u) sub -> isprog_vars vs u)
    -> isprog_vars (vs ++ dom_sub sub) t
    -> isprog_vars vs (lsubst t sub).
Proof.
  introv w k1 k2.
  allrw @isprog_vars_eq; repnd.
  dands.

  {
    eapply subvars_eqvars;[|apply eqvars_sym; apply eqvars_free_vars_disjoint].
    rw subvars_app_l; dands.

    - rw subvars_remove_nvars; auto.

    - eapply subvars_trans;[apply sub_free_vars_sub_keep_first_subvars|].
      rw subvars_eq; introv i.
      apply in_sub_free_vars in i; exrepnd.
      apply k1 in i0.
      apply isprog_vars_eq in i0; repnd.
      rw subvars_eq in i2; apply i2 in i1; auto.
  }

  { apply nt_wf_lsubst_iff; dands; auto.
    introv i j.
    apply sub_find_some in j.
    apply k1 in j; eauto 3 with slow.
  }
Qed.

(* !!MOVE *)
Lemma isprog_vars_comm {o} :
  forall (t : @NTerm o) vs1 vs2,
    isprog_vars (vs1 ++ vs2) t
    -> isprog_vars (vs2 ++ vs1) t.
Proof.
  introv isp.
  allrw @isprog_vars_eq; repnd; dands; auto.
  apply subvars_comm_r; auto.
Qed.

(* !!MOVE *)
Lemma isprog_vars_subst2 {o} :
  forall (t : @NTerm o) v u vs,
    wf_term t
    -> isprog_vars vs u
    -> isprog_vars (v :: vs) t
    -> isprog_vars vs (subst t v u).
Proof.
  introv w k1 k2.
  apply isprog_vars_lsubst2; simpl; auto.

  - introv i; repndors; cpx.

  - apply isprog_vars_comm; simpl; auto.
Qed.
