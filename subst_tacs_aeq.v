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
  along with VPrl.  If not, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)

Require Export csubst.
Require Export computation6.
Require Export subst_tacs.
Require Export cequiv_tacs.


Lemma aeq_simple_lsubstc_subst_ex {p} :
  forall (t : @NTerm p) x B ws s cs wt ct,
    {wb : wf_term B
     & {cb : cover_vars_upto B (csub_filter s [x]) [x]
     & alphaeqc
         (lsubstc (subst B x t) ws s cs)
         (substc (lsubstc t wt s ct) x (lsubstc_vars B wb (csub_filter s [x]) [x] cb)) }}.
Proof.
  introv.

  pose proof (change_bvars_alpha_wspec (free_vars t) B) as q.
  destruct q as [B' q]; exrepnd.

  applydup @alphaeq_preserves_free_vars in q as efvs.
  applydup @alphaeq_preserves_wf in q as ewf.

  assert (wf_term (subst B' x t)) as wf'.
  { allrw @wf_term_eq.
    allrw @nt_wf_lsubst_iff.
    rw ewf; rw <- efvs; auto. }

  assert (cover_vars (subst B' x t) s) as cov'.
  { allrw @cover_vars_eq; allrw subvars_eq.
    introv i; apply cs.
    allrw @eqset_free_vars_disjoint; allsimpl.
    rw <- efvs in i; auto. }

  pose proof (simple_lsubstc_subst_ex t x B' wf' s cov' wt ct q0) as h.
  exrepnd.

  allrw @nt_wf_eq.
  dup wb as wfb.
  apply ewf in wfb.

  assert (cover_vars_upto B (csub_filter s [x]) [x]) as covb.
  { clear h1; allunfold @cover_vars_upto; allsimpl.
    rw efvs; auto. }

  exists wfb covb.

  assert (alphaeqc
            (lsubstc (subst B x t) ws s cs)
            (lsubstc (subst B' x t) wf' s cov')) as aeq1.
  { unfold alphaeqc; simpl.
    repeat (apply lsubst_alpha_congr2); auto. }

  eapply alphaeqc_trans;[eauto|]; clear aeq1.
  rw h1; clear h1.

  unfold alphaeqc; simpl.
  repeat (apply lsubst_alpha_congr2); eauto 3 with slow.
Qed.

Ltac lsubstc_subst_aeq :=
  match goal with
    | [ |- context[lsubstc (subst ?B ?x ?t) ?ws ?s ?cs] ] =>
      let eq := fresh "eq" in
      let h  := fresh "h"  in
      let wb := fresh "wb" in
      let cb := fresh "cb" in
      let wt := fresh "wt" in
      let ct := fresh "ct" in
      assert (wf_term t) as wt by auto;
        assert (cover_vars t s) as ct by auto;
        pose proof (aeq_simple_lsubstc_subst_ex t x B ws s cs wt ct) as eq;
        destruct eq as [wb eq]; destruct eq as [cb eq];
        rwg eq; clear eq

    | [ H : context[lsubstc (subst ?B ?x ?t) ?ws ?s ?cs] |- _ ] =>
      let eq := fresh "eq" in
      let h  := fresh "h"  in
      let wb := fresh "wb" in
      let cb := fresh "cb" in
      let wt := fresh "wt" in
      let ct := fresh "ct" in
      assert (wf_term t) as wt by auto;
        assert (cover_vars t s) as ct by auto;
        pose proof (aeq_simple_lsubstc_subst_ex t x B ws s cs wt ct) as eq;
        destruct eq as [wb eq]; destruct eq as [cb eq];
        rwg_h H eq; clear eq
  end.

Ltac lsubstc_subst_aeq2 :=
  match goal with
    | [ |- context[lsubstc (subst ?B ?x ?t) ?ws ?s ?cs] ] =>
      let eq := fresh "eq" in
      let h  := fresh "h"  in
      let wb := fresh "wb" in
      let cb := fresh "cb" in
      let wt := fresh "wt" in
      let ct := fresh "ct" in
      assert (wf_term t) as wt;
        [ auto
        | assert (cover_vars t s) as ct;
          [ auto
          | pose proof (aeq_simple_lsubstc_subst_ex t x B ws s cs wt ct) as eq;
            destruct eq as [wb eq]; destruct eq as [cb eq];
            rwg eq; clear eq
          ]
        ]

    | [ H : context[lsubstc (subst ?B ?x ?t) ?ws ?s ?cs] |- _ ] =>
      let eq := fresh "eq" in
      let h  := fresh "h"  in
      let wb := fresh "wb" in
      let cb := fresh "cb" in
      let wt := fresh "wt" in
      let ct := fresh "ct" in
      assert (wf_term t) as wt;
        [ auto
        | assert (cover_vars t s) as ct;
          [ auto
          | pose proof (aeq_simple_lsubstc_subst_ex t x B ws s cs wt ct) as eq;
            destruct eq as [wb eq]; destruct eq as [cb eq];
            rwg_h H eq; clear eq
          ]
        ]
  end.
