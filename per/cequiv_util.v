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
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export lsubst_hyps.

Fixpoint csub_keep {o} (sub : @CSub o) (vars : list NVar) : CSub :=
  match sub with
  | nil => nil
  | (v, t) :: xs =>
      if memvar v vars
      then (v, t) :: csub_keep xs vars
      else csub_keep xs vars
  end.

Lemma csub2sub_csub_keep {o} :
  forall (s : @CSub o) vs,
    csub2sub (csub_keep s vs) = sub_keep (csub2sub s) vs.
Proof.
  induction s; introv; simpl; auto.
  destruct a; simpl; boolvar; simpl; auto.
  f_equal; auto.
Qed.

Lemma lsubstc_csub_filter_free_vars {o} :
  forall (t : @NTerm o) w s c,
    {c' : cover_vars t (csub_keep s (free_vars t))
     & lsubstc t w s c = lsubstc t w (csub_keep s (free_vars t)) c'}.
Proof.
  introv.

  pose proof (simple_lsubst_trim t (csub2sub s)) as e.
  autodimp e hyp.
  { introv i.
    apply in_csub2sub in i.
    destruct i as [cl wf]; rw cl; auto. }

  assert (cover_vars t (csub_keep s (free_vars t))) as c'.
  { allrw @cover_vars_eq; allrw @subvars_prop; introv i.
    applydup c in i.
    allrw <- @dom_csub_eq.
    rw @csub2sub_csub_keep.
    allrw @in_dom_sub_iff; exrepnd.
    exists t0.
    apply in_sub_keep; dands; auto. }

  exists c'.
  apply cterm_eq; simpl.
  unfold csubst; rw e.
  rw @csub2sub_csub_keep; auto.
Qed.

Lemma cequivc_lsubstc {o} :
  forall lib (t : @NTerm o) w (s1 s2 : CSub) c1 c2,
    isprogram (csubst t s1)
    -> isprogram (csubst t s2)
    -> cequiv_csub lib s1 s2
    -> cequivc lib (lsubstc t w s1 c1) (lsubstc t w s2 c2).
Proof.
  introv isp1 isp2 ceq.
  unfold cequivc; simpl.
  unfold cequivc.
  apply cequiv_lsubst; auto.
  apply cequiv_subst_iff_cequiv_csub; auto.
Qed.

Fixpoint csub_find {o} (s : @CSub o) (var : NVar) : option CTerm :=
  match s with
  | [] => None
  | (v, t) :: xs => if beq_var v var then Some t else csub_find xs var
  end.

Lemma csub_find_as_sub_find {o} :
  forall (s : @CSub o) (v : NVar),
    sub_find (csub2sub s) v
    = match csub_find s v with
      | Some t => Some (get_cterm t)
      | None => None
      end.
Proof.
  induction s; introv; simpl; auto.
  destruct a; simpl; boolvar; auto.
Qed.

Lemma implies_cequiv_csub_if_eq_doms {o} :
  forall lib (s1 s2 : @CSub o),
    no_repeats (dom_csub s1)
    -> dom_csub s1 = dom_csub s2
    -> (forall v t1 t2,
           csub_find s1 v = Some t1
           -> csub_find s2 v = Some t2
           -> cequivc lib t1 t2)
    -> cequiv_csub lib s1 s2.
Proof.
  induction s1; introv norep eqd imp; allsimpl.
  - destruct s2; allsimpl; GC; cpx.
  - destruct s2; allsimpl; GC; cpx.
    allrw @no_repeats_cons.
    destruct a, p; allsimpl; subst; ginv.
    constructor; auto.
    + pose proof (imp n0 c c0) as h; boolvar; repeat (autodimp h hyp).
    + apply IHs1; tcsp.
      introv e1 e2; repnd.
      pose proof (csub_find_as_sub_find s1 v) as h1.
      rw e1 in h1.
      apply sub_find_some in h1.
      apply in_dom_sub in h1.
      rw @dom_csub_eq in h1.
      apply (imp v); auto; repnd; boolvar; tcsp.
Qed.

Lemma dom_csub_csub_keep {o} :
  forall (s : @CSub o) vs,
    dom_csub (csub_keep s vs) = lKeep deq_nvar vs (dom_csub s).
Proof.
  induction s; introv; simpl; auto.
  destruct a; simpl; boolvar; allsimpl; try (rw IHs); tcsp.
Qed.

Lemma in_lkeep :
  forall {A} (a : A) deq keep s,
    LIn a (lKeep deq keep s) <=> (LIn a keep # LIn a s).
Proof.
  induction s; simpl; boolvar; simpl; try (rw IHs);
  split; intro h;
  repnd; repndors; subst; dands; tcsp.
Qed.

Lemma implies_no_repeats_lkeep :
  forall {A} deq keep (s : list A),
    no_repeats s
    -> no_repeats (lKeep deq keep s).
Proof.
  induction s; introv norep; allsimpl; auto.
  allrw no_repeats_cons; repnd.
  boolvar; auto.
  constructor; auto.
  rw @in_lkeep; tcsp.
Qed.

Lemma no_repeats_snoc :
  forall {A} (x : A) l,
    no_repeats (snoc l x) <=> (no_repeats l # !LIn x l).
Proof.
  induction l; simpl; tcsp.
  - rw no_repeats_cons; simpl; tcsp.
  - allrw @no_repeats_cons; allrw in_snoc; allrw not_over_or.
    rw IHl; split; sp.
Qed.

Lemma vswf_hypotheses_implies_no_repeats {o} :
  forall vs (H : @bhyps o),
    vswf_hypotheses vs H
    -> no_repeats (vars_hyps H).
Proof.
  induction H using rev_list_indT; introv wf; allsimpl; auto.
  allrw @vswf_hypotheses_snoc; repnd; allrw in_app_iff; allrw not_over_or; repnd.
  rw @vars_hyps_snoc.
  rw @no_repeats_snoc; tcsp.
Qed.

Lemma csub_find_csub_keep {o} :
  forall (s : @CSub o) vs v,
    csub_find (csub_keep s vs) v
    = if memvar v vs then csub_find s v
      else None.
Proof.
  induction s; introv; simpl; boolvar; tcsp; repnd; boolvar; allsimpl; GC;
  boolvar; auto; GC; tcsp; try (rw IHs); boolvar; tcsp.
Qed.

Lemma lsubstc_mk_var_if_csub_find {o} :
  forall v (s : @CSub o) w c t,
    csub_find s v = Some t
    -> lsubstc (mk_var v) w s c = t.
Proof.
  introv e.
  pose proof (csub_find_as_sub_find s v) as h.
  rw e in h.
  apply cterm_eq; simpl.
  unfold csubst; unflsubst; simpl; rw h; auto.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/" "../cequiv/" "../close/")
*** End:
*)
