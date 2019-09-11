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


Require Export csubst.
Require Export terms5.


Definition mkc_fresh {o} (v : NVar) (t : @CVTerm o [v]) : CTerm :=
  let (a,x) := t in
    exist isprog (mk_fresh v a) (isprog_fresh_implies v a x).

Lemma cover_vars_fresh {p} :
  forall v b sub,
    @cover_vars p (mk_lam v b) sub
    <=> cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw app_nil_r.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma lsubstc_mk_fresh {p} :
  forall v b sub,
  forall w1 : wf_term b,
  forall w  : wf_term (mk_fresh v b),
  forall c1 : cover_vars_upto b (@csub_filter p sub [v]) [v],
  forall c  : cover_vars (mk_fresh v b) sub,
    lsubstc (mk_fresh v b) w sub c
    = mkc_fresh v (lsubstc_vars b w1 (csub_filter sub [v]) [v] c1).
Proof.
  unfold lsubstc; simpl; sp.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_csub2sub.
  rw @fold_fresh; sp.
Qed.

Lemma lsubstc_mk_fresh_ex {p} :
  forall v b sub,
  forall w  : wf_term (@mk_fresh p v b),
  forall c  : cover_vars (mk_fresh v b) sub,
    {w' : wf_term b
     & {c' : cover_vars_upto b (csub_filter sub [v]) [v]
        & lsubstc (mk_fresh v b) w sub c
             = mkc_fresh v (lsubstc_vars b w' (csub_filter sub [v]) [v] c')}}.
Proof.
  sp.

  duplicate w.
  rw @wf_fresh_iff in w; sp.

  duplicate c.
  rw @cover_vars_fresh in c; sp.

  exists w c.
  apply lsubstc_mk_fresh.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/" "../terms/" "../computation/")
*** End:
*)
