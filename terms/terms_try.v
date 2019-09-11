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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export csubst.


Lemma lsubstc_mk_try {o} :
  forall (t1 t2 : @NTerm o) x v sub,
  forall w1 : wf_term t1,
  forall w2 : wf_term t2,
  forall wv : wf_term v,
  forall w  : wf_term (mk_try t1 t2 x v),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall cv : cover_vars_upto v (csub_filter sub [x]) [x],
  forall c  : cover_vars (mk_try t1 t2 x v) sub,
    lsubstc (mk_try t1 t2 x v) w sub c
    = mkc_try (lsubstc t1 w1 sub c1)
              (lsubstc t2 w2 sub c2)
              x
              (lsubstc_vars v wv (csub_filter sub [x]) [x] cv).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl;
  change_to_lsubst_aux4; simpl;
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub; tcsp.
Qed.

Lemma cover_vars_try {p} :
  forall a n v b sub,
    @cover_vars p (mk_try a n v b) sub
    <=> cover_vars a sub
        # cover_vars n sub
        # cover_vars_upto b (csub_filter sub [v]) [v].
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  allrw remove_nvars_nil_l; allrw app_nil_r.
  allrw subvars_app_l.
  rw subvars_remove_nvars; simpl.
  rw @dom_csub_csub_filter.
  assert (v :: remove_nvars [v] (dom_csub sub)
          = [v] ++ remove_nvars [v] (dom_csub sub)) as eq by auto.
  rw eq.
  rw subvars_app_remove_nvars_r.
  rw subvars_swap_r; sp.
Qed.

Lemma lsubstc_mk_try_ex {o} :
  forall (t1 t2 : @NTerm o) x v sub,
  forall w : wf_term (mk_try t1 t2 x v),
  forall c : cover_vars (mk_try t1 t2 x v) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {wv : wf_term v
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {cv : cover_vars_upto v (csub_filter sub [x]) [x]
   & lsubstc (mk_try t1 t2 x v) w sub c
     = mkc_try (lsubstc t1 w1 sub c1)
               (lsubstc t2 w2 sub c2)
               x
               (lsubstc_vars v wv (csub_filter sub [x]) [x] cv)}}}}}}.
Proof.
  introv.

  duplicate w.
  apply wf_try_iff in w; repnd.
  exists w1 w2 w.

  duplicate c.
  apply cover_vars_try in c; repnd.
  exists c1 c2 c.
  apply lsubstc_mk_try.
Qed.


(*
*** Local Variables:
*** coq-load-path: ("." "../util/")
*** End:
*)
