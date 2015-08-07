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
  Authors: Abhishek Anand & Vincent Rahli & Mark Bickford

*)


Require Export csubst2.

Lemma lsubstc_mk_arithop {p} :
  forall op u v sub,
  forall w1 : wf_term u,
  forall w2 : @wf_term p v,
  forall w  : wf_term (mk_arithop op u v),
  forall c1 : cover_vars u sub,
  forall c2 : cover_vars v sub,
  forall c  : cover_vars (mk_arithop op u v) sub,
    lsubstc (mk_arithop op u v) w sub c
    = mkc_arithop op (lsubstc u w1 sub c1)(lsubstc v w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub. sp.
Qed.

Lemma lsubstc_mk_minus {p} :
  forall u sub,
  forall w1 : @wf_term p u,
  forall w  : wf_term (mk_minus u),
  forall c1 : cover_vars u sub,
  forall c  : cover_vars (mk_minus u) sub,
    lsubstc (mk_minus u) w sub c
    = mkc_minus (lsubstc u w1 sub c1).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub. sp.
Qed.

Lemma cover_vars_arithop {p} :
  forall op t1 t2 sub,
    cover_vars (@mk_arithop p op t1 t2) sub
    <=> cover_vars t1 sub
        # cover_vars t2 sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw app_nil_r. sp.

Qed.


Lemma cover_vars_minus {p} :
  forall t  sub,
    cover_vars (@mk_minus p t) sub
    <=> cover_vars t sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl.
  rw @remove_nvars_nil_l; rw app_nil_r.
  allrw subvars_app_l.
  allrw subvars_remove_nvars; simpl.
  allrw @dom_csub_csub_filter.
  allrw app_nil_r. sp.

Qed.

Lemma lsubstc_mk_arithop_ex {p} :
  forall op u v sub,
  forall w  : wf_term (@mk_arithop p op u v),
  forall c  : cover_vars (mk_arithop op u v) sub,
     {w1 : wf_term u
     & {w2 : wf_term v
     & {c1 : cover_vars u sub
     & {c2 : cover_vars v sub 
     & lsubstc (mk_arithop op u v) w sub c
          = mkc_arithop op (lsubstc u w1 sub c1) (lsubstc v w2 sub c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw @wf_arithop_iff in w; sp.

  duplicate c.
  rw @cover_vars_arithop in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_arithop.
Qed.


Lemma lsubstc_mk_minus_ex {p} :
  forall u sub,
  forall w  : wf_term (@mk_minus p u),
  forall c  : cover_vars (mk_minus u) sub,
     {w1 : wf_term u
     & {c1 : cover_vars u sub
     & lsubstc (mk_minus u) w sub c
          = mkc_minus (lsubstc u w1 sub c1) }}.
Proof.
  sp.

  duplicate w.
  (* Why does this not work?  when it's the same as
     rw @covers_vars_arithop in c in the previous lemma ?
  rw @wf_minus_iff in w0; sp. *)
  assert (wf_term u) as wf.
  pose proof (@wf_minus_iff p u) as z. apply z. auto.

  duplicate c.
  pose proof (@cover_vars_minus p u sub) as xx.
  assert (cover_vars u sub) as cv. 
  apply xx. auto.

  exists wf cv.
  apply lsubstc_mk_minus.
Qed.

Lemma lsubstc_mk_integer {p} :
  forall i sub,
  forall w  : wf_term (mk_integer i),
  forall c  : cover_vars (mk_integer i) sub,
    lsubstc (@mk_integer p i) w sub c
    = mkc_integer i.
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  auto.
Qed.

Lemma cover_vars_integer {p} :
  forall i sub,
    cover_vars (@mk_integer p i) sub.
Proof.
  sp; repeat (rw @cover_vars_eq); unfold cover_vars_upto; simpl. auto.
Qed.

