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


Require Export csubst3.
Require Export alphaeq3.


Lemma aeq_lsubstc_mk_subtype_ex {o} :
  forall (t1 t2 : @NTerm o)
         (sub : CSubstitution)
         (w : wf_term (mk_subtype t1 t2)) (c : cover_vars (mk_subtype t1 t2) sub),
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & alphaeqc (lsubstc (mk_subtype t1 t2) w sub c)
              (mkc_subtype (lsubstc t1 w1 sub c1) (lsubstc t2 w2 sub c2)) }}}}.
Proof.
  introv.
  pose proof (lsubstc_mk_subtype_ex t1 t2 sub w c) as h.
  exrepnd.
  exists w1 w2 c1 c2.
  rw h1.
  unfold alphaeqc; simpl.
  unfold mk_subtype, mk_vsubtype, mk_member, mk_equality, mk_function.
  repeat prove_alpha_eq4.
  pose proof (ex_fresh_var (all_vars (csubst t2 sub))) as fvs.
  exrepnd.
  apply (al_bterm_aux [v]); simpl; auto.
  { apply disjoint_singleton_l.
    allrw in_app_iff; allrw not_over_or; sp. }
  repeat (rw @lsubst_aux_trivial_cl_term2; eauto 3 with slow);
  apply cover_vars_iff_closed_lsubstc; auto.
Qed.
