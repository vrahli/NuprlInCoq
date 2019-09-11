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


Require Export alphaeq_sub.


Lemma lsubst_aux_alpha_congr2 {o} :
  forall (t1 t2 : @NTerm o) sub1 sub2,
    alpha_eq t1 t2
    -> disjoint (sub_free_vars sub1) (bound_vars t1)
    -> disjoint (sub_free_vars sub2) (bound_vars t2)
    -> alphaeq_sub sub1 sub2
    -> alpha_eq (lsubst_aux t1 sub1) (lsubst_aux t2 sub2).
Proof.
  introv aeq disj1 disj2 aeqsub.
  pose proof (lsubst_aux_alpha_congr t1 t2 (dom_sub sub1) (range sub1) (range sub2)) as h.
  allrw @length_dom.
  allrw @length_range.
  applydup @alphaeq_sub_implies_eq_doms in aeqsub as ed.
  applydup @alphaeq_sub_implies_eq_lengths in aeqsub as el.
  allrw <- @sub_free_vars_is_flat_map_free_vars_range.
  applydup @alphaeq_sub_implies_alpha_eq in aeqsub as br.
  repeat (autodimp h hyp).
  rw <- @sub_eta in h.
  rw ed in h.
  rw <- @sub_eta in h; auto.
Qed.

Lemma lsubst_alpha_congr3 {o} :
  forall (t1 t2 : @NTerm o) sub1 sub2,
    alpha_eq t1 t2
    -> alphaeq_sub sub1 sub2
    -> alpha_eq (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv aeq aeqsub.
  pose proof (unfold_lsubst sub1 t1) as h.
  pose proof (unfold_lsubst sub2 t2) as k.
  exrepnd.
  rw k0; rw h0.
  apply lsubst_aux_alpha_congr2; eauto with slow.
Qed.

Lemma lsubst_alpha_congr4 {o} :
  forall l1 l2 (t1 t2 : @NTerm o) sub1 sub2,
    alpha_eq_bterm (bterm l1 t1) (bterm l2 t2)
    -> alphaeq_sub_range sub1 sub2
    -> l1 = dom_sub sub1
    -> l2 = dom_sub sub2
    -> alpha_eq (lsubst t1 sub1) (lsubst t2 sub2).
Proof.
  introv aeq aeqsub e1 e2; subst.
  inversion aeq as [? ? ? ? ? disj len1 len2 norep a]; subst; clear aeq.
  allrw @length_dom.
  apply (lsubst_alpha_congr3
          _ _
          (combine lv (range sub1))
          (combine lv (range sub2))) in a.

  - pose proof (lsubst_nest_same_alpha t1 (dom_sub sub1) lv (range sub1)) as h1.
    allrw @length_dom.
    allrw @length_range.
    allrw disjoint_app_r; repnd.
    repeat (autodimp h1 hyp).

    pose proof (lsubst_nest_same_alpha t2 (dom_sub sub2) lv (range sub2)) as h2.
    allrw @length_dom.
    allrw @length_range.
    allrw disjoint_app_r; repnd.
    repeat (autodimp h2 hyp); try omega.

    allrw <- @sub_eta.
    eapply alpha_eq_trans;[apply alpha_eq_sym; exact h1|].
    eapply alpha_eq_trans;[|exact h2]; auto.

  - apply alphaeq_sub_range_implies_alphaeq_sub; auto.
Qed.
