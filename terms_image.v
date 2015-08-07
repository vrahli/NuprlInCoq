(*

  Copyright 2014 Cornell University
  Copyright 201% Cornell University

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


Require Export alphaeq.
Require Export cvterm2.
Require Export terms_props.

Lemma fold_image {p} :
  forall (a b : @NTerm p), oterm (Can NImage) [ nobnd a, nobnd b ] = mk_image a b.
Proof.
  sp.
Qed.

Lemma lsubstc_mk_image {o} :
  forall A B sub,
  forall wA : wf_term A,
  forall wB : @wf_term o B,
  forall w  : wf_term (mk_image A B),
  forall cA : cover_vars A sub,
  forall cB : cover_vars B sub,
  forall c  : cover_vars (mk_image A B) sub,
   lsubstc (mk_image A B) w sub c =
             mkc_image (lsubstc A wA sub cA)
                         (lsubstc B wB sub cB).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r.
  allrw @fold_nobnd;
  rw @fold_image; auto.
Qed.

Lemma lsubstc_mk_image_ex {p} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_image p t1 t2),
  forall c  : cover_vars (mk_image t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_image t1 t2) w sub c
             = mkc_image (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_image_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_image_iff; sp. }

  assert (cover_vars t1 sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  assert (cover_vars t2 sub) as c2.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 w2 c1 c2.
  apply lsubstc_mk_image.
Qed.
