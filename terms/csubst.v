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


Require Export substitution4.
Require Export alphaeq2.


Lemma wf_sub_csub2sub {p} :
  forall sub, wf_sub (@csub2sub p sub).
Proof.
  introv lin.
  apply in_csub2sub in lin.
  unfold isprogram in lin; sp.
Qed.
Hint Immediate wf_sub_csub2sub.

Theorem csubst_preserves_wf_term {p} :
  forall sub t,
    @wf_term p t
    -> wf_term (csubst t sub).
Proof.
  introv wt.
  unfold csubst.
  apply lsubst_preserves_wf_term; sp.
Qed.

Lemma csubst_wf_term {p} :
  forall t sub,
    wf_term (@csubst p t sub)
    -> wf_term t.
Proof.
  sp.
  allrw @wf_term_eq.
  apply @lsubst_nt_wf with (sub := csub2sub sub); sp.
Qed.

Lemma lsubstc_csubst_ex {o} :
  forall (t : @NTerm o) sub1 sub2 w p,
    {w' : wf_term t & {p' : cover_vars t (sub1 ++ sub2) &
      lsubstc (csubst t sub1) w sub2 p = lsubstc t w' (sub1 ++ sub2) p'}}.
Proof.
  sp.
  assert (nt_wf (csubst t sub1)) as wf by (rw @nt_wf_eq; sp).

  apply lsubst_nt_wf in wf.
  rw @nt_wf_eq in wf.

  assert (cover_vars t (sub1 ++ sub2)) as c.
  allrw @cover_vars_eq.
  apply free_vars_csubst_sub in p.
  allrw @dom_csub_app; sp.

  exists wf c.

  unfold lsubstc.
  apply cterm_eq; simpl.
  apply csubst_app.
Qed.

Lemma lsubstc_csubst_eq {o} :
  forall t sub1 sub2 w w' p p',
      lsubstc (@csubst o t sub1) w sub2 p = lsubstc t w' (sub1 ++ sub2) p'.
Proof.
  intros.
  generalize (lsubstc_csubst_ex t sub1 sub2 w p); sp.
  rw e.
  apply lsubstc_eq; auto.
Qed.

Lemma lsubstc_csubst_ex2 {o} :
  forall t sub1 sub2 w p,
    {w' : wf_term (@csubst o t sub1) &
    {p' : cover_vars (csubst t sub1) sub2 &
      lsubstc (csubst t sub1) w' sub2 p' = lsubstc t w (sub1 ++ sub2) p}}.
Proof.
  sp.
  assert (wf_term (csubst t sub1)) as w'.
  apply wf_term_csubst; sp.
  assert (cover_vars (csubst t sub1) sub2) as p'.
  rw <- @cover_vars_csubst; sp.
  exists w' p'.
  apply lsubstc_csubst_eq.
Qed.

Lemma lsubstc_mk_axiom {o} :
  forall p sub c,
    lsubstc mk_axiom p sub c = @mkc_axiom o.
Proof.
  unfold lsubstc, mkc_axiom; sp.
  apply cterm_eq; sp.
Qed.

Lemma csubst_mk_bottom {p} :
  forall sub, @csubst p mk_bottom sub = mk_bottom.
Proof. intro.
 apply @csubst_trivial . simpl. eauto.
Qed.

Lemma lsubstc_mk_bottom {o} :
  forall p sub c,
    lsubstc mk_bottom p sub c = @mkc_bottom o.
Proof.
  unfold lsubstc, mkc_bottom; sp.
  apply cterm_eq; sp. simpl. apply csubst_mk_bottom.
Qed.

Lemma lsubstc_mk_uni {o} :
  forall i p sub c,
    lsubstc (mk_uni i) p sub c = @mkc_uni o i.
Proof.
  unfold lsubstc, mkc_uni; sp.
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_base {o} :
  forall p sub c,
    lsubstc mk_base p sub c = @mkc_base o.
Proof.
  unfold lsubstc, mkc_base, mkc_base; sp.
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_atom {o} :
  forall p sub c,
    lsubstc mk_atom p sub c = @mkc_atom o.
Proof.
  unfold lsubstc, mkc_atom, mkc_atom; sp.
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_uatom {o} :
  forall p sub c,
    lsubstc mk_uatom p sub c = @mkc_uatom o.
Proof.
  unfold lsubstc, mkc_uatom, mkc_uatom; sp.
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_token {o} :
  forall s p sub c,
    lsubstc (mk_token s) p sub c = @mkc_token o s.
Proof.
  unfold lsubstc, mkc_token; sp.
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_utoken {o} :
  forall s p sub c,
    lsubstc (mk_utoken s) p sub c = @mkc_utoken o s.
Proof.
  unfold lsubstc, mkc_utoken; sp.
  apply cterm_eq; sp.
Qed.

Lemma csubst_mk_false {o} :
  forall sub, csubst mk_false sub = @mk_false o.
Proof.
  intro; unfold csubst; simpl; fold @mk_axiom.
  change_to_lsubst_aux4; simpl.
  repeat (rewrite sub_filter_nil_r).
  assert (sub_find (csub2sub sub) nvarx = None [+] LIn nvarx [nvarx]) as or by (simpl; sp).
  rw <- @sub_find_sub_filter_none in or.
  rewrite or; sp.
Qed.

Lemma lsubstc_mk_false {o} :
  forall p sub c,
    lsubstc mk_false p sub c = @mkc_false o.
Proof.
  unfold lsubstc, mkc_false; sp.
  apply cterm_eq; simpl.
  apply csubst_mk_false; auto.
Qed.

Lemma lsubstc_mk_free_from_atom {o} :
  forall t1 t2 T sub,
  forall w1 : @wf_term o t1,
  forall w2 : wf_term t2,
  forall wT : wf_term T,
  forall w  : wf_term (mk_free_from_atom t1 t2 T),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall cT : cover_vars T sub,
  forall c  : cover_vars (mk_free_from_atom t1 t2 T) sub,
    lsubstc (mk_free_from_atom t1 t2 T) w sub c
    = mkc_free_from_atom (lsubstc t1 w1 sub c1)
                   (lsubstc t2 w2 sub c2)
                   (lsubstc T wT sub cT).
Proof.
  sp; unfold lsubstc; simpl.
  assert (csubst (mk_free_from_atom t1 t2 T) sub
          = mk_free_from_atom (csubst t1 sub) (csubst t2 sub) (csubst T sub))
         by (unfold csubst; simpl;
             change_to_lsubst_aux4; simpl;
             rw @sub_filter_nil_r;
             allrw @fold_nobnd;
             rw @fold_free_from_atom; sp).
  apply cterm_eq; auto.
Qed.

Lemma lsubstc_mk_free_from_atom_ex {o} :
  forall t1 t2 T sub,
  forall w  : wf_term (@mk_free_from_atom o t1 t2 T),
  forall c  : cover_vars (mk_free_from_atom t1 t2 T) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {wT : wf_term T
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {cT : cover_vars T sub
      & lsubstc (mk_free_from_atom t1 t2 T) w sub c
           = mkc_free_from_atom (lsubstc t1 w1 sub c1)
                          (lsubstc t2 w2 sub c2)
                          (lsubstc T wT sub cT)}}}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_free_from_atom_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_free_from_atom_iff; sp. }

  assert (wf_term T) as w3.
  { allrw <- @wf_free_from_atom_iff; sp. }

  assert (cover_vars t1 sub) as c1.
  { unfold cover_vars in c; allsimpl.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  assert (cover_vars t2 sub) as c2.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  assert (cover_vars T sub) as c3.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 w2 w3 c1 c2 c3.
  apply lsubstc_mk_free_from_atom.
Qed.

Lemma lsubstc_mk_efree_from_atom {o} :
  forall t1 t2 T sub,
  forall w1 : @wf_term o t1,
  forall w2 : wf_term t2,
  forall wT : wf_term T,
  forall w  : wf_term (mk_efree_from_atom t1 t2 T),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall cT : cover_vars T sub,
  forall c  : cover_vars (mk_efree_from_atom t1 t2 T) sub,
    lsubstc (mk_efree_from_atom t1 t2 T) w sub c
    = mkc_efree_from_atom (lsubstc t1 w1 sub c1)
                   (lsubstc t2 w2 sub c2)
                   (lsubstc T wT sub cT).
Proof.
  sp; unfold lsubstc; simpl.
  assert (csubst (mk_efree_from_atom t1 t2 T) sub
          = mk_efree_from_atom (csubst t1 sub) (csubst t2 sub) (csubst T sub))
         by (unfold csubst; simpl;
             change_to_lsubst_aux4; simpl;
             rw @sub_filter_nil_r;
             allrw @fold_nobnd;
             rw @fold_efree_from_atom; sp).
  apply cterm_eq; auto.
Qed.

Lemma lsubstc_mk_efree_from_atom_ex {o} :
  forall t1 t2 T sub,
  forall w  : wf_term (@mk_efree_from_atom o t1 t2 T),
  forall c  : cover_vars (mk_efree_from_atom t1 t2 T) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {wT : wf_term T
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {cT : cover_vars T sub
      & lsubstc (mk_efree_from_atom t1 t2 T) w sub c
           = mkc_efree_from_atom (lsubstc t1 w1 sub c1)
                          (lsubstc t2 w2 sub c2)
                          (lsubstc T wT sub cT)}}}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_efree_from_atom_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_efree_from_atom_iff; sp. }

  assert (wf_term T) as w3.
  { allrw <- @wf_efree_from_atom_iff; sp. }

  assert (cover_vars t1 sub) as c1.
  { unfold cover_vars in c; allsimpl.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  assert (cover_vars t2 sub) as c2.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  assert (cover_vars T sub) as c3.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 w2 w3 c1 c2 c3.
  apply lsubstc_mk_efree_from_atom.
Qed.

Lemma lsubstc_mk_free_from_atoms {o} :
  forall t1 t2 sub,
  forall w1 : @wf_term o t1,
  forall w2 : wf_term t2,
  forall w  : wf_term (mk_free_from_atoms t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_free_from_atoms t1 t2) sub,
    lsubstc (mk_free_from_atoms t1 t2) w sub c
    = mkc_free_from_atoms (lsubstc t1 w1 sub c1)
                          (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  assert (csubst (mk_free_from_atoms t1 t2) sub
          = mk_free_from_atoms (csubst t1 sub) (csubst t2 sub))
         by (unfold csubst; simpl;
             change_to_lsubst_aux4; simpl;
             rw @sub_filter_nil_r;
             allrw @fold_nobnd;
             rw @fold_free_from_atoms; sp).
  apply cterm_eq; auto.
Qed.

Lemma lsubstc_mk_free_from_atoms_ex {o} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_free_from_atoms o t1 t2),
  forall c  : cover_vars (mk_free_from_atoms t1 t2) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
      & lsubstc (mk_free_from_atoms t1 t2) w sub c
           = mkc_free_from_atoms (lsubstc t1 w1 sub c1)
                          (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_free_from_atoms_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_free_from_atoms_iff; sp. }

  assert (cover_vars t1 sub) as c1.
  { unfold cover_vars in c; allsimpl.
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
  apply lsubstc_mk_free_from_atoms.
Qed.

Lemma lsubstc_mk_equality {o} :
  forall t1 t2 T sub,
  forall w1 : @wf_term o t1,
  forall w2 : wf_term t2,
  forall wT : wf_term T,
  forall w  : wf_term (mk_equality t1 t2 T),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall cT : cover_vars T sub,
  forall c  : cover_vars (mk_equality t1 t2 T) sub,
    lsubstc (mk_equality t1 t2 T) w sub c
    = mkc_equality (lsubstc t1 w1 sub c1)
                   (lsubstc t2 w2 sub c2)
                   (lsubstc T wT sub cT).
Proof.
  sp; unfold lsubstc; simpl.
  assert (csubst (mk_equality t1 t2 T) sub
          = mk_equality (csubst t1 sub) (csubst t2 sub) (csubst T sub))
         by (unfold csubst; simpl;
             change_to_lsubst_aux4; simpl;
             rw @sub_filter_nil_r;
             allrw @fold_nobnd;
             rw @fold_equality; sp).
  apply cterm_eq; auto.
Qed.

Lemma lsubstc_mk_equality_ex {o} :
  forall t1 t2 T sub,
  forall w  : wf_term (@mk_equality o t1 t2 T),
  forall c  : cover_vars (mk_equality t1 t2 T) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {wT : wf_term T
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {cT : cover_vars T sub
      & lsubstc (mk_equality t1 t2 T) w sub c
           = mkc_equality (lsubstc t1 w1 sub c1)
                          (lsubstc t2 w2 sub c2)
                          (lsubstc T wT sub cT)}}}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_equality_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_equality_iff; sp. }

  assert (wf_term T) as w3.
  { allrw <- @wf_equality_iff; sp. }

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

  assert (cover_vars T sub) as c3.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 w2 w3 c1 c2 c3.
  apply lsubstc_mk_equality.
Qed.

Lemma lsubstc_mk_member {o} :
  forall t T sub,
  forall wt : wf_term t,
  forall wT : @wf_term o T,
  forall w  : wf_term (mk_member t T),
  forall ct : cover_vars t sub,
  forall cT : cover_vars T sub,
  forall c  : cover_vars (mk_member t T) sub,
    lsubstc (mk_member t T) w sub c
    = mkc_member (lsubstc t wt sub ct)
                 (lsubstc T wT sub cT).
Proof.
  unfold mk_member; sp.
  rw <- @fold_mkc_member.
  apply lsubstc_mk_equality.
Qed.

Lemma lsubstc_mk_member_ex {o} :
  forall t T sub,
  forall w  : wf_term (@mk_member o t T),
  forall c  : cover_vars (mk_member t T) sub,
    {wt : wf_term t
     & {wT : wf_term T
     & {ct : cover_vars t sub
     & {cT : cover_vars T sub
        & lsubstc (mk_member t T) w sub c
             = mkc_member (lsubstc t wt sub ct)
                          (lsubstc T wT sub cT)}}}}.
Proof.
  unfold mk_member; sp.
  generalize (lsubstc_mk_equality_ex t t T sub w c); sp.
  rewrite @lsubstc_replace with (w2 := w2) (p2 := c2) in e.
  exists w2 wT c2 cT; sp.
  rw <- @fold_mkc_member; sp.
Qed.

Lemma lsubstc_mk_requality {o} :
  forall t1 t2 T sub,
  forall w1 : @wf_term o t1,
  forall w2 : wf_term t2,
  forall wT : wf_term T,
  forall w  : wf_term (mk_requality t1 t2 T),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall cT : cover_vars T sub,
  forall c  : cover_vars (mk_equality t1 t2 T) sub,
    lsubstc (mk_requality t1 t2 T) w sub c
    = mkc_requality (lsubstc t1 w1 sub c1)
                    (lsubstc t2 w2 sub c2)
                    (lsubstc T wT sub cT).
Proof.
  sp; unfold lsubstc; simpl.
  assert (csubst (mk_requality t1 t2 T) sub
          = mk_requality (csubst t1 sub) (csubst t2 sub) (csubst T sub))
    by (unfold csubst; simpl;
        change_to_lsubst_aux4; simpl;
        rw @sub_filter_nil_r;
        allrw @fold_nobnd;
        rw @fold_requality; sp).
  apply cterm_eq; auto.
Qed.

Lemma lsubstc_mk_requality_ex {o} :
  forall t1 t2 T sub,
  forall w  : wf_term (@mk_requality o t1 t2 T),
  forall c  : cover_vars (mk_requality t1 t2 T) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {wT : wf_term T
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {cT : cover_vars T sub
      & lsubstc (mk_requality t1 t2 T) w sub c
        = mkc_requality (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)
                        (lsubstc T wT sub cT)}}}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_requality_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_requality_iff; sp. }

  assert (wf_term T) as w3.
  { allrw <- @wf_requality_iff; sp. }

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

  assert (cover_vars T sub) as c3.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 w2 w3 c1 c2 c3.
  apply lsubstc_mk_requality.
Qed.

Lemma lsubstc_mk_rmember {o} :
  forall t T sub,
  forall wt : wf_term t,
  forall wT : @wf_term o T,
  forall w  : wf_term (mk_rmember t T),
  forall ct : cover_vars t sub,
  forall cT : cover_vars T sub,
  forall c  : cover_vars (mk_rmember t T) sub,
    lsubstc (mk_rmember t T) w sub c
    = mkc_rmember (lsubstc t wt sub ct)
                  (lsubstc T wT sub cT).
Proof.
  unfold mk_rmember; sp.
  rw <- @fold_mkc_rmember.
  apply lsubstc_mk_requality.
Qed.

Lemma lsubstc_mk_rmember_ex {o} :
  forall t T sub,
  forall w  : wf_term (@mk_rmember o t T),
  forall c  : cover_vars (mk_rmember t T) sub,
    {wt : wf_term t
     & {wT : wf_term T
     & {ct : cover_vars t sub
     & {cT : cover_vars T sub
        & lsubstc (mk_rmember t T) w sub c
          = mkc_rmember (lsubstc t wt sub ct)
                        (lsubstc T wT sub cT)}}}}.
Proof.
  unfold mk_rmember; sp.
  generalize (lsubstc_mk_requality_ex t t T sub w c); sp.
  rewrite @lsubstc_replace with (w2 := w2) (p2 := c2) in e.
  exists w2 wT c2 cT; sp.
  rw <- @fold_mkc_rmember; sp.
Qed.

Lemma lsubstc_mk_tequality {o} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term o t2,
  forall w  : wf_term (mk_tequality t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_tequality t1 t2) sub,
    lsubstc (mk_tequality t1 t2) w sub c
    = mkc_tequality (lsubstc t1 w1 sub c1)
                    (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  assert (csubst (mk_tequality t1 t2) sub
          = mk_tequality (csubst t1 sub) (csubst t2 sub))
         by (unfold csubst; simpl;
             change_to_lsubst_aux4; simpl;
             rw @sub_filter_nil_r; sp).
  apply cterm_eq; auto.
Qed.

Lemma lsubstc_mk_tequality_ex {o} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_tequality o t1 t2),
  forall c  : cover_vars (mk_tequality t1 t2) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
      & lsubstc (mk_tequality t1 t2) w sub c
           = mkc_tequality (lsubstc t1 w1 sub c1)
                           (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_tequality_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_tequality_iff; sp. }

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
  apply lsubstc_mk_tequality.
Qed.

Lemma lsubstc_mk_type {o} :
  forall t sub,
  forall wt : @wf_term o t,
  forall w  : wf_term (mk_type t),
  forall ct : cover_vars t sub,
  forall c  : cover_vars (mk_type t) sub,
    lsubstc (mk_type t) w sub c
    = mkc_type (lsubstc t wt sub ct).
Proof.
  unfold mk_type; sp.
  rw <- @fold_mkc_type.
  apply lsubstc_mk_tequality.
Qed.

Lemma lsubstc_mk_type_ex {o} :
  forall t sub,
  forall w  : wf_term (@mk_type o t),
  forall c  : cover_vars (mk_type t) sub,
    {wt : wf_term t
     & {ct : cover_vars t sub
        & lsubstc (mk_type t) w sub c
             = mkc_type (lsubstc t wt sub ct)}}.
Proof.
  unfold mk_type; sp.
  generalize (lsubstc_mk_tequality_ex t t sub w c); sp.
  rewrite @lsubstc_replace with (w2 := w2) (p2 := c2) in e.
  exists w2 c2; sp.
  rw <- @fold_mkc_type; sp.
Qed.

Lemma lsubstc_mk_approx {o} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term o t2,
  forall w  : wf_term (mk_approx t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_approx t1 t2) sub,
    lsubstc (mk_approx t1 t2) w sub c
    = mkc_approx (lsubstc t1 w1 sub c1)
                 (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r.
  allrw @fold_nobnd.
  rw @fold_approx; sp.
Qed.

Lemma lsubstc_mk_approx_ex {o} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_approx o t1 t2),
  forall c  : cover_vars (mk_approx t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_approx t1 t2) w sub c
             = mkc_approx (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_approx_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_approx_iff; sp. }

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
  apply lsubstc_mk_approx.
Qed.

Lemma lsubstc_mk_cequiv {o} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term o t2,
  forall w  : wf_term (mk_cequiv t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_cequiv t1 t2) sub,
    lsubstc (mk_cequiv t1 t2) w sub c
    = mkc_cequiv (lsubstc t1 w1 sub c1)
                  (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r.
  allrw @fold_nobnd.
  rw @fold_cequiv; sp.
Qed.

Lemma lsubstc_mk_cequiv_ex {p} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_cequiv p t1 t2),
  forall c  : cover_vars (mk_cequiv t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_cequiv t1 t2) w sub c
             = mkc_cequiv (lsubstc t1 w1 sub c1)
                           (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_cequiv_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_cequiv_iff; sp. }

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
  apply lsubstc_mk_cequiv.
Qed.

Lemma lsubstc_mk_pair {p} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_pair t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_pair t1 t2) sub,
    lsubstc (mk_pair t1 t2) w sub c
    = mkc_pair (lsubstc t1 w1 sub c1)
               (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r.
  allrw @fold_nobnd.
  rw @fold_pair; sp.
Qed.

Lemma lsubstc_mk_pair_ex {p} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_pair p t1 t2),
  forall c  : cover_vars (mk_pair t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_pair t1 t2) w sub c
             = mkc_pair (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw @wf_pair; sp. }

  assert (wf_term t2) as w2.
  { allrw @wf_pair; sp. }

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
  apply lsubstc_mk_pair.
Qed.

Lemma lsubstc_mk_sup {p} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_sup t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_sup t1 t2) sub,
    lsubstc (mk_sup t1 t2) w sub c
    = mkc_sup (lsubstc t1 w1 sub c1)
              (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r.
  allrw @fold_nobnd.
  rw @fold_sup; sp.
Qed.

Lemma lsubstc_mk_sup_ex {p} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_sup p t1 t2),
  forall c  : cover_vars (mk_sup t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_sup t1 t2) w sub c
             = mkc_sup (lsubstc t1 w1 sub c1)
                       (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw @wf_sup_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw @wf_sup_iff; sp. }

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
  apply lsubstc_mk_sup.
Qed.

Lemma lsubstc_mk_refl {p} :
  forall (t1 : @NTerm p) sub,
  forall w1 : wf_term t1,
  forall w  : wf_term (mk_refl t1),
  forall c1 : cover_vars t1 sub,
  forall c  : cover_vars (mk_refl t1) sub,
    lsubstc (mk_refl t1) w sub c
    = mkc_refl (lsubstc t1 w1 sub c1).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r.
  allrw @fold_nobnd.
  rw @fold_refl; sp.
Qed.

Lemma lsubstc_mk_refl_ex {p} :
  forall t1 sub,
  forall w  : wf_term (@mk_refl p t1),
  forall c  : cover_vars (mk_refl t1) sub,
    {w1 : wf_term t1
     & {c1 : cover_vars t1 sub
        & lsubstc (mk_refl t1) w sub c
          = mkc_refl (lsubstc t1 w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw @wf_refl_iff; sp. }

  assert (cover_vars t1 sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_refl.
Qed.

Lemma lsubstc_mk_texc {o} :
  forall (t1 t2 : @NTerm o) sub,
  forall w1 : wf_term t1,
  forall w2 : wf_term t2,
  forall w  : wf_term (mk_texc t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_texc t1 t2) sub,
    lsubstc (mk_texc t1 t2) w sub c
    = mkc_texc (lsubstc t1 w1 sub c1)
               (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  allrw @fold_nobnd.
  rw @sub_filter_nil_r; sp.
Qed.

Lemma wf_texc {p} :
  forall a b : @NTerm p, wf_term (mk_texc a b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [|?| o l bw e]; subst.
  generalize (bw (nobnd a)) (bw (nobnd b)); simpl; intros bw1 bw2.
  autodimp bw1 hyp.
  autodimp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma lsubstc_mk_texc_ex {o} :
  forall (t1 t2 : @NTerm o) sub,
  forall w  : wf_term (mk_texc t1 t2),
  forall c  : cover_vars (mk_texc t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
     & lsubstc (mk_texc t1 t2) w sub c
       = mkc_texc (lsubstc t1 w1 sub c1)
                  (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw @wf_texc; sp. }

  assert (wf_term t2) as w2.
  { allrw @wf_texc; sp. }

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
  apply lsubstc_mk_texc.
Qed.

Lemma lsubstc_mk_union {p} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_union t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_union t1 t2) sub,
    lsubstc (mk_union t1 t2) w sub c
    = mkc_union (lsubstc t1 w1 sub c1)
                (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  allrw @fold_nobnd.
  rw @sub_filter_nil_r; sp.
Qed.

Lemma wf_union {p} :
  forall a b : @NTerm p, wf_term (mk_union a b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [|?| o l bw e]; subst.
  generalize (bw (nobnd a)) (bw (nobnd b)); simpl; intros bw1 bw2.
  autodimp bw1 hyp.
  autodimp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma lsubstc_mk_union_ex {p} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_union p t1 t2),
  forall c  : cover_vars (mk_union t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_union t1 t2) w sub c
          = mkc_union (lsubstc t1 w1 sub c1)
                      (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw @wf_union; sp. }

  assert (wf_term t2) as w2.
  { allrw @wf_union; sp. }

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
  apply lsubstc_mk_union.
Qed.

Lemma lsubstc_mk_eunion {p} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_eunion t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_eunion t1 t2) sub,
    lsubstc (mk_eunion t1 t2) w sub c
    = mkc_eunion (lsubstc t1 w1 sub c1)
                 (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  allrw @fold_nobnd.
  rw @sub_filter_nil_r; sp.
Qed.

Lemma wf_eunion {p} :
  forall a b : @NTerm p, wf_term (mk_eunion a b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [|?| o l bw e]; subst.
  generalize (bw (nobnd a)) (bw (nobnd b)); simpl; intros bw1 bw2.
  autodimp bw1 hyp.
  autodimp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma lsubstc_mk_eunion_ex {p} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_eunion p t1 t2),
  forall c  : cover_vars (mk_eunion t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_eunion t1 t2) w sub c
          = mkc_eunion (lsubstc t1 w1 sub c1)
                       (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw @wf_eunion; sp. }

  assert (wf_term t2) as w2.
  { allrw @wf_eunion; sp. }

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
  apply lsubstc_mk_eunion.
Qed.

Lemma lsubstc_mk_pertype {p} :
  forall R sub,
  forall w  : @wf_term p R,
  forall w' : wf_term (mk_pertype R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_pertype R) sub,
    lsubstc (mk_pertype R) w' sub c'
    = mkc_pertype (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r.
  allrw @fold_nobnd.
  rw @fold_pertype; sp.
Qed.

Lemma lsubstc_mk_pertype_ex {p} :
  forall R sub,
  forall w : wf_term (@mk_pertype p R),
  forall c : cover_vars (mk_pertype R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & lsubstc (mk_pertype R) w sub c
             = mkc_pertype (lsubstc R w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term R) as w1.
  { allrw <- @wf_pertype_iff; sp. }

  assert (cover_vars R sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_pertype.
Qed.

Lemma lsubstc_mk_exception {p} :
  forall (a R : @NTerm p) sub,
  forall wa : wf_term a,
  forall w  : wf_term R,
  forall w' : wf_term (mk_exception a R),
  forall c  : cover_vars R sub,
  forall ca : cover_vars a sub,
  forall c' : cover_vars (mk_exception a R) sub,
    lsubstc (mk_exception a R) w' sub c'
    = mkc_exception (lsubstc a wa sub ca) (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @fold_exception; sp.
Qed.

Lemma wf_exception_iff {p} :
  forall a b : @NTerm p, wf_term (mk_exception a b) <=> (wf_term a # wf_term b).
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [|?| o l bw e]; subst.
  generalize (bw (nobnd a)) (bw (nobnd b)); simpl; intros bw1 bw2.
  autodimp bw1 hyp.
  autodimp bw2 hyp.
  inversion bw1; subst.
  inversion bw2; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma lsubstc_mk_exception_ex {p} :
  forall a R sub,
  forall w : wf_term (@mk_exception p a R),
  forall c : cover_vars (mk_exception a R) sub,
    {w1 : wf_term a
     & {w2 : wf_term R
     & {c1 : cover_vars a sub
     & {c2 : cover_vars R sub
     & lsubstc (mk_exception a R) w sub c
       = mkc_exception (lsubstc a w1 sub c1) (lsubstc R w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term a) as w1.
  { allrw @wf_exception_iff; sp. }

  assert (wf_term R) as w2.
  { allrw @wf_exception_iff; sp. }

  assert (cover_vars a sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  assert (cover_vars R sub) as c2.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 w2 c1 c2.
  apply lsubstc_mk_exception.
Qed.

Lemma lsubstc_mk_sleep {p} :
  forall R sub,
  forall w  : @wf_term p R,
  forall w' : wf_term (mk_sleep R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_sleep R) sub,
    lsubstc (mk_sleep R) w' sub c'
    = mkc_sleep (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @fold_sleep; sp.
Qed.

Lemma wf_sleep_iff {p} :
  forall a : @NTerm p, wf_term (mk_sleep a) <=> wf_term a.
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [|?| o l bw e]; subst.
  generalize (bw (nobnd a)); simpl; intros bw1.
  autodimp bw1 hyp.
  inversion bw1; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma lsubstc_mk_sleep_ex {p} :
  forall R sub,
  forall w : wf_term (@mk_sleep p R),
  forall c : cover_vars (mk_sleep R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & lsubstc (mk_sleep R) w sub c
          = mkc_sleep (lsubstc R w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term R) as w1.
  { allrw @wf_sleep_iff; sp. }

  assert (cover_vars R sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_sleep.
Qed.

Lemma lsubstc_mk_squash {p} :
  forall R sub,
  forall w  : @wf_term p R,
  forall w' : wf_term (mk_squash R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_squash R) sub,
    lsubstc (mk_squash R) w' sub c'
    = mkc_squash (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd. sp.
Qed.

Lemma lsubstc_mk_squash_ex {p} :
  forall R sub,
  forall w : wf_term (@mk_squash p R),
  forall c : cover_vars (mk_squash R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & lsubstc (mk_squash R) w sub c
          = mkc_squash (lsubstc R w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term R) as w1.
  { allrw @wf_squash; sp. }

  assert (cover_vars R sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_squash.
Qed.

Lemma lsubstc_mk_ipertype {p} :
  forall R sub,
  forall w  : @wf_term p R,
  forall w' : wf_term (mk_ipertype R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_ipertype R) sub,
    lsubstc (mk_ipertype R) w' sub c'
    = mkc_ipertype (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  assert (csubst (mk_ipertype R) sub = mk_ipertype (csubst R sub))
         by (unfold csubst; simpl;
             change_to_lsubst_aux4; simpl;
             rw @sub_filter_nil_r; allrw @fold_nobnd;
             rw @fold_ipertype; sp).
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_ipertype_ex {p} :
  forall R sub,
  forall w : wf_term (@mk_ipertype p R),
  forall c : cover_vars (mk_ipertype R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & lsubstc (mk_ipertype R) w sub c
             = mkc_ipertype (lsubstc R w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term R) as w1.
  { allrw <- @wf_ipertype_iff; sp. }

  assert (cover_vars R sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_ipertype.
Qed.

Lemma lsubstc_mk_spertype {p} :
  forall R sub,
  forall w  : @wf_term p R,
  forall w' : wf_term (mk_spertype R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_spertype R) sub,
    lsubstc (mk_spertype R) w' sub c'
    = mkc_spertype (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  assert (csubst (mk_spertype R) sub = mk_spertype (csubst R sub))
         by (unfold csubst; simpl;
             change_to_lsubst_aux4; simpl;
             rw @sub_filter_nil_r; allrw @fold_nobnd;
             rw @fold_spertype; sp).
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_spertype_ex {p} :
  forall R sub,
  forall w : wf_term (@mk_spertype p R),
  forall c : cover_vars (mk_spertype R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & lsubstc (mk_spertype R) w sub c
          = mkc_spertype (lsubstc R w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term R) as wf.
  { allrw <- @wf_spertype_iff; sp. }

  assert (cover_vars R sub) as cv.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists wf cv.
  apply lsubstc_mk_spertype.
Qed.

Lemma lsubstc_mk_tuni {p} :
  forall R sub,
  forall w  : @wf_term p R,
  forall w' : wf_term (mk_tuni R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_tuni R) sub,
    lsubstc (mk_tuni R) w' sub c'
    = mkc_tuni (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  assert (csubst (mk_tuni R) sub = mk_tuni (csubst R sub))
         by (unfold csubst; simpl;
             change_to_lsubst_aux4; simpl;
             rw @sub_filter_nil_r; allrw @fold_nobnd;
             rw @fold_tuni; sp).
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_tuni_ex {p} :
  forall R sub,
  forall w : wf_term (@mk_tuni p R),
  forall c : cover_vars (mk_tuni R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & lsubstc (mk_tuni R) w sub c
          = mkc_tuni (lsubstc R w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term R) as wf.
  { allrw <- @wf_tuni_iff; sp. }

  assert (cover_vars R sub) as cv.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists wf cv.
  apply lsubstc_mk_tuni.
Qed.

(*
Lemma lsubstc_mk_esquash :
  forall R sub,
  forall w  : wf_term R,
  forall w' : wf_term (mk_esquash R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_esquash R) sub,
    lsubstc (mk_esquash R) w' sub c'
    = mkc_esquash (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  assert (csubst (mk_esquash R) sub = mk_esquash (csubst R sub))
         by (unfold csubst; simpl;
             change_to_lsubst_aux4; simpl;
             rw @sub_filter_nil_r; allrw @fold_nobnd.
             rw fold_esquash; sp).

  rewrite dep_pair_eq with (eq0 := H)
          (pb := isprog_esquash (csubst R sub)
                                (isprog_csubst R sub w c)); sp.
  apply UIP_dec.
  apply bool_dec.
Qed.

Lemma lsubstc_mk_esquash_ex :
  forall R sub,
  forall w : wf_term (mk_esquash R),
  forall c : cover_vars (mk_esquash R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & lsubstc (mk_esquash R) w sub c
             = mkc_esquash (lsubstc R w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term R).
  unfold wf_term in w.
  simpl in w.
  allrw andb_true; sp.

  assert (cover_vars R sub).
  unfold cover_vars in c.
  simpl in c.
  repeat (rw remove_nvars_nil_l in c).
  rw app_nil_r in c.
  repeat (rw @over_vars_app_l in c); sp.

  exists H H0.
  apply lsubstc_mk_esquash.
Qed.
*)

Lemma lsubstc_mk_apply {p} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_apply t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_apply t1 t2) sub,
    lsubstc (mk_apply t1 t2) w sub c
    = mkc_apply (lsubstc t1 w1 sub c1)
                (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @fold_apply; sp.
Qed.

Lemma lsubstc_mk_apply_ex {p} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_apply p t1 t2),
  forall c  : cover_vars (mk_apply t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_apply t1 t2) w sub c
             = mkc_apply (lsubstc t1 w1 sub c1)
                         (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_apply_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_apply_iff; sp. }

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
  apply lsubstc_mk_apply.
Qed.

Lemma lsubstc_mk_apply2 {p} :
  forall t1 t2 t3 sub,
  forall w1 : wf_term t1,
  forall w2 : wf_term t2,
  forall w3 : @wf_term p t3,
  forall w  : wf_term (mk_apply2 t1 t2 t3),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c3 : cover_vars t3 sub,
  forall c  : cover_vars (mk_apply2 t1 t2 t3) sub,
    lsubstc (mk_apply2 t1 t2 t3) w sub c
    = mkc_apply2 (lsubstc t1 w1 sub c1)
                 (lsubstc t2 w2 sub c2)
                 (lsubstc t3 w3 sub c3).
Proof.
  unfold mk_apply2; sp.
  rw @mkc_apply2_eq.

  assert (wf_term (mk_apply t1 t2)) as w12 by (apply wf_apply; sp).

  assert (cover_vars (mk_apply t1 t2) sub) as c12 by (rw @cover_vars_apply; sp).

  rewrite @lsubstc_mk_apply with (w1 := w12) (w2 := w3) (c1 := c12) (c2 := c3); sp.
  rewrite @lsubstc_mk_apply with (w1 := w1) (w2 := w2) (c1 := c1) (c2 := c2); sp.
Qed.

Lemma lsubstc_mk_apply2_ex {p} :
  forall t1 t2 t3 sub,
  forall w  : wf_term (@mk_apply2 p t1 t2 t3),
  forall c  : cover_vars (mk_apply2 t1 t2 t3) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {w3 : wf_term t3
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
     & {c3 : cover_vars t3 sub
        & lsubstc (mk_apply2 t1 t2 t3) w sub c
          = mkc_apply2 (lsubstc t1 w1 sub c1)
                       (lsubstc t2 w2 sub c2)
                       (lsubstc t3 w3 sub c3)}}}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_apply2_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_apply2_iff; sp. }

  assert (wf_term t3) as w3.
  { allrw <- @wf_apply2_iff; sp. }

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

  assert (cover_vars t3 sub) as c3.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 w2 w3 c1 c2 c3.
  apply lsubstc_mk_apply2.
Qed.

Lemma isprog_vars_csubst {p} :
  forall t   : NTerm,
  forall sub : @CSub p,
  forall vs  : list NVar,
    wf_term t
    -> cover_vars_upto t sub vs
    -> isprog_vars vs (csubst t sub).
Proof.
  introv wf cv.
  apply isprog_vars_eq.
  unfold cover_vars_upto in cv.
  rw @free_vars_csubst.
  rw @dom_csub_eq.
  rw @subvars_remove_nvars.
  dands; auto.
  allrw @wf_term_eq.
  unfold csubst.
  apply lsubst_wf_if_eauto; auto.
Qed.

Lemma csubst_var_not_in {p} :
  forall v sub,
    ! LIn v (dom_csub sub)
    -> csubst (mk_var v) sub = @mk_var p v.
Proof.
  intros.
  unfold csubst; simpl.
  rw <- @dom_csub_eq in H.
  rw <- @sub_find_none_iff in H.
  change_to_lsubst_aux4; simpl.
  rw H; sp.
Qed.

Definition lsubstc_vars {p}
           (t   : NTerm)
           (w   : wf_term t)
           (sub : @CSub p)
           (vs  : list NVar)
           (p   : cover_vars_upto t sub vs) : CVTerm vs :=
  exist (isprog_vars vs)
        (csubst t sub)
        (isprog_vars_csubst t sub vs w p).

Lemma lsubstc_vars_var_not_in {p} :
  forall v sub w c,
    lsubstc_vars (mk_var v) w (csub_filter sub [v]) [v] c
    = @mkc_var p v.
Proof.
  introv.
  apply cvterm_eq; simpl.
  apply csubst_var_not_in.
  rw @dom_csub_csub_filter; rw in_remove_nvars; simpl; tcsp.
Qed.

Lemma lsubstc_vars_mk_axiom {p} :
  forall sub w v,
  forall c : cover_vars_upto mk_axiom sub [v],
    lsubstc_vars mk_axiom w sub [v] c
    = @mkcv_axiom p v.
Proof.
  introv; apply cvterm_eq; simpl; auto.
Qed.

Lemma lsubstc_mk_cbv {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_cbv t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_cbv t1 v t2) sub,
    lsubstc (mk_cbv t1 v t2) w sub c
    = mkc_cbv (lsubstc t1 w1 sub c1)
              v
              (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_cbv; sp.
Qed.

Lemma lsubstc_mk_cbv_ex {p} :
  forall t1 v t2 sub,
  forall w  : wf_term (@mk_cbv p t1 v t2),
  forall c  : cover_vars (mk_cbv t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
        & lsubstc (mk_cbv t1 v t2) w sub c
             = mkc_cbv (lsubstc t1 w1 sub c1)
                       v
                       (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_cbv_iff in w; sp.

  duplicate c.
  rw @cover_vars_cbv in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_cbv.
Qed.

Lemma lsubstc_mk_halts {p} :
  forall t sub,
  forall wt : @wf_term p t,
  forall w  : wf_term (mk_halts t),
  forall ct : cover_vars t sub,
  forall c  : cover_vars (mk_halts t) sub,
    lsubstc (mk_halts t) w sub c
    = mkc_halts (lsubstc t wt sub ct).
Proof.
  unfold mk_halts; sp.
  rw <- @fold_mkc_halts.
  generalize (lsubstc_mk_approx_ex
                mk_axiom
                (mk_cbv t nvarx mk_axiom)
                sub
                w
                c); sp.
  rw e; clear e.
  rw @lsubstc_mk_axiom.
  generalize (lsubstc_mk_cbv_ex
                t nvarx mk_axiom
                sub
                w2 c2); sp.
  rw e; clear e.
  rewrite @lsubstc_replace with (w2 := wt) (p2 := ct).
  rw @lsubstc_vars_mk_axiom; sp.
Qed.

Lemma lsubstc_mk_halts_ex {p} :
  forall t sub,
  forall w  : wf_term (@mk_halts p t),
  forall c  : cover_vars (mk_halts t) sub,
    {wt : wf_term t
     & {ct : cover_vars t sub
        & lsubstc (mk_halts t) w sub c
             = mkc_halts (lsubstc t wt sub ct)}}.
Proof.
  sp.
  duplicate w; duplicate c.
  rw <- @wf_halts_iff in w.
  rw @cover_vars_halts in c.
  exists w c.
  apply lsubstc_mk_halts.
Qed.

Lemma lsubstc_mk_spread {p} :
  forall t1 x y t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_spread t1 x y t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [x,y]) [x,y],
  forall c  : cover_vars (mk_spread t1 x y t2) sub,
    lsubstc (mk_spread t1 x y t2) w sub c
    = mkc_spread (lsubstc t1 w1 sub c1)
                 x y
                 (lsubstc_vars t2 w2 (csub_filter sub [x,y]) [x,y] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_spread; sp.
Qed.

Lemma lsubstc_mk_spread_ex {p} :
  forall t1 x y t2 sub,
  forall w  : wf_term (@mk_spread p t1 x y t2),
  forall c  : cover_vars (mk_spread t1 x y t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [x,y]) [x,y]
        & lsubstc (mk_spread t1 x y t2) w sub c
          = mkc_spread (lsubstc t1 w1 sub c1)
                       x y
                       (lsubstc_vars t2 w2 (csub_filter sub [x,y]) [x,y] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw @wf_spread in w; sp.

  duplicate c.
  rw @cover_vars_spread in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_spread.
Qed.

Lemma lsubstc_mk_function {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_function t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_function t1 v t2) sub,
    lsubstc (mk_function t1 v t2) w sub c
    = mkc_function (lsubstc t1 w1 sub c1)
              v
              (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_function; sp.
Qed.

Lemma lsubstc_mk_function_ex {p} :
  forall t1 v t2 sub,
  forall w  : wf_term (@mk_function p t1 v t2),
  forall c  : cover_vars (mk_function t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
        & lsubstc (mk_function t1 v t2) w sub c
             = mkc_function (lsubstc t1 w1 sub c1)
                            v
                            (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_function_iff in w; sp.

  duplicate c.
  rw @cover_vars_function in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_function.
Qed.

Lemma lsubstc_mk_product {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_product t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_product t1 v t2) sub,
    lsubstc (mk_product t1 v t2) w sub c
    = mkc_product (lsubstc t1 w1 sub c1)
                  v
                  (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_product; sp.
Qed.

Lemma lsubstc_mk_product_ex {p} :
  forall t1 v t2 sub,
  forall w  : wf_term (@mk_product p t1 v t2),
  forall c  : cover_vars (mk_product t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
        & lsubstc (mk_product t1 v t2) w sub c
             = mkc_product (lsubstc t1 w1 sub c1)
                            v
                            (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_product_iff in w; sp.

  duplicate c.
  rw @cover_vars_product in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_product.
Qed.

Lemma lsubstc_mk_isect {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_isect t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_isect t1 v t2) sub,
    lsubstc (mk_isect t1 v t2) w sub c
    = mkc_isect (lsubstc t1 w1 sub c1)
                v
                (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_isect; sp.
Qed.

Lemma lsubstc_mk_isect_ex {p} :
  forall t1 v t2 sub,
  forall w  : wf_term (@mk_isect p t1 v t2),
  forall c  : cover_vars (mk_isect t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
        & lsubstc (mk_isect t1 v t2) w sub c
             = mkc_isect (lsubstc t1 w1 sub c1)
                         v
                         (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_isect_iff in w; sp.

  duplicate c.
  rw @cover_vars_isect in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_isect.
Qed.

Lemma lsubstc_mk_top {o} :
  forall p sub c,
    lsubstc mk_top p sub c = @mkc_top o.
Proof.
  introv.
  unfold mk_top, mkc_top.
  generalize (lsubstc_mk_isect_ex
                mk_false nvarx mk_false sub p c); intro k; exrepnd.
  rw k1.
  rw @lsubstc_mk_false.
  assert (mk_cv [nvarx] mkc_false
          = lsubstc_vars mk_false w2 (csub_filter sub [nvarx]) [nvarx] c2)
    as eq by (apply cvterm_eq; simpl; rw @csubst_mk_false; sp).
  rw <- eq; sp.
Qed.

Lemma lsubstc_mk_uall {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_uall t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_uall t1 v t2) sub,
    lsubstc (mk_uall t1 v t2) w sub c
    = mkc_uall (lsubstc t1 w1 sub c1)
                v
                (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  introv.
  apply lsubstc_mk_isect.
Qed.

Lemma lsubstc_mk_uall_ex {p} :
  forall t1 v t2 sub,
  forall w  : wf_term (@mk_uall p t1 v t2),
  forall c  : cover_vars (mk_uall t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
        & lsubstc (mk_uall t1 v t2) w sub c
             = mkc_uall (lsubstc t1 w1 sub c1)
                         v
                         (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.
  apply lsubstc_mk_isect_ex.
Qed.

Lemma lsubstc_mk_disect {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_disect t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_disect t1 v t2) sub,
    lsubstc (mk_disect t1 v t2) w sub c
    = mkc_disect (lsubstc t1 w1 sub c1)
                 v
                 (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_disect; sp.
Qed.

Lemma lsubstc_mk_disect_ex {p} :
  forall t1 v t2 sub,
  forall w  : wf_term (@mk_disect p t1 v t2),
  forall c  : cover_vars (mk_disect t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
        & lsubstc (mk_disect t1 v t2) w sub c
             = mkc_disect (lsubstc t1 w1 sub c1)
                         v
                         (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_disect_iff in w; sp.

  duplicate c.
  rw @cover_vars_disect in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_disect.
Qed.

Lemma lsubstc_mk_eisect {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_eisect t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_eisect t1 v t2) sub,
    lsubstc (mk_eisect t1 v t2) w sub c
    = mkc_eisect (lsubstc t1 w1 sub c1)
                v
                (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_eisect; sp.
Qed.

Lemma lsubstc_mk_eisect_ex {p} :
  forall t1 v t2 sub,
  forall w  : wf_term (@mk_eisect p t1 v t2),
  forall c  : cover_vars (mk_eisect t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
        & lsubstc (mk_eisect t1 v t2) w sub c
             = mkc_eisect (lsubstc t1 w1 sub c1)
                          v
                          (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_eisect_iff in w; sp.

  duplicate c.
  rw @cover_vars_eisect in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_eisect.
Qed.

Lemma lsubstc_mk_set {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_set t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_set t1 v t2) sub,
    lsubstc (mk_set t1 v t2) w sub c
    = mkc_set (lsubstc t1 w1 sub c1)
              v
              (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_set; sp.
Qed.

Lemma lsubstc_mk_set_ex {p} :
  forall t1 v t2 sub,
  forall w  : wf_term (@mk_set p t1 v t2),
  forall c  : cover_vars (mk_set t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
        & lsubstc (mk_set t1 v t2) w sub c
             = mkc_set (lsubstc t1 w1 sub c1)
                       v
                       (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_set_iff in w; sp.

  duplicate c.
  rw @cover_vars_set in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_set.
Qed.

Lemma lsubstc_mk_tunion {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_tunion t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_tunion t1 v t2) sub,
    lsubstc (mk_tunion t1 v t2) w sub c
    = mkc_tunion (lsubstc t1 w1 sub c1)
              v
              (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_tunion; sp.
Qed.

Lemma lsubstc_mk_tunion_ex {p} :
  forall t1 v t2 sub,
  forall w  : wf_term (@mk_tunion p t1 v t2),
  forall c  : cover_vars (mk_tunion t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
        & lsubstc (mk_tunion t1 v t2) w sub c
             = mkc_tunion (lsubstc t1 w1 sub c1)
                       v
                       (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_tunion_iff in w; sp.

  duplicate c.
  rw @cover_vars_tunion in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_tunion.
Qed.

Lemma lsubstc_mk_quotient {p} :
  forall t1 v1 v2 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_quotient t1 v1 v2 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v1,v2]) [v1,v2],
  forall c  : cover_vars (mk_quotient t1 v1 v2 t2) sub,
    lsubstc (mk_quotient t1 v1 v2 t2) w sub c
    = mkc_quotient (lsubstc t1 w1 sub c1)
                   v1 v2
                   (lsubstc_vars t2 w2 (csub_filter sub [v1,v2]) [v1,v2] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_quotient; sp.
Qed.

Lemma lsubstc_mk_quotient_ex {p} :
  forall t1 v1 v2 t2 sub,
  forall w  : wf_term (@mk_quotient p t1 v1 v2 t2),
  forall c  : cover_vars (mk_quotient t1 v1 v2 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v1,v2]) [v1,v2]
        & lsubstc (mk_quotient t1 v1 v2 t2) w sub c
             = mkc_quotient (lsubstc t1 w1 sub c1)
                            v1 v2
                            (lsubstc_vars t2 w2 (csub_filter sub [v1,v2]) [v1,v2] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_quotient_iff in w; sp.

  duplicate c.
  rw @cover_vars_quotient in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_quotient.
Qed.

Lemma lsubstc_mk_w {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_w t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_w t1 v t2) sub,
    lsubstc (mk_w t1 v t2) w sub c
    = mkc_w
        (lsubstc t1 w1 sub c1)
        v
        (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_w; sp.
Qed.

Lemma lsubstc_mk_w_ex {p} :
  forall t1 v t2 sub,
  forall w : wf_term (@mk_w p t1 v t2),
  forall c : cover_vars (mk_w t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
     & lsubstc (mk_w t1 v t2) w sub c
       = mkc_w (lsubstc t1 w1 sub c1)
               v
               (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_w_iff in w; sp.

  duplicate c.
  rw @cover_vars_w in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_w.
Qed.

Lemma lsubstc_mk_m {p} :
  forall t1 v t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_m t1 v t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars_upto t2 (csub_filter sub [v]) [v],
  forall c  : cover_vars (mk_m t1 v t2) sub,
    lsubstc (mk_m t1 v t2) w sub c
    = mkc_m
        (lsubstc t1 w1 sub c1)
        v
        (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub.
  rw @fold_m; sp.
Qed.

Lemma lsubstc_mk_m_ex {p} :
  forall t1 v t2 sub,
  forall w : wf_term (@mk_m p t1 v t2),
  forall c : cover_vars (mk_m t1 v t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars_upto t2 (csub_filter sub [v]) [v]
     & lsubstc (mk_m t1 v t2) w sub c
       = mkc_m (lsubstc t1 w1 sub c1)
               v
               (lsubstc_vars t2 w2 (csub_filter sub [v]) [v] c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_m_iff in w; sp.

  duplicate c.
  rw @cover_vars_m in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_m.
Qed.

Lemma lsubstc_mk_pw {o} :
  forall P ap A bp ba B cp ca cb C p sub,
  forall wP : wf_term P,
  forall wA : wf_term A,
  forall wB : wf_term B,
  forall wC : wf_term C,
  forall wp : @wf_term o p,
  forall w  : wf_term (mk_pw P ap A bp ba B cp ca cb C p),
  forall cvP : cover_vars P sub,
  forall cvA : cover_vars_upto A (csub_filter sub [ap]) [ap],
  forall cvB : cover_vars_upto B (csub_filter sub [bp,ba]) [bp,ba],
  forall cvC : cover_vars_upto C (csub_filter sub [cp,ca,cb]) [cp,ca,cb],
  forall cvp : cover_vars p sub,
  forall cv  : cover_vars (mk_pw P ap A bp ba B cp ca cb C p) sub,
    lsubstc (mk_pw P ap A bp ba B cp ca cb C p) w sub cv
    = mkc_pw
        (lsubstc P wP sub cvP)
        ap
        (lsubstc_vars A wA (csub_filter sub [ap]) [ap] cvA)
        bp ba
        (lsubstc_vars B wB (csub_filter sub [bp,ba]) [bp,ba] cvB)
        cp ca cb
        (lsubstc_vars C wC (csub_filter sub [cp,ca,cb]) [cp,ca,cb] cvC)
        (lsubstc p wp sub cvp).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  allrw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub.
  rw @fold_pw; sp.
Qed.

Lemma lsubstc_mk_pw_ex {o} :
  forall P ap A bp ba B cp ca cb C p sub,
  forall w : wf_term (@mk_pw o P ap A bp ba B cp ca cb C p),
  forall c : cover_vars (mk_pw P ap A bp ba B cp ca cb C p) sub,
    {wP : wf_term P
     & {wA : wf_term A
     & {wB : wf_term B
     & {wC : wf_term C
     & {wp : wf_term p
     & {cvP : cover_vars P sub
     & {cvA : cover_vars_upto A (csub_filter sub [ap]) [ap]
     & {cvB : cover_vars_upto B (csub_filter sub [bp,ba]) [bp,ba]
     & {cvC : cover_vars_upto C (csub_filter sub [cp,ca,cb]) [cp,ca,cb]
     & {cvp : cover_vars p sub
     & lsubstc (mk_pw P ap A bp ba B cp ca cb C p) w sub c
       = mkc_pw
           (lsubstc P wP sub cvP)
           ap
           (lsubstc_vars A wA (csub_filter sub [ap]) [ap] cvA)
           bp ba
           (lsubstc_vars B wB (csub_filter sub [bp,ba]) [bp,ba] cvB)
           cp ca cb
           (lsubstc_vars C wC (csub_filter sub [cp,ca,cb]) [cp,ca,cb] cvC)
           (lsubstc p wp sub cvp)}}}}}}}}}}.
Proof.
  sp.

  duplicate w.
  apply wf_pw_iff in w; sp.

  duplicate c.
  apply cover_vars_pw in c; sp.

  exists w1 w2 w3 w4 w.
  exists c1 c2 c3 c4 c.
  apply lsubstc_mk_pw.
Qed.

Lemma lsubstc_mk_pm {o} :
  forall P ap A bp ba B cp ca cb C p sub,
  forall wP : wf_term P,
  forall wA : wf_term A,
  forall wB : wf_term B,
  forall wC : wf_term C,
  forall wp : @wf_term o p,
  forall w  : wf_term (mk_pm P ap A bp ba B cp ca cb C p),
  forall cvP : cover_vars P sub,
  forall cvA : cover_vars_upto A (csub_filter sub [ap]) [ap],
  forall cvB : cover_vars_upto B (csub_filter sub [bp,ba]) [bp,ba],
  forall cvC : cover_vars_upto C (csub_filter sub [cp,ca,cb]) [cp,ca,cb],
  forall cvp : cover_vars p sub,
  forall cv  : cover_vars (mk_pm P ap A bp ba B cp ca cb C p) sub,
    lsubstc (mk_pm P ap A bp ba B cp ca cb C p) w sub cv
    = mkc_pm
        (lsubstc P wP sub cvP)
        ap
        (lsubstc_vars A wA (csub_filter sub [ap]) [ap] cvA)
        bp ba
        (lsubstc_vars B wB (csub_filter sub [bp,ba]) [bp,ba] cvB)
        cp ca cb
        (lsubstc_vars C wC (csub_filter sub [cp,ca,cb]) [cp,ca,cb] cvC)
        (lsubstc p wp sub cvp).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  allrw @sub_filter_nil_r; allrw @fold_nobnd.
  allrw @sub_filter_csub2sub; sp.
Qed.

Lemma lsubstc_mk_pm_ex {o} :
  forall P ap A bp ba B cp ca cb C p sub,
  forall w : wf_term (@mk_pm o P ap A bp ba B cp ca cb C p),
  forall c : cover_vars (mk_pm P ap A bp ba B cp ca cb C p) sub,
    {wP : wf_term P
     & {wA : wf_term A
     & {wB : wf_term B
     & {wC : wf_term C
     & {wp : wf_term p
     & {cvP : cover_vars P sub
     & {cvA : cover_vars_upto A (csub_filter sub [ap]) [ap]
     & {cvB : cover_vars_upto B (csub_filter sub [bp,ba]) [bp,ba]
     & {cvC : cover_vars_upto C (csub_filter sub [cp,ca,cb]) [cp,ca,cb]
     & {cvp : cover_vars p sub
     & lsubstc (mk_pm P ap A bp ba B cp ca cb C p) w sub c
       = mkc_pm
           (lsubstc P wP sub cvP)
           ap
           (lsubstc_vars A wA (csub_filter sub [ap]) [ap] cvA)
           bp ba
           (lsubstc_vars B wB (csub_filter sub [bp,ba]) [bp,ba] cvB)
           cp ca cb
           (lsubstc_vars C wC (csub_filter sub [cp,ca,cb]) [cp,ca,cb] cvC)
           (lsubstc p wp sub cvp)}}}}}}}}}}.
Proof.
  sp.

  duplicate w.
  apply wf_pm_iff in w; sp.

  duplicate c.
  apply cover_vars_pm in c; sp.

  exists w1 w2 w3 w4 w.
  exists c1 c2 c3 c4 c.
  apply lsubstc_mk_pm.
Qed.

Lemma lsubstc_mk_lam {p} :
  forall v b sub,
  forall w1 : wf_term b,
  forall w  : wf_term (mk_lam v b),
  forall c1 : cover_vars_upto b (@csub_filter p sub [v]) [v],
  forall c  : cover_vars (mk_lam v b) sub,
    lsubstc (mk_lam v b) w sub c
    = mkc_lam v (lsubstc_vars b w1 (csub_filter sub [v]) [v] c1).
Proof.
  unfold lsubstc; simpl; sp.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_csub2sub.
  rw @fold_lam; sp.
Qed.

Lemma lsubstc_mk_lam_ex {p} :
  forall v b sub,
  forall w  : wf_term (@mk_lam p v b),
  forall c  : cover_vars (mk_lam v b) sub,
    {w' : wf_term b
     & {c' : cover_vars_upto b (csub_filter sub [v]) [v]
        & lsubstc (mk_lam v b) w sub c
             = mkc_lam v (lsubstc_vars b w' (csub_filter sub [v]) [v] c')}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_lam_iff in w; sp.

  duplicate c.
  rw @cover_vars_lam in c; sp.

  exists w c.
  apply lsubstc_mk_lam.
Qed.

Lemma lsubstc_mk_id {p} :
  forall sub w c,
    lsubstc mk_id w sub c = @mkc_id p.
Proof.
  sp.
  unfold mkc_id, mk_id.
  generalize (lsubstc_mk_lam_ex nvarx (mk_var nvarx) sub w c); sp.
  rw e; clear e.
  rw @lsubstc_vars_var_not_in; sp.
Qed.

Lemma lsubstc_mk_subtype {p} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_subtype t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_subtype t1 t2) sub,
    lsubstc (mk_subtype t1 t2) w sub c
    = mkc_vsubtype (lsubstc t1 w1 sub c1)
                   (newvar t2)
                   (lsubstc t2 w2 sub c2).
Proof.
  unfold mk_subtype, mk_vsubtype; sp.

  generalize (lsubstc_mk_member_ex
                mk_id
                (mk_function t1 (newvar t2) t2)
                sub
                w
                c); sp.
  allrw.

  rw @lsubstc_mk_id.
  rw <- @fold_mkc_vsubtype.

  generalize (lsubstc_mk_function_ex
                t1
                (newvar t2)
                t2
                sub
                wT
                cT); sp.
  allrw; clear_irr.

  assert (lsubstc_vars t2 w2 (csub_filter sub [newvar t2]) [newvar t2] c3
          = cvterm_var (newvar t2) (lsubstc t2 w2 sub c2)) as eq;
    try (rw eq; auto).

  apply cvterm_eq; simpl.
  apply csubst_csub_filter; allrw disjoint_singleton_r.
  apply newvar_prop.
Qed.

Lemma lsubstc_mk_subtype_ex {p} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_subtype p t1 t2),
  forall c  : cover_vars (mk_subtype t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_subtype t1 t2) w sub c
             = mkc_vsubtype (lsubstc t1 w1 sub c1)
                            (newvar t2)
                            (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_subtype_iff in w; sp.

  duplicate c.
  rw @cover_vars_subtype in c; sp.

  exists w1 w c1 c.
  apply lsubstc_mk_subtype.
Qed.

Lemma sp_lsubstc_mk_subtype {p} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_subtype t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_subtype t1 t2) sub,
    ! LIn nvarx (free_vars t2)
    -> lsubstc (mk_subtype t1 t2) w sub c
       = mkc_subtype (lsubstc t1 w1 sub c1)
                     (lsubstc t2 w2 sub c2).
Proof.
  intros.
  generalize (lsubstc_mk_subtype_ex t1 t2 sub w c); sp; clear_irr.
  allrw.
  remember (lsubstc t1 w1 sub c1); clear Heqc0.
  remember (lsubstc t2 w2 sub c2); clear Heqc3.
  destruct c0, c3.
  unfold mkc_subtype, mkc_vsubtype, mk_subtype.
  rw @newvar_not_in_free_vars; sp.
  assert (mk_vsubtype x nvarx x0 = mk_vsubtype x (newvar x0) x0).
  rw @newvar_prog; sp.
  apply cterm_eq; sp.
Qed.

Lemma sp_lsubstc_mk_subtype_ex {p} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_subtype p t1 t2),
  forall c  : cover_vars (mk_subtype t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & !LIn nvarx (free_vars t2)
             -> lsubstc (mk_subtype t1 t2) w sub c
                = mkc_subtype (lsubstc t1 w1 sub c1)
                              (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.

  duplicate w.
  rw <- @wf_subtype_iff in w; sp.

  duplicate c.
  rw @cover_vars_subtype in c; sp.

  exists w1 w c1 c.
  apply sp_lsubstc_mk_subtype.
Qed.

Lemma subset_free_vars_csub_app {p} :
  forall t sub1 sub2,
    disjoint (free_vars t) (@dom_csub p sub2)
    -> csubst t (sub1 ++ sub2) = csubst t sub1.
Proof.
  unfold csubst; sp.
  rw <- @csub2sub_app.
  apply subset_free_vars_sub_app; sp.
  allrw in_app_iff; sp; allapply @in_csub2sub; sp.
  rw @dom_csub_eq; auto.
Qed.

Lemma subset_free_vars_csub_snoc {p} :
  forall t sub v u,
    ! LIn v (@free_vars p t)
    -> csubst t (snoc sub (v,u)) = csubst t sub.
Proof.
  intros.
  rw snoc_as_append.
  rw @subset_free_vars_csub_app; simpl; auto.
  unfold disjoint; simpl; sp; subst; sp.
Qed.

Lemma subset_free_vars_csub_snoc_app {p} :
  forall t sub1 sub2 v u,
    ! LIn v (@free_vars p t)
    -> csubst t (snoc sub1 (v,u) ++ sub2) = csubst t (sub1 ++ sub2).
Proof.
  intros.
  repeat (rw <- @csubst_app).
  rw @subset_free_vars_csub_snoc; sp.
Qed.

Lemma cover_vars_app_disjoint {p} :
  forall t sub1 sub2,
    @cover_vars p t (sub1 ++ sub2)
    -> disjoint (free_vars t) (dom_csub sub2)
    -> cover_vars t sub1.
Proof.
  sp.
  allrw @cover_vars_eq.
  rw @dom_csub_app in H.
  allrw subvars_eq.
  unfold subset; unfold subset in H; sp.
  apply_in_hyp pp.
  allrw in_app_iff; sp.
  unfold disjoint in H0.
  apply H0 in X; sp.
Qed.

Lemma cover_vars_snoc_disjoint {p} :
  forall t sub v u,
    @cover_vars p t (snoc sub (v,u))
    -> ! LIn v (free_vars t)
    -> cover_vars t sub.
Proof.
  intros.
  allrw snoc_as_append.
  apply cover_vars_app_disjoint in H; sp.
  simpl; unfold disjoint; simpl; sp; subst; sp.
Qed.

Lemma subset_free_vars_lsubstc_app {o} :
  forall t sub1 sub2 p c,
  forall d : disjoint (free_vars t) (@dom_csub o sub2),
    lsubstc t p (sub1 ++ sub2) c
    = lsubstc t p sub1 (cover_vars_app_disjoint t sub1 sub2 c d).
Proof.
  unfold lsubstc; sp.
  apply cterm_eq; simpl.
  apply subset_free_vars_csub_app; sp.
Qed.

Lemma subset_free_vars_lsubstc_app_ex {o} :
  forall t sub1 sub2 p c,
  forall d : disjoint (free_vars t) (@dom_csub o sub2),
    {c' : cover_vars t sub1
     & lsubstc t p (sub1 ++ sub2) c
          = lsubstc t p sub1 c'}.
Proof.
  sp.
  exists (cover_vars_app_disjoint t sub1 sub2 c d).
  apply subset_free_vars_lsubstc_app.
Qed.

Lemma subset_free_vars_lsubstc_snoc {o} :
  forall t sub v u p c,
  forall d : ! LIn v (@free_vars o t),
    lsubstc t p (snoc sub (v,u)) c
    = lsubstc t p sub (cover_vars_snoc_disjoint t sub v u c d).
Proof.
  unfold lsubstc; sp.
  apply cterm_eq; simpl.
  apply subset_free_vars_csub_snoc; auto.
Qed.

Lemma subset_free_vars_lsubstc_snoc_ex {o} :
  forall t sub v u p c,
  forall d : ! LIn v (@free_vars o t),
    {c' : cover_vars t sub
     & lsubstc t p (snoc sub (v,u)) c
          = lsubstc t p sub c'}.
Proof.
  sp.
  exists (cover_vars_snoc_disjoint t sub v u c d).
  apply subset_free_vars_lsubstc_snoc.
Qed.

Lemma csubst_snoc_var {o} :
  forall sub v u,
    ! LIn v (@dom_csub o sub)
    -> csubst (mk_var v) (snoc sub (v,u)) = get_cterm u.
Proof.
  intros.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw snoc_as_append.
  rw <- @csub2sub_app; simpl.
  rw @sub_find_app.
  rw <- @dom_csub_eq in H.
  rw <- @sub_find_none_iff in H.
  rw H.
  simpl.
  rw <- beq_var_refl; auto.
Qed.

Lemma lsubstc_snoc_var {o} :
  forall sub v u p c,
    ! LIn v (@dom_csub o sub)
    -> lsubstc (mk_var v) p (snoc sub (v,u)) c = u.
Proof.
  unfold lsubstc; sp.

  destruct u.

  assert (exist (fun t : NTerm => isprog t) x i =
          exist (fun t : NTerm => isprog t)
                (get_cterm (exist (fun t : NTerm => isprog t) x i))
                i) by (simpl; sp).

  rw H0.

  apply cterm_eq; simpl.
  apply csubst_snoc_var; auto.
Qed.

Lemma csubst_snoc_var2 {p} :
  forall x sub v u,
    LIn x (@dom_csub p sub)
    -> csubst (mk_var x) (snoc sub (v,u))
       = csubst (mk_var x) sub.
Proof.
  intros.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw snoc_as_append.
  rw <- @csub2sub_app; simpl.
  rw @sub_find_app.
  allrw <- @dom_csub_eq.
  allapply @in_dom_sub_exists; sp.
  allrw; sp.
Qed.

Lemma lsubstc_snoc_var2 {o} :
  forall x sub v u p c,
  forall i : LIn x (@dom_csub o sub),
    lsubstc (mk_var x) p (snoc sub (v,u)) c
    = lsubstc (mk_var x) p sub (cover_vars_var x sub i).
Proof.
  unfold lsubstc; sp.
  apply cterm_eq; simpl.
  apply csubst_snoc_var2; auto.
Qed.

Lemma lsubstc_snoc_var2_ex {o} :
  forall x sub v u p c,
  forall i : LIn x (@dom_csub o sub),
    {c' : cover_vars (mk_var x) sub
     & lsubstc (mk_var x) p (snoc sub (v,u)) c
       = lsubstc (mk_var x) p sub c'}.
Proof.
  intros.
  exists (cover_vars_var x sub i).
  apply lsubstc_snoc_var2.
Qed.

Lemma csubst_subst_snoc_eq {o} :
  forall s b x y a,
    !LIn y (bound_vars b)
    -> !LIn y (@dom_csub o s)
    -> (y <> x -> !LIn y (free_vars b))
    -> csubst (subst b x (mk_var y)) (snoc s (y, a))
       = csubst (csubst b (csub_filter s [x])) [(x, a)].
Proof.
  introv niybb niys niyfb.
  rewrite csubst_app.
  unfold subst, csubst.
  try (rw lsubstn_lsubst; try (complete (simpl; rw disjoint_singleton_r; sp))).
  rewrite simple_lsubst_lsubst;
    try (complete (sp; allapply @in_csub2sub; sp));
    try (complete (simpl; sp; cpx; simpl; apply disjoint_singleton_l; auto)).
  rewrite lsubst_sub_singleton.
  rewrite fold_csubst.
  rewrite csubst_snoc_var; auto.
  rewrite <- csub2sub_app; simpl.
  rewrite <- snoc_as_append.
  rewrite <- lsubst_swap;
    try (complete (sp; allapply @in_csub2sub; sp));
    try (complete (rewrite @dom_csub_eq; rewrite @dom_csub_csub_filter; rw @in_remove_nvars; simpl; sp)).
  repeat (rewrite <- csub2sub_cons).
  repeat (rewrite fold_csubst).
  destruct (eq_var_dec y x); subst.
  (* if they're equal it's easy *)
  rewrite csubst_cons_trim.
  rewrite csub_filter_snoc1; sp.
  (* if they're not: *)
  rewrite <- csubst_csub_filter with (l := [y]);
    try (complete (rw disjoint_sym; rw disjoint_singleton_l; sp)).
  assert (x <> y) as d by auto; simpl.
  apply memvar_singleton_diff_r in d; rewrite d.
  rewrite csub_filter_snoc1; sp.
  rewrite csubst_cons_trim.
  rewrite <- csub_filter_app_r; simpl.
  symmetry.
  rewrite <- csubst_csub_filter with (l := [y]); simpl;
    try (complete (rw disjoint_sym; rw disjoint_singleton_l; sp)).
  rewrite d.
  rewrite csub_filter_swap.
  rewrite <- csub_filter_app_r; sp.
Qed.

Lemma csubst_subst_snoc_eq2 {o} :
  forall s b x y a,
    !LIn y (bound_vars b)
    -> !LIn y (@dom_csub o s)
    -> (y <> x -> !LIn y (free_vars b))
    -> csubst (subst b x (mk_var y)) (snoc s (y, a))
       = csubst b (snoc (csub_filter s [x]) (x, a)).
Proof.
  introv niybb niys niyfb.
  rw @csubst_subst_snoc_eq; sp.
  rw @csubst_app.
  rw snoc_as_append; sp.
Qed.

Lemma csubst_subst_snoc_eq3 {o} :
  forall s b x y a,
    !LIn y (bound_vars b)
    -> !LIn y (@dom_csub o s)
    -> (y <> x -> !LIn y (free_vars b))
    -> csubst (subst b x (mk_var y)) (snoc s (y, a))
       = csubst b ((x,a) :: s).
Proof.
  introv niybb niys niyfb.
  rw @csubst_subst_snoc_eq2; sp.
  rw <- @csubst_swap.
  rw <- @csubst_cons_trim; sp.
  rw @dom_csub_csub_filter; rw in_remove_nvars; simpl; sp.
Qed.

Lemma lsubstc_subst_snoc_eq {o} :
  forall s b x y a w1 w2 c1 c2,
    !LIn y (bound_vars b)
    -> !LIn y (@dom_csub o s)
    -> (y <> x -> !LIn y (free_vars b))
    -> lsubstc (subst b x (mk_var y)) w1 (snoc s (y, a)) c1
       = substc a x (lsubstc_vars b w2 (csub_filter s [x]) [x] c2).
Proof.
  intros.
  rewrite substc_eq_lsubstc; simpl.
  apply lsubstc_eq_if_csubst.
  apply csubst_subst_snoc_eq; sp.
Qed.

Lemma simple_lsubstc_subst {o} :
  forall t x B ws s cs wt ct wb cb,
    disjoint (@free_vars o t) (bound_vars B)
    -> lsubstc (subst B x t) ws s cs
       = substc (lsubstc t wt s ct) x
                (lsubstc_vars B wb (csub_filter s [x]) [x] cb).
Proof.
  introv disj.
  rw @substc_eq_lsubstc.
  apply lsubstc_eq_if_csubst; simpl.

  unfold csubst, subst; simpl.
  allrw @fold_subst.
  allrw @fold_csubst.

  apply simple_csubst_subst; sp.
Qed.

Lemma isprog_vars_lsubst {o} :
  forall vs t sub,
    (forall t, LIn t (@range o sub) -> isprogram t)
    -> isprog_vars (vs ++ dom_sub sub) t
    -> isprog_vars vs (lsubst t sub).
Proof.
  introv csub isp.
  allrw @isprog_vars_eq; repnd.
  allrw subvars_prop.
  dands.

  introv i.
  rw @isprogram_lsubst2 in i.
  allrw in_remove_nvars; repnd.
  discover; allrw in_app_iff; sp.

  introv j.
  apply csub.
  rw @in_range_iff; exists v; sp.

  generalize (lsubst_wf_iff sub); intro e.
  dest_imp e hyp.
  apply prog_sub_implies_wf.
  rw <- @prog_sub_eq; sp.
  rw <- e; sp.
Qed.

Lemma isprog_vars_app_implies_isprog_vars_csubst {o} :
  forall vs t sub,
    isprog_vars (vs ++ @dom_csub o sub) t
    -> isprog_vars vs (csubst t sub).
Proof.
  introv isp.
  unfold csubst.
  apply isprog_vars_lsubst; sp.
  allrw @in_range_iff; sp.
  allapply @in_csub2sub; sp.
  rw @dom_csub_eq; sp.
Qed.

Lemma isprog_vars_csubst_iff {o} :
  forall vs t sub,
    isprog_vars (vs ++ @dom_csub o sub) t
    <=> isprog_vars vs (csubst t sub).
Proof.
  introv; split; intro k.
  apply isprog_vars_app_implies_isprog_vars_csubst; sp.
  unfold csubst in k.

  allrw @isprog_vars_eq; repnd.
  generalize (lsubst_wf_iff (csub2sub sub)); intro e.
  dest_imp e hyp.
  generalize (e t); clear e; intro e.
  rw <- e in k; sp.

  generalize (isprogram_lsubst2 t (csub2sub sub)); intro i.
  dest_imp i hyp.
  introv j; allapply @in_csub2sub; sp.
  rw i in k0.
  allrw subvars_prop.
  introv j.
  generalize (k0 x); intro l.
  allrw in_app_iff.
  allrw in_remove_nvars.
  allrw @dom_csub_eq.
  destruct (in_deq NVar deq_nvar x (dom_csub sub)); tcsp.
Qed.

Lemma lsubstc2_lsubstc {o} :
  forall bp ba B p a wp wB s cvp cvB va w c,
    disjoint (free_vars p) (bound_vars B)
    -> !LIn va (bound_vars B)
    -> !LIn va (dom_csub s)
    -> !(ba = bp)
    -> lsubstc2 bp (lsubstc p wp s cvp) ba a
                (lsubstc_vars B wB (csub_filter s [bp, ba]) [bp, ba] cvB)
       = lsubstc (lsubst B [(bp, p), (ba, @mk_var o va)]) w (snoc s (va, a)) c.
Proof.
  introv disj1 disj2 disj3 disj4.
  assert (!LIn va (free_vars p))
         as nivap
         by (allrw @cover_vars_eq; allrw subvars_prop; intro k; discover; sp).

  assert (isprogram (csubst p s))
         as isp
         by (apply isprogram_csubst; sp; rw @nt_wf_eq; sp).

  apply cterm_eq; simpl.
  unfold csubst; simpl.

  repeat (rw @simple_lsubst_lsubst; simpl);
    try (complete (sp; cpx; simpl; rw disjoint_singleton_l; sp));
    try (complete (sp; allapply @in_csub2sub; sp; allunfold @isprogram; sp; allrw; sp)).

  rw <- @sub_filter_csub2sub.
  rw <- @sub_filter_lsubst_sub; simpl.

  rw @lsubst_sub_trivial_closed1;
    try (complete (simpl; sp; cpx; allapply @in_csub2sub; sp)).

  generalize (lsubst_shift B
                           (sub_filter (csub2sub s) [bp, ba])
                           [(bp, csubst p s), (ba, get_cterm a)]
                           []).
  intro eq.

  dest_imp eq hyp.
  simpl; introv i; allrw in_app_iff; allsimpl; sp; cpx;
  allrw @in_sub_filter; sp; allapply @in_csub2sub; sp.

  dest_imp eq hyp.
  simpl; rw <- @dom_sub_sub_filter; unfold disjoint; introv i;
  allrw in_remove_nvars; sp.

  allrw app_nil_r.
  rw eq; clear eq; simpl.

  assert (csubst p s = lsubst p (csub2sub (snoc s (va, a)))) as eq1.
  (* begin proof of assert *)
  unfold csubst; rw @csub2sub_snoc.
  generalize (subset_free_vars_sub_app p (csub2sub s) [(va, get_cterm a)]); intro eq.
  dest_imp eq hyp.
  introv i; allrw in_app_iff; allrw in_single_iff; sp; cpx; allapply @in_csub2sub; sp.
  dest_imp eq hyp.
  simpl; rw disjoint_singleton_r; sp.
  rw snoc_as_append; rw eq; sp.
  (* end proof of assert *)

  rw <- eq1; clear eq1.

  assert (get_cterm a = lsubst (mk_var va) (csub2sub (snoc s (va, a)))) as eq2.
  rw @csub2sub_snoc.
  change_to_lsubst_aux4; simpl; sp.
  rw @sub_find_snoc.
  boolvar.
  assert (!LIn va (dom_sub (csub2sub s))) as niva by (rw @dom_csub_eq; sp).
  rw <- @sub_find_none_iff in niva; rw niva; sp.

  rw <- eq2; clear eq2.

  rw @csub2sub_snoc.

  assert (forall T (l : list T) x y, x :: y :: l = [x,y] ++ l) as eqc by sp.

  symmetry.
  rw eqc.
  rw @lsubst_aux_app_sub_filter; simpl;
    try (complete (allrw @prog_sub_cons; sp; unfold prog_sub, sub_range_sat; simpl; sp));
    try (complete (apply @prog_sub_sub_filter; sp));
    try (complete (rw @prog_sub_snoc; sp)).

  rw @sub_filter_snoc; boolvar; sp.
  allrw not_over_or; repnd.

  allunfold @cover_vars_upto.
  allrw subvars_prop.

  generalize (in_deq NVar deq_nvar va (free_vars B)); intro i; destruct i as [i|i];
  try (complete (discover; allsimpl; sp; allrw @dom_csub_csub_filter;
                 allrw in_remove_nvars; repnd; sp)).

  generalize (lsubst_sub_filter
                B
                ((bp, csubst p s)
                   :: (ba, get_cterm a)
                   :: snoc (sub_filter (csub2sub s) [bp, ba]) (va, get_cterm a))
                [va]); simpl; boolvar; try (complete sp); intro eq.
  dest_imp eq hyp.
  introv k; sp; cpx; allrw in_snoc; sp; cpx; allrw @in_sub_filter; repnd.
  allapply @in_csub2sub; sp.
  dest_imp eq hyp.
  rw disjoint_singleton_r; sp.
  rw <- eq; clear eq.
  rw @sub_filter_snoc; boolvar; sp; allrw not_over_or; sp.
  rw <- @sub_filter_app_r; simpl.

  symmetry.
  generalize (lsubst_sub_filter
                B
                ((bp, csubst p s)
                   :: (ba, get_cterm a)
                   :: sub_filter (csub2sub s) [bp, ba])
                [va]); simpl; boolvar; try (complete sp); intro eq.
  dest_imp eq hyp.
  introv k; sp; cpx; allrw in_snoc; sp; cpx; allrw @in_sub_filter; repnd.
  allapply @in_csub2sub; sp.
  dest_imp eq hyp.
  rw disjoint_singleton_r; sp.
  rw <- eq; clear eq.
  rw <- @sub_filter_app_r; simpl; sp.
Qed.

Lemma cover_vars_lsubst_if {o} :
  forall sub s t,
    subvars (free_vars t) (dom_sub s ++ @dom_csub o sub)
    -> (forall v u, LIn (v,u) s -> cover_vars u sub)
    -> cover_vars (lsubst t s) sub.
Proof.
  introv sv cv.
  rw @cover_vars_eq; allrw subvars_prop; introv i.

  generalize (eqvars_free_vars_disjoint t s); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in i; clear eqv.
  allrw in_app_iff; allrw in_remove_nvars; sp; discover; allrw in_app_iff; sp.
  allrw @in_sub_free_vars_iff; exrepnd.
  allrw @in_sub_keep_first; repnd; discover; allrw in_app_iff; sp;
  allapply @sub_find_some; discover;
  allrw @cover_vars_eq; allrw subvars_prop;
  discover; sp.
Qed.

Lemma cover_vars_upto_lsubst_if {o} :
  forall sub s t vs,
    subvars (free_vars t) (vs ++ dom_sub s ++ @dom_csub o sub)
    -> (forall v u, LIn (v,u) s -> cover_vars_upto u sub vs)
    -> cover_vars_upto (lsubst t s) sub vs.
Proof.
  introv sv cv.
  allunfold @cover_vars_upto; allrw subvars_prop; introv i.

  generalize (eqvars_free_vars_disjoint t s); intro eqv.
  rw eqvars_prop in eqv.
  apply eqv in i; clear eqv.
  allrw in_app_iff; allrw in_remove_nvars; sp; discover; allrw in_app_iff; sp.
  allrw @in_sub_free_vars_iff; exrepnd.
  allrw @in_sub_keep_first; repnd; discover; allrw in_app_iff; sp;
  allapply @sub_find_some; discover;
  allrw @cover_vars_eq; allrw subvars_prop;
  discover; sp; allrw in_app_iff; sp.
Qed.

Lemma cover_vars_upto_app_disjoint {o} :
  forall t sub1 sub2 vs,
    @cover_vars_upto o t (sub1 ++ sub2) vs
    -> disjoint (free_vars t) (dom_csub sub2)
    -> cover_vars_upto t sub1 vs.
Proof.
  introv cvu disj.
  allunfold @cover_vars_upto.
  allrw subvars_prop.
  rw @dom_csub_app in cvu.
  introv i.
  applydup cvu in i; allrw in_app_iff; repdors; try (complete sp).
  apply disj in i0; sp.
Qed.

Lemma cover_vars_upto_snoc_disjoint {o} :
  forall t sub v u vs,
    @cover_vars_upto o t (snoc sub (v,u)) vs
    -> ! LIn v (free_vars t)
    -> cover_vars_upto t sub vs.
Proof.
  introv cvu nit.
  allrw snoc_as_append.
  apply cover_vars_upto_app_disjoint in cvu; sp.
  simpl; unfold disjoint; simpl; sp; subst; sp.
Qed.

Lemma subset_free_vars_lsubstc_vars_snoc {o} :
  forall t sub v u p vs c,
  forall d : ! LIn v (@free_vars o t),
    lsubstc_vars t p (snoc sub (v,u)) vs c
    = lsubstc_vars t p sub vs (cover_vars_upto_snoc_disjoint t sub v u vs c d).
Proof.
  introv; apply cvterm_eq; simpl; auto.
  apply subset_free_vars_csub_snoc; auto.
Qed.

Lemma subset_free_vars_lsubstc_vars_snoc_ex {o} :
  forall t sub v u p vs c,
  forall d : ! LIn v (@free_vars o t),
    {c' : cover_vars_upto t sub vs
     & lsubstc_vars t p (snoc sub (v,u)) vs c
          = lsubstc_vars t p sub vs c'}.
Proof.
  sp.
  exists (cover_vars_upto_snoc_disjoint t sub v u vs c d).
  apply subset_free_vars_lsubstc_vars_snoc.
Qed.

Lemma csub_filter_snoc {o} :
  forall sub v t vars,
    @csub_filter o (snoc sub (v, t)) vars
    = if memvar v vars
      then csub_filter sub vars
      else snoc (csub_filter sub vars) (v, t).
Proof.
  induction sub; simpl; sp; allsimpl.
  rewrite IHsub; boolvar; sp.
Qed.

Lemma lsubstc_vars_csub_filter_snoc {o} :
  forall t wt s v u vs cv cv',
    (!LIn v vs -> !LIn v (free_vars t))
    -> lsubstc_vars t wt (@csub_filter o (snoc s (v, u)) vs) vs cv
       = lsubstc_vars t wt (csub_filter s vs) vs cv'.
Proof.
  introv hyp.
  revert cv.
  rw @csub_filter_snoc; introv.
  boolvar; clear_irr; sp.
  generalize (subset_free_vars_lsubstc_vars_snoc_ex t (csub_filter s vs) v u wt vs cv).
  intro k; dest_imp k h; exrepnd; clear_irr; sp.
Qed.

Lemma lsubstc_vars_csub_filter_snoc_ex {o} :
  forall t wt s v u vs cv,
    (!LIn v vs -> !LIn v (free_vars t))
    -> {cv' : cover_vars_upto t (@csub_filter o s vs) vs
        & lsubstc_vars t wt (csub_filter (snoc s (v, u)) vs) vs cv
          = lsubstc_vars t wt (csub_filter s vs) vs cv'}.
Proof.
  introv hyp.
  assert (cover_vars_upto t (csub_filter s vs) vs) as cv'.
  (* begin proof of assert *)
  allunfold @cover_vars_upto.
  allrw subvars_prop; introv i.
  applydup cv in i as i0.
  allrw in_app_iff; repdors; sp.
  revert i0.
  rw @csub_filter_snoc; boolvar; intro i0; sp.
  rw @dom_csub_snoc in i0; simpl in i0; rw in_snoc in i0; repdors; subst; sp.
  (* end proof of assert *)

  exists cv'.
  apply lsubstc_vars_csub_filter_snoc; sp.
Qed.

Lemma csubst_mk_apply {o} :
  forall f a s,
    csubst (@mk_apply o f a) s = mk_apply (csubst f s) (csubst a s).
Proof.
  intros.
  unfold csubst.
  change_to_lsubst_aux4; simpl; sp.
  allrw @fold_nobnd.
  rw @fold_apply.
  rw @sub_filter_nil_r; allrw @fold_nobnd. sp.
Qed.

Lemma fold_csubst1 {o} :
  forall t v u, lsubst t [(v, @get_cterm o u)] = csubst t [(v,u)].
Proof.
  introv.
  unfold csubst; simpl; sp.
Qed.

Lemma csubst_mk_var_in {o} :
  forall v t,
    csubst (@mk_var o v) [(v, t)] = get_cterm t.
Proof.
  introv; unfold csubst.
  change_to_lsubst_aux4; simpl; boolvar; sp.
Qed.

Lemma cover_vars_implies_cover_vars_upto {o} :
  forall t vs sub1 sub2,
    @cover_vars o t (sub1 ++ sub2)
    -> dom_csub sub2 = vs
    -> cover_vars_upto t (csub_filter sub1 vs) vs.
Proof.
  introv cv domeq; subst.
  unfold cover_vars_upto.
  rw @cover_vars_eq in cv.
  prove_subvars cv.
  allrw @dom_csub_app.
  allrw in_app_iff; allrw @dom_csub_csub_filter; allrw in_remove_nvars; sp.
  destruct (in_deq NVar deq_nvar v (dom_csub sub2)); sp.
Qed.

Lemma cover_vars_if_subvars {o} :
  forall t sub1 sub2,
    subvars (dom_csub sub1) (@dom_csub o sub2)
    -> cover_vars t sub1
    -> cover_vars t sub2.
Proof.
  introv sv cv.
  allrw @cover_vars_eq.
  apply subvars_trans with (vs2 := dom_csub sub1); sp.
Qed.

Lemma simple_substc {o} :
  forall t x B ws s cs wb cb,
    lsubstc (@csubst o B [(x, t)]) ws s cs
    = substc t x (lsubstc_vars B wb (csub_filter s [x]) [x] cb).
Proof.
  introv.

  assert (csubst B [(x, t)] = subst B x (get_cterm t))
    as eq by (unfold csubst; simpl;rw @fold_subst; sp).
  revert ws cs.
  rw eq; clear eq; introv.

  generalize (simple_lsubstc_subst
                (get_cterm t) x B ws s cs
                (wf_cterm t) (cover_vars_cterm t s)
                wb cb); intro k.

  dest_imp k hyp; try (complete (rw @free_vars_cterm; sp)).
  rw k; clear k.

  rw @lsubstc_cterm; sp.
Qed.

Lemma simple_substc2 {o} :
  forall t x u s w c cu,
    !LIn x (@dom_csub o s)
    -> lsubstc u w (snoc s (x,t)) c
       = substc t x (lsubstc_vars u w (csub_filter s [x]) [x] cu).
Proof.
  introv nixs.

  assert (wf_term (csubst u [(x, t)])) as wc by (apply csubst_preserves_wf_term; sp).
  assert (cover_vars (csubst u [(x, t)]) s) as cc by (apply cover_vars_csubst3; simpl; sp).

  generalize (simple_substc t x u wc s cc w cu); intro eq.
  rewrite <- eq; clear eq.

  generalize (lsubstc_csubst_ex u [(x,t)] s wc cc); intro eq; exrepnd; clear_irr; allrw.

  revert c.
  rw snoc_as_append; introv.
  generalize (lsubstc_shift_ex u s [(x,t)] [] w).
  allrw app_nil_r; simpl; intro k.
  generalize (k c); clear k; intro k.
  dest_imp k hyp.
  rw disjoint_singleton_r; sp.
  exrepnd; clear_irr; sp.
Qed.

Lemma cover_vars_change_sub {o} :
  forall t sub1 sub2,
    dom_csub sub1 = @dom_csub o sub2
    -> cover_vars t sub1
    -> cover_vars t sub2.
Proof.
  introv eq cv.
  allrw @cover_vars_eq.
  allrw subvars_prop; allsimpl.
  introv i; discover; allrw <-; sp.
Qed.

Lemma lsubstc_vars_disjoint {o} :
  forall t w s vs c,
    disjoint (@free_vars o t) vs
    -> {c' : cover_vars t s
        $ lsubstc_vars t w s vs c = mk_cv vs (lsubstc t w s c')}.
Proof.
  introv disj.

  assert (cover_vars t s) as cov.
  rw @cover_vars_eq.
  unfold cover_vars_upto in c.
  allrw subvars_prop; introv i.
  applydup c in i as j; allrw in_app_iff.
  apply disj in i; sp.

  exists cov.
  apply cvterm_eq; simpl; sp.
Qed.

Lemma lsubstc_csub_filter_eq {o} :
  forall t w s vs c,
    {c' : @cover_vars o t s $ lsubstc t w (csub_filter s vs) c = lsubstc t w s c'}.
Proof.
  introv.

  assert (cover_vars t s) as cov.
  allrw @cover_vars_eq; allrw subvars_prop; introv i.
  apply c in i; allrw @dom_csub_csub_filter; allrw in_remove_nvars; sp.

  exists cov.
  apply cterm_eq; simpl.
  apply csubst_csub_filter.
  introv i.
  rw @cover_vars_eq in c.
  rw subvars_prop in c.
  apply c in i.
  rw @dom_csub_csub_filter in i.
  rw in_remove_nvars in i; sp.
Qed.

Lemma lsubstc_mk_partial {o} :
  forall R sub,
  forall w  : @wf_term o R,
  forall w' : wf_term (mk_partial R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_partial R) sub,
    lsubstc (mk_partial R) w' sub c'
    = mkc_partial (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @fold_partial; sp.
Qed.

Lemma lsubstc_mk_partial_ex {o} :
  forall R sub,
  forall w : wf_term (@mk_partial o R),
  forall c : cover_vars (mk_partial R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & lsubstc (mk_partial R) w sub c
             = mkc_partial (lsubstc R w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term R) as w1.
  { allrw <- @wf_partial_iff; sp. }

  assert (cover_vars R sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_partial.
Qed.

Lemma lsubstc_mk_admiss {o} :
  forall R sub,
  forall w  : @wf_term o R,
  forall w' : wf_term (mk_admiss R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_admiss R) sub,
    lsubstc (mk_admiss R) w' sub c'
    = mkc_admiss (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @fold_admiss; sp.
Qed.

Lemma lsubstc_mk_mono {o} :
  forall R sub,
  forall w  : @wf_term o R,
  forall w' : wf_term (mk_mono R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_mono R) sub,
    lsubstc (mk_mono R) w' sub c'
    = mkc_mono (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @fold_mono; sp.
Qed.

Lemma csubst_mk_id {o} :
  forall (sub : @CSub o), csubst mk_id sub = mk_id.
Proof.
  introv.
  unfold csubst, lsubst.
  rw <- @sub_free_vars_is_flat_map_free_vars_range.
  rw @sub_free_vars_csub2sub; simpl.
  rw @sub_find_sub_filter; simpl; tcsp.
Qed.

Lemma csubst_mk_fun {o} :
  forall (A B : @NTerm o) sub,
    alpha_eq (csubst (mk_fun A B) sub)
             (mk_fun (csubst A sub) (csubst B sub)).
Proof.
  introv.
  unfold mk_fun, csubst, lsubst.
  rw <- @sub_free_vars_is_flat_map_free_vars_range.
  rw @sub_free_vars_csub2sub; simpl.
  boolvar; try (complete (provefalse; sp)).
  unfold mk_function, nobnd; simpl.
  rw @sub_filter_nil_r.
  prove_alpha_eq3.
  remember (csub2sub sub) as csub.
  pose proof (newvar_prop B) as ni.
  pose proof (newvar_prop (lsubst_aux B (csub2sub sub))) as ni2.
  rw @lsubst_aux_sub_filter; auto; disjoint_reasoningv; auto;[].
  apply alpha_eq_bterm_congr2; spc;[].
  apply disjoint_app_r_same.
  revert ni2.
  repeat (rw @isprogram_lsubst_aux2);
    try (complete (subst; introv i; apply in_csub2sub in i; auto));[].
  introv ni2 i j.
  allrw in_app_iff; allsimpl.
  allrw in_remove_nvars; repnd.
  repndors; subst; tcsp.
Qed.

Lemma lsubstc_mk_fun {o} :
  forall A B sub,
  forall wA : wf_term A,
  forall wB : @wf_term o B,
  forall w  : wf_term (mk_fun A B),
  forall cA : cover_vars A sub,
  forall cB : cover_vars B sub,
  forall c  : cover_vars (mk_fun A B) sub,
    alphaeqc (lsubstc (mk_fun A B) w sub c)
             (mkc_fun (lsubstc A wA sub cA)
                      (lsubstc B wB sub cB)).
Proof.
  unfold mk_member.
  introv.
  unfold alphaeqc; simpl.
  apply csubst_mk_fun.
Qed.

Lemma lsubstc_mk_fun_ex {o} :
  forall A B sub,
  forall w : wf_term (@mk_fun o A B),
  forall c  : cover_vars (mk_fun A B) sub,
    {wA : wf_term A
     & {wB : wf_term B
     & {cA : cover_vars A sub
     & {cB : cover_vars B sub
     & alphaeqc (lsubstc (mk_fun A B) w sub c)
                (mkc_fun (lsubstc A wA sub cA)
                         (lsubstc B wB sub cB))}}}}.
Proof.
  sp.

  assert (wf_term A) as wa.
  { allrw @wf_fun_iff; sp. }

  assert (wf_term B) as wb.
  { allrw @wf_fun_iff; sp. }

  assert (cover_vars A sub) as ca.
  { rw @cover_vars_fun in c; sp. }

  assert (cover_vars B sub) as cb.
  { rw @cover_vars_fun in c; sp. }

  exists wa wb ca cb.
  apply lsubstc_mk_fun.
Qed.

Lemma lsubstc_mk_subtype_rel {o} :
  forall A B sub,
  forall wA : wf_term A,
  forall wB : @wf_term o B,
  forall w  : wf_term (mk_subtype_rel A B),
  forall cA : cover_vars A sub,
  forall cB : cover_vars B sub,
  forall c  : cover_vars (mk_subtype_rel A B) sub,
    alphaeqc (lsubstc (mk_subtype_rel A B) w sub c)
             (mkc_subtype_rel (lsubstc A wA sub cA)
                              (lsubstc B wB sub cB)).
Proof.
  introv.
  unfold mk_subtype_rel.

  pose proof (lsubstc_mk_member_ex mk_id (mk_fun A B) sub w c) as q; exrepnd.
  rw q1; clear q1.

  unfold alphaeqc; simpl.
  unfold mk_subtype_rel.
  rw @csubst_mk_id.
  unfold mk_member, mk_equality.
  prove_alpha_eq3.
  apply csubst_mk_fun.
Qed.

Lemma cover_vars_subtype_rel {p} :
  forall (a b : @NTerm p) sub,
    cover_vars (mk_subtype_rel a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  introv.
  rw @cover_vars_member.
  rw @cover_vars_fun.
  split; intro k; repnd; dands; auto.
Qed.

Lemma lsubstc_mk_subtype_rel_ex {o} :
  forall A B sub,
  forall w : wf_term (@mk_subtype_rel o A B),
  forall c  : cover_vars (mk_subtype_rel A B) sub,
    {wA : wf_term A
     & {wB : wf_term B
     & {cA : cover_vars A sub
     & {cB : cover_vars B sub
     & alphaeqc (lsubstc (mk_subtype_rel A B) w sub c)
                (mkc_subtype_rel (lsubstc A wA sub cA)
                                 (lsubstc B wB sub cB))}}}}.
Proof.
  sp.

  assert (wf_term A) as wa.
  { allrw @wf_subtype_rel_iff; sp. }

  assert (wf_term B) as wb.
  { allrw @wf_subtype_rel_iff; sp. }

  assert (cover_vars A sub) as ca.
  { rw @cover_vars_subtype_rel in c; sp. }

  assert (cover_vars B sub) as cb.
  { rw @cover_vars_subtype_rel in c; sp. }

  exists wa wb ca cb.
  apply lsubstc_mk_subtype_rel.
Qed.

Lemma lsubstc_mk_ufun {o} :
  forall A B sub,
  forall wA : wf_term A,
  forall wB : @wf_term o B,
  forall w  : wf_term (mk_ufun A B),
  forall cA : cover_vars A sub,
  forall cB : cover_vars B sub,
  forall c  : cover_vars (mk_ufun A B) sub,
    alphaeqc (lsubstc (mk_ufun A B) w sub c)
             (mkc_ufun (lsubstc A wA sub cA)
                       (lsubstc B wB sub cB)).
Proof.
  unfold mk_member.
  introv.
  rw <- @fold_mkc_ufun.
  remember (cnewvar (lsubstc B wB sub cB)) as nv.
  unfold mkc_isect.
  allunfold @lsubstc.
  allunfold @csubst.
  unfold alphaeqc.
  simpl. allunfold @cnewvar. allsimpl.
  unfold mk_fun.
  pose proof (prog_sub_csub2sub sub) as Hpr.
  remember (csub2sub sub) as csub.
  change_to_lsubst_aux4.
  unfold mk_function, nobnd.
  simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  unfold mk_isect.
  prove_alpha_eq3.
  remember (csub2sub sub) as csub.
  pose proof (newvar_prop B).
  rw @lsubst_aux_sub_filter; auto; disjoint_reasoningv; auto;[].
  apply alpha_eq_bterm_congr2; spc;[].
  apply disjoint_app_r_same.
  rw <- @lsubst_lsubst_aux_prog_sub; auto.
  allrw @wf_term_eq.
  rw @cover_vars_eq in cB.
  rw subvars_prop in cB.
  dimp (isprogram_lsubst B csub); auto; [|subst; rw @dom_csub_eq; auto].
  simpl_sub4.
  cpx.
Qed.

Lemma lsubstc_mk_ufun_ex {o} :
  forall A B sub,
  forall w : wf_term (@mk_ufun o A B),
  forall c  : cover_vars (mk_ufun A B) sub,
    {wA : wf_term A
     & {wB : wf_term B
     & {cA : cover_vars A sub
     & {cB : cover_vars B sub
     & alphaeqc (lsubstc (mk_ufun A B) w sub c)
                (mkc_ufun (lsubstc A wA sub cA)
                          (lsubstc B wB sub cB))}}}}.
Proof.
  sp.

  assert (wf_term A) as wa.
  { allrw @wf_ufun; sp. }

  assert (wf_term B) as wb.
  { allrw @wf_ufun; sp. }

  assert (cover_vars A sub) as ca.
  { rw @cover_vars_ufun in c; sp. }

  assert (cover_vars B sub) as cb.
  { rw @cover_vars_ufun in c; sp. }

  exists wa wb ca cb.
  apply lsubstc_mk_ufun.
Qed.

Lemma lsubstc_mk_eufun {o} :
  forall A B sub,
  forall wA : wf_term A,
  forall wB : @wf_term o B,
  forall w  : wf_term (mk_eufun A B),
  forall cA : cover_vars A sub,
  forall cB : cover_vars B sub,
  forall c  : cover_vars (mk_eufun A B) sub,
    alphaeqc (lsubstc (mk_eufun A B) w sub c)
             (mkc_eufun (lsubstc A wA sub cA)
                        (lsubstc B wB sub cB)).
Proof.
  unfold mk_member.
  introv.
  rw <- @fold_mkc_eufun.
  remember (cnewvar (lsubstc B wB sub cB)) as nv.
  unfold mkc_isect.
  allunfold @lsubstc.
  allunfold @csubst.
  unfold alphaeqc.
  simpl. allunfold @cnewvar. allsimpl.
  unfold mk_fun.
  pose proof (prog_sub_csub2sub sub) as Hpr.
  remember (csub2sub sub) as csub.
  change_to_lsubst_aux4.
  unfold mk_function, nobnd.
  simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  unfold mk_eisect.
  prove_alpha_eq3.
  remember (csub2sub sub) as csub.
  pose proof (newvar_prop B).
  rw @lsubst_aux_sub_filter; auto; disjoint_reasoningv; auto;[].
  apply alpha_eq_bterm_congr2; spc;[].
  apply disjoint_app_r_same.
  rw <- @lsubst_lsubst_aux_prog_sub; auto.
  allrw @wf_term_eq.
  rw @cover_vars_eq in cB.
  rw subvars_prop in cB.
  dimp (isprogram_lsubst B csub); auto; [|subst; rw @dom_csub_eq; auto].
  simpl_sub4.
  cpx.
Qed.

Lemma lsubstc_mk_eufun_ex {o} :
  forall A B sub,
  forall w : wf_term (@mk_eufun o A B),
  forall c  : cover_vars (mk_eufun A B) sub,
    {wA : wf_term A
     & {wB : wf_term B
     & {cA : cover_vars A sub
     & {cB : cover_vars B sub
     & alphaeqc (lsubstc (mk_eufun A B) w sub c)
                (mkc_eufun (lsubstc A wA sub cA)
                           (lsubstc B wB sub cB))}}}}.
Proof.
  sp.

  assert (wf_term A) as wa.
  { allrw @wf_eufun; sp. }

  assert (wf_term B) as wb.
  { allrw @wf_eufun; sp. }

  assert (cover_vars A sub) as ca.
  { rw @cover_vars_eufun in c; sp. }

  assert (cover_vars B sub) as cb.
  { rw @cover_vars_eufun in c; sp. }

  exists wa wb ca cb.
  apply lsubstc_mk_eufun.
Qed.

Lemma lsubstc_mk_prod {o} :
  forall A B sub,
  forall wA : wf_term A,
  forall wB : @wf_term o B,
  forall w  : wf_term (mk_prod A B),
  forall cA : cover_vars A sub,
  forall cB : cover_vars B sub,
  forall c  : cover_vars (mk_prod A B) sub,
    alphaeqc (lsubstc (mk_prod A B) w sub c)
             (mkc_prod (lsubstc A wA sub cA)
                       (lsubstc B wB sub cB)).
Proof.
  unfold mk_member.
  introv.
  rw <- @fold_mkc_prod.
  remember (cnewvar (lsubstc B wB sub cB)) as nv.
  unfold mkc_product.
  allunfold @lsubstc.
  allunfold @csubst.
  unfold alphaeqc.
  simpl. allunfold @cnewvar. allsimpl.
  unfold mk_prod.
  pose proof (prog_sub_csub2sub sub) as Hpr.
  remember (csub2sub sub) as csub.
  change_to_lsubst_aux4.
  unfold mk_product, nobnd.
  simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  prove_alpha_eq3.
  remember (csub2sub sub) as csub.
  pose proof (newvar_prop B).
  rw @lsubst_aux_sub_filter; auto; disjoint_reasoningv; auto;[].
  apply alpha_eq_bterm_congr2; spc;[].
  apply disjoint_app_r_same.
  rw <- @lsubst_lsubst_aux_prog_sub; auto.
  allrw @wf_term_eq.
  rw @cover_vars_eq in cB.
  rw subvars_prop in cB.
  dimp (isprogram_lsubst B csub); auto; [|subst; rw @dom_csub_eq; auto].
  simpl_sub4.
  cpx.
Qed.

Lemma lsubstc_mk_prod_ex {o} :
  forall A B sub,
  forall w : wf_term (@mk_prod o A B),
  forall c  : cover_vars (mk_prod A B) sub,
    {wA : wf_term A
     & {wB : wf_term B
     & {cA : cover_vars A sub
     & {cB : cover_vars B sub
     & alphaeqc (lsubstc (mk_prod A B) w sub c)
                (mkc_prod (lsubstc A wA sub cA)
                          (lsubstc B wB sub cB))}}}}.
Proof.
  sp.

  assert (wf_term A) as wa.
  { allrw @wf_prod; sp. }

  assert (wf_term B) as wb.
  { allrw @wf_prod; sp. }

  assert (cover_vars A sub) as ca.
  { rw @cover_vars_prod in c; sp. }

  assert (cover_vars B sub) as cb.
  { rw @cover_vars_prod in c; sp. }

  exists wa wb ca cb.
  apply lsubstc_mk_prod.
Qed.

Lemma lsubstc_mk_iff {o} :
  forall A B sub,
  forall wA : wf_term A,
  forall wB : @wf_term o B,
  forall w  : wf_term (mk_iff A B),
  forall cA : cover_vars A sub,
  forall cB : cover_vars B sub,
  forall c  : cover_vars (mk_iff A B) sub,
    alphaeqc (lsubstc (mk_iff A B) w sub c)
             (mkc_iff (lsubstc A wA sub cA)
                      (lsubstc B wB sub cB)).
Proof.
  unfold mk_iff, mkc_iff.
  introv.

  unfold alphaeqc; simpl.
  unfold csubst.
  change_to_lsubst_aux4.
  unfold mk_prod, mk_fun, nobnd.
  simpl.
  allrw @sub_filter_nil_r; allrw @fold_nobnd.
  unfold mk_product, mk_function, nobnd.

  prove_alpha_eq3.

  prove_alpha_eq3.

  pose proof (newvar_prop B).
  rw @lsubst_aux_sub_filter; auto; disjoint_reasoningv; auto.
  apply alpha_eq_bterm_congr2; spc.

  apply disjoint_app_r_same.
  rw disjoint_app_l; dands; rw disjoint_singleton_l;
  try (apply @newvar_prop).
  rw @isprogram_lsubst_aux2.
  rw in_remove_nvars; dands; intro k; repnd; apply newvar_prop in k0; sp.
  introv k.
  apply in_csub2sub in k; auto.

  apply alpha_eq_bterm_congr2; spc.

  prove_alpha_eq3.

  rw @lsubst_aux_sub_filter; auto.
  disjoint_reasoningv; auto.
  apply subvars_not_in with (vs1 := free_vars (mk_fun B A)).
  rw @free_vars_fun.
  apply subvars_app_trivial_l.
  apply newvar_prop.

  apply alpha_eq_bterm_congr2; spc.
  allrw @fold_nobnd.
  rw @fold_function; fold (mk_fun B A).
  rw <- @sub_filter_app_r.
  rw @lsubst_aux_sub_filter; auto.
  disjoint_reasoningv; auto; try (apply newvar_prop).
  apply subvars_not_in with (vs1 := free_vars (mk_fun B A)); try (apply newvar_prop).
  rw @free_vars_fun.
  apply subvars_app_trivial_r.

  disjoint_reasoningv; auto; try (apply newvar_prop).
  allrw @fold_nobnd.
  rw @fold_function; fold (mk_fun B A).
  rw <- @sub_filter_app_r.
  rw @lsubst_aux_sub_filter; auto; try disjoint_reasoningv; auto; try (apply newvar_prop).
  rw @isprogram_lsubst_aux2.
  rw in_remove_nvars; intro k; repnd; apply newvar_prop in k0; sp.
  introv k; apply in_csub2sub in k; auto.
  apply subvars_not_in with (vs1 := free_vars (mk_fun B A)); try (apply newvar_prop).
  rw @free_vars_fun; apply subvars_app_trivial_r.

  allrw @fold_nobnd.
  rw @fold_function; fold (mk_fun B A).
  rw <- @sub_filter_app_r.
  rw @lsubst_aux_sub_filter; auto; try disjoint_reasoningv; auto; try (apply newvar_prop).
  apply subvars_not_in with (vs1 := free_vars (mk_fun B A)); try (apply newvar_prop).
  rw @free_vars_fun; apply subvars_app_trivial_r.

  rw @isprogram_lsubst_aux2.
  rw in_remove_nvars; intro k; repnd; apply newvar_prop in k0; sp.
  introv k; apply in_csub2sub in k; auto.

  disjoint_reasoningv; simpl; auto; rw remove_nvars_nil_l; rw app_nil_r;
  allrw @fold_nobnd;
  rw @fold_function; fold (mk_fun B A);
  try (rw in_app_iff; rw not_over_or; dands).

  rw @lsubst_aux_sub_filter; auto; try disjoint_reasoningv; auto; try (apply newvar_prop).
  rw @isprogram_lsubst_aux2.
  rw in_remove_nvars; intro k; repnd.
  assert (subvars (free_vars B) (free_vars (mk_fun B A))) as sv.
  rw @free_vars_fun; apply subvars_app_trivial_l.
  rw subvars_prop in sv.
  apply sv in k0; apply newvar_prop in k0; sp.
  introv k; apply in_csub2sub in k; sp.
  apply subvars_not_in with (vs1 := free_vars (mk_fun B A)); try (apply newvar_prop).
  rw @free_vars_fun; apply subvars_app_trivial_l.

  rw in_remove_nvars.
  apply not_over_not_lin_nvar; left.
  rw @lsubst_aux_sub_filter; auto; try disjoint_reasoningv; auto; try (apply newvar_prop).
  rw @isprogram_lsubst_aux2.
  rw in_remove_nvars; intro k; repnd.
  assert (subvars (free_vars A) (free_vars (mk_fun B A))) as sv.
  rw @free_vars_fun; apply subvars_app_trivial_r.
  rw subvars_prop in sv.
  apply sv in k0; apply newvar_prop in k0; sp.
  introv k; apply in_sub_filter in k; repnd; apply in_csub2sub in k0; sp.

  allrw @fold_nobnd;
  rw @fold_function;
    fold (mk_fun B A);
    fold (mk_fun (lsubst_aux B (csub2sub sub)) (lsubst_aux A (csub2sub sub))).
  rw @lsubst_aux_sub_filter; auto; try disjoint_reasoningv; auto; try (apply newvar_prop).
  apply subvars_not_in with (vs1 := free_vars (mk_fun (lsubst_aux B (csub2sub sub)) (lsubst_aux A (csub2sub sub)))); try (apply newvar_prop).
  rw @free_vars_fun; apply subvars_app_trivial_l.
  apply subvars_not_in with (vs1 := free_vars (mk_fun B A)); try (apply newvar_prop).
  rw @free_vars_fun; apply subvars_app_trivial_l.
  rw in_remove_nvars.
  apply not_over_not_lin_nvar; left.
  rw <- @sub_filter_app_r.
  rw @lsubst_aux_sub_filter; auto; try disjoint_reasoningv; auto; try (apply newvar_prop).
  apply subvars_not_in with (vs1 := free_vars (mk_fun (lsubst_aux B (csub2sub sub)) (lsubst_aux A (csub2sub sub)))); try (apply newvar_prop).
  rw @free_vars_fun; apply subvars_app_trivial_r.
  apply subvars_not_in with (vs1 := free_vars (mk_fun B A)); try (apply newvar_prop).
  rw @free_vars_fun; apply subvars_app_trivial_r.

  rw @isprogram_lsubst_aux2.
  rw in_remove_nvars; intro k; repnd.
  assert (subvars (free_vars B) (free_vars (mk_fun B A))) as sv.
  rw @free_vars_fun; apply subvars_app_trivial_l.
  rw subvars_prop in sv.
  apply sv in k0; apply newvar_prop in k0; sp.
  introv k; apply in_csub2sub in k; sp.

  rw in_remove_nvars.
  apply not_over_not_lin_nvar; left.
  rw @isprogram_lsubst_aux2.
  rw in_remove_nvars; intro k; repnd.
  assert (subvars (free_vars A) (free_vars (mk_fun B A))) as sv.
  rw @free_vars_fun; apply subvars_app_trivial_r.
  rw subvars_prop in sv.
  apply sv in k0; apply newvar_prop in k0; sp.
  introv k; apply in_csub2sub in k; sp.

  apply subvars_not_in with (vs1 := free_vars (mk_fun (lsubst_aux B (csub2sub sub)) (lsubst_aux A (csub2sub sub)))); try (apply newvar_prop).
  rw @free_vars_fun; apply subvars_app_trivial_l.

  rw in_remove_nvars.
  apply not_over_not_lin_nvar; left.
  apply subvars_not_in with (vs1 := free_vars (mk_fun (lsubst_aux B (csub2sub sub)) (lsubst_aux A (csub2sub sub)))); try (apply newvar_prop).
  rw @free_vars_fun; apply subvars_app_trivial_r.
Qed.

Lemma cover_vars_iff {o} :
  forall a b sub,
    cover_vars (@mk_iff o a b) sub
    <=> cover_vars a sub
        # cover_vars b sub.
Proof.
  introv.
  rw @cover_vars_prod.
  allrw @cover_vars_fun.
  split; sp.
Qed.

Lemma wf_iff {o} :
  forall (a b : @NTerm o),
    wf_term (mk_iff a b) <=> (wf_term a # wf_term b).
Proof.
  introv.
  unfold mk_iff.
  rw @wf_prod.
  allrw @wf_fun.
  split; sp.
Qed.

Lemma lsubstc_mk_iff_ex {o} :
  forall A B sub,
  forall w : wf_term (@mk_iff o A B),
  forall c  : cover_vars (mk_iff A B) sub,
    {wA : wf_term A
     & {wB : wf_term B
     & {cA : cover_vars A sub
     & {cB : cover_vars B sub
     & alphaeqc (lsubstc (mk_iff A B) w sub c)
                (mkc_iff (lsubstc A wA sub cA)
                         (lsubstc B wB sub cB))}}}}.
Proof.
  sp.

  assert (wf_term A) as wa.
  { allrw @wf_iff; sp. }

  assert (wf_term B) as wb.
  { allrw @wf_iff; sp. }

  assert (cover_vars A sub) as ca.
  { rw @cover_vars_iff in c; sp. }

  assert (cover_vars B sub) as cb.
  { rw @cover_vars_iff in c; sp. }

  exists wa wb ca cb.
  apply lsubstc_mk_iff.
Qed.

Lemma wf_admiss_iff {p} :
  forall a : @NTerm p, wf_term (mk_admiss a) <=> wf_term a.
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [|?| o l bw e]; subst.
  generalize (bw (nobnd a)); simpl; intros bw1.
  autodimp bw1 hyp.
  inversion bw1; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma lsubstc_mk_admiss_ex {o} :
  forall R sub,
  forall w : wf_term (@mk_admiss o R),
  forall c : cover_vars (mk_admiss R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & lsubstc (mk_admiss R) w sub c
             = mkc_admiss (lsubstc R w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term R) as w1.
  { allrw @wf_admiss_iff; sp. }

  assert (cover_vars R sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_admiss.
Qed.

Lemma wf_mono_iff {p} :
  forall a : @NTerm p, wf_term (mk_mono a) <=> wf_term a.
Proof.
  introv; split; intro w; repnd.
  rw @wf_term_eq in w.
  inversion w as [|?| o l bw e]; subst.
  generalize (bw (nobnd a)); simpl; intros bw1.
  autodimp bw1 hyp.
  inversion bw1; subst.
  allrw @nt_wf_eq; sp.
  apply nt_wf_eq.
  constructor; simpl; sp; subst; constructor; rw @nt_wf_eq; sp.
Qed.

Lemma lsubstc_mk_mono_ex {o} :
  forall R sub,
  forall w : wf_term (@mk_mono o R),
  forall c : cover_vars (mk_mono R) sub,
    {w1 : wf_term R
     & {c1 : cover_vars R sub
        & lsubstc (mk_mono R) w sub c
             = mkc_mono (lsubstc R w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term R) as w1.
  { allrw @wf_mono_iff; sp. }

  assert (cover_vars R sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_mono.
Qed.

Lemma lsubstc_mk_or {o} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term o t2,
  forall w  : wf_term (mk_or t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_or t1 t2) sub,
    lsubstc (mk_or t1 t2) w sub c
    = mkc_or (lsubstc t1 w1 sub c1)
             (lsubstc t2 w2 sub c2).
Proof.
  sp.
  apply lsubstc_mk_union.
Qed.

Lemma lsubstc_mk_or_ex {o} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_or o t1 t2),
  forall c  : cover_vars (mk_or t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_or t1 t2) w sub c
          = mkc_or (lsubstc t1 w1 sub c1)
                   (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.
  apply lsubstc_mk_union_ex.
Qed.

Lemma lsubstc_mk_eor {o} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term o t2,
  forall w  : wf_term (mk_eor t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_eor t1 t2) sub,
    lsubstc (mk_eor t1 t2) w sub c
    = mkc_eor (lsubstc t1 w1 sub c1)
              (lsubstc t2 w2 sub c2).
Proof.
  sp.
  apply lsubstc_mk_eunion.
Qed.

Lemma lsubstc_mk_eor_ex {o} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_eor o t1 t2),
  forall c  : cover_vars (mk_eor t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_eor t1 t2) w sub c
          = mkc_eor (lsubstc t1 w1 sub c1)
                    (lsubstc t2 w2 sub c2)}}}}.
Proof.
  sp.
  apply lsubstc_mk_eunion_ex.
Qed.

Lemma lsubstc_mk_not {o} :
  forall t1 sub,
  forall w1 : @wf_term o t1,
  forall w  : wf_term (mk_not t1),
  forall c1 : cover_vars t1 sub,
  forall c  : cover_vars (mk_not t1) sub,
    lsubstc (mk_not t1) w sub c
    = mkc_not (lsubstc t1 w1 sub c1).
Proof.
  introv.
  unfold mk_not, mk_fun.
  generalize (newvar_not_in_free_vars (@mk_void o)); intro ev.
  simpl in ev; dest_imp ev hyp; rw ev.

  assert (wf_term (mk_function t1 nvarx mk_void)) as wff by (apply wf_function; sp).
  assert (cover_vars_upto mk_void (csub_filter sub [nvarx]) [nvarx]) as cvv by (unfold cover_vars_upto; simpl; sp).
  assert (cover_vars (mk_function t1 nvarx mk_void) sub) as cvf by (apply cover_vars_function; sp).
  generalize (lsubstc_mk_function t1 nvarx mk_void sub w1 wf_void wff c1 cvv cvf); intro e.
  clear_irr.
  rw e.

  apply cterm_eq; simpl.
  unfold mk_fun.
  rw ev.
  assert (csubst mk_void (csub_filter sub [nvarx]) = mk_void) as e2;
    try (complete (rw e2; sp)).
  unfold csubst.
  change_to_lsubst_aux4; simpl.
  allrw @sub_filter_nil_r; allrw @fold_nobnd.
  rw <- @sub_filter_csub2sub.
  rw <- @sub_filter_app_r; simpl.
  generalize (sub_find_sub_filter_none [nvarx, nvarx] nvarx (csub2sub sub)); intro e3.
  destruct e3 as [ea eb].
  clear ea; autodimp eb hyp; try (complete (simpl; sp)).
  rw eb; sp.
Qed.

Lemma lsubstc_mk_not_ex {o} :
  forall t1 sub,
  forall w : wf_term (@mk_not o t1),
  forall c : cover_vars (mk_not t1) sub,
    {w1 : wf_term t1
     & {c1 : cover_vars t1 sub
        & lsubstc (mk_not t1) w sub c
             = mkc_not (lsubstc t1 w1 sub c1)}}.
Proof.
  sp.

  duplicate w.
  rw @wf_not in w; sp.

  duplicate c.
  rw @cover_vars_not in c; sp.

  exists w c.
  apply lsubstc_mk_not.
Qed.

Lemma subst_preserves_wf_term {o} :
  forall t v u, @wf_term o u -> wf_term t -> wf_term (subst t v u).
Proof.
  introv wu wt.
  apply lsubst_preserves_wf_term; auto.
  unfold wf_sub, sub_range_sat; simpl; sp; cpx.
  apply nt_wf_eq; sp.
Qed.

Lemma covered_subst {o} :
  forall t v u vs,
    covered t (v :: vs)
    -> @covered o u vs
    -> covered (subst t v u) vs.
Proof.
  introv ct cu.
  allunfold @covered.
  generalize (eqvars_free_vars_disjoint t [(v,u)]); intro eqvs.
  apply eqvars_sym in eqvs.
  apply subvars_eqvars with (s2 := vs) in eqvs; auto.
  simpl; boolvar; simpl; rw app_nil_r;
  try (rw subvars_app_l); rw subvars_remove_nvars; dands; auto;
  rw subvars_swap_r; simpl; auto.
Qed.

Lemma covered_snoc_weak {o} :
  forall t v vs, @covered o t vs -> covered t (snoc vs v).
Proof.
  introv c.
  allunfold @covered.
  provesv.
  apply in_snoc; sp.
Qed.

Lemma lsubstc_mk_fix {o} :
  forall R sub,
  forall w  : @wf_term o R,
  forall w' : wf_term (mk_fix R),
  forall c  : cover_vars R sub,
  forall c' : cover_vars (mk_fix R) sub,
    lsubstc (mk_fix R) w' sub c'
    = mkc_fix (lsubstc R w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  unfold mk_fix. refl.
Qed.

Lemma lsubstc_mk_fix_ex {o} :
  forall f sub,
  forall w : wf_term (@mk_fix o f),
  forall c : cover_vars (mk_fix f) sub,
    {w1 : wf_term f
     & {c1 : cover_vars f sub
        & lsubstc (mk_fix f) w sub c
             = mkc_fix (lsubstc f w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term f) as w1.
  { allrw @wf_fix_iff; sp. }

  assert (cover_vars f sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_fix.
Qed.

Lemma csubst_mk_zero {o} :
  forall sub, csubst mk_zero sub = @mk_zero o.
Proof.
  sp.
Qed.

Lemma lsubstc_mk_zero {o} :
  forall p sub c,
    lsubstc mk_zero p sub c = @mkc_zero o.
Proof.
  unfold lsubstc, mkc_zero; sp.
  apply cterm_eq; sp.
Qed.

Lemma lsubstc_mk_int {o} :
  forall p sub c,
    lsubstc mk_int p sub c = @mkc_int o.
Proof.
  unfold lsubstc, mkc_zero; sp.
  apply cterm_eq.
  simpl.
  auto.
Qed.

Lemma lsubstc_mk_bot {o} :
  forall w s c, lsubstc mk_bot w s c = @mkc_bot o.
Proof.
  intros.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; auto.
Qed.

Lemma csubst_mk_lam {o} :
  forall v b sub,
    csubst (@mk_lam o v b) sub
    = mk_lam v (csubst b (csub_filter sub [v])).
Proof.
  introv.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_csub2sub; sp.
Qed.

Lemma csubst_mk_isect {o} :
  forall a v b sub,
    csubst (@mk_isect o a v b) sub
    = mk_isect (csubst a sub) v (csubst b (csub_filter sub [v])).
Proof.
  introv.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @sub_filter_csub2sub; sp.
Qed.

Lemma csubst_mk_equality {o} :
  forall a b A sub,
    csubst (@mk_equality o a b A) sub
    = mk_equality (csubst a sub) (csubst b sub) (csubst A sub).
Proof.
  introv.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd. sp.
Qed.

Lemma csubst_mk_requality {o} :
  forall a b A sub,
    csubst (@mk_requality o a b A) sub
    = mk_requality (csubst a sub) (csubst b sub) (csubst A sub).
Proof.
  introv.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd. sp.
Qed.

Lemma csubst_mk_tequality {o} :
  forall a b sub,
    csubst (@mk_tequality o a b) sub
    = mk_tequality (csubst a sub) (csubst b sub).
Proof.
  introv.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd. sp.
Qed.

Lemma csubst_mk_var_out {o} :
  forall v s,
    !LIn v (dom_csub s)
    -> csubst (mk_var v) s = @mk_var o v.
Proof.
  introv ni; simpl.
  unfold csubst.
  change_to_lsubst_aux4.
  apply lsubst_aux_var_csub2sub_out; sp.
Qed.

Lemma csubst_mk_var_out2 {o} :
  forall v s vs,
    LIn v vs
    -> csubst (mk_var v) (csub_filter s vs) = @mk_var o v.
Proof.
  introv ni; simpl.
  apply csubst_mk_var_out.
  rw @dom_csub_csub_filter.
  rw in_remove_nvars; sp.
Qed.

Lemma csubst_cons_var {o} :
  forall sub v u,
    csubst (@mk_var o v) ((v,u) :: sub) = get_cterm u.
Proof.
  intros.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  boolvar; sp.
  apply disjoint_nil_l.
Qed.

Lemma lsubstc_cons_var {o} :
  forall sub v u p c,
    lsubstc (@mk_var o v) p ((v,u) :: sub) c = u.
Proof.
  unfold lsubstc; sp.

  destruct u.

  assert (exist (fun t : NTerm => isprog t) x i =
          exist (fun t : NTerm => isprog t)
                (get_cterm (exist (fun t : NTerm => isprog t) x i))
                i) as h by (simpl; sp).

  rw h.

  apply cterm_eq; simpl.
  apply csubst_cons_var; auto.
Qed.

Lemma csubst_cons_var2 {o} :
  forall x sub v u,
    x <> v
    -> csubst (@mk_var o x) ((v,u) :: sub)
       = csubst (mk_var x) sub.
Proof.
  intros.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  boolvar; sp.
  apply disjoint_nil_l.
Qed.

Lemma cover_vars_cons {o} :
  forall v sub a b,
    cover_vars (@mk_var o v) ((a,b) :: sub)
    -> v <> a
    -> cover_vars (mk_var v) sub.
Proof.
  introv cv d.
  allrw @cover_vars_eq; simpl.
  provesv; allrw in_single_iff; subst.
  allsimpl; sp.
Qed.

Lemma lsubstc_cons_var2 {o} :
  forall x sub v u p c,
  forall i : x <> v,
    lsubstc (@mk_var o x) p ((v,u) :: sub) c
    = lsubstc (mk_var x) p sub (cover_vars_cons x sub v u c i).
Proof.
  unfold lsubstc; sp.
  apply cterm_eq; simpl.
  apply csubst_cons_var2; auto.
Qed.

Lemma lsubstc_cons_var2_ex {o} :
  forall x sub v u p c,
  forall i : x <> v,
    {c' : cover_vars (@mk_var o x) sub
     & lsubstc (mk_var x) p ((v,u) :: sub) c
       = lsubstc (mk_var x) p sub c'}.
Proof.
  intros.
  exists (cover_vars_cons x sub v u c i).
  apply lsubstc_cons_var2.
Qed.

Lemma subset_free_vars_lsubstc_cons {o} :
  forall t sub v u p c,
  forall d : !LIn v (@free_vars o t),
    lsubstc t p ((v,u) :: sub) c
    = lsubstc t p sub (cover_vars_cons_disjoint t sub v u c d).
Proof.
  unfold lsubstc; sp.
  apply cterm_eq; simpl.
  apply subset_free_vars_csub_cons; auto.
Qed.

Lemma subset_free_vars_lsubstc_cons_ex {o} :
  forall t sub v u p c,
  forall d : !LIn v (@free_vars o t),
    {c' : cover_vars t sub
     & lsubstc t p ((v,u) :: sub) c
       = lsubstc t p sub c'}.
Proof.
  sp.
  exists (cover_vars_cons_disjoint t sub v u c d).
  apply subset_free_vars_lsubstc_cons.
Qed.

Lemma lsubstc_mk_ispair {o} :
  forall t1 t2 t3 sub,
  forall w1 : wf_term t1,
  forall w2 : wf_term t2,
  forall w3 : @wf_term o t3,
  forall w  : wf_term (mk_ispair t1 t2 t3),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c3 : cover_vars t3 sub,
  forall c  : cover_vars (mk_ispair t1 t2 t3) sub,
    lsubstc (mk_ispair t1 t2 t3) w sub c
    = mkc_ispair (lsubstc t1 w1 sub c1)
                 (lsubstc t2 w2 sub c2)
                 (lsubstc t3 w3 sub c3).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl;
  change_to_lsubst_aux4; simpl;
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @fold_ispair; sp.
Qed.

Lemma fold_can_test {p} :
  forall test (a b c : @NTerm p),
    oterm (NCan (NCanTest test)) [ nobnd a, nobnd b, nobnd c ]
    = mk_can_test test a b c.
Proof. sp. Qed.

Lemma lsubstc_mk_can_test {o} :
  forall test t1 t2 t3 sub,
  forall w1 : wf_term t1,
  forall w2 : wf_term t2,
  forall w3 : @wf_term o t3,
  forall w  : wf_term (mk_can_test test t1 t2 t3),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c3 : cover_vars t3 sub,
  forall c  : cover_vars (mk_can_test test t1 t2 t3) sub,
    lsubstc (mk_can_test test t1 t2 t3) w sub c
    = mkc_can_test test (lsubstc t1 w1 sub c1)
                 (lsubstc t2 w2 sub c2)
                 (lsubstc t3 w3 sub c3).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl;
  change_to_lsubst_aux4; simpl;
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @fold_can_test; sp.
Qed.

Lemma lsubstc_mk_ispair_ex {o} :
  forall t1 t2 t3 sub,
  forall w  : wf_term (@mk_ispair o t1 t2 t3),
  forall c  : cover_vars (mk_ispair t1 t2 t3) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {w3 : wf_term t3
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {c3 : cover_vars t3 sub
      & lsubstc (mk_ispair t1 t2 t3) w sub c
           = mkc_ispair (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)
                        (lsubstc t3 w3 sub c3)}}}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw <- @wf_ispair_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw <- @wf_ispair_iff; sp. }

  assert (wf_term t3) as w3.
  { allrw <- @wf_ispair_iff; sp. }

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

  assert (cover_vars t3 sub) as c3.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 w2 w3 c1 c2 c3.
  apply lsubstc_mk_ispair.
Qed.


Lemma lsubstc_mk_can_test_ex {o} :
  forall test t1 t2 t3 sub,
  forall w  : wf_term (@mk_can_test o test t1 t2 t3),
  forall c  : cover_vars (mk_can_test test t1 t2 t3) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {w3 : wf_term t3
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {c3 : cover_vars t3 sub
      & lsubstc (mk_can_test test t1 t2 t3) w sub c
           = mkc_can_test test (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)
                        (lsubstc t3 w3 sub c3)}}}}}}.
Proof.
  sp.

  assert (wf_term t1) as w1.
  { allrw @wf_can_test_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw @wf_can_test_iff; sp. }

  assert (wf_term t3) as w3.
  { allrw @wf_can_test_iff; sp. }

  assert (cover_vars t1 sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c);sp. }

  assert (cover_vars t2 sub) as c2.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  assert (cover_vars t3 sub) as c3.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 w2 w3 c1 c2 c3.
  apply lsubstc_mk_can_test.
Qed.

Lemma lsubstc_mk_eta_pair {o} :
  forall t sub,
  forall w  : @wf_term o t,
  forall w' : wf_term (mk_eta_pair t),
  forall c  : cover_vars t sub,
  forall c' : cover_vars (mk_eta_pair t) sub,
    lsubstc (mk_eta_pair t) w' sub c'
    = mkc_eta_pair (lsubstc t w sub c).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  allrw @sub_filter_nil_r; allrw @fold_nobnd.
  generalize (sub_find_sub_filter_none [nvarx, nvary] nvarx (csub2sub sub)); intro e.
  destruct e as [e1 e2].
  clear e1; autodimp e2 hyp; try (complete (simpl; sp)).
  rw e2; clear e2.
  generalize (sub_find_sub_filter_none [nvarx, nvary] nvary (csub2sub sub)); intro e.
  destruct e as [e1 e2].
  clear e1; autodimp e2 hyp; try (complete (simpl; sp)).
  rw e2; clear e2.
  allrw @fold_spread.
  allrw @fold_pair.
  allrw @fold_pi1.
  allrw @fold_pi2.
  rw @fold_eta_pair; sp.
Qed.

Lemma lsubstc_mk_eta_pair_ex {o} :
  forall t sub,
  forall w : wf_term (@mk_eta_pair o t),
  forall c : cover_vars (mk_eta_pair t) sub,
    {w1 : wf_term t
     & {c1 : cover_vars t sub
        & lsubstc (mk_eta_pair t) w sub c
             = mkc_eta_pair (lsubstc t w1 sub c1)}}.
Proof.
  sp.

  assert (wf_term t) as w1.
  { allrw @wf_eta_pair; sp. }

  assert (cover_vars t sub) as c1.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }

  exists w1 c1.
  apply lsubstc_mk_eta_pair.
Qed.

Lemma lsubstc_mk_btrue {o} :
  forall (w : @wf_term o mk_btrue) s c,
    lsubstc mk_btrue w s c = mkc_btrue.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; auto.
Qed.
Hint Rewrite @lsubstc_mk_btrue : slow.

Lemma lsubstc_mk_bfalse {o} :
  forall (w : @wf_term o mk_bfalse) s c,
    lsubstc mk_bfalse w s c = mkc_bfalse.
Proof.
  introv.
  apply cterm_eq; simpl.
  apply csubst_trivial; simpl; auto.
Qed.
Hint Rewrite @lsubstc_mk_bfalse : slow.
