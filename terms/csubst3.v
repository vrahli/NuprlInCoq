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


Require Export csubst2.


Lemma isprogram_isint {o} :
  forall a b c,
    isprogram a
    -> isprogram b
    -> @isprogram o c
    -> isprogram (mk_isint a b c).
Proof.
  repeat constructor.
  unfold closed; simpl.
  allrw <- null_iff_nil.
  repeat (rw null_app).
  repeat (rw null_iff_nil).
  allunfold @isprogram; allunfold @closed.
  repeat (rewrite remove_nvars_nil_l); sp.
  simpl; sp; allunfold @isprogram; sp; subst; constructor; auto.
Qed.

Lemma isprogram_isint_iff {p} :
  forall a b c, (isprogram a # isprogram b # @isprogram p c) <=> isprogram (mk_isint a b c).
Proof.
  intros; split; intro i.
  apply isprogram_isint; sp.
  inversion i as [cl w].
  allunfold @closed; allsimpl.
  allrw remove_nvars_nil_l.
  allrw app_nil_r.
  allrw app_eq_nil_iff; repnd; allrw.
  inversion w as [| | o lnt k meq ]; allsimpl; subst.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)); intros i1 i2 i3.
  dest_imp i1 hyp; dest_imp i2 hyp; dest_imp i3 hyp.
  unfold isprogram; allrw.
  inversion i1; inversion i2; inversion i3; subst; sp.
Qed.

Lemma isprog_isint {p} :
  forall a b c,
    isprog a
    -> isprog b
    -> @isprog p c
    -> isprog (mk_isint a b c).
Proof.
  sp; allrw @isprog_eq.
  apply isprogram_isint; auto.
Qed.

Definition mkc_isint {p} (t1 t2 t3 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
  exist isprog (mk_isint a b c) (isprog_isint a b c x y z).

Lemma mkc_isint_eq {p} :
  forall a b c d e f,
    mkc_isint a b c = @mkc_isint p d e f
    -> a = d # b = e # c = f.
Proof.
  introv eq.
  destruct_cterms.
  allunfold @mkc_isint.
  inversion eq; subst; dands; tcsp; eauto with pi.
Qed.

Lemma fold_isint {p} :
  forall a b c,
    oterm (NCan (NCanTest CanIsint)) [ nobnd a, nobnd b, @nobnd p c ]
    = mk_isint a b c.
Proof.
  sp.
Qed.

Lemma lsubstc_mk_isint {p} :
  forall t1 t2 t3 sub,
  forall w1 : wf_term t1,
  forall w2 : wf_term t2,
  forall w3 : @wf_term p t3,
  forall w  : wf_term (mk_isint t1 t2 t3),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c3 : cover_vars t3 sub,
  forall c  : cover_vars (mk_isint t1 t2 t3) sub,
    lsubstc (mk_isint t1 t2 t3) w sub c
    = mkc_isint (lsubstc t1 w1 sub c1)
                  (lsubstc t2 w2 sub c2)
                  (lsubstc t3 w3 sub c3).
Proof.
  introv.

  apply cterm_eq; simpl.
  unfold csubst; simpl;
  change_to_lsubst_aux4; simpl;
  rw @sub_filter_nil_r;
  allrw @fold_nobnd;
  rw @fold_isint; sp.
Qed.

Lemma lsubstc_mk_isint_ex {p} :
  forall t1 t2 t3 sub,
  forall w  : wf_term (@mk_isint p t1 t2 t3),
  forall c  : cover_vars (mk_isint t1 t2 t3) sub,
  {w1 : wf_term t1
   & {w2 : wf_term t2
   & {w3 : wf_term t3
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
   & {c3 : cover_vars t3 sub
      & lsubstc (mk_isint t1 t2 t3) w sub c
           = mkc_isint (lsubstc t1 w1 sub c1)
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
  apply lsubstc_mk_isint.
Qed.
