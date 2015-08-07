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
  along with VPrl.  Ifnot, see <http://www.gnu.org/licenses/>.


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export cvterm.
Require Export cequiv.


Lemma isprog_add_implies {p} :
  forall (a b : @NTerm p),
    isprog a
    -> isprog b
    -> isprog (mk_add a b).
Proof.
  introv ispa ispb.
  apply isprog_vars_nil_iff_isprog.
  apply isprog_vars_add; sp.
Qed.

Definition mkc_add {p} (t1 t2 : @CTerm p) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
    exist isprog (mk_add a b) (isprog_add_implies a b x y).

Lemma mkcv_add_substc {o} :
  forall v a b (t : @CTerm o),
    substc t v (mkcv_add [v] a b)
    = mkc_add (substc t v a) (substc t v b).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.

Lemma reduces_to_add_integer {o} :
  forall lib (k1 k2 : Z),
    @reduces_to o lib (mk_add (mk_integer k1) (mk_integer k2)) (mk_integer (k1 + k2)).
Proof.
  introv.
  apply reduces_to_if_step.
  csunf; simpl; dcwf h; simpl; auto.
Qed.

Lemma cequiv_mk_add_integer {o} :
  forall lib (k1 k2 : Z),
    @cequiv o lib (mk_add (mk_integer k1) (mk_integer k2)) (mk_integer (k1 + k2)).
Proof.
  introv.
  apply reduces_to_implies_cequiv; eauto 3 with slow.
  apply isprogram_eq; apply isprog_add_implies; eauto 3 with slow.
Qed.

Lemma cequivc_mkc_add_integer {o} :
  forall lib (k1 k2 : Z),
    @cequivc o lib (mkc_add (mkc_integer k1) (mkc_integer k2)) (mkc_integer (k1 + k2)).
Proof.
  introv.
  unfold cequivc; simpl.
  apply cequiv_mk_add_integer.
Qed.

Lemma lsubstc_mk_add {p} :
  forall t1 t2 sub,
  forall w1 : wf_term t1,
  forall w2 : @wf_term p t2,
  forall w  : wf_term (mk_add t1 t2),
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_add t1 t2) sub,
    lsubstc (mk_add t1 t2) w sub c
    = mkc_add (lsubstc t1 w1 sub c1)
              (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl.
  change_to_lsubst_aux4; simpl.
  rw @sub_filter_nil_r; allrw @fold_nobnd; sp.
Qed.

Lemma lsubstc_mk_add_ex {p} :
  forall t1 t2 sub,
  forall w  : wf_term (@mk_add p t1 t2),
  forall c  : cover_vars (mk_add t1 t2) sub,
    {w1 : wf_term t1
     & {w2 : wf_term t2
     & {c1 : cover_vars t1 sub
     & {c2 : cover_vars t2 sub
        & lsubstc (mk_add t1 t2) w sub c
             = mkc_add (lsubstc t1 w1 sub c1)
                       (lsubstc t2 w2 sub c2)}}}}.
Proof.
  introv.

  assert (wf_term t1) as w1.
  { allrw @wf_arithop_iff; sp. }

  assert (wf_term t2) as w2.
  { allrw @wf_arithop_iff; sp. }

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
  apply lsubstc_mk_add.
Qed.

Lemma implies_approx_add {p} :
  forall lib f g a b,
    approx lib f g
    -> @approx p lib a b
    -> approx lib (mk_add f a) (mk_add g b).
Proof.
  introv H1p H2p.
  applydup @approx_relates_only_progs in H1p.
  applydup @approx_relates_only_progs in H2p.
  repnd.
  unfold mk_add.
  repeat (prove_approx);sp.
Qed.

Lemma implies_cequivc_mkc_add {o} :
  forall lib (a b c d : @CTerm o),
    cequivc lib a c
    -> cequivc lib b d
    -> cequivc lib (mkc_add a b) (mkc_add c d).
Proof.
  introv c1 c2; destruct_cterms; allunfold @cequivc; allsimpl.
  destruct c1, c2.
  split; apply implies_approx_add; auto.
Qed.
