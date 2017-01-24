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


Require Export substitution.
Require Export terms_props.
Require Export cvterm.

Lemma isprog_int_eq {o} :
  forall a b c d : @NTerm o,
    isprog (mk_int_eq a b c d)
    <=> (isprog a
         # isprog b
         # isprog c
         # isprog d).
Proof.
  introv.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_less.
Qed.

Lemma isprog_int_eq_implies {o} :
  forall a b c d : @NTerm o,
    isprog a
    -> isprog b
    -> isprog c
    -> isprog d
    -> isprog (mk_int_eq a b c d).
Proof.
  introv u v w z.
  apply isprog_less; sp.
Qed.

Definition mkc_int_eq {o} (t1 t2 t3 t4 : @CTerm o) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
  let (d,w) := t4 in
    exist isprog (mk_int_eq a b c d) (isprog_int_eq_implies a b c d x y z w).


Lemma isprog_atom_eq {o} :
  forall a b c d : @NTerm o,
    isprog (mk_int_eq a b c d)
    <=> (isprog a
         # isprog b
         # isprog c
         # isprog d).
Proof.
  introv.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_less.
Qed.

Lemma isprog_atom_eq_implies {o} :
  forall a b c d : @NTerm o,
    isprog a
    -> isprog b
    -> isprog c
    -> isprog d
    -> isprog (mk_atom_eq a b c d).
Proof.
  introv u v w z.
  apply isprog_atom_eq; sp.
Qed.

Lemma implies_isprog_atom_eq {o} :
  forall (a b c d : @NTerm o),
    isprog a
    -> isprog b
    -> isprog c
    -> isprog d
    -> isprog (mk_atom_eq a b c d).
Proof.
  introv ispa ispb ispc ispd.
  apply isprog_atom_eq; sp.
Qed.

Definition mkc_atom_eq {o} (t1 t2 t3 t4 : @CTerm o) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
  let (d,w) := t4 in
    exist isprog (mk_atom_eq a b c d) (isprog_atom_eq_implies a b c d x y z w).


Lemma fold_int_eq {p} :
  forall (m n a b : @NTerm p),
   oterm (NCan (NCompOp CompOpEq)) [ nobnd m, nobnd n, nobnd a, nobnd b]
    = mk_int_eq m n a b.
Proof. sp. Qed. 

Lemma lsubstc_mk_int_eq {o} :
  forall m n t1 t2 sub,
  forall wm : wf_term m,
  forall wn : wf_term n,
  forall w1 : wf_term t1,
  forall w2 : @wf_term o t2,
  forall w  : wf_term (mk_int_eq m n t1 t2),
  forall cm : cover_vars m sub,
  forall cn : cover_vars n sub,
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_int_eq m n t1 t2) sub,
    lsubstc (mk_int_eq m n t1 t2) w sub c
    = mkc_int_eq (lsubstc m wm sub cm)
                 (lsubstc n wn sub cn)
                 (lsubstc t1 w1 sub c1)
                 (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl;
  change_to_lsubst_aux4; simpl;
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @fold_int_eq; sp.
Qed.


Lemma lsubstc_mk_int_eq_ex {o} :
  forall m n t1 t2 sub,
  forall w  : wf_term (@mk_int_eq o m n t1 t2),
  forall c  : cover_vars (mk_int_eq m n t1 t2) sub,
  {wm : wf_term m 
   & {wn : wf_term n
   & {w1 : wf_term t1
   & {w2 : wf_term t2
   & {cm : cover_vars m sub
   & {cn : cover_vars n sub
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
      & lsubstc (mk_int_eq m n t1 t2) w sub c
           = mkc_int_eq (lsubstc m wm sub cm)
                        (lsubstc n wn sub cn)
                        (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)}}}}}}}}.
Proof.
  sp.

  assert (wf_term m # wf_term n # wf_term t1 # wf_term t2) as wf.
  { rw @wf_compop_iff in w; sp. }
  repnd.

  assert (cover_vars m sub # cover_vars n sub # cover_vars t1 sub # cover_vars t2 sub) as cov.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }
  repnd.

  exists wf0 wf1 wf2 wf cov0 cov1 cov2 cov.
  apply lsubstc_mk_int_eq.
Qed.


Lemma fold_atom_eq {p} :
  forall (m n a b : @NTerm p),
   oterm (NCan (NCompOp CompOpEq)) [ nobnd m, nobnd n, nobnd a, nobnd b]
    = mk_atom_eq m n a b.
Proof. sp. Qed.

Lemma lsubstc_mk_atom_eq {o} :
  forall m n t1 t2 sub,
  forall wm : wf_term m,
  forall wn : wf_term n,
  forall w1 : wf_term t1,
  forall w2 : @wf_term o t2,
  forall w  : wf_term (mk_atom_eq m n t1 t2),
  forall cm : cover_vars m sub,
  forall cn : cover_vars n sub,
  forall c1 : cover_vars t1 sub,
  forall c2 : cover_vars t2 sub,
  forall c  : cover_vars (mk_atom_eq m n t1 t2) sub,
    lsubstc (mk_atom_eq m n t1 t2) w sub c
    = mkc_atom_eq (lsubstc m wm sub cm)
                 (lsubstc n wn sub cn)
                 (lsubstc t1 w1 sub c1)
                 (lsubstc t2 w2 sub c2).
Proof.
  sp; unfold lsubstc; simpl.
  apply cterm_eq; simpl.
  unfold csubst; simpl;
  change_to_lsubst_aux4; simpl;
  rw @sub_filter_nil_r; allrw @fold_nobnd.
  rw @fold_int_eq; sp.
Qed.


Lemma lsubstc_mk_atom_eq_ex {o} :
  forall m n t1 t2 sub,
  forall w  : wf_term (@mk_atom_eq o m n t1 t2),
  forall c  : cover_vars (mk_atom_eq m n t1 t2) sub,
  {wm : wf_term m 
   & {wn : wf_term n
   & {w1 : wf_term t1
   & {w2 : wf_term t2
   & {cm : cover_vars m sub
   & {cn : cover_vars n sub
   & {c1 : cover_vars t1 sub
   & {c2 : cover_vars t2 sub
      & lsubstc (mk_atom_eq m n t1 t2) w sub c
           = mkc_atom_eq (lsubstc m wm sub cm)
                        (lsubstc n wn sub cn)
                        (lsubstc t1 w1 sub c1)
                        (lsubstc t2 w2 sub c2)}}}}}}}}.
Proof.
  sp.

  assert (wf_term m # wf_term n # wf_term t1 # wf_term t2) as wf.
  { rw @wf_compop_iff in w; sp. }
  repnd.

  assert (cover_vars m sub # cover_vars n sub # cover_vars t1 sub # cover_vars t2 sub) as cov.
  { unfold cover_vars in c.
    simpl in c.
    repeat (rw remove_nvars_nil_l in c).
    rw app_nil_r in c.
    repeat (rw @over_vars_app_l in c); sp. }
  repnd.

  exists wf0 wf1 wf2 wf cov0 cov1 cov2 cov.
  apply lsubstc_mk_atom_eq.
Qed.