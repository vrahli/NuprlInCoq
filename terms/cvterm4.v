(*

  Copyright 2014 Cornell University
  Copyright 2015 Cornell University
  Copyright 2016 Cornell University
  Copyright 2017 Cornell University
  Copyright 2018 Cornell University

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


Require Export cvterm2.

Lemma wf_inteq_iff {p} :
  forall a b c d : @NTerm p,
    (wf_term a # wf_term b # wf_term c # wf_term d) <=> wf_term (mk_int_eq a b c d).
Proof.
  introv; split; intro i.
  apply wf_less; sp.
  allrw @wf_term_eq.
  inversion i as [| o lnt k e]; subst; allsimpl.
  generalize (k (nobnd a)) (k (nobnd b)) (k (nobnd c)) (k (nobnd d)); intros k1 k2 k3 k4.
  repeat (dest_imp k1 hyp).
  repeat (dest_imp k2 hyp).
  repeat (dest_imp k3 hyp).
  repeat (dest_imp k4 hyp).
  inversion k1; subst.
  inversion k2; subst.
  inversion k3; subst.
  inversion k4; subst; sp.
Qed.

Lemma isprog_vars_inteq {p} :
  forall (a b c d : @NTerm p) vs,
    isprog_vars vs (mk_int_eq a b c d)
    <=> (isprog_vars vs a
         # isprog_vars vs b
         # isprog_vars vs c
         # isprog_vars vs d).
Proof.
  introv.
  repeat (rw @isprog_vars_eq; simpl).
  repeat (rw remove_nvars_nil_l).
  repeat (rw app_nil_r).
  repeat (rw subvars_app_l).
  repeat (rw <- @wf_term_eq).
  allrw <- @wf_inteq_iff; split; sp.
Qed.

Lemma isprog_inteq {o} :
  forall a b c d : @NTerm o,
    isprog (mk_int_eq a b c d)
    <=> (isprog a
         # isprog b
         # isprog c
         # isprog d).
Proof.
  introv.
  allrw @isprog_vars_nil_iff_isprog.
  apply isprog_vars_inteq.
Qed.

Lemma isprog_inteq_implies {o} :
  forall a b c d : @NTerm o,
    isprog a
    -> isprog b
    -> isprog c
    -> isprog d
    -> isprog (mk_int_eq a b c d).
Proof.
  introv u v w z.
  apply isprog_inteq; sp.
Qed.

Definition mkc_inteq {o} (t1 t2 t3 t4 : @CTerm o) : CTerm :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
  let (d,w) := t4 in
    exist isprog (mk_int_eq a b c d) (isprog_inteq_implies a b c d x y z w).

Lemma isprog_vars_inteq_implies {p} :
  forall (a b c d : @NTerm p) vs,
    isprog_vars vs a
    -> isprog_vars vs b
    -> isprog_vars vs c
    -> isprog_vars vs d
    -> isprog_vars vs (mk_int_eq a b c d).
Proof.
  introv ispa ispb ispc ispd.
  apply isprog_vars_inteq; sp.
Qed.

Definition mkcv_inteq {p} vs (t1 t2 t3 t4 : @CVTerm p vs) : CVTerm vs :=
  let (a,x) := t1 in
  let (b,y) := t2 in
  let (c,z) := t3 in
  let (d,w) := t4 in
    exist (isprog_vars vs) (mk_int_eq a b c d) (isprog_vars_inteq_implies a b c d vs x y z w).

Lemma mkcv_inteq_substc {o} :
  forall v a b c d (t : @CTerm o),
    substc t v (mkcv_inteq [v] a b c d)
    = mkc_inteq (substc t v a) (substc t v b) (substc t v c) (substc t v d).
Proof.
  introv.
  destruct_cterms.
  apply cterm_eq; simpl.
  repeat unfsubst.
Qed.
