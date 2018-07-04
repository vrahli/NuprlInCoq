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

  Authors: Vincent Rahli

*)


Require Export per_props_tacs.
Require Export per_props_util.


Lemma lsubstc_mk_refname {o} :
  forall n w (s : @CSub o) c,
    lsubstc (mk_refname n) w s c = mkc_refname n.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @lsubstc_mk_refname : slow.

Lemma substc_mkcv_refname {o} :
  forall v (t : @CTerm o) n,
    substc t v (mkcv_refname [v] n) = mkc_refname n.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc_mkcv_refname : slow.

Lemma dest_nuprl_refname {o} :
  forall (lib : @SL o) eq n,
    nuprl lib (mkc_refname n) (mkc_refname n) eq
    -> per_bar (per_refname nuprl) lib (mkc_refname n) (mkc_refname n) eq.
Proof.
  introv cl.
  eapply dest_close_per_refname_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprl_refname2 {o} :
  forall lib (eq : per(o)) n,
    nuprl lib (mkc_refname n) (mkc_refname n) eq
    -> eq <=2=> (equality_of_refname_bar lib n).
Proof.
  introv u.
  apply dest_nuprl_refname in u.
  unfold per_bar in u; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply (per_bar_eq_equality_of_refname_bar_lib_per _ bar)].
  apply implies_eq_term_equals_per_bar_eq.
  apply all_in_bar_ext_intersect_bars_same; simpl; auto.
  introv br ext; introv.
  pose proof (u0 _ br _ ext x) as u0; simpl in *.
  unfold per_refname in *; exrepnd; spcast; auto; GC.
  ccomputes_to_valc_ext_val; auto.
Qed.

Lemma tequality_refname {o} :
  forall lib n, @tequality o lib (mkc_refname n) (mkc_refname n).
Proof.
  introv.
  exists (equality_of_refname_bar lib n).
  apply CL_refname.
  exists n; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve tequality_refname : slow.

Hint Rewrite @substc2_equality : slow.
Hint Rewrite @mkcv_equality_substc : slow.
Hint Rewrite @mkc_var_substc : slow.

Lemma equality_in_refname {p} :
  forall lib (t1 t2 : @CTerm p) n,
    equality lib t1 t2 (mkc_refname n)
    -> equality_of_refname_bar lib n t1 t2.
Proof.
  unfold equality; introv e; exrepnd.
  apply dest_nuprl_refname2 in e1.
  apply e1 in e0; auto.
Qed.

Lemma type_refname {o} :
  forall (lib : @SL o) n,
    type lib (mkc_refname n).
Proof.
  introv; unfold type; eauto 3 with slow.
Qed.
Hint Resolve type_refname : slow.

Lemma equality_in_refname_iff {p} :
  forall lib (t1 t2 : @CTerm p) n,
    equality lib t1 t2 (mkc_refname n)
    <-> equality_of_refname_bar lib n t1 t2.
Proof.
  introv; split; intro h; try apply equality_in_refname; auto.
  exists (equality_of_refname_bar lib n); dands; auto.
  apply CL_refname; unfold per_refname; exists n; dands; spcast; eauto 3 with slow.
Qed.

Lemma iscvalue_mkc_ref {o} :
  forall name, @iscvalue o (mkc_ref name).
Proof.
  introv; repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscvalue_mkc_ref : slow.
