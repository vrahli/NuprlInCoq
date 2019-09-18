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


Lemma lsubstc_mk_csname {o} :
  forall n w (s : @CSub o) c,
    lsubstc (mk_csname n) w s c = mkc_csname n.
Proof.
  introv; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @lsubstc_mk_csname : slow.

Lemma substc_mkcv_csname {o} :
  forall v (t : @CTerm o) n,
    substc t v (mkcv_csname [v] n) = mkc_csname n.
Proof.
  introv; destruct_cterms; apply cterm_eq; simpl; auto.
Qed.
Hint Rewrite @substc_mkcv_csname : slow.

Lemma dest_nuprl_csname {o} :
  forall (lib : @library o) eq n,
    nuprl lib (mkc_csname n) (mkc_csname n) eq
    -> per_bar (per_csname nuprl) lib (mkc_csname n) (mkc_csname n) eq.
Proof.
  introv cl.
  eapply dest_close_per_csname_l in cl;
    try (apply computes_to_valc_refl; eauto 3 with slow); eauto 3 with slow.
Qed.

Lemma dest_nuprl_csname2 {o} :
  forall lib (eq : per(o)) n,
    nuprl lib (mkc_csname n) (mkc_csname n) eq
    -> eq <=2=> (equality_of_csname_bar lib n).
Proof.
  introv u.
  apply dest_nuprl_csname in u.
  unfold per_bar in u; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply per_bar_eq_equality_of_csname_bar_lib_per].
  apply implies_eq_term_equals_per_bar_eq.
  eapply in_open_bar_ext_pres; eauto; clear u1; introv u1.
  unfold per_csname in *; exrepnd; spcast; auto; GC.
  ccomputes_to_valc_ext_val; auto.
Qed.

Lemma tequality_csname {o} :
  forall lib n, @tequality o lib (mkc_csname n) (mkc_csname n).
Proof.
  introv.
  exists (equality_of_csname_bar lib n).
  apply CL_csname.
  exists n; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve tequality_csname : slow.

Hint Rewrite @substc2_equality : slow.
Hint Rewrite @mkcv_equality_substc : slow.
Hint Rewrite @mkc_var_substc : slow.

Lemma equality_in_csname {p} :
  forall lib (t1 t2 : @CTerm p) n,
    equality lib t1 t2 (mkc_csname n)
    -> equality_of_csname_bar lib n t1 t2.
Proof.
  unfold equality; introv e; exrepnd.
  apply dest_nuprl_csname2 in e1.
  apply e1 in e0; auto.
Qed.

Lemma type_csname {o} :
  forall (lib : @library o) n,
    type lib (mkc_csname n).
Proof.
  introv; unfold type; eauto 3 with slow.
Qed.
Hint Resolve type_csname : slow.

Lemma equality_in_csname_iff {p} :
  forall lib (t1 t2 : @CTerm p) n,
    equality lib t1 t2 (mkc_csname n)
    <-> equality_of_csname_bar lib n t1 t2.
Proof.
  introv; split; intro h; try apply equality_in_csname; auto.
  exists (equality_of_csname_bar lib n); dands; auto.
  apply CL_csname; unfold per_csname; exists n; dands; spcast; eauto 3 with slow.
Qed.

Lemma iscvalue_mkc_choice_seq {o} :
  forall name, @iscvalue o (mkc_choice_seq name).
Proof.
  introv; repeat constructor; simpl; tcsp.
Qed.
Hint Resolve iscvalue_mkc_choice_seq : slow.
