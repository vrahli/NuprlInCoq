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


  Websites : http://nuprl.org/html/verification/
             http://nuprl.org/html/Nuprl2Coq
             https://github.com/vrahli/NuprlInCoq

  Authors: Vincent Rahli
           Abhishek Anand

*)


Require Export per_props_util.


Lemma dest_nuprl_qnat {o} :
  forall (lib : @library o) eq,
    nuprl lib mkc_qnat mkc_qnat eq
    -> per_bar (per_qnat nuprl) lib mkc_qnat mkc_qnat eq.
Proof.
  introv cl.
  eapply dest_close_per_qnat_l in cl; eauto 3 with slow.
  unfold per_qnat_bar in *; exrepnd.
  exists bar (equality_of_qnat_bar_lib_per lib).
  dands; auto.

  {
    introv br ext; introv.
    unfold per_qnat; dands; spcast; eauto 3 with slow.
  }

  {
    eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym;apply per_bar_eq_equality_of_qnat_bar_lib_per.
  }
Qed.

Lemma dest_nuprl_qnat2 {o} :
  forall lib (eq : per(o)),
    nuprl lib mkc_qnat mkc_qnat eq
    -> eq <=2=> (equality_of_qnat_bar lib).
Proof.
  introv u.
  apply dest_nuprl_qnat in u.
  unfold per_bar in u; exrepnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply (per_bar_eq_equality_of_qnat_bar_lib_per _ bar)].
  apply implies_eq_term_equals_per_bar_eq.
  apply all_in_bar_ext_intersect_bars_same; simpl; auto.
  introv br ext; introv.
  pose proof (u0 _ br _ ext x) as u0; simpl in *.
  unfold per_qnat in *; exrepnd; spcast; auto.
Qed.

Lemma nuprl_qnat {p} :
  forall lib, @nuprl p lib mkc_qnat mkc_qnat (equality_of_qnat_bar lib).
Proof.
  sp.
  apply CL_qnat.
  unfold per_qnat; sp; spcast; eauto 3 with slow.
Qed.
Hint Resolve nuprl_qnat : slow.

Lemma equality_in_qnat {p} :
  forall lib (t1 t2 : @CTerm p),
    equality lib t1 t2 mkc_qnat <=> equality_of_qnat_bar lib t1 t2.
Proof.
  intros; split; intro e.

  - unfold equality in e; exrepnd.
    apply dest_nuprl_qnat2 in e1.
    apply e1 in e0; auto.

  - exists (equality_of_qnat_bar lib); dands; auto; eauto 3 with slow.
Qed.

Lemma tequality_qnat {p} : forall lib, @tequality p lib mkc_qnat mkc_qnat.
Proof.
  introv.
  exists (@equality_of_qnat_bar p lib).
  apply CL_qnat; split; dands; spcast; eauto 3 with slow.
Qed.
Hint Resolve tequality_qnat : slow.
