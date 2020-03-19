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


Require Export type_sys.
Require Export per_ceq_bar.
Require Export close_util_bar.
Require Export nuprl_mon_func.


Lemma ccequivc_ext_preserves_equality_of_qlt {o} :
  forall lib (a b c d : @CTerm o),
    ccequivc_ext lib a c
    -> ccequivc_ext lib b d
    -> equality_of_qlt lib a b
    -> equality_of_qlt lib c d.
Proof.
  introv ceqa ceqb equ ext.
  applydup equ in ext; exrepnd.
  exists n m.
  applydup ceqa in ext.
  applydup ceqb in ext.
  spcast.
  eapply cequivc_trans in ext3;[|apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto].
  eapply cequivc_trans in ext4;[|apply cequivc_sym;apply computes_to_valc_implies_cequivc;eauto].
  apply cequivc_nat_implies_computes_to_valc in ext3.
  apply cequivc_nat_implies_computes_to_valc in ext4.
  dands; spcast; auto.
Qed.
Hint Resolve ccequivc_ext_preserves_equality_of_qlt : slow.

Lemma implies_eq_term_equals_per_qlt_bar2 {o} :
  forall lib (a b c d : @CTerm o),
    ccequivc_ext lib a c
    -> ccequivc_ext lib b d
    -> (equality_of_qlt_bar lib a b) <=2=> (equality_of_qlt_bar lib c d).
Proof.
  introv ceqa ceqb; introv.
  unfold equality_of_qlt_bar; split; introv h; exrepnd;
    eapply in_open_bar_pres; eauto; clear h; introv exd h; eauto 3 with slow;
      eapply ccequivc_ext_preserves_equality_of_qlt; try exact h; eauto 3 with slow.
Qed.

Lemma per_bar_eq_equality_of_qlt_bar_lib_per {o} :
  forall (lib : @library o) (a b : @CTerm o),
    (per_bar_eq lib (equality_of_qlt_bar_lib_per lib a b))
    <=2=> (equality_of_qlt_bar lib a b).
Proof.
  introv; simpl; unfold per_bar_eq; split; intro h; eauto 3 with slow.

  - apply in_open_bar_ext_in_open_bar.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    eapply in_open_bar_pres; eauto; clear h.
    introv h; introv; simpl in *; tcsp.

  - apply in_open_bar_ext_in_open_bar in h.
    eapply in_open_bar_ext_pres; eauto; clear h.
    introv h; simpl in *.
    eapply in_open_bar_pres; eauto; clear h.
    introv h; introv; simpl in *; tcsp.
Qed.

Lemma per_qlt_bar_implies_per_bar {o} :
  forall ts lib (T T' : @CTerm o) eq,
    per_qlt (close ts) lib T T' eq
    -> per_bar (close ts) lib T T' eq.
Proof.
  introv per.
  unfold per_qlt in *; exrepnd.

  exists (equality_of_qlt_bar_lib_per lib a b).
  dands.

  - apply in_ext_ext_implies_in_open_bar_ext; introv.
    apply CL_qlt.
    unfold per_qlt; dands; auto.
    eexists; eexists; eexists; eexists; dands; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|]; clear per1.
    apply eq_term_equals_sym; apply per_bar_eq_equality_of_qlt_bar_lib_per.
Qed.
Hint Resolve per_qlt_bar_implies_per_bar : slow.
