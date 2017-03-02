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
  Authors: Abhishek Anand & Vincent Rahli

*)

Require Export per_props.


(* !!MOVE *)
Hint Resolve alphaeqc_trans : slow.
Hint Resolve alphaeqc_sym : slow.

Lemma respects_alphaeqc_alphaeqc {o} : respects2 alphaeqc (@alphaeqc o).
Proof.
  unfold respects2; dands; introv aeq1 aeq2; eauto 3 with slow.
Qed.
Hint Resolve respects_alphaeqc_alphaeqc : respects.

Lemma member_respects_alphaeqc_l {o} :
  forall lib (t1 t2 T : @CTerm o),
    alphaeqc t1 t2 -> member lib t1 T -> member lib t2 T.
Proof.
  introv aeq mem.
  allunfold @member.
  eapply equality_respects_alphaeqc_left;[exact aeq|].
  eapply equality_respects_alphaeqc_right;[exact aeq|].
  auto.
Qed.

Lemma member_respects_alphaeqc_r {o} :
  forall lib (t T1 T2 : @CTerm o),
    alphaeqc T1 T2 -> member lib t T1 -> member lib t T2.
Proof.
  introv aeq mem.
  allunfold @member.
  eapply alphaeqc_preserving_equality; eauto.
Qed.

Lemma respects_alphaeqc_member {o} :
  forall (lib : @library o), respects2 alphaeqc (member lib).
Proof.
  introv; unfold respects2; dands; introv aeq1 aeq2; eauto 3 with slow.
  - eapply member_respects_alphaeqc_l; eauto.
  - eapply member_respects_alphaeqc_r; eauto.
Qed.
Hint Resolve respects_alphaeqc_member : respects.

Lemma respects_alphaeqc_equorsq3 {o} :
  forall lib (t1 t2 T1 T2 : @CTerm o),
    alphaeqc T1 T2
    -> equorsq lib t1 t2 T1
    -> equorsq lib t1 t2 T2.
Proof.
  introv aeq e.
  eauto 3 with slow.
  pose proof (respects_alphaeqc_equorsq lib) as h.
  destruct h as [h1 h]; repnd.
  eapply h; eauto.
Qed.

Lemma respects_alphaeqc_cequivc {p} : forall lib, respects2 alphaeqc (@cequivc p lib).
Proof.
  introv; unfolds_base; dands; introv Hr Heq; allsimpl;
  try (complete (left; eauto 3 with nequality)).
  - apply (cequivc_trans lib a' a b); auto; apply cequivc_sym; apply alphaeqc_implies_cequivc; auto.
  - apply (cequivc_trans lib a b b'); auto; apply alphaeqc_implies_cequivc; auto.
Qed.
Hint Resolve respects_alphaeqc_cequivc : respects.
