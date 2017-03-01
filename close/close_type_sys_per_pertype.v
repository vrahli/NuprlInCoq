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


Require Import type_sys_useful.
Require Import dest_close.



Lemma eq_term_equals_per_pertype_eq {o} :
  forall (eqr1 eqr2 : CTerm -> CTerm -> per(o)),
    (forall x y, (eqr1 x y) <=2=> (eqr2 x y))
    -> (per_pertype_eq eqr1) <=2=> (per_pertype_eq eqr2).
Proof.
  introv eiff.
  unfold per_pertype_eq, inhabited.
  split; introv h; exrepnd.

  - exists t.
    apply eiff; auto.

  - exists t.
    apply eiff; auto.
Qed.

Lemma per_pertype_eq_sym {o} :
  forall (eqr : CTerm -> CTerm -> per(o)) t1 t2,
    is_per eqr
    -> per_pertype_eq eqr t1 t2
    -> per_pertype_eq eqr t2 t1.
Proof.
  introv isp per.
  unfold per_pertype_eq in *; exrepnd.
  destruct isp as [sym trans].
  apply sym; auto.
Qed.

Lemma per_pertype_eq_trans {o} :
  forall (eqr : CTerm -> CTerm -> per(o)) t1 t2 t3,
    is_per eqr
    -> per_pertype_eq eqr t1 t2
    -> per_pertype_eq eqr t2 t3
    -> per_pertype_eq eqr t1 t3.
Proof.
  introv isp per1 per2.
  unfold per_pertype_eq in *.
  destruct isp as [sym trans].
  eapply trans; eauto.
Qed.

Lemma per_pertype_eq_cequivc {o} :
  forall lib ts R (eqr : CTerm -> CTerm -> per(o)) t1 t2,
    (forall x y, type_system_props lib ts (mkc_apply2 R x y) (eqr x y))
    -> cequivc lib t1 t2
    -> per_pertype_eq eqr t1 t1
    -> per_pertype_eq eqr t1 t2.
Proof.
  introv tsb ceq per.
  unfold per_pertype_eq in *.
  pose proof (tsb t1 t2) as q.

  dts_props q uv tv te tes tet tev.

  unfold type_value_respecting_body in *.

  pose proof (te (mkc_apply2 R t1 t1)) as q.
  autodimp q hyp.
  { apply implies_cequivc_apply2; auto; apply cequivc_sym; auto. }

  pose proof (tsb t1 t1) as h.

  dts_props h uv2 tv2 te2 tes2 tet2 tev2.

  apply uv2 in q.

  unfold inhabited in *; exrepnd.
  exists t.
  apply q; auto.
Qed.

Lemma close_type_system_pertype {p} :
  forall lib (ts : cts(p)) T (eq : per) R eqr,
    type_system lib ts
    -> defines_only_universes lib ts
    -> computes_to_valc lib T (mkc_pertype R)
    -> (forall x y : CTerm, close lib ts (mkc_apply2 R x y) (eqr x y))
    -> (forall x y : CTerm,
           type_system_props lib (close lib ts)
                             (mkc_apply2 R x y)
                             (eqr x y))
    -> is_per eqr
    -> eq <=2=> (per_pertype_eq eqr)
    -> per_pertype lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou comp clr tsr isp eqiff per.
  clear per.

  prove_ts_props SCase.

  - SCase "uniquely_valued".
    introv cls.
    dest_close_lr h.
    clear cls.
    unfold per_pertype in h; exrepnd; spcast.
    ccomputes_to_eqval.
    eapply eq_term_equals_trans;[eauto|].
    eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].

    pose proof (type_system_props_pertype_eq_term_equals lib (close lib ts) R eqr eqr0) as q.
    repeat (autodimp q hyp).

    apply eq_term_equals_per_pertype_eq; auto.

  - SCase "type_extensionality".
    introv eqt.
    apply CL_pertype.
    exists R eqr; dands; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  - SCase "type_value_respecting".
    introv ceq.
    apply CL_pertype.
    eapply cequivc_mkc_pertype in comp;[|eauto]; exrepnd.
    exists b eqr; dands; spcast; auto.

    introv.
    pose proof (tsr x y) as q.
    dts_props q uv tv te tes tet tev.
    apply te.
    apply implies_cequivc_apply2; auto.

  - SCase "term_symmetric".
    introv e.
    apply eqiff in e; apply eqiff.
    eapply per_pertype_eq_sym; eauto.

  - SCase "term_transitive".
    introv e1 e2.
    apply eqiff in e1; apply eqiff in e2; apply eqiff.
    eapply per_pertype_eq_trans; eauto.

  - SCase "term_value_respecting".
    introv e c; spcast.
    apply eqiff in e; apply eqiff; clear eqiff.

    eapply per_pertype_eq_cequivc; eauto.
Qed.
