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
Require Import dest_close.


(*
Lemma per_int_uniquely_valued {p} :
  forall lib (ts : cts(p)), uniquely_valued (per_int lib ts).
Proof.
 unfold uniquely_valued, per_int, eq_term_equals; sp.
 allrw; sp.
Qed.

Lemma per_int_type_extensionality {p} :
  forall lib (ts : cts(p)), type_extensionality (per_int lib ts).
Proof.
  unfold type_extensionality, per_int, eq_term_equals; sp.
  allrw <-; sp.
Qed.

Lemma per_int_type_value_respecting {p} :
  forall lib (ts : cts(p)), type_value_respecting lib (per_int lib ts).
Proof.
 sp; unfold type_value_respecting, per_int; sp; auto.
 spcast; apply @cequivc_int with (T := T); auto.
Qed.

Lemma per_int_term_symmetric {p} :
  forall lib (ts : cts(p)), term_symmetric (per_int lib ts).
Proof.
  unfold term_symmetric, term_equality_symmetric, per_int; introv ts h e; repnd; spcast.
  apply h in e; apply h.
  allunfold @equality_of_int; exrepnd.
  exists k; sp.
Qed.

Lemma per_int_term_transitive {p} :
  forall lib (ts : cts(p)), term_transitive (per_int lib ts).
Proof.
  unfold term_transitive, term_equality_transitive, per_int.
  introv cts i e1 e2; repnd; spcast.
  apply i in e1; apply i in e2; apply i; clear i.
  allunfold @equality_of_int; exrepnd.
  exists k; sp.
  ccomputes_to_eqval; spcast; sp.
Qed.

Lemma per_int_term_value_respecting {p} :
  forall lib (ts : cts(p)), term_value_respecting lib (per_int lib ts).
Proof.
  unfold term_value_respecting, term_equality_respecting, per_int.
  introv cts i e c; repnd.
  apply i in e; apply i.
  allunfold @equality_of_int; exrepnd.
  exists k; sp.
  spcast; apply @cequivc_integer with (t := t); auto.
Qed.

Lemma per_int_type_system {p} :
  forall lib (ts : cts(p)), type_system lib (per_int lib ts).
Proof.
  intros; unfold type_system; sp;
    try apply per_int_uniquely_valued; auto;
      try apply per_int_type_extensionality; auto;
        try apply per_int_type_value_respecting; auto;
          try apply per_int_term_symmetric; auto;
            try apply per_int_term_transitive; auto;
              try apply per_int_term_value_respecting; auto.
Qed.
*)

Lemma close_type_system_int {p} :
  forall lib (ts : cts(p)) T eq,
    type_system lib ts
    -> defines_only_universes lib ts
    -> per_int lib (close lib ts) T eq
    -> type_system_props lib (close lib ts) T eq.
Proof.
  introv tysys dou per.
  unfold per_int in per; repnd; spcast.

  prove_ts_props Case.

  + SCase "uniquely_valued".
    introv cl.
    eapply eq_term_equals_trans;[eauto|].
    dest_close_lr h.
    onedts uv tye tyvr tes tet tevr.
    unfold per_int in h; repnd.
    apply eq_term_equals_sym; auto.

  + SCase "type_extensionality".
    introv eqt.
    apply CL_int.
    split; spcast; auto.
    eapply eq_term_equals_trans;[|eauto].
    apply eq_term_equals_sym; auto.

  + SCase "type_value_respecting".
    introv ceq.
    apply CL_int.
    apply cequivc_int in ceq; auto.
    split; spcast; auto.

  + SCase "term_symmetric".
    introv e.
    apply per in e; apply per; clear per.
    unfold equality_of_int in *; exrepnd; exists k; auto.

  + SCase "term_transitive".
    introv e1 e2.
    apply per in e1; apply per in e2; apply per; clear per.
    unfold equality_of_int in *; exrepnd; exists k; auto.
    ccomputes_to_eqval; dands; spcast; auto.

  + SCase "term_value_respecting".
    introv e c; spcast.
    apply per in e; apply per; clear per.
    unfold equality_of_int in *; exrepnd; spcast.
    exists k; dands; spcast; auto.
    eapply cequivc_integer; eauto.
Qed.
