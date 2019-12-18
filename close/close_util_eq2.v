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


  Website: http://nuprl.org/html/verification/
  Authors: Abhishek Anand & Vincent Rahli

*)


Require Export type_sys.
Require Import dest_close.
Require Export per_ceq_bar.

Require Export close_util_eq.
Require Export close_util1.


Lemma uniquely_valued_per_bar_per_eq {o} :
  forall inh (ts : cts(o)) lib T T1 T2 eq1 eq2 a1 a2 A B eqa,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A B (eqa lib' x))
    -> ccomputes_to_valc_ext inh lib T (mkc_equality a1 a2 A)
    -> per_bar inh (per_eq inh ts) lib T T1 eq1
    -> per_bar inh (per_eq inh ts) lib T T2 eq2
    -> (eq1 <=2=> eq2).
Proof.
  introv tsp comp pera perb.
  eapply uniquely_valued_per_bar2; eauto.
  clear eq1 eq2 pera perb.
  introv ext pera perb.
  unfold per_eq in *; exrepnd; spcast.

  eapply lib_extends_preserves_ccomputes_to_valc in comp;[|exact ext].
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  hide_hyp pera1.

  apply ccequivc_ext_mkc_equality_implies in ceq.
  apply ccequivc_ext_mkc_equality_implies in ceq0.
  repnd.

  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  clear pera0 perb0.

  introv; split; introv h.

  { eapply eq_per_eq_bar_respects_ccequivc_ext in h;
      [| | |
       |eapply ccequivc_ext_trans;[apply ccequivc_ext_sym;exact ceq1|exact ceq3]
       |eapply ccequivc_ext_trans;[apply ccequivc_ext_sym;exact ceq2|exact ceq4]
      ]; eauto 2 with slow.

    eapply simple_implies_iff_per_eq_eq; try exact h.
    apply in_ext_ext_implies_in_open_bar_ext.

    introv.
    pose proof (pera3 _ e) as pera3; simpl in *.
    pose proof (perb3 _ e) as perb3; simpl in *.
    pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
    eapply type_sys_props4_ccequivc_ext_implies_eq_term_equals; eauto 3 with slow. }

  { eapply eq_per_eq_bar_respects_ccequivc_ext in h;
      [| | |
       |eapply ccequivc_ext_trans;[apply ccequivc_ext_sym;exact ceq3|exact ceq1]
       |eapply ccequivc_ext_trans;[apply ccequivc_ext_sym;exact ceq4|exact ceq2]
      ]; eauto 2 with slow.

    eapply simple_implies_iff_per_eq_eq; try exact h.
    apply in_ext_ext_implies_in_open_bar_ext.

    introv.
    pose proof (pera3 _ e) as pera3; simpl in *.
    pose proof (perb3 _ e) as perb3; simpl in *.
    pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
    eapply type_sys_props4_ccequivc_ext_implies_eq_term_equals; eauto 3 with slow. }
Qed.
Hint Resolve uniquely_valued_per_bar_per_eq : slow.

Lemma per_bar_per_eq_implies_close {o} :
  forall inh (ts : cts(o)) lib T T' eq,
    per_bar inh (per_eq inh (close inh ts)) lib T T' eq
    -> close inh ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists eqa; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.
  apply CL_eq; auto.
Qed.

Lemma ccequivc_ext_equality {o} :
  forall inh lib (T T' : @CTerm o) a b A,
    ccequivc_ext inh lib T T'
    -> ccomputes_to_valc_ext inh lib T (mkc_equality a b A)
    -> ccomputes_to_valc_ext inh lib T' (mkc_equality a b A).
Proof.
  introv ceq comp; eauto 3 with slow.
Qed.

Lemma ccequivc_ext_implies_per_eq1 {o} :
  forall inh (ts : cts(o)) lib T0 T T' T3 eq a1 a2 A b1 b2 B (eqa : lib-per(inh,lib,o)),
    ccomputes_to_valc_ext inh lib T (mkc_equality a1 a2 A)
    -> ccomputes_to_valc_ext inh lib T' (mkc_equality b1 b2 B)
    -> in_ext_ext inh lib (fun lib' x => ts lib' A B (eqa lib' x))
    -> eqorceq_ext inh lib eqa a1 b1
    -> eqorceq_ext inh lib eqa a2 b2
    -> (eq <=2=> (eq_per_eq_bar inh lib a1 a2 eqa))
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A B (eqa lib' x))
    -> (T0 = T {+} T0 = T')
    -> ccequivc_ext inh lib T0 T3
    -> per_eq inh ts lib T0 T3 eq.
Proof.
  introv comp1 comp2 iext eor1 eor2 eqiff tsp h ceq; unfold per_eq in *; exrepnd; spcast.

  repndors; subst.

  - eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
    exists A A a1 a2 a1 a2 eqa; dands; spcast; auto; eauto 3 with slow.
    eapply in_ext_ext_type_sys_props4_ccequivc_ext_implies; eauto 3 with slow.

  - eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
    exists B B b1 b2 b1 b2 eqa; dands; spcast; auto; eauto 3 with slow.

    { eapply in_ext_ext_type_sys_props4_ccequivc_ext_implies; eauto 3 with slow. }

    eapply eq_term_equals_trans;[eauto|].
    apply eqorceq_implies_iff_per_eq_eq; eauto 3 with slow.
Qed.

Lemma type_value_respecting_trans_per_bar_per_eq1 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A A' B a1 a' a2 b' (eqa : lib-per(inh,lib,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A B (eqa lib' x))
    -> ccomputes_to_valc_ext inh lib T1 (mkc_equality a' b' A')
    -> ccomputes_to_valc_ext inh lib T (mkc_equality a1 a2 A)
    -> ccequivc_ext inh lib a1 a'
    -> ccequivc_ext inh lib a2 b'
    -> ccequivc_ext inh lib A A'
    -> per_bar inh (per_eq inh ts) lib T1 T2 eq
    -> per_bar inh (per_eq inh ts) lib T T2 eq.
Proof.
  introv tsp comp1 comp2 ceq1 ceq2 ceq3 per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_eq in *; exrepnd.
  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  eapply lib_extends_preserves_ccomputes_to_valc in comp2;[|exact e].
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq; repnd.

  exists A B0 a1 a2 b1 b2 eqa1; dands; spcast; eauto 3 with slow.

  - introv.
    pose proof (tsp lib'0 (lib_extends_trans e0 e)) as tsp; simpl in *.
    pose proof (per4 lib'0 e0) as per4; simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    eapply tyvrt1; eauto; eauto 4 with slow.

  - eapply cequivc_ext_eqorceq_ext_trans1; try exact per5; eauto 2 with slow.
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eauto 3 with slow. }

  - eapply cequivc_ext_eqorceq_ext_trans1; eauto; eauto 2 with slow.
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eauto 3 with slow. }

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.

    introv; split; introv h.

    { eapply eq_per_eq_bar_respects_ccequivc_ext in h;
        [| | |
         |eapply ccequivc_ext_trans;[eapply lib_extends_preserves_ccequivc_ext;[exact e|exact ceq1] |exact ceq0]
         |eapply ccequivc_ext_trans;[eapply lib_extends_preserves_ccequivc_ext;[exact e|exact ceq2] |exact ceq4]
        ]; eauto 2 with slow.
      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
          try exact tsp; try exact per4; eauto 3 with slow. }
      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
          try exact tsp; try exact per4; eauto 3 with slow. }
      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
          try exact tsp; try exact per4; eauto 3 with slow. } }

    { eapply eq_per_eq_bar_respects_ccequivc_ext in h;
        [| | |
         |eapply ccequivc_ext_trans;apply ccequivc_ext_sym;[exact ceq0|eapply lib_extends_preserves_ccequivc_ext;[exact e|exact ceq1] ]
         |eapply ccequivc_ext_trans;apply ccequivc_ext_sym;[exact ceq4|eapply lib_extends_preserves_ccequivc_ext;[exact e|exact ceq2] ]
        ]; eauto 2 with slow.
      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
          try exact tsp; try exact per4; eauto 3 with slow. }
      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
          try exact tsp; try exact per4; eauto 3 with slow. }
      { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
          try exact tsp; try exact per4; eauto 3 with slow. } }
Qed.

Lemma type_value_respecting_trans_per_bar_per_eq2 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A A' B a1 a' a2 b' (eqa : lib-per(inh,lib,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A B (eqa lib' x))
    -> ccomputes_to_valc_ext inh lib T1 (mkc_equality a' b' A')
    -> ccomputes_to_valc_ext inh lib T (mkc_equality a1 a2 A)
    -> ccequivc_ext inh lib a1 a'
    -> ccequivc_ext inh lib a2 b'
    -> ccequivc_ext inh lib A A'
    -> per_bar inh (per_eq inh ts) lib T2 T1 eq
    -> per_bar inh (per_eq inh ts) lib T T2 eq.
Proof.
  introv tsp comp1 comp2 ceq1 ceq2 ceq3 per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_eq in *; exrepnd.
  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  eapply lib_extends_preserves_ccomputes_to_valc in comp2;[|exact e].
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq; repnd.
  exists A A0 a1 a2 a0 a3 eqa1; dands; spcast; eauto 3 with slow.

  - introv.
    pose proof (tsp lib'0 (lib_extends_trans e0 e)) as tsp; simpl in *.
    pose proof (per4 lib'0 e0) as per4; simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    eapply tyvrt1; eauto; eauto 4 with slow.

  - eapply cequivc_ext_eqorceq_ext_trans2; eauto; eauto 2 with slow.
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eauto 3 with slow. }

  - eapply cequivc_ext_eqorceq_ext_trans2; eauto; eauto 2 with slow.
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eauto 3 with slow. }

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply eqorceq_implies_iff_per_eq_eq;
      try apply in_ext_ext_implies_in_open_bar_ext;
      try apply in_ext_implies_all_in_bar_trivial_bar;
      eauto 2 with slow;
      try (eapply cequivc_ext_eqorceq_ext_trans2; eauto; eauto 2 with slow);
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
                     try exact tsp; try exact per4; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
                     try exact tsp; try exact per4; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
                     try exact tsp; try exact per4; eauto 3 with slow));
      eauto 3 with slow.
Qed.

Lemma eq_per_eq_bar_sym {o} :
  forall inh lib a1 a2 (eqa : lib-per(inh,lib,o)) t1 t2,
    eq_per_eq_bar inh lib a1 a2 eqa t1 t2
    -> eq_per_eq_bar inh lib a1 a2 eqa t2 t1.
Proof.
  introv h; unfold eq_per_eq_bar in *; exrepnd.
  eapply in_open_bar_ext_pres; eauto; clear h; introv h.
  unfold eq_per_eq in *.
  repnd; dands; auto.
Qed.

Lemma eq_per_eq_bar_trans {o} :
  forall inh lib a1 a2 (eqa : lib-per(inh,lib,o)) t1 t2 t3,
    eq_per_eq_bar inh lib a1 a2 eqa t1 t2
    -> eq_per_eq_bar inh lib a1 a2 eqa t2 t3
    -> eq_per_eq_bar inh lib a1 a2 eqa t1 t3.
Proof.
  introv e1 e2; unfold eq_per_eq_bar in *; exrepnd.
  eapply in_open_bar_ext_comb; try exact e2; clear e2.
  eapply in_open_bar_ext_pres; eauto; clear e1; introv e1 e2.
  unfold eq_per_eq in *.
  repnd; dands; auto.
Qed.

Lemma eq_per_eq_bar_resp {o} :
  forall inh lib a1 a2 (eqa : lib-per(inh,lib,o)) t1 t2,
    eq_per_eq_bar inh lib a1 a2 eqa t1 t1
    -> ccequivc_ext inh lib t1 t2
    -> eq_per_eq_bar inh lib a1 a2 eqa t1 t2.
Proof.
  introv h ceq; unfold eq_per_eq_bar in *; exrepnd.
  eapply in_open_bar_ext_pres; eauto; clear h; introv h.
  unfold eq_per_eq in *.
  repnd; dands; spcast; eauto 3 with slow.
Qed.

Lemma type_symmetric_per_bar_per_eq1 {o} :
  forall inh lib (ts : cts(o)) T T' A B a1 a2 (eqa : lib-per(inh,lib,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A B (eqa lib' x))
    -> ccomputes_to_valc_ext inh lib T (mkc_equality a1 a2 A)
    -> per_bar inh (per_eq inh ts) lib T T' eq
    -> per_bar inh (per_eq inh ts) lib T' T eq.
Proof.
  introv tsp comp1 per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_eq in *; exrepnd.
  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq; repnd.
  exists B0 A b1 b2 a1 a2 eqa1; dands; spcast; eauto 3 with slow.

  - introv.
    pose proof (tsp lib'0 (lib_extends_trans e0 e)) as tsp; simpl in *.
    pose proof (per4 lib'0 e0) as per4; simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
    eapply tygs; eauto 5 with slow.

  - eapply eqorceq_ext_sym; auto;
      [eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
       try exact tsp; try exact per4; eauto 2 with slow
      |eapply eqorceq_ext_trans;[| | |apply ccequivc_ext_implies_eqorceq_ext;eauto|eauto] ].
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }

  - eapply eqorceq_ext_sym; auto;
      [eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
       try exact tsp; try exact per4; eauto 2 with slow
      |eapply eqorceq_ext_trans;[| | |apply ccequivc_ext_implies_eqorceq_ext;eauto|eauto] ].
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
        try exact tsp; try exact per4; eauto 3 with slow. }

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym;
      apply eqorceq_implies_iff_per_eq_eq;
      try apply in_ext_ext_implies_in_open_bar_ext;
      try apply in_ext_implies_in_open_bar;
      try (apply eqorceq_ext_sym; auto);
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
                     try exact tsp; try exact per4; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
                     try exact tsp; try exact per4; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
                     try exact tsp; try exact per4; eauto 3 with slow));
      eauto 3 with slow.
Qed.

Lemma type_symmetric_per_bar_per_eq2 {o} :
  forall inh lib (ts : cts(o)) T T' A B a1 a2 (eqa : lib-per(inh,lib,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A B (eqa lib' x))
    -> ccomputes_to_valc_ext inh lib T (mkc_equality a1 a2 A)
    -> per_bar inh (per_eq inh ts) lib T' T eq
    -> per_bar inh (per_eq inh ts) lib T T' eq.
Proof.
  introv tsp comp1 per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_eq in *; exrepnd.
  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq; repnd.
  exists B0 A0 b1 b2 a0 a3 eqa1; dands; spcast; eauto 3 with slow.

  - eapply eqorceq_ext_sym; auto.
    eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
      try (exact tsp); try exact per4; eauto 3 with slow.

  - eapply eqorceq_ext_sym; auto.
    eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
      try (exact tsp); try exact per4; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply eqorceq_implies_iff_per_eq_eq;
      try apply in_ext_ext_implies_in_open_bar_ext;
      try apply in_ext_implies_in_open_bar;
      try (apply eqorceq_ext_sym; auto);
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
                     try exact tsp; try exact per4; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
                     try exact tsp; try exact per4; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
                     try exact tsp; try exact per4; eauto 3 with slow));
      eauto 3 with slow.
Qed.

Lemma type_transitive_per_bar_per_eq1 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A B a1 a2 (eqa : lib-per(inh,lib,o)) eq1 eq2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A B (eqa lib' x))
    -> ccomputes_to_valc_ext inh lib T (mkc_equality a1 a2 A)
    -> per_bar inh (per_eq inh ts) lib T1 T eq1
    -> per_bar inh (per_eq inh ts) lib T T2 eq2
    -> per_bar inh (per_eq inh ts) lib T1 T2 eq1.
Proof.
  introv tsp comp1 pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa1; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; eauto; clear pera1; introv pera1 perb1.

  unfold per_eq in *; exrepnd.
  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq; repnd.
  apply ccequivc_ext_mkc_equality_implies in ceq0; repnd.
  exists A1 B0 a4 a5 b1 b2 eqa2; dands; spcast; eauto 3 with slow.

  - introv.
    pose proof (tsp lib'0 (lib_extends_trans e0 e)) as tsp; simpl in *.
    pose proof (pera4 lib'0 e0) as pera4; simpl in *.
    pose proof (perb4 lib'0 e0) as perb4; simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

    pose proof (tyvrt1 A B1 A1 (eqa3 lib'0 e0)) as xx.
    repeat (autodimp xx hyp); eauto 2 with slow;[].

    pose proof (tyvrt1 A A0 B0 (eqa2 lib'0 e0)) as yy.
    repeat (autodimp yy hyp); eauto 2 with slow;[].
    apply tygs in xx.

    pose proof (dum A A1 B0 (eqa3 lib'0 e0) (eqa2 lib'0 e0)) as q.
    repeat (autodimp q hyp); tcsp.

  - eapply eqorceq_ext_trans1; eauto;
      [| |
       |eapply eqorceq_ext_eq_change_per1;
        [|eapply eqorceq_ext_sym;
          [|eapply cequivc_ext_eqorceq_ext_trans2;
            [| | | |eauto];[| | |eauto 3 with slow] ] ] ];
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
                     try exact tsp; eauto; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
                     try exact tsp; eauto; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
                     try exact tsp; eauto; eauto 3 with slow)).
    { eapply in_ext_ext_type_sys_props4_ccequivc_ext_trans_implies_eq_term_equals1;
        try exact tsp; try exact pera4; try exact perb4; eauto 3 with slow. }

  - eapply eqorceq_ext_trans1; eauto;
      [| |
       |eapply eqorceq_ext_eq_change_per1;
        [|eapply eqorceq_ext_sym;
          [|eapply cequivc_ext_eqorceq_ext_trans2;
            [| | | |eauto];[| | |eauto 3 with slow] ] ] ];
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
                     try exact tsp; eauto; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
                     try exact tsp; eauto; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
                     try exact tsp; eauto; eauto 3 with slow)).
    { eapply in_ext_ext_type_sys_props4_ccequivc_ext_trans_implies_eq_term_equals1;
        try exact tsp; try exact pera4; try exact perb4; eauto 3 with slow. }

  - eapply eq_term_equals_trans;[eauto|].
    apply eqorceq_implies_iff_per_eq_eq;
      try apply in_ext_ext_implies_in_open_bar_ext;
      try apply in_ext_implies_in_open_bar;
      try apply eqorceq_ext_refl.
    { eapply in_ext_ext_type_sys_props4_ccequivc_ext_trans_implies_eq_term_equals1;
        try exact tsp; try exact pera4; try exact perb4; eauto 2 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
        try (exact tsp); try exact per4; eauto 2 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
        try (exact tsp); try exact per4; eauto 2 with slow. }
    { eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
        try (exact tsp); try exact per4; eauto 2 with slow. }
Qed.

Lemma type_transitive_per_bar_per_eq2 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A B a1 a2 (eqa : lib-per(inh,lib,o)) eq1 eq2,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A B (eqa lib' x))
    -> ccomputes_to_valc_ext inh lib T (mkc_equality a1 a2 A)
    -> per_bar inh (per_eq inh ts) lib T1 T eq1
    -> per_bar inh (per_eq inh ts) lib T T2 eq2
    -> per_bar inh (per_eq inh ts) lib T1 T2 eq2.
Proof.
  introv tsp comp1 pera perb.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_comb; try exact perb1; clear perb1.
  eapply in_open_bar_ext_pres; eauto; clear pera1; introv pera1 perb1.

  unfold per_eq in *; exrepnd.
  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  computes_to_eqval_ext.
  hide_hyp perb1.
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq; repnd.
  apply ccequivc_ext_mkc_equality_implies in ceq0; repnd.
  exists A1 B0 a4 a5 b1 b2 eqa2; dands; spcast; eauto 3 with slow.

  - introv.
    pose proof (tsp lib'0 (lib_extends_trans e0 e)) as tsp; simpl in *.
    pose proof (pera4 lib'0 e0) as pera4; simpl in *.
    pose proof (perb4 lib'0 e0) as perb4; simpl in *.
    onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.

    pose proof (tyvrt1 A B1 A1 (eqa3 lib'0 e0)) as xx.
    repeat (autodimp xx hyp); eauto 2 with slow;[].

    pose proof (tyvrt1 A A0 B0 (eqa2 lib'0 e0)) as yy.
    repeat (autodimp yy hyp); eauto 2 with slow;[].
    apply tygs in xx.

    pose proof (dum A A1 B0 (eqa3 lib'0 e0) (eqa2 lib'0 e0)) as q.
    repeat (autodimp q hyp); tcsp.

  - eapply eqorceq_ext_trans1; eauto;
      [| |
       |eapply eqorceq_ext_eq_change_per1;
        [|eapply eqorceq_ext_sym;
          [|eapply cequivc_ext_eqorceq_ext_trans2;
            [| | | |eauto];[| | |eauto 3 with slow] ] ] ];
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
                     try exact tsp; eauto; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
                     try exact tsp; eauto; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
                     try exact tsp; eauto; eauto 3 with slow)).
    { eapply in_ext_ext_type_sys_props4_ccequivc_ext_trans_implies_eq_term_equals1;
        try exact tsp; try exact pera4; try exact perb4; eauto 3 with slow. }

  - eapply eqorceq_ext_trans1; eauto;
      [| |
       |eapply eqorceq_ext_eq_change_per1;
        [|eapply eqorceq_ext_sym;
          [|eapply cequivc_ext_eqorceq_ext_trans2;
            [| | | |eauto];[| | |eauto 3 with slow] ] ] ];
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
                     try exact tsp; eauto; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
                     try exact tsp; eauto; eauto 3 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
                     try exact tsp; eauto; eauto 3 with slow)).
    { eapply in_ext_ext_type_sys_props4_ccequivc_ext_trans_implies_eq_term_equals1;
        try exact tsp; try exact pera4; try exact perb4; eauto 3 with slow. }

  - eapply eq_term_equals_trans;[eauto|].
    apply eqorceq_implies_iff_per_eq_eq;
      try apply in_ext_ext_implies_in_open_bar_ext;
      try apply in_ext_implies_in_open_bar;
      try apply eqorceq_ext_refl;
      try (complete (introv; tcsp));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow));
      try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per;
                     try (exact tsp); try exact per4; eauto 2 with slow)).

    { apply eqorceq_ext_sym;
        try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
                       try (exact tsp); try exact per4; eauto 2 with slow)).

      eapply eqorceq_ext_eq_change_per1;
        [|eapply eqorceq_ext_trans1; try exact pera5;
          try apply ccequivc_ext_implies_eqorceq_ext;
          try (eapply ccequivc_ext_trans; try exact ceq1; apply ccequivc_ext_sym;auto);
          try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
                         try (exact tsp); try exact per4; eauto 2 with slow));
          try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
                         try (exact tsp); try exact per4; eauto 2 with slow));
          try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
                         try (exact tsp); try exact per4; eauto 2 with slow))
        ].
      { eapply in_ext_ext_type_sys_props4_ccequivc_ext_trans_implies_eq_term_equals1;
          try exact tsp; try exact pera4; try exact perb4; eauto 3 with slow. }
    }

    { apply eqorceq_ext_sym;
        try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per;
                       try (exact tsp); try exact per4; eauto 2 with slow)).

      eapply eqorceq_ext_eq_change_per1;
        [|eapply eqorceq_ext_trans1; try exact pera6;
          try apply ccequivc_ext_implies_eqorceq_ext;
          try (eapply ccequivc_ext_trans; try exact ceq2; apply ccequivc_ext_sym;auto);
          try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_symmetric_change_per3;
                         try (exact tsp); try exact per4; eauto 2 with slow));
          try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_transitive_change_per3;
                         try (exact tsp); try exact per4; eauto 2 with slow));
          try (complete (eapply in_ext_ext_type_sys_props4_implies_in_ext_ext_term_equality_respecting_change_per3;
                         try (exact tsp); try exact per4; eauto 2 with slow))
        ].
      { eapply in_ext_ext_type_sys_props4_ccequivc_ext_trans_implies_eq_term_equals1;
          try exact tsp; try exact pera4; try exact perb4; eauto 3 with slow. }
    }
Qed.

Lemma implies_type_equality_respecting_trans1_per_eq {o} :
  forall inh lib ts (T T' : @CTerm o) A B a1 a2 b1 b2 (eqa : lib-per(inh,lib,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> T ===>(inh,lib) (mkc_equality a1 a2 A)
    -> T' ===>(inh,lib) (mkc_equality b1 b2 B)
    -> in_ext_ext inh lib (fun lib' x => close inh ts lib' A B (eqa lib' x))
    -> eqorceq_ext inh lib eqa a1 b1
    -> eqorceq_ext inh lib eqa a2 b2
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A B (eqa lib' x))
    -> type_equality_respecting_trans1 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou c1 c2 inextcl eos1 eos2 inexttsp; introv h ceq cl.
  repndors; subst.

  * dup ceq as c.
    eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
    dup inexttsp as inexttsp'.
    eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in inexttsp';[|apply ccequivc_ext_refl].
    dclose_lr; clear cl.
    apply per_bar_per_eq_implies_close.
    eapply type_value_respecting_trans_per_bar_per_eq1;
      try exact h; try exact c1; eauto 3 with slow.

  * dup ceq as c.
    eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
    dup inexttsp as inexttsp'.
    apply in_ext_ext_type_sys_props4_sym in inexttsp'.
    dup inexttsp' as inexttsp''.
    eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in inexttsp';[|apply ccequivc_ext_refl].
    dclose_lr; clear cl.
    apply per_bar_per_eq_implies_close.
    eapply type_value_respecting_trans_per_bar_per_eq1;
      try exact h; try exact c2; eauto 3 with slow.

  * dup ceq as c.
    eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
    dup inexttsp as inexttsp'.
    eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in inexttsp';[|apply ccequivc_ext_refl].
    apply in_ext_ext_type_sys_props4_sym in inexttsp'.
    dclose_lr; clear cl.
    apply per_bar_per_eq_implies_close.
    eapply type_value_respecting_trans_per_bar_per_eq2;
      try exact h; try exact c1; eauto 3 with slow.

  * dup ceq as c.
    eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
    dup inexttsp as inexttsp'.
    apply in_ext_ext_type_sys_props4_sym in inexttsp'.
    dup inexttsp' as inexttsp''.
    eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in inexttsp';[|apply ccequivc_ext_refl].
    apply in_ext_ext_type_sys_props4_sym in inexttsp'.
    dclose_lr; clear cl.
    apply per_bar_per_eq_implies_close.
    eapply type_value_respecting_trans_per_bar_per_eq2;
      try exact h; try exact c2; eauto 3 with slow.
Qed.

Lemma type_value_respecting_trans_per_bar_per_eq3 {o} :
  forall inh lib (ts : cts(o)) T T1 T2 A B a b (eqa : lib-per(inh,lib,o)) eq,
    in_ext_ext inh lib (fun lib' x => type_sys_props4 inh ts lib' A B (eqa lib' x))
    -> ccomputes_to_valc_ext inh lib T (mkc_equality a b A)
    -> ccequivc_ext inh lib T1 T2
    -> per_bar inh (per_eq inh ts) lib T T1 eq
    -> per_bar inh (per_eq inh ts) lib T T2 eq.
Proof.
  introv tsp comp1 ceq1 per.
  unfold per_bar in *; exrepnd.
  exists eqa0; dands; auto.
  eapply in_open_bar_ext_pres; eauto; clear per1; introv per1.

  unfold per_eq in *; exrepnd.
  eapply lib_extends_preserves_ccomputes_to_valc in comp1;[|exact e].
  computes_to_eqval_ext.
  apply ccequivc_ext_mkc_equality_implies in ceq; repnd.

  eapply lib_extends_preserves_ccequivc_ext in ceq1;[|eauto].
  eapply ccequivc_ext_equality in ceq1;[|eauto].

  exists A0 B0 a1 a2 b1 b2 eqa1; dands; spcast; eauto 3 with slow.
Qed.

Lemma implies_type_equality_respecting_trans2_per_eq {o} :
  forall inh lib ts (T T' : @CTerm o) A B a1 a2 b1 b2 (eqa : lib-per(inh,lib,o)),
    type_system inh ts
    -> defines_only_universes inh ts
    -> T ===>(inh,lib) (mkc_equality a1 a2 A)
    -> T' ===>(inh,lib) (mkc_equality b1 b2 B)
    -> in_ext_ext inh lib (fun lib' x => close inh ts lib' A B (eqa lib' x))
    -> eqorceq_ext inh lib eqa a1 b1
    -> eqorceq_ext inh lib eqa a2 b2
    -> in_ext_ext inh lib (fun lib' x => type_sys_props4 inh (close inh ts) lib' A B (eqa lib' x))
    -> type_equality_respecting_trans2 inh (close inh ts) lib T T'.
Proof.
  introv tsts dou c1 c2 inextcl eos1 eos2 inexttsp; introv h cl ceq.
  repndors; subst.

  * dclose_lr; clear cl.
    apply per_bar_per_eq_implies_close.
    eapply type_value_respecting_trans_per_bar_per_eq3; eauto.

  * apply in_ext_ext_type_sys_props4_sym in inexttsp.
    dclose_lr; clear cl.
    apply per_bar_per_eq_implies_close.
    eapply type_value_respecting_trans_per_bar_per_eq3; eauto.

  * apply in_ext_ext_type_sys_props4_sym in inexttsp.
    dclose_lr; clear cl.
    apply per_bar_per_eq_implies_close.
    apply in_ext_ext_type_sys_props4_sym in inexttsp.
    eapply type_symmetric_per_bar_per_eq2 in h; eauto.
    eapply type_value_respecting_trans_per_bar_per_eq3; eauto.

  * dclose_lr; clear cl.
    apply per_bar_per_eq_implies_close.
    apply in_ext_ext_type_sys_props4_sym in inexttsp.
    eapply type_symmetric_per_bar_per_eq2 in h; eauto.
    eapply type_value_respecting_trans_per_bar_per_eq3; eauto.
Qed.
