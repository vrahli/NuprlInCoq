(*

  Copyright 2014 Cornell University

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


Lemma implies_eq_term_equals_per_bar_eq {o} :
  forall {lib} (bar1 bar2 : @BarLib o lib) (eqa eqb : lib-per(lib,o)),
    all_in_bar_ext (intersect_bars bar1 bar2) (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> (per_bar_eq bar1 eqa) <=2=> (per_bar_eq bar2 eqb).
Proof.
  introv alla; introv; split; intro h.

  - apply (per_bar_eq_intersect_bars_right bar2 bar1).
    eapply all_in_bar_ext_eq_term_equals_preserves_per_bar_eq; eauto.
    apply (per_bar_eq_intersect_bars_left bar1 bar2); auto.

  - apply (per_bar_eq_intersect_bars_left bar1 bar2).
    apply all_in_bar_ext_eq_term_equals_sym in alla.
    eapply all_in_bar_ext_eq_term_equals_preserves_per_bar_eq; eauto.
    apply (per_bar_eq_intersect_bars_right bar2 bar1); auto.
Qed.

Definition uniquely_valued_def {o} (ts : cts(o)) lib T :=
  forall T1 T2 eq1 eq2,
    ts lib T T1 eq1
    -> ts lib T T2 eq2
    -> eq1 <=2=> eq2.

Lemma uniquely_valued_per_bar2 {o} :
  forall (ts : cts(o)) lib T,
    in_ext lib (fun lib => uniquely_valued_def ts lib T)
    -> uniquely_valued_def (per_bar ts) lib T.
Proof.
  introv uv pera perb.
  unfold per_bar in *; exrepnd.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  clear pera1 perb1.

  apply implies_eq_term_equals_per_bar_eq.
  introv br ext; introv; simpl in *; exrepnd.

  pose proof (pera0 _ br0 lib'0 (lib_extends_trans ext br3) x) as pera0.
  pose proof (perb0 _ br2 lib'0 (lib_extends_trans ext br1) x) as perb0.
  simpl in *.
  eapply uv; eauto.
Qed.

Lemma type_sys_props4_implies_eq_term_equals {o} :
  forall (ts : cts(o)) lib A B C D eqa eqa1 eqa2,
    type_sys_props4 ts lib A B eqa
    -> ts lib A C eqa1
    -> ts lib A D eqa2
    -> eqa1 <=2=> eqa2.
Proof.
  introv h w q; introv.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply uv in w.
  apply uv in q.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.

Lemma uniquely_valued_per_bar_per_eq {o} :
  forall (ts : cts(o)) lib T T1 T2 eq1 eq2 a1 a2 A B eqa,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> computes_to_valc lib T (mkc_equality a1 a2 A)
    -> per_bar (per_eq ts) lib T T1 eq1
    -> per_bar (per_eq ts) lib T T2 eq2
    -> (eq1 <=2=> eq2).
Proof.
  introv tsp comp pera perb.
  eapply uniquely_valued_per_bar2; eauto.
  clear eq1 eq2 pera perb.
  introv ext pera perb.
  unfold per_eq in *; exrepnd; spcast.

  eapply lib_extends_preserves_computes_to_valc in comp;[|exact ext].
  repeat computes_to_eqval.
  eapply eq_term_equals_trans;[eauto|].
  eapply eq_term_equals_trans;[|apply eq_term_equals_sym;eauto].
  clear pera0 perb0.

  apply (simple_implies_iff_per_eq_eq _ (trivial_bar lib')).
  apply in_ext_ext_implies_all_in_bar_ext.

  introv.
  pose proof (pera3 _ e) as pera3; simpl in *.
  pose proof (perb3 _ e) as perb3; simpl in *.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  eapply type_sys_props4_implies_eq_term_equals; eauto.
Qed.
Hint Resolve uniquely_valued_per_bar_per_eq : slow.

Lemma per_bar_per_eq_implies_close {o} :
  forall (ts : cts(o)) lib T T' eq,
    per_bar (per_eq (close ts)) lib T T' eq
    -> close ts lib T T' eq.
Proof.
  introv per.
  apply CL_bar.
  unfold per_bar in per; exrepnd.
  exists bar eqa; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.
  apply CL_eq; auto.
Qed.

Lemma ccequivc_ext_equality {o} :
  forall lib (T T' : @CTerm o) a b A,
    ccequivc_ext lib T T'
    -> computes_to_valc lib T (mkc_equality a b A)
    -> {a' : CTerm , {b' : CTerm , {A' : CTerm ,
        ccomputes_to_valc lib T' (mkc_equality a' b' A')
        # ccequivc_ext lib a a'
        # ccequivc_ext lib b b'
        # ccequivc_ext lib A A' }}}.
Proof.
  introv ceq comp.
  pose proof (ceq lib) as ceq'; simpl in ceq'; autodimp ceq' hyp; eauto 3 with slow; spcast.
  eapply cequivc_mkc_equality in ceq';[|eauto]; exrepnd.
  exists a' b' T'0; dands; spcast; auto.

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_equality a b A) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_equality a' b' T'0) ceq'1) as z.
    eapply cequivc_mkc_equality in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_equality a b A) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_equality a' b' T'0) ceq'1) as z.
    eapply cequivc_mkc_equality in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }

  {
    introv ext.
    pose proof (ceq lib' ext) as c; simpl in c; spcast.

    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T (mkc_equality a b A) comp) as w.
    pose proof (lib_extends_preserves_computes_to_valc lib lib' ext T' (mkc_equality a' b' T'0) ceq'1) as z.
    eapply cequivc_mkc_equality in c;[|eauto]; exrepnd.
    computes_to_eqval; auto.
  }
Qed.

Lemma ccequivc_ext_implies_eqorceq_ext {o} :
  forall lib (a b : @CTerm o) eqa,
    ccequivc_ext lib a b
    -> eqorceq_ext lib eqa a b.
Proof.
  introv ceq; introv.
  right; eauto 3 with slow.
Qed.
Hint Resolve ccequivc_ext_implies_eqorceq_ext : slow.

Lemma in_ext_ext_type_sys_props4_ccequivc_ext_implies {o} :
  forall lib (ts : cts(o)) T A B A' eqa,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> (T = A {+} T = B)
    -> ccequivc_ext lib T A'
    -> in_ext_ext lib (fun lib' x => ts lib' T A' (eqa lib' x)).
Proof.
  introv tsp h ceq; introv.
  pose proof (tsp _ e) as tsp.
  simpl in *; spcast.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  apply tyvr; eauto 3 with slow.
Qed.

Lemma in_ext_ext_eq_term_equals_refl {o} :
  forall lib (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqa lib' x)).
Proof.
  repeat introv; tcsp.
Qed.
Hint Resolve in_ext_ext_eq_term_equals_refl : slow.


Lemma ccequivc_ext_implies_per_eq1 {o} :
  forall (ts : cts(o)) lib T0 T T' T3 eq a1 a2 A b1 b2 B (eqa : lib-per(lib,o)),
    computes_to_valc lib T (mkc_equality a1 a2 A)
    -> computes_to_valc lib T' (mkc_equality b1 b2 B)
    -> in_ext_ext lib (fun lib' x => ts lib' A B (eqa lib' x))
    -> eqorceq_ext lib eqa a1 b1
    -> eqorceq_ext lib eqa a2 b2
    -> (eq <=2=> (eq_per_eq_bar lib a1 a2 eqa))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> (T0 = T {+} T0 = T')
    -> ccequivc_ext lib T0 T3
    -> per_eq ts lib T0 T3 eq.
Proof.
  introv comp1 comp2 iext eor1 eor2 eqiff tsp h ceq; unfold per_eq in *; exrepnd; spcast.

  repndors; subst.

  - eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
    exists A A' a1 a2 a' b' eqa; dands; spcast; auto; eauto 3 with slow.
    eapply in_ext_ext_type_sys_props4_ccequivc_ext_implies; eauto.

  - eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
    exists B A' b1 b2 a' b' eqa; dands; spcast; auto; eauto 3 with slow.

    { eapply in_ext_ext_type_sys_props4_ccequivc_ext_implies; eauto. }

    eapply eq_term_equals_trans;[eauto|].
    apply (eqorceq_implies_iff_per_eq_eq _ (trivial_bar lib));
      try apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;
      try apply in_ext_implies_all_in_bar_trivial_bar; eauto 3 with slow.
Qed.

Lemma ccequivc_ext_preserves_in_ext_ext_type_sys_props4 {o} :
  forall ts lib (A A' B : @CTerm o) eqa,
    ccequivc_ext lib A A'
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A' B (eqa lib' x)).
Proof.
  introv ceq tsp; introv.
  pose proof (tsp _ e) as tsp; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  unfold type_sys_props4; dands; auto.

  - introv tsts.
    apply (uv T3).
    apply (tyvrt A A' T3 eq'); eauto 3 with slow.

  - introv tsts eqs.
    pose proof (tyvrt A A' T3 (eqa lib' e)) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    eapply tys in q;eauto.
    pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
    pose proof (dum A A' T3 (eqa lib' e) eq') as w.
    repeat (autodimp w hyp); tcsp.
    apply tygs; auto.

  - introv w c.
    repndors; subst; tcsp.

    pose proof (tyvr A T3) as q; repeat (autodimp q hyp); eauto 3 with slow.
    pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
    pose proof (dum A A' T3 (eqa lib' e) (eqa lib' e)) as w.
    repeat (autodimp w hyp); tcsp.
    apply tygs; auto.

  - introv h c tsts.
    repndors; subst; tcsp; try (complete (eapply tyvrt; eauto)).

    + pose proof (tyvrt A T3 T4 eq') as q; repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
      pose proof (dum A A' T4 (eqa lib' e) eq') as w.
      repeat (autodimp w hyp); tcsp.
      apply tygs; auto.

    + pose proof (tyvrt A T3 T4 eq') as q; repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
      pose proof (dum A A' T4 (eqa lib' e) eq') as w.
      repeat (autodimp w hyp); tcsp.
      apply tygs; auto.

  - introv; split; intro q.

    + pose proof (tyvrt A A' T3 eq') as h; repeat (autodimp h hyp); eauto 3 with slow.
      apply tygs in h.
      pose proof (tyvr A A') as z; repeat (autodimp z hyp); eauto 3 with slow.
      pose proof (dum A T3 A' eq' (eqa lib' e)) as w.
      repeat (autodimp w hyp); tcsp.

    + pose proof (tyvrt A A' T3 eq') as h; repeat (autodimp h hyp); eauto 3 with slow.
      pose proof (tyvr A A') as z; repeat (autodimp z hyp); eauto 3 with slow.
      apply tygs in z.
      pose proof (dum A A' T3 (eqa lib' e) eq') as w.
      repeat (autodimp w hyp); tcsp.

  - pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
    pose proof (dum A A' B (eqa lib' e) (eqa lib' e)) as w.
    repeat (autodimp w hyp); tcsp.
    apply tygs; auto.

  - introv h ts1 ts2.
    repndors; subst; tcsp; try (complete (eapply dum; eauto)).

    pose proof (tyvrt A A' T4 eq2) as h; repeat (autodimp h hyp); eauto 3 with slow.
    pose proof (tyvrt A A' T3 eq1) as q; repeat (autodimp q hyp); eauto 3 with slow.
    apply tygs in q.

    pose proof (dum A T3 T4 eq1 eq2) as w.
    repeat (autodimp w hyp); tcsp; try (complete (apply tygs; auto)).
Qed.

Lemma cequivc_ext_eqorceq_ext_trans1 {o} :
  forall lib (a b c : @CTerm o) (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> ccequivc_ext lib a b
    -> eqorceq_ext lib eqa b c
    -> eqorceq_ext lib eqa a c.
Proof.
  introv resp trans sym ceq eoc; introv.
  pose proof (eoc _ e) as eoc.
  pose proof (resp _ e) as resp.
  pose proof (sym _ e) as sym.
  pose proof (trans _ e) as trans.
  simpl in *; spcast.
  unfold eqorceq in *; repndors.

  - left.
    eapply trans;[|eauto].
    apply sym.
    apply resp;[|apply ccequivc_ext_sym; eauto 3 with slow].
    eapply trans;[eauto|]; tcsp.

  - right.
    eapply ccequivc_ext_trans;[|eauto]; eauto 3 with slow.
Qed.

Lemma eq_term_equals_preserves_term_equality_respecting {o} :
  forall lib (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> term_equality_respecting lib eqa1
    -> term_equality_respecting lib eqa2.
Proof.
  introv eqs resp e ceq.
  apply eqs.
  apply resp; auto.
  apply eqs; auto.
Qed.
Hint Resolve eq_term_equals_preserves_term_equality_respecting : slow.

Lemma eq_term_equals_preserves_term_equality_symmetric {o} :
  forall (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> term_equality_symmetric eqa1
    -> term_equality_symmetric eqa2.
Proof.
  introv eqs sym e.
  apply eqs; apply eqs in e; tcsp.
Qed.
Hint Resolve eq_term_equals_preserves_term_equality_symmetric : slow.

Lemma eq_term_equals_preserves_term_equality_transitive {o} :
  forall (eqa1 eqa2 : per(o)),
    (eqa1 <=2=> eqa2)
    -> term_equality_transitive eqa1
    -> term_equality_transitive eqa2.
Proof.
  introv eqs tr e1 e2.
  apply eqs; apply eqs in e1; apply eqs in e2; tcsp.
  eapply tr; eauto.
Qed.
Hint Resolve eq_term_equals_preserves_term_equality_transitive : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals1 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B A' B',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' A' B' (eqa1 lib' x))
    -> ccequivc_ext lib A A'
    -> in_ext_ext lib' (fun lib'' x => term_equality_respecting lib'' (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  pose proof (tyvrt A A' B' (eqa1 lib'0 e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals1 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals1 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B A' B',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' A' B' (eqa1 lib' x))
    -> ccequivc_ext lib A A'
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  pose proof (tyvrt A A' B' (eqa1 lib'0 e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals1 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals1 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B A' B',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' A' B' (eqa1 lib' x))
    -> ccequivc_ext lib A A'
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  pose proof (tyvrt A A' B' (eqa1 lib'0 e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals1 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals2 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B A' B',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' B' A' (eqa1 lib' x))
    -> ccequivc_ext lib A A'
    -> in_ext_ext lib' (fun lib'' x => term_equality_respecting lib'' (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  pose proof (tyvrt A A' B' (eqa1 lib'0 e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals2 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals2 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B A' B',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' B' A' (eqa1 lib' x))
    -> ccequivc_ext lib A A'
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  pose proof (tyvrt A A' B' (eqa1 lib'0 e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals2 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals2 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B A' B',
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' B' A' (eqa1 lib' x))
    -> ccequivc_ext lib A A'
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
  pose proof (tyvrt A A' B' (eqa1 lib'0 e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals2 : slow.

Lemma type_value_respecting_trans_per_bar_per_eq1 {o} :
  forall lib (ts : cts(o)) T T1 T2 A A' B a1 a' a2 b' (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> computes_to_valc lib T1 (mkc_equality a' b' A')
    -> computes_to_valc lib T (mkc_equality a1 a2 A)
    -> ccequivc_ext lib a1 a'
    -> ccequivc_ext lib a2 b'
    -> ccequivc_ext lib A A'
    -> per_bar (per_eq ts) lib T1 T2 eq
    -> per_bar (per_eq ts) lib T T2 eq.
Proof.
  introv tsp comp1 comp2 ceq1 ceq2 ceq3 per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  unfold per_eq in *; exrepnd.
  spcast.
  eapply lib_extends_preserves_computes_to_valc in comp1;[|exact x].
  eapply lib_extends_preserves_computes_to_valc in comp2;[|exact x].
  computes_to_eqval.
  exists A B0 a1 a2 b1 b2 eqa1; dands; spcast; eauto 3 with slow.

  - introv.
    pose proof (tsp lib'1 (lib_extends_trans e x)) as tsp; simpl in *.
    pose proof (per4 lib'1 e) as per4; simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto; eauto 3 with slow.

  - eapply cequivc_ext_eqorceq_ext_trans1; eauto; eauto 3 with slow.

  - eapply cequivc_ext_eqorceq_ext_trans1; eauto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply (implies_iff_per_eq_eq _ (trivial_bar lib'0));
      try apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;
      try apply in_ext_implies_all_in_bar_trivial_bar; eauto 3 with slow.
Qed.

Lemma cequivc_ext_eqorceq_ext_trans2 {o} :
  forall lib (a b c : @CTerm o) (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> ccequivc_ext lib a b
    -> eqorceq_ext lib eqa c b
    -> eqorceq_ext lib eqa a c.
Proof.
  introv resp trans sym ceq eoc; introv.
  pose proof (eoc _ e) as eoc.
  pose proof (resp _ e) as resp.
  pose proof (sym _ e) as sym.
  pose proof (trans _ e) as trans.
  simpl in *; spcast.
  unfold eqorceq in *; repndors.

  - left.
    eapply trans;[|eauto].
    apply sym.
    apply resp;[|apply ccequivc_ext_sym; eauto 3 with slow].
    eapply trans;[eauto|]; tcsp.

  - right.
    apply ccequivc_ext_sym in eoc.
    eapply ccequivc_ext_trans;[|eauto]; eauto 3 with slow.
Qed.

Lemma type_value_respecting_trans_per_bar_per_eq2 {o} :
  forall lib (ts : cts(o)) T T1 T2 A A' B a1 a' a2 b' (eqa : lib-per(lib,o)) eq,
    in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> computes_to_valc lib T1 (mkc_equality a' b' A')
    -> computes_to_valc lib T (mkc_equality a1 a2 A)
    -> ccequivc_ext lib a1 a'
    -> ccequivc_ext lib a2 b'
    -> ccequivc_ext lib A A'
    -> per_bar (per_eq ts) lib T2 T1 eq
    -> per_bar (per_eq ts) lib T T2 eq.
Proof.
  introv tsp comp1 comp2 ceq1 ceq2 ceq3 per.
  unfold per_bar in *; exrepnd.
  exists bar eqa0; dands; auto.
  introv br ext; introv.
  pose proof (per0 _ br _ ext x) as per0; simpl in *.

  unfold per_eq in *; exrepnd.
  spcast.
  eapply lib_extends_preserves_computes_to_valc in comp1;[|exact x].
  eapply lib_extends_preserves_computes_to_valc in comp2;[|exact x].
  computes_to_eqval.
  exists A A0 a1 a2 a0 a3 eqa1; dands; spcast; eauto 3 with slow.

  - introv.
    pose proof (tsp lib'1 (lib_extends_trans e x)) as tsp; simpl in *.
    pose proof (per4 lib'1 e) as per4; simpl in *.
    onedtsp4 uv tys tyvr tyvrt tes tet tevr tygs tygt dum.
    eapply tyvrt; eauto; eauto 3 with slow.

  - eapply cequivc_ext_eqorceq_ext_trans2; eauto; eauto 3 with slow.

  - eapply cequivc_ext_eqorceq_ext_trans2; eauto; eauto 3 with slow.

  - eapply eq_term_equals_trans;[eauto|].
    apply eq_term_equals_sym.
    apply (eqorceq_implies_iff_per_eq_eq _ (trivial_bar lib'0));
      try apply in_ext_ext_implies_all_in_bar_ext_trivial_bar;
      try apply in_ext_implies_all_in_bar_trivial_bar; eauto 3 with slow;
        eapply cequivc_ext_eqorceq_ext_trans2; eauto; eauto 3 with slow.
Qed.

Lemma eq_per_eq_bar_sym {o} :
  forall lib a1 a2 (eqa : lib-per(lib,o)) t1 t2,
    eq_per_eq_bar lib a1 a2 eqa t1 t2
    -> eq_per_eq_bar lib a1 a2 eqa t2 t1.
Proof.
  introv e; unfold eq_per_eq_bar in *; exrepnd.
  exists bar; introv br ext; introv.
  pose proof (e0 _ br _ ext x) as e0; simpl in *.
  unfold eq_per_eq in *.
  repnd; dands; auto.
Qed.

Lemma eq_per_eq_bar_trans {o} :
  forall lib a1 a2 (eqa : lib-per(lib,o)) t1 t2 t3,
    eq_per_eq_bar lib a1 a2 eqa t1 t2
    -> eq_per_eq_bar lib a1 a2 eqa t2 t3
    -> eq_per_eq_bar lib a1 a2 eqa t1 t3.
Proof.
  introv e1 e2; unfold eq_per_eq_bar in *; exrepnd.
  exists (intersect_bars bar0 bar); introv br ext; introv.
  simpl in *; exrepnd.
  pose proof (e2 _ br0 lib'0 (lib_extends_trans ext br3) x) as e2; simpl in *.
  pose proof (e0 _ br2 lib'0 (lib_extends_trans ext br1) x) as e0; simpl in *.
  unfold eq_per_eq in *.
  repnd; dands; auto.
Qed.

Lemma eq_per_eq_bar_resp {o} :
  forall lib a1 a2 (eqa : lib-per(lib,o)) t1 t2,
    eq_per_eq_bar lib a1 a2 eqa t1 t1
    -> ccequivc_ext lib t1 t2
    -> eq_per_eq_bar lib a1 a2 eqa t1 t2.
Proof.
  introv e ceq; unfold eq_per_eq_bar in *; exrepnd.
  exists bar; introv br ext; introv.
  simpl in *; exrepnd.
  pose proof (e0 _ br _ ext x) as e0; simpl in *.
  unfold eq_per_eq in *.

  pose proof (ceq _ x) as ceq; simpl in ceq; spcast.
  repnd; dands; spcast; auto.
  eapply cequivc_axiom;[eauto|]; eauto 3 with slow.
Qed.


Lemma close_type_system_eq {o} :
  forall lib (ts : cts(o))
         T T' (eq : per) A B a1 a2 b1 b2 (eqa : lib-per(lib,o)),
    type_system ts
    -> defines_only_universes ts
    -> type_monotone ts
    -> computes_to_valc lib T (mkc_equality a1 a2 A)
    -> computes_to_valc lib T' (mkc_equality b1 b2 B)
    -> in_ext_ext lib (fun lib' x => close ts lib' A B (eqa lib' x))
    -> eqorceq_ext lib eqa a1 b1
    -> eqorceq_ext lib eqa a2 b2
    -> (eq <=2=> (eq_per_eq_bar lib a1 a2 eqa))
    -> per_eq (close ts) lib T T' eq
    -> in_ext_ext lib (fun lib' x => type_sys_props4 (close ts) lib' A B (eqa lib' x))
    -> type_sys_props4 (close ts) lib T T' eq.
Proof.
  introv tsts dou mon c1 c2 inextcl eos1 eos2 eqiff per; introv inexttsp.

  prove_type_sys_props4 SCase; introv.

  + SCase "uniquely_valued".
    introv cl.
    dclose_lr; clear cl.
    apply per_eq_implies_per_bar in per.
    eapply uniquely_valued_per_bar_per_eq; eauto.

  + SCase "type_symmetric".
    introv cl eqs.
    dclose_lr; clear cl.
    apply per_bar_per_eq_implies_close.
    eapply type_extensionality_per_bar; eauto.

  + SCase "type_value_respecting".
    introv h ceq.
    apply CL_eq.
    eapply ccequivc_ext_implies_per_eq1; try exact h; eauto.

  + SCase "type_value_respecting_trans".
    introv h ceq cl.

    repndors; subst.

    * dup ceq as c.
      eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
      dup inexttsp as inexttsp'.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in inexttsp';[|eauto].
      dclose_lr; clear cl.
      apply per_bar_per_eq_implies_close.
      eapply type_value_respecting_trans_per_bar_per_eq1;
        try exact h; try exact c1; eauto 3 with slow.

    * dup ceq as c.
      eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
      dup inexttsp as inexttsp'.
      apply in_ext_ext_type_sys_props4_sym in inexttsp'.
      dup inexttsp' as inexttsp''.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in inexttsp';[|eauto].
      dclose_lr; clear cl.
      apply per_bar_per_eq_implies_close.
      eapply type_value_respecting_trans_per_bar_per_eq1;
        try exact h; try exact c2; eauto 3 with slow.

    * dup ceq as c.
      eapply ccequivc_ext_equality in ceq;[|eauto]; exrepnd; spcast.
      dup inexttsp as inexttsp'.
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in inexttsp';[|eauto].
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
      eapply ccequivc_ext_preserves_in_ext_ext_type_sys_props4 in inexttsp';[|eauto].
      apply in_ext_ext_type_sys_props4_sym in inexttsp'.
      dclose_lr; clear cl.
      apply per_bar_per_eq_implies_close.
      eapply type_value_respecting_trans_per_bar_per_eq2;
        try exact h; try exact c2; eauto 3 with slow.

  + SCase "term_symmetric".
    clear per.
    introv ee.
    apply eqiff in ee; apply eqiff.
    apply eq_per_eq_bar_sym; auto.

  + SCase "term_transitive".
    clear per.
    introv ee1 ee2.
    apply eqiff in ee1; apply eqiff in ee2; apply eqiff.
    eapply eq_per_eq_bar_trans; eauto.

  + SCase "term_value_respecting".
    clear per.
    introv ee ceq.
    apply eqiff in ee; apply eqiff; clear eqiff.
    apply eq_per_eq_bar_resp; auto.

  + SCase "type_gsymmetric".
    clear per.
    dup inexttsp as inexttsp'.
    apply in_ext_ext_type_sys_props4_sym in inexttsp'.

    split; introv cl; dclose_lr; apply per_bar_per_eq_implies_close.

    *

XXXX
    split; introv cl; dclose_lr; apply CL_eq;
      unfold per_eq_bar in *; exrepnd.

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 a0 a3 A A0) as w1.
      repeat (autodimp w1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 a0 a3 A A0) as w2.
      repeat (autodimp w2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 a0 a3 A A0) as w3.
      repeat (autodimp w3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in w3.
      pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans (close ts) lib (intersect_bars bar bar0) A B A0 B0 eqa eqa0) as w4.
      repeat (autodimp w4 hyp); eauto 3 with slow;[].

      exists B0 A b0 b3 a1 a2 eqa.
      dands; auto.

      {
        exists (intersect_bars bar bar0); dands; eauto 3 with slow.

        { eapply all_in_bar_ext_type_sys_props4_implies_ts_sym;
            [apply implies_all_in_bar_ext_intersect_bars_left;eauto|].
          eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2;eauto 3 with slow. }

        { eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow;[].
          eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow. }

        { eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow;[].
          eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow. }
      }

      {
        eapply eq_term_equals_trans;[eauto|].
        eapply (eqorceq_implies_iff_per_eq_eq _ (intersect_bars bar bar0)); eauto 3 with slow sym.
        { eapply eq_term_equals_preserves_all_in_bar_ext_term_equality_symmetric; eauto 3 with slow. }
        { eapply eq_term_equals_preserves_all_in_bar_ext_term_equality_transitive; eauto 3 with slow. }
        { eapply eq_term_equals_preserves_all_in_bar_ext_term_equality_respecting; eauto 3 with slow. }
      }
    }

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 b0 b3 A B0) as w1.
      repeat (autodimp w1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 b0 b3 A B0) as w2.
      repeat (autodimp w2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 b0 b3 A B0) as w3.
      repeat (autodimp w3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in w3.

      pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans3 (close ts) lib (intersect_bars bar bar0) A B B0 A0 eqa eqa0) as w4.
      repeat (autodimp w4 hyp); eauto 3 with slow;[].

      exists A A0 a1 a2 a0 a3 eqa.
      dands; auto.

      {
        exists (intersect_bars bar bar0); dands; eauto 3 with slow.

        { eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans4;eauto 3 with slow. }

        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow. }

        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow. }
      }

      {
        eapply eq_term_equals_trans;[eauto|].
        apply eq_term_equals_sym.
        eapply (eqorceq_implies_iff_per_eq_eq _ (intersect_bars bar bar0)); eauto 3 with slow.
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow. }
        { eapply implies_all_in_bar_ext_eqorceq_trans_ccequivc; eauto; eauto 3 with slow.
          eapply implies_all_in_bar_ext_eqorceq_sym;
            [|apply implies_all_in_bar_ext_intersect_bars_left;eauto|]; eauto 3 with slow. }
      }
    }

  + SCase "type_gtransitive".
    sp.

  + SCase "type_mtransitive".
    clear per.
    rename_hyp_with eq1 cl1.
    rename_hyp_with eq2 cl2.

    repndors; subst; dclose_lr; clear cl1 cl2;
      allunfold @per_eq_bar; exrepnd.

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T a1 a2 b0 b3 A B0) as w1.
      repeat (autodimp w1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T a1 a2 b0 b3 A B0) as w2.
      repeat (autodimp w2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T a1 a2 b0 b3 A B0) as w3.
      repeat (autodimp w3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in w3.
      pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans3 (close ts) lib (intersect_bars bar bar0) A B B0 A0 eqa eqa0) as w4.
      repeat (autodimp w4 hyp); eauto 3 with slow;[].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar1 T a1 a2 a4 a5 A A1) as z1.
      repeat (autodimp z1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar1 T a1 a2 a4 a5 A A1) as z2.
      repeat (autodimp z2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar1 T a1 a2 a4 a5 A A1) as z3.
      repeat (autodimp z3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in z3.
      pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans (close ts) lib (intersect_bars bar bar1) A B A1 B1 eqa eqa1) as z4.
      repeat (autodimp z4 hyp); eauto 3 with slow;[].

      dands; apply CL_eq; unfold per_eq_bar.

      - exists A0 B1 a0 a3 b4 b5 eqa0; dands; auto.

        exists (intersect3bars bar bar0 bar1); dands; eauto 3 with slow.

        + pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2 (close ts) lib (intersect_bars bar bar1) A B A1 B1 eqa eqa1) as u1.
          repeat (autodimp u1 hyp); eauto 3 with slow;[].
          pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans4 (close ts) lib (intersect_bars bar bar0) A B B0 A0 eqa eqa0) as u2.
          repeat (autodimp u2 hyp); eauto 3 with slow;[].
          eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1 in u1; try (exact w4); eauto 3 with slow;[].
          eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1 in u2; try (exact w4); eauto 3 with slow;[].

          pose proof (all_in_bar_ext_type_sys_props4_trans2 (close ts) lib (intersect3bars bar bar0 bar1) A B A0 B1 eqa eqa0) as q.
          repeat (autodimp q hyp); eauto 3 with slow.

          eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1; eauto 3 with slow.
          eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2; eauto 3 with slow.

        + eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
          apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b0 _ A B); eauto 4 with slow;[].
          apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a4); eauto 4 with slow;[].
          apply all_in_bar_ccequivc_sym.
          eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

        + eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
          apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b3 _ A B); eauto 4 with slow;[].
          apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a5); eauto 4 with slow;[].
          apply all_in_bar_ccequivc_sym.
          eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

      - exists A0 B1 a0 a3 b4 b5 eqa0; dands; auto.

        + exists (intersect3bars bar bar0 bar1); dands; eauto 3 with slow.

          * pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2 (close ts) lib (intersect_bars bar bar1) A B A1 B1 eqa eqa1) as u1.
            repeat (autodimp u1 hyp); eauto 3 with slow;[].
            pose proof (all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans4 (close ts) lib (intersect_bars bar bar0) A B B0 A0 eqa eqa0) as u2.
            repeat (autodimp u2 hyp); eauto 3 with slow;[].
            eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1 in u1; try (exact w4); eauto 3 with slow;[].
            eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1 in u2; try (exact w4); eauto 3 with slow;[].

            pose proof (all_in_bar_ext_type_sys_props4_trans2 (close ts) lib (intersect3bars bar bar0 bar1) A B A0 B1 eqa eqa0) as q.
            repeat (autodimp q hyp); eauto 3 with slow.

            eapply all_in_bar_ext_type_sys_props4_change_eq_term_equals1; eauto 3 with slow.
            eapply all_in_bar_ext_type_sys_props4_implies_type_equality_respecting_trans2; eauto 3 with slow.

          * eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b0 _ A B); eauto 4 with slow;[].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a4); eauto 4 with slow;[].
            apply all_in_bar_ccequivc_sym.
            eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

          * eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b3 _ A B); eauto 4 with slow;[].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a5); eauto 4 with slow;[].
            apply all_in_bar_ccequivc_sym.
            eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

        + eapply eq_term_equals_trans;[eauto|].
          apply (eqorceq_implies_iff_per_eq_eq _ (intersect3bars bar bar0 bar1)); eauto 5 with slow.

          * eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow].
            apply all_in_bar_ext_eq_term_equals_sym; eauto 3 with slow.

          * eapply (all_in_bar_ext_eqorceq_eq_term_equals _ _ eqa);
              [|eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow];apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ b0); eauto 3 with slow.
            { eapply all_in_bar_ccequivc_trans; eauto 3 with slow. }
            { eapply implies_all_in_bar_ext_eqorceq_sym; eauto 4 with slow. }

          * eapply (all_in_bar_ext_eqorceq_eq_term_equals _ _ eqa);
              [|eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow];apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ b3); eauto 3 with slow.
            { eapply all_in_bar_ccequivc_trans; eauto 3 with slow. }
            { eapply implies_all_in_bar_ext_eqorceq_sym; eauto 4 with slow. }
    }

    {
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar0 T' b1 b2 b0 b3 B B0) as w1.
      repeat (autodimp w1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar0 T' b1 b2 b0 b3 B B0) as w2.
      repeat (autodimp w2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar0 T' b1 b2 b0 b3 B B0) as w3.
      repeat (autodimp w3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in w3.
      pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans3 (close ts) lib (intersect_bars bar bar0) B A B0 A0 eqa eqa0) as w4.
      repeat (autodimp w4 hyp); eauto 3 with slow;[].

      pose proof (two_computes_to_valc_ceq_bar_mkc_equality1 bar bar1 T' b1 b2 a4 a5 B A1) as z1.
      repeat (autodimp z1 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality2 bar bar1 T' b1 b2 a4 a5 B A1) as z2.
      repeat (autodimp z2 hyp);[].
      pose proof (two_computes_to_valc_ceq_bar_mkc_equality3 bar bar1 T' b1 b2 a4 a5 B A1) as z3.
      repeat (autodimp z3 hyp);[].
      apply all_in_bar_ccequivc_implies_all_in_bar_ccequivc_ext in z3.
      pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans (close ts) lib (intersect_bars bar bar1) B A A1 B1 eqa eqa1) as z4.
      repeat (autodimp z4 hyp); eauto 3 with slow;[].

      dands; apply CL_eq; unfold per_eq_bar.

      - exists A0 B1 a0 a3 b4 b5 eqa0; dands; auto.

        exists (intersect3bars bar bar0 bar1); dands; eauto 3 with slow.

        + pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans2 (close ts) lib (intersect_bars bar bar1) B A A1 B1 eqa eqa1) as u1.
          repeat (autodimp u1 hyp); eauto 3 with slow;[].
          pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans4 (close ts) lib (intersect_bars bar bar0) B A B0 A0 eqa eqa0) as u2.
          repeat (autodimp u2 hyp); eauto 3 with slow;[].

          eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1 in u1; try (exact w4); eauto 3 with slow;[].
          eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1 in u2; try (exact w4); eauto 3 with slow;[].

          pose proof (all_in_bar_ext_type_sys_props4_sym_trans2 (close ts) lib (intersect3bars bar bar0 bar1) B A A0 B1 eqa eqa0) as q.
          repeat (autodimp q hyp); eauto 3 with slow.

          eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1; eauto 3 with slow.
          eapply all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans2; eauto 3 with slow.

        + eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
          apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b0 _ A B); eauto 4 with slow;[].
          apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a4); eauto 4 with slow;[].
          apply all_in_bar_ccequivc_sym.
          eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

        + eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
          apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b3 _ A B); eauto 4 with slow;[].
          apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a5); eauto 4 with slow;[].
          apply all_in_bar_ccequivc_sym.
          eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

      - exists A0 B1 a0 a3 b4 b5 eqa0; dands; auto.

        + exists (intersect3bars bar bar0 bar1); dands; eauto 3 with slow.

          * pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans2 (close ts) lib (intersect_bars bar bar1) B A A1 B1 eqa eqa1) as u1.
            repeat (autodimp u1 hyp); eauto 3 with slow.
            pose proof (all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans4 (close ts) lib (intersect_bars bar bar0) B A B0 A0 eqa eqa0) as u2.
            repeat (autodimp u2 hyp); eauto 3 with slow.

            eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1 in u1; try (exact w4); eauto 3 with slow;[].
            eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1 in u2; try (exact w4); eauto 3 with slow;[].
            pose proof (all_in_bar_ext_type_sys_props4_sym_trans2 (close ts) lib (intersect3bars bar bar0 bar1) B A A0 B1 eqa eqa0) as q.
            repeat (autodimp q hyp); eauto 3 with slow.

            eapply all_in_bar_ext_type_sys_props4_sym_change_eq_term_equals1; eauto 3 with slow.
            eapply all_in_bar_ext_type_sys_props4_sym_implies_type_equality_respecting_trans2; eauto 3 with slow.

          * eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b0 _ A B); eauto 4 with slow;[].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a4); eauto 4 with slow;[].
            apply all_in_bar_ccequivc_sym.
            eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

          * eapply all_in_bar_ext_eqorceq_eq_term_equals2;[|apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans _ _ (close ts) _ _ b3 _ A B); eauto 4 with slow;[].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ a5); eauto 4 with slow;[].
            apply all_in_bar_ccequivc_sym.
            eapply all_in_bar_ccequivc_trans; eauto 3 with slow.

        + eapply eq_term_equals_trans;[eauto|].
          apply (eqorceq_implies_iff_per_eq_eq _ (intersect3bars bar bar0 bar1)); eauto 5 with slow.

          * eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow].
            apply all_in_bar_ext_eq_term_equals_sym; eauto 3 with slow.

          * eapply (all_in_bar_ext_eqorceq_eq_term_equals _ _ eqa);
              [|eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow];apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ b0); eauto 3 with slow.
            { eapply all_in_bar_ccequivc_trans; eauto 3 with slow. }
            { eapply implies_all_in_bar_ext_eqorceq_sym; eauto 4 with slow. }

          * eapply (all_in_bar_ext_eqorceq_eq_term_equals _ _ eqa);
              [|eapply all_in_bar_ext_eq_term_equals_trans;[|eauto 3 with slow];apply all_in_bar_ext_eq_term_equals_sym;eauto 3 with slow].
            apply (implies_all_in_bar_ext_eqorceq_trans_ccequivc _ _ _ b3); eauto 3 with slow.
            { eapply all_in_bar_ccequivc_trans; eauto 3 with slow. }
            { eapply implies_all_in_bar_ext_eqorceq_sym; eauto 4 with slow. }
    }
Qed.
