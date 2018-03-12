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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in w.
  apply uv in q.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.

Lemma type_sys_props4_ccequivc_ext_implies_eq_term_equals {o} :
  forall (ts : cts(o)) lib A B C D A1 A2 eqa eqa1 eqa2,
    type_sys_props4 ts lib A B eqa
    -> ts lib A1 C eqa1
    -> ts lib A2 D eqa2
    -> ccequivc_ext lib A A1
    -> ccequivc_ext lib A A2
    -> eqa1 <=2=> eqa2.
Proof.
  introv h w q u v; introv.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A1 C eqa1) as xx; repeat (autodimp xx hyp).
  pose proof (tyvrt1 A A2 D eqa2) as yy; repeat (autodimp yy hyp).
  apply uv in xx.
  apply uv in yy.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tyvr; eauto 3 with slow.
Qed.

Lemma in_ext_ext_eq_term_equals_refl {o} :
  forall lib (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqa lib' x)).
Proof.
  repeat introv; tcsp.
Qed.
Hint Resolve in_ext_ext_eq_term_equals_refl : slow.

Lemma ccequivc_ext_preserves_in_type_sys_props4 {o} :
  forall ts lib (A A' B : @CTerm o) eq,
    ccequivc_ext lib A A'
    -> type_sys_props4 ts lib A B eq
    -> type_sys_props4 ts lib A' B eq.
Proof.
  introv ceq tsp; introv.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  unfold type_sys_props4; dands; auto.

  - introv tsts.
    apply (uv T3).
    apply (tyvrt1 A A' T3 eq'); eauto 3 with slow.

  - introv tsts eqs.
    pose proof (tyvrt1 A A' T3 eq) as q.
    repeat (autodimp q hyp); eauto 3 with slow.
    eapply tys in q;eauto.
    pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
    pose proof (dum A A' T3 eq eq') as w.
    repeat (autodimp w hyp); tcsp.
    apply tygs; auto.

  - introv w c.
    repndors; subst; tcsp.

    pose proof (tyvr A T3) as q; repeat (autodimp q hyp); eauto 3 with slow.
    pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
    pose proof (dum A A' T3 eq eq) as w.
    repeat (autodimp w hyp); tcsp.
    apply tygs; auto.

  - introv h c tsts.
    repndors; subst; tcsp; try (complete (eapply tyvrt1; eauto)).

    + pose proof (tyvrt1 A T3 T4 eq') as q; repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
      pose proof (dum A A' T4 eq eq') as w.
      repeat (autodimp w hyp); tcsp.
      apply tygs; auto.

    + pose proof (tyvrt1 A T3 T4 eq') as q; repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
      pose proof (dum A A' T4 eq eq') as w.
      repeat (autodimp w hyp); tcsp.
      apply tygs; auto.

  - introv h c tsts.
    repndors; subst; tcsp; try (complete (eapply tyvrt2; eauto)).

    + pose proof (tyvrt1 A A' T3 eq') as z; repeat (autodimp z hyp); eauto 3 with slow.
      pose proof (tyvrt2 A T3 T4 eq') as q; repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
      pose proof (dum A A' T4 eq eq') as w.
      repeat (autodimp w hyp); tcsp.
      apply tygs; auto.

    + pose proof (tyvrt1 A A' T3 eq') as z; repeat (autodimp z hyp); eauto 3 with slow.
      pose proof (tyvrt2 A T3 T4 eq') as q; repeat (autodimp q hyp); eauto 3 with slow.
      pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
      pose proof (dum A A' T4 eq eq') as w.
      repeat (autodimp w hyp); tcsp.
      apply tygs; auto.

  - introv; split; intro q.

    + pose proof (tyvrt1 A A' T3 eq') as h; repeat (autodimp h hyp); eauto 3 with slow.
      apply tygs in h.
      pose proof (tyvr A A') as z; repeat (autodimp z hyp); eauto 3 with slow.
      pose proof (dum A T3 A' eq' eq) as w.
      repeat (autodimp w hyp); tcsp.

    + pose proof (tyvrt1 A A' T3 eq') as h; repeat (autodimp h hyp); eauto 3 with slow.
      pose proof (tyvr A A') as z; repeat (autodimp z hyp); eauto 3 with slow.
      apply tygs in z.
      pose proof (dum A A' T3 eq eq') as w.
      repeat (autodimp w hyp); tcsp.

  - pose proof (tyvr A A') as h; repeat (autodimp h hyp); eauto 3 with slow.
    pose proof (dum A A' B eq eq) as w.
    repeat (autodimp w hyp); tcsp.
    apply tygs; auto.

  - introv h ts1 ts2.
    repndors; subst; tcsp; try (complete (eapply dum; eauto)).

    pose proof (tyvrt1 A A' T4 eq2) as h; repeat (autodimp h hyp); eauto 3 with slow.
    pose proof (tyvrt1 A A' T3 eq1) as q; repeat (autodimp q hyp); eauto 3 with slow.
    apply tygs in q.

    pose proof (dum A T3 T4 eq1 eq2) as w.
    repeat (autodimp w hyp); tcsp; try (complete (apply tygs; auto)).
Qed.

Lemma ccequivc_ext_preserves_in_ext_ext_type_sys_props4 {o} :
  forall ts lib (A A' B : @CTerm o) eqa,
    ccequivc_ext lib A A'
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A' B (eqa lib' x)).
Proof.
  introv ceq tsp; introv.
  pose proof (tsp _ e) as tsp; simpl in *.
  eapply ccequivc_ext_preserves_in_type_sys_props4; eauto; eauto 3 with slow.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A' B' (eqa1 lib'0 e)) as q.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A' B' (eqa1 lib'0 e)) as q.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A' B' (eqa1 lib'0 e)) as q.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A' B' (eqa1 lib'0 e)) as q.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A' B' (eqa1 lib'0 e)) as q.
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
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  pose proof (tyvrt1 A A' B' (eqa1 lib'0 e)) as q.
  repeat (autodimp q hyp); eauto 3 with slow.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals2 : slow.

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

Lemma eqorceq_ext_sym {o} :
  forall lib (a b : @CTerm o) (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> eqorceq_ext lib eqa a b
    -> eqorceq_ext lib eqa b a.
Proof.
  introv sym eoc; introv.
  pose proof (eoc _ e) as eoc.
  pose proof (sym _ e) as sym.
  simpl in *; spcast.
  unfold eqorceq in *; repndors; tcsp.
  right.
  apply ccequivc_ext_sym; auto.
Qed.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals3 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B C,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' A C (eqa1 lib' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in tsts.
  apply tsts in ceq; apply tsts; tcsp.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals3 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals3 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B C,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' A C (eqa1 lib' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts e1 e2; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in tsts.
  apply tsts in e1; apply tsts in e2; apply tsts; tcsp.
  eapply tet; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals3 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals3 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B C,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' A C (eqa1 lib' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_respecting lib'' (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts e1 ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply uv in tsts.
  apply tsts in e1; apply tsts; tcsp.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals3 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals4 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B C,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' C A (eqa1 lib' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_symmetric (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs in tsts.
  apply uv in tsts.
  apply tsts in ceq; apply tsts; tcsp.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_symmetric_eq_term_equals4 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals4 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B C,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' C A (eqa1 lib' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_transitive (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts e1 e2; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs in tsts.
  apply uv in tsts.
  apply tsts in e1; apply tsts in e2; apply tsts; tcsp.
  eapply tet; eauto.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_transitive_eq_term_equals4 : slow.

Lemma in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals4 {o} :
  forall ts lib' lib (eqa : lib-per(lib,o)) (eqa1 : lib-per(lib',o)) A B C,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' A B (eqa lib' x))
    -> in_ext_ext lib' (fun lib' x => ts lib' C A (eqa1 lib' x))
    -> in_ext_ext lib' (fun lib'' x => term_equality_respecting lib'' (eqa1 lib'' x)).
Proof.
  introv ext tsp tsts e1 ceq; introv.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp; simpl in *.
  pose proof (tsts _ e) as tsts; simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs in tsts.
  apply uv in tsts.
  apply tsts in e1; apply tsts; tcsp.
Qed.
Hint Resolve in_ext_ext_type_sys_props4_implies_term_equality_respecting_eq_term_equals4 : slow.

Lemma eqorceq_ext_trans1 {o} :
  forall lib (a b c : @CTerm o) (eqa : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> eqorceq_ext lib eqa a b
    -> eqorceq_ext lib eqa b c
    -> eqorceq_ext lib eqa a c.
Proof.
  introv sym trans resp ceq1 ceq2; introv.
  pose proof (ceq1 _ e) as ceq1.
  pose proof (ceq2 _ e) as ceq2.
  pose proof (resp _ e) as resp.
  pose proof (sym _ e) as sym.
  pose proof (trans _ e) as trans.
  simpl in *; spcast.
  unfold eqorceq in *; repndors.

  - left.
    eapply trans; eauto.

  - left.
    eapply trans;[|eauto].
    apply sym.
    apply resp; auto;[|apply ccequivc_ext_sym;auto].
    apply resp;[|apply ccequivc_ext_sym; eauto 3 with slow].
    eapply trans;[eauto|]; tcsp.

  - left.
    eapply trans;[eauto|].
    apply resp; auto.
    eapply trans;[eauto|]; tcsp.

  - right.
    eapply ccequivc_ext_trans;[|eauto]; eauto 3 with slow.
Qed.

Lemma in_ext_ext_type_sys_props4_trans_implies_eq_term_equals1 {o} :
  forall ts lib lib' (eqa1 eqa2 : lib-per(lib',o)) (eqa : lib-per(lib,o)) A B C D,
    lib_extends lib' lib
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A B (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' B C (eqa2 lib'' x))
    -> in_ext_ext lib (fun lib' x => type_sys_props4 ts lib' B D (eqa lib' x))
    -> in_ext_ext lib' (fun lib'' x => (eqa1 lib'' x) <=2=> (eqa2 lib'' x)).
Proof.
  introv ext tsa tsb tsp; introv.
  pose proof (tsa _ e) as tsa.
  pose proof (tsb _ e) as tsb.
  pose proof (tsp _ (lib_extends_trans e ext)) as tsp.
  simpl in *.
  onedtsp4 uv tys tyvr tyvrt1 tyvrt2 tes tet tevr tygs tygt dum.
  apply tygs in tsa.
  apply uv in tsa.
  apply uv in tsb.
  eapply eq_term_equals_trans;[|eauto].
  apply eq_term_equals_sym;auto.
Qed.

Lemma in_ext_ext_eq_term_equals_sym {o} :
  forall lib (eqa1 eqa2 : lib-per(lib,o)),
    in_ext_ext lib (fun lib' x => (eqa1 lib' x) <=2=> (eqa2 lib' x))
    -> in_ext_ext lib (fun lib' x => (eqa2 lib' x) <=2=> (eqa1 lib' x)).
Proof.
  introv ext; introv.
  apply eq_term_equals_sym; tcsp.
Qed.

Lemma eqorceq_ext_eq_change_per1 {o} :
  forall lib (eqa eqb : lib-per(lib,o)) a b,
    in_ext_ext lib (fun lib' x => (eqa lib' x) <=2=> (eqb lib' x))
    -> eqorceq_ext lib eqa a b
    -> eqorceq_ext lib eqb a b.
Proof.
  introv iext eoc; introv.
  pose proof (eoc _ e) as eoc.
  unfold eqorceq in *; simpl in *; repndors; tcsp.
  left.
  apply iext; eauto.
Qed.

Lemma eqorceq_ext_refl {o} :
  forall lib (eqa : lib-per(lib,o)) a,
    eqorceq_ext lib eqa a a.
Proof.
  repeat introv.
  right; eauto 3 with slow.
Qed.
Hint Resolve eqorceq_ext_refl : slow.

Lemma eqorceq_ext_trans {o} :
  forall lib (eqa : lib-per(lib,o)) (a b c : @CTerm o),
    in_ext_ext lib (fun lib' x => term_equality_symmetric (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_transitive (eqa lib' x))
    -> in_ext_ext lib (fun lib' x => term_equality_respecting lib' (eqa lib' x))
    -> eqorceq_ext lib eqa a b
    -> eqorceq_ext lib eqa b c
    -> eqorceq_ext lib eqa a c.
Proof.
  introv sym trans resp h q; introv.
  pose proof (h _ e) as h; simpl in h.
  pose proof (q _ e) as q; simpl in q.
  eapply eqorceq_trans; eauto.
Qed.

Lemma in_ext_ext_type_sys_props4_ccequivc_ext_trans_implies_eq_term_equals1 {o} :
  forall ts lib lib' (eqa1 eqa2 : lib-per(lib',o)) (eqa : lib-per(lib,o)) A B C D B1 B2,
    lib_extends lib' lib
    -> in_ext_ext lib (fun lib'' x => type_sys_props4 ts lib'' B D (eqa lib'' x))
    -> ccequivc_ext lib' B B1
    -> ccequivc_ext lib' B B2
    -> in_ext_ext lib' (fun lib'' x => ts lib'' A B1 (eqa1 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => ts lib'' B2 C (eqa2 lib'' x))
    -> in_ext_ext lib' (fun lib'' x => (eqa1 lib'' x) <=2=> (eqa2 lib'' x)).
Proof.
  introv ext tsp ceqa eqb h w.
  eapply in_ext_ext_type_sys_props4_trans_implies_eq_term_equals1;
    try exact tsp; auto.

  { eapply trans_ccequivc_ext_in_ext_eq_types_implies3;
      try exact h; eauto; eauto 3 with slow.
    apply in_ext_ext_type_sys_props4_sym; eauto. }

  { eapply trans_ccequivc_ext_in_ext_eq_types_implies;
      try exact w; eauto; eauto 3 with slow. }
Qed.
